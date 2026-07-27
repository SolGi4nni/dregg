//! The streaming response-emit path (roadmap Stage 2).
//!
//! The default serve crosses `drorb_serve`/`drorb_serve_metered`, which return the
//! WHOLE response in one buffer — the host holds the entire response before it writes
//! a byte. This path instead pulls the response out of the proven core one bounded
//! chunk at a time through the re-entrant `drorb_serve_stream` seam (`idx :: chunkSize
//! :: request` in, `flags :: chunk` out), writing each chunk straight to the socket
//! and dropping it. So the host never materializes the whole response — its per-request
//! working set is one chunk, whatever the response size.
//!
//! The emitted chunks reassemble to the exact `drorb_serve` response byte-for-byte
//! (proven core-side: `Reactor.ServeStream.serveChunkList_flatten`), so the wire bytes
//! are identical to the batch path; only the host's memory profile changes.
//!
//! This path mirrors the NON-metered `drorb_serve` decision (the proven
//! `servePipelineFull2` fold), so it is gated OFF by default (`DRORB_STREAM_SERVE=1`)
//! and the default metered conformance path is untouched. Streaming the metered serve
//! (IP-filter / rate gates) is a follow-on once those gates thread through the stream
//! seam.

use std::io::Write;
use std::sync::mpsc::{Receiver, Sender};

use crate::pool::PooledBuf;
use crate::serve::{Seam, ServeGateway};

/// `flags` bit 0: more chunks follow this one.
const FLAG_MORE: u8 = 1;
/// `flags` bit 1: the proven keep-alive decision for this response.
const FLAG_KEEPALIVE: u8 = 2;

/// Whether the streaming response-emit path is enabled (`DRORB_STREAM_SERVE=1`).
/// Off by default, so the default byte-identical metered serve path is preserved.
pub fn enabled() -> bool {
    matches!(std::env::var("DRORB_STREAM_SERVE").as_deref(), Ok("1"))
}

/// The bounded body-chunk size the emit pacer cuts at (`DRORB_STREAM_CHUNK`, default
/// 64 KiB). Floored at 1 so the pacer always makes progress; the proven core also
/// floors it (`paceBody` uses `max 1 chunk`).
pub fn chunk_size() -> u32 {
    std::env::var("DRORB_STREAM_CHUNK")
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(64 * 1024)
}

/// What the streamed emit recorded once the whole response reached the wire.
pub struct StreamedServe {
    /// The response HEAD chunk (status line + headers + blank line) — for the status
    /// class and access-log record; never the whole response.
    pub head: Vec<u8>,
    /// The exact number of response bytes written to the socket.
    pub bytes: u64,
    /// The proven keep-alive decision for this response.
    pub keepalive: bool,
}

/// Stream one request's response to `client` a bounded chunk at a time through the
/// proven `drorb_serve_stream` seam. The host holds one chunk at a time — its working
/// set is bounded by `chunk_size`, never the whole response.
///
/// Returns `Some(Ok(outcome))` after the whole response has been written,
/// `Some(Err(_))` on a client write error mid-stream, or `None` if the serve thread is
/// gone. Runs on the CONNECTION thread; only the per-chunk `drorb_serve_stream`
/// crossing touches the runtime-owner thread (via `gw`), like the proxy streaming path.
pub fn serve_streamed<W: Write>(
    req: &[u8],
    keepalive_req: bool,
    client: &mut W,
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> Option<std::io::Result<StreamedServe>> {
    let chunk = chunk_size();
    let mut idx: u32 = 0;
    let mut bytes: u64 = 0;
    let mut head: Vec<u8> = Vec::new();
    let mut keepalive_core = false;

    loop {
        // Frame `idx(4 BE) :: chunkSize(4 BE) :: request` into a pooled buffer (reused
        // from the pool each iteration; no growing per-request allocation).
        let mut framed = gw.pool().take();
        framed.clear();
        framed.extend_from_slice(&idx.to_be_bytes());
        framed.extend_from_slice(&chunk.to_be_bytes());
        framed.extend_from_slice(req);

        let out = gw.call_seam(framed, Seam::ServeStream, reply_tx, reply_rx)?;
        if out.is_empty() {
            // Past the last chunk (defensive; the `more` flag normally ends the loop).
            break;
        }
        let flags = out[0];
        let chunk_bytes = &out[1..];

        // Index 0 is the response HEAD — keep a copy for status/log recording.
        if idx == 0 {
            head.extend_from_slice(chunk_bytes);
            keepalive_core = flags & FLAG_KEEPALIVE != 0;
        }

        if let Err(e) = client.write_all(chunk_bytes) {
            return Some(Err(e));
        }
        bytes += chunk_bytes.len() as u64;
        // `out` (this chunk's pooled buffer) drops here, back to the pool — the host
        // never accumulates chunks.

        if flags & FLAG_MORE == 0 {
            break;
        }
        idx += 1;
    }

    if let Err(e) = client.flush() {
        return Some(Err(e));
    }

    Some(Ok(StreamedServe {
        head,
        bytes,
        // Honour BOTH the request's keep-alive intent and the proven core's decision.
        keepalive: keepalive_req && keepalive_core,
    }))
}
