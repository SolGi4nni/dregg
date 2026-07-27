//! The UDP/QUIC IO path: recv a datagram, drive the proven `Seam::Datagram`
//! (the stateful QUIC/H3 server — verified EverCrypt handshake + 1-RTT packet
//! protection, proven H3 dispatch, guarded serve), and send the response
//! datagram(s) back to the sender.
//!
//! Like the TCP paths, this host owns only the socket, the recv/send loop, and
//! the QUIC connection state; it never parses, decrypts, or rewrites a datagram.
//! The proven core stays a pure `ByteArray → ByteArray`, so the mutable QUIC
//! connection table (and thus the handshake-derived 1-RTT keys, keyed by
//! connection ID) lives HOST-SIDE as one opaque serialized `ServerState` blob:
//! each datagram call is `stateLen ‖ prior state ‖ datagram` in and
//! `newStateLen ‖ new state ‖ k ‖ (len ‖ datagram)*k` out. The host stores the
//! returned state verbatim and replays it on the next datagram — so the real
//! 1-RTT keys derived during the handshake persist across datagrams. The host
//! never interprets the state bytes; its only contract is to carry them forward.
//! A datagram the core drops (a forged/corrupt packet that fails AEAD auth)
//! yields `k = 0` and the host sends nothing.
//!
//! It runs on its own thread and funnels every datagram through the SAME serve
//! gateway the TCP paths use, so the single Lean runtime owner serializes the
//! proven computation across all protocols (one process, one runtime). The state
//! blob is owned by this single-threaded loop, so no lock is needed.

use std::net::UdpSocket;
use std::sync::atomic::Ordering;
use std::sync::mpsc::channel;

use crate::serve::{Seam, ServeGateway};

/// Bind `addr` as UDP and serve QUIC Initial datagrams through the proven core
/// until shutdown. Blocking recv with a short timeout so the SIGINT flag is
/// observed promptly.
pub fn run(addr: &str, gw: ServeGateway) {
    let sock = match UdpSocket::bind(addr) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("dataplane: UDP bind {addr} failed: {e}");
            return;
        }
    };
    let local = sock
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| addr.to_string());
    let _ = sock.set_read_timeout(Some(std::time::Duration::from_millis(200)));
    eprintln!(
        "dataplane: listening on {local}/udp (QUIC Initial decrypt → proven H3 dispatch, over the leanc-compiled proven serve)"
    );

    // One reusable reply channel for this loop's blocking calls into the serve
    // thread; the loop is single-threaded, so one channel suffices.
    let (reply_tx, reply_rx) = channel();
    let mut buf = [0u8; 65536];

    // The host-owned QUIC connection state: one opaque serialized `ServerState`
    // the proven core returns and we replay on the next datagram. Empty = the
    // core's `ServerState.empty` sentinel (the first datagram). The proven core
    // is the only thing that ever interprets these bytes.
    let mut state: Vec<u8> = Vec::new();

    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return;
        }
        let (n, peer) = match sock.recv_from(&mut buf) {
            Ok(x) => x,
            Err(e)
                if e.kind() == std::io::ErrorKind::WouldBlock
                    || e.kind() == std::io::ErrorKind::TimedOut =>
            {
                continue;
            }
            Err(_) => continue,
        };

        // Frame the call: stateLen(4 BE) ‖ prior state ‖ datagram.
        let mut req = gw.pool().take();
        req.extend_from_slice(&(state.len() as u32).to_be_bytes());
        req.extend_from_slice(&state);
        req.extend_from_slice(&buf[..n]);
        let resp = match gw.call_seam(req, Seam::Datagram, &reply_tx, &reply_rx) {
            Some(r) => r,
            None => return, // serve thread gone (shutdown)
        };

        // Parse: newStateLen(4 BE) ‖ new state ‖ k(2 BE) ‖ (dgLen(4 BE) ‖ dg)*k.
        // A malformed/short response (never expected from the proven core) is a
        // hard drop: leave state untouched, send nothing.
        let (new_state, dgrams) = match parse_seam_response(&resp) {
            Some(x) => x,
            None => {
                eprintln!("dataplane: UDP {n}B from {peer} — malformed seam response, dropped");
                continue;
            }
        };
        state.clear();
        state.extend_from_slice(new_state);

        if dgrams.is_empty() {
            eprintln!(
                "dataplane: UDP {n}B from {peer} — no reply (drop/ack-only), state {}B",
                state.len()
            );
        } else {
            let mut sent = 0usize;
            for dg in &dgrams {
                let _ = sock.send_to(dg, peer);
                sent += dg.len();
            }
            eprintln!(
                "dataplane: UDP {n}B from {peer} — served, sent {} datagram(s) / {sent}B, state {}B",
                dgrams.len(),
                state.len()
            );
        }
    }
}

/// Split the framed seam response into `(new_state, output_datagrams)`.
/// Layout: `newStateLen(4 BE) ‖ new state ‖ k(2 BE) ‖ (dgLen(4 BE) ‖ dg)*k`.
/// Returns `None` on any length that runs past the buffer.
fn parse_seam_response(resp: &[u8]) -> Option<(&[u8], Vec<&[u8]>)> {
    let mut off = 0usize;
    let take = |off: &mut usize, len: usize| -> Option<()> {
        if *off + len > resp.len() {
            None
        } else {
            *off += len;
            Some(())
        }
    };
    // state
    if resp.len() < 4 {
        return None;
    }
    let state_len = u32::from_be_bytes([resp[0], resp[1], resp[2], resp[3]]) as usize;
    off = 4;
    let state_start = off;
    take(&mut off, state_len)?;
    let new_state = &resp[state_start..off];
    // count
    if off + 2 > resp.len() {
        return None;
    }
    let k = u16::from_be_bytes([resp[off], resp[off + 1]]) as usize;
    off += 2;
    let mut dgrams = Vec::with_capacity(k);
    for _ in 0..k {
        if off + 4 > resp.len() {
            return None;
        }
        let dl =
            u32::from_be_bytes([resp[off], resp[off + 1], resp[off + 2], resp[off + 3]]) as usize;
        off += 4;
        let ds = off;
        take(&mut off, dl)?;
        dgrams.push(&resp[ds..off]);
    }
    Some((new_state, dgrams))
}
