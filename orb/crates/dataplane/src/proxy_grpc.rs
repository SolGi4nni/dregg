//! gRPC / gRPC-Web proxy host seam — PREPARED, NOT WIRED. Nothing calls it.
//!
//! ⚠ This file said "wired into the running dataplane" until 2026-07-28, and it was
//! not true on the day it was written. `is_grpc`, `is_grpc_web` and `frame_len` have
//! ZERO callers outside this module's own `#[cfg(test)]` block — measured repo-wide —
//! which is why `main.rs` declares the module under `#[allow(dead_code)]`. Nothing in
//! this repo could report it: the ten `orb/crates/*` packages were in neither the root
//! workspace's `members` nor its `exclude` for the whole 2026-07 window, so no build
//! ever compiled this subtree and no lint ever ran over it.
//!
//! `Seam::GrpcFrameLen` is constructed HERE and nowhere else, so the dispatch arm at
//! `serve.rs`'s `Seam::GrpcFrameLen => drorb_grpc_frame_len` can never fire, and the
//! proven Lean export `drorb_grpc_frame_len` (`Reactor/Proxy/Grpc.lean:270`) is an
//! IDLE CARRIER: in the archive, in the serve closure, crossed by nothing.
//!
//! KEPT, not deleted, and this is the true reason: orb's own reachability ratchet
//! already counts it — `scripts/reachability-audit.sh` files `drorb_grpc_frame_len`
//! in the ORPHANED bucket with `reason: "dead-dispatch"`, one of the 20 orphans its
//! baseline pins, and that baseline's stated policy is that WIRING a seam lowers the
//! number. Deleting this host half would leave the same proven export orphaned with no
//! prepared crossing at all — the identical orphan count and strictly less to wire. So
//! this is the unwired half of a seam whose Lean half is proven, and it says so.
//!
//! gRPC is HTTP/2 with a length-prefixed message framing inside the DATA payload
//! and a `grpc-status` trailer. The byte transport is the existing streaming
//! passthrough (the h2 engine owns the stream and DATA frames; the reverse-proxy
//! forward moves the bytes); the gRPC-specific *decisions* are the proven core in
//! `Reactor.Proxy.Grpc`:
//!
//! * message framing (`decodeFrame` / `encodeFrame`, faithful roundtrip) — [`frame_len`]
//!   (the `drorb_grpc_frame_len` seam) is the crossing a host WOULD consult to find a
//!   message boundary and enforce the max-message-size limit while streaming. No host
//!   consults it today;
//! * `grpc-status` codes and the HTTP→gRPC status map;
//! * gRPC-Web framing translation (data frames identical, trailers as a `0x80`
//!   trailer frame) — proven faithful; the byte transcode reuses the passthrough.
//!
//! This module is the host seam: content-type detection so the host would know a
//! request is gRPC, and the frame-length crossing. It never re-implements the
//! framing decision — that is the proven `drorb_grpc_frame_len`. What is missing to
//! make the claim in the first line true is a call from the h2 / reverse-proxy path
//! (`h2.rs`, `proxy_dial.rs`), and until one exists this file describes an intention.

use std::sync::mpsc::{Receiver, Sender};

use crate::serve::{Seam, ServeGateway};

/// gRPC content-type prefix. `application/grpc`, `application/grpc+proto`,
/// `application/grpc;charset=…` are gRPC; `application/grpc-web[-text]` are not
/// (the char after `grpc` is `-`, not end / `+` / `;`).
fn ct_is_grpc(ct: &[u8]) -> bool {
    let p = b"application/grpc";
    if !ct.starts_with(p) {
        return false;
    }
    match ct.get(p.len()) {
        None => true,
        Some(&b'+') | Some(&b';') => true,
        _ => false,
    }
}

/// gRPC-Web (binary or text) content-type.
fn ct_is_grpc_web(ct: &[u8]) -> bool {
    let p = b"application/grpc-web";
    if !ct.starts_with(p) {
        return false;
    }
    // grpc-web, grpc-web-text, grpc-web+proto, grpc-web-text+proto, …
    true
}

/// Find the `content-type` header value (case-insensitive) in a request head.
fn content_type(req: &[u8]) -> Option<&[u8]> {
    let head_end = req
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(req.len());
    let head = &req[..head_end];
    for line in head.split(|&b| b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if let Some(colon) = line.iter().position(|&b| b == b':') {
            let (name, val) = line.split_at(colon);
            if name.eq_ignore_ascii_case(b"content-type") {
                let v = &val[1..];
                let start = v.iter().position(|&b| b != b' ').unwrap_or(v.len());
                return Some(&v[start..]);
            }
        }
    }
    None
}

/// Whether the request is a gRPC RPC (plain gRPC content-type).
pub fn is_grpc(req: &[u8]) -> bool {
    content_type(req).map(ct_is_grpc).unwrap_or(false)
}

/// Whether the request is a gRPC-Web RPC (needs translation to gRPC upstream).
pub fn is_grpc_web(req: &[u8]) -> bool {
    content_type(req).map(ct_is_grpc_web).unwrap_or(false)
}

/// Cross the proven `drorb_grpc_frame_len` seam: parse a gRPC frame header and
/// return the declared payload length, so the host can find the message boundary
/// / enforce max-message-size while streaming the DATA through the passthrough.
/// `None` when fewer than 5 header bytes are present.
pub fn frame_len(
    header: &[u8],
    gw: &ServeGateway,
    reply_tx: &Sender<crate::pool::PooledBuf>,
    reply_rx: &Receiver<crate::pool::PooledBuf>,
) -> Option<usize> {
    let mut input = gw.pool().take();
    input.clear();
    input.extend_from_slice(header);
    let out = gw.call_seam(input, Seam::GrpcFrameLen, reply_tx, reply_rx)?;
    if out.is_empty() {
        return None;
    }
    std::str::from_utf8(&out).ok()?.trim().parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_grpc() {
        assert!(is_grpc(
            b"POST /p HTTP/1.1\r\ncontent-type: application/grpc\r\n\r\n"
        ));
        assert!(is_grpc(
            b"POST /p HTTP/1.1\r\nContent-Type: application/grpc+proto\r\n\r\n"
        ));
        assert!(!is_grpc(
            b"POST /p HTTP/1.1\r\ncontent-type: application/grpc-web\r\n\r\n"
        ));
        assert!(!is_grpc(
            b"GET / HTTP/1.1\r\ncontent-type: text/plain\r\n\r\n"
        ));
    }

    #[test]
    fn detects_grpc_web() {
        assert!(is_grpc_web(
            b"POST /p HTTP/1.1\r\ncontent-type: application/grpc-web+proto\r\n\r\n"
        ));
        assert!(is_grpc_web(
            b"POST /p HTTP/1.1\r\ncontent-type: application/grpc-web-text\r\n\r\n"
        ));
        assert!(!is_grpc_web(
            b"POST /p HTTP/1.1\r\ncontent-type: application/grpc\r\n\r\n"
        ));
    }
}
