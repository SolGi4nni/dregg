//! The HTTP CONNECT tunnel lane wired into the running dataplane.
//!
//! `CONNECT host:port` asks the edge to open a bidirectional TCP tunnel and
//! thereafter blindly relay bytes both ways (RFC 9110 §9.3.6). The sans-IO split
//! is the same as every other reactor decision:
//!
//! * the CORE decides WHETHER to tunnel — the proven default-deny admission gate
//!   `Reactor.Proxy.Connect.decide` (deny-first, allow-must-match, default-deny),
//!   exported as `drorb_connect_gate` and crossed on the runtime-owner serve
//!   thread through [`Seam::ConnectGate`]. A target absent from the allow list is
//!   refused `403`; the host never makes the admission decision itself.
//! * the HOST owns the sockets — it dials the admitted target and runs the blind
//!   bidirectional pump ([`pump`], `std::io::copy` each way, half-close on EOF),
//!   the same streaming discipline as the reverse-proxy passthrough.
//!
//! The allow list is configured out of band via `DRORB_CONNECT_ALLOW`
//! (comma-separated `host:port` patterns, `*` = wildcard axis, e.g. `*:443`).
//! Unset ⇒ empty allow list ⇒ default-deny refuses every CONNECT.

use std::io::Write;
use std::net::{TcpStream, ToSocketAddrs};
use std::sync::mpsc::{Receiver, Sender};
use std::time::Duration;

use crate::pool::PooledBuf;
use crate::serve::{Seam, ServeGateway};

/// How long to wait for the upstream TCP connect on an admitted target.
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);

/// RFC 9110 success line for an established tunnel (bare status, no body).
const H1_200_ESTABLISHED: &[u8] = b"HTTP/1.1 200 Connection Established\r\n\r\n";
/// Refusal for a target the ACL denies (or an unconfigured edge: default-deny).
const H1_403_FORBIDDEN: &[u8] =
    b"HTTP/1.1 403 Forbidden\r\nContent-Length: 9\r\nConnection: close\r\n\r\nForbidden";
/// A malformed CONNECT request-line target.
const H1_400_BAD_REQUEST: &[u8] =
    b"HTTP/1.1 400 Bad Request\r\nContent-Length: 11\r\nConnection: close\r\n\r\nBad Request";
/// The admitted target could not be dialled.
const H1_502_BAD_GATEWAY: &[u8] =
    b"HTTP/1.1 502 Bad Gateway\r\nContent-Length: 11\r\nConnection: close\r\n\r\nBad Gateway";

/// Is this request an HTTP CONNECT?
pub fn is_connect(req: &[u8]) -> bool {
    req.starts_with(b"CONNECT ")
}

/// Parse the `host:port` target from the CONNECT request line.
fn parse_target(req: &[u8]) -> Option<String> {
    let line_end = req
        .windows(2)
        .position(|w| w == b"\r\n")
        .unwrap_or(req.len());
    let line = &req[..line_end];
    let mut parts = line.split(|&b| b == b' ');
    let _method = parts.next()?; // "CONNECT"
    let target = parts.next()?;
    let t = std::str::from_utf8(target).ok()?.trim();
    if t.is_empty() {
        None
    } else {
        Some(t.to_string())
    }
}

/// The configured allow-list patterns from `DRORB_CONNECT_ALLOW`. Empty when
/// unset — which the proven gate treats as default-deny (refuse everything).
fn allow_list() -> Vec<String> {
    std::env::var("DRORB_CONNECT_ALLOW")
        .ok()
        .map(|s| {
            s.split(',')
                .map(|p| p.trim().to_string())
                .filter(|p| !p.is_empty())
                .collect()
        })
        .unwrap_or_default()
}

/// Cross the proven `drorb_connect_gate` seam: marshal `target\nallow\n…` and
/// read the single verdict byte (`1` ⇒ admit). The DECISION is the proven core's;
/// the host contributes only the parsed target and the configured allow list.
fn gate_admits(
    target: &str,
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> bool {
    let mut input = gw.pool().take();
    input.clear();
    input.extend_from_slice(target.as_bytes());
    for p in allow_list() {
        input.push(b'\n');
        input.extend_from_slice(p.as_bytes());
    }
    match gw.call_seam(input, Seam::ConnectGate, reply_tx, reply_rx) {
        Some(out) => out.first() == Some(&1u8),
        None => false,
    }
}

/// The blind bidirectional byte pump: relay `client` ⇄ `upstream` until either
/// side closes, half-closing the peer's write side on each EOF. This is the
/// "blind forwarding of data, in both directions" the CONNECT tunnel promises.
fn pump(client: TcpStream, upstream: TcpStream) {
    let mut client_rx = match client.try_clone() {
        Ok(s) => s,
        Err(_) => return,
    };
    let mut client_tx = client;
    let mut up_rx = match upstream.try_clone() {
        Ok(s) => s,
        Err(_) => return,
    };
    let mut up_tx = upstream;

    // upstream -> client on a helper thread.
    let up_to_client = std::thread::spawn(move || {
        let _ = std::io::copy(&mut up_rx, &mut client_tx);
        let _ = client_tx.shutdown(std::net::Shutdown::Write);
    });
    // client -> upstream on this thread.
    let _ = std::io::copy(&mut client_rx, &mut up_tx);
    let _ = up_tx.shutdown(std::net::Shutdown::Write);
    let _ = up_to_client.join();
}

/// Handle one CONNECT request end to end: run the proven admission gate, and on
/// admit dial the target and pump; otherwise write the canned refusal. The
/// connection is consumed either way (tunnel closes it, or the error is terminal).
pub fn handle_connect(
    req: &[u8],
    client: TcpStream,
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) {
    let mut client = client;
    let target = match parse_target(req) {
        Some(t) => t,
        None => {
            let _ = client.write_all(H1_400_BAD_REQUEST);
            return;
        }
    };

    // The proven default-deny gate decides.
    if !gate_admits(&target, gw, reply_tx, reply_rx) {
        let _ = client.write_all(H1_403_FORBIDDEN);
        return;
    }

    // Admitted: resolve and dial the upstream.
    let addr = match target.to_socket_addrs().ok().and_then(|mut it| it.next()) {
        Some(a) => a,
        None => {
            let _ = client.write_all(H1_502_BAD_GATEWAY);
            return;
        }
    };
    let upstream = match TcpStream::connect_timeout(&addr, CONNECT_TIMEOUT) {
        Ok(s) => s,
        Err(_) => {
            let _ = client.write_all(H1_502_BAD_GATEWAY);
            return;
        }
    };
    upstream.set_nodelay(true).ok();

    // Switch to tunnel mode: 2xx, then blind relay both ways.
    if client.write_all(H1_200_ESTABLISHED).is_err() {
        return;
    }
    client.set_nodelay(true).ok();
    // Clear read timeouts: a tunnel may idle indefinitely between bytes.
    client.set_read_timeout(None).ok();
    upstream.set_read_timeout(None).ok();
    pump(client, upstream);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_connect() {
        assert!(is_connect(b"CONNECT example.com:443 HTTP/1.1\r\n\r\n"));
        assert!(!is_connect(b"GET / HTTP/1.1\r\n\r\n"));
    }

    #[test]
    fn parses_target() {
        assert_eq!(
            parse_target(b"CONNECT api.internal:443 HTTP/1.1\r\nHost: x\r\n\r\n"),
            Some("api.internal:443".to_string())
        );
        assert_eq!(parse_target(b"CONNECT  HTTP/1.1\r\n\r\n"), None);
    }
}
