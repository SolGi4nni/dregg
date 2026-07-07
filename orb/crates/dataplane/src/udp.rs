//! The UDP/QUIC IO path: recv a datagram, drive the proven `Seam::Datagram`
//! (verified EverCrypt QUIC-Initial decrypt → proven H3 dispatch → guarded
//! serve), and send the response datagram back to the sender.
//!
//! Like the TCP paths, this host owns only the socket and the recv/send loop; it
//! never parses, decrypts, or rewrites a datagram. The datagram bytes go into the
//! proven core unchanged, and the served bytes come back out unchanged. A datagram
//! the proven core drops (a forged/corrupt Initial that fails AEAD authentication)
//! yields zero response bytes, and the host sends nothing — the AEAD's authenticity
//! gate, observed by the host as "no reply".
//!
//! It runs on its own thread and funnels every datagram through the SAME serve
//! gateway the TCP paths use, so the single Lean runtime owner serializes the
//! proven computation across all protocols (one process, one runtime).

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
                continue
            }
            Err(_) => continue,
        };

        let mut req = gw.pool().take();
        req.extend_from_slice(&buf[..n]);
        let resp = match gw.call_seam(req, Seam::Datagram, &reply_tx, &reply_rx) {
            Some(r) => r,
            None => return, // serve thread gone (shutdown)
        };
        if resp.is_empty() {
            eprintln!(
                "dataplane: UDP {n}B from {peer} — dropped (parse/AEAD-auth failure, no reply)"
            );
        } else {
            let _ = sock.send_to(&resp, peer);
            eprintln!(
                "dataplane: UDP {n}B from {peer} — decrypted + H3-dispatched, sent {}B",
                resp.len()
            );
        }
    }
}
