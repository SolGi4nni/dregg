//! The portable fallback IO path: a thread-per-connection blocking host.
//!
//! Each accepted connection is handled by its own thread (soft-capped), which
//! reads a request off the wire, hands the request bytes to the serve thread
//! over the gateway, waits for the response, and writes it back — all while
//! other connection threads overlap their own reads, writes, and keep-alive idle
//! waits. This is the path used on platforms without io_uring (macOS and
//! others); on Linux the io_uring loop is preferred but this path remains
//! available for comparison.
//!
//! Buffers are pooled: the connection's accumulation buffer, the request buffer
//! handed to the serve thread, and the response buffer handed back all come from
//! and return to the shared [`BufferPool`], so a warm host allocates nothing per
//! request on the Rust side (§ `pool`).

use std::io::{Read, Write};
use std::net::{IpAddr, Ipv4Addr, TcpListener, TcpStream};
use std::sync::atomic::Ordering;
use std::sync::mpsc::channel;
use std::sync::Arc;
use std::time::Duration;

use crate::http::{
    annotate_connection, next_request, request_wants_keepalive, response_is_self_delimited, Frame,
    H2_PREFACE,
};
use crate::pool::PooledBuf;
use crate::serve::{Meter, Seam, ServeGateway};
use crate::ws;

/// How long a kept-alive connection may sit idle between requests before the
/// host reclaims it.
const IDLE_TIMEOUT: Duration = Duration::from_secs(60);

/// Ceiling on concurrent connection threads. Beyond it, new connections are
/// closed immediately (refused) rather than spawning unbounded threads.
const MAX_CONNS: usize = 1024;

/// One socket read into a pooled accumulation buffer. Returns bytes read
/// (0 = clean EOF).
fn fill(data: &mut Vec<u8>, stream: &mut TcpStream) -> std::io::Result<usize> {
    let mut chunk = [0u8; 16384];
    let n = stream.read(&mut chunk)?;
    data.extend_from_slice(&chunk[..n]);
    Ok(n)
}

/// The client address the IP-filter gate should decide on. The connection's real
/// accept peer is the default; when that peer is a trusted proxy (here: loopback,
/// the only peer this host binds for), a well-formed `X-Forwarded-For` in the
/// request head overrides it with the originating client the proxy attributes —
/// the standard edge-attribution pattern (the proven core still decides admit or
/// deny). Only the FIRST address of the forwarded chain (the closest client) is
/// honored, and only when it parses as an IP; anything else falls back to `peer`.
fn client_addr(req: &[u8], peer: IpAddr) -> IpAddr {
    if !peer.is_loopback() {
        return peer; // never trust a forwarded header from an untrusted peer
    }
    // Scan the request head (up to the blank line) for `X-Forwarded-For`.
    let head_end = req
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 2)
        .unwrap_or(req.len());
    for line in req[..head_end].split(|&b| b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let Some(colon) = line.iter().position(|&b| b == b':') else {
            continue;
        };
        let (name, rest) = line.split_at(colon);
        if !name.eq_ignore_ascii_case(b"x-forwarded-for") {
            continue;
        }
        let value = &rest[1..]; // drop the ':'
        let first = value.split(|&b| b == b',').next().unwrap_or(value);
        let trimmed: &[u8] = {
            let s = first
                .iter()
                .position(|b| !b.is_ascii_whitespace())
                .unwrap_or(first.len());
            let e = first
                .iter()
                .rposition(|b| !b.is_ascii_whitespace())
                .map(|p| p + 1)
                .unwrap_or(s);
            &first[s..e]
        };
        if let Ok(text) = std::str::from_utf8(trimmed) {
            if let Ok(ip) = text.parse::<IpAddr>() {
                return ip;
            }
        }
        break; // first X-Forwarded-For header seen; do not scan further
    }
    peer
}

/// Handle one accepted connection: the keep-alive loop. Reads a request, routes
/// it through the proven core, writes the response, and loops on the same socket
/// until the client asks to close, the response cannot be kept alive, EOF, an
/// idle timeout, or an error.
fn handle_conn(mut stream: TcpStream, gw: &ServeGateway) {
    use std::io::ErrorKind;

    // The accept peer for this connection — the default client address the
    // IP-filter gate decides on. Unresolvable peers fall back to an unspecified
    // address, which the default-admit ruleset passes.
    let peer_ip = stream
        .peer_addr()
        .map(|a| a.ip())
        .unwrap_or(IpAddr::V4(Ipv4Addr::UNSPECIFIED));

    // Per-connection request index, threaded as the rate bucket's standing
    // depletion: request 0 sees a full bucket, request `cap` and later find it
    // empty (a burst on ONE kept-alive connection is what trips the limiter).
    let mut conn_seq: u64 = 0;

    // Sockets accepted from a non-blocking listener inherit non-blocking mode on
    // BSD/macOS; force this connection back to blocking so the idle read below
    // blocks (up to the read timeout) instead of returning WouldBlock at once.
    let _ = stream.set_nonblocking(false);
    let _ = stream.set_nodelay(true);
    let _ = stream.set_read_timeout(Some(IDLE_TIMEOUT));

    // Pooled accumulation buffer, reused across every request on this
    // connection; a per-connection reply channel, reused across keep-alive
    // requests so no channel is allocated per request.
    let mut acc: PooledBuf = gw.pool().take();
    let (reply_tx, reply_rx) = channel::<PooledBuf>();

    'conn: loop {
        // Peek at the connection opener: an h2c preface is not HTTP/1.1-framed.
        if acc.is_empty() {
            match fill(&mut acc, &mut stream) {
                Ok(0) => return,
                Ok(_) => {}
                Err(e)
                    if e.kind() == ErrorKind::WouldBlock || e.kind() == ErrorKind::TimedOut =>
                {
                    return
                }
                Err(_) => return,
            }
            if acc.len() >= H2_PREFACE.len() && acc.starts_with(H2_PREFACE) {
                // h2c prior-knowledge (RFC 9113 §3.3/§3.4): the client writes its
                // connection preface, SETTINGS, and the request HEADERS as one
                // opening burst and then WAITS for the server to answer — it sends
                // nothing more until it gets the server SETTINGS + response frames.
                // So the host must collect the burst up to the request HEADERS
                // frame and then serve; a plain blocking read past that point
                // deadlocks (the client waits on us, we wait on it) and the client
                // times out. Read with a short grace timeout, stopping as soon as
                // the HEADERS frame is buffered, then hand the whole burst to the
                // proven H2 serve once and reply.
                let _ = stream.set_read_timeout(Some(Duration::from_millis(200)));
                while !crate::http::h2c_burst_complete(&acc) {
                    match fill(&mut acc, &mut stream) {
                        Ok(0) => break, // peer closed
                        Ok(_) => {}     // more of the burst arrived; rescan
                        Err(e)
                            if e.kind() == ErrorKind::WouldBlock
                                || e.kind() == ErrorKind::TimedOut =>
                        {
                            break // grace elapsed: serve whatever we have
                        }
                        Err(_) => return,
                    }
                }
                let mut req = gw.pool().take();
                req.extend_from_slice(&acc);
                if let Some(resp) = gw.call(req, &reply_tx, &reply_rx) {
                    let _ = stream.write_all(&resp);
                }
                return;
            }
        }

        // Read exactly one complete request into `acc`.
        let total = loop {
            match next_request(&acc) {
                Frame::Complete(n) => break n,
                Frame::Oversize => return,
                Frame::NeedMore => match fill(&mut acc, &mut stream) {
                    Ok(0) => {
                        // Clean close only on a request boundary (empty buffer).
                        return;
                    }
                    Ok(_) => {}
                    Err(_) => return, // I/O error or idle timeout
                },
            }
        };

        // Move the request bytes into a pooled buffer, then drop them from the
        // accumulation buffer, retaining any pipelined bytes for the next round.
        let mut req = gw.pool().take();
        req.extend_from_slice(&acc[..total]);
        acc.drain(..total);

        // Access-log capture (opt-in, `DRORB_ACCESS_LOG`): grab the request line
        // and effective client BEFORE the request buffer is consumed by the serve
        // call, and start the request timer. Cheap and skipped entirely when the
        // log is off. `emit` writes one line at whichever response path serves it.
        let req_start = std::time::Instant::now();
        let logrec = if crate::access_log::enabled() {
            Some((
                crate::access_log::ReqLine::parse(&req),
                client_addr(&req, peer_ip),
            ))
        } else {
            None
        };
        let emit = |resp: &[u8], backend: Option<&str>| {
            // Untrusted-shell observability from the serve loop: bump the metric
            // counters (total / status-class / bytes / per-backend) for every
            // served response, then the opt-in access log. Neither touches the
            // proven core's decision.
            crate::metrics::record(resp, backend);
            if let Some((rl, client)) = &logrec {
                crate::access_log::log(*client, rl, resp, backend, req_start);
            }
        };

        // WebSocket lane (RFC 6455): if this request is an Upgrade, complete the
        // handshake here (the host owns the accept token — see `ws`) and keep the
        // connection OPEN, running every subsequent frame through the proven
        // `Seam::WsFrame`. This is the TCP analogue of the proven Ingress fork.
        if ws::is_ws_upgrade(&req) {
            // AUTH GATE: the RFC 6455 handshake must not bypass authentication. Run
            // the upgrade REQUEST through the deployed `/admin` JWT gate (the same
            // gate the request path's fold runs) BEFORE returning 101. If the
            // upgrade targets a protected path with no/invalid credentials the gate
            // returns a 401; write that refusal and close instead of upgrading. An
            // authorized upgrade returns no gate bytes and proceeds to the 101.
            let mut gate_req = gw.pool().take();
            gate_req.extend_from_slice(&req);
            match gw.call_seam(gate_req, Seam::UpgradeGate, &reply_tx, &reply_rx) {
                Some(refusal) if !refusal.is_empty() => {
                    let _ = stream.write_all(&refusal);
                    return;
                }
                Some(_) => {} // authorized: no refusal bytes — complete the handshake
                None => return, // serve thread gone (shutdown)
            }
            if let Some(resp) = ws::upgrade_response(&req) {
                if stream.write_all(&resp).is_err() {
                    return;
                }
                eprintln!("dataplane: WS upgrade OK — connection open, proven frame loop");
                ws_frame_loop(&mut stream, gw, &reply_tx, &reply_rx, &mut acc);
            }
            return;
        }

        let keepalive_req = request_wants_keepalive(&req);

        // Effect/continuation seam (`DRORB_EFFECT_SEAM=1`): the PROVEN core drives
        // the whole fabric decision — whether to proxy (which backend), whether to
        // cache (which key, what lifetime, gate-admitted HIT), and what to do with
        // an upstream reply — and the interpreter loop only executes the yielded
        // effects. `should_handle` is a conservative host prefilter (the seam is
        // consulted for the proxy route and the cacheable-route shape); the core
        // still makes the real decision. A `None` return means the request is not
        // one the seam acts on, so it falls through to the metered serve below
        // (which carries the real IP-filter / rate gates).
        if crate::interp::enabled() && crate::interp::should_handle(&req) {
            if let Some(mut resp) = crate::interp::run_effect_serve(&req, gw, &reply_tx, &reply_rx) {
                let keepalive = keepalive_req && response_is_self_delimited(&resp);
                annotate_connection(&mut resp, keepalive);
                emit(&resp, None);
                if stream.write_all(&resp).is_err() {
                    return;
                }
                if !keepalive {
                    return;
                }
                continue 'conn;
            }
        }

        // Reverse-proxy lane (established hook, effect seam OFF): a request under a
        // proxy route (/api) with a configured backend fleet is forwarded to a LIVE
        // upstream via `drorb_proxy_pick`. Returns None when no fleet is configured,
        // so /api falls through to the normal serve unchanged.
        if !crate::interp::enabled() && crate::proxy_hook::is_proxy_path(&req) {
            if let Some((mut resp, backend)) =
                crate::proxy_hook::handle_proxy(&req, gw, &reply_tx, &reply_rx)
            {
                let keepalive = keepalive_req && response_is_self_delimited(&resp);
                annotate_connection(&mut resp, keepalive);
                emit(&resp, backend.as_deref());
                if stream.write_all(&resp).is_err() {
                    return;
                }
                if !keepalive {
                    return;
                }
                continue 'conn;
            }
        }

        // Per-host reverse-proxy: an operator config virtual host `route … proxy
        // <pool>` forwards requests whose `Host` names a declared proxy vhost to the
        // live backend fleet — the same `handle_proxy` path as `/api`, but gated on the
        // request authority instead of a fixed path. The proven `drorb_proxy_pick` still
        // chooses the backend; the `hostGlob` served path answers a proxy block route
        // with a placeholder, so the real forward is decided here, host-side. Fires
        // independent of the effect seam (a config vhost may proxy any path under a host).
        if let Some(dep) = crate::config::get() {
            if dep.is_vhost_proxy(&req) {
                if let Some((mut resp, backend)) =
                    crate::proxy_hook::handle_proxy(&req, gw, &reply_tx, &reply_rx)
                {
                    let keepalive = keepalive_req && response_is_self_delimited(&resp);
                    annotate_connection(&mut resp, keepalive);
                    emit(&resp, backend.as_deref());
                    if stream.write_all(&resp).is_err() {
                        return;
                    }
                    if !keepalive {
                        return;
                    }
                    continue 'conn;
                }
            }
        }

        // Config route-table serve: when the operator config (DRORB_CONFIG) declares
        // its own route table, non-proxy requests are served through `drorb_serve_cfg`
        // — the SAME proven fourteen-stage fold, but over the config's declared routes
        // (redirect/respond/static answered directly). Proxy `/api` requests were
        // already handled above (effect seam / proxy hook), so they never reach here.
        // With no DRORB_CONFIG (or a routeless one) this is skipped and the default
        // metered serve runs unchanged — so the default conformance is untouched.
        if let Some(dep) = crate::config::get() {
            if dep.has_routes() {
                if let Some(mut resp) = gw.call_cfg(&dep.config_text, &req, &reply_tx, &reply_rx) {
                    let keepalive = keepalive_req && response_is_self_delimited(&resp);
                    annotate_connection(&mut resp, keepalive);
                    emit(&resp, None);
                    if stream.write_all(&resp).is_err() {
                        return;
                    }
                    if !keepalive {
                        return;
                    }
                    continue 'conn;
                }
            }
        }

        // Cross the METERED seam: the proven IP-filter gate decides on this
        // connection's client address (accept peer, or the forwarded client when
        // the peer is a trusted proxy) and the rate gate on the per-connection
        // request index. `conn_seq` advances once per served request, so a burst
        // on one kept-alive connection depletes the bucket.
        let meter = Meter {
            client: client_addr(&req, peer_ip),
            seq: conn_seq,
        };
        conn_seq = conn_seq.saturating_add(1);
        let mut resp = match gw.call_metered(req, meter, &reply_tx, &reply_rx) {
            Some(r) => r,
            None => return, // serve thread gone (shutdown)
        };

        let keepalive = keepalive_req && response_is_self_delimited(&resp);
        annotate_connection(&mut resp, keepalive);
        emit(&resp, None);
        if stream.write_all(&resp).is_err() {
            return;
        }
        if !keepalive {
            return;
        }
        continue 'conn; // serve the next request (pipelined bytes already buffered)
    }
}

/// The open-connection WebSocket frame loop. After the 101 handshake, every
/// inbound chunk of frame bytes is handed to the proven `Seam::WsFrame`
/// (`drorb_serve_ws_frame`: decode + unmask + reassemble + re-encode) and the
/// proven response bytes are written straight back — a proven-path echo over one
/// kept-open TCP connection. Any bytes the client pipelined right after the
/// upgrade (already in `acc`) are fed first. Returns when the peer closes or on
/// error.
///
/// Each chunk is fed to a fresh WebSocket codec (the proven `drorbServeWsFrame`
/// starts from `{}` per call), so a frame must arrive whole in one recv — true
/// for the small client frames this demo drives over loopback, and the same
/// scheduling choice the C shell (`ffi/mac_io.c`) makes. Cross-recv partial-frame
/// buffering would carry the codec across calls; it is a host scheduling change,
/// not a change to the proven decoder.
fn ws_frame_loop(
    stream: &mut TcpStream,
    gw: &ServeGateway,
    reply_tx: &std::sync::mpsc::Sender<PooledBuf>,
    reply_rx: &std::sync::mpsc::Receiver<PooledBuf>,
    acc: &mut PooledBuf,
) {
    // Frames may sit idle on an open WebSocket; block indefinitely between them.
    let _ = stream.set_read_timeout(None);

    // Feed any bytes pipelined right after the upgrade request.
    if !acc.is_empty() {
        let mut req = gw.pool().take();
        req.extend_from_slice(acc);
        acc.clear();
        match gw.call_seam(req, Seam::WsFrame, reply_tx, reply_rx) {
            Some(out) if !out.is_empty() => {
                if stream.write_all(&out).is_err() {
                    return;
                }
            }
            Some(_) => {}
            None => return,
        }
    }

    let mut chunk = [0u8; 65536];
    loop {
        let n = match stream.read(&mut chunk) {
            Ok(0) => return, // peer closed
            Ok(n) => n,
            Err(_) => return,
        };
        let mut req = gw.pool().take();
        req.extend_from_slice(&chunk[..n]);
        match gw.call_seam(req, Seam::WsFrame, reply_tx, reply_rx) {
            Some(out) if !out.is_empty() => {
                if stream.write_all(&out).is_err() {
                    return;
                }
            }
            Some(_) => {} // control/incomplete frame produced no echo bytes
            None => return, // serve thread gone
        }
    }
}

/// Run the blocking accept loop on `listener` until shutdown, driving every
/// request through `gw`.
pub fn run(listener: TcpListener, gw: ServeGateway) {
    // Non-blocking accept so the SIGINT flag is observed promptly.
    listener
        .set_nonblocking(true)
        .expect("failed to set the listener non-blocking");

    let gw = Arc::new(gw);
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping accept loop");
            break;
        }
        match listener.accept() {
            Ok((stream, _peer)) => {
                if crate::ACTIVE_CONNS.load(Ordering::SeqCst) >= MAX_CONNS {
                    drop(stream); // at the soft cap: refuse by closing immediately
                    continue;
                }
                crate::ACTIVE_CONNS.fetch_add(1, Ordering::SeqCst);
                let gw = Arc::clone(&gw);
                let _ = std::thread::Builder::new()
                    .name("drorb-conn".into())
                    .spawn(move || {
                        handle_conn(stream, &gw);
                        crate::ACTIVE_CONNS.fetch_sub(1, Ordering::SeqCst);
                    });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(_) => {
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
}
