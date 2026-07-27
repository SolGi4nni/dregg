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
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::sync::mpsc::channel;
use std::time::Duration;

use crate::http::{
    Frame, H2_PREFACE, annotate_connection, next_request, request_wants_keepalive,
    response_is_self_delimited,
};
use crate::pool::PooledBuf;
use crate::serve::{Meter, Seam, ServeGateway};
use crate::ws;

/// How long a kept-alive connection may sit idle between requests before the
/// host reclaims it.
const IDLE_TIMEOUT: Duration = Duration::from_secs(60);

/// Ceiling on concurrent connection WORKER THREADS. Beyond it, new connections are
/// closed immediately (refused) rather than spawning unbounded threads.
///
/// This is a THREAD bound, not a connection bound, and that is why it is far below
/// the process-wide connection ceiling (`standing::process_conn_cap()`, 32768 at the
/// default descriptor budget): this host is thread-per-connection, and 1024 threads
/// is already ~8 GiB of reserved stack. The shard reactors hold connections in a
/// slab and spawn no thread per connection, so a ceiling that low would be an
/// arbitrary throughput cut there — the two backends bound different resources and
/// deliberately bound them differently. The accept loop checks BOTH, so
/// `DRORB_MAX_CONNS` is honored here too and is never silently ignored.
const MAX_CONNS: usize = 1024;

/// The process-global per-source connection counter for this reactor. Shared
/// (striped, not a single global mutex) because the blocking host is
/// thread-per-connection: the accept loop increments, each worker thread
/// decrements when it returns. Enforces the config's `max-connections` cap
/// per source (the proven `Reactor.Stage.ConnLimit` decision).
/// THE ONE process-wide table, shared with the io_uring / kqueue reactors — this
/// host no longer owns a private instance. (It was for a long time the only backend
/// that enforced the cap process-wide at all; the shard reactors have been moved
/// onto the same table. See conformance/dos/FINDING-per-shard-standing.md.)
fn source_table() -> &'static crate::standing::SharedStanding {
    crate::standing::source_table()
}

/// The canned `503 Service Unavailable` a source at/over its `max-connections` cap
/// receives — the wire form of the proven `Reactor.Stage.ConnLimit.resp503`.
const CONN_LIMIT_503: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Type: text/plain\r\nContent-Length: 36\r\nConnection: close\r\n\r\nper-source connection limit reached\n";

/// The canned `429 Too Many Requests` a source over its `rate-limit` window receives
/// — the wire form of the proven `Reactor.Stage.StickTable.resp429`.
const RATE_LIMIT_429: &[u8] =
    b"HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain\r\nContent-Length: 20\r\nConnection: close\r\n\r\nrate limit exceeded\n";

/// The canned `408 Request Timeout` a connection whose header phase overran
/// `slowloris-timeout` receives — the wire form of the proven
/// `Reactor.Stage.Slowloris.resp408`.
const SLOWLORIS_408: &[u8] =
    b"HTTP/1.1 408 Request Timeout\r\nContent-Type: text/plain\r\nContent-Length: 23\r\nConnection: close\r\n\r\nrequest header timeout\n";

/// Whether the RESPONSE itself asks the host to close the connection: its head
/// carries a `Connection` header naming the `close` token (RFC 9112 §9.6). The
/// request's own keep-alive intent (`request_wants_keepalive`) and the response
/// framing (`response_is_self_delimited`) are the other two inputs to the
/// disposition; this is the third, so a response that states `Connection: close`
/// — a canned error, a forwarded upstream reply, a config `respond`/braid stage
/// — is honored by closing rather than held open until the idle timeout.
///
/// Scans only the head (up to the blank line) and matches `close` as a
/// comma-separated, OWS-trimmed token so `Connection: keep-alive` does not
/// false-match on a substring. Self-contained: it reads bytes only, mirroring
/// the request-side scan, and never rewrites the response.
fn response_wants_close(resp: &[u8]) -> bool {
    let head_end = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 2)
        .unwrap_or(resp.len());
    for line in resp[..head_end].split(|&b| b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let Some(colon) = line.iter().position(|&b| b == b':') else {
            continue;
        };
        let (name, rest) = line.split_at(colon);
        if !name.eq_ignore_ascii_case(b"connection") {
            continue;
        }
        // Each comma-separated token, OWS-trimmed, matched case-insensitively.
        for tok in rest[1..].split(|&b| b == b',') {
            let s = tok
                .iter()
                .position(|b| !b.is_ascii_whitespace())
                .unwrap_or(tok.len());
            let e = tok
                .iter()
                .rposition(|b| !b.is_ascii_whitespace())
                .map(|p| p + 1)
                .unwrap_or(s);
            if tok[s..e].eq_ignore_ascii_case(b"close") {
                return true;
            }
        }
    }
    false
}

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
pub(crate) fn client_addr(req: &[u8], peer: IpAddr) -> IpAddr {
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
fn handle_conn(stream: TcpStream, gw: &ServeGateway) {
    handle_conn_prefilled(stream, gw, &[]);
}

/// [`handle_conn`] over a connection whose first bytes have ALREADY been read off
/// the socket: the entry point a completion reactor uses when it hands a live
/// connection over mid-flight (`uring::proxy_handoff` / `kqueue::proxy_handoff`).
/// `prefill` is that reactor's accumulation buffer verbatim - the request it just
/// framed plus anything the client pipelined behind it - seeded into this loop's
/// accumulator, so the request is framed here exactly as if it had arrived on this
/// thread. An empty `prefill` IS `handle_conn`.
///
/// The reactors need it for the reverse-proxy lane: the upstream hop BLOCKS on a
/// second socket, which a shard may never do, so the connection leaves the shard
/// for a thread that may block - the same fork `ws_handoff` / `connect_handoff` /
/// `h2c_handoff` make. There is exactly ONE reverse-proxy implementation in this
/// host (the `proxy_hook` arm below), and every reactor runs that one.
pub(crate) fn handle_conn_prefilled(mut stream: TcpStream, gw: &ServeGateway, prefill: &[u8]) {
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
    // Monotonic connection-open instant. The rate gate's real `Rate.refill` credits
    // `rate * elapsed` tokens, so a connection throttled to `429` recovers as this
    // clock advances. Packed (with the standing count) into the single `seq` scalar
    // the metered serve ABI carries: `seq = (min(elapsed_secs, cap) << 32) |
    // min(conn_seq, cap)`, where `cap` is the operator's `burst-cap`.
    let conn_start = std::time::Instant::now();

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
    // Bytes a handing-over reactor already read off this socket become the head of
    // this loop's accumulator, so the first framing pass sees the request it framed
    // instead of blocking on a read whose bytes are already consumed.
    acc.extend_from_slice(prefill);
    let (reply_tx, reply_rx) = channel::<PooledBuf>();

    'conn: loop {
        // Peek at the connection opener: an h2c preface is not HTTP/1.1-framed.
        if acc.is_empty() {
            match fill(&mut acc, &mut stream) {
                Ok(0) => return,
                Ok(_) => {}
                Err(e) if e.kind() == ErrorKind::WouldBlock || e.kind() == ErrorKind::TimedOut => {
                    return;
                }
                Err(_) => return,
            }
            // An h2c preface may arrive split across reads: while the buffered
            // bytes are still a strict prefix of the preface head, keep reading
            // before deciding which protocol this connection speaks (the same
            // slowloris deadline as the HTTP/1.1 header phase guards the wait —
            // a preface drip past the deadline is dropped).
            let slow_timeout = crate::config::slowloris_timeout();
            let wait_start = std::time::Instant::now();
            while acc.len() < H2_PREFACE.len() && H2_PREFACE.starts_with(&acc) {
                if crate::standing::header_expired(
                    slow_timeout,
                    wait_start,
                    std::time::Instant::now(),
                ) {
                    return;
                }
                match fill(&mut acc, &mut stream) {
                    Ok(0) => return, // peer closed mid-preface
                    Ok(_) => {}
                    Err(_) => return,
                }
            }
            if acc.starts_with(H2_PREFACE) {
                // h2c prior-knowledge (RFC 9113 §3.3/§3.4): hand the connection
                // to the interactive engine host (`h2::host_conn`) — one verified
                // engine state, threaded across socket reads. A one-shot answer
                // cannot carry SETTINGS synchronization, PING liveness, or
                // WINDOW_UPDATE-paced response bodies (everything after the
                // client's first flight), so the connection leaves the HTTP/1.1
                // keep-alive loop here for good; the engine's close flag decides
                // the teardown.
                crate::h2::host_conn(stream, &acc);
                return;
            }
        }

        // SLOWLORIS: the header-phase deadline for the FIRST request on this
        // connection. Captured at the start of reading it; a drip that has not
        // completed a request head within `slowloris-timeout` is dropped with the REAL
        // proven 408 (`slowloris_fires`). Only the first request (`conn_seq == 0`) is
        // guarded — the classic slowloris defense. A fully-silent partial is reaped by
        // the socket read timeout (`IDLE_TIMEOUT`) instead.
        let slow_timeout = crate::config::slowloris_timeout();
        let hdr_start = std::time::Instant::now();
        // Read exactly one complete request into `acc`.
        // RFC 9110 §10.1.1: at most one interim `100 Continue` per request.
        let mut interim_100_sent = false;
        let total = loop {
            // Consult the deadline BEFORE framing, so a slow drip that finally completes
            // its head past the deadline is still refused (mirrors the io_uring shard).
            if conn_seq == 0
                && crate::standing::header_expired(
                    slow_timeout,
                    hdr_start,
                    std::time::Instant::now(),
                )
            {
                let _ = stream.write_all(SLOWLORIS_408);
                let _ = stream.flush();
                crate::metrics::note_request_timeout();
                return;
            }
            // BODY-SIZE gate — refuse an over-cap body with the proven `413`, then CUT
            // the connection (the over-cap body is never drained). Checked on each
            // recv-driven re-entry BEFORE framing, so a declared `Content-Length` over
            // the cap is rejected up front AND a chunked / streamed body whose ACTUAL
            // bytes pass the cap mid-stream is caught the moment it does — closing the
            // `Content-Length`-absent bypass. A `0` cap (directive absent) never fires.
            if crate::http::body_over_limit(&acc, crate::config::max_body_size()) {
                let _ = stream.write_all(crate::http::BODY_413);
                let _ = stream.flush();
                crate::metrics::note_body_limit_refused();
                return;
            }
            match next_request(&acc) {
                Frame::Complete(n) => break n,
                Frame::Oversize => return,
                Frame::NeedMore => {
                    // RFC 9110 §10.1.1: a paused `Expect: 100-continue` request
                    // (complete head, body pending) is answered the interim `100`
                    // once, so the client ships the body it is withholding.
                    if !interim_100_sent && crate::interim::wants_interim_100(&acc) {
                        interim_100_sent = true;
                        let _ = stream.write_all(crate::interim::INTERIM_100);
                        let _ = stream.flush();
                    }
                    match fill(&mut acc, &mut stream) {
                        Ok(0) => {
                            // Clean close only on a request boundary (empty buffer).
                            return;
                        }
                        Ok(_) => {}
                        Err(_) => return, // I/O error or idle timeout
                    }
                }
            }
        };

        // MIXED-PORT OPENER CLASSIFICATION: a FIRST flight whose request line has
        // no `HTTP/` version token is neither protocol's well-formed opener — not
        // an HTTP/1.x request, and not the H2 preface (that forked to the engine
        // at the peek above). Terminate without a reply, the one answer both
        // protocols assign (RFC 9113 §3.4 invalid-preface connection error —
        // an HTTP/1.1 status line is only frame garbage to an H2 client; RFC 9112
        // §2.2/§3 close on a malformed request-line).
        if conn_seq == 0 && crate::http::opener_lacks_http_version(&acc[..total]) {
            return;
        }

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
        let logrec = if crate::access_log::enabled() || crate::otel::enabled() {
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
            crate::metrics::observe_latency(req_start.elapsed());
            if let Some((rl, client)) = &logrec {
                crate::access_log::log(*client, rl, resp, backend, req_start);
                crate::otel::record_span(*client, rl, resp, backend, req_start);
            }
        };
        // The same observability for a STREAMED response, whose body was written
        // straight to the socket and so was never in hand as one buffer: the host
        // records the status off the response head and the exact streamed byte total.
        let emit_streamed = |head: &[u8], bytes: u64, backend: Option<&str>| {
            crate::metrics::record_streamed(head, bytes, backend);
            crate::metrics::observe_latency(req_start.elapsed());
            if let Some((rl, client)) = &logrec {
                crate::access_log::log_streamed(*client, rl, head, bytes, backend, req_start);
                crate::otel::record_span_streamed(*client, rl, head, bytes, backend, req_start);
            }
        };

        // WebSocket lane (RFC 6455): if this request is an Upgrade, complete the
        // handshake here (the host owns the accept token — see `ws`) and keep the
        // connection OPEN, running every subsequent frame through the proven
        // incremental WebSocket seams (`drorb_ws_header` / `drorb_ws_admit` /
        // `drorb_ws_utf8` / `drorb_ws_close_body` / `drorb_ws_encode_*`, crossed
        // from `ws` + `ws_assembly`). This is the TCP analogue of the proven
        // Ingress fork.
        // The body lives in `serve_ws_upgrade` so the io_uring and kqueue reactors
        // run the IDENTICAL gate → 101 → proven-pump sequence off their handoff
        // threads (there is exactly one WebSocket implementation in this host).
        if ws::is_ws_upgrade(&req) {
            serve_ws_upgrade(&req, &mut stream, gw, &acc, &reply_tx, &reply_rx);
            return;
        }

        let keepalive_req = request_wants_keepalive(&req);

        // CERTIFIED EXPORT-FUNCTION SERVE: the chosen route (`GET /`), when
        // `DRORB_CAKE_SERVE=1`, is answered by the certified export-function machine
        // code linked into this process (ffi/cake/serve.S, driven by the re-entrant
        // cake_serve_ffi.c) rather than the leanc-compiled proven serve. The response
        // bytes are produced by the machine code. It is delimited by close (no
        // Content-Length), so this arm writes the bytes and closes the connection.
        // Returns false for every other request and every non-demo build, so
        // everything else runs the proven pipeline below.
        if crate::cake_serve::wants_cake_serve(&req) {
            let mut cake = gw.pool().take();
            if crate::cake_serve::serve_cake_into(&req, &mut cake) {
                emit(&cake, None);
                let _ = stream.write_all(&cake);
                return;
            }
        }

        // GEARS-ENMESH: the exact `GET /health` request, when `DRORB_HEALTH_NATIVE=1`,
        // is answered by cake--pancake-compiled x64 machine code linked into this
        // process (ffi/health/health.S, driven by the re-entrant health_ffi.c) rather
        // than the leanc-compiled proven serve. The response bytes are produced by the
        // CakeML machine code and are byte-identical to the leanc path's wire output.
        // Returns false for every other request and every non-demo build (the native
        // library is not linked), so everything else runs the proven pipeline below.
        if crate::serve::wants_native_health(&req) {
            let mut native = gw.pool().take();
            if crate::serve::serve_native_into(&req, &mut native) {
                let keepalive = keepalive_req
                    && response_is_self_delimited(&native)
                    && !response_wants_close(&native);
                // The cake bytes are the final wire form (they already carry the
                // Connection header the leanc path's host annotation adds), so write
                // them as-is — no re-annotation.
                emit(&native, None);
                if stream.write_all(&native).is_err() {
                    return;
                }
                if !keepalive {
                    return;
                }
                continue 'conn;
            }
        }

        // CONNECT tunnel lane: the proven default-deny admission gate
        // (`drorb_connect_gate`) decides whether the named `host:port` may be
        // tunnelled; on admit the host dials it and runs the blind bidirectional
        // pump (reusing the streaming discipline), otherwise it writes the 403.
        // The connection is consumed by the tunnel either way.
        if crate::proxy_connect::is_connect(&req) {
            let tunnel_stream = match stream.try_clone() {
                Ok(s) => s,
                Err(_) => return,
            };
            crate::proxy_connect::handle_connect(&req, tunnel_stream, gw, &reply_tx, &reply_rx);
            return;
        }

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
            if let Some(mut resp) = crate::interp::run_effect_serve(&req, gw, &reply_tx, &reply_rx)
            {
                let keepalive = keepalive_req
                    && response_is_self_delimited(&resp)
                    && !response_wants_close(&resp);
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
            match crate::proxy_hook::handle_proxy_streaming(
                &req,
                keepalive_req,
                &mut stream,
                gw,
                &reply_tx,
                &reply_rx,
            ) {
                Some(Ok(out)) => {
                    // The upstream reply was already streamed to the client; the
                    // host only records it and decides the connection disposition.
                    emit_streamed(&out.head, out.bytes, out.backend.as_deref());
                    if !out.keepalive {
                        return;
                    }
                    continue 'conn;
                }
                Some(Err(_)) => return, // client write failed mid-stream
                None => {}              // no fleet configured: fall through
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
                match crate::proxy_hook::handle_proxy_streaming(
                    &req,
                    keepalive_req,
                    &mut stream,
                    gw,
                    &reply_tx,
                    &reply_rx,
                ) {
                    Some(Ok(out)) => {
                        emit_streamed(&out.head, out.bytes, out.backend.as_deref());
                        if !out.keepalive {
                            return;
                        }
                        continue 'conn;
                    }
                    Some(Err(_)) => return,
                    None => {}
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
                    let keepalive = keepalive_req
                        && response_is_self_delimited(&resp)
                        && !response_wants_close(&resp);
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

        // Host-side static-file streaming lane (roadmap Stage 3, gated on
        // `DRORB_STATIC_ROOT`): ANY request under the serving prefix is DECIDED by
        // the proven core and only executed here. The PATH decision (split /
        // decode-once / UTF-8 gate / clamped dot-walk) crosses the proven
        // `drorb_static_resolve`; the RESPONSE decision — the 405 method gate, the
        // 404, the conditional 304 (the proven ConditionalRequest matcher +
        // exact-date If-Modified-Since), Range (206 single window / 206
        // multipart/byteranges / 416), every header byte and every file byte
        // window — crosses `drorb_static_decide` (Route.StaticDecide), and the
        // host streams the planned windows with a BOUNDED buffer, never
        // materializing the file. Unset ⇒ inert ⇒ the default serve path is
        // byte-identical.
        if let Some(sr) = crate::static_serve::get() {
            if sr.is_static_path(&req) {
                let resolve = |rel: &[u8]| gw.call_static_resolve(rel, &reply_tx, &reply_rx);
                let decide = |frame: &[u8]| gw.call_static_decide(frame, &reply_tx, &reply_rx);
                let zc_fd = {
                    use std::os::unix::io::AsRawFd;
                    Some(stream.as_raw_fd())
                };
                match sr.handle_streaming_zc(
                    &req,
                    keepalive_req,
                    &mut stream,
                    zc_fd,
                    resolve,
                    decide,
                ) {
                    Ok(out) => {
                        emit_streamed(&out.head, out.bytes, None);
                        if !out.keepalive {
                            return;
                        }
                        conn_seq = conn_seq.saturating_add(1);
                        continue 'conn;
                    }
                    Err(_) => return, // client write failed mid-stream
                }
            }
        }

        // Streaming response-emit path (`DRORB_STREAM_SERVE=1`): pull the proven
        // response out of `drorb_serve_stream` one bounded chunk at a time and write
        // each straight to the socket, so the host never holds the whole response.
        // The chunks reassemble to the exact `drorb_serve` bytes
        // (`serveChunkList_flatten`), so the wire output is byte-identical; only the
        // host's memory profile changes. Gated OFF by default (this path mirrors the
        // NON-metered serve), so the default metered conformance path is untouched.
        if crate::stream_serve::enabled() {
            match crate::stream_serve::serve_streamed(
                &req,
                keepalive_req,
                &mut stream,
                gw,
                &reply_tx,
                &reply_rx,
            ) {
                Some(Ok(out)) => {
                    emit_streamed(&out.head, out.bytes, None);
                    if !out.keepalive {
                        return;
                    }
                    conn_seq = conn_seq.saturating_add(1);
                    continue 'conn;
                }
                Some(Err(_)) => return, // client write failed mid-stream
                None => crate::serve::serve_owner_gone(),
            }
        }

        // Cross the METERED seam: the proven IP-filter gate decides on this
        // connection's client address (accept peer, or the forwarded client when
        // the peer is a trusted proxy) and the rate gate on the per-connection
        // request index. `conn_seq` advances once per served request, so a burst
        // on one kept-alive connection depletes the bucket.
        // DoS admission state the proven fold gates decide on, threaded into the
        // metered context (`Reactor.DeployPipeline.ctxOfMeteredConn`). `active` is the
        // source's standing concurrent-connection count EXCLUDING this connection (the
        // per-source counter incremented this connection at accept, so subtract one);
        // the fold's conn-limit gate answers the proven `503` once it reaches
        // `connCap`. `hdr_span` is how long this request's header phase took, in whole
        // seconds against the capture at the start of the read; the fold's slowloris
        // gate answers the proven `408` once it reaches `headerTimeout`. Both are
        // enforced accept-path side too (defence in depth); threading them here routes
        // the refusal through the verified serialize path instead of a byte blob.
        let meter = Meter {
            client: client_addr(&req, peer_ip),
            // The one rate scalar: elapsed-seconds clock in the high 32 bits, the
            // standing request count in the low 32, both clamped at the OPERATOR'S
            // configured `burst-cap` (`serve::pack_rate_scalar`). The proven
            // reconstruction (`Reactor.Stage.Rate.countOfPacked`/`clockOfPacked`) splits
            // them and runs the real time-based `Rate.refill`, so the deployed limiter
            // refuses at the CONFIGURED point and recovers over time.
            seq: crate::serve::pack_rate_scalar(conn_seq, conn_start.elapsed().as_secs()),
            active: u64::from(source_table().active(peer_ip).saturating_sub(1)),
            hdr_span: hdr_start.elapsed().as_secs(),
            // THE COUNTING READ for the proven `429` gate: this REQUEST's arrival is
            // noted against the source's request window and the prior count crossed.
            // The accept loop's own `rate_note` counts CONNECTION arrivals only, so on
            // a kept-alive connection it never sees requests 2..N — this is where a
            // per-source REQUEST-rate bound becomes observable at all.
            rate_prior: u64::from(source_table().req_note_prior(
                peer_ip,
                crate::config::rate_limit(),
                crate::config::rate_window(),
                std::time::Instant::now(),
            )),
        };
        conn_seq = conn_seq.saturating_add(1);
        // Braid 0: the default serve is now the CONFIG-DRIVEN metered fold. The
        // request crosses `drorb_serve_metered_cfg` carrying the active deployment
        // config (`config::get()`), so the running default serve is a fold over
        // `deployment.middleware.chain`. With no `DRORB_CONFIG` the config is EMPTY
        // and the proven core serves `servePipelineOfMetered defaultDeployment` —
        // byte-for-byte the old `call_metered` (`servePipelineOfMetered_default`,
        // `rfl`), so the default conformance is untouched. A config declaring routes
        // was already served through `call_cfg` above and never reaches here; this
        // arm handles the routeless / no-config default. A future middleware braid is
        // a config-gated append to the chain, not shared-file surgery here.
        // Braid: when the deployment is braid-marked (`DRORB_BRAID=1`), the request
        // crosses the metered BRAIDED seam (`drorb_serve_metered_braided`) — the same
        // connection-aware IP-filter/rate gate chain, but folding over
        // `braidedDeployment` (the proven forward-auth gate + request-id echo at the
        // head). The composition is proven (`servePipelineOfMetered_braided_off_eq`
        // byte-identical when unmarked, `_fa_denies_status` = 401,
        // `_rid_echoes`). Unset ⇒ the config-driven default metered fold runs
        // unchanged (`servePipelineOfMetered_default` anchor intact).
        let mut resp = if crate::config::braid_enabled() {
            match gw.call_metered_braided(&req, meter, &reply_tx, &reply_rx) {
                Some(r) => r,
                None => crate::serve::serve_owner_gone(),
            }
        } else if let Some(gw_sel) = crate::gateway::selector() {
            // GATEWAY UMBRELLA (`DRORB_GATEWAY`): the whole request is dispatched by the
            // proven `Dsl.Config.Gateway.denoteOn` host -> vhost -> route -> action fold,
            // crossing `drorb_serve_gateway` with the connection context `meter` in scope.
            // respond / redirect / basic_auth / static are served on the wire in Lean; a
            // proxy route answers the 502 placeholder (the real upstream dial is the
            // extended host-side step). Unset ⇒ inert ⇒ the config-driven default runs.
            match gw.call_gateway(gw_sel, &req, meter, &reply_tx, &reply_rx) {
                Some(r) => r,
                None => crate::serve::serve_owner_gone(),
            }
        } else {
            let active_cfg = crate::config::get();
            // The seam scans the config text for the middleware POLICY (max-body-size /
            // allow-method / allow-host) AND the route table. Use the parsed config's
            // text when a valid route config is in force, else the boot-cached RAW bytes
            // (so a policy-only config the route grammar does not model still enforces
            // its policy). No config ⇒ empty ⇒ byte-identical default.
            let raw;
            let cfg_bytes: &[u8] = match active_cfg.as_ref() {
                Some(d) => d.config_text.as_slice(),
                None => {
                    raw = crate::config::raw_text();
                    &raw
                }
            };
            match gw.call_metered_cfg(cfg_bytes, &req, meter, &reply_tx, &reply_rx) {
                Some(r) => r,
                None => crate::serve::serve_owner_gone(),
            }
        };

        // REAL GZIP SEAM (`DRORB_RUST_GZIP=1`): replace the proven stored-block gzip
        // stage's (uncompressed) body with real flate2 DEFLATE before framing. Keyed on
        // the response's own `Content-Encoding: gzip`; inert when the flag is unset or
        // the response was not gzipped. Runs BEFORE keepalive detection so the rewritten
        // Content-Length is what decides self-delimitation. (Trusted, not verified.)
        if crate::gzip::enabled() {
            crate::gzip::recompress(&mut resp);
        }
        let keepalive =
            keepalive_req && response_is_self_delimited(&resp) && !response_wants_close(&resp);
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

/// **The one WebSocket upgrade path in this host.** Given a framed request head
/// that [`ws::is_ws_upgrade`] accepted and a BLOCKING `stream` positioned right
/// after it, run the whole RFC 6455 lane: the proven `Seam::UpgradeGate`
/// admission crossing, the 101 handshake response, then the proven frame pump to
/// close. `pipelined` is whatever the client sent immediately after the upgrade
/// request (fed to the engine before the first recv); empty is the common case.
///
/// Every reactor calls THIS function, so there is exactly one implementation of
/// the gate → 101 → pump sequence: the blocking host calls it inline on its
/// connection thread, and the io_uring / kqueue reactors call it on the handoff
/// thread the connection's fd was moved to (`uring::ws_handoff`,
/// `Reactor::ws_handoff`). The host only moves bytes; every decision inside is
/// the proven core's (`drorb_upgrade_gate`, `drorb_ws_header`, `drorb_ws_admit`,
/// `drorb_ws_utf8`, `drorb_ws_close_body`).
pub(crate) fn serve_ws_upgrade(
    req: &[u8],
    stream: &mut TcpStream,
    gw: &ServeGateway,
    pipelined: &[u8],
    reply_tx: &std::sync::mpsc::Sender<PooledBuf>,
    reply_rx: &std::sync::mpsc::Receiver<PooledBuf>,
) {
    // AUTH GATE: the RFC 6455 handshake must not bypass authentication. Run
    // the upgrade REQUEST through the deployed `/admin` JWT gate (the same
    // gate the request path's fold runs) BEFORE returning 101. If the
    // upgrade targets a protected path with no/invalid credentials the gate
    // returns a 401; write that refusal and close instead of upgrading. An
    // authorized upgrade returns no gate bytes and proceeds to the 101.
    let mut gate_req = gw.pool().take();
    gate_req.extend_from_slice(req);
    match gw.call_seam(gate_req, Seam::UpgradeGate, reply_tx, reply_rx) {
        Some(refusal) if !refusal.is_empty() => {
            let _ = stream.write_all(&refusal);
            return;
        }
        Some(_) => {} // authorized: no refusal bytes — complete the handshake
        None => crate::serve::serve_owner_gone(),
    }
    if let Some((resp, ws_cfg)) = ws::upgrade_response(req) {
        if stream.write_all(&resp).is_err() {
            return;
        }
        ws_frame_loop(stream, gw, pipelined, ws_cfg);
    }
}

/// The open-connection WebSocket frame loop (RFC 6455 §5). After the 101
/// handshake, ONE persistent, bounded, streaming codec
/// ([`crate::ws_assembly::WsEngine`]) is fed every recv chunk, so frames and
/// messages may straddle any number of recvs and the per-connection memory is
/// capped by construction (14-byte header + 125-byte control + one ≤ 16 MiB
/// reassembly buffer; over-limit messages are refused with close 1009 before
/// buffering). Echo replies, pongs, and close frames come back in `out` and
/// are written as produced. `Flow::Shut` means a close frame was emitted (a
/// close-handshake reply or a §7.1.7 connection failure): write it, let the
/// peer read it, and drop the connection. Any bytes the client pipelined
/// right after the upgrade (`pipelined`) are fed first.
fn ws_frame_loop(
    stream: &mut TcpStream,
    gw: &ServeGateway,
    pipelined: &[u8],
    ws_cfg: crate::ws::WsConfig,
) {
    use crate::ws_assembly::{Flow, WsEngine};

    // Frames may sit idle on an open WebSocket; block indefinitely between them.
    let _ = stream.set_read_timeout(None);

    // Carry the handshake's negotiated RFC 7692 permessage-deflate state into
    // the frame engine (uncompressed when nothing was negotiated).
    let mut engine = WsEngine::with_config(ws_cfg);
    let mut out: PooledBuf = gw.pool().take();

    // Feed any bytes pipelined right after the upgrade request.
    if !pipelined.is_empty() {
        let flow = engine.feed(pipelined, &mut out);
        if !out.is_empty() {
            if stream.write_all(&out).is_err() {
                return;
            }
            out.clear();
        }
        if flow == Flow::Shut {
            ws_close_drain(stream);
            return;
        }
    }

    let mut chunk = [0u8; 65536];
    loop {
        let n = match stream.read(&mut chunk) {
            Ok(0) => return, // peer closed
            Ok(n) => n,
            Err(_) => return,
        };
        let flow = engine.feed(&chunk[..n], &mut out);
        if !out.is_empty() {
            if stream.write_all(&out).is_err() {
                return;
            }
            out.clear();
        }
        if flow == Flow::Shut {
            ws_close_drain(stream);
            return;
        }
    }
}

/// After our close frame is on the wire: shut down the write side and briefly
/// drain the peer, so the close frame is delivered before the socket drops (an
/// immediate close with unread bytes queued could turn into a reset that
/// destroys it in flight). Bounded: at most 5 seconds, then the socket drops.
fn ws_close_drain(stream: &mut TcpStream) {
    let _ = stream.shutdown(std::net::Shutdown::Write);
    let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
    let deadline = std::time::Instant::now() + Duration::from_secs(5);
    let mut sink = [0u8; 65536];
    while std::time::Instant::now() < deadline {
        match stream.read(&mut sink) {
            Ok(0) | Err(_) => break, // peer finished (or is gone)
            Ok(_) => {}              // discard: the connection is already failed
        }
    }
}

/// RAII guard that decrements the two connection counters EXACTLY ONCE when a
/// connection worker returns — INCLUDING on an unwinding panic inside
/// [`handle_conn`]. The counters are incremented on the accept path (the
/// per-source `admit` and the process-global `ACTIVE_CONNS.fetch_add`); a bare
/// decrement placed AFTER `handle_conn` is skipped when `handle_conn` panics,
/// leaking both counters — the per-source count wedges that source's
/// `max-connections` gate, and `ACTIVE_CONNS` creeps toward `MAX_CONNS`,
/// eventually bricking accept for the whole host. Running the decrement in
/// `Drop` makes it fire on every exit path, panic included.
struct ConnCountGuard {
    ip: IpAddr,
}

impl Drop for ConnCountGuard {
    fn drop(&mut self) {
        source_table().on_close(self.ip);
        crate::ACTIVE_CONNS.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Run the blocking accept loop on `listener` until shutdown, driving every
/// request through `gw`.
pub fn run(listener: TcpListener, gw: ServeGateway) {
    // Non-blocking accept so the SIGINT flag is observed promptly.
    listener
        .set_nonblocking(true)
        .expect("failed to set the listener non-blocking");

    // The serve-owner set (`DRORB_SERVE_OWNERS`, default 1 = the original
    // single-owner model): each accepted connection is PINNED to one owner,
    // assigned round-robin, so per-connection request/response FIFO order is
    // preserved while distinct connections' seam crossings overlap across
    // owners. Owner 0 is the primary runtime owner (the one `main` also hands
    // to the TLS/UDP/admin paths).
    let owners: Vec<Arc<ServeGateway>> = crate::serve::serve_owner_set(gw)
        .into_iter()
        .map(Arc::new)
        .collect();
    let mut next_owner = 0usize;
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping accept loop");
            break;
        }
        match listener.accept() {
            Ok((mut stream, peer)) => {
                // The two RESOURCE ceilings, before any per-source policy: this
                // host's worker-THREAD bound, and the process-wide CONNECTION bound
                // every backend shares (`DRORB_MAX_CONNS`). The thread bound is the
                // lower of the two at default settings, so this host's behaviour is
                // unchanged; the second is here so an operator who states a process
                // connection ceiling gets it on every `--io` rather than on two of
                // three. This accept loop is single-threaded, so read-then-admit has
                // no race — the shard reactors need `enter_counted`'s atomic
                // reservation, which is why that call and this check differ.
                let conn_cap = crate::standing::process_conn_cap();
                if crate::ACTIVE_CONNS.load(Ordering::SeqCst) >= MAX_CONNS
                    || (conn_cap != 0 && source_table().total_active() >= conn_cap)
                {
                    drop(stream); // at a resource ceiling: refuse by closing immediately
                    continue;
                }
                // REACTOR-LEVEL per-source connection-limit gate. The check-and-count
                // is atomic per source (`admit`), so a source at/over its cap is
                // refused the REAL 503 and closed WITHOUT spawning a serve — the
                // proven `Reactor.Stage.ConnLimit` decision on accept-path standing
                // state. `cap == 0` (directive absent) admits every source (unchanged).
                let ip = peer.ip();
                let cap = crate::config::max_connections();
                if !source_table().admit(ip, cap) {
                    let _ = stream.write_all(CONN_LIMIT_503); // best-effort 503
                    let _ = stream.flush();
                    crate::metrics::note_conn_limit_refused();
                    drop(stream); // decrement not needed: admit did not increment
                    continue;
                }
                // REACTOR-LEVEL per-source REQUEST-RATE gate — note this arrival; over
                // the `rate-limit` window ⇒ the REAL 429, closed WITHOUT spawning a
                // serve (`rate_limit_fires`). The `admit` above already incremented the
                // connection counter, so decrement here (`on_close`) to keep it exact.
                if source_table().rate_note(
                    ip,
                    crate::config::rate_limit(),
                    crate::config::rate_window(),
                    std::time::Instant::now(),
                ) {
                    let _ = stream.write_all(RATE_LIMIT_429); // best-effort 429
                    let _ = stream.flush();
                    crate::metrics::note_rate_limit_refused();
                    drop(stream);
                    source_table().on_close(ip);
                    continue;
                }
                crate::ACTIVE_CONNS.fetch_add(1, Ordering::SeqCst);
                // Pin this connection to one serve owner (round-robin).
                let gw = Arc::clone(&owners[next_owner]);
                next_owner = (next_owner + 1) % owners.len();
                let spawned =
                    std::thread::Builder::new()
                        .name("drorb-conn".into())
                        .spawn(move || {
                            // RAII: decrement both connection counters EXACTLY ONCE when
                            // this worker returns — the guard's `Drop` runs on a normal
                            // return AND on an unwinding panic inside `handle_conn`, so a
                            // panicking connection can no longer leak a counter toward the
                            // accept cap. Matches the `admit` + `ACTIVE_CONNS` increments.
                            let _guard = ConnCountGuard { ip };
                            handle_conn(stream, &gw);
                        });
                if spawned.is_err() {
                    // The worker thread was never created, so its guard never runs;
                    // undo the two accept-path increments here (the old code leaked
                    // both on spawn failure).
                    source_table().on_close(ip);
                    crate::ACTIVE_CONNS.fetch_sub(1, Ordering::SeqCst);
                }
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

#[cfg(test)]
mod robustness_tests {
    use super::*;
    use std::net::Ipv4Addr;

    /// Serialize the tests that touch the process-global `ACTIVE_CONNS`: they each
    /// establish and re-check a baseline for that shared counter, which is only
    /// stable if no sibling test mutates it concurrently.
    static COUNTER_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// A connection worker whose `handle_conn` PANICS must not leak either
    /// connection counter. This drives the exact accept-path → worker-thread
    /// shape: `admit` + `ACTIVE_CONNS.fetch_add` on the accept side, then a worker
    /// that creates the `ConnCountGuard` and panics (standing in for a panic inside
    /// `handle_conn`). After joining every panicking worker, both counters must be
    /// back at baseline — the guard's `Drop` ran on the unwind. Before the fix (a
    /// bare decrement placed after `handle_conn`) these panics would leak, creeping
    /// the per-source count and `ACTIVE_CONNS` toward the accept cap.
    #[test]
    fn conn_counters_do_not_leak_on_panicking_conn() {
        let _serial = COUNTER_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // A unique source address so the process-global per-source table is
        // isolated from any other test (TEST-NET-3, RFC 5737).
        let ip = IpAddr::V4(Ipv4Addr::new(203, 0, 113, 17));
        let base_active = crate::ACTIVE_CONNS.load(Ordering::SeqCst);
        assert_eq!(
            source_table().active(ip),
            0,
            "test precondition: this source starts with no standing connections"
        );

        const N: usize = 128;
        let mut handles = Vec::with_capacity(N);
        for _ in 0..N {
            // Accept-path increments (cap 0 = admit every source).
            assert!(source_table().admit(ip, 0));
            crate::ACTIVE_CONNS.fetch_add(1, Ordering::SeqCst);
            handles.push(std::thread::spawn(move || {
                let _guard = ConnCountGuard { ip };
                panic!("simulated panic inside handle_conn");
            }));
        }
        // Every worker panics; join returns Err — expected and ignored.
        for h in handles {
            let _ = h.join();
        }

        assert_eq!(
            source_table().active(ip),
            0,
            "per-source standing counter leaked on panicking connections"
        );
        assert_eq!(
            crate::ACTIVE_CONNS.load(Ordering::SeqCst),
            base_active,
            "ACTIVE_CONNS leaked on panicking connections (would creep toward MAX_CONNS)"
        );
    }

    /// The guard decrements exactly once on the NORMAL (non-panicking) return path
    /// too — no double-decrement, no missed decrement — and leaves `ACTIVE_CONNS`
    /// back at its baseline (the guard subtracts it, paired with the add here).
    #[test]
    fn conn_counter_balanced_on_normal_return() {
        let _serial = COUNTER_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ip = IpAddr::V4(Ipv4Addr::new(203, 0, 113, 18));
        let base_active = crate::ACTIVE_CONNS.load(Ordering::SeqCst);
        assert!(source_table().admit(ip, 0));
        crate::ACTIVE_CONNS.fetch_add(1, Ordering::SeqCst);
        assert_eq!(source_table().active(ip), 1);
        {
            let _guard = ConnCountGuard { ip };
            // normal return: guard drops here
        }
        assert_eq!(
            source_table().active(ip),
            0,
            "guard decremented the per-source counter exactly once on a normal return"
        );
        assert_eq!(
            crate::ACTIVE_CONNS.load(Ordering::SeqCst),
            base_active,
            "guard decremented ACTIVE_CONNS exactly once on a normal return"
        );
    }
}
