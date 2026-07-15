//! Reverse-proxy backend dialling: the host side of the proxy forward.
//!
//! The proven core (`Reactor.ProxyDial`, exported as `drorb_proxy_pick`) decides
//! WHICH backend a request goes to — `Proxy.selectChain` over the eligible
//! (healthy ∧ active) pool, honouring live health, the circuit breaker, and
//! session affinity. This module is the HOST side of that split: it opens the
//! real TCP connection to the chosen backend, forwards the request bytes, and
//! returns the upstream's response bytes. No selection logic lives here — the
//! backend id always comes from the proven pick; this module only maps that id to
//! a configured socket, dials it, and moves bytes.
//!
//! The split mirrors `drorb_serve`: the core is sans-IO and decides meaning; the
//! host owns the sockets. Before this module, the proxy LB ran inside the core and
//! stamped its choice into a header, but nothing ever opened a socket to a backend
//! — the forward was proven-but-not-connected. This closes it.
//!
//! On Linux with a plaintext-TCP client, the proxied response BODY is moved by
//! the kernel splice relay ([`forward_streaming_spliced`]): upstream socket →
//! pipe → client socket via `splice(2)`, never entering this process. Only the
//! response head (which the host must read to frame the body and set the
//! connection disposition) is buffered in userspace.
//!
//! ## Live inputs the host contributes to the proven pick
//!
//! * **health mask** — `Fleet` runs active TCP probes against each backend and
//!   packs an up/down bit per backend into a `u8`. A backend that fails to accept
//!   is marked down; the proven selector (fed this mask) then never chooses it
//!   (`Reactor.ProxyDial.pick_health_ejects`).
//! * **circuit breaker** — after `breaker_threshold` consecutive forward failures
//!   a backend's bit is forced down (breaker open); a success closes it again.
//!   Same mechanism, same proven ejection.
//! * **affinity key** — [`sticky_key`] extracts the session key (a `sid` cookie,
//!   else the request target) and feeds it to the pick; rendezvous hashing pins a
//!   session to one backend across requests.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// A configured backend fleet: the id→socket map plus live health and breaker
/// state. Ids match the proven `Reactor.ProxyDial.fleet` backend ids (0,1,2,…).
pub struct Fleet {
    /// backend id → its socket address.
    by_id: HashMap<u32, SocketAddr>,
    /// Live health bitmask: bit `i` set ⇒ backend `i` is up (probe OK AND breaker
    /// closed). This is the `mask` byte handed to the proven `drorb_proxy_pick`.
    health: AtomicU32,
    /// Per-backend consecutive-failure counter for the circuit breaker.
    breaker: Mutex<HashMap<u32, u32>>,
    /// Per-backend in-flight forward count (incremented around the upstream dial),
    /// for operator introspection (`/admin/backends`). One atomic per configured
    /// backend, so the hot path is lock-free.
    inflight: HashMap<u32, AtomicU32>,
    /// Consecutive forward failures that open a backend's breaker.
    breaker_threshold: u32,
    /// How long to wait dialling / probing a backend before giving up.
    dial_timeout: Duration,
    /// Shard-local round counter the weighted-round-robin LB policy walks. Bumped
    /// once per proven pick so a round-robin config visibly rotates backends.
    round: AtomicU32,
}

/// A read-only snapshot of one backend's operational health, for the admin
/// surface (`/admin/backends`). Assembled by [`Fleet::snapshot`].
pub struct BackendHealth {
    /// The proven-pick backend id.
    pub id: u32,
    /// The configured socket address.
    pub addr: SocketAddr,
    /// Whether the backend is currently eligible (probe OK and breaker closed) —
    /// its bit in the live mask the proven selector consumes.
    pub up: bool,
    /// Forwards currently in flight to this backend.
    pub inflight: u32,
    /// Consecutive forward failures recorded against the breaker.
    pub breaker_failures: u32,
    /// Whether the breaker has tripped open (`breaker_failures ≥ threshold`).
    pub breaker_open: bool,
}

impl Fleet {
    /// Build a fleet from a spec string like `0=127.0.0.1:9400,1=127.0.0.1:9401`.
    /// All configured backends start assumed-up; the health loop / breaker demote
    /// them on real failures. Returns `None` if the spec names no backend.
    pub fn parse(spec: &str, breaker_threshold: u32, dial_timeout: Duration) -> Option<Fleet> {
        let mut by_id = HashMap::new();
        let mut mask: u32 = 0;
        for entry in spec.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let (id_s, addr_s) = entry.split_once('=')?;
            let id: u32 = id_s.trim().parse().ok()?;
            let addr: SocketAddr = addr_s.trim().parse().ok()?;
            by_id.insert(id, addr);
            mask |= 1 << id;
        }
        if by_id.is_empty() {
            return None;
        }
        let inflight = by_id.keys().map(|&id| (id, AtomicU32::new(0))).collect();
        Some(Fleet {
            by_id,
            health: AtomicU32::new(mask),
            breaker: Mutex::new(HashMap::new()),
            inflight,
            breaker_threshold,
            dial_timeout,
            round: AtomicU32::new(0),
        })
    }

    /// Read the fleet spec from `DRORB_PROXY_BACKENDS` (see [`Fleet::parse`]).
    pub fn from_env() -> Option<Fleet> {
        let spec = std::env::var("DRORB_PROXY_BACKENDS").ok()?;
        let thr = std::env::var("DRORB_PROXY_BREAKER")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3);
        Fleet::parse(&spec, thr, Duration::from_millis(500))
    }

    /// The live health bitmask, low 8 bits, as the `mask` byte the proven pick
    /// consumes. Bit `i` ⇒ backend `i` is up.
    pub fn mask(&self) -> u8 {
        (self.health.load(Ordering::SeqCst) & 0xff) as u8
    }

    /// The socket for a backend id, if configured.
    pub fn addr(&self, id: u32) -> Option<SocketAddr> {
        self.by_id.get(&id).copied()
    }

    /// The next round-counter value (low 8 bits), advanced by one. The
    /// weighted-round-robin LB policy reduces this modulo the eligible pool size,
    /// so successive picks under a round-robin config rotate across backends.
    pub fn next_round(&self) -> u8 {
        (self.round.fetch_add(1, Ordering::SeqCst) & 0xff) as u8
    }

    /// The live per-backend in-flight load, one byte per backend id `0..3`
    /// (saturating at 255), as the `conns` bytes the proven load-aware pick
    /// (`drorb_lb_pick`) consumes. Backend ids match the proven `fleetC` (0,1,2);
    /// an unconfigured id reads as zero load.
    pub fn conns_bytes(&self) -> Vec<u8> {
        (0u32..3)
            .map(|id| {
                self.inflight
                    .get(&id)
                    .map(|c| c.load(Ordering::SeqCst).min(255) as u8)
                    .unwrap_or(0)
            })
            .collect()
    }

    fn set_up(&self, id: u32, up: bool) {
        let bit = 1u32 << id;
        if up {
            self.health.fetch_or(bit, Ordering::SeqCst);
        } else {
            self.health.fetch_and(!bit, Ordering::SeqCst);
        }
    }

    /// A successful forward: close the breaker and mark the backend up.
    pub fn record_success(&self, id: u32) {
        self.breaker.lock().unwrap().insert(id, 0);
        self.set_up(id, true);
    }

    /// A failed forward: bump the breaker; once it trips, force the backend down
    /// (breaker open) so the proven selector routes around it.
    pub fn record_failure(&self, id: u32) {
        let mut b = self.breaker.lock().unwrap();
        let n = b.entry(id).or_insert(0);
        *n += 1;
        if *n >= self.breaker_threshold {
            self.set_up(id, false);
        }
    }

    fn inflight_inc(&self, id: u32) {
        if let Some(c) = self.inflight.get(&id) {
            c.fetch_add(1, Ordering::SeqCst);
        }
    }

    fn inflight_dec(&self, id: u32) {
        if let Some(c) = self.inflight.get(&id) {
            c.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// A per-backend health snapshot for operator introspection
    /// (`/admin/backends`): address, live up/down, in-flight forwards, and breaker
    /// state, ordered by backend id. Read-only — it never touches the mask the
    /// proven selector consumes.
    pub fn snapshot(&self) -> Vec<BackendHealth> {
        let mask = self.health.load(Ordering::SeqCst);
        let breaker = self.breaker.lock().unwrap();
        let mut out: Vec<BackendHealth> = self
            .by_id
            .iter()
            .map(|(&id, &addr)| {
                let failures = breaker.get(&id).copied().unwrap_or(0);
                BackendHealth {
                    id,
                    addr,
                    up: mask & (1 << id) != 0,
                    inflight: self
                        .inflight
                        .get(&id)
                        .map(|c| c.load(Ordering::SeqCst))
                        .unwrap_or(0),
                    breaker_failures: failures,
                    breaker_open: failures >= self.breaker_threshold,
                }
            })
            .collect();
        out.sort_by_key(|b| b.id);
        out
    }

    /// One active-health sweep: TCP-probe every configured backend and set its
    /// bit up iff the connection is accepted (a breaker-open backend stays down
    /// until a probe succeeds). Returns the resulting mask.
    pub fn probe_once(&self) -> u8 {
        for (&id, &addr) in &self.by_id {
            let up = TcpStream::connect_timeout(&addr, self.dial_timeout).is_ok();
            if up {
                // Probe recovered the backend: clear any open breaker.
                self.breaker.lock().unwrap().insert(id, 0);
            }
            self.set_up(id, up);
        }
        self.mask()
    }

    /// Spawn the background active-health loop: sweep every `interval` until the
    /// process exits. The mask it maintains is what the proven selector sees.
    pub fn spawn_health_checks(self: Arc<Self>, interval: Duration) {
        std::thread::Builder::new()
            .name("drorb-proxy-health".into())
            .spawn(move || {
                loop {
                    self.probe_once();
                    std::thread::sleep(interval);
                }
            })
            .expect("failed to spawn the proxy health-check thread");
    }
}

/// The request target (the path in the request line), as bytes.
fn request_target(req: &[u8]) -> Option<&[u8]> {
    let line_end = req.windows(2).position(|w| w == b"\r\n")?;
    let line = &req[..line_end];
    let mut it = line.splitn(3, |&c| c == b' ');
    it.next()?; // method
    it.next() // target
}

/// Is this request one the reverse proxy should forward? Targets under `/api`.
pub fn is_proxy_path(req: &[u8]) -> bool {
    match request_target(req) {
        Some(t) => t == b"/api" || t.starts_with(b"/api/") || t.starts_with(b"/api?"),
        None => false,
    }
}

/// Extract the session-affinity key: the `sid=` cookie value if present, else the
/// request target. These bytes are hashed by the proven rendezvous policy, so one
/// session pins to one backend across requests.
pub fn sticky_key(req: &[u8]) -> Vec<u8> {
    // Scan headers for a Cookie line and a `sid=` crumb.
    let head_end = req
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(req.len());
    let head = &req[..head_end];
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 7 && line[..7].eq_ignore_ascii_case(b"cookie:") {
            for crumb in line[7..].split(|&c| c == b';') {
                let crumb = trim_ascii(crumb);
                if let Some(v) = crumb.strip_prefix(b"sid=") {
                    return v.to_vec();
                }
            }
        }
    }
    request_target(req).map(|t| t.to_vec()).unwrap_or_default()
}

fn trim_ascii(mut b: &[u8]) -> &[u8] {
    while let [f, rest @ ..] = b {
        if f.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., l] = b {
        if l.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    b
}

/// The eight connection-scoped ("hop-by-hop") header names an intermediary MUST NOT
/// forward to the next hop (RFC 9110 §7.6.1), lowercase. Mirrors the proven
/// `Reactor.ProxyForward.hopByHopNames`.
const HOP_BY_HOP: [&[u8]; 9] = [
    b"connection",
    b"keep-alive",
    b"proxy-authenticate",
    b"proxy-authorization",
    b"te",
    b"trailer",
    b"transfer-encoding",
    b"upgrade",
    b"proxy-connection",
];

/// The lowercased header NAME of a header line — the bytes before the first colon,
/// ASCII-lowercased. Mirrors `Reactor.ProxyForward.headerNameLower`.
fn header_name_lower(line: &[u8]) -> Vec<u8> {
    line.iter()
        .take_while(|&&b| b != b':')
        .map(|b| b.to_ascii_lowercase())
        .collect()
}

/// Trim ASCII OWS (SP / HTAB) from both ends of a token. Mirrors
/// `Reactor.ProxyForward.trimOWS`.
fn trim_ows(mut b: &[u8]) -> &[u8] {
    while let [f, rest @ ..] = b {
        if *f == b' ' || *f == b'\t' {
            b = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., l] = b {
        if *l == b' ' || *l == b'\t' {
            b = rest;
        } else {
            break;
        }
    }
    b
}

/// The field names listed across every `Connection` header line of `hlines`: each
/// `Connection` value split on commas, each token OWS-trimmed and lowercased, empties
/// dropped. These are ALSO hop-by-hop for this hop (RFC 9110 §7.6.1). Mirrors
/// `Reactor.ProxyForward.connectionTokens`.
fn connection_tokens(hlines: &[&[u8]]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for line in hlines {
        if header_name_lower(line) == b"connection" {
            let value: &[u8] = match line.iter().position(|&b| b == b':') {
                Some(p) => &line[p + 1..],
                None => &[],
            };
            for tok in value.split(|&b| b == b',') {
                let t: Vec<u8> = trim_ows(tok)
                    .iter()
                    .map(|b| b.to_ascii_lowercase())
                    .collect();
                if !t.is_empty() {
                    out.push(t);
                }
            }
        }
    }
    out
}

/// **Strip hop-by-hop headers from a request before forwarding it upstream**
/// (RFC 9110 §7.6.1). The request line is kept verbatim; every header line whose
/// (case-insensitive) name is one of the eight fixed hop-by-hop fields OR a token
/// named in a `Connection` header is dropped; surviving headers and the body pass
/// through unchanged. This is the byte-for-byte host image of the proven
/// `Reactor.ProxyForward.stripHopByHop` (`demo_strip` proves the exact bytes; the
/// `strips_hop_by_hop_request_headers` test asserts the same constant here).
pub fn strip_hop_by_hop(req: &[u8]) -> Vec<u8> {
    // Split at the first CRLFCRLF into (head, body); a request without one is
    // malformed and forwarded untouched.
    let (head, body): (&[u8], &[u8]) = match find(req, b"\r\n\r\n") {
        Some(p) => (&req[..p], &req[p + 4..]),
        None => return req.to_vec(),
    };
    let mut lines = head
        .split(|&b| b == b'\n')
        .map(|l| l.strip_suffix(b"\r").unwrap_or(l));
    let Some(req_line) = lines.next() else {
        return req.to_vec();
    };
    let hlines: Vec<&[u8]> = lines.collect();
    let conn = connection_tokens(&hlines);

    let mut out = Vec::with_capacity(req.len());
    out.extend_from_slice(req_line);
    for line in &hlines {
        let name = header_name_lower(line);
        let drop = HOP_BY_HOP.iter().any(|h| name == *h) || conn.iter().any(|t| *t == name);
        if !drop {
            out.extend_from_slice(b"\r\n");
            out.extend_from_slice(line);
        }
    }
    out.extend_from_slice(b"\r\n\r\n");
    out.extend_from_slice(body);
    out
}

/// The proxy's `Via` field-value line, `Via: 1.1 drorb` (RFC 9110 §7.6.3): HTTP
/// version `1.1` and this proxy's pseudonym. Mirrors `Reactor.ProxyForward.viaLine`.
const VIA_LINE: &[u8] = b"Via: 1.1 drorb";

/// **Build the request forwarded upstream** (RFC 9110 §7.6): hop-by-hop headers
/// stripped (§7.6.1, [`strip_hop_by_hop`]'s discipline), a `Via` field added
/// (§7.6.3), and — when the host knows the originating client address — an
/// `X-Forwarded-For` field added (§7.6.2, de-facto). The request line and body are
/// verbatim. Byte-identical to the proven `Reactor.ProxyForward.forwardReq`
/// (`demo_forward_req` proves the exact bytes; the `forward_request_matches_proven_demo`
/// test asserts the same constants here).
pub fn forward_request(req: &[u8], client_ip: &[u8]) -> Vec<u8> {
    let (head, body): (&[u8], &[u8]) = match find(req, b"\r\n\r\n") {
        Some(p) => (&req[..p], &req[p + 4..]),
        None => return req.to_vec(),
    };
    let mut lines = head
        .split(|&b| b == b'\n')
        .map(|l| l.strip_suffix(b"\r").unwrap_or(l));
    let Some(req_line) = lines.next() else {
        return req.to_vec();
    };
    let hlines: Vec<&[u8]> = lines.collect();
    let conn = connection_tokens(&hlines);

    let mut out = Vec::with_capacity(req.len() + 64);
    out.extend_from_slice(req_line);
    // Proxy identity: Via, then X-Forwarded-For (only when a client address is
    // known — a header with an empty value is never emitted).
    out.extend_from_slice(b"\r\n");
    out.extend_from_slice(VIA_LINE);
    if !client_ip.is_empty() {
        out.extend_from_slice(b"\r\nX-Forwarded-For: ");
        out.extend_from_slice(client_ip);
    }
    for line in &hlines {
        let name = header_name_lower(line);
        let drop = HOP_BY_HOP.iter().any(|h| name == *h) || conn.iter().any(|t| *t == name);
        if !drop {
            out.extend_from_slice(b"\r\n");
            out.extend_from_slice(line);
        }
    }
    out.extend_from_slice(b"\r\n\r\n");
    out.extend_from_slice(body);
    out
}

/// The connection-scoped ("hop-by-hop") header names to strip from an UPSTREAM
/// RESPONSE before returning it to the client (RFC 9110 §7.6.1), lowercase —
/// the request set MINUS `transfer-encoding`, which frames a chunked response body
/// this proxy forwards VERBATIM and so must be preserved. Mirrors
/// `Reactor.ProxyForward.respHopByHopNames`.
const RESP_HOP_BY_HOP: [&[u8]; 8] = [
    b"connection",
    b"keep-alive",
    b"proxy-authenticate",
    b"proxy-authorization",
    b"te",
    b"trailer",
    b"upgrade",
    b"proxy-connection",
];

/// **Transform an upstream RESPONSE head** (status line + headers, through the
/// terminating CRLFCRLF) before it is returned to the client: strip response
/// hop-by-hop headers (RFC 9110 §7.6.1; `Transfer-Encoding` PRESERVED for
/// pass-through framing) and add a `Via` field (§7.6.3). The `Connection`
/// disposition is stripped here and then set by the host ([`crate::http::annotate_connection`]),
/// so the intermediary owns the client connection independently of the upstream.
/// Byte-identical to the proven `Reactor.ProxyForward.forwardRespHead` on the
/// header block (`demo_forward_resp` proves the block bytes).
pub fn forward_response_head(head: &[u8]) -> Vec<u8> {
    // `head` includes the terminating CRLFCRLF; transform the block before it and
    // re-append the separator so the result stays a framed head.
    let block_end = find(head, b"\r\n\r\n").unwrap_or(head.len());
    let block = &head[..block_end];
    let trailer = &head[block_end..];
    let mut lines = block
        .split(|&b| b == b'\n')
        .map(|l| l.strip_suffix(b"\r").unwrap_or(l));
    let Some(status_line) = lines.next() else {
        return head.to_vec();
    };
    let hlines: Vec<&[u8]> = lines.collect();
    let conn = connection_tokens(&hlines);

    let mut out = Vec::with_capacity(head.len() + 32);
    out.extend_from_slice(status_line);
    out.extend_from_slice(b"\r\n");
    out.extend_from_slice(VIA_LINE);
    for line in &hlines {
        let name = header_name_lower(line);
        let drop = RESP_HOP_BY_HOP.iter().any(|h| name == *h) || conn.iter().any(|t| *t == name);
        if !drop {
            out.extend_from_slice(b"\r\n");
            out.extend_from_slice(line);
        }
    }
    out.extend_from_slice(trailer);
    out
}

/// Forward `req` to `addr` over a fresh TCP connection and return the upstream's
/// full response bytes. The connection is opened, the request is written with its
/// hop-by-hop headers stripped ([`strip_hop_by_hop`], RFC 9110 §7.6.1), and the
/// response is read until the upstream signals completion by Content-Length or by
/// closing. This is a REAL socket to a REAL backend — the forward the "no upstream
/// connection" gap was missing.
pub fn forward(addr: SocketAddr, req: &[u8], timeout: Duration) -> std::io::Result<Vec<u8>> {
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(&strip_hop_by_hop(req))?;
    up.flush()?;
    read_response(&mut up)
}

/// Read one full HTTP/1.1 response: headers, then the Content-Length body if
/// present, else to EOF. Enough for a reverse-proxy hop over loopback backends.
fn read_response(sock: &mut TcpStream) -> std::io::Result<Vec<u8>> {
    let mut buf = Vec::with_capacity(4096);
    let mut chunk = [0u8; 16384];
    // 1. Read at least the header block.
    let head_end = loop {
        if let Some(p) = find(&buf, b"\r\n\r\n") {
            break p + 4;
        }
        let n = sock.read(&mut chunk)?;
        if n == 0 {
            return Ok(buf); // closed before a full header block
        }
        buf.extend_from_slice(&chunk[..n]);
    };
    // 2. If Content-Length is given, read exactly that many body bytes; otherwise
    //    read until the peer closes (Connection: close framing).
    match content_length(&buf[..head_end]) {
        Some(clen) => {
            let want = head_end + clen;
            while buf.len() < want {
                let n = sock.read(&mut chunk)?;
                if n == 0 {
                    break;
                }
                buf.extend_from_slice(&chunk[..n]);
            }
        }
        None => loop {
            let n = sock.read(&mut chunk)?;
            if n == 0 {
                break;
            }
            buf.extend_from_slice(&chunk[..n]);
        },
    }
    Ok(buf)
}

pub(crate) fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

pub(crate) fn content_length(head: &[u8]) -> Option<usize> {
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 15 && line[..15].eq_ignore_ascii_case(b"content-length:") {
            let v = trim_ascii(&line[15..]);
            return std::str::from_utf8(v).ok()?.trim().parse().ok();
        }
    }
    None
}

/// Whether the response head declares `Transfer-Encoding: chunked`.
pub(crate) fn is_chunked(head: &[u8]) -> bool {
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 18 && line[..18].eq_ignore_ascii_case(b"transfer-encoding:") {
            let v = trim_ascii(&line[18..]).to_ascii_lowercase();
            return v.windows(7).any(|w| w == b"chunked");
        }
    }
    false
}

/// The outcome of a STREAMED proxy forward: the metadata the host records for a
/// response whose body it wrote straight to the client instead of buffering.
pub struct Streamed {
    /// The response head (status line + headers, through CRLFCRLF) as written to
    /// the client — annotated with the host's connection disposition. The host
    /// reads only the status line off it (metrics / access log).
    pub head: Vec<u8>,
    /// Total bytes written to the client (annotated head + streamed body).
    pub bytes: u64,
    /// Whether the upstream framing lets the client connection stay open
    /// (Content-Length or chunked, AND the request asked for keep-alive, AND the
    /// body streamed to its framed end). A close-delimited body or a mid-stream
    /// error forces the connection closed.
    pub keepalive: bool,
    /// Whether the body reached its framed end with no upstream/client error — a
    /// clean forward, for the circuit breaker.
    pub complete: bool,
}

/// The bounded copy buffer for the streaming body pump: one block held at a time,
/// so peak host memory for a forward is this plus the response head regardless of
/// the upstream body size. A slow client back-pressures the upstream because the
/// next upstream read only happens after the current block is written to the
/// client (TCP flow control on the upstream socket then throttles the backend).
const STREAM_CHUNK: usize = 64 * 1024;

/// A dialled upstream with its response head read and framed: the common starting
/// point of both body pumps (the portable userspace copy and the Linux kernel
/// splice). `buf[..head_end]` is the raw head through CRLFCRLF; `buf[head_end..]`
/// is body over-read while finding it (bounded by one read block).
struct UpstreamHead {
    up: TcpStream,
    buf: Vec<u8>,
    head_end: usize,
    /// The head's `Content-Length`, when declared.
    clen: Option<usize>,
    /// Whether the head declares `Transfer-Encoding: chunked`.
    chunked: bool,
}

/// Dial `addr`, write `req` with its hop-by-hop headers stripped
/// ([`strip_hop_by_hop`], RFC 9110 §7.6.1), and read through the response head
/// (CRLFCRLF). `Err` here means nothing has reached the client yet (dial failure,
/// request-write failure, or the upstream closing before a full head), so the
/// caller may still send a 502.
fn dial_and_read_head(
    addr: SocketAddr,
    req: &[u8],
    timeout: Duration,
    client_ip: &[u8],
) -> std::io::Result<UpstreamHead> {
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(&forward_request(req, client_ip))?;
    up.flush()?;

    // Read the response head. A single read may over-read into the body; those
    // bytes are kept in `buf` past `head_end` for the body pump to write first.
    let mut buf = Vec::with_capacity(4096);
    let mut chunk = [0u8; 16384];
    let head_end = loop {
        if let Some(p) = find(&buf, b"\r\n\r\n") {
            break p + 4;
        }
        let n = up.read(&mut chunk)?;
        if n == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "upstream closed before a full response head",
            ));
        }
        buf.extend_from_slice(&chunk[..n]);
    };
    let clen = content_length(&buf[..head_end]);
    let chunked = is_chunked(&buf[..head_end]);
    Ok(UpstreamHead {
        up,
        buf,
        head_end,
        clen,
        chunked,
    })
}

/// Forward `req` to `addr` and STREAM the upstream response to `client` as it
/// arrives — the head first (so time-to-first-byte tracks the upstream, not the
/// whole body), then the body copied block-by-block with a bounded buffer — rather
/// than reading the whole reply into memory and returning it. The host annotates
/// the head with its keep-alive disposition (never overriding an upstream
/// `Connection` header, preserving the proven serve's header contract), then
/// frames the body by Content-Length, chunked (streamed verbatim up to its
/// terminating zero-chunk), or, with neither, connection close (streamed to EOF).
///
/// This is the portable pump (any `Write` client); on Linux the proxy lane uses
/// [`forward_streaming_spliced`], whose wire output is identical but whose body
/// bytes never enter userspace.
///
/// `Err` is returned ONLY when nothing has reached the client yet (dial failure,
/// request-write failure, or the upstream closing before a full response head) so
/// the caller may still send a 502. Once the head is on the wire a later error
/// just stops the stream and surfaces as `complete = false`; the caller closes the
/// connection rather than corrupting the response already in flight.
#[cfg(not(target_os = "linux"))]
pub fn forward_streaming<W: Write>(
    addr: SocketAddr,
    req: &[u8],
    timeout: Duration,
    keepalive_req: bool,
    client_ip: &[u8],
    client: &mut W,
) -> std::io::Result<Streamed> {
    let mut uh = dial_and_read_head(addr, req, timeout, client_ip)?;

    // Framing + keep-alive disposition from the head.
    let keepalive = keepalive_req && (uh.clen.is_some() || uh.chunked);

    // Annotate the head with the host's connection disposition (only when the
    // upstream states none), then write it. From here a failure is mid-stream.
    let mut head = forward_response_head(&uh.buf[..uh.head_end]);
    crate::http::annotate_connection(&mut head, keepalive);
    if client.write_all(&head).is_err() {
        return Ok(Streamed {
            head,
            bytes: 0,
            keepalive: false,
            complete: false,
        });
    }
    let mut bytes = head.len() as u64;

    // Stream the body per its framing. `leftover` is the body bytes already
    // read while finding the head end.
    let mut chunk = vec![0u8; STREAM_CHUNK];
    let leftover = &uh.buf[uh.head_end..];
    let complete = match uh.clen {
        Some(clen) => stream_fixed(&mut uh.up, client, leftover, clen, &mut chunk, &mut bytes),
        None if uh.chunked => stream_chunked(&mut uh.up, client, leftover, &mut chunk, &mut bytes),
        None => stream_to_eof(&mut uh.up, client, leftover, &mut chunk, &mut bytes),
    };

    Ok(Streamed {
        head,
        bytes,
        keepalive: keepalive && complete,
        complete,
    })
}

/// The kernel-side body relay (Linux): response-body bytes cross
/// upstream-socket → pipe → client-socket entirely inside the kernel via
/// `splice(2)`, never entering this process's address space. The pipe is the
/// mandated middle hop (`splice` requires one end to be a pipe); with
/// `SPLICE_F_MOVE` the kernel forwards page references, not copies. The pipe's
/// capacity plus the drain-before-refill loop preserves the userspace pump's
/// back-pressure: a slow client stalls the pipe drain, which stalls the next
/// upstream fill, and TCP flow control then throttles the backend.
#[cfg(target_os = "linux")]
mod kernel_splice {
    use std::net::TcpStream;
    use std::os::fd::{AsRawFd, RawFd};

    /// Largest single fill request: the default pipe capacity, so one
    /// upstream→pipe fill is always drainable by the pipe→client loop.
    const SPLICE_CHUNK: usize = 64 * 1024;

    /// How a relay pump ended.
    pub(crate) enum Outcome {
        /// The pump ran on the kernel relay; `true` = the body reached its
        /// framed end (all `n` bytes, or a clean upstream EOF).
        Ran(bool),
        /// The very first splice was refused (`EINVAL`/`ENOSYS`) with no byte
        /// moved — this kernel/socket cannot splice; the caller may rerun the
        /// userspace pump from exactly where it stands.
        Unsupported,
    }

    /// One kernel pipe pair, the splice relay for a single response body.
    /// Both ends are closed on drop.
    pub(crate) struct Relay {
        r: RawFd,
        w: RawFd,
    }

    thread_local! {
        /// One idle splice relay parked per connection thread, reused across
        /// proxied forwards so the common path costs no `pipe2`/`close(2)` per
        /// request — the pipe is a per-thread fixture, not a per-forward one.
        /// INVARIANT: only a relay whose pipe is known-EMPTY is ever parked here
        /// (a clean forward that drained every byte, or one that never spliced a
        /// byte at all). A relay left holding undrained body bytes is dropped, so
        /// stale bytes can never prepend to the next response ([`Relay::release`]).
        static IDLE_RELAY: std::cell::RefCell<Option<Relay>> =
            const { std::cell::RefCell::new(None) };
    }

    impl Relay {
        pub(crate) fn new() -> Option<Relay> {
            let mut fds = [0i32; 2];
            if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
                return None;
            }
            Some(Relay {
                r: fds[0],
                w: fds[1],
            })
        }

        /// The thread's parked relay, or a fresh pipe when none is parked. `None`
        /// only when `pipe2` itself fails. The common (keep-alive) case reuses the
        /// same pipe across every forward on the connection with zero syscalls.
        pub(crate) fn acquire() -> Option<Relay> {
            IDLE_RELAY
                .with(|c| c.borrow_mut().take())
                .or_else(Relay::new)
        }

        /// Park this relay for the thread's next forward. CALLER CONTRACT: only
        /// call this when the pipe is empty — a clean `Outcome::Ran(true)` (every
        /// filled byte was drained) or an `Outcome::Unsupported` (no byte was ever
        /// spliced). A relay from a mid-body failure (`Ran(false)`) may still hold
        /// undrained bytes and must be DROPPED instead, never parked.
        pub(crate) fn release(self) {
            IDLE_RELAY.with(|c| {
                let mut slot = c.borrow_mut();
                if slot.is_none() {
                    *slot = Some(self);
                }
                // A relay is already parked (nested forward): drop this extra —
                // its `Drop` closes the pipe.
            });
        }

        /// One `splice(2)`, EINTR-retried: move up to `n` bytes from `from` to
        /// `to` without lifting them into userspace. `Ok(0)` = EOF on `from`.
        fn splice_once(from: RawFd, to: RawFd, n: usize) -> std::io::Result<usize> {
            loop {
                let rc = unsafe {
                    libc::splice(
                        from,
                        std::ptr::null_mut(),
                        to,
                        std::ptr::null_mut(),
                        n,
                        libc::SPLICE_F_MOVE | libc::SPLICE_F_MORE,
                    )
                };
                if rc >= 0 {
                    return Ok(rc as usize);
                }
                let e = std::io::Error::last_os_error();
                if e.kind() != std::io::ErrorKind::Interrupted {
                    return Err(e);
                }
            }
        }

        fn unsupported(e: &std::io::Error) -> bool {
            matches!(e.raw_os_error(), Some(libc::EINVAL) | Some(libc::ENOSYS))
        }

        /// Drain exactly `in_pipe` bytes pipe→client. `false` = the client side
        /// failed mid-body.
        fn drain(&self, client: RawFd, mut in_pipe: usize, bytes: &mut u64) -> bool {
            while in_pipe > 0 {
                match Self::splice_once(self.r, client, in_pipe) {
                    Ok(0) | Err(_) => return false,
                    Ok(m) => {
                        *bytes += m as u64;
                        in_pipe -= m;
                    }
                }
            }
            true
        }

        /// Move exactly `remaining` bytes upstream→client through the pipe (the
        /// Content-Length framing). `Ran(false)` covers an upstream that
        /// truncated the body, a timeout, and a client that stopped reading —
        /// the same cases the userspace pump reports as incomplete.
        pub(crate) fn move_exact(
            &self,
            up: &TcpStream,
            client: &TcpStream,
            mut remaining: usize,
            bytes: &mut u64,
        ) -> Outcome {
            let (uf, cf) = (up.as_raw_fd(), client.as_raw_fd());
            let mut first = true;
            while remaining > 0 {
                let filled = match Self::splice_once(uf, self.w, remaining.min(SPLICE_CHUNK)) {
                    Ok(0) => return Outcome::Ran(false), // upstream truncated the body
                    Ok(n) => n,
                    Err(e) if first && Self::unsupported(&e) => return Outcome::Unsupported,
                    Err(_) => return Outcome::Ran(false),
                };
                first = false;
                if !self.drain(cf, filled, bytes) {
                    return Outcome::Ran(false);
                }
                remaining -= filled;
            }
            Outcome::Ran(true)
        }

        /// Move bytes upstream→client until the upstream signals EOF (the
        /// close-delimited framing). `Ran(true)` = clean EOF reached.
        pub(crate) fn move_to_eof(
            &self,
            up: &TcpStream,
            client: &TcpStream,
            bytes: &mut u64,
        ) -> Outcome {
            let (uf, cf) = (up.as_raw_fd(), client.as_raw_fd());
            let mut first = true;
            loop {
                let filled = match Self::splice_once(uf, self.w, SPLICE_CHUNK) {
                    Ok(0) => return Outcome::Ran(true), // upstream closed: complete
                    Ok(n) => n,
                    Err(e) if first && Self::unsupported(&e) => return Outcome::Unsupported,
                    Err(_) => return Outcome::Ran(false),
                };
                first = false;
                if !self.drain(cf, filled, bytes) {
                    return Outcome::Ran(false);
                }
            }
        }
    }

    impl Drop for Relay {
        fn drop(&mut self) {
            unsafe {
                libc::close(self.r);
                libc::close(self.w);
            }
        }
    }
}

/// The L4 verbatim pump, kernel-side: move bytes `from` → `to` until EOF on
/// `from` via the splice relay. Returns `false` only when the relay could not
/// run at all (no pipe, or splice refused before any byte moved), so the caller
/// may fall back to its userspace copy from byte 0; a mid-stream failure ends
/// the direction exactly as a userspace copy error would, and returns `true`.
#[cfg(target_os = "linux")]
pub(crate) fn splice_to_eof(from: &TcpStream, to: &TcpStream) -> bool {
    let mut bytes = 0u64;
    match kernel_splice::Relay::new().map(|r| r.move_to_eof(from, to, &mut bytes)) {
        Some(kernel_splice::Outcome::Ran(_)) => true,
        Some(kernel_splice::Outcome::Unsupported) | None => false,
    }
}

/// The streaming proxy forward with the response BODY moved by `splice(2)`
/// (Linux, plaintext-TCP client): the head is still read, framed, and
/// connection-annotated in userspace — the host must see it to know the body's
/// framing and the connection disposition — but the body bytes flow
/// upstream-socket → pipe → client-socket entirely inside the kernel, never
/// entering this process. The wire output is byte-identical to the portable
/// pump's; only the copy path changes.
///
/// Two body classes stay in userspace, by necessity:
/// * head over-read — bytes past CRLFCRLF that arrived in the head's last read
///   block are already in this process and are written out before the relay
///   takes over (bounded by one 16 KiB read block);
/// * chunked bodies — the terminating zero-chunk must be SEEN to keep the
///   client connection alive, and splice cannot inspect what it moves, so
///   chunked framing keeps the bounded userspace pump.
///
/// Same `Err` contract as the portable pump: `Err` only while nothing has
/// reached the client, so the caller may still send a 502.
#[cfg(target_os = "linux")]
pub fn forward_streaming_spliced(
    addr: SocketAddr,
    req: &[u8],
    timeout: Duration,
    keepalive_req: bool,
    client_ip: &[u8],
    client: &mut TcpStream,
) -> std::io::Result<Streamed> {
    let mut uh = dial_and_read_head(addr, req, timeout, client_ip)?;

    // Framing + keep-alive disposition, and the annotated head, exactly as the
    // portable pump computes them.
    let keepalive = keepalive_req && (uh.clen.is_some() || uh.chunked);
    let mut head = forward_response_head(&uh.buf[..uh.head_end]);
    crate::http::annotate_connection(&mut head, keepalive);
    if client.write_all(&head).is_err() {
        return Ok(Streamed {
            head,
            bytes: 0,
            keepalive: false,
            complete: false,
        });
    }
    let mut bytes = head.len() as u64;
    let leftover = &uh.buf[uh.head_end..];

    let complete = match uh.clen {
        // Content-Length body: leftover in userspace (already read), the
        // remainder kernel-side.
        Some(clen) => {
            let take = leftover.len().min(clen);
            if take > 0 && client.write_all(&leftover[..take]).is_err() {
                false
            } else {
                bytes += take as u64;
                let remaining = clen - take;
                if remaining == 0 {
                    true
                } else {
                    match kernel_splice::Relay::acquire() {
                        Some(r) => match r.move_exact(&uh.up, client, remaining, &mut bytes) {
                            // Clean run: the pipe drained empty — park it for reuse.
                            kernel_splice::Outcome::Ran(true) => {
                                r.release();
                                true
                            }
                            // Mid-body failure: the pipe may hold undrained bytes,
                            // so `r` is dropped (its pipe closed), never parked.
                            kernel_splice::Outcome::Ran(false) => false,
                            // Splice refused before any byte moved: the pipe is
                            // empty and reusable; fall back to the userspace pump.
                            kernel_splice::Outcome::Unsupported => {
                                r.release();
                                let mut chunk = vec![0u8; STREAM_CHUNK];
                                stream_fixed(
                                    &mut uh.up,
                                    client,
                                    &[],
                                    remaining,
                                    &mut chunk,
                                    &mut bytes,
                                )
                            }
                        },
                        None => {
                            let mut chunk = vec![0u8; STREAM_CHUNK];
                            stream_fixed(&mut uh.up, client, &[], remaining, &mut chunk, &mut bytes)
                        }
                    }
                }
            }
        }
        // Chunked body: framing must be inspected for its terminator, which
        // splice cannot do — the bounded userspace pump carries it.
        None if uh.chunked => {
            let mut chunk = vec![0u8; STREAM_CHUNK];
            stream_chunked(&mut uh.up, client, leftover, &mut chunk, &mut bytes)
        }
        // Close-delimited body: kernel-side to upstream EOF.
        None => {
            if !leftover.is_empty() && client.write_all(leftover).is_err() {
                false
            } else {
                bytes += leftover.len() as u64;
                match kernel_splice::Relay::acquire() {
                    Some(r) => match r.move_to_eof(&uh.up, client, &mut bytes) {
                        // Clean EOF: the pipe drained empty — park it for reuse.
                        kernel_splice::Outcome::Ran(true) => {
                            r.release();
                            true
                        }
                        // Mid-body failure: the pipe may hold undrained bytes, so
                        // `r` is dropped (its pipe closed), never parked.
                        kernel_splice::Outcome::Ran(false) => false,
                        // Splice refused before any byte moved: pipe empty and
                        // reusable; fall back to the userspace pump.
                        kernel_splice::Outcome::Unsupported => {
                            r.release();
                            let mut chunk = vec![0u8; STREAM_CHUNK];
                            stream_to_eof(&mut uh.up, client, &[], &mut chunk, &mut bytes)
                        }
                    },
                    None => {
                        let mut chunk = vec![0u8; STREAM_CHUNK];
                        stream_to_eof(&mut uh.up, client, &[], &mut chunk, &mut bytes)
                    }
                }
            }
        }
    };

    Ok(Streamed {
        head,
        bytes,
        keepalive: keepalive && complete,
        complete,
    })
}

/// Stream exactly `clen` body bytes from `up` to `client`, starting with the
/// already-read `leftover`. Returns whether the full body was delivered.
fn stream_fixed<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    clen: usize,
    chunk: &mut [u8],
    bytes: &mut u64,
) -> bool {
    let mut remaining = clen;
    let take = leftover.len().min(remaining);
    if take > 0 {
        if client.write_all(&leftover[..take]).is_err() {
            return false;
        }
        *bytes += take as u64;
        remaining -= take;
    }
    while remaining > 0 {
        let n = match up.read(chunk) {
            Ok(0) => return false, // upstream truncated the body
            Ok(n) => n,
            Err(_) => return false,
        };
        let w = n.min(remaining);
        if client.write_all(&chunk[..w]).is_err() {
            return false;
        }
        *bytes += w as u64;
        remaining -= w;
    }
    true
}

/// Stream a close-delimited body (no Content-Length, not chunked) to EOF. The
/// connection cannot be kept alive, but events are forwarded as they arrive — an
/// upstream that drips (e.g. `text/event-stream`) reaches the client incrementally.
fn stream_to_eof<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    chunk: &mut [u8],
    bytes: &mut u64,
) -> bool {
    if !leftover.is_empty() {
        if client.write_all(leftover).is_err() {
            return false;
        }
        *bytes += leftover.len() as u64;
    }
    loop {
        let n = match up.read(chunk) {
            Ok(0) => return true, // upstream closed: the response is complete
            Ok(n) => n,
            Err(_) => return false,
        };
        if client.write_all(&chunk[..n]).is_err() {
            return false;
        }
        *bytes += n as u64;
    }
}

/// Stream a chunked body verbatim to the client, parsing a copy just enough to
/// detect the terminating zero-chunk so the client connection can stay open
/// without waiting for the upstream to close. Same bounded buffer / back-pressure
/// as the fixed path. Returns whether the terminator was reached cleanly.
fn stream_chunked<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    chunk: &mut [u8],
    bytes: &mut u64,
) -> bool {
    let mut parser = ChunkedParser::new();
    if !leftover.is_empty() {
        if client.write_all(leftover).is_err() {
            return false;
        }
        *bytes += leftover.len() as u64;
        if parser.advance(leftover) {
            return true;
        }
    }
    loop {
        let n = match up.read(chunk) {
            Ok(0) => return false, // upstream closed before the terminating chunk
            Ok(n) => n,
            Err(_) => return false,
        };
        if client.write_all(&chunk[..n]).is_err() {
            return false;
        }
        *bytes += n as u64;
        if parser.advance(&chunk[..n]) {
            return true;
        }
    }
}

/// An incremental HTTP/1.1 chunked-transfer parser. It never buffers the body; it
/// only tracks enough state across streamed blocks to report when the terminating
/// zero-length chunk (and its trailer/CRLF) has been fully seen.
pub(crate) struct ChunkedParser {
    st: ChunkSt,
    size: usize,
}

enum ChunkSt {
    /// Reading the chunk-size hex line; `size` accumulates.
    Size,
    /// In a chunk extension (`;…`) on the size line — skip to CR.
    SizeExt,
    /// Saw the CR of the size line; the next byte is its LF.
    SizeCr,
    /// Consuming this many remaining data bytes of the current chunk.
    Data(usize),
    /// After the chunk data, the CR of its trailing CRLF.
    DataCr,
    /// After the chunk-data CR, its LF.
    DataLf,
    /// Start of a trailer line after the last-chunk (or the final CRLF).
    TrailerStart,
    /// Within a trailer line, before its CR.
    TrailerLine,
    /// Saw the CR of a trailer line; the next byte is its LF.
    TrailerLineCr,
    /// Saw the CR of the final empty line; the next byte is its LF → done.
    TrailerFinalCr,
    /// The terminating zero-chunk has been fully consumed.
    Done,
}

impl ChunkedParser {
    pub(crate) fn new() -> Self {
        ChunkedParser {
            st: ChunkSt::Size,
            size: 0,
        }
    }

    /// Advance the parser over `data`. Returns `true` once the terminating
    /// zero-chunk (with any trailers and the final CRLF) has been consumed.
    pub(crate) fn advance(&mut self, data: &[u8]) -> bool {
        let mut i = 0;
        while i < data.len() {
            match self.st {
                ChunkSt::Size => {
                    let b = data[i];
                    match b {
                        b'0'..=b'9' => {
                            self.size = self.size * 16 + (b - b'0') as usize;
                            i += 1;
                        }
                        b'a'..=b'f' => {
                            self.size = self.size * 16 + (b - b'a' + 10) as usize;
                            i += 1;
                        }
                        b'A'..=b'F' => {
                            self.size = self.size * 16 + (b - b'A' + 10) as usize;
                            i += 1;
                        }
                        b'\r' => {
                            self.st = ChunkSt::SizeCr;
                            i += 1;
                        }
                        b';' => {
                            self.st = ChunkSt::SizeExt;
                            i += 1;
                        }
                        _ => i += 1, // tolerate stray whitespace on the size line
                    }
                }
                ChunkSt::SizeExt => {
                    if data[i] == b'\r' {
                        self.st = ChunkSt::SizeCr;
                    }
                    i += 1;
                }
                ChunkSt::SizeCr => {
                    i += 1; // consume the LF
                    self.st = if self.size == 0 {
                        ChunkSt::TrailerStart
                    } else {
                        ChunkSt::Data(self.size)
                    };
                }
                ChunkSt::Data(n) => {
                    let take = n.min(data.len() - i);
                    i += take;
                    let left = n - take;
                    self.st = if left == 0 {
                        ChunkSt::DataCr
                    } else {
                        ChunkSt::Data(left)
                    };
                }
                ChunkSt::DataCr => {
                    i += 1; // consume the CR after the chunk data
                    self.st = ChunkSt::DataLf;
                }
                ChunkSt::DataLf => {
                    i += 1; // consume the LF
                    self.size = 0;
                    self.st = ChunkSt::Size;
                }
                ChunkSt::TrailerStart => {
                    if data[i] == b'\r' {
                        self.st = ChunkSt::TrailerFinalCr;
                        i += 1;
                    } else {
                        self.st = ChunkSt::TrailerLine;
                    }
                }
                ChunkSt::TrailerLine => {
                    if data[i] == b'\r' {
                        self.st = ChunkSt::TrailerLineCr;
                    }
                    i += 1;
                }
                ChunkSt::TrailerLineCr => {
                    i += 1; // consume the LF ending a trailer line
                    self.st = ChunkSt::TrailerStart;
                }
                ChunkSt::TrailerFinalCr => {
                    // The final LF closes the terminating zero-chunk; the response
                    // is done and any bytes past it belong to no more of this reply.
                    self.st = ChunkSt::Done;
                    return true;
                }
                ChunkSt::Done => return true,
            }
        }
        matches!(self.st, ChunkSt::Done)
    }
}

/// A `502 Bad Gateway` response (the chosen backend could not be reached).
pub fn bad_gateway() -> Vec<u8> {
    b"HTTP/1.1 502 Bad Gateway\r\nContent-Length: 11\r\nConnection: close\r\n\r\nbad gateway"
        .to_vec()
}

/// A `504 Gateway Timeout` response: the chosen backend accepted the connection
/// but did not return a valid response head within the dial timeout (distinct from
/// a `502` connect/forward failure). Mirrors `Reactor.ProxyForward.gatewayError true`.
pub fn gateway_timeout() -> Vec<u8> {
    b"HTTP/1.1 504 Gateway Timeout\r\nContent-Length: 15\r\nConnection: close\r\n\r\ngateway timeout"
        .to_vec()
}

/// A `503 Service Unavailable` response (no backend is eligible — every backend
/// down or breaker-open, so the proven pick returned nothing).
pub fn service_unavailable() -> Vec<u8> {
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Length: 19\r\nConnection: close\r\n\r\nno healthy upstream"
        .to_vec()
}

/// What the host records after a STREAMED proxy hop: the response head (status
/// line for metrics / the access log), the total bytes written, whether the
/// client connection may stay open, and the dialled backend (for the log / metric
/// per-backend counter). The body itself was already written straight to the
/// client by [`forward_streaming`], never buffered.
pub struct StreamOutcome {
    pub head: Vec<u8>,
    pub bytes: u64,
    pub keepalive: bool,
    pub backend: Option<String>,
}

/// The whole streaming reverse-proxy hop for one request: the proven pick +
/// breaker + sticky-affinity discipline around a caller-supplied forward. The
/// backend is ALWAYS the proven pick's; this function never selects.
///
/// It writes the whole response (a streamed upstream reply, or a 502/503 when no
/// backend is eligible / reachable) to `client` and returns the [`StreamOutcome`]
/// the host records. `Err` is only the case where a client write failed and the
/// connection must be dropped.
fn handle_streaming_via<P, W, F>(
    req: &[u8],
    fleet: &Fleet,
    client: &mut W,
    pick: P,
    forward_via: F,
) -> std::io::Result<StreamOutcome>
where
    P: Fn(u8, &[u8]) -> Option<u32>,
    W: Write,
    F: FnOnce(SocketAddr, &[u8], Duration, &mut W) -> std::io::Result<Streamed>,
{
    let key = sticky_key(req);
    let id = match pick(fleet.mask(), &key) {
        Some(id) => id,
        None => {
            let resp = service_unavailable();
            client.write_all(&resp)?;
            return Ok(StreamOutcome {
                bytes: resp.len() as u64,
                head: resp,
                keepalive: false,
                backend: None,
            });
        }
    };
    let addr = match fleet.addr(id) {
        Some(a) => a,
        None => {
            let resp = bad_gateway();
            client.write_all(&resp)?;
            return Ok(StreamOutcome {
                bytes: resp.len() as u64,
                head: resp,
                keepalive: false,
                backend: None,
            });
        }
    };
    fleet.inflight_inc(id);
    let out = forward_via(addr, req, fleet.dial_timeout, client);
    fleet.inflight_dec(id);
    match out {
        Ok(s) => {
            // A clean forward closes the breaker; a mid-stream truncation counts
            // as a failure, the same as a buffered forward that errored.
            if s.complete {
                fleet.record_success(id);
            } else {
                fleet.record_failure(id);
            }
            Ok(StreamOutcome {
                head: s.head,
                bytes: s.bytes,
                keepalive: s.keepalive,
                backend: Some(addr.to_string()),
            })
        }
        Err(e) => {
            // Nothing reached the client yet (dial / no valid response head): the
            // breaker takes the failure. A read/connect timeout is a 504 Gateway
            // Timeout (the upstream accepted but did not answer in time); any other
            // failure is a 502 Bad Gateway (RFC 9110 §15.6.5 / §15.6.3, mirrors
            // `Reactor.ProxyForward.gatewayError`).
            fleet.record_failure(id);
            let resp = if matches!(
                e.kind(),
                std::io::ErrorKind::TimedOut | std::io::ErrorKind::WouldBlock
            ) {
                gateway_timeout()
            } else {
                bad_gateway()
            };
            client.write_all(&resp)?;
            Ok(StreamOutcome {
                bytes: resp.len() as u64,
                head: resp,
                keepalive: false,
                backend: None,
            })
        }
    }
}

/// The streaming reverse-proxy hop for a plaintext-TCP client. On Linux the
/// response BODY moves kernel-side ([`forward_streaming_spliced`]): upstream
/// socket → pipe → client socket, no userspace copy. Elsewhere it is the
/// portable bounded-buffer pump ([`forward_streaming`]). The wire bytes are the
/// same either way; the proven pick / breaker / affinity discipline is
/// [`handle_streaming_via`]'s, unchanged.
pub fn handle_streaming_tcp<P>(
    req: &[u8],
    keepalive_req: bool,
    fleet: &Fleet,
    client: &mut TcpStream,
    pick: P,
) -> std::io::Result<StreamOutcome>
where
    P: Fn(u8, &[u8]) -> Option<u32>,
{
    // The originating client address for `X-Forwarded-For` (RFC 9110 §7.6.2).
    let client_ip = client
        .peer_addr()
        .map(|a| a.ip().to_string().into_bytes())
        .unwrap_or_default();
    #[cfg(target_os = "linux")]
    {
        handle_streaming_via(req, fleet, client, pick, |addr, req, timeout, client| {
            forward_streaming_spliced(addr, req, timeout, keepalive_req, &client_ip, client)
        })
    }
    #[cfg(not(target_os = "linux"))]
    {
        handle_streaming_via(req, fleet, client, pick, |addr, req, timeout, client| {
            forward_streaming(addr, req, timeout, keepalive_req, &client_ip, client)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_fleet_spec_and_mask() {
        let f = Fleet::parse(
            "0=127.0.0.1:9400,2=127.0.0.1:9402",
            3,
            Duration::from_millis(50),
        )
        .unwrap();
        assert_eq!(f.mask(), 0b101);
        assert_eq!(f.addr(0), Some("127.0.0.1:9400".parse().unwrap()));
        assert_eq!(f.addr(1), None);
    }

    #[test]
    fn breaker_opens_after_threshold() {
        let f = Fleet::parse("1=127.0.0.1:9401", 2, Duration::from_millis(50)).unwrap();
        assert_eq!(f.mask(), 0b010);
        f.record_failure(1);
        assert_eq!(f.mask(), 0b010); // one failure: still up
        f.record_failure(1);
        assert_eq!(f.mask(), 0b000); // threshold: breaker open, bit cleared
        f.record_success(1);
        assert_eq!(f.mask(), 0b010); // success closes the breaker
    }

    /// Byte-parity with the proven `Reactor.ProxyForward.demo_strip`: the SAME
    /// request and SAME expected forwarded bytes the Lean `demo_strip` proves —
    /// `Connection` (fixed hop), `Keep-Alive` (fixed hop), and `X-Trace` (a
    /// `Connection`-named token) removed; `Host`, `Accept`, and body kept verbatim.
    #[test]
    fn strips_hop_by_hop_request_headers() {
        let req = b"GET /api HTTP/1.1\r\nHost: e.x\r\nConnection: keep-alive, X-Trace\r\nX-Trace: abc\r\nKeep-Alive: timeout=5\r\nAccept: */*\r\n\r\nBODY";
        let want = b"GET /api HTTP/1.1\r\nHost: e.x\r\nAccept: */*\r\n\r\nBODY";
        assert_eq!(strip_hop_by_hop(req), want.to_vec());

        // No hop-by-hop headers present: the request is unchanged.
        let plain = b"GET /api HTTP/1.1\r\nHost: e.x\r\nAccept: */*\r\n\r\nBODY";
        assert_eq!(strip_hop_by_hop(plain), plain.to_vec());

        // Case-insensitive names and the body pass through untouched.
        let mixed = b"POST /api HTTP/1.1\r\nHost: e.x\r\nTRANSFER-ENCODING: chunked\r\nContent-Length: 3\r\n\r\nabc";
        let want_mixed = b"POST /api HTTP/1.1\r\nHost: e.x\r\nContent-Length: 3\r\n\r\nabc";
        assert_eq!(strip_hop_by_hop(mixed), want_mixed.to_vec());
    }

    /// Byte-parity with the proven `Reactor.ProxyForward.demo_forward_req`: the
    /// forwarded request strips hop-by-hop, adds `Via`, and adds `X-Forwarded-For`
    /// when a client address is known — the SAME bytes the Lean `demo_forward_req`
    /// proves.
    #[test]
    fn forward_request_matches_proven_demo() {
        let req = b"GET / HTTP/1.1\r\nConnection: keep-alive\r\nHost: x\r\n\r\nBODY";
        let want =
            b"GET / HTTP/1.1\r\nVia: 1.1 drorb\r\nX-Forwarded-For: 1.2.3.4\r\nHost: x\r\n\r\nBODY";
        assert_eq!(forward_request(req, b"1.2.3.4"), want.to_vec());
        // No known client address: Via added, X-Forwarded-For omitted.
        let want_noip = b"GET / HTTP/1.1\r\nVia: 1.1 drorb\r\nHost: x\r\n\r\nBODY";
        assert_eq!(forward_request(req, b""), want_noip.to_vec());
        // Proxy-Connection (legacy hop-by-hop) is stripped too.
        let pc = b"GET / HTTP/1.1\r\nProxy-Connection: keep-alive\r\nHost: x\r\n\r\n";
        let out = forward_request(pc, b"");
        assert!(
            !out.windows(b"proxy-connection".len())
                .any(|w| w.eq_ignore_ascii_case(b"proxy-connection"))
        );
    }

    /// Byte-parity with the proven `Reactor.ProxyForward.demo_forward_resp`: the
    /// response head strips hop-by-hop, PRESERVES `Transfer-Encoding` (framing), and
    /// adds `Via` — the SAME block bytes the Lean `demo_forward_resp` proves (with
    /// the CRLFCRLF separator re-appended).
    #[test]
    fn forward_response_head_matches_proven_demo() {
        let head = b"HTTP/1.1 200 OK\r\nConnection: close\r\nKeep-Alive: timeout=5\r\nTransfer-Encoding: chunked\r\nETag: \"z\"\r\n\r\n";
        let want = b"HTTP/1.1 200 OK\r\nVia: 1.1 drorb\r\nTransfer-Encoding: chunked\r\nETag: \"z\"\r\n\r\n";
        assert_eq!(forward_response_head(head), want.to_vec());
    }

    #[test]
    fn detects_proxy_path_and_sticky_key() {
        assert!(is_proxy_path(b"GET /api/users HTTP/1.1\r\nHost: x\r\n\r\n"));
        assert!(is_proxy_path(b"GET /api HTTP/1.1\r\n\r\n"));
        assert!(!is_proxy_path(b"GET /health HTTP/1.1\r\n\r\n"));
        assert_eq!(
            sticky_key(b"GET /api HTTP/1.1\r\nCookie: a=1; sid=SESSION42; b=2\r\n\r\n"),
            b"SESSION42".to_vec()
        );
        assert_eq!(
            sticky_key(b"GET /api/x HTTP/1.1\r\nHost: y\r\n\r\n"),
            b"/api/x".to_vec()
        );
    }

    #[test]
    fn chunked_parser_detects_terminator() {
        // Two data chunks then the last-chunk with no trailers.
        let body = b"5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n";
        let mut p = ChunkedParser::new();
        assert!(p.advance(body));

        // Split across feeds: the terminator must be detected on the last feed.
        let mut p = ChunkedParser::new();
        assert!(!p.advance(b"5\r\nhel"));
        assert!(!p.advance(b"lo\r\n0\r\n"));
        assert!(p.advance(b"\r\n"));

        // A trailer line before the final CRLF is consumed too.
        let mut p = ChunkedParser::new();
        assert!(p.advance(b"0\r\nX-Trailer: v\r\n\r\n"));

        // An unterminated stream is not "done".
        let mut p = ChunkedParser::new();
        assert!(!p.advance(b"5\r\nhello\r\n"));
    }

    #[test]
    fn detects_chunked_and_content_length() {
        assert!(is_chunked(
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"
        ));
        assert!(is_chunked(
            b"HTTP/1.1 200 OK\r\ntransfer-encoding: gzip, chunked\r\n\r\n"
        ));
        assert!(!is_chunked(b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n\r\n"));
        assert_eq!(
            content_length(b"HTTP/1.1 200 OK\r\nContent-Length: 42\r\n\r\n"),
            Some(42)
        );
    }

    /// Byte-identity harness for the spliced forward (Linux): a canned upstream
    /// response on a real loopback socket, a real loopback client pair, and the
    /// exact bytes the client end received. The canned head states its own
    /// `Connection`, so the host's annotation adds nothing and the expected
    /// client bytes are the upstream bytes verbatim.
    /// The bytes the client SHOULD receive for a given upstream response: the head
    /// run through the proven response transform ([`forward_response_head`] — strip
    /// hop-by-hop, add `Via`) and connection-annotated for the host's keep-alive
    /// decision, followed by the upstream body VERBATIM. The proxy transforms only
    /// the head; the body is byte-identical to the upstream's.
    #[cfg(target_os = "linux")]
    fn expected_client(canned: &[u8], keepalive: bool) -> Vec<u8> {
        let he = find(canned, b"\r\n\r\n").unwrap() + 4;
        let mut head = forward_response_head(&canned[..he]);
        crate::http::annotate_connection(&mut head, keepalive);
        [head, canned[he..].to_vec()].concat()
    }

    #[cfg(target_os = "linux")]
    fn spliced_roundtrip(canned: Vec<u8>) -> (Streamed, Vec<u8>) {
        use std::net::TcpListener;

        let up_l = TcpListener::bind("127.0.0.1:0").unwrap();
        let up_addr = up_l.local_addr().unwrap();
        let canned_srv = canned.clone();
        let up_thread = std::thread::spawn(move || {
            let (mut s, _) = up_l.accept().unwrap();
            let mut req = [0u8; 4096];
            let _ = s.read(&mut req);
            s.write_all(&canned_srv).unwrap();
        });

        let cl_l = TcpListener::bind("127.0.0.1:0").unwrap();
        let mut client_near = TcpStream::connect(cl_l.local_addr().unwrap()).unwrap();
        let (mut client_far, _) = cl_l.accept().unwrap();
        let collector = std::thread::spawn(move || {
            let mut got = Vec::new();
            client_far.read_to_end(&mut got).unwrap();
            got
        });

        let out = forward_streaming_spliced(
            up_addr,
            b"GET /api/x HTTP/1.1\r\nHost: t\r\n\r\n",
            Duration::from_secs(5),
            true,
            b"127.0.0.1",
            &mut client_near,
        )
        .unwrap();
        drop(client_near); // EOF so the collector's read_to_end returns
        up_thread.join().unwrap();
        (out, collector.join().unwrap())
    }

    /// Content-Length body across several splice chunks: the client receives the
    /// upstream bytes verbatim, and the forward reports complete + keepalive.
    #[cfg(target_os = "linux")]
    #[test]
    fn spliced_fixed_body_is_byte_identical() {
        let body: Vec<u8> = (0..300_000u32)
            .map(|i| (i.wrapping_mul(31) % 251) as u8)
            .collect();
        let head = format!(
            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: keep-alive\r\n\r\n",
            body.len()
        );
        let canned = [head.as_bytes(), &body].concat();
        let (out, got) = spliced_roundtrip(canned.clone());
        let expect = expected_client(&canned, true);
        assert!(out.complete);
        assert!(out.keepalive);
        assert_eq!(out.bytes, expect.len() as u64);
        assert_eq!(
            got, expect,
            "spliced client bytes differ from the transformed response"
        );
    }

    /// Close-delimited body (no Content-Length, not chunked): spliced to
    /// upstream EOF, verbatim, and the connection is marked not-keepalive.
    #[cfg(target_os = "linux")]
    #[test]
    fn spliced_close_delimited_body_is_byte_identical() {
        let body: Vec<u8> = (0..150_000u32)
            .map(|i| (i.wrapping_mul(17) % 253) as u8)
            .collect();
        let canned = [
            b"HTTP/1.1 200 OK\r\nConnection: close\r\n\r\n".as_slice(),
            &body,
        ]
        .concat();
        let (out, got) = spliced_roundtrip(canned.clone());
        assert!(out.complete);
        assert!(!out.keepalive);
        assert_eq!(
            got,
            expected_client(&canned, false),
            "spliced client bytes differ from the transformed response"
        );
    }

    /// Chunked body: stays on the userspace pump (its terminator must be seen),
    /// still verbatim on the wire and keepalive-preserving.
    #[cfg(target_os = "linux")]
    #[test]
    fn spliced_entry_chunked_body_is_byte_identical() {
        let canned = b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n".to_vec();
        let (out, got) = spliced_roundtrip(canned.clone());
        assert!(out.complete);
        assert!(out.keepalive);
        assert_eq!(
            got,
            expected_client(&canned, true),
            "chunked fallback client bytes differ from the transformed response"
        );
    }

    /// The pooled splice relay is REUSED across sequential forwards on one thread
    /// (a kept-alive connection's successive proxied replies): every forward must
    /// still be byte-identical to its upstream, proving the parked pipe carries no
    /// stale bytes from the prior forward. Distinct bodies each round rule out a
    /// pipe left dirty between reuses.
    #[cfg(target_os = "linux")]
    #[test]
    fn pooled_relay_reuse_is_byte_identical() {
        for round in 0..4u32 {
            // Distinct fixed-length body each round, spanning several splice fills.
            let seed = 13u32.wrapping_add(round * 7);
            let body: Vec<u8> = (0..200_003u32)
                .map(|i| (i.wrapping_mul(seed).wrapping_add(round) % 251) as u8)
                .collect();
            let head = format!(
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: keep-alive\r\n\r\n",
                body.len()
            );
            let canned = [head.as_bytes(), &body].concat();
            let (out, got) = spliced_roundtrip(canned.clone());
            let expect = expected_client(&canned, true);
            assert!(out.complete, "round {round}: forward not complete");
            assert!(out.keepalive, "round {round}: keep-alive lost");
            assert_eq!(out.bytes, expect.len() as u64, "round {round}: byte count");
            assert_eq!(
                got, expect,
                "round {round}: pooled-relay client bytes differ from the transformed response"
            );
        }
    }

    /// A close-delimited (EOF-framed) forward followed by a fixed-length one, on
    /// the same thread: the EOF path parks the relay after a clean drain, and the
    /// next forward reuses it byte-identically — the two framings share one pipe.
    #[cfg(target_os = "linux")]
    #[test]
    fn pooled_relay_reuse_across_framings() {
        let eof_body: Vec<u8> = (0..120_000u32)
            .map(|i| (i.wrapping_mul(53) % 249) as u8)
            .collect();
        let eof_canned = [
            b"HTTP/1.1 200 OK\r\nConnection: close\r\n\r\n".as_slice(),
            &eof_body,
        ]
        .concat();
        let (o1, g1) = spliced_roundtrip(eof_canned.clone());
        assert!(o1.complete && !o1.keepalive);
        assert_eq!(g1, expected_client(&eof_canned, false));

        let fx_body: Vec<u8> = (0..90_000u32)
            .map(|i| (i.wrapping_mul(29) % 251) as u8)
            .collect();
        let fx_canned = [
            format!(
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: keep-alive\r\n\r\n",
                fx_body.len()
            )
            .as_bytes(),
            &fx_body,
        ]
        .concat();
        let (o2, g2) = spliced_roundtrip(fx_canned.clone());
        assert!(o2.complete && o2.keepalive);
        assert_eq!(
            g2,
            expected_client(&fx_canned, true),
            "reused-across-framings client bytes differ from the transformed response"
        );
    }
}
