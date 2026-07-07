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
            .spawn(move || loop {
                self.probe_once();
                std::thread::sleep(interval);
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

/// Forward `req` to `addr` over a fresh TCP connection and return the upstream's
/// full response bytes. The connection is opened, the request is written verbatim
/// (the proven core already produced a forwardable request head; the host adds no
/// meaning), and the response is read until the upstream signals completion by
/// Content-Length or by closing. This is a REAL socket to a REAL backend — the
/// forward the "no upstream connection" gap was missing.
pub fn forward(addr: SocketAddr, req: &[u8], timeout: Duration) -> std::io::Result<Vec<u8>> {
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(req)?;
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

fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

fn content_length(head: &[u8]) -> Option<usize> {
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 15 && line[..15].eq_ignore_ascii_case(b"content-length:") {
            let v = trim_ascii(&line[15..]);
            return std::str::from_utf8(v).ok()?.trim().parse().ok();
        }
    }
    None
}

/// A `502 Bad Gateway` response (the chosen backend could not be reached).
pub fn bad_gateway() -> Vec<u8> {
    b"HTTP/1.1 502 Bad Gateway\r\nContent-Length: 11\r\nConnection: close\r\n\r\nbad gateway"
        .to_vec()
}

/// A `503 Service Unavailable` response (no backend is eligible — every backend
/// down or breaker-open, so the proven pick returned nothing).
pub fn service_unavailable() -> Vec<u8> {
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Length: 19\r\nConnection: close\r\n\r\nno healthy upstream"
        .to_vec()
}

/// The whole reverse-proxy hop for one request, given a `pick` that returns the
/// PROVEN backend choice (the `drorb_proxy_pick` seam: `(mask, key) → id`).
///
/// * ask the proven selector which backend, feeding it the live mask + sticky key;
/// * map the id to its socket and dial it, forwarding the request;
/// * record breaker success/failure so repeated upstream failures open the breaker;
/// * on no eligible backend → 503; on a dial/forward error → 502.
///
/// The backend is ALWAYS the proven pick's; this function never selects. Returns
/// the response bytes and, on a successful forward, the dialled backend address
/// (for the access log; `None` on 502/503).
pub fn handle<P>(req: &[u8], fleet: &Fleet, pick: P) -> (Vec<u8>, Option<String>)
where
    P: Fn(u8, &[u8]) -> Option<u32>,
{
    let key = sticky_key(req);
    let id = match pick(fleet.mask(), &key) {
        Some(id) => id,
        None => return (service_unavailable(), None),
    };
    let addr = match fleet.addr(id) {
        Some(a) => a,
        None => return (bad_gateway(), None),
    };
    fleet.inflight_inc(id);
    let out = forward(addr, req, fleet.dial_timeout);
    fleet.inflight_dec(id);
    match out {
        Ok(resp) => {
            fleet.record_success(id);
            (resp, Some(addr.to_string()))
        }
        Err(_) => {
            fleet.record_failure(id);
            (bad_gateway(), None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_fleet_spec_and_mask() {
        let f = Fleet::parse("0=127.0.0.1:9400,2=127.0.0.1:9402", 3, Duration::from_millis(50))
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
}
