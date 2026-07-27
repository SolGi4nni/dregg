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
use std::net::{SocketAddr, TcpStream, ToSocketAddrs};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};
use std::time::Duration;

use crate::pool::ConnPool;

/// The process-wide upstream keep-alive connection pool: a per-backend cache of
/// idle, message-boundary-clean sockets reused across forwards instead of
/// dialling a fresh TCP connection per request. Shared by every host IO path that
/// forwards through this module (the buffered [`forward`] the effect seam drives
/// and the streaming pumps the proxy hook drives).
///
/// Disabled by `DRORB_PROXY_NOPOOL=1` (every forward then dials fresh, the A/B
/// contrast for the reuse measurement). The per-host idle cap and max idle age
/// have plain defaults; a deployment can raise the cap with `DRORB_PROXY_POOL_MAX`.
fn conn_pool() -> Option<&'static Arc<ConnPool>> {
    static POOL: OnceLock<Option<Arc<ConnPool>>> = OnceLock::new();
    POOL.get_or_init(|| {
        let off = std::env::var("DRORB_PROXY_NOPOOL")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false);
        if off {
            return None;
        }
        let max_per_host = std::env::var("DRORB_PROXY_POOL_MAX")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(32usize);
        Some(ConnPool::new(max_per_host, Duration::from_secs(90)))
    })
    .as_ref()
}

/// `(reused, dialed)` upstream-forward counts since start, or `None` when pooling
/// is disabled — the observability seam for the connection-reuse check.
pub fn pool_stats() -> Option<(u64, u64)> {
    conn_pool().map(|p| p.stats())
}

/// A connected upstream socket for `addr`: a pooled idle socket when one is warm
/// (reuse — no dial), else a fresh `connect(2)`. The `bool` is `true` when the
/// socket came from the pool, so the caller can retry a stale reuse with a fresh
/// dial. Timeouts/`TCP_NODELAY` are set here so a reused socket behaves exactly as
/// a freshly dialled one for the forward.
fn dial_or_reuse(addr: SocketAddr, timeout: Duration) -> std::io::Result<(TcpStream, bool)> {
    if let Some(pool) = conn_pool() {
        if let Some(up) = pool.checkout(addr) {
            up.set_nodelay(true).ok();
            up.set_read_timeout(Some(timeout)).ok();
            up.set_write_timeout(Some(timeout)).ok();
            pool.note_reused();
            return Ok((up, true));
        }
        pool.note_dialed();
    }
    let up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    Ok((up, false))
}

/// Return a message-boundary-clean upstream socket to the pool for `addr`, so the
/// next forward to that backend reuses it. A no-op when pooling is disabled. The
/// CALLER guarantees the whole framed reply was consumed and the upstream did not
/// signal `Connection: close` (see [`resp_upstream_keepalive`]).
fn return_to_pool(addr: SocketAddr, stream: TcpStream) {
    if let Some(pool) = conn_pool() {
        pool.checkin(addr, stream);
    }
    // else: pooling disabled — `stream` drops here, closing the socket.
}

/// Whether an UPSTREAM response head lets its connection be REUSED for a later
/// forward: HTTP/1.1 keeps the connection alive unless the response carries a
/// `Connection: close` (any comma-separated `close` token, case-insensitive). An
/// HTTP/1.0 upstream defaults to close and is only reusable with an explicit
/// `Connection: keep-alive`; that older wire form is treated as not-reusable here
/// (conservative — such a socket is dialled fresh next time rather than risking a
/// half-closed reuse).
pub(crate) fn resp_upstream_keepalive(head: &[u8]) -> bool {
    let mut http11 = false;
    let mut saw_close = false;
    let mut saw_keepalive = false;
    for (i, line) in head.split(|&c| c == b'\n').enumerate() {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if i == 0 {
            // Status line: note the HTTP version.
            http11 = line.windows(8).any(|w| w.eq_ignore_ascii_case(b"HTTP/1.1"));
            continue;
        }
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
                if t == b"close" {
                    saw_close = true;
                } else if t == b"keep-alive" {
                    saw_keepalive = true;
                }
            }
        }
    }
    if saw_close {
        return false;
    }
    http11 || saw_keepalive
}

/// Finalize an upstream response HEAD for the client: run the proven GATED response
/// transform ([`forward_response_head_gated`] — refuse a bare-LF head, else strip
/// response hop-by-hop headers and add `Via`) then stamp the host's client-connection
/// disposition ([`crate::http::annotate_connection`]). Both streaming pumps (the
/// portable userspace copy and the Linux kernel splice) build the client head through
/// THIS one helper, so the refusal and the strip + `Via` are byte-identical across the
/// IO paths.
///
/// `None` is the proven core REFUSING the upstream head (RFC 9112 §2.2 — its line
/// terminators are ambiguous, so this hop and the client would parse it differently).
/// The caller answers the client [`bad_gateway`] and forwards nothing.
fn client_resp_head(raw_head: &[u8], keepalive: bool) -> Option<Vec<u8>> {
    let mut head = forward_response_head_gated(raw_head)?;
    crate::http::annotate_connection(&mut head, keepalive);
    Some(head)
}

/// The proven response-head gate REFUSED this upstream head (RFC 9112 §2.2: its line
/// terminators are ambiguous, so this hop and the client would disagree about where
/// its fields — and therefore its message — end). Answer the client `502 Bad Gateway`
/// (RFC 9110 §15.6.3, the status for an invalid response from an inbound server) and
/// forward NOTHING: not the head, not a byte of the body. `complete: false` records
/// the backend's failure with the circuit breaker — an upstream emitting heads this
/// hop cannot forward unambiguously is unhealthy.
fn refuse_upstream_head<W: Write>(client: &mut W) -> Streamed {
    let resp = bad_gateway();
    let wrote = client.write_all(&resp).is_ok();
    let bytes = if wrote { resp.len() as u64 } else { 0 };
    Streamed {
        head: resp,
        bytes,
        keepalive: false,
        complete: false,
    }
}

/// Resolve a reverse-proxy backend target to a socket address — the host side of
/// "which machine", the dual of the proven "which backend id". Name resolution is
/// deliberately OUTSIDE the verified core: it is host I/O (the system resolver,
/// `/etc/hosts`, a container's embedded DNS), not something the proof reasons
/// about. The proven part is the forward once a socket is open; turning
/// `gateway:8080` into an address is glue.
///
/// A dotted-quad / bracketed-IPv6 literal (`127.0.0.1:9400`, `[::1]:80`) is parsed
/// directly — no lookup. Anything else (a service name like `gateway:8080`) goes
/// through `getaddrinfo` via [`ToSocketAddrs`], which consults `/etc/hosts` and the
/// configured resolvers — in a compose network, Docker's embedded DNS at
/// `127.0.0.11`. Returns `None` on any resolution failure; the caller renders that
/// as a `502`, never a panic.
fn resolve_target(target: &str) -> Option<SocketAddr> {
    // Fast path: a literal `IP:port` needs no lookup.
    if let Ok(addr) = target.parse::<SocketAddr>() {
        return Some(addr);
    }
    // Host-name path: the system resolver; take the first usable address.
    target.to_socket_addrs().ok().and_then(|mut it| it.next())
}

/// A configured backend fleet: the id→target map plus live health and breaker
/// state. Ids match the proven `Reactor.ProxyDial.fleet` backend ids (0,1,2,…).
pub struct Fleet {
    /// backend id → its configured target string: an `IP:port` literal or a
    /// `host:port` service name. Names are turned into a socket host-side by
    /// [`resolve_target`], cached in `resolved`.
    targets: HashMap<u32, String>,
    /// backend id → the last resolution of its target ([`resolve_target`]'s
    /// result). `None` until a name first resolves (or after it stops resolving);
    /// seeded at parse and refreshed by the active-health sweep, so a backend whose
    /// DNS record changes (a restarted container) is re-pinned without a
    /// reconfigure, and the hot path reads a cached socket rather than calling the
    /// resolver per forward.
    resolved: HashMap<u32, RwLock<Option<SocketAddr>>>,
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
    /// The configured target — an `IP:port` literal or a `host:port` service name.
    pub addr: String,
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
    /// Build a fleet from a spec string like `0=127.0.0.1:9400,1=gateway:8080`.
    /// A backend target may be an `IP:port` literal or a `host:port` service name;
    /// the name is resolved host-side by [`resolve_target`]. All configured
    /// backends start assumed-up; the health loop / breaker demote them on real
    /// failures. A target that does not resolve at parse time is still registered
    /// (seeded unresolved) and retried at dial / health-sweep — an unresolvable
    /// backend yields a `502` at forward, it never fails the whole fleet here.
    /// Returns `None` only if the spec names no backend, or an id is malformed.
    pub fn parse(spec: &str, breaker_threshold: u32, dial_timeout: Duration) -> Option<Fleet> {
        let mut targets = HashMap::new();
        let mut resolved = HashMap::new();
        let mut mask: u32 = 0;
        for entry in spec.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let (id_s, addr_s) = entry.split_once('=')?;
            let id: u32 = id_s.trim().parse().ok()?;
            let target = addr_s.trim().to_string();
            // Seed the resolution cache: a literal resolves now, an as-yet
            // unresolvable service name stays `None` and is retried later.
            resolved.insert(id, RwLock::new(resolve_target(&target)));
            targets.insert(id, target);
            mask |= 1 << id;
        }
        if targets.is_empty() {
            return None;
        }
        let inflight = targets.keys().map(|&id| (id, AtomicU32::new(0))).collect();
        Some(Fleet {
            targets,
            resolved,
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

    /// The socket for a backend id: the cached resolution of its target, if
    /// configured and currently resolvable. A literal / already-resolved name is a
    /// cache read (no lookup on the hot path); a cold or previously-failed name is
    /// re-resolved once here, so a backend that came up between health sweeps is
    /// reachable immediately. `None` — unconfigured id, or a name that still does
    /// not resolve — is the caller's cue to emit a `502`.
    pub fn addr(&self, id: u32) -> Option<SocketAddr> {
        let target = self.targets.get(&id)?;
        if let Some(cached) = self.resolved.get(&id).and_then(|c| *c.read().unwrap()) {
            return Some(cached);
        }
        let addr = resolve_target(target)?;
        if let Some(slot) = self.resolved.get(&id) {
            *slot.write().unwrap() = Some(addr);
        }
        Some(addr)
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
            .targets
            .iter()
            .map(|(&id, target)| {
                let failures = breaker.get(&id).copied().unwrap_or(0);
                BackendHealth {
                    id,
                    addr: target.clone(),
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

    /// One active-health sweep: re-resolve each backend's target (refreshing the
    /// cache so a restarted container's new address is picked up), then TCP-probe
    /// it and set its bit up iff the connection is accepted. A target that no
    /// longer resolves probes down. A breaker-open backend stays down until a probe
    /// succeeds. Returns the resulting mask.
    pub fn probe_once(&self) -> u8 {
        for (&id, target) in &self.targets {
            let addr = resolve_target(target);
            if let Some(slot) = self.resolved.get(&id) {
                *slot.write().unwrap() = addr;
            }
            let up = match addr {
                Some(a) => TcpStream::connect_timeout(&a, self.dial_timeout).is_ok(),
                None => false,
            };
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

/// The lowercased header NAME of a header line — the bytes before the first colon,
/// ASCII-lowercased. Host-side only: the connection-POOL decision
/// ([`resp_upstream_keepalive`], "may this upstream socket be reused") reads it. The
/// forwarded header block is not decided here — that is the proven core's, crossed
/// below.
fn header_name_lower(line: &[u8]) -> Vec<u8> {
    line.iter()
        .take_while(|&&b| b != b':')
        .map(|b| b.to_ascii_lowercase())
        .collect()
}

/// Trim ASCII OWS (SP / HTAB) from both ends of a token. Host-side only, same
/// connection-pool use as [`header_name_lower`].
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

// ---------------------------------------------------------------------------
// The proxy forward transforms — THE PROVEN OBJECT, CALLED.
//
// `Reactor.ProxyForwardHead` is the machine-checked RFC 9110 §7.6 forward: the
// hop-by-hop strip (§7.6.1, including `Connection`-token expansion), the `Via`
// proxy identity (§7.6.3), the `X-Forwarded-For` client address (§7.6.2), and the
// response-side strip that DELIBERATELY preserves `Transfer-Encoding` framing. Its
// guarantees are theorems over ALL inputs — `stripped_survivor_not_dropped`,
// `hop_named_line_removed`, `endToEnd_line_preserved`, `forward_via_line`,
// `forward_xff_line`, `resp_connection_removed`, `resp_transfer_encoding_preserved`,
// `reqLine_isPrefix` / `forward_body_isSuffix`.
//
// The three host entry points below are CALLS to its `@[export]`s. There is no Rust
// reimplementation of the transform: before this, `strip_hop_by_hop` /
// `forward_request` / the response-head transform were hand-written byte-mirrors of the
// Lean, checked only by unit tests on three demo constants — case testing, with zero
// formal content, and the twin was free to drift on every input the demos did not
// name. The host now contributes buffer marshalling and nothing else.
//
// Thread discipline: identical to the framing seam in `http.rs`
// (`drorb_frame_request`). Each export is a pure `ByteArray -> ByteArray`; every
// per-call object is created, consumed, and dropped on the one calling thread, and
// the only cross-thread state is the module's persistent globals. So the crossing
// runs directly on the calling IO/shard thread (registered once through
// `crate::http::ensure_lean_thread`) — no job channel, no runtime-owner hop.
//
// `Reactor.ProxyForwardHead` is NOT in `Dataplane`'s import closure, so `lean_boot`
// does not initialize it; the first crossing does, guarded and process-wide, exactly
// as the framing seam initializes `Body.FrameRaw`. Its export object is archived by
// the explicit `lake build Reactor.ProxyForwardHead:c.o.export` line in
// `ffi/build-dataplane-lib.sh` — without it the symbols are absent and the host link
// fails LOUDLY (undefined `drorb_proxy_strip_req`), never silently falling back.
// ---------------------------------------------------------------------------

/// Opaque Lean heap object; only `*mut LeanObject` is ever held.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    /// `initialize_Reactor_ProxyForwardHead` — module initializer for the forward
    /// transforms' closure (`Reactor.ProxyForwardHead` → `Reactor.ServeStep`).
    /// Guarded (idempotent) like every generated module init. The generated C
    /// signature is `lean_object *(uint8_t builtin)` — one argument, no world
    /// token — so it is declared here exactly as emitted.
    #[link_name = "initialize_drorb_Reactor_ProxyForwardHead"]
    fn initialize_Reactor_ProxyForwardHead(builtin: u8) -> *mut LeanObject;
    /// `@[export drorb_proxy_strip_req]` (`Reactor.ProxyForward.stripHopByHop`) —
    /// the raw request bytes in, the request with every hop-by-hop field (fixed set
    /// + `Connection`-named tokens) removed out. Request line and body verbatim.
    fn drorb_proxy_strip_req(req: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_proxy_forward_req]` (`Reactor.ProxyForward.forwardReq`) —
    /// the FULL forwarded request: hop-by-hop stripped AND the `Via` /
    /// `X-Forwarded-For` proxy-identity lines injected. First argument is the client
    /// ip bytes (EMPTY ⇒ no `X-Forwarded-For` — a header with an empty value is
    /// never emitted), second the raw request.
    fn drorb_proxy_forward_req(ip: *mut LeanObject, req: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_proxy_forward_resp_gated]`
    /// (`Reactor.ProxyForward.forwardRespHeadGated`) — the GATED response-head
    /// transform, and the ONLY response-head seam the host may cross. An upstream
    /// RESPONSE header block in; a tagged verdict out (`Reactor.ProxyForward.
    /// encodeRespHead`): first byte `1` ⇒ REFUSE this head (RFC 9112 §2.2 bare LF —
    /// two hops would parse it differently, i.e. response splitting), first byte `0`
    /// ⇒ the remaining bytes are the transformed head to forward.
    fn drorb_proxy_forward_resp_gated(head: *mut LeanObject) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — stateless.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Ensure this thread may cross the forward-transform seam: the thread is
/// registered with the Lean runtime and the `Reactor.ProxyForwardHead` module
/// closure is initialized (once, process-wide).
fn ensure_forward_seam() {
    use std::sync::Once;
    static MODULE: Once = Once::new();
    // Register the thread FIRST — the module init below allocates on it.
    crate::http::ensure_lean_thread();
    MODULE.call_once(|| {
        // SAFETY: standard guarded module init, on a registered thread, after the
        // process-global runtime is up (the IO hosts start only after the serve
        // gateway's boot handshake).
        unsafe {
            let res = initialize_Reactor_ProxyForwardHead(1);
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Reactor_ProxyForwardHead returned an IO error"
            );
            drorb_obj_dec(res);
        }
    });
}

/// Cross a single-argument proven transform: bytes in, transformed bytes out.
/// Runs on the calling thread (registered on first use).
fn cross_bytes(
    entry: unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject,
    data: &[u8],
) -> Vec<u8> {
    ensure_forward_seam();
    // SAFETY: `entry` is a real `@[export] ByteArray -> ByteArray` symbol; the
    // argument is a fresh sarray the callee consumes, the result an owned sarray
    // copied out then released — created, consumed, and dropped on this one thread.
    unsafe {
        let arg = drorb_sarray_of_bytes(data.as_ptr(), data.len());
        let out = entry(arg);
        let n = drorb_sarray_len(out);
        let v = std::slice::from_raw_parts(drorb_sarray_ptr(out), n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

/// **Strip hop-by-hop headers from a request before forwarding it upstream**
/// (RFC 9110 §7.6.1) — the proven `Reactor.ProxyForward.stripHopByHop`, crossed.
/// The request line is kept verbatim; every header line whose (case-insensitive)
/// name is a fixed hop-by-hop field OR a token named in a `Connection` header is
/// dropped; surviving headers and the body pass through unchanged. Every one of
/// those clauses is a theorem over ALL requests, not a case test.
pub fn strip_hop_by_hop(req: &[u8]) -> Vec<u8> {
    cross_bytes(drorb_proxy_strip_req, req)
}

/// **Build the request forwarded upstream** (RFC 9110 §7.6) — the proven
/// `Reactor.ProxyForward.forwardReq`, crossed: hop-by-hop headers stripped
/// (§7.6.1), a `Via` field added (§7.6.3), and — when the host knows the
/// originating client address — an `X-Forwarded-For` field added (§7.6.2,
/// de-facto). An empty `client_ip` emits no `X-Forwarded-For`. Request line and
/// body verbatim.
pub fn forward_request(req: &[u8], client_ip: &[u8]) -> Vec<u8> {
    ensure_forward_seam();
    // SAFETY: as `cross_bytes`, for the two-argument export — both fresh sarrays
    // are consumed by the callee, the owned result copied out then released, all
    // on this one registered thread.
    unsafe {
        let ip = drorb_sarray_of_bytes(client_ip.as_ptr(), client_ip.len());
        let r = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let out = drorb_proxy_forward_req(ip, r);
        let n = drorb_sarray_len(out);
        let v = std::slice::from_raw_parts(drorb_sarray_ptr(out), n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

/// **Transform an upstream RESPONSE head, or REFUSE it** — the proven
/// `Reactor.ProxyForward.forwardRespHeadGated`, crossed. This is the response-head
/// seam the serving paths use, and now the ONLY one: the ungated
/// `drorb_proxy_forward_resp` export and its `forward_response_head` wrapper are
/// RETIRED. Its contract was "the host must not call it", and
/// `Reactor.ProxyForward.ungated_resp_seam_differs` machine-checks that crossing it
/// instead restores the response-splitting leak — so it is not reachable from here at
/// all rather than reachable-but-forbidden.
///
/// `None` means the proven core refused the upstream head because its line
/// terminators are ambiguous: RFC 9112 §2.2 lets a recipient treat a bare LF as a
/// line terminator, so a head containing one has TWO admissible parses, and this hop
/// would hand its client a head it read differently from the way the client will —
/// HTTP response splitting (a `Set-Cookie` this proxy never saw as a field, or a
/// whole second message, riding inside what this hop reads as one field VALUE;
/// `Reactor.ProxyForward.respBareLF_gate_not_vacuous` witnesses exactly that on the
/// measured vector). The proxy fails CLOSED: the caller answers [`bad_gateway`]
/// (RFC 9110 §15.6.3 — the upstream produced an invalid response) and forwards
/// nothing.
///
/// The proven transform consumes the header BLOCK (no trailing CRLFCRLF); `head` as
/// the host holds it includes the separator. Delimiting the block and re-appending
/// the separator is the host's marshalling — no header-field decision is taken here,
/// and no bare-LF decision either: the verdict byte comes from Lean.
pub fn forward_response_head_gated(head: &[u8]) -> Option<Vec<u8>> {
    let block_end = find(head, b"\r\n\r\n").unwrap_or(head.len());
    let tagged = cross_bytes(drorb_proxy_forward_resp_gated, &head[..block_end]);
    match tagged.split_first() {
        // `0 :: out` — the transformed head; re-append the separator the block excluded.
        Some((0, out)) => {
            let mut v = out.to_vec();
            v.extend_from_slice(&head[block_end..]);
            Some(v)
        }
        // `1` — refused. Any other payload (an empty cross, a tag the encoder never
        // emits) is treated as a refusal too: this seam fails closed by construction.
        _ => None,
    }
}

/// Forward `req` to `addr` — over a pooled keep-alive socket when one is warm,
/// else a fresh dial — and return the upstream's full response bytes. The request
/// is written with its hop-by-hop headers stripped ([`strip_hop_by_hop`], RFC 9110
/// §7.6.1; the effect-seam caller has already added `Via`/`X-Forwarded-For` in the
/// proven core), and the response is read until the upstream signals completion by
/// Content-Length or by closing. After a CLEAN Content-Length reply from a
/// keep-alive upstream the socket is returned to the pool for the next forward. A
/// stale pooled socket is retried ONCE with a fresh dial (nothing has been read
/// back to the caller yet). A reply whose head the PROVEN bare-LF gate refuses is
/// never pooled: this hop and the upstream do not agree where that message ends,
/// so the socket is closed rather than handed to the next forward.
pub fn forward(addr: SocketAddr, req: &[u8], timeout: Duration) -> std::io::Result<Vec<u8>> {
    let forward_bytes = strip_hop_by_hop(req);
    let (mut up, reused) = dial_or_reuse(addr, timeout)?;
    let resp = match forward_once(&mut up, &forward_bytes) {
        Ok(r) => r,
        // A pooled socket the upstream had already closed: dial fresh and retry.
        Err(_) if reused => {
            if let Some(pool) = conn_pool() {
                pool.note_dialed();
            }
            let fresh = TcpStream::connect_timeout(&addr, timeout)?;
            fresh.set_nodelay(true).ok();
            fresh.set_read_timeout(Some(timeout)).ok();
            fresh.set_write_timeout(Some(timeout)).ok();
            up = fresh;
            forward_once(&mut up, &forward_bytes)?
        }
        Err(e) => return Err(e),
    };
    // Return the socket to the pool only when it sits EXACTLY at a Content-Length
    // message boundary (no over-read into a next reply) and the upstream did not
    // signal `Connection: close` — otherwise it is dropped (closed).
    //
    // ★ The PROVEN bare-LF gate decides FIRST (RFC 9112 §2.2). `content_length` and
    // `resp_upstream_keepalive` below are LF-TOLERANT scanners — they terminate a header
    // line on a bare LF — while the proven core is CRLF-only. On a head carrying a bare
    // LF the two disagree about which field lines exist, so they disagree about where
    // this reply ENDS on the wire; pooling a socket whose message boundary is not agreed
    // hands the NEXT forward on that socket whatever this one failed to consume.
    //
    // The CLIENT of this exchange is already answered `502` — the caller threads `resp`
    // into `drorb_serve_resume`, which crosses `Reactor.ServeStep.proxyRespTransformGated`
    // — but that refusal does not un-poison a pooled socket, and the victim would be a
    // DIFFERENT client's later request. So the same verdict has to reach this decision
    // too. The verdict is not recomputed here: `forward_response_head_gated` IS the
    // serving path's gate (`Reactor.ProxyForward.forwardRespHeadGated`), crossed, so the
    // two cannot drift. A refused head drops the socket and the leftovers die with it.
    // (The accept path recomputes a head transform it discards; this is the pooling
    // optimization, and correctness of the message boundary outranks it.)
    if let Some(he) = find(&resp, b"\r\n\r\n").map(|p| p + 4) {
        if forward_response_head_gated(&resp[..he]).is_some() {
            if let Some(clen) = content_length(&resp[..he]) {
                if resp.len() == he + clen && resp_upstream_keepalive(&resp[..he]) {
                    return_to_pool(addr, up);
                }
            }
        }
    }
    Ok(resp)
}

/// Write `forward_bytes` to `up` and read one full HTTP/1.1 response back.
fn forward_once(up: &mut TcpStream, forward_bytes: &[u8]) -> std::io::Result<Vec<u8>> {
    up.write_all(forward_bytes)?;
    up.flush()?;
    read_response(up)
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

/// Whether the response head declares `Content-Type: text/event-stream` — a
/// Server-Sent Events stream. Such a response is a long-lived, event-at-a-time
/// stream (Caddy's `flush_interval -1` routes): the body must be relayed to the
/// client the instant each event arrives, never batched, and the upstream read
/// must NOT time out between sparse events. Matched case-insensitively on the
/// media type, ignoring any `; charset=…` parameter.
pub(crate) fn is_event_stream(head: &[u8]) -> bool {
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 13 && line[..13].eq_ignore_ascii_case(b"content-type:") {
            let v = trim_ascii(&line[13..]);
            // The media type is up to the first `;`; compare it trimmed.
            let mt = match v.iter().position(|&b| b == b';') {
                Some(p) => trim_ascii(&v[..p]),
                None => v,
            };
            return mt.eq_ignore_ascii_case(b"text/event-stream");
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

/// Write an already-built forward request to `up` and read through the response
/// head (CRLFCRLF), framing it into an [`UpstreamHead`]. Shared by a fresh dial
/// and a pooled-socket reuse. `Err` means nothing has reached the client yet
/// (write failure, or the upstream closing before a full head).
fn send_and_read_head(mut up: TcpStream, forward: &[u8]) -> std::io::Result<UpstreamHead> {
    up.write_all(forward)?;
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

/// Forward `req` to `addr` — over a pooled keep-alive socket when one is warm,
/// else a fresh dial — with its hop-by-hop headers stripped and `Via`/`X-Forwarded-For`
/// added ([`forward_request`], RFC 9110 §7.6), and read through the response head
/// (CRLFCRLF). A stale pooled socket (write/read fails on reuse) is retried ONCE
/// with a fresh dial, safe because nothing has reached the client yet. `Err` here
/// means nothing reached the client (dial failure, request-write failure, or the
/// upstream closing before a full head), so the caller may still send a 502.
fn dial_and_read_head(
    addr: SocketAddr,
    req: &[u8],
    timeout: Duration,
    client_ip: &[u8],
) -> std::io::Result<UpstreamHead> {
    let forward = forward_request(req, client_ip);
    let (up, reused) = dial_or_reuse(addr, timeout)?;
    match send_and_read_head(up, &forward) {
        Ok(uh) => Ok(uh),
        // A pooled socket the upstream had already closed: dial fresh and retry.
        Err(_) if reused => {
            if let Some(pool) = conn_pool() {
                pool.note_dialed();
            }
            let fresh = TcpStream::connect_timeout(&addr, timeout)?;
            fresh.set_nodelay(true).ok();
            fresh.set_read_timeout(Some(timeout)).ok();
            fresh.set_write_timeout(Some(timeout)).ok();
            send_and_read_head(fresh, &forward)
        }
        Err(e) => Err(e),
    }
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
    // Whether the UPSTREAM socket can be pooled for reuse after this reply.
    let upstream_reusable = resp_upstream_keepalive(&uh.buf[..uh.head_end]);

    // SSE (`text/event-stream`) — Caddy's `flush_interval -1` streaming mode: the
    // body is a long-lived, event-at-a-time stream. Flush the client after every
    // block so each event reaches even a buffered writer immediately, and CLEAR
    // the upstream read timeout so a stream that goes quiet between sparse events
    // is not truncated by the dial-timeout deadline (`set_read_timeout` was armed
    // on the dial). Keeping the connection open for the long-lived stream is the
    // point of the mode.
    let sse = is_event_stream(&uh.buf[..uh.head_end]);
    if sse {
        uh.up.set_read_timeout(None).ok();
    }

    // Build the client head through the shared finalizer (refuse a bare-LF head,
    // else strip response hop-by-hop, add `Via`, stamp the client disposition), then
    // write it. From here a failure is mid-stream. Flush it so an SSE client sees the
    // head (and can open its `EventSource`) before the first event.
    let head = match client_resp_head(&uh.buf[..uh.head_end], keepalive) {
        Some(h) => h,
        // The proven gate REFUSED the upstream head (RFC 9112 §2.2): 502, forward nothing.
        None => return Ok(refuse_upstream_head(client)),
    };
    if client.write_all(&head).is_err() {
        return Ok(Streamed {
            head,
            bytes: 0,
            keepalive: false,
            complete: false,
        });
    }
    if sse {
        client.flush().ok();
    }
    let mut bytes = head.len() as u64;

    // Stream the body per its framing. `leftover` is the body bytes already
    // read while finding the head end.
    let mut chunk = vec![0u8; STREAM_CHUNK];
    let leftover = &uh.buf[uh.head_end..];
    let complete = match uh.clen {
        Some(clen) => stream_fixed(
            &mut uh.up, client, leftover, clen, &mut chunk, &mut bytes, sse,
        ),
        None if uh.chunked => {
            stream_chunked(&mut uh.up, client, leftover, &mut chunk, &mut bytes, sse)
        }
        None => stream_to_eof(&mut uh.up, client, leftover, &mut chunk, &mut bytes, sse),
    };

    // A cleanly-completed fixed-length reply from a keep-alive upstream leaves the
    // socket exactly at the next request boundary: return it to the pool. (Chunked
    // and close-delimited replies are not pooled — see [`maybe_pool_upstream`].)
    maybe_pool_upstream(addr, uh.up, uh.clen, complete, upstream_reusable);

    Ok(Streamed {
        head,
        bytes,
        keepalive: keepalive && complete,
        complete,
    })
}

/// Return the upstream socket to the pool iff this reply left it at a clean
/// request boundary: a fully-delivered `Content-Length` body (`complete`) from a
/// keep-alive-willing upstream (`upstream_reusable`). Chunked replies (whose
/// verbatim pass-through may over-read past the terminator) and close-delimited
/// replies (whose upstream closes the socket) are NEVER pooled — the socket drops
/// (closes) instead. This is the single check-in gate for the streaming pumps, so
/// the pooling safety rule lives in exactly one place.
fn maybe_pool_upstream(
    addr: SocketAddr,
    up: TcpStream,
    clen: Option<usize>,
    complete: bool,
    upstream_reusable: bool,
) {
    if complete && clen.is_some() && upstream_reusable {
        return_to_pool(addr, up);
    }
    // else: `up` drops here, closing the socket.
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

    // Framing + keep-alive disposition, and the client head, through the SAME
    // shared finalizer the portable pump uses (strip response hop-by-hop, add
    // `Via`, stamp the client disposition) — so the response-side transform is
    // byte-identical across the userspace and splice IO paths.
    let keepalive = keepalive_req && (uh.clen.is_some() || uh.chunked);
    let upstream_reusable = resp_upstream_keepalive(&uh.buf[..uh.head_end]);

    // SSE (`text/event-stream`) — the `flush_interval -1` streaming mode (see the
    // portable pump). CLEAR the upstream read timeout so a long-lived stream that
    // goes quiet between sparse events is not truncated: `splice(2)` inherits the
    // socket's `SO_RCVTIMEO` and would surface a timeout as `EAGAIN` (a mid-body
    // failure) exactly as the userspace `read` does. Flushing per-event is
    // unconditional on this path — the client is a raw nodelay `TcpStream`, so
    // splice delivers each event to the wire the instant it is moved.
    let sse = is_event_stream(&uh.buf[..uh.head_end]);
    if sse {
        uh.up.set_read_timeout(None).ok();
    }

    let head = match client_resp_head(&uh.buf[..uh.head_end], keepalive) {
        Some(h) => h,
        // The proven gate REFUSED the upstream head (RFC 9112 §2.2): 502, forward nothing.
        None => return Ok(refuse_upstream_head(client)),
    };
    if client.write_all(&head).is_err() {
        return Ok(Streamed {
            head,
            bytes: 0,
            keepalive: false,
            complete: false,
        });
    }
    if sse {
        client.flush().ok();
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
                                    sse,
                                )
                            }
                        },
                        None => {
                            let mut chunk = vec![0u8; STREAM_CHUNK];
                            stream_fixed(
                                &mut uh.up,
                                client,
                                &[],
                                remaining,
                                &mut chunk,
                                &mut bytes,
                                sse,
                            )
                        }
                    }
                }
            }
        }
        // Chunked body: framing must be inspected for its terminator, which
        // splice cannot do — the bounded userspace pump carries it.
        None if uh.chunked => {
            let mut chunk = vec![0u8; STREAM_CHUNK];
            stream_chunked(&mut uh.up, client, leftover, &mut chunk, &mut bytes, sse)
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
                            stream_to_eof(&mut uh.up, client, &[], &mut chunk, &mut bytes, sse)
                        }
                    },
                    None => {
                        let mut chunk = vec![0u8; STREAM_CHUNK];
                        stream_to_eof(&mut uh.up, client, &[], &mut chunk, &mut bytes, sse)
                    }
                }
            }
        }
    };

    // A cleanly-completed fixed-length reply from a keep-alive upstream leaves the
    // upstream socket exactly at the next request boundary (the splice/userspace
    // pump moved EXACTLY the Content-Length body): return it to the pool. Chunked
    // and close-delimited replies are not pooled ([`maybe_pool_upstream`]).
    maybe_pool_upstream(addr, uh.up, uh.clen, complete, upstream_reusable);

    Ok(Streamed {
        head,
        bytes,
        keepalive: keepalive && complete,
        complete,
    })
}

/// Stream exactly `clen` body bytes from `up` to `client`, starting with the
/// already-read `leftover`. Returns whether the full body was delivered. When
/// `flush` is set (a `flush_interval -1` streaming route), the client writer is
/// flushed after every block so a buffered writer delivers each block at once.
fn stream_fixed<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    clen: usize,
    chunk: &mut [u8],
    bytes: &mut u64,
    flush: bool,
) -> bool {
    let mut remaining = clen;
    let take = leftover.len().min(remaining);
    if take > 0 {
        if client.write_all(&leftover[..take]).is_err() {
            return false;
        }
        if flush && client.flush().is_err() {
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
        if flush && client.flush().is_err() {
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
/// With `flush` set the client is flushed after each read so a buffered writer
/// (TLS, `BufWriter`) still delivers each SSE event the moment it arrives.
fn stream_to_eof<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    chunk: &mut [u8],
    bytes: &mut u64,
    flush: bool,
) -> bool {
    if !leftover.is_empty() {
        if client.write_all(leftover).is_err() {
            return false;
        }
        if flush && client.flush().is_err() {
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
        if flush && client.flush().is_err() {
            return false;
        }
        *bytes += n as u64;
    }
}

/// Stream a chunked body verbatim to the client, parsing a copy just enough to
/// detect the terminating zero-chunk so the client connection can stay open
/// without waiting for the upstream to close. Same bounded buffer / back-pressure
/// as the fixed path. Returns whether the terminator was reached cleanly. With
/// `flush` set (an SSE / `flush_interval -1` route) the client is flushed after
/// each block so each event reaches a buffered client as it is emitted.
fn stream_chunked<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    chunk: &mut [u8],
    bytes: &mut u64,
    flush: bool,
) -> bool {
    let mut parser = ChunkedParser::new();
    if !leftover.is_empty() {
        if client.write_all(leftover).is_err() {
            return false;
        }
        if flush && client.flush().is_err() {
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
        if flush && client.flush().is_err() {
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

    /// The thin host-glue resolver: an `IP:port` literal parses with no lookup;
    /// a real service name (`localhost`) goes through the system resolver; a
    /// `.invalid` name (RFC 6761 — guaranteed never to resolve) is `None`, the
    /// caller's cue for a 502.
    #[test]
    fn resolve_target_literal_name_and_failure() {
        assert_eq!(
            resolve_target("127.0.0.1:9400"),
            "127.0.0.1:9400".parse().ok()
        );
        assert_eq!(resolve_target("[::1]:80"), "[::1]:80".parse().ok());
        assert!(resolve_target("localhost:9400").is_some());
        assert_eq!(resolve_target("drorb-no-such-backend.invalid:9400"), None);
    }

    /// A `host:port` service-name backend is a first-class fleet entry: the id is
    /// registered and its mask bit set, and `addr` returns the resolved socket.
    #[test]
    fn fleet_registers_service_name_backend() {
        let f = Fleet::parse("0=localhost:9400", 3, Duration::from_millis(50)).unwrap();
        assert_eq!(f.mask(), 0b1);
        assert_eq!(f.addr(0), resolve_target("localhost:9400"));
        assert!(f.addr(0).is_some());
    }

    /// A configured-but-unresolvable service name does NOT fail the whole fleet at
    /// parse (docker start ordering: the service may not exist yet). It is
    /// registered, but `addr` is `None` — the forward path renders that as a 502,
    /// never a crash.
    #[test]
    fn fleet_keeps_unresolvable_backend_and_addr_is_none() {
        let f = Fleet::parse(
            "0=drorb-no-such-backend.invalid:9400",
            3,
            Duration::from_millis(50),
        )
        .unwrap();
        assert_eq!(f.mask(), 0b1); // registered, assumed-up until the health sweep
        assert_eq!(f.addr(0), None); // the 502 cue at forward time
    }

    /// GATE — end-to-end reverse_proxy to a HOSTNAME backend: a real upstream on a
    /// loopback socket reachable by the name `localhost`, driven through the whole
    /// `handle_streaming_tcp` hop (proven pick → host resolve → dial → forward).
    /// The client receives the upstream's 200 response, proving the service-name
    /// backend was resolved and forwarded to.
    #[test]
    fn hostname_backend_proxies_end_to_end() {
        use std::net::TcpListener;

        // Bind the upstream on whatever family `localhost` resolves to, so the
        // name-resolved dial lands on it deterministically.
        let fam = resolve_target("localhost:0").unwrap();
        let up_l = TcpListener::bind(SocketAddr::new(fam.ip(), 0)).unwrap();
        let port = up_l.local_addr().unwrap().port();
        let up_thread = std::thread::spawn(move || {
            let (mut s, _) = up_l.accept().unwrap();
            let mut req = [0u8; 4096];
            let _ = s.read(&mut req);
            s.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nhi")
                .unwrap();
        });

        let spec = format!("0=localhost:{port}");
        let fleet = Fleet::parse(&spec, 3, Duration::from_millis(500)).unwrap();

        let cl_l = TcpListener::bind("127.0.0.1:0").unwrap();
        let mut client_near = TcpStream::connect(cl_l.local_addr().unwrap()).unwrap();
        let (mut client_far, _) = cl_l.accept().unwrap();
        let collector = std::thread::spawn(move || {
            let mut got = Vec::new();
            client_far.read_to_end(&mut got).unwrap();
            got
        });

        let out = handle_streaming_tcp(
            b"GET /api/x HTTP/1.1\r\nHost: t\r\n\r\n",
            false,
            &fleet,
            &mut client_near,
            |_mask, _key| Some(0),
        )
        .unwrap();
        drop(client_near);
        up_thread.join().unwrap();
        let got = collector.join().unwrap();

        assert!(
            out.backend.is_some(),
            "a hostname backend forward records the dialled socket"
        );
        let text = String::from_utf8_lossy(&got);
        assert!(
            text.starts_with("HTTP/1.1 200 OK"),
            "client got the upstream 200: {text:?}"
        );
        assert!(
            text.ends_with("hi"),
            "client got the upstream body: {text:?}"
        );
    }

    /// GATE — an unresolvable hostname backend yields a 502, not a panic. The
    /// proven pick chooses the (assumed-up) backend, the host resolve fails, and
    /// the hop writes a `502 Bad Gateway` to the client.
    #[test]
    fn unresolvable_hostname_backend_is_502_not_crash() {
        use std::net::TcpListener;

        let fleet = Fleet::parse(
            "0=drorb-no-such-backend.invalid:9400",
            3,
            Duration::from_millis(200),
        )
        .unwrap();

        let cl_l = TcpListener::bind("127.0.0.1:0").unwrap();
        let mut client_near = TcpStream::connect(cl_l.local_addr().unwrap()).unwrap();
        let (mut client_far, _) = cl_l.accept().unwrap();
        let collector = std::thread::spawn(move || {
            let mut got = Vec::new();
            client_far.read_to_end(&mut got).unwrap();
            got
        });

        let out = handle_streaming_tcp(
            b"GET /api/x HTTP/1.1\r\nHost: t\r\n\r\n",
            false,
            &fleet,
            &mut client_near,
            |_mask, _key| Some(0),
        )
        .unwrap();
        drop(client_near);
        let got = collector.join().unwrap();

        assert_eq!(out.backend, None, "no socket was dialled");
        let text = String::from_utf8_lossy(&got);
        assert!(
            text.starts_with("HTTP/1.1 502"),
            "unresolvable backend → 502: {text:?}"
        );
    }

    /// The upstream-reuse predicate: an HTTP/1.1 head with no `Connection: close`
    /// is reusable; a `close` token (in any casing / list position) retires it;
    /// an HTTP/1.0 head is reusable only with an explicit `keep-alive`.
    #[test]
    fn resp_upstream_keepalive_predicate() {
        assert!(resp_upstream_keepalive(
            b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n\r\n"
        ));
        assert!(!resp_upstream_keepalive(
            b"HTTP/1.1 200 OK\r\nConnection: close\r\n\r\n"
        ));
        assert!(!resp_upstream_keepalive(
            b"HTTP/1.1 200 OK\r\nConnection: keep-alive, Close\r\n\r\n"
        ));
        // HTTP/1.0 defaults to close; only an explicit keep-alive reuses.
        assert!(!resp_upstream_keepalive(
            b"HTTP/1.0 200 OK\r\nContent-Length: 0\r\n\r\n"
        ));
        assert!(resp_upstream_keepalive(
            b"HTTP/1.0 200 OK\r\nConnection: Keep-Alive\r\n\r\n"
        ));
    }

    /// The SSE detector fires on `text/event-stream` (any casing, with or without
    /// a `; charset=…` parameter) and stays quiet for ordinary content types — so
    /// only a real event stream enters the flush-per-event / no-read-timeout mode.
    #[test]
    fn is_event_stream_predicate() {
        assert!(is_event_stream(
            b"HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\n\r\n"
        ));
        assert!(is_event_stream(
            b"HTTP/1.1 200 OK\r\nContent-Type: text/event-stream; charset=utf-8\r\n\r\n"
        ));
        assert!(is_event_stream(
            b"HTTP/1.1 200 OK\r\ncontent-type:  TEXT/Event-Stream \r\n\r\n"
        ));
        assert!(!is_event_stream(
            b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n"
        ));
        assert!(!is_event_stream(
            b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n"
        ));
        // A `text/event-stream` token buried in another header is NOT a match.
        assert!(!is_event_stream(
            b"HTTP/1.1 200 OK\r\nX-Note: text/event-stream\r\nContent-Type: text/html\r\n\r\n"
        ));
        assert!(!is_event_stream(
            b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
        ));
    }

    /// A bare [`ConnPool`] round-trips a live socket and retires a peer-closed one.
    #[test]
    fn conn_pool_checkin_checkout_roundtrip() {
        use std::net::TcpListener;
        let pool = crate::pool::ConnPool::new(4, Duration::from_secs(30));
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = l.local_addr().unwrap();
        // A live, quiet peer: accept and hold the connection open.
        let keeper = std::thread::spawn(move || {
            let (s, _) = l.accept().unwrap();
            std::thread::sleep(Duration::from_millis(200));
            drop(s);
        });
        let c = TcpStream::connect(addr).unwrap();
        pool.checkin(addr, c);
        // The idle socket is live and pending-free: it checks back out.
        assert!(
            pool.checkout(addr).is_some(),
            "a live idle socket should reuse"
        );
        // The pool is now empty for this addr.
        assert!(pool.checkout(addr).is_none(), "no second idle socket");
        keeper.join().unwrap();
    }

    /// The upstream connection is REUSED across two sequential buffered forwards to
    /// the same backend: the upstream accepts ONE connection and serves BOTH
    /// requests on it. This is the observable proof that [`forward`] pools the
    /// keep-alive socket instead of dialling fresh per request.
    #[test]
    fn buffered_forward_reuses_upstream_socket() {
        use std::net::TcpListener;
        use std::sync::atomic::{AtomicU32, Ordering};

        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = l.local_addr().unwrap();
        let accepts = Arc::new(AtomicU32::new(0));
        let accepts_srv = Arc::clone(&accepts);
        // One accepted connection serves TWO keep-alive Content-Length replies.
        let up = std::thread::spawn(move || {
            let (mut s, _) = l.accept().unwrap();
            accepts_srv.fetch_add(1, Ordering::SeqCst);
            let mut buf = [0u8; 4096];
            for i in 0..2 {
                // Read one request head.
                let mut acc = Vec::new();
                loop {
                    if find(&acc, b"\r\n\r\n").is_some() {
                        break;
                    }
                    let n = s.read(&mut buf).unwrap();
                    if n == 0 {
                        return; // client hung up early
                    }
                    acc.extend_from_slice(&buf[..n]);
                }
                let body = format!("reply{i}");
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{}",
                    body.len(),
                    body
                );
                s.write_all(resp.as_bytes()).unwrap();
            }
            std::thread::sleep(Duration::from_millis(50));
        });

        let req = b"GET /api HTTP/1.1\r\nHost: t\r\n\r\n";
        let r1 = forward(addr, req, Duration::from_secs(5)).unwrap();
        assert!(r1.ends_with(b"reply0"), "first reply body");
        // Give the socket a moment to be parked before the second forward.
        std::thread::sleep(Duration::from_millis(20));
        let r2 = forward(addr, req, Duration::from_secs(5)).unwrap();
        assert!(r2.ends_with(b"reply1"), "second reply body");

        up.join().unwrap();
        assert_eq!(
            accepts.load(Ordering::SeqCst),
            1,
            "two forwards must reuse ONE upstream connection (pooled), not dial twice"
        );
        // The reuse is also reflected in the pool's counters (pooling is on by
        // default in the test process): at least one forward reused a socket.
        if let Some((reused, _dialed)) = pool_stats() {
            assert!(
                reused >= 1,
                "the pool reused counter should record the reuse"
            );
        }
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
        crate::http::boot_test_runtime();
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
        crate::http::boot_test_runtime();
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
        crate::http::boot_test_runtime();
        let head = b"HTTP/1.1 200 OK\r\nConnection: close\r\nKeep-Alive: timeout=5\r\nTransfer-Encoding: chunked\r\nETag: \"z\"\r\n\r\n";
        let want = b"HTTP/1.1 200 OK\r\nVia: 1.1 drorb\r\nTransfer-Encoding: chunked\r\nETag: \"z\"\r\n\r\n";
        // Through the GATED seam — the one the serving paths cross. On a clean
        // CRLF head the gate forwards, and forwards the identical block bytes
        // (`Reactor.ProxyForward.respGate_clean`), so this pins the marshalling of
        // the seam that actually serves rather than of a retired twin.
        assert_eq!(forward_response_head_gated(head), Some(want.to_vec()));
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
    /// run through the proven response transform ([`forward_response_head_gated`] —
    /// strip hop-by-hop, add `Via`) and connection-annotated for the host's keep-alive
    /// decision, followed by the upstream body VERBATIM. The proxy transforms only
    /// the head; the body is byte-identical to the upstream's.
    #[cfg(target_os = "linux")]
    fn expected_client(canned: &[u8], keepalive: bool) -> Vec<u8> {
        crate::http::boot_test_runtime();
        let he = find(canned, b"\r\n\r\n").unwrap() + 4;
        let mut head = forward_response_head_gated(&canned[..he])
            .expect("canned upstream head is clean CRLF, so the gate forwards it");
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
