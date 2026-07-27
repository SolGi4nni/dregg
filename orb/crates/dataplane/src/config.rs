//! Load — and at runtime RE-load — an ARBITRARY operator deployment config.
//!
//! When `DRORB_CONFIG=<file>` is set, the host reads that file and crosses the
//! proven `drorb_deployment_of_config` parser at boot. The parser
//! (`Dsl.Config.parseChars` + `denoteOn defaultDeployment`, parse-soundness
//! `Dsl.Config.parse_render`) returns the runtime projections of the denoted
//! `DeploymentConfig`: the LB-policy byte the reverse-proxy dial runs, and the
//! declared layer-4 listener bindings. The host caches those and drives the
//! running serve from them — so the composition the operator WROTE runs, not a
//! selection among hard-coded named deployments.
//!
//! ## Runtime reconfiguration (SIGHUP)
//!
//! The cached deployment lives behind an atomically-swappable cell rather than a
//! write-once slot. On SIGHUP (`reconfig`), the host RE-reads `DRORB_CONFIG`,
//! re-parses it through the SAME proven parser, and — only if it parses —
//! swaps in the new deployment for every subsequent request. The swap is a
//! single `RwLock` write of an `Arc`; a request already in flight holds its own
//! `Arc` snapshot (`get`) and finishes under the config it started on, while the
//! next request picks up the new one. That refcount IS the drain window: the old
//! deployment object stays alive exactly as long as an in-flight request still
//! references it (see `reconfig` for the correspondence to the proven `Drain`).
//! A parse failure leaves the cell untouched — the running config is kept
//! (fail-safe).
//!
//! No Lean value is held across the FFI: the parse happens once per (re)load,
//! its projections are plain bytes, and each per-request step re-threads the
//! cached LB byte to `drorb_serve_step_pol` (whose chain is
//! `Dsl.Config.dialChainOfByte`, provably the denoted deployment's `dialChain`
//! for the parsed pool).

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock, RwLock};

use crate::serve::{Seam, ServeGateway};

// ---------------------------------------------------------------------------
// SAFE-BY-DEFAULT DoS gate values.
//
// The reactor accept/body path reads the gates below through the `pub fn`
// projections. Historically every gate defaulted to `0` (OFF), so a stock
// deploy — DRORB_CONFIG unset, or set without the DoS directives — ran with NO
// connection cap, NO rate limit, NO slowloris timeout and NO body cap: wide
// open. These constants make each gate default to a sane NON-ZERO value that is
// ON out of the box yet fully overridable from the operator config grammar:
//
//   * an ABSENT directive now yields the SAFE DEFAULT below (not `0`);
//   * an EXPLICIT directive overrides it — INCLUDING an explicit `0`, which is
//     the documented way to DISABLE a gate (`0` = unlimited, unchanged);
//
// so the config-as-data path is untouched: the operator still tunes every value,
// but the *default* is now the one we would defend rather than "off". The values
// are chosen comfortably above ordinary (and localhost-conformance) traffic so a
// legitimate client is never gated, while a single abusive source is bounded.

/// Default per-source CONCURRENT-connection cap (`max-connections`). Bounds one
/// source below the host's global/per-shard ceilings so a single IP cannot
/// monopolize the accept pool. `0` (explicit) disables.
pub const DEFAULT_MAX_CONNECTIONS: u32 = 512;

/// Default per-source request-arrival cap per `rate-window` (`rate-limit`).
/// Bounds a connection/arrival flood from one source; ~20x above the peak
/// localhost conformance connection rate. `0` (explicit) disables.
pub const DEFAULT_RATE_LIMIT: u32 = 2000;

/// Default rate-limit window width in ms (`rate-window`). Always positive.
pub const DEFAULT_RATE_WINDOW_MS: u64 = 1000;

/// Default slowloris header-completion timeout in ms (`slowloris-timeout`): a
/// connection whose request headers do not complete within this span after
/// accept is dropped with `408`. Well above any real client's header phase
/// (which completes in well under a second). `0` (explicit) disables.
pub const DEFAULT_SLOWLORIS_MS: u64 = 30_000;

/// Default maximum request-body size in bytes (`max-body-size`): 128 MiB. Bounds
/// per-request memory against an unbounded upload while remaining generous for
/// ordinary payloads. `0` (explicit) disables.
pub const DEFAULT_MAX_BODY_SIZE: u64 = 128 * 1024 * 1024;

/// Default PER-CONNECTION burst capacity (`burst-cap`): the most requests ONE
/// connection may issue before any time passes. A browser multiplexes a whole page
/// over one HTTP/2 connection and reuses one keep-alive connection across a page too
/// — nginx and h2o default `SETTINGS_MAX_CONCURRENT_STREAMS` to 128 and 100, and a
/// heavy page is two to four hundred subresources — so this sits above the heaviest
/// realistic page load while still bounding what one connection can fire.
///
/// THIS IS NOT the per-source arrival limit (`rate-limit`) nor the per-source
/// connection cap (`max-connections`): three different bounds over three different
/// quantities. See `Reactor/Stage/Rate.lean` for the table. `0` (explicit) disables.
///
/// The value the proven gate used to carry was `8`, as a Lean literal no directive
/// could reach: a default deploy answered `429` to the ninth request on one
/// keep-alive connection.
pub const DEFAULT_BURST_CAP: u32 = 512;

/// Default PER-CONNECTION refill rate in tokens per elapsed second (`burst-refill`):
/// the sustained request rate ONE connection may hold once its burst is spent. Far
/// above a browser (which is bounded by round trips and rendering) and above an
/// ordinary API client, while a request cannon on a single connection is held to
/// this rate. `0` (explicit) makes the burst a hard per-connection budget with no
/// recovery — a latch, not a bucket — so it is a deliberate choice, not a default.
/// The value the proven gate used to carry was `1`.
pub const DEFAULT_BURST_REFILL: u32 = 64;

/// The runtime projections of a parsed `DeploymentConfig`.
pub struct Deployment {
    /// The LB-policy byte the parsed pool declared. Threaded (byte 0) to
    /// `drorb_serve_step_pol` so the running dial runs the config's policy.
    pub lb_policy: u8,
    /// The declared L4 listener lines (`bind\tpool\tmode\tid,id,…`), in order.
    pub l4_binds: Vec<String>,
    /// The raw config-file bytes, prepended to each HTTP request crossing the
    /// `drorb_serve_cfg` route-table seam (the proven parser re-parses them; the
    /// parse-soundness theorem guarantees the recovered `ParsedConfig`).
    pub config_text: Vec<u8>,
    /// Number of routes the config declares. When `> 0`, HTTP requests are served
    /// through `drorb_serve_cfg` (the config's route table); when `0`, the default
    /// (metered) serve runs unchanged.
    pub route_count: u32,
    /// The hostnames whose virtual-host block declares a reverse-proxy route
    /// (`vproxy` projection lines). A request whose `Host` header names one of these
    /// is forwarded host-side to the configured backend fleet — the proven pick still
    /// chooses the backend. The `hostGlob` served path answers such a route with a
    /// placeholder, so the real forward is decided here.
    pub vproxy_hosts: Vec<String>,
}

impl Deployment {
    /// Does the config declare its own route table?
    pub fn has_routes(&self) -> bool {
        self.route_count > 0
    }

    /// Is this request's `Host` a declared reverse-proxy virtual host? Reads the
    /// `Host` request header (case-insensitive name, value trimmed of an optional
    /// `:port`) and checks membership in `vproxy_hosts`.
    pub fn is_vhost_proxy(&self, req: &[u8]) -> bool {
        if self.vproxy_hosts.is_empty() {
            return false;
        }
        match host_header(req) {
            Some(h) => self.vproxy_hosts.iter().any(|v| v.as_str() == h),
            None => false,
        }
    }
}

/// Extract the `Host` request-header value (name matched case-insensitively, an
/// optional `:port` stripped), as a `&str` borrowed from the request bytes.
fn host_header(req: &[u8]) -> Option<&str> {
    // Skip the request line.
    let mut rest = req;
    let line_end = rest.windows(2).position(|w| w == b"\r\n")?;
    rest = &rest[line_end + 2..];
    loop {
        let end = rest.windows(2).position(|w| w == b"\r\n")?;
        if end == 0 {
            return None; // end of headers
        }
        let line = &rest[..end];
        if let Some(colon) = line.iter().position(|&b| b == b':') {
            let (name, val) = line.split_at(colon);
            if name.eq_ignore_ascii_case(b"host") {
                let v = &val[1..]; // drop the ':'
                let s = std::str::from_utf8(v).ok()?.trim();
                return Some(s.split(':').next().unwrap_or(s));
            }
        }
        rest = &rest[end + 2..];
    }
}

impl Deployment {
    /// The bind address of the first declared L4 listener, if any.
    pub fn first_l4_bind(&self) -> Option<&str> {
        self.l4_binds
            .first()
            .and_then(|line| line.split('\t').next())
            .filter(|b| !b.is_empty())
    }
}

/// The atomically-swappable active deployment. `None` when no valid
/// `DRORB_CONFIG` is in force (the host then runs the byte-identical default
/// path). Reads take a read lock and clone the `Arc` (cheap); a (re)load takes
/// the write lock and replaces the slot.
static CELL: OnceLock<RwLock<Option<Arc<Deployment>>>> = OnceLock::new();

/// The config generation: `0` before any config is applied; incremented on every
/// successful (re)load. Surfaced by `/metrics` as `drorb_config_generation`.
static GENERATION: AtomicU64 = AtomicU64::new(0);

fn cell() -> &'static RwLock<Option<Arc<Deployment>>> {
    CELL.get_or_init(|| RwLock::new(None))
}

/// The current config generation (0 = default / none applied).
pub fn generation() -> u64 {
    GENERATION.load(Ordering::SeqCst)
}

/// The raw `DRORB_CONFIG` file bytes, cached at boot (and on reload) INDEPENDENT of
/// whether the proven ROUTE parser accepted them. The metered serve seam scans these
/// for the middleware POLICY directives (`max-body-size` / `allow-method` /
/// `allow-host`) via the proven `Reactor.Deploy.parsePolicy`, so an operator policy is
/// enforced on the default serve even by a config the route grammar does not model.
/// Empty when `DRORB_CONFIG` is unset / unreadable — the byte-identical default.
static RAW: OnceLock<RwLock<Vec<u8>>> = OnceLock::new();

fn raw_cell() -> &'static RwLock<Vec<u8>> {
    RAW.get_or_init(|| RwLock::new(Vec::new()))
}

/// The per-source concurrent-connection cap parsed from the `max-connections <n>`
/// directive in `DRORB_CONFIG` (the SAME operator config grammar as the proven
/// `Reactor.Deploy.parsePolicyLine`, space-separated, one directive per line).
/// `0` means NO limit — mirroring the proven `Reactor.Stage.ConnLimit.admits`,
/// whose cap `0` always admits. Now SAFE-BY-DEFAULT: initialized to
/// `DEFAULT_MAX_CONNECTIONS` (ON before any config load), overridden by an
/// explicit `max-connections` directive (including an explicit `0` to disable). A
/// lock-free atomic: written on load/reload (`set_raw`), read on the accept hot
/// path (`max_connections`) with no lock.
static MAX_CONNECTIONS: AtomicU64 = AtomicU64::new(DEFAULT_MAX_CONNECTIONS as u64);

/// The active per-source connection cap (`0` = unlimited). Read on every accept by
/// the reactors (`uring`/`kqueue`/`blocking`); a plain relaxed atomic load.
pub fn max_connections() -> u32 {
    MAX_CONNECTIONS.load(Ordering::Relaxed) as u32
}

/// The per-source REQUEST-RATE cap parsed from the `rate-limit <n>` directive: at
/// most `n` request arrivals from one source within each `rate-window` before the
/// reactor answers `429 Too Many Requests` at accept (the wire form of the proven
/// `Reactor.Stage.StickTable.resp429` / `Reactor.Stage.Rate.resp429`). `0` = NO
/// limit — mirroring the proven admission rule, whose `0` threshold always
/// admits. Now SAFE-BY-DEFAULT: initialized to `DEFAULT_RATE_LIMIT` (ON before
/// any config load), overridden by an explicit `rate-limit` directive (`0`
/// disables). A lock-free atomic, read on the accept hot path.
static RATE_LIMIT: AtomicU64 = AtomicU64::new(DEFAULT_RATE_LIMIT as u64);

/// The rate-limit sliding-window length in MILLISECONDS (`rate-window <ms>`), the
/// span over which `rate-limit` arrivals are counted before the window ages
/// (resets). Defaults to 1000 ms; the window slides so a source that pauses for a
/// full window recovers (the counter ages — no leak).
static RATE_WINDOW_MS: AtomicU64 = AtomicU64::new(DEFAULT_RATE_WINDOW_MS);

/// The slowloris header-arrival timeout in MILLISECONDS (`slowloris-timeout <ms>`):
/// a connection whose request headers do NOT complete within this span after accept
/// is dropped with `408 Request Timeout` (the wire form of the proven
/// `Reactor.Stage.Slowloris.resp408`). `0` = disabled, mirroring the proven
/// `expired`, whose `0` timeout never expires. Now SAFE-BY-DEFAULT: initialized to
/// `DEFAULT_SLOWLORIS_MS` (ON before any config load), overridden by an explicit
/// `slowloris-timeout` directive (`0` disables).
static SLOWLORIS_MS: AtomicU64 = AtomicU64::new(DEFAULT_SLOWLORIS_MS);

/// The maximum request-body size in BYTES (`max-body-size <n>`): a request whose
/// body exceeds this — a declared `Content-Length` over the cap, OR a chunked /
/// streamed body whose ACTUAL accumulated bytes pass the cap mid-stream — is refused
/// `413 Content Too Large` and the connection is cut. `0` = disabled (directive
/// absent / unparsable), mirroring the proven `Reactor.Stage.BodyLimit` cap: the
/// enforcement counts the actual streamed bytes, so a chunked upload with NO
/// `Content-Length` cannot bypass it. Read on the body-read hot path. Now
/// SAFE-BY-DEFAULT: initialized to `DEFAULT_MAX_BODY_SIZE` (ON before any config
/// load), overridden by an explicit `max-body-size` directive (`0` disables).
static MAX_BODY_SIZE: AtomicU64 = AtomicU64::new(DEFAULT_MAX_BODY_SIZE);

/// The PER-CONNECTION burst capacity parsed from the `burst-cap <n>` directive — the
/// operator's value for the proven `Reactor.Stage.Rate` token bucket's capacity. `0`
/// means NO per-connection limit, mirroring the proven
/// `Reactor.Stage.Rate.admitsAt_unlimited`. SAFE-BY-DEFAULT (`DEFAULT_BURST_CAP`).
/// A lock-free atomic: written on load/reload, read on the serve path.
static BURST_CAP: AtomicU64 = AtomicU64::new(DEFAULT_BURST_CAP as u64);

/// The PER-CONNECTION refill rate parsed from the `burst-refill <n>` directive, in
/// tokens per elapsed second — the operator's value for the same bucket's `rate`.
/// SAFE-BY-DEFAULT (`DEFAULT_BURST_REFILL`).
static BURST_REFILL: AtomicU64 = AtomicU64::new(DEFAULT_BURST_REFILL as u64);

/// The active per-source request-rate cap (`0` = unlimited). Read on every accept.
pub fn rate_limit() -> u32 {
    RATE_LIMIT.load(Ordering::Relaxed) as u32
}

/// The active PER-CONNECTION burst capacity (`0` = unlimited). Read once per request
/// on the serve path and CROSSED to the fold, where the proven
/// `Reactor.Stage.Rate.admitsAt` decides — no comparison happens on this side.
pub fn burst_cap() -> u32 {
    BURST_CAP.load(Ordering::Relaxed) as u32
}

/// The active PER-CONNECTION refill rate, tokens per elapsed second. Crossed, not
/// compared: the proven bucket does the refill.
pub fn burst_refill() -> u32 {
    BURST_REFILL.load(Ordering::Relaxed) as u32
}

/// The active request-body byte cap (`0` = unlimited). Read on the body-read hot path
/// by every reactor; a relaxed atomic load.
pub fn max_body_size() -> usize {
    MAX_BODY_SIZE.load(Ordering::Relaxed) as usize
}

/// The active rate-limit window (defaults to 1000 ms; never zero, so the window
/// always has positive width and the counter deterministically ages).
pub fn rate_window() -> std::time::Duration {
    std::time::Duration::from_millis(RATE_WINDOW_MS.load(Ordering::Relaxed).max(1))
}

/// The active slowloris header timeout (`Duration::ZERO` = disabled). Read on every
/// accept and on the header-read sweep by the reactors.
pub fn slowloris_timeout() -> std::time::Duration {
    std::time::Duration::from_millis(SLOWLORIS_MS.load(Ordering::Relaxed))
}

/// Scan the raw config bytes for the LAST `max-connections <n>` directive (a total
/// scan). An absent directive yields the SAFE DEFAULT (`DEFAULT_MAX_CONNECTIONS`,
/// ON); an EXPLICIT directive overrides it, INCLUDING an explicit `0` which
/// disables the gate (`0` = unlimited). Mirrors `parsePolicyLine`'s
/// whitespace-tokenized match so the Rust reactor reads the same directive the
/// proven serve-level `MwPolicy` does.
fn scan_max_connections(bytes: &[u8]) -> u32 {
    let text = String::from_utf8_lossy(bytes);
    let mut cap: u32 = DEFAULT_MAX_CONNECTIONS;
    for line in text.lines() {
        let toks: Vec<&str> = line.split_whitespace().collect();
        if let ["max-connections", n] = toks.as_slice() {
            if let Ok(v) = n.parse::<u32>() {
                cap = v;
            }
        }
    }
    cap
}

/// Scan the raw config bytes for the LAST occurrence of each accept-path DoS
/// directive (same whitespace-tokenized grammar as `max-connections`), returning
/// `(rate_limit, rate_window_ms, slowloris_ms, max_body)`. An absent directive
/// keeps its SAFE DEFAULT (`DEFAULT_RATE_LIMIT`, `DEFAULT_RATE_WINDOW_MS`,
/// `DEFAULT_SLOWLORIS_MS`, `DEFAULT_MAX_BODY_SIZE` — all ON); an EXPLICIT directive
/// overrides it, INCLUDING an explicit `0` which disables that gate.
fn scan_dos_directives(bytes: &[u8]) -> (u32, u64, u64, u64, u32, u32) {
    let text = String::from_utf8_lossy(bytes);
    let mut rate: u32 = DEFAULT_RATE_LIMIT;
    let mut window_ms: u64 = DEFAULT_RATE_WINDOW_MS;
    let mut slow_ms: u64 = DEFAULT_SLOWLORIS_MS;
    let mut max_body: u64 = DEFAULT_MAX_BODY_SIZE;
    let mut burst_cap: u32 = DEFAULT_BURST_CAP;
    let mut burst_refill: u32 = DEFAULT_BURST_REFILL;
    for line in text.lines() {
        let toks: Vec<&str> = line.split_whitespace().collect();
        match toks.as_slice() {
            ["rate-limit", n] => {
                if let Ok(v) = n.parse::<u32>() {
                    rate = v;
                }
            }
            ["rate-window", n] => {
                if let Ok(v) = n.parse::<u64>() {
                    window_ms = v.max(1);
                }
            }
            ["slowloris-timeout", n] => {
                if let Ok(v) = n.parse::<u64>() {
                    slow_ms = v;
                }
            }
            ["max-body-size", n] => {
                if let Ok(v) = n.parse::<u64>() {
                    max_body = v;
                }
            }
            ["burst-cap", n] => {
                if let Ok(v) = n.parse::<u32>() {
                    burst_cap = v;
                }
            }
            ["burst-refill", n] => {
                if let Ok(v) = n.parse::<u32>() {
                    burst_refill = v;
                }
            }
            _ => {}
        }
    }
    (rate, window_ms, slow_ms, max_body, burst_cap, burst_refill)
}

/// A clone of the raw `DRORB_CONFIG` bytes (empty when none is in force). The seam
/// scans this for the middleware-policy directives; a directive-free config yields the
/// empty policy and the byte-identical default serve (`serveUnderPolicyMetered_default`).
pub fn raw_text() -> Vec<u8> {
    raw_cell().read().unwrap().clone()
}

/// Cache the raw config bytes for the policy scan (called by `load`/`reload`).
fn set_raw(bytes: &[u8]) {
    *raw_cell().write().unwrap() = bytes.to_vec();
    // Re-derive the reactor-level connection cap from the same bytes, so a SIGHUP
    // reload retunes the accept-path gate atomically alongside the serve config.
    MAX_CONNECTIONS.store(scan_max_connections(bytes) as u64, Ordering::Relaxed);
    // Likewise re-derive the request-rate + slowloris + body-size gates from the
    // same directive grammar, retuned atomically on every (re)load.
    let (rate, window_ms, slow_ms, max_body, burst_cap, burst_refill) = scan_dos_directives(bytes);
    RATE_LIMIT.store(rate as u64, Ordering::Relaxed);
    RATE_WINDOW_MS.store(window_ms, Ordering::Relaxed);
    SLOWLORIS_MS.store(slow_ms, Ordering::Relaxed);
    MAX_BODY_SIZE.store(max_body, Ordering::Relaxed);
    // The PER-CONNECTION burst parameters, retuned on the same (re)load. They are
    // CROSSED to the proven fold, never compared here.
    BURST_CAP.store(burst_cap as u64, Ordering::Relaxed);
    BURST_REFILL.store(burst_refill as u64, Ordering::Relaxed);
}

/// The outcome of a runtime reload (SIGHUP).
pub enum ReloadOutcome {
    /// The new config parsed and was swapped in; carries the new generation.
    Applied { generation: u64 },
    /// The new config FAILED to parse (or could not be read); the running config
    /// was kept (fail-safe). `reason` describes why.
    KeptOld { reason: String },
    /// `DRORB_CONFIG` is unset — there is nothing to reload.
    NoConfig,
}

/// Boot-time load: read `DRORB_CONFIG` (once) and install it as generation 1.
/// `None`/unreadable/unparseable ⇒ the cell stays empty and the host runs the
/// byte-identical default path. Must be called on / after the serve gateway is up.
pub fn load(gw: &ServeGateway) {
    let path = match std::env::var("DRORB_CONFIG") {
        Ok(p) => p,
        Err(_) => return, // no config: default deployment
    };
    // Cache the raw bytes for the middleware-policy scan REGARDLESS of whether the
    // route parser accepts them — the policy directives are enforced on the default
    // serve even if the route grammar does not model the file.
    if let Ok(bytes) = std::fs::read(&path) {
        set_raw(&bytes);
    }
    match parse_from_path(gw, &path) {
        Ok(dep) => {
            eprintln!(
                "dataplane: DRORB_CONFIG={path} PARSED by the proven core -> lb_policy={}, {} route(s), {} L4 listener(s)",
                dep.lb_policy,
                dep.route_count,
                dep.l4_binds.len()
            );
            *cell().write().unwrap() = Some(Arc::new(dep));
            GENERATION.store(1, Ordering::SeqCst);
        }
        Err(reason) => {
            eprintln!("dataplane: DRORB_CONFIG={path}: {reason}; using default");
        }
    }
}

/// Runtime reload (SIGHUP): re-read `DRORB_CONFIG`, re-parse it via the proven
/// parser, and — only if it parses — atomically swap it in as the new
/// generation. On any read/parse failure the running config is kept untouched
/// (fail-safe). Callable at any time from the reconfig watcher thread.
pub fn reload(gw: &ServeGateway) -> ReloadOutcome {
    let path = match std::env::var("DRORB_CONFIG") {
        Ok(p) => p,
        Err(_) => return ReloadOutcome::NoConfig,
    };
    if let Ok(bytes) = std::fs::read(&path) {
        set_raw(&bytes);
    }
    match parse_from_path(gw, &path) {
        Ok(dep) => {
            // The atomic swap: the write lock publishes the new Arc. A request
            // mid-flight holds an older Arc (from `get`) and finishes under it;
            // the next `get` returns the new one. No request observes a torn
            // config, and none is dropped — the old object drains out on its
            // last referent.
            *cell().write().unwrap() = Some(Arc::new(dep));
            let generation = GENERATION.fetch_add(1, Ordering::SeqCst) + 1;
            ReloadOutcome::Applied { generation }
        }
        Err(reason) => ReloadOutcome::KeptOld { reason },
    }
}

/// Whether the deployment is BRAID-marked (`DRORB_BRAID=1`): the running metered serve
/// then folds over `Reactor.Deploy.braidedDeployment` (the proven forward-auth gate +
/// request-id echo composed at the head of the deployed chain) instead of
/// `defaultDeployment`. Read once (env is fixed for the process lifetime);
/// `1`/`true`/`yes`/`on` enable. Unset ⇒ the default metered serve is byte-identical to
/// today (`servePipelineOfMetered_default` anchor intact).
pub fn braid_enabled() -> bool {
    static BRAID: OnceLock<bool> = OnceLock::new();
    *BRAID.get_or_init(|| {
        std::env::var("DRORB_BRAID")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

/// A snapshot of the active deployment, if a valid config is in force. Returns an
/// `Arc` clone (cheap), so the caller keeps the config it observed alive for the
/// whole request even if a concurrent reload swaps the cell.
pub fn get() -> Option<Arc<Deployment>> {
    cell().read().unwrap().clone()
}

/// Read a config file and cross the proven parser. `Ok(dep)` when it parses;
/// `Err(reason)` on an unreadable file or a parser rejection (the caller keeps
/// the old config / falls back to default). Crosses the runtime-owner thread via
/// `gw`.
fn parse_from_path(gw: &ServeGateway, path: &str) -> Result<Deployment, String> {
    let text = std::fs::read(path).map_err(|e| format!("cannot read ({e})"))?;
    let (tx, rx) = std::sync::mpsc::channel();
    let mut input = gw.pool().take();
    input.clear();
    input.extend_from_slice(&text);
    let out = gw
        .call_seam(input, Seam::DeploymentOfConfig, &tx, &rx)
        .ok_or_else(|| "serve thread gone".to_string())?;
    if out.is_empty() {
        return Err("did not parse (proven parser returned none)".to_string());
    }
    let s = String::from_utf8_lossy(&out);
    // The projection lines are prefix-tagged, so scan by tag (order-robust):
    //   lb\t<byte>            — the LB policy byte
    //   routes\t<count>       — the number of declared routes
    //   bind\tpool\tmode\tids — one per declared L4 listener
    let mut lb_policy: Option<u8> = None;
    let mut route_count: u32 = 0;
    let mut l4_binds: Vec<String> = Vec::new();
    let mut vproxy_hosts: Vec<String> = Vec::new();
    for line in s.lines() {
        if let Some(b) = line.strip_prefix("lb\t") {
            lb_policy = b.parse::<u8>().ok();
        } else if let Some(n) = line.strip_prefix("routes\t") {
            route_count = n.parse::<u32>().unwrap_or(0);
        } else if let Some(h) = line.strip_prefix("vproxy\t") {
            vproxy_hosts.push(h.to_string());
        } else if !line.is_empty() {
            l4_binds.push(line.to_string());
        }
    }
    let lb_policy = lb_policy.ok_or_else(|| "parser returned no lb policy".to_string())?;
    Ok(Deployment {
        lb_policy,
        l4_binds,
        config_text: text,
        route_count,
        vproxy_hosts,
    })
}
