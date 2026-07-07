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
