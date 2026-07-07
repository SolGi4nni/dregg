//! The native dataplane: a real keep-alive, concurrent HTTP/1.1 host whose
//! request-handling core is the leanc-compiled proven serve.
//!
//! Every crossing of the boundary is one call to the exported `drorb_serve`
//! (`ByteArray -> ByteArray`), the same proven pipeline the shipped binaries
//! run. This host owns the sockets, the accept loop, and the connection
//! lifecycle; it never rewrites a request or a response. The bytes read off the
//! wire go in unchanged and the proven response bytes go back out unchanged. The
//! host reads only HTTP/1.1 *framing* metadata — message length and connection
//! disposition — so it knows where one request ends and the next begins and
//! whether to keep the connection open. The meaning of every request is decided
//! solely by the proven core.
//!
//! ## Structure
//!
//! - `serve`    — the Lean seam: boot the runtime and cross it, on one owner
//!                thread; the gateway other threads use to reach it.
//! - `pool`     — a fixed pool of reusable byte buffers; zero steady-state
//!                host-side allocation on the request hot path.
//! - `http`     — IO-agnostic HTTP/1.1 framing shared by both IO paths.
//! - `uring`    — the high-performance Linux IO path: per-core io_uring shards
//!                (preferred on Linux).
//! - `blocking` — the portable thread-per-connection fallback (macOS and other
//!                platforms; also selectable on Linux for comparison).

use std::net::{TcpListener, ToSocketAddrs};
use std::sync::atomic::{AtomicBool, AtomicUsize};

/// Opt-in access logging (env `DRORB_ACCESS_LOG`): one structured line per served
/// request, emitted from the host serve loop — outside the proven core.
mod access_log;
/// The gated operator admin listener (`DRORB_ADMIN_LISTEN`): `GET /metrics` +
/// `/healthz`, plus the operational endpoints `/admin/config`, `/admin/backends`,
/// `POST /admin/drain`, `POST /admin/reload`. Untrusted-shell observability and
/// the two already-proven levers (config reload, graceful drain); separate from
/// the serve listeners.
mod admin;
mod blocking;
/// Dataplane-side response cache (store + coalescing) for the proven core's
/// cacheability decision. Wired into the serve path by the hook reported
/// alongside this module; unused from non-test code until that hook lands.
#[allow(dead_code)]
mod cache;
/// Boot-time load of an arbitrary operator `DeploymentConfig` (DRORB_CONFIG) via
/// the proven `drorb_deployment_of_config` parser — the config→deployment path.
mod config;
mod http;
/// The effect/continuation interpreter loop: a dumb executor that drives the
/// proven resumable serve (`drorb_serve_step`/`drorb_serve_resume`), executing
/// yielded effects (SEED: proxyDial). Opt-in via `DRORB_EFFECT_SEAM=1`.
mod interp;
/// The layer-4 (raw TCP / UDP) passthrough listener: accept, choose the upstream
/// via the proven `drorb_proxy_pick`, dial it, and splice bytes verbatim. The
/// running host shell of the proven `Reactor.L4` forwarding model. Binds only
/// when `DRORB_L4_LISTEN` (TCP) / `DRORB_L4_UDP` (UDP) is set.
mod l4;
/// A lightweight operational metrics surface (request/status/byte/backend
/// counters) and the gated admin listener (`DRORB_ADMIN_LISTEN`) exposing
/// `GET /metrics` + `GET /healthz`. Untrusted-shell observability, incremented
/// from the host serve loop — outside the proven core.
mod metrics;
mod pool;
mod proxy_dial;
mod proxy_hook;
/// Runtime reconfiguration on SIGHUP: re-read + re-parse `DRORB_CONFIG` and
/// atomically swap the active config, draining in-flight requests per the proven
/// `Drain` discipline. The untrusted shell that executes the proven drain decision.
mod reconfig;
mod serve;
/// The HTTPS front door: a TLS 1.3 listener that terminates real TLS in-process
/// over the verified server handshake + record layer, then serves each decrypted
/// request through the proven core. Binds only when `DRORB_TLS_LISTEN` is set;
/// the plaintext listener is unaffected.
mod tls;
mod udp;
#[cfg(target_os = "linux")]
mod uring;
mod ws;

/// Set once a SIGINT is received; the IO paths observe it and stop.
pub static SHUTDOWN: AtomicBool = AtomicBool::new(false);

/// Count of connection threads currently in flight, for the blocking path's
/// soft cap.
pub static ACTIVE_CONNS: AtomicUsize = AtomicUsize::new(0);

extern "C" fn on_sigint(_sig: i32) {
    SHUTDOWN.store(true, std::sync::atomic::Ordering::SeqCst);
}

unsafe extern "C" {
    fn signal(signum: i32, handler: usize) -> usize;
}

const SIGINT: i32 = 2;

/// Which IO path to run.
#[derive(Clone, Copy, PartialEq)]
enum IoMode {
    /// io_uring on Linux, blocking elsewhere.
    Auto,
    /// Force the blocking thread-per-connection path.
    Blocking,
    /// Force the io_uring path (Linux only).
    Uring,
}

struct Config {
    bind: String,
    io: IoMode,
    /// io_uring shard count — read only by the Linux io_uring path.
    #[cfg_attr(not(target_os = "linux"), allow(dead_code))]
    shards: usize,
    /// UDP bind address for the QUIC/HTTP-3 datagram path, or `None` to disable
    /// it. Defaults to the same HOST:PORT as `bind` (TCP and UDP are separate
    /// namespaces, so one process serves both on the one port number).
    udp: Option<String>,
}

fn usage() {
    eprintln!(
        "\
drorb dataplane — a keep-alive, concurrent HTTP/1.1 host driving the
leanc-compiled proven serve.

USAGE:
    dataplane [ADDR]
    dataplane --bind ADDR [--io auto|blocking|uring] [--shards N]
              [--udp ADDR | --no-udp]
    dataplane --help

ADDR is HOST:PORT (e.g. 127.0.0.1:8080 or 0.0.0.0:443) or a bare PORT
(e.g. 8080), which binds 127.0.0.1. If omitted, the DRORB_BIND environment
variable is used, else 127.0.0.1:8080.

This one process serves, over real sockets, every protocol through the
leanc-compiled proven serve:
  - TCP: HTTP/1.1 and h2c (HTTP/2 cleartext prior-knowledge, forked to the real
    H2 engine) via `drorb_serve`, and WebSocket (RFC 6455 Upgrade kept open,
    every frame through the proven `drorb_serve_ws_frame`);
  - UDP: QUIC Initial packets, decrypted by verified EverCrypt packet protection
    and dispatched through the proven HTTP/3 path (`drorb_serve_datagram`).

--io selects the TCP IO path: 'auto' (io_uring on Linux, blocking elsewhere),
'blocking' (thread-per-connection), or 'uring' (Linux io_uring). Overridable
via DRORB_IO. --shards sets the io_uring shard count (default: CPU count),
overridable via DRORB_SHARDS. --udp sets the QUIC/UDP bind (default: same
HOST:PORT as ADDR; DRORB_UDP overrides); --no-udp disables it.

The meaning of every request is decided solely by the proven core; the host
owns only the sockets, the accept/recv loops, HTTP/1.1 framing, and the RFC 6455
handshake token. SIGINT stops it."
    );
}

/// Normalize an ADDR argument: a bare port binds 127.0.0.1; HOST:PORT is used
/// verbatim.
fn normalize_addr(a: &str) -> String {
    if a.parse::<u16>().is_ok() {
        format!("127.0.0.1:{a}")
    } else {
        a.to_string()
    }
}

fn parse_io(s: &str) -> IoMode {
    match s {
        "auto" => IoMode::Auto,
        "blocking" => IoMode::Blocking,
        "uring" => IoMode::Uring,
        other => {
            eprintln!("dataplane: unknown --io mode {other} (want auto|blocking|uring)");
            std::process::exit(2);
        }
    }
}

fn default_shards() -> usize {
    std::env::var("DRORB_SHARDS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        })
}

fn parse_config() -> Config {
    let mut args = std::env::args().skip(1);
    let mut bind: Option<String> = None;
    let mut io: Option<IoMode> = None;
    let mut shards: Option<usize> = None;
    let mut udp: Option<String> = None;
    let mut no_udp = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "-h" | "--help" => {
                usage();
                std::process::exit(0);
            }
            "--bind" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --bind needs an ADDR argument");
                    std::process::exit(2);
                });
                bind = Some(normalize_addr(&v));
            }
            "--io" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --io needs a mode argument");
                    std::process::exit(2);
                });
                io = Some(parse_io(&v));
            }
            "--shards" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --shards needs a count argument");
                    std::process::exit(2);
                });
                shards = Some(v.parse().unwrap_or_else(|_| {
                    eprintln!("dataplane: --shards wants a positive integer");
                    std::process::exit(2);
                }));
            }
            "--udp" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --udp needs an ADDR argument");
                    std::process::exit(2);
                });
                udp = Some(normalize_addr(&v));
            }
            "--no-udp" => no_udp = true,
            other if other.starts_with('-') => {
                eprintln!("dataplane: unknown option {other}");
                usage();
                std::process::exit(2);
            }
            other => bind = Some(normalize_addr(other)),
        }
    }
    let bind = bind
        .or_else(|| std::env::var("DRORB_BIND").ok().map(|v| normalize_addr(&v)))
        .unwrap_or_else(|| "127.0.0.1:8080".to_string());
    let io = io
        .or_else(|| std::env::var("DRORB_IO").ok().map(|v| parse_io(&v)))
        .unwrap_or(IoMode::Auto);
    let shards = shards.unwrap_or_else(default_shards).max(1);
    // The QUIC/UDP path defaults to the same HOST:PORT as the TCP bind (separate
    // namespaces), overridable via --udp / DRORB_UDP, disabled by --no-udp.
    let udp = if no_udp {
        None
    } else {
        udp.or_else(|| std::env::var("DRORB_UDP").ok().map(|v| normalize_addr(&v)))
            .or_else(|| Some(bind.clone()))
    };
    Config {
        bind,
        io,
        shards,
        udp,
    }
}

/// The deployment selector the running host binds the accept surface from, read
/// from `DRORB_DEPLOYMENT`. `0` (unset / `default`) is the default deployment
/// (no declared L4 listener); `1` (`alt`) is the non-default deployment whose
/// `DeploymentConfig.l4Listeners` declares a raw-TCP passthrough.
fn deployment_selector() -> u8 {
    match std::env::var("DRORB_DEPLOYMENT").ok().as_deref() {
        Some("alt") | Some("1") => 1,
        _ => 0,
    }
}

/// Query the proven `drorb_l4_bind` projection for a deployment selector and
/// return the bind address of the first declared L4 listener, or `None` when the
/// deployment declares none. The projection output is newline-joined
/// `bind\tpool\tmode\tid,id,…` lines (`DeploymentConfig.l4Listeners`).
fn deployment_l4_bind(gw: &serve::ServeGateway, sel: u8) -> Option<String> {
    let (tx, rx) = std::sync::mpsc::channel();
    let mut input = gw.pool().take();
    input.push(sel);
    let out = gw.call_seam(input, serve::Seam::L4Bind, &tx, &rx)?;
    if out.is_empty() {
        return None;
    }
    let text = String::from_utf8_lossy(&out);
    let first = text.lines().next()?;
    let bind = first.split('\t').next()?;
    if bind.is_empty() {
        None
    } else {
        Some(bind.to_string())
    }
}

fn bind_listener(bind: &str) -> TcpListener {
    let addrs: Vec<_> = match bind.to_socket_addrs() {
        Ok(a) => a.collect(),
        Err(e) => {
            eprintln!("dataplane: cannot resolve bind address {bind}: {e}");
            std::process::exit(1);
        }
    };
    TcpListener::bind(&addrs[..]).unwrap_or_else(|e| {
        eprintln!("dataplane: bind {bind} failed: {e}");
        std::process::exit(1);
    })
}

fn main() {
    let cfg = parse_config();

    // Install the SIGINT handler before we bring anything up.
    // SAFETY: `on_sigint` is an `extern "C"` handler that only stores into an
    // atomic — async-signal-safe; installing it before any work is standard.
    unsafe { signal(SIGINT, on_sigint as *const () as usize) };

    // The shared buffer pool: request/response buffers up to a typical head+small
    // body reserve; retain a generous warm set so a burst does not thrash.
    let pool = pool::BufferPool::new(16 << 10, 4096);

    // Bring up the runtime on its dedicated owner thread; the gateway routes
    // every request there. Blocks until the runtime is up.
    let gw = serve::spawn_serve_thread(pool);

    // Load an ARBITRARY operator config (DRORB_CONFIG) through the proven parser,
    // ONCE, now that the runtime is up. When present, it drives the reverse-proxy
    // dial (config LB policy) and the L4 accept surface below; when absent the host
    // runs the byte-identical default. This is the config→deployment last mile.
    config::load(&gw);

    // Runtime reconfiguration: install the SIGHUP handler and spawn the watcher
    // that re-reads + re-parses DRORB_CONFIG and atomically swaps the active
    // config, draining in-flight requests per the proven Drain discipline.
    reconfig::install(gw.clone());

    // The gated admin listener (DRORB_ADMIN_LISTEN, a bare PORT binds localhost),
    // SEPARATE from the serve listeners: GET /metrics + /healthz, plus the
    // operational endpoints /admin/config, /admin/backends, POST /admin/drain,
    // POST /admin/reload. Bound only when the env var is set; the serve path is
    // unaffected. It carries a serve-gateway handle so /admin/reload crosses the
    // proven parser on the runtime-owner thread.
    if let Ok(admin_listen) = std::env::var("DRORB_ADMIN_LISTEN") {
        let admin_addr = normalize_addr(&admin_listen);
        let admin_listener = bind_listener(&admin_addr);
        let admin_local = admin_listener
            .local_addr()
            .map(|a| a.to_string())
            .unwrap_or_else(|_| admin_addr.clone());
        let gw_admin = gw.clone();
        std::thread::Builder::new()
            .name("drorb-admin".into())
            .spawn(move || admin::run_admin(admin_listener, gw_admin))
            .expect("failed to spawn the admin listener thread");
        eprintln!(
            "dataplane: admin surface on {admin_local} (GET /metrics, /healthz, /admin/config, \
             /admin/backends; POST /admin/drain, /admin/reload)"
        );
    }

    let listener = bind_listener(&cfg.bind);
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| cfg.bind.clone());

    // Bring up the QUIC/HTTP-3 datagram listener on its own thread, sharing the
    // one serve gateway (hence the one Lean runtime owner) with the TCP paths.
    // One process, both listeners live, every protocol through the proven serve.
    if let Some(udp_addr) = cfg.udp.clone() {
        let gw_udp = gw.clone();
        std::thread::Builder::new()
            .name("drorb-udp".into())
            .spawn(move || udp::run(&udp_addr, gw_udp))
            .expect("failed to spawn the UDP/QUIC listener thread");
    }

    // The HTTPS front door: an ADDITIONAL TLS 1.3 listener on DRORB_TLS_LISTEN
    // (HOST:PORT or a bare PORT). Each accepted connection is terminated in-process
    // over the VERIFIED TLS 1.3 server (handshake + record layer, `drorb_tls_serve`)
    // and served through the same proven core, then closed. The plaintext listener
    // below is unaffected — TLS is gated on the env var. Certificate material loads
    // once from DRORB_TLS_CERT / DRORB_TLS_SEED (self-signed conformance default).
    if let Ok(tls_listen) = std::env::var("DRORB_TLS_LISTEN") {
        let tls_addr = normalize_addr(&tls_listen);
        match tls::load_cert() {
            Some(cert) => {
                let tls_listener = bind_listener(&tls_addr);
                let tls_local = tls_listener
                    .local_addr()
                    .map(|a| a.to_string())
                    .unwrap_or_else(|_| tls_addr.clone());
                let gw_tls = gw.clone();
                std::thread::Builder::new()
                    .name("drorb-tls".into())
                    .spawn(move || tls::run(tls_listener, gw_tls, cert))
                    .expect("failed to spawn the TLS listener thread");
                eprintln!(
                    "dataplane: HTTPS front door on {tls_local} (verified TLS 1.3 terminate → the proven serve)"
                );
            }
            None => {
                eprintln!("dataplane: DRORB_TLS_LISTEN set but no usable cert — TLS listener not bound");
            }
        }
    }

    // The layer-4 (raw TCP / UDP) passthrough listeners. When a backend fleet is
    // configured (`DRORB_PROXY_BACKENDS`) and `DRORB_L4_LISTEN` / `DRORB_L4_UDP`
    // is set, bind a raw passthrough listener that forwards every connection /
    // datagram to the proven `drorb_proxy_pick` upstream, bytes verbatim — no
    // HTTP parsed. Shares the one serve gateway (hence the one Lean runtime owner)
    // and the same fleet the reverse-proxy lane uses.
    if let Some(fleet) = proxy_hook::fleet() {
        // The L4 TCP listen address: when a non-default deployment is selected
        // (`DRORB_DEPLOYMENT`), it is GENERATED from that deployment's
        // `DeploymentConfig.l4Listeners` projection (queried across `drorb_l4_bind`)
        // — a config-declared L4 listener is bound at deploy time. Otherwise it
        // falls back to the `DRORB_L4_LISTEN` env, so the existing behavior stands.
        // Highest priority: an arbitrary operator config's declared L4 listener,
        // parsed from DRORB_CONFIG by the proven core (DeploymentConfig.l4Listeners).
        let l4_from_config = config::get().and_then(|d| d.first_l4_bind().map(str::to_string));
        if let Some(b) = &l4_from_config {
            eprintln!(
                "dataplane: L4 bind {b} GENERATED from DRORB_CONFIG (arbitrary DeploymentConfig.l4Listeners)"
            );
        }
        let dep_sel = deployment_selector();
        let l4_from_cfg = if l4_from_config.is_none() && dep_sel != 0 {
            match deployment_l4_bind(&gw, dep_sel) {
                Some(b) => {
                    eprintln!(
                        "dataplane: L4 bind {b} GENERATED from deployment {dep_sel} (DeploymentConfig.l4Listeners)"
                    );
                    Some(b)
                }
                None => None,
            }
        } else {
            None
        };
        let l4_tcp = l4_from_config
            .or(l4_from_cfg)
            .or_else(|| std::env::var("DRORB_L4_LISTEN").ok());
        if let Some(l4_tcp) = l4_tcp {
            let addr = normalize_addr(&l4_tcp);
            let fleet = std::sync::Arc::clone(fleet);
            let gw_l4 = gw.clone();
            std::thread::Builder::new()
                .name("drorb-l4-tcp".into())
                .spawn(move || l4::run(&addr, fleet, gw_l4))
                .expect("failed to spawn the L4 TCP listener thread");
        }
        if let Ok(l4_udp) = std::env::var("DRORB_L4_UDP") {
            let addr = normalize_addr(&l4_udp);
            let fleet = std::sync::Arc::clone(fleet);
            let gw_l4 = gw.clone();
            std::thread::Builder::new()
                .name("drorb-l4-udp".into())
                .spawn(move || l4::run_udp(&addr, fleet, gw_l4))
                .expect("failed to spawn the L4 UDP listener thread");
        }
    }

    // Choose the IO path. io_uring is preferred on Linux; the blocking path is
    // the portable fallback and is also selectable on Linux for comparison.
    let use_uring = match cfg.io {
        IoMode::Auto => cfg!(target_os = "linux"),
        IoMode::Blocking => false,
        IoMode::Uring => {
            if !cfg!(target_os = "linux") {
                eprintln!("dataplane: --io uring requires Linux; falling back to blocking");
                false
            } else {
                true
            }
        }
    };

    #[cfg(target_os = "linux")]
    if use_uring {
        use std::os::fd::AsRawFd;
        eprintln!(
            "dataplane: listening on {local} (io_uring, {} shards, over the leanc-compiled proven serve; SIGINT to stop)",
            cfg.shards
        );
        let fd = listener.as_raw_fd();
        let gw2 = gw.clone();
        // Watch for SIGINT and exit promptly; the shards block in the ring.
        std::thread::spawn(watch_shutdown);
        uring::run(fd, gw2, cfg.shards);
        drop(listener);
        std::process::exit(0);
    }

    let _ = use_uring; // (non-Linux: always the blocking path)
    eprintln!(
        "dataplane: listening on {local} (keep-alive HTTP/1.1, blocking thread-per-connection, over the leanc-compiled proven serve; SIGINT to stop)"
    );
    blocking::run(listener, gw);
    std::process::exit(0);
}

/// Watch the shutdown flag and exit the process once set. Used by the io_uring
/// path, whose shards block inside the ring and are torn down with the process.
#[cfg(target_os = "linux")]
fn watch_shutdown() {
    use std::sync::atomic::Ordering;
    loop {
        if SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping");
            std::process::exit(0);
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}
