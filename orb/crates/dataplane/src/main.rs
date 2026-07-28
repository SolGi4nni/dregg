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
/// Durable COLD tier for the response cache: a content-addressable on-disk store
/// with a TTL reaper, realizing `Cache/Disk.lean` (injective+traversal-safe
/// key→path, round-trip, TTL, eviction). Gated behind `DRORB_DISK_CACHE=1`.
#[allow(dead_code)]
mod cache_disk;
mod cake_serve;
/// The gated CapTP wire-frame seam (`DRORB_CAPTP_LISTEN`): a minimal listener
/// that frames/deframes capability-transport messages through the PROVEN codec
/// (`Captp.Frame`/`Captp.Encode` via `drorb_captp_frame`). Serve path untouched.
mod captp;
/// Boot-time load of an arbitrary operator `DeploymentConfig` (DRORB_CONFIG) via
/// the proven `drorb_deployment_of_config` parser — the config→deployment path.
mod config;
/// The gated ts2021 control-plane HTTP front-door (`DRORB_CONTROL_LISTEN`):
/// `GET /key` serves the server Noise responder static pubkey; `POST /ts2021`
/// + `Upgrade: tailscale-control-protocol` switches (101) the connection into
/// the raw controlbase channel, spliced verbatim to the verified Noise responder
/// (`DRORB_CONTROL_RESPONDER`, a `control-live coord`). Thin host glue for the
/// HTTP/upgrade plumbing; the crypto + coordination stay the verified Lean.
mod control;
/// The SOCKS5 CONNECT egress-handshake driver, driven entirely by the PROVEN
/// decision (`Reactor.Socks.hstep` via `drorb_socks_step`): the host owns only
/// socket I/O and the client messages; every advance/tunnel/close verdict is the
/// proven gate. A gated self-test (`DRORB_SOCKS_SELFTEST`) drives it end-to-end.
mod socks;
// The DERP relay TLS front (DRORB_DERP_TLS_LISTEN): terminate a stock client's
// HTTPS DERP dial over the VERIFIED Lean terminator and splice the plaintext to
// the verified Lean relay. Byte-moving only; see crates/dataplane/src/derp_front.rs.
/// The provided-buffer ring (`io_uring` buf_ring) backing zero-copy receive on
/// the Linux IO path.
#[cfg(target_os = "linux")]
mod bufring;
mod derp_front;
mod gateway;
/// The real-gzip reactor seam: post-serve, replace the proven stored-block gzip
/// stage's (uncompressed) output with real `flate2` DEFLATE. Trusted (principled
/// TCB, like the crypto FFI), not verified. Opt-in via `DRORB_RUST_GZIP=1`.
mod gzip;
/// The interactive h2c host: the verified HTTP/2 connection engine threaded
/// across socket reads, one engine state per connection (the blocking host
/// forks here on the h2c prior-knowledge preface).
mod h2;
mod http;
mod interim;
/// The effect/continuation interpreter loop: a dumb executor that drives the
/// proven resumable serve (`drorb_serve_step`/`drorb_serve_resume`), executing
/// yielded effects (SEED: proxyDial). Opt-in via `DRORB_EFFECT_SEAM=1`.
mod interp;
/// The macOS / BSD IO path: per-core kqueue completion-queue reactors (the
/// sibling of `uring`; preferred over the blocking fallback on those platforms).
#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
))]
mod kqueue;
/// The layer-4 (raw TCP / UDP) passthrough listener: accept, choose the upstream
/// via the proven `drorb_proxy_pick`, dial it, and splice bytes verbatim. The
/// running host shell of the proven `Reactor.L4` forwarding model. Binds only
/// when `DRORB_L4_LISTEN` (TCP) / `DRORB_L4_UDP` (UDP) is set.
mod l4;
#[cfg(target_os = "linux")]
mod l4_uring;
/// A lightweight operational metrics surface (request/status/byte/backend
/// counters) and the gated admin listener (`DRORB_ADMIN_LISTEN`) exposing
/// `GET /metrics` + `GET /healthz`. Untrusted-shell observability, incremented
/// from the host serve loop — outside the proven core.
mod metrics;
/// Opt-in OpenTelemetry per-request span emission (`DRORB_OTEL`): one OTLP/JSON
/// span per served request to a sink + a bounded in-memory ring buffer. Untrusted-
/// shell observability from the host serve loop, outside the proven core (ob.5).
mod otel;
mod outbound;
mod pool;
/// The post-quantum C-ABI seam (drorb_pq_ml_dsa_verify / drorb_pq_ml_kem_*):
/// the dregg-pq-backed symbols ffi/crypto_shim.o resolves against — the REAL
/// dregg wire (the pure-Lean exes link ffi/pq_stub.o fail-closed stubs instead).
mod pq;
mod proxy_connect;
mod proxy_dial;
/// gRPC / gRPC-Web proxy host seam — PREPARED, NOT WIRED, and the `#[allow(dead_code)]`
/// below is load-bearing: nothing in this crate calls `is_grpc`, `is_grpc_web` or
/// `frame_len`. `Seam::GrpcFrameLen` is constructed only inside that module, so the
/// dispatch arm in `serve.rs` can never fire and the proven Lean export
/// `drorb_grpc_frame_len` is an idle carrier — orb's own reachability ratchet already
/// counts it as an orphan with `reason: "dead-dispatch"`. See the module header for
/// why it is kept rather than deleted, and for what wiring it would take.
#[allow(dead_code)]
mod proxy_grpc;
mod proxy_hook;
/// Runtime reconfiguration on SIGHUP: re-read + re-parse `DRORB_CONFIG` and
/// atomically swap the active config, draining in-flight requests per the proven
/// `Drain` discipline. The untrusted shell that executes the proven drain decision.
mod reconfig;
/// Automated certificate renewal scheduler (DRORB_ACME_RENEW): parse the leaf
/// notAfter, re-issue near end of life, hot-reload the pool. Untrusted shell.
mod renewal;
mod serve;
/// Per-source STANDING counters for the reactor accept path (connection-limit /
/// rate / slowloris) — the state the sans-IO serve fold structurally cannot carry.
mod standing;
/// Host-side static-file streaming (roadmap Stage 3): a `DRORB_STATIC_ROOT` file
/// under the serving prefix is streamed to the client with a bounded buffer — the
/// core decides the head, the shell streams the body, never materialized whole.
mod static_serve;
mod stream_serve;
/// The HTTPS front door: a TLS 1.3 listener that terminates real TLS in-process
/// over the verified server handshake + record layer, then serves each decrypted
/// request through the proven core. Binds only when `DRORB_TLS_LISTEN` is set;
/// the plaintext listener is unaffected.
mod tls;
mod udp;
#[cfg(target_os = "linux")]
mod uring;
/// The WireGuard transport tunnel seam ([`wg`]): seal/open the L4 UDP
/// datagram path through the proven transport data plane (Wire.sealPacket /
/// Wire.openPacket + the anti-replay Window). Gated on DRORB_L4_WG_KEY (relay)
/// and DRORB_WG_SELFTEST (my-hand round-trip check); the plaintext path is
/// untouched when unset.
mod wg;
/// The multi-worker supervisor (`--workers N`): spawn N independent copies of
/// this binary behind one SO_REUSEPORT port so the kernel load-balances across N
/// proven runtimes. A shell-only change — each worker runs the same proven serve.
mod workers;
mod ws;
mod ws_assembly;

/// Set once a shutdown signal (SIGINT or SIGTERM) is received; the IO paths
/// observe it and stop accepting.
pub static SHUTDOWN: AtomicBool = AtomicBool::new(false);

/// Set once a *graceful* shutdown signal (SIGTERM) is received, distinguishing it
/// from a prompt SIGINT. When set, the process exit path first begins a drain and
/// waits (bounded) for in-flight requests to finish before exiting, so
/// `docker stop` / `systemctl stop` is a graceful drain rather than a hard-kill.
pub static GRACEFUL_DRAIN: AtomicBool = AtomicBool::new(false);

/// Count of blocking-host WORKER THREADS currently in flight, for that host's
/// thread ceiling (`blocking::MAX_CONNS`) and the graceful-drain wait.
///
/// **This is not the connection gauge.** It is incremented only by
/// `blocking::run`'s accept loop, so on the shard reactors — the ones that ship —
/// it is permanently zero. It was nevertheless what `/admin/connections` and
/// `drorb_active_connections` reported, which made both a flat lie on the deployed
/// reactor: a serve holding hundreds of connections reported `0`. Those two now
/// read `standing::source_table().total_active()`, which every backend maintains.
///
/// It stays a separate counter deliberately: it counts THREADS (the resource the
/// blocking host's ceiling is about) and it is the drain wait's input, and the
/// reactor teardown does not run connections through the close funnel, so feeding
/// the reactor-wide connection count into `finish_and_exit` would turn every
/// SIGTERM into a full `DRORB_DRAIN_GRACE_MS` stall. The reactor drain being a
/// no-op is a known, documented gap; it is not made worse or better here.
pub static ACTIVE_CONNS: AtomicUsize = AtomicUsize::new(0);

extern "C" fn on_sigint(_sig: i32) {
    SHUTDOWN.store(true, std::sync::atomic::Ordering::SeqCst);
}

/// SIGTERM handler: async-signal-safe (two atomic stores only). Marks the
/// shutdown as graceful and raises the shared stop flag; the actual drain +
/// bounded wait + exit runs off-signal in [`finish_and_exit`].
extern "C" fn on_sigterm(_sig: i32) {
    GRACEFUL_DRAIN.store(true, std::sync::atomic::Ordering::SeqCst);
    SHUTDOWN.store(true, std::sync::atomic::Ordering::SeqCst);
}

unsafe extern "C" {
    fn signal(signum: i32, handler: usize) -> usize;
}

const SIGINT: i32 = 2;
const SIGTERM_SIG: i32 = 15;

/// The default file-descriptor cap applied at startup (overridable via
/// `DRORB_MAX_FDS`), bounding the process so a descriptor leak or flood cannot
/// exhaust the box.
///
/// The reactor's own connection ceiling is DERIVED from whatever soft limit this
/// ends up applying (`standing::derive_process_conn_cap`), so the reactor cap
/// necessarily binds before `EMFILE` does. It used not to: this comment claimed to
/// be "well above the connection ceilings so the reactor's own caps bind first"
/// while the shard reactors carried `MAX_CONNS_PER_SHARD` (16384) PER SHARD — 393,216
/// on a 24-core host, six times this budget — so accept failed with `EMFILE` long
/// before any connection ceiling was reached and the "cap" was unreachable.
const DEFAULT_MAX_FDS: u64 = 65_536;

/// Apply the startup resource caps so the dataplane cannot exhaust the host.
///
///   * `RLIMIT_NOFILE` is set to `min(hard, DRORB_MAX_FDS | DEFAULT_MAX_FDS)` —
///     this both RAISES a too-small soft limit and CAPS the process below a huge
///     system hard limit, giving a known descriptor bound. The hard limit is
///     left untouched. `DRORB_MAX_FDS=0` skips the fd cap entirely.
///   * `RLIMIT_AS` (address space) is set ONLY when `DRORB_MAX_AS_BYTES` is given
///     — an opt-in memory ceiling — since a blanket AS cap risks aborting a
///     legitimately large process (the Lean runtime's arenas).
///   * The PROCESS-WIDE CONNECTION CEILING (`standing::process_conn_cap`) is derived
///     from the descriptor soft limit this function ends up with and installed here,
///     so the two are consistent by construction rather than two constants that
///     drift. `DRORB_MAX_CONNS` overrides it outright.
///
/// Best-effort: a failing `setrlimit` is logged, never fatal. Uses `libc` for the
/// correct per-platform `struct rlimit` layout and resource constants.
fn apply_resource_limits() {
    /// The descriptor soft limit actually in force after the block below, whatever
    /// path it took (raised, capped, refused, or skipped entirely) — read back with
    /// `getrlimit` rather than assumed, so the connection ceiling is derived from
    /// the budget the process HAS and not the one it asked for.
    fn fd_soft_limit() -> u64 {
        // SAFETY: `getrlimit` is a libc call given a correctly-typed `libc::rlimit`
        // naming live stack storage.
        unsafe {
            let mut cur: libc::rlimit = std::mem::zeroed();
            if libc::getrlimit(libc::RLIMIT_NOFILE, &mut cur) == 0 {
                let soft = cur.rlim_cur as u64;
                // RLIM_INFINITY reads as an enormous number; treat it as "unknown"
                // so the ceiling falls back to its own constant rather than
                // multiplying out to nonsense.
                if soft == libc::RLIM_INFINITY as u64 {
                    0
                } else {
                    soft
                }
            } else {
                0
            }
        }
    }
    let want_fds = std::env::var("DRORB_MAX_FDS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(DEFAULT_MAX_FDS);
    if want_fds > 0 {
        // SAFETY: `getrlimit`/`setrlimit` are libc calls given a correctly-typed
        // `libc::rlimit`; the pointers name live stack storage.
        unsafe {
            let mut cur: libc::rlimit = std::mem::zeroed();
            if libc::getrlimit(libc::RLIMIT_NOFILE, &mut cur) == 0 {
                let target = want_fds.min(cur.rlim_max as u64);
                let new = libc::rlimit {
                    rlim_cur: target as libc::rlim_t,
                    rlim_max: cur.rlim_max,
                };
                if libc::setrlimit(libc::RLIMIT_NOFILE, &new) == 0 {
                    eprintln!(
                        "dataplane: RLIMIT_NOFILE soft cap set to {target} (hard {}); \
                         override via DRORB_MAX_FDS (0 disables)",
                        cur.rlim_max
                    );
                } else {
                    eprintln!(
                        "dataplane: setrlimit(RLIMIT_NOFILE, {target}) failed: {}",
                        std::io::Error::last_os_error()
                    );
                }
            }
        }
    }
    if let Some(bytes) = std::env::var("DRORB_MAX_AS_BYTES")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|&b| b > 0)
    {
        // SAFETY: as above; `libc::rlimit` is the correct layout.
        unsafe {
            let mut cur: libc::rlimit = std::mem::zeroed();
            if libc::getrlimit(libc::RLIMIT_AS, &mut cur) == 0 {
                let hard = cur.rlim_max as u64;
                let target = if hard == libc::RLIM_INFINITY as u64 {
                    bytes
                } else {
                    bytes.min(hard)
                };
                let new = libc::rlimit {
                    rlim_cur: target as libc::rlim_t,
                    rlim_max: cur.rlim_max,
                };
                if libc::setrlimit(libc::RLIMIT_AS, &new) == 0 {
                    eprintln!(
                        "dataplane: RLIMIT_AS (address space) soft cap set to {target} bytes (DRORB_MAX_AS_BYTES)"
                    );
                } else {
                    eprintln!(
                        "dataplane: setrlimit(RLIMIT_AS, {target}) failed: {}",
                        std::io::Error::last_os_error()
                    );
                }
            }
        }
    }
    // The PROCESS-WIDE connection ceiling, from the descriptor budget the process
    // actually ended up with. Announced, because a bound nobody can see is a bound
    // that gets rediscovered by measurement (which is how the 393,216 was found).
    let fds = fd_soft_limit();
    let conn_cap = standing::derive_process_conn_cap(fds);
    standing::set_process_conn_cap(conn_cap);
    if conn_cap == 0 {
        eprintln!(
            "dataplane: process-wide connection ceiling DISABLED (DRORB_MAX_CONNS=0); \
             the descriptor limit ({fds}) is the only bound"
        );
    } else {
        eprintln!(
            "dataplane: process-wide connection ceiling {conn_cap} (fd soft limit {fds}); \
             override via DRORB_MAX_CONNS (0 disables). This is a PROCESS bound, not \
             a per-shard one, and it holds at every --shards value"
        );
    }
}

/// The single graceful-shutdown / exit funnel. Every process-exit path routes
/// here so exactly one caller performs the teardown:
///
///   * on a GRACEFUL (SIGTERM) shutdown it begins a drain (`/healthz` → 503 so a
///     fronting balancer bleeds traffic away), then WAITS — up to
///     `DRORB_DRAIN_GRACE_MS` (default 30s) — for the in-flight connection count
///     (`ACTIVE_CONNS`, tracked on the blocking path) to reach zero, so in-flight
///     requests finish instead of being cut. On the reactor paths, whose shards
///     stop servicing on `SHUTDOWN`, `ACTIVE_CONNS` is already zero and the wait
///     returns immediately after the orderly reactor teardown;
///   * on a prompt (SIGINT) shutdown it exits at once, unchanged.
///
/// A one-shot guard means a second caller (e.g. the shutdown-watcher thread and
/// the main thread both observing `SHUTDOWN`) parks instead of racing the exit.
fn finish_and_exit() -> ! {
    use std::sync::atomic::Ordering;
    static EXITING: AtomicBool = AtomicBool::new(false);
    if EXITING.swap(true, Ordering::SeqCst) {
        // Another caller owns the exit; wait for it to terminate the process.
        loop {
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
    }
    if GRACEFUL_DRAIN.load(Ordering::SeqCst) {
        reconfig::begin_drain();
        let grace = std::env::var("DRORB_DRAIN_GRACE_MS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .unwrap_or(30_000);
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(grace);
        let mut inflight = ACTIVE_CONNS.load(Ordering::SeqCst);
        while inflight > 0 && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(50));
            inflight = ACTIVE_CONNS.load(Ordering::SeqCst);
        }
        if inflight > 0 {
            eprintln!(
                "dataplane: graceful drain grace ({grace} ms) elapsed with {inflight} \
                 in-flight request(s) still open — exiting"
            );
        } else {
            eprintln!(
                "dataplane: graceful drain complete — all in-flight requests finished; exiting 0"
            );
        }
    }
    std::process::exit(0)
}

/// Which IO path to run.
#[derive(Clone, Copy, PartialEq)]
enum IoMode {
    /// io_uring on Linux, blocking elsewhere.
    Auto,
    /// Force the blocking thread-per-connection path.
    Blocking,
    /// Force the io_uring path (Linux only).
    Uring,
    /// Force the kqueue reactor path (macOS/BSD only).
    Kqueue,
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
    /// Number of independent worker processes to run behind the one
    /// `SO_REUSEPORT` port. `1` (default) is the ordinary single-process path,
    /// unchanged. `N > 1` makes the parent a supervisor that spawns N copies of
    /// this binary, each with its own proven Lean runtime + serve thread; the
    /// kernel load-balances connections across them (~Nx past the single
    /// serve-thread ceiling on Linux/BSD). See `workers`.
    workers: usize,
}

fn usage() {
    eprintln!(
        "\
drorb dataplane — a keep-alive, concurrent HTTP/1.1 host driving the
leanc-compiled proven serve.

USAGE:
    dataplane [ADDR]
    dataplane --bind ADDR [--io auto|blocking|uring|kqueue] [--shards N]
              [--udp ADDR | --no-udp] [--workers N]
    dataplane --help

ADDR is HOST:PORT (e.g. 127.0.0.1:8080 or 0.0.0.0:443) or a bare PORT
(e.g. 8080), which binds 127.0.0.1. If omitted, the DRORB_BIND environment
variable is used, else 127.0.0.1:8080.

This one process serves, over real sockets, every protocol through the
leanc-compiled proven serve:
  - TCP: HTTP/1.1 and h2c (HTTP/2 cleartext prior-knowledge, forked to the real
    H2 engine) via `drorb_serve`, and WebSocket (RFC 6455 Upgrade kept open,
    frames through the host's bounded streaming codec — `ws`/`ws_assembly`);
  - UDP: QUIC Initial packets, decrypted by verified EverCrypt packet protection
    and dispatched through the proven HTTP/3 path (`drorb_serve_datagram`).

--io selects the TCP IO path: 'auto' (io_uring on Linux, the kqueue reactor on
macOS/BSD), 'blocking' (thread-per-connection), 'uring' (Linux io_uring), or
'kqueue' (macOS/BSD kqueue reactor). Overridable via DRORB_IO. --shards sets the
reactor shard count (io_uring or kqueue; default: CPU count), overridable via
DRORB_SHARDS. --udp sets the QUIC/UDP bind (default: same
HOST:PORT as ADDR; DRORB_UDP overrides); --no-udp disables it.

--workers N (env DRORB_WORKERS; default 1) runs N independent worker processes
behind the one SO_REUSEPORT port, each with its own proven Lean runtime and serve
thread. The kernel load-balances connections across them, so throughput scales
past the single serve-thread ceiling — up to ~Nx on Linux/BSD, where SO_REUSEPORT
hash-distributes across processes. (On Darwin the duplicate bind is permitted but
not cross-distributed; use a front load balancer there.) N=1 is the ordinary
single-process path, unchanged.

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
        "kqueue" => IoMode::Kqueue,
        other => {
            eprintln!("dataplane: unknown --io mode {other} (want auto|blocking|uring|kqueue)");
            std::process::exit(2);
        }
    }
}

/// **The reactor-scoped `DRORB_*` flags**: every environment flag this binary reads
/// that is NOT read by all three IO paths, paired with the reactors that DO honor it.
/// The full var -> reactor table (including the flags honored everywhere) is
/// `docs/gateway/ENV-BY-REACTOR.md`; this list is only the asymmetric rows, because
/// those are the ones an operator can set and silently not get.
///
/// Derived by auditing the READ SITES: a flag read in `config.rs` / `serve.rs` /
/// `tls.rs` / `renewal.rs` / `main.rs` (or reached through `proxy_hook`'s handoff to
/// `blocking::handle_conn_prefilled`, which all three reactors perform) is honored
/// everywhere and is absent here. A flag read only in `blocking.rs` / `uring.rs` /
/// `kqueue.rs` — or in a module only one of them calls — is asymmetric and listed.
///
/// This exists because `DRORB_GATEWAY` was read ONLY by `blocking.rs` while the
/// production reactor is io_uring: the operator got a different serve with no
/// diagnostic. `DRORB_GATEWAY` is now honored by all three (so it is not in this
/// table); the guard below makes the remaining asymmetries LOUD at startup instead
/// of leaving the next one to be found by an audit.
///
/// **Ratcheted.** `scripts/env-flag-audit.sh --check` (a `scripts/ci.sh` step)
/// re-derives the asymmetry from the READ SITES and fails when a flag is reachable
/// from some reactors and not others without a row here — so the table cannot rot
/// back into the `DRORB_GATEWAY` state. The markers below are what that script
/// excises: the flags NAMED here are table data, not read sites.
// RATCHET-TABLE-BEGIN REACTOR_SCOPED_FLAGS
const REACTOR_SCOPED_FLAGS: &[(&str, &[&str])] = &[
    // The streaming response-emit path pumps the socket with BLOCKING writes, which a
    // shard may never do; there is no completion-reactor implementation of it.
    ("DRORB_STREAM_SERVE", &["blocking"]),
    ("DRORB_STREAM_CHUNK", &["blocking"]),
    // `proxy_connect` (HTTP CONNECT) is called by the blocking host and the io_uring
    // shard; the kqueue reactor has no CONNECT arm.
    ("DRORB_CONNECT_ALLOW", &["blocking", "io_uring"]),
    // The static-file lane (`static_serve`) is wired into the blocking host and the
    // io_uring shard only.
    ("DRORB_STATIC_ROOT", &["blocking", "io_uring"]),
    ("DRORB_STATIC_PREFIX", &["blocking", "io_uring"]),
    ("DRORB_STATIC_SPA", &["blocking", "io_uring"]),
    ("DRORB_STATIC_SPA_INDEX", &["blocking", "io_uring"]),
    ("DRORB_STATIC_NO_ZEROCOPY", &["blocking", "io_uring"]),
    // The effect-seam interpreter (`interp`) — and the disk cache it drives — is
    // called by the blocking host and the io_uring shard only.
    ("DRORB_EFFECT_SEAM", &["blocking", "io_uring"]),
    ("DRORB_DISK_CACHE", &["blocking", "io_uring"]),
    ("DRORB_DISK_CACHE_DIR", &["blocking", "io_uring"]),
    // io_uring MECHANISM knobs: they name ring features (buf_ring/SendZc, native
    // dial, splice), so they are meaningless to the other paths by construction.
    ("DRORB_ZC", &["io_uring"]),
    ("DRORB_PROXY_BLOCKING", &["io_uring"]),
    ("DRORB_PROXY_NOSTREAM", &["io_uring"]),
    ("DRORB_PROXY_TIMEOUT_MS", &["io_uring"]),
    // kqueue MECHANISM knob.
    ("DRORB_KQ_TRACE", &["kqueue"]),
    // Per-core SHARD COUNT. Read here (`default_shards`) and handed to
    // `uring::run` / `kqueue::run`; the blocking host is thread-per-connection and
    // has no shard concept, so an operator who sets it on `--io blocking` gets
    // nothing. Found by `scripts/env-flag-audit.sh` (A4-NO-HOME): it was already
    // tabled in docs/gateway/ENV-BY-REACTOR.md as "io_uring, kqueue" but had no row
    // here, so it was silently ignored on the blocking path with no diagnostic —
    // the same shape as `DRORB_GATEWAY`, one table narrower.
    ("DRORB_SHARDS", &["io_uring", "kqueue"]),
];
// RATCHET-TABLE-END REACTOR_SCOPED_FLAGS

/// Startup guard for the failure shape this binary already shipped once: a flag the
/// operator set, that the ACTIVE reactor does not read, ignored in silence. Called
/// once from each reactor arm with that arm's name. It never refuses to start — a
/// deployment that exports one env block to several differently-flagged processes is
/// legitimate — but the ignored flag is named on stderr, so "I set it and nothing
/// happened" is answered at boot instead of by an audit.
fn warn_unhonored_flags(active: &str) {
    for (var, honored) in REACTOR_SCOPED_FLAGS {
        if std::env::var_os(var).is_some() && !honored.contains(&active) {
            eprintln!(
                "dataplane: WARNING: {var} is set but the ACTIVE {active} reactor does not read it - it is being IGNORED (honored by: {}). See docs/gateway/ENV-BY-REACTOR.md",
                honored.join(", ")
            );
        }
    }
}

/// **Every `DRORB_SPAN` value `serve::span_number()` accepts.** Mirrors the
/// `Some("N") => Some(N)` arms in `crates/dataplane/src/serve.rs`; a value outside
/// this set parses to `None` and the deployed default serve stays in force.
// RATCHET-TABLE-BEGIN DRORB_SPAN
const SELECTABLE_SPANS: &[u8] = &[
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
];

/// **The spans that answer `GET /.well-known/acme-challenge/<token>`** with the
/// RFC 8555 §8.1 key authorization. Not asserted here — *derived from the driven
/// audit*: `docs/gateway/ACME-SPAN-AUDIT.md` started one `dataplane` process per
/// span and fetched the challenge path with `curl`, and only these four (plus the
/// UNSET default, which needs no entry) returned `200 text/plain` with the key
/// authorization. They are the `conformantServe*` wrappers, which carry the
/// challenge arm; the other 21 are bare inner serves (`403`) or echo exemplars
/// that route nothing.
const ACME_SERVING_SPANS: &[u8] = &[19, 20, 22, 23];
// RATCHET-TABLE-END DRORB_SPAN

/// True when this process will try to obtain or renew certificates over ACME.
/// Either scheduler answers HTTP-01 out of the SERVE path, so either one makes a
/// non-ACME span a live outage rather than a benchmark choice:
/// `DRORB_ACME_RENEW` drives the configured-leaf renewal thread and
/// `DRORB_TLS_ONDEMAND` the on-demand issue/sweep (`renewal.rs`, `tls/ondemand.rs`).
fn acme_enabled() -> Option<&'static str> {
    for var in ["DRORB_ACME_RENEW", "DRORB_TLS_ONDEMAND"] {
        if std::env::var_os(var)
            .map(|v| !v.is_empty())
            .unwrap_or(false)
        {
            return Some(var);
        }
    }
    None
}

/// Startup guard for the quietest way to lose a production deployment: pick a
/// `DRORB_SPAN` that does not carry the ACME HTTP-01 challenge route. The span
/// family diverts EVERY HTTP serve job to an alternative proven entry point, and
/// 21 of the 25 selectable ones answer the challenge path with `403` (the bare
/// inner serves) or with an echo (the measurement exemplars). Nothing fails at
/// boot, nothing fails on the first request — the certificate simply stops being
/// renewable, and the deployment goes down ~90 days later when it expires.
///
/// Two outcomes, deliberately different:
///
/// * **ACME is enabled** (`DRORB_ACME_RENEW` / `DRORB_TLS_ONDEMAND`) and the span
///   cannot serve the challenge — REFUSE TO START. That combination has no
///   legitimate reading: the process is configured to renew certificates over a
///   route it will answer `403` on. Booting it produces a server that works
///   perfectly until it doesn't, with nothing in the log at the moment the damage
///   is done. There is no override flag on purpose — an override is how this
///   becomes quiet again.
/// * **ACME is off** — WARN. Running a measurement span with no TLS configured is
///   the whole point of the span family, so refusing would break the benchmark
///   lane; but the operator should still be told what this span cannot do, in case
///   ACME is turned on later.
///
/// Called once, before the worker supervisor forks and before any listener binds,
/// so the refusal happens on the parent and nothing ever accepts a connection.
fn check_span_acme() {
    let raw = match std::env::var("DRORB_SPAN") {
        Ok(v) if !v.is_empty() => v,
        _ => return, // unset: the deployed default serves HTTP-01.
    };
    let parsed = raw
        .trim()
        .parse::<u8>()
        .ok()
        .filter(|n| SELECTABLE_SPANS.contains(n));
    let span = match parsed {
        Some(n) => n,
        None => {
            eprintln!(
                "dataplane: WARNING: DRORB_SPAN={raw} is not a selectable span - it is being IGNORED and the deployed default serve is in force. Selectable spans are 1-{}. See docs/gateway/ACME-SPAN-AUDIT.md",
                SELECTABLE_SPANS.last().copied().unwrap_or(0)
            );
            return;
        }
    };
    if ACME_SERVING_SPANS.contains(&span) {
        return;
    }
    let serving: Vec<String> = ACME_SERVING_SPANS.iter().map(|n| n.to_string()).collect();
    let serving = serving.join(", ");
    match acme_enabled() {
        Some(acme_var) => {
            eprintln!(
                "dataplane: FATAL: DRORB_SPAN={span} selects a serve that does NOT answer GET /.well-known/acme-challenge/<token>, but ACME is ENABLED ({acme_var} is set). Every HTTP-01 challenge on this span is refused, so CERTIFICATE RENEWAL WILL FAIL - silently, until the certificate expires and the deployment goes down. Refusing to start. Fix: leave DRORB_SPAN unset (the deployed default), or select a span that serves HTTP-01 ({serving}); if you are measuring, unset {acme_var}. See docs/gateway/ACME-SPAN-AUDIT.md"
            );
            std::process::exit(2);
        }
        None => {
            eprintln!(
                "dataplane: WARNING: DRORB_SPAN={span} selects a serve that does NOT answer GET /.well-known/acme-challenge/<token> - CERTIFICATE RENEWAL VIA ACME HTTP-01 WOULD FAIL on this span, and would fail silently until the certificate expired. It is only a warning because no ACME scheduler is enabled in this process (DRORB_ACME_RENEW / DRORB_TLS_ONDEMAND are unset); setting one with this span refuses to start. Spans that serve HTTP-01: {serving}, or leave DRORB_SPAN unset. See docs/gateway/ACME-SPAN-AUDIT.md"
            );
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
    let mut workers: Option<usize> = None;
    while let Some(a) = args.next() {
        match a.as_str() {
            "-h" | "--help" => {
                usage();
                std::process::exit(0);
            }
            // The verified outbound (client) path: dial ADDR, put a
            // verified-serialized `GET / HTTP/1.1` request on the wire, and parse
            // the response as a verified client (crossing `drorb_response_parse`).
            // A curl-equivalent through the proven client core.
            "--verified-outbound" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --verified-outbound needs an ADDR argument");
                    std::process::exit(2);
                });
                let addr: std::net::SocketAddr = v.parse().unwrap_or_else(|_| {
                    eprintln!("dataplane: --verified-outbound wants a host:port ADDR");
                    std::process::exit(2);
                });
                outbound::boot_client_runtime();
                let req = outbound::verified_serialize_request(b"GET", b"/", b"HTTP/1.1");
                // append the Host / Connection headers so the upstream frames and closes
                let mut full = req;
                full.truncate(full.len().saturating_sub(2)); // drop the trailing blank CRLF
                full.extend_from_slice(b"Host: localhost\r\nConnection: close\r\n\r\n");
                match outbound::dial_and_parse(addr, &full, std::time::Duration::from_secs(3)) {
                    Ok(Some(r)) => {
                        println!(
                            "verified-outbound: parsed upstream response status={} bodyLen={}",
                            r.status,
                            r.body.len()
                        );
                        std::process::exit(0);
                    }
                    Ok(None) => {
                        println!("verified-outbound: verified parser rejected the response");
                        std::process::exit(1);
                    }
                    Err(e) => {
                        eprintln!("verified-outbound: dial/io error: {e}");
                        std::process::exit(1);
                    }
                }
            }
            // The verified H2 outbound path: dial ADDR, open an h2c connection with
            // the proven `Client.H2` submit octets (preface + SETTINGS + HEADERS),
            // read the response frame flight, and reassemble it with the verified
            // `Client.H2Receive` path. The H2 analogue of `--verified-outbound`.
            "--verified-outbound-h2" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --verified-outbound-h2 needs ADDR [AUTHORITY [PATH]]");
                    std::process::exit(2);
                });
                let addr: std::net::SocketAddr = v.parse().unwrap_or_else(|_| {
                    eprintln!("dataplane: --verified-outbound-h2 wants a host:port ADDR");
                    std::process::exit(2);
                });
                let authority = args.next().unwrap_or_else(|| "localhost".to_string());
                let path = args.next().unwrap_or_else(|| "/".to_string());
                outbound::boot_client_runtime();
                outbound::boot_h2_client();
                match outbound::h2_dial_and_parse(
                    addr,
                    authority.as_bytes(),
                    path.as_bytes(),
                    std::time::Duration::from_secs(3),
                ) {
                    Ok(Some(r)) => {
                        println!(
                            "verified-outbound-h2: reassembled upstream response status={} bodyLen={}",
                            r.status,
                            r.body.len()
                        );
                        std::process::exit(0);
                    }
                    Ok(None) => {
                        println!("verified-outbound-h2: verified receive rejected the response");
                        std::process::exit(1);
                    }
                    Err(e) => {
                        eprintln!("verified-outbound-h2: dial/io error: {e}");
                        std::process::exit(1);
                    }
                }
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
            "--workers" | "-w" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --workers needs a count argument");
                    std::process::exit(2);
                });
                workers = Some(v.parse().unwrap_or_else(|_| {
                    eprintln!("dataplane: --workers wants a positive integer");
                    std::process::exit(2);
                }));
            }
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
    let workers = workers
        .or_else(|| {
            std::env::var("DRORB_WORKERS")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
        })
        .unwrap_or(1)
        .max(1);
    Config {
        bind,
        io,
        shards,
        udp,
        workers,
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
    // On the libc platforms, bind the listener OURSELVES with SO_REUSEADDR +
    // SO_REUSEPORT so several worker processes (see `--workers`) can share the
    // one port and the kernel load-balances accepts across them: Linux and the
    // BSDs hash-distribute connections across every SO_REUSEPORT socket bound to
    // the address, INCLUDING across processes, giving ~Nx throughput past the
    // single serve-thread ceiling at zero proof cost. (Darwin only *permits* the
    // duplicate bind — it does not cross-distribute; there --workers still runs N
    // identical serves but a front load balancer is needed to spread load.) A
    // plain std bind sets neither option, so a second process would fail with
    // EADDRINUSE; this is the one enabling change.
    #[cfg(any(
        target_os = "linux",
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd",
        target_os = "dragonfly"
    ))]
    for addr in &addrs {
        match bind_reuseport_listener(*addr) {
            Ok(l) => return l,
            Err(e) => {
                eprintln!("dataplane: SO_REUSEPORT bind {addr} failed: {e}");
            }
        }
    }
    TcpListener::bind(&addrs[..]).unwrap_or_else(|e| {
        eprintln!("dataplane: bind {bind} failed: {e}");
        std::process::exit(1);
    })
}

/// Bind a fresh listening socket on `addr` with `SO_REUSEADDR` + `SO_REUSEPORT`
/// set before the bind, returned as an owned blocking [`TcpListener`]. This is
/// the shared-port primitive the multi-worker supervisor relies on.
#[cfg(any(
    target_os = "linux",
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
))]
fn bind_reuseport_listener(addr: std::net::SocketAddr) -> std::io::Result<TcpListener> {
    use std::os::fd::FromRawFd;
    let domain = if addr.is_ipv4() {
        libc::AF_INET
    } else {
        libc::AF_INET6
    };
    // SAFETY: each libc call is checked; the sockaddr storage is a correctly
    // sized, zero-initialized struct for the address family, and the fd is closed
    // on any subsequent failure (or adopted by the returned TcpListener).
    unsafe {
        let fd = libc::socket(domain, libc::SOCK_STREAM, 0);
        if fd < 0 {
            return Err(std::io::Error::last_os_error());
        }
        let on: libc::c_int = 1;
        let set = |opt: libc::c_int| {
            libc::setsockopt(
                fd,
                libc::SOL_SOCKET,
                opt,
                &on as *const libc::c_int as *const libc::c_void,
                std::mem::size_of::<libc::c_int>() as libc::socklen_t,
            );
        };
        set(libc::SO_REUSEADDR);
        set(libc::SO_REUSEPORT);
        let rc = match addr {
            std::net::SocketAddr::V4(a) => {
                let mut s: libc::sockaddr_in = std::mem::zeroed();
                #[cfg(any(target_os = "macos", target_os = "ios", target_vendor = "apple"))]
                {
                    s.sin_len = std::mem::size_of::<libc::sockaddr_in>() as u8;
                }
                s.sin_family = libc::AF_INET as libc::sa_family_t;
                s.sin_port = a.port().to_be();
                s.sin_addr = libc::in_addr {
                    s_addr: u32::from_ne_bytes(a.ip().octets()),
                };
                libc::bind(
                    fd,
                    &s as *const libc::sockaddr_in as *const libc::sockaddr,
                    std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
                )
            }
            std::net::SocketAddr::V6(a) => {
                let mut s: libc::sockaddr_in6 = std::mem::zeroed();
                #[cfg(any(target_os = "macos", target_os = "ios", target_vendor = "apple"))]
                {
                    s.sin6_len = std::mem::size_of::<libc::sockaddr_in6>() as u8;
                }
                s.sin6_family = libc::AF_INET6 as libc::sa_family_t;
                s.sin6_port = a.port().to_be();
                s.sin6_addr = libc::in6_addr {
                    s6_addr: a.ip().octets(),
                };
                libc::bind(
                    fd,
                    &s as *const libc::sockaddr_in6 as *const libc::sockaddr,
                    std::mem::size_of::<libc::sockaddr_in6>() as libc::socklen_t,
                )
            }
        };
        if rc < 0 {
            let e = std::io::Error::last_os_error();
            libc::close(fd);
            return Err(e);
        }
        if libc::listen(fd, 1024) < 0 {
            let e = std::io::Error::last_os_error();
            libc::close(fd);
            return Err(e);
        }
        Ok(TcpListener::from_raw_fd(fd))
    }
}

fn main() {
    let cfg = parse_config();

    // The quietest misconfiguration this binary has: a DRORB_SPAN that cannot
    // answer the ACME HTTP-01 challenge. Checked HERE — before the worker
    // supervisor forks and before any listener binds — so the refusal happens
    // once, on the parent, and no process ever accepts a connection it could not
    // renew a certificate for. A spawned worker inherits the vetted env, so it
    // skips the check rather than repeating the message N times.
    if std::env::var_os("DRORB_WORKER").is_none() {
        check_span_acme();
    }

    // Multi-worker supervisor: when `--workers N` (N > 1) is requested and this
    // is not itself a spawned worker, become the supervisor — spawn N copies of
    // this binary (each a full single-owner runtime) sharing the SO_REUSEPORT
    // port, and never boot a Lean runtime in the parent. Each worker re-enters
    // main() with DRORB_WORKER set and runs the ordinary single-process path
    // below, unchanged. This is a pure shell change: every worker runs the same
    // proven serve, so there is no proof impact.
    if cfg.workers > 1 && std::env::var_os("DRORB_WORKER").is_none() {
        workers::supervise(cfg.workers);
        // supervise() runs until shutdown, then exits the process.
        return;
    }

    // Make the Lean-VERIFIED post-quantum cores the accept/reject authority for
    // this process BEFORE any listener exists, so no request can ever be served
    // by the unverified fips204 / ml-kem crate fallbacks. Asserts on a stale
    // archive rather than falling back silently (see pq::install_verified_cores).
    pq::install_verified_cores();

    // Cap the process's descriptors (and, opt-in, address space) at startup so a
    // leak or flood cannot exhaust the box before the reactor's own caps bind.
    apply_resource_limits();

    // Install the shutdown handlers before we bring anything up. SIGINT is the
    // prompt stop (unchanged); SIGTERM is a GRACEFUL drain so `docker stop` /
    // `systemctl stop` finishes in-flight requests instead of hard-killing.
    // SAFETY: both handlers are `extern "C"` and only store into atomics —
    // async-signal-safe; installing them before any work is standard.
    unsafe {
        signal(SIGINT, on_sigint as *const () as usize);
        signal(SIGTERM_SIG, on_sigterm as *const () as usize);
    }

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

    // The durable disk-cache reaper (gated by DRORB_DISK_CACHE): a background
    // thread that sweeps expired cold-tier entries every 60s. Held for the life
    // of the process; a no-op (None) when the disk tier is disabled.
    let _disk_reaper = cache_disk::spawn_reaper(60);

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

    // The gated CapTP wire-frame seam (DRORB_CAPTP_LISTEN, a bare PORT binds
    // localhost), SEPARATE from the serve listeners: a minimal listener that
    // frames/deframes capability-transport messages entirely through the proven
    // codec (Captp.Frame/Encode, crossed via drorb_captp_frame). Bound only when
    // the env var is set; the serve path is unaffected. It deploys the wire CODEC
    // (bounded, crash-safe framing), NOT the full object-capability protocol.
    if let Ok(captp_listen) = std::env::var("DRORB_CAPTP_LISTEN") {
        let captp_addr = normalize_addr(&captp_listen);
        let captp_listener = bind_listener(&captp_addr);
        std::thread::Builder::new()
            .name("drorb-captp".into())
            .spawn(move || captp::run_captp(captp_listener))
            .expect("failed to spawn the CapTP listener thread");
    }

    // The gated ts2021 control-plane front-door (DRORB_CONTROL_LISTEN, a bare
    // PORT binds localhost), SEPARATE from the serve listeners: GET /key ->
    // the server Noise responder static pubkey; POST /ts2021 + Upgrade ->
    // 101 Switching Protocols -> the raw controlbase stream, spliced to the
    // verified Noise responder (DRORB_CONTROL_RESPONDER). Bound only when the
    // env var is set; the serve path is unaffected. Additive host glue — the
    // Noise crypto + register/map coordination stay the verified Lean.
    if let Ok(control_listen) = std::env::var("DRORB_CONTROL_LISTEN") {
        let control_addr = normalize_addr(&control_listen);
        let control_listener = bind_listener(&control_addr);
        std::thread::Builder::new()
            .name("drorb-control".into())
            .spawn(move || control::run_control(control_listener))
            .expect("failed to spawn the control listener thread");
    }

    // The DERP relay TLS front (DRORB_DERP_TLS_LISTEN, a bare PORT binds localhost).
    // A STOCK tailscale client dials its home DERP region over HTTPS, so the verified
    // Lean relay -- which speaks plaintext -- needs the verified TLS terminator in
    // front of it. This listener makes the SAME crossing the ts2021 control front
    // makes (control::terminate_tls -> drorb_tls_terminate) and splices the decrypted
    // stream to the relay's loopback listener (DRORB_DERP_PLAIN). Bound only when the
    // env var is set. Additive host glue: the framing, the upgrade and the forwarding
    // stay the verified Lean.
    if let Ok(derp_listen) = std::env::var("DRORB_DERP_TLS_LISTEN") {
        let derp_addr = normalize_addr(&derp_listen);
        let derp_listener = bind_listener(&derp_addr);
        std::thread::Builder::new()
            .name("drorb-derp-front".into())
            .spawn(move || derp_front::run_derp_front(derp_listener))
            .expect("failed to spawn the DERP TLS front listener thread");
    }

    // Gated SOCKS5 CONNECT self-test (DRORB_SOCKS_SELFTEST): drive the proven
    // handshake decision over a real loopback socket pair against an in-process
    // fake SOCKS5 responder, print the verdict, and exit. Off by default; the
    // serve path is untouched. This is the my-hand wiring of the proven decision
    // to a real socket.
    // Gated WireGuard transport-tunnel self-test (DRORB_WG_SELFTEST): seal a
    // datagram, move it over a real loopback UDP socket pair, open it under the
    // proven anti-replay window, and confirm the round-trip + replay refusal.
    // Off by default; the serve path is untouched. This is the my-hand wiring of
    // the proven transport seal/open to a real socket.
    if std::env::var("DRORB_WG_SELFTEST").is_ok() {
        let ok = wg::selftest();
        eprintln!(
            "dataplane: WireGuard transport-tunnel self-test (proven drorb_wg_seal/drorb_wg_open) -> {}",
            if ok {
                "PASS (sealed round-trip opened, replay refused by the proven window)"
            } else {
                "FAIL"
            }
        );
        std::process::exit(if ok { 0 } else { 1 });
    }

    if std::env::var("DRORB_SOCKS_SELFTEST").is_ok() {
        let ok = socks::selftest();
        eprintln!(
            "dataplane: SOCKS5 CONNECT self-test (proven drorb_socks_step) -> {}",
            if ok {
                "PASS (tunnelUp reached via the proven gate)"
            } else {
                "FAIL"
            }
        );
        std::process::exit(if ok { 0 } else { 1 });
    }

    // Gated ts2021 control record-codec self-test (DRORB_CONTROL_SELFTEST): a
    // my-hand roundtrip of the host-side controlbase record framer
    // ([type:4][len:u16 BE]) over boundary sizes, then exit. Serve path untouched.
    if std::env::var("DRORB_CONTROL_SELFTEST").is_ok() {
        std::process::exit(control::selftest());
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
                eprintln!(
                    "dataplane: DRORB_TLS_LISTEN set but no usable cert — TLS listener not bound"
                );
            }
        }
    }

    // Automated certificate renewal (DRORB_ACME_RENEW): a background scheduler
    // that reads the served leaf's notAfter, re-issues near end of life via the
    // ACME driver, and hot-reloads the pool - no restart, no dropped connection.
    // A no-op when the env var is unset.
    renewal::install();

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

    // Choose the IO path. The per-core reactor is preferred on each platform
    // (io_uring on Linux, the kqueue reactor on macOS/BSD); the blocking
    // thread-per-connection path is the portable fallback and an explicit escape
    // hatch everywhere.

    // Linux: io_uring is the auto/default reactor.
    #[cfg(target_os = "linux")]
    {
        let use_uring = match cfg.io {
            IoMode::Auto | IoMode::Uring => true,
            IoMode::Blocking => false,
            IoMode::Kqueue => {
                eprintln!("dataplane: --io kqueue requires macOS/BSD; falling back to io_uring");
                true
            }
        };
        if use_uring {
            use std::os::fd::AsRawFd;
            // Zero-copy datapath (buf_ring borrow-recv + SendZc), opt-in via
            // DRORB_ZC=1. Removes the two shell-owned full-payload copies (#1 on
            // receive, #5 on send), realizing the proven `Datapath`/`Uring`
            // lease+in-place-write in the running bytes; the serve output stays
            // byte-identical. Falls back per-shard to plain recv/send when the
            // kernel lacks buf_ring.
            let zc = std::env::var("DRORB_ZC").map(|v| v == "1").unwrap_or(false);
            warn_unhonored_flags("io_uring");
            eprintln!(
                "dataplane: listening on {local} (io_uring, {} shards{}, over the leanc-compiled proven serve; SIGINT to stop)",
                cfg.shards,
                if zc {
                    ", zero-copy (buf_ring recv + SendZc)"
                } else {
                    ""
                }
            );
            let fd = listener.as_raw_fd();
            let gw2 = gw.clone();
            // Watch for SIGINT and exit promptly; the shards block in the ring.
            std::thread::spawn(watch_shutdown);
            uring::run(fd, gw2, cfg.shards, zc);
            drop(listener);
            finish_and_exit();
        }
    }

    // macOS / BSD: the kqueue completion-queue reactor is the auto/default path.
    #[cfg(any(
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd",
        target_os = "dragonfly"
    ))]
    {
        let use_kqueue = match cfg.io {
            IoMode::Auto | IoMode::Kqueue => true,
            IoMode::Blocking => false,
            IoMode::Uring => {
                eprintln!(
                    "dataplane: --io uring requires Linux; falling back to the kqueue reactor"
                );
                true
            }
        };
        if use_kqueue {
            warn_unhonored_flags("kqueue");
            eprintln!(
                "dataplane: listening on {local} (kqueue reactor, {} shards, SO_REUSEPORT, over the leanc-compiled proven serve; SIGINT to stop)",
                cfg.shards
            );
            // The kqueue shards each bind their OWN SO_REUSEPORT listener on this
            // address; release the plain-bound probe listener so the shards can
            // rebind the port (SO_REUSEPORT requires every binder to set it).
            let addr = local.clone();
            drop(listener);
            kqueue::run(&addr, gw, cfg.shards);
            finish_and_exit();
        }
    }

    warn_unhonored_flags("blocking");
    eprintln!(
        "dataplane: listening on {local} (keep-alive HTTP/1.1, blocking thread-per-connection, over the leanc-compiled proven serve; SIGINT to stop)"
    );
    blocking::run(listener, gw);
    finish_and_exit();
}

/// Watch the shutdown flag and exit the process once set. Used by the io_uring
/// path, whose shards block inside the ring and are torn down with the process.
/// Routes through [`finish_and_exit`] so a SIGTERM shutdown drains gracefully.
#[cfg(target_os = "linux")]
fn watch_shutdown() {
    use std::sync::atomic::Ordering;
    loop {
        if SHUTDOWN.load(Ordering::SeqCst) {
            if GRACEFUL_DRAIN.load(Ordering::SeqCst) {
                eprintln!("dataplane: SIGTERM — draining");
            } else {
                eprintln!("dataplane: SIGINT — stopping");
            }
            if let Some(s) = uring::stats() {
                eprintln!("dataplane: {s}");
            }
            finish_and_exit();
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}
