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
/// The gated CapTP wire-frame seam (`DRORB_CAPTP_LISTEN`): a minimal listener
/// that frames/deframes capability-transport messages through the PROVEN codec
/// (`Captp.Frame`/`Captp.Encode` via `drorb_captp_frame`). Serve path untouched.
mod captp;
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
/// Boot-time load of an arbitrary operator `DeploymentConfig` (DRORB_CONFIG) via
/// the proven `drorb_deployment_of_config` parser — the config→deployment path.
mod config;
/// The real-gzip reactor seam: post-serve, replace the proven stored-block gzip
/// stage's (uncompressed) output with real `flate2` DEFLATE. Trusted (principled
/// TCB, like the crypto FFI), not verified. Opt-in via `DRORB_RUST_GZIP=1`.
mod gzip;
/// The interactive h2c host: the verified HTTP/2 connection engine threaded
/// across socket reads, one engine state per connection (the blocking host
/// forks here on the h2c prior-knowledge preface).
mod h2;
mod http;
/// The effect/continuation interpreter loop: a dumb executor that drives the
/// proven resumable serve (`drorb_serve_step`/`drorb_serve_resume`), executing
/// yielded effects (SEED: proxyDial). Opt-in via `DRORB_EFFECT_SEAM=1`.
mod interp;
mod interim;
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
mod outbound;
mod pool;
mod proxy_connect;
mod proxy_dial;
/// gRPC / gRPC-Web proxy host seam: content-type detection and the proven
/// `drorb_grpc_frame_len` crossing. The DATA passthrough reuses the streaming
/// forward; the framing decisions are the proven `Reactor.Proxy.Grpc`.
#[allow(dead_code)]
mod proxy_grpc;
mod proxy_hook;
/// The post-quantum C-ABI seam (drorb_pq_ml_dsa_verify / drorb_pq_ml_kem_*):
/// the dregg-pq-backed symbols ffi/crypto_shim.o resolves against — the REAL
/// dregg wire (the pure-Lean exes link ffi/pq_stub.o fail-closed stubs instead).
mod pq;
/// Runtime reconfiguration on SIGHUP: re-read + re-parse `DRORB_CONFIG` and
/// atomically swap the active config, draining in-flight requests per the proven
/// `Drain` discipline. The untrusted shell that executes the proven drain decision.
mod reconfig;
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
/// The provided-buffer ring (`io_uring` buf_ring) backing zero-copy receive on
/// the Linux IO path.
#[cfg(target_os = "linux")]
mod bufring;
#[cfg(target_os = "linux")]
mod uring;
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
mod ws;
mod ws_assembly;
/// The multi-worker supervisor (`--workers N`): spawn N independent copies of
/// this binary behind one SO_REUSEPORT port so the kernel load-balances across N
/// proven runtimes. A shell-only change — each worker runs the same proven serve.
mod workers;

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
            eprintln!(
                "dataplane: listening on {local} (io_uring, {} shards{}, over the leanc-compiled proven serve; SIGINT to stop)",
                cfg.shards,
                if zc { ", zero-copy (buf_ring recv + SendZc)" } else { "" }
            );
            let fd = listener.as_raw_fd();
            let gw2 = gw.clone();
            // Watch for SIGINT and exit promptly; the shards block in the ring.
            std::thread::spawn(watch_shutdown);
            uring::run(fd, gw2, cfg.shards, zc);
            drop(listener);
            std::process::exit(0);
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
                eprintln!("dataplane: --io uring requires Linux; falling back to the kqueue reactor");
                true
            }
        };
        if use_kqueue {
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
            std::process::exit(0);
        }
    }

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
            if let Some(s) = uring::stats() {
                eprintln!("dataplane: {s}");
            }
            std::process::exit(0);
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}
