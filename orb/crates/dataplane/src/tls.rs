//! The HTTPS front door: a TLS 1.3 listener that terminates real TLS in-process
//! over the VERIFIED server handshake + record layer, then serves each decrypted
//! request through the same proven core the plaintext path runs.
//!
//! This module owns only the socket lifecycle for the TLS port: accept a TCP
//! connection, hand its raw fd to the runtime-owner thread's `drorb_tls_serve`
//! seam (`serve::ServeGateway::serve_tls`), and let the verified TLS 1.3 server
//! run the whole connection in-process — the RFC 8446 handshake
//! (`TlsHandshake.serverStep`: ClientHello parse, X25519 ECDHE, key schedule,
//! Certificate/CertificateVerify/Finished flight, client-Finished check), then
//! the established record layer (`TlsHandshake.appStep`) which opens each
//! application_data record, crosses the proven `drorb_serve` on the decrypted
//! request, and seals the response. Nothing in this file parses a TLS record or
//! touches a key; the proven Lean core does, over verified HACL*/EverCrypt.
//!
//! The plaintext listener is untouched: this is an ADDITIONAL listener, bound
//! only when `DRORB_TLS_LISTEN` is set. The certificate material is a POOL: an
//! Ed25519 default end-entity certificate (DER) plus its 32-byte RFC 8032 signing
//! seed, and — when the operator supplies it — an ECDSA-P256 leaf and an
//! RSA-PSS-2048 leaf. The verified handshake presents the one the proven
//! `chooseCert` selects from the pool per the client's `signature_algorithms`, so
//! a real client that rejects Ed25519 (curl/LibreSSL/browsers) is served an
//! ECDSA-P256 or RSA-PSS certificate and connects. All material loads once at
//! boot from the `DRORB_TLS_*` environment (see [`load_cert`]), defaulting to the
//! self-signed material under `conformance/tls/`.
//!
//! The verified handshake additionally negotiates **ALPN** (`h2` then
//! `http/1.1`): when the client selects `h2` the decrypted record stream drives
//! the proven HTTP/2 connection engine, otherwise the HTTP/1.1 serve — both
//! Lean-side, this file is protocol-agnostic. It also issues
//! **session-resumption** tickets, and does **SNI**-based cert selection and
//! **0-RTT** — all over the same proven `serverStep`. Two of those read the
//! environment Lean-side (not through this cert ABI): `DRORB_TLS_ECDSA_SNI` /
//! `DRORB_TLS_RSA_SNI` bind a pool entry to a host name, and
//! `DRORB_TLS_EARLY_DIR` opts into 0-RTT with a single-use anti-replay register
//! at that path (unset ⇒ resumption only). See `deploy/README.md`.

use std::net::TcpListener;
use std::os::fd::{FromRawFd, IntoRawFd};
use std::sync::atomic::Ordering;
use std::sync::{Arc, OnceLock, RwLock};
use std::time::Duration;

use crate::serve::ServeGateway;

pub(crate) mod ondemand;

/// The certificate pool the verified TLS server selects from and presents,
/// loaded once and shared by every connection. Each optional member is an EMPTY
/// vec when the operator did not supply it (the verified side reads empty =
/// "absent"). The Ed25519 default is always present.
pub struct TlsCert {
    /// Ed25519 default end-entity certificate (DER) and its 32-byte seed.
    pub cert_der: Vec<u8>,
    pub seed: Vec<u8>,
    /// ECDSA-P256 leaf (DER) and its 32-byte raw signing scalar; empty = absent.
    pub ecdsa_cert: Vec<u8>,
    pub ecdsa_priv: Vec<u8>,
    /// RSA-PSS-2048 leaf (DER) and its big-endian modulus / public exponent /
    /// private exponent; all empty = absent.
    pub rsa_cert: Vec<u8>,
    pub rsa_n: Vec<u8>,
    pub rsa_e: Vec<u8>,
    pub rsa_d: Vec<u8>,
}

/// The Ed25519 default leaf: `(env var, default path)`. Required — without it
/// there is no TLS listener at all.
const ED25519_MATERIAL: [(&str, &str); 2] = [
    ("DRORB_TLS_CERT", "conformance/tls/cert.der"),
    ("DRORB_TLS_SEED", "conformance/tls/seed.bin"),
];

/// The optional pool members: `(env var, default path)`, ECDSA-P256 first then
/// RSA-PSS-2048. Each group is admitted only when ALL of its members load.
const ECDSA_MATERIAL: [(&str, &str); 2] = [
    ("DRORB_TLS_ECDSA_CERT", "conformance/tls/ecdsa-cert.der"),
    ("DRORB_TLS_ECDSA_KEY", "conformance/tls/ecdsa-key.bin"),
];
const RSA_MATERIAL: [(&str, &str); 4] = [
    ("DRORB_TLS_RSA_CERT", "conformance/tls/rsa-cert.der"),
    ("DRORB_TLS_RSA_N", "conformance/tls/rsa-n.bin"),
    ("DRORB_TLS_RSA_E", "conformance/tls/rsa-e.bin"),
    ("DRORB_TLS_RSA_D", "conformance/tls/rsa-d.bin"),
];

/// Resolve one material slot to the path it actually reads: the env var when
/// set, else the built-in default. Single source of truth for BOTH [`load_cert`]
/// and the hot-reload watcher, so the set of files watched can never drift from
/// the set of files loaded.
fn material_path((env, default): (&str, &str)) -> String {
    std::env::var(env).unwrap_or_else(|_| default.to_string())
}

/// Every file the certificate pool is read from, in load order.
fn cert_paths() -> Vec<String> {
    ED25519_MATERIAL
        .iter()
        .chain(ECDSA_MATERIAL.iter())
        .chain(RSA_MATERIAL.iter())
        .map(|&slot| material_path(slot))
        .collect()
}

/// Read a required certificate file, returning `None` (with a diagnostic) so the
/// caller skips binding the TLS listener rather than aborting the whole host.
fn read_required(what: &str, path: &str) -> Option<Vec<u8>> {
    match std::fs::read(path) {
        Ok(b) => Some(b),
        Err(e) => {
            eprintln!("dataplane: TLS listener disabled — cannot read {what} {path}: {e}");
            None
        }
    }
}

/// Read an OPTIONAL pool member: from `env` if set, else from `default_path`.
/// Returns an empty vec (this member is "absent") when the file does not exist —
/// so the pool degrades gracefully — and reports only a set-but-unreadable env.
fn read_optional(env: &str, default_path: &str) -> Vec<u8> {
    let (path, explicit) = match std::env::var(env) {
        Ok(p) => (p, true),
        Err(_) => (default_path.to_string(), false),
    };
    match std::fs::read(&path) {
        Ok(b) => b,
        Err(e) => {
            if explicit {
                eprintln!("dataplane: TLS — ignoring {env}={path}: {e}");
            }
            Vec::new()
        }
    }
}

/// Load the certificate pool from the `DRORB_TLS_*` environment.
///
/// * Ed25519 default (required): `DRORB_TLS_CERT` / `DRORB_TLS_SEED`, defaulting
///   to the self-signed conformance material. Returns `None` if either is missing
///   or the seed is not exactly 32 bytes.
/// * ECDSA-P256 (optional): `DRORB_TLS_ECDSA_CERT` (DER leaf) +
///   `DRORB_TLS_ECDSA_KEY` (32-byte raw scalar). Added to the pool only when BOTH
///   are set and readable.
/// * RSA-PSS-2048 (optional): `DRORB_TLS_RSA_CERT` (DER leaf) + `DRORB_TLS_RSA_N`
///   / `DRORB_TLS_RSA_E` / `DRORB_TLS_RSA_D` (big-endian components). Added only
///   when ALL are set and readable.
///
/// The verified handshake presents whichever the proven `chooseCert` selects for
/// the client's `signature_algorithms`; the ECDSA / RSA members let curl and
/// browsers (which reject Ed25519) connect.
pub fn load_cert() -> Option<TlsCert> {
    let cert_path = material_path(ED25519_MATERIAL[0]);
    let seed_path = material_path(ED25519_MATERIAL[1]);
    let cert_der = read_required("cert", &cert_path)?;
    let seed = read_required("seed", &seed_path)?;
    if seed.len() != 32 {
        eprintln!(
            "dataplane: TLS listener disabled — seed {seed_path} is {} bytes, want 32 (RFC 8032 §5.1.5)",
            seed.len()
        );
        return None;
    }

    // ECDSA-P256 (optional): both the leaf DER and the 32-byte scalar must load.
    let (ecdsa_cert, ecdsa_priv) = {
        let c = read_optional(ECDSA_MATERIAL[0].0, ECDSA_MATERIAL[0].1);
        let k = read_optional(ECDSA_MATERIAL[1].0, ECDSA_MATERIAL[1].1);
        if c.is_empty() || k.is_empty() {
            (Vec::new(), Vec::new())
        } else if k.len() != 32 {
            eprintln!(
                "dataplane: TLS — ignoring ECDSA cert: signing scalar is {} bytes, want 32",
                k.len()
            );
            (Vec::new(), Vec::new())
        } else {
            eprintln!("dataplane: TLS — ECDSA-P256 certificate in the pool");
            (c, k)
        }
    };

    // RSA-PSS-2048 (optional): leaf DER + big-endian n/e/d must all load.
    let (rsa_cert, rsa_n, rsa_e, rsa_d) = {
        let c = read_optional(RSA_MATERIAL[0].0, RSA_MATERIAL[0].1);
        let n = read_optional(RSA_MATERIAL[1].0, RSA_MATERIAL[1].1);
        let e = read_optional(RSA_MATERIAL[2].0, RSA_MATERIAL[2].1);
        let d = read_optional(RSA_MATERIAL[3].0, RSA_MATERIAL[3].1);
        if c.is_empty() || n.is_empty() || e.is_empty() || d.is_empty() {
            (Vec::new(), Vec::new(), Vec::new(), Vec::new())
        } else {
            eprintln!("dataplane: TLS — RSA-PSS-2048 certificate in the pool");
            (c, n, e, d)
        }
    };

    Some(TlsCert {
        cert_der,
        seed,
        ecdsa_cert,
        ecdsa_priv,
        rsa_cert,
        rsa_n,
        rsa_e,
        rsa_d,
    })
}

// --- the live certificate pool (hot reload) -------------------------------- //

/// The certificate pool every NEW connection is served from.
///
/// Certificate material used to be read once at boot and captured by the accept
/// loop, so rotating a certificate meant restarting the process — which makes
/// automated renewal (whose whole point is to rewrite the leaf every few weeks)
/// impossible to run without dropping traffic. The pool now lives behind this
/// cell instead, and the accept loop takes a fresh handle per connection.
///
/// **Why a swap cannot disturb a live connection.** The pool is an `Arc`. An
/// accepted connection clones the handle BEFORE it starts, and holds that clone
/// for its whole life; a reload replaces the cell's handle but the old pool stays
/// alive for as long as any connection still references it, and is freed only
/// when the last one finishes. So a reload is invisible to connections already
/// running (they keep serving under the certificate they handshook with, which is
/// the only correct behaviour — their keys are bound to that leaf) and takes
/// effect from the very next handshake. Nothing is closed, drained, or paused.
static CERTS: OnceLock<RwLock<Arc<TlsCert>>> = OnceLock::new();

/// Read the cell without letting a poisoned lock take the listener down: a
/// panicking reader/writer must not cost us the ability to serve TLS.
fn certs_cell() -> Option<&'static RwLock<Arc<TlsCert>>> {
    CERTS.get()
}

/// Publish `cert` as the pool new connections are served from, returning the
/// handle. Called once at boot from [`run`] and again on every reload.
fn install(cert: TlsCert) -> Arc<TlsCert> {
    let arc = Arc::new(cert);
    match CERTS.get() {
        Some(cell) => {
            let mut w = cell.write().unwrap_or_else(|e| e.into_inner());
            *w = Arc::clone(&arc);
        }
        None => {
            let _ = CERTS.set(RwLock::new(Arc::clone(&arc)));
        }
    }
    arc
}

/// The pool a new connection should be served from, or `None` before [`run`]
/// has installed one.
pub fn current() -> Option<Arc<TlsCert>> {
    certs_cell().map(|cell| Arc::clone(&cell.read().unwrap_or_else(|e| e.into_inner())))
}

/// Build the PER-CONNECTION pool an on-demand SNI is served from: the boot
/// Ed25519 default (so a client that accepts Ed25519 still connects) plus the
/// freshly minted ECDSA-P256 leaf for THIS SNI in the ECDSA slot. No RSA member.
///
/// The proven `chooseCert` presents the ECDSA leaf to any real client (whose
/// `signature_algorithms` never offer Ed25519), and because the leaf was minted
/// for exactly this connection's peeked SNI, the presented certificate names the
/// host. The leaf is left name-agnostic (`names = []`); on-demand therefore
/// requires that the static `DRORB_TLS_ECDSA_SNI` binding is NOT set (it would
/// pin the ECDSA slot to one host, defeating per-SNI selection).
fn ondemand_pool(boot: &TlsCert, leaf: &ondemand::SniCert) -> Arc<TlsCert> {
    Arc::new(TlsCert {
        cert_der: boot.cert_der.clone(),
        seed: boot.seed.clone(),
        ecdsa_cert: leaf.cert_der.clone(),
        ecdsa_priv: leaf.priv_scalar.clone(),
        rsa_cert: Vec::new(),
        rsa_n: Vec::new(),
        rsa_e: Vec::new(),
        rsa_d: Vec::new(),
    })
}

/// A short identity tag for a pool, so an operator can SEE that a reload
/// actually changed the served material (it is printed on every reload and is
/// what the reload demo compares). This is an identity tag for logs — a
/// non-cryptographic FNV-1a over the leaf DERs — NOT a security fingerprint;
/// nothing authenticates anything against it.
pub fn pool_tag(c: &TlsCert) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for part in [&c.cert_der, &c.ecdsa_cert, &c.rsa_cert] {
        for &b in part.iter() {
            h ^= b as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    format!("{h:016x}")
}

/// Re-read the certificate pool from its files and publish it to new
/// connections. In-flight connections are untouched (see [`CERTS`]).
///
/// A reload that cannot produce a usable pool — a half-written file mid-renewal,
/// a bad seed length — **keeps the previous pool serving** and reports the error.
/// That ordering is the point: `load_cert` fully validates the new material
/// before `install` publishes it, so a broken renewal degrades to "still serving
/// the old certificate" rather than to "no certificate".
pub fn reload() -> Result<String, String> {
    let fresh = load_cert().ok_or_else(|| {
        "certificate material did not load; keeping the previous pool".to_string()
    })?;
    let tag = pool_tag(&fresh);
    install(fresh);
    Ok(tag)
}

/// A change stamp for the pool's files: `(len, mtime)` per path, `None` for a
/// file that is absent or unreadable. Comparing stamps detects a rotation
/// without reading (or hashing) the material every tick.
fn cert_stamp() -> Vec<Option<(u64, std::time::SystemTime)>> {
    cert_paths()
        .iter()
        .map(|p| {
            std::fs::metadata(p)
                .ok()
                .map(|m| (m.len(), m.modified().unwrap_or(std::time::UNIX_EPOCH)))
        })
        .collect()
}

/// Watch the pool's files and reload when any of them changes.
///
/// This is the mechanism automated renewal needs: a renewal process writes the
/// new leaf over the configured paths and the gateway picks it up on its own,
/// with no signal, no restart, and no dropped connection. `DRORB_TLS_WATCH` sets
/// the poll interval in seconds (default 5); `0` disables the watcher, leaving
/// [`reload`] available to an explicit caller.
///
/// A renewal that writes several files is not atomic across them, so a tick can
/// observe a half-rotated pool. Two things keep that safe rather than merely
/// unlikely: a reload that fails validation leaves the old pool serving, and the
/// stamp keeps changing while the writes continue, so the following tick reloads
/// again and converges on the complete new pool.
fn spawn_watcher() {
    let secs = std::env::var("DRORB_TLS_WATCH")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(5);
    if secs == 0 {
        eprintln!("dataplane: TLS cert watch disabled (DRORB_TLS_WATCH=0)");
        return;
    }
    let _ = std::thread::Builder::new()
        .name("drorb-tls-certwatch".into())
        .spawn(move || {
            let mut seen = cert_stamp();
            loop {
                std::thread::sleep(Duration::from_secs(secs));
                if crate::SHUTDOWN.load(Ordering::SeqCst) {
                    return;
                }
                let now = cert_stamp();
                if now == seen {
                    continue;
                }
                seen = now;
                match reload() {
                    Ok(tag) => eprintln!(
                        "dataplane: TLS certificate material changed on disk — reloaded, pool={tag} (live connections undisturbed)"
                    ),
                    Err(e) => eprintln!("dataplane: TLS cert reload FAILED: {e}"),
                }
            }
        });
}

/// Run the TLS accept loop on `listener` until shutdown. Each accepted
/// connection is handed off on its own thread to the verified TLS server via
/// `gw.serve_tls`; the serve-owner thread runs the whole connection there (it
/// serializes with the plaintext serve — the honest single-owner trade). The
/// accept loop itself never blocks on a connection.
pub fn run(listener: TcpListener, gw: ServeGateway, cert: TlsCert) {
    // KEX posture (DRORB_TLS_KEX). The verified server reads this env var itself
    // and builds the ServerParams accordingly (Dataplane.Tls.KexPosture drives
    // deployedTlsParams); we surface it here for operator visibility and to flag
    // a mistyped value. `preferred` (default) offers X25519MLKEM768 + X25519 and
    // honors the client's best group; `required` pins the hybrid (classical
    // clients rejected); `classical` offers only X25519 (no post-quantum).
    let posture = match std::env::var("DRORB_TLS_KEX").ok().as_deref() {
        Some("required") => "required",
        Some("classical") => "classical",
        None | Some("") | Some("preferred") => "preferred",
        Some(other) => {
            eprintln!("dataplane: TLS - unknown DRORB_TLS_KEX={other:?}, using preferred");
            "preferred"
        }
    };
    eprintln!("dataplane: TLS KEX posture = {posture}");
    listener
        .set_nonblocking(true)
        .expect("failed to set the TLS listener non-blocking");
    let gw = Arc::new(gw);
    // Publish the boot pool, then start watching its files so a renewal is
    // picked up without a restart.
    let boot = install(cert);
    eprintln!("dataplane: TLS certificate pool loaded, pool={}", pool_tag(&boot));
    spawn_watcher();
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping TLS accept loop");
            break;
        }
        match listener.accept() {
            Ok((stream, peer)) => {
                // Sockets accepted from a non-blocking listener inherit
                // non-blocking mode on BSD/macOS; force this connection back to
                // blocking so the Lean record-layer reads (which rely on
                // SO_RCVTIMEO — ignored on a non-blocking fd) actually block for
                // the peer's next record instead of returning EAGAIN at once.
                let _ = stream.set_nonblocking(false);
                let _ = stream.set_nodelay(true);
                // The Lean side owns and closes the fd; take it out of Rust's
                // stream so the socket is not double-closed on drop.
                let fd = stream.into_raw_fd();
                let gw = Arc::clone(&gw);
                // Take the BOOT pool handle HERE, once, for this connection's
                // whole life — a reload after this point cannot disturb it.
                let Some(boot) = current() else {
                    eprintln!("dataplane: TLS — no certificate pool installed; dropping connection");
                    // Re-own the fd so dropping it closes the socket (we took it
                    // out of the stream above precisely so Lean could own it).
                    drop(unsafe { std::net::TcpStream::from_raw_fd(fd) });
                    continue;
                };
                // Bind the peer address to this fd before the verified server
                // touches it, so the observation seam can attribute the requests
                // it reports back (the proven side never sees the peer address).
                obs::accepted(fd as u32, peer.ip());
                let _ = std::thread::Builder::new()
                    .name("drorb-tls-conn".into())
                    .spawn(move || {
                        // On-demand SNI path: PEEK the ClientHello (non-destructive
                        // — the proven server still reads the whole handshake) and,
                        // for an SNI we hold no leaf for, ask the authorizer + mint.
                        // This runs on the connection thread, NOT the accept loop,
                        // so a slow ACME order never blocks accepting other peers.
                        // Disabled (`DRORB_TLS_ONDEMAND` unset) ⇒ zero added work.
                        let cert = if ondemand::enabled() {
                            match ondemand::peek_sni(fd) {
                                Some(sni) => match ondemand::resolve(&sni) {
                                    ondemand::Resolution::Serve(leaf) => {
                                        ondemand_pool(&boot, &leaf)
                                    }
                                    ondemand::Resolution::Refuse => {
                                        // Re-own the fd so the drop closes the
                                        // socket (Lean never runs on it).
                                        drop(unsafe { std::net::TcpStream::from_raw_fd(fd) });
                                        return;
                                    }
                                    ondemand::Resolution::Passthrough => boot,
                                },
                                None => boot,
                            }
                        } else {
                            boot
                        };
                        gw.serve_tls(fd, cert);
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

// --- the host observation seam --------------------------------------------- //

/// The host side of the `drorb_tls_obs_*` seam: what the verified TLS connection
/// reports about itself, turned into the SAME metrics, OTel spans and access-log
/// lines the plaintext reactors emit.
///
/// ## Why this module exists
///
/// `blocking.rs` / `kqueue.rs` / `uring.rs` observe every request because the
/// host owns their loop: it holds the request bytes, gets the response bytes
/// back from the proven serve, and times the round trip. The HTTPS front door is
/// built the other way round — [`run`] hands the whole connection to the verified
/// server and the decrypted traffic never returns to the host — so none of that
/// instrumentation could fire, and HTTPS traffic was un-metered, un-traced and
/// un-logged. That is a poor property for a gateway whose front door is HTTPS.
///
/// The proven side now REPORTS what it did (see the `drorb_tls_obs_*` seam in
/// `Dataplane.lean`) and this module records it. The recording is untrusted-shell
/// work in exactly the sense the other three modules are: it reads bytes that are
/// already decided, renders text, and returns nothing the proven code consults.
///
/// ## What it adds over the plaintext instrumentation
///
/// Everything the plaintext path reports, plus the facts that only exist on a TLS
/// connection and that an operator of a PQ-capable gateway actually needs: the
/// negotiated group (and so whether the post-quantum hybrid was used), the cipher
/// suite, the ALPN protocol, and the SNI host — the last read by the PROVEN
/// ClientHello parser, not re-parsed here.
///
/// ## h2-over-TLS requests ARE now itemised (from inside the proof)
///
/// When ALPN selects `h2` the connection is driven by the proven HTTP/2 engine,
/// and its requests/responses live inside HPACK-encoded frames. Decoding those
/// in the host would duplicate — in untrusted Rust — the parsing the proven
/// engine already does correctly, the exact inversion this codebase avoids. So
/// the fix was made in the proof-carrying component: the engine records each
/// dispatched request/response on its own state (`H2.Conn.ReqObs`) and REPORTS
/// it through `drorb_h2_obs_req` (see [`drorb_h2_obs_req`]), which renders the
/// SAME metric / span / access-log line the HTTP/1.1 tls seam does — with no
/// host-side HPACK. `drorb_tls_connections_total{alpn="h2"}` still counts h2
/// connections; now the requests on them are itemised too.
///
/// Requests served from ACCEPTED 0-RTT early data on the h2 path are reported by
/// the same hook (`enterApp` reports its first-burst dispatch). One residual: the
/// h2 path has no per-request BEGIN, so a reported request's latency is measured
/// from the connection clock rather than that single request's service.
///
/// Requests served from ACCEPTED 0-RTT early data are likewise not itemised; 0-RTT
/// is opt-in (`DRORB_TLS_EARLY_DIR`) and off by default.
///
/// ## Lifetime and boundedness
///
/// State is keyed by file descriptor. [`accepted`] installs a fresh entry the
/// moment a connection is accepted, which is also what clears whatever the
/// PREVIOUS connection on that (reused) descriptor left behind — so a stale entry
/// can never be read, and the map is bounded by the process descriptor table
/// rather than growing with connections served.
pub(crate) mod obs {
    use std::collections::HashMap;
    use std::net::{IpAddr, Ipv4Addr};
    use std::sync::Mutex;
    use std::time::Instant;

    use crate::access_log::{self, ReqLine};
    use crate::metrics;
    use crate::otel;

    /// Opaque Lean heap object; we only ever hold and hand back the pointer.
    #[repr(C)]
    pub struct LeanObject {
        _private: [u8; 0],
    }

    unsafe extern "C" {
        fn drorb_sarray_len(o: *mut LeanObject) -> usize;
        fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
        fn drorb_obj_dec(o: *mut LeanObject);
        fn drorb_io_unit_ok() -> *mut LeanObject;
    }

    /// What the verified handshake settled on for one connection, as the host
    /// needs it for a span / log line. Every field is reported by the proven
    /// side (except `peer`, which only the host can see).
    #[derive(Clone, Debug)]
    pub struct TlsInfo {
        pub peer: IpAddr,
        pub sni: String,
        pub alpn: String,
        /// The negotiated named group, as its IANA code point.
        pub group: u32,
        /// The negotiated cipher suite, as its IANA code point.
        pub suite: u32,
        pub start: Option<Instant>,
    }

    impl Default for TlsInfo {
        fn default() -> Self {
            TlsInfo {
                peer: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
                sni: String::new(),
                alpn: String::new(),
                group: 0,
                suite: 0,
                start: None,
            }
        }
    }

    impl TlsInfo {
        /// The negotiated group's name. `0x11EC` is X25519MLKEM768, the
        /// post-quantum hybrid (`xwingGroup` in the proven handshake).
        pub fn group_name(&self) -> String {
            match self.group {
                0x11EC => "X25519MLKEM768".to_string(),
                0x001D => "x25519".to_string(),
                0x0017 => "secp256r1".to_string(),
                0 => "-".to_string(),
                g => format!("0x{g:04x}"),
            }
        }

        /// Was the post-quantum hybrid key exchange actually negotiated? This is
        /// the fact an operator rolling out PQ needs per request, and it is not
        /// observable from outside the connection.
        pub fn pq_hybrid(&self) -> bool {
            self.group == 0x11EC
        }

        /// The negotiated cipher suite's name (RFC 8446 §B.4).
        pub fn suite_name(&self) -> String {
            match self.suite {
                0x1301 => "TLS_AES_128_GCM_SHA256".to_string(),
                0x1302 => "TLS_AES_256_GCM_SHA384".to_string(),
                0x1303 => "TLS_CHACHA20_POLY1305_SHA256".to_string(),
                0 => "-".to_string(),
                s => format!("0x{s:04x}"),
            }
        }
    }

    /// Per-descriptor connection state. See the module note on boundedness.
    fn conns() -> &'static Mutex<HashMap<u32, TlsInfo>> {
        static CONNS: std::sync::OnceLock<Mutex<HashMap<u32, TlsInfo>>> =
            std::sync::OnceLock::new();
        CONNS.get_or_init(|| Mutex::new(HashMap::new()))
    }

    /// Run `f` against the entry for `fd`, if one exists.
    fn with<R>(fd: u32, f: impl FnOnce(&mut TlsInfo) -> R) -> Option<R> {
        let mut m = conns().lock().unwrap_or_else(|e| e.into_inner());
        m.get_mut(&fd).map(f)
    }

    /// A connection was accepted on `fd` from `peer`. Installs a FRESH entry,
    /// which is what makes a reused descriptor safe.
    pub fn accepted(fd: u32, peer: IpAddr) {
        let mut m = conns().lock().unwrap_or_else(|e| e.into_inner());
        m.insert(
            fd,
            TlsInfo {
                peer,
                ..TlsInfo::default()
            },
        );
    }

    /// Borrow an owned Lean `ByteArray` as host bytes, then release it. The seam
    /// passes each `ByteArray` owned (`lean_inc` at the call site), so the host
    /// must drop it or the connection leaks one buffer per call.
    ///
    /// # Safety
    /// `o` must be a live owned Lean sarray, or null.
    unsafe fn take_bytes(o: *mut LeanObject) -> Vec<u8> {
        if o.is_null() {
            return Vec::new();
        }
        unsafe {
            let n = drorb_sarray_len(o);
            let p = drorb_sarray_ptr(o);
            let v = if n == 0 || p.is_null() {
                Vec::new()
            } else {
                std::slice::from_raw_parts(p, n).to_vec()
            };
            drorb_obj_dec(o);
            v
        }
    }

    /// Run an observation body so that NOTHING it does can reach the proven
    /// connection: a panic in host-side rendering unwinds into Lean as undefined
    /// behaviour, so it is caught and dropped here. Observation failing must cost
    /// at most the observation.
    fn guard(f: impl FnOnce() + std::panic::UnwindSafe) -> *mut LeanObject {
        let _ = std::panic::catch_unwind(f);
        unsafe { drorb_io_unit_ok() }
    }

    // --- the exported hooks (see `Dataplane.lean`) -------------------------- //
    //
    // Signatures match the code Lean GENERATES, which erases the `IO` world
    // token: an `@[extern] ... : IO Unit` taking (UInt32, ByteArray) is called as
    // `f(uint32_t, lean_object*)` and must return the IO result object.

    /// The proven ClientHello parser read this connection's SNI (empty = none).
    #[unsafe(no_mangle)]
    pub extern "C" fn drorb_tls_obs_sni(fd: u32, sni: *mut LeanObject) -> *mut LeanObject {
        let host = unsafe { take_bytes(sni) };
        guard(move || {
            let host = String::from_utf8_lossy(&host).to_string();
            with(fd, |i| i.sni = host);
        })
    }

    /// The handshake established: record the negotiated parameters.
    #[unsafe(no_mangle)]
    pub extern "C" fn drorb_tls_obs_conn(
        fd: u32,
        group: u32,
        suite: u32,
        alpn: *mut LeanObject,
    ) -> *mut LeanObject {
        let alpn = unsafe { take_bytes(alpn) };
        guard(move || {
            let alpn = String::from_utf8_lossy(&alpn).to_string();
            metrics::note_tls_connection(&alpn);
            with(fd, |i| {
                i.group = group;
                i.suite = suite;
                i.alpn = alpn;
            });
        })
    }

    /// A request is about to be served: start its clock.
    #[unsafe(no_mangle)]
    pub extern "C" fn drorb_tls_obs_begin(fd: u32) -> *mut LeanObject {
        guard(move || {
            with(fd, |i| i.start = Some(Instant::now()));
        })
    }

    /// A request was served: emit the metric, the span and the access-log line.
    #[unsafe(no_mangle)]
    pub extern "C" fn drorb_tls_obs_req(
        fd: u32,
        req: *mut LeanObject,
        resp: *mut LeanObject,
    ) -> *mut LeanObject {
        let req = unsafe { take_bytes(req) };
        let resp = unsafe { take_bytes(resp) };
        guard(move || {
            let Some(info) = with(fd, |i| i.clone()) else {
                // No entry: the connection was not accepted through `run` (or the
                // descriptor was recycled underneath us). Record nothing rather
                // than attribute the request to the wrong connection.
                return;
            };
            let start = info.start.unwrap_or_else(Instant::now);
            let line = ReqLine::parse(&req);

            // The same three surfaces the plaintext reactors drive, in the same
            // order, so HTTPS and HTTP traffic land in one consistent picture.
            metrics::record(&resp, None);
            metrics::observe_latency(start.elapsed());
            metrics::note_tls_request(info.pq_hybrid());
            otel::record_span_tls(info.peer, &line, &resp, start, &info);
            access_log::log_tls(info.peer, &line, &resp, start, &info);
        })
    }

    /// An h2-over-TLS request was served: the proven HTTP/2 engine reported it
    /// (see `drorb_h2_obs_req` in `Dataplane.lean`) with the method, `:path`,
    /// `:status`, response body byte count and stream id it ALREADY computed.
    /// The host renders the same metric / span / access-log line the HTTP/1.1
    /// tls seam does, so h2 traffic is itemised without the host ever decoding
    /// HPACK — the blind spot closed from inside the proof.
    #[unsafe(no_mangle)]
    pub extern "C" fn drorb_h2_obs_req(
        fd: u32,
        method: *mut LeanObject,
        path: *mut LeanObject,
        status: u32,
        _stream: u32,
        resp_bytes: u32,
    ) -> *mut LeanObject {
        let method = unsafe { take_bytes(method) };
        let path = unsafe { take_bytes(path) };
        guard(move || {
            let Some(info) = with(fd, |i| i.clone()) else {
                // Descriptor not tracked (recycled, or not accepted through
                // `run`): record nothing rather than misattribute the request.
                return;
            };
            // No per-request begin on the h2 path (the engine batches frames),
            // so latency is best-effort from the connection clock.
            let start = info.start.unwrap_or_else(Instant::now);
            let line = ReqLine {
                method: String::from_utf8_lossy(&method).to_string(),
                path: String::from_utf8_lossy(&path).to_string(),
            };
            let status = status.to_string();
            // The same three surfaces, in the same order, as `drorb_tls_obs_req`
            // — but from the engine's structured report, not response bytes.
            metrics::record_streamed(
                format!("HTTP/2 {status} ").as_bytes(),
                resp_bytes as u64,
                None,
            );
            metrics::observe_latency(start.elapsed());
            metrics::note_tls_request(info.pq_hybrid());
            otel::record_span_tls_status(info.peer, &line, &status, start, &info);
            access_log::log_tls_h2(info.peer, &line, &status, resp_bytes as u64, start, &info);
        })
    }
}

// --- the host static-file lane on the TLS path ----------------------------- //
//
// The HTTPS front door terminates the whole connection inside the proven Lean
// server (`drorb_tls_serve`), so the decrypted request never reaches a host
// reactor the way a plaintext request does — the static-file lane the plaintext
// reactors (blocking/uring/kqueue) dispatch could not fire, and a `/static/*`
// request returned `404` over TLS while returning the file on plaintext.
//
// This seam closes that gap. The verified record layer, on a request the proven
// serve answered with a `404`, hands the decrypted request bytes back here; for a
// request under the configured static prefix this crosses the SAME proven
// `drorb_static_resolve` / `drorb_static_decide` decisions the plaintext lane
// crosses and returns the served response bytes (`head ++ body`), which the Lean
// side seals through the record layer. EMPTY means "not a static-lane hit" — the
// proven `404` stands.
//
// Called ONLY from the runtime-owner serve thread, from inside `drorb_tls_serve`
// (the record layer's per-request step). It therefore invokes the proven
// `drorb_static_resolve` / `drorb_static_decide` C symbols DIRECTLY — the same
// single-owner discipline `run_tls_conn` uses to call `drorb_tls_serve` — rather
// than routing them back through the serve-thread job queue, which would deadlock
// (the serve thread is busy running this very connection).

/// Opaque Lean heap object; only ever held and handed back as a pointer.
#[repr(C)]
struct StaticLeanObj {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut StaticLeanObj;
    fn drorb_sarray_len(o: *mut StaticLeanObj) -> usize;
    fn drorb_sarray_ptr(o: *mut StaticLeanObj) -> *const u8;
    fn drorb_obj_dec(o: *mut StaticLeanObj);
    /// Wrap an owned Lean `ByteArray` as a successful `IO ByteArray` result
    /// (`lean_io_result_mk_ok`, a static inline not nameable from Rust — see
    /// `crates/dataplane/ffi/drorb_ffi.c`).
    fn drorb_io_bytes_ok(o: *mut StaticLeanObj) -> *mut StaticLeanObj;
    /// The proven static-file PATH decision (`Route.StaticResolve.resolveRel`).
    fn drorb_static_resolve(input: *mut StaticLeanObj) -> *mut StaticLeanObj;
    /// The proven static-file RESPONSE decision (`Route.StaticDecide`).
    fn drorb_static_decide(input: *mut StaticLeanObj) -> *mut StaticLeanObj;
}

/// Cross the proven `drorb_static_resolve` seam DIRECTLY (serve-owner thread).
/// The relative target bytes in; the '/'-joined resolved path on the core's
/// accept (`0x01 ++ path`), `None` on its reject (`0x00`) — the caller answers
/// `404`. Mirrors `ServeGateway::call_static_resolve`, sans the job queue.
fn static_resolve_direct(rel: &[u8]) -> Option<Vec<u8>> {
    unsafe {
        let input = drorb_sarray_of_bytes(rel.as_ptr(), rel.len());
        let out = drorb_static_resolve(input); // consumes `input`
        let n = drorb_sarray_len(out);
        let p = drorb_sarray_ptr(out);
        let v = if n == 0 || p.is_null() {
            Vec::new()
        } else {
            std::slice::from_raw_parts(p, n).to_vec()
        };
        drorb_obj_dec(out);
        match v.split_first() {
            Some((&1, resolved)) => Some(resolved.to_vec()),
            _ => None,
        }
    }
}

/// Cross the proven `drorb_static_decide` seam DIRECTLY (serve-owner thread).
/// The boundary-fact frame in; the encoded serving plan out, `None` on an empty
/// (malformed-frame) output. Mirrors `ServeGateway::call_static_decide`.
fn static_decide_direct(frame: &[u8]) -> Option<Vec<u8>> {
    unsafe {
        let input = drorb_sarray_of_bytes(frame.as_ptr(), frame.len());
        let out = drorb_static_decide(input); // consumes `input`
        let n = drorb_sarray_len(out);
        let p = drorb_sarray_ptr(out);
        let v = if n == 0 || p.is_null() {
            Vec::new()
        } else {
            std::slice::from_raw_parts(p, n).to_vec()
        };
        drorb_obj_dec(out);
        if v.is_empty() {
            None
        } else {
            Some(v)
        }
    }
}

/// **`drorb_static_tls_serve` — the static-file lane for the HTTPS front door.**
/// `req` is the decrypted request bytes (owned Lean `ByteArray`, consumed here);
/// `keepalive` is the proven keep-alive verdict (`0`/`1`) the record layer
/// already computed, threaded in so the served `Connection` header matches the
/// connection's disposition. Returns an `IO ByteArray`: the served response bytes
/// (`head ++ body`) for a static-lane hit, or EMPTY when the request is not under
/// the static prefix / no static root is configured / the serve failed — in which
/// case the Lean side keeps the proven `404`.
///
/// # Safety
/// Invoked only by leanc-generated code on the runtime-owner serve thread, with
/// `req` an owned Lean sarray (or null).
#[unsafe(no_mangle)]
pub extern "C" fn drorb_static_tls_serve(
    req: *mut StaticLeanObj,
    keepalive: u32,
) -> *mut StaticLeanObj {
    // Borrow the request bytes, then release the owned argument.
    let req_bytes: Vec<u8> = unsafe {
        if req.is_null() {
            Vec::new()
        } else {
            let n = drorb_sarray_len(req);
            let p = drorb_sarray_ptr(req);
            let v = if n == 0 || p.is_null() {
                Vec::new()
            } else {
                std::slice::from_raw_parts(p, n).to_vec()
            };
            drorb_obj_dec(req);
            v
        }
    };

    let out: Vec<u8> = (|| {
        let sr = crate::static_serve::get()?;
        if !sr.is_static_path(&req_bytes) {
            return None;
        }
        sr.serve_tls_buf(
            &req_bytes,
            keepalive != 0,
            static_resolve_direct,
            static_decide_direct,
        )
        .ok()
    })()
    .unwrap_or_default();

    unsafe {
        let ba = drorb_sarray_of_bytes(out.as_ptr(), out.len());
        drorb_io_bytes_ok(ba)
    }
}
