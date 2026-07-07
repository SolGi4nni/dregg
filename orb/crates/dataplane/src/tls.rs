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
//! The verified handshake additionally negotiates **ALPN** (`http/1.1`), issues
//! **session-resumption** tickets, and does **SNI**-based cert selection and
//! **0-RTT** — all over the same proven `serverStep`. Two of those read the
//! environment Lean-side (not through this cert ABI): `DRORB_TLS_ECDSA_SNI` /
//! `DRORB_TLS_RSA_SNI` bind a pool entry to a host name, and
//! `DRORB_TLS_EARLY_DIR` opts into 0-RTT with a single-use anti-replay register
//! at that path (unset ⇒ resumption only). See `deploy/README.md`.

use std::net::TcpListener;
use std::os::fd::IntoRawFd;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

use crate::serve::ServeGateway;

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
    let cert_path =
        std::env::var("DRORB_TLS_CERT").unwrap_or_else(|_| "conformance/tls/cert.der".to_string());
    let seed_path =
        std::env::var("DRORB_TLS_SEED").unwrap_or_else(|_| "conformance/tls/seed.bin".to_string());
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
        let c = read_optional("DRORB_TLS_ECDSA_CERT", "conformance/tls/ecdsa-cert.der");
        let k = read_optional("DRORB_TLS_ECDSA_KEY", "conformance/tls/ecdsa-key.bin");
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
        let c = read_optional("DRORB_TLS_RSA_CERT", "conformance/tls/rsa-cert.der");
        let n = read_optional("DRORB_TLS_RSA_N", "conformance/tls/rsa-n.bin");
        let e = read_optional("DRORB_TLS_RSA_E", "conformance/tls/rsa-e.bin");
        let d = read_optional("DRORB_TLS_RSA_D", "conformance/tls/rsa-d.bin");
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

/// Run the TLS accept loop on `listener` until shutdown. Each accepted
/// connection is handed off on its own thread to the verified TLS server via
/// `gw.serve_tls`; the serve-owner thread runs the whole connection there (it
/// serializes with the plaintext serve — the honest single-owner trade). The
/// accept loop itself never blocks on a connection.
pub fn run(listener: TcpListener, gw: ServeGateway, cert: TlsCert) {
    listener
        .set_nonblocking(true)
        .expect("failed to set the TLS listener non-blocking");
    let gw = Arc::new(gw);
    let cert = Arc::new(cert);
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping TLS accept loop");
            break;
        }
        match listener.accept() {
            Ok((stream, _peer)) => {
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
                let cert = Arc::clone(&cert);
                let _ = std::thread::Builder::new()
                    .name("drorb-tls-conn".into())
                    .spawn(move || {
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
