//! The DERP relay's TLS front door — the crossing, and nothing else.
//!
//! # What was broken
//!
//! drorb's DERP relay is the verified Lean one (`DerpRelayLive`, forwarding through
//! the proven `Derp.Server.dispatch`, upgrading through the proven `Derp.Upgrade`).
//! It speaks plaintext. A **stock** `tailscale` client does not: `derphttp.Client`
//! dials `https://<host>:<DERPPort>/derp`, so the relay saw a TLS ClientHello where
//! `GET /derp` should have been and logged `no HTTP upgrade` on every attempt. The
//! client then reported `derphttp.Client.Recv connect to region 1: EOF` forever —
//! no relay fallback, and no transport for the disco `CallMeMaybe` that makes hole
//! punching work between peers with no path to each other.
//!
//! # What this is
//!
//! Exactly the crossing `control.rs` already makes for the ts2021 front, pointed at
//! the relay: accept the TLS connection, hand its fd to the **verified** Lean
//! terminator (`@[export drorb_tls_terminate]` — the same `serverStep` /
//! `chooseCert` / `kexStep` and the same proven `appStep` open + `sealAppData` seal
//! record layer as `drorb_tls_serve`, with the decrypted duplex stream pumped
//! through a file descriptor), and splice that plaintext stream to the Lean relay's
//! loopback listener.
//!
//! No TLS is implemented here and no DERP is implemented here. This file owns file
//! descriptors and copies bytes between two sockets; every protocol decision on
//! either side of it — the handshake, the record layer, the certificate choice, the
//! ALPN pin, the HTTP upgrade, the frame codec, the forwarding — is proven Lean.
//! The single crossing function is `control::terminate_tls`, shared with the control
//! front so there is one implementation of it and not two.
//!
//! # Why the client accepts a self-signed leaf
//!
//! `derphttp` pins the relay's certificate by hash when the served `DERPNode` carries
//! `CertName: "sha256-raw:<hex sha256 of the leaf DER>"`
//! (`tlsdial.SetConfigExpectedCertHash`), instead of building a PKI path. That is how
//! a self-hosted region is reachable without a public CA; `derp-relay certname` prints
//! the value and `scripts/run-tailnet.sh` threads it into the served netmap.
//!
//! A pin names ONE certificate, so this front serves a **single-leaf pool**: the
//! Ed25519 leaf from `DRORB_TLS_CERT` / `DRORB_TLS_SEED` and nothing else. The HTTPS
//! front door's pool ([`crate::tls::load_cert`]) also carries the optional ECDSA-P256
//! and RSA-PSS leaves, and the proven `chooseCert` picks among them by the client's
//! `signature_algorithms` — which for a stock `tailscale` client means it presents the
//! ECDSA leaf, whose hash is NOT the advertised pin, and the client rejects the
//! connection with `cert hash does not match expected cert hash` (measured, not
//! guessed). Restricting the pool to one member is what makes "advertised == presented"
//! hold by construction rather than by luck.
//!
//! # Configuration
//!
//! * `DRORB_DERP_TLS_LISTEN` — `host:port` (or a bare port ⇒ localhost) this front
//!   binds. This is the port the served DERPMap advertises as `DERPPort`.
//! * `DRORB_DERP_PLAIN` — `host:port` of the verified Lean relay's plaintext
//!   listener. Defaults to `127.0.0.1:3341`.
//!
//! Unset `DRORB_DERP_TLS_LISTEN` leaves everything exactly as before.

use std::io::{Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream};

/// Copy bytes one way until EOF, then half-close the destination so the peer's read
/// returns EOF instead of hanging. Errors end the direction; they are not protocol
/// events, because this function knows nothing about the protocol.
fn pump(mut from: TcpStream, mut to: TcpStream) {
    let mut buf = [0u8; 16384];
    loop {
        match from.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => {
                if to.write_all(&buf[..n]).is_err() {
                    break;
                }
            }
        }
    }
    let _ = to.shutdown(Shutdown::Write);
}

/// One accepted TLS connection: terminate it over the verified Lean terminator, dial
/// the Lean relay's plaintext listener, and splice the two streams in both directions
/// until either side closes.
fn handle(tls_stream: TcpStream, cert: std::sync::Arc<crate::tls::TlsCert>, relay_addr: String) {
    let (plain, term) = match crate::control::terminate_tls(tls_stream, cert, "drorb-derp-tls") {
        Ok(p) => p,
        Err(e) => {
            eprintln!("dataplane: DERP TLS — terminator crossing failed: {e}");
            return;
        }
    };
    // Dial the relay only once the terminated connection actually produces plaintext.
    // A client that abandons the handshake (a failed certificate pin, a probe) would
    // otherwise still occupy a `ConnId` slot in the relay, which holds slots for the
    // life of the process.
    let mut first = [0u8; 16384];
    let n = match (&plain).read(&mut first) {
        Ok(0) | Err(_) => {
            drop(plain);
            let _ = term.join();
            return;
        }
        Ok(n) => n,
    };
    let mut relay = match TcpStream::connect(&relay_addr) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("dataplane: DERP TLS — cannot reach the verified relay at {relay_addr}: {e}");
            drop(plain);
            let _ = term.join();
            return;
        }
    };
    if relay.write_all(&first[..n]).is_err() {
        drop(plain);
        let _ = term.join();
        return;
    }
    relay.set_nodelay(true).ok();
    plain.set_nodelay(true).ok();
    // The relay holds a DERP connection open for the node's whole session and both
    // directions idle for long stretches (keep-alives only), so neither pump may
    // carry a read timeout.
    let (plain_r, relay_w) = match (plain.try_clone(), relay.try_clone()) {
        (Ok(a), Ok(b)) => (a, b),
        _ => {
            eprintln!("dataplane: DERP TLS — socket clone failed");
            let _ = term.join();
            return;
        }
    };
    let up = std::thread::Builder::new()
        .name("drorb-derp-splice".into())
        .spawn(move || pump(plain_r, relay_w));
    pump(relay, plain);
    if let Ok(h) = up {
        let _ = h.join();
    }
    let _ = term.join();
}

/// The single-leaf certificate pool this front presents: the Ed25519 leaf named by
/// `DRORB_TLS_CERT` and its 32-byte RFC 8032 seed from `DRORB_TLS_SEED`, with the
/// optional ECDSA / RSA pool members deliberately EMPTY.
///
/// The served `CertName` pins one certificate by SHA-256; a multi-member pool lets the
/// proven `chooseCert` present a different member for a different client
/// `signature_algorithms` list, and the pin then fails. One member, one presented leaf,
/// one hash — the advertised pin and the presented certificate cannot disagree.
fn single_leaf_cert() -> Option<crate::tls::TlsCert> {
    let cert_path =
        std::env::var("DRORB_TLS_CERT").unwrap_or_else(|_| "conformance/tls/cert.der".to_string());
    let seed_path =
        std::env::var("DRORB_TLS_SEED").unwrap_or_else(|_| "conformance/tls/seed.bin".to_string());
    let cert_der = match std::fs::read(&cert_path) {
        Ok(b) if !b.is_empty() => b,
        _ => {
            eprintln!("dataplane: DERP TLS — cannot read the leaf {cert_path}");
            return None;
        }
    };
    let seed = match std::fs::read(&seed_path) {
        Ok(b) if b.len() == 32 => b,
        Ok(b) => {
            eprintln!(
                "dataplane: DERP TLS — seed {seed_path} is {} bytes, want 32 (RFC 8032 §5.1.5)",
                b.len()
            );
            return None;
        }
        Err(e) => {
            eprintln!("dataplane: DERP TLS — cannot read the seed {seed_path}: {e}");
            return None;
        }
    };
    Some(crate::tls::TlsCert {
        cert_der,
        seed,
        ecdsa_cert: Vec::new(),
        ecdsa_priv: Vec::new(),
        rsa_cert: Vec::new(),
        rsa_n: Vec::new(),
        rsa_e: Vec::new(),
        rsa_d: Vec::new(),
    })
}

/// Serve the DERP TLS front on `listener`, splicing every terminated connection to the
/// verified Lean relay named by `DRORB_DERP_PLAIN`.
pub fn run_derp_front(listener: TcpListener) {
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| "?".to_string());
    let relay_addr =
        std::env::var("DRORB_DERP_PLAIN").unwrap_or_else(|_| "127.0.0.1:3341".to_string());

    // The terminator's duplex pump pair needs REAL task concurrency (see
    // `control::ensure_task_manager`): with no Lean task manager `IO.asTask` runs the
    // inbound pump INLINE and the two directions serialize, which for a
    // long-lived DERP connection means the relay's frames never reach the client.
    crate::control::ensure_task_manager();

    let cert = match single_leaf_cert() {
        Some(c) => std::sync::Arc::new(c),
        None => {
            eprintln!(
                "dataplane: DRORB_DERP_TLS_LISTEN set but no usable certificate material — \
                 the DERP TLS front is NOT running (a stock client cannot reach the relay)"
            );
            return;
        }
    };
    eprintln!(
        "dataplane: DERP TLS front on {local} -> verified Lean relay at {relay_addr} \
         (VERIFIED TLS 1.3, drorb_tls_terminate)"
    );
    for conn in listener.incoming() {
        match conn {
            Ok(stream) => {
                let cert = cert.clone();
                let relay_addr = relay_addr.clone();
                if let Err(e) = std::thread::Builder::new()
                    .name("drorb-derp-front".into())
                    .spawn(move || handle(stream, cert, relay_addr))
                {
                    eprintln!("dataplane: DERP TLS — connection thread spawn failed: {e}");
                }
            }
            Err(e) => eprintln!("dataplane: DERP TLS — accept failed: {e}"),
        }
    }
}
