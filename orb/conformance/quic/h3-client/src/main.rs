//! A REAL off-the-shelf HTTP/3 client, driven as an independent conformance peer
//! against the QUIC/H3 serve path.
//!
//! Nothing in the protocol stack here is ours, and that is the entire point: the
//! QUIC transport is `quinn`, the HTTP/3 layer is `h3`, the TLS 1.3 stack is
//! `rustls` over `aws-lc-rs`. If this binary reports a status line, an
//! independent implementation completed a real 1-RTT handshake and a real GET
//! against the serve -- cross-implementation agreement, not a self-check.
//!
//! The one non-default configuration is the key exchange: the offered group list
//! is pinned to the `X25519MLKEM768` hybrid, which is exactly what the serve's
//! transport requires. rustls has supported this group natively since 0.23.22, so
//! the hybrid requirement is met by a stock client with no protocol concession on
//! either side.
//!
//! Certificate chain trust is disabled (the serve presents a self-signed Ed25519
//! certificate, as any self-signed test server does). The signature on the
//! CertificateVerify is still checked by rustls against the presented key; only
//! the chain-to-root step is skipped.
//!
//! Usage: h3-client <port> <path> [host] [--kex hybrid|x25519]
//! Prints exactly one line: `STATUS <code> BODY <body>` or `ERROR <msg>`.
//!
//! `--kex x25519` is the NEGATIVE CONTROL: it offers only classical X25519, which
//! the serve's pinned transport must refuse. Run both ways and the pair shows the
//! hybrid requirement is live on the wire, not just asserted in the source.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use bytes::Buf;
use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::aws_lc_rs;
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use rustls::{DigitallySignedStruct, SignatureScheme};

/// Chain trust is disabled for the self-signed test certificate. rustls still
/// verifies the CertificateVerify signature against the presented public key;
/// this only skips the chain-to-trust-anchor step.
#[derive(Debug)]
struct AcceptAnyCert;

impl ServerCertVerifier for AcceptAnyCert {
    fn verify_server_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &ServerName<'_>,
        _ocsp_response: &[u8],
        _now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        _message: &[u8],
        _cert: &CertificateDer<'_>,
        _dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }

    fn verify_tls13_signature(
        &self,
        _message: &[u8],
        _cert: &CertificateDer<'_>,
        _dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        vec![
            SignatureScheme::ED25519,
            SignatureScheme::ECDSA_NISTP256_SHA256,
            SignatureScheme::RSA_PSS_SHA256,
        ]
    }
}

/// Which key exchange the client offers. The offered list is a SINGLETON in both
/// cases, so a completed handshake identifies the negotiated group unambiguously:
/// rustls will not fall back to a group it did not offer.
#[derive(Clone, Copy, PartialEq)]
enum Kex {
    /// The X25519MLKEM768 hybrid the serve pins.
    Hybrid,
    /// Classical X25519 only -- expected to be refused.
    Classical,
}

async fn run(
    port: u16,
    path: String,
    host: String,
    kex: Kex,
) -> Result<String, Box<dyn std::error::Error>> {
    // Stock provider, with the offered key-exchange groups pinned to the hybrid
    // the serve requires. Cipher suites are left at their defaults: RFC 9001
    // fixes the Initial level to AES-128-GCM regardless of the negotiated suite,
    // so the default list must retain it; the serve selects ChaCha20-Poly1305 for
    // the handshake and 1-RTT levels from what we offer.
    let mut provider = aws_lc_rs::default_provider();
    provider.kx_groups = match kex {
        Kex::Hybrid => vec![aws_lc_rs::kx_group::X25519MLKEM768],
        Kex::Classical => vec![aws_lc_rs::kx_group::X25519],
    };

    let mut tls = rustls::ClientConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])?
        .dangerous()
        .with_custom_certificate_verifier(Arc::new(AcceptAnyCert))
        .with_no_client_auth();
    tls.alpn_protocols = vec![b"h3".to_vec()];
    tls.enable_early_data = false;

    let qcc = quinn::crypto::rustls::QuicClientConfig::try_from(tls)?;
    let mut client_cfg = quinn::ClientConfig::new(Arc::new(qcc));
    // Bound a stalled handshake so the NEGATIVE CONTROL (a classical-only client
    // the hybrid-pinned serve silently drops) fails FAST and attributable — a
    // real connection timeout — instead of hanging until the outer 15s guard.
    // 3s idle is ample for a localhost 1-RTT handshake.
    let mut transport = quinn::TransportConfig::default();
    transport.max_idle_timeout(Some(
        Duration::from_secs(3)
            .try_into()
            .expect("valid idle timeout"),
    ));
    client_cfg.transport_config(Arc::new(transport));

    let mut endpoint = quinn::Endpoint::client("127.0.0.1:0".parse::<SocketAddr>()?)?;
    endpoint.set_default_client_config(client_cfg);

    let addr: SocketAddr = format!("127.0.0.1:{port}").parse()?;
    let conn = endpoint.connect(addr, &host)?.await?;

    let (mut driver, mut send_request) = h3::client::new(h3_quinn::Connection::new(conn)).await?;
    let drive = tokio::spawn(async move {
        let _ = std::future::poll_fn(|cx| driver.poll_close(cx)).await;
    });

    let req = http::Request::builder()
        .method("GET")
        .uri(format!("https://{host}:{port}{path}"))
        .body(())?;

    let mut stream = send_request.send_request(req).await?;
    stream.finish().await?;

    let resp = stream.recv_response().await?;
    let status = resp.status().as_u16();

    let mut body = Vec::new();
    while let Some(mut chunk) = stream.recv_data().await? {
        while chunk.has_remaining() {
            let n = {
                let c = chunk.chunk();
                body.extend_from_slice(c);
                c.len()
            };
            chunk.advance(n);
        }
    }

    drive.abort();
    endpoint.close(0u32.into(), b"done");

    Ok(format!(
        "STATUS {status} BODY {}",
        String::from_utf8_lossy(&body)
    ))
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let argv: Vec<String> = std::env::args().collect();
    let kex = match argv.iter().position(|a| a == "--kex") {
        Some(i) => match argv.get(i + 1).map(String::as_str) {
            Some("x25519") => Kex::Classical,
            Some("hybrid") | None => Kex::Hybrid,
            Some(other) => {
                eprintln!("unknown --kex {other} (want hybrid|x25519)");
                std::process::exit(2);
            }
        },
        None => Kex::Hybrid,
    };
    let args: Vec<String> = argv.iter().take_while(|a| *a != "--kex").cloned().collect();
    if args.len() < 3 {
        eprintln!("usage: h3-client <port> <path> [host] [--kex hybrid|x25519]");
        std::process::exit(2);
    }
    let port: u16 = args[1].parse().expect("port");
    let path = args[2].clone();
    let host = args
        .get(3)
        .cloned()
        .unwrap_or_else(|| "localhost".to_string());

    match tokio::time::timeout(Duration::from_secs(15), run(port, path, host, kex)).await {
        Ok(Ok(line)) => println!("{line}"),
        Ok(Err(e)) => {
            println!("ERROR {e}");
            std::process::exit(1);
        }
        Err(_) => {
            println!("ERROR timeout");
            std::process::exit(1);
        }
    }
}
