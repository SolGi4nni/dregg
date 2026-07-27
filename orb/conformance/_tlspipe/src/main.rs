//! Minimal post-quantum (X25519MLKEM768) TLS 1.3 pipe for driving the target.
//!
//! The target front door negotiates ONLY the PQ hybrid group, so stock openssl
//! / python ssl cannot reach it. This tool opens one PQ TLS 1.3 connection,
//! writes a raw request read from a file, reads the raw response until EOF or an
//! idle read-timeout, and writes those response bytes verbatim to stdout.
//!
//! Usage: tlspipe <host:port> <reqfile> [alpn] [read-timeout-ms]
//!   alpn            ALPN protocol to offer (default "http/1.1"); "none" = omit.
//!   read-timeout-ms idle read timeout in ms (default 2000); the streaming
//!                   (SSE) probes rely on this to unblock a never-closing body.
//!
//! stderr carries a one-line diagnostic: negotiated group, protocol, and ALPN.
//! Nothing here verifies certificates (the target is self-signed conformance
//! material); this is a wire-level probe, not a trust decision.
use std::io::{Read, Write};
use std::net::TcpStream;
use std::sync::Arc;
use std::time::Duration;

use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::aws_lc_rs;
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use rustls::{ClientConfig, ClientConnection, DigitallySignedStruct, SignatureScheme};

#[derive(Debug)]
struct AcceptAny;
impl ServerCertVerifier for AcceptAny {
    fn verify_server_cert(
        &self,
        _e: &CertificateDer<'_>,
        _i: &[CertificateDer<'_>],
        _s: &ServerName<'_>,
        _o: &[u8],
        _n: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }
    fn verify_tls12_signature(
        &self,
        _m: &[u8],
        _c: &CertificateDer<'_>,
        _d: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }
    fn verify_tls13_signature(
        &self,
        _m: &[u8],
        _c: &CertificateDer<'_>,
        _d: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        vec![
            SignatureScheme::ED25519,
            SignatureScheme::ECDSA_NISTP256_SHA256,
            SignatureScheme::RSA_PSS_SHA256,
            SignatureScheme::RSA_PKCS1_SHA256,
        ]
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let addr = args.next().unwrap_or_else(|| {
        eprintln!("usage: tlspipe <host:port> <reqfile> [alpn] [read-timeout-ms]");
        std::process::exit(2);
    });
    let reqfile = args.next().unwrap_or_else(|| {
        eprintln!("usage: tlspipe <host:port> <reqfile> [alpn] [read-timeout-ms]");
        std::process::exit(2);
    });
    let alpn = args.next().unwrap_or_else(|| "http/1.1".to_string());
    let timeout_ms: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(2000);

    let req = std::fs::read(&reqfile).unwrap_or_else(|e| {
        eprintln!("read {reqfile}: {e}");
        std::process::exit(2);
    });

    let mut provider = aws_lc_rs::default_provider();
    provider.kx_groups = vec![aws_lc_rs::kx_group::X25519MLKEM768];
    let provider = Arc::new(provider);

    let mut config = ClientConfig::builder_with_provider(provider)
        .with_safe_default_protocol_versions()
        .unwrap()
        .dangerous()
        .with_custom_certificate_verifier(Arc::new(AcceptAny))
        .with_no_client_auth();
    if alpn != "none" {
        config.alpn_protocols = vec![alpn.clone().into_bytes()];
    }

    let server_name = ServerName::try_from("localhost").unwrap();
    let mut conn = ClientConnection::new(Arc::new(config), server_name).unwrap();
    let mut sock = TcpStream::connect(&addr).unwrap_or_else(|e| {
        eprintln!("connect {addr}: {e}");
        std::process::exit(2);
    });
    sock.set_read_timeout(Some(Duration::from_millis(timeout_ms)))
        .ok();

    let mut resp = Vec::new();
    {
        let mut tls = rustls::Stream::new(&mut conn, &mut sock);
        if let Err(e) = tls.write_all(&req) {
            eprintln!("HANDSHAKE/WRITE FAILED: {e}");
            std::process::exit(1);
        }
        if let Err(e) = tls.flush() {
            eprintln!("flush: {e}");
            std::process::exit(1);
        }
        // Read until EOF or an idle timeout (WouldBlock/TimedOut) — streaming
        // bodies never send EOF, so the timeout is the terminator there.
        let mut buf = [0u8; 16384];
        loop {
            match tls.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => resp.extend_from_slice(&buf[..n]),
                Err(ref e)
                    if e.kind() == std::io::ErrorKind::WouldBlock
                        || e.kind() == std::io::ErrorKind::TimedOut =>
                {
                    break
                }
                Err(_) => break,
            }
        }
    }
    let group = conn.negotiated_key_exchange_group().map(|g| {
        let raw: u16 = g.name().into();
        format!("{:?}(0x{:04X})", g.name(), raw)
    });
    let negalpn = conn
        .alpn_protocol()
        .map(|p| String::from_utf8_lossy(p).to_string());
    eprintln!(
        "group={:?} proto={:?} alpn={:?} resp_bytes={}",
        group,
        conn.protocol_version(),
        negalpn,
        resp.len()
    );
    std::io::stdout().write_all(&resp).ok();
}
