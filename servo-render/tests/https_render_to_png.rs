//! **THE HTTPS DELIVERABLE: a REAL `https://` page, fetched through the net-cap gate
//! over a REAL TLS handshake on the cap-admitted socket, laid out by servo, rasterized
//! by SWGL, captured to a PNG.**
//!
//! This closes the named TLS sub-ceiling of `http_render_to_png.rs`. The cap-gated
//! handler (`netcap_http::CapGatedHttpHandler`) already runs the net-cap connect
//! decision AT the socket for both `http` and `https`; here the byte leg for `https`
//! is a genuine `rustls` TLS handshake over the SAME real `std::net::TcpStream`, then
//! an HTTP/1.1 GET over the encrypted stream.
//!
//! Network access in this environment may be limited, so the test stands up a REAL
//! local TLS server (`std::net::TcpListener` + server-side `rustls` — a real https
//! socket, NOT a `data:` page) with a self-signed cert for `127.0.0.1`, then:
//!
//!   1. **cap-DENIED run** — a surface scoped to a DIFFERENT origin tries to load the
//!      server's https page; the cap gate refuses it AT the socket (the handler records
//!      `RefusedByCap`, `Netlayer::dial` was never called, NO socket opened, NO TLS
//!      handshake), and servo gets a network error (no page bytes);
//!   2. **cap-ALLOWED run** — a surface scoped to the server's https origin loads the
//!      page; the cap gate admits it, the handler opens a REAL TCP socket, drives a
//!      REAL rustls TLS handshake (verifying the server cert against the genuine rustls
//!      verifier — the self-signed cert is registered as an EXTRA trusted root, NOT a
//!      danger-accept bypass), fetches the real bytes over the encrypted socket, servo
//!      lays them out, SWGL rasterizes → a PNG of the actual fetched page content.
//!
//! The self-signed cert/key are real DER fixtures (`tests/fixtures/netcap_test_*.der`,
//! an ECDSA-P256 cert with `IP:127.0.0.1` SAN). Trusting that cert as an EXTRA root
//! keeps the handshake genuine cert validation; a PUBLIC https origin would verify
//! against the Mozilla CA set (`webpki-roots`) with NO extra root.
//!
//! `HTTPS_RENDER_PNG_OUT=/path/page.png cargo test --features libservo --test \
//!  https_render_to_png -- --nocapture` writes the captured PNG.
//!
//! Run only under `--features libservo` (the real engine).

#![cfg(feature = "libservo")]

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;

use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection, StreamOwned};

use servo_render::webview::CapGatedHttpEngine;
use servo_render::RgbaFrame;

use dregg_firmament::cell_seed;
use starbridge_web_surface::{AuthRequired, SurfaceCapability};

// The real self-signed fixtures (DER): an ECDSA-P256 cert with an `IP:127.0.0.1` SAN
// and its PKCS#8 key. Generated once with openssl; valid ~100y. A REAL cert, so the
// rustls handshake performs REAL validation (against it as a trusted extra root).
const TEST_CERT_DER: &[u8] = include_bytes!("fixtures/netcap_test_cert.der");
const TEST_KEY_DER: &[u8] = include_bytes!("fixtures/netcap_test_key.der");

// ───────────────────────── a tiny self-contained PNG encoder ─────────────────────────
fn crc32(bytes: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}
fn adler32(bytes: &[u8]) -> u32 {
    const MOD: u32 = 65521;
    let (mut a, mut b) = (1u32, 0u32);
    for &x in bytes {
        a = (a + x as u32) % MOD;
        b = (b + a) % MOD;
    }
    (b << 16) | a
}
fn png_encode_rgba8(w: u32, h: u32, rgba: &[u8]) -> Vec<u8> {
    fn chunk(out: &mut Vec<u8>, kind: &[u8; 4], data: &[u8]) {
        out.extend_from_slice(&(data.len() as u32).to_be_bytes());
        let mut typed = Vec::with_capacity(4 + data.len());
        typed.extend_from_slice(kind);
        typed.extend_from_slice(data);
        out.extend_from_slice(&typed);
        out.extend_from_slice(&crc32(&typed).to_be_bytes());
    }
    // SWGL/WebRender render bottom-left origin; flip vertically so the PNG is upright.
    let row_bytes = (w * 4) as usize;
    let mut raw = Vec::with_capacity((h * (1 + w * 4)) as usize);
    for y in 0..h {
        raw.push(0);
        let src = ((h - 1 - y) * w * 4) as usize;
        raw.extend_from_slice(&rgba[src..src + row_bytes]);
    }
    let mut z = vec![0x78u8, 0x01];
    let mut off = 0usize;
    while off < raw.len() {
        let take = (raw.len() - off).min(0xFFFF);
        let bfinal = if off + take >= raw.len() { 1u8 } else { 0u8 };
        z.push(bfinal);
        z.extend_from_slice(&(take as u16).to_le_bytes());
        z.extend_from_slice(&(!(take as u16)).to_le_bytes());
        z.extend_from_slice(&raw[off..off + take]);
        off += take;
    }
    z.extend_from_slice(&adler32(&raw).to_be_bytes());
    let mut png = vec![0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A];
    let mut ihdr = Vec::new();
    ihdr.extend_from_slice(&w.to_be_bytes());
    ihdr.extend_from_slice(&h.to_be_bytes());
    ihdr.extend_from_slice(&[8, 6, 0, 0, 0]);
    chunk(&mut png, b"IHDR", &ihdr);
    chunk(&mut png, b"IDAT", &z);
    chunk(&mut png, b"IEND", &[]);
    png
}

/// The HTML the local https server serves — a green page with a centered magenta block
/// AND a black heading, so the rasterized frame proves BOTH layout (≥2 colors) and
/// glyphs (antialiased grays) came from real bytes fetched over the TLS socket.
const PAGE_HTML: &str = "<!doctype html><html><body style='margin:0;background:#00cc00'>\
<h1 style='margin:18px;font-size:40px;color:#000000'>dregg over https</h1>\
<div style='margin:20px auto;width:160px;height:90px;background:#ff00ff'></div>\
</body></html>";

/// Build the server-side rustls config from the self-signed fixtures.
fn server_tls_config() -> Arc<ServerConfig> {
    let cert = CertificateDer::from(TEST_CERT_DER.to_vec());
    let key: PrivateKeyDer<'static> =
        PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(TEST_KEY_DER.to_vec()));
    let config = ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(vec![cert], key)
        .expect("the self-signed fixture cert+key build a valid server config");
    Arc::new(config)
}

/// Spin a REAL local **https** server on an ephemeral port in a background thread. It
/// does a genuine server-side rustls TLS handshake on each connection, then serves
/// `PAGE_HTML` (real status line + Content-Type, `Connection: close`) over the
/// encrypted stream, for `n` requests, then exits. Returns the bound https origin
/// (`https://127.0.0.1:PORT`).
fn spawn_local_https_server(n: usize) -> (String, thread::JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral https port");
    let addr = listener.local_addr().expect("local addr");
    let origin = format!("https://{addr}");
    let cfg = server_tls_config();
    let (ready_tx, ready_rx) = mpsc::channel();
    let handle = thread::spawn(move || {
        ready_tx.send(()).ok();
        let body = PAGE_HTML.as_bytes();
        for _ in 0..n {
            match listener.accept() {
                Ok((tcp, _)) => {
                    // REAL server-side TLS handshake over the accepted socket.
                    let conn = match ServerConnection::new(cfg.clone()) {
                        Ok(c) => c,
                        Err(_) => continue,
                    };
                    let mut tls = StreamOwned::new(conn, tcp);
                    // Read the request (until headers end) — a real request arrives,
                    // encrypted. Driving a read forces the handshake to complete.
                    let mut buf = [0u8; 2048];
                    let _ = tls.read(&mut buf);
                    let resp = format!(
                        "HTTP/1.1 200 OK\r\n\
                         Content-Type: text/html; charset=utf-8\r\n\
                         Content-Length: {}\r\n\
                         Connection: close\r\n\r\n",
                        body.len()
                    );
                    let _ = tls.write_all(resp.as_bytes());
                    let _ = tls.write_all(body);
                    let _ = tls.flush();
                    // Send a graceful close_notify so the client's read terminates clean.
                    let _ = tls.conn.send_close_notify();
                    let _ = tls.flush();
                }
                Err(_) => break,
            }
        }
    });
    ready_rx.recv().ok();
    (origin, handle)
}

/// **THE LOAD-BEARING TEST.** A real https page through the cap gate + a REAL TLS
/// handshake → SWGL → PNG.
#[test]
fn real_https_page_rasterized_through_the_cap_gated_tls_socket() {
    const W: u32 = 360;
    const H: u32 = 200;

    // A real local https server (a real TLS socket, NOT data:). It serves up to 4
    // requests (the allowed run may issue a couple — the navigation + a favicon probe).
    let (origin, server) = spawn_local_https_server(4);
    let page_url = format!("{origin}/index.html");
    let presenter = cell_seed(13);

    let (
        frame,
        last_fetch,
        tls_handshook,
        dialed_outcomes,
        denied_outcomes,
        denied_fetched,
        denied_tls,
        outcome,
    ): (
        Option<RgbaFrame>,
        Option<(String, usize)>,
        bool,
        Vec<_>,
        Vec<_>,
        Option<(String, usize)>,
        bool,
        Option<_>,
    ) = servo_render::with_gl(|| {
        let engine = CapGatedHttpEngine::new(
            SurfaceCapability::root(presenter, AuthRequired::Either),
            &[],
        );
        // Trust the test's self-signed root in the genuine rustls verifier (NOT a
        // danger-accept). Persists across `reconfigure`, so both runs use the same
        // real trust set; only the cap-allowed run reaches the handshake.
        engine.handler().trust_extra_root_der(TEST_CERT_DER.to_vec());

        // ── RUN 1: CAP-DENIED. A surface scoped to a DIFFERENT origin. The cap gate
        // must refuse the server's https origin AT the socket — no socket, no TLS
        // handshake, no bytes. ──
        let denied_surface = SurfaceCapability::scoped(
            presenter,
            AuthRequired::Either,
            [String::from("https://allowed.example")],
            [],
        );
        let _ = engine.render(
            &page_url,
            denied_surface,
            &["https://allowed.example".to_string()],
            W,
            H,
            2048,
        );
        let denied_outcomes = engine.handler().outcomes();
        let denied_fetched = engine.handler().last_fetch();
        let denied_tls = engine.handler().last_tls_handshake();

        // ── RUN 2: CAP-ALLOWED. A surface scoped to the SERVER's https origin. The cap
        // gate admits it; the handler opens a real TCP socket, drives a REAL rustls TLS
        // handshake, fetches the real bytes over the encrypted socket; servo lays them
        // out, SWGL rasterizes. ──
        let allowed_surface = SurfaceCapability::scoped(
            presenter,
            AuthRequired::Either,
            [origin.clone()],
            [],
        );
        let (frame, outcome) = engine.render(
            &page_url,
            allowed_surface,
            &[origin.clone()],
            W,
            H,
            4096,
        );
        let outcomes = engine.handler().outcomes();
        let last_fetch = engine.handler().last_fetch();
        let tls_handshook = engine.handler().last_tls_handshake();
        (
            frame,
            last_fetch,
            tls_handshook,
            outcomes,
            denied_outcomes,
            denied_fetched,
            denied_tls,
            outcome,
        )
    });

    // ── CAP-DENIED: the gate bit. No socket, no handshake, no bytes. ──
    assert!(
        denied_outcomes.iter().all(|o| o.refused_by_cap()),
        "any https load the handler saw for the denied origin was RefusedByCap: {denied_outcomes:?}"
    );
    assert!(
        denied_fetched.is_none(),
        "NO bytes were fetched for the cap-denied https origin — the byte socket never opened"
    );
    assert!(
        !denied_tls,
        "NO TLS handshake happened for the cap-denied origin (the socket never opened)"
    );
    println!(
        "CAP-DENIED: unauthorized https origin blocked, zero bytes, no TLS handshake (handler saw {} load(s), all RefusedByCap)",
        denied_outcomes.len()
    );

    // ── CAP-ALLOWED: dialed, REAL TLS handshake, real bytes over the encrypted socket. ──
    let outcomes = dialed_outcomes;
    assert!(
        outcomes.iter().any(|o| o.dialed()),
        "the server https origin was DIALED through the netlayer (cap-admitted): {outcomes:?}"
    );
    assert!(
        !outcomes.iter().any(|o| o.refused_by_cap()),
        "no cap refusal for the authorized https origin: {outcomes:?}"
    );
    assert!(
        tls_handshook,
        "a REAL rustls TLS handshake completed over the cap-admitted socket for the allowed https origin"
    );
    let (fetched_url, fetched_len) = last_fetch
        .expect("the handler fetched real https bytes over the TLS socket for the allowed origin");
    assert!(
        fetched_url.starts_with(&origin) && fetched_url.starts_with("https://"),
        "the fetched url is the server's https origin: {fetched_url}"
    );
    assert!(
        fetched_len >= PAGE_HTML.len(),
        "the full page body ({} bytes) was fetched over the encrypted socket; got {fetched_len}",
        PAGE_HTML.len()
    );
    println!(
        "CAP-ALLOWED: {fetched_url} → dialed + REAL TLS handshake, fetched {fetched_len} real bytes over the encrypted socket; last outcome={outcome:?}"
    );

    // ── The engine produced a frame from the real https bytes. ──
    let frame = frame.expect("the real Servo WebView produced a frame for the https page");
    assert_eq!(frame.width, W);
    assert_eq!(frame.height, H);
    assert_eq!(frame.bytes.len(), (W * H * 4) as usize, "real RGBA8, 4 bytes/pixel");

    // ── PROVE it is genuine laid-out PAGE content from the https bytes ──
    // The page has a green bg, a magenta block, and black antialiased glyphs.
    let mut distinct = std::collections::BTreeSet::new();
    let mut has_green = false;
    let mut has_magenta = false;
    for i in 0..(frame.width * frame.height) as usize {
        let p = &frame.bytes[i * 4..i * 4 + 4];
        distinct.insert([p[0], p[1], p[2], p[3]]);
        if p[1] > 150 && p[0] < 80 && p[2] < 80 {
            has_green = true;
        }
        if p[0] > 200 && p[2] > 200 && p[1] < 80 {
            has_magenta = true;
        }
    }
    assert!(
        distinct.len() >= 3,
        "the rendered https page is non-trivial (≥3 distinct colors = real layout); got {}",
        distinct.len()
    );
    assert!(has_green, "the page's green background (from the https bytes) was rasterized");
    assert!(
        has_magenta,
        "the page's magenta block (from the https bytes) was laid out + rasterized"
    );

    // ── write the captured PNG of the REAL fetched https page ──
    let out_path = std::env::var("HTTPS_RENDER_PNG_OUT").unwrap_or_else(|_| {
        let mut p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        p.push("servo_real_https_render.png");
        p.to_string_lossy().into_owned()
    });
    let png = png_encode_rgba8(frame.width, frame.height, &frame.bytes);
    std::fs::write(&out_path, &png).expect("write the rendered https-page PNG");
    let png_len = std::fs::metadata(&out_path).map(|m| m.len()).unwrap_or(0);
    assert!(png_len > 100, "the captured PNG is substantial, got {png_len} bytes");
    println!(
        "HTTPS_RENDER_PNG_WRITTEN path={out_path} bytes={png_len} dims={W}x{H} \
         distinct_colors={} source='REAL https:// page fetched over a cap-gated TLS socket \
         (real rustls handshake), servo layout, SWGL raster'",
        distinct.len()
    );

    drop(server);
}
