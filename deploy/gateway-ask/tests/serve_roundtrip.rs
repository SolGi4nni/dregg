//! End-to-end: bind a real ephemeral socket, serve the sidecar through the
//! hardened `http_serve` loop, and drive the on-demand-TLS `ask` + the health
//! probe + the capability gate over real HTTP — proving the wired serve path,
//! not just the handler in isolation.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

use dregg_gateway_ask::{GatewayState, handle};
use http_serve::limits::Limits;
use http_serve::serve_on;
use starbridge_domains::{ChallengeMethod, DomainBinding, DomainRegistry};

fn get(addr: std::net::SocketAddr, target: &str) -> String {
    let mut conn = TcpStream::connect(addr).expect("connect");
    conn.write_all(
        format!("GET {target} HTTP/1.1\r\nHost: gateway\r\nConnection: close\r\n\r\n").as_bytes(),
    )
    .unwrap();
    let mut resp = String::new();
    conn.read_to_string(&mut resp).unwrap();
    resp
}

#[test]
fn ask_and_health_over_a_real_socket() {
    let reg = DomainRegistry::new().with_apex("example.host");
    reg.adopt(DomainBinding::verified(
        "blog.acme.com",
        "acme-blog",
        "alice",
        ChallengeMethod::Txt,
        "nonce",
        1,
    ));
    let state = GatewayState::new(Arc::new(reg));

    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let addr = listener.local_addr().unwrap();
    std::thread::spawn(move || {
        let _ = serve_on(listener, move |req| handle(&state, req), Limits::default());
    });

    // The on-demand-TLS ask: a verified host is 200, an unknown host is 404.
    let ok = get(addr, "/internal/site-exists?domain=blog.acme.com");
    assert!(ok.starts_with("HTTP/1.1 200"), "verified ask: {ok}");
    let no = get(addr, "/internal/site-exists?domain=evil.example.com");
    assert!(no.starts_with("HTTP/1.1 404"), "unknown ask: {no}");

    // The health probe the deploy gate polls.
    let hz = get(addr, "/healthz");
    assert!(hz.starts_with("HTTP/1.1 200"), "healthz: {hz}");

    // The capability gate with no issuer configured is fail-closed (503).
    let auth = get(addr, "/auth?cap=ops-admin");
    assert!(auth.starts_with("HTTP/1.1 503"), "fail-closed auth: {auth}");
}
