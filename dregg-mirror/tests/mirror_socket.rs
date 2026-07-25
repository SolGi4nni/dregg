//! # The real socket.
//!
//! `mirror_router.rs` drives `Mirror::handle` directly, which is the right place to bite
//! the logic — but it never proves the thing SERVES. This binds a real listener, speaks
//! real HTTP/1.1 at it over TCP, and reads the bytes back off the wire: the status line,
//! the content type, and the trust language, exactly as a browser arriving from a post
//! would receive them.
//!
//! std only — no client library, so what is under test is the response this crate actually
//! writes, not a client's interpretation of it.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};

use dregg_mirror::store::MemoryStore;
use dregg_mirror::uri::Kind;
use dregg_mirror::{fixtures, Mirror, MirrorConfig, PageConfig};
use http_serve::{limits::Limits, ServeRequest, WebRequest, WebResponse};

/// Bind an ephemeral port, serve the mirror on it, and return `(port, full_addr)`.
fn serve_one() -> (u16, String) {
    let mut store = MemoryStore::new();
    let addr = store.insert(
        Kind::Poll,
        fixtures::poll("Should the mirror ship?", &[("yes", 41), ("no", 3)], 30),
    );
    let mirror = Mirror::new(
        store,
        MirrorConfig {
            page: PageConfig {
                origin: "dregg.gg".into(),
                extension_url: "https://dregg.gg/extension".into(),
            },
            ..Default::default()
        },
    );

    let listener = TcpListener::bind("127.0.0.1:0").expect("bind an ephemeral port");
    let port = listener.local_addr().unwrap().port();
    std::thread::spawn(move || {
        let handler = move |req: &ServeRequest| -> WebResponse {
            mirror.handle(&WebRequest::new(req.method, &req.target, req.body.clone()))
        };
        let _ = http_serve::serve_on(listener, handler, Limits::default());
    });
    (port, addr)
}

/// One HTTP/1.1 request over TCP; returns the whole response as text.
fn request(port: u16, target: &str) -> String {
    let mut s = TcpStream::connect(("127.0.0.1", port)).expect("connect");
    write!(
        s,
        "GET {target} HTTP/1.1\r\nHost: dregg.gg\r\nConnection: close\r\n\r\n"
    )
    .expect("write request");
    s.flush().unwrap();
    let mut out = String::new();
    s.read_to_string(&mut out).expect("read response");
    out
}

#[test]
fn a_click_from_a_post_gets_a_real_page_over_a_real_socket() {
    let (port, addr) = serve_one();

    // The link as it survives a truncated post: the short prefix.
    let res = request(port, &format!("/poll/{}", &addr[..8]));

    assert!(res.starts_with("HTTP/1.1 200"), "status line: {:?}", &res[..40.min(res.len())]);
    assert!(res.to_ascii_lowercase().contains("content-type: text/html"));
    // The object rendered, by deos-view.
    assert!(res.contains("Should the mirror ship?"));
    assert!(res.contains(r#"<div class="deos-card">"#));
    // …under the tier it is actually entitled to, over the wire.
    assert!(res.contains(r#"data-trust="server""#));
    assert!(res.contains("✓ verified by dregg.gg (trust the origin)"));
    assert!(res.contains("dregg.gg checked this object. You did not."));
    // …with the way up on the page.
    assert!(res.contains(&format!("dregg://poll/b3_{addr}")));
    assert!(res.contains("https://dregg.gg/extension"));
}

#[test]
fn a_dead_reference_refuses_over_the_wire_and_renders_no_card() {
    let (port, _) = serve_one();
    let res = request(port, &format!("/poll/{}", "0".repeat(64)));
    assert!(res.starts_with("HTTP/1.1 404"), "status line: {:?}", &res[..40.min(res.len())]);
    assert!(res.contains("No object at that reference"));
    assert!(res.contains("⚠ unverified — original link shown"));
    assert!(!res.contains(r#"<div class="deos-card">"#));
}

#[test]
fn health_answers_on_the_socket() {
    let (port, _) = serve_one();
    let res = request(port, "/healthz");
    assert!(res.starts_with("HTTP/1.1 200"));
    assert!(res.trim_end().ends_with("ok"));
}
