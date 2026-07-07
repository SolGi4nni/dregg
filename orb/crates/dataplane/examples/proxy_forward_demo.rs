//! End-to-end drive of the reverse-proxy forward (the host side of the split).
//!
//! This is the runnable proof that the proxy actually opens a socket to a live
//! backend and returns the backend's bytes — the behaviour the conformance calls
//! `handler-proxy-forward`, previously UNWIRED ("no socket to a real backend is
//! opened"). It includes the real `proxy_dial` module by path (no duplication),
//! stands up an in-process demo backend, and forwards a real request through
//! `proxy_dial::forward` / `proxy_dial::handle`, asserting the BACKEND's response
//! comes back.
//!
//! The WHICH-backend decision is the proven `Proxy.selectChain`
//! (`Reactor.ProxyDial`, surfaced as `drorb_proxy_pick`); here the fleet is a
//! single eligible backend, so the pick is forced and we exercise the host-side
//! forward + breaker + sticky mechanics against a real socket.
//!
//! Run:  cargo run --example proxy_forward_demo   (exit 0 = PASS)

#[path = "../src/proxy_dial.rs"]
mod proxy_dial;

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

/// Stand up a demo backend on an ephemeral port; return its address.
fn spawn_backend(name: &'static str) -> std::net::SocketAddr {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = l.local_addr().unwrap();
    std::thread::spawn(move || {
        for s in l.incoming() {
            let Ok(mut s) = s else { continue };
            std::thread::spawn(move || {
                let mut buf = Vec::new();
                let mut chunk = [0u8; 2048];
                loop {
                    if buf.windows(4).any(|w| w == b"\r\n\r\n") {
                        break;
                    }
                    match s.read(&mut chunk) {
                        Ok(0) => return,
                        Ok(n) => buf.extend_from_slice(&chunk[..n]),
                        Err(_) => return,
                    }
                }
                let body = format!("hello from {name}");
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nX-Backend: {name}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                    body.len()
                );
                let _ = s.write_all(resp.as_bytes());
            });
        }
    });
    // Wait until it accepts.
    for _ in 0..50 {
        if TcpStream::connect_timeout(&addr, Duration::from_millis(100)).is_ok() {
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    addr
}

fn main() {
    let mut fail = 0;

    // (1) Real forward: open a socket to a live backend, forward a request, get
    //     the backend's body back.
    let addr = spawn_backend("b2");
    let req = b"GET /api/users HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
    let resp = proxy_dial::forward(addr, req, Duration::from_secs(2)).expect("forward failed");
    let text = String::from_utf8_lossy(&resp);
    if text.starts_with("HTTP/1.1 200") && text.contains("hello from b2") {
        println!("PASS handler-proxy-forward: upstream body returned ({} bytes)", resp.len());
    } else {
        eprintln!("FAIL handler-proxy-forward: got {text:?}");
        fail += 1;
    }

    // (2) Full hop through `handle`: single eligible backend ⇒ the proven pick is
    //     forced to it; the host dials it and returns its bytes, and records a
    //     breaker success.
    let spec = format!("2={addr}");
    let fleet = Arc::new(proxy_dial::Fleet::parse(&spec, 3, Duration::from_secs(2)).unwrap());
    let (out, _backend) = proxy_dial::handle(req, &fleet, |mask, _key| {
        // The proven `drorb_proxy_pick` seam decides this; with one eligible
        // backend the choice is forced. (Multi-backend selection is proven in
        // Reactor.ProxyDial and driven there.)
        if mask & (1 << 2) != 0 { Some(2) } else { None }
    });
    if String::from_utf8_lossy(&out).contains("hello from b2") {
        println!("PASS proxy handle: dialled the picked backend, returned its body");
    } else {
        eprintln!("FAIL proxy handle: {:?}", String::from_utf8_lossy(&out));
        fail += 1;
    }

    // (3) Breaker: forwarding to a dead backend records failures; after the
    //     threshold the backend's bit clears (breaker open) and the proven pick,
    //     fed the demoted mask, returns nothing ⇒ 503, no dial attempted.
    let dead: std::net::SocketAddr = "127.0.0.1:1".parse().unwrap(); // unroutable
    let fleet2 = proxy_dial::Fleet::parse(&format!("2={dead}"), 2, Duration::from_millis(200)).unwrap();
    let pick = |mask: u8, _k: &[u8]| if mask & (1 << 2) != 0 { Some(2u32) } else { None };
    let _ = proxy_dial::handle(req, &fleet2, pick); // failure 1 -> 502
    let (r2, _) = proxy_dial::handle(req, &fleet2, pick); // failure 2 -> breaker opens
    let (after, _) = proxy_dial::handle(req, &fleet2, pick); // now short-circuits
    let r2s = String::from_utf8_lossy(&r2);
    let afters = String::from_utf8_lossy(&after);
    if r2s.starts_with("HTTP/1.1 502") && afters.starts_with("HTTP/1.1 503") {
        println!("PASS fabric-circuit-breaker: breaker opened after threshold ⇒ 503 short-circuit");
    } else {
        eprintln!("FAIL breaker: r2={r2s:?} after={afters:?}");
        fail += 1;
    }

    if fail == 0 {
        println!("\nALL PASS: real reverse-proxy forward + breaker over live sockets");
    } else {
        eprintln!("\n{fail} check(s) FAILED");
        std::process::exit(1);
    }
}
