//! A minimal real HTTP/1.1 backend for the reverse-proxy conformance.
//!
//! This is the LIVE upstream the proxy forwards to — the "real backend socket"
//! whose absence made the proxy scenarios UNWIRED. It is deliberately tiny: it
//! accepts TCP connections, reads a request, and replies 200 with a body that
//! names this backend and echoes the request target, so a driver can prove
//! (a) traffic actually reached a backend and (b) WHICH backend served it (for
//! load-balance / sticky-affinity checks).
//!
//! Usage:  proxy_backend <BIND> <NAME>
//!   e.g.  proxy_backend 127.0.0.1:9402 b2
//!
//! It stamps `X-Backend: <NAME>` and returns `backend <NAME> served <target>`.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};

fn handle(mut s: TcpStream, name: &str) {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 4096];
    // Read up to the end of the request head (enough for a GET; bodies ignored).
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
    // Recover the request target for the echo.
    let target = buf
        .windows(2)
        .position(|w| w == b"\r\n")
        .map(|e| &buf[..e])
        .and_then(|line| line.splitn(3, |&c| c == b' ').nth(1))
        .and_then(|t| std::str::from_utf8(t).ok())
        .unwrap_or("?")
        .to_string();

    let body = format!("backend {name} served {target}");
    let resp = format!(
        "HTTP/1.1 200 OK\r\nX-Backend: {name}\r\nContent-Type: text/plain\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    let _ = s.write_all(resp.as_bytes());
    let _ = s.flush();
}

fn main() {
    let mut args = std::env::args().skip(1);
    let bind = args.next().unwrap_or_else(|| "127.0.0.1:9402".to_string());
    let name = args.next().unwrap_or_else(|| "backend".to_string());
    let listener = TcpListener::bind(&bind).unwrap_or_else(|e| {
        eprintln!("proxy_backend: bind {bind} failed: {e}");
        std::process::exit(1);
    });
    eprintln!("proxy_backend {name} listening on {bind}");
    for stream in listener.incoming() {
        match stream {
            Ok(s) => {
                let name = name.clone();
                std::thread::spawn(move || handle(s, &name));
            }
            Err(_) => continue,
        }
    }
}
