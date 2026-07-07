//! The gated operator admin listener: observability plus the operational
//! endpoints that steer the running host without a signal.
//!
//! Bound only when `DRORB_ADMIN_LISTEN` is set (a bare PORT binds 127.0.0.1), on
//! a port SEPARATE from the serve listeners. It is intentionally minimal and
//! synchronous (one connection at a time): an operator sidecar, not a traffic
//! path. Nothing here is in the proven core — it reads state the host already
//! holds (the counters, the active config projections, the proxy fleet health)
//! and drives the two already-proven levers (config reload, graceful drain).
//!
//! ## Routes
//!
//! * `GET  /metrics`       — the counters, Prometheus text exposition format
//!                           (`crate::metrics::render`);
//! * `GET  /healthz`       — `200 ok` while serving; `503 draining` once shutdown
//!                           has begun OR an operator drain is in progress;
//! * `GET  /admin/config`  — the active config generation, LB policy, route count,
//!                           and declared reverse-proxy vhosts (JSON);
//! * `GET  /admin/backends` — the proxy fleet's per-backend health: address,
//!                           up/down, in-flight, breaker state (JSON);
//! * `POST /admin/drain`   — begin a standing graceful drain
//!                           (`crate::reconfig::begin_drain`); `/healthz` flips to
//!                           503, in-flight requests finish. Idempotent;
//! * `POST /admin/reload`  — re-read + re-parse `DRORB_CONFIG` and atomically swap
//!                           it in, the same proven path as SIGHUP
//!                           (`crate::reconfig::reload_now`); returns the outcome
//!                           and the new generation (JSON).
//!
//! Everything else is `404`; a wrong method on a known path is `405`.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::atomic::Ordering;
use std::time::Duration;

use crate::config::ReloadOutcome;
use crate::serve::ServeGateway;

/// Whether the host is currently serving (used by `/healthz`): false once
/// shutdown has begun or an operator has begun a graceful drain.
fn serving() -> bool {
    !crate::SHUTDOWN.load(Ordering::SeqCst) && !crate::reconfig::drain_begun()
}

/// Run the admin listener accept loop. Answers each route synchronously (one
/// connection at a time — this is an operator sidecar). The `gw` lets the reload
/// route cross the proven parser on the runtime-owner thread. Returns when
/// shutdown begins.
pub fn run_admin(listener: TcpListener, gw: ServeGateway) {
    listener
        .set_nonblocking(true)
        .expect("failed to set the admin listener non-blocking");
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return;
        }
        match listener.accept() {
            Ok((stream, _peer)) => {
                let _ = handle_admin(stream, &gw);
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(_) => std::thread::sleep(Duration::from_millis(50)),
        }
    }
}

/// Handle one admin connection: read the request head, route on the method+path,
/// write the response, close.
fn handle_admin(mut stream: TcpStream, gw: &ServeGateway) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(5)))?;
    stream.set_nodelay(true).ok();

    // Read until the end of the request head (blank line) or a small cap.
    let mut buf = Vec::with_capacity(1024);
    let mut chunk = [0u8; 1024];
    loop {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&chunk[..n]);
        if buf.windows(4).any(|w| w == b"\r\n\r\n") || buf.len() > 16 << 10 {
            break;
        }
    }

    let head = buf.split(|&b| b == b'\r').next().unwrap_or(&buf);
    let mut parts = head.split(|&b| b == b' ');
    let method = parts.next().unwrap_or(&[]);
    let path = parts.next().unwrap_or(&[]);
    // Ignore a query string on the path.
    let path = path.split(|&b| b == b'?').next().unwrap_or(path);

    let resp: Vec<u8> = match (method, path) {
        (b"GET", b"/metrics") => http_response(
            200,
            "text/plain; version=0.0.4; charset=utf-8",
            crate::metrics::render().as_bytes(),
        ),
        (b"GET", b"/healthz") => {
            if serving() {
                http_response(200, "text/plain; charset=utf-8", b"ok\n")
            } else {
                http_response(503, "text/plain; charset=utf-8", b"draining\n")
            }
        }
        (b"GET", b"/admin/config") => json_response(200, &config_json()),
        (b"GET", b"/admin/backends") => json_response(200, &backends_json()),
        (b"POST", b"/admin/drain") => {
            let started = crate::reconfig::begin_drain();
            // Idempotent: 200 either way — `started` reports whether THIS call began it.
            json_response(
                200,
                &format!(
                    "{{\"status\":\"draining\",\"started_by_this_call\":{},\"healthz\":503}}\n",
                    started
                ),
            )
        }
        (b"POST", b"/admin/reload") => {
            let (status, body) = reload_json(gw);
            json_response(status, &body)
        }
        // A known path with the wrong method: 405. Otherwise 404.
        (_, p) if is_known_path(p) => {
            http_response(405, "text/plain; charset=utf-8", b"method not allowed\n")
        }
        _ => http_response(404, "text/plain; charset=utf-8", b"not found\n"),
    };

    stream.write_all(&resp)?;
    Ok(())
}

/// Is `path` one of the routes we serve (used to distinguish 404 from 405)?
fn is_known_path(path: &[u8]) -> bool {
    matches!(
        path,
        b"/metrics"
            | b"/healthz"
            | b"/admin/config"
            | b"/admin/backends"
            | b"/admin/drain"
            | b"/admin/reload"
    )
}

/// `GET /admin/config`: the active config generation, LB policy, declared route
/// count, and reverse-proxy vhost hostnames. When no `DRORB_CONFIG` is in force
/// (the byte-identical default path) `active` is false and the projections are
/// their defaults.
fn config_json() -> String {
    let generation = crate::config::generation();
    match crate::config::get() {
        Some(dep) => {
            let vhosts = json_str_array(dep.vproxy_hosts.iter().map(String::as_str));
            format!(
                "{{\"active\":true,\"generation\":{},\"lb_policy\":{},\"routes\":{},\"vhosts\":{}}}\n",
                generation, dep.lb_policy, dep.route_count, vhosts
            )
        }
        None => format!(
            "{{\"active\":false,\"generation\":{},\"lb_policy\":null,\"routes\":0,\"vhosts\":[]}}\n",
            generation
        ),
    }
}

/// `GET /admin/backends`: the proxy fleet's per-backend health. When no fleet is
/// configured (`DRORB_PROXY_BACKENDS` unset), `configured` is false and the list
/// is empty.
fn backends_json() -> String {
    match crate::proxy_hook::fleet() {
        Some(fleet) => {
            let items: Vec<String> = fleet
                .snapshot()
                .into_iter()
                .map(|b| {
                    format!(
                        "{{\"id\":{},\"address\":{},\"up\":{},\"inflight\":{},\"breaker_open\":{},\"breaker_failures\":{}}}",
                        b.id,
                        json_str(&b.addr.to_string()),
                        b.up,
                        b.inflight,
                        b.breaker_open,
                        b.breaker_failures
                    )
                })
                .collect();
            format!(
                "{{\"configured\":true,\"backends\":[{}]}}\n",
                items.join(",")
            )
        }
        None => "{\"configured\":false,\"backends\":[]}\n".to_string(),
    }
}

/// `POST /admin/reload`: run the proven reload (same path as SIGHUP) and report
/// the outcome plus the resulting generation. Returns the HTTP status to use
/// alongside the JSON body.
fn reload_json(gw: &ServeGateway) -> (u16, String) {
    match crate::reconfig::reload_now(gw, "admin") {
        ReloadOutcome::Applied { generation } => (
            200,
            format!(
                "{{\"status\":\"applied\",\"generation\":{}}}\n",
                generation
            ),
        ),
        ReloadOutcome::KeptOld { reason } => (
            // The running config is kept (fail-safe); the request itself is
            // well-formed, so report 200 with the rejection and current generation.
            200,
            format!(
                "{{\"status\":\"rejected\",\"reason\":{},\"generation\":{}}}\n",
                json_str(&reason),
                crate::config::generation()
            ),
        ),
        ReloadOutcome::NoConfig => (
            200,
            format!(
                "{{\"status\":\"no_config\",\"generation\":{}}}\n",
                crate::config::generation()
            ),
        ),
    }
}

/// A JSON string literal (quoted, minimally escaped) for `s`.
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A JSON array of string literals.
fn json_str_array<'a>(items: impl Iterator<Item = &'a str>) -> String {
    let mut out = String::from("[");
    let mut first = true;
    for it in items {
        if !first {
            out.push(',');
        }
        first = false;
        out.push_str(&json_str(it));
    }
    out.push(']');
    out
}

/// A `200`/`4xx`/`5xx` JSON response.
fn json_response(status: u16, body: &str) -> Vec<u8> {
    http_response(status, "application/json; charset=utf-8", body.as_bytes())
}

/// Assemble a self-delimited HTTP/1.1 response with `Connection: close`.
fn http_response(status: u16, content_type: &str, body: &[u8]) -> Vec<u8> {
    let reason = match status {
        200 => "OK",
        404 => "Not Found",
        405 => "Method Not Allowed",
        503 => "Service Unavailable",
        _ => "OK",
    };
    let mut out = Vec::with_capacity(body.len() + 128);
    out.extend_from_slice(
        format!(
            "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        )
        .as_bytes(),
    );
    out.extend_from_slice(body);
    out
}
