//! A lightweight operational metrics surface, and the gated admin listener that
//! exposes it.
//!
//! This is untrusted-shell observability, exactly like `access_log`: the host
//! counts what it already has in hand at each response — the served response
//! bytes and (for a proxied request) the dialled backend — from the serve loop,
//! OUTSIDE the proven core. No counter feeds any request decision; the proven
//! core neither reads nor is affected by any of this. The counters are plain
//! atomics.
//!
//! ## What is counted
//!
//! * `drorb_requests_total` — every request served through the host loop;
//! * `drorb_responses_total{class=…}` — per status-class (2xx/3xx/4xx/5xx/other);
//! * `drorb_response_bytes_total` — total response bytes written;
//! * `drorb_active_connections` — connection threads currently in flight
//!   (`crate::ACTIVE_CONNS`);
//! * `drorb_backend_requests_total{backend=…}` — per-backend proxied counts;
//! * `drorb_config_generation` — the active config generation (`config`);
//! * `drorb_reloads_applied_total` / `drorb_reloads_rejected_total` — SIGHUP
//!   reconfig outcomes (`reconfig`);
//! * `drorb_draining` — 1 while a reconfig swap is in progress, else 0.
//!
//! ## The admin listener
//!
//! The counters here are rendered by [`render`] and served, alongside the
//! operational endpoints, by the gated admin listener in [`crate::admin`] (bound
//! only when `DRORB_ADMIN_LISTEN` is set, on a port SEPARATE from the serve
//! listeners). This module owns only the counting and the Prometheus rendering.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

static REQUESTS: AtomicU64 = AtomicU64::new(0);
static R2XX: AtomicU64 = AtomicU64::new(0);
static R3XX: AtomicU64 = AtomicU64::new(0);
static R4XX: AtomicU64 = AtomicU64::new(0);
static R5XX: AtomicU64 = AtomicU64::new(0);
static ROTHER: AtomicU64 = AtomicU64::new(0);
static BYTES_OUT: AtomicU64 = AtomicU64::new(0);

/// Per-backend proxied request counts, keyed by the dialled `host:port`.
static BACKENDS: Mutex<BTreeMap<String, u64>> = Mutex::new(BTreeMap::new());

/// Record one served request from the host serve loop: bump the total, the
/// status-class bucket, and the response-byte total, and — for a proxied
/// request — the dialled backend's count. Cheap and lock-free except the
/// per-backend map (touched only on a proxied request).
pub fn record(resp: &[u8], backend: Option<&str>) {
    REQUESTS.fetch_add(1, Ordering::Relaxed);
    BYTES_OUT.fetch_add(resp.len() as u64, Ordering::Relaxed);
    match status_class(resp) {
        Some(2) => &R2XX,
        Some(3) => &R3XX,
        Some(4) => &R4XX,
        Some(5) => &R5XX,
        _ => &ROTHER,
    }
    .fetch_add(1, Ordering::Relaxed);
    if let Some(b) = backend {
        if let Ok(mut map) = BACKENDS.lock() {
            *map.entry(b.to_string()).or_insert(0) += 1;
        }
    }
}

/// The leading digit of the HTTP status code in a response head
/// (`HTTP/1.1 SP CODE …`), or `None` if the head is not recognisable.
fn status_class(resp: &[u8]) -> Option<u8> {
    let head = resp.split(|&b| b == b'\r').next().unwrap_or(resp);
    let sp = head.iter().position(|&b| b == b' ')?;
    let after = &head[sp + 1..];
    let code: &[u8] = after.split(|&b| b == b' ').next().unwrap_or(after);
    if code.len() == 3 && code.iter().all(|b| b.is_ascii_digit()) {
        Some(code[0] - b'0')
    } else {
        None
    }
}

/// Render the counters in Prometheus text exposition format. Served by the admin
/// listener's `GET /metrics` route ([`crate::admin`]).
pub(crate) fn render() -> String {
    let mut out = String::with_capacity(1024);
    let total = REQUESTS.load(Ordering::Relaxed);
    out.push_str("# HELP drorb_requests_total Requests served through the host loop.\n");
    out.push_str("# TYPE drorb_requests_total counter\n");
    out.push_str(&format!("drorb_requests_total {total}\n"));

    out.push_str("# HELP drorb_responses_total Responses by status class.\n");
    out.push_str("# TYPE drorb_responses_total counter\n");
    for (class, cell) in [
        ("2xx", &R2XX),
        ("3xx", &R3XX),
        ("4xx", &R4XX),
        ("5xx", &R5XX),
        ("other", &ROTHER),
    ] {
        out.push_str(&format!(
            "drorb_responses_total{{class=\"{class}\"}} {}\n",
            cell.load(Ordering::Relaxed)
        ));
    }

    out.push_str("# HELP drorb_response_bytes_total Total response bytes written.\n");
    out.push_str("# TYPE drorb_response_bytes_total counter\n");
    out.push_str(&format!(
        "drorb_response_bytes_total {}\n",
        BYTES_OUT.load(Ordering::Relaxed)
    ));

    out.push_str("# HELP drorb_active_connections Connection handlers in flight.\n");
    out.push_str("# TYPE drorb_active_connections gauge\n");
    out.push_str(&format!(
        "drorb_active_connections {}\n",
        crate::ACTIVE_CONNS.load(Ordering::SeqCst)
    ));

    out.push_str("# HELP drorb_backend_requests_total Proxied requests per backend.\n");
    out.push_str("# TYPE drorb_backend_requests_total counter\n");
    if let Ok(map) = BACKENDS.lock() {
        for (backend, count) in map.iter() {
            out.push_str(&format!(
                "drorb_backend_requests_total{{backend=\"{backend}\"}} {count}\n"
            ));
        }
    }

    out.push_str("# HELP drorb_config_generation Active operator-config generation.\n");
    out.push_str("# TYPE drorb_config_generation gauge\n");
    out.push_str(&format!(
        "drorb_config_generation {}\n",
        crate::config::generation()
    ));

    out.push_str("# HELP drorb_reloads_applied_total SIGHUP reconfigs applied.\n");
    out.push_str("# TYPE drorb_reloads_applied_total counter\n");
    out.push_str(&format!(
        "drorb_reloads_applied_total {}\n",
        crate::reconfig::reloads_applied()
    ));

    out.push_str("# HELP drorb_reloads_rejected_total SIGHUP reconfigs rejected (fail-safe).\n");
    out.push_str("# TYPE drorb_reloads_rejected_total counter\n");
    out.push_str(&format!(
        "drorb_reloads_rejected_total {}\n",
        crate::reconfig::reloads_rejected()
    ));

    out.push_str("# HELP drorb_draining 1 while a reconfig swap is in progress or an operator drain is active.\n");
    out.push_str("# TYPE drorb_draining gauge\n");
    out.push_str(&format!(
        "drorb_draining {}\n",
        u8::from(crate::reconfig::draining())
    ));

    out
}
