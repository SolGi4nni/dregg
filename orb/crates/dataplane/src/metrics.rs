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
//! * `drorb_requests_refused_total{reason=…}` — requests refused at the reactor
//!   DoS gate, per reason: `conn_limit` (per-source concurrent-connection cap,
//!   the `503`), `rate_limit` (per-source request-rate window, the `429`), and
//!   `timeout` (header phase overran the slowloris deadline, the `408`), and
//!   `body_limit` (request body over the configured byte cap — declared
//!   `Content-Length` or streamed bytes — the `413`). These are the fire counts
//!   of the accept-path / body-read gates the proven reactor decides;
//! * `drorb_request_duration_microseconds` — a fixed-bucket latency histogram of
//!   request handling time, observed on-the-fly at each finalized response;
//! * `drorb_config_generation` — the active config generation (`config`);
//! * `drorb_reloads_applied_total` / `drorb_reloads_rejected_total` — SIGHUP
//!   reconfig outcomes (`reconfig`);
//! * `drorb_draining` — 1 while a reconfig swap is in progress, else 0.
//! * `drorb_upstream_conn_reused_total` / `drorb_upstream_conn_dialed_total` —
//!   upstream forwards served on a pooled keep-alive socket vs. opened fresh.
//!
//! ## Overhead
//!
//! Every counter is a single relaxed `fetch_add` on a process-static atomic;
//! the latency histogram is a `take_while` bucket scan over 12 fixed bounds plus
//! two relaxed `fetch_add`s. No allocation, no lock (the per-backend map aside,
//! touched only on a proxied request), no cross-thread coordination on the hot
//! path — the aggregation across threads happens lazily at render time.
//!
//! ## The admin listener
//!
//! The counters here are rendered by [`render`] and served, alongside the
//! operational endpoints, by the gated admin listener in [`crate::admin`] (bound
//! only when `DRORB_ADMIN_LISTEN` is set, on a port SEPARATE from the serve
//! listeners). This module owns only the counting and the Prometheus rendering.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

static REQUESTS: AtomicU64 = AtomicU64::new(0);
static R2XX: AtomicU64 = AtomicU64::new(0);
static R3XX: AtomicU64 = AtomicU64::new(0);
static R4XX: AtomicU64 = AtomicU64::new(0);
static R5XX: AtomicU64 = AtomicU64::new(0);
static ROTHER: AtomicU64 = AtomicU64::new(0);
static BYTES_OUT: AtomicU64 = AtomicU64::new(0);

/// Per-backend proxied request counts, keyed by the dialled `host:port`.
static BACKENDS: Mutex<BTreeMap<String, u64>> = Mutex::new(BTreeMap::new());

/// DoS-gate fire counters (lock-free). Each is incremented once at the reactor
/// accept gate when a source is refused: over its per-source connection cap
/// (`503`), over its per-source request-rate window (`429`), or timed out
/// mid-header (slowloris `408`). Both the io_uring and blocking reactors feed
/// them, so the surface is IO-path-independent.
static REFUSED_CONN_LIMIT: AtomicU64 = AtomicU64::new(0);
static REFUSED_RATE_LIMIT: AtomicU64 = AtomicU64::new(0);
static REQUEST_TIMEOUTS: AtomicU64 = AtomicU64::new(0);
static REFUSED_BODY_LIMIT: AtomicU64 = AtomicU64::new(0);

/// The latency-histogram upper bounds, in microseconds (the `le` thresholds).
/// There is one bucket per bound plus a final `+Inf` overflow bucket (13
/// buckets). An observed value `v` counts in the FIRST bucket whose bound is
/// `≥ v` — exactly the proven `Metrics.bucketIndex` rule (`bounds.takeWhile
/// (· < v) |>.length`).
const LATENCY_BOUNDS_US: [u64; 12] = [
    100, 250, 500, 1_000, 2_500, 5_000, 10_000, 25_000, 50_000, 100_000, 500_000, 1_000_000,
];

/// Per-bucket observation counts (lock-free). Index `i < 12` counts observations
/// `≤ LATENCY_BOUNDS_US[i]` and `>` the previous bound; index `12` is the `+Inf`
/// overflow bucket. The exposed `le` values are the running (cumulative) totals,
/// computed at render time.
static LATENCY_BUCKETS: [AtomicU64; 13] = [const { AtomicU64::new(0) }; 13];

/// Running sum of observed latencies, in microseconds (the histogram `_sum`).
static LATENCY_SUM_US: AtomicU64 = AtomicU64::new(0);

/// Requests served over the HTTPS front door, and the subset of those whose
/// connection negotiated the post-quantum hybrid key exchange.
///
/// These exist because the front door's traffic is otherwise indistinguishable
/// from the plaintext listener's in the totals above: `drorb_requests_total`
/// counts both. Splitting HTTPS out is what lets an operator see the TLS share of
/// traffic at all, and the PQ counter answers the question a gateway rolling out
/// post-quantum key exchange actually has — *what fraction of my real traffic
/// negotiated the hybrid group* — which cannot be observed from outside the
/// connection. Fed by the TLS observation seam (`tls::obs`).
static TLS_REQUESTS: AtomicU64 = AtomicU64::new(0);
static TLS_PQ_REQUESTS: AtomicU64 = AtomicU64::new(0);

/// HTTPS connections by negotiated ALPN protocol.
///
/// This exists to keep an honest accounting of a KNOWN gap. Per-request
/// observability on the TLS front door currently covers HTTP/1.1-over-TLS: an
/// h2-over-TLS connection is driven by the proven HTTP/2 engine, whose request
/// and response live inside HPACK-encoded frames that the host does not decode
/// (and should not — that is the proven engine's job), so its individual requests
/// do not appear in `drorb_tls_requests_total`.
///
/// Counting connections per ALPN means that gap is MEASURED rather than silent:
/// an operator can see exactly how much of their HTTPS traffic is on the path
/// whose requests are not itemised, instead of mistaking a partial request count
/// for the whole picture.
static TLS_CONNS: Mutex<BTreeMap<String, u64>> = Mutex::new(BTreeMap::new());

/// Record one served request from the host serve loop: bump the total, the
/// status-class bucket, and the response-byte total, and — for a proxied
/// request — the dialled backend's count. Cheap and lock-free except the
/// per-backend map (touched only on a proxied request).
pub fn record(resp: &[u8], backend: Option<&str>) {
    record_streamed(resp, resp.len() as u64, backend);
}

/// Count one request served over the HTTPS front door, and whether its
/// connection used the post-quantum hybrid key exchange. Called from the TLS
/// observation seam IN ADDITION to [`record`], so a TLS request appears in both
/// the overall totals and the HTTPS split.
/// Count one established HTTPS connection by its negotiated ALPN protocol
/// (`http/1.1`, `h2`, or `none` when the client offered no ALPN). See
/// [`TLS_CONNS`] for why this is tracked separately from the request counters.
pub fn note_tls_connection(alpn: &str) {
    let key = if alpn.is_empty() { "none" } else { alpn };
    if let Ok(mut m) = TLS_CONNS.lock() {
        *m.entry(key.to_string()).or_insert(0) += 1;
    }
}

pub fn note_tls_request(pq_hybrid: bool) {
    TLS_REQUESTS.fetch_add(1, Ordering::Relaxed);
    if pq_hybrid {
        TLS_PQ_REQUESTS.fetch_add(1, Ordering::Relaxed);
    }
}

/// Record one served request whose body was STREAMED to the client (so the whole
/// response bytes were never in hand): the status class is read from the response
/// `head`, and the byte total is the caller's exact streamed count. Otherwise
/// identical to [`record`].
pub fn record_streamed(head: &[u8], bytes: u64, backend: Option<&str>) {
    REQUESTS.fetch_add(1, Ordering::Relaxed);
    BYTES_OUT.fetch_add(bytes, Ordering::Relaxed);
    match status_class(head) {
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

/// Note one request refused at the per-source CONNECTION-limit gate (the `503`).
/// Lock-free; called once from the reactor accept path when a source is at or
/// over its `max-connections` cap.
pub fn note_conn_limit_refused() {
    REFUSED_CONN_LIMIT.fetch_add(1, Ordering::Relaxed);
}

/// Note one request refused at the per-source REQUEST-RATE gate (the `429`).
/// Lock-free; called once from the reactor accept path when a source is over its
/// `rate-limit` window.
pub fn note_rate_limit_refused() {
    REFUSED_RATE_LIMIT.fetch_add(1, Ordering::Relaxed);
}

/// Note one connection torn down for overrunning the header-read deadline
/// (slowloris `408`). Lock-free; called once from the reactor when the header
/// phase expires.
pub fn note_request_timeout() {
    REQUEST_TIMEOUTS.fetch_add(1, Ordering::Relaxed);
}

/// Note one request refused at the body-size gate (the `413`): a declared
/// `Content-Length` over the cap, or a chunked / streamed body whose ACTUAL
/// accumulated bytes passed the cap mid-stream. Lock-free; called once from the
/// reactor body-read path at each 413 fire, on every IO path.
pub fn note_body_limit_refused() {
    REFUSED_BODY_LIMIT.fetch_add(1, Ordering::Relaxed);
}

/// Observe one finalized request's handling latency into the fixed-bucket
/// histogram. Lock-free and allocation-free: selects the bucket by the same rule
/// as the proven `Metrics.bucketIndex` (the first bucket whose µs bound is `≥ us`),
/// bumps it by one, and adds the elapsed µs to the running sum.
pub fn observe_latency(elapsed: std::time::Duration) {
    let us = elapsed.as_micros().min(u64::MAX as u128) as u64;
    // First bucket whose upper bound is `≥ us`: count the bounds strictly below
    // `us` (the overflow index `12` when `us` exceeds every bound).
    let idx = LATENCY_BOUNDS_US.iter().take_while(|&&b| b < us).count();
    LATENCY_BUCKETS[idx].fetch_add(1, Ordering::Relaxed);
    LATENCY_SUM_US.fetch_add(us, Ordering::Relaxed);
}

/// Total requests served through the host loop (the `/admin/connections`
/// projection).
pub fn requests_total() -> u64 {
    REQUESTS.load(Ordering::Relaxed)
}

/// Total response bytes written (the `/admin/connections` projection).
pub fn bytes_out_total() -> u64 {
    BYTES_OUT.load(Ordering::Relaxed)
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

    out.push_str(
        "# HELP drorb_tls_requests_total Requests served over the HTTPS front door (subset of drorb_requests_total).\n",
    );
    out.push_str("# TYPE drorb_tls_requests_total counter\n");
    out.push_str(&format!(
        "drorb_tls_requests_total {}\n",
        TLS_REQUESTS.load(Ordering::Relaxed)
    ));
    out.push_str(
        "# HELP drorb_tls_pq_requests_total HTTPS requests whose connection negotiated the X25519MLKEM768 post-quantum hybrid key exchange.\n",
    );
    out.push_str("# TYPE drorb_tls_pq_requests_total counter\n");
    out.push_str(&format!(
        "drorb_tls_pq_requests_total {}\n",
        TLS_PQ_REQUESTS.load(Ordering::Relaxed)
    ));

    {
        let conns = TLS_CONNS.lock().map(|m| m.clone()).unwrap_or_default();
        if !conns.is_empty() {
            out.push_str(
                "# HELP drorb_tls_connections_total HTTPS connections by negotiated ALPN protocol. Requests on an h2 connection ARE now itemised (the proven H2 engine reports each via drorb_h2_obs_req).\n",
            );
            out.push_str("# TYPE drorb_tls_connections_total counter\n");
            for (alpn, n) in conns {
                out.push_str(&format!(
                    "drorb_tls_connections_total{{alpn=\"{alpn}\"}} {n}\n"
                ));
            }
        }
    }

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

    // The VALUE changed, the FAMILY did not: this is the sum of the per-source
    // standing counters — the connections this PROCESS holds right now, on whatever
    // backend and however many shards — where it used to be `crate::ACTIVE_CONNS`,
    // which only the blocking host increments and which therefore read a permanent
    // 0 on the reactor that ships. The HELP text and the family fleet are left
    // byte-identical because `Admin/MetricsFormat.lean` states them (`deployedRegistry`
    // / `baselineMetricsText`); the sample VALUE is a free variable there, so
    // correcting it does not move the exposition away from its Lean model.
    out.push_str("# HELP drorb_active_connections Connection handlers in flight.\n");
    out.push_str("# TYPE drorb_active_connections gauge\n");
    out.push_str(&format!(
        "drorb_active_connections {}\n",
        crate::standing::source_table().total_active()
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

    out.push_str(
        "# HELP drorb_requests_refused_total Requests refused at the reactor DoS gate, by reason.\n",
    );
    out.push_str("# TYPE drorb_requests_refused_total counter\n");
    out.push_str(&format!(
        "drorb_requests_refused_total{{reason=\"conn_limit\"}} {}\n",
        REFUSED_CONN_LIMIT.load(Ordering::Relaxed)
    ));
    out.push_str(&format!(
        "drorb_requests_refused_total{{reason=\"rate_limit\"}} {}\n",
        REFUSED_RATE_LIMIT.load(Ordering::Relaxed)
    ));
    out.push_str(&format!(
        "drorb_requests_refused_total{{reason=\"timeout\"}} {}\n",
        REQUEST_TIMEOUTS.load(Ordering::Relaxed)
    ));
    out.push_str(&format!(
        "drorb_requests_refused_total{{reason=\"body_limit\"}} {}\n",
        REFUSED_BODY_LIMIT.load(Ordering::Relaxed)
    ));

    out.push_str(
        "# HELP drorb_request_duration_microseconds Request handling latency in microseconds.\n",
    );
    out.push_str("# TYPE drorb_request_duration_microseconds histogram\n");
    let mut cumulative: u64 = 0;
    for (i, bound) in LATENCY_BOUNDS_US.iter().enumerate() {
        cumulative += LATENCY_BUCKETS[i].load(Ordering::Relaxed);
        out.push_str(&format!(
            "drorb_request_duration_microseconds_bucket{{le=\"{bound}\"}} {cumulative}\n"
        ));
    }
    cumulative += LATENCY_BUCKETS[12].load(Ordering::Relaxed);
    out.push_str(&format!(
        "drorb_request_duration_microseconds_bucket{{le=\"+Inf\"}} {cumulative}\n"
    ));
    out.push_str(&format!(
        "drorb_request_duration_microseconds_sum {}\n",
        LATENCY_SUM_US.load(Ordering::Relaxed)
    ));
    out.push_str(&format!(
        "drorb_request_duration_microseconds_count {cumulative}\n"
    ));

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

    if let Some((reused, dialed)) = crate::proxy_dial::pool_stats() {
        out.push_str(
            "# HELP drorb_upstream_conn_reused_total Upstream forwards served on a pooled keep-alive socket (dial skipped).\n",
        );
        out.push_str("# TYPE drorb_upstream_conn_reused_total counter\n");
        out.push_str(&format!("drorb_upstream_conn_reused_total {reused}\n"));

        out.push_str(
            "# HELP drorb_upstream_conn_dialed_total Upstream forwards that opened a fresh connection (pool miss or stale entry).\n",
        );
        out.push_str("# TYPE drorb_upstream_conn_dialed_total counter\n");
        out.push_str(&format!("drorb_upstream_conn_dialed_total {dialed}\n"));
    }

    out
}
