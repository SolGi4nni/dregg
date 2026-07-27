//! Opt-in OpenTelemetry span emission for the plaintext HTTP/1.1 serve path (ob.5).
//!
//! Controlled by the `DRORB_OTEL` environment variable:
//!   * unset / empty / `0`  — disabled (the default);
//!   * `1` or `stderr`      — one OTLP/JSON span object per served request to stderr;
//!   * `stdout`             — the same, to stdout;
//!   * any other value      — treated as a file path, opened for append.
//!
//! Regardless of the sink, the last [`RING_CAP`] emitted spans are retained in a
//! bounded in-memory ring buffer ([`recent_spans`]) so a span is real and
//! inspectable even with no collector attached.
//!
//! This is untrusted-shell observability emitted from the host serve loop, exactly
//! like [`crate::access_log`] and [`crate::metrics`]. It never touches the proven
//! core or its decision: the host reads only the request line, the response status
//! it already has in hand, and the wall-clock it measured, then renders a span.
//!
//! ## Format — proven span model, mirrored here byte-for-byte
//!
//! The OTLP/JSON span-object shape is the one proven in `O11y/OtelExport.lean`
//! (`O11y.OtelExport.spanJsonAttrs` / `exportResourceSpans`): the 128-bit trace id
//! and 64-bit span id render to lowercase hex of the mandated widths (32 / 16
//! chars — `hexOf_len`, injective by `hexOf_inj`), and the export envelope is the
//! OTLP `resourceSpans` structure a collector ingests. Each request span carries
//! `http.request.method`, `url.path`, `http.response.status_code` and `duration_us`
//! as OTLP key/value attributes.
//!
//! ## Trace / span identity
//!
//! Each request gets a fresh 128-bit trace id and 64-bit span id derived from a
//! per-process seed (mixed once at startup) and a monotonic per-request counter run
//! through `splitmix64`. Both ids are forced non-zero (the W3C trace-context and the
//! proven `Span.Wf` both reject an all-zero id). This is adequate for a real,
//! inspectable local span buffer; a production deployment feeding a collector across
//! a trust boundary would seed from a CSPRNG (residual — see the module notes).
//!
//! ## Reaching a collector
//!
//! Spans go to three places, independently configurable: the local sink above,
//! the in-memory ring, and — when `DRORB_OTLP_ENDPOINT` (or the standard
//! `OTEL_EXPORTER_OTLP_ENDPOINT`) names a collector — a real OTLP/HTTP push,
//! batched on a background thread with a bounded queue and retry. See the push
//! section below for why the body is JSON rather than protobuf.
//!
//! ## Scoped residuals
//!
//! * **OTLP/protobuf** is not implemented; the push sends `application/json`,
//!   which the OTLP specification defines and collectors accept. The reasoning is
//!   at the push implementation.
//! * **The push is plain HTTP** to the collector, i.e. it assumes a local or
//!   trusted-network collector (the sidecar deployment). Pushing telemetry over
//!   TLS to a remote collector is not implemented.
//! * **Trace ids are not CSPRNG-seeded** (see below) — adequate for a local span
//!   buffer and a trusted collector, not for a trust boundary.

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::net::{IpAddr, TcpStream};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use crate::access_log::ReqLine;

/// Where emitted span objects go.
enum Sink {
    Stderr,
    Stdout,
    File(Mutex<std::fs::File>),
}

static SINK: OnceLock<Option<Sink>> = OnceLock::new();

/// Resolve (once) the configured sink from `DRORB_OTEL`.
fn sink() -> Option<&'static Sink> {
    SINK.get_or_init(|| {
        let v = std::env::var("DRORB_OTEL").ok()?;
        match v.as_str() {
            "" | "0" => None,
            "1" | "stderr" => Some(Sink::Stderr),
            "stdout" => Some(Sink::Stdout),
            path => match OpenOptions::new().create(true).append(true).open(path) {
                Ok(f) => Some(Sink::File(Mutex::new(f))),
                Err(e) => {
                    eprintln!(
                        "dataplane: DRORB_OTEL={path}: cannot open ({e}); OTel span export disabled"
                    );
                    None
                }
            },
        }
    })
    .as_ref()
}

/// Is OTel span emission enabled — either a local sink or a collector to push
/// to? Cheap after the first call (the env is read once).
pub fn enabled() -> bool {
    sink().is_some() || push_enabled()
}

/// The `service.name` resource attribute (env `DRORB_OTEL_SERVICE`, default
/// `drorb-dataplane`), resolved once.
fn service_name() -> &'static str {
    static SVC: OnceLock<String> = OnceLock::new();
    SVC.get_or_init(|| {
        std::env::var("DRORB_OTEL_SERVICE").unwrap_or_else(|_| "drorb-dataplane".to_string())
    })
}

// --- trace / span identity ------------------------------------------------- //

/// Per-process 64-bit seed, mixed once from the boot wall-clock and the pid so two
/// processes on the same box do not share a trace-id stream.
fn seed() -> u64 {
    static SEED: OnceLock<u64> = OnceLock::new();
    *SEED.get_or_init(|| {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        let pid = std::process::id() as u64;
        splitmix64(nanos ^ (pid.wrapping_mul(0x9E37_79B9_7F4A_7C15)))
    })
}

/// A monotonic per-request counter driving the id derivation.
static SPAN_COUNTER: AtomicU64 = AtomicU64::new(0);

/// SplitMix64 finalizer — a fast, well-distributed 64-bit mixing function.
fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Force a 64-bit id non-zero (an all-zero id is rejected by W3C trace-context and
/// by the proven `Span.Wf`).
fn nz(x: u64) -> u64 {
    if x == 0 { 1 } else { x }
}

/// A freshly minted `(trace_id_128, span_id_64)` for one request. The trace id is
/// the two mixed halves; the span id is a third independent mix. All parts non-zero.
fn fresh_ids() -> (u128, u64) {
    let n = SPAN_COUNTER.fetch_add(1, Ordering::Relaxed);
    let s = seed();
    let hi = nz(splitmix64(s ^ n));
    let lo = nz(splitmix64(s ^ n ^ 0xD1B5_4A32_D192_ED03));
    let span = nz(splitmix64(s ^ (n.rotate_left(17)) ^ 0xA0761_D6478_BD642F));
    (((hi as u128) << 64) | (lo as u128), span)
}

// --- the ring buffer ------------------------------------------------------- //

/// How many recent span objects the in-memory buffer retains.
pub const RING_CAP: usize = 1024;

static RING: Mutex<std::collections::VecDeque<String>> =
    Mutex::new(std::collections::VecDeque::new());

/// Push one rendered span object into the bounded ring, dropping the oldest when full.
fn ring_push(span: String) {
    if let Ok(mut q) = RING.lock() {
        if q.len() == RING_CAP {
            q.pop_front();
        }
        q.push_back(span);
    }
}

/// A snapshot of the recent span objects (oldest first). Real and inspectable with
/// no collector attached — used by the my-hand verify and any admin surface.
pub fn recent_spans() -> Vec<String> {
    RING.lock()
        .map(|q| q.iter().cloned().collect())
        .unwrap_or_default()
}

/// The full OTLP `resourceSpans` JSON envelope over the current ring contents — the
/// exact body an OTLP/JSON collector ingests. Mirrors `O11y.OtelExport.exportResourceSpans`.
pub fn export_resource_spans() -> String {
    export_envelope(&recent_spans())
}

// --- rendering ------------------------------------------------------------- //

/// Escape a string for a JSON string literal (double-quote, backslash, control chars).
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
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
    out
}

/// One OTLP/JSON key/value attribute with a string value.
fn attr(key: &str, val: &str) -> String {
    format!(
        "{{\"key\":\"{}\",\"value\":{{\"stringValue\":\"{}\"}}}}",
        key,
        json_escape(val)
    )
}

/// The 3-digit status code from an HTTP response head (`HTTP/1.1 SP CODE ...`), or
/// `-` if the head is not recognisable. Same rule as `access_log::status_of`.
fn status_of(resp: &[u8]) -> &str {
    let head = resp.split(|&b| b == b'\r').next().unwrap_or(resp);
    if let Some(sp) = head.iter().position(|&b| b == b' ') {
        let after = &head[sp + 1..];
        let code: &[u8] = after.split(|&b| b == b' ').next().unwrap_or(after);
        if code.len() == 3 && code.iter().all(|b| b.is_ascii_digit()) {
            return std::str::from_utf8(code).unwrap_or("-");
        }
    }
    "-"
}

/// Render one request span to its OTLP/JSON span object (the shape proven in
/// `O11y.OtelExport.spanJsonAttrs`). `extra` carries already-rendered attribute
/// objects appended after the four every request has — the TLS connection
/// attributes for an HTTPS request, empty for a plaintext one.
fn render_span_with(
    trace: u128,
    span: u64,
    req: &ReqLine,
    status: &str,
    dur_us: u128,
    extra: &[String],
) -> String {
    let name = format!("{} {}", req.method, req.path);
    let mut all = vec![
        attr("http.request.method", &req.method),
        attr("url.path", &req.path),
        attr("http.response.status_code", status),
        attr("duration_us", &dur_us.to_string()),
    ];
    all.extend_from_slice(extra);
    let attrs = all.join(",");
    format!(
        "{{\"traceId\":\"{:032x}\",\"spanId\":\"{:016x}\",\"parentSpanId\":\"{:016x}\",\"name\":\"{}\",\"attributes\":[{}]}}",
        trace,
        span,
        0u64, // request root span: parent is the all-zero id
        json_escape(&name),
        attrs
    )
}

/// Render one plaintext request span — the four universal attributes, no extras.
fn render_span(trace: u128, span: u64, req: &ReqLine, status: &str, dur_us: u128) -> String {
    render_span_with(trace, span, req, status, dur_us, &[])
}

/// The OTLP `resourceSpans` envelope wrapping a set of already-rendered span objects.
fn export_envelope(spans: &[String]) -> String {
    format!(
        "{{\"resourceSpans\":[{{\"resource\":{{\"attributes\":[{}]}},\"scopeSpans\":[{{\"scope\":{{\"name\":\"drorb.dataplane\",\"version\":\"otel-1.0\"}},\"spans\":[{}]}}]}}]}}",
        attr("service.name", service_name()),
        spans.join(",")
    )
}

// --- the per-request emit hook --------------------------------------------- //

/// Emit one OTel span for a served request. No-op when disabled. `backend` is the
/// dialled upstream for a proxied request, else `None`. Mirrors `access_log::log`.
pub fn record_span(
    client: IpAddr,
    req: &ReqLine,
    resp: &[u8],
    backend: Option<&str>,
    start: Instant,
) {
    record_span_streamed(client, req, resp, resp.len() as u64, backend, start);
}

/// Emit one OTel span for a request whose body was STREAMED to the client (status
/// read from the response `head`; `bytes` is the exact streamed total). Otherwise
/// identical to [`record_span`]. Mirrors `access_log::log_streamed`.
pub fn record_span_streamed(
    _client: IpAddr,
    req: &ReqLine,
    head: &[u8],
    _bytes: u64,
    _backend: Option<&str>,
    start: Instant,
) {
    // Skip the id draw + render entirely when there is nowhere for the span to
    // go — neither a local sink nor a collector.
    if sink().is_none() && !push_enabled() {
        return;
    }
    let dur_us = start.elapsed().as_micros();
    let (trace, span) = fresh_ids();
    emit(render_span(trace, span, req, status_of(head), dur_us));
}

/// Emit one OTel span for a request served over the HTTPS front door.
///
/// Identical to [`record_span`] except that the span also carries the TLS
/// connection attributes, under the OpenTelemetry semantic-convention names an
/// off-the-shelf collector already understands (`tls.*`, `server.address`), plus
/// `tls.pq_hybrid` — which has no standard name because negotiating a
/// post-quantum group is not yet a convention, and which is exactly the fact a
/// gateway rolling out PQ needs per request.
///
/// The values come from the verified connection through `tls::obs`; nothing here
/// re-parses TLS. Absent facts (no SNI, no ALPN) are omitted from the span rather
/// than emitted empty, so a collector sees no attribute instead of a false one.
pub fn record_span_tls(
    client: IpAddr,
    req: &ReqLine,
    resp: &[u8],
    start: Instant,
    info: &crate::tls::obs::TlsInfo,
) {
    record_span_tls_status(client, req, status_of(resp), start, info);
}

/// As [`record_span_tls`], but for an h2-over-TLS request the proven HTTP/2
/// engine reported structurally (`drorb_h2_obs_req`): the `:status` arrives as
/// a decimal string rather than parsed from a response head. Same TLS
/// attributes, same sink, so h1 and h2 spans are indistinguishable downstream.
pub fn record_span_tls_status(
    _client: IpAddr,
    req: &ReqLine,
    status: &str,
    start: Instant,
    info: &crate::tls::obs::TlsInfo,
) {
    if sink().is_none() && !push_enabled() {
        return;
    }
    let dur_us = start.elapsed().as_micros();
    let (trace, span) = fresh_ids();
    let mut extra = vec![
        attr("tls.protocol.name", "tls"),
        attr("tls.protocol.version", "1.3"),
        attr("tls.cipher", &info.suite_name()),
        attr("tls.group", &info.group_name()),
        attr("tls.pq_hybrid", &info.pq_hybrid().to_string()),
        attr("network.protocol.name", "https"),
    ];
    if !info.sni.is_empty() {
        extra.push(attr("tls.server.name", &info.sni));
        extra.push(attr("server.address", &info.sni));
    }
    if !info.alpn.is_empty() {
        extra.push(attr("network.protocol.alpn", &info.alpn));
    }
    let obj = render_span_with(trace, span, req, status, dur_us, &extra);
    emit(obj);
}

/// Retain a rendered span in the ring, write it to the configured sink, and hand
/// it to the OTLP push queue. The single path every emitted span takes.
fn emit(obj: String) {
    ring_push(obj.clone());
    push_enqueue(&obj);
    let Some(sink) = sink() else {
        return;
    };
    let line = {
        let mut l = obj;
        l.push('\n');
        l
    };
    match sink {
        Sink::Stderr => {
            let _ = std::io::stderr().write_all(line.as_bytes());
        }
        Sink::Stdout => {
            let _ = std::io::stdout().write_all(line.as_bytes());
        }
        Sink::File(m) => {
            if let Ok(mut f) = m.lock() {
                let _ = f.write_all(line.as_bytes());
            }
        }
    }
}

// --- OTLP/HTTP push --------------------------------------------------------- //
//
// Spans used to reach a collector only by someone tailing the sink file, which
// makes the gateway's traces a local artifact rather than telemetry. This is the
// push side: the same OTLP/JSON body, batched and POSTed to a real collector.
//
// ## JSON, not protobuf — and why that is the right call here
//
// The OTLP specification defines both `application/json` and
// `application/x-protobuf` over HTTP, and collectors accept either. Protobuf
// would mean either a code-generation dependency or a hand-written wire encoder
// in the host — new unverified surface, in a process whose entire argument is
// that its parsing lives in proven code. JSON reuses the body this module ALREADY
// renders (the shape mirrored from the proven `O11y.OtelExport` model), so the
// exporter adds a transport and no new encoding. The cost is bytes on the wire to
// the collector, which is a hop inside the operator's own network. If protobuf is
// later required for volume, it is a swap of the encoder behind this same queue.
//
// ## The HTTP client is deliberately minimal
//
// A blocking `POST` written directly on `TcpStream`: one request per flush, no
// keep-alive, no TLS to the collector. That is honest about what it is — the
// collector is expected to be local or on a trusted network, which is the usual
// sidecar deployment. Pushing telemetry over TLS to a remote collector would want
// this to go through the verified client path instead; it is NOT implemented here
// and is the named residual.

/// The push queue: spans rendered since the last flush.
static PUSH_Q: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// How many spans may sit unflushed before the oldest are dropped. A collector
/// that is down must cost bounded memory, never the serving process.
const PUSH_Q_CAP: usize = 4096;

/// The configured OTLP/HTTP traces endpoint, resolved once from
/// `DRORB_OTLP_ENDPOINT` (e.g. `http://127.0.0.1:4318/v1/traces`). The standard
/// `OTEL_EXPORTER_OTLP_ENDPOINT` is honoured as a fallback, with `/v1/traces`
/// appended when it names only the collector root, per the OTLP specification.
fn push_endpoint() -> Option<&'static (String, u16, String)> {
    static EP: OnceLock<Option<(String, u16, String)>> = OnceLock::new();
    EP.get_or_init(|| {
        let raw = std::env::var("DRORB_OTLP_ENDPOINT")
            .ok()
            .or_else(|| {
                std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
                    .ok()
                    .map(|b| {
                        if b.contains("/v1/") {
                            b
                        } else {
                            format!("{}/v1/traces", b.trim_end_matches('/'))
                        }
                    })
            })?;
        match parse_http_url(&raw) {
            Some(t) => Some(t),
            None => {
                eprintln!(
                    "dataplane: DRORB_OTLP_ENDPOINT={raw}: not a usable http:// URL; OTLP push disabled"
                );
                None
            }
        }
    })
    .as_ref()
}

/// Split an `http://host:port/path` URL into its parts. Only plain `http` is
/// accepted — see the residual note above on why TLS to the collector is out of
/// scope here rather than silently downgraded.
fn parse_http_url(raw: &str) -> Option<(String, u16, String)> {
    let rest = raw.strip_prefix("http://")?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    if authority.is_empty() {
        return None;
    }
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (h.to_string(), p.parse().ok()?),
        None => (authority.to_string(), 80u16),
    };
    if host.is_empty() {
        return None;
    }
    Some((host, port, path.to_string()))
}

/// Is OTLP push configured?
pub fn push_enabled() -> bool {
    push_endpoint().is_some()
}

/// Queue one rendered span for the next flush. Drops the OLDEST spans when the
/// queue is at capacity: with a collector down, recent traces are the useful
/// ones, and the serving path must never block on telemetry.
fn push_enqueue(obj: &str) {
    if !push_enabled() {
        return;
    }
    ensure_pusher();
    let mut q = PUSH_Q.lock().unwrap_or_else(|e| e.into_inner());
    if q.len() >= PUSH_Q_CAP {
        let overflow = q.len() + 1 - PUSH_Q_CAP;
        q.drain(..overflow);
    }
    q.push(obj.to_string());
}

/// POST one OTLP/JSON body to the collector. Returns the status line on success.
fn push_post(spans: &[String]) -> Result<String, String> {
    let (host, port, path) = push_endpoint().ok_or("no endpoint")?;
    let body = export_envelope(spans);
    let mut stream = TcpStream::connect((host.as_str(), *port))
        .map_err(|e| format!("connect {host}:{port}: {e}"))?;
    stream
        .set_write_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    let req = format!(
        "POST {path} HTTP/1.1\r\nHost: {host}:{port}\r\nContent-Type: application/json\r\n\
         Content-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream
        .write_all(req.as_bytes())
        .and_then(|_| stream.write_all(body.as_bytes()))
        .map_err(|e| format!("write: {e}"))?;
    let mut resp = Vec::new();
    stream
        .read_to_end(&mut resp)
        .map_err(|e| format!("read: {e}"))?;
    let status = resp
        .split(|&b| b == b'\r')
        .next()
        .map(|l| String::from_utf8_lossy(l).to_string())
        .unwrap_or_default();
    if status.contains(" 2") {
        Ok(status)
    } else {
        Err(format!("collector replied: {status}"))
    }
}

/// Flush the queue to the collector once. Spans are taken out BEFORE the POST and
/// put back on failure, so a flush that cannot reach the collector retries on the
/// next tick instead of losing the batch.
pub fn push_flush() -> Option<Result<String, String>> {
    push_endpoint()?;
    let batch: Vec<String> = {
        let mut q = PUSH_Q.lock().unwrap_or_else(|e| e.into_inner());
        if q.is_empty() {
            return None;
        }
        std::mem::take(&mut *q)
    };
    match push_post(&batch) {
        Ok(s) => Some(Ok(s)),
        Err(e) => {
            // Requeue at the FRONT so ordering survives a failed flush, still
            // bounded by the capacity rule.
            let mut q = PUSH_Q.lock().unwrap_or_else(|e| e.into_inner());
            let mut restored = batch;
            restored.append(&mut q);
            if restored.len() > PUSH_Q_CAP {
                let overflow = restored.len() - PUSH_Q_CAP;
                restored.drain(..overflow);
            }
            *q = restored;
            Some(Err(e))
        }
    }
}

/// Start the background exporter on first use, exactly once.
///
/// Self-starting rather than launched from `main` on purpose: the exporter is
/// only useful once something has a span to send, and starting it here keeps the
/// whole feature contained in this module — no startup-sequence edit, and no
/// thread in a process that never emits a span.
fn ensure_pusher() {
    static STARTED: OnceLock<()> = OnceLock::new();
    STARTED.get_or_init(spawn_pusher);
}

/// Flush the queue to the collector every `DRORB_OTLP_INTERVAL` seconds
/// (default 5). No-op when no endpoint is configured.
fn spawn_pusher() {
    let Some((host, port, path)) = push_endpoint() else {
        return;
    };
    let secs = std::env::var("DRORB_OTLP_INTERVAL")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|s| *s > 0)
        .unwrap_or(5);
    eprintln!("dataplane: OTLP/HTTP push -> http://{host}:{port}{path} (JSON, every {secs}s)");
    let _ = std::thread::Builder::new()
        .name("drorb-otlp-push".into())
        .spawn(move || {
            let mut failing = false;
            loop {
                std::thread::sleep(Duration::from_secs(secs));
                match push_flush() {
                    Some(Ok(_)) => {
                        if failing {
                            eprintln!("dataplane: OTLP push recovered");
                            failing = false;
                        }
                    }
                    Some(Err(e)) => {
                        // Report the transition, not every tick, so a collector
                        // that is down does not itself flood the logs.
                        if !failing {
                            eprintln!(
                                "dataplane: OTLP push failing: {e} (spans queued, will retry)"
                            );
                            failing = true;
                        }
                    }
                    None => {}
                }
            }
        });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_are_nonzero_and_distinct() {
        let (t1, s1) = fresh_ids();
        let (t2, s2) = fresh_ids();
        assert_ne!(t1, 0);
        assert_ne!(s1, 0);
        assert_ne!(t2, 0);
        assert_ne!(s2, 0);
        // Overwhelmingly likely distinct (different counter values, mixed).
        assert_ne!((t1, s1), (t2, s2));
    }

    #[test]
    fn span_object_has_mandated_id_widths_and_attrs() {
        let rl = ReqLine {
            method: "GET".to_string(),
            path: "/api/users".to_string(),
        };
        let obj = render_span(0x1u128, 0x2u64, &rl, "200", 1234);
        // 32-hex traceId, 16-hex spanId (the RFC-mandated widths, proven in Lean).
        assert!(obj.contains("\"traceId\":\"00000000000000000000000000000001\""));
        assert!(obj.contains("\"spanId\":\"0000000000000002\""));
        assert!(obj.contains("\"parentSpanId\":\"0000000000000000\""));
        assert!(obj.contains("\"name\":\"GET /api/users\""));
        assert!(obj.contains("\"http.request.method\""));
        assert!(obj.contains("\"stringValue\":\"200\""));
        assert!(obj.contains("\"duration_us\""));
    }

    #[test]
    fn json_escapes_hostile_path() {
        let rl = ReqLine {
            method: "GET".to_string(),
            path: "/a\"b\\c".to_string(),
        };
        let obj = render_span(0x1u128, 0x2u64, &rl, "200", 1);
        // The quote and backslash are escaped so the object stays valid JSON.
        assert!(obj.contains("/a\\\"b\\\\c"));
    }

    #[test]
    fn envelope_wraps_resource_and_scope() {
        let spans = vec![render_span(
            0x1u128,
            0x2u64,
            &ReqLine {
                method: "GET".to_string(),
                path: "/x".to_string(),
            },
            "204",
            9,
        )];
        let env = export_envelope(&spans);
        assert!(env.contains("\"resourceSpans\":["));
        assert!(env.contains("\"service.name\""));
        assert!(env.contains("\"scopeSpans\":["));
        assert!(env.contains("\"spans\":["));
    }
}
