//! Opt-in access logging for the plaintext HTTP/1.1 serve path.
//!
//! Controlled by the `DRORB_ACCESS_LOG` environment variable:
//!   * unset / empty / `0`  — disabled (the default);
//!   * `1` or `stderr`      — one line per served request to stderr;
//!   * any other value      — treated as a file path, opened for append.
//!
//! This is untrusted-shell observability emitted from the host serve loop. It
//! never touches the proven core or its decision — the host only reads the
//! request line and the response status it already has in hand, and writes a line.
//! It is deliberately outside the verified boundary.
//!
//! Each served request emits one compact `key=val` line:
//!
//! ```text
//! ts=<iso8601-utc> client=<ip> method=<m> path=<p> status=<code> backend=<b> bytes=<n> dur_us=<d>
//! ```
//!
//! `backend` is the dialled upstream for a reverse-proxied request, else `-`.
//! Only the plaintext HTTP/1.1 path is logged; the TLS front door serves whole
//! connections inside the proven core and is not per-request host-observable.

use std::fs::OpenOptions;
use std::io::Write;
use std::net::IpAddr;
use std::sync::{Mutex, OnceLock};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

/// Where access-log lines go.
enum Sink {
    Stderr,
    File(Mutex<std::fs::File>),
}

static SINK: OnceLock<Option<Sink>> = OnceLock::new();

/// Resolve (once) the configured sink from `DRORB_ACCESS_LOG`.
fn sink() -> Option<&'static Sink> {
    SINK.get_or_init(|| {
        let v = std::env::var("DRORB_ACCESS_LOG").ok()?;
        match v.as_str() {
            "" | "0" => None,
            "1" | "stderr" => Some(Sink::Stderr),
            path => match OpenOptions::new().create(true).append(true).open(path) {
                Ok(f) => Some(Sink::File(Mutex::new(f))),
                Err(e) => {
                    eprintln!(
                        "dataplane: DRORB_ACCESS_LOG={path}: cannot open ({e}); access log disabled"
                    );
                    None
                }
            },
        }
    })
    .as_ref()
}

/// Is access logging enabled? Cheap after the first call (the env is read once).
pub fn enabled() -> bool {
    sink().is_some()
}

/// The method + path of a request, captured before the request buffer is
/// consumed by the serve call.
pub struct ReqLine {
    pub method: String,
    pub path: String,
}

impl ReqLine {
    /// Parse the request line (`METHOD SP PATH SP VERSION`) from the head. Best
    /// effort: missing / non-UTF-8 fields become `-`.
    pub fn parse(req: &[u8]) -> ReqLine {
        let line = req.split(|&b| b == b'\n').next().unwrap_or(&[]);
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let mut it = line.split(|&b| b == b' ').filter(|s| !s.is_empty());
        let dec = |b: Option<&[u8]>| {
            b.and_then(|s| std::str::from_utf8(s).ok())
                .map(sanitize)
                .unwrap_or_else(|| "-".to_string())
        };
        ReqLine {
            method: dec(it.next()),
            path: dec(it.next()),
        }
    }
}

/// The 3-digit status code from an HTTP response head (`HTTP/1.1 SP CODE ...`),
/// or `-` if the head is not recognisable.
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

/// Keep one log field on one line and space-free: replace control characters and
/// spaces with `_`, and cap the length so a hostile request cannot bloat a line.
fn sanitize(s: &str) -> String {
    let mut out: String = s
        .chars()
        .take(2048)
        .map(|c| if c.is_control() || c == ' ' { '_' } else { c })
        .collect();
    if s.chars().count() > 2048 {
        out.push('…');
    }
    out
}

/// Emit one access-log line for a served request. No-op when logging is disabled.
/// `backend` is the dialled upstream address for a proxied request, else `None`.
pub fn log(client: IpAddr, req: &ReqLine, resp: &[u8], backend: Option<&str>, start: Instant) {
    let Some(sink) = sink() else {
        return;
    };
    let line = format!(
        "ts={} client={} method={} path={} status={} backend={} bytes={} dur_us={}\n",
        iso8601_now(),
        client,
        req.method,
        req.path,
        status_of(resp),
        backend.unwrap_or("-"),
        resp.len(),
        start.elapsed().as_micros(),
    );
    match sink {
        Sink::Stderr => {
            let _ = std::io::stderr().write_all(line.as_bytes());
        }
        Sink::File(m) => {
            if let Ok(mut f) = m.lock() {
                let _ = f.write_all(line.as_bytes());
            }
        }
    }
}

/// The current UTC time as an ISO-8601 string with microseconds, dependency-free.
fn iso8601_now() -> String {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = now.as_secs();
    let micros = now.subsec_micros();
    let days = (secs / 86_400) as i64;
    let sod = secs % 86_400;
    let (h, mi, s) = (sod / 3600, (sod % 3600) / 60, sod % 60);
    let (y, m, d) = civil_from_days(days);
    format!("{y:04}-{m:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{micros:06}Z")
}

/// Days since the Unix epoch → `(year, month, day)` in UTC. Howard Hinnant's
/// public-domain `civil_from_days` (chrono-compatible), no external crate.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let m = (if mp < 10 { mp + 3 } else { mp - 9 }) as u32; // [1, 12]
    (y + i64::from(m <= 2), m, d)
}
