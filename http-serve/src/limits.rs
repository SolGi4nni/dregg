//! `limits` — the **public-surface robustness bounds** for the serving core:
//! per-socket read/write timeouts + an overall request deadline (slow-loris), a
//! request body-size cap (`413`, untrusted `Content-Length`), a
//! connection-concurrency gate (thread-per-connection DoS), and explicit
//! `Transfer-Encoding: chunked` request decoding.
//!
//! Ported dregg-native from the prior operated layer (the hardened
//! connection loop: `Limits` :93, `read_sized_body` :839, `read_chunked_body`
//! :869, `is_timeout` :950), where these bounds guarded the public internet
//! surface. The current [`serve_http_connection`](crate::serve::serve_http_connection)
//! enforces only the 64 KiB header cap — no read/write timeout, no body cap, no
//! connection ceiling, no deadline. These limits reject only abusive/malformed
//! traffic; a well-behaved client sees the same bytes as before.
//!
//! Everything here is pure `std` (the crate's no-deps property is preserved).
//!
//! WIRING (main loop): add `pub mod limits;` to `http-serve/src/lib.rs`, then in
//! `serve.rs`
//! - `serve_http`: hold a [`ConnGate`] permit around each spawned connection
//!   thread (`Limits::from_env().max_connections`);
//! - `serve_http_connection`: take a `&Limits`, call [`Limits::apply_socket`]
//!   first, carry `deadline = Instant::now() + limits.request_deadline` through
//!   the header loop (408 via [`is_timeout`] / deadline check), use
//!   `limits.max_header_bytes` for the 431 cap, and read the body through
//!   [`read_sized_body`] / [`read_chunked_body`] mapping [`BodyOutcome`] to
//!   413/408/400 (`WebResponse::error`).

use std::io::Read;
use std::net::TcpStream;
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// Default cap on the request header block; larger is rejected with 431.
pub const DEFAULT_MAX_HEADER_BYTES: usize = 64 * 1024;
/// Default per-socket read timeout (idle-stall guard).
pub const DEFAULT_READ_TIMEOUT_MS: u64 = 30_000;
/// Default per-socket write timeout.
pub const DEFAULT_WRITE_TIMEOUT_MS: u64 = 30_000;
/// Default total wall-clock budget to read one request (slow-trickle guard).
pub const DEFAULT_REQUEST_DEADLINE_MS: u64 = 60_000;
/// Default request body-size cap (declared or actual); over this is a 413.
pub const DEFAULT_MAX_BODY_BYTES: usize = 4 * 1024 * 1024;
/// Default cap on simultaneously-served connections (thread-per-connection DoS
/// guard); excess connections wait for a slot.
pub const DEFAULT_MAX_CONNECTIONS: usize = 1024;

/// Robustness limits for the connection loop, configurable via `DREGG_HTTP_*` env.
#[derive(Debug, Clone)]
pub struct Limits {
    /// Per-socket read timeout (a stalled peer's read fails, not hangs).
    pub read_timeout: Duration,
    /// Per-socket write timeout.
    pub write_timeout: Duration,
    /// Total wall-clock budget to read one request (slow-loris/slow-trickle).
    pub request_deadline: Duration,
    /// Cap on the request header block → 431.
    pub max_header_bytes: usize,
    /// Cap on the (declared or actual) request body → 413.
    pub max_body_bytes: usize,
    /// Cap on simultaneously-served connections (see [`ConnGate`]).
    pub max_connections: usize,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits {
            read_timeout: Duration::from_millis(DEFAULT_READ_TIMEOUT_MS),
            write_timeout: Duration::from_millis(DEFAULT_WRITE_TIMEOUT_MS),
            request_deadline: Duration::from_millis(DEFAULT_REQUEST_DEADLINE_MS),
            max_header_bytes: DEFAULT_MAX_HEADER_BYTES,
            max_body_bytes: DEFAULT_MAX_BODY_BYTES,
            max_connections: DEFAULT_MAX_CONNECTIONS,
        }
    }
}

impl Limits {
    /// Limits from the `DREGG_HTTP_{READ_TIMEOUT_MS, WRITE_TIMEOUT_MS,
    /// REQUEST_DEADLINE_MS, MAX_HEADER_BYTES, MAX_BODY_BYTES, MAX_CONNECTIONS}`
    /// env vars, defaulting per the constants above.
    pub fn from_env() -> Limits {
        Limits {
            read_timeout: env_ms("DREGG_HTTP_READ_TIMEOUT_MS", DEFAULT_READ_TIMEOUT_MS),
            write_timeout: env_ms("DREGG_HTTP_WRITE_TIMEOUT_MS", DEFAULT_WRITE_TIMEOUT_MS),
            request_deadline: env_ms(
                "DREGG_HTTP_REQUEST_DEADLINE_MS",
                DEFAULT_REQUEST_DEADLINE_MS,
            ),
            max_header_bytes: env_usize("DREGG_HTTP_MAX_HEADER_BYTES", DEFAULT_MAX_HEADER_BYTES),
            max_body_bytes: env_usize("DREGG_HTTP_MAX_BODY_BYTES", DEFAULT_MAX_BODY_BYTES),
            max_connections: env_usize("DREGG_HTTP_MAX_CONNECTIONS", DEFAULT_MAX_CONNECTIONS)
                .max(1),
        }
    }

    /// Apply the per-socket timeouts to an accepted connection — the first thing
    /// a hardened connection handler does.
    pub fn apply_socket(&self, stream: &TcpStream) -> std::io::Result<()> {
        stream.set_read_timeout(Some(self.read_timeout))?;
        stream.set_write_timeout(Some(self.write_timeout))
    }

    /// The absolute deadline for reading the request that starts now.
    pub fn deadline_from_now(&self) -> Instant {
        Instant::now() + self.request_deadline
    }
}

/// Read a `Duration` in ms from an env var, falling back to `default_ms`.
fn env_ms(key: &str, default_ms: u64) -> Duration {
    let ms = std::env::var(key)
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(default_ms);
    Duration::from_millis(ms)
}

/// Read a `usize` from an env var, falling back to `default`.
fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(default)
}

/// Whether an IO error is a socket read/write timeout (a stalled peer).
pub fn is_timeout(e: &std::io::Error) -> bool {
    matches!(
        e.kind(),
        std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
    )
}

/// The terminal states of a bounded body read — the caller maps these onto
/// `413` / `408` / `400` responses.
#[derive(Debug)]
pub enum BodyOutcome {
    /// The full body was read.
    Body(Vec<u8>),
    /// The declared/actual size exceeds the cap → 413.
    TooLarge,
    /// A read timed out or the request deadline passed → 408.
    Timeout,
    /// The chunked framing was malformed → 400.
    Malformed,
}

/// Read an identity (Content-Length) body, capping at `max` and bounding total
/// time by `deadline`. `leftover` is whatever already followed the header block.
pub fn read_sized_body<R: Read>(
    stream: &mut R,
    leftover: &[u8],
    len: usize,
    max: usize,
    deadline: Instant,
) -> std::io::Result<BodyOutcome> {
    if len > max {
        return Ok(BodyOutcome::TooLarge);
    }
    let mut body = leftover.to_vec();
    let mut tmp = [0u8; 8192];
    while body.len() < len {
        if Instant::now() >= deadline {
            return Ok(BodyOutcome::Timeout);
        }
        match stream.read(&mut tmp) {
            Ok(0) => break, // peer closed early — serve what arrived, truncated below
            Ok(n) => body.extend_from_slice(&tmp[..n]),
            Err(e) if is_timeout(&e) => return Ok(BodyOutcome::Timeout),
            Err(e) => return Err(e),
        }
    }
    body.truncate(len);
    Ok(BodyOutcome::Body(body))
}

/// Decode a `Transfer-Encoding: chunked` request body, capping the decoded size
/// at `max` and bounding total time by `deadline`. `leftover` is whatever already
/// followed the header block.
pub fn read_chunked_body<R: Read>(
    stream: &mut R,
    leftover: &[u8],
    max: usize,
    deadline: Instant,
) -> std::io::Result<BodyOutcome> {
    let mut raw = leftover.to_vec();
    let mut decoded: Vec<u8> = Vec::new();
    let mut cursor = 0usize;
    let mut tmp = [0u8; 8192];

    loop {
        match find_subslice(&raw[cursor..], b"\r\n") {
            Some(rel) => {
                let line_end = cursor + rel;
                let size_line = &raw[cursor..line_end];
                // chunk-size [ ";" chunk-ext ]
                let size = match std::str::from_utf8(size_line)
                    .ok()
                    .map(|s| s.split(';').next().unwrap_or("").trim())
                    .and_then(|s| usize::from_str_radix(s, 16).ok())
                {
                    Some(v) => v,
                    None => return Ok(BodyOutcome::Malformed),
                };
                let data_start = line_end + 2;
                if size == 0 {
                    // The last chunk; the body is complete (trailers, if any, are
                    // not part of the entity and are ignored).
                    return Ok(BodyOutcome::Body(decoded));
                }
                if decoded.len() + size > max {
                    return Ok(BodyOutcome::TooLarge);
                }
                let need = data_start + size + 2; // data + trailing CRLF
                if raw.len() < need {
                    match fill(stream, &mut raw, &mut tmp, max, deadline)? {
                        Some(outcome) => return Ok(outcome),
                        None => continue,
                    }
                }
                decoded.extend_from_slice(&raw[data_start..data_start + size]);
                cursor = data_start + size + 2; // skip data + CRLF
            }
            None => match fill(stream, &mut raw, &mut tmp, max, deadline)? {
                Some(outcome) => return Ok(outcome),
                None => {}
            },
        }
    }
}

/// Read one more block into `raw` for the chunked decoder. Returns
/// `Some(outcome)` on a terminal condition (timeout / EOF / over-cap), `None` if
/// more bytes were appended and decoding should continue.
fn fill<R: Read>(
    stream: &mut R,
    raw: &mut Vec<u8>,
    tmp: &mut [u8],
    max: usize,
    deadline: Instant,
) -> std::io::Result<Option<BodyOutcome>> {
    if Instant::now() >= deadline {
        return Ok(Some(BodyOutcome::Timeout));
    }
    match stream.read(tmp) {
        Ok(0) => Ok(Some(BodyOutcome::Malformed)), // EOF mid-body
        Ok(n) => {
            raw.extend_from_slice(&tmp[..n]);
            // Bound the raw buffer too (framing overhead beyond the decoded cap).
            if raw.len() > max.saturating_add(64 * 1024) {
                return Ok(Some(BodyOutcome::TooLarge));
            }
            Ok(None)
        }
        Err(e) if is_timeout(&e) => Ok(Some(BodyOutcome::Timeout)),
        Err(e) => Err(e),
    }
}

/// First index of `needle` in `haystack` (the header/chunk terminator scan).
fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// A pure-`std` counting semaphore bounding simultaneously-served connections —
/// the thread-per-connection DoS guard. `acquire` blocks until a slot frees;
/// dropping the [`ConnPermit`] releases it.
#[derive(Clone)]
pub struct ConnGate {
    inner: Arc<(Mutex<usize>, Condvar)>,
    max: usize,
}

impl ConnGate {
    /// A gate admitting at most `max` (≥ 1) concurrent permits.
    pub fn new(max: usize) -> ConnGate {
        ConnGate {
            inner: Arc::new((Mutex::new(0), Condvar::new())),
            max: max.max(1),
        }
    }

    /// Block until a slot is free, then take it. The permit releases on drop.
    pub fn acquire(&self) -> ConnPermit {
        let (lock, cvar) = &*self.inner;
        let mut live = lock.lock().unwrap_or_else(|e| e.into_inner());
        while *live >= self.max {
            live = cvar.wait(live).unwrap_or_else(|e| e.into_inner());
        }
        *live += 1;
        ConnPermit {
            inner: Arc::clone(&self.inner),
        }
    }

    /// The number of permits currently held (for tests/metrics).
    pub fn in_flight(&self) -> usize {
        *self.inner.0.lock().unwrap_or_else(|e| e.into_inner())
    }
}

/// A held connection slot; dropping it frees the slot and wakes one waiter.
pub struct ConnPermit {
    inner: Arc<(Mutex<usize>, Condvar)>,
}

impl Drop for ConnPermit {
    fn drop(&mut self) {
        let (lock, cvar) = &*self.inner;
        let mut live = lock.lock().unwrap_or_else(|e| e.into_inner());
        *live = live.saturating_sub(1);
        cvar.notify_one();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn far() -> Instant {
        Instant::now() + Duration::from_secs(60)
    }

    // ── the 413 cap: a declared oversize body never reads a byte ──────────────
    #[test]
    fn a_declared_oversize_body_is_too_large_before_reading() {
        let mut stream = Cursor::new(vec![0u8; 16]);
        let out = read_sized_body(&mut stream, &[], 100, 10, far()).unwrap();
        assert!(matches!(out, BodyOutcome::TooLarge));
        assert_eq!(stream.position(), 0, "no bytes read for a refused body");
    }

    #[test]
    fn a_sized_body_reads_leftover_plus_stream() {
        let mut stream = Cursor::new(b"world".to_vec());
        let out = read_sized_body(&mut stream, b"hello ", 11, 100, far()).unwrap();
        match out {
            BodyOutcome::Body(b) => assert_eq!(b, b"hello world"),
            other => panic!("expected body, got {other:?}"),
        }
    }

    // ── a passed deadline reads as 408, not a hang ─────────────────────────────
    #[test]
    fn a_passed_deadline_times_out_a_sized_body() {
        let mut stream = Cursor::new(Vec::<u8>::new());
        let past = Instant::now() - Duration::from_millis(1);
        let out = read_sized_body(&mut stream, &[], 10, 100, past).unwrap();
        assert!(matches!(out, BodyOutcome::Timeout));
    }

    // ── chunked decoding: roundtrip, extensions tolerated, split reads ────────
    #[test]
    fn chunked_body_decodes_across_leftover_and_stream() {
        // "hello world" as 5;ext + 6 + terminator, split between leftover and stream.
        let leftover = b"5;x=y\r\nhello\r\n";
        let mut stream = Cursor::new(b"6\r\n world\r\n0\r\n\r\n".to_vec());
        let out = read_chunked_body(&mut stream, leftover, 100, far()).unwrap();
        match out {
            BodyOutcome::Body(b) => assert_eq!(b, b"hello world"),
            other => panic!("expected body, got {other:?}"),
        }
    }

    #[test]
    fn chunked_over_cap_is_too_large_and_bad_framing_is_malformed() {
        let mut stream = Cursor::new(b"ff\r\n".to_vec());
        let out = read_chunked_body(&mut stream, &[], 10, far()).unwrap();
        assert!(matches!(out, BodyOutcome::TooLarge), "0xff > cap 10");

        let mut bad = Cursor::new(b"zz\r\nhello\r\n0\r\n\r\n".to_vec());
        let out = read_chunked_body(&mut bad, &[], 100, far()).unwrap();
        assert!(matches!(out, BodyOutcome::Malformed));

        // EOF mid-body (no terminating chunk) is malformed, not an infinite loop.
        let mut eof = Cursor::new(b"5\r\nhel".to_vec());
        let out = read_chunked_body(&mut eof, &[], 100, far()).unwrap();
        assert!(matches!(out, BodyOutcome::Malformed));
    }

    // ── the connection gate bounds concurrency and releases on drop ───────────
    #[test]
    fn the_conn_gate_bounds_concurrency() {
        let gate = ConnGate::new(2);
        let a = gate.acquire();
        let _b = gate.acquire();
        assert_eq!(gate.in_flight(), 2);

        // A third acquire blocks until a permit drops.
        let gate2 = gate.clone();
        let t = std::thread::spawn(move || {
            let _c = gate2.acquire();
            gate2.in_flight()
        });
        std::thread::sleep(Duration::from_millis(50));
        assert_eq!(gate.in_flight(), 2, "third waiter has not been admitted");
        drop(a);
        assert_eq!(t.join().unwrap(), 2, "waiter admitted after a release");
        // And everything releases.
        std::thread::sleep(Duration::from_millis(10));
    }

    #[test]
    fn limits_default_and_env_floor() {
        let l = Limits::default();
        assert_eq!(l.max_header_bytes, DEFAULT_MAX_HEADER_BYTES);
        assert_eq!(l.max_body_bytes, DEFAULT_MAX_BODY_BYTES);
        assert!(l.max_connections >= 1);
        assert!(l.deadline_from_now() > Instant::now());
    }
}
