//! Request observability — a structured event per handled request, with a request id.
//!
//! The retired gateway emitted nothing: no log line, no metric, no correlation id — a
//! production hosting edge that is invisible in an incident. This is the minimal, honest
//! version: the gateway mints a **request id** per request and emits one structured
//! [`RequestEvent`] (method, path, host, whether a subject was resolved — never the
//! subject value, which is a capability — status, and duration) through an injected
//! [`Observer`]. A deployment plugs in its metrics/tracing sink; the in-tree
//! [`StderrObserver`] writes one JSON line per request (dependency-free), and the
//! default [`NullObserver`] is silent (tests / embedded use).
//!
//! Deliberately NOT logging the subject or credential keeps a request log from becoming
//! a capability leak — the request id correlates a request across systems without it.

use http_serve::HttpMethod;

/// One handled request, as the gateway observes it.
#[derive(Debug, Clone)]
pub struct RequestEvent<'a> {
    /// The per-request correlation id (unguessable hex).
    pub request_id: &'a str,
    /// The request method.
    pub method: HttpMethod,
    /// The request path (query stripped).
    pub path: &'a str,
    /// The request `Host`.
    pub host: &'a str,
    /// Whether the gateway resolved a verified subject (NOT the subject itself — that is
    /// a capability, never logged).
    pub authenticated: bool,
    /// The response status.
    pub status: u16,
    /// Handler wall-clock in microseconds.
    pub elapsed_us: u128,
}

/// The observability sink the gateway emits a [`RequestEvent`] to per request.
pub trait Observer: Send + Sync {
    /// Record one handled request.
    fn on_request(&self, event: &RequestEvent<'_>);
}

/// A silent observer (the default) — no I/O.
pub struct NullObserver;

impl Observer for NullObserver {
    fn on_request(&self, _event: &RequestEvent<'_>) {}
}

/// A structured stderr observer — one JSON line per request.
pub struct StderrObserver;

impl Observer for StderrObserver {
    fn on_request(&self, e: &RequestEvent<'_>) {
        eprintln!(
            "{{\"kind\":\"request\",\"request_id\":\"{}\",\"method\":\"{}\",\"path\":{},\"host\":{},\"authenticated\":{},\"status\":{},\"elapsed_us\":{}}}",
            e.request_id,
            e.method,
            json_str(e.path),
            json_str(e.host),
            e.authenticated,
            e.status,
            e.elapsed_us,
        );
    }
}

/// Encode `s` as a JSON string literal (quotes + the mandatory escapes), so a path or
/// host with a quote / backslash / control char cannot break the log line's framing.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_str_escapes_framing_chars() {
        assert_eq!(json_str("a\"b\\c"), "\"a\\\"b\\\\c\"");
        assert_eq!(json_str("line\nbreak"), "\"line\\nbreak\"");
        // A control char is \u-escaped, not emitted raw.
        assert_eq!(json_str("\u{1}"), "\"\\u0001\"");
    }
}
