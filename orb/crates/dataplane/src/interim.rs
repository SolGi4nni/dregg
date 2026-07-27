//! Interim `100 Continue` emission (RFC 9110 §10.1.1).
//!
//! A client that announces `Expect: 100-continue` pauses before shipping its
//! body until the server either answers the interim `100` or responds
//! finally. The proven serve is a complete-request → response function, so
//! the interim — a response emitted MID-REQUEST, after the head but before
//! the body — is inherently an IO-loop behaviour: it lives here, at the
//! accumulation seam, next to the framing (`http::next_request`) whose
//! `NeedMore` verdict is exactly the "head arrived, body pending" moment.
//!
//! The decision is deliberately narrow (fail-closed to "send nothing", which
//! is always allowed — §10.1.1 lets the server omit the interim when the
//! final response is coming anyway):
//!
//! * the accumulated bytes hold a COMPLETE head (CRLFCRLF seen);
//! * the request line is `HTTP/1.1` (an interim to a 1.0 client is illegal);
//! * some `Expect` header field's value is exactly `100-continue`
//!   (case-insensitive, OWS-trimmed) — an UNKNOWN expectation must NOT get
//!   the interim (it gets the proven fold's `417`);
//! * the caller observed `Frame::NeedMore`, i.e. the announced body has not
//!   fully arrived (a complete request is served finally, no interim).
//!
//! Per-connection dedup (send the interim at most once per request) is the
//! caller's state (`interim_100_sent` on the connection).

/// The interim response bytes (a complete interim message — no headers, no
/// body, per RFC 9112 §2.1).
pub const INTERIM_100: &[u8] = b"HTTP/1.1 100 Continue\r\n\r\n";

/// Case-insensitive ASCII equality.
fn eq_ignore_case(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|(x, y)| x.to_ascii_lowercase() == y.to_ascii_lowercase())
}

/// OWS-trim (SP / HTAB, RFC 9110 §5.6.3).
fn trim_ows(mut v: &[u8]) -> &[u8] {
    while let [b' ' | b'\t', rest @ ..] = v {
        v = rest;
    }
    while let [rest @ .., b' ' | b'\t'] = v {
        v = rest;
    }
    v
}

/// The accumulated bytes hold a complete `HTTP/1.1` head that announced
/// `Expect: 100-continue` and whose body has not fully arrived (the caller
/// observed `Frame::NeedMore`). See the module doc for the exact criteria.
pub fn wants_interim_100(acc: &[u8]) -> bool {
    let head_end = match acc.windows(4).position(|w| w == b"\r\n\r\n") {
        Some(p) => p, // head lines end here; the CRLFCRLF is the terminator
        None => return false,
    };
    let head = &acc[..head_end];
    let mut lines = head
        .split(|&b| b == b'\n')
        .map(|l| l.strip_suffix(b"\r").unwrap_or(l));
    // Request line: must be HTTP/1.1 (interim responses are 1.1+).
    match lines.next() {
        Some(line) if line.ends_with(b"HTTP/1.1") => {}
        _ => return false,
    }
    // Header fields: any `Expect` whose value is exactly `100-continue`.
    for line in lines {
        let Some(colon) = line.iter().position(|&b| b == b':') else {
            continue;
        };
        if eq_ignore_case(&line[..colon], b"expect")
            && eq_ignore_case(trim_ows(&line[colon + 1..]), b"100-continue")
        {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fires_on_expect_100_continue_partial_body() {
        let acc = b"POST /health HTTP/1.1\r\nHost: x\r\nExpect: 100-continue\r\nContent-Length: 5\r\n\r\n";
        assert!(wants_interim_100(acc));
    }

    #[test]
    fn fires_case_insensitive_with_ows() {
        let acc = b"POST / HTTP/1.1\r\nexpect:  100-CONTINUE \r\nContent-Length: 5\r\n\r\n";
        assert!(wants_interim_100(acc));
    }

    #[test]
    fn silent_on_unknown_expectation() {
        // The unknown expectation gets the proven fold's 417, never an interim.
        let acc = b"GET /health HTTP/1.1\r\nExpect: some-unknown-99\r\n\r\n";
        assert!(!wants_interim_100(acc));
    }

    #[test]
    fn silent_on_http_1_0() {
        let acc = b"POST / HTTP/1.0\r\nExpect: 100-continue\r\nContent-Length: 5\r\n\r\n";
        assert!(!wants_interim_100(acc));
    }

    #[test]
    fn silent_on_incomplete_head() {
        let acc = b"POST / HTTP/1.1\r\nExpect: 100-continue\r\n";
        assert!(!wants_interim_100(acc));
    }

    #[test]
    fn silent_without_expect() {
        let acc = b"POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\n";
        assert!(!wants_interim_100(acc));
    }
}
