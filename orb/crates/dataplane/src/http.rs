//! HTTP/1.1 framing. The host reads only what it needs to delimit messages on
//! the byte stream (where a request ends, where the next begins) and to decide
//! whether the connection stays open. It parses no request semantics and
//! rewrites nothing — the meaning of every request is the proven core's job.
//!
//! The framing is IO-agnostic: [`next_request`] inspects an accumulation buffer
//! and reports whether a complete request is present, without knowing how the
//! bytes arrived. Both the blocking thread-per-connection loop and the io_uring
//! loop drive it — one by filling the buffer with blocking reads, the other by
//! appending io_uring recv completions.

/// Cap on a single buffered request (head + body). A request larger than this
/// is refused by closing the connection rather than growing without bound.
pub const REQUEST_CAP: usize = 8 << 20; // 8 MiB

/// The HTTP/2 cleartext (h2c) connection preface. If a connection opens with
/// this, its framing is binary HTTP/2 frames, not CRLF-delimited HTTP/1.1
/// messages; the host hands the whole opening burst to the proven core once
/// (which forks to the H2 engine) and then closes — it does not attempt
/// HTTP/1.1 keep-alive framing on an h2c stream.
pub const H2_PREFACE: &[u8] = b"PRI * HTTP/2.0\r\n";

/// The full 24-octet HTTP/2 client connection preface
/// (`PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`, RFC 9113 §3.4). The buffer opens with it
/// on an h2c prior-knowledge connection; [`H2_PREFACE`] is its 16-octet head,
/// enough to fork on.
const H2_PREFACE_FULL: usize = 24;

/// Whether the h2c opening burst in `buf` already carries a complete request
/// HEADERS frame (RFC 9113 §6.2, frame type `0x01`) past the 24-octet client
/// connection preface. The host uses this to decide it has enough of the burst
/// to hand to the proven H2 serve — a prior-knowledge client (curl/nghttp2)
/// writes its preface, SETTINGS, and request HEADERS as one burst, then waits
/// for the response, so the host must not block for bytes that never come once
/// the HEADERS frame is in hand.
///
/// Walks the 9-octet frame headers (`u24 length | type | flags | u31 stream-id`)
/// from the end of the preface; returns `true` as soon as a fully-buffered
/// HEADERS frame is seen, `false` if the scan runs off the end of the buffer
/// (a partial frame — read more).
pub fn h2c_burst_complete(buf: &[u8]) -> bool {
    let mut i = H2_PREFACE_FULL;
    while i + 9 <= buf.len() {
        let len = ((buf[i] as usize) << 16) | ((buf[i + 1] as usize) << 8) | (buf[i + 2] as usize);
        let ftype = buf[i + 3];
        let end = i + 9 + len;
        if end > buf.len() {
            return false; // frame body not fully buffered yet
        }
        if ftype == 0x01 {
            return true; // a complete request HEADERS frame is present
        }
        i = end;
    }
    false
}

/// The result of scanning an accumulation buffer for the next complete request.
pub enum Frame {
    /// Not enough bytes yet; read more and rescan.
    NeedMore,
    /// A complete request occupies the first `usize` bytes of the buffer.
    Complete(usize),
    /// The request exceeds [`REQUEST_CAP`]; the connection must be closed.
    Oversize,
}

/// Scan `data` for one complete HTTP/1.1 request (head through CRLFCRLF plus a
/// framed body). Pure: it does no IO and mutates nothing.
pub fn next_request(data: &[u8]) -> Frame {
    // 1. Find the end of the head (CRLFCRLF).
    let head_end = match data.windows(4).position(|w| w == b"\r\n\r\n") {
        Some(p) => p + 4,
        None => {
            return if data.len() > REQUEST_CAP {
                Frame::Oversize
            } else {
                Frame::NeedMore
            };
        }
    };

    // 2. Frame the body.
    match body_frame(&data[..head_end]) {
        BodyFrame::Fixed(n) => {
            let total = head_end + n;
            if total > REQUEST_CAP {
                Frame::Oversize
            } else if data.len() < total {
                Frame::NeedMore
            } else {
                Frame::Complete(total)
            }
        }
        BodyFrame::Chunked => match chunked_len(data, head_end) {
            Some(clen) => {
                let total = head_end + clen;
                if total > REQUEST_CAP {
                    Frame::Oversize
                } else {
                    Frame::Complete(total)
                }
            }
            None => {
                if data.len() > REQUEST_CAP {
                    Frame::Oversize
                } else {
                    Frame::NeedMore
                }
            }
        },
    }
}

/// Where a request's body ends, once the head is in hand.
enum BodyFrame {
    /// Body is exactly `len` bytes (Content-Length, or none → 0).
    Fixed(usize),
    /// Body is chunked; the host must scan chunk framing to find its end.
    Chunked,
}

/// Case-insensitive search for `needle` (lowercase ASCII) in `hay`.
fn find_ci(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || hay.len() < needle.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&i| {
        hay[i..i + needle.len()]
            .iter()
            .zip(needle)
            .all(|(a, b)| a.to_ascii_lowercase() == *b)
    })
}

/// Read a header value (bytes after `name:` up to CRLF) from a header block.
/// `name` is lowercase and colon-free.
fn header_value<'a>(head: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
    let mut i = 0;
    while i < head.len() {
        let line_end = head[i..]
            .windows(2)
            .position(|w| w == b"\r\n")
            .map(|p| i + p)
            .unwrap_or(head.len());
        let line = &head[i..line_end];
        if let Some(colon) = line.iter().position(|&c| c == b':') {
            let (n, v) = line.split_at(colon);
            if n.len() == name.len()
                && n.iter().zip(name).all(|(a, b)| a.to_ascii_lowercase() == *b)
            {
                let val = &v[1..]; // skip ':'
                let start = val
                    .iter()
                    .position(|&c| c != b' ' && c != b'\t')
                    .unwrap_or(val.len());
                let end = val
                    .iter()
                    .rposition(|&c| c != b' ' && c != b'\t')
                    .map(|p| p + 1)
                    .unwrap_or(start);
                return Some(&val[start..end]);
            }
        }
        i = line_end + 2;
    }
    None
}

/// Given the head bytes (through CRLFCRLF), decide how the body is framed.
fn body_frame(head: &[u8]) -> BodyFrame {
    if let Some(te) = header_value(head, b"transfer-encoding") {
        if find_ci(te, b"chunked").is_some() {
            return BodyFrame::Chunked;
        }
    }
    if let Some(cl) = header_value(head, b"content-length") {
        let s = std::str::from_utf8(cl).ok().map(str::trim).unwrap_or("");
        if let Ok(n) = s.parse::<usize>() {
            return BodyFrame::Fixed(n);
        }
    }
    BodyFrame::Fixed(0)
}

/// Scan chunked body framing starting at `start` in `buf`. Returns the byte
/// length of the whole chunked section (including the terminating 0-chunk and
/// trailers) if it is fully present, or `None` if more bytes are needed.
fn chunked_len(buf: &[u8], start: usize) -> Option<usize> {
    let mut i = start;
    loop {
        // chunk-size line: hex digits up to CRLF (ignore any ;ext).
        let nl = buf[i..].windows(2).position(|w| w == b"\r\n")? + i;
        let size_str = std::str::from_utf8(&buf[i..nl]).ok()?;
        let hex = size_str.split(';').next().unwrap_or("").trim();
        let size = usize::from_str_radix(hex, 16).ok()?;
        i = nl + 2; // past the size line's CRLF
        if size == 0 {
            // trailers: header lines until an empty line (CRLF).
            loop {
                let end = buf[i..].windows(2).position(|w| w == b"\r\n")? + i;
                if end == i {
                    return Some(end + 2 - start); // empty line — end of trailers
                }
                i = end + 2;
            }
        }
        i += size; // chunk data
        if i + 2 > buf.len() {
            return None;
        }
        i += 2; // trailing CRLF after chunk data
    }
}

/// Whether the connection should stay open after this request, per HTTP/1.1
/// rules: HTTP/1.1 defaults to keep-alive unless `Connection: close`; HTTP/1.0
/// defaults to close unless `Connection: keep-alive`.
pub fn request_wants_keepalive(head: &[u8]) -> bool {
    let is_11 = find_ci(head, b"http/1.1").is_some();
    match header_value(head, b"connection") {
        Some(v) if find_ci(v, b"close").is_some() => false,
        Some(v) if find_ci(v, b"keep-alive").is_some() => true,
        _ => is_11,
    }
}

/// Annotate an HTTP/1.1 response in place with an explicit `Connection` header
/// reflecting the host's keep-alive decision, unless the response already
/// carries one. The proven serve emits the status line, headers, and body; the
/// host owns only the connection disposition on the wire, and states it here.
///
/// This matters for strict HTTP/1.1 clients (Apache Bench, some proxies) that
/// key connection reuse off an explicit `Connection: keep-alive` token: without
/// it they fall back to close-delimited framing and read until the server
/// closes, while a host that keeps the socket open for the next request waits on
/// them — both sides block until the client's poll times out. An explicit
/// `Connection: keep-alive` (or `close`) removes the ambiguity. The header is
/// inserted right after the status line and never added when the response — for
/// instance a forwarded upstream reply — already states its own disposition.
pub fn annotate_connection(resp: &mut Vec<u8>, keepalive: bool) {
    // Insertion point: just past the status line's CRLF. A response with no
    // status-line CRLF is not a well-formed HTTP/1.1 head (e.g. raw H2 frames);
    // leave it untouched.
    let Some(status_end) = resp.windows(2).position(|w| w == b"\r\n").map(|p| p + 2) else {
        return;
    };
    let head_end = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(resp.len());
    if header_value(&resp[..head_end], b"connection").is_some() {
        return; // response already states its own connection disposition
    }
    let token: &[u8] = if keepalive {
        b"Connection: keep-alive\r\n"
    } else {
        b"Connection: close\r\n"
    };
    resp.splice(status_end..status_end, token.iter().copied());
}

/// Whether the *response* is self-delimiting (has Content-Length or is chunked).
/// A response with neither is delimited by connection close, so keep-alive is
/// impossible and the host must close after writing it. Reads response framing
/// headers only; never rewrites the response.
pub fn response_is_self_delimited(resp: &[u8]) -> bool {
    let head_end = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(resp.len());
    let head = &resp[..head_end];
    header_value(head, b"content-length").is_some()
        || header_value(head, b"transfer-encoding")
            .map(|te| find_ci(te, b"chunked").is_some())
            .unwrap_or(false)
}
