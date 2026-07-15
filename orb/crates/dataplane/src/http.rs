//! HTTP/1.1 framing. The host reads only what it needs to delimit messages on
//! the byte stream (where a request ends, where the next begins) and to decide
//! whether the connection stays open. It parses no request semantics and
//! rewrites nothing — the meaning of every request is the proven core's job.
//!
//! **The framing decision itself is the proven core's job too.** [`next_request`]
//! does not compute the request boundary: it crosses `drorb_frame_request`
//! (`Body.FrameRaw.frameRequestExport`, the C-ABI wrapper of the proven
//! `Body.FrameRaw.frameRaw`) with the raw accumulation buffer and acts on the
//! encoded verdict. Where each request ends — and the smuggling rejection when
//! the framing is ambiguous (CL.TE / TE.CL overlap, duplicate/invalid
//! `Content-Length`, malformed chunk) — is therefore governed by the
//! machine-checked decision (`frameRaw_no_smuggle_general`, `frameRaw_faithful`,
//! `frameRaw_bounded`), not by a host reimplementation that could drift from it.
//! The host retains only what is not a framing decision: the [`REQUEST_CAP`]
//! resource limit (a DoS bound) and the h2c binary-preface fork (HTTP/2 frames,
//! not CRLF-delimited messages).
//!
//! The crossing runs on the calling IO thread, registered once with
//! `lean_initialize_thread` — the same discipline as the attached serve owners
//! (see `serve.rs::spawn_attached_owner` and the multi-owner runtime-safety
//! analysis): the export is a pure `ByteArray -> ByteArray`, every per-call
//! object is created, consumed, and dropped on the one calling thread, and the
//! only cross-thread objects are the module's persistent globals. No thread hop,
//! no job channel — the framing verdict is a direct call.
//!
//! The framing is IO-agnostic: [`next_request`] inspects an accumulation buffer
//! and reports whether a complete request is present, without knowing how the
//! bytes arrived. Both the blocking thread-per-connection loop and the io_uring
//! loop drive it — one by filling the buffer with blocking reads, the other by
//! appending io_uring recv completions. The IO hosts start only after the serve
//! gateway's boot handshake, so the process-global Lean runtime is always up
//! before the first framing scan.

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

/// Whether a connection's opening flight — already resolved to a complete
/// request boundary by the raw framer — cannot actually be an HTTP/1.x request
/// because its first line carries no `HTTP/` version token anywhere
/// (RFC 9112 §2.3: `request-line = method SP request-target SP HTTP-version`,
/// `HTTP-version = "HTTP/" DIGIT "." DIGIT`).
///
/// On a port that speaks both protocols such an opener is neither protocol's
/// well-formed first flight: not an HTTP/1.x request (no version token), and
/// not the HTTP/2 preface (`PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n` — the well-formed
/// preface forked to the H2 engine before framing). The host terminates it
/// without a reply, the one answer both protocols assign: RFC 9113 §3.4
/// REQUIRES treating an invalid preface as a connection error and terminating
/// (an HTTP/1.1 status line is only frame garbage to an H2 client; the GOAWAY
/// is optional), and RFC 9112 §2.2/§3 permits closing on a request line that
/// fails the grammar. Only the FIRST flight on a connection is ever classified
/// (a preface arrives nowhere else), and a request line with ANY `HTTP/`
/// version token (`HTTP/1.1`, `HTTP/2.0`, even `HTTP/9.9`) never matches, so
/// every version-carrying HTTP/1.x request still reaches the proven serve and
/// its real 505/400 answers.
pub fn opener_lacks_http_version(req: &[u8]) -> bool {
    let line_end = req.iter().position(|&b| b == b'\n').unwrap_or(req.len());
    !req[..line_end].windows(5).any(|w| w == b"HTTP/")
}

/// The result of scanning an accumulation buffer for the next complete request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Frame {
    /// Not enough bytes yet; read more and rescan.
    NeedMore,
    /// A complete request occupies the first `usize` bytes of the buffer.
    Complete(usize),
    /// The request must be refused by closing the connection: either it exceeds
    /// [`REQUEST_CAP`], or the proven framer rejected it — ambiguous/malformed
    /// body framing (a `Content-Length` overlapping a chunked
    /// `Transfer-Encoding`, a duplicate/conflicting/non-integer
    /// `Content-Length`, a non-final or unimplemented transfer coding, or a
    /// malformed chunk — RFC 9112 §6.1/§6.3). The rejection IS the
    /// machine-checked `Body.FrameRaw.frameRaw = .reject` decision
    /// (`frameRaw_no_smuggle_general`: such a message is never resolved to a
    /// `complete` boundary), so no octet is reinterpreted as a smuggled second
    /// request.
    Oversize,
}

// ---------------------------------------------------------------------------
// The proven framing seam: `drorb_frame_request` (`Body.FrameRaw`).
//
// These declarations are http.rs's own (the serve seam in `serve.rs` keeps
// its own set): the framing crossing is made from IO threads, not the serve
// owner, and shares nothing with the serve job channel.
// ---------------------------------------------------------------------------

/// Opaque Lean heap object; only `*mut LeanObject` is ever held.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    /// `initialize_Body_FrameRaw` — module initializer for the proven raw
    /// framer's closure (`Body.FrameRaw` → `Body.Framing` → `Body.Smuggling` →
    /// `Body.Chunked`/`Body.ContentLength` → `Body.Hex`/`Body.Basic`). Guarded
    /// (idempotent) like every generated module init.
    fn initialize_Body_FrameRaw(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_frame_request]` — the raw accumulation buffer in, the
    /// encoded `Body.Framing.Outcome` verdict out: `[0]` = needMore,
    /// `[1, reason]` = reject, `[2, le64 consumed]` = complete.
    fn drorb_frame_request(input: *mut LeanObject) -> *mut LeanObject;
    /// Register/unregister a host thread with the Lean runtime (thread-local
    /// allocator state). Required before any allocation on a thread the runtime
    /// did not create; exactly the runtime's own worker discipline.
    fn lean_initialize_thread();
    fn lean_finalize_thread();

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — stateless.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Per-thread registration with the Lean runtime, dropped (unregistered) when
/// the thread exits — the blocking path runs a thread per connection, so the
/// guard must release the thread-local heap or every closed connection would
/// leak one.
struct FrameThreadGuard;

impl FrameThreadGuard {
    fn attach() -> Self {
        // SAFETY: the IO hosts run only after the serve gateway's boot
        // handshake, so the process-global runtime is initialized; registering
        // a foreign thread before its first runtime call is the documented
        // contract (and REQUIRED under LEAN_SMALL_ALLOCATOR — an unregistered
        // thread crashes on its first allocation).
        unsafe { lean_initialize_thread() };
        FrameThreadGuard
    }
}

impl Drop for FrameThreadGuard {
    fn drop(&mut self) {
        // SAFETY: registered in `attach` on this same thread; release on exit.
        unsafe { lean_finalize_thread() };
    }
}

thread_local! {
    static FRAME_THREAD: FrameThreadGuard = FrameThreadGuard::attach();
}

/// Register this thread with the Lean runtime (released on thread exit).
/// Shared by EVERY seam this crate crosses from IO threads — a thread must
/// register exactly once, so all seams (request framing here, the WebSocket
/// verdict in `ws.rs`) go through this one thread-local guard.
pub(crate) fn ensure_lean_thread() {
    FRAME_THREAD.with(|_| {});
}

/// Boot the process-global Lean runtime once, for TEST processes only (the
/// production binary boots it in the serve gateway). On a dedicated thread
/// that is then parked for the process lifetime, so harness threads register
/// themselves exactly like production IO threads. Shared by every test module
/// in this crate — the runtime must boot exactly once per process.
#[cfg(test)]
pub(crate) fn boot_test_runtime() {
    use std::sync::Once;
    static BOOT: Once = Once::new();
    BOOT.call_once(|| {
        unsafe extern "C" {
            fn lean_initialize_runtime_module();
            fn lean_io_mark_end_initialization();
        }
        let (tx, rx) = std::sync::mpsc::channel::<()>();
        std::thread::Builder::new()
            .name("test-runtime-boot".into())
            .spawn(move || {
                // SAFETY: standard runtime boot, once per process.
                unsafe {
                    lean_initialize_runtime_module();
                    lean_io_mark_end_initialization();
                }
                let _ = tx.send(());
                loop {
                    std::thread::park();
                }
            })
            .expect("failed to spawn the test boot thread");
        rx.recv().expect("test runtime boot failed");
    });
}

/// Ensure this thread may cross the framing seam: the thread is registered with
/// the runtime and the `Body.FrameRaw` module closure is initialized (once,
/// process-wide). `Body.FrameRaw` is not in the serve module's import closure,
/// so `lean_boot` does not initialize it; the first framing scan does.
fn ensure_frame_seam() {
    use std::sync::Once;
    static MODULE: Once = Once::new();
    // Register the thread FIRST — the module init below allocates on it.
    ensure_lean_thread();
    MODULE.call_once(|| {
        // SAFETY: standard guarded module init, on a registered thread, after
        // the process-global runtime is up (same pattern as the verified
        // outbound client's second-module boot).
        unsafe {
            let res = initialize_Body_FrameRaw(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Body_FrameRaw returned an IO error"
            );
            drorb_obj_dec(res);
        }
    });
}

/// Cross the proven framing decision with the raw buffer; returns the encoded
/// verdict bytes. Runs on the calling thread (registered on first use).
fn frame_verdict(data: &[u8]) -> Vec<u8> {
    ensure_frame_seam();
    // SAFETY: `drorb_frame_request` is the real `@[export]` symbol; the
    // argument is a fresh sarray the callee consumes, the result an owned
    // sarray copied out then released — created, consumed, and dropped on this
    // one thread.
    unsafe {
        let arg = drorb_sarray_of_bytes(data.as_ptr(), data.len());
        let out = drorb_frame_request(arg);
        let n = drorb_sarray_len(out);
        let v = std::slice::from_raw_parts(drorb_sarray_ptr(out), n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

/// Scan `data` for one complete HTTP/1.1 request (head through CRLFCRLF plus a
/// framed body). The boundary/reject decision is the proven core's
/// (`drorb_frame_request` = `Body.FrameRaw.frameRaw`); the host contributes
/// only the [`REQUEST_CAP`] resource bound. Pure: no IO, mutates nothing.
pub fn next_request(data: &[u8]) -> Frame {
    match frame_verdict(data).split_first() {
        // needMore — still subject to the host's resource cap: a buffer past
        // REQUEST_CAP with no complete request is refused, not grown.
        Some((&0, _)) => {
            if data.len() > REQUEST_CAP {
                Frame::Oversize
            } else {
                Frame::NeedMore
            }
        }
        // reject (the reason byte names which smuggling/malformation fired) —
        // a single, unsplittable fate: close the connection.
        Some((&1, _reason)) => Frame::Oversize,
        // complete: the next 8 octets are the consumed count, little-endian.
        Some((&2, le)) if le.len() == 8 => {
            let mut consumed = 0usize;
            for (i, b) in le.iter().enumerate() {
                consumed |= (*b as usize) << (8 * i);
            }
            // `frameRaw_bounded` proves consumed <= data.len(); a violation
            // here means the linked archive and this host disagree on the ABI —
            // fail closed rather than desync.
            if consumed > data.len() || consumed > REQUEST_CAP {
                Frame::Oversize
            } else {
                Frame::Complete(consumed)
            }
        }
        // Any other shape is an ABI mismatch: fail closed.
        _ => Frame::Oversize,
    }
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
                && n.iter()
                    .zip(name)
                    .all(|(a, b)| a.to_ascii_lowercase() == *b)
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

// ---------------------------------------------------------------------------
// Byte-identity gate: the seam-governed framing vs. the retired host framer.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod frame_identity {
    use super::*;

    /// The RETIRED host framer, kept verbatim as the byte-identity reference
    /// only — it no longer exists in the production binary (the proven core
    /// makes the framing decision). Every helper below is the pre-deploy code,
    /// unmodified.
    mod host_reference {
        use super::super::{Frame, REQUEST_CAP, find_ci};

        enum BodyFrame {
            Fixed(usize),
            Chunked,
            Reject,
        }

        fn header_values<'a>(head: &'a [u8], name: &[u8]) -> Vec<&'a [u8]> {
            let mut out = Vec::new();
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
                        && n.iter()
                            .zip(name)
                            .all(|(a, b)| a.to_ascii_lowercase() == *b)
                    {
                        let val = &v[1..];
                        let start = val
                            .iter()
                            .position(|&c| c != b' ' && c != b'\t')
                            .unwrap_or(val.len());
                        let end = val
                            .iter()
                            .rposition(|&c| c != b' ' && c != b'\t')
                            .map(|p| p + 1)
                            .unwrap_or(start);
                        out.push(&val[start..end]);
                    }
                }
                i = line_end + 2;
            }
            out
        }

        fn body_frame(head: &[u8]) -> BodyFrame {
            let te_chunked = header_values(head, b"transfer-encoding")
                .iter()
                .any(|te| find_ci(te, b"chunked").is_some());
            let mut cl_present = false;
            let mut cl_bad = false;
            let mut cl_val: Option<usize> = None;
            for cl in header_values(head, b"content-length") {
                cl_present = true;
                match std::str::from_utf8(cl)
                    .ok()
                    .map(str::trim)
                    .and_then(|s| s.parse::<usize>().ok())
                {
                    Some(n) => match cl_val {
                        Some(prev) if prev != n => cl_bad = true,
                        _ => cl_val = Some(n),
                    },
                    None => cl_bad = true,
                }
            }
            if te_chunked && cl_present {
                return BodyFrame::Reject;
            }
            if cl_bad {
                return BodyFrame::Reject;
            }
            if te_chunked {
                return BodyFrame::Chunked;
            }
            if let Some(n) = cl_val {
                return BodyFrame::Fixed(n);
            }
            BodyFrame::Fixed(0)
        }

        fn chunked_len(buf: &[u8], start: usize) -> Option<usize> {
            let mut i = start;
            loop {
                let nl = buf[i..].windows(2).position(|w| w == b"\r\n")? + i;
                let size_str = std::str::from_utf8(&buf[i..nl]).ok()?;
                let hex = size_str.split(';').next().unwrap_or("").trim();
                let size = usize::from_str_radix(hex, 16).ok()?;
                i = nl + 2;
                if size == 0 {
                    loop {
                        let end = buf[i..].windows(2).position(|w| w == b"\r\n")? + i;
                        if end == i {
                            return Some(end + 2 - start);
                        }
                        i = end + 2;
                    }
                }
                i += size;
                if i + 2 > buf.len() {
                    return None;
                }
                i += 2;
            }
        }

        pub fn next_request(data: &[u8]) -> Frame {
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
            match body_frame(&data[..head_end]) {
                BodyFrame::Reject => Frame::Oversize,
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
    }

    /// Boot the process-global Lean runtime once (the crate-shared test boot;
    /// the harness threads that call `next_request` register themselves
    /// exactly like production IO threads).
    fn boot_runtime_once() {
        crate::http::boot_test_runtime();
    }

    fn req(s: &str) -> Vec<u8> {
        s.as_bytes().to_vec()
    }

    /// The valid-request corpus: on every one of these (and every prefix of
    /// every one — each accumulation state the IO loops could observe) the
    /// seam-governed framing must equal the retired host framer exactly.
    fn valid_corpus() -> Vec<(&'static str, Vec<u8>)> {
        vec![
            ("get-noBody", req("GET / HTTP/1.1\r\nHost: a\r\n\r\n")),
            ("get-10", req("GET /x HTTP/1.0\r\n\r\n")),
            (
                "get-pipelined",
                req("GET /a HTTP/1.1\r\nHost: a\r\n\r\nGET /b HTTP/1.1\r\nHost: a\r\n\r\n"),
            ),
            (
                "post-cl0",
                req("POST / HTTP/1.1\r\nContent-Length: 0\r\n\r\n"),
            ),
            (
                "post-cl5",
                req("POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhello"),
            ),
            (
                "post-cl5-pipelined",
                req("POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhelloGET / HTTP/1.1\r\n\r\n"),
            ),
            (
                "post-cl5-short",
                req("POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhel"),
            ),
            (
                "cl-case-ws",
                req("POST / HTTP/1.1\r\ncOnTeNt-LeNgTh:   3  \r\n\r\nabc"),
            ),
            (
                "dup-cl-agreeing",
                req("POST / HTTP/1.1\r\nContent-Length: 3\r\nContent-Length: 3\r\n\r\nabc"),
            ),
            (
                "chunked-1",
                req("POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n"),
            ),
            (
                "chunked-2",
                req(
                    "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\nA\r\n0123456789\r\n0\r\n\r\n",
                ),
            ),
            (
                "chunked-partial",
                req("POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel"),
            ),
            (
                "chunked-pipelined",
                req(
                    "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi\r\n0\r\n\r\nGET / HTTP/1.1\r\n\r\n",
                ),
            ),
            (
                "chunked-ext",
                req(
                    "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n5;name=value\r\nhello\r\n0\r\n\r\n",
                ),
            ),
            (
                "chunked-trailer",
                req(
                    "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX-Trailer: v\r\n\r\n",
                ),
            ),
            ("partial-head", req("GET / HTTP/1.1\r\nHost: incompl")),
            ("empty", Vec::new()),
            (
                "obsolete-fold-untouched",
                req("GET / HTTP/1.1\r\nX-A: 1\r\nHost: a\r\n\r\n"),
            ),
        ]
    }

    /// Byte-identity over the valid corpus and every prefix, with the verdicts
    /// of both framers dumped to files for an external `cmp`.
    #[test]
    fn seam_matches_host_on_valid_corpus() {
        boot_runtime_once();
        let dir = std::path::Path::new("/tmp/drorb-frame-cmp");
        let _ = std::fs::create_dir_all(dir);
        let mut seam_dump = String::new();
        let mut host_dump = String::new();
        for (name, bytes) in valid_corpus() {
            for cut in 0..=bytes.len() {
                let pfx = &bytes[..cut];
                let seam = next_request(pfx);
                let host = host_reference::next_request(pfx);
                seam_dump.push_str(&format!("{name}[..{cut}] => {seam:?}\n"));
                host_dump.push_str(&format!("{name}[..{cut}] => {host:?}\n"));
                assert_eq!(seam, host, "framing diverged on {name}[..{cut}]");
            }
        }
        std::fs::write(dir.join("seam.txt"), seam_dump).unwrap();
        std::fs::write(dir.join("host.txt"), host_dump).unwrap();
    }

    /// The RFC MUSTs: the smuggling shapes are rejected by BOTH framers (the
    /// host framer already rejected them; the proven decision must keep doing
    /// so on the live wire).
    #[test]
    fn smuggling_shapes_reject() {
        boot_runtime_once();
        let cases: Vec<(&str, Vec<u8>)> = vec![
            (
                "clte",
                req(
                    "POST / HTTP/1.1\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\nSMUGGL",
                ),
            ),
            (
                "tecl",
                req(
                    "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nContent-Length: 6\r\n\r\n0\r\n\r\nSMUGGL",
                ),
            ),
            (
                "dup-cl-conflicting",
                req("POST / HTTP/1.1\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello!"),
            ),
            (
                "non-integer-cl",
                req("POST / HTTP/1.1\r\nContent-Length: 5x\r\n\r\nhello"),
            ),
        ];
        for (name, bytes) in cases {
            assert_eq!(
                next_request(&bytes),
                Frame::Oversize,
                "{name}: the proven framer must reject"
            );
            assert_eq!(
                host_reference::next_request(&bytes),
                Frame::Oversize,
                "{name}: the reference must agree (RFC MUST)"
            );
        }
    }

    /// Where the proven decision is STRICTER than the retired host framer —
    /// named divergences, all in the reject-more direction on non-valid
    /// messages (RFC 9112 §6.1/§6.3 allow or require refusal of every one):
    /// an unimplemented transfer coding and chunked-not-final. None of these
    /// shapes is in the valid corpus; the old framer ACCEPTED them.
    ///
    /// (Chunk-size extensions and chunked trailers are NOT divergences: both
    /// framers accept them — RFC 7230 §4.1.1/§4.1.2 REQUIRE a recipient to —
    /// via the proven `Chunked.decodeStreamExt`. They live in the valid
    /// corpus above, boundary-checked against the reference on every prefix.)
    #[test]
    fn strict_only_rejections_are_named() {
        boot_runtime_once();
        // Transfer-Encoding: gzip — old: framed as no-body; new: reject.
        assert_eq!(
            next_request(&req("POST / HTTP/1.1\r\nTransfer-Encoding: gzip\r\n\r\n")),
            Frame::Oversize
        );
        // chunked, gzip (chunked not final) — old: chunked; new: reject.
        assert_eq!(
            next_request(&req(
                "POST / HTTP/1.1\r\nTransfer-Encoding: chunked, gzip\r\n\r\n0\r\n\r\n"
            )),
            Frame::Oversize
        );
        // A non-hex chunk-size token stays a reject (framing-safety: never
        // parsed as data) even with extension tolerance in place.
        assert_eq!(
            next_request(&req(
                "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\nZZ\r\nhello\r\n0\r\n\r\n"
            )),
            Frame::Oversize
        );
    }

    /// The killed footgun: a Content-Length near `usize::MAX` made the old
    /// framer compute `head_end + n` — an arithmetic overflow (a panic under
    /// overflow checks; a WRAPPED, too-small "complete" boundary without them,
    /// i.e. a desync). The proven decision computes over `Nat`: the verdict is
    /// simply NeedMore until the resource cap refuses the connection.
    #[test]
    fn huge_content_length_cannot_overflow() {
        boot_runtime_once();
        let huge = req(&format!(
            "POST / HTTP/1.1\r\nContent-Length: {}\r\n\r\nx",
            usize::MAX
        ));
        assert_eq!(next_request(&huge), Frame::NeedMore);
        let old = std::panic::catch_unwind(|| host_reference::next_request(&huge));
        match old {
            Err(_) => {} // overflow panic — the crash-on-long-input footgun
            Ok(frame) => assert_ne!(
                frame,
                Frame::NeedMore,
                "old framer neither panicked nor desynced?"
            ),
        }
    }

    /// The resource cap stays host-side: a buffer past REQUEST_CAP with no
    /// complete request is refused by both framers.
    #[test]
    fn request_cap_is_host_side() {
        boot_runtime_once();
        let mut big = req("GET /");
        big.resize(REQUEST_CAP + 2, b'a');
        assert_eq!(next_request(&big), Frame::Oversize);
        assert_eq!(host_reference::next_request(&big), Frame::Oversize);
    }
}
