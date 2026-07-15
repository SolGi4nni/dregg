//! The RFC 6455 WebSocket lane, host side: the opening **handshake** (§4) and
//! the **frame-level codec** (§5) — header decode, structural validation, and
//! server-frame encode.
//!
//! The handshake needs SHA-1 for the `Sec-WebSocket-Accept` token, which the
//! proven core does not ship; it is handshake framing, not data path. The frame
//! codec here is the wire grammar only: a STREAMING header decoder whose state
//! is one fixed 14-byte buffer (a header may straddle any number of recvs, and
//! `MAX_HEADER` is the largest header RFC 6455 permits, so no input schedule
//! can grow it). The host owns only that byte ACCUMULATION: the frame-parse
//! VERDICT on the accumulated prefix — needMore / fail-1002 (§5.1/§5.2/§5.5
//! structural rules) / the decoded header — is the proven core's
//! (`Ws.Decode.decodeHeader`, crossed via `drorb_ws_header`), and the §7.4
//! close-code registry decision is `Ws.Decode.closeCodeOk` (via
//! `drorb_ws_close_ok`). The OUTBOUND direction is governed the same way:
//! every server-frame header this host writes is the proven core's
//! (`Ws.Encode.frameHeader` via `drorb_ws_encode_header` — mask bit provably
//! zero, minimal-rung ladder, proven decode∘encode round trip), and the close
//! frame is `Ws.Encode.encodeClose` via `drorb_ws_encode_close`; the host
//! contributes only the payload memcpy. Message reassembly — the bounded,
//! stateful part — lives in [`crate::ws_assembly`].
//!
//! ## The RFC 7692 permessage-deflate extension seam (host layer)
//!
//! Bare RFC 6455 §5.2 requires RSV1=RSV2=RSV3=0, and the proven header verdict
//! enforces exactly that. RFC 7692 REDEFINES the RSV1 bit: once the
//! `permessage-deflate` extension is negotiated in the handshake, RSV1 on the
//! first frame of a data message is the "per-message compressed" marker, and
//! is no longer a violation. This host models that faithfully WITHOUT weakening
//! the proven verdict: when — and only when — the handshake negotiated
//! permessage-deflate, the header decoder PEELS the RSV1 bit off byte 0 before
//! crossing the proven seam and carries it as [`FrameHeader::rsv1`]. Everything
//! the proven decoder governs (RSV2/RSV3, opcode, length, mask, control shape)
//! still governs; only the one bit RFC 7692 reassigns is handled in the host
//! layer. When the extension is NOT negotiated the bit is left in place and the
//! proven verdict rejects it (1002) exactly as before. Negotiation itself lives
//! in [`upgrade_response`]; the inflate/deflate of message payloads (a trusted
//! `flate2`/miniz_oxide codec, the same principled-TCB posture as the reactor
//! gzip seam) lives in [`crate::ws_assembly`].

/// SHA-1 (RFC 3174), one-shot. Used ONLY for the handshake accept token; never on
/// the WebSocket data path.
fn sha1(msg: &[u8]) -> [u8; 20] {
    let (mut h0, mut h1, mut h2, mut h3, mut h4): (u32, u32, u32, u32, u32) =
        (0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0);
    let mut m = msg.to_vec();
    let bits = (msg.len() as u64) * 8;
    m.push(0x80);
    while m.len() % 64 != 56 {
        m.push(0);
    }
    m.extend_from_slice(&bits.to_be_bytes());
    for chunk in m.chunks_exact(64) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let (mut a, mut b, mut c, mut d, mut e) = (h0, h1, h2, h3, h4);
        for (i, wi) in w.iter().enumerate() {
            let (f, k): (u32, u32) = match i {
                0..=19 => ((b & c) | ((!b) & d), 0x5A827999),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
                _ => (b ^ c ^ d, 0xCA62C1D6),
            };
            let t = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(*wi);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = t;
        }
        h0 = h0.wrapping_add(a);
        h1 = h1.wrapping_add(b);
        h2 = h2.wrapping_add(c);
        h3 = h3.wrapping_add(d);
        h4 = h4.wrapping_add(e);
    }
    let mut out = [0u8; 20];
    for (i, h) in [h0, h1, h2, h3, h4].into_iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&h.to_be_bytes());
    }
    out
}

/// Base64 (RFC 4648) encode.
fn base64(input: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity((input.len() + 2) / 3 * 4);
    for chunk in input.chunks(3) {
        let b = [
            chunk[0],
            *chunk.get(1).unwrap_or(&0),
            *chunk.get(2).unwrap_or(&0),
        ];
        let v = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | (b[2] as u32);
        out.push(T[((v >> 18) & 63) as usize] as char);
        out.push(T[((v >> 12) & 63) as usize] as char);
        out.push(if chunk.len() > 1 {
            T[((v >> 6) & 63) as usize] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            T[(v & 63) as usize] as char
        } else {
            '='
        });
    }
    out
}

/// Case-insensitive substring search over a byte buffer.
fn ci_find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&i| {
        hay[i..i + needle.len()]
            .iter()
            .zip(needle)
            .all(|(a, b)| a.to_ascii_lowercase() == b.to_ascii_lowercase())
    })
}

/// Is this request an RFC 6455 WebSocket upgrade? The lane discriminator — the
/// TCP analogue of the proven Ingress fork on the h2c preface.
pub fn is_ws_upgrade(head: &[u8]) -> bool {
    ci_find(head, b"sec-websocket-key:").is_some() && ci_find(head, b"websocket").is_some()
}

/// The RFC 6455 magic GUID appended to the client key before hashing.
const GUID: &[u8] = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

/// The negotiated per-connection WebSocket extension state (RFC 7692). Built by
/// [`upgrade_response`] from the client's `Sec-WebSocket-Extensions` offer and
/// carried for the connection's life to [`crate::ws_assembly::WsEngine`], which
/// applies it to inbound RSV1 handling and outbound compression.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WsConfig {
    /// `permessage-deflate` was negotiated: RSV1 is the per-message compressed
    /// marker and data messages may be compressed in both directions.
    pub deflate: bool,
    /// The client's compressor MUST reset its LZ77 window per message (our
    /// decompressor may therefore reset per message too).
    pub client_no_context_takeover: bool,
    /// Our compressor MUST reset its LZ77 window per message.
    pub server_no_context_takeover: bool,
}

/// Parse the client's `Sec-WebSocket-Extensions` offer and decide the negotiated
/// `permessage-deflate` parameters (RFC 7692 §5, §7). The offer is a
/// comma-separated list of extensions, each a semicolon-separated
/// name/parameter list; a client may send several `permessage-deflate` offers
/// (fallbacks) and the server accepts the first it can satisfy.
///
/// This host's `flate2`/miniz_oxide codec is fixed at the maximal 15-bit LZ77
/// window in BOTH directions (the window-bits knob needs a zlib backend we do
/// not link). So:
///   - a `server_max_window_bits=N` with `N < 15` REQUIRES our compressor to
///     shrink its window, which it cannot; such an offer is skipped (the next
///     offer, or plain no-extension, is used);
///   - `client_max_window_bits` bounds the CLIENT's compressor, which our
///     15-bit decompressor decodes at any value ≤ 15 — so it is accepted and
///     never echoed back (echoing it would force the client's window and is
///     unnecessary here);
///   - `{server,client}_no_context_takeover` are both honorable — we reset the
///     relevant stream per message — and are echoed when offered.
///
/// Returns the response `Sec-WebSocket-Extensions` header VALUE (without the
/// header name or CRLF) alongside the [`WsConfig`], or `None` when no offer can
/// be satisfied (the connection then runs uncompressed).
fn negotiate_deflate(head: &[u8]) -> Option<(String, WsConfig)> {
    let hi = ci_find(head, b"sec-websocket-extensions:")?;
    let mut p = hi + b"sec-websocket-extensions:".len();
    let start = p;
    while p < head.len() && head[p] != b'\r' && head[p] != b'\n' {
        p += 1;
    }
    let value = std::str::from_utf8(&head[start..p]).ok()?;

    // Each comma-separated element is one extension offer.
    for offer in value.split(',') {
        let mut parts = offer.split(';').map(str::trim);
        let name = parts.next().unwrap_or("");
        if !name.eq_ignore_ascii_case("permessage-deflate") {
            continue;
        }
        let mut cfg = WsConfig {
            deflate: true,
            client_no_context_takeover: false,
            server_no_context_takeover: false,
        };
        let mut server_window_ok = true;
        let mut resp = String::from("permessage-deflate");
        for param in parts {
            if param.is_empty() {
                continue;
            }
            let (key, val) = match param.split_once('=') {
                Some((k, v)) => (k.trim(), Some(v.trim().trim_matches('"'))),
                None => (param, None),
            };
            match key {
                "server_no_context_takeover" => {
                    cfg.server_no_context_takeover = true;
                    resp.push_str("; server_no_context_takeover");
                }
                "client_no_context_takeover" => {
                    cfg.client_no_context_takeover = true;
                    resp.push_str("; client_no_context_takeover");
                }
                "server_max_window_bits" => {
                    // We cannot shrink our compressor's window below 15. Any
                    // value the client pins here we cannot honor; skip this
                    // offer. (A bare `server_max_window_bits` with no value is
                    // malformed per RFC 7692 §7.1.2.2 — also skip.)
                    let ok = matches!(val.and_then(|v| v.parse::<u8>().ok()), Some(15));
                    if !ok {
                        server_window_ok = false;
                    }
                }
                "client_max_window_bits" => {
                    // Bounds the CLIENT's compressor window; our 15-bit
                    // decompressor decodes any value ≤ 15. Accept silently.
                    // A value outside 8..=15 is malformed — skip this offer.
                    if let Some(v) = val {
                        match v.parse::<u8>() {
                            Ok(8..=15) => {}
                            _ => server_window_ok = false,
                        }
                    }
                }
                // Unknown parameter — an offer we do not understand; skip it.
                _ => server_window_ok = false,
            }
        }
        if server_window_ok {
            return Some((resp, cfg));
        }
    }
    None
}

/// Build the 101 Switching Protocols response for a WebSocket upgrade request,
/// or `None` if it carries no `Sec-WebSocket-Key`. The accept token is
/// `base64(sha1(key ++ GUID))` (RFC 6455 §4.2.2). If the request offers a
/// `permessage-deflate` extension this host can satisfy, the response carries
/// the negotiated `Sec-WebSocket-Extensions` header and the returned
/// [`WsConfig`] records it (RFC 7692); otherwise the connection runs
/// uncompressed.
pub fn upgrade_response(head: &[u8]) -> Option<(Vec<u8>, WsConfig)> {
    let ki = ci_find(head, b"sec-websocket-key:")?;
    let mut p = ki + b"sec-websocket-key:".len();
    while p < head.len() && (head[p] == b' ' || head[p] == b'\t') {
        p += 1;
    }
    let start = p;
    while p < head.len() && head[p] != b'\r' && head[p] != b'\n' {
        p += 1;
    }
    let key = &head[start..p];
    let mut cat = Vec::with_capacity(key.len() + GUID.len());
    cat.extend_from_slice(key);
    cat.extend_from_slice(GUID);
    let accept = base64(&sha1(&cat));

    let (ext_header, cfg) = match negotiate_deflate(head) {
        Some((value, cfg)) => (format!("Sec-WebSocket-Extensions: {value}\r\n"), cfg),
        None => (String::new(), WsConfig::default()),
    };

    Some((
        format!(
            "HTTP/1.1 101 Switching Protocols\r\n\
             Upgrade: websocket\r\n\
             Connection: Upgrade\r\n\
             Sec-WebSocket-Accept: {accept}\r\n\
             {ext_header}\r\n"
        )
        .into_bytes(),
        cfg,
    ))
}

// ---------------------------------------------------------------------------
// The proven frame-parse seam: `drorb_ws_header` / `drorb_ws_close_ok`
// (`Ws.Decode`). The header decoder below keeps only the byte ACCUMULATION;
// every verdict it reports — needMore / fail-1002 / a decoded header — is the
// proven core's (`Ws.Decode.decodeHeader`), crossed per accumulation step.
//
// These declarations are ws.rs's own (http.rs keeps its own set for the
// request-framing seam): the crossing is made from the same IO threads, whose
// runtime registration is shared through `http::ensure_lean_thread`.
// ---------------------------------------------------------------------------

/// Opaque Lean heap object; only `*mut LeanObject` is ever held.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    /// `initialize_Ws_Decode` — module initializer for the proven header
    /// decoder's closure (`Ws.Decode` → `Ws.Length`/`Ws.Frame` → `Ws.Basic`).
    /// Guarded (idempotent) like every generated module init.
    fn initialize_Ws_Decode(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_ws_header]` — the accumulated header prefix in, the
    /// encoded `Ws.Decode.Verdict` out: `[0]` = needMore, `[1, hi, lo]` = bad
    /// (close code big-endian), `[2, fin, opcode, used, mask4, len8]` = done
    /// (length little-endian).
    fn drorb_ws_header(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_ws_close_ok]` — the §7.4 close-code registry decision:
    /// 1 iff the code may appear on the wire.
    fn drorb_ws_close_ok(code: u32) -> u8;
    /// `initialize_Ws_Encode` — module initializer for the proven outbound
    /// encoder's closure (`Ws.Encode` → `Ws.Decode`/`Ws.Mask`/`Ws.ReassemblyClose`).
    /// Guarded (idempotent) like every generated module init.
    fn initialize_Ws_Encode(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_ws_encode_header]` — the §5.2 SERVER-frame header for
    /// (fin, opcode nibble, payload length): mask bit zero (§5.1), the proven
    /// minimal-rung length ladder, 2–10 octets
    /// (`Ws.Encode.frameHeader` / `frameHeaderExport_size_bounds`).
    fn drorb_ws_encode_header(fin: u8, op: u8, len: u64) -> *mut LeanObject;
    /// `@[export drorb_ws_encode_close]` — the complete §5.5.1 close frame
    /// carrying `code` big-endian with an empty reason: exactly 4 octets
    /// (`Ws.Encode.encodeClose` / `encodeCloseExport_size`).
    fn drorb_ws_encode_close(code: u32) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — stateless.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Ensure this thread may cross the WebSocket verdict seams: the thread is
/// registered with the runtime (the crate-wide guard) and the `Ws.Decode` +
/// `Ws.Encode` module closures are initialized (once, process-wide — they are
/// not in the serve module's import closure, so `lean_boot` does not
/// initialize them).
fn ensure_ws_seam() {
    use std::sync::Once;
    static MODULE: Once = Once::new();
    // Register the thread FIRST — the module init below allocates on it.
    crate::http::ensure_lean_thread();
    MODULE.call_once(|| {
        // SAFETY: standard guarded module init, on a registered thread, after
        // the process-global runtime is up (same pattern as the request-framing
        // seam's module boot).
        unsafe {
            let res = initialize_Ws_Decode(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Ws_Decode returned an IO error"
            );
            drorb_obj_dec(res);
            let res = initialize_Ws_Encode(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Ws_Encode returned an IO error"
            );
            drorb_obj_dec(res);
        }
    });
}

/// Cross the proven header verdict with the accumulated prefix; returns the
/// encoded verdict bytes. Runs on the calling thread (registered on first use).
fn header_verdict(prefix: &[u8]) -> Vec<u8> {
    ensure_ws_seam();
    // SAFETY: `drorb_ws_header` is the real `@[export]` symbol; the argument is
    // a fresh sarray the callee consumes, the result an owned sarray copied out
    // then released — created, consumed, and dropped on this one thread.
    unsafe {
        let arg = drorb_sarray_of_bytes(prefix.as_ptr(), prefix.len());
        let out = drorb_ws_header(arg);
        let n = drorb_sarray_len(out);
        let v = std::slice::from_raw_parts(drorb_sarray_ptr(out), n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

// ---------------------------------------------------------------------------
// RFC 6455 §5 frame codec: streaming header decoder + server-frame encoder.
// ---------------------------------------------------------------------------

/// Frame opcodes (RFC 6455 §5.2). Values 0x3–0x7 and 0xB–0xF are reserved and
/// refused at decode.
pub const OP_CONT: u8 = 0x0;
pub const OP_TEXT: u8 = 0x1;
pub const OP_BINARY: u8 = 0x2;
pub const OP_CLOSE: u8 = 0x8;
pub const OP_PING: u8 = 0x9;
pub const OP_PONG: u8 = 0xA;

/// Close codes this endpoint sends (RFC 6455 §7.4.1).
pub const CLOSE_PROTOCOL_ERROR: u16 = 1002;
pub const CLOSE_INVALID_PAYLOAD: u16 = 1007;
pub const CLOSE_TOO_BIG: u16 = 1009;

/// May `code` appear on the wire in a close frame (RFC 6455 §7.4)? 0–999 are
/// unused; 1004–1006 and 1015 are reserved and MUST NOT be sent on the wire;
/// 1016–2999 are reserved for future protocol revisions; 1012–1014 are
/// registered post-6455; 3000–4999 are registered/private use.
///
/// The decision is the proven core's (`Ws.Decode.closeCodeOk`, with the
/// reserved codes pinned refused by theorem), crossed per close frame.
pub fn close_code_ok(code: u16) -> bool {
    ensure_ws_seam();
    // SAFETY: a scalar-only `@[export]` call on a registered thread.
    unsafe { drorb_ws_close_ok(code as u32) != 0 }
}

/// A decoded frame header (§5.2). The payload has NOT been read yet; `mask` is
/// the client masking key the payload bytes must be XOR-unmasked with (§5.3).
#[derive(Clone, Copy)]
pub struct FrameHeader {
    pub fin: bool,
    pub opcode: u8,
    pub len: u64,
    pub mask: [u8; 4],
    /// The RFC 7692 RSV1 "per-message compressed" bit. Always `false` unless
    /// `permessage-deflate` was negotiated (the decoder only peels it then);
    /// under bare RFC 6455 an RSV1 frame is a §5.2 violation the proven verdict
    /// rejects before a header is ever produced.
    pub rsv1: bool,
}

/// The longest header §5.2 permits: 2 fixed + 8 extended-length + 4 mask bytes.
pub const MAX_HEADER: usize = 14;

/// One `HeaderDecoder::step` outcome.
pub enum HeaderStep {
    /// Input exhausted mid-header; the partial header is retained, feed more.
    NeedMore,
    /// A complete, structurally valid header; `.1` input bytes were consumed.
    Done(FrameHeader, usize),
    /// A structural violation; fail the connection with this close code.
    Bad(u16),
}

/// Streaming frame-header decoder. Accumulates header bytes across reads into
/// a FIXED `MAX_HEADER`-byte buffer — never a growing one. The VERDICT on the
/// accumulated prefix — needMore, fail with 1002 (§5.2 RSV ≠ 0, a reserved
/// opcode, §5.1 missing mask, §5.5 control shape, §5.2 extended-length top
/// bit), or a decoded header — is the proven core's `Ws.Decode.decodeHeader`,
/// crossed each step:
///   - `Ws.Decode.decodeHeader_extend` (verdict stability) makes the
///     accumulate-and-retry schedule sound: a decided verdict never changes
///     when more bytes arrive, on any recv split;
///   - `Ws.Decode.no_needMore_of_14` (progress) means a full 14-byte buffer is
///     always decided, so the fixed accumulator can never stall;
///   - `Ws.Decode.done_used_bounds` bounds `used` by the accumulated prefix,
///     so the consumed-count arithmetic below cannot underflow or overrun.
/// A verdict outside those proven shapes means the linked archive and this
/// host disagree on the ABI — every such arm fails closed (1002).
///
/// When `rsv1_ok` (the connection negotiated permessage-deflate), the RSV1 bit
/// of byte 0 is the RFC 7692 per-message-compressed marker rather than a §5.2
/// violation: it is peeled off before the proven verdict is crossed and
/// reported in [`FrameHeader::rsv1`]. RSV2/RSV3 and every other structural rule
/// remain the proven verdict's.
pub struct HeaderDecoder {
    buf: [u8; MAX_HEADER],
    have: usize,
    /// permessage-deflate negotiated: treat RSV1 as the compressed marker.
    rsv1_ok: bool,
}

impl HeaderDecoder {
    pub fn new() -> Self {
        HeaderDecoder::with_deflate(false)
    }

    /// Construct a decoder that treats RSV1 as the RFC 7692 compressed marker
    /// (peeled before the proven verdict) iff `rsv1_ok`.
    pub fn with_deflate(rsv1_ok: bool) -> Self {
        HeaderDecoder {
            buf: [0; MAX_HEADER],
            have: 0,
            rsv1_ok,
        }
    }

    /// Feed input bytes; on `Done` the decoder has reset itself for the next
    /// frame. `Bad` is terminal — the caller fails the connection.
    ///
    /// `Done(hdr, n)` reports the header-owned byte count `n` CONSUMED FROM
    /// THIS `input` (earlier header bytes were consumed by earlier steps);
    /// bytes past the header stay the caller's (payload).
    pub fn step(&mut self, input: &[u8]) -> HeaderStep {
        // Accumulate greedily up to the fixed ceiling; the fill is pure byte
        // shuffling — which of these bytes are header vs payload is decided
        // below by the proven core, and the input pointer advances only by
        // the header bytes the verdict claims.
        let prev = self.have;
        let take = (MAX_HEADER - self.have).min(input.len());
        self.buf[self.have..self.have + take].copy_from_slice(&input[..take]);
        self.have += take;

        // RFC 7692: with permessage-deflate negotiated, the RSV1 bit of byte 0
        // is the per-message compressed marker, not a §5.2 violation. Peel it
        // off before crossing the proven verdict (which enforces RSV=0), and
        // remember it for the decoded header. RSV2/RSV3 stay for the proven
        // verdict to reject. Without the extension the bit is left in place and
        // the proven verdict rejects it, exactly as bare RFC 6455 requires.
        let rsv1 = self.rsv1_ok && self.have >= 1 && (self.buf[0] & 0x40) != 0;
        let mut probe = self.buf;
        if rsv1 {
            probe[0] &= !0x40;
        }
        let v = header_verdict(&probe[..self.have]);
        match v.split_first() {
            Some((&0, rest)) if rest.is_empty() => {
                if self.have == MAX_HEADER {
                    // `no_needMore_of_14`: the proven decoder never returns
                    // needMore on a full buffer. ABI mismatch — fail closed.
                    HeaderStep::Bad(CLOSE_PROTOCOL_ERROR)
                } else {
                    // needMore with a non-full buffer implies the fill took
                    // ALL of `input`; the caller reads more and re-steps.
                    HeaderStep::NeedMore
                }
            }
            Some((&1, code)) if code.len() == 2 => {
                HeaderStep::Bad(u16::from_be_bytes([code[0], code[1]]))
            }
            Some((&2, rest)) if rest.len() == 15 => {
                let fin = rest[0] != 0;
                let opcode = rest[1];
                let used = rest[2] as usize;
                let mask = [rest[3], rest[4], rest[5], rest[6]];
                let mut len = 0u64;
                for (i, b) in rest[7..15].iter().enumerate() {
                    len |= (*b as u64) << (8 * i);
                }
                // `done_used_bounds` proves prev < used <= have (the previous
                // step's needMore means the header needs more than `prev`
                // octets). A violation is an ABI mismatch — fail closed
                // rather than desync the stream.
                if used <= prev || used > self.have {
                    return HeaderStep::Bad(CLOSE_PROTOCOL_ERROR);
                }
                self.have = 0; // reset for the next frame
                HeaderStep::Done(
                    FrameHeader {
                        fin,
                        opcode,
                        len,
                        mask,
                        rsv1,
                    },
                    used - prev,
                )
            }
            // Any other shape is an ABI mismatch: fail closed.
            _ => HeaderStep::Bad(CLOSE_PROTOCOL_ERROR),
        }
    }
}

/// Encode one SERVER frame (unmasked, §5.1) onto `out`, minimal-length form.
///
/// The header octets are the proven core's (`Ws.Encode.frameHeader`, crossed
/// via `drorb_ws_encode_header`): the mask bit provably zero
/// (`frameHeader_unmasked`), the length on the proven minimal rung
/// (`encodeFrame_canonical`), and the whole frame proven to round-trip through
/// the inbound `Ws.Decode.decodeHeader` + `Ws.Mask` unmask back to exactly
/// (fin, opcode, payload) (`encode_decode_roundtrip`). The payload bytes ride
/// verbatim after the header — `Ws.Encode.encodeFrame_eq` proves the frame
/// factors as header ++ payload, so this host's contribution is a memcpy,
/// never a header decision.
pub fn encode_frame_into(out: &mut Vec<u8>, fin: bool, opcode: u8, payload: &[u8]) {
    ensure_ws_seam();
    // SAFETY: a scalar-in, owned-sarray-out `@[export]` call on a registered
    // thread; the result is copied out then released on this one thread.
    unsafe {
        let hdr = drorb_ws_encode_header(fin as u8, opcode, payload.len() as u64);
        let n = drorb_sarray_len(hdr);
        // `frameHeaderExport_size_bounds`: a header is 2–10 octets. Any other
        // shape means the linked archive and this host disagree on the ABI —
        // stop rather than write a desyncing frame onto the wire.
        assert!(
            (2..=10).contains(&n),
            "ws encode-header ABI mismatch: {n} octets"
        );
        out.extend_from_slice(std::slice::from_raw_parts(drorb_sarray_ptr(hdr), n));
        drorb_obj_dec(hdr);
    }
    out.extend_from_slice(payload);
}

/// Encode one SERVER frame with the RFC 7692 RSV1 "per-message compressed" bit
/// set (`rsv1 = true`) or clear (`rsv1 = false`, identical to
/// [`encode_frame_into`]). The header octets are still the proven core's
/// (`Ws.Encode.frameHeader`, RSV provably zero); when compression is in effect
/// the host sets the ONE bit RFC 7692 reassigns on byte 0, on top of the proven
/// header — the outbound analogue of the inbound RSV1 peel. Only the first
/// frame of a compressed data message carries it; continuation and control
/// frames never do.
pub fn encode_frame_ext_into(out: &mut Vec<u8>, fin: bool, opcode: u8, rsv1: bool, payload: &[u8]) {
    let start = out.len();
    encode_frame_into(out, fin, opcode, payload);
    if rsv1 {
        out[start] |= 0x40;
    }
}

/// Encode a close frame carrying `code` and an empty reason (§5.5.1). The
/// whole 4-octet frame is the proven core's (`Ws.Encode.encodeClose`, crossed
/// via `drorb_ws_encode_close`); `Ws.Encode.closeBody_encodeClose` proves the
/// emitted body round-trips through the proven inbound close-body verdict to
/// exactly `code`.
pub fn encode_close_into(out: &mut Vec<u8>, code: u16) {
    ensure_ws_seam();
    // SAFETY: as above — scalar in, owned sarray out, one thread.
    unsafe {
        let f = drorb_ws_encode_close(code as u32);
        let n = drorb_sarray_len(f);
        // `encodeCloseExport_size`: a close frame is exactly 4 octets.
        assert!(n == 4, "ws encode-close ABI mismatch: {n} octets");
        out.extend_from_slice(std::slice::from_raw_parts(drorb_sarray_ptr(f), n));
        drorb_obj_dec(f);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfc6455_accept_vector() {
        // RFC 6455 §1.3: key "dGhlIHNhbXBsZSBub25jZQ==" → accept
        // "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=".
        let head = b"GET /chat HTTP/1.1\r\nUpgrade: websocket\r\n\
                     Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\n";
        let (resp, cfg) = upgrade_response(head).unwrap();
        let resp = String::from_utf8(resp).unwrap();
        assert!(resp.contains("Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="));
        // No extension offered: the connection runs uncompressed.
        assert!(!cfg.deflate);
        assert!(!resp.to_lowercase().contains("sec-websocket-extensions"));
    }

    #[test]
    fn negotiates_permessage_deflate() {
        // A bare permessage-deflate offer is accepted and echoed.
        let head = b"GET / HTTP/1.1\r\nUpgrade: websocket\r\n\
                     Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\
                     Sec-WebSocket-Extensions: permessage-deflate\r\n\r\n";
        let (resp, cfg) = upgrade_response(head).unwrap();
        let resp = String::from_utf8(resp).unwrap();
        assert!(cfg.deflate);
        assert!(resp.contains("Sec-WebSocket-Extensions: permessage-deflate"));

        // client_max_window_bits (bare) is accepted, not echoed; context
        // takeover params are honored and echoed.
        let head = b"GET / HTTP/1.1\r\nUpgrade: websocket\r\n\
                     Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\
                     Sec-WebSocket-Extensions: permessage-deflate; \
                     client_max_window_bits; server_no_context_takeover\r\n\r\n";
        let (resp, cfg) = upgrade_response(head).unwrap();
        let resp = String::from_utf8(resp).unwrap();
        assert!(cfg.deflate && cfg.server_no_context_takeover);
        assert!(resp.contains("server_no_context_takeover"));
        assert!(!resp.contains("client_max_window_bits"));

        // A server_max_window_bits=10 offer we cannot honor is declined; with no
        // fallback offer the connection runs uncompressed.
        let head = b"GET / HTTP/1.1\r\nUpgrade: websocket\r\n\
                     Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\
                     Sec-WebSocket-Extensions: permessage-deflate; \
                     server_max_window_bits=10\r\n\r\n";
        let (resp, cfg) = upgrade_response(head).unwrap();
        let resp = String::from_utf8(resp).unwrap();
        assert!(!cfg.deflate);
        assert!(!resp.to_lowercase().contains("sec-websocket-extensions"));

        // A fallback offer after an unsatisfiable one is taken.
        let head = b"GET / HTTP/1.1\r\nUpgrade: websocket\r\n\
                     Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\
                     Sec-WebSocket-Extensions: permessage-deflate; \
                     server_max_window_bits=10, permessage-deflate\r\n\r\n";
        let (_, cfg) = upgrade_response(head).unwrap();
        assert!(cfg.deflate);
    }

    /// Mask a client payload (test helper; the server never masks).
    fn masked(payload: &[u8], mask: [u8; 4]) -> Vec<u8> {
        payload
            .iter()
            .enumerate()
            .map(|(i, &b)| b ^ mask[i & 3])
            .collect()
    }

    /// Build a client (masked) frame.
    fn client_frame(fin: bool, opcode: u8, payload: &[u8]) -> Vec<u8> {
        let mask = [0x37, 0xfa, 0x21, 0x3d];
        let mut f = vec![if fin { 0x80 } else { 0x00 } | opcode];
        let n = payload.len();
        if n <= 125 {
            f.push(0x80 | n as u8);
        } else if n <= 0xFFFF {
            f.push(0x80 | 126);
            f.extend_from_slice(&(n as u16).to_be_bytes());
        } else {
            f.push(0x80 | 127);
            f.extend_from_slice(&(n as u64).to_be_bytes());
        }
        f.extend_from_slice(&mask);
        f.extend_from_slice(&masked(payload, mask));
        f
    }

    #[test]
    fn header_streams_across_arbitrary_splits() {
        crate::http::boot_test_runtime();
        // §1.3 example: masked "Hello" text frame, fed one byte at a time.
        let frame = client_frame(true, OP_TEXT, b"Hello");
        let mut dec = HeaderDecoder::new();
        let mut done = None;
        for (i, b) in frame.iter().enumerate() {
            match dec.step(std::slice::from_ref(b)) {
                HeaderStep::NeedMore => {}
                HeaderStep::Done(h, used) => {
                    done = Some((h, i, used));
                    break;
                }
                HeaderStep::Bad(_) => panic!("valid header refused"),
            }
        }
        let (h, at, used) = done.expect("header never completed");
        assert!(h.fin && h.opcode == OP_TEXT && h.len == 5);
        assert_eq!((at, used), (5, 1)); // 2 fixed + 4 mask = 6 header bytes
    }

    #[test]
    fn header_rejects_rsv_unmasked_and_reserved_opcode() {
        crate::http::boot_test_runtime();
        for bad in [
            vec![0xC1, 0x80], // RSV1 set
            vec![0x81, 0x05], // unmasked client frame
            vec![0x83, 0x80], // reserved opcode 0x3
            vec![0x09, 0x80], // fragmented ping (FIN=0, control)
            vec![0x89, 0xFE], // ping with 126-byte payload
        ] {
            match HeaderDecoder::new().step(&bad) {
                HeaderStep::Bad(CLOSE_PROTOCOL_ERROR) => {}
                _ => panic!("structural violation admitted: {bad:02x?}"),
            }
        }
    }

    #[test]
    fn close_code_registry() {
        crate::http::boot_test_runtime();
        for ok in [1000u16, 1002, 1003, 1007, 1011, 1014, 3000, 4999] {
            assert!(close_code_ok(ok), "{ok} wrongly refused");
        }
        for bad in [0u16, 999, 1004, 1005, 1006, 1015, 1016, 1100, 2000, 2999] {
            assert!(!close_code_ok(bad), "{bad} wrongly admitted");
        }
    }

    /// The RETIRED host header decoder and close-code registry, kept verbatim
    /// as the byte-identity reference: the seam-governed codec must report
    /// exactly these verdicts on every input schedule.
    mod host_reference {
        use super::super::{
            CLOSE_PROTOCOL_ERROR, FrameHeader, HeaderStep, MAX_HEADER, OP_BINARY, OP_CLOSE,
            OP_CONT, OP_PING, OP_PONG, OP_TEXT,
        };

        pub fn close_code_ok(code: u16) -> bool {
            matches!(code, 1000..=1003 | 1007..=1014 | 3000..=4999)
        }

        /// The RETIRED host frame encoder, verbatim — the byte-identity
        /// reference for the seam-governed `encode_frame_into`.
        pub fn encode_frame_into(out: &mut Vec<u8>, fin: bool, opcode: u8, payload: &[u8]) {
            out.push(if fin { 0x80 } else { 0x00 } | opcode);
            let n = payload.len();
            if n <= 125 {
                out.push(n as u8);
            } else if n <= 0xFFFF {
                out.push(126);
                out.extend_from_slice(&(n as u16).to_be_bytes());
            } else {
                out.push(127);
                out.extend_from_slice(&(n as u64).to_be_bytes());
            }
            out.extend_from_slice(payload);
        }

        /// The RETIRED close-frame construction, verbatim.
        pub fn encode_close_into(out: &mut Vec<u8>, code: u16) {
            encode_frame_into(out, true, OP_CLOSE, &code.to_be_bytes());
        }

        pub struct HeaderDecoder {
            buf: [u8; MAX_HEADER],
            have: usize,
        }

        impl HeaderDecoder {
            pub fn new() -> Self {
                HeaderDecoder {
                    buf: [0; MAX_HEADER],
                    have: 0,
                }
            }

            pub fn step(&mut self, input: &[u8]) -> HeaderStep {
                let mut used = 0usize;
                while self.have < 2 {
                    if used == input.len() {
                        return HeaderStep::NeedMore;
                    }
                    self.buf[self.have] = input[used];
                    self.have += 1;
                    used += 1;
                }
                let b0 = self.buf[0];
                let b1 = self.buf[1];
                if b0 & 0x70 != 0 {
                    return HeaderStep::Bad(CLOSE_PROTOCOL_ERROR);
                }
                let opcode = b0 & 0x0f;
                if !matches!(
                    opcode,
                    OP_CONT | OP_TEXT | OP_BINARY | OP_CLOSE | OP_PING | OP_PONG
                ) {
                    return HeaderStep::Bad(CLOSE_PROTOCOL_ERROR);
                }
                if b1 & 0x80 == 0 {
                    return HeaderStep::Bad(CLOSE_PROTOCOL_ERROR);
                }
                let fin = b0 & 0x80 != 0;
                let len7 = b1 & 0x7f;
                if opcode >= OP_CLOSE && (!fin || len7 > 125) {
                    return HeaderStep::Bad(CLOSE_PROTOCOL_ERROR);
                }
                let ext: usize = match len7 {
                    126 => 2,
                    127 => 8,
                    _ => 0,
                };
                let need = 2 + ext + 4;
                while self.have < need {
                    if used == input.len() {
                        return HeaderStep::NeedMore;
                    }
                    self.buf[self.have] = input[used];
                    self.have += 1;
                    used += 1;
                }
                let len: u64 = match len7 {
                    126 => u16::from_be_bytes([self.buf[2], self.buf[3]]) as u64,
                    127 => {
                        let v = u64::from_be_bytes(self.buf[2..10].try_into().unwrap());
                        if v & (1 << 63) != 0 {
                            return HeaderStep::Bad(CLOSE_PROTOCOL_ERROR);
                        }
                        v
                    }
                    n => n as u64,
                };
                let mask: [u8; 4] = self.buf[need - 4..need].try_into().unwrap();
                self.have = 0;
                HeaderStep::Done(
                    FrameHeader {
                        fin,
                        opcode,
                        len,
                        mask,
                        rsv1: false,
                    },
                    used,
                )
            }
        }
    }

    /// Render a step outcome for transcript comparison.
    fn show_step(s: &HeaderStep) -> String {
        match s {
            HeaderStep::NeedMore => "NeedMore".into(),
            HeaderStep::Bad(c) => format!("Bad({c})"),
            HeaderStep::Done(h, used) => format!(
                "Done(fin={} opcode={:#x} len={} mask={:02x?} used={used})",
                h.fin, h.opcode, h.len, h.mask
            ),
        }
    }

    /// The header corpus: valid frames on every length rung (with payload
    /// bytes trailing, so consumed-count accounting is exercised), §5.2
    /// receiver-tolerated non-canonical lengths, and every §5.1/§5.2/§5.5
    /// violation class the retired decoder refused.
    fn header_corpus() -> Vec<(&'static str, Vec<u8>)> {
        const MASK: [u8; 4] = [0x37, 0xfa, 0x21, 0x3d];
        let big = vec![0u8; 66000];
        let mut corpus: Vec<(&'static str, Vec<u8>)> = vec![
            ("text-hello", client_frame(true, OP_TEXT, b"Hello")),
            ("text-empty", client_frame(true, OP_TEXT, b"")),
            ("binary-nonfin", client_frame(false, OP_BINARY, b"frag")),
            ("cont-fin", client_frame(true, OP_CONT, b"tail")),
            ("ping-125", client_frame(true, OP_PING, &[0x61; 125])),
            ("close-code", client_frame(true, OP_CLOSE, &[0x03, 0xe8])),
            ("text-16bit-rung", client_frame(true, OP_TEXT, &[0x62; 126])),
            (
                "binary-16bit-max",
                client_frame(true, OP_BINARY, &vec![7u8; 65535]),
            ),
            ("binary-64bit-rung", client_frame(true, OP_BINARY, &big)),
        ];
        // Non-canonical 64-bit rung carrying length 5 (tolerated on receive).
        let mut noncanon = vec![0x82, 0x80 | 127];
        noncanon.extend_from_slice(&5u64.to_be_bytes());
        noncanon.extend_from_slice(&MASK);
        noncanon.extend_from_slice(&[1, 2, 3, 4, 5]);
        corpus.push(("binary-64bit-noncanonical", noncanon));
        // Non-canonical 16-bit rung carrying length 0.
        let mut noncanon16 = vec![0x81, 0x80 | 126, 0, 0];
        noncanon16.extend_from_slice(&MASK);
        corpus.push(("text-16bit-noncanonical-zero", noncanon16));
        // Violations: RSV bits, every reserved opcode, unmasked, fragmented
        // controls, oversize controls, MSB-set 64-bit length.
        corpus.push(("rsv1", vec![0xC1, 0x80, 0, 0, 0, 0]));
        corpus.push(("rsv2", vec![0xA1, 0x80, 0, 0, 0, 0]));
        corpus.push(("rsv3", vec![0x91, 0x80, 0, 0, 0, 0]));
        for (name, op) in [
            ("op3", 0x3u8),
            ("op4", 0x4),
            ("op5", 0x5),
            ("op6", 0x6),
            ("op7", 0x7),
            ("opB", 0xB),
            ("opC", 0xC),
            ("opD", 0xD),
            ("opE", 0xE),
            ("opF", 0xF),
        ] {
            corpus.push((
                Box::leak(format!("reserved-{name}").into_boxed_str()),
                vec![0x80 | op, 0x81, 0x37, 0xfa, 0x21, 0x3d, 0x00],
            ));
        }
        corpus.push(("unmasked", vec![0x81, 0x05, b'h', b'e', b'l', b'l', b'o']));
        corpus.push(("fragmented-close", vec![0x08, 0x80, 0, 0, 0, 0]));
        corpus.push(("fragmented-ping", vec![0x09, 0x80, 0, 0, 0, 0]));
        corpus.push(("fragmented-pong", vec![0x0A, 0x80, 0, 0, 0, 0]));
        corpus.push(("ping-126", vec![0x89, 0xFE, 0, 126, 0, 0, 0, 0]));
        corpus.push(("close-126", vec![0x88, 0xFE, 0, 126, 0, 0, 0, 0]));
        let mut msb = vec![0x82, 0x80 | 127];
        msb.extend_from_slice(&(1u64 << 63 | 1).to_be_bytes());
        msb.extend_from_slice(&MASK);
        corpus.push(("msb-64bit-length", msb));
        corpus
    }

    /// **Byte-identity of the frame-parse verdict.** Over the whole corpus,
    /// under BOTH accumulation schedules the engine can produce — one bulk
    /// step per prefix cut, and a fresh byte-by-byte stream — the seam-governed
    /// decoder must report exactly the retired host decoder's verdict sequence.
    /// Both transcripts are dumped for an external `cmp`.
    #[test]
    fn seam_matches_host_on_header_corpus() {
        crate::http::boot_test_runtime();
        let dir = std::path::Path::new("/tmp/drorb-ws-cmp");
        let _ = std::fs::create_dir_all(dir);
        let mut seam_dump = String::new();
        let mut host_dump = String::new();
        for (name, bytes) in header_corpus() {
            // Cap the scan window: everything past the largest header plus a
            // couple of payload bytes is decided identically (headers are at
            // most 14 bytes; the big-payload entries only exercise `used`).
            let window = bytes.len().min(MAX_HEADER + 3);
            // (a) one bulk step per prefix cut, fresh decoders each time.
            for cut in 0..=window {
                let pfx = &bytes[..cut];
                let seam = HeaderDecoder::new().step(pfx);
                let host = host_reference::HeaderDecoder::new().step(pfx);
                seam_dump.push_str(&format!("{name}[..{cut}] => {}\n", show_step(&seam)));
                host_dump.push_str(&format!("{name}[..{cut}] => {}\n", show_step(&host)));
                assert_eq!(
                    show_step(&seam),
                    show_step(&host),
                    "bulk verdict diverged on {name}[..{cut}]"
                );
            }
            // (b) a fresh byte-by-byte stream: the full outcome sequence.
            let mut seam_dec = HeaderDecoder::new();
            let mut host_dec = host_reference::HeaderDecoder::new();
            for (i, b) in bytes[..window].iter().enumerate() {
                let seam = seam_dec.step(std::slice::from_ref(b));
                let host = host_dec.step(std::slice::from_ref(b));
                seam_dump.push_str(&format!("{name}@{i} => {}\n", show_step(&seam)));
                host_dump.push_str(&format!("{name}@{i} => {}\n", show_step(&host)));
                assert_eq!(
                    show_step(&seam),
                    show_step(&host),
                    "streamed verdict diverged on {name}@{i}"
                );
                if matches!(seam, HeaderStep::Bad(_) | HeaderStep::Done(..)) {
                    break;
                }
            }
        }
        std::fs::write(dir.join("seam.txt"), seam_dump).unwrap();
        std::fs::write(dir.join("host.txt"), host_dump).unwrap();
    }

    /// **Byte-identity of the close-code registry**, exhaustively: all 65536
    /// codes, the proven decision vs the retired host `matches!`.
    #[test]
    fn seam_matches_host_on_every_close_code() {
        crate::http::boot_test_runtime();
        let dir = std::path::Path::new("/tmp/drorb-ws-cmp");
        let _ = std::fs::create_dir_all(dir);
        let mut seam_dump = String::with_capacity(1 << 17);
        let mut host_dump = String::with_capacity(1 << 17);
        for code in 0..=u16::MAX {
            let seam = close_code_ok(code);
            let host = host_reference::close_code_ok(code);
            seam_dump.push_str(&format!("{code}={}\n", seam as u8));
            host_dump.push_str(&format!("{code}={}\n", host as u8));
            assert_eq!(seam, host, "close-code registry diverged on {code}");
        }
        std::fs::write(dir.join("seam-close.txt"), seam_dump).unwrap();
        std::fs::write(dir.join("host-close.txt"), host_dump).unwrap();
    }

    /// **Byte-identity of the outbound encoder.** Across every ladder-rung
    /// boundary, every opcode, and both FIN values, the seam-governed encoder
    /// must produce exactly the retired host encoder's bytes — and the close
    /// frame must match over all 65536 codes. (No §5.5 skips: both encoders
    /// are total in the same way; the control-shape guarantee lives in the
    /// callers and in the proven round-trip's hypotheses.)
    #[test]
    fn seam_matches_host_on_encoded_frames() {
        crate::http::boot_test_runtime();
        let lens: [usize; 12] = [
            0, 1, 2, 124, 125, 126, 127, 1000, 65534, 65535, 65536, 70000,
        ];
        for &n in &lens {
            let payload = vec![0xA5u8; n];
            for opcode in [OP_CONT, OP_TEXT, OP_BINARY, OP_CLOSE, OP_PING, OP_PONG] {
                for fin in [true, false] {
                    let (mut seam, mut host) = (Vec::new(), Vec::new());
                    encode_frame_into(&mut seam, fin, opcode, &payload);
                    host_reference::encode_frame_into(&mut host, fin, opcode, &payload);
                    assert_eq!(
                        seam, host,
                        "encoded frame diverged: fin={fin} opcode={opcode:#x} len={n}"
                    );
                }
            }
        }
        for code in 0..=u16::MAX {
            let (mut seam, mut host) = (Vec::new(), Vec::new());
            encode_close_into(&mut seam, code);
            host_reference::encode_close_into(&mut host, code);
            assert_eq!(seam, host, "close frame diverged on code {code}");
        }
    }
}
