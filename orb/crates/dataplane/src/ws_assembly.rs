//! Bounded, streaming WebSocket message engine (RFC 6455 §5.4–§5.6, §7, §8.1).
//!
//! One [`WsEngine`] lives for the WHOLE connection — decoder state persists
//! across recvs, so frames and messages may straddle any number of socket
//! reads. Its memory ceiling is fixed by construction:
//!
//!   - a 14-byte header accumulator ([`crate::ws::HeaderDecoder`]),
//!   - a 125-byte control-frame buffer (§5.5 caps control payloads at 125),
//!   - ONE message reassembly buffer hard-capped at [`MAX_MESSAGE`] — a data
//!     frame whose declared length would push the message over the cap is
//!     refused with close 1009 BEFORE any of its payload is buffered,
//!
//! and `feed` is a flat loop (no recursion anywhere), so no input schedule can
//! grow host state or the call stack. This module keeps only the BUFFERING;
//! every decision is the proven core's, crossed per event:
//!
//!   - §5.1 client masking, §5.2 RSV=0 / defined opcodes / 63-bit length,
//!     §5.5 control shape — at header time, by the proven header verdict
//!     (`Ws.Decode.decodeHeader` via the [`crate::ws`] decoder);
//!   - §5.4 fragmentation discipline + the reassembly bound — at header time,
//!     by the proven admission verdict (`Ws.ReassemblyAdmit.admit` via
//!     `drorb_ws_admit`): a continuation needs an open message, a new data
//!     opcode may not preempt one, control frames may interleave, and the cap
//!     refusal (1009) lands before buffering — proven to agree with the
//!     `Ws.Reassembly.step` fragmentation FSM exactly;
//!   - §5.6/§8.1 text messages are valid UTF-8, validated INCREMENTALLY by
//!     the proven automaton (`Ws.Utf8.run` via `drorb_ws_utf8`): the host
//!     holds one watermark-state word, a character may straddle fragment or
//!     recv boundaries, a definite violation fails fast (close 1007) — proven
//!     equivalent to the whole-string RFC 3629 spec on every chunk schedule;
//!   - §5.5.1/§7 close frames: 2-byte code, registry-valid code, UTF-8
//!     reason, and the handshake reply (echo the peer's code) — by the proven
//!     close-body verdict (`Ws.ReassemblyClose.closeBody` via
//!     `drorb_ws_close_body`); a protocol failure sends the matching code
//!     before the connection drops.
//!
//! Complete data messages are echoed back as one unfragmented server frame;
//! pings are answered with payload-echoing pongs (§5.5.2/§5.5.3).
//!
//! ## RFC 7692 permessage-deflate
//!
//! When the handshake negotiated permessage-deflate ([`crate::ws::WsConfig`]),
//! a data message whose FIRST frame carries RSV1 (the compressed marker peeled
//! by [`crate::ws::HeaderDecoder`]) has a DEFLATE-compressed payload. Such a
//! message is buffered compressed (the reassembly cap and per-frame masking are
//! unchanged), then, at delivery, its concatenated payload — with the RFC 7692
//! §7.2.2 trailing `00 00 FF FF` re-appended — is inflated; UTF-8 validation of
//! a text message runs on the DECOMPRESSED bytes. Echoes are compressed when
//! the extension is in effect (RSV1 set, the trailing `00 00 FF FF` stripped
//! per §7.2.1). Context takeover — whether the inflate/deflate LZ77 window
//! carries across messages — follows the negotiated `no_context_takeover`
//! parameters. The DEFLATE codec itself is `flate2`/miniz_oxide: a trusted,
//! well-audited data transform, the same principled-TCB posture as the reactor
//! gzip seam (`crate::gzip`) and the crypto FFI — NOT verified. The framing,
//! masking, fragmentation, close, and UTF-8 DECISIONS around it stay the proven
//! core's; only the byte-for-byte compression transform is trusted.

use crate::ws::{
    CLOSE_INVALID_PAYLOAD, CLOSE_PROTOCOL_ERROR, FrameHeader, HeaderDecoder, HeaderStep, OP_BINARY,
    OP_CLOSE, OP_PING, OP_PONG, OP_TEXT, WsConfig, encode_close_into, encode_frame_ext_into,
    encode_frame_into,
};
use flate2::{Compress, Compression, Decompress, FlushCompress, FlushDecompress, Status};

/// Hard ceiling on one reassembled message (all fragments together). A frame
/// that would exceed it is refused with close 1009 (§7.4.1) before buffering.
/// Passed to the proven admission verdict as the cap on every crossing.
pub const MAX_MESSAGE: usize = 16 << 20; // 16 MiB

/// Keep the reassembly buffer's retained capacity modest between messages so
/// one large message does not pin its high-water allocation for the
/// connection's remaining life.
const RETAIN_CAP: usize = 64 * 1024;

/// What the connection loop must do after a `feed`.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Flow {
    /// Keep reading; a frame or message may still be mid-flight.
    Continue,
    /// A close frame is in the output (handshake reply or protocol failure):
    /// write the pending bytes, then close the connection. Terminal.
    Shut,
}

#[derive(Clone, Copy)]
enum State {
    /// Between frames / mid-header.
    Header,
    /// Mid-payload: `got` of `hdr.len` bytes consumed so far.
    Payload { hdr: FrameHeader, got: u64 },
}

// ---------------------------------------------------------------------------
// The proven reassembly/UTF-8/close seams: `drorb_ws_admit` (the §5.4 + cap
// admission verdict, `Ws.ReassemblyAdmit`), `drorb_ws_utf8` (the incremental
// RFC 3629 automaton, `Ws.Utf8`), `drorb_ws_close_body` (the §5.5.1/§7.4
// close-body verdict, `Ws.ReassemblyClose`). The engine below keeps only the
// byte BUFFERING; every admission, UTF-8, and close decision it reports —
// and every `msg_op` state transition it applies — is the proven core's.
//
// These declarations are ws_assembly.rs's own (ws.rs keeps its own set for
// the header seam): the crossing is made from the same IO threads, whose
// runtime registration is shared through `http::ensure_lean_thread`.
// ---------------------------------------------------------------------------

/// Opaque Lean heap object; only `*mut LeanObject` is ever held.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    /// `initialize_Ws_ReassemblyAdmit` / `initialize_Ws_ReassemblyClose` —
    /// module initializers for the verdicts' closures (they pull `Ws.Utf8`,
    /// `Ws.Reassembly`, `Ws.Decode` transitively). Guarded (idempotent) like
    /// every generated module init.
    fn initialize_Ws_ReassemblyAdmit(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    fn initialize_Ws_ReassemblyClose(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_ws_admit]` — the header-time admission verdict:
    /// (msg-state, buffered, opcode, fin, declared len, cap) in; packed
    /// verdict out. High 32 bits `2` = accept (bits 8–11 the message opcode
    /// while the payload streams, bits 4–7 the state after the frame, bit 0
    /// delivery on completion); `1` = reject (low 16 bits the close code).
    fn drorb_ws_admit(m: u32, buf_len: u64, opcode: u32, fin: u8, len: u64, cap: u64) -> u64;
    /// `@[export drorb_ws_utf8]` — the incremental UTF-8 automaton: watermark
    /// state + newly unmasked payload octets in, next state out (`0` = at a
    /// character boundary, `1–7` = mid-character, `0xFF` = definite
    /// violation).
    fn drorb_ws_utf8(state: u32, chunk: *mut LeanObject) -> u32;
    /// `@[export drorb_ws_close_body]` — the close-body verdict: the
    /// reassembled close payload in, packed verdict out (bits 16–31: `0` =
    /// echo an empty close, `1` = echo the code in bits 0–15, `2` = fail the
    /// connection with the code in bits 0–15).
    fn drorb_ws_close_body(payload: *mut LeanObject) -> u32;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — stateless.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Ensure this thread may cross the reassembly seams: the thread is
/// registered with the runtime (the crate-wide guard) and the two verdict
/// modules' closures are initialized (once, process-wide — they are not in
/// the serve module's import closure, so `lean_boot` does not initialize
/// them).
fn ensure_ws_assembly_seam() {
    use std::sync::Once;
    static MODULE: Once = Once::new();
    // Register the thread FIRST — the module init below allocates on it.
    crate::http::ensure_lean_thread();
    MODULE.call_once(|| {
        // SAFETY: standard guarded module init, on a registered thread, after
        // the process-global runtime is up (same pattern as the header seam's
        // module boot in ws.rs).
        unsafe {
            let res = initialize_Ws_ReassemblyAdmit(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Ws_ReassemblyAdmit returned an IO error"
            );
            drorb_obj_dec(res);
            let res = initialize_Ws_ReassemblyClose(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Ws_ReassemblyClose returned an IO error"
            );
            drorb_obj_dec(res);
        }
    });
}

/// Cross the proven admission verdict with the engine's between-frames state
/// and the arriving header's fields. Runs on the calling thread (registered
/// on first use).
fn ws_admit(msg_op: u8, buf_len: u64, opcode: u8, fin: bool, len: u64) -> u64 {
    ensure_ws_assembly_seam();
    // SAFETY: a scalar-only `@[export]` call on a registered thread.
    unsafe {
        drorb_ws_admit(
            msg_op as u32,
            buf_len,
            opcode as u32,
            fin as u8,
            len,
            MAX_MESSAGE as u64,
        )
    }
}

/// Advance the proven UTF-8 automaton over newly unmasked payload octets.
fn ws_utf8(state: u32, chunk: &[u8]) -> u32 {
    ensure_ws_assembly_seam();
    // SAFETY: the argument is a fresh sarray the callee consumes; the result
    // is a scalar — created and consumed on this one thread.
    unsafe {
        let arg = drorb_sarray_of_bytes(chunk.as_ptr(), chunk.len());
        drorb_ws_utf8(state, arg)
    }
}

/// Cross the proven close-body verdict with a complete close payload.
fn ws_close_body(payload: &[u8]) -> u32 {
    ensure_ws_assembly_seam();
    // SAFETY: as `ws_utf8` — fresh consumed sarray in, scalar out.
    unsafe {
        let arg = drorb_sarray_of_bytes(payload.as_ptr(), payload.len());
        drorb_ws_close_body(arg)
    }
}

// ---------------------------------------------------------------------------
// RFC 7692 permessage-deflate codec (TRUSTED `flate2`/miniz_oxide, NOT proven).
//
// The window is fixed at the maximal 15 bits in both directions — the negotiation
// in `crate::ws::upgrade_response` accepts no offer that would need a smaller one.
// ---------------------------------------------------------------------------

/// The RFC 7692 §7.2.2 sync-flush marker: an empty DEFLATE block. The sender
/// strips it; the receiver re-appends it before inflating.
const DEFLATE_TAIL: [u8; 4] = [0x00, 0x00, 0xFF, 0xFF];

/// Per-connection inflate context (the client → server direction).
struct Inflater {
    dec: Decompress,
    /// Reset the LZ77 window each message (client_no_context_takeover).
    reset_each: bool,
}

impl Inflater {
    fn new(reset_each: bool) -> Self {
        // zlib_header = false: a raw DEFLATE stream (RFC 7692 uses no zlib wrapper).
        Inflater {
            dec: Decompress::new(false),
            reset_each,
        }
    }

    /// Inflate one complete compressed message payload into `out`, appending the
    /// §7.2.2 sync-flush tail first. Bounded by `cap` (a decompression-bomb
    /// guard); returns `Err(())` on a corrupt stream or an over-cap expansion.
    ///
    /// Draining idiom (the mirror of [`deflate_sync`]): a permessage-deflate
    /// stream carries no BFINAL, so `StreamEnd` never arrives — completion is
    /// "all input consumed AND the last `decompress_vec` left spare room", i.e.
    /// it had no more to emit. Letting `decompress_vec` own the output buffer
    /// (rather than a fixed scratch array copied out per call) keeps the loop
    /// off any buffer-boundary special case.
    fn inflate(&mut self, compressed: &[u8], cap: usize, out: &mut Vec<u8>) -> Result<(), ()> {
        if self.reset_each {
            self.dec.reset(false);
        }
        let mut input = Vec::with_capacity(compressed.len() + DEFLATE_TAIL.len());
        input.extend_from_slice(compressed);
        input.extend_from_slice(&DEFLATE_TAIL);

        let start_in = self.dec.total_in();
        loop {
            // `decompress_vec` writes only into existing spare capacity and never
            // reallocates, so guarantee a nonzero margin before each call.
            if out.capacity() - out.len() < 4096 {
                out.reserve(64 * 1024);
            }
            let spare = out.capacity() - out.len();
            let consumed = (self.dec.total_in() - start_in) as usize;
            let before_out = self.dec.total_out();
            let status = self
                .dec
                .decompress_vec(&input[consumed..], out, FlushDecompress::None)
                .map_err(|_| ())?;
            let produced = (self.dec.total_out() - before_out) as usize;
            if out.len() > cap {
                return Err(());
            }
            let all_input_done = (self.dec.total_in() - start_in) as usize == input.len();
            if status == Status::StreamEnd {
                break;
            }
            if all_input_done && produced < spare {
                break;
            }
        }
        Ok(())
    }
}

/// Per-connection deflate context (the server → client direction).
struct Deflater {
    enc: Compress,
    /// Reset the LZ77 window each message (server_no_context_takeover).
    reset_each: bool,
}

/// Compress `data` through `enc` and terminate with a single DEFLATE sync flush
/// (the RFC 7692 §7.2.1 message boundary), appending the raw bytes (INCLUDING
/// the trailing `00 00 FF FF` marker) to `out`.
///
/// One loop feeding the whole message under `FlushCompress::Sync`, draining into
/// `out`'s spare capacity via `compress_vec`. The completion test is the zlib
/// idiom in its output-vector form: the flush is done once ALL input has been
/// consumed AND a call produced fewer bytes than the spare room it was given —
/// i.e. it did not fill the buffer, so nothing more is pending. A naive "stop
/// when a call emits nothing" is wrong (a `Sync` flush re-emits its marker every
/// call → non-termination), and a fixed scratch buffer whose size the output
/// happens to land on exactly is the boundary that corrupts the stream; letting
/// `compress_vec` own the buffer sidesteps both.
fn deflate_sync(enc: &mut Compress, data: &[u8], out: &mut Vec<u8>) {
    let start_in = enc.total_in();
    loop {
        // `compress_vec` writes only into existing spare capacity and never
        // reallocates, so guarantee a nonzero margin before each call.
        if out.capacity() - out.len() < 4096 {
            out.reserve(64 * 1024);
        }
        let spare = out.capacity() - out.len();
        let consumed = (enc.total_in() - start_in) as usize;
        let before_out = enc.total_out();
        enc.compress_vec(&data[consumed..], out, FlushCompress::Sync)
            .expect("flate2 in-memory compress");
        let produced = (enc.total_out() - before_out) as usize;
        let all_input_done = (enc.total_in() - start_in) as usize == data.len();
        if all_input_done && produced < spare {
            break;
        }
    }
}

impl Deflater {
    fn new(reset_each: bool) -> Self {
        Deflater {
            enc: Compress::new(Compression::default(), false),
            reset_each,
        }
    }

    /// Compress one complete message into `out` as an RFC 7692 §7.2.1 payload:
    /// a sync-flushed DEFLATE stream with the trailing `00 00 FF FF` removed.
    fn deflate(&mut self, data: &[u8], out: &mut Vec<u8>) {
        let start = out.len();
        deflate_sync(&mut self.enc, data, out);
        // Strip the trailing sync-flush marker (§7.2.1). An empty message
        // sync-flushes to `00 00 00 FF FF`, so the strip leaves a single `00` —
        // exactly the one octet the RFC requires for an empty compressed payload.
        let n = out.len();
        if n >= start + 4 && out[n - 4..] == DEFLATE_TAIL {
            out.truncate(n - 4);
        }
        if self.reset_each {
            self.enc.reset();
        }
    }
}

pub struct WsEngine {
    dec: HeaderDecoder,
    state: State,
    /// The inflate/deflate contexts, present iff permessage-deflate negotiated
    /// (RFC 7692). When both are `None` the engine behaves exactly as bare RFC
    /// 6455. Context takeover — whether each LZ77 window carries across messages
    /// — was baked into these at construction from the negotiated parameters.
    inflater: Option<Inflater>,
    deflater: Option<Deflater>,
    /// Whether the in-flight data message's opening frame carried RSV1 (its
    /// payload is DEFLATE-compressed). Meaningful only while a message is open.
    msg_compressed: bool,
    /// The bounded reassembly buffer for the in-flight data message.
    msg: Vec<u8>,
    /// Opcode of the in-flight data message; `0` (= continuation, which can
    /// never OPEN a message) means none is open (§5.4 state). Every value
    /// stored here is the proven admission verdict's `during`/`after` output.
    msg_op: u8,
    /// The admitted frame's after-completion state (the verdict's `after`).
    frame_after: u8,
    /// Whether the admitted frame's completion delivers a message (the
    /// verdict's `deliver`).
    frame_deliver: bool,
    /// The proven UTF-8 automaton's watermark state over `msg`: `0` = at a
    /// character boundary, `1–7` = mid-character (at most one partial
    /// character is ever pending). Only meaningful while `msg_op == OP_TEXT`.
    utf8: u32,
    /// Control-frame payload accumulator (§5.5: at most 125 bytes).
    ctl: [u8; 125],
    ctl_len: usize,
}

impl WsEngine {
    /// A bare RFC 6455 engine with no extension negotiated (uncompressed).
    pub fn new() -> Self {
        WsEngine::with_config(WsConfig::default())
    }

    /// An engine carrying the handshake's negotiated RFC 7692 state. When
    /// `cfg.deflate` the header decoder treats RSV1 as the compressed marker and
    /// the inflate/deflate contexts are live (their LZ77 windows carry across
    /// messages unless the negotiated `no_context_takeover` parameters say
    /// otherwise).
    pub fn with_config(cfg: WsConfig) -> Self {
        let (inflater, deflater) = if cfg.deflate {
            (
                Some(Inflater::new(cfg.client_no_context_takeover)),
                Some(Deflater::new(cfg.server_no_context_takeover)),
            )
        } else {
            (None, None)
        };
        WsEngine {
            dec: HeaderDecoder::with_deflate(cfg.deflate),
            state: State::Header,
            inflater,
            deflater,
            msg_compressed: false,
            msg: Vec::new(),
            msg_op: 0,
            frame_after: 0,
            frame_deliver: false,
            utf8: 0,
            ctl: [0; 125],
            ctl_len: 0,
        }
    }

    /// Feed one chunk of inbound bytes. Reply frames (echoes, pongs, closes)
    /// are appended to `out`; the caller writes them and, on [`Flow::Shut`],
    /// closes the connection. After `Shut`, remaining input is not processed
    /// (§7.1.7: fail the connection).
    pub fn feed(&mut self, mut input: &[u8], out: &mut Vec<u8>) -> Flow {
        loop {
            match self.state {
                State::Header => match self.dec.step(input) {
                    HeaderStep::NeedMore => return Flow::Continue,
                    HeaderStep::Bad(code) => return fail(out, code),
                    HeaderStep::Done(hdr, used) => {
                        input = &input[used..];
                        if let Err(code) = self.on_header(&hdr) {
                            return fail(out, code);
                        }
                        self.state = State::Payload { hdr, got: 0 };
                    }
                },
                State::Payload { hdr, got } => {
                    let take = ((hdr.len - got).min(input.len() as u64)) as usize;
                    let (chunk, rest) = input.split_at(take);
                    input = rest;
                    if take > 0 {
                        let base = got as usize;
                        if hdr.opcode >= OP_CLOSE {
                            // Control payload: fixed buffer (len ≤ 125 was
                            // enforced at the header, so this cannot overrun).
                            for (i, &b) in chunk.iter().enumerate() {
                                self.ctl[self.ctl_len + i] = b ^ hdr.mask[(base + i) & 3];
                            }
                            self.ctl_len += take;
                        } else {
                            // Data payload: unmask straight into the bounded
                            // reassembly buffer (its cap was enforced by the
                            // admission verdict, before any byte was
                            // buffered), then advance the proven UTF-8
                            // automaton over exactly the new octets.
                            let start = self.msg.len();
                            self.msg.extend(
                                chunk
                                    .iter()
                                    .enumerate()
                                    .map(|(i, &b)| b ^ hdr.mask[(base + i) & 3]),
                            );
                            // A compressed message buffers its DEFLATE bytes;
                            // UTF-8 is validated on the decompressed message at
                            // delivery, not on the compressed octets here.
                            if self.msg_op == OP_TEXT && !self.msg_compressed {
                                self.utf8 = ws_utf8(self.utf8, &self.msg[start..]);
                                if self.utf8 > 7 {
                                    // Definite violation — proven: no
                                    // continuation could make it valid.
                                    return fail(out, CLOSE_INVALID_PAYLOAD); // §8.1 fail fast
                                }
                            }
                        }
                    }
                    let got = got + take as u64;
                    if got < hdr.len {
                        self.state = State::Payload { hdr, got };
                        return Flow::Continue; // input exhausted mid-payload
                    }
                    self.state = State::Header;
                    if let Flow::Shut = self.on_frame(&hdr, out) {
                        return Flow::Shut;
                    }
                }
            }
        }
    }

    /// §5.4 fragmentation discipline + the reassembly bound, decided at
    /// header time — before any payload byte is buffered. The decision is the
    /// proven admission verdict's (`Ws.ReassemblyAdmit.admit`, proven to
    /// agree with the `Ws.Reassembly.step` FSM exactly); this method only
    /// stores the returned state transition.
    fn on_header(&mut self, h: &FrameHeader) -> Result<(), u16> {
        // RFC 7692 RSV1 discipline (the header decoder only ever sets `rsv1`
        // when permessage-deflate was negotiated): the compressed marker is
        // valid ONLY on the frame that OPENS a data message — a fresh TEXT or
        // BINARY. An RSV1 continuation, or an RSV1 control frame, is a protocol
        // error (§5.2 / RFC 7692 §6). `msg_op == 0` means no message is open.
        let opens_message = matches!(h.opcode, OP_TEXT | OP_BINARY) && self.msg_op == 0;
        if h.rsv1 && !opens_message {
            return Err(CLOSE_PROTOCOL_ERROR);
        }

        let v = ws_admit(self.msg_op, self.msg.len() as u64, h.opcode, h.fin, h.len);
        if v >> 32 == 2 {
            self.msg_op = ((v >> 8) & 0xF) as u8;
            self.frame_after = ((v >> 4) & 0xF) as u8;
            self.frame_deliver = v & 1 != 0;
            // Latch the message's compression state on its opening frame.
            if opens_message {
                self.msg_compressed = h.rsv1;
            }
            Ok(())
        } else {
            Err((v & 0xFFFF) as u16) // reject: 1002 (§5.4) or 1009 (§7.4.1)
        }
    }

    /// A complete frame (payload fully consumed): control replies and
    /// end-of-message echo.
    fn on_frame(&mut self, h: &FrameHeader, out: &mut Vec<u8>) -> Flow {
        match h.opcode {
            OP_CLOSE => self.on_close(out),
            OP_PING => {
                // §5.5.2/§5.5.3: a pong carrying the ping's payload.
                encode_frame_into(out, true, OP_PONG, &self.ctl[..self.ctl_len]);
                self.ctl_len = 0;
                Flow::Continue
            }
            OP_PONG => {
                self.ctl_len = 0; // §5.5.3: unsolicited pongs are ignored
                Flow::Continue
            }
            _ => {
                if !self.frame_deliver {
                    return Flow::Continue; // absorbed: more fragments coming
                }
                // Message complete (the verdict's `deliver`). Resolve the final
                // payload: if the message was compressed (RFC 7692), inflate the
                // buffered DEFLATE bytes (with the §7.2.2 tail re-appended);
                // `self.msg` then holds the plaintext.
                if self.msg_compressed {
                    let mut plain = Vec::new();
                    let inflater = self
                        .inflater
                        .as_mut()
                        .expect("permessage-deflate negotiated for a compressed message");
                    if inflater
                        .inflate(&self.msg, MAX_MESSAGE, &mut plain)
                        .is_err()
                    {
                        // Undecompressable or a decompression bomb (§7.2.2): fail.
                        return fail(out, CLOSE_INVALID_PAYLOAD);
                    }
                    // A compressed TEXT message is validated on the DECOMPRESSED
                    // bytes, whole (§5.6/§8.1): the proven automaton from a clean
                    // start must end back on a character boundary (state 0).
                    if self.msg_op == OP_TEXT && ws_utf8(0, &plain) != 0 {
                        return fail(out, CLOSE_INVALID_PAYLOAD);
                    }
                    std::mem::swap(&mut self.msg, &mut plain);
                } else if self.msg_op == OP_TEXT && self.utf8 != 0 {
                    // Uncompressed text must END on a character boundary: the
                    // incremental automaton must be back at state 0 — a clean
                    // prefix with a dangling partial character is still invalid
                    // UTF-8 (§5.6/§8.1).
                    return fail(out, CLOSE_INVALID_PAYLOAD);
                }

                // Echo. With permessage-deflate in effect, compress the plaintext
                // and set RSV1 (§7.2.1); otherwise send it verbatim.
                let op = self.msg_op;
                if let Some(deflater) = self.deflater.as_mut() {
                    let mut z = Vec::new();
                    deflater.deflate(&self.msg, &mut z);
                    encode_frame_ext_into(out, true, op, true, &z);
                } else {
                    encode_frame_into(out, true, op, &self.msg);
                }

                self.msg.clear();
                if self.msg.capacity() > RETAIN_CAP {
                    self.msg.shrink_to(RETAIN_CAP);
                }
                self.msg_op = self.frame_after; // idle again (the verdict's `after`)
                self.msg_compressed = false;
                self.utf8 = 0;
                Flow::Continue
            }
        }
    }

    /// A complete close frame (§5.5.1, §7.1.4): the proven close-body verdict
    /// decides — echo in kind, echo the peer's code, or fail the connection.
    fn on_close(&mut self, out: &mut Vec<u8>) -> Flow {
        let n = self.ctl_len;
        self.ctl_len = 0;
        let v = ws_close_body(&self.ctl[..n]);
        match v >> 16 {
            0 => {
                // No status code: reply in kind.
                encode_frame_into(out, true, OP_CLOSE, &[]);
                Flow::Shut
            }
            1 => {
                // Valid body: echo the peer's code (handshake reply).
                encode_close_into(out, (v & 0xFFFF) as u16);
                Flow::Shut
            }
            _ => fail(out, (v & 0xFFFF) as u16), // 1002 or 1007
        }
    }
}

/// Fail the WebSocket connection (§7.1.7): emit a close frame carrying `code`;
/// the caller writes it and drops the transport.
fn fail(out: &mut Vec<u8>, code: u16) -> Flow {
    encode_close_into(out, code);
    Flow::Shut
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ws::{CLOSE_PROTOCOL_ERROR, CLOSE_TOO_BIG, OP_BINARY, OP_CONT, close_code_ok};

    const MASK: [u8; 4] = [0xa5, 0x5a, 0x00, 0xff];

    fn client_frame(fin: bool, opcode: u8, payload: &[u8]) -> Vec<u8> {
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
        f.extend_from_slice(&MASK);
        f.extend(payload.iter().enumerate().map(|(i, &b)| b ^ MASK[i & 3]));
        f
    }

    fn server_frame(opcode: u8, payload: &[u8]) -> Vec<u8> {
        let mut f = Vec::new();
        encode_frame_into(&mut f, true, opcode, payload);
        f
    }

    // ---- RFC 7692 permessage-deflate test scaffolding -----------------------

    /// A permessage-deflate connection with context takeover in both directions.
    fn deflate_cfg() -> WsConfig {
        WsConfig {
            deflate: true,
            ..Default::default()
        }
    }

    /// Compress a message the way a permessage-deflate sender does — sync flush,
    /// trailing `00 00 FF FF` stripped — through the supplied (possibly
    /// context-retaining) compressor. Uses the same `deflate_sync` idiom as the
    /// engine, so the sender emulation cannot diverge from it.
    fn deflate_with(enc: &mut Compress, data: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();
        super::deflate_sync(enc, data, &mut out);
        let n = out.len();
        if n >= 4 && out[n - 4..] == [0, 0, 0xFF, 0xFF] {
            out.truncate(n - 4);
        }
        out
    }

    /// One-shot deflate through a fresh compressor (no context takeover).
    fn deflate_payload(data: &[u8]) -> Vec<u8> {
        deflate_with(&mut Compress::new(Compression::default(), false), data)
    }

    /// Inflate a received permessage-deflate payload through the supplied
    /// (possibly context-retaining) decompressor.
    fn inflate_with(dec: &mut Decompress, comp: &[u8]) -> Vec<u8> {
        let mut input = comp.to_vec();
        input.extend_from_slice(&[0, 0, 0xFF, 0xFF]);
        let mut out = Vec::new();
        let mut scratch = [0u8; 8192];
        let mut off = 0usize;
        loop {
            let ib = dec.total_in();
            let ob = dec.total_out();
            let st = dec
                .decompress(&input[off..], &mut scratch, FlushDecompress::None)
                .unwrap();
            let di = (dec.total_in() - ib) as usize;
            let dob = (dec.total_out() - ob) as usize;
            off += di;
            out.extend_from_slice(&scratch[..dob]);
            if st == Status::StreamEnd || (di == 0 && dob == 0) {
                break;
            }
        }
        out
    }

    /// Build a masked client data frame with RSV1 set (a compressed message's
    /// opening frame); `comp` is the already-compressed payload.
    fn client_frame_compressed(fin: bool, opcode: u8, comp: &[u8]) -> Vec<u8> {
        let mut f = client_frame(fin, opcode, comp);
        f[0] |= 0x40;
        f
    }

    /// Parse a single unfragmented server frame: (opcode, rsv1, payload).
    fn parse_server_frame(f: &[u8]) -> (u8, bool, Vec<u8>) {
        let b0 = f[0];
        let (op, rsv1) = (b0 & 0x0F, b0 & 0x40 != 0);
        let n7 = f[1] & 0x7F;
        let (n, mut p): (usize, usize) = match n7 {
            126 => (u16::from_be_bytes([f[2], f[3]]) as usize, 4),
            127 => (
                u64::from_be_bytes(f[2..10].try_into().unwrap()) as usize,
                10,
            ),
            k => (k as usize, 2),
        };
        assert_eq!(f[1] & 0x80, 0, "server frame must not be masked");
        let payload = f[p..p + n].to_vec();
        p += n;
        assert_eq!(p, f.len(), "trailing bytes after single server frame");
        (op, rsv1, payload)
    }

    #[test]
    fn deflate_roundtrip_text_echo() {
        crate::http::boot_test_runtime();
        let msg = "hello permessage-deflate — repeated. ".repeat(30);
        let comp = deflate_payload(msg.as_bytes());
        // The compressed payload really is smaller (the codec is doing work).
        assert!(comp.len() < msg.len());
        let frame = client_frame_compressed(true, OP_TEXT, &comp);
        let mut eng = WsEngine::with_config(deflate_cfg());
        let mut out = Vec::new();
        assert!(eng.feed(&frame, &mut out) == Flow::Continue);
        let (op, rsv1, payload) = parse_server_frame(&out);
        assert!(
            op == OP_TEXT && rsv1,
            "echo must be a compressed text frame"
        );
        let got = inflate_with(&mut Decompress::new(false), &payload);
        assert_eq!(got, msg.as_bytes());
    }

    #[test]
    fn deflate_binary_and_fragmented_message() {
        crate::http::boot_test_runtime();
        // A compressed message fragmented across three frames: only the first
        // carries RSV1; continuations carry the rest of the SAME deflate stream.
        let data: Vec<u8> = (0..5000u32).map(|i| (i % 7) as u8).collect();
        let comp = deflate_payload(&data);
        let (a, rest) = comp.split_at(comp.len() / 3);
        let (b, c) = rest.split_at(rest.len() / 2);
        let mut wire = client_frame_compressed(false, OP_BINARY, a);
        wire.extend(client_frame(false, OP_CONT, b));
        wire.extend(client_frame(true, OP_CONT, c));
        let mut eng = WsEngine::with_config(deflate_cfg());
        let mut out = Vec::new();
        assert!(eng.feed(&wire, &mut out) == Flow::Continue);
        let (op, rsv1, payload) = parse_server_frame(&out);
        assert!(op == OP_BINARY && rsv1);
        assert_eq!(inflate_with(&mut Decompress::new(false), &payload), data);
    }

    #[test]
    fn deflate_context_takeover_both_directions() {
        crate::http::boot_test_runtime();
        let mut eng = WsEngine::with_config(deflate_cfg());
        // Persistent client compressor (inbound takeover) + decompressor (the
        // server's echoes use outbound takeover).
        let mut cli_enc = Compress::new(Compression::default(), false);
        let mut cli_dec = Decompress::new(false);
        for msg in [
            &b"the quick brown fox"[..],
            &b"the quick brown fox jumps over"[..],
            &b"the quick brown fox jumps over the lazy dog"[..],
        ] {
            let comp = deflate_with(&mut cli_enc, msg);
            let frame = client_frame_compressed(true, OP_BINARY, &comp);
            let mut out = Vec::new();
            assert!(eng.feed(&frame, &mut out) == Flow::Continue);
            let (op, rsv1, payload) = parse_server_frame(&out);
            assert!(op == OP_BINARY && rsv1);
            assert_eq!(inflate_with(&mut cli_dec, &payload), msg);
        }
    }

    #[test]
    fn deflate_no_context_takeover_resets_each_message() {
        crate::http::boot_test_runtime();
        let cfg = WsConfig {
            deflate: true,
            client_no_context_takeover: true,
            server_no_context_takeover: true,
        };
        let mut eng = WsEngine::with_config(cfg);
        for msg in [&b"aaaabbbbcccc"[..], &b"ddddeeeeffff"[..]] {
            // Client resets each message (fresh compressor); server must too.
            let comp = deflate_payload(msg);
            let frame = client_frame_compressed(true, OP_TEXT, &comp);
            let mut out = Vec::new();
            assert!(eng.feed(&frame, &mut out) == Flow::Continue);
            let (op, rsv1, payload) = parse_server_frame(&out);
            assert!(op == OP_TEXT && rsv1);
            // Fresh decompressor each message: the echo must self-contain.
            assert_eq!(inflate_with(&mut Decompress::new(false), &payload), msg);
        }
    }

    #[test]
    fn deflate_empty_message_roundtrips() {
        crate::http::boot_test_runtime();
        let comp = deflate_payload(b"");
        let frame = client_frame_compressed(true, OP_TEXT, &comp);
        let mut eng = WsEngine::with_config(deflate_cfg());
        let mut out = Vec::new();
        assert!(eng.feed(&frame, &mut out) == Flow::Continue);
        let (op, rsv1, payload) = parse_server_frame(&out);
        assert!(op == OP_TEXT && rsv1);
        // A compressed empty payload is a single 0x00 octet (never truly empty).
        assert!(!payload.is_empty());
        assert!(inflate_with(&mut Decompress::new(false), &payload).is_empty());
    }

    #[test]
    fn uncompressed_message_on_deflate_connection_still_works() {
        crate::http::boot_test_runtime();
        // RSV1 clear: an uncompressed message on a deflate-negotiated connection
        // is valid; the server may still compress its echo.
        let mut eng = WsEngine::with_config(deflate_cfg());
        let frame = client_frame(true, OP_TEXT, b"plain on a deflate connection");
        let mut out = Vec::new();
        assert!(eng.feed(&frame, &mut out) == Flow::Continue);
        let (op, rsv1, payload) = parse_server_frame(&out);
        assert!(op == OP_TEXT && rsv1, "server compresses the echo");
        assert_eq!(
            inflate_with(&mut Decompress::new(false), &payload),
            b"plain on a deflate connection"
        );
    }

    #[test]
    fn rsv1_on_continuation_is_protocol_error() {
        crate::http::boot_test_runtime();
        let comp = deflate_payload(b"fragmented");
        let (a, b) = comp.split_at(comp.len() / 2);
        let mut wire = client_frame_compressed(false, OP_TEXT, a);
        // An RSV1 continuation is illegal (RFC 7692 §6): only the opener carries it.
        wire.extend(client_frame_compressed(true, OP_CONT, b));
        let mut eng = WsEngine::with_config(deflate_cfg());
        let mut out = Vec::new();
        assert!(eng.feed(&wire, &mut out) == Flow::Shut);
        let (op, _, payload) = parse_server_frame(&out);
        assert_eq!(op, OP_CLOSE);
        assert_eq!(
            u16::from_be_bytes([payload[0], payload[1]]),
            CLOSE_PROTOCOL_ERROR
        );
    }

    #[test]
    fn compressed_invalid_utf8_fails_1007() {
        crate::http::boot_test_runtime();
        // Bytes that decompress to invalid UTF-8 on a TEXT message: 1007, checked
        // on the DECOMPRESSED payload.
        let comp = deflate_payload(&[0xff, 0xfe, 0xfd]);
        let frame = client_frame_compressed(true, OP_TEXT, &comp);
        let mut eng = WsEngine::with_config(deflate_cfg());
        let mut out = Vec::new();
        assert!(eng.feed(&frame, &mut out) == Flow::Shut);
        let (op, _, payload) = parse_server_frame(&out);
        assert_eq!(op, OP_CLOSE);
        assert_eq!(
            u16::from_be_bytes([payload[0], payload[1]]),
            CLOSE_INVALID_PAYLOAD
        );
    }

    #[test]
    fn corrupt_deflate_stream_fails() {
        crate::http::boot_test_runtime();
        // A block declaring the reserved DEFLATE type (BTYPE=3) is rejected by
        // any decoder: fail (1007), never a panic or a hang.
        let frame = client_frame_compressed(true, OP_BINARY, &[0x07, 0x00, 0x00]);
        let mut eng = WsEngine::with_config(deflate_cfg());
        let mut out = Vec::new();
        assert!(eng.feed(&frame, &mut out) == Flow::Shut);
        let (op, _, payload) = parse_server_frame(&out);
        assert_eq!(op, OP_CLOSE);
        assert_eq!(
            u16::from_be_bytes([payload[0], payload[1]]),
            CLOSE_INVALID_PAYLOAD
        );
    }

    #[test]
    fn echoes_a_text_message_fed_byte_by_byte() {
        crate::http::boot_test_runtime();
        let frame = client_frame(true, OP_TEXT, "hi \u{2603}".as_bytes());
        let mut eng = WsEngine::new();
        let mut out = Vec::new();
        for b in &frame {
            assert!(eng.feed(std::slice::from_ref(b), &mut out) == Flow::Continue);
        }
        assert_eq!(out, server_frame(OP_TEXT, "hi \u{2603}".as_bytes()));
    }

    #[test]
    fn reassembles_fragments_with_interleaved_ping() {
        crate::http::boot_test_runtime();
        let mut wire = client_frame(false, OP_TEXT, b"frag");
        wire.extend(client_frame(true, OP_PING, b"p"));
        wire.extend(client_frame(true, OP_CONT, b"mented"));
        let mut eng = WsEngine::new();
        let mut out = Vec::new();
        assert!(eng.feed(&wire, &mut out) == Flow::Continue);
        let mut want = server_frame(OP_PONG, b"p"); // pong first (§5.5.2)
        want.extend(server_frame(OP_TEXT, b"fragmented"));
        assert_eq!(out, want);
    }

    #[test]
    fn fragmentation_discipline() {
        crate::http::boot_test_runtime();
        // Continuation with no open message.
        let mut out = Vec::new();
        assert!(WsEngine::new().feed(&client_frame(true, OP_CONT, b"x"), &mut out) == Flow::Shut);
        assert_eq!(out, server_frame(OP_CLOSE, &1002u16.to_be_bytes()));
        // A new text frame inside an open fragmented message.
        let mut wire = client_frame(false, OP_TEXT, b"a");
        wire.extend(client_frame(true, OP_TEXT, b"b"));
        let mut out = Vec::new();
        assert!(WsEngine::new().feed(&wire, &mut out) == Flow::Shut);
        assert_eq!(out, server_frame(OP_CLOSE, &1002u16.to_be_bytes()));
    }

    #[test]
    fn over_limit_refused_with_1009_before_buffering() {
        crate::http::boot_test_runtime();
        // A single frame declaring MAX_MESSAGE+1 bytes: refused at the header.
        let mut hdr = vec![0x82, 0x80 | 127];
        hdr.extend_from_slice(&((MAX_MESSAGE as u64) + 1).to_be_bytes());
        hdr.extend_from_slice(&MASK);
        let mut eng = WsEngine::new();
        let mut out = Vec::new();
        assert!(eng.feed(&hdr, &mut out) == Flow::Shut);
        assert_eq!(out, server_frame(OP_CLOSE, &1009u16.to_be_bytes()));
        assert_eq!(eng.msg.capacity(), 0); // nothing was buffered
    }

    #[test]
    fn utf8_char_may_straddle_fragments_but_not_dangle() {
        crate::http::boot_test_runtime();
        // U+2603 = e2 98 83 split across two fragments: valid.
        let mut wire = client_frame(false, OP_TEXT, &[0xe2, 0x98]);
        wire.extend(client_frame(true, OP_CONT, &[0x83]));
        let mut out = Vec::new();
        assert!(WsEngine::new().feed(&wire, &mut out) == Flow::Continue);
        assert_eq!(out, server_frame(OP_TEXT, &[0xe2, 0x98, 0x83]));
        // The same bytes with the message ENDING mid-character: 1007.
        let wire = client_frame(true, OP_TEXT, &[0xe2, 0x98]);
        let mut out = Vec::new();
        assert!(WsEngine::new().feed(&wire, &mut out) == Flow::Shut);
        assert_eq!(out, server_frame(OP_CLOSE, &1007u16.to_be_bytes()));
    }

    #[test]
    fn definite_utf8_violation_fails_fast_mid_message() {
        crate::http::boot_test_runtime();
        // 0xff can begin no UTF-8 sequence: refused on an UNFINISHED message.
        let wire = client_frame(false, OP_TEXT, &[b'a', 0xff]);
        let mut out = Vec::new();
        assert!(WsEngine::new().feed(&wire, &mut out) == Flow::Shut);
        assert_eq!(out, server_frame(OP_CLOSE, &1007u16.to_be_bytes()));
    }

    #[test]
    fn close_handshake_echoes_the_code() {
        crate::http::boot_test_runtime();
        let wire = client_frame(true, OP_CLOSE, &[0x03, 0xe8]); // 1000
        let mut out = Vec::new();
        assert!(WsEngine::new().feed(&wire, &mut out) == Flow::Shut);
        assert_eq!(out, server_frame(OP_CLOSE, &1000u16.to_be_bytes()));
    }

    #[test]
    fn close_frame_validation() {
        crate::http::boot_test_runtime();
        // 1-byte close payload: 1002.
        let mut out = Vec::new();
        assert!(
            WsEngine::new().feed(&client_frame(true, OP_CLOSE, &[0x03]), &mut out) == Flow::Shut
        );
        assert_eq!(out, server_frame(OP_CLOSE, &1002u16.to_be_bytes()));
        // Reserved code 1005: 1002.
        let mut out = Vec::new();
        assert!(
            WsEngine::new().feed(&client_frame(true, OP_CLOSE, &[0x03, 0xed]), &mut out)
                == Flow::Shut
        );
        assert_eq!(out, server_frame(OP_CLOSE, &1002u16.to_be_bytes()));
        // Valid code, non-UTF-8 reason: 1007.
        let mut out = Vec::new();
        assert!(
            WsEngine::new().feed(&client_frame(true, OP_CLOSE, &[0x03, 0xe8, 0xff]), &mut out)
                == Flow::Shut
        );
        assert_eq!(out, server_frame(OP_CLOSE, &1007u16.to_be_bytes()));
    }

    // -----------------------------------------------------------------------
    // Verdict identity: the proven seams against the retired host logic, on
    // corpora that cover every branch either side has.
    // -----------------------------------------------------------------------

    /// A tiny deterministic generator — no dependencies.
    fn next_u64(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = *seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    /// The engine's RETIRED incremental UTF-8 logic, byte-for-byte: a
    /// watermark over an accumulating buffer, advanced with `from_utf8`.
    struct RetiredUtf8 {
        buf: Vec<u8>,
        ok: usize,
    }
    impl RetiredUtf8 {
        fn new() -> Self {
            RetiredUtf8 {
                buf: Vec::new(),
                ok: 0,
            }
        }
        /// `false` = definite violation (the retired fail-fast).
        fn feed(&mut self, chunk: &[u8]) -> bool {
            self.buf.extend_from_slice(chunk);
            match std::str::from_utf8(&self.buf[self.ok..]) {
                Ok(_) => {
                    self.ok = self.buf.len();
                    true
                }
                Err(e) => {
                    self.ok += e.valid_up_to();
                    e.error_len().is_none()
                }
            }
        }
        /// The retired end-of-message boundary check.
        fn complete(&self) -> bool {
            self.ok == self.buf.len()
        }
    }

    /// Drive the proven automaton and the retired logic over one byte string
    /// under one chunking; both must fail on the same chunk or agree on the
    /// final boundary verdict.
    fn check_utf8_identity(bytes: &[u8], cuts: &[usize]) {
        let mut state: u32 = 0;
        let mut retired = RetiredUtf8::new();
        let mut prev = 0;
        for (k, &cut) in cuts.iter().chain(std::iter::once(&bytes.len())).enumerate() {
            let chunk = &bytes[prev..cut];
            prev = cut;
            state = ws_utf8(state, chunk);
            let proven_alive = state <= 7;
            let retired_alive = retired.feed(chunk);
            assert_eq!(
                proven_alive, retired_alive,
                "fail-fast divergence at chunk {k} of {bytes:02x?} cuts {cuts:?}"
            );
            if !proven_alive {
                return; // both failed on the same chunk
            }
        }
        assert_eq!(
            state == 0,
            retired.complete(),
            "boundary divergence on {bytes:02x?} cuts {cuts:?}"
        );
    }

    #[test]
    fn utf8_verdict_identity_exhaustive_two_octets() {
        crate::http::boot_test_runtime();
        // Every 1- and 2-octet string, whole and split at every position.
        for b0 in 0..=255u8 {
            check_utf8_identity(&[b0], &[]);
            for b1 in 0..=255u8 {
                check_utf8_identity(&[b0, b1], &[]);
                check_utf8_identity(&[b0, b1], &[1]);
            }
        }
    }

    #[test]
    fn utf8_verdict_identity_boundary_scalars() {
        crate::http::boot_test_runtime();
        // The RFC 3629 corner sequences, whole, split everywhere, and
        // truncated (a dangling partial character).
        let corners: &[&[u8]] = &[
            &[0x7F],
            &[0xC2, 0x80],
            &[0xDF, 0xBF],
            &[0xE0, 0xA0, 0x80], // smallest 3-octet (overlong boundary)
            &[0xE0, 0x9F, 0xBF], // overlong: must refuse
            &[0xED, 0x9F, 0xBF], // U+D7FF: last before the surrogates
            &[0xED, 0xA0, 0x80], // U+D800: surrogate, must refuse
            &[0xEE, 0x80, 0x80], // U+E000: first after the surrogates
            &[0xEF, 0xBF, 0xBF],
            &[0xF0, 0x90, 0x80, 0x80], // smallest 4-octet
            &[0xF0, 0x8F, 0xBF, 0xBF], // overlong: must refuse
            &[0xF4, 0x8F, 0xBF, 0xBF], // U+10FFFF: the last scalar
            &[0xF4, 0x90, 0x80, 0x80], // beyond: must refuse
            &[0xC0, 0xAF],             // classic overlong
            &[0xC1, 0xBF],
            &[0x80],
            &[0xFE],
            &[0xFF],
        ];
        for c in corners {
            for cut in 0..c.len() {
                check_utf8_identity(c, &[cut]);
                check_utf8_identity(&c[..cut], &[]); // truncated: may dangle
            }
            check_utf8_identity(c, &[]);
        }
    }

    #[test]
    fn utf8_verdict_identity_random_corpus() {
        crate::http::boot_test_runtime();
        let mut seed = 0x5EED_0001u64;
        for case in 0..4000 {
            // Half the corpus: valid UTF-8 built from random scalars, then
            // (for half of those) one random byte mutated. Other half: raw
            // random bytes.
            let mut bytes: Vec<u8> = Vec::new();
            if case % 2 == 0 {
                let chars = next_u64(&mut seed) % 24;
                for _ in 0..chars {
                    loop {
                        let v = (next_u64(&mut seed) % 0x110000) as u32;
                        if let Some(c) = char::from_u32(v) {
                            let mut buf = [0u8; 4];
                            bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
                            break;
                        }
                    }
                }
                if case % 4 == 0 && !bytes.is_empty() {
                    let i = (next_u64(&mut seed) as usize) % bytes.len();
                    bytes[i] = (next_u64(&mut seed) & 0xFF) as u8;
                }
            } else {
                let n = next_u64(&mut seed) % 48;
                for _ in 0..n {
                    bytes.push((next_u64(&mut seed) & 0xFF) as u8);
                }
            }
            // A random chunking: each position is a cut with probability 1/4.
            let mut cuts = Vec::new();
            for i in 1..bytes.len() {
                if next_u64(&mut seed) % 4 == 0 {
                    cuts.push(i);
                }
            }
            check_utf8_identity(&bytes, &cuts);
        }
    }

    /// The engine's RETIRED admission logic, byte-for-byte (`on_header`
    /// before the proven verdict): the new `msg_op` or the close code.
    fn retired_admit(msg_op: u8, buf_len: usize, opcode: u8, len: u64) -> Result<u8, u16> {
        let mut m = msg_op;
        match opcode {
            OP_TEXT | OP_BINARY => {
                if m != 0 {
                    return Err(CLOSE_PROTOCOL_ERROR);
                }
                m = opcode;
            }
            OP_CONT => {
                if m == 0 {
                    return Err(CLOSE_PROTOCOL_ERROR);
                }
            }
            _ => return Ok(m),
        }
        if len > (MAX_MESSAGE - buf_len) as u64 {
            return Err(CLOSE_TOO_BIG);
        }
        Ok(m)
    }

    #[test]
    fn admit_verdict_identity_on_boundary_grid() {
        crate::http::boot_test_runtime();
        let max = MAX_MESSAGE as u64;
        let bufs: &[usize] = &[0, 1, 2, MAX_MESSAGE / 2, MAX_MESSAGE - 1, MAX_MESSAGE];
        let lens: &[u64] = &[0, 1, 2, 125, max - 1, max, max + 1, 1 << 62];
        for &opcode in &[OP_CONT, OP_TEXT, OP_BINARY, OP_CLOSE, OP_PING, OP_PONG] {
            for &msg_op in &[0u8, OP_TEXT, OP_BINARY] {
                for &fin in &[false, true] {
                    for &buf_len in bufs {
                        // The engine's invariant: the buffer is empty between
                        // messages (msg is cleared whenever msg_op returns to
                        // 0), so only reachable states are compared.
                        if msg_op == 0 && buf_len != 0 {
                            continue;
                        }
                        for &len in lens {
                            let v = ws_admit(msg_op, buf_len as u64, opcode, fin, len);
                            match retired_admit(msg_op, buf_len, opcode, len) {
                                Ok(m) => {
                                    assert_eq!(
                                        v >> 32,
                                        2,
                                        "accept divergence: op {opcode} m {msg_op} fin {fin} buf {buf_len} len {len}"
                                    );
                                    let during = ((v >> 8) & 0xF) as u8;
                                    let after = ((v >> 4) & 0xF) as u8;
                                    let deliver = v & 1 != 0;
                                    assert_eq!(during, m, "during divergence");
                                    // The verdict also fixes the completion
                                    // transition the retired code spread
                                    // across on_frame:
                                    let is_data = opcode < OP_CLOSE;
                                    assert_eq!(deliver, is_data && fin, "deliver divergence");
                                    assert_eq!(
                                        after,
                                        if is_data && fin { 0 } else { during },
                                        "after divergence"
                                    );
                                }
                                Err(code) => {
                                    assert_eq!(
                                        v >> 32,
                                        1,
                                        "reject divergence: op {opcode} m {msg_op} fin {fin} buf {buf_len} len {len}"
                                    );
                                    assert_eq!((v & 0xFFFF) as u16, code, "code divergence");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// The engine's RETIRED close-body logic, byte-for-byte (`on_close`
    /// before the proven verdict): (tag, code) with tag 0 = echo empty,
    /// 1 = echo code, 2 = fail.
    fn retired_close(p: &[u8]) -> (u32, u16) {
        let n = p.len();
        if n == 0 {
            return (0, 0);
        }
        if n == 1 {
            return (2, CLOSE_PROTOCOL_ERROR);
        }
        let code = u16::from_be_bytes([p[0], p[1]]);
        if !close_code_ok(code) {
            return (2, CLOSE_PROTOCOL_ERROR);
        }
        if std::str::from_utf8(&p[2..n]).is_err() {
            return (2, CLOSE_INVALID_PAYLOAD);
        }
        (1, code)
    }

    #[test]
    fn close_verdict_identity_on_corpus() {
        crate::http::boot_test_runtime();
        let mut cases: Vec<Vec<u8>> = vec![vec![], vec![0x03], vec![0xFF]];
        // Every status code across and beyond the registry, bare.
        for code in 0..=5200u16 {
            cases.push(code.to_be_bytes().to_vec());
        }
        // Reasons: valid, invalid, and dangling-partial UTF-8, on valid and
        // invalid codes.
        for code in [1000u16, 1005, 999, 2999, 3000, 4999] {
            for reason in [
                b"bye".to_vec(),
                vec![0xE2, 0x98, 0x83],
                vec![0xFF],
                vec![0xE2, 0x98],
                vec![0xED, 0xA0, 0x80],
            ] {
                let mut p = code.to_be_bytes().to_vec();
                p.extend_from_slice(&reason);
                cases.push(p);
            }
        }
        for p in &cases {
            let v = ws_close_body(p);
            let (tag, code) = retired_close(p);
            assert_eq!(v >> 16, tag, "close tag divergence on {p:02x?}");
            if tag != 0 {
                assert_eq!(
                    (v & 0xFFFF) as u16,
                    code,
                    "close code divergence on {p:02x?}"
                );
            }
        }
    }
}
