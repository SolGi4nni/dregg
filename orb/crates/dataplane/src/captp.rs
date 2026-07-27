//! The capability-transport (CapTP) wire-frame seam: a minimal listener that
//! frames and deframes capability-transport messages entirely through the
//! PROVEN codec.
//!
//! The frame layer proves a total, consumed-monotone decoder and a value-exact
//! round-trip against the encoder (`Captp.Frame` / `Captp.Encode`, crossed via
//! `drorb_captp_frame` — `Captp.Export`). This host keeps only the socket and
//! the byte accumulation; the deframe verdict on every prefix — a bounded
//! reject, or a decoded frame with its canonical re-encoding — is the proven
//! core's. The listener DEFRAMES an incoming prefix with `decodeFrame` and
//! REFRAMES its response with `encodeFrame`, so both halves of the codec govern
//! the actual bytes: the read side always terminates and strictly consumes, and
//! a malformed prefix is rejected in bounded time with no crash — the same
//! green-proof/governed-wire bridge the HTTP/1.1 request framer and the
//! WebSocket header verdict already stand on.
//!
//! SCOPE (honest): this deploys the wire CODEC — the bounded, crash-safe framing
//! of capability-transport messages. It is NOT the full object-capability
//! protocol: descriptor resolution against the session tables, promise
//! pipelining, third-party handoff, and import/export-table GC stay proven-core
//! or prose, un-wired. This seam governs the BYTES, not yet the objects they
//! name.
//!
//! Gated on `DRORB_CAPTP_LISTEN`; the serve path is untouched when it is unset.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};

// ---------------------------------------------------------------------------
// The proven frame-codec seam: `drorb_captp_frame` (`Captp.Export`). These
// declarations are captp.rs's own (ws.rs / http.rs keep their own sets); the
// crossing is made from threads registered through the crate-wide runtime guard
// (`http::ensure_lean_thread`).
// ---------------------------------------------------------------------------

/// Opaque Lean heap object; only `*mut LeanObject` is ever held.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    /// `initialize_Captp_Export` — module initializer for the proven codec's
    /// closure (`Captp.Export` → `Captp.Encode`/`Captp.Frame` → `Captp.Basic`).
    /// Guarded (idempotent) like every generated module init.
    #[link_name = "initialize_drorb_Captp_Export"]
    fn initialize_Captp_Export(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_captp_frame]` — an accumulated wire prefix in, the encoded
    /// deframe/reframe verdict out: `[0]` = a bounded reject (the prefix is not a
    /// decodable frame), `[1, kind, c0,c1,c2,c3, <encodeFrame f>]` = the leading
    /// frame decoded to `f`, consuming `c` octets (little-endian u32), with `f`'s
    /// canonical re-encoding following.
    fn drorb_captp_frame(input: *mut LeanObject) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — stateless.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Ensure this thread may cross the CapTP codec seam: the thread is registered
/// with the runtime (the crate-wide guard) and the `Captp.Export` module closure
/// is initialized once, process-wide.
fn ensure_captp_seam() {
    use std::sync::Once;
    static MODULE: Once = Once::new();
    // Register the thread FIRST — the module init below allocates on it.
    crate::http::ensure_lean_thread();
    MODULE.call_once(|| {
        // SAFETY: standard guarded module init, on a registered thread, after the
        // process-global runtime is up (same pattern as the WebSocket seam boot).
        unsafe {
            let res = initialize_Captp_Export(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Captp_Export returned an IO error"
            );
            drorb_obj_dec(res);
        }
    });
}

/// The deframe/reframe verdict on an accumulated wire prefix. Returns the
/// encoded verdict bytes (see `drorb_captp_frame`). Runs on the calling thread
/// (registered on first use). Total: the proven decoder never faults, so every
/// prefix — including a malformed one — yields a bounded verdict.
pub fn deframe(prefix: &[u8]) -> Vec<u8> {
    ensure_captp_seam();
    // SAFETY: `drorb_captp_frame` is the real `@[export]` symbol; the argument is
    // a fresh sarray the callee consumes, the result an owned sarray copied out
    // then released — created, consumed, and dropped on this one thread.
    unsafe {
        let arg = drorb_sarray_of_bytes(prefix.as_ptr(), prefix.len());
        let out = drorb_captp_frame(arg);
        let n = drorb_sarray_len(out);
        let v = std::slice::from_raw_parts(drorb_sarray_ptr(out), n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

/// The verdict a deframe reached, classified for the host.
pub enum Deframe {
    /// The prefix decoded to a frame of the given kind tag, consuming `used`
    /// octets; `reencoded` is its canonical re-encoding (the proven `encodeFrame`
    /// output) the listener frames back onto the wire.
    Frame {
        kind: u8,
        used: u32,
        reencoded: Vec<u8>,
    },
    /// The prefix is not a decodable frame — a bounded reject, no crash.
    Reject,
}

/// Classify the raw verdict bytes `drorb_captp_frame` returned.
pub fn classify(verdict: &[u8]) -> Deframe {
    match verdict.first() {
        Some(1) if verdict.len() >= 6 => {
            let used = u32::from_le_bytes([verdict[2], verdict[3], verdict[4], verdict[5]]);
            Deframe::Frame {
                kind: verdict[1],
                used,
                reencoded: verdict[6..].to_vec(),
            }
        }
        // `[1, ...]` too short to carry a header is impossible from the proven
        // export (it always emits kind + 4-octet count), but a defensive host
        // treats any unrecognized shape as a bounded reject rather than trusting
        // it.
        _ => Deframe::Reject,
    }
}

// ---------------------------------------------------------------------------
// The minimal CapTP echo/bootstrap listener.
// ---------------------------------------------------------------------------

/// One connection: read the frame prefix, cross the proven deframe verdict, and
/// respond. On a decoded frame the listener writes back the canonical
/// re-encoding (a bootstrap echo governed by the proven `encodeFrame`); on a
/// malformed prefix it writes a single reject octet `0x00` and closes — bounded,
/// no crash. The frame codec carries no outer length delimiter (it is
/// consumed-monotone: `decodeFrame` takes exactly one frame off the prefix), so
/// the seam reads what the peer sent in one accumulation and lets the proven
/// decoder decide.
fn handle(mut stream: TcpStream) {
    let mut buf = [0u8; 4096];
    let n = match stream.read(&mut buf) {
        Ok(0) => return, // peer closed with no bytes
        Ok(n) => n,
        Err(_) => return,
    };
    let verdict = deframe(&buf[..n]);
    let reply: Vec<u8> = match classify(&verdict) {
        Deframe::Frame { reencoded, .. } => reencoded,
        Deframe::Reject => vec![0u8],
    };
    let _ = stream.write_all(&reply);
    let _ = stream.flush();
}

/// Run the gated CapTP wire-frame listener: accept connections and drive each
/// through the proven deframe/reframe seam, one thread per connection. Never
/// returns while the listener is live.
pub fn run_captp(listener: TcpListener) {
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| "?".to_string());
    // Warm the seam so the first connection does not pay module-init latency
    // and so a boot failure surfaces before any peer connects.
    ensure_captp_seam();
    eprintln!(
        "dataplane: CapTP wire-frame seam on {local} (proven decodeFrame/encodeFrame; \
         deframe -> canonical reframe, malformed -> bounded reject)"
    );
    for conn in listener.incoming() {
        match conn {
            Ok(stream) => {
                std::thread::Builder::new()
                    .name("drorb-captp-conn".into())
                    .spawn(move || handle(stream))
                    .ok();
            }
            Err(_) => continue,
        }
    }
}
