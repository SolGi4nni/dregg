//! The interactive h2c host: one verified HTTP/2 connection-engine state per
//! accepted connection, threaded across socket reads on the connection's own
//! thread.
//!
//! The blocking host forks here when a connection opens with the HTTP/2
//! cleartext prior-knowledge preface (`PRI * HTTP/2.0\r\n`, RFC 9113 §3.4).
//! Every protocol decision — preface validation, frame walking, HPACK with the
//! real decode-side dynamic table, the per-stream FSM, SETTINGS/PING
//! acknowledgement, flow-control pacing, GOAWAY/RST_STREAM emission — happens
//! inside the verified connection engine, reached through its two exports:
//! `drorb_h2c_conn_init` (a fresh opaque engine state) and
//! `drorb_h2c_conn_feed` (one socket read in; the successor state plus a
//! close-flag-prefixed octet string out). This host moves bytes and closes
//! cleanly (shutdown + drain, so the peer sees FIN, never RST) — nothing else.
//!
//! Why a ONE-SHOT answer cannot host the engine: SETTINGS synchronization,
//! PING liveness probes, and WINDOW_UPDATE-paced response bodies all arrive
//! AFTER the client's first flight (RFC 9113 §6.5.3/§6.7/§6.9), so the
//! connection must stay open with the engine state threaded across reads —
//! exactly this loop. (The retired one-shot path also crossed the HTTP/1.1
//! conformant serve seam, whose request-validation gate answers the binary
//! preface `505` — the preface never reached the H2 engine at all.)
//!
//! Thread discipline (the multi-owner safety premise, exactly as
//! `static_serve::cross`): this connection thread registers itself with the
//! booted process-global runtime once before its first crossing and
//! deregisters at thread exit. The engine state and every per-feed
//! input/output object are created, used, and dropped on this ONE registered
//! thread — no heap object ever crosses between threads, and the only objects
//! shared with other owner threads are the module's persistent top-level
//! constants.

use std::io::{ErrorKind, Read, Write};
use std::net::{Shutdown, TcpStream};
use std::time::Duration;

/// An idle HTTP/2 connection with no traffic is reclaimed after this long.
const H2_IDLE_TIMEOUT: Duration = Duration::from_secs(15);

/// How long the close-side drain waits for the peer's remaining octets before
/// the socket is dropped anyway.
const DRAIN_TIMEOUT: Duration = Duration::from_secs(1);

/// Read-buffer size for one socket read fed to the engine.
const READ_CHUNK: usize = 65536;

/// Opaque Lean runtime object (never dereferenced on the Rust side).
#[repr(C)]
struct LeanObject {
    _opaque: [u8; 0],
}

// The verified engine seam plus the byte-marshalling adapter
// (ffi/drorb_ffi.c) and the runtime's thread (de)registration entry points.
// Duplicate extern DECLARATIONS of the same symbols as `serve.rs` — both
// resolve to the one linked library.
unsafe extern "C" {
    /// A fresh engine connection state for one accepted socket (opaque).
    fn drorb_h2c_conn_init(unit: u8) -> *mut LeanObject;
    /// Feed one socket read: consumes `state` and `input`, returns the owned
    /// pair `(state', flag ++ octets)` — octet 0 of the ByteArray is the close
    /// flag (1 = write the rest, then close cleanly), octets 1.. are the
    /// response frames to write.
    fn drorb_h2c_conn_feed(state: *mut LeanObject, input: *mut LeanObject) -> *mut LeanObject;

    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_pair_split(
        pair: *mut LeanObject,
        fst: *mut *mut LeanObject,
        snd: *mut *mut LeanObject,
    );

    fn lean_initialize_thread();
    fn lean_finalize_thread();
}

/// Register THIS thread with the booted process-global runtime, once, and
/// deregister at thread exit. A crossing only happens while a connection is
/// being served, which requires the booted serve gateway, so the process
/// runtime is already up when this first runs on any connection thread.
fn register_thread() {
    struct Registration;
    impl Drop for Registration {
        fn drop(&mut self) {
            // SAFETY: paired with the successful `lean_initialize_thread` below.
            unsafe { lean_finalize_thread() }
        }
    }
    thread_local! {
        static REGISTERED: Registration = {
            // SAFETY: the runtime is booted (see above) and this thread has
            // not registered before (thread_local runs once per thread).
            unsafe { lean_initialize_thread() };
            Registration
        };
    }
    REGISTERED.with(|_| ());
}

/// One engine crossing: feed `bytes` to `state`, copy the engine's returned
/// octet string (close flag + response frames) into `out` (cleared first),
/// and return the successor state.
///
/// SAFETY: caller must be a runtime-registered thread and `state` must be the
/// live engine state created on THIS thread. `drorb_h2c_conn_feed` consumes
/// both arguments; the returned pair is destructured into two owned fields,
/// the octets are copied out, and the octet object is dropped — create,
/// consume, copy-out, drop, all on this one registered thread.
unsafe fn feed(state: *mut LeanObject, bytes: &[u8], out: &mut Vec<u8>) -> *mut LeanObject {
    unsafe {
        let input = drorb_sarray_of_bytes(bytes.as_ptr(), bytes.len());
        let pair = drorb_h2c_conn_feed(state, input);
        let mut next: *mut LeanObject = std::ptr::null_mut();
        let mut octets: *mut LeanObject = std::ptr::null_mut();
        drorb_pair_split(pair, &mut next, &mut octets);
        let n = drorb_sarray_len(octets);
        out.clear();
        out.extend_from_slice(std::slice::from_raw_parts(drorb_sarray_ptr(octets), n));
        drorb_obj_dec(octets);
        next
    }
}

/// Host one h2c connection interactively: create one engine state, then loop —
/// feed the buffered opening bytes and every subsequent socket read to the
/// engine, write the octets it returns, and stop when the engine raises its
/// close flag (clean teardown: half-close, drain, so the peer sees FIN), the
/// peer closes, or the idle timeout fires.
///
/// `first` is the opening burst the caller already read off the socket (it
/// starts with the h2c preface head — that is why we are here). The engine
/// buffers partial frames in its state, so chunk boundaries carry no meaning.
pub fn host_conn(mut stream: TcpStream, first: &[u8]) {
    register_thread();
    let _ = stream.set_read_timeout(Some(H2_IDLE_TIMEOUT));

    // SAFETY: the engine state is created, threaded through `feed`, and
    // dropped on this one registered thread (see the module header).
    let mut state = unsafe { drorb_h2c_conn_init(0) };
    let mut out: Vec<u8> = Vec::with_capacity(4096);
    let mut chunk = vec![0u8; READ_CHUNK.max(first.len())];

    let mut n = first.len();
    chunk[..n].copy_from_slice(first);

    loop {
        state = unsafe { feed(state, &chunk[..n], &mut out) };
        let (close, octets) = match out.split_first() {
            Some((&flag, rest)) => (flag == 1, rest),
            // The engine always prefixes the close flag; an empty return is
            // out-of-contract — fail closed.
            None => (true, &[][..]),
        };
        if !octets.is_empty() && stream.write_all(octets).is_err() {
            break;
        }
        if close {
            // Clean teardown: half-close our side, then drain the peer's
            // remaining octets so the kernel sends FIN, not RST.
            let _ = stream.shutdown(Shutdown::Write);
            let _ = stream.set_read_timeout(Some(DRAIN_TIMEOUT));
            while matches!(stream.read(&mut chunk), Ok(m) if m > 0) {}
            break;
        }
        n = loop {
            match stream.read(&mut chunk) {
                Ok(0) => break 0, // peer closed
                Ok(m) => break m,
                Err(e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(_) => break 0, // idle timeout or error: reclaim
            }
        };
        if n == 0 {
            break;
        }
    }

    // Drop the engine state on the same registered thread that created it.
    // SAFETY: `state` is the owned successor from the last `feed` (or the
    // initial state); nothing else references it.
    unsafe { drorb_obj_dec(state) };
}
