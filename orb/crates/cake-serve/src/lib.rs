//! Integration pattern: drive a verified export-function serve entry from a
//! per-core-shard reactor over zero-copy buffers, giving each shard its own
//! heap.
//!
//! # The constraint
//!
//! The emitted stage exposes three region slots — the heap base, the stack
//! base, and the address just past the stack — as PROCESS-GLOBAL words, plus an
//! init entry `cml_main` that reads them, and (with main-return enabled) the
//! export function `serve` as an ordinary SysV-ABI symbol:
//!
//! ```text
//!   serve(ctrl, req, len, resp)   // rdi, rsi, rdx, rcx ; returns bytes written
//! ```
//!
//! A share-nothing dataplane runs one reactor per core (each an
//! `SO_REUSEPORT` shard, a thread with its own completion-queue loop). Every
//! shard wants to call `serve` on its own request buffers. But the region slots
//! are a single global triple: if two shard threads pointed them at different
//! heaps and called concurrently, they would race on the globals and then
//! stomp each other's heap.
//!
//! # The per-shard-heap solution
//!
//! Give the region slots THREAD-LOCAL storage, so each shard thread has its own
//! heap base / stack / end and its own runtime frontier. Then the sequence per
//! shard is:
//!
//!   1. allocate this thread's heap+stack region once,
//!   2. install it into the thread-local slots (`cake_shard_install`),
//!   3. run `cml_main` once to latch the runtime ready,
//!   4. call `serve` per request, forever, over the borrowed request/response
//!      buffers with no copy.
//!
//! Steps 1–3 are the `ensure_shard_init` latch below (Rust-side thread-local
//! bookkeeping); the linked object holds the matching per-thread region slots.
//! When the real emitted object is linked, its region slots must likewise be
//! given thread-local storage (a storage-class change on the emitted words), or
//! — the fallback the process-shard supervisor already uses — each shard runs
//! as its own PROCESS so the global triple is naturally private.
//!
//! # Trust boundary
//!
//! The heap/stack setup, the thread-local install, and the borrow of the
//! request/response buffers across the FFI call are TRUSTED host glue. This
//! module proves the export function RUNS per shard over a private heap; it
//! does not verify the glue.

use std::alloc::{alloc, dealloc, Layout};
use std::cell::{Cell, RefCell};
use std::os::raw::{c_long, c_uchar};

unsafe extern "C" {
    /// Runtime init: reads this thread's region slots and latches ready. With
    /// main-return enabled it RETURNS rather than running to program exit, so
    /// the host can then call `serve` repeatedly.
    fn cml_main();

    /// The export function. SysV ABI: `ctrl`, `req`, `len`, `resp` in
    /// rdi/rsi/rdx/rcx. Returns the number of bytes written into `resp`, or a
    /// negative code on a broken precondition.
    fn serve(ctrl: *const c_uchar, req: *const c_uchar, len: c_long, resp: *mut c_uchar) -> c_long;

    /// Install this thread's heap/stack region into the thread-local region
    /// slots, ahead of the first `cml_main`. (For a real object whose slots are
    /// process-global, this is instead a direct write to the global triple —
    /// safe only under the per-process-shard fallback.)
    fn cake_shard_install(heap: *mut c_uchar, stack: *mut c_uchar, stackend: *mut c_uchar);
}

/// Per-shard heap+stack region. One contiguous, word-aligned block: the heap
/// occupies the low half, the stack the high half, matching the region the init
/// entry expects.
const HEAP_BYTES: usize = 8 * 1024 * 1024;
const STACK_BYTES: usize = 8 * 1024 * 1024;
const REGION_ALIGN: usize = 16;

/// The control byte the host places at `ctrl[0]`. The stand-in salts its output
/// with it, so a round-trip confirms the control-block argument really flows.
const CTRL_SALT: u8 = 0x3C;

struct ShardHeap {
    base: *mut u8,
    layout: Layout,
    heap: *mut u8,
    stack: *mut u8,
    stackend: *mut u8,
}

impl ShardHeap {
    fn new() -> Self {
        let total = HEAP_BYTES + STACK_BYTES;
        let layout = Layout::from_size_align(total, REGION_ALIGN).expect("bad region layout");
        // SAFETY: layout is non-zero and validly aligned.
        let base = unsafe { alloc(layout) };
        assert!(!base.is_null(), "shard heap allocation failed");
        // SAFETY: offsets are within the single `total`-byte allocation.
        let (heap, stack, stackend) = unsafe { (base, base.add(HEAP_BYTES), base.add(total)) };
        ShardHeap {
            base,
            layout,
            heap,
            stack,
            stackend,
        }
    }
}

impl Drop for ShardHeap {
    fn drop(&mut self) {
        // SAFETY: `base`/`layout` are exactly what `alloc` returned. Runs at
        // thread exit, after this shard has stopped calling `serve`.
        unsafe { dealloc(self.base, self.layout) };
    }
}

thread_local! {
    /// Whether this shard thread has completed install + init.
    static SHARD_READY: Cell<bool> = const { Cell::new(false) };
    /// This shard's owned heap region; kept alive for the thread's lifetime so
    /// the installed slot pointers stay valid.
    static SHARD_HEAP: RefCell<Option<ShardHeap>> = const { RefCell::new(None) };
    /// This shard's control block, reused across calls (no per-call alloc).
    static SHARD_CTRL: RefCell<[u8; 32]> = const { RefCell::new([0u8; 32]) };
}

/// Idempotent per-thread init: allocate this shard's heap, install it into the
/// thread-local region slots, and run the runtime init once. Cheap no-op after
/// the first call on a given thread.
fn ensure_shard_init() {
    if SHARD_READY.with(Cell::get) {
        return;
    }
    let region = ShardHeap::new();
    // SAFETY: `region` outlives every subsequent `serve` on this thread (it is
    // moved into the thread-local below and dropped only at thread exit). The
    // install + init touch only this thread's thread-local slots.
    unsafe {
        cake_shard_install(region.heap, region.stack, region.stackend);
        cml_main();
    }
    SHARD_HEAP.with(|h| *h.borrow_mut() = Some(region));
    SHARD_READY.with(|r| r.set(true));
}

/// Call the export-function serve for one request on the current shard thread,
/// zero-copy: the borrowed `req`/`resp` buffers are handed to the FFI directly.
/// Initialises this thread's heap+runtime on first use. Returns the number of
/// bytes written into `resp`.
///
/// Panics if `resp` is shorter than `req` or if the export function reports a
/// broken precondition.
pub fn call_cake_serve(req: &[u8], resp: &mut [u8]) -> usize {
    ensure_shard_init();
    assert!(
        resp.len() >= req.len(),
        "response buffer ({}) shorter than request ({})",
        resp.len(),
        req.len()
    );

    let req_ptr = req.as_ptr();
    let req_len = req.len() as c_long;
    let resp_ptr = resp.as_mut_ptr();

    let n = SHARD_CTRL.with(|c| {
        let mut ctrl = c.borrow_mut();
        ctrl[0] = CTRL_SALT;
        // SAFETY: `ctrl` is a live 32-byte block; `req`/`resp` are live borrows
        // for the duration of the call; init has run on this thread; the callee
        // writes at most `req_len` bytes into `resp` (asserted >= req.len()).
        unsafe { serve(ctrl.as_ptr(), req_ptr, req_len, resp_ptr) }
    });

    assert!(n >= 0, "serve reported failure code {n}");
    n as usize
}

/// The reference transform the linked stand-in computes, for tests and for
/// documenting the expected bytes. (For a real serve this would be the modelled
/// specification of the stage.)
pub fn reference_transform(req: &[u8], out: &mut [u8]) {
    for (i, &b) in req.iter().enumerate() {
        let k = 0xA5u8 ^ (i as u8);
        out[i] = b ^ k ^ CTRL_SALT;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expected(req: &[u8]) -> Vec<u8> {
        let mut out = vec![0u8; req.len()];
        reference_transform(req, &mut out);
        out
    }

    /// The export function runs on the calling (main) thread over a private
    /// heap, and produces the modelled bytes.
    #[test]
    fn single_thread_roundtrip() {
        let req = b"GET / HTTP/1.1\r\n";
        let mut resp = [0u8; 64];
        let n = call_cake_serve(req, &mut resp);
        assert_eq!(n, req.len());
        assert_eq!(&resp[..n], &expected(req)[..]);
    }

    /// Idempotent init: many calls on one thread reuse the one heap + one init.
    #[test]
    fn repeated_calls_reuse_shard() {
        let mut resp = [0u8; 128];
        for i in 0..1000u32 {
            let req = format!("request-number-{i}");
            let n = call_cake_serve(req.as_bytes(), &mut resp);
            assert_eq!(&resp[..n], &expected(req.as_bytes())[..]);
        }
    }

    /// The per-shard-heap property off the main thread: a spawned shard thread
    /// initialises its OWN heap and runs the export function there.
    #[test]
    fn spawned_shard_has_own_heap() {
        let handle = std::thread::spawn(|| {
            let req = b"spawned-shard-request";
            let mut resp = [0u8; 64];
            let n = call_cake_serve(req, &mut resp);
            assert_eq!(n, req.len());
            assert_eq!(&resp[..n], &expected(req)[..]);
            resp[..n].to_vec()
        });
        let got = handle.join().expect("shard thread panicked");
        assert_eq!(got, expected(b"spawned-shard-request"));
    }

    /// The load-bearing test: N shard threads, each pinned to its own core,
    /// each hammering the export function over its own distinct inputs. If the
    /// heap were shared instead of per-thread, the stand-in's canary guard
    /// would trip (serve returns negative -> panic) or outputs would corrupt.
    /// All shards passing proves each ran on a private heap.
    #[test]
    fn shards_no_crosstalk_across_cores() {
        const SHARDS: usize = 4;
        const ITERS: usize = 5000;

        let handles: Vec<_> = (0..SHARDS)
            .map(|shard| {
                std::thread::spawn(move || {
                    pin_to_core(shard);
                    let mut resp = [0u8; 256];
                    for i in 0..ITERS {
                        // Distinct per-shard, per-iteration payload.
                        let req = format!("shard-{shard:02}-iter-{i:06}-payload");
                        let n = call_cake_serve(req.as_bytes(), &mut resp);
                        assert_eq!(n, req.len(), "shard {shard} short write at {i}");
                        assert_eq!(
                            &resp[..n],
                            &expected(req.as_bytes())[..],
                            "shard {shard} corrupted output at iter {i}"
                        );
                    }
                    shard
                })
            })
            .collect();

        for h in handles {
            let shard = h.join().expect("a shard thread panicked");
            let _ = shard;
        }
    }

    /// Pin the current thread to core `idx` (best effort). Mirrors the reactor's
    /// per-core shard placement so the no-crosstalk test runs on real distinct
    /// cores, not just distinct threads.
    #[cfg(target_os = "linux")]
    fn pin_to_core(idx: usize) {
        unsafe {
            let mut set: libc::cpu_set_t = std::mem::zeroed();
            libc::CPU_ZERO(&mut set);
            let ncpu = libc::sysconf(libc::_SC_NPROCESSORS_ONLN);
            let core = if ncpu > 0 { idx % (ncpu as usize) } else { idx };
            libc::CPU_SET(core, &mut set);
            let _ = libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set);
        }
    }

    #[cfg(not(target_os = "linux"))]
    fn pin_to_core(_idx: usize) {}
}
