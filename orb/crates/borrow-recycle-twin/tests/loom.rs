//! Gap F (`docs/engine/review/URING-REFINEMENT-SCOPE.md`): the cross-thread
//! borrow↔recycle handoff of the mmap'd provided-buffer slice — the ONE
//! elevated-severity reactor corner the single-threaded `Uring/*.lean` LTS
//! cannot express and no other test covers. A use-after-recycle here is a
//! *cross-connection data disclosure* (the kernel re-lends the recycled slot
//! and overwrites bytes a serve worker is still reading), not a mere leak.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p borrow-recycle-twin --release --test loom -- --test-threads=1
//! ```
//!
//! # What the real handoff is (uring.rs / serve.rs / bufring.rs, drorb)
//!
//! 1. **shard thread**, `on_recv_br` (uring.rs:1756): the kernel delivered
//!    conn A's bytes into buffer `bid`; the shard sets `conn.leased_bid =
//!    Some(bid)` (uring.rs:1859), wraps a raw view `BorrowedReq::new(ptr, len)`
//!    into the mmap'd `bufs` region (`bufring.rs::slice`, :119), and hands it
//!    to the serve worker via `submit_borrowed_metered(borrowed, meter, reply)`
//!    with `reply = ServeReply::Shard(mtx, efd, slot)` (uring.rs:1849/1869).
//! 2. **serve worker thread** (serve.rs:1254–1281): reads the borrowed slice
//!    inside `serve_*_into(job.req.bytes(), …)`, builds the response, then
//!    fires the reply: `mailbox.send(ShardDone { conn, resp })` **then**
//!    `wake(efd)` (serve.rs:1278–1279).
//! 3. **shard thread**, `on_wakeup` (uring.rs:881): the eventfd Read completion
//!    wakes it; it drains `mrx.try_recv()` and calls `stage_response`
//!    (uring.rs:903), which does `c.leased_bid.take()` → `br.recycle(bid)` →
//!    `BufRing::add` (bufring.rs:136): a Release store on the ring tail that
//!    republishes the slot, after which the **kernel may re-lend and overwrite
//!    it**.
//!
//! The safety claim (`uring.rs:1862`, a doc-comment, machine-checked nowhere
//! before this model): *the worker's read of the slice happens-before the
//! shard's recycle*, carried by `worker-read → mailbox.send (Release) →
//! shard try_recv (Acquire) → recycle`. The `wake(efd)`/eventfd Read pair is a
//! strictly stronger syscall barrier layered on top; this model captures only
//! the **weakest link** (the mpsc channel's Release/Acquire), so a green result
//! is conservative.
//!
//! # What THIS loom model covers vs the real deploy (read before trusting)
//!
//! - MODELS: the recycle-direction race only — one lease, one worker, the
//!   completion signal (`done`, Release/Acquire = the mpsc guarantee), the
//!   `leased_bid.take()` recycle-once, and the *strongest adversary* for the
//!   kernel overwrite (it fires immediately on recycle, earlier than any real
//!   kernel re-lend). The delivery direction (kernel wrote the bytes → shard
//!   observed the CQE → handed the borrow to the worker) is taken as already
//!   happens-before-established (the io_uring CQE is a syscall barrier and the
//!   worker is spawned after it), so it is encoded as an ordered write before
//!   the worker starts.
//! - DOES NOT model: the io_uring SQ/CQ rings themselves (see `ring-twin`), the
//!   eventfd coalescing (see `wake-twin`), the plain-recv fallback path
//!   (uring.rs:1914, gap D), multishot re-arm (the deploy is one-shot), or the
//!   `bufring.rs` tail Release/Acquire against the *kernel* (that pairing is the
//!   trusted kernel-ABI floor). This is loom evidence for ONE invariant on a
//!   faithful hand-model — NOT a proof that `uring.rs` is verified.
#![cfg(loom)]

use std::sync::atomic::{AtomicBool as StdBool, AtomicUsize as StdUsize, Ordering as StdOrd};

use loom::cell::UnsafeCell;
use loom::sync::Arc;
use loom::sync::atomic::{AtomicU32, Ordering};
use loom::thread;

/// Conn A's bytes — what the worker is entitled to read from its leased slot.
const GEN_A: u32 = 0xAA;
/// Conn B's bytes — what a re-lend of the recycled slot would overwrite with.
/// The worker observing this value IS the cross-connection disclosure.
const GEN_B: u32 = 0xBB;
/// The leased buffer id (`Conn.leased_bid = Some(BID)`).
const BID: u32 = 7;

/// Shared borrow↔recycle handoff state.
struct Handoff {
    /// The provided-buffer slot's bytes: non-atomic memory, exactly like the
    /// mmap'd `bufs` region a `bufring.rs::slice` borrow points into. `UnsafeCell`
    /// so loom tracks every access and reports a use-after-recycle as a concurrent
    /// load/store (a causality error) — not merely as a wrong value.
    buf: UnsafeCell<u32>,
    /// serve-worker → shard completion signal: `mailbox.send(ShardDone)` +
    /// `wake(efd)`. Release/Acquire is the *weakest* ordering the std mpsc channel
    /// already provides; the eventfd syscall is strictly stronger on top.
    done: AtomicU32,
    /// The per-connection lease (`Conn.leased_bid: Option<u16>`). 0 = None,
    /// nonzero = Some(bid); recycle-once = a single swap-to-0.
    lease: AtomicU32,
}

/// Count of loom schedules explored, for the report.
static ITERS: StdUsize = StdUsize::new(0);

/// PRIMARY ASSURANCE. The deployed handoff: the shard recycles (and the kernel
/// re-lends + overwrites) only after it observes the worker's completion signal.
/// loom explores every interleaving and every C11-permitted read; the invariant
/// asserted is **no use-after-recycle** — enforced three ways:
///   (a) loom's `UnsafeCell` access tracking: the worker's read and the shard's
///       overwrite are never concurrent (they are ordered by the `done` handoff);
///   (b) value: the worker always reads `GEN_A`, never the `GEN_B` re-lend;
///   (c) recycle-once: `lease.take()` yields `Some(BID)` exactly at the recycle.
/// Green over all schedules = the borrow↔recycle handoff is interleaving-safe
/// for this model.
#[test]
fn borrow_recycle_is_interleaving_safe() {
    loom::model(|| {
        ITERS.fetch_add(1, StdOrd::Relaxed);

        let h = Arc::new(Handoff {
            // Delivery direction already established (CQE syscall barrier + spawn):
            // the kernel wrote conn A's bytes into the slot.
            buf: UnsafeCell::new(GEN_A),
            done: AtomicU32::new(0),
            lease: AtomicU32::new(BID),
        });

        // WORKER (serve thread): read the borrowed slice, then signal completion.
        let hw = h.clone();
        let worker = thread::spawn(move || {
            // serve_*_into(job.req.bytes(), …): the read of the leased mmap slice.
            let seen = hw.buf.with(|p| unsafe { *p });
            // The worker must observe ITS OWN connection's bytes.
            assert_eq!(
                seen, GEN_A,
                "USE-AFTER-RECYCLE: worker read conn-B bytes — cross-connection disclosure"
            );
            // mailbox.send(ShardDone) + wake(efd): publish read-completion.
            hw.done.store(1, Ordering::Release);
        });

        // SHARD (main): wait for the wakeup, then recycle, then (strongest
        // adversary) let the kernel re-lend + overwrite the slot immediately.
        while h.done.load(Ordering::Acquire) == 0 {
            loom::thread::yield_now();
        }
        // stage_response: `leased_bid.take()` → `br.recycle(bid)`. Recycle-once.
        let taken = h.lease.swap(0, Ordering::AcqRel);
        assert_eq!(taken, BID, "recycle-once: the lease is taken exactly here");
        // The recycle republished the slot (bufring `add`: Release store on the
        // ring tail); the kernel re-lends and overwrites with conn B's bytes NOW.
        h.buf.with_mut(|p| unsafe { *p = GEN_B });

        worker.join().unwrap();
    });

    eprintln!(
        "loom: borrow_recycle_is_interleaving_safe — {} schedules explored, no use-after-recycle",
        ITERS.load(StdOrd::Relaxed)
    );
}

/// TEETH. The *counter-model*: if the shard recycled (and the kernel re-lent +
/// overwrote) WITHOUT first observing the worker's completion signal — i.e. the
/// `done`/eventfd handoff removed — the read and the overwrite are genuinely
/// concurrent, and loom finds the interleaving where the worker reads the `GEN_B`
/// re-lend. This proves (a) the invariant is real and violable, and (b) the
/// green `borrow_recycle_is_interleaving_safe` above is meaningful: loom WOULD
/// have caught a handoff that recycles a still-borrowed slot.
///
/// `buf` is a relaxed atomic here (not `UnsafeCell`) so the disclosed *value* is
/// asserted directly — the same static-flag pattern `ring-twin`'s litmus uses —
/// rather than surfacing as a loom causality panic.
#[test]
fn recycle_without_worker_signal_discloses() {
    static DISCLOSURE_REACHED: StdBool = StdBool::new(false);

    loom::model(|| {
        let buf = Arc::new(AtomicU32::new(GEN_A));
        let lease = Arc::new(AtomicU32::new(BID));

        // WORKER: read the borrowed slice.
        let bw = buf.clone();
        let worker = thread::spawn(move || bw.load(Ordering::Relaxed));

        // SHARD: recycle + kernel re-lend/overwrite — with NO wait on the worker.
        let taken = lease.swap(0, Ordering::AcqRel);
        assert_eq!(taken, BID);
        buf.store(GEN_B, Ordering::Relaxed);

        let seen = worker.join().unwrap();
        if seen == GEN_B {
            // The worker read a slot the kernel had already re-lent to conn B.
            DISCLOSURE_REACHED.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        DISCLOSURE_REACHED.load(StdOrd::Relaxed),
        "loom found NO disclosure without the handoff — the teeth test is broken; \
         the green safe test no longer witnesses that the completion signal is load-bearing"
    );
    eprintln!(
        "loom: recycle_without_worker_signal_discloses — disclosure REACHED (as expected); \
         the done/eventfd handoff is load-bearing"
    );
}
