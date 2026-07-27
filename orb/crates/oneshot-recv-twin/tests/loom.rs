//! The **DEPLOYED one-shot buffer-select recv path** (`crates/dataplane/src/uring.rs`):
//! the per-request lease `acquire -> process -> recycle` cycle through the single
//! `Conn.leased_bid` cell. This IS the real deployed path — the recv is one-shot
//! (`recv_br_sqe`, uring.rs:757, has NO multishot flag), so at most one recv is in
//! flight and at most one lease is held per connection at a time, and the NEXT
//! recv is armed only after the current request's response recycled its lease.
//! The invariant: over that cycle the lease is recycled EXACTLY ONCE, the borrowed
//! slot is not recycled before the serve worker finished reading it (no
//! cross-request disclosure), and every lent buffer id returns to the ring — no
//! cross-request lease leak.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p oneshot-recv-twin --release --test loom -- --test-threads=1
//! ```
//!
//! # What the real one-shot cycle is (uring.rs / serve.rs / bufring.rs, drorb)
//!
//! 1. **shard thread**, `arm_recv` (uring.rs:789) -> `recv_br_sqe` (uring.rs:757):
//!    arms ONE buffer-select recv (plain `Recv` + `BUFFER_SELECT`, NO
//!    `IORING_RECV_MULTISHOT`). Exactly one CQE will land for it.
//! 2. **shard thread**, `on_recv_br` (uring.rs:1975): the kernel delivered the
//!    request into provided buffer `bid` (the model's `deliver`). On the borrow
//!    fast path the shard ACQUIRES the lease — `conn.leased_bid = Some(bid)`
//!    (uring.rs:2079) — wraps a raw view of the mmap'd slot (`BorrowedReq::new`,
//!    `bufring.rs::slice`), and hands it to a serve worker via
//!    `submit_borrowed_metered(borrowed, meter, reply)` with
//!    `reply = ServeReply::Shard(mtx, efd, slot)`.
//! 3. **serve worker thread** (serve.rs:1640-1647): reads the borrowed slice
//!    inside `serve_*_into(job.req.bytes(), ...)`, builds the response, then
//!    `mailbox.send(ShardDone { conn, resp })` **then** `wake(efd)`.
//! 4. **shard thread**, `on_wakeup` (uring.rs:917) -> `stage_response`
//!    (uring.rs:949) -> `stage_response_appended` (uring.rs:978): RECYCLES the
//!    lease — `c.leased_bid.take()` -> `br.recycle(bid)` (uring.rs:981-985) — then
//!    stages and arms the response send.
//! 5. **shard thread**, `on_send` -> `finish_send` (uring.rs:2448): on keep-alive,
//!    `dispatch_acc` -> `arm_recv` arms the NEXT recv — the next per-request cycle.
//!    The next recv is armed ONLY here, AFTER step 4 recycled: that is the one-shot
//!    serialization that keeps the single `leased_bid` cell holding at most one
//!    live lease.
//!
//! The lease is also recycled-exactly-once on the two OTHER shard-side edges that
//! terminate a cycle: the submit-failed arm (`leased_bid = None` then
//! `recycle_bid`, uring.rs:2100/2102, when the serve thread is gone at shutdown)
//! and `close` (`leased_bid.take()` -> recycle, uring.rs:2461). All three edges run
//! on the one shard thread and are mutually exclusive for a given lease; the single
//! `Option::take()` is the recycle-exactly-once mechanism across them.
//!
//! The safety claim (uring.rs:2073-2076 / :981-982, doc-comments, machine-checked
//! nowhere before this model): *the worker's read of the borrowed slot
//! happens-before the shard's recycle* (carried by `worker-read -> mailbox.send
//! (Release) -> shard try_recv (Acquire) -> recycle`; the `wake(efd)`/eventfd Read
//! is a strictly stronger syscall barrier on top), and *the one-shot single-recv
//! serialization means the single `leased_bid` cell never holds two live leases*,
//! so every lent `bid` is recycled exactly once and none leaks from the ring.
//!
//! # What THIS loom model covers vs the real deploy (read before trusting)
//!
//! - MODELS the per-request one-shot cycle around the single `leased_bid` cell and
//!   the buf_ring slot re-lent for the NEXT request:
//!   (1) NO recycle-before-process — the worker reads its OWN request's bytes, never
//!       the next request's re-lend of the same slot (a cross-request disclosure),
//!       carried by the mailbox Release/Acquire handoff (the weakest real link;
//!       the eventfd syscall is stronger);
//!   (2) recycle-EXACTLY-once — the single `Option::take()` yields the lease once;
//!   (3) buffer CONSERVATION — the lent `bid` returns to the ring (`leased_bid` ends
//!       `None`), so the ring never bleeds buffers.
//!   The LITMUS (`overlapping_recv_leaks_lease`) removes the one-shot serialization
//!   — two concurrent deliveries into the single per-connection lease cell, what an
//!   overlapping / multishot recv would do — and loom finds the interleaving where a
//!   delivery overwrites a still-`Some` cell before its `take`, leaking that `bid`
//!   from the ring (recycles < acquires). This is exactly the hazard the deployed
//!   one-shot design forbids by keeping one recv in flight per connection.
//! - DOES NOT model: the io_uring SQ/CQ rings themselves (see `ring-twin`), the
//!   eventfd coalescing that carries the wake (see `wake-twin`), the plain-recv /
//!   accumulation fallback (uring.rs:2139-2151, which recycles its slot immediately
//!   before any worker touches it — no cross-thread lease there), the prospective
//!   multishot re-arm race (see `multishot-twin` — the deploy is one-shot), or the
//!   `bufring.rs` tail Release/Acquire against the KERNEL (the trusted kernel-ABI
//!   floor). This shares the recycle-direction edge with `borrow-recycle-twin` but
//!   adds the per-request lease-CELL conservation and the cross-request re-lend +
//!   overlap-leak that the single-lease model omits. loom evidence for these
//!   invariants on a faithful hand-model — NOT a proof that `uring.rs` is verified.
#![cfg(loom)]

use std::sync::atomic::{AtomicBool as StdBool, AtomicUsize as StdUsize, Ordering as StdOrd};

use loom::cell::UnsafeCell;
use loom::sync::Arc;
use loom::sync::atomic::{AtomicU32, Ordering};
use loom::thread;

/// Request N's bytes — what the worker is entitled to read from its leased slot.
const REQ_N: u32 = 0xA1;
/// Request N+1's bytes — what the kernel re-lending the SAME recycled slot writes
/// for the next one-shot recv. A worker for request N observing this is a
/// cross-request disclosure.
const REQ_N1: u32 = 0xB2;
/// The leased buffer id for request N (`Conn.leased_bid = Some(BID)`).
const BID: u32 = 7;
/// Two distinct buffer ids for the overlap litmus (two concurrent deliveries).
const BID1: u32 = 11;
const BID2: u32 = 13;

/// Shared per-connection one-shot recv state.
struct Conn {
    /// The provided-buffer slot's bytes: non-atomic mmap'd memory, exactly like the
    /// `bufring.rs::slice` view a borrow points into. `UnsafeCell` so loom tracks
    /// every access and reports a recycle-before-process as a concurrent load/store
    /// (a causality error), not merely a wrong value.
    slot: UnsafeCell<u32>,
    /// serve-worker -> shard completion signal: `mailbox.send(ShardDone)` + `wake(efd)`.
    /// Release/Acquire is the WEAKEST ordering the std mpsc channel already provides;
    /// the eventfd syscall is strictly stronger on top.
    done: AtomicU32,
    /// The single per-connection lease cell (`Conn.leased_bid: Option<u16>`). 0 = None,
    /// nonzero = Some(bid); recycle = a single swap-to-0 (`Option::take`).
    leased: AtomicU32,
    /// Count of recycles performed — the conservation witness. One acquire must yield
    /// exactly one recycle; a leak shows up as recycles < acquires.
    recycles: AtomicU32,
}

/// Count of loom schedules explored, per test, for the report.
static ITERS_CYCLE: StdUsize = StdUsize::new(0);

/// PRIMARY ASSURANCE. One full DEPLOYED one-shot per-request cycle, with the buf_ring
/// slot RE-LENT for the next request (the single-cell reuse a busy keep-alive
/// connection drives). The worker (serve thread) processes request N from the leased
/// slot; concurrently the shard, on the worker's wakeup, recycles the single lease and
/// — being one-shot — only then lets the next recv's delivery reuse the slot. loom
/// explores every interleaving and every C11-permitted read; the invariants asserted:
///   (a) NO recycle-before-process — the worker reads REQ_N, never the REQ_N1 re-lend
///       (loom `UnsafeCell` access tracking makes the read and the re-lend overwrite
///       never concurrent; value asserted too);
///   (b) recycle-EXACTLY-once — `leased.take()` yields `Some(BID)` exactly at the recycle;
///   (c) CONSERVATION — `recycles == 1` and `leased` ends `None`: the lent bid returned
///       to the ring, no cross-request leak.
/// Green over all schedules = the one-shot per-request lease cycle is interleaving-safe
/// for this model.
#[test]
fn oneshot_recv_cycle_recycles_once_and_conserves() {
    loom::model(|| {
        ITERS_CYCLE.fetch_add(1, StdOrd::Relaxed);

        let c = Arc::new(Conn {
            // deliver (step 2) already established: the CQE is a syscall barrier and
            // the worker is spawned after it, so the kernel's write of request N into
            // the slot is ordered before the worker starts.
            slot: UnsafeCell::new(REQ_N),
            done: AtomicU32::new(0),
            leased: AtomicU32::new(BID), // shard ACQUIRED the lease at on_recv_br
            recycles: AtomicU32::new(0),
        });

        // WORKER (serve thread): read the borrowed slot for request N, then signal
        // completion (mailbox.send(ShardDone) + wake(efd)).
        let cw = c.clone();
        let worker = thread::spawn(move || {
            let seen = cw.slot.with(|p| unsafe { *p });
            assert_eq!(
                seen, REQ_N,
                "CROSS-REQUEST DISCLOSURE: worker read request N+1's bytes — the slot \
                 was recycled + re-lent before the serve read finished"
            );
            cw.done.store(1, Ordering::Release);
        });

        // SHARD (on_wakeup -> stage_response_appended): wait for the wakeup, recycle the
        // single lease exactly once, then — being ONE-SHOT — the next recv's delivery
        // re-lends the SAME slot for request N+1 (finish_send -> arm_recv fires only
        // after this recycle).
        while c.done.load(Ordering::Acquire) == 0 {
            loom::thread::yield_now();
        }
        let taken = c.leased.swap(0, Ordering::AcqRel);
        assert_eq!(
            taken, BID,
            "recycle-exactly-once: the single lease cell is taken here"
        );
        c.recycles.fetch_add(1, Ordering::AcqRel);
        // The recycle republished the slot; the next one-shot recv's delivery reuses it.
        c.slot.with_mut(|p| unsafe { *p = REQ_N1 });

        worker.join().unwrap();

        assert_eq!(
            c.recycles.load(Ordering::Acquire),
            1,
            "conservation: the acquired lease is recycled exactly once (no leak, no double-recycle)"
        );
        assert_eq!(
            c.leased.load(Ordering::Acquire),
            0,
            "the single lease cell returned to None — the bid is back in the ring"
        );
    });

    eprintln!(
        "loom: oneshot_recv_cycle_recycles_once_and_conserves — {} schedules explored, \
         recycled exactly once, conserved, no recycle-before-process",
        ITERS_CYCLE.load(StdOrd::Relaxed)
    );
}

/// TEETH. The *counter-model* for the ONE-SHOT serialization. The deployed recv is
/// one-shot precisely so that at most ONE recv is in flight per connection and the
/// single `leased_bid` cell holds at most one live lease. Remove that — model TWO
/// concurrent deliveries landing into the single per-connection lease cell, what an
/// overlapping / multishot recv (two recvs in flight on one fd) would do — and the
/// cell's single slot cannot track two leases: loom finds the interleaving where one
/// delivery's `store(Some(bid))` overwrites the other's still-`Some` cell BEFORE that
/// other's `take`, so the overwritten `bid` is never recycled — a buffer id LEAKED
/// from the provided-buffer ring (`recycles < acquires`). A ring that bleeds buffers
/// this way degrades to permanent `-ENOBUFS` fallback, killing the zero-copy path.
///
/// This proves (a) the one-shot single-recv serialization is load-bearing for buffer
/// conservation, and (b) the green cycle test above is meaningful: loom WOULD have
/// caught a recv path that let two deliveries share the single lease cell.
///
/// The leak is flagged (not asserted-against) so the test passes exactly when loom
/// REACHES it — the same static-flag teeth pattern the other twins' litmus tests use.
#[test]
fn overlapping_recv_leaks_lease() {
    static LEAK_REACHED: StdBool = StdBool::new(false);

    loom::model(|| {
        // The single per-connection lease cell, starting empty (None), and the
        // conservation counter. TWO deliveries each lend a distinct bid.
        let leased = Arc::new(AtomicU32::new(0));
        let recycles = Arc::new(AtomicU32::new(0));

        // Each "delivery" is a would-be concurrent recv completion for one fd: ACQUIRE
        // (store Some(bid) into the shared lease cell), then its response RECYCLES via
        // take. Two of them run concurrently — the overlap the one-shot design forbids.
        let l1 = leased.clone();
        let r1 = recycles.clone();
        let d1 = thread::spawn(move || {
            l1.store(BID1, Ordering::Release); // acquire: leased_bid = Some(bid1)
            let t = l1.swap(0, Ordering::AcqRel); // response recycles via take()
            if t != 0 {
                r1.fetch_add(1, Ordering::AcqRel);
            }
        });
        let l2 = leased.clone();
        let r2 = recycles.clone();
        let d2 = thread::spawn(move || {
            l2.store(BID2, Ordering::Release);
            let t = l2.swap(0, Ordering::AcqRel);
            if t != 0 {
                r2.fetch_add(1, Ordering::AcqRel);
            }
        });

        d1.join().unwrap();
        d2.join().unwrap();

        // Two bids were lent (acquires == 2). If a store clobbered a still-Some cell
        // before its take, a take returns 0 and that bid is recycled zero times: fewer
        // than two recycles total = a leaked buffer id.
        if recycles.load(Ordering::Acquire) < 2 {
            LEAK_REACHED.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        LEAK_REACHED.load(StdOrd::Relaxed),
        "loom found NO leak with two concurrent deliveries into the single lease cell — \
         the teeth test is broken; the green cycle test no longer witnesses that the \
         one-shot single-recv serialization is load-bearing for buffer conservation"
    );
    eprintln!(
        "loom: overlapping_recv_leaks_lease — buffer-id LEAK REACHED (as expected); \
         the one-shot single-recv-per-connection serialization is load-bearing"
    );
}
