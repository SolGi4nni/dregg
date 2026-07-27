//! io_uring **multishot-recv re-arm coordination** — a reactor concurrency edge
//! not covered by any existing twin. When a multishot recv posts its terminal
//! CQE (the provided-buffer ring is exhausted, `res == -ENOBUFS`, `F_MORE`
//! cleared), the multishot is OFF and must be re-armed — but only once a buffer
//! is free again, and a buffer becomes free when a serve worker RECYCLES its
//! lease. If that recycle runs on the worker thread, the re-arm decision races
//! the recycle. The invariant: the recv is re-armed EXACTLY ONCE per exhaustion
//! once a buffer is available — never dropped, never double-armed.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p multishot-twin --release --test loom -- --test-threads=1
//! ```
//!
//! # The two edges (what the threads model)
//!
//! 1. **shard thread**, terminal CQE: the kernel drained the last free buffer
//!    and posted `res == -ENOBUFS` with `F_MORE` cleared. In the deployed
//!    one-shot analog this is `on_recv_br`'s ENOBUFS arm (uring.rs:1979) and the
//!    F_MORE terminal test is `on_send_zc`'s `cqueue::more(flags)` (uring.rs:2386).
//!    The shard publishes `armed = OFF`, then RE-CHECKS whether a buffer is free
//!    and, if so, tries to claim the re-arm.
//! 2. **worker thread**, recycle: a serve worker finished with its lease and
//!    republishes the slot into the ring — `BufRing::recycle`/`add` (bufring.rs:129/136),
//!    the model's `recycle_bid` (uring.rs:2157) moved onto the worker. It
//!    publishes `free += 1`, then RE-CHECKS whether the multishot is OFF and, if
//!    so, tries to claim the re-arm.
//!
//! The re-arm needs BOTH conditions — `armed == OFF` AND `free > 0` — and each is
//! made true by a DIFFERENT thread. The load-bearing discipline: each thread
//! re-checks the OTHER condition AFTER publishing its own, with a SeqCst FENCE
//! between the publish and the re-check (this is the store-buffering shape — under
//! Release/Acquire, and even under SeqCst atomic operations as loom models them,
//! BOTH re-checks may miss the other's write and neither arms; loom found exactly
//! that lost re-arm twice before the fence, see `try_rearm`), and the transition
//! to ARMED is claimed by a single compare-exchange (so only one thread arms — no
//! double-arm). Drop the fence, the re-check, or the CAS and loom finds the break.
//!
//! # What THIS loom model covers vs the real deploy (read before trusting)
//!
//! - MODELS, over every interleaving of one terminal-CQE and one concurrent
//!   recycle: (1) NO lost re-arm — after both edges settle with a buffer free the
//!   multishot ends ARMED (the receive restarts); (2) NO double-arm — the OFF→ARMED
//!   transition fires exactly once, so there are never two multishot recvs in
//!   flight on one fd (which would double-deliver bytes and double-consume the
//!   ring); (3) buffer conservation — an arm consumes exactly the one recycled
//!   buffer, `free` never underflows.
//! - DOES NOT model: the io_uring SQ/CQ rings themselves (see `ring-twin`), the
//!   eventfd wakeup that carries the poke (see `wake-twin`), the borrow↔recycle
//!   data race the lease itself rides (see `borrow-recycle-twin` / `splitsend-twin`),
//!   more than one outstanding buffer / a ring of depth > 1 (this isolates the
//!   single-buffer exhaustion boundary, the tightest re-arm witness), or the
//!   kernel-side buf_ring tail Release/Acquire (the trusted kernel-ABI floor).
//!   Crucially it does NOT claim the deployed one-shot `uring.rs` contains this
//!   race — the deploy re-arms and recycles on the same shard thread; this is a
//!   PROSPECTIVE-design model. loom evidence for ONE invariant on a faithful
//!   hand-model — NOT a proof that `uring.rs` is verified.
#![cfg(loom)]

use std::sync::atomic::{AtomicBool as StdBool, AtomicUsize as StdUsize, Ordering as StdOrd};

use loom::sync::Arc;
use loom::sync::atomic::{AtomicU32, Ordering, fence};
use loom::thread;

/// Multishot armed-state: a multishot recv SQE is in flight for the fd.
const ARMED: u32 = 1;
/// Multishot armed-state: the multishot terminated (F_MORE cleared) and no
/// re-arm has been claimed yet.
const OFF: u32 = 0;

/// Shared multishot re-arm state for one connection's fd.
struct ReArm {
    /// Whether a multishot recv SQE is currently in flight (`ARMED`/`OFF`). The
    /// OFF→ARMED transition is the re-arm; it is claimed by a single CAS so it can
    /// fire at most once per exhaustion — no two multishot recvs on one fd.
    armed: AtomicU32,
    /// Free provided buffers in the ring. The terminal CQE fires because this hit
    /// zero (exhaustion); a recycle bumps it; an arm consumes exactly one.
    free: AtomicU32,
    /// Total re-arms claimed — the witness that the OFF→ARMED transition fired
    /// exactly once (never zero = a dropped/lost re-arm, never twice = a double-arm).
    arms: AtomicU32,
}

/// The re-arm coordination, run by BOTH edges after each publishes its condition.
/// Re-arm iff the multishot is OFF and a buffer is free, claiming the transition
/// atomically. Returns whether THIS call performed the re-arm.
///
/// Two things are load-bearing, and loom pinned down BOTH:
///
///  1. **The CAS.** The `OFF`→`ARMED` claim is a compare-exchange, so it wins at
///     most once until something sets `armed` back to `OFF` — two concurrent
///     callers can never both arm (no double-arm). `split_check_and_arm_double_arms`
///     is the teeth for this.
///
///  2. **A SeqCst fence between publish and re-check.** This is the classic
///     two-flag rendezvous / store-buffering (SB) shape: the terminal-CQE edge
///     publishes `armed = OFF` and then reads `free`; the recycle edge publishes
///     `free += 1` and then reads `armed`. Those are stores and loads on TWO
///     SEPARATE locations, and under mere Release/Acquire — AND even under SeqCst
///     atomic *operations* as loom models them — the SB outcome is PERMITTED:
///     BOTH threads' re-check can miss the other's just-published write, so
///     neither arms and the recv is stranded with a buffer free. loom found
///     exactly that (both the Release/Acquire and the SeqCst-atomics cuts failed
///     `multishot_rearm_exactly_once` with a lost re-arm). The primitive that
///     forbids SB — and that loom models faithfully — is a SeqCst FENCE placed on
///     each thread BETWEEN its publish store and its re-check load. The two
///     fences are totally ordered; whichever thread's fence is second sees the
///     other's already-published flag and drives the single arm. No lost re-arm.
fn try_rearm(s: &ReArm) -> bool {
    // SB-freedom: a SeqCst fence between this edge's publish (done by the caller —
    // `armed = OFF` on the terminal-CQE side, `free += 1` on the recycle side) and
    // its re-check of the OTHER flag below. Without it, both re-checks may miss
    // and neither arms — the lost re-arm loom finds when this fence is removed.
    fence(Ordering::SeqCst);
    // Is there a buffer to arm the recv with? (Recycle's published half.)
    if s.free.load(Ordering::Acquire) == 0 {
        return false;
    }
    // Claim the OFF→ARMED transition. Only one caller can win this CAS.
    if s.armed
        .compare_exchange(OFF, ARMED, Ordering::AcqRel, Ordering::Acquire)
        .is_ok()
    {
        // We armed the recv: consume exactly the one buffer it will land into.
        s.free.fetch_sub(1, Ordering::AcqRel);
        s.arms.fetch_add(1, Ordering::AcqRel);
        true
    } else {
        false
    }
}

/// Count of loom schedules explored, per test, for the report.
static ITERS_REARM: StdUsize = StdUsize::new(0);

/// PRIMARY ASSURANCE. The exhaustion boundary: the multishot is ARMED but the
/// ring is empty (`free == 0`), so the next completion is the terminal ENOBUFS
/// CQE. Concurrently a worker recycles the one lease it held. loom explores every
/// interleaving of the terminal-CQE edge and the recycle edge; the invariants
/// asserted are:
///   (a) NO lost re-arm — the multishot ends ARMED (`armed == ARMED`): a buffer
///       became free and the receive restarted, never stranded;
///   (b) NO double-arm — the OFF→ARMED transition fired EXACTLY once
///       (`arms == 1`): never two multishot recvs on one fd (double-deliver);
///   (c) buffer conservation — the arm consumed exactly the recycled buffer, so
///       `free` returns to 0 with no underflow.
/// Green over all schedules = the multishot re-arm coordination is
/// interleaving-safe for this model.
#[test]
fn multishot_rearm_exactly_once() {
    loom::model(|| {
        ITERS_REARM.fetch_add(1, StdOrd::Relaxed);

        let s = Arc::new(ReArm {
            armed: AtomicU32::new(ARMED), // multishot in flight
            free: AtomicU32::new(0),      // ring exhausted — next CQE is terminal
            arms: AtomicU32::new(0),
        });

        // SHARD: the terminal ENOBUFS CQE. Publish OFF, then re-check for a buffer.
        // `try_rearm`'s leading SeqCst fence orders this publish before the recycle
        // edge's `armed` re-check (SB both-miss forbidden — see `try_rearm`).
        let ss = s.clone();
        let shard = thread::spawn(move || {
            ss.armed.store(OFF, Ordering::Release);
            try_rearm(&ss);
        });

        // WORKER: recycle the held lease. Publish the buffer, then re-check OFF.
        // Same fence carries the other leg of the two-flag rendezvous.
        let sw = s.clone();
        let worker = thread::spawn(move || {
            sw.free.fetch_add(1, Ordering::AcqRel);
            try_rearm(&sw);
        });

        shard.join().unwrap();
        worker.join().unwrap();

        let armed = s.armed.load(Ordering::Acquire);
        let arms = s.arms.load(Ordering::Acquire);
        let free = s.free.load(Ordering::Acquire);

        assert_eq!(
            armed, ARMED,
            "LOST RE-ARM: multishot ended OFF with a buffer recycled — the receive \
             stalled though a provided buffer is free (a dropped CQE)"
        );
        assert_eq!(
            arms, 1,
            "the OFF->ARMED transition must fire exactly once (got {arms}): \
             0 = dropped re-arm, 2 = double-arm / two multishot recvs on one fd"
        );
        assert_eq!(
            free, 0,
            "buffer conservation: the single re-arm consumed exactly the one \
             recycled buffer — free must return to 0, never underflow"
        );
    });

    eprintln!(
        "loom: multishot_rearm_exactly_once — {} schedules explored, re-armed exactly once, no drop / no double-arm",
        ITERS_REARM.load(StdOrd::Relaxed)
    );
}

/// TEETH #1 — DROPPED re-arm. The counter-model where the RECYCLE side does NOT
/// re-check (`try_rearm` after the recycle is removed) — the "recycle forgot to
/// poke the recv back to life" bug. Now only the terminal-CQE side ever arms, and
/// loom finds the interleaving where the recycle publishes its buffer AFTER the
/// terminal CQE already checked and gave up: the shard sees `free == 0`, returns
/// unarmed; the worker then bumps `free` to 1 but never re-checks. The multishot
/// stays OFF with a buffer free — a stranded connection whose receive never
/// restarts (a genuinely dropped CQE). This proves the recycle-side re-check is
/// load-bearing and that the green safe test above is meaningful.
///
/// The bad state is flagged (not asserted-against) so the test passes exactly when
/// loom REACHES the lost re-arm — the same static-flag teeth pattern the other
/// twins' litmus tests use.
#[test]
fn recycle_without_recheck_drops_rearm() {
    static DROP_REACHED: StdBool = StdBool::new(false);

    loom::model(|| {
        let s = Arc::new(ReArm {
            armed: AtomicU32::new(ARMED),
            free: AtomicU32::new(0),
            arms: AtomicU32::new(0),
        });

        // SHARD: terminal CQE — publish OFF, then re-check (this side is intact —
        // the ONLY change from the safe test is the worker's missing re-check).
        let ss = s.clone();
        let shard = thread::spawn(move || {
            ss.armed.store(OFF, Ordering::Release);
            try_rearm(&ss);
        });

        // WORKER: recycle — publish the buffer but DO NOT re-check (the bug).
        let sw = s.clone();
        let worker = thread::spawn(move || {
            sw.free.fetch_add(1, Ordering::AcqRel);
            // BUG: no try_rearm(&sw) here.
        });

        shard.join().unwrap();
        worker.join().unwrap();

        // A buffer is free but the multishot is still OFF and never re-armed.
        if s.armed.load(Ordering::Acquire) == OFF
            && s.free.load(Ordering::Acquire) > 0
            && s.arms.load(Ordering::Acquire) == 0
        {
            DROP_REACHED.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        DROP_REACHED.load(StdOrd::Relaxed),
        "loom found NO dropped re-arm without the recycle-side re-check — the teeth \
         test is broken; the green safe test no longer witnesses that the recycle \
         must re-check for an OFF multishot"
    );
    eprintln!(
        "loom: recycle_without_recheck_drops_rearm — dropped re-arm REACHED (as expected); \
         the recycle-side re-check is load-bearing"
    );
}

/// TEETH #2 — DOUBLE-arm. The counter-model where the OFF→ARMED transition is
/// claimed by a non-atomic check-then-store (TOCTOU) instead of the CAS. Both the
/// terminal-CQE side and the recycle side can read `armed == OFF` and `free > 0`
/// in the same window, both store `ARMED`, and both `arms += 1`: the fd now has
/// TWO multishot recvs in flight — they double-deliver bytes and double-consume
/// the ring (`free` underflows past 0). loom finds that interleaving. This proves
/// the single-CAS claim is load-bearing (not the plain check-and-store).
#[test]
fn split_check_and_arm_double_arms() {
    static DOUBLE_ARM_REACHED: StdBool = StdBool::new(false);

    /// BROKEN re-arm: check `armed`/`free`, then store — two critical steps, no CAS.
    fn rearm_broken(s: &ReArm) {
        if s.free.load(Ordering::Acquire) == 0 {
            return;
        }
        // TOCTOU window: a concurrent caller that read the same OFF has also
        // passed. Non-atomic claim: read OFF, then store ARMED.
        if s.armed.load(Ordering::Acquire) == OFF {
            s.armed.store(ARMED, Ordering::Release);
            s.free.fetch_sub(1, Ordering::AcqRel);
            s.arms.fetch_add(1, Ordering::AcqRel);
        }
    }

    loom::model(|| {
        // Start OFF with a buffer already free, so BOTH edges' re-checks see the
        // arm-ready condition and can race on the claim.
        let s = Arc::new(ReArm {
            armed: AtomicU32::new(OFF),
            free: AtomicU32::new(1),
            arms: AtomicU32::new(0),
        });

        let ss = s.clone();
        let shard = thread::spawn(move || rearm_broken(&ss));
        let sw = s.clone();
        let worker = thread::spawn(move || rearm_broken(&sw));

        shard.join().unwrap();
        worker.join().unwrap();

        if s.arms.load(Ordering::Acquire) >= 2 {
            // Two multishot recvs armed on one fd from a single free buffer.
            DOUBLE_ARM_REACHED.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        DOUBLE_ARM_REACHED.load(StdOrd::Relaxed),
        "loom found NO double-arm with a split check-and-store — the teeth test is \
         broken; the green safe test no longer witnesses that the single-CAS claim \
         of the OFF->ARMED transition is load-bearing"
    );
    eprintln!(
        "loom: split_check_and_arm_double_arms — double-arm REACHED (as expected); \
         the single compare-exchange claim of the re-arm is load-bearing"
    );
}
