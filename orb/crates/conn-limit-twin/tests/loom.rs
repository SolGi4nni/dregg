//! Blocking reactor's SHARED per-source **connection-limit gate**
//! (`SharedStanding::admit` / `on_close`, `crates/dataplane/src/standing.rs`):
//! the `ConnLimit` check-and-increment must be a SINGLE critical section so
//! concurrent accept/worker threads from one source can never both read
//! `active == cap-1` and both admit — the TOCTOU over-admit that lets a source
//! exceed the configured `max-connections` cap. Plus the accept/close
//! conservation: a concurrent `on_close` frees exactly one slot, and the counter
//! never over- or under-counts.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p conn-limit-twin --release --test loom -- --test-threads=1
//! ```
//!
//! # What the real gate is (standing.rs, drorb)
//!
//! The io_uring / kqueue shards keep their per-source counters in the LOCK-FREE
//! [`Standing`] (`standing.rs:60`): one `Standing` per shard, touched only by that
//! shard's single event-loop thread. There is NO cross-thread race there — that is
//! precisely why it needs no lock, and why loom has nothing to explore for it
//! (modeling it would be vacuous: a single thread, one interleaving).
//!
//! The `SharedStanding` variant (`standing.rs:155`) is the concurrent one — the
//! thread-per-connection *blocking* reactor, whose accept loop and per-connection
//! worker threads run at the same time. Its per-source counter is striped under
//! `Mutex<HashMap<IpAddr,u32>>`, and one source's traffic all hashes to one stripe,
//! so two concurrent accepts from that source contend on the SAME lock:
//!
//! 1. **accept thread**, `admit(ip, cap)` (`standing.rs:229`): takes the stripe
//!    lock ONCE, reads `n = active(ip)`, and — still holding the lock — refuses if
//!    `n >= cap`, else increments and admits. The check and the increment are one
//!    critical section (`standing.rs:230-236`).
//! 2. **worker thread**, `on_close(ip)` (`standing.rs:241`): when the connection's
//!    worker returns, takes the stripe lock, decrements (saturating at zero, drops
//!    the entry at zero).
//!
//! The safety claim (`standing.rs:227-228`, doc-comment, machine-checked nowhere
//! before this model): *the single critical section means concurrent accepts from
//! one source cannot both slip past the cap boundary — no TOCTOU over-admit*, so
//! `active(ip)` never exceeds `cap`; and accept/close is conserved
//! (`active = #admitted - #closed`, never negative). This is the run-time
//! counterpart of the `conn_conservation` / `ConnLimit.admits` invariants proven
//! in `Reactor/StandingCounters.lean`. `SharedStanding::rate_note` (`standing.rs:211`,
//! the `429` gate) rests on the IDENTICAL single-critical-section discipline (one
//! stripe held across age-and-count), so this model witnesses that pattern too.
//!
//! # What THIS loom model covers vs the real deploy (read before trusting)
//!
//! - MODELS, over every interleaving of two concurrent accepts on one source's
//!   stripe (one `u32` behind one `loom::sync::Mutex`, exactly the striped
//!   `active(ip)` slot): (1) NO over-admit — the peak concurrent `active` never
//!   exceeds `cap`, and with `cap==1` exactly one of two racing accepts is admitted;
//!   (2) accept/close conservation — a worker's concurrent `on_close` frees exactly
//!   one slot and the counter returns to zero with no double-count and no underflow.
//! - DOES NOT model: the `HashMap`/striping itself (a source maps to one fixed
//!   stripe — modeled as that one counter — and distinct stripes are independent by
//!   construction), the lock-free shard-path [`Standing`] (single-threaded, nothing
//!   to interleave), the `rate_note` window aging / `Instant` clock, the accept
//!   syscall or the worker's socket I/O, or `on_close`'s saturating-subtract as a
//!   real underflow source (the accept/close discipline calls it once per admitted
//!   conn — this model closes only what it admitted). This is loom evidence for the
//!   check-and-increment ATOMICITY of one striped counter — NOT a proof that
//!   `standing.rs` is verified.
#![cfg(loom)]

use std::sync::atomic::{AtomicBool as StdBool, AtomicUsize as StdUsize, Ordering as StdOrd};

use loom::sync::{Arc, Mutex};
use loom::thread;

/// The per-source connection cap under test (`config::max_connections()` for one
/// source's stripe). `1` puts the boundary between "admit" and "refuse" right where
/// two concurrent accepts collide — the tightest witness for the TOCTOU corner.
const CAP: u32 = 1;

/// One source's striped standing slot: `active` is `SharedStanding`'s
/// `active(ip)` count; `peak` is the max `active` ever reached — the run-time
/// witness that the cap was never exceeded (`peak <= CAP` iff no over-admit).
#[derive(Default)]
struct Gate {
    active: u32,
    peak: u32,
}

/// FAITHFUL `admit`: the whole check-and-increment under ONE stripe lock
/// (`standing.rs:229-237`). Returns whether this accept was admitted.
fn admit(gate: &Mutex<Gate>, cap: u32) -> bool {
    let mut g = gate.lock().unwrap();
    if cap != 0 && g.active >= cap {
        return false;
    }
    g.active += 1;
    if g.active > g.peak {
        g.peak = g.active;
    }
    true
}

/// FAITHFUL `on_close` (`standing.rs:241-249`): one decrement under the stripe lock.
fn close(gate: &Mutex<Gate>) {
    let mut g = gate.lock().unwrap();
    g.active = g.active.saturating_sub(1);
}

/// Count of loom schedules explored, per test, for the report.
static ITERS_OVER: StdUsize = StdUsize::new(0);
static ITERS_CONS: StdUsize = StdUsize::new(0);

/// PRIMARY ASSURANCE. Two concurrent accepts from ONE source race on that source's
/// stripe with `cap == 1`. loom explores every interleaving of the two critical
/// sections; the invariant asserted is **no over-admit**:
///   (a) peak: `active` never exceeds `cap` at any point (the run-time `ConnLimit`
///       bound) — enforced by the `peak` witness recorded inside each admit;
///   (b) decision consistency: EXACTLY ONE of the two racing accepts is admitted
///       (`cap == 1`), never both, never neither;
///   (c) conservation: the final `active` equals the number admitted — every admit
///       is exactly one increment, no lost or duplicated count.
/// Green over all schedules = the single-critical-section admit is TOCTOU-free for
/// this model.
#[test]
fn admit_gate_never_over_admits() {
    loom::model(|| {
        ITERS_OVER.fetch_add(1, StdOrd::Relaxed);

        let gate = Arc::new(Mutex::new(Gate::default()));

        // Two accept threads, same source, contending on the one stripe lock.
        let g1 = gate.clone();
        let a1 = thread::spawn(move || admit(&g1, CAP));
        let g2 = gate.clone();
        let a2 = thread::spawn(move || admit(&g2, CAP));

        let admitted = a1.join().unwrap() as u32 + a2.join().unwrap() as u32;

        let g = gate.lock().unwrap();
        assert!(
            g.peak <= CAP,
            "OVER-ADMIT: active peaked at {} over cap {} — two accepts both slipped past the ConnLimit boundary",
            g.peak,
            CAP
        );
        assert_eq!(
            admitted, CAP,
            "decision consistency: with cap {CAP} exactly one of two racing accepts must be admitted"
        );
        assert_eq!(
            g.active, admitted,
            "conservation: final active must equal the number admitted (one increment per admit)"
        );
    });

    eprintln!(
        "loom: admit_gate_never_over_admits — {} schedules explored, no over-admit",
        ITERS_OVER.load(StdOrd::Relaxed)
    );
}

/// PRIMARY ASSURANCE (accept/close conservation). Two workers each admit-then-close
/// on one source (`cap == 1`): the interleaving of one worker's `on_close` with the
/// other's `admit` is the accept/close race. Over every interleaving:
///   (a) peak: `active` never exceeds `cap` (a concurrent close never lets a second
///       admit push the source over the cap mid-flight);
///   (b) conservation: the source returns to `active == 0` — every admitted conn is
///       closed exactly once, no double-count, no residue, no underflow.
#[test]
fn admit_close_conserved() {
    loom::model(|| {
        ITERS_CONS.fetch_add(1, StdOrd::Relaxed);

        let gate = Arc::new(Mutex::new(Gate::default()));

        // Two workers: each admits, and if admitted, closes when it "returns".
        let g1 = gate.clone();
        let w1 = thread::spawn(move || {
            if admit(&g1, CAP) {
                close(&g1);
                true
            } else {
                false
            }
        });
        let g2 = gate.clone();
        let w2 = thread::spawn(move || {
            if admit(&g2, CAP) {
                close(&g2);
                true
            } else {
                false
            }
        });

        w1.join().unwrap();
        w2.join().unwrap();

        let g = gate.lock().unwrap();
        assert!(
            g.peak <= CAP,
            "OVER-ADMIT under concurrent close: active peaked at {} over cap {}",
            g.peak,
            CAP
        );
        assert_eq!(
            g.active, 0,
            "conservation: every admitted conn closed exactly once — active must return to zero"
        );
    });

    eprintln!(
        "loom: admit_close_conserved — {} schedules explored, conserved (active returns to zero, never over cap)",
        ITERS_CONS.load(StdOrd::Relaxed)
    );
}

/// TEETH. The *counter-model*: a BROKEN `admit` that splits the check and the
/// increment into TWO critical sections (reads `active` under the lock, DROPS the
/// lock, then re-takes it to increment) — the classic TOCTOU. Two concurrent
/// accepts on `cap == 1` can both read `active == 0` in the first critical section,
/// both pass the `< cap` check, and both increment in the second: the source ends
/// with `active == 2 > cap`, an over-admit past the `ConnLimit` gate. loom finds
/// that interleaving. This proves (a) holding the lock across the WHOLE
/// check-and-increment is load-bearing, and (b) the green safe tests above are
/// meaningful: loom WOULD have caught a gate that releases the lock mid-decision.
///
/// The bad state is detected and flagged (not asserted-against) so the test passes
/// exactly when loom REACHES the over-admit — the same static-flag teeth pattern
/// `ring-twin`, the gap-F litmus, and the SplitSend litmus use.
#[test]
fn split_check_and_increment_over_admits() {
    static OVER_ADMIT_REACHED: StdBool = StdBool::new(false);

    /// BROKEN admit: check in one critical section, increment in another.
    fn admit_broken(gate: &Mutex<Gate>, cap: u32) -> bool {
        // First critical section: read the count, then RELEASE the lock.
        let n = {
            let g = gate.lock().unwrap();
            g.active
        };
        if cap != 0 && n >= cap {
            return false;
        }
        // TOCTOU window: a concurrent accept that read the same `n` before either
        // incremented has also passed the check. Second critical section: increment.
        let mut g = gate.lock().unwrap();
        g.active += 1;
        if g.active > g.peak {
            g.peak = g.active;
        }
        true
    }

    loom::model(|| {
        let gate = Arc::new(Mutex::new(Gate::default()));

        let g1 = gate.clone();
        let a1 = thread::spawn(move || admit_broken(&g1, CAP));
        let g2 = gate.clone();
        let a2 = thread::spawn(move || admit_broken(&g2, CAP));

        let admitted = a1.join().unwrap() as u32 + a2.join().unwrap() as u32;

        let g = gate.lock().unwrap();
        if g.peak > CAP || admitted > CAP {
            // Both accepts slipped past the cap: the source is over-admitted.
            OVER_ADMIT_REACHED.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        OVER_ADMIT_REACHED.load(StdOrd::Relaxed),
        "loom found NO over-admit with a split check-and-increment — the teeth test \
         is broken; the green safe tests no longer witness that the single critical \
         section is load-bearing"
    );
    eprintln!(
        "loom: split_check_and_increment_over_admits — over-admit REACHED (as expected); \
         holding the stripe lock across the whole check-and-increment is load-bearing"
    );
}
