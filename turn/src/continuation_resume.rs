//! continuation_resume: THE LIVE PROMISE-RESUME PATH — a suspended turn's captured
//! continuation (a passable umem) is parked awaiting resolution, handed off, and on
//! resolution RESUMED to its post-state and reified into the running ledger — completing
//! the turn WITHOUT re-executing it.
//!
//! # The revolution made load-bearing
//!
//! [`crate::continuation`] gives the first-class object — a continuation = the captured
//! intermediate [`UProjection`](crate::umem::UProjection) plus the remaining Blum ops still
//! to fold — and `turn/tests/mid_forest_yield_point.rs` proves the executor captures a
//! genuine mid-flight boundary and that `resume()` reaches the straight-through post. But
//! that resume is checked against a witness; nothing in the running system DEPENDS on it.
//!
//! Today's pending machinery ([`crate::pending::PendingTurnRegistry`]) suspends a turn by
//! re-storing the WHOLE [`Turn`](crate::turn::Turn) plus its
//! [`ResolutionCondition`](crate::pending::ResolutionCondition) and, when the condition is
//! met, RE-EXECUTES the turn from its original pre-state. The intermediate computation it
//! already performed is thrown away and recomputed.
//!
//! This module is the third revolution (after time-travel and agent-memory) made LIVE: a
//! suspended turn parks its continuation — the captured passable umem of the work already
//! done — under the SAME promise vocabulary (`ResolutionCondition` / `BrokenReason` from
//! [`crate::pending`]). When the promise resolves, the parked continuation is handed back,
//! [`Continuation::resume`](crate::continuation::Continuation::resume)d (folding the
//! remaining tail to the post projection), and [`reify_ledger`](crate::umem::reify_ledger)d
//! into the running ledger. The turn COMPLETES by resuming the passable umem, not by
//! re-running its effects. This is "a promise IS a passable umem" closing the loop in the
//! live pending machinery.
//!
//! ```text
//!   suspend (mid-forest yield):  pre --[ops..cut]--> MID   (capture MID as a Continuation)
//!                                MID  ════════►  park + serialize + hand off (the promise)
//!   resolve (condition met):     MID --[ops cut..]--> POST (resume the tail)
//!                                POST  ──reify_ledger──►  the running ledger (turn complete)
//!
//!   THE GUARANTEE:  reify_ledger(resume(suspend(turn))) == the ledger straight-through run.
//! ```
//!
//! # Soundness (fail-closed, inherited — nothing new is trusted)
//!
//!  * [`Continuation::resume`](crate::continuation::Continuation::resume) already refuses an
//!    undisciplined tail or a tail whose prev-claims do not match the captured umem (a
//!    spliced / foreign continuation): [`ResumeError`]. A handed-off continuation that was
//!    tampered in flight cannot be resumed.
//!  * [`reify_ledger`](crate::umem::reify_ledger) refuses a post projection outside the
//!    faithful class (interfaces / cap tombstones / inconsistent heap boundary):
//!    [`ReifyError`]. A resumed state that cannot reproduce a byte-identical ledger is
//!    refused rather than landed.
//!  * the resume reaches the WHOLE-turn post (the full remaining tail is folded), so the
//!    landed state is exactly what straight-through execution commits — NOT the mid-forest
//!    prefix the atomicity note in [`crate::continuation`] warns is non-committable.

use std::collections::HashMap;

use dregg_cell::Ledger;
use serde::{Deserialize, Serialize};

use crate::continuation::{Continuation, ResumeError};
use crate::pending::{BrokenReason, ResolutionCondition};
use crate::umem::{ReifyError, UProjection, reify_ledger};

/// A suspended turn parked as its passable-umem continuation, awaiting resolution.
///
/// `Serialize`/`Deserialize`: a parked continuation is the wire object handed off along the
/// promise pipe — suspended on one machine, resumed (after its condition is met) on another.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParkedContinuation {
    /// The captured continuation — the intermediate umem plus the remaining ops to fold.
    pub continuation: Continuation,
    /// The condition that must be met before the continuation may be resumed (the same
    /// vocabulary as [`crate::pending::PendingEntry`]).
    pub condition: ResolutionCondition,
    /// Block height at which this parked promise breaks if still unresolved.
    pub timeout_height: u64,
}

/// The outcome of resuming a parked continuation into the running ledger.
#[derive(Clone, Debug)]
pub struct ResumedTurn {
    /// The turn whose continuation was resumed.
    pub turn_hash: [u8; 32],
    /// The post-state projection the resumed tail folded to (the completed turn's state).
    pub post: UProjection,
    /// How many remaining ops the resume folded. `0` iff the parked continuation was already
    /// complete (suspended at the end of its program — resume is then an identity).
    pub resumed_ops: usize,
}

/// Why a parked continuation could not be resumed into the ledger (all fail-closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResumeFailure {
    /// No continuation is parked under this turn hash.
    NotParked([u8; 32]),
    /// The continuation's tail is not a genuine suspension of this computation (undisciplined
    /// or a prev-claim that does not match the captured umem) — see [`ResumeError`].
    BadTail(ResumeError),
    /// The resumed post-state is outside the reify faithful class — see [`ReifyError`].
    Unreifiable(ReifyError),
}

impl std::fmt::Display for ResumeFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResumeFailure::NotParked(h) => {
                write!(
                    f,
                    "no continuation parked under turn {:02x}{:02x}..",
                    h[0], h[1]
                )
            }
            ResumeFailure::BadTail(e) => write!(f, "continuation tail refused: {e}"),
            ResumeFailure::Unreifiable(e) => write!(f, "resumed post not reifiable: {e}"),
        }
    }
}

impl std::error::Error for ResumeFailure {}

/// Registry of suspended turns parked as passable-umem continuations.
///
/// Mirrors the shape of [`crate::pending::PendingTurnRegistry`] (it reuses that module's
/// [`ResolutionCondition`] / [`BrokenReason`]) but parks a CONTINUATION rather than a whole
/// re-runnable turn: resolution RESUMES the captured umem into the ledger instead of
/// re-executing from the pre-state.
#[derive(Clone, Debug, Default)]
pub struct ResumableTurnRegistry {
    parked: HashMap<[u8; 32], ParkedContinuation>,
}

impl ResumableTurnRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            parked: HashMap::new(),
        }
    }

    /// Park a captured continuation under `turn_hash`, awaiting `condition`.
    ///
    /// `continuation` is typically obtained from
    /// [`TurnExecutor::capture_yielded_continuation`](crate::executor::TurnExecutor::capture_yielded_continuation)
    /// after a mid-forest yield, or from
    /// [`Continuation::suspend`](crate::continuation::Continuation::suspend).
    pub fn park(
        &mut self,
        turn_hash: [u8; 32],
        continuation: Continuation,
        condition: ResolutionCondition,
        timeout_height: u64,
    ) {
        self.parked.insert(
            turn_hash,
            ParkedContinuation {
                continuation,
                condition,
                timeout_height,
            },
        );
    }

    /// Park an already-assembled [`ParkedContinuation`] (e.g. one decoded from a hand-off).
    pub fn park_entry(&mut self, turn_hash: [u8; 32], entry: ParkedContinuation) {
        self.parked.insert(turn_hash, entry);
    }

    /// Look up a parked continuation.
    pub fn get(&self, turn_hash: &[u8; 32]) -> Option<&ParkedContinuation> {
        self.parked.get(turn_hash)
    }

    /// Number of currently parked continuations.
    pub fn len(&self) -> usize {
        self.parked.len()
    }

    /// Whether the registry has no parked continuations.
    pub fn is_empty(&self) -> bool {
        self.parked.is_empty()
    }

    /// The turn hashes whose `AwaitHeight` condition is satisfied at `current_height` — the
    /// node should resume these (the continuation analogue of
    /// [`PendingTurnRegistry::check_height_conditions`](crate::pending::PendingTurnRegistry::check_height_conditions)).
    pub fn ready_by_height(&self, current_height: u64) -> Vec<[u8; 32]> {
        self.parked
            .iter()
            .filter(|(_, e)| {
                matches!(e.condition, ResolutionCondition::AwaitHeight(h) if current_height >= h)
            })
            .map(|(h, _)| *h)
            .collect()
    }

    /// The turn hashes whose `AwaitReceipt` condition is met by the arrival of
    /// `receipt_turn_hash` — the node should resume these.
    pub fn ready_by_receipt(&self, receipt_turn_hash: &[u8; 32]) -> Vec<[u8; 32]> {
        self.parked
            .iter()
            .filter(|(_, e)| {
                matches!(
                    &e.condition,
                    ResolutionCondition::AwaitReceipt { turn_hash, .. }
                    if turn_hash == receipt_turn_hash
                )
            })
            .map(|(h, _)| *h)
            .collect()
    }

    /// Break and DROP every parked continuation whose `timeout_height` has passed, reporting
    /// `(turn_hash, BrokenReason::Timeout)` for each — the promise broke before it resolved,
    /// so the suspended work is discarded (the ledger is never touched).
    pub fn break_timed_out(&mut self, current_height: u64) -> Vec<([u8; 32], BrokenReason)> {
        let expired: Vec<[u8; 32]> = self
            .parked
            .iter()
            .filter(|(_, e)| current_height > e.timeout_height)
            .map(|(h, _)| *h)
            .collect();
        let mut broken = Vec::with_capacity(expired.len());
        for h in expired {
            self.parked.remove(&h);
            broken.push((h, BrokenReason::Timeout));
        }
        broken
    }

    /// Drop a parked continuation as a broken promise (e.g. a dependency broke), reporting
    /// the reason. Returns `true` if a continuation was parked under `turn_hash`.
    pub fn break_promise(&mut self, turn_hash: [u8; 32], _reason: BrokenReason) -> bool {
        self.parked.remove(&turn_hash).is_some()
    }

    /// **RESUME INTO THE LEDGER** — the live completion step.
    ///
    /// Removes the parked continuation for `turn_hash`, RESUMES it (folding the remaining
    /// tail to the post projection under the memcheck discipline), reifies that post into a
    /// fresh ledger, and INSTALLS it into `ledger` — the suspended turn is now complete in
    /// the running system, having been finished by resuming the passable umem rather than
    /// re-executing its effects.
    ///
    /// Fail-closed: an absent entry ([`ResumeFailure::NotParked`]), a tail that is not a
    /// genuine suspension ([`ResumeFailure::BadTail`]), or a post outside the reify faithful
    /// class ([`ResumeFailure::Unreifiable`]) all refuse and leave `ledger` UNTOUCHED — the
    /// parked entry is restored on a reify refusal so the promise can be retried.
    ///
    /// The caller is responsible for having checked the resolution condition (via
    /// [`Self::ready_by_height`] / [`Self::ready_by_receipt`]) — exactly as the node drives
    /// [`PendingTurnRegistry`](crate::pending::PendingTurnRegistry).
    pub fn resume_into_ledger(
        &mut self,
        turn_hash: [u8; 32],
        ledger: &mut Ledger,
    ) -> Result<ResumedTurn, ResumeFailure> {
        let entry = self
            .parked
            .remove(&turn_hash)
            .ok_or(ResumeFailure::NotParked(turn_hash))?;

        let resumed_ops = entry.continuation.remaining.len();
        let post = match entry.continuation.resume() {
            Ok(p) => p,
            Err(e) => {
                // A bad tail is a hard refusal: do NOT re-park (the continuation is not a
                // genuine suspension and never will be).
                return Err(ResumeFailure::BadTail(e));
            }
        };
        let reified = match reify_ledger(&post) {
            Ok(l) => l,
            Err(e) => {
                // Reify refused (non-faithful post): restore the parked entry so the promise
                // can be retried, and leave `ledger` untouched.
                self.parked.insert(turn_hash, entry);
                return Err(ResumeFailure::Unreifiable(e));
            }
        };
        *ledger = reified;
        Ok(ResumedTurn {
            turn_hash,
            post,
            resumed_ops,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::umem::{UKey, UProjection, UVal, UmemKind, UmemOp};
    use dregg_cell::CellId;

    fn cell(b: u8) -> CellId {
        CellId([b; 32])
    }

    /// A two-write program against one balance: 10 -> 20 -> 30. Returns (pre, ops).
    fn program() -> (UProjection, Vec<UmemOp>) {
        let mut pre = UProjection::new();
        pre.insert(UKey::Balance(cell(1)), UVal::Int(10));
        let ops = vec![
            UmemOp {
                kind: UmemKind::Write,
                key: UKey::Balance(cell(1)),
                val: Some(UVal::Int(20)),
                prev_val: Some(UVal::Int(10)),
                prev_serial: 0,
            },
            UmemOp {
                kind: UmemKind::Write,
                key: UKey::Balance(cell(1)),
                val: Some(UVal::Int(30)),
                prev_val: Some(UVal::Int(20)),
                prev_serial: 1,
            },
        ];
        (pre, ops)
    }

    /// Parking, the height-condition readiness check, and resume bookkeeping over a pure
    /// continuation (no ledger reify — that lives in the integration test, which needs real
    /// cells). Proves the registry mirrors the pending vocabulary and that resume folds the
    /// remaining tail.
    #[test]
    fn park_ready_and_resume_bookkeeping() {
        let (pre, ops) = program();
        // Suspend after the first write — a genuine middle (one op already folded, one left).
        let cont = Continuation::suspend(&pre, &ops, 1);
        assert!(!cont.is_complete());

        let turn_hash = [7u8; 32];
        let mut reg = ResumableTurnRegistry::new();
        reg.park(turn_hash, cont, ResolutionCondition::AwaitHeight(100), 1000);
        assert_eq!(reg.len(), 1);

        // Not ready before height 100; ready at/after.
        assert!(reg.ready_by_height(99).is_empty());
        assert_eq!(reg.ready_by_height(100), vec![turn_hash]);

        // The parked continuation resumes to the straight-through post via a direct fold
        // (the reify-into-ledger step is exercised end-to-end in the integration test).
        let entry = reg.get(&turn_hash).unwrap();
        let resumed = entry
            .continuation
            .resume()
            .expect("disciplined tail resumes");
        let straight = crate::umem::fold(&pre, &ops);
        assert_eq!(
            resumed, straight,
            "resume reaches the straight-through post"
        );
        assert_eq!(entry.continuation.remaining.len(), 1, "one op left to fold");
    }

    /// A handed-off parked continuation survives serialize/deserialize byte-faithfully.
    #[test]
    fn parked_continuation_handoff_round_trip() {
        let (pre, ops) = program();
        let cont = Continuation::suspend(&pre, &ops, 1);
        let parked = ParkedContinuation {
            continuation: cont,
            condition: ResolutionCondition::AwaitHeight(50),
            timeout_height: 500,
        };
        let wire = serde_json::to_vec(&parked).expect("encodes");
        let landed: ParkedContinuation = serde_json::from_slice(&wire).expect("decodes");
        assert_eq!(
            landed, parked,
            "parked continuation is byte-faithful across the pipe"
        );
    }

    /// FAIL-CLOSED: resuming an absent turn refuses; a tampered tail refuses through the
    /// registry too (the BadTail path).
    #[test]
    fn resume_refuses_absent_and_tampered() {
        let mut reg = ResumableTurnRegistry::new();
        let mut ledger = Ledger::new();

        // Absent.
        assert!(matches!(
            reg.resume_into_ledger([9u8; 32], &mut ledger),
            Err(ResumeFailure::NotParked(h)) if h == [9u8; 32]
        ));

        // Tampered tail: forge the prev-claim so it no longer matches the captured umem.
        let (pre, ops) = program();
        let mut cont = Continuation::suspend(&pre, &ops, 1);
        cont.remaining[0].prev_val = Some(UVal::Int(999));
        let turn_hash = [1u8; 32];
        reg.park(turn_hash, cont, ResolutionCondition::AwaitHeight(0), 1000);
        let err = reg
            .resume_into_ledger(turn_hash, &mut ledger)
            .expect_err("a tampered tail must refuse");
        assert!(matches!(err, ResumeFailure::BadTail(_)));
        // A hard tail refusal does not re-park (it can never succeed).
        assert!(
            reg.is_empty(),
            "a bad-tail entry is consumed, not re-parked"
        );
    }

    /// A timed-out parked promise breaks and is dropped (the suspended work is discarded).
    #[test]
    fn timeout_breaks_and_drops() {
        let (pre, ops) = program();
        let cont = Continuation::suspend(&pre, &ops, 1);
        let mut reg = ResumableTurnRegistry::new();
        reg.park([3u8; 32], cont, ResolutionCondition::AwaitHeight(10), 100);

        assert!(reg.break_timed_out(50).is_empty(), "not timed out yet");
        let broken = reg.break_timed_out(101);
        assert_eq!(broken.len(), 1);
        assert_eq!(broken[0].0, [3u8; 32]);
        assert!(matches!(broken[0].1, BrokenReason::Timeout));
        assert!(reg.is_empty());
    }
}
