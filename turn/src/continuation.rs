//! continuation: a partial turn / promise as a PASSABLE umem.
//!
//! # The revolution
//!
//! Today a pending turn (`crate::pending::PendingEntry`) suspends by re-storing the
//! WHOLE `Turn` plus its [`ResolutionCondition`](crate::pending::ResolutionCondition):
//! when the condition is met, the node RE-EXECUTES the turn from its original pre-state.
//! The "intermediate computation state" of a turn that is mid-flight is BESPOKE — there
//! is no first-class object that says "here is exactly where the computation paused, with
//! its accumulated state captured, ready to be handed off and resumed from THAT point."
//!
//! The universal-memory bridge (`crate::umem`) already gives us exactly that object: a
//! [`UProjection`](crate::umem::UProjection) is a portable, witnessed snapshot of executor
//! state, and a [`UmemOp`](crate::umem::UmemOp) trace is the Blum memory-op program whose
//! [`fold`](crate::umem::fold) carries one projection to the next under the memcheck
//! discipline ([`disciplined`](crate::umem::disciplined)).
//!
//! So a **continuation = a passable umem**: the intermediate projection reached so far,
//! PLUS the remaining ops still to fold. Resuming a continuation = handing the umem back
//! and folding the rest. Resolving a promise = handing back the umem that the resolution
//! produced. This braids CapTP promise-pipelining DOWN into the memory layer: the thing
//! that flows along the pipe is not a re-runnable `Turn` but a captured, witnessed
//! intermediate state.
//!
//! ```text
//!   run straight through:   pre --[op0 op1 | op2 op3]--> post
//!
//!   suspend at the cut:     pre --[op0 op1]--> MID          (capture MID as a umem)
//!                                              MID  ════════►  (hand off: serialize, send)
//!   resume from the umem:                      MID --[op2 op3]--> post
//!
//!   THE GUARANTEE:  resume(suspend(pre, [op0 op1 | op2 op3])) == fold(pre, all_ops)
//! ```
//!
//! # What this module IS (and is not)
//!
//! This is the **continuation object + the suspend/resume round-trip** over the REAL
//! `crate::umem` machinery — `Continuation` carries a genuine [`UProjection`] intermediate
//! state and a genuine remaining-[`UmemOp`] tail, and [`Continuation::resume`] folds the
//! tail under the same memcheck semantics the executor-state bridge uses. The round-trip
//! is witnessed: the resumed post equals the run-straight-through post, and the discipline
//! holds across the cut.
//!
//! It is NOT yet wired to a mid-forest executor checkpoint. The executor's journal is
//! whole-turn (`crate::umem::emit_trace` re-reads the journal AFTER the turn commits),
//! so capturing a continuation from a turn paused *between two of its effects* needs the
//! one seam named below.
//!
//! ## THE SEAM — `mid-forest checkpoint`
//!
//! To capture a continuation from the LIVE executor mid-flight (rather than from a trace
//! cut, as this module proves), the executor must expose a checkpoint between two effects
//! of a running call-forest: snapshot the journal-so-far as a `UProjection` (it already
//! can, via `project_executor_state` + the prefix of the journal), emit the prefix ops,
//! and hand the rest of the forest forward as the continuation's "remaining work". The
//! hook would live next to `crate::executor::execute`'s forest walk (`executor/execute.rs`,
//! the depth-first effect application loop) — a `yield_point` that returns a
//! `Continuation` instead of completing. Until that hook exists, a continuation is
//! captured from a completed turn's trace (this module) — which is sufficient to PROVE the
//! round-trip is sound, and to carry promise-resolution intermediate state across the pipe.

use serde::{Deserialize, Serialize};

use crate::umem::{UKey, UProjection, UVal, UmemKind, UmemOp, disciplined, fold};

/// A continuation captured as a passable umem: the intermediate projection reached so far,
/// plus the remaining Blum ops still to fold to reach the final state.
///
/// This is the first-class object a partial turn / promise suspends INTO. It is
/// `Serialize`/`Deserialize` — a continuation can be handed off (suspended on one machine,
/// resumed on another), which is the whole point: the intermediate computation state is a
/// portable witnessed object, not a bespoke in-memory parking slot.
///
/// `captured` is serialized as an ordered `Vec` of `(UKey, UVal)` pairs (NOT the in-memory
/// `BTreeMap`), because the structured `UKey` is an enum, not a string — a JSON/postcard map
/// requires string keys. The `Vec` form is canonical: the map's `BTreeMap` iteration order is
/// deterministic, so the wire bytes are stable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Continuation {
    /// The intermediate executor-state projection reached at the suspend point — the
    /// captured umem, as an ordered key/value list. Resuming folds
    /// [`remaining`](Self::remaining) over THIS.
    captured: Vec<(UKey, UVal)>,
    /// The remaining Blum memory-ops still to fold, with serials re-based so the captured
    /// umem is the init boundary (see [`suspend`](Self::suspend)). On resume, these are
    /// applied (under the memcheck discipline) to `captured` to reach the final state.
    pub remaining: Vec<UmemOp>,
    /// How many ops were already folded into the captured umem before the cut. Carried for
    /// debuggability and for the hand-off receipt; not load-bearing for the fold.
    pub consumed: usize,
}

/// Why a [`Continuation::resume`] refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResumeError {
    /// The remaining ops violate the per-op memcheck discipline (a read whose returned
    /// value disagrees with its claimed prev, or a non-monotone serial). A continuation
    /// whose tail is undisciplined is not a genuine suspension and is refused fail-closed.
    Undisciplined,
    /// A remaining op claims a previous value that disagrees with the captured intermediate
    /// state at that address — the tail does not belong to THIS captured umem (a spliced or
    /// mismatched continuation). Refused fail-closed.
    PrevMismatch {
        /// Debug rendering of the offending op's address.
        key: String,
    },
}

impl std::fmt::Display for ResumeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResumeError::Undisciplined => {
                write!(f, "continuation tail violates the memcheck discipline")
            }
            ResumeError::PrevMismatch { key } => write!(
                f,
                "continuation tail's prev claim at {key} does not match the captured umem"
            ),
        }
    }
}

impl std::error::Error for ResumeError {}

impl Continuation {
    /// **SUSPEND** — cut a full Blum program `(pre, ops)` at `cut` and capture the prefix's
    /// resulting state as a passable umem.
    ///
    /// `pre` is the state before the program; `ops` is the whole program; `cut` is how many
    /// ops have already run (the suspend point). The returned `Continuation` carries the
    /// intermediate projection `fold(pre, ops[..cut])` and the remaining tail `ops[cut..]`.
    ///
    /// `cut` is clamped to `ops.len()` (a cut at the end yields an empty tail — a
    /// continuation that resumes to its captured state unchanged).
    ///
    /// The tail's serials are RE-BASED so the captured umem is the new init boundary: each
    /// remaining op's positional serial drops by `cut`, and any `prev_serial` that pointed
    /// before the cut becomes `0` (the init boundary of the resumed program). This keeps the
    /// tail self-[`disciplined`](crate::umem::disciplined) on its own — a suspended program
    /// is a genuine standalone program over its captured state, which is what makes it
    /// passable.
    pub fn suspend(pre: &UProjection, ops: &[UmemOp], cut: usize) -> Self {
        let cut = cut.min(ops.len());
        let captured_map = fold(pre, &ops[..cut]);
        let cut_serial = cut as u64;
        let remaining = ops[cut..]
            .iter()
            .map(|op| {
                let mut op = op.clone();
                // A prev_serial referencing a pre-cut position folds into the init boundary
                // (0); one referencing a post-cut position shifts down by `cut`.
                op.prev_serial = op.prev_serial.saturating_sub(cut_serial);
                op
            })
            .collect();
        Continuation {
            captured: captured_map.into_iter().collect(),
            remaining,
            consumed: cut,
        }
    }

    /// The captured intermediate umem as a `UProjection` (rebuilt from the wire list).
    pub fn captured(&self) -> UProjection {
        self.captured.iter().cloned().collect()
    }

    /// **RESUME** — fold the remaining ops over the captured umem to reach the final state.
    ///
    /// Fail-closed: the remaining tail must be self-disciplined (the memcheck per-op rule)
    /// AND every op's claimed prev must match the captured intermediate state as the fold
    /// walks it — otherwise the continuation is rejected (it is not a genuine suspension of
    /// THIS computation).
    pub fn resume(&self) -> Result<UProjection, ResumeError> {
        if !disciplined(&self.remaining) {
            return Err(ResumeError::Undisciplined);
        }
        // Walk the tail, checking each op's prev claim against the running fold from the
        // captured state — the same independent re-walk the umem bridge test uses as teeth.
        let mut current = self.captured();
        for op in &self.remaining {
            if op.prev_val != current.get(&op.key).cloned() {
                return Err(ResumeError::PrevMismatch {
                    key: format!("{:?}", op.key),
                });
            }
            if let UmemKind::Write = op.kind {
                match &op.val {
                    Some(v) => {
                        current.insert(op.key.clone(), v.clone());
                    }
                    None => {
                        current.remove(&op.key);
                    }
                }
            }
        }
        Ok(current)
    }

    /// Is this continuation already fully resolved (nothing left to fold)? A continuation
    /// suspended at the end of its program resumes to its captured state.
    pub fn is_complete(&self) -> bool {
        self.remaining.is_empty()
    }

    /// Serialize this continuation for hand-off (the passable-umem wire form).
    pub fn to_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(self).expect("continuation: canonical JSON encoding")
    }

    /// Deserialize a handed-off continuation.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, serde_json::Error> {
        serde_json::from_slice(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::CellId;

    fn cell(b: u8) -> CellId {
        CellId([b; 32])
    }

    /// Build a small, disciplined two-write program: set balance(c1) 10→20, then 20→30.
    /// Returns (pre, ops).
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

    /// THE round-trip keystone: suspend at every cut, resume, and get the SAME post as
    /// running straight through.
    #[test]
    fn suspend_resume_equals_straight_through() {
        let (pre, ops) = program();
        let straight = fold(&pre, &ops);

        for cut in 0..=ops.len() {
            let k = Continuation::suspend(&pre, &ops, cut);
            let resumed = k.resume().expect("disciplined continuation resumes");
            assert_eq!(
                resumed, straight,
                "suspend at cut {cut} then resume must equal run-straight-through"
            );
        }
    }

    /// The continuation survives a HAND-OFF: serialize at the cut, deserialize elsewhere,
    /// resume — still the same post. This is the "pass a umem-ref down the pipe" property.
    #[test]
    fn handoff_round_trip() {
        let (pre, ops) = program();
        let straight = fold(&pre, &ops);

        let suspended = Continuation::suspend(&pre, &ops, 1);
        let wire = suspended.to_bytes();
        // ... travels across the pipe / to another machine ...
        let landed = Continuation::from_bytes(&wire).expect("handed-off continuation decodes");
        assert_eq!(landed, suspended, "hand-off is byte-faithful");

        let resumed = landed.resume().expect("resumes after hand-off");
        assert_eq!(
            resumed, straight,
            "resume after hand-off reaches the final state"
        );
    }

    /// A continuation cut at the end is complete and resumes to its captured state.
    #[test]
    fn complete_continuation_is_identity() {
        let (pre, ops) = program();
        let k = Continuation::suspend(&pre, &ops, ops.len());
        assert!(k.is_complete());
        assert_eq!(k.resume().unwrap(), k.captured());
        assert_eq!(k.resume().unwrap(), fold(&pre, &ops));
    }

    /// TEETH (fail-closed): a continuation whose tail's prev claim was tampered to no
    /// longer match the captured umem is REFUSED — you cannot smuggle a foreign tail onto
    /// a captured intermediate state.
    #[test]
    fn tampered_tail_refused() {
        let (pre, ops) = program();
        let mut k = Continuation::suspend(&pre, &ops, 1);
        // The captured umem has balance(c1) == 20. Forge the tail's prev to 999.
        k.remaining[0].prev_val = Some(UVal::Int(999));
        assert!(
            matches!(k.resume(), Err(ResumeError::PrevMismatch { .. })),
            "a tail that does not belong to the captured umem must be refused"
        );
    }

    /// TEETH (fail-closed): an undisciplined tail (a read whose returned value disagrees
    /// with its claimed prev) is refused.
    #[test]
    fn undisciplined_tail_refused() {
        // Build a continuation whose captured umem has balance(c1) == 20, then forge the
        // tail into an undisciplined READ (returned value != claimed prev). We construct it
        // via suspend (the public path) and then corrupt the tail to be a bad read.
        let mut pre = UProjection::new();
        pre.insert(UKey::Balance(cell(1)), UVal::Int(20));
        let mut k = Continuation::suspend(&pre, &[], 0);
        k.remaining = vec![UmemOp {
            kind: UmemKind::Read,
            key: UKey::Balance(cell(1)),
            val: Some(UVal::Int(20)),
            prev_val: Some(UVal::Int(999)), // read returns != claimed prev: undisciplined
            prev_serial: 0,
        }];
        assert_eq!(k.resume(), Err(ResumeError::Undisciplined));
    }
}
