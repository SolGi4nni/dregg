//! SYMBOLIC EXECUTION — a runtime witness mode + a collapse orchestrator.
//!
//! # The thesis
//!
//! A turn's *state transition* (balances / capabilities / nonces) is the
//! `AbstractState = (balanceTotal, authGraph)` progress proved witness-FREE in
//! `metatheory/Dregg2/Spec/ExecRefinement.lean` (`Exec ⊑ Abstract`). The
//! *witness layer* — the per-turn `pre_state_hash` / `post_state_hash` Merkle
//! commitments folded into the receipt — is a SEPARATE, derivable artifact: it
//! is what a remote light client needs to be convinced, NOT what the local
//! state transition needs to *happen*.
//!
//! [`WitnessMode::Symbolic`] exploits that split. A symbolic turn applies the
//! full state transition (the abstract progress) but DEFERS witness
//! materialization: it does not compute the state anchor
//! (`crate::state_commit`, the AIR-bound chip 8-felt commitment), so its receipt carries a
//! DEFERRED sentinel post/pre state hash ([`DEFERRED_STATE_HASH`], all-zeros,
//! which the conditional/atomic paths already tolerate). The witnesses are
//! recovered ON DEMAND by [`collapse`], which re-runs the recorded symbolic
//! turns through FULL execution to reproduce EXACTLY what a Full run would have
//! witnessed.
//!
//! # Soundness — what stays invariant
//!
//! Symbolic mode defers only the WITNESS, never a DECISION:
//!
//! * **Full is the correct default.** [`WitnessMode::default`] is `Full`. A
//!   caller opts into `Symbolic` explicitly, for local/unpublishable work.
//! * **Admission gates are NOT deferred.** Every legality gate — the
//!   `NoteSpend` STARK, committed-note conservation, the sovereign-witness
//!   check, authority/no-amplification, nonce/fee — runs IDENTICALLY in both
//!   modes. Symbolic skips computing the Merkle *root*; it never skips the
//!   *decision* a turn's legality rests on. A turn that is rejected in Full is
//!   rejected in Symbolic, at the same action, for the same reason.
//! * **Symbolic state is local / unpublishable, and the verifiers ENFORCE
//!   that.** A receipt carrying [`DEFERRED_STATE_HASH`] is not a network
//!   artifact: it has no usable commitment to publish to a light client.
//!   Publishing requires [`collapse`], the ONLY witness path. Every chain
//!   verifier in `crate::verify` refuses such a receipt outright
//!   (`VerifyError::DeferredWitness`) unless the caller names the
//!   `*_allowing_deferred` variant, which is for verifying one's OWN
//!   un-collapsed chain and nothing else. Until 2026-07-31 this paragraph was
//!   the only thing standing between a deferred receipt and a verifier's
//!   `Ok(())`: `is_deferred` had zero callers outside two `debug_assert!`s,
//!   both compiled out in release.
//! * **Collapse reproduces Full.** Determinism is already discharged (the
//!   pinned timestamp + cost model + the recorded post-root tooth), so
//!   re-running a recorded turn under Full re-derives the byte-identical
//!   receipt a Full run would have produced. [`collapse`] asserts this against
//!   the recorded post-root teeth.
//!
//! # What is deferred (and what is not, yet)
//!
//! The DOMINANT per-turn witness cost is the ledger Merkle `Ledger::root()`
//! materialization (O(k·log N) over the touched cells, or an O(N) rebuild on a
//! structural change) folded into `pre_state_hash` / `post_state_hash`. That is
//! what Symbolic defers, on both the live engine receipt AND the replay-tape
//! double-execution (the World skips `History::record_commit` and buffers the
//! turn).
//!
//! NOT yet deferred: the per-cell EXTENDED-FIELD / HEAP sub-roots
//! (`CellState::set_field_ext` / `set_heap` in the `cell` crate eagerly call
//! `compute_fields_root` / `compute_heap_root`). These fire only for
//! extended-key field writes and heap effects (not the common
//! transfer/cap/nonce path), and deferring them needs a `Ledger::Pending`-style
//! mark-dirty refactor of `CellState` with its own membership-witness
//! invariants — a `cell`-crate change out of this module's scope. Noted as a
//! follow-up; the ledger-root deferral is the headline saving.
//!
//! # The known architectural gap
//!
//! The *light-client semantics of a deferred-witness turn* are out of scope:
//! an un-collapsed symbolic receipt cannot convince a remote verifier (it has
//! no real commitment). That is by design — Symbolic is a LOCAL fast path, and
//! `collapse` is the bridge back to publishable witnesses. A turn must be
//! collapsed before its receipt crosses the publish boundary.

use crate::turn::{Turn, TurnReceipt};
use crate::{ComputronCosts, TurnExecutor};
use dregg_cell::Ledger;

/// The DEFERRED sentinel a symbolic receipt carries in its state-hash fields.
///
/// All-zeros — the same value the conditional / atomic execution paths already
/// tolerate as "no materialized root here yet". It is NOT a real commitment:
/// it is the marker that says "this turn's witness was deferred; collapse to
/// materialize it". A receipt carrying this is local-only and unpublishable.
pub const DEFERRED_STATE_HASH: [u8; 32] = [0u8; 32];

/// `true` iff `receipt`'s state-hash fields are the deferred sentinel — i.e.
/// this receipt was produced under [`WitnessMode::Symbolic`] and has NOT yet
/// been collapsed to real witnesses. Such a receipt is local-only: its
/// `pre_state_hash` / `post_state_hash` are not real commitments and must not
/// cross the publish boundary until [`collapse`] materializes them.
pub fn is_deferred(receipt: &TurnReceipt) -> bool {
    receipt.post_state_hash == DEFERRED_STATE_HASH && receipt.pre_state_hash == DEFERRED_STATE_HASH
}

/// The runtime witness mode of the executor.
///
/// This selects ONLY whether per-turn Merkle witnesses are materialized eagerly
/// (the publishable default) or deferred (the local fast path). It does NOT
/// change which turns are admitted: every legality gate runs identically in
/// both modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum WitnessMode {
    /// THE CORRECT DEFAULT. Every committed turn materializes its
    /// `pre_state_hash` / `post_state_hash` state anchors (the AIR-bound chip
    /// 8-felt commitment, `crate::state_commit`), so the receipt is immediately
    /// publishable to a light client.
    #[default]
    Full,
    /// THE LOCAL FAST PATH. The state transition fully applies (balances /
    /// caps / nonces — the abstract progress), but witness materialization is
    /// DEFERRED: the executor does not compute the state anchor, and the receipt
    /// carries [`DEFERRED_STATE_HASH`] in its state-hash fields. A symbolic
    /// receipt is local/unpublishable until [`collapse`] re-derives its real
    /// witnesses. Admission gates are NOT deferred — only the witness is.
    Symbolic,
}

impl WitnessMode {
    /// `true` for [`WitnessMode::Symbolic`] (witness deferred).
    pub fn is_symbolic(&self) -> bool {
        matches!(self, WitnessMode::Symbolic)
    }

    /// The `u8` wire/atomic encoding (`0` = Full, `1` = Symbolic).
    pub fn as_u8(&self) -> u8 {
        match self {
            WitnessMode::Full => 0,
            WitnessMode::Symbolic => 1,
        }
    }

    /// Decode from the `u8` atomic encoding. Any non-`1` value is `Full` (the
    /// safe default — an unrecognized mode never silently drops witnesses).
    pub fn from_u8(v: u8) -> Self {
        match v {
            1 => WitnessMode::Symbolic,
            _ => WitnessMode::Full,
        }
    }
}

/// The outcome of collapsing a recorded symbolic run back to real witnesses.
#[derive(Clone, Debug)]
pub struct CollapseResult {
    /// The witnessed receipts, in turn order — each with REAL materialized
    /// `pre_state_hash` / `post_state_hash` (exactly what a Full run produces).
    pub receipts: Vec<TurnReceipt>,
    /// The final materialized ledger root after replaying all collapsed turns —
    /// the publishable commitment to the post-state.
    pub final_root: [u8; 32],
}

/// Re-run `turns` (a recorded symbolic run) through FULL execution against a
/// freshly-seeded `ledger`, materializing the real witnesses + commitments that
/// Symbolic mode deferred.
///
/// `ledger` MUST be seeded to the SAME pre-state the symbolic run started from
/// (e.g. a clone of the world's pre-symbolic ledger, or a fresh genesis replay),
/// and `timestamp` / `costs` MUST match the symbolic run's pinned config — under
/// those equalities the receipts re-derive byte-identically (the determinism the
/// replay tape already relies on).
///
/// Because Full is the executor's default behavior, collapse is just "run the
/// recorded turns with witnesses on": every legality gate already passed under
/// Symbolic (admission is mode-independent), so each turn commits again, and the
/// materialized `post_state_hash` equals the witness a Full run would have
/// produced at that step.
///
/// Returns the witnessed receipts + the final materialized root. Returns
/// `Err(reason)` if any recorded turn does NOT re-commit — a real integrity
/// event (it would mean the symbolic run admitted a turn Full execution
/// refuses, which the shared admission gate makes impossible barring corruption).
pub fn collapse(
    turns: &[Turn],
    mut ledger: Ledger,
    timestamp: i64,
    costs: ComputronCosts,
) -> Result<CollapseResult, String> {
    // A fresh FULL executor pinned to the symbolic run's config. Full is the
    // default mode, so this materializes every witness.
    let mut exec = TurnExecutor::new(costs);
    exec.set_timestamp(timestamp);
    collapse_with(turns, &mut exec, &mut ledger)
}

/// [`collapse`] against a caller-provided executor + ledger (already pinned and
/// seeded). Used when the caller needs the collapse to run against an executor
/// configured identically to the live one (factories, federation id, chain
/// heads) — e.g. the world's collapse path, which clones its live config.
///
/// `exec` MUST be in [`WitnessMode::Full`] (collapse's whole purpose is to
/// materialize witnesses); it is forced to Full here defensively.
pub fn collapse_with(
    turns: &[Turn],
    exec: &mut TurnExecutor,
    ledger: &mut Ledger,
) -> Result<CollapseResult, String> {
    // Defensive: collapse materializes witnesses, so it MUST run Full.
    exec.set_witness_mode(WitnessMode::Full);

    let mut receipts = Vec::with_capacity(turns.len());
    for (i, turn) in turns.iter().enumerate() {
        // Thread the chain head exactly as the live commit path does, so the
        // re-derived receipt chains identically.
        let mut turn = turn.clone();
        turn.previous_receipt_hash = exec.get_last_receipt_hash(&turn.agent);
        match exec.execute(&turn, ledger) {
            crate::turn::TurnResult::Committed { receipt, .. } => {
                exec.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                // A collapsed receipt is a Full receipt: its witness is real.
                // This is a RETURN, not a `debug_assert!` — collapse is the only
                // bridge to a publishable receipt, and a check that is compiled
                // out in release is exactly the check a release build needs.
                if is_deferred(&receipt) {
                    return Err(format!(
                        "collapse: re-derived receipt #{i} (agent {:?}) STILL carries the \
                         deferred sentinel — collapse must materialize a real witness, and \
                         this one would leave the publish boundary uncommitted",
                        receipt.agent
                    ));
                }
                receipts.push(receipt);
            }
            other => {
                return Err(format!(
                    "collapse: recorded symbolic turn #{i} (agent {:?}) did NOT re-commit \
                     under Full execution ({}) — this is an integrity event (the symbolic run \
                     admitted a turn Full execution refuses)",
                    turn.agent,
                    match other {
                        crate::turn::TurnResult::Rejected { reason, at_action } =>
                            format!("rejected: {reason:?} at action {at_action:?}"),
                        crate::turn::TurnResult::Expired => "expired".to_string(),
                        crate::turn::TurnResult::Pending => "pending".to_string(),
                        crate::turn::TurnResult::Committed { .. } => unreachable!(),
                    }
                ));
            }
        }
    }

    // The collapse's materialized head is the LAST re-derived receipt's AIR-bound
    // post-state anchor — the same object the receipts chain on. (It was
    // `ledger.root()`, the trusted-Rust BLAKE3 tree; that value is not comparable
    // to what the receipts now carry, so taking it from the chain head is both
    // correct and the only self-consistent choice.) An empty collapse materialized
    // no transition, so its head is the deferred sentinel.
    let final_root = receipts
        .last()
        .map(|r| r.post_state_hash)
        .unwrap_or(DEFERRED_STATE_HASH);
    Ok(CollapseResult {
        receipts,
        final_root,
    })
}
