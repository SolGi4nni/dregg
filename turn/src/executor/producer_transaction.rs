//! Transaction boundary for the demoted Rust producer reference.
//!
//! `dregg-exec-lean` runs the Rust executor in place to obtain a differential
//! result and receipt substrate, then installs the verified Lean verdict. A
//! verified rejection must therefore undo more than the `Ledger`: the Rust run
//! may have advanced a receipt head, Stingray budget, rate-limit windows, or
//! executor observation state.
//!
//! Append-only note/revocation accumulators and the reactive/factory registries
//! are deliberately not cloned here. The producer fences every effect that can
//! mutate them *before* this checkpoint is taken. Factory quota has its own
//! whole-turn checkpoint inside `TurnExecutor::execute`, so Rust fallback is
//! transactional without imposing an O(history) clone on every covered turn.

use dregg_cell::CellId;

use super::{RateLimitStateSnapshot, TurnExecutor};
use crate::{
    turn::{ConsumedCapWitness, TurnReceipt},
    umem::{UProjection, UmemTurnWitness},
};

/// Opaque pre-image of side tables reachable from the verified producer's
/// covered set. It is intentionally non-`Clone`: one checkpoint authorizes one
/// rollback, preventing stale pre-images from being replayed later.
pub struct ProducerReferenceCheckpoint {
    rate_limits: RateLimitStateSnapshot,
    budget: Option<BudgetCheckpoint>,
    receipt_agent: CellId,
    previous_receipt_hash: Option<[u8; 32]>,
    last_write_set: Vec<CellId>,
    consumed_cap_witnesses: Vec<ConsumedCapWitness>,
    last_umem_witness: Option<Result<UmemTurnWitness, String>>,
    last_umem_yield: Option<UProjection>,
}

struct BudgetCheckpoint {
    spent: u64,
    debit_len: usize,
}

impl TurnExecutor {
    /// Whether this turn can debit factory quota. Used to keep ordinary turns
    /// off the registry-clone path while retaining a whole-turn inverse for
    /// direct and capability-wrapped factory births.
    pub(super) fn turn_mutates_factory_registry(turn: &crate::turn::Turn) -> bool {
        fn effect_mutates_factory(effect: &crate::action::Effect) -> bool {
            match effect {
                crate::action::Effect::CreateCellFromFactory { .. } => true,
                crate::action::Effect::ExerciseViaCapability { inner_effects, .. } => {
                    inner_effects.iter().any(effect_mutates_factory)
                }
                _ => false,
            }
        }
        fn tree_mutates_factory(tree: &crate::forest::CallTree) -> bool {
            tree.action.effects.iter().any(effect_mutates_factory)
                || tree.children.iter().any(tree_mutates_factory)
        }
        turn.call_forest.roots.iter().any(tree_mutates_factory)
    }

    /// Capture the mutable side-state pre-image immediately before a
    /// speculative Rust reference run under the verified producer.
    ///
    /// Only the selected agent's authority-chain entry is copied, and the
    /// Stingray inverse records a length/counter rather than cloning its full
    /// debit history. The producer owns exclusive turn execution while this
    /// checkpoint is live.
    pub fn checkpoint_producer_reference(
        &self,
        receipt_agent: CellId,
    ) -> ProducerReferenceCheckpoint {
        let rate_limits = self.rate_limit_state_snapshot();
        let budget = self.budget_gate.as_ref().map(|gate| {
            let gate = gate.lock().unwrap_or_else(|error| error.into_inner());
            BudgetCheckpoint {
                spent: gate.slice.spent,
                debit_len: gate.slice.debits.len(),
            }
        });
        let previous_receipt_hash = self.get_last_receipt_hash(&receipt_agent);
        let last_write_set = self
            .last_write_set
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .clone();
        let consumed_cap_witnesses = self
            .consumed_cap_witnesses
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .clone();
        let last_umem_witness = self
            .last_umem_witness
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .clone();
        let last_umem_yield = self
            .last_umem_yield
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .clone();

        ProducerReferenceCheckpoint {
            rate_limits,
            budget,
            receipt_agent,
            previous_receipt_hash,
            last_write_set,
            consumed_cap_witnesses,
            last_umem_witness,
            last_umem_yield,
        }
    }

    /// Restore the pre-image after the verified producer rejects a turn the
    /// Rust reference speculatively ran. Consuming the checkpoint makes the
    /// inverse single-use.
    pub fn rollback_producer_reference(&self, checkpoint: ProducerReferenceCheckpoint) {
        self.restore_rate_limit_state(&checkpoint.rate_limits)
            .expect("an in-memory rate-limit checkpoint is valid");
        if let (Some(gate), Some(previous)) = (&self.budget_gate, checkpoint.budget) {
            let mut gate = gate.lock().unwrap_or_else(|error| error.into_inner());
            gate.slice.spent = previous.spent;
            gate.slice.debits.truncate(previous.debit_len);
        }
        self.restore_last_receipt_hash(checkpoint.receipt_agent, checkpoint.previous_receipt_hash);
        *self
            .last_write_set
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.last_write_set;
        *self
            .consumed_cap_witnesses
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.consumed_cap_witnesses;
        *self
            .last_umem_witness
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.last_umem_witness;
        *self
            .last_umem_yield
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.last_umem_yield;
    }

    /// Advance the authority chain to the exact receipt the verified producer
    /// returned.
    pub fn record_authoritative_receipt_head(&self, agent: CellId, receipt_hash: [u8; 32]) {
        self.record_receipt_hash(agent, receipt_hash);
    }

    /// Re-stamp, re-sign, and atomically advance the authority chain to that
    /// exact final receipt. Keeping those operations in one API prevents the
    /// pre-restamp Rust hash from surviving as the next turn's expected head.
    pub fn restamp_authoritative_committed_receipt(
        &self,
        receipt: TurnReceipt,
        authoritative_post_root: [u8; 32],
    ) -> TurnReceipt {
        let receipt = self.restamp_committed_receipt(receipt, authoritative_post_root);
        self.record_authoritative_receipt_head(receipt.agent, receipt.receipt_hash());
        receipt
    }
}
