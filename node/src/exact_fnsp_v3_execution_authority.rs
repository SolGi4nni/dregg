//! Opaque authority for the executor-produced half of an exact FNSP-v3 finalization.
//!
//! The exact-v3 proof/finalizer used to accept four adjacent caller values: a durable actor-shaped
//! [`Cell`], a [`V9RotationContext`], a [`TurnReceipt`], and a [`CommitRecord`].  Equality checks on
//! those values are necessary, but they do not establish provenance: a caller can assemble a
//! mutually consistent synthetic tuple which was never produced by the node executor.
//!
//! This module removes that raw construction surface.  [`execute_and_authenticate_finalized_turn`]
//! is the only non-test constructor.  It:
//!
//! 1. loads the actor from durable storage and requires the executor pre-ledger to contain that
//!    exact `Cell` (not merely the same `CellId`);
//! 2. captures both complete V9 contexts from the executor-owned accumulator roots and the actual
//!    pre/post ledgers;
//! 3. invokes the node's one producer gate itself;
//! 4. verifies the returned receipt's turn/forest/actor, both state commitments, and the node
//!    cipherclerk's executor signature; and
//! 5. derives the complete commit record from the full pre/post `Cell` diff.
//!
//! Any failed post-execution check restores the caller's ledger snapshot and drops the consumed
//! per-turn executor, including its mutated side tables.  The type is non-`Clone`, its fields are
//! private, and no function accepts a caller-authored receipt or commit record.
//!
//! ## Why this is not the live exact-v3 cutover
//!
//! The current exact-v3 descriptor/anchor is an accumulator *subtransition*: it freezes the stable
//! actor frame and changes only the eight FNS3 nullifier lanes.  A real whole turn advances the
//! author nonce (and can apply fees/other effects), so its canonical `TurnReceipt::post_state_hash`
//! cannot in general equal that subtransition's AFTER commitment.  A receipt-root epoch bump alone
//! cannot erase this semantic difference.  Promotion therefore still requires either a typed exact
//! subreceipt bound into this real receipt, or a widened exact descriptor proving the complete
//! actor/turn transition.  This module deliberately supplies the executor authority both choices
//! need without registering either choice live.

use core::fmt;
use std::error::Error;

use dregg_cell::commitment::V9RotationContext;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_persist::{CommitRecord, PersistentStore, StoreError};
use dregg_sdk::{AgentCipherclerk, SignedTurn};
use dregg_turn::{TurnExecutor, TurnReceipt, TurnResult};

use crate::signed_turn_validation::ValidatedSignedTurn;

/// Consensus-owned coordinates which do not come from turn execution.
///
/// The execution-derived record fields (`turn_hash`, `creator`, `receipt_hash`, `ledger_root`,
/// touched cells, and removals) are intentionally absent.  They are always derived inside this
/// module, so a caller cannot mix them across executor runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FinalizedRecordCoordinates {
    ordinal: u64,
    height: u64,
    block_id: [u8; 32],
    block_executed_up_to: u64,
}

impl FinalizedRecordCoordinates {
    pub(crate) const fn new(
        ordinal: u64,
        height: u64,
        block_id: [u8; 32],
        block_executed_up_to: u64,
    ) -> Self {
        Self {
            ordinal,
            height,
            block_id,
            block_executed_up_to,
        }
    }
}

/// Opaque evidence for one real executor-produced transition and its derived durable record.
///
/// This is intentionally non-`Clone`.  Read-only accessors let the future exact-v3 join validate
/// its subframe; consuming accessors prevent the receipt/record from being detached and recombined
/// with a second authority.
pub(crate) struct ExecutorProducedFinalizedTurn {
    durable_actor_pre: Cell,
    context_before: V9RotationContext,
    context_after: V9RotationContext,
    receipt: TurnReceipt,
    record: CommitRecord,
}

impl ExecutorProducedFinalizedTurn {
    pub(crate) fn durable_actor_pre(&self) -> &Cell {
        &self.durable_actor_pre
    }

    pub(crate) const fn context_before(&self) -> V9RotationContext {
        self.context_before
    }

    pub(crate) const fn context_after(&self) -> V9RotationContext {
        self.context_after
    }

    pub(crate) fn receipt(&self) -> &TurnReceipt {
        &self.receipt
    }

    pub(crate) fn record(&self) -> &CommitRecord {
        &self.record
    }

    pub(crate) fn into_receipt_and_record(self) -> (TurnReceipt, CommitRecord) {
        (self.receipt, self.record)
    }
}

/// Strict failures while turning a real executor call into opaque finalization authority.
#[derive(Debug)]
pub(crate) enum ExecutorProducedFinalizationError {
    ValidatedTurnHashMismatch,
    DurableActorMissing,
    DurableActorMismatch,
    ProducerDidNotCommit(String),
    ProducerRejectedAfterMutation,
    ReceiptTurnMismatch,
    ReceiptForestMismatch,
    ReceiptActorMismatch,
    ReceiptBeforeContextMismatch,
    ReceiptAfterContextMismatch,
    ExecutorSignatureInvalid,
    Store(StoreError),
}

impl fmt::Display for ExecutorProducedFinalizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValidatedTurnHashMismatch => {
                f.write_str("executor authority turn differs from the validated SignedTurn")
            }
            Self::DurableActorMissing => {
                f.write_str("executor authority actor is absent from durable storage")
            }
            Self::DurableActorMismatch => f.write_str(
                "executor authority pre-state actor differs from the durable actor snapshot",
            ),
            Self::ProducerDidNotCommit(reason) => {
                write!(f, "executor did not commit the finalized turn: {reason}")
            }
            Self::ProducerRejectedAfterMutation => f.write_str(
                "executor returned a non-commit result after mutating its ledger; snapshot restored",
            ),
            Self::ReceiptTurnMismatch => {
                f.write_str("executor receipt does not name the validated turn")
            }
            Self::ReceiptForestMismatch => {
                f.write_str("executor receipt does not name the authenticated call forest")
            }
            Self::ReceiptActorMismatch => {
                f.write_str("executor receipt does not name the durable actor")
            }
            Self::ReceiptBeforeContextMismatch => f.write_str(
                "executor receipt BEFORE commitment was not derived from its captured pre-context",
            ),
            Self::ReceiptAfterContextMismatch => f.write_str(
                "executor receipt AFTER commitment was not derived from its captured post-context",
            ),
            Self::ExecutorSignatureInvalid => f.write_str(
                "executor receipt is not signed by the independently held node cipherclerk",
            ),
            Self::Store(error) => write!(f, "durable actor lookup failed: {error}"),
        }
    }
}

impl Error for ExecutorProducedFinalizationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Store(error) => Some(error),
            _ => None,
        }
    }
}

/// Execute through the node's one producer gate and seal the exact values it produced.
///
/// `executor` is consumed.  This matters on refusal: a committed Rust/Lean execution mutates
/// executor-owned note/revocation side tables in addition to `ledger`.  If receipt or durable
/// provenance validation later fails, restoring only the ledger would leave those side tables
/// advanced.  Consuming and dropping the executor makes rollback complete for this additive,
/// currently non-live route.
#[allow(clippy::too_many_arguments)]
pub(crate) fn execute_and_authenticate_finalized_turn(
    store: &PersistentStore,
    node_cipherclerk: &AgentCipherclerk,
    executor: TurnExecutor,
    signed: &SignedTurn,
    validated: ValidatedSignedTurn,
    ledger: &mut Ledger,
    lean_producer_enabled: bool,
    coordinates: FinalizedRecordCoordinates,
) -> Result<ExecutorProducedFinalizedTurn, ExecutorProducedFinalizationError> {
    let turn_hash = signed.turn.hash();
    if turn_hash != validated.turn_hash() {
        return Err(ExecutorProducedFinalizationError::ValidatedTurnHashMismatch);
    }

    let durable_actor = store
        .lookup_cell(&signed.turn.agent)
        .map_err(ExecutorProducedFinalizationError::Store)?
        .ok_or(ExecutorProducedFinalizationError::DurableActorMissing)?;
    if ledger.get(&signed.turn.agent) != Some(&durable_actor) {
        return Err(ExecutorProducedFinalizationError::DurableActorMismatch);
    }

    let pre = ledger.clone();
    let roots_before = executor_roots(&executor);
    let result = super::executor_setup::execute_via_producer(
        &executor,
        &signed.turn,
        ledger,
        lean_producer_enabled,
    );
    let roots_after = executor_roots(&executor);

    let receipt = match result {
        TurnResult::Committed { receipt, .. } => receipt,
        other => {
            if *ledger != pre {
                *ledger = pre;
                return Err(ExecutorProducedFinalizationError::ProducerRejectedAfterMutation);
            }
            return Err(ExecutorProducedFinalizationError::ProducerDidNotCommit(
                format!("{other:?}"),
            ));
        }
    };

    match seal_execution(
        store,
        node_cipherclerk,
        signed,
        validated,
        &pre,
        ledger,
        roots_before,
        roots_after,
        receipt,
        coordinates,
    ) {
        Ok(authority) => Ok(authority),
        Err(error) => {
            *ledger = pre;
            Err(error)
        }
    }
}

type ExecutorRoots = (
    dregg_circuit::Faithful8,
    dregg_circuit::Faithful8,
    dregg_circuit::Faithful8,
);

fn executor_roots(executor: &TurnExecutor) -> ExecutorRoots {
    (
        executor.note_nullifiers.lock().unwrap().root8(),
        executor.note_commitments.lock().unwrap().root8(),
        executor.note_revoked.lock().unwrap().root8(),
    )
}

#[allow(clippy::too_many_arguments)]
fn seal_execution(
    store: &PersistentStore,
    node_cipherclerk: &AgentCipherclerk,
    signed: &SignedTurn,
    validated: ValidatedSignedTurn,
    pre: &Ledger,
    post: &Ledger,
    roots_before: ExecutorRoots,
    roots_after: ExecutorRoots,
    receipt: TurnReceipt,
    coordinates: FinalizedRecordCoordinates,
) -> Result<ExecutorProducedFinalizedTurn, ExecutorProducedFinalizationError> {
    let turn_hash = signed.turn.hash();
    if turn_hash != validated.turn_hash() {
        return Err(ExecutorProducedFinalizationError::ValidatedTurnHashMismatch);
    }
    let durable_actor = store
        .lookup_cell(&signed.turn.agent)
        .map_err(ExecutorProducedFinalizationError::Store)?
        .ok_or(ExecutorProducedFinalizationError::DurableActorMissing)?;
    if pre.get(&signed.turn.agent) != Some(&durable_actor) {
        return Err(ExecutorProducedFinalizationError::DurableActorMismatch);
    }
    if receipt.turn_hash != turn_hash {
        return Err(ExecutorProducedFinalizationError::ReceiptTurnMismatch);
    }
    if receipt.forest_hash != signed.turn.call_forest.compute_hash() {
        return Err(ExecutorProducedFinalizationError::ReceiptForestMismatch);
    }
    if receipt.agent != signed.turn.agent {
        return Err(ExecutorProducedFinalizationError::ReceiptActorMismatch);
    }

    let (nullifiers_before, commitments_before, revoked_before) = roots_before;
    let context_before = dregg_turn::state_commit::consensus_ctx(
        pre,
        nullifiers_before,
        commitments_before,
        revoked_before,
    );
    let expected_before = dregg_turn::state_commit::consensus_state_commitment(
        pre,
        &signed.turn.agent,
        &context_before,
    );
    if receipt.pre_state_hash != expected_before {
        return Err(ExecutorProducedFinalizationError::ReceiptBeforeContextMismatch);
    }

    let (nullifiers_after, commitments_after, revoked_after) = roots_after;
    let context_after = dregg_turn::state_commit::consensus_ctx(
        post,
        nullifiers_after,
        commitments_after,
        revoked_after,
    );
    let expected_after = dregg_turn::state_commit::consensus_state_commitment(
        post,
        &signed.turn.agent,
        &context_after,
    );
    if receipt.post_state_hash != expected_after {
        return Err(ExecutorProducedFinalizationError::ReceiptAfterContextMismatch);
    }

    dregg_turn::verify_receipt_signature_with_keys(&receipt, &[node_cipherclerk.public_key().0])
        .map_err(|_| ExecutorProducedFinalizationError::ExecutorSignatureInvalid)?;

    let (touched_cells, removed) = complete_post_image(pre, post);
    let record = CommitRecord {
        ordinal: coordinates.ordinal,
        height: coordinates.height,
        block_id: coordinates.block_id,
        block_executed_up_to: coordinates.block_executed_up_to,
        turn_hash,
        creator: signed.turn.agent.0,
        receipt_hash: receipt.receipt_hash(),
        ledger_root: dregg_persist::canonical_ledger_root(post),
        touched_cells,
        removed,
    };

    Ok(ExecutorProducedFinalizedTurn {
        durable_actor_pre: durable_actor,
        context_before,
        context_after,
        receipt,
        record,
    })
}

/// Derive the authoritative durable overlay from the complete `Cell` diff, never the lossy
/// `LedgerDelta` projection.
fn complete_post_image(pre: &Ledger, post: &Ledger) -> (Vec<Cell>, Vec<[u8; 32]>) {
    let mut touched_cells = Vec::new();
    let mut removed = Vec::new();
    for (id, cell) in post.iter() {
        if pre.get(id) != Some(cell) {
            touched_cells.push(cell.clone());
        }
    }
    for (id, _) in pre.iter() {
        if post.get(id).is_none() {
            removed.push(id.0);
        }
    }
    (touched_cells, removed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::commitment_set::CommitmentSet;
    use dregg_cell::nullifier_set::NullifierSet;
    use dregg_cell::revoked_set::RevokedSet;
    use dregg_persist::CommitRecord;
    use dregg_turn::{CallForest, Turn};
    use dregg_types::{PublicKey, Signature, sign};

    fn signed_turn(cclerk: &AgentCipherclerk, actor: CellId) -> SignedTurn {
        let turn = Turn {
            agent: actor,
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: vec![],
            cross_effect_dependencies: vec![],
            effect_witness_index_map: vec![],
        };
        SignedTurn {
            signature: Signature([0; 64]),
            signer: cclerk.public_key(),
            pq_signature: vec![],
            pq_signer: vec![],
            turn,
        }
    }

    fn durable_store(actor: &Cell) -> PersistentStore {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .commit_finalized_turn(
                0,
                &CommitRecord {
                    ordinal: 0,
                    height: 0,
                    block_id: [0x01; 32],
                    block_executed_up_to: 0,
                    turn_hash: [0x02; 32],
                    creator: actor.id().0,
                    receipt_hash: [0x03; 32],
                    ledger_root: [0x04; 32],
                    touched_cells: vec![actor.clone()],
                    removed: vec![],
                },
            )
            .expect("durable actor");
        store
    }

    fn roots() -> ExecutorRoots {
        (
            NullifierSet::new().root8(),
            CommitmentSet::new().root8(),
            RevokedSet::new().root8(),
        )
    }

    fn signed_receipt(
        cclerk: &AgentCipherclerk,
        signed: &SignedTurn,
        pre: &Ledger,
        post: &Ledger,
        roots_before: ExecutorRoots,
        roots_after: ExecutorRoots,
    ) -> TurnReceipt {
        let before = dregg_turn::state_commit::consensus_ctx(
            pre,
            roots_before.0,
            roots_before.1,
            roots_before.2,
        );
        let after = dregg_turn::state_commit::consensus_ctx(
            post,
            roots_after.0,
            roots_after.1,
            roots_after.2,
        );
        let mut receipt = TurnReceipt {
            turn_hash: signed.turn.hash(),
            forest_hash: signed.turn.call_forest.compute_hash(),
            pre_state_hash: dregg_turn::state_commit::consensus_state_commitment(
                pre,
                &signed.turn.agent,
                &before,
            ),
            post_state_hash: dregg_turn::state_commit::consensus_state_commitment(
                post,
                &signed.turn.agent,
                &after,
            ),
            agent: signed.turn.agent,
            ..TurnReceipt::default()
        };
        let signature = sign(
            &cclerk.gossip_signing_key(),
            &receipt.canonical_executor_signed_message(),
        );
        receipt.executor_signature = Some(signature.0.to_vec());
        receipt
    }

    fn fixture() -> (
        PersistentStore,
        AgentCipherclerk,
        SignedTurn,
        ValidatedSignedTurn,
        Ledger,
        Ledger,
    ) {
        let cclerk = AgentCipherclerk::from_seed([7; 64]);
        let token_id = *blake3::hash(b"default").as_bytes();
        let mut actor = Cell::with_balance(cclerk.public_key().0, token_id, 100);
        actor.state.set_nonce(0);
        let mut pre = Ledger::new();
        pre.insert_cell(actor.clone()).expect("pre actor");
        let mut post = pre.clone();
        post.get_mut(&actor.id())
            .expect("post actor")
            .state
            .set_nonce(1);
        let signed = signed_turn(&cclerk, actor.id());
        let validated = ValidatedSignedTurn::from_turn_hash_for_test(signed.turn.hash());
        (durable_store(&actor), cclerk, signed, validated, pre, post)
    }

    fn coordinates() -> FinalizedRecordCoordinates {
        FinalizedRecordCoordinates::new(9, 10, [0x44; 32], 11)
    }

    #[test]
    fn opaque_authority_derives_receipt_and_commit_record_from_one_execution_image() {
        let (store, cclerk, signed, validated, pre, mut post) = fixture();
        let roots_before = roots();
        let roots_after = roots();
        let receipt = signed_receipt(&cclerk, &signed, &pre, &post, roots_before, roots_after);
        // A second changed cell proves the record comes from the complete ledger diff, not just
        // the actor or a caller-authored `LedgerDelta`.
        let extra = Cell::with_balance([0x22; 32], [0x23; 32], 5);
        post.insert_cell(extra.clone()).expect("extra post cell");
        let receipt = signed_receipt(&cclerk, &signed, &pre, &post, roots_before, roots_after);
        let authority = seal_execution(
            &store,
            &cclerk,
            &signed,
            validated,
            &pre,
            &post,
            roots_before,
            roots_after,
            receipt,
            coordinates(),
        )
        .expect("sealed executor authority");

        assert_eq!(
            authority.durable_actor_pre(),
            pre.get(&signed.turn.agent).unwrap()
        );
        assert_eq!(authority.receipt().turn_hash, signed.turn.hash());
        assert_eq!(authority.record().turn_hash, signed.turn.hash());
        assert_eq!(authority.record().creator, signed.turn.agent.0);
        assert_eq!(
            authority.record().receipt_hash,
            authority.receipt().receipt_hash()
        );
        assert_eq!(
            authority.record().ledger_root,
            dregg_persist::canonical_ledger_root(&post)
        );
        assert!(
            authority
                .record()
                .touched_cells
                .iter()
                .any(|cell| cell == &extra)
        );
    }

    #[test]
    fn mixed_context_and_receipt_are_refused_even_when_receipt_is_genuinely_signed() {
        let (store, cclerk, signed, validated, pre, post) = fixture();
        let roots_before = roots();
        let roots_after = roots();
        let receipt = signed_receipt(&cclerk, &signed, &pre, &post, roots_before, roots_after);
        let mut mixed_nullifiers = NullifierSet::new();
        mixed_nullifiers
            .insert(dregg_cell::Nullifier([0x31; 32]), 31)
            .expect("different root");
        let mixed_roots = (mixed_nullifiers.root8(), roots_before.1, roots_before.2);

        assert!(matches!(
            seal_execution(
                &store,
                &cclerk,
                &signed,
                validated,
                &pre,
                &post,
                mixed_roots,
                roots_after,
                receipt,
                coordinates(),
            ),
            Err(ExecutorProducedFinalizationError::ReceiptBeforeContextMismatch)
        ));
    }

    #[test]
    fn same_id_mutated_durable_actor_and_mixed_post_image_are_refused() {
        let (store, cclerk, signed, validated, mut pre, post) = fixture();
        let roots_before = roots();
        let roots_after = roots();
        let receipt = signed_receipt(&cclerk, &signed, &pre, &post, roots_before, roots_after);

        // Cell identity excludes mutable state.  A same-id nonce substitution must still fail the
        // durable snapshot check before its internally consistent context can be authority.
        pre.get_mut(&signed.turn.agent)
            .expect("actor")
            .state
            .set_nonce(99);
        assert!(matches!(
            seal_execution(
                &store,
                &cclerk,
                &signed,
                validated,
                &pre,
                &post,
                roots_before,
                roots_after,
                receipt,
                coordinates(),
            ),
            Err(ExecutorProducedFinalizationError::DurableActorMismatch)
        ));

        let (_, _, _, _, pre, mut mixed_post) = fixture();
        mixed_post
            .get_mut(&signed.turn.agent)
            .expect("post actor")
            .state
            .set_nonce(2);
        let receipt = signed_receipt(&cclerk, &signed, &pre, &post, roots_before, roots_after);
        assert!(matches!(
            seal_execution(
                &store,
                &cclerk,
                &signed,
                validated,
                &pre,
                &mixed_post,
                roots_before,
                roots_after,
                receipt,
                coordinates(),
            ),
            Err(ExecutorProducedFinalizationError::ReceiptAfterContextMismatch)
        ));
    }

    #[test]
    fn receipt_from_another_executor_key_is_not_authority() {
        let (store, cclerk, signed, validated, pre, post) = fixture();
        let attacker = AgentCipherclerk::from_seed([0x99; 64]);
        let roots_before = roots();
        let roots_after = roots();
        let receipt = signed_receipt(&attacker, &signed, &pre, &post, roots_before, roots_after);
        assert!(matches!(
            seal_execution(
                &store,
                &cclerk,
                &signed,
                validated,
                &pre,
                &post,
                roots_before,
                roots_after,
                receipt,
                coordinates(),
            ),
            Err(ExecutorProducedFinalizationError::ExecutorSignatureInvalid)
        ));
    }
}
