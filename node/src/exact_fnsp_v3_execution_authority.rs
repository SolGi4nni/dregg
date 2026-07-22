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
//! Execution occurs against an owned ledger candidate.  Neither that candidate nor the consumed
//! executor (including all of its mutated side tables) is released before the later durable CAS.
//! The caller's live ledger therefore remains untouched on every preparation/join failure.  The
//! type is non-`Clone`, its fields are private, and no function accepts a caller-authored receipt
//! or commit record.
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
use dregg_cell::{Cell, Ledger};
use dregg_persist::{
    CommitRecord, PreparedExactFnspV3StateTransitionV1, UntrustedExactFnspV3ActivationV1,
};
use dregg_sdk::SignedTurn;
use dregg_turn::executor::ExactFnspV3AdmissionError;
use dregg_turn::faithful_note_spend_exact_v3::FaithfulNoteSpendExactV3ProofCarrier;
use dregg_turn::{
    AcceptedFaithfulNoteSpendExactV3, Effect, ExactFnspV3ReceiptEpoch,
    ExactFnspV3ReceiptEpochError, ExactFnspV3ReceiptEpochV1, ExactFnspV3StatePoint,
    PreparedExactFnspV3ReceiptFrameV1, TurnExecutor, TurnReceipt, TurnResult,
    UntrustedExactFnspV3CommittedFrameHeadBindingV1, UntrustedExactFnspV3ReceiptFrameJoinV1,
};
use dregg_types::{Signature, verify};

use crate::exact_fnsp_v3_activation::{
    ExactFnspV3ExecutorSignerAuthority, PreparedExactFnspV3Predecessor,
};
use crate::exact_fnsp_v3_actor_authority::{
    DurableExactFnspV3ActorAuthority, DurableExactFnspV3ActorAuthorityError,
    DurableExactFnspV3ActorCoordinates,
};
use crate::signed_turn_validation::ValidatedSignedTurn;
use crate::state::NodeStateInner;

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
    core: ExecutorProducedFinalizedTurnCore,
    accepted: AcceptedFaithfulNoteSpendExactV3,
}

struct ExecutorProducedFinalizedTurnCore {
    durable_actor_pre: Cell,
    actor_coordinates: DurableExactFnspV3ActorCoordinates,
    post_ledger: Ledger,
    post_executor: TurnExecutor,
    context_before: V9RotationContext,
    context_after: V9RotationContext,
    proof_context_before: V9RotationContext,
    receipt: TurnReceipt,
    record: CommitRecord,
    executor_public_key: [u8; 32],
    executor_consensus_predecessors:
        crate::executor_side_state_persistence::ExecutorConsensusPredecessors,
    authenticated_exact_spend: AuthenticatedExactFnspV3Spend,
}

/// Values which have passed every receipt/ledger/store consistency check, but are deliberately
/// not yet executor authority.  Only the one live producer wrapper below can combine this seal
/// with the consumed post-execution [`TurnExecutor`].  In particular, private falsifier tests can
/// exercise the consistency checks without gaining a synthetic authority constructor.
struct ValidatedExecutionSeal {
    durable_actor_pre: Cell,
    actor_coordinates: DurableExactFnspV3ActorCoordinates,
    post_ledger: Ledger,
    context_before: V9RotationContext,
    context_after: V9RotationContext,
    receipt: TurnReceipt,
    record: CommitRecord,
    executor_public_key: [u8; 32],
    authenticated_exact_spend: AuthenticatedExactFnspV3Spend,
}

impl ExecutorProducedFinalizedTurn {
    #[cfg(test)]
    pub(crate) fn durable_actor_pre(&self) -> &Cell {
        &self.core.durable_actor_pre
    }

    #[cfg(test)]
    pub(crate) fn receipt(&self) -> &TurnReceipt {
        &self.core.receipt
    }

    #[cfg(test)]
    pub(crate) fn record(&self) -> &CommitRecord {
        &self.core.record
    }

    /// Proof-accepted public coordinates used to authenticate the historical note-root row before
    /// the lazy epoch is installed.  The linear acceptance token remains owned by this authority.
    pub(crate) fn accepted_binding(
        &self,
    ) -> dregg_turn::FaithfulNoteSpendExactV3AcceptanceBinding<'_> {
        self.accepted.binding()
    }

    /// Revalidate the actor/ledger/durable coordinate key after off-lock proof and execution,
    /// before any activation or frame authority is selected.
    pub(crate) fn revalidate_actor_locked(
        &self,
        locked: &NodeStateInner,
    ) -> Result<(), DurableExactFnspV3ActorAuthorityError> {
        self.core.actor_coordinates.revalidate_locked(locked)
    }

    /// Consume executor authority together with the proof-bound exact subreceipt.
    ///
    /// The frame is still explicitly untrusted until every full-turn coordinate is welded to the
    /// receipt minted above, its retained acceptance is welded to the exactly-one admitted signed
    /// `NoteSpend`, and the same executor key signs the frame domain.
    pub(crate) fn bind_exact_frame(
        self,
        signer: &ExactFnspV3ExecutorSignerAuthority,
        predecessor: PreparedExactFnspV3Predecessor,
    ) -> Result<ExecutorProducedExactFnspV3FinalizedTurn, ExecutorProducedFinalizationError> {
        let activation = predecessor.activation();
        if activation.executor_public_key() != self.core.executor_public_key
            || signer.public_key().0 != self.core.executor_public_key
            || predecessor.actor() != self.core.receipt.agent
            || predecessor.player_predecessor_receipt_hash()
                != self.core.receipt.previous_receipt_hash
        {
            return Err(ExecutorProducedFinalizationError::ExecutorKeyChangedAtFrameJoin);
        }
        let Self { core, accepted } = self;
        let frame = if let Some(head) = predecessor.committed_head() {
            let epoch = ExactFnspV3ReceiptEpoch::new(head.epoch())
                .map_err(ExecutorProducedFinalizationError::ReceiptEpoch)?;
            let exact_after =
                ExactFnspV3StatePoint::new(head.exact_after().root(), head.exact_after().count())
                    .map_err(ExecutorProducedFinalizationError::ReceiptEpoch)?;
            let binding =
                UntrustedExactFnspV3CommittedFrameHeadBindingV1::from_untrusted_coordinates(
                    epoch,
                    head.activation_hash(),
                    head.frame_hash(),
                    head.receipt_log_index(),
                    exact_after,
                    head.federation_id(),
                );
            PreparedExactFnspV3ReceiptFrameV1::extend_from_head_binding(
                binding,
                predecessor.receipt_log_index(),
                predecessor.player_predecessor_receipt_index(),
                core.receipt.clone(),
                accepted,
            )
        } else {
            PreparedExactFnspV3ReceiptFrameV1::begin(
                activation.epoch(),
                predecessor.receipt_log_index(),
                predecessor.player_predecessor_receipt_index(),
                core.receipt.clone(),
                accepted,
            )
        }
        .map_err(ExecutorProducedFinalizationError::ReceiptEpoch)?;
        let authorized_epoch = activation.epoch().clone();
        let first_frame_activation = predecessor.into_first_frame_activation();
        core.bind_prepared_frame(signer, &authorized_epoch, frame, first_frame_activation)
    }
}

impl ExecutorProducedFinalizedTurnCore {
    fn bind_prepared_frame(
        self,
        signer: &ExactFnspV3ExecutorSignerAuthority,
        authorized_epoch: &ExactFnspV3ReceiptEpochV1,
        frame: PreparedExactFnspV3ReceiptFrameV1,
        first_frame_activation: Option<UntrustedExactFnspV3ActivationV1>,
    ) -> Result<ExecutorProducedExactFnspV3FinalizedTurn, ExecutorProducedFinalizationError> {
        if signer.public_key().0 != self.executor_public_key {
            return Err(ExecutorProducedFinalizationError::ExecutorKeyChangedAtFrameJoin);
        }
        let frame = frame
            .into_join_parts_for_epoch(authorized_epoch)
            .map_err(ExecutorProducedFinalizationError::ReceiptEpoch)?;
        if frame.full_receipt_hash() != self.receipt.receipt_hash()
            || frame.turn_hash() != self.receipt.turn_hash
            || frame.forest_hash() != self.receipt.forest_hash
            || frame.agent() != self.receipt.agent
            || frame.federation_id() != self.receipt.federation_id
            || frame.full_pre_state_hash() != self.receipt.pre_state_hash
            || frame.full_post_state_hash() != self.receipt.post_state_hash
        {
            return Err(ExecutorProducedFinalizationError::ExactFrameReceiptMismatch);
        }
        self.authenticated_exact_spend.matches_frame(&frame)?;

        let frame_signature = signer.sign(&frame.executor_signature_message_v1());
        if !verify(
            &signer.public_key(),
            &frame.executor_signature_message_v1(),
            &frame_signature,
        ) {
            return Err(ExecutorProducedFinalizationError::ExactFrameSignatureInvalid);
        }

        Ok(ExecutorProducedExactFnspV3FinalizedTurn {
            durable_actor_pre: self.durable_actor_pre,
            actor_coordinates: self.actor_coordinates,
            post_ledger: self.post_ledger,
            post_executor: self.post_executor,
            context_before: self.context_before,
            context_after: self.context_after,
            proof_context_before: self.proof_context_before,
            receipt: self.receipt,
            record: self.record,
            executor_public_key: self.executor_public_key,
            executor_consensus_predecessors: self.executor_consensus_predecessors,
            frame_signature,
            frame,
            first_frame_activation,
        })
    }
}

/// Signed-turn coordinates for the one exact spend executed by this receipt.
///
/// Retaining the original typed effect avoids a second, subtly divergent encoding of the full
/// proof carrier.  The strict decoded root height is retained separately because it is a semantic
/// coordinate of the accepted statement.
struct AuthenticatedExactFnspV3Spend {
    effect: Effect,
    root_height: u64,
}

/// Public coordinates needed to prepare the store-owned exact append before proof work.
///
/// This is not an admission token.  It is available only after the complete minimal exact-turn
/// shape and canonical carrier decode have passed; proof acceptance remains the opaque linear
/// authority returned by [`verify_exact_fnsp_v3_turn_acceptance`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ExactFnspV3RouteCoordinates {
    nullifier: [u8; 32],
    value: u64,
}

impl ExactFnspV3RouteCoordinates {
    pub(crate) const fn nullifier(self) -> [u8; 32] {
        self.nullifier
    }

    pub(crate) const fn value(self) -> u64 {
        self.value
    }
}

impl AuthenticatedExactFnspV3Spend {
    fn from_signed_turn(signed: &SignedTurn) -> Result<Self, ExecutorProducedFinalizationError> {
        let spends = exact_note_spends(&signed.turn.call_forest);
        if spends.len() != 1 {
            return Err(
                ExecutorProducedFinalizationError::ExactNoteSpendCardinality {
                    found: spends.len(),
                },
            );
        }
        // Minimal durably reconstructible slice.  A recursive spend is discovered above so it is
        // rejected explicitly rather than missed, but capability wrappers, siblings, children,
        // and extra actions can mutate executor-only state which the atomic store does not yet
        // persist/reseed. Widen this only alongside an executable persistence characterization.
        let [root] = signed.turn.call_forest.roots.as_slice() else {
            return Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported);
        };
        if root.action.target != signed.turn.agent
            || !matches!(
                root.action.authorization,
                dregg_turn::Authorization::Unchecked
            )
            || root.action.preconditions != Default::default()
            || root.action.may_delegate != dregg_turn::DelegationMode::None
            || root.action.commitment_mode != dregg_turn::CommitmentMode::Full
            || root.action.balance_change.is_some()
            || !root.action.witness_blobs.is_empty()
            || !signed.turn.sovereign_witnesses.is_empty()
            || signed.turn.execution_proof.is_some()
            || signed.turn.execution_proof_cell.is_some()
            || signed.turn.execution_proof_new_commitment.is_some()
            || signed.turn.custom_program_proofs.is_some()
            || !signed.turn.effect_binding_proofs.is_empty()
            || !signed.turn.cross_effect_dependencies.is_empty()
            || !signed.turn.effect_witness_index_map.is_empty()
            || signed.turn.conservation_proof.is_some()
        {
            return Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported);
        }
        let [effect] = root.action.effects.as_slice() else {
            return Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported);
        };
        if !root.children.is_empty() || !matches!(effect, Effect::NoteSpend { .. }) {
            return Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported);
        }
        let effect = effect.clone();
        let Effect::NoteSpend {
            spending_proof,
            value,
            value_commitment,
            ..
        } = &effect
        else {
            unreachable!("exact_note_spends returns only NoteSpend effects")
        };
        // Until direct NoteCreate is admitted into the same exact frame, a single spent note can
        // satisfy the executor's note-conservation gate only at value zero.  Enforce that before
        // phase-1 charging so the characterized route is total after proof acceptance.
        if *value != 0 || value_commitment.is_some() {
            return Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported);
        }
        let carrier =
            FaithfulNoteSpendExactV3ProofCarrier::decode(spending_proof).map_err(|error| {
                ExecutorProducedFinalizationError::ExactProofCarrierInvalid(error.to_string())
            })?;
        Ok(Self {
            effect,
            root_height: carrier.root_height(),
        })
    }

    fn route_coordinates(&self) -> ExactFnspV3RouteCoordinates {
        let Effect::NoteSpend {
            nullifier, value, ..
        } = &self.effect
        else {
            unreachable!("authenticated exact spend is a NoteSpend")
        };
        ExactFnspV3RouteCoordinates {
            nullifier: nullifier.0,
            value: *value,
        }
    }

    fn matches_frame(
        &self,
        frame: &UntrustedExactFnspV3ReceiptFrameJoinV1,
    ) -> Result<(), ExecutorProducedFinalizationError> {
        if !frame.matches_signed_effect(&self.effect) {
            return Err(ExecutorProducedFinalizationError::ExactFrameCarrierMismatch);
        }
        let binding = frame.accepted_binding();
        let Effect::NoteSpend {
            nullifier,
            note_tree_root,
            value,
            asset_type,
            value_commitment,
            ..
        } = &self.effect
        else {
            unreachable!("authenticated exact spend is a NoteSpend")
        };
        if binding.historical_root_height() != self.root_height
            || binding.historical_note_root() != *note_tree_root
            || binding.nullifier() != nullifier.0
            || binding.value() != *value
            || binding.asset_type() != *asset_type
            || binding.value_commitment() != *value_commitment
        {
            return Err(ExecutorProducedFinalizationError::ExactFrameStatementMismatch);
        }
        Ok(())
    }
}

/// Classify a signed turn before the legacy FNSP-v2 decoder sees it.
///
/// Ordinary turns and other FNSP versions return `Ok(None)`.  The presence of any recursive
/// `FNSP || version=3` carrier irrevocably selects this route; the subsequent strict projection
/// then rejects malformed, mixed, wrapped, or multi-effect shapes instead of falling through to
/// legacy execution or its rejection/charging logic.
pub(crate) fn exact_fnsp_v3_route_coordinates(
    signed: &SignedTurn,
) -> Result<Option<ExactFnspV3RouteCoordinates>, ExecutorProducedFinalizationError> {
    use dregg_turn::faithful_note_spend_exact_v3::{
        FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC, FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION,
    };

    let selects_exact_v3 = exact_note_spends(&signed.turn.call_forest)
        .into_iter()
        .any(|effect| {
            let Effect::NoteSpend { spending_proof, .. } = effect else {
                unreachable!("exact_note_spends returns only NoteSpend effects")
            };
            spending_proof.starts_with(&FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC)
                && spending_proof.get(FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC.len())
                    == Some(&FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION)
        });
    if !selects_exact_v3 {
        return Ok(None);
    }
    Ok(Some(
        AuthenticatedExactFnspV3Spend::from_signed_turn(signed)?.route_coordinates(),
    ))
}

/// Verify the real exact-v3 carrier off-lock against one store-snapshot-owned transition.
///
/// The outer anchor is rebuilt from the durable actor and ledger snapshot, while its nullifier
/// coordinate is replaced by the exact accumulator's FNS3 value.  No caller-authored statement,
/// verifier identity, or transition tuple reaches the proof verifier.
pub(crate) fn verify_exact_fnsp_v3_turn_acceptance(
    signed: &SignedTurn,
    prepared: &PreparedExactFnspV3StateTransitionV1,
    actor: &DurableExactFnspV3ActorAuthority,
    executor: &TurnExecutor,
) -> Result<AcceptedFaithfulNoteSpendExactV3, ExecutorProducedFinalizationError> {
    let authenticated = AuthenticatedExactFnspV3Spend::from_signed_turn(signed)?;
    let cas = prepared.cas();
    let (_, commitments, revoked) = executor_roots(executor);
    let mut context = dregg_turn::state_commit::consensus_ctx(
        actor.ledger(),
        dregg_circuit::Faithful8::from_bytes32(&u32_lanes_to_bytes(
            cas.expected().fns3().map(|felt| felt.as_u32()),
        )),
        commitments,
        revoked,
    );
    // Keep this assignment explicit: `consensus_ctx` currently preserves the supplied value, but
    // exact authority must remain correct if that constructor later derives a legacy root itself.
    context.nullifier_root = dregg_circuit::Faithful8::from_bytes32(&u32_lanes_to_bytes(
        cas.expected().fns3().map(|felt| felt.as_u32()),
    ));
    let anchor = dregg_turn::derive_exact_fnsp_v3_durable_anchor(
        actor.actor(),
        &context,
        cas.expected().fns3(),
        cas.successor().fns3(),
    )
    .map_err(|error| ExecutorProducedFinalizationError::ExactProofAcceptance(error.to_string()))?;
    dregg_turn::verify_faithful_note_spend_exact_v3_acceptance(
        &authenticated.effect,
        prepared.validated(),
        &anchor,
    )
    .map_err(|error| ExecutorProducedFinalizationError::ExactProofAcceptance(error.to_string()))
}

/// Final non-`Clone` authority joining real execution, exact proof acceptance, epoch continuity,
/// and an executor signature over the exact frame domain.
pub(crate) struct ExecutorProducedExactFnspV3FinalizedTurn {
    durable_actor_pre: Cell,
    actor_coordinates: DurableExactFnspV3ActorCoordinates,
    post_ledger: Ledger,
    post_executor: TurnExecutor,
    context_before: V9RotationContext,
    context_after: V9RotationContext,
    proof_context_before: V9RotationContext,
    receipt: TurnReceipt,
    record: CommitRecord,
    executor_public_key: [u8; 32],
    executor_consensus_predecessors:
        crate::executor_side_state_persistence::ExecutorConsensusPredecessors,
    frame_signature: Signature,
    frame: UntrustedExactFnspV3ReceiptFrameJoinV1,
    first_frame_activation: Option<UntrustedExactFnspV3ActivationV1>,
}

/// Consuming view used only by the node's exact finalizer.  There is no constructor and the
/// accepted token remains owned by `frame` until the finalizer consumes it into the durable CAS.
pub(crate) struct ExactFnspV3ExecutorFinalizationParts {
    durable_actor_pre: Cell,
    actor_coordinates: DurableExactFnspV3ActorCoordinates,
    post_ledger: Ledger,
    post_executor: TurnExecutor,
    context_before: V9RotationContext,
    context_after: V9RotationContext,
    proof_context_before: V9RotationContext,
    receipt: TurnReceipt,
    record: CommitRecord,
    executor_public_key: [u8; 32],
    executor_consensus_predecessors:
        crate::executor_side_state_persistence::ExecutorConsensusPredecessors,
    frame_signature: Signature,
    frame: UntrustedExactFnspV3ReceiptFrameJoinV1,
    first_frame_activation: Option<UntrustedExactFnspV3ActivationV1>,
}

impl ExecutorProducedExactFnspV3FinalizedTurn {
    pub(crate) fn durable_actor_pre(&self) -> &Cell {
        &self.durable_actor_pre
    }

    pub(crate) fn post_ledger(&self) -> &Ledger {
        &self.post_ledger
    }

    pub(crate) const fn context_before(&self) -> V9RotationContext {
        self.context_before
    }

    pub(crate) const fn context_after(&self) -> V9RotationContext {
        self.context_after
    }

    pub(crate) const fn proof_context_before(&self) -> V9RotationContext {
        self.proof_context_before
    }

    pub(crate) fn receipt(&self) -> &TurnReceipt {
        &self.receipt
    }

    pub(crate) fn record(&self) -> &CommitRecord {
        &self.record
    }

    pub(crate) fn frame(&self) -> &UntrustedExactFnspV3ReceiptFrameJoinV1 {
        &self.frame
    }

    /// The signed flag-day candidate, present only while finalizing the first exact frame.
    /// It remains part of this non-Clone executor authority until the atomic store call consumes
    /// both values together.
    pub(crate) fn first_frame_activation(&self) -> Option<&UntrustedExactFnspV3ActivationV1> {
        self.first_frame_activation.as_ref()
    }

    /// Revalidate the complete durable/RAM actor snapshot after off-lock proof and execution.
    ///
    /// The store's eventual atomic CAS covers its durable rows, but it cannot detect a RAM-only
    /// ledger writer which left the durable commit cursor unchanged.  Exact finalization installs
    /// the retained whole-ledger post-image, so this fence is required immediately before prepare
    /// and commit to avoid replacing such a concurrent writer.
    pub(crate) fn revalidate_actor_locked(
        &self,
        locked: &NodeStateInner,
    ) -> Result<(), DurableExactFnspV3ActorAuthorityError> {
        self.actor_coordinates.revalidate_locked(locked)
    }

    /// Reverify immediately before the durable CAS, not just at join time.
    pub(crate) fn verify_frame_signature(&self) -> bool {
        verify(
            &dregg_types::PublicKey(self.executor_public_key),
            &self.frame.executor_signature_message_v1(),
            &self.frame_signature,
        )
    }

    pub(crate) fn into_finalization_parts(self) -> ExactFnspV3ExecutorFinalizationParts {
        ExactFnspV3ExecutorFinalizationParts {
            durable_actor_pre: self.durable_actor_pre,
            actor_coordinates: self.actor_coordinates,
            post_ledger: self.post_ledger,
            post_executor: self.post_executor,
            context_before: self.context_before,
            context_after: self.context_after,
            proof_context_before: self.proof_context_before,
            receipt: self.receipt,
            record: self.record,
            executor_public_key: self.executor_public_key,
            executor_consensus_predecessors: self.executor_consensus_predecessors,
            frame_signature: self.frame_signature,
            frame: self.frame,
            first_frame_activation: self.first_frame_activation,
        }
    }
}

impl ExactFnspV3ExecutorFinalizationParts {
    pub(crate) fn verify_frame_signature(&self) -> bool {
        verify(
            &dregg_types::PublicKey(self.executor_public_key),
            &self.frame.executor_signature_message_v1(),
            &self.frame_signature,
        )
    }

    pub(crate) fn into_commit_components(
        self,
    ) -> (
        Cell,
        DurableExactFnspV3ActorCoordinates,
        Ledger,
        TurnExecutor,
        V9RotationContext,
        V9RotationContext,
        V9RotationContext,
        TurnReceipt,
        CommitRecord,
        [u8; 32],
        crate::executor_side_state_persistence::ExecutorConsensusPredecessors,
        Signature,
        UntrustedExactFnspV3ReceiptFrameJoinV1,
        Option<UntrustedExactFnspV3ActivationV1>,
    ) {
        (
            self.durable_actor_pre,
            self.actor_coordinates,
            self.post_ledger,
            self.post_executor,
            self.context_before,
            self.context_after,
            self.proof_context_before,
            self.receipt,
            self.record,
            self.executor_public_key,
            self.executor_consensus_predecessors,
            self.frame_signature,
            self.frame,
            self.first_frame_activation,
        )
    }
}

/// Strict failures while turning a real executor call into opaque finalization authority.
#[derive(Debug)]
pub(crate) enum ExecutorProducedFinalizationError {
    ValidatedTurnHashMismatch,
    DurableActorMismatch,
    ActorOrdinalMismatch,
    ProducerDidNotCommit(String),
    ProducerRejectedAfterMutation,
    ReceiptTurnMismatch,
    ReceiptForestMismatch,
    ReceiptActorMismatch,
    ReceiptBeforeContextMismatch,
    ReceiptAfterContextMismatch,
    ExecutorSignatureInvalid,
    ExactNoteSpendCardinality { found: usize },
    ExactProofCarrierInvalid(String),
    ExactProofAcceptance(String),
    ExactTurnShapeUnsupported,
    ExactChargedRoutePreflight(String),
    ExactExecutorHasBudgetGate,
    NonDurableExecutorSideStateMutation,
    ExactAdmission(ExactFnspV3AdmissionError),
    ExactAdmissionMissingAfterCommit,
    ExecutorKeyChangedAtFrameJoin,
    ExactFrameReceiptMismatch,
    ExactFrameCarrierMismatch,
    ExactFrameStatementMismatch,
    ExactFrameSignatureInvalid,
    ReceiptEpoch(ExactFnspV3ReceiptEpochError),
}

impl fmt::Display for ExecutorProducedFinalizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValidatedTurnHashMismatch => {
                f.write_str("executor authority turn differs from the validated SignedTurn")
            }
            Self::DurableActorMismatch => f.write_str(
                "executor authority pre-state actor differs from the durable actor snapshot",
            ),
            Self::ActorOrdinalMismatch => f.write_str(
                "finalized record ordinal differs from the captured durable commit cursor",
            ),
            Self::ProducerDidNotCommit(reason) => {
                write!(f, "executor did not commit the finalized turn: {reason}")
            }
            Self::ProducerRejectedAfterMutation => f.write_str(
                "executor returned a non-commit result after mutating its isolated ledger candidate",
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
            Self::ExactNoteSpendCardinality { found } => write!(
                f,
                "exact executor authority requires exactly one recursively nested NoteSpend, found {found}",
            ),
            Self::ExactProofCarrierInvalid(error) => {
                write!(f, "signed exact FNSP-v3 proof carrier is invalid: {error}")
            }
            Self::ExactProofAcceptance(error) => {
                write!(f, "exact FNSP-v3 proof acceptance failed: {error}")
            }
            Self::ExactTurnShapeUnsupported => f.write_str(
                "exact FNSP-v3 staged slice requires a zero-value/no-value-commitment, self-targeted, unchecked, one-action/one-NoteSpend envelope with no sidecars",
            ),
            Self::ExactChargedRoutePreflight(reason) => write!(
                f,
                "exact FNSP-v3 route is not total after fee/nonce charging: {reason}"
            ),
            Self::ExactExecutorHasBudgetGate => f.write_str(
                "exact FNSP-v3 live slice refuses an executor with a non-durable budget gate",
            ),
            Self::NonDurableExecutorSideStateMutation => f.write_str(
                "exact FNSP-v3 execution changed a non-durable executor side-state map",
            ),
            Self::ExactAdmission(error) => {
                write!(f, "exact FNSP-v3 executor admission refused linear handoff: {error}")
            }
            Self::ExactAdmissionMissingAfterCommit => f.write_str(
                "committed exact FNSP-v3 turn did not yield its verifier-accepted admission token",
            ),
            Self::ExecutorKeyChangedAtFrameJoin => f.write_str(
                "cipherclerk at exact-frame join differs from the executor receipt signer",
            ),
            Self::ExactFrameReceiptMismatch => f.write_str(
                "proof-bound exact frame does not name the executor-produced full-turn receipt",
            ),
            Self::ExactFrameCarrierMismatch => f.write_str(
                "exact frame acceptance does not bind the authenticated signed proof carrier",
            ),
            Self::ExactFrameStatementMismatch => f.write_str(
                "exact frame statement does not bind every authenticated signed NoteSpend coordinate",
            ),
            Self::ExactFrameSignatureInvalid => {
                f.write_str("executor-produced exact frame signature failed self-verification")
            }
            Self::ReceiptEpoch(error) => write!(f, "exact receipt epoch refused frame: {error}"),
        }
    }
}

impl Error for ExecutorProducedFinalizationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::ReceiptEpoch(error) => Some(error),
            Self::ExactAdmission(error) => Some(error),
            _ => None,
        }
    }
}

/// Execute through the node's one producer gate and seal the exact values it produced.
///
/// `executor` is consumed and retained with the isolated post-ledger candidate.  A committed
/// Rust/Lean execution mutates many executor-owned side tables in addition to the ledger, so
/// retaining only three accumulator roots would not be a complete post-image.  The later durable
/// finalizer must consume both candidates and may release an install token only after its CAS.
#[allow(clippy::too_many_arguments)]
pub(crate) fn execute_and_authenticate_finalized_turn(
    executor: TurnExecutor,
    accepted: AcceptedFaithfulNoteSpendExactV3,
    signed: &SignedTurn,
    validated: ValidatedSignedTurn,
    actor_authority: DurableExactFnspV3ActorAuthority,
    signer: &ExactFnspV3ExecutorSignerAuthority,
    lean_producer_enabled: bool,
    coordinates: FinalizedRecordCoordinates,
) -> Result<ExecutorProducedFinalizedTurn, ExecutorProducedFinalizationError> {
    let turn_hash = signed.turn.hash();
    if turn_hash != validated.turn_hash() {
        return Err(ExecutorProducedFinalizationError::ValidatedTurnHashMismatch);
    }

    let (durable_actor, ledger, actor_coordinates) = actor_authority.into_execution_parts();
    if actor_coordinates.actor_id() != signed.turn.agent
        || ledger.get(&signed.turn.agent) != Some(&durable_actor)
    {
        return Err(ExecutorProducedFinalizationError::DurableActorMismatch);
    }
    if coordinates.ordinal != actor_coordinates.commit_cursor() {
        return Err(ExecutorProducedFinalizationError::ActorOrdinalMismatch);
    }
    // Fail before executing: budget slices are executor-local today and cannot be reconstructed
    // from the atomic finalized-turn record.
    if executor.budget_gate.is_some() {
        return Err(ExecutorProducedFinalizationError::ExactExecutorHasBudgetGate);
    }
    // Validate and bind the characterized exact route before installing the linear token or
    // allowing phase-1 fee/nonce charging. A caller cannot preinstall authority for a different
    // genuine proof and make the executor discover that mismatch only after mutation.
    let authenticated_exact_spend = AuthenticatedExactFnspV3Spend::from_signed_turn(signed)?;
    if !durable_actor.program.is_none() {
        return Err(
            ExecutorProducedFinalizationError::ExactChargedRoutePreflight(
                "actor/target cell has a post-effect program gate".into(),
            ),
        );
    }
    if durable_actor.state.nonce() == u64::MAX {
        return Err(
            ExecutorProducedFinalizationError::ExactChargedRoutePreflight(
                "actor nonce is exhausted".into(),
            ),
        );
    }
    executor
        .validate_without_apply(&signed.turn, &ledger)
        .map_err(|error| {
            ExecutorProducedFinalizationError::ExactChargedRoutePreflight(error.to_string())
        })?;
    let Effect::NoteSpend { nullifier, .. } = &authenticated_exact_spend.effect else {
        unreachable!("authenticated exact spend is a NoteSpend")
    };
    if executor.note_nullifiers.lock().unwrap().contains(nullifier) {
        return Err(
            ExecutorProducedFinalizationError::ExactChargedRoutePreflight(
                "legacy nullifier accumulator already contains the exact nullifier".into(),
            ),
        );
    }
    if !accepted.matches_signed_effect(&authenticated_exact_spend.effect) {
        return Err(ExecutorProducedFinalizationError::ExactFrameCarrierMismatch);
    }
    let executor_consensus_predecessors =
        crate::executor_side_state_persistence::capture_executor_consensus_predecessors(&executor)
            .map_err(|_| ExecutorProducedFinalizationError::NonDurableExecutorSideStateMutation)?;
    executor
        .install_exact_fnsp_v3_admission(accepted)
        .map_err(ExecutorProducedFinalizationError::ExactAdmission)?;

    let pre = ledger;
    let mut post = pre.clone();
    let roots_before = executor_roots(&executor);
    let rate_limits_before = executor.rate_limit_counters.lock().unwrap().clone();
    let rate_limit_sums_before = executor.rate_limit_sum_counters.lock().unwrap().clone();
    let result = super::executor_setup::execute_via_producer(
        &executor,
        &signed.turn,
        &mut post,
        lean_producer_enabled,
    );
    let roots_after = executor_roots(&executor);
    if *executor.rate_limit_counters.lock().unwrap() != rate_limits_before
        || *executor.rate_limit_sum_counters.lock().unwrap() != rate_limit_sums_before
    {
        return Err(ExecutorProducedFinalizationError::NonDurableExecutorSideStateMutation);
    }

    let (receipt, accepted) = match result {
        TurnResult::Committed { receipt, .. } => {
            executor
                .promote_applied_exact_fnsp_v3_admission_after_commit()
                .map_err(ExecutorProducedFinalizationError::ExactAdmission)?;
            let accepted = executor
                .take_consumed_exact_fnsp_v3_admission()
                .map_err(ExecutorProducedFinalizationError::ExactAdmission)?
                .ok_or(ExecutorProducedFinalizationError::ExactAdmissionMissingAfterCommit)?;
            (receipt, accepted)
        }
        other => {
            if dregg_persist::canonical_ledger_root(&post)
                != dregg_persist::canonical_ledger_root(&pre)
            {
                return Err(ExecutorProducedFinalizationError::ProducerRejectedAfterMutation);
            }
            return Err(ExecutorProducedFinalizationError::ProducerDidNotCommit(
                format!("{other:?}"),
            ));
        }
    };

    let seal = seal_execution(
        durable_actor,
        actor_coordinates,
        signer.public_key(),
        signed,
        validated,
        &pre,
        &post,
        roots_before,
        roots_after,
        receipt,
        coordinates,
    )?;

    // The whole-turn receipt still uses the deployed legacy nullifier-set root.  The proof-local
    // exact descriptor instead starts from FNS3(root,count); this context is constructible only
    // with the mandatory verifier-accepted token recovered from the committed execution.
    let mut proof_context_before = seal.context_before;
    proof_context_before.nullifier_root = dregg_circuit::Faithful8::from_bytes32(
        &u32_lanes_to_bytes(accepted.binding().prior_fns3()),
    );

    // This is the sole authority mint.  `seal_execution` cannot construct this type, and the
    // consumed executor is the exact instance whose side tables were mutated by the producer.
    Ok(ExecutorProducedFinalizedTurn {
        core: ExecutorProducedFinalizedTurnCore {
            durable_actor_pre: seal.durable_actor_pre,
            actor_coordinates: seal.actor_coordinates,
            post_ledger: seal.post_ledger,
            post_executor: executor,
            context_before: seal.context_before,
            context_after: seal.context_after,
            proof_context_before,
            receipt: seal.receipt,
            record: seal.record,
            executor_public_key: seal.executor_public_key,
            executor_consensus_predecessors,
            authenticated_exact_spend: seal.authenticated_exact_spend,
        },
        accepted,
    })
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
    durable_actor: Cell,
    actor_coordinates: DurableExactFnspV3ActorCoordinates,
    executor_public_key: dregg_types::PublicKey,
    signed: &SignedTurn,
    validated: ValidatedSignedTurn,
    pre: &Ledger,
    post: &Ledger,
    roots_before: ExecutorRoots,
    roots_after: ExecutorRoots,
    receipt: TurnReceipt,
    coordinates: FinalizedRecordCoordinates,
) -> Result<ValidatedExecutionSeal, ExecutorProducedFinalizationError> {
    let turn_hash = signed.turn.hash();
    if turn_hash != validated.turn_hash() {
        return Err(ExecutorProducedFinalizationError::ValidatedTurnHashMismatch);
    }
    let authenticated_exact_spend = AuthenticatedExactFnspV3Spend::from_signed_turn(signed)?;
    if actor_coordinates.actor_id() != signed.turn.agent
        || pre.get(&signed.turn.agent) != Some(&durable_actor)
    {
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

    dregg_turn::verify_receipt_signature_with_keys(&receipt, &[executor_public_key.0])
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

    Ok(ValidatedExecutionSeal {
        durable_actor_pre: durable_actor,
        actor_coordinates,
        post_ledger: post.clone(),
        context_before,
        context_after,
        receipt,
        record,
        executor_public_key: executor_public_key.0,
        authenticated_exact_spend,
    })
}

fn u32_lanes_to_bytes(lanes: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (lane, value) in lanes.into_iter().enumerate() {
        bytes[lane * 4..lane * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

fn exact_note_spends(forest: &dregg_turn::CallForest) -> Vec<&Effect> {
    fn collect<'a>(effect: &'a Effect, out: &mut Vec<&'a Effect>) {
        match effect {
            Effect::NoteSpend { .. } => out.push(effect),
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, out);
                }
            }
            _ => {}
        }
    }

    let mut spends = Vec::new();
    for effect in forest.total_effects() {
        collect(effect, &mut spends);
    }
    spends
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
    // `Ledger` is backed by a `HashMap`.  Its process-random iteration order must not leak into
    // the durable record: the same state transition has one canonical post-image regardless of
    // insertion order or hash seed.
    touched_cells.sort_unstable_by_key(|cell| cell.id().0);
    removed.sort_unstable();
    (touched_cells, removed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_fnsp_v3_activation::ExactFnspV3ExecutorSignerAuthority;
    use crate::exact_fnsp_v3_actor_authority::capture_durable_exact_fnsp_v3_actor_for_test;
    use dregg_cell::CellId;
    use dregg_cell::commitment_set::CommitmentSet;
    use dregg_cell::nullifier_set::NullifierSet;
    use dregg_cell::revoked_set::RevokedSet;
    use dregg_persist::{CommitRecord, PersistentStore};
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::{Action, Authorization, CallForest, CommitmentMode, DelegationMode, Turn};
    use dregg_types::{Signature, sign};

    fn exact_spend(tag: u8) -> Effect {
        Effect::NoteSpend {
            nullifier: dregg_cell::Nullifier([tag; 32]),
            note_tree_root: [tag.wrapping_add(1); 32],
            value: 0,
            asset_type: 23,
            spending_proof: FaithfulNoteSpendExactV3ProofCarrier::new(
                u64::from(tag),
                vec![tag.wrapping_add(2)],
            )
            .expect("bounded proof carrier")
            .encode(),
            value_commitment: None,
        }
    }

    fn signed_turn(cclerk: &AgentCipherclerk, actor: CellId) -> SignedTurn {
        let mut call_forest = CallForest::new();
        call_forest.add_root(Action {
            target: actor,
            method: [0x61; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![exact_spend(0x31)],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });
        let turn = Turn {
            agent: actor,
            nonce: 0,
            call_forest,
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
        let mut ledger = Ledger::new();
        ledger.insert_cell(actor.clone()).expect("checkpoint actor");
        store.checkpoint_ledger(&ledger, 0).expect("checkpoint");
        store
            .commit_finalized_turn(
                0,
                &CommitRecord {
                    ordinal: 0,
                    height: 1,
                    block_id: [0x01; 32],
                    block_executed_up_to: 0,
                    turn_hash: [0x02; 32],
                    creator: actor.id().0,
                    receipt_hash: [0x03; 32],
                    ledger_root: dregg_persist::canonical_ledger_root(&ledger),
                    touched_cells: vec![actor.clone()],
                    removed: vec![],
                },
            )
            .expect("durable actor");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("exact initial state");
        store
    }

    #[allow(clippy::too_many_arguments)]
    fn seal_execution_for_test(
        store: &PersistentStore,
        cclerk: &AgentCipherclerk,
        signed: &SignedTurn,
        validated: ValidatedSignedTurn,
        pre: &Ledger,
        post: &Ledger,
        roots_before: ExecutorRoots,
        roots_after: ExecutorRoots,
        receipt: TurnReceipt,
        coordinates: FinalizedRecordCoordinates,
    ) -> Result<ValidatedExecutionSeal, ExecutorProducedFinalizationError> {
        let (_, durable_live_ledger) = store
            .load_latest_ledger_checkpoint()
            .expect("load test checkpoint")
            .expect("test checkpoint exists");
        let authority = capture_durable_exact_fnsp_v3_actor_for_test(
            store,
            &durable_live_ledger,
            signed.turn.agent,
        )
        .expect("test durable actor authority");
        let (durable_actor, _durable_ledger, actor_coordinates) = authority.into_execution_parts();
        seal_execution(
            durable_actor,
            actor_coordinates,
            cclerk.public_key(),
            signed,
            validated,
            pre,
            post,
            roots_before,
            roots_after,
            receipt,
            coordinates,
        )
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
    fn exact_route_classifier_selects_v3_fail_closed_and_excludes_other_routes() {
        let (_, cclerk, signed, _, _, _) = fixture();

        let selected = exact_fnsp_v3_route_coordinates(&signed)
            .expect("valid exact-v3 route")
            .expect("v3 selected");
        assert_eq!(selected.nullifier(), [0x31; 32]);
        assert_eq!(selected.value(), 0);

        let mut malformed_v3 = signed.clone();
        let Effect::NoteSpend { spending_proof, .. } =
            &mut malformed_v3.turn.call_forest.roots[0].action.effects[0]
        else {
            unreachable!()
        };
        spending_proof.truncate(5); // retain `FNSP || version=3`, corrupt the carrier body.
        assert!(
            exact_fnsp_v3_route_coordinates(&malformed_v3).is_err(),
            "a malformed v3-prefixed carrier must not fall through to legacy dispatch"
        );

        let mut v2 = signed.clone();
        let Effect::NoteSpend { spending_proof, .. } =
            &mut v2.turn.call_forest.roots[0].action.effects[0]
        else {
            unreachable!()
        };
        spending_proof[4] = 2;
        assert!(
            exact_fnsp_v3_route_coordinates(&v2)
                .expect("v2 classification")
                .is_none(),
            "the exact-v3 classifier must leave v2 to its existing route"
        );

        let mut ordinary = signed_turn(&cclerk, signed.turn.agent);
        ordinary.turn.call_forest.roots[0].action.effects.clear();
        assert!(
            exact_fnsp_v3_route_coordinates(&ordinary)
                .expect("ordinary classification")
                .is_none()
        );
    }

    #[tokio::test]
    async fn durable_actor_coordinates_refuse_ram_ledger_drift() {
        let (store, _, signed, _, pre, _) = fixture();
        let authority =
            capture_durable_exact_fnsp_v3_actor_for_test(&store, &pre, signed.turn.agent)
                .expect("durable actor authority");
        let coordinates = authority.coordinates();

        let temp = tempfile::tempdir().expect("temporary node state");
        let state = crate::state::NodeState::new(temp.path(), Vec::new()).expect("node state");
        let mut locked = state.write().await;
        locked.store = std::sync::Arc::new(store);
        locked.ledger = pre;
        coordinates
            .revalidate_locked(&locked)
            .expect("unchanged actor snapshot");

        locked
            .ledger
            .get_mut(&signed.turn.agent)
            .expect("live actor")
            .state
            .set_nonce(1);
        assert!(matches!(
            coordinates.revalidate_locked(&locked),
            Err(DurableExactFnspV3ActorAuthorityError::SnapshotMoved)
        ));
    }

    #[test]
    fn exact_spend_projection_refuses_zero_two_nested_and_mixed_version_carriers() {
        let (_, cclerk, signed, _, _, _) = fixture();

        let mut zero = signed.clone();
        zero.turn.call_forest.roots[0].action.effects.clear();
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&zero),
            Err(ExecutorProducedFinalizationError::ExactNoteSpendCardinality { found: 0 })
        ));

        let mut two = signed.clone();
        two.turn.call_forest.roots[0]
            .action
            .effects
            .push(exact_spend(0x41));
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&two),
            Err(ExecutorProducedFinalizationError::ExactNoteSpendCardinality { found: 2 })
        ));

        let mut nested = signed_turn(&cclerk, signed.turn.agent);
        nested.turn.call_forest.roots[0].action.effects = vec![Effect::ExerciseViaCapability {
            cap_slot: 7,
            inner_effects: vec![exact_spend(0x51)],
        }];
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&nested),
            Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported)
        ));

        let mut malformed = signed.clone();
        let Effect::NoteSpend { spending_proof, .. } =
            &mut malformed.turn.call_forest.roots[0].action.effects[0]
        else {
            unreachable!()
        };
        spending_proof[4] = 2; // exact route is version 3; v2 must not be mixed in.
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&malformed),
            Err(ExecutorProducedFinalizationError::ExactProofCarrierInvalid(
                _
            ))
        ));

        let mut nonconserving = signed.clone();
        let Effect::NoteSpend { value, .. } =
            &mut nonconserving.turn.call_forest.roots[0].action.effects[0]
        else {
            unreachable!()
        };
        *value = 1;
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&nonconserving),
            Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported)
        ));

        let mut committed_value = signed.clone();
        let Effect::NoteSpend {
            value_commitment, ..
        } = &mut committed_value.turn.call_forest.roots[0].action.effects[0]
        else {
            unreachable!()
        };
        *value_commitment = Some([0x91; 32]);
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&committed_value),
            Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported)
        ));

        let mut charged_sidecar = signed;
        charged_sidecar.turn.call_forest.roots[0]
            .action
            .witness_blobs
            .push(dregg_turn::action::WitnessBlob {
                kind: dregg_turn::action::WitnessKind::Cleartext,
                bytes: vec![1],
            });
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&charged_sidecar),
            Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported)
        ));

        let mut different_target = signed_turn(&cclerk, charged_sidecar.turn.agent);
        different_target.turn.call_forest.roots[0].action.target = dregg_cell::CellId([0xee; 32]);
        assert!(matches!(
            AuthenticatedExactFnspV3Spend::from_signed_turn(&different_target),
            Err(ExecutorProducedFinalizationError::ExactTurnShapeUnsupported)
        ));
    }

    /// Full 3,760-column HidingFRI proof -> verifier-minted admission -> ONE producer gate ->
    /// executor-signed full receipt -> proof-bound exact frame.  Heavy by construction; keep it
    /// out of the default loop and run focused under release on the proof/GPU build node.
    #[test]
    #[ignore = "real exact-v3 HidingFRI proof and node producer/frame weld; run focused --release"]
    fn genuine_exact_proof_crosses_one_producer_gate_and_binds_distinct_full_receipt() {
        use dregg_cell::commitment::digest8_to_bytes32;
        use dregg_cell::note::Note;
        use dregg_cell::{AuthRequired, Permissions};
        use dregg_circuit::exact_nullifier_aafi::{
            ExactNullifierAafi, validate_exact_aafi_witness,
        };
        use dregg_circuit_prove::faithful_note_spend::FaithfulNoteOpening;
        use dregg_circuit_prove::faithful_note_spend_exact_v3::{
            FaithfulNoteSpendExactV3Claim, compose_staged_exact_v3_witness,
            prove_staged_exact_v3_zk,
        };
        use dregg_commit::poseidon2_tree::Poseidon2NoteTree16;
        use dregg_turn::{ExactFnspV3ReceiptEpoch, ExactFnspV3StatePoint, Finality};

        let mut cclerk = AgentCipherclerk::from_seed([0x71; 64]);
        let token_id = *blake3::hash(b"default").as_bytes();
        let mut actor = Cell::with_balance(cclerk.public_key().0, token_id, 1_000);
        actor.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let actor_id = actor.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(actor.clone()).expect("actor ledger");
        let store = durable_store(&actor);

        // A zero-value note keeps the deliberately narrow one-effect live slice conserving.  The
        // future characterized widening carries direct NoteCreate outputs in the same authority.
        let spending_key = core::array::from_fn(|index| 0xc0u8.wrapping_add(index as u8));
        let note = Note::with_nonce(
            Note::faithful_owner_v2(&spending_key),
            [0x0123_4567_89ab_cdef, 0, 0, 0, 0, 0, 0, 0],
            core::array::from_fn(|index| 0x40u8.wrapping_add(index as u8)),
            core::array::from_fn(|index| 0x80u8.wrapping_add(index as u8)),
        );
        let mut note_tree = Poseidon2NoteTree16::new();
        note_tree.append_commitment(&note.faithful_commitment_v2().0);
        let note_path = note_tree.prove_membership(0).expect("note membership");
        let opening = FaithfulNoteOpening {
            owner: note.owner,
            value: 0,
            asset_type: note.fields[0],
            creation_nonce: note.creation_nonce,
            randomness: note.randomness,
            spending_key,
        };
        let nullifier = note.faithful_nullifier_v2(&spending_key).0;
        let exact = ExactNullifierAafi::new()
            .prepare_insert(nullifier, 0)
            .expect("fresh exact transition");
        let prepared_transition = store
            .prepare_exact_fnsp_v3_transition_or_replay(nullifier, 0)
            .expect("same-snapshot durable exact transition");
        assert_eq!(
            prepared_transition.cas().expected().root(),
            exact.prior_root
        );
        assert_eq!(
            prepared_transition.cas().successor().root(),
            exact.successor_root
        );

        let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        executor.set_executor_signing_key(cclerk.gossip_signing_key().to_bytes());
        let federation_id = [0x72; 32];
        executor.set_local_federation_id(federation_id);
        let real_context_before = dregg_turn::state_commit::consensus_ctx(
            &ledger,
            executor.note_nullifiers.lock().unwrap().root8(),
            executor.note_commitments.lock().unwrap().root8(),
            executor.note_revoked.lock().unwrap().root8(),
        );
        let mut proof_context_before = real_context_before;
        proof_context_before.nullifier_root =
            dregg_circuit::Faithful8::from_bytes32(&digest8_to_bytes32(exact.prior_state_commit));
        let anchor = dregg_turn::derive_exact_fnsp_v3_durable_anchor(
            &actor,
            &proof_context_before,
            exact.prior_state_commit,
            exact.successor_state_commit,
        )
        .expect("proof-local durable anchor");

        let root_height = 7;
        let historical_lanes = note_tree.root().limbs().map(|felt| felt.as_u32());
        let witness = compose_staged_exact_v3_witness(
            &opening,
            &note_path,
            FaithfulNoteSpendExactV3Claim {
                root_height,
                historical_note_root: historical_lanes,
            },
            &exact,
            *anchor.before_payload(),
        )
        .expect("exact witness composition");
        let proof_bytes = prove_staged_exact_v3_zk(&witness)
            .expect("real hiding proof")
            .to_postcard()
            .expect("canonical proof transport");
        let carrier = FaithfulNoteSpendExactV3ProofCarrier::new(root_height, proof_bytes)
            .expect("strict exact carrier")
            .encode();
        let historical_note_root = u32_lanes_to_bytes(historical_lanes);
        let effect = Effect::NoteSpend {
            nullifier: dregg_cell::Nullifier(nullifier),
            note_tree_root: historical_note_root,
            value: 0,
            asset_type: opening.asset_type,
            spending_proof: carrier,
            value_commitment: None,
        };
        validate_exact_aafi_witness(&exact).expect("witness remains independently valid");
        let accepted_for_stale_ordinal =
            dregg_turn::verify_faithful_note_spend_exact_v3_acceptance(
                &effect,
                prepared_transition.validated(),
                &anchor,
            )
            .expect("code-owned real verifier acceptance");
        let accepted_for_success = dregg_turn::verify_faithful_note_spend_exact_v3_acceptance(
            &effect,
            prepared_transition.validated(),
            &anchor,
        )
        .expect("code-owned real verifier acceptance");
        let mut legacy_tip = TurnReceipt {
            agent: actor_id,
            federation_id,
            post_state_hash: dregg_turn::state_commit::consensus_state_commitment(
                &ledger,
                &actor_id,
                &real_context_before,
            ),
            finality: Finality::Final,
            ..TurnReceipt::default()
        };
        legacy_tip.executor_signature = Some(
            sign(
                &cclerk.gossip_signing_key(),
                &legacy_tip.canonical_executor_signed_message(),
            )
            .0
            .to_vec(),
        );
        let legacy_hash = legacy_tip.receipt_hash();
        executor.set_last_receipt_hash(actor_id, legacy_hash);

        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: actor_id,
            method: [0x73; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![effect],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });
        let turn = Turn {
            agent: actor_id,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: Some(legacy_hash),
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
        let signed = SignedTurn {
            signature: Signature([0; 64]),
            signer: cclerk.public_key(),
            pq_signature: vec![],
            pq_signer: vec![],
            turn,
        };
        let validated = ValidatedSignedTurn::from_turn_hash_for_test(signed.turn.hash());
        let encoded_legacy_tip = postcard::to_stdvec(&legacy_tip).expect("legacy tip wire");
        store
            .append_receipt_chain_entry(0, &encoded_legacy_tip)
            .expect("durable legacy tip");
        cclerk
            .append_receipt_already_durable(0, legacy_tip.clone())
            .expect("in-memory legacy player head");
        let signer = ExactFnspV3ExecutorSignerAuthority::capture(&cclerk);
        let stale_actor_authority =
            capture_durable_exact_fnsp_v3_actor_for_test(&store, &ledger, actor_id)
                .expect("store-authenticated actor snapshot");
        let commit_ordinal = store.commit_cursor().expect("commit cursor");
        let mut stale_executor = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        stale_executor.set_executor_signing_key(cclerk.gossip_signing_key().to_bytes());
        stale_executor.set_local_federation_id(federation_id);
        stale_executor.set_last_receipt_hash(actor_id, legacy_hash);
        let stale_result = execute_and_authenticate_finalized_turn(
            stale_executor,
            accepted_for_stale_ordinal,
            &signed,
            validated,
            stale_actor_authority,
            &signer,
            false,
            FinalizedRecordCoordinates::new(commit_ordinal + 1, 10, [0x44; 32], 11),
        );
        assert!(matches!(
            stale_result,
            Err(ExecutorProducedFinalizationError::ActorOrdinalMismatch)
        ));

        let actor_authority =
            capture_durable_exact_fnsp_v3_actor_for_test(&store, &ledger, actor_id)
                .expect("fresh store-authenticated actor snapshot");
        let authority = execute_and_authenticate_finalized_turn(
            executor,
            accepted_for_success,
            &signed,
            validated,
            actor_authority,
            &signer,
            false,
            FinalizedRecordCoordinates::new(commit_ordinal, 10, [0x44; 32], 11),
        )
        .expect("one real producer gate mints authority");
        assert_eq!(ledger.get(&actor_id).unwrap().state.nonce(), 0);
        assert_eq!(
            authority
                .core
                .post_ledger
                .get(&actor_id)
                .unwrap()
                .state
                .nonce(),
            1
        );

        let exact_initial = ExactFnspV3StatePoint::new(
            prepared_transition.cas().expected().root(),
            prepared_transition.cas().expected().count(),
        )
        .expect("exact initial point");
        let activation = ExactFnspV3ReceiptEpochV1::prepare(
            ExactFnspV3ReceiptEpoch::new(1).expect("exact epoch"),
            federation_id,
            signer.public_key().0,
            1,
            Some(legacy_hash),
            exact_initial,
        )
        .expect("epoch activation");
        let predecessor = crate::exact_fnsp_v3_activation::exact_fnsp_v3_current_predecessor(
            &store, &cclerk, activation, actor_id,
        )
        .expect("store-authorized frame predecessor");
        let joined = authority
            .bind_exact_frame(&signer, predecessor)
            .expect("executor/proof/frame join");
        assert!(joined.verify_frame_signature());
        assert_eq!(
            joined.post_ledger().get(&actor_id).unwrap().state.nonce(),
            1
        );
        assert_ne!(
            joined.receipt().post_state_hash,
            joined.frame().proof_outer_after().to_bytes(),
            "whole-turn nonce transition is not the proof-local exact AFTER anchor",
        );
    }

    #[test]
    fn opaque_authority_derives_receipt_and_commit_record_from_one_execution_image() {
        let (store, cclerk, signed, validated, pre, mut post) = fixture();
        let roots_before = roots();
        let roots_after = roots();
        // A second changed cell proves the record comes from the complete ledger diff, not just
        // the actor or a caller-authored `LedgerDelta`.
        let extra = Cell::with_balance([0x22; 32], [0x23; 32], 5);
        post.insert_cell(extra.clone()).expect("extra post cell");
        let receipt = signed_receipt(&cclerk, &signed, &pre, &post, roots_before, roots_after);
        let seal = seal_execution_for_test(
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
            seal.durable_actor_pre,
            *pre.get(&signed.turn.agent).unwrap()
        );
        assert_eq!(seal.receipt.turn_hash, signed.turn.hash());
        assert_eq!(seal.record.turn_hash, signed.turn.hash());
        assert_eq!(seal.record.creator, signed.turn.agent.0);
        assert_eq!(seal.record.receipt_hash, seal.receipt.receipt_hash());
        assert_eq!(
            seal.record.ledger_root,
            dregg_persist::canonical_ledger_root(&post)
        );
        assert!(seal.record.touched_cells.iter().any(|cell| cell == &extra));
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
            seal_execution_for_test(
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
            seal_execution_for_test(
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
            seal_execution_for_test(
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
            seal_execution_for_test(
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

    #[test]
    fn complete_post_image_is_canonical_across_ledger_insertion_orders() {
        let token = [0x55; 32];
        let actor = Cell::with_balance([0x10; 32], token, 1);
        let changed_low = Cell::with_balance([0x20; 32], token, 2);
        let changed_high = Cell::with_balance([0xf0; 32], token, 3);
        let removed_low = Cell::with_balance([0x30; 32], token, 4);
        let removed_high = Cell::with_balance([0xe0; 32], token, 5);

        let mut pre_forward = Ledger::new();
        for cell in [
            &actor,
            &changed_low,
            &changed_high,
            &removed_low,
            &removed_high,
        ] {
            pre_forward.insert_cell(cell.clone()).expect("pre cell");
        }
        let mut pre_reverse = Ledger::new();
        for cell in [
            &removed_high,
            &removed_low,
            &changed_high,
            &changed_low,
            &actor,
        ] {
            pre_reverse.insert_cell(cell.clone()).expect("pre cell");
        }

        let mut changed_low_post = changed_low.clone();
        changed_low_post.state.set_nonce(7);
        let mut changed_high_post = changed_high.clone();
        changed_high_post.state.set_nonce(8);
        let added = Cell::with_balance([0x80; 32], token, 6);

        let mut post_forward = Ledger::new();
        for cell in [&actor, &changed_low_post, &added, &changed_high_post] {
            post_forward.insert_cell(cell.clone()).expect("post cell");
        }
        let mut post_reverse = Ledger::new();
        for cell in [&changed_high_post, &added, &changed_low_post, &actor] {
            post_reverse.insert_cell(cell.clone()).expect("post cell");
        }

        let forward = complete_post_image(&pre_forward, &post_forward);
        let reverse = complete_post_image(&pre_reverse, &post_reverse);
        assert_eq!(forward, reverse);
        assert!(
            forward
                .0
                .windows(2)
                .all(|pair| pair[0].id().0 < pair[1].id().0)
        );
        assert!(forward.1.windows(2).all(|pair| pair[0] < pair[1]));
    }
}
