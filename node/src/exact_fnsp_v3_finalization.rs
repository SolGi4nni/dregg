//! Durable join for one executor-produced exact FNSP-v3 spend.
//!
//! There is deliberately no compatibility constructor here.  Preparation consumes the opaque
//! [`ExecutorProducedExactFnspV3FinalizedTurn`] minted by the executor-authority lane after it has
//! joined all of the following:
//!
//! * one authenticated `SignedTurn` with exactly one recursively nested `NoteSpend`;
//! * the real executor-produced full receipt and internally derived `CommitRecord`;
//! * an accepted exact-v3 proof carrier and its proof-local FNS3 receipt frame;
//! * an authorized receipt epoch; and
//! * an executor signature over the exact frame domain.
//!
//! This module adds the durable exact-state and history joins.  It prepares the CAS from the
//! accepted nullifier/value, compares every root/count/FNS3 coordinate, rebuilds the proof-local
//! outer anchors from the executor's durable actor pre-state and captured pre-context, authenticates
//! `(historical height, note root)`, and retains the whole opaque authority until a consuming atomic
//! store call.  The commit record is never caller-supplied.
//!
//! The real full receipt and proof-local exact anchors are intentionally distinct.  A real turn
//! advances nonce and may change fees/other state, while the exact descriptor changes only FNS3 in
//! its stable proof frame.  No full-receipt/anchor equality appears here.
//!
//! The authorized epoch, every signed frame, and the current global exact head share the
//! finalized-turn transaction.  Ordinary receipts may interleave: every frame names its exact
//! global log row and separately proves the latest predecessor row for that frame's actor.

use core::fmt;
use std::error::Error;

use dregg_cell::Ledger;
use dregg_federation::frost::MlDsaPublicKey;
use dregg_persist::commit_log::{CommitOutcome, FinalizedFaithfulRootWeld};
use dregg_persist::faithful_note_root_history::StoreAuthenticatedHistoricalRoot;
use dregg_persist::{
    CommittedExactFnspV3FrameHeadV1, ExactFnspV3DurableReceiptLinkV1, ExactFnspV3StateCasV1,
    PersistentStore, PreparedExactFnspV3StateTransitionV1, StoreError,
    UntrustedExactFnspV3ActivationV1, UntrustedExactFnspV3FrameV1,
};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{
    ExactFnspV3DurableAnchor, ExactFnspV3OuterCommit, ExactFnspV3ReceiptLinkV1,
    ExactFnspV3StatePoint, FaithfulNoteSpendExactV3AcceptanceBinding, TurnReceipt,
    derive_exact_fnsp_v3_durable_anchor,
};
use dregg_types::PublicKey;

use crate::exact_fnsp_v3_execution_authority::ExecutorProducedExactFnspV3FinalizedTurn;

/// Authenticated inputs needed to replay the faithful note-root history.
///
/// A bare `FaithfulNoteRootHistoryV1` is structural data, not authority.  Preparation loads the
/// history itself through the hybrid-verifying store API and requires a real nonzero threshold.
pub(crate) struct ExactFnspV3HistoryAuthority<'a> {
    pub(crate) ed25519_committee: &'a [PublicKey],
    pub(crate) ml_dsa_committee: &'a [MlDsaPublicKey],
    pub(crate) threshold: usize,
}

/// Opaque candidate retaining executor, proof, frame, CAS, and history joins until commit.
///
/// There is no CAS, record, receipt, frame, or acceptance getter.  Both store methods consume
/// `self`, so none of those authorities can be detached and recombined with another turn.
pub(crate) struct PreparedExactFnspV3Finalization {
    cas: ExactFnspV3StateCasV1,
    authority: ExecutorProducedExactFnspV3FinalizedTurn,
    encoded_receipt: Vec<u8>,
    _historical_root_authority: StoreAuthenticatedHistoricalRoot,
}

/// Opaque proof that the executor post-image may be released after durable success.
///
/// A fresh commit retains the complete post-ledger and the same consumed executor which produced
/// it.  An idempotent replay deliberately retains neither: the persistence contract says replay
/// must not re-apply purely in-memory state already rebuilt from durable storage.
pub(crate) struct DurablyCommittedExactFnspV3Turn {
    outcome: CommitOutcome,
    committed_head: CommittedExactFnspV3FrameHeadV1,
    finalized_receipt_core_id: dregg_turn::FinalizedReceiptIdV1,
    fresh_post_execution: Option<FreshExactFnspV3PostExecution>,
}

struct FreshExactFnspV3PostExecution {
    ledger: Ledger,
    receipt: TurnReceipt,
    receipt_index: u64,
    finalized_receipt_core_id: dregg_turn::FinalizedReceiptIdV1,
    install_receipt_head: bool,
    source_commit_ordinal: u64,
    source_receipt_hash: [u8; 32],
    resolution_events: Vec<dregg_turn::ResolutionEvent>,
}

impl DurablyCommittedExactFnspV3Turn {
    pub(crate) const fn outcome(&self) -> CommitOutcome {
        self.outcome
    }

    pub(crate) const fn committed_head(&self) -> &CommittedExactFnspV3FrameHeadV1 {
        &self.committed_head
    }

    /// Signer-independent semantic identity persisted with this exact finalized turn.
    pub(crate) const fn finalized_receipt_core_id(&self) -> dregg_turn::FinalizedReceiptIdV1 {
        self.finalized_receipt_core_id
    }

    /// Install the two real in-memory owners only after a fresh durable transaction.
    ///
    /// Short-lived executor nullifiers are intentionally not installed: every future production
    /// executor is reseeded from the faithful nullifier records committed in the same transaction.
    pub(crate) fn install_fresh_post_execution(
        self,
        live_ledger: &mut Ledger,
        cclerk: &mut AgentCipherclerk,
        state: &crate::state::NodeState,
        store: &PersistentStore,
    ) -> Result<CommitOutcome, ExactFnspV3FinalizationError> {
        if let Some(fresh) = self.fresh_post_execution {
            // Fresh RAM publication is downstream of the signer-independent consensus object,
            // not merely of the writer's success bit.  Re-read the canonical core by the public
            // receipt coordinate and require the exact id and receipt identity that the atomic
            // writer returned.  FRE1/local signatures never participate in this decision.
            let (persisted_id, persisted_core) = store
                .finalized_receipt_core_v1(fresh.receipt_index)
                .map_err(ExactFnspV3FinalizationError::Store)?
                .ok_or_else(|| {
                    ExactFnspV3FinalizationError::Store(StoreError::Integrity(format!(
                        "fresh exact receipt {} has no durable FRC1 semantic core",
                        fresh.receipt_index
                    )))
                })?;
            if persisted_id != fresh.finalized_receipt_core_id
                || persisted_core.id() != fresh.finalized_receipt_core_id
                || persisted_core.turn_hash() != fresh.receipt.turn_hash
                || persisted_core.agent() != fresh.receipt.agent.0
                || persisted_core.federation_id() != fresh.receipt.federation_id
            {
                return Err(ExactFnspV3FinalizationError::Store(StoreError::Integrity(
                    "fresh exact receipt disagrees with its durable FRC1 semantic core".into(),
                )));
            }
            if fresh.install_receipt_head {
                cclerk
                    .append_receipt_already_durable(fresh.receipt_index, fresh.receipt)
                    .map_err(|error| {
                        ExactFnspV3FinalizationError::ReceiptHeadInstall(error.to_string())
                    })?;
            }
            *live_ledger = fresh.ledger;
            crate::executor_side_state_persistence::trace_durable_resolution_events(
                &fresh.resolution_events,
            );
            crate::promise_resolutions::publish_durable_resolution_events(
                state,
                store,
                fresh.source_commit_ordinal,
                fresh.source_receipt_hash,
                &fresh.resolution_events,
            )
            .map_err(ExactFnspV3FinalizationError::PromiseResolution)?;
        }
        Ok(self.outcome)
    }
}

impl PreparedExactFnspV3Finalization {
    /// Atomically append (or byte-exactly replay) the executor-produced full receipt.
    pub(crate) fn commit_appending_receipt(
        self,
        store: &PersistentStore,
        faithful: FinalizedFaithfulRootWeld<'_>,
    ) -> Result<DurablyCommittedExactFnspV3Turn, ExactFnspV3FinalizationError> {
        self.commit(store, faithful, false)
    }

    /// Require the executor-produced full receipt to exist byte-for-byte during crash recovery.
    pub(crate) fn commit_existing_receipt(
        self,
        store: &PersistentStore,
        faithful: FinalizedFaithfulRootWeld<'_>,
    ) -> Result<DurablyCommittedExactFnspV3Turn, ExactFnspV3FinalizationError> {
        self.commit(store, faithful, true)
    }

    fn commit(
        self,
        store: &PersistentStore,
        faithful: FinalizedFaithfulRootWeld<'_>,
        require_existing_receipt: bool,
    ) -> Result<DurablyCommittedExactFnspV3Turn, ExactFnspV3FinalizationError> {
        validate_faithful_coordinates(self.authority.frame().accepted_binding(), &faithful)?;

        // Reverify the executor's frame-domain signature at the durable boundary, after all
        // caller-provided commit coordinates have been checked and immediately before consuming
        // the opaque authority into the atomic store operation.
        let authority = self.authority.into_finalization_parts();
        if !authority.verify_frame_signature() {
            return Err(ExactFnspV3FinalizationError::FrameSignatureInvalid);
        }
        let (
            durable_actor_pre,
            actor_coordinates,
            post_ledger,
            post_executor,
            context_before,
            context_after,
            proof_context_before,
            receipt,
            record,
            executor_public_key,
            executor_consensus_predecessors,
            frame_signature,
            frame,
            first_frame_activation,
        ) = authority.into_commit_components();
        let expected_ordinal = record.ordinal;
        let receipt_index = frame.receipt_log_index();
        if receipt_index != actor_coordinates.receipt_log_next_index() {
            return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
                "captured receipt cursor",
            ));
        }

        let predecessor = match frame.predecessor() {
            ExactFnspV3ReceiptLinkV1::EpochActivation(hash) => {
                ExactFnspV3DurableReceiptLinkV1::EpochActivation(hash)
            }
            ExactFnspV3ReceiptLinkV1::ExactFrame(hash) => {
                ExactFnspV3DurableReceiptLinkV1::ExactFrame(hash)
            }
        };
        let durable_frame = UntrustedExactFnspV3FrameV1::authenticate_devnet_executor(
            frame.epoch().get(),
            frame.receipt_log_index(),
            predecessor,
            frame.activation_hash(),
            frame.frame_hash(),
            frame.full_predecessor_receipt_index(),
            frame.full_predecessor_receipt_hash(),
            frame.agent().0,
            frame.federation_id(),
            frame.turn_hash(),
            frame.forest_hash(),
            frame.full_receipt_hash(),
            frame.full_pre_state_hash(),
            frame.full_post_state_hash(),
            self.cas.expected(),
            self.cas.successor(),
            frame.proof_outer_before().to_bytes(),
            frame.proof_outer_after().to_bytes(),
            frame.accepted_statement_digest(),
            frame.signed_spending_proof_digest(),
            executor_public_key,
            frame_signature,
        )
        .map_err(ExactFnspV3FinalizationError::Store)?;

        // Resolve the finalized turn on the retained executor candidate before capturing its
        // successor.  This registry is the consensus owner: resolving only NodeState's legacy RAM
        // mirror after commit would make dependent promises disappear again after restart.
        // Events remain candidate-local until the redb transaction below returns Fresh.
        let resolution_events = post_executor
            .reactive_registry
            .lock()
            .map_err(|_| {
                ExactFnspV3FinalizationError::ExecutorState(
                    "executor pending registry mutex is poisoned".into(),
                )
            })?
            .resolve(
                receipt.turn_hash,
                dregg_turn::ResolutionOutcome::Resolved(receipt.clone()),
            );

        // The short-lived executor owns consensus/admission state beyond the ledger.  Snapshot its
        // complete successor and weld both React CAS predecessors into this exact-frame writer;
        // otherwise a committed exact receipt could resolve a promise whose replay/nullifier gate
        // disappeared on restart.
        let mut executor_state =
            crate::executor_side_state_persistence::capture_finalized_executor_consensus_state(
                &post_executor,
                &executor_consensus_predecessors,
            )
            .map_err(ExactFnspV3FinalizationError::ExecutorState)?;
        executor_state.promise_resolutions = crate::promise_resolutions::resolution_candidates(
            expected_ordinal,
            record.receipt_hash,
            &resolution_events,
        )
        .map_err(ExactFnspV3FinalizationError::PromiseResolution)?;

        // Keep every non-Clone authority alive across the atomic call.  Only the store-returned
        // committed head below becomes recovery authority.
        let frame_hash = frame.frame_hash();
        let frame_epoch = frame.epoch();
        let result = if require_existing_receipt {
            store.commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame_existing_receipt(
                expected_ordinal,
                &record,
                receipt_index,
                &self.encoded_receipt,
                faithful,
                self.cas,
                durable_frame,
                first_frame_activation,
                &executor_state,
            )
        } else {
            store.commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame(
                expected_ordinal,
                &record,
                receipt_index,
                &self.encoded_receipt,
                faithful,
                self.cas,
                durable_frame,
                first_frame_activation,
                &executor_state,
            )
        };

        // Explicitly retain the authority locals until the store call has returned.
        drop((
            durable_actor_pre,
            actor_coordinates,
            context_before,
            context_after,
            proof_context_before,
            frame,
            frame_hash,
            frame_epoch,
            post_executor,
        ));
        let durable = result.map_err(ExactFnspV3FinalizationError::Store)?;
        let finalized_receipt_core_id = durable.finalized_receipt_core_id;
        let fresh_post_execution =
            durable
                .outcome
                .freshly_committed
                .then_some(FreshExactFnspV3PostExecution {
                    ledger: post_ledger,
                    receipt,
                    receipt_index,
                    finalized_receipt_core_id,
                    install_receipt_head: !require_existing_receipt,
                    source_commit_ordinal: expected_ordinal,
                    source_receipt_hash: record.receipt_hash,
                    resolution_events,
                });
        Ok(DurablyCommittedExactFnspV3Turn {
            outcome: durable.outcome,
            committed_head: durable.committed_head,
            finalized_receipt_core_id,
            fresh_post_execution,
        })
    }
}

/// Prepare the sole exact-v3 node finalization candidate.
///
/// The input is already executor/frame-bound and non-Clone.  No raw `SignedTurn`, validation token,
/// actor, V9 context, receipt, frame, transition, acceptance, or commit record is accepted here.
pub(crate) fn prepare_exact_fnsp_v3_finalization(
    store: &PersistentStore,
    authority: ExecutorProducedExactFnspV3FinalizedTurn,
    prepared_transition: PreparedExactFnspV3StateTransitionV1,
    history_authority: ExactFnspV3HistoryAuthority<'_>,
) -> Result<PreparedExactFnspV3Finalization, ExactFnspV3FinalizationError> {
    if !authority.verify_frame_signature() {
        return Err(ExactFnspV3FinalizationError::FrameSignatureInvalid);
    }
    store
        .validate_live_exact_fnsp_v3_faithful_bridge()
        .map_err(ExactFnspV3FinalizationError::Store)?;

    let binding = authority.frame().accepted_binding();
    let cas = prepared_transition.cas();
    validate_persisted_frame_predecessor(store, &authority, cas)?;
    validate_bound_authority_cas(&authority, cas)?;
    let historical_root_authority = validate_authenticated_history(
        store,
        history_authority,
        binding.historical_root_height(),
        binding.historical_note_root(),
    )?;

    let encoded_receipt = postcard::to_stdvec(authority.receipt())
        .map_err(|error| ExactFnspV3FinalizationError::ReceiptEncoding(error.to_string()))?;
    Ok(PreparedExactFnspV3Finalization {
        cas,
        authority,
        encoded_receipt,
        _historical_root_authority: historical_root_authority,
    })
}

fn validate_persisted_frame_predecessor(
    store: &PersistentStore,
    authority: &ExecutorProducedExactFnspV3FinalizedTurn,
    cas: ExactFnspV3StateCasV1,
) -> Result<(), ExactFnspV3FinalizationError> {
    // Store opening already performs the full canonical receipt/frame replay.  Finalization needs
    // only the signed live boundary, loaded from one snapshot so activation, current frame, and
    // exact head cannot be mixed across concurrent writers.
    let live = store
        .exact_fnsp_v3_live_authority()
        .map_err(ExactFnspV3FinalizationError::Store)?;
    let frame = authority.frame();
    let candidate = authority.first_frame_activation();
    let Some((activation, committed)) = live else {
        let candidate =
            candidate.ok_or(ExactFnspV3FinalizationError::PersistedActivationMissing)?;
        validate_first_frame_activation_candidate(candidate, frame, cas)?;
        return Ok(());
    };
    if frame.epoch().get() != activation.epoch()
        || frame.activation_hash() != activation.activation_hash()
        || frame.federation_id() != activation.federation_id()
        || frame.receipt_log_index() < activation.receipt_cutover_next_index()
    {
        return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
            "activation scope",
        ));
    }

    let current_exact = committed
        .as_ref()
        .map(CommittedExactFnspV3FrameHeadV1::exact_after)
        .unwrap_or_else(|| activation.exact_initial());
    let sequence = cas.expected().generation();
    if sequence == activation.exact_initial().generation() && current_exact == cas.expected() {
        if committed.is_some()
            || frame.predecessor()
                != ExactFnspV3ReceiptLinkV1::EpochActivation(activation.activation_hash())
            || cas.expected() != activation.exact_initial()
        {
            return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
                "first frame",
            ));
        }
    } else if sequence == current_exact.generation() {
        let head = committed.ok_or(ExactFnspV3FinalizationError::PersistedHeadMismatch(
            "missing current frame head",
        ))?;
        if frame.predecessor() != ExactFnspV3ReceiptLinkV1::ExactFrame(head.frame_hash())
            || frame.receipt_log_index() <= head.receipt_log_index()
            || frame.before().root() != head.exact_after().root()
            || frame.before().count() != head.exact_after().count()
            || frame.before().fns3() != head.exact_after().fns3()
            || frame.federation_id() != head.federation_id()
        {
            return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
                "current predecessor",
            ));
        }
    } else if sequence < current_exact.generation() {
        // Historical replay is verified against its immutable dense frame row inside the same
        // writer transaction.  The current tip may legitimately be several frames later.
        if committed.is_none() {
            return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
                "historical replay without head",
            ));
        }
    } else {
        return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
            "future exact sequence",
        ));
    }
    Ok(())
}

fn validate_first_frame_activation_candidate(
    activation: &UntrustedExactFnspV3ActivationV1,
    frame: &dregg_turn::UntrustedExactFnspV3ReceiptFrameJoinV1,
    cas: ExactFnspV3StateCasV1,
) -> Result<(), ExactFnspV3FinalizationError> {
    if frame.epoch().get() != activation.epoch()
        || frame.activation_hash() != activation.activation_hash()
        || frame.federation_id() != activation.federation_id()
        || frame.receipt_log_index() != activation.receipt_cutover_next_index()
        || frame.predecessor()
            != ExactFnspV3ReceiptLinkV1::EpochActivation(activation.activation_hash())
        || cas.expected() != activation.exact_initial()
        || cas.expected().generation() != activation.exact_initial().generation()
    {
        return Err(ExactFnspV3FinalizationError::PersistedHeadMismatch(
            "prepared first-frame activation",
        ));
    }
    Ok(())
}

fn validate_bound_authority_cas(
    authority: &ExecutorProducedExactFnspV3FinalizedTurn,
    cas: ExactFnspV3StateCasV1,
) -> Result<(), ExactFnspV3FinalizationError> {
    let binding = authority.frame().accepted_binding();
    validate_frame_points_against_cas(authority.frame().before(), authority.frame().after(), cas)?;

    let expected = cas.expected();
    let successor = cas.successor();
    let append = cas.append_record();
    let comparisons = [
        (
            append.raw == binding.nullifier()
                && append.value == binding.value()
                && append.seq == expected.generation(),
            ExactFnspV3Coordinate::AppendRecord,
        ),
        (
            binding.prior_root() == expected.root().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::PriorRoot,
        ),
        (
            binding.prior_count() == expected.count(),
            ExactFnspV3Coordinate::PriorCount,
        ),
        (
            binding.prior_fns3() == expected.fns3().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::PriorFns3,
        ),
        (
            binding.successor_root() == successor.root().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::SuccessorRoot,
        ),
        (
            binding.successor_count() == successor.count(),
            ExactFnspV3Coordinate::SuccessorCount,
        ),
        (
            binding.successor_fns3() == successor.fns3().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::SuccessorFns3,
        ),
    ];
    for (matches, coordinate) in comparisons {
        if !matches {
            return Err(ExactFnspV3FinalizationError::CoordinateMismatch(coordinate));
        }
    }

    // Rebuild proof-local anchors only from the executor's durable pre-state and captured real
    // pre-context.  The real post-context is intentionally not substituted: it also contains the
    // nonce/effects of the whole turn, while this descriptor's stable frame changes only FNS3.
    let anchor = derive_exact_fnsp_v3_durable_anchor(
        authority.durable_actor_pre(),
        &authority.proof_context_before(),
        expected.fns3(),
        successor.fns3(),
    )
    .map_err(|error| ExactFnspV3FinalizationError::Anchor(error.to_string()))?;
    validate_proof_outer_commits(
        &anchor,
        authority.frame().proof_outer_before(),
        authority.frame().proof_outer_after(),
        binding,
    )
}

fn validate_frame_points_against_cas(
    before: ExactFnspV3StatePoint,
    after: ExactFnspV3StatePoint,
    cas: ExactFnspV3StateCasV1,
) -> Result<(), ExactFnspV3FinalizationError> {
    let expected = cas.expected();
    let successor = cas.successor();
    let comparisons = [
        (
            before.root() == expected.root(),
            ExactFnspV3Coordinate::FramePriorRoot,
        ),
        (
            before.count() == expected.count(),
            ExactFnspV3Coordinate::FramePriorCount,
        ),
        (
            before.fns3() == expected.fns3(),
            ExactFnspV3Coordinate::FramePriorFns3,
        ),
        (
            after.root() == successor.root(),
            ExactFnspV3Coordinate::FrameSuccessorRoot,
        ),
        (
            after.count() == successor.count(),
            ExactFnspV3Coordinate::FrameSuccessorCount,
        ),
        (
            after.fns3() == successor.fns3(),
            ExactFnspV3Coordinate::FrameSuccessorFns3,
        ),
    ];
    for (matches, coordinate) in comparisons {
        if !matches {
            return Err(ExactFnspV3FinalizationError::CoordinateMismatch(coordinate));
        }
    }
    Ok(())
}

fn validate_proof_outer_commits(
    anchor: &ExactFnspV3DurableAnchor,
    frame_before: ExactFnspV3OuterCommit,
    frame_after: ExactFnspV3OuterCommit,
    binding: FaithfulNoteSpendExactV3AcceptanceBinding<'_>,
) -> Result<(), ExactFnspV3FinalizationError> {
    let expected_before = anchor.before_commit();
    let expected_after = anchor.after_commit();
    let comparisons = [
        (
            frame_before.lanes() == expected_before
                && binding.before_outer_commit() == expected_before.map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::BeforeOuterCommit,
        ),
        (
            frame_after.lanes() == expected_after
                && binding.after_outer_commit() == expected_after.map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::AfterOuterCommit,
        ),
    ];
    for (matches, coordinate) in comparisons {
        if !matches {
            return Err(ExactFnspV3FinalizationError::CoordinateMismatch(coordinate));
        }
    }
    Ok(())
}

fn validate_authenticated_history(
    store: &PersistentStore,
    authority: ExactFnspV3HistoryAuthority<'_>,
    height: u64,
    root: [u8; 32],
) -> Result<StoreAuthenticatedHistoricalRoot, ExactFnspV3FinalizationError> {
    if authority.threshold == 0
        || authority.ed25519_committee.len() < authority.threshold
        || authority.ml_dsa_committee.len() < authority.threshold
    {
        return Err(ExactFnspV3FinalizationError::InvalidHistoryAuthority);
    }
    let expected = store
        .faithful_note_root_expectation()
        .map_err(ExactFnspV3FinalizationError::Store)?
        .ok_or(ExactFnspV3FinalizationError::FaithfulHistoryUninitialized)?;

    // A first-frame activation is the one deliberate full-chain audit point.  Once activated,
    // every append preserves the dense sealed history in the finalized transaction, and online
    // finalization consumes only the direct signed row plus signed current tail/index seal.
    if store
        .exact_fnsp_v3_live_authority()
        .map_err(ExactFnspV3FinalizationError::Store)?
        .is_none()
    {
        store
            .load_faithful_note_root_history_hybrid(
                authority.ed25519_committee,
                authority.ml_dsa_committee,
                authority.threshold,
                expected,
            )
            .map_err(ExactFnspV3FinalizationError::Store)?;
    }

    store
        .store_authenticated_historical_root_hybrid(
            authority.ed25519_committee,
            authority.ml_dsa_committee,
            authority.threshold,
            height,
            root,
        )
        .map_err(ExactFnspV3FinalizationError::Store)?
        .ok_or(ExactFnspV3FinalizationError::HistoricalRootUnauthenticated)
}

fn validate_faithful_coordinates(
    binding: FaithfulNoteSpendExactV3AcceptanceBinding<'_>,
    faithful: &FinalizedFaithfulRootWeld<'_>,
) -> Result<(), ExactFnspV3FinalizationError> {
    let [spent] = faithful.spent_nullifiers else {
        return Err(ExactFnspV3FinalizationError::FaithfulSpendCardinality {
            actual: faithful.spent_nullifiers.len(),
        });
    };
    let [statement] = faithful.finalized_spends else {
        return Err(ExactFnspV3FinalizationError::FaithfulStatementCardinality {
            actual: faithful.finalized_spends.len(),
        });
    };
    if spent.nullifier != binding.nullifier()
        || spent.value != binding.value()
        || statement.nullifier != binding.nullifier()
        || statement.value != binding.value()
        || statement.asset_type != binding.asset_type()
        || statement.root_height != binding.historical_root_height()
        || statement.historical_note_root.to_bytes() != binding.historical_note_root()
    {
        return Err(ExactFnspV3FinalizationError::CoordinateMismatch(
            ExactFnspV3Coordinate::FaithfulSpend,
        ));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExactFnspV3Coordinate {
    AppendRecord,
    PriorRoot,
    PriorCount,
    PriorFns3,
    SuccessorRoot,
    SuccessorCount,
    SuccessorFns3,
    FramePriorRoot,
    FramePriorCount,
    FramePriorFns3,
    FrameSuccessorRoot,
    FrameSuccessorCount,
    FrameSuccessorFns3,
    BeforeOuterCommit,
    AfterOuterCommit,
    FaithfulSpend,
}

#[derive(Debug)]
pub(crate) enum ExactFnspV3FinalizationError {
    FrameSignatureInvalid,
    PersistedActivationMissing,
    PersistedHeadMismatch(&'static str),
    InvalidHistoryAuthority,
    FaithfulHistoryUninitialized,
    HistoricalRootUnauthenticated,
    FaithfulSpendCardinality { actual: usize },
    FaithfulStatementCardinality { actual: usize },
    CoordinateMismatch(ExactFnspV3Coordinate),
    Anchor(String),
    ReceiptEncoding(String),
    ExecutorState(String),
    PromiseResolution(String),
    ReceiptHeadInstall(String),
    Store(StoreError),
}

impl fmt::Display for ExactFnspV3FinalizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FrameSignatureInvalid => {
                f.write_str("exact FNSP-v3 executor frame signature is invalid")
            }
            Self::PersistedActivationMissing => {
                f.write_str("exact FNSP-v3 store-authenticated activation is missing")
            }
            Self::PersistedHeadMismatch(coordinate) => {
                write!(
                    f,
                    "exact FNSP-v3 persisted frame-head mismatch at {coordinate}"
                )
            }
            Self::InvalidHistoryAuthority => {
                f.write_str("faithful note-root history authority has no real hybrid threshold")
            }
            Self::FaithfulHistoryUninitialized => {
                f.write_str("authenticated faithful note-root history is uninitialized")
            }
            Self::HistoricalRootUnauthenticated => f.write_str(
                "exact FNSP-v3 historical note root is absent from authenticated history",
            ),
            Self::FaithfulSpendCardinality { actual } => write!(
                f,
                "faithful weld carries {actual} spends; exact v3 requires one"
            ),
            Self::FaithfulStatementCardinality { actual } => write!(
                f,
                "faithful weld carries {actual} statements; exact v3 requires one"
            ),
            Self::CoordinateMismatch(coordinate) => {
                write!(f, "exact FNSP-v3 coordinate mismatch at {coordinate:?}")
            }
            Self::Anchor(error) => write!(f, "exact FNSP-v3 durable anchor refused: {error}"),
            Self::ReceiptEncoding(error) => {
                write!(f, "exact FNSP-v3 receipt encoding failed: {error}")
            }
            Self::ExecutorState(error) => {
                write!(f, "exact FNSP-v3 executor-state snapshot failed: {error}")
            }
            Self::PromiseResolution(error) => {
                write!(f, "exact FNSP-v3 promise-resolution weld failed: {error}")
            }
            Self::ReceiptHeadInstall(error) => {
                write!(
                    f,
                    "exact FNSP-v3 durable receipt-head install failed: {error}"
                )
            }
            Self::Store(error) => write!(f, "exact FNSP-v3 durable store refused: {error}"),
        }
    }
}

impl Error for ExactFnspV3FinalizationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Store(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi;

    fn point(head: dregg_persist::ExactFnspV3StateHeadV1) -> ExactFnspV3StatePoint {
        ExactFnspV3StatePoint::new(head.root(), head.count()).expect("canonical exact state point")
    }

    #[test]
    fn production_bootstrap_creates_a_joinable_empty_prefix() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("bootstrap from durable faithful prefix");
        store
            .validate_live_exact_fnsp_v3_faithful_bridge()
            .expect("sealed empty prefix");
    }

    #[test]
    fn hostile_mixed_cas_and_frame_points_are_refused() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("empty exact authority");
        let honest = store
            .prepare_exact_fnsp_v3_append_or_replay([0x31; 32], 31)
            .expect("honest CAS");
        validate_frame_points_against_cas(
            point(honest.expected()),
            point(honest.successor()),
            honest,
        )
        .expect("matching frame/CAS");

        // Same predecessor, different append/successor: a frame from another accepted spend cannot
        // be paired with this store-prepared candidate.
        let other = store
            .prepare_exact_fnsp_v3_append_or_replay([0x32; 32], 32)
            .expect("other CAS");
        assert!(matches!(
            validate_frame_points_against_cas(
                point(honest.expected()),
                point(other.successor()),
                honest,
            ),
            Err(ExactFnspV3FinalizationError::CoordinateMismatch(
                ExactFnspV3Coordinate::FrameSuccessorRoot
                    | ExactFnspV3Coordinate::FrameSuccessorFns3
            ))
        ));
    }

    #[test]
    fn hostile_stale_frame_predecessor_is_refused() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("empty exact authority");
        let current = store
            .prepare_exact_fnsp_v3_append_or_replay([0x41; 32], 41)
            .expect("current CAS");

        let mut stale = ExactNullifierAafi::new();
        let first = stale.prepare_insert([0x40; 32], 40).expect("first");
        stale.apply_witness(&first).expect("advance stale state");
        let second = stale.prepare_insert([0x41; 32], 41).expect("second");
        let stale_before = ExactFnspV3StatePoint::new(second.prior_root, second.prior_count)
            .expect("stale before");
        let stale_after = ExactFnspV3StatePoint::new(second.successor_root, second.successor_count)
            .expect("stale after");

        assert!(matches!(
            validate_frame_points_against_cas(stale_before, stale_after, current),
            Err(ExactFnspV3FinalizationError::CoordinateMismatch(
                ExactFnspV3Coordinate::FramePriorRoot
                    | ExactFnspV3Coordinate::FramePriorCount
                    | ExactFnspV3Coordinate::FramePriorFns3
            ))
        ));
    }
}
