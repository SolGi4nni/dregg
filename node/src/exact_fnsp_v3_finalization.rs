//! Non-live node authority for one exact FNSP-v3 finalized spend.
//!
//! This module deliberately stops short of `blocklace_sync` registration.  It exists to make the
//! cutover boundary a type instead of a pile of adjacent `if`s: the prepared value owns a
//! store-prepared CAS and an opaque proof-acceptance token,
//! after joining both of them to the authenticated turn coordinates, caller-supplied receipt,
//! current durable actor snapshot, and authenticated historical note root.
//!
//! This still is not the live authority.  The V9 context and receipt are caller-supplied values;
//! the executor does not yet return an opaque token that proves they were derived together from
//! its durable pre-state snapshot and execution result.  Durable actor equality plus receipt
//! outer-commit equality are necessary checks, but they cannot substitute for that missing typed
//! executor snapshot/receipt seam.  In fact, exact equality below is presently a deliberately
//! unmintable synthetic gate: the exact anchor changes only FNS3, whereas a real full-turn receipt
//! also commits nonce advancement and may commit fees and other effects.  The live design needs a
//! typed exact-FNS3 subreceipt/frame bound into the full receipt (or a full-turn exact descriptor),
//! not a reinterpretation of the full executor post-state hash.  Keep this candidate unregistered
//! until that seam exists.
//!
//! Two nullifier commitments coexist during migration and must never be compared as though they
//! were the same tree:
//!
//! * `StoredAttestedRoot::nullifier_set_root` is the deployed sorted-dense `FNL8/FNN8` root;
//! * the v3 receipt frame carries `FNS3(root8, count)` for the linked append-order `FNI2/FNN2`
//!   accumulator.
//!
//! They are joined by exact equality of their complete `(sequence, nullifier, value)` durable
//! prefix.  Persistence repeats that equality check under its writer transaction.  Receipt
//! BEFORE/AFTER hashes, on the other hand, must equal the v3 outer commitments exactly.  The
//! current executor therefore cannot mint this candidate for any real turn; a versioned/epoch
//! typed subreceipt/frame migration is a prerequisite for making the route live.

use core::fmt;
use std::error::Error;

use dregg_cell::commitment::{V9RotationContext, digest8_to_bytes32};
use dregg_cell::{Cell, Nullifier};
use dregg_circuit::exact_nullifier_aafi::{ExactAppendRecord, ValidatedExactAafiTransition};
use dregg_federation::frost::MlDsaPublicKey;
use dregg_persist::commit_log::{CommitOutcome, FinalizedFaithfulRootWeld};
use dregg_persist::{
    CommitRecord, ExactFnspV3StateCasV1, FaithfulNoteRootHistoryV1, PersistentStore, StoreError,
};
use dregg_sdk::SignedTurn;
use dregg_turn::faithful_note_spend_exact_v3::FaithfulNoteSpendExactV3ProofCarrier;
use dregg_turn::{
    AcceptedFaithfulNoteSpendExactV3, Effect, ExactFnspV3DurableAnchor,
    FaithfulNoteSpendExactV3AcceptanceBinding, TurnReceipt, derive_exact_fnsp_v3_durable_anchor,
};
use dregg_types::PublicKey;

use crate::signed_turn_validation::ValidatedSignedTurn;

/// Authenticated inputs needed to replay the faithful note-root history.
///
/// A bare `FaithfulNoteRootHistoryV1::new` value is only structurally valid, not authenticated.
/// The orchestrator therefore loads the history itself through the hybrid-verifying store API.
pub(crate) struct ExactFnspV3HistoryAuthority<'a> {
    pub(crate) ed25519_committee: &'a [PublicKey],
    pub(crate) ml_dsa_committee: &'a [MlDsaPublicKey],
    pub(crate) threshold: usize,
}

/// Opaque, non-live candidate for one exact-v3 durable finalization call.
///
/// There is no CAS getter and both commit methods consume `self`.  An accepted proof cannot be
/// detached from its exact transition and reused beside another finalized turn.  This type does
/// not prove that the caller-supplied V9 context and receipt came from one executor run.
pub(crate) struct PreparedExactFnspV3Finalization {
    cas: ExactFnspV3StateCasV1,
    accepted: AcceptedFaithfulNoteSpendExactV3,
    receipt: TurnReceipt,
    encoded_receipt: Vec<u8>,
    turn_hash: [u8; 32],
    actor: [u8; 32],
}

impl PreparedExactFnspV3Finalization {
    /// Append (or byte-exactly replay) the presently synthetic receipt in the carrying transaction.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_appending_receipt(
        self,
        store: &PersistentStore,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        faithful: FinalizedFaithfulRootWeld<'_>,
    ) -> Result<CommitOutcome, ExactFnspV3FinalizationError> {
        self.validate_commit_coordinates(record, &faithful)?;
        store
            .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3(
                expected_ordinal,
                record,
                note_commitments,
                receipt_index,
                &self.encoded_receipt,
                faithful,
                self.cas,
            )
            .map_err(ExactFnspV3FinalizationError::Store)
    }

    /// Require a presently synthetic receipt that already exists byte-for-byte (crash recovery).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_existing_receipt(
        self,
        store: &PersistentStore,
        expected_ordinal: u64,
        record: &CommitRecord,
        note_commitments: &[[u8; 32]],
        receipt_index: u64,
        faithful: FinalizedFaithfulRootWeld<'_>,
    ) -> Result<CommitOutcome, ExactFnspV3FinalizationError> {
        self.validate_commit_coordinates(record, &faithful)?;
        store
            .commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_existing_receipt(
                expected_ordinal,
                record,
                note_commitments,
                receipt_index,
                &self.encoded_receipt,
                faithful,
                self.cas,
            )
            .map_err(ExactFnspV3FinalizationError::Store)
    }

    fn validate_commit_coordinates(
        &self,
        record: &CommitRecord,
        faithful: &FinalizedFaithfulRootWeld<'_>,
    ) -> Result<(), ExactFnspV3FinalizationError> {
        if record.turn_hash != self.turn_hash {
            return Err(ExactFnspV3FinalizationError::CommitRecordTurnMismatch);
        }
        if record.creator != self.actor {
            return Err(ExactFnspV3FinalizationError::CommitRecordActorMismatch);
        }
        if record.receipt_hash != self.receipt.receipt_hash() {
            return Err(ExactFnspV3FinalizationError::CommitRecordReceiptMismatch);
        }

        // Join the legacy finalized-spend authority to the same signed public spend.  Its
        // successor_nullifier_root intentionally remains the legacy FNL8/FNN8 root; the exact AAFI
        // successor is bound by `accepted` + `cas` and is persisted beside it atomically.
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
        let binding = self.accepted.binding();
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
}

/// Prepare a non-live exact-v3 finalized-store candidate.
///
/// This remains crate-private and is not called by `blocklace_sync`.  The caller must first run
/// the normal SignedTurn perimeter and exact proof acceptance, then supply their opaque results.
/// Promotion also requires a future opaque executor-produced token joining its durable input
/// snapshot, V9 context, receipt, and commit record; this function deliberately does not mint it.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_exact_fnsp_v3_candidate(
    store: &PersistentStore,
    signed: &SignedTurn,
    validated_signed: ValidatedSignedTurn,
    receipt: &TurnReceipt,
    actor: &Cell,
    v9_context: &V9RotationContext,
    transition: &ValidatedExactAafiTransition,
    accepted: AcceptedFaithfulNoteSpendExactV3,
    history_authority: ExactFnspV3HistoryAuthority<'_>,
) -> Result<PreparedExactFnspV3Finalization, ExactFnspV3FinalizationError> {
    let turn_hash = signed.turn.hash();
    if turn_hash != validated_signed.turn_hash() {
        return Err(ExactFnspV3FinalizationError::ValidatedTurnHashMismatch);
    }
    if actor.id() != signed.turn.agent {
        return Err(ExactFnspV3FinalizationError::ActorCellMismatch);
    }
    validate_durable_actor(store, actor)?;

    let spends = exact_note_spends(&signed.turn.call_forest);
    let [signed_effect] = spends.as_slice() else {
        return Err(ExactFnspV3FinalizationError::SignedSpendCardinality {
            actual: spends.len(),
        });
    };
    let Effect::NoteSpend {
        nullifier,
        value,
        note_tree_root,
        asset_type,
        spending_proof,
        ..
    } = signed_effect
    else {
        unreachable!("exact_note_spends returns only NoteSpend")
    };
    // The 76 public lanes do not identify every byte of the carrier.  Require the opaque token's
    // post-verification, domain-separated digest to name the exact proof bytes embedded in this
    // authenticated signed effect before joining any durable state or receipt coordinates.
    if !accepted.matches_signed_effect(signed_effect) {
        return Err(ExactFnspV3FinalizationError::AcceptedProofCarrierMismatch);
    }

    validate_receipt_identity(signed, validated_signed, receipt)?;
    validate_legacy_exact_prefix(store)?;

    // Preparation is read-only.  Persistence replays the complete exact prefix and repeats the
    // legacy/exact prefix equality check under the final writer transaction.
    let cas = store
        .prepare_exact_fnsp_v3_append_or_replay(nullifier.0, *value)
        .map_err(ExactFnspV3FinalizationError::Store)?;
    validate_cas_transition(cas, transition)?;

    let anchor = derive_exact_fnsp_v3_durable_anchor(
        actor,
        v9_context,
        cas.expected().fns3(),
        cas.successor().fns3(),
    )
    .map_err(|error| ExactFnspV3FinalizationError::Anchor(error.to_string()))?;
    validate_accepted_binding(
        accepted.binding(),
        transition,
        cas,
        &anchor,
        *nullifier,
        *value,
        *note_tree_root,
        *asset_type,
        spending_proof,
    )?;
    validate_receipt_anchor(receipt, &anchor)?;
    validate_authenticated_history(
        store,
        history_authority,
        accepted.binding().historical_root_height(),
        accepted.binding().historical_note_root(),
    )?;

    let encoded_receipt = postcard::to_stdvec(receipt)
        .map_err(|error| ExactFnspV3FinalizationError::ReceiptEncoding(error.to_string()))?;
    Ok(PreparedExactFnspV3Finalization {
        cas,
        accepted,
        receipt: receipt.clone(),
        encoded_receipt,
        turn_hash,
        actor: actor.id().0,
    })
}

fn validate_durable_actor(
    store: &PersistentStore,
    actor: &Cell,
) -> Result<(), ExactFnspV3FinalizationError> {
    let durable = store
        .lookup_cell(&actor.id())
        .map_err(ExactFnspV3FinalizationError::Store)?
        .ok_or(ExactFnspV3FinalizationError::DurableActorMissing)?;
    // `Cell` equality covers every serialized identity/state/policy field.  Its skipped leaf-cache
    // is intentionally not semantic state and is reconstructed dirty after durable decode.
    if durable != *actor {
        return Err(ExactFnspV3FinalizationError::DurableActorMismatch);
    }
    Ok(())
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

    let mut out = Vec::new();
    for effect in forest.total_effects() {
        collect(effect, &mut out);
    }
    out
}

fn validate_receipt_identity(
    signed: &SignedTurn,
    validated: ValidatedSignedTurn,
    receipt: &TurnReceipt,
) -> Result<(), ExactFnspV3FinalizationError> {
    if receipt.turn_hash != validated.turn_hash() {
        return Err(ExactFnspV3FinalizationError::ReceiptTurnMismatch);
    }
    if receipt.agent != signed.turn.agent {
        return Err(ExactFnspV3FinalizationError::ReceiptActorMismatch);
    }
    if receipt.forest_hash != signed.turn.call_forest.compute_hash() {
        return Err(ExactFnspV3FinalizationError::ReceiptForestMismatch);
    }
    Ok(())
}

fn validate_legacy_exact_prefix(
    store: &PersistentStore,
) -> Result<(), ExactFnspV3FinalizationError> {
    let legacy = store
        .load_faithful_nullifier_records()
        .map_err(ExactFnspV3FinalizationError::Store)?;
    let exact = store
        .exact_fnsp_v3_append_records()
        .map_err(ExactFnspV3FinalizationError::Store)?
        .ok_or(ExactFnspV3FinalizationError::ExactAuthorityUninitialized)?;
    let legacy: Vec<_> = legacy
        .into_iter()
        .map(|(nullifier, value, seq)| ExactAppendRecord {
            seq,
            raw: nullifier.0,
            value,
        })
        .collect();
    if legacy != exact {
        return Err(ExactFnspV3FinalizationError::LegacyExactPrefixMismatch {
            legacy: legacy.len(),
            exact: exact.len(),
        });
    }
    Ok(())
}

fn validate_cas_transition(
    cas: ExactFnspV3StateCasV1,
    transition: &ValidatedExactAafiTransition,
) -> Result<(), ExactFnspV3FinalizationError> {
    let expected = cas.expected();
    let successor = cas.successor();
    let append = cas.append_record();
    let comparisons = [
        (
            append.raw == transition.inserted_raw()
                && append.value == transition.inserted_value()
                && append.seq == expected.generation(),
            ExactFnspV3Coordinate::AppendRecord,
        ),
        (
            expected.root() == transition.prior_root(),
            ExactFnspV3Coordinate::PriorRoot,
        ),
        (
            expected.count() == transition.prior_count(),
            ExactFnspV3Coordinate::PriorCount,
        ),
        (
            successor.root() == transition.successor_root(),
            ExactFnspV3Coordinate::SuccessorRoot,
        ),
        (
            successor.count() == transition.successor_count(),
            ExactFnspV3Coordinate::SuccessorCount,
        ),
    ];
    for (matches, coordinate) in comparisons {
        if !matches {
            return Err(ExactFnspV3FinalizationError::CoordinateMismatch(coordinate));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_accepted_binding(
    accepted: FaithfulNoteSpendExactV3AcceptanceBinding<'_>,
    transition: &ValidatedExactAafiTransition,
    cas: ExactFnspV3StateCasV1,
    anchor: &ExactFnspV3DurableAnchor,
    nullifier: Nullifier,
    value: u64,
    note_tree_root: [u8; 32],
    asset_type: u64,
    spending_proof: &[u8],
) -> Result<(), ExactFnspV3FinalizationError> {
    let carrier = FaithfulNoteSpendExactV3ProofCarrier::decode(spending_proof)
        .map_err(|error| ExactFnspV3FinalizationError::Carrier(error.to_string()))?;
    let expected = cas.expected();
    let successor = cas.successor();
    let comparisons = [
        (
            accepted.nullifier() == nullifier.0,
            ExactFnspV3Coordinate::SignedNullifier,
        ),
        (
            accepted.value() == value,
            ExactFnspV3Coordinate::SignedValue,
        ),
        (
            accepted.asset_type() == asset_type,
            ExactFnspV3Coordinate::SignedAsset,
        ),
        (
            accepted.historical_root_height() == carrier.root_height(),
            ExactFnspV3Coordinate::HistoricalHeight,
        ),
        (
            accepted.historical_note_root() == note_tree_root,
            ExactFnspV3Coordinate::HistoricalRoot,
        ),
        (
            accepted.prior_root() == expected.root().map(|felt| felt.as_u32())
                && accepted.prior_root() == transition.prior_root().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::PriorRoot,
        ),
        (
            accepted.prior_count() == expected.count()
                && accepted.prior_count() == transition.prior_count(),
            ExactFnspV3Coordinate::PriorCount,
        ),
        (
            accepted.prior_fns3() == expected.fns3().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::PriorFns3,
        ),
        (
            accepted.successor_root() == successor.root().map(|felt| felt.as_u32())
                && accepted.successor_root()
                    == transition.successor_root().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::SuccessorRoot,
        ),
        (
            accepted.successor_count() == successor.count()
                && accepted.successor_count() == transition.successor_count(),
            ExactFnspV3Coordinate::SuccessorCount,
        ),
        (
            accepted.successor_fns3() == successor.fns3().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::SuccessorFns3,
        ),
        (
            accepted.before_outer_commit() == anchor.before_commit().map(|felt| felt.as_u32()),
            ExactFnspV3Coordinate::BeforeOuterCommit,
        ),
        (
            accepted.after_outer_commit() == anchor.after_commit().map(|felt| felt.as_u32()),
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

fn validate_receipt_anchor(
    receipt: &TurnReceipt,
    anchor: &ExactFnspV3DurableAnchor,
) -> Result<(), ExactFnspV3FinalizationError> {
    if receipt.pre_state_hash != digest8_to_bytes32(anchor.before_commit()) {
        return Err(ExactFnspV3FinalizationError::ReceiptBeforeAnchorMismatch);
    }
    if receipt.post_state_hash != digest8_to_bytes32(anchor.after_commit()) {
        return Err(ExactFnspV3FinalizationError::ReceiptAfterAnchorMismatch);
    }
    Ok(())
}

fn validate_authenticated_history(
    store: &PersistentStore,
    authority: ExactFnspV3HistoryAuthority<'_>,
    height: u64,
    root: [u8; 32],
) -> Result<(), ExactFnspV3FinalizationError> {
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
    let history = store
        .load_faithful_note_root_history_hybrid(
            authority.ed25519_committee,
            authority.ml_dsa_committee,
            authority.threshold,
            expected,
        )
        .map_err(ExactFnspV3FinalizationError::Store)?;
    if !history_contains_pair(&history, height, root) {
        return Err(ExactFnspV3FinalizationError::HistoricalRootUnauthenticated);
    }
    Ok(())
}

fn history_contains_pair(history: &FaithfulNoteRootHistoryV1, height: u64, root: [u8; 32]) -> bool {
    (history.anchor().height == height && history.anchor().root.to_bytes() == root)
        || history.envelopes().iter().any(|envelope| {
            envelope.record.height == height && envelope.record.successor.to_bytes() == root
        })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExactFnspV3Coordinate {
    SignedNullifier,
    SignedValue,
    SignedAsset,
    HistoricalHeight,
    HistoricalRoot,
    AppendRecord,
    PriorRoot,
    PriorCount,
    PriorFns3,
    SuccessorRoot,
    SuccessorCount,
    SuccessorFns3,
    BeforeOuterCommit,
    AfterOuterCommit,
    FaithfulSpend,
}

#[derive(Debug)]
pub(crate) enum ExactFnspV3FinalizationError {
    ValidatedTurnHashMismatch,
    ActorCellMismatch,
    DurableActorMissing,
    DurableActorMismatch,
    AcceptedProofCarrierMismatch,
    SignedSpendCardinality { actual: usize },
    ReceiptTurnMismatch,
    ReceiptActorMismatch,
    ReceiptForestMismatch,
    ReceiptBeforeAnchorMismatch,
    ReceiptAfterAnchorMismatch,
    ExactAuthorityUninitialized,
    LegacyExactPrefixMismatch { legacy: usize, exact: usize },
    InvalidHistoryAuthority,
    FaithfulHistoryUninitialized,
    HistoricalRootUnauthenticated,
    CommitRecordTurnMismatch,
    CommitRecordActorMismatch,
    CommitRecordReceiptMismatch,
    FaithfulSpendCardinality { actual: usize },
    FaithfulStatementCardinality { actual: usize },
    CoordinateMismatch(ExactFnspV3Coordinate),
    Anchor(String),
    Carrier(String),
    ReceiptEncoding(String),
    Store(StoreError),
}

impl fmt::Display for ExactFnspV3FinalizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValidatedTurnHashMismatch => f.write_str("validated SignedTurn hash mismatch"),
            Self::ActorCellMismatch => {
                f.write_str("durable actor cell is not the signed turn agent")
            }
            Self::DurableActorMissing => {
                f.write_str("signed actor has no current durable cell snapshot")
            }
            Self::DurableActorMismatch => {
                f.write_str("supplied actor pre-state differs from its durable snapshot")
            }
            Self::AcceptedProofCarrierMismatch => f.write_str(
                "accepted exact-v3 token does not name the signed NoteSpend proof carrier bytes",
            ),
            Self::SignedSpendCardinality { actual } => {
                write!(
                    f,
                    "exact FNSP-v3 finalization requires one signed NoteSpend, got {actual}"
                )
            }
            Self::ReceiptTurnMismatch => f.write_str("receipt does not name the validated turn"),
            Self::ReceiptActorMismatch => f.write_str("receipt does not name the signed actor"),
            Self::ReceiptForestMismatch => {
                f.write_str("receipt forest hash does not name the signed forest")
            }
            Self::ReceiptBeforeAnchorMismatch => f.write_str(
                "full receipt BEFORE hash is not the synthetic exact-FNSP-v3-only actor anchor",
            ),
            Self::ReceiptAfterAnchorMismatch => f.write_str(
                "full receipt AFTER hash is not the synthetic exact-FNSP-v3-only actor anchor",
            ),
            Self::ExactAuthorityUninitialized => {
                f.write_str("exact FNSP-v3 durable authority is uninitialized")
            }
            Self::LegacyExactPrefixMismatch { legacy, exact } => write!(
                f,
                "legacy/exact nullifier append prefixes differ ({legacy} != {exact})"
            ),
            Self::InvalidHistoryAuthority => {
                f.write_str("faithful note-root history authority has no real hybrid threshold")
            }
            Self::FaithfulHistoryUninitialized => {
                f.write_str("authenticated faithful note-root history is uninitialized")
            }
            Self::HistoricalRootUnauthenticated => f.write_str(
                "exact FNSP-v3 historical note root is absent from authenticated history",
            ),
            Self::CommitRecordTurnMismatch => {
                f.write_str("commit record does not name the accepted turn")
            }
            Self::CommitRecordActorMismatch => {
                f.write_str("commit record does not name the accepted actor")
            }
            Self::CommitRecordReceiptMismatch => {
                f.write_str("commit record does not name the accepted receipt")
            }
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
            Self::Carrier(error) => write!(f, "exact FNSP-v3 carrier refused: {error}"),
            Self::ReceiptEncoding(error) => {
                write!(f, "exact FNSP-v3 receipt encoding failed: {error}")
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

    use dregg_cell::commitment::RotationCarrierMaterial;
    use dregg_circuit::Faithful8;
    use dregg_circuit::exact_nullifier_aafi::{
        Digest8, ExactNullifierAafi, validate_exact_aafi_witness,
    };
    use dregg_circuit::field::BabyBear;
    use dregg_persist::{CanonicalFaithfulRoot, FaithfulNoteRootAnchorV1};

    fn actor() -> Cell {
        let mut actor = Cell::new([7; 32], [9; 32]);
        assert!(actor.state.credit_balance(17));
        actor.state.set_nonce(3);
        actor
    }

    fn context(prior_fns3: Digest8) -> V9RotationContext {
        V9RotationContext {
            cells_root: BabyBear::new(101),
            nullifier_root: Faithful8::from_bytes32(&digest8_to_bytes32(prior_fns3)),
            commitments_root: Faithful8::ZERO,
            revoked_root: Faithful8::ZERO,
            iroot: BabyBear::new(202),
            material: RotationCarrierMaterial::default(),
        }
    }

    #[test]
    fn production_bootstrap_creates_a_joinable_empty_prefix() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("bootstrap from durable faithful prefix");
        validate_legacy_exact_prefix(&store).expect("byte-identical empty prefix");
    }

    #[test]
    fn same_id_mutated_actor_cannot_supply_the_v9_anchor_prestate() {
        let store = PersistentStore::open_in_memory().expect("store");
        let actor = actor();
        let record = CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [0x11; 32],
            block_executed_up_to: 1,
            turn_hash: [0x12; 32],
            creator: actor.id().0,
            receipt_hash: [0x13; 32],
            ledger_root: [0x14; 32],
            touched_cells: vec![actor.clone()],
            removed: vec![],
        };
        store
            .commit_finalized_turn(0, &record)
            .expect("durable actor snapshot");
        validate_durable_actor(&store, &actor).expect("byte-exact durable actor");

        // Mutable state is not part of CellId derivation.  Merely naming the same actor therefore
        // cannot authorize a context/anchor derived from a stale or invented pre-state.
        let mut same_id_mutated = actor.clone();
        same_id_mutated.state.set_nonce(4);
        assert_eq!(same_id_mutated.id(), actor.id());
        assert!(matches!(
            validate_durable_actor(&store, &same_id_mutated),
            Err(ExactFnspV3FinalizationError::DurableActorMismatch)
        ));
    }

    #[test]
    fn stale_transition_refuses_against_current_store_prepared_cas() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("empty exact authority");

        // Build N from a different frontier (after unrelated M), while the durable store still
        // prepares N from genesis.  Equal spend coordinates do not rescue a stale root/count pair.
        let mut stale_accumulator = ExactNullifierAafi::new();
        let unrelated = stale_accumulator
            .prepare_insert([0x32; 32], 32)
            .expect("unrelated witness");
        stale_accumulator
            .apply_witness(&unrelated)
            .expect("advance stale frontier");
        let stale_witness = stale_accumulator
            .prepare_insert([0x31; 32], 31)
            .expect("stale witness");
        let stale = validate_exact_aafi_witness(&stale_witness).expect("stale transition");

        let current = store
            .prepare_exact_fnsp_v3_append_or_replay([0x31; 32], 31)
            .expect("current candidate");
        assert!(matches!(
            validate_cas_transition(current, &stale),
            Err(ExactFnspV3FinalizationError::CoordinateMismatch(
                ExactFnspV3Coordinate::PriorRoot
                    | ExactFnspV3Coordinate::PriorCount
                    | ExactFnspV3Coordinate::SuccessorRoot
                    | ExactFnspV3Coordinate::SuccessorCount
            ))
        ));
    }

    #[test]
    fn repeated_preparation_is_read_only_and_coordinate_stable() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("empty exact authority");

        let raw = [0x41; 32];
        let value = 410;
        let witness = ExactNullifierAafi::new()
            .prepare_insert(raw, value)
            .expect("witness");
        let transition = validate_exact_aafi_witness(&witness).expect("transition");

        let first = store
            .prepare_exact_fnsp_v3_append_or_replay(raw, value)
            .expect("fresh candidate");
        validate_cas_transition(first, &transition).expect("fresh coordinates");
        let second = store
            .prepare_exact_fnsp_v3_append_or_replay(raw, value)
            .expect("second read-only preparation");
        validate_cas_transition(second, &transition).expect("repeated coordinates");
        assert_eq!(second, first);
    }

    #[test]
    fn synthetic_receipt_gate_refuses_legacy_nullifier_semantics() {
        let witness = ExactNullifierAafi::new()
            .prepare_insert([0x55; 32], 55)
            .expect("witness");
        let transition = validate_exact_aafi_witness(&witness).expect("transition");
        let actor = actor();
        let anchor = derive_exact_fnsp_v3_durable_anchor(
            &actor,
            &context(witness.prior_state_commit),
            witness.prior_state_commit,
            witness.successor_state_commit,
        )
        .expect("anchor");
        let mut receipt = TurnReceipt {
            pre_state_hash: digest8_to_bytes32(anchor.before_commit()),
            post_state_hash: digest8_to_bytes32(anchor.after_commit()),
            ..TurnReceipt::default()
        };
        assert!(validate_receipt_anchor(&receipt, &anchor).is_ok());

        // The deployed root is a different construction even for the same append prefix.  A
        // receipt carrying it must not be silently reinterpreted as FNS3.  Nor does the positive
        // fixture claim executor mintability: real full-turn post-state also includes nonce and
        // any other effects, hence requires a typed exact-FNS3 subreceipt/frame.
        let mut legacy = dregg_cell::nullifier_set::NullifierSet::new();
        legacy
            .insert(
                Nullifier(transition.inserted_raw()),
                transition.inserted_value(),
            )
            .expect("legacy append");
        receipt.post_state_hash = legacy.faithful_root8_exact().to_bytes32();
        assert!(matches!(
            validate_receipt_anchor(&receipt, &anchor),
            Err(ExactFnspV3FinalizationError::ReceiptAfterAnchorMismatch)
        ));
    }

    #[test]
    fn receipt_identity_joins_validated_turn_actor_and_forest() {
        let actor = actor();
        let turn = dregg_turn::Turn {
            agent: actor.id(),
            nonce: 0,
            call_forest: dregg_turn::CallForest::new(),
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
        let signed = SignedTurn {
            turn,
            signature: dregg_types::Signature([0; 64]),
            signer: PublicKey([0; 32]),
            pq_signature: vec![],
            pq_signer: vec![],
        };
        let validated = ValidatedSignedTurn::from_turn_hash_for_test(signed.turn.hash());
        let mut receipt = TurnReceipt {
            turn_hash: validated.turn_hash(),
            forest_hash: signed.turn.call_forest.compute_hash(),
            agent: actor.id(),
            ..TurnReceipt::default()
        };
        assert!(validate_receipt_identity(&signed, validated, &receipt).is_ok());
        receipt.forest_hash[0] ^= 1;
        assert!(matches!(
            validate_receipt_identity(&signed, validated, &receipt),
            Err(ExactFnspV3FinalizationError::ReceiptForestMismatch)
        ));
    }

    #[test]
    fn historical_pair_must_be_present_in_the_replayed_history() {
        let root = CanonicalFaithfulRoot::from_bytes([0; 32]).expect("canonical root");
        let history = FaithfulNoteRootHistoryV1::new(
            FaithfulNoteRootAnchorV1::new([1; 32], [2; 32], 0, 7, 0, root).expect("anchor"),
        );
        assert!(history_contains_pair(&history, 7, [0; 32]));
        assert!(!history_contains_pair(&history, 8, [0; 32]));
        assert!(!history_contains_pair(&history, 7, [1; 32]));
    }
}
