//! Restart-durable signer-independent finalized receipt identities.
//!
//! Exact FNSP-v3 finalization already welds the executor receipt, commit record, authenticated
//! consensus root/time, faithful note-root edge, and signed exact frame in one redb transaction.
//! This module projects those independently checked values into `FRC1` and persists the semantic
//! core in that same transaction.  The executor's local signature envelope is deliberately not
//! stored here and is not part of the core id.

use std::collections::{BTreeMap, BTreeSet};

use dregg_federation::frost::MlDsaPublicKey;
use dregg_turn::{
    FinalizedExecutionContextV1, FinalizedReceiptCoreV1, FinalizedReceiptIdV1,
    FinalizedReceiptPredecessorV1, TurnReceipt,
};
use dregg_types::PublicKey;
use redb::{ReadableTable, ReadableTableMetadata, TableDefinition};

use crate::commit_log::{CommitRecord, FinalizedFaithfulRootWeld, decode_commit_record};
use crate::faithful_note_root_history::{FaithfulNoteRootEnvelopeV1, FaithfulNoteRootRecordV1};
use crate::{PersistentStore, Result, StoreError, StoredAttestedRoot};

pub(crate) const FINALIZED_RECEIPT_CORES_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("finalized_receipt_cores_v1");
pub(crate) const FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("finalized_receipt_core_by_receipt_index_v1");
pub(crate) const FINALIZED_RECEIPT_INDEX_BY_CORE_V1: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("finalized_receipt_index_by_core_v1");
pub(crate) const FINALIZED_RECEIPT_CORE_HEADS_V1: TableDefinition<&[u8; 32], &[u8; 72]> =
    TableDefinition::new("finalized_receipt_core_heads_v1");

const HEAD_LEN: usize = 72;

/// The latest semantic-core coordinate for one receipt-chain agent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DurableFinalizedReceiptCoreHeadV1 {
    receipt_index: u64,
    legacy_receipt_hash: [u8; 32],
    core_id: FinalizedReceiptIdV1,
}

impl DurableFinalizedReceiptCoreHeadV1 {
    pub const fn receipt_index(self) -> u64 {
        self.receipt_index
    }

    pub const fn legacy_receipt_hash(self) -> [u8; 32] {
        self.legacy_receipt_hash
    }

    pub const fn core_id(self) -> FinalizedReceiptIdV1 {
        self.core_id
    }
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(format!("finalized FRC1: {}", message.into()))
}

fn decode_receipt(bytes: &[u8]) -> Result<TurnReceipt> {
    let (receipt, remainder): (TurnReceipt, &[u8]) = postcard::take_from_bytes(bytes)?;
    if !remainder.is_empty() {
        return Err(integrity("receipt encoding has trailing bytes"));
    }
    Ok(receipt)
}

fn decode_core(bytes: &[u8]) -> Result<FinalizedReceiptCoreV1> {
    FinalizedReceiptCoreV1::decode_canonical(bytes)
        .map_err(|error| integrity(format!("invalid core wire: {error}")))
}

fn encode_head(head: DurableFinalizedReceiptCoreHeadV1) -> [u8; HEAD_LEN] {
    let mut out = [0u8; HEAD_LEN];
    out[..8].copy_from_slice(&head.receipt_index.to_le_bytes());
    out[8..40].copy_from_slice(&head.legacy_receipt_hash);
    out[40..72].copy_from_slice(&head.core_id.bytes());
    out
}

fn decode_head(bytes: &[u8; HEAD_LEN]) -> Result<DurableFinalizedReceiptCoreHeadV1> {
    let receipt_index = u64::from_le_bytes(bytes[..8].try_into().expect("fixed head width"));
    let legacy_receipt_hash = bytes[8..40].try_into().expect("fixed head width");
    if legacy_receipt_hash == [0; 32] {
        return Err(integrity("head carries a zero legacy receipt hash"));
    }
    let core_id =
        FinalizedReceiptIdV1::from_bytes(bytes[40..72].try_into().expect("fixed head width"))
            .map_err(|error| integrity(format!("invalid head core id: {error}")))?;
    Ok(DurableFinalizedReceiptCoreHeadV1 {
        receipt_index,
        legacy_receipt_hash,
        core_id,
    })
}

fn validate_legacy_predecessor_in(
    write: &redb::WriteTransaction,
    receipt_index: u64,
    predecessor_index: Option<u64>,
    predecessor_hash: Option<[u8; 32]>,
) -> Result<()> {
    if predecessor_index.is_some() != predecessor_hash.is_some() {
        return Err(integrity(
            "legacy predecessor index/hash optionality disagrees",
        ));
    }
    let (Some(index), Some(hash)) = (predecessor_index, predecessor_hash) else {
        return Ok(());
    };
    if index >= receipt_index {
        return Err(integrity("legacy predecessor is not before its successor"));
    }
    let receipts = write.open_table(crate::tables::RECEIPT_CHAIN)?;
    let encoded = receipts
        .get(index)?
        .ok_or_else(|| integrity(format!("legacy predecessor receipt {index} is missing")))?;
    let receipt = decode_receipt(encoded.value())?;
    if receipt.receipt_hash() != hash {
        return Err(integrity(
            "legacy predecessor hash disagrees with durable receipt",
        ));
    }
    Ok(())
}

fn validate_consensus_coordinates(
    record: &CommitRecord,
    faithful: &FaithfulNoteRootRecordV1,
    attested: &StoredAttestedRoot,
    receipt: &TurnReceipt,
    core: &FinalizedReceiptCoreV1,
) -> Result<()> {
    let context = core.context();
    let tau_round = attested
        .finality_round
        .ok_or_else(|| integrity("authenticated finality round is absent"))?;
    if context.block_id() != record.block_id
        || context.block_id() != faithful.block_id
        || attested.blocklace_block_id != Some(context.block_id())
        || context.tau_round() != tau_round
        || context.consensus_unix_seconds() != attested.timestamp
        || core.turn_hash() != record.turn_hash
        || core.turn_hash() != receipt.turn_hash
        || core.agent() != record.creator
        || core.agent() != receipt.agent.0
        || core.federation_id() != faithful.federation_id
        || core.federation_id() != receipt.federation_id
        || attested.federation_id.0 != core.federation_id()
        || core.committee_epoch() != faithful.committee_epoch
        || record.receipt_hash != receipt.receipt_hash()
        || record.height != faithful.height
        || attested.height != faithful.height
    {
        return Err(integrity(
            "core/receipt/commit/faithful-edge/attestation coordinates disagree",
        ));
    }
    Ok(())
}

fn derive_core(
    record: &CommitRecord,
    faithful: &FaithfulNoteRootRecordV1,
    attested: &StoredAttestedRoot,
    predecessor: FinalizedReceiptPredecessorV1,
    receipt: &TurnReceipt,
) -> Result<FinalizedReceiptCoreV1> {
    let tau_round = attested
        .finality_round
        .ok_or_else(|| integrity("authenticated finality round is absent"))?;
    let context = FinalizedExecutionContextV1::new(record.block_id, tau_round, attested.timestamp);
    let core = FinalizedReceiptCoreV1::from_receipt(
        context,
        faithful.committee_epoch,
        predecessor,
        receipt,
    )
    .map_err(|error| integrity(format!("core derivation failed: {error}")))?;
    validate_consensus_coordinates(record, faithful, attested, receipt, &core)?;
    Ok(core)
}

/// Stage the semantic core for a fresh exact frame.
///
/// The predecessor is selected from the durable per-agent semantic head.  A populated legacy
/// receipt link with no semantic head becomes an explicitly tagged one-time cutover; later rows
/// must extend both the semantic id and the still-live legacy receipt coordinate.
pub(crate) fn stage_fresh_finalized_receipt_core_in(
    write: &redb::WriteTransaction,
    record: &CommitRecord,
    receipt_index: u64,
    predecessor_index: Option<u64>,
    predecessor_hash: Option<[u8; 32]>,
    encoded_receipt: &[u8],
    faithful: &FinalizedFaithfulRootWeld<'_>,
) -> Result<FinalizedReceiptIdV1> {
    validate_legacy_predecessor_in(write, receipt_index, predecessor_index, predecessor_hash)?;
    let receipt = decode_receipt(encoded_receipt)?;
    let current_head = {
        let heads = write.open_table(FINALIZED_RECEIPT_CORE_HEADS_V1)?;
        heads
            .get(&receipt.agent.0)?
            .map(|guard| decode_head(guard.value()))
            .transpose()?
    };
    let predecessor = match (current_head, predecessor_index, predecessor_hash) {
        (None, None, None) => FinalizedReceiptPredecessorV1::Genesis,
        (None, Some(legacy_receipt_index), Some(legacy_receipt_hash)) => {
            FinalizedReceiptPredecessorV1::LegacyCutover {
                legacy_receipt_index,
                legacy_receipt_hash,
            }
        }
        (Some(head), Some(index), Some(hash))
            if head.receipt_index == index && head.legacy_receipt_hash == hash =>
        {
            FinalizedReceiptPredecessorV1::Core {
                core_id: head.core_id,
                legacy_receipt_index: index,
                legacy_receipt_hash: hash,
            }
        }
        (Some(_), None, None) => {
            return Err(integrity("existing semantic head was omitted by successor"));
        }
        _ => {
            return Err(integrity(
                "successor does not extend the durable semantic head",
            ));
        }
    };
    let core = derive_core(
        record,
        &faithful.envelope.record,
        faithful.attested_root,
        predecessor,
        &receipt,
    )?;
    let core_id = core.id();
    let core_bytes = core.to_canonical_bytes();
    {
        let mut cores = write.open_table(FINALIZED_RECEIPT_CORES_V1)?;
        if cores.get(&core_id.bytes())?.is_some() {
            return Err(integrity("fresh semantic core id already exists"));
        }
        cores.insert(&core_id.bytes(), core_bytes.as_slice())?;
    }
    {
        let mut by_index = write.open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)?;
        if by_index.get(receipt_index)?.is_some() {
            return Err(integrity("fresh receipt index already has a semantic core"));
        }
        by_index.insert(receipt_index, &core_id.bytes())?;
    }
    {
        let mut by_id = write.open_table(FINALIZED_RECEIPT_INDEX_BY_CORE_V1)?;
        if by_id.get(&core_id.bytes())?.is_some() {
            return Err(integrity(
                "fresh semantic core id already has a receipt index",
            ));
        }
        by_id.insert(&core_id.bytes(), receipt_index)?;
    }
    {
        let mut heads = write.open_table(FINALIZED_RECEIPT_CORE_HEADS_V1)?;
        let head = encode_head(DurableFinalizedReceiptCoreHeadV1 {
            receipt_index,
            legacy_receipt_hash: receipt.receipt_hash(),
            core_id,
        });
        heads.insert(&receipt.agent.0, &head)?;
    }
    Ok(core_id)
}

/// Verify a historical idempotent replay without repairing any missing semantic row.
pub(crate) fn verify_replayed_finalized_receipt_core_in(
    write: &redb::WriteTransaction,
    record: &CommitRecord,
    receipt_index: u64,
    predecessor_index: Option<u64>,
    predecessor_hash: Option<[u8; 32]>,
    encoded_receipt: &[u8],
    faithful: &FinalizedFaithfulRootWeld<'_>,
) -> Result<FinalizedReceiptIdV1> {
    validate_legacy_predecessor_in(write, receipt_index, predecessor_index, predecessor_hash)?;
    let core_id = {
        let by_index = write.open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)?;
        let guard = by_index
            .get(receipt_index)?
            .ok_or_else(|| integrity("replay is missing receipt-index semantic core"))?;
        FinalizedReceiptIdV1::from_bytes(*guard.value())
            .map_err(|error| integrity(format!("invalid replay core id: {error}")))?
    };
    let core = {
        let cores = write.open_table(FINALIZED_RECEIPT_CORES_V1)?;
        let guard = cores
            .get(&core_id.bytes())?
            .ok_or_else(|| integrity("replay is missing semantic core bytes"))?;
        decode_core(guard.value())?
    };
    if core.id() != core_id {
        return Err(integrity("replay core bytes hash to a different id"));
    }
    {
        let by_id = write.open_table(FINALIZED_RECEIPT_INDEX_BY_CORE_V1)?;
        let indexed_receipt = by_id
            .get(&core_id.bytes())?
            .ok_or_else(|| integrity("replay is missing semantic core reverse index"))?;
        if indexed_receipt.value() != receipt_index {
            return Err(integrity("replay semantic core reverse index disagrees"));
        }
    }
    let legacy = match core.predecessor() {
        FinalizedReceiptPredecessorV1::Genesis => (None, None),
        FinalizedReceiptPredecessorV1::LegacyCutover {
            legacy_receipt_index,
            legacy_receipt_hash,
        }
        | FinalizedReceiptPredecessorV1::Core {
            legacy_receipt_index,
            legacy_receipt_hash,
            ..
        } => (Some(legacy_receipt_index), Some(legacy_receipt_hash)),
    };
    if legacy != (predecessor_index, predecessor_hash) {
        return Err(integrity("replay frame and semantic predecessor disagree"));
    }
    let receipt = decode_receipt(encoded_receipt)?;
    let expected = derive_core(
        record,
        &faithful.envelope.record,
        faithful.attested_root,
        core.predecessor(),
        &receipt,
    )?;
    if expected != core {
        return Err(integrity(
            "replayed semantic core differs from durable bytes",
        ));
    }
    Ok(core_id)
}

fn audit_loaded_core(
    core: &FinalizedReceiptCoreV1,
    receipt: &TurnReceipt,
    record: &CommitRecord,
    faithful: &FaithfulNoteRootRecordV1,
    attested: &StoredAttestedRoot,
) -> Result<()> {
    let expected = derive_core(record, faithful, attested, core.predecessor(), receipt)?;
    if &expected != core {
        return Err(integrity("durable core does not rederive at open"));
    }
    Ok(())
}

fn reauthenticate_local_consensus_evidence(
    externally_authenticated_executor: [u8; 32],
    faithful: &FaithfulNoteRootEnvelopeV1,
    attested: &StoredAttestedRoot,
) -> Result<()> {
    let [signer] = faithful.hybrid_quorum.as_slice() else {
        return Err(integrity(
            "solo exact epoch requires exactly one faithful hybrid author",
        ));
    };
    let externally_authenticated_executor = PublicKey(externally_authenticated_executor);
    if signer.pubkey != externally_authenticated_executor {
        return Err(integrity(
            "faithful author is not the exact activation executor",
        ));
    }
    let pq = MlDsaPublicKey(
        signer
            .ml_dsa_pubkey
            .as_slice()
            .try_into()
            .map_err(|_| integrity("faithful author ML-DSA key has the wrong length"))?,
    );
    if !faithful.verify_hybrid(
        std::slice::from_ref(&externally_authenticated_executor),
        std::slice::from_ref(&pq),
        1,
    ) {
        return Err(integrity(
            "faithful hybrid edge failed local restart authentication",
        ));
    }
    if !attested.has_any_valid_committee_signature(
        std::slice::from_ref(&externally_authenticated_executor),
        std::slice::from_ref(&pq),
    ) {
        return Err(integrity(
            "attested consensus root failed local restart authentication",
        ));
    }
    Ok(())
}

impl PersistentStore {
    /// Load one signer-independent semantic core by its global receipt index.
    pub fn finalized_receipt_core_v1(
        &self,
        receipt_index: u64,
    ) -> Result<Option<(FinalizedReceiptIdV1, FinalizedReceiptCoreV1)>> {
        let read = self.db.begin_read()?;
        let by_index = read.open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)?;
        let Some(id) = by_index.get(receipt_index)? else {
            return Ok(None);
        };
        let id = FinalizedReceiptIdV1::from_bytes(*id.value())
            .map_err(|error| integrity(format!("invalid indexed core id: {error}")))?;
        let cores = read.open_table(FINALIZED_RECEIPT_CORES_V1)?;
        let bytes = cores
            .get(&id.bytes())?
            .ok_or_else(|| integrity("receipt index names a missing semantic core"))?;
        let core = decode_core(bytes.value())?;
        if core.id() != id {
            return Err(integrity("indexed core bytes hash to a different id"));
        }
        let by_id = read.open_table(FINALIZED_RECEIPT_INDEX_BY_CORE_V1)?;
        let reverse = by_id
            .get(&id.bytes())?
            .ok_or_else(|| integrity("receipt-indexed core is missing its reverse index"))?;
        if reverse.value() != receipt_index {
            return Err(integrity("receipt/core reverse indexes disagree"));
        }
        Ok(Some((id, core)))
    }

    /// Load one signer-independent semantic core by its typed id and return the unique receipt
    /// index that names it.
    ///
    /// The core and both index rows are checked in both directions on every read.  A missing row,
    /// mismatched coordinate, or id/hash mismatch is an integrity error rather than an absent
    /// result or a silently selected row.  The reverse index keeps this lookup logarithmic; the
    /// full restart audit additionally proves global cardinality and uniqueness.
    pub fn finalized_receipt_core_v1_by_id(
        &self,
        id: FinalizedReceiptIdV1,
    ) -> Result<Option<(u64, FinalizedReceiptCoreV1)>> {
        let read = self.db.begin_read()?;
        let by_id = read.open_table(FINALIZED_RECEIPT_INDEX_BY_CORE_V1)?;
        let cores = read.open_table(FINALIZED_RECEIPT_CORES_V1)?;
        let reverse = by_id.get(&id.bytes())?;
        let bytes = cores.get(&id.bytes())?;
        let (reverse, bytes) = match (reverse, bytes) {
            (None, None) => return Ok(None),
            (Some(_), None) => {
                return Err(integrity("core reverse index names missing core bytes"));
            }
            (None, Some(_)) => {
                return Err(integrity("semantic core bytes are not reverse-indexed"));
            }
            (Some(reverse), Some(bytes)) => (reverse, bytes),
        };
        let core = decode_core(bytes.value())?;
        if core.id() != id {
            return Err(integrity("requested core bytes hash to a different id"));
        }
        let index = reverse.value();
        let by_index = read.open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)?;
        let forward = by_index
            .get(index)?
            .ok_or_else(|| integrity("core reverse index names a missing receipt index"))?;
        if forward.value() != &id.bytes() {
            return Err(integrity("core/receipt reverse indexes disagree"));
        }
        Ok(Some((index, core)))
    }

    /// Load the latest semantic core coordinate for one agent.
    pub fn finalized_receipt_core_head_v1(
        &self,
        agent: &[u8; 32],
    ) -> Result<Option<DurableFinalizedReceiptCoreHeadV1>> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(FINALIZED_RECEIPT_CORE_HEADS_V1)?;
        heads
            .get(agent)?
            .map(|guard| decode_head(guard.value()))
            .transpose()
    }

    /// Full restart audit.  Live writes are O(log N); boot deliberately rederives every semantic
    /// row and every per-agent head from canonical receipts plus authenticated consensus records.
    pub(crate) fn audit_finalized_receipt_cores_v1_on_open(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let frames =
            crate::exact_fnsp_v3_frame_head::exact_fnsp_v3_frame_receipt_coordinates_from_read(
                &read,
            )?;
        let frame_by_receipt: BTreeMap<u64, _> = frames
            .into_iter()
            .map(|frame| (frame.receipt_index, frame))
            .collect();
        let by_index = read.open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)?;
        let by_id = read.open_table(FINALIZED_RECEIPT_INDEX_BY_CORE_V1)?;
        let cores = read.open_table(FINALIZED_RECEIPT_CORES_V1)?;
        let heads = read.open_table(FINALIZED_RECEIPT_CORE_HEADS_V1)?;
        if by_index.len()? != by_id.len()?
            || by_index.len()? != cores.len()?
            || by_index.len()? != frame_by_receipt.len() as u64
        {
            return Err(integrity("frame/core/index cardinalities disagree"));
        }

        let mut faithful_by_block = BTreeMap::new();
        let faithful_rows = read.open_table(crate::tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        for row in faithful_rows.iter()? {
            let (_, bytes) = row.map_err(|error| StoreError::Database(error.to_string()))?;
            let envelope = FaithfulNoteRootEnvelopeV1::from_bytes(bytes.value())?;
            if faithful_by_block
                .insert(envelope.record.block_id, envelope)
                .is_some()
            {
                return Err(integrity("duplicate faithful block id"));
            }
        }

        let receipts = read.open_table(crate::tables::RECEIPT_CHAIN)?;
        let attested = read.open_table(crate::tables::ATTESTED_ROOTS)?;
        let idx_turn = read.open_table(crate::tables::IDX_TURN_BY_HASH)?;
        let log = read.open_table(crate::tables::COMMIT_LOG)?;
        let compacted = read.open_table(crate::tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        let mut rebuilt_heads: BTreeMap<[u8; 32], DurableFinalizedReceiptCoreHeadV1> =
            BTreeMap::new();
        let mut referenced_ids = BTreeSet::new();

        for row in by_index.iter()? {
            let (index, id) = row.map_err(|error| StoreError::Database(error.to_string()))?;
            let receipt_index = index.value();
            let core_id = FinalizedReceiptIdV1::from_bytes(*id.value())
                .map_err(|error| integrity(format!("invalid indexed core id: {error}")))?;
            if !referenced_ids.insert(core_id.bytes()) {
                return Err(integrity("one semantic core id is indexed more than once"));
            }
            let reverse = by_id
                .get(&core_id.bytes())?
                .ok_or_else(|| integrity("semantic core reverse index is missing"))?;
            if reverse.value() != receipt_index {
                return Err(integrity("semantic core reverse index disagrees"));
            }
            let frame = frame_by_receipt
                .get(&receipt_index)
                .ok_or_else(|| integrity("semantic core has no exact frame"))?;
            let core_bytes = cores
                .get(&core_id.bytes())?
                .ok_or_else(|| integrity("indexed semantic core bytes are missing"))?;
            let core = decode_core(core_bytes.value())?;
            if core.id() != core_id {
                return Err(integrity("semantic core id/hash mismatch"));
            }
            let encoded_receipt = receipts
                .get(receipt_index)?
                .ok_or_else(|| integrity("semantic core receipt row is missing"))?;
            let receipt = decode_receipt(encoded_receipt.value())?;
            if frame.agent != receipt.agent.0
                || frame.turn_hash != receipt.turn_hash
                || frame.receipt_hash != receipt.receipt_hash()
            {
                return Err(integrity("semantic core receipt and exact frame disagree"));
            }
            let faithful_envelope = faithful_by_block
                .get(&core.context().block_id())
                .ok_or_else(|| integrity("semantic core has no faithful consensus edge"))?;
            let faithful = &faithful_envelope.record;
            let attested_bytes = attested
                .get(faithful.height)?
                .ok_or_else(|| integrity("semantic core has no attested root"))?;
            let attested_root: StoredAttestedRoot = postcard::from_bytes(attested_bytes.value())?;
            reauthenticate_local_consensus_evidence(
                frame.executor_public_key,
                faithful_envelope,
                &attested_root,
            )?;

            let record = if let Some(ordinal) = idx_turn.get(&core.turn_hash())? {
                let bytes = log
                    .get(ordinal.value())?
                    .ok_or_else(|| integrity("turn index names a missing commit record"))?;
                decode_commit_record(bytes.value())?
            } else if compacted.get(&core.context().block_id())?.is_some() {
                CommitRecord {
                    ordinal: 0,
                    height: faithful.height,
                    block_id: core.context().block_id(),
                    block_executed_up_to: 0,
                    turn_hash: receipt.turn_hash,
                    creator: receipt.agent.0,
                    receipt_hash: receipt.receipt_hash(),
                    ledger_root: attested_root.merkle_root,
                    touched_cells: Vec::new(),
                    removed: Vec::new(),
                }
            } else {
                return Err(integrity(
                    "semantic core is neither live-indexed nor covered by compaction",
                ));
            };

            let legacy = match core.predecessor() {
                FinalizedReceiptPredecessorV1::Genesis => (None, None),
                FinalizedReceiptPredecessorV1::LegacyCutover {
                    legacy_receipt_index,
                    legacy_receipt_hash,
                }
                | FinalizedReceiptPredecessorV1::Core {
                    legacy_receipt_index,
                    legacy_receipt_hash,
                    ..
                } => (Some(legacy_receipt_index), Some(legacy_receipt_hash)),
            };
            if legacy
                != (
                    frame.predecessor_receipt_index,
                    frame.predecessor_receipt_hash,
                )
            {
                return Err(integrity(
                    "semantic core predecessor and exact frame disagree",
                ));
            }
            if let (Some(previous_index), Some(previous_hash)) = legacy {
                if previous_index >= receipt_index {
                    return Err(integrity("semantic predecessor order regressed"));
                }
                let previous_bytes = receipts
                    .get(previous_index)?
                    .ok_or_else(|| integrity("semantic legacy predecessor is missing"))?;
                if decode_receipt(previous_bytes.value())?.receipt_hash() != previous_hash {
                    return Err(integrity("semantic legacy predecessor hash mismatch"));
                }
            }
            match (rebuilt_heads.get(&receipt.agent.0), core.predecessor()) {
                (None, FinalizedReceiptPredecessorV1::Genesis)
                    if receipt.previous_receipt_hash.is_none() => {}
                (None, FinalizedReceiptPredecessorV1::LegacyCutover { .. }) => {}
                (
                    Some(previous),
                    FinalizedReceiptPredecessorV1::Core {
                        core_id: predecessor_id,
                        legacy_receipt_index,
                        legacy_receipt_hash,
                    },
                ) if previous.core_id == predecessor_id
                    && previous.receipt_index == legacy_receipt_index
                    && previous.legacy_receipt_hash == legacy_receipt_hash => {}
                _ => return Err(integrity("semantic per-agent chain is broken")),
            }
            audit_loaded_core(&core, &receipt, &record, faithful, &attested_root)?;
            rebuilt_heads.insert(
                receipt.agent.0,
                DurableFinalizedReceiptCoreHeadV1 {
                    receipt_index,
                    legacy_receipt_hash: receipt.receipt_hash(),
                    core_id,
                },
            );
        }
        if referenced_ids.len() as u64 != cores.len()?
            || referenced_ids.len() as u64 != by_id.len()?
            || rebuilt_heads.len() as u64 != heads.len()?
        {
            return Err(integrity("semantic core/head coverage is incomplete"));
        }
        for (agent, expected) in rebuilt_heads {
            let actual = heads
                .get(&agent)?
                .ok_or_else(|| integrity("rebuilt semantic head is missing"))?;
            if decode_head(actual.value())? != expected {
                return Err(integrity("durable semantic head disagrees with replay"));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(
        ordinal: u64,
        height: u64,
        block_id: [u8; 32],
        receipt: &TurnReceipt,
    ) -> CommitRecord {
        CommitRecord {
            ordinal,
            height,
            block_id,
            block_executed_up_to: height,
            turn_hash: receipt.turn_hash,
            creator: receipt.agent.0,
            receipt_hash: receipt.receipt_hash(),
            ledger_root: [0x55; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn consensus_weld<'a>(
        height: u64,
        block_id: [u8; 32],
        federation: [u8; 32],
        envelope: &'a mut FaithfulNoteRootEnvelopeV1,
        attested: &'a mut StoredAttestedRoot,
    ) -> FinalizedFaithfulRootWeld<'a> {
        let root = crate::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap();
        envelope.record = FaithfulNoteRootRecordV1::new(
            [0x11; 32],
            federation,
            7,
            height - 1,
            height,
            0,
            0,
            root,
            root,
            block_id,
        )
        .unwrap();
        *attested = StoredAttestedRoot {
            merkle_root: [0x55; 32],
            note_tree_root: Some(root.to_bytes()),
            nullifier_set_root: None,
            height,
            timestamp: 1_700_000_000 + height as i64,
            blocklace_block_id: Some(block_id),
            finality_round: Some(100 + height),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId(federation),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };
        FinalizedFaithfulRootWeld {
            initial_anchor: None,
            envelope,
            author_committee: &[],
            author_ml_dsa_committee: &[],
            attested_root: attested,
            spent_nullifiers: &[],
            finalized_spends: &[],
        }
    }

    #[test]
    fn head_codec_rejects_zero_identities() {
        let valid = DurableFinalizedReceiptCoreHeadV1 {
            receipt_index: 9,
            legacy_receipt_hash: [7; 32],
            core_id: FinalizedReceiptIdV1::from_bytes([8; 32]).unwrap(),
        };
        assert_eq!(decode_head(&encode_head(valid)).unwrap(), valid);
        let mut zero_legacy = encode_head(valid);
        zero_legacy[8..40].fill(0);
        assert!(decode_head(&zero_legacy).is_err());
        let mut zero_core = encode_head(valid);
        zero_core[40..72].fill(0);
        assert!(decode_head(&zero_core).is_err());
    }

    #[test]
    fn core_width_is_the_pinned_wire_width() {
        assert_eq!(dregg_turn::FINALIZED_RECEIPT_CORE_V1_LEN, 592);
    }

    #[test]
    fn arbitrary_self_signed_restart_rows_do_not_replace_activation_authority() {
        // The attacker's ML-DSA-65 derivation below goes through `dregg-pq`, which aborts the
        // process with no verified core installed — see
        // `FaithfulNoteRootEnvelopeV1::verify_hybrid`.
        dregg_pq_testkit::install_or_panic();
        let federation = [0x33; 32];
        let block = [0x61; 32];
        let root = crate::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap();
        let record =
            FaithfulNoteRootRecordV1::new([0x11; 32], federation, 7, 0, 1, 0, 0, root, root, block)
                .unwrap();
        let attacker_seed = [0xA1; 32];
        let attacker = dregg_types::SigningKey::from_bytes(&attacker_seed);
        let attacker_public = attacker.public_key();
        let (attacker_pq_public, attacker_pq) =
            dregg_federation::frost::MlDsaSigningKey::from_seed(&attacker_seed);
        let message = record.signing_message();
        let mut envelope = FaithfulNoteRootEnvelopeV1 {
            record,
            hybrid_quorum: vec![dregg_types::HybridQuorumSig {
                pubkey: attacker_public,
                signature: dregg_types::sign(&attacker, &message),
                ml_dsa_pubkey: attacker_pq_public.0.to_vec(),
                pq_signature: attacker_pq.sign(&message).unwrap(),
            }],
        };
        let mut attested = StoredAttestedRoot {
            merkle_root: [0x55; 32],
            note_tree_root: Some(root.to_bytes()),
            nullifier_set_root: None,
            height: 1,
            timestamp: 1_700_000_001,
            blocklace_block_id: Some(block),
            finality_round: Some(101),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId(federation),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };
        attested.quorum_signatures = vec![(
            attacker_public,
            dregg_types::sign(&attacker, &attested.signing_message()),
        )];

        assert!(
            reauthenticate_local_consensus_evidence(attacker_public.0, &envelope, &attested)
                .is_ok(),
            "the actual activation key may reauthenticate its own separate evidence"
        );
        let real_activation = dregg_types::SigningKey::from_bytes(&[0xB2; 32]).public_key();
        assert!(
            reauthenticate_local_consensus_evidence(real_activation.0, &envelope, &attested)
                .is_err(),
            "valid signatures under attacker-selected replacement keys are not authority"
        );

        // Keep the mutable binding load-bearing: a replacement row cannot become acceptable by
        // rewriting the self-carried public key alone because its signatures cease to verify.
        envelope.hybrid_quorum[0].pubkey = real_activation;
        assert!(
            reauthenticate_local_consensus_evidence(real_activation.0, &envelope, &attested)
                .is_err()
        );
    }

    #[test]
    fn durable_head_selects_genesis_then_core_and_refuses_stale_legacy_link() {
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x33; 32];
        let agent = dregg_cell::CellId([0x44; 32]);
        let first_block = [0x61; 32];
        let first = TurnReceipt {
            turn_hash: [0x71; 32],
            forest_hash: [1; 32],
            pre_state_hash: [2; 32],
            post_state_hash: [3; 32],
            effects_hash: [4; 32],
            timestamp: 1_700_000_001,
            finality: dregg_turn::Finality::Final,
            agent,
            federation_id: federation,
            ..Default::default()
        };
        let first_bytes = postcard::to_stdvec(&first).unwrap();
        store.append_receipt_chain_entry(0, &first_bytes).unwrap();
        let first_record = record(0, 1, first_block, &first);
        let mut first_envelope = FaithfulNoteRootEnvelopeV1 {
            record: FaithfulNoteRootRecordV1::new(
                [1; 32],
                federation,
                7,
                0,
                1,
                0,
                0,
                crate::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap(),
                crate::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap(),
                first_block,
            )
            .unwrap(),
            hybrid_quorum: Vec::new(),
        };
        let mut first_attested = StoredAttestedRoot {
            merkle_root: [0; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 0,
            timestamp: 0,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 0,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };
        let first_weld = consensus_weld(
            1,
            first_block,
            federation,
            &mut first_envelope,
            &mut first_attested,
        );
        let write = store.db.begin_write().unwrap();
        let first_id = stage_fresh_finalized_receipt_core_in(
            &write,
            &first_record,
            0,
            None,
            None,
            &first_bytes,
            &first_weld,
        )
        .unwrap();
        write.commit().unwrap();

        let second_block = [0x62; 32];
        let second = TurnReceipt {
            turn_hash: [0x72; 32],
            forest_hash: [5; 32],
            pre_state_hash: [6; 32],
            post_state_hash: [7; 32],
            effects_hash: [8; 32],
            timestamp: 1_700_000_002,
            finality: dregg_turn::Finality::Final,
            agent,
            federation_id: federation,
            previous_receipt_hash: Some(first.receipt_hash()),
            ..Default::default()
        };
        let second_bytes = postcard::to_stdvec(&second).unwrap();
        store.append_receipt_chain_entry(1, &second_bytes).unwrap();
        let second_record = record(1, 2, second_block, &second);
        let mut second_envelope = first_envelope.clone();
        let mut second_attested = first_attested.clone();
        let second_weld = consensus_weld(
            2,
            second_block,
            federation,
            &mut second_envelope,
            &mut second_attested,
        );
        let write = store.db.begin_write().unwrap();
        let second_id = stage_fresh_finalized_receipt_core_in(
            &write,
            &second_record,
            1,
            Some(0),
            Some(first.receipt_hash()),
            &second_bytes,
            &second_weld,
        )
        .unwrap();
        write.commit().unwrap();
        assert_eq!(
            store
                .finalized_receipt_core_v1_by_id(first_id)
                .unwrap()
                .map(|(index, core)| (index, core.id())),
            Some((0, first_id))
        );
        assert_eq!(
            store
                .finalized_receipt_core_v1_by_id(second_id)
                .unwrap()
                .map(|(index, core)| (index, core.id())),
            Some((1, second_id))
        );
        assert!(
            store
                .finalized_receipt_core_v1_by_id(
                    FinalizedReceiptIdV1::from_bytes([0xFE; 32]).unwrap()
                )
                .unwrap()
                .is_none()
        );
        let (_, second_core) = store.finalized_receipt_core_v1(1).unwrap().unwrap();
        assert_eq!(
            second_core.predecessor(),
            FinalizedReceiptPredecessorV1::Core {
                core_id: first_id,
                legacy_receipt_index: 0,
                legacy_receipt_hash: first.receipt_hash(),
            }
        );
        assert_ne!(first_id, second_id);

        let third_block = [0x63; 32];
        let third = TurnReceipt {
            turn_hash: [0x73; 32],
            timestamp: 1_700_000_003,
            finality: dregg_turn::Finality::Final,
            agent,
            federation_id: federation,
            previous_receipt_hash: Some(second.receipt_hash()),
            ..Default::default()
        };
        let third_bytes = postcard::to_stdvec(&third).unwrap();
        store.append_receipt_chain_entry(2, &third_bytes).unwrap();
        let third_record = record(2, 3, third_block, &third);
        let mut third_envelope = second_envelope.clone();
        let mut third_attested = second_attested.clone();
        let third_weld = consensus_weld(
            3,
            third_block,
            federation,
            &mut third_envelope,
            &mut third_attested,
        );
        let write = store.db.begin_write().unwrap();
        assert!(
            stage_fresh_finalized_receipt_core_in(
                &write,
                &third_record,
                2,
                Some(0),
                Some(first.receipt_hash()),
                &third_bytes,
                &third_weld,
            )
            .is_err(),
            "a stale valid legacy receipt link must not replace the durable semantic head"
        );
        write.abort().unwrap();
        assert!(store.finalized_receipt_core_v1(2).unwrap().is_none());

        let write = store.db.begin_write().unwrap();
        {
            let mut by_index = write
                .open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)
                .unwrap();
            by_index.insert(2, &first_id.bytes()).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store.finalized_receipt_core_v1(2).is_err(),
            "a duplicated forward coordinate must disagree with the canonical reverse index"
        );

        let write = store.db.begin_write().unwrap();
        {
            let mut by_index = write
                .open_table(FINALIZED_RECEIPT_CORE_BY_RECEIPT_INDEX_V1)
                .unwrap();
            by_index.remove(2).unwrap();
        }
        {
            let mut cores = write.open_table(FINALIZED_RECEIPT_CORES_V1).unwrap();
            cores.remove(&first_id.bytes()).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store.finalized_receipt_core_v1_by_id(first_id).is_err(),
            "a receipt-indexed id with missing core bytes is corruption, not absence"
        );
    }

    #[test]
    fn first_semantic_core_after_a_legacy_receipt_is_an_explicit_cutover() {
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x33; 32];
        let agent = dregg_cell::CellId([0x45; 32]);
        let legacy = TurnReceipt {
            turn_hash: [0x70; 32],
            timestamp: 1_700_000_000,
            finality: dregg_turn::Finality::Final,
            agent,
            federation_id: federation,
            ..Default::default()
        };
        let legacy_bytes = postcard::to_stdvec(&legacy).unwrap();
        store.append_receipt_chain_entry(0, &legacy_bytes).unwrap();

        let block_id = [0x64; 32];
        let exact = TurnReceipt {
            turn_hash: [0x74; 32],
            timestamp: 1_700_000_001,
            finality: dregg_turn::Finality::Final,
            agent,
            federation_id: federation,
            previous_receipt_hash: Some(legacy.receipt_hash()),
            ..Default::default()
        };
        let exact_bytes = postcard::to_stdvec(&exact).unwrap();
        store.append_receipt_chain_entry(1, &exact_bytes).unwrap();
        let exact_record = record(1, 1, block_id, &exact);
        let mut envelope = FaithfulNoteRootEnvelopeV1 {
            record: FaithfulNoteRootRecordV1::new(
                [1; 32],
                federation,
                7,
                0,
                1,
                0,
                0,
                crate::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap(),
                crate::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap(),
                block_id,
            )
            .unwrap(),
            hybrid_quorum: Vec::new(),
        };
        let mut attested = StoredAttestedRoot {
            merkle_root: [0; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 0,
            timestamp: 0,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 0,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };
        let weld = consensus_weld(1, block_id, federation, &mut envelope, &mut attested);
        let write = store.db.begin_write().unwrap();
        let id = stage_fresh_finalized_receipt_core_in(
            &write,
            &exact_record,
            1,
            Some(0),
            Some(legacy.receipt_hash()),
            &exact_bytes,
            &weld,
        )
        .unwrap();
        write.commit().unwrap();

        let (queried_index, queried_core) =
            store.finalized_receipt_core_v1_by_id(id).unwrap().unwrap();
        assert_eq!(queried_index, 1);
        assert_eq!(queried_core.id(), id);
        assert_eq!(
            queried_core.predecessor(),
            FinalizedReceiptPredecessorV1::LegacyCutover {
                legacy_receipt_index: 0,
                legacy_receipt_hash: legacy.receipt_hash(),
            }
        );

        let write = store.db.begin_write().unwrap();
        let replayed_id = verify_replayed_finalized_receipt_core_in(
            &write,
            &exact_record,
            1,
            Some(0),
            Some(legacy.receipt_hash()),
            &exact_bytes,
            &weld,
        )
        .unwrap();
        write.abort().unwrap();
        assert_eq!(replayed_id, id);
    }
}
