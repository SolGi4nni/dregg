//! Atomic one-shot consumption of a Path of Angels holding capability.
//!
//! The Solana admission service issues a short-lived opaque receipt, but it is
//! not allowed to spend that receipt in an HTTP transaction.  A spend becomes
//! authoritative only here: beside the exact finalized Dregg turn, receipt,
//! and Lean-authored PoA event in the central redb transaction.  The reverse
//! index makes omission and invention on idempotent replay observable.

use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

pub(crate) const POA_HOLDING_CONSUMPTIONS_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("poa_holding_consumptions_v1");
pub(crate) const POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("poa_holding_consumption_by_commit_ordinal_v1");

const WIRE_DOMAIN: &[u8] = b"dregg-poa-holding-consumption-v1\0";
const MAX_WIRE_BYTES: usize = 4096;

/// Finalization input prepared only after the node has matched an active V2
/// capability to the validated SignedTurn signer and signer-derived agent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaHoldingConsumptionV1 {
    capability_receipt_id: [u8; 32],
    player: [u8; 32],
    player_cell: [u8; 32],
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    poa_batch_digest: [u8; 32],
    poa_event_index: u32,
    poa_stream_digest: [u8; 32],
    poa_event_sequence: u64,
    poa_event_digest: [u8; 32],
}

impl PreparedPoaHoldingConsumptionV1 {
    pub fn new(
        capability_receipt_id: [u8; 32],
        player: [u8; 32],
        player_cell: [u8; 32],
        commit_ordinal: u64,
        turn_hash: [u8; 32],
        receipt_hash: [u8; 32],
        poa_batch_digest: [u8; 32],
        poa_event_index: u32,
        poa_stream_digest: [u8; 32],
        poa_event_sequence: u64,
        poa_event_digest: [u8; 32],
    ) -> Result<Self> {
        let prepared = Self {
            capability_receipt_id,
            player,
            player_cell,
            commit_ordinal,
            turn_hash,
            receipt_hash,
            poa_batch_digest,
            poa_event_index,
            poa_stream_digest,
            poa_event_sequence,
            poa_event_digest,
        };
        prepared.validate()?;
        Ok(prepared)
    }

    pub const fn capability_receipt_id(&self) -> [u8; 32] {
        self.capability_receipt_id
    }

    pub const fn player(&self) -> [u8; 32] {
        self.player
    }

    pub const fn player_cell(&self) -> [u8; 32] {
        self.player_cell
    }

    pub(crate) fn matches_poa_event(&self, event: &crate::PreparedPoaEventEnvelopeV1) -> bool {
        self.poa_batch_digest == event.event_digest()
            && self.poa_event_index == 0
            && self.poa_stream_digest == event.stream_digest()
            && self.poa_event_sequence == event.sequence()
            && self.poa_event_digest == event.event_digest()
    }

    pub(crate) fn matches_poa_batch(&self, batch: &crate::PreparedPoaEventBatchV2) -> bool {
        let signer = batch.coordinate().signer();
        let signer_cell =
            dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes());
        if self.poa_batch_digest != batch.batch_digest()
            || self.player != signer
            || self.player_cell != signer_cell.0
        {
            return false;
        }
        let mut matching = batch.events().iter().filter(|event| {
            self.poa_event_index == event.event_index()
                && self.poa_stream_digest == event.stream_digest()
                && self.poa_event_sequence == event.sequence()
                && self.poa_event_digest == event.event_digest()
        });
        matching.next().is_some() && matching.next().is_none()
    }

    fn validate(&self) -> Result<()> {
        if self.capability_receipt_id == [0; 32]
            || self.player == [0; 32]
            || self.player_cell == [0; 32]
            || self.poa_batch_digest == [0; 32]
            || self.poa_stream_digest == [0; 32]
            || self.poa_event_sequence == 0
            || self.poa_event_digest == [0; 32]
        {
            return Err(integrity(
                "PoA holding consumption has a zero capability/player identity",
            ));
        }
        Ok(())
    }
}

/// Exact durable consumer of one otherwise unlinkable holding capability.
/// This record is node-internal and is never part of the public game status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaHoldingConsumptionV1 {
    capability_receipt_id: [u8; 32],
    player: [u8; 32],
    player_cell: [u8; 32],
    commit_ordinal: u64,
    block_id: [u8; 32],
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    poa_batch_digest: [u8; 32],
    poa_event_index: u32,
    poa_stream_digest: [u8; 32],
    poa_event_sequence: u64,
    poa_event_digest: [u8; 32],
}

impl PoaHoldingConsumptionV1 {
    pub const fn capability_receipt_id(&self) -> [u8; 32] {
        self.capability_receipt_id
    }
    pub const fn commit_ordinal(&self) -> u64 {
        self.commit_ordinal
    }
    pub const fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }
    pub const fn receipt_hash(&self) -> [u8; 32] {
        self.receipt_hash
    }

    fn encode(&self) -> Result<Vec<u8>> {
        let payload = postcard::to_stdvec(self)
            .map_err(|error| StoreError::Serialization(error.to_string()))?;
        if payload.len() > MAX_WIRE_BYTES {
            return Err(integrity("PoA holding consumption wire exceeds its bound"));
        }
        let mut wire = payload;
        wire.extend_from_slice(&seal(&wire));
        Ok(wire)
    }

    fn decode(wire: &[u8]) -> Result<Self> {
        if wire.len() < 32 || wire.len() > MAX_WIRE_BYTES + 32 {
            return Err(integrity("PoA holding consumption wire length is invalid"));
        }
        let split = wire.len() - 32;
        let (payload, supplied_seal) = wire.split_at(split);
        if seal(payload).as_slice() != supplied_seal {
            return Err(integrity("PoA holding consumption seal mismatch"));
        }
        let decoded: Self = postcard::from_bytes(payload)
            .map_err(|error| StoreError::Serialization(error.to_string()))?;
        if decoded.capability_receipt_id == [0; 32]
            || decoded.player == [0; 32]
            || decoded.player_cell == [0; 32]
            || decoded.poa_batch_digest == [0; 32]
            || decoded.poa_stream_digest == [0; 32]
            || decoded.poa_event_sequence == 0
            || decoded.poa_event_digest == [0; 32]
        {
            return Err(integrity("PoA holding consumption identity is invalid"));
        }
        Ok(decoded)
    }
}

impl PersistentStore {
    pub fn load_poa_holding_consumption(
        &self,
        capability_receipt_id: &[u8; 32],
    ) -> Result<Option<PoaHoldingConsumptionV1>> {
        let read = self.db.begin_read()?;
        let rows = read.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        let Some(wire) = rows.get(capability_receipt_id)? else {
            return Ok(None);
        };
        let decoded = PoaHoldingConsumptionV1::decode(wire.value())?;
        if decoded.capability_receipt_id != *capability_receipt_id {
            return Err(integrity("PoA holding consumption key/wire mismatch"));
        }
        Ok(Some(decoded))
    }

    pub fn audit_poa_holding_consumptions(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let rows = read.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        let reverse = read.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        let metadata = read.open_table(tables::METADATA)?;
        let compacted = read.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        let compacted_floor = metadata
            .get(tables::META_COMMIT_COMPACTED)?
            .map(|value| value.value())
            .unwrap_or(0);
        let mut row_count = 0_u64;
        for entry in rows.iter()? {
            let (key, wire) = entry.map_err(db_error)?;
            let decoded = PoaHoldingConsumptionV1::decode(wire.value())?;
            if decoded.capability_receipt_id != *key.value() {
                return Err(integrity("PoA holding consumption key/wire mismatch"));
            }
            let reverse_id = reverse
                .get(decoded.commit_ordinal)?
                .ok_or_else(|| integrity("PoA holding consumption omitted reverse index"))?;
            if *reverse_id.value() != decoded.capability_receipt_id {
                return Err(integrity("PoA holding consumption reverse index mismatch"));
            }
            match commits.get(decoded.commit_ordinal)? {
                Some(commit) => {
                    let commit = crate::commit_log::decode_commit_record(commit.value())?;
                    if commit.block_id != decoded.block_id
                        || commit.turn_hash != decoded.turn_hash
                        || commit.receipt_hash != decoded.receipt_hash
                    {
                        return Err(integrity(
                            "PoA holding consumption disagrees with generic commit",
                        ));
                    }
                }
                None if decoded.commit_ordinal < compacted_floor => {
                    if compacted.get(&decoded.block_id)?.is_none() {
                        return Err(integrity(
                            "compacted PoA holding consumption has no block carrier",
                        ));
                    }
                }
                None => {
                    return Err(integrity(
                        "PoA holding consumption has no generic commit carrier",
                    ));
                }
            }
            row_count = row_count
                .checked_add(1)
                .ok_or_else(|| integrity("PoA holding consumption count overflow"))?;
        }
        if reverse.len()? != row_count {
            return Err(integrity(
                "PoA holding consumption reverse index has invention",
            ));
        }
        Ok(())
    }
}

pub(crate) fn initialize_poa_holding_consumption_tables_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
    let _ = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
    Ok(())
}

pub(crate) fn stage_fresh_poa_holding_consumption_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    prepared: &PreparedPoaHoldingConsumptionV1,
) -> Result<()> {
    prepared.validate()?;
    if record.ordinal != commit_ordinal
        || prepared.commit_ordinal != commit_ordinal
        || prepared.turn_hash != record.turn_hash
        || prepared.receipt_hash != record.receipt_hash
    {
        return Err(integrity(
            "PoA holding consumption disagrees with carrying commit coordinates",
        ));
    }
    let stored = plan(record, prepared);
    let wire = stored.encode()?;
    {
        let rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        if rows.get(&prepared.capability_receipt_id)?.is_some() {
            return Err(integrity("PoA holding capability already has a consumer"));
        }
        let reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        if reverse.get(commit_ordinal)?.is_some() {
            return Err(integrity(
                "fresh commit ordinal already consumes a PoA holding capability",
            ));
        }
    }
    let mut rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
    rows.insert(&prepared.capability_receipt_id, wire.as_slice())?;
    let mut reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
    reverse.insert(commit_ordinal, &prepared.capability_receipt_id)?;
    Ok(())
}

pub(crate) fn verify_replayed_poa_holding_consumption_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    prepared: Option<&PreparedPoaHoldingConsumptionV1>,
) -> Result<()> {
    let indexed = {
        let reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        reverse.get(commit_ordinal)?.map(|entry| *entry.value())
    };
    let (Some(prepared), Some(indexed_id)) = (prepared, indexed) else {
        return match (prepared.is_some(), indexed.is_some()) {
            (false, false) => Ok(()),
            _ => Err(integrity(
                "replayed finalized turn omitted or invented its PoA holding consumption weld",
            )),
        };
    };
    if indexed_id != prepared.capability_receipt_id {
        return Err(integrity(
            "replayed PoA holding consumption names a different capability",
        ));
    }
    let stored_wire = {
        let rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        rows.get(&indexed_id)?
            .ok_or_else(|| integrity("PoA holding reverse index points to no row"))?
            .value()
            .to_vec()
    };
    let expected = plan(record, prepared).encode()?;
    if stored_wire != expected {
        return Err(integrity(
            "replayed PoA holding consumption is not byte-identical",
        ));
    }
    Ok(())
}

pub(crate) fn truncate_poa_holding_consumptions_in(
    write: &WriteTransaction,
    new_cursor: u64,
) -> Result<u64> {
    let doomed: Vec<(u64, [u8; 32])> = {
        let reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        reverse
            .range(new_cursor..)?
            .map(|entry| {
                entry
                    .map(|(ordinal, id)| (ordinal.value(), *id.value()))
                    .map_err(db_error)
            })
            .collect::<Result<_>>()?
    };
    let mut rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
    let mut reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
    for (ordinal, id) in &doomed {
        rows.remove(id)?;
        reverse.remove(*ordinal)?;
    }
    u64::try_from(doomed.len()).map_err(|_| integrity("PoA holding rewind count exceeds u64"))
}

fn plan(
    record: &CommitRecord,
    prepared: &PreparedPoaHoldingConsumptionV1,
) -> PoaHoldingConsumptionV1 {
    PoaHoldingConsumptionV1 {
        capability_receipt_id: prepared.capability_receipt_id,
        player: prepared.player,
        player_cell: prepared.player_cell,
        commit_ordinal: prepared.commit_ordinal,
        block_id: record.block_id,
        turn_hash: prepared.turn_hash,
        receipt_hash: prepared.receipt_hash,
        poa_batch_digest: prepared.poa_batch_digest,
        poa_event_index: prepared.poa_event_index,
        poa_stream_digest: prepared.poa_stream_digest,
        poa_event_sequence: prepared.poa_event_sequence,
        poa_event_digest: prepared.poa_event_digest,
    }
}

fn seal(payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(WIRE_DOMAIN);
    hasher.update(payload);
    hasher.finalize().into()
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

fn db_error(error: redb::StorageError) -> StoreError {
    StoreError::Database(error.to_string())
}
