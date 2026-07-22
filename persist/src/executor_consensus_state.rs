//! Durable consensus/admission state owned by short-lived `TurnExecutor`s.
//!
//! The ledger is not the executor's complete transition state. Note-create
//! commitments, revocations, inbound bridge nullifiers, and rate-limit counters
//! all affect later admission or committed roots. This module gives the first
//! three typed, lossless durable tables and exposes an opaque same-transaction
//! hook for the node's versioned rate-limit snapshot codec.

use std::collections::HashSet;

use redb::{ReadableTable, ReadableTableMetadata, WriteTransaction};

use crate::{PersistentStore, Result, StoreError, tables};

pub const MAX_EXECUTOR_ACCUMULATOR_RECORDS: u64 = 1_000_000;
pub const MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecutorNoteCommitmentRecord {
    pub commitment: [u8; 32],
    pub value: u64,
    pub seq: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecutorRevocationRecord {
    pub key: [u8; 32],
    pub height: u64,
    pub seq: u64,
}

/// Complete post-execution accumulator image. Record vectors are in append
/// order; bridged nullifiers are in strict key order.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecutorAccumulatorSnapshot {
    pub note_commitments: Vec<ExecutorNoteCommitmentRecord>,
    pub revocations: Vec<ExecutorRevocationRecord>,
    pub bridged_nullifiers: Vec<[u8; 32]>,
}

/// The executor-owned consensus state welded to one finalized commit.
///
/// `rate_limit_snapshot = None` means carry the preceding durable snapshot
/// forward (and means canonical empty at ordinal zero). It never means reset.
/// `Some(bytes)` replaces the snapshot at this commit ordinal; bytes are the
/// node's strictly decoded/re-encoded canonical rate-state envelope.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FinalizedExecutorConsensusState {
    pub accumulators: ExecutorAccumulatorSnapshot,
    pub rate_limit_snapshot: Option<Vec<u8>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AccumulatorFrontier {
    notes: u64,
    revocations: u64,
    bridged: u64,
}

impl ExecutorAccumulatorSnapshot {
    pub fn validate_canonical(&self) -> Result<()> {
        for (kind, len) in [
            ("note-commitment", self.note_commitments.len()),
            ("revocation", self.revocations.len()),
            ("bridged-nullifier", self.bridged_nullifiers.len()),
        ] {
            if u64::try_from(len).unwrap_or(u64::MAX) > MAX_EXECUTOR_ACCUMULATOR_RECORDS {
                return Err(StoreError::Integrity(format!(
                    "{kind} snapshot exceeds the durable record bound"
                )));
            }
        }
        let mut note_keys = HashSet::with_capacity(self.note_commitments.len());
        for (index, record) in self.note_commitments.iter().enumerate() {
            let expected = u64::try_from(index).map_err(|_| {
                StoreError::Integrity("note-commitment sequence does not fit u64".to_string())
            })?;
            if record.seq != expected || !note_keys.insert(record.commitment) {
                return Err(StoreError::Integrity(
                    "note-commitment snapshot is not a dense unique append sequence".to_string(),
                ));
            }
        }

        let mut revocation_keys = HashSet::with_capacity(self.revocations.len());
        for (index, record) in self.revocations.iter().enumerate() {
            let expected = u64::try_from(index).map_err(|_| {
                StoreError::Integrity("revocation sequence does not fit u64".to_string())
            })?;
            if record.seq != expected || !revocation_keys.insert(record.key) {
                return Err(StoreError::Integrity(
                    "revocation snapshot is not a dense unique append sequence".to_string(),
                ));
            }
        }

        if self
            .bridged_nullifiers
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(StoreError::Integrity(
                "bridged-nullifier snapshot is not strictly sorted and unique".to_string(),
            ));
        }
        Ok(())
    }

    fn frontier(&self) -> Result<AccumulatorFrontier> {
        Ok(AccumulatorFrontier {
            notes: u64::try_from(self.note_commitments.len()).map_err(|_| {
                StoreError::Integrity("note-commitment count does not fit u64".to_string())
            })?,
            revocations: u64::try_from(self.revocations.len()).map_err(|_| {
                StoreError::Integrity("revocation count does not fit u64".to_string())
            })?,
            bridged: u64::try_from(self.bridged_nullifiers.len()).map_err(|_| {
                StoreError::Integrity("bridged-nullifier count does not fit u64".to_string())
            })?,
        })
    }
}

fn encode_value_seq(value: u64, seq: u64) -> [u8; 16] {
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&value.to_le_bytes());
    out[8..].copy_from_slice(&seq.to_le_bytes());
    out
}

fn decode_value_seq(bytes: &[u8; 16]) -> (u64, u64) {
    let mut value = [0u8; 8];
    value.copy_from_slice(&bytes[..8]);
    let mut seq = [0u8; 8];
    seq.copy_from_slice(&bytes[8..]);
    (u64::from_le_bytes(value), u64::from_le_bytes(seq))
}

fn encode_frontier(frontier: AccumulatorFrontier) -> [u8; 24] {
    let mut out = [0u8; 24];
    out[..8].copy_from_slice(&frontier.notes.to_le_bytes());
    out[8..16].copy_from_slice(&frontier.revocations.to_le_bytes());
    out[16..].copy_from_slice(&frontier.bridged.to_le_bytes());
    out
}

fn decode_frontier(bytes: &[u8; 24]) -> AccumulatorFrontier {
    let mut notes = [0u8; 8];
    notes.copy_from_slice(&bytes[..8]);
    let mut revocations = [0u8; 8];
    revocations.copy_from_slice(&bytes[8..16]);
    let mut bridged = [0u8; 8];
    bridged.copy_from_slice(&bytes[16..]);
    AccumulatorFrontier {
        notes: u64::from_le_bytes(notes),
        revocations: u64::from_le_bytes(revocations),
        bridged: u64::from_le_bytes(bridged),
    }
}

fn checked_capacity(count: u64, kind: &str) -> Result<usize> {
    if count > MAX_EXECUTOR_ACCUMULATOR_RECORDS {
        return Err(StoreError::Integrity(format!(
            "{kind} count {count} exceeds durable bound {MAX_EXECUTOR_ACCUMULATOR_RECORDS}"
        )));
    }
    usize::try_from(count)
        .map_err(|_| StoreError::Integrity(format!("{kind} count does not fit usize")))
}

fn load_accumulators_from_write(
    write_txn: &WriteTransaction,
    expected_note_count: u64,
) -> Result<ExecutorAccumulatorSnapshot> {
    let positional = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
    let notes = write_txn.open_table(tables::NOTE_COMMITMENT_RECORDS_V1)?;
    if positional.len()? != expected_note_count || notes.len()? != expected_note_count {
        return Err(StoreError::Integrity(format!(
            "positional note/faithful-record counts disagree ({}, {}, expected {expected_note_count}); legacy nonempty images require an explicit value/sequence migration",
            positional.len()?,
            notes.len()?
        )));
    }

    let mut note_records = Vec::with_capacity(checked_capacity(expected_note_count, "note")?);
    let mut seen_note_seq = vec![false; note_records.capacity()];
    for entry in notes.iter()? {
        let (key, bytes) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        let commitment = *key.value();
        let (value, seq) = decode_value_seq(bytes.value());
        let index = checked_capacity(seq, "note sequence")?;
        if index >= seen_note_seq.len() || seen_note_seq[index] {
            return Err(StoreError::Integrity(
                "note-commitment sequence is duplicated or outside the dense durable range"
                    .to_string(),
            ));
        }
        let Some(positional_commitment) = positional.get(seq)? else {
            return Err(StoreError::Integrity(
                "note-commitment record has no positional leaf".to_string(),
            ));
        };
        if positional_commitment.value() != &commitment {
            return Err(StoreError::Integrity(
                "note-commitment record disagrees with positional leaf".to_string(),
            ));
        }
        seen_note_seq[index] = true;
        note_records.push(ExecutorNoteCommitmentRecord {
            commitment,
            value,
            seq,
        });
    }
    if seen_note_seq.iter().any(|seen| !seen) {
        return Err(StoreError::Integrity(
            "note-commitment sequence has a durable gap".to_string(),
        ));
    }
    note_records.sort_by_key(|record| (record.seq, record.commitment));

    let revocations = write_txn.open_table(tables::REVOCATION_RECORDS_V1)?;
    let revocation_count = revocations.len()?;
    let mut revocation_records =
        Vec::with_capacity(checked_capacity(revocation_count, "revocation")?);
    let mut seen_revocation_seq = vec![false; revocation_records.capacity()];
    for entry in revocations.iter()? {
        let (key, bytes) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        let (height, seq) = decode_value_seq(bytes.value());
        let index = checked_capacity(seq, "revocation sequence")?;
        if index >= seen_revocation_seq.len() || seen_revocation_seq[index] {
            return Err(StoreError::Integrity(
                "revocation sequence is duplicated or outside the dense durable range".to_string(),
            ));
        }
        seen_revocation_seq[index] = true;
        revocation_records.push(ExecutorRevocationRecord {
            key: *key.value(),
            height,
            seq,
        });
    }
    if seen_revocation_seq.iter().any(|seen| !seen) {
        return Err(StoreError::Integrity(
            "revocation sequence has a durable gap".to_string(),
        ));
    }
    revocation_records.sort_by_key(|record| (record.seq, record.key));

    let bridges = write_txn.open_table(tables::BRIDGED_NULLIFIERS_V1)?;
    let mut bridged_nullifiers = Vec::with_capacity(checked_capacity(bridges.len()?, "bridge")?);
    for entry in bridges.iter()? {
        let (key, _) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        bridged_nullifiers.push(*key.value());
    }
    bridged_nullifiers.sort_unstable();

    let snapshot = ExecutorAccumulatorSnapshot {
        note_commitments: note_records,
        revocations: revocation_records,
        bridged_nullifiers,
    };
    snapshot.validate_canonical()?;
    Ok(snapshot)
}

fn prefix_agrees<T: PartialEq>(durable: &[T], submitted: &[T]) -> bool {
    submitted.get(..durable.len()) == Some(durable)
}

fn stage_rate_snapshot_in(
    write_txn: &WriteTransaction,
    ordinal: u64,
    snapshot: Option<&[u8]>,
    fresh: bool,
) -> Result<()> {
    if snapshot.is_some_and(|bytes| bytes.len() > MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES) {
        return Err(StoreError::Integrity(format!(
            "executor rate snapshot exceeds {} bytes",
            MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES
        )));
    }
    let mut table = write_txn.open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)?;
    let existing = table.get(ordinal)?.map(|guard| guard.value().to_vec());
    match (fresh, snapshot, existing.as_deref()) {
        (true, Some(bytes), None) => {
            table.insert(ordinal, bytes)?;
        }
        (true, None, None) => {}
        (true, _, Some(_)) => {
            return Err(StoreError::Integrity(
                "fresh executor rate snapshot ordinal already exists".to_string(),
            ));
        }
        (false, Some(bytes), Some(existing)) if existing == bytes => {}
        (false, None, None) => {}
        (false, _, _) => {
            return Err(StoreError::Integrity(
                "replayed executor rate snapshot differs from durable ordinal".to_string(),
            ));
        }
    }
    Ok(())
}

/// Validate and stage a complete post-execution image. Returns the new durable
/// positional note count for the caller to publish in `METADATA`.
pub(crate) fn stage_fresh_executor_consensus_state_in(
    write_txn: &WriteTransaction,
    ordinal: u64,
    durable_note_count: u64,
    note_commitments: &[[u8; 32]],
    state: &FinalizedExecutorConsensusState,
) -> Result<u64> {
    state.accumulators.validate_canonical()?;
    let durable = load_accumulators_from_write(write_txn, durable_note_count)?;
    if !prefix_agrees(
        &durable.note_commitments,
        &state.accumulators.note_commitments,
    ) || !prefix_agrees(&durable.revocations, &state.accumulators.revocations)
        || durable.bridged_nullifiers.iter().any(|key| {
            state
                .accumulators
                .bridged_nullifiers
                .binary_search(key)
                .is_err()
        })
    {
        return Err(StoreError::Integrity(
            "submitted executor accumulator image is not an extension of durable state".to_string(),
        ));
    }

    let fresh_notes = &state.accumulators.note_commitments[durable.note_commitments.len()..];
    if fresh_notes.len() != note_commitments.len()
        || fresh_notes
            .iter()
            .zip(note_commitments)
            .any(|(record, expected)| &record.commitment != expected)
    {
        return Err(StoreError::Integrity(
            "executor commitment suffix does not equal finalized NoteCreate leaf order".to_string(),
        ));
    }

    {
        let mut positional = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
        let mut records = write_txn.open_table(tables::NOTE_COMMITMENT_RECORDS_V1)?;
        for record in fresh_notes {
            if positional.get(record.seq)?.is_some() || records.get(&record.commitment)?.is_some() {
                return Err(StoreError::Integrity(
                    "fresh note-commitment suffix collides with durable state".to_string(),
                ));
            }
            positional.insert(record.seq, &record.commitment)?;
            let encoded = encode_value_seq(record.value, record.seq);
            records.insert(&record.commitment, &encoded)?;
        }
    }

    {
        let mut records = write_txn.open_table(tables::REVOCATION_RECORDS_V1)?;
        for record in &state.accumulators.revocations[durable.revocations.len()..] {
            if records.get(&record.key)?.is_some() {
                return Err(StoreError::Integrity(
                    "fresh revocation suffix collides with durable state".to_string(),
                ));
            }
            let encoded = encode_value_seq(record.height, record.seq);
            records.insert(&record.key, &encoded)?;
        }
    }

    {
        let mut bridges = write_txn.open_table(tables::BRIDGED_NULLIFIERS_V1)?;
        for key in &state.accumulators.bridged_nullifiers {
            if durable.bridged_nullifiers.binary_search(key).is_err() {
                bridges.insert(key, ordinal)?;
            }
        }
    }

    let frontier = state.accumulators.frontier()?;
    {
        let mut frontiers = write_txn.open_table(tables::EXECUTOR_ACCUMULATOR_FRONTIERS_V1)?;
        if frontiers.get(ordinal)?.is_some() {
            return Err(StoreError::Integrity(
                "fresh executor accumulator frontier already exists".to_string(),
            ));
        }
        let encoded = encode_frontier(frontier);
        frontiers.insert(ordinal, &encoded)?;
    }
    stage_rate_snapshot_in(
        write_txn,
        ordinal,
        state.rate_limit_snapshot.as_deref(),
        true,
    )?;
    Ok(frontier.notes)
}

pub(crate) fn verify_replayed_executor_consensus_state_in(
    write_txn: &WriteTransaction,
    ordinal: u64,
    durable_note_count: u64,
    note_commitments: &[[u8; 32]],
    state: &FinalizedExecutorConsensusState,
) -> Result<()> {
    state.accumulators.validate_canonical()?;
    let frontiers = write_txn.open_table(tables::EXECUTOR_ACCUMULATOR_FRONTIERS_V1)?;
    let Some(frontier) = frontiers.get(ordinal)? else {
        return Err(StoreError::Integrity(
            "replayed finalized turn has no executor accumulator frontier".to_string(),
        ));
    };
    let frontier = decode_frontier(frontier.value());
    if frontier != state.accumulators.frontier()? {
        return Err(StoreError::Integrity(
            "replayed executor accumulator frontier differs from durable ordinal".to_string(),
        ));
    }

    let durable = load_accumulators_from_write(write_txn, durable_note_count)?;
    if durable.note_commitments.get(..frontier.notes as usize)
        != Some(state.accumulators.note_commitments.as_slice())
        || durable.revocations.get(..frontier.revocations as usize)
            != Some(state.accumulators.revocations.as_slice())
    {
        return Err(StoreError::Integrity(
            "replayed executor accumulator records differ from durable history".to_string(),
        ));
    }
    let bridges = write_txn.open_table(tables::BRIDGED_NULLIFIERS_V1)?;
    let mut at_ordinal = Vec::new();
    for entry in bridges.iter()? {
        let (key, inserted_at) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        if inserted_at.value() <= ordinal {
            at_ordinal.push(*key.value());
        }
    }
    at_ordinal.sort_unstable();
    if at_ordinal != state.accumulators.bridged_nullifiers {
        return Err(StoreError::Integrity(
            "replayed bridged-nullifier gate differs from durable history".to_string(),
        ));
    }
    let note_start = state
        .accumulators
        .note_commitments
        .len()
        .checked_sub(note_commitments.len())
        .ok_or_else(|| {
            StoreError::Integrity(
                "replayed NoteCreate suffix is longer than accumulator frontier".to_string(),
            )
        })?;
    if state.accumulators.note_commitments[note_start..]
        .iter()
        .map(|record| record.commitment)
        .ne(note_commitments.iter().copied())
    {
        return Err(StoreError::Integrity(
            "replayed executor commitment suffix differs from finalized NoteCreate order"
                .to_string(),
        ));
    }
    stage_rate_snapshot_in(
        write_txn,
        ordinal,
        state.rate_limit_snapshot.as_deref(),
        false,
    )
}

/// Regress every executor-side table to the last surviving commit frontier.
/// This runs inside the commit-log recovery writer, so the log/cursor and all
/// admission state move back together or not at all.
pub(crate) fn truncate_executor_consensus_state_in(
    write_txn: &WriteTransaction,
    new_cursor: u64,
) -> Result<()> {
    let (target, tracked_tail_exists) = {
        let frontiers = write_txn.open_table(tables::EXECUTOR_ACCUMULATOR_FRONTIERS_V1)?;
        let mut target = None;
        if new_cursor > 0 {
            for entry in frontiers.range(0..new_cursor)? {
                let (_, bytes) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
                target = Some(decode_frontier(bytes.value()));
            }
        }
        let mut tracked_tail_exists = false;
        for entry in frontiers.range(new_cursor..)? {
            entry.map_err(|error| StoreError::Database(error.to_string()))?;
            tracked_tail_exists = true;
            break;
        }
        (target, tracked_tail_exists)
    };

    // Sparse rate replacements are ordinal-owned even when no accumulator
    // frontier was present (future/legacy callers may carry only the rate hook).
    {
        let mut rates = write_txn.open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)?;
        let doomed: Vec<u64> = rates
            .range(new_cursor..)?
            .map(|entry| {
                entry
                    .map(|(ordinal, _)| ordinal.value())
                    .map_err(|error| StoreError::Database(error.to_string()))
            })
            .collect::<Result<_>>()?;
        for ordinal in doomed {
            rates.remove(ordinal)?;
        }
    }

    if !tracked_tail_exists {
        return Ok(());
    }
    let target = target.unwrap_or(AccumulatorFrontier {
        notes: 0,
        revocations: 0,
        bridged: 0,
    });
    if target.notes > MAX_EXECUTOR_ACCUMULATOR_RECORDS
        || target.revocations > MAX_EXECUTOR_ACCUMULATOR_RECORDS
        || target.bridged > MAX_EXECUTOR_ACCUMULATOR_RECORDS
    {
        return Err(StoreError::Integrity(
            "surviving executor accumulator frontier exceeds durable bounds".to_string(),
        ));
    }

    {
        let mut records = write_txn.open_table(tables::NOTE_COMMITMENT_RECORDS_V1)?;
        let doomed: Vec<[u8; 32]> = records
            .iter()?
            .filter_map(|entry| match entry {
                Ok((key, value)) => {
                    let (_, seq) = decode_value_seq(value.value());
                    (seq >= target.notes).then_some(Ok(*key.value()))
                }
                Err(error) => Some(Err(StoreError::Database(error.to_string()))),
            })
            .collect::<Result<_>>()?;
        for key in doomed {
            records.remove(&key)?;
        }
    }
    {
        let mut positional = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
        let doomed: Vec<u64> = positional
            .range(target.notes..)?
            .map(|entry| {
                entry
                    .map(|(seq, _)| seq.value())
                    .map_err(|error| StoreError::Database(error.to_string()))
            })
            .collect::<Result<_>>()?;
        for seq in doomed {
            positional.remove(seq)?;
        }
    }
    {
        let mut records = write_txn.open_table(tables::REVOCATION_RECORDS_V1)?;
        let doomed: Vec<[u8; 32]> = records
            .iter()?
            .filter_map(|entry| match entry {
                Ok((key, value)) => {
                    let (_, seq) = decode_value_seq(value.value());
                    (seq >= target.revocations).then_some(Ok(*key.value()))
                }
                Err(error) => Some(Err(StoreError::Database(error.to_string()))),
            })
            .collect::<Result<_>>()?;
        for key in doomed {
            records.remove(&key)?;
        }
    }
    {
        let mut bridges = write_txn.open_table(tables::BRIDGED_NULLIFIERS_V1)?;
        let doomed: Vec<[u8; 32]> = bridges
            .iter()?
            .filter_map(|entry| match entry {
                Ok((key, ordinal)) => (ordinal.value() >= new_cursor).then_some(Ok(*key.value())),
                Err(error) => Some(Err(StoreError::Database(error.to_string()))),
            })
            .collect::<Result<_>>()?;
        for key in doomed {
            bridges.remove(&key)?;
        }
        if bridges.len()? != target.bridged {
            return Err(StoreError::Integrity(
                "bridged-nullifier rollback does not match surviving frontier".to_string(),
            ));
        }
    }
    {
        let mut frontiers = write_txn.open_table(tables::EXECUTOR_ACCUMULATOR_FRONTIERS_V1)?;
        let doomed: Vec<u64> = frontiers
            .range(new_cursor..)?
            .map(|entry| {
                entry
                    .map(|(ordinal, _)| ordinal.value())
                    .map_err(|error| StoreError::Database(error.to_string()))
            })
            .collect::<Result<_>>()?;
        for ordinal in doomed {
            frontiers.remove(ordinal)?;
        }
    }
    {
        let mut meta = write_txn.open_table(tables::METADATA)?;
        meta.insert(tables::META_NOTE_TREE_SIZE, target.notes)?;
    }
    {
        let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
        meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
        meta_bytes.remove(tables::META_POSEIDON2_NOTE_TREE_ROOT_CACHE)?;
    }
    Ok(())
}

impl PersistentStore {
    /// Load the complete strict executor accumulator image. A legacy nonempty
    /// positional note table without value/sequence records is an integrity
    /// failure, never an empty/default reconstruction.
    pub fn load_executor_accumulator_snapshot(&self) -> Result<ExecutorAccumulatorSnapshot> {
        let note_count = self.note_count()?;
        let write_txn = self.db.begin_write()?;
        let snapshot = load_accumulators_from_write(&write_txn, note_count)?;
        // Read-only use of a writer lets this path share one validation routine.
        // Dropping without commit performs no mutation.
        drop(write_txn);
        Ok(snapshot)
    }

    /// Latest sparse rate snapshot at or before `commit_cursor - 1`.
    /// `None` is the canonical empty state (no replacement has ever landed).
    pub fn load_latest_rate_limit_snapshot_bytes(&self) -> Result<Option<Vec<u8>>> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(None);
        }
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)?;
        let mut latest = None;
        for entry in table.range(0..cursor)? {
            let (ordinal, bytes) =
                entry.map_err(|error| StoreError::Database(error.to_string()))?;
            latest = Some((ordinal.value(), bytes.value().to_vec()));
        }
        Ok(latest.map(|(_, bytes)| bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commit_log::CommitRecord;
    use dregg_cell::commitment_set::CommitmentSet;
    use dregg_cell::note::NoteCommitment;
    use dregg_cell::revoked_set::RevokedSet;

    fn record(tag: u8, ledger_root: [u8; 32]) -> CommitRecord {
        CommitRecord {
            ordinal: 0,
            height: u64::from(tag) + 1,
            block_id: [tag.wrapping_add(10); 32],
            block_executed_up_to: u64::from(tag) + 1,
            turn_hash: [tag.wrapping_add(20); 32],
            creator: [tag.wrapping_add(30); 32],
            receipt_hash: [tag.wrapping_add(40); 32],
            ledger_root,
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn state_one(rate: Option<&[u8]>) -> FinalizedExecutorConsensusState {
        FinalizedExecutorConsensusState {
            accumulators: ExecutorAccumulatorSnapshot {
                note_commitments: vec![ExecutorNoteCommitmentRecord {
                    commitment: [1; 32],
                    value: 91,
                    seq: 0,
                }],
                revocations: vec![ExecutorRevocationRecord {
                    key: [2; 32],
                    height: 7,
                    seq: 0,
                }],
                bridged_nullifiers: vec![[3; 32]],
            },
            rate_limit_snapshot: rate.map(|bytes| bytes.to_vec()),
        }
    }

    fn state_two(rate: Option<&[u8]>) -> FinalizedExecutorConsensusState {
        let mut state = state_one(rate);
        state
            .accumulators
            .note_commitments
            .push(ExecutorNoteCommitmentRecord {
                commitment: [4; 32],
                value: 92,
                seq: 1,
            });
        state
            .accumulators
            .revocations
            .push(ExecutorRevocationRecord {
                key: [5; 32],
                height: 8,
                seq: 1,
            });
        state.accumulators.bridged_nullifiers.push([6; 32]);
        state
    }

    #[test]
    fn restart_roundtrip_reconstructs_values_sequences_roots_and_duplicate_gates() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("executor-side-state.redb");
        let state = state_one(Some(b"canonical-rate-v1"));
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        {
            let store = PersistentStore::open(&path).unwrap();
            store
                .commit_finalized_turn_with_executor_state(
                    0,
                    &record(0, empty_root),
                    &[[1; 32]],
                    &state,
                )
                .unwrap();
        }

        let store = PersistentStore::open(&path).unwrap();
        let restored = store.load_executor_accumulator_snapshot().unwrap();
        assert_eq!(restored, state.accumulators);
        assert_eq!(
            store.load_latest_rate_limit_snapshot_bytes().unwrap(),
            Some(b"canonical-rate-v1".to_vec())
        );

        let mut commitments = CommitmentSet::from_records(
            restored
                .note_commitments
                .iter()
                .map(|record| (record.commitment, record.value, record.seq)),
        )
        .unwrap();
        assert!(commitments.insert(NoteCommitment([1; 32]), 91).is_err());
        commitments.insert(NoteCommitment([9; 32]), 99).unwrap();
        assert_eq!(commitments.seq_of(&NoteCommitment([9; 32])), Some(1));

        let mut revoked = RevokedSet::from_records(
            restored
                .revocations
                .iter()
                .map(|record| (record.key, record.height, record.seq)),
        )
        .unwrap();
        assert!(revoked.insert([2; 32], 7).is_err());
        revoked.insert([8; 32], 9).unwrap();
        assert_eq!(revoked.seq_of(&[8; 32]), Some(1));

        assert_eq!(restored.bridged_nullifiers, vec![[3; 32]]);
    }

    #[test]
    fn late_atomic_failure_leaves_accumulators_and_cursor_untouched() {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("atomic-abort.redb")).unwrap();
        {
            let write = store.db.begin_write().unwrap();
            {
                let mut rates = write
                    .open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)
                    .unwrap();
                rates.insert(0, b"preexisting".as_slice()).unwrap();
            }
            write.commit().unwrap();
        }
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let error = store.commit_finalized_turn_with_executor_state(
            0,
            &record(0, empty_root),
            &[[1; 32]],
            &state_one(Some(b"conflict")),
        );
        assert!(error.is_err());
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert_eq!(store.note_count().unwrap(), 0);
        assert_eq!(
            store.load_executor_accumulator_snapshot().unwrap(),
            ExecutorAccumulatorSnapshot::default()
        );
        let read = store.db.begin_read().unwrap();
        let rates = read
            .open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)
            .unwrap();
        assert_eq!(rates.get(0).unwrap().unwrap().value(), b"preexisting");
    }

    #[test]
    fn replay_requires_exact_accumulator_and_rate_some_none_shape() {
        let dir = tempfile::tempdir().unwrap();
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let record = record(0, empty_root);

        let store = PersistentStore::open(&dir.path().join("replay-some.redb")).unwrap();
        let state = state_one(Some(b"rate-a"));
        store
            .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &state)
            .unwrap();
        assert!(
            !store
                .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &state)
                .unwrap()
                .freshly_committed
        );
        let mut wrong_rate = state.clone();
        wrong_rate.rate_limit_snapshot = Some(b"rate-b".to_vec());
        assert!(
            store
                .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &wrong_rate)
                .is_err()
        );
        let mut omitted = state.clone();
        omitted.rate_limit_snapshot = None;
        assert!(
            store
                .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &omitted)
                .is_err()
        );

        let store = PersistentStore::open(&dir.path().join("replay-none.redb")).unwrap();
        let state = state_one(None);
        store
            .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &state)
            .unwrap();
        assert!(
            store
                .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &state)
                .is_ok()
        );
    }

    #[test]
    fn noncanonical_and_legacy_incomplete_images_fail_closed() {
        let mut gap = state_one(None);
        gap.accumulators.note_commitments[0].seq = 1;
        assert!(gap.accumulators.validate_canonical().is_err());
        let mut duplicate_bridge = state_one(None);
        duplicate_bridge
            .accumulators
            .bridged_nullifiers
            .push([3; 32]);
        assert!(duplicate_bridge.accumulators.validate_canonical().is_err());

        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("legacy.redb")).unwrap();
        store
            .store_note_commitment(&NoteCommitment([7; 32]))
            .unwrap();
        let error = store.load_executor_accumulator_snapshot().unwrap_err();
        assert!(
            error
                .to_string()
                .contains("explicit value/sequence migration"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn divergent_tail_rollback_restores_every_executor_frontier() {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("rollback.redb")).unwrap();
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let first = state_one(Some(b"rate-one"));
        let second = state_two(Some(b"rate-two"));
        store
            .commit_finalized_turn_with_executor_state(
                0,
                &record(0, empty_root),
                &[[1; 32]],
                &first,
            )
            .unwrap();
        store
            .commit_finalized_turn_with_executor_state(
                1,
                &record(1, [0xff; 32]),
                &[[4; 32]],
                &second,
            )
            .unwrap();

        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.note_count().unwrap(), 1);
        assert_eq!(
            store.load_executor_accumulator_snapshot().unwrap(),
            first.accumulators
        );
        assert_eq!(
            store.load_latest_rate_limit_snapshot_bytes().unwrap(),
            Some(b"rate-one".to_vec())
        );
    }
}
