//! Durable consensus/admission state owned by short-lived `TurnExecutor`s.
//!
//! The ledger is not the executor's complete transition state. Note-create
//! commitments, revocations, inbound bridge nullifiers, and rate-limit counters
//! all affect later admission or committed roots. This module gives the first
//! three typed, lossless durable tables and exposes an opaque same-transaction
//! hook for the node's versioned rate-limit snapshot codec.

use std::collections::HashSet;

use dregg_cell::factory::FactoryRegistrySnapshot;
use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};

use crate::{PersistentStore, Result, StoreError, tables};

pub const MAX_EXECUTOR_ACCUMULATOR_RECORDS: u64 = 1_000_000;
pub const MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_REACTIVE_REGISTRY_BYTES: usize = 64 * 1024 * 1024;
pub const REACTIVE_NULLIFIER_DOMAIN_V1: &str = "dregg-reactive-nullifiers-v1";
pub const REACTIVE_REGISTRY_DOMAIN_V1: &str = "dregg-pending-registry-v1";
pub const EMPTY_REACTIVE_REGISTRY_V1: &[u8; 6] = b"DPRG1\0";

/// Compare-and-swap candidate for the durable pending-turn registry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReactiveRegistryCasV1 {
    pub expected_pre_commitment: [u8; 32],
    pub successor_bytes: Vec<u8>,
}

impl ReactiveRegistryCasV1 {
    pub fn new(expected_pre_commitment: [u8; 32], successor_bytes: Vec<u8>) -> Self {
        Self {
            expected_pre_commitment,
            successor_bytes,
        }
    }
}

impl Default for ReactiveRegistryCasV1 {
    fn default() -> Self {
        Self {
            expected_pre_commitment: reactive_registry_commitment(EMPTY_REACTIVE_REGISTRY_V1),
            successor_bytes: EMPTY_REACTIVE_REGISTRY_V1.to_vec(),
        }
    }
}

/// Compare-and-swap candidate for the React-only replay gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReactiveNullifierCasV1 {
    pub expected_pre_commitment: [u8; 32],
    /// Strictly sorted and duplicate-free successor image.
    pub successor_keys: Vec<[u8; 32]>,
}

impl ReactiveNullifierCasV1 {
    pub fn new(expected_pre_commitment: [u8; 32], successor_keys: Vec<[u8; 32]>) -> Self {
        Self {
            expected_pre_commitment,
            successor_keys,
        }
    }
}

impl Default for ReactiveNullifierCasV1 {
    fn default() -> Self {
        Self {
            expected_pre_commitment: reactive_nullifier_commitment(&[]),
            successor_keys: Vec::new(),
        }
    }
}

pub fn reactive_registry_commitment(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(REACTIVE_REGISTRY_DOMAIN_V1);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

pub fn reactive_nullifier_commitment(keys: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(REACTIVE_NULLIFIER_DOMAIN_V1);
    hasher.update(&(keys.len() as u64).to_le_bytes());
    for key in keys {
        hasher.update(key);
    }
    *hasher.finalize().as_bytes()
}

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
///
/// `factory_registry_snapshot` has the same sparse replacement semantics, but
/// is decoded and canonicalized again at this persistence boundary. The two
/// optional byte images share one hard size envelope.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FinalizedExecutorConsensusState {
    pub accumulators: ExecutorAccumulatorSnapshot,
    pub rate_limit_snapshot: Option<Vec<u8>>,
    pub factory_registry_snapshot: Option<Vec<u8>>,
    pub reactive_registry: ReactiveRegistryCasV1,
    pub reactive_nullifiers: ReactiveNullifierCasV1,
    /// Typed observer outcomes produced while resolving the carrying receipt.
    /// These rows are not execution authority, but they must share the source
    /// commit's transaction or a crash can erase a game-visible resolution.
    pub promise_resolutions: Vec<crate::PromiseResolutionCandidateV1>,
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

fn latest_sparse_snapshot_before(
    write_txn: &WriteTransaction,
    table_definition: TableDefinition<u64, &[u8]>,
    ordinal: u64,
) -> Result<Option<Vec<u8>>> {
    let table = write_txn.open_table(table_definition)?;
    let mut latest = None;
    for entry in table.range(0..ordinal)? {
        let (_, bytes) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        latest = Some(bytes.value().to_vec());
    }
    Ok(latest)
}

fn validate_sparse_snapshot_envelope(
    write_txn: &WriteTransaction,
    ordinal: u64,
    state: &FinalizedExecutorConsensusState,
) -> Result<()> {
    let carried_rate = if state.rate_limit_snapshot.is_none() {
        latest_sparse_snapshot_before(write_txn, tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1, ordinal)?
    } else {
        None
    };
    let carried_factory = if state.factory_registry_snapshot.is_none() {
        latest_sparse_snapshot_before(
            write_txn,
            tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1,
            ordinal,
        )?
    } else {
        None
    };
    let effective_rate = state
        .rate_limit_snapshot
        .as_deref()
        .or(carried_rate.as_deref());
    let effective_factory = state
        .factory_registry_snapshot
        .as_deref()
        .or(carried_factory.as_deref());
    validate_reactive_registry_bytes(&state.reactive_registry.successor_bytes)?;
    let rate_bytes = effective_rate.map_or(0, <[u8]>::len);
    let factory_bytes = effective_factory.map_or(0, <[u8]>::len);
    let total = rate_bytes
        .checked_add(factory_bytes)
        .and_then(|bytes| bytes.checked_add(state.reactive_registry.successor_bytes.len()))
        .ok_or_else(|| {
            StoreError::Integrity("executor snapshot envelope byte length overflow".to_string())
        })?;
    if total > MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES {
        return Err(StoreError::Integrity(format!(
            "executor snapshot envelope is {total} bytes (maximum {MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES})"
        )));
    }
    if let Some(bytes) = effective_factory {
        FactoryRegistrySnapshot::from_canonical_bytes(bytes).map_err(|error| {
            StoreError::Integrity(format!(
                "executor factory-registry snapshot is not canonical: {error}"
            ))
        })?;
    }
    Ok(())
}

fn validate_reactive_registry_bytes(bytes: &[u8]) -> Result<()> {
    if bytes.len() > MAX_REACTIVE_REGISTRY_BYTES {
        return Err(StoreError::Integrity(format!(
            "reactive registry is {} bytes (maximum {MAX_REACTIVE_REGISTRY_BYTES})",
            bytes.len()
        )));
    }
    dregg_turn::PendingTurnRegistry::from_canonical_bytes(bytes).map_err(|error| {
        StoreError::Integrity(format!(
            "reactive registry is not a canonical pending-turn image: {error}"
        ))
    })?;
    Ok(())
}

fn validate_reactive_nullifier_keys(keys: &[[u8; 32]]) -> Result<()> {
    if u64::try_from(keys.len()).unwrap_or(u64::MAX) > MAX_EXECUTOR_ACCUMULATOR_RECORDS {
        return Err(StoreError::Integrity(
            "reactive-nullifier image exceeds the durable record bound".to_string(),
        ));
    }
    if keys.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(StoreError::Integrity(
            "reactive-nullifier image is not strictly sorted and unique".to_string(),
        ));
    }
    Ok(())
}

fn latest_reactive_registry_before(write_txn: &WriteTransaction, ordinal: u64) -> Result<Vec<u8>> {
    Ok(latest_sparse_snapshot_before(
        write_txn,
        tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1,
        ordinal,
    )?
    .unwrap_or_else(|| EMPTY_REACTIVE_REGISTRY_V1.to_vec()))
}

fn load_reactive_nullifiers_from_write(
    write_txn: &WriteTransaction,
    at_or_before_ordinal: Option<u64>,
) -> Result<Vec<[u8; 32]>> {
    let table = write_txn.open_table(tables::REACTIVE_NULLIFIERS_V1)?;
    if table.len()? > MAX_EXECUTOR_ACCUMULATOR_RECORDS {
        return Err(StoreError::Integrity(
            "durable reactive-nullifier table exceeds its record bound".to_string(),
        ));
    }
    let mut keys = Vec::with_capacity(checked_capacity(table.len()?, "reactive nullifier")?);
    for entry in table.iter()? {
        let (key, inserted_at) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        if at_or_before_ordinal.is_none_or(|ordinal| inserted_at.value() <= ordinal) {
            keys.push(*key.value());
        }
    }
    validate_reactive_nullifier_keys(&keys)?;
    Ok(keys)
}

fn stage_fresh_reactive_state_in(
    write_txn: &WriteTransaction,
    ordinal: u64,
    state: &FinalizedExecutorConsensusState,
) -> Result<()> {
    validate_reactive_registry_bytes(&state.reactive_registry.successor_bytes)?;
    validate_reactive_nullifier_keys(&state.reactive_nullifiers.successor_keys)?;

    let durable_registry = latest_reactive_registry_before(write_txn, ordinal)?;
    validate_reactive_registry_bytes(&durable_registry)?;
    if reactive_registry_commitment(&durable_registry)
        != state.reactive_registry.expected_pre_commitment
    {
        return Err(StoreError::Integrity(
            "reactive-registry compare-and-swap predecessor differs from durable state".to_string(),
        ));
    }
    {
        let mut snapshots =
            write_txn.open_table(tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1)?;
        if snapshots.get(ordinal)?.is_some() {
            return Err(StoreError::Integrity(
                "fresh reactive-registry ordinal already exists".to_string(),
            ));
        }
        snapshots.insert(ordinal, state.reactive_registry.successor_bytes.as_slice())?;
    }

    let durable_nullifiers = load_reactive_nullifiers_from_write(write_txn, None)?;
    if reactive_nullifier_commitment(&durable_nullifiers)
        != state.reactive_nullifiers.expected_pre_commitment
    {
        return Err(StoreError::Integrity(
            "reactive-nullifier compare-and-swap predecessor differs from durable state"
                .to_string(),
        ));
    }
    if durable_nullifiers.iter().any(|key| {
        state
            .reactive_nullifiers
            .successor_keys
            .binary_search(key)
            .is_err()
    }) {
        return Err(StoreError::Integrity(
            "reactive-nullifier successor is not an extension of durable state".to_string(),
        ));
    }
    {
        let mut nullifiers = write_txn.open_table(tables::REACTIVE_NULLIFIERS_V1)?;
        for key in &state.reactive_nullifiers.successor_keys {
            if durable_nullifiers.binary_search(key).is_err() {
                nullifiers.insert(key, ordinal)?;
            }
        }
    }
    {
        let mut frontiers =
            write_txn.open_table(tables::EXECUTOR_REACTIVE_NULLIFIER_FRONTIERS_V1)?;
        if frontiers.get(ordinal)?.is_some() {
            return Err(StoreError::Integrity(
                "fresh reactive-nullifier frontier already exists".to_string(),
            ));
        }
        let count =
            u64::try_from(state.reactive_nullifiers.successor_keys.len()).map_err(|_| {
                StoreError::Integrity("reactive-nullifier count does not fit u64".to_string())
            })?;
        frontiers.insert(ordinal, count)?;
    }
    Ok(())
}

fn verify_replayed_reactive_state_in(
    write_txn: &WriteTransaction,
    ordinal: u64,
    state: &FinalizedExecutorConsensusState,
) -> Result<()> {
    validate_reactive_registry_bytes(&state.reactive_registry.successor_bytes)?;
    validate_reactive_nullifier_keys(&state.reactive_nullifiers.successor_keys)?;
    let registry_predecessor = latest_reactive_registry_before(write_txn, ordinal)?;
    validate_reactive_registry_bytes(&registry_predecessor)?;
    if reactive_registry_commitment(&registry_predecessor)
        != state.reactive_registry.expected_pre_commitment
    {
        return Err(StoreError::Integrity(
            "replayed reactive-registry predecessor commitment differs from durable history"
                .to_string(),
        ));
    }
    let snapshots = write_txn.open_table(tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1)?;
    let Some(registry) = snapshots.get(ordinal)? else {
        return Err(StoreError::Integrity(
            "replayed finalized turn has no reactive-registry successor".to_string(),
        ));
    };
    if registry.value() != state.reactive_registry.successor_bytes.as_slice() {
        return Err(StoreError::Integrity(
            "replayed reactive-registry successor differs from durable ordinal".to_string(),
        ));
    }
    drop(registry);
    drop(snapshots);

    let frontiers = write_txn.open_table(tables::EXECUTOR_REACTIVE_NULLIFIER_FRONTIERS_V1)?;
    let Some(count) = frontiers.get(ordinal)? else {
        return Err(StoreError::Integrity(
            "replayed finalized turn has no reactive-nullifier frontier".to_string(),
        ));
    };
    if count.value()
        != u64::try_from(state.reactive_nullifiers.successor_keys.len()).unwrap_or(u64::MAX)
    {
        return Err(StoreError::Integrity(
            "replayed reactive-nullifier frontier differs from durable ordinal".to_string(),
        ));
    }
    let predecessor = if ordinal == 0 {
        Vec::new()
    } else {
        load_reactive_nullifiers_from_write(write_txn, Some(ordinal - 1))?
    };
    if reactive_nullifier_commitment(&predecessor)
        != state.reactive_nullifiers.expected_pre_commitment
    {
        return Err(StoreError::Integrity(
            "replayed reactive-nullifier predecessor commitment differs from durable history"
                .to_string(),
        ));
    }
    let durable = load_reactive_nullifiers_from_write(write_txn, Some(ordinal))?;
    if durable != state.reactive_nullifiers.successor_keys {
        return Err(StoreError::Integrity(
            "replayed reactive-nullifier image differs from durable history".to_string(),
        ));
    }
    Ok(())
}

fn stage_sparse_snapshot_in(
    write_txn: &WriteTransaction,
    table_definition: TableDefinition<u64, &[u8]>,
    kind: &str,
    ordinal: u64,
    snapshot: Option<&[u8]>,
    fresh: bool,
) -> Result<()> {
    let mut table = write_txn.open_table(table_definition)?;
    let existing = table.get(ordinal)?.map(|guard| guard.value().to_vec());
    match (fresh, snapshot, existing.as_deref()) {
        (true, Some(bytes), None) => {
            table.insert(ordinal, bytes)?;
        }
        (true, None, None) => {}
        (true, _, Some(_)) => {
            return Err(StoreError::Integrity(format!(
                "fresh executor {kind} snapshot ordinal already exists"
            )));
        }
        (false, Some(bytes), Some(existing)) if existing == bytes => {}
        (false, None, None) => {}
        (false, _, _) => {
            return Err(StoreError::Integrity(format!(
                "replayed executor {kind} snapshot differs from durable ordinal"
            )));
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
    validate_sparse_snapshot_envelope(write_txn, ordinal, state)?;
    stage_fresh_reactive_state_in(write_txn, ordinal, state)?;
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
    stage_sparse_snapshot_in(
        write_txn,
        tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1,
        "rate-limit",
        ordinal,
        state.rate_limit_snapshot.as_deref(),
        true,
    )?;
    stage_sparse_snapshot_in(
        write_txn,
        tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1,
        "factory-registry",
        ordinal,
        state.factory_registry_snapshot.as_deref(),
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
    validate_sparse_snapshot_envelope(write_txn, ordinal, state)?;
    verify_replayed_reactive_state_in(write_txn, ordinal, state)?;
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
    stage_sparse_snapshot_in(
        write_txn,
        tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1,
        "rate-limit",
        ordinal,
        state.rate_limit_snapshot.as_deref(),
        false,
    )?;
    stage_sparse_snapshot_in(
        write_txn,
        tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1,
        "factory-registry",
        ordinal,
        state.factory_registry_snapshot.as_deref(),
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
    {
        let mut factories = write_txn.open_table(tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1)?;
        let doomed: Vec<u64> = factories
            .range(new_cursor..)?
            .map(|entry| {
                entry
                    .map(|(ordinal, _)| ordinal.value())
                    .map_err(|error| StoreError::Database(error.to_string()))
            })
            .collect::<Result<_>>()?;
        for ordinal in doomed {
            factories.remove(ordinal)?;
        }
    }
    {
        let mut registries =
            write_txn.open_table(tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1)?;
        let doomed: Vec<u64> = registries
            .range(new_cursor..)?
            .map(|entry| {
                entry
                    .map(|(ordinal, _)| ordinal.value())
                    .map_err(|error| StoreError::Database(error.to_string()))
            })
            .collect::<Result<_>>()?;
        for ordinal in doomed {
            registries.remove(ordinal)?;
        }
    }
    let reactive_target = {
        let mut frontiers =
            write_txn.open_table(tables::EXECUTOR_REACTIVE_NULLIFIER_FRONTIERS_V1)?;
        let mut target = 0;
        if new_cursor > 0 {
            for entry in frontiers.range(0..new_cursor)? {
                let (_, count) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
                target = count.value();
            }
        }
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
        target
    };
    {
        let mut nullifiers = write_txn.open_table(tables::REACTIVE_NULLIFIERS_V1)?;
        let doomed: Vec<[u8; 32]> = nullifiers
            .iter()?
            .filter_map(|entry| match entry {
                Ok((key, inserted_at)) => {
                    (inserted_at.value() >= new_cursor).then_some(Ok(*key.value()))
                }
                Err(error) => Some(Err(StoreError::Database(error.to_string()))),
            })
            .collect::<Result<_>>()?;
        for key in doomed {
            nullifiers.remove(&key)?;
        }
        if nullifiers.len()? != reactive_target {
            return Err(StoreError::Integrity(
                "reactive-nullifier rollback does not match surviving frontier".to_string(),
            ));
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

    /// Latest sparse canonical factory-registry snapshot at or before
    /// `commit_cursor - 1`. `None` is the canonical empty registry.
    pub fn load_latest_factory_registry_snapshot_bytes(&self) -> Result<Option<Vec<u8>>> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(None);
        }
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1)?;
        let mut latest = None;
        for entry in table.range(0..cursor)? {
            let (ordinal, bytes) =
                entry.map_err(|error| StoreError::Database(error.to_string()))?;
            latest = Some((ordinal.value(), bytes.value().to_vec()));
        }
        let Some((_, bytes)) = latest else {
            return Ok(None);
        };
        FactoryRegistrySnapshot::from_canonical_bytes(&bytes).map_err(|error| {
            StoreError::Integrity(format!(
                "durable factory-registry snapshot is not canonical: {error}"
            ))
        })?;
        Ok(Some(bytes))
    }

    /// Typed form of [`Self::load_latest_factory_registry_snapshot_bytes`].
    pub fn load_latest_factory_registry_snapshot(&self) -> Result<Option<FactoryRegistrySnapshot>> {
        self.load_latest_factory_registry_snapshot_bytes()?
            .map(|bytes| {
                FactoryRegistrySnapshot::from_canonical_bytes(&bytes).map_err(|error| {
                    StoreError::Integrity(format!(
                        "durable factory-registry snapshot is not canonical: {error}"
                    ))
                })
            })
            .transpose()
    }

    /// Exact canonical pending-turn registry at the durable commit cursor.
    pub fn load_latest_reactive_registry_snapshot_bytes(&self) -> Result<Vec<u8>> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(EMPTY_REACTIVE_REGISTRY_V1.to_vec());
        }
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1)?;
        let mut latest = None;
        for entry in table.range(0..cursor)? {
            let (_, bytes) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
            latest = Some(bytes.value().to_vec());
        }
        let bytes = latest.unwrap_or_else(|| EMPTY_REACTIVE_REGISTRY_V1.to_vec());
        validate_reactive_registry_bytes(&bytes)?;
        Ok(bytes)
    }

    /// Strictly sorted React-only replay keys at the durable commit cursor.
    pub fn load_reactive_nullifier_keys(&self) -> Result<Vec<[u8; 32]>> {
        let cursor = self.commit_cursor()?;
        let write_txn = self.db.begin_write()?;
        let keys = if cursor == 0 {
            Vec::new()
        } else {
            load_reactive_nullifiers_from_write(&write_txn, Some(cursor - 1))?
        };
        drop(write_txn);
        Ok(keys)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commit_log::CommitRecord;
    use dregg_cell::commitment_set::CommitmentSet;
    use dregg_cell::note::NoteCommitment;
    use dregg_cell::revoked_set::RevokedSet;
    use dregg_cell::{CellId, Preconditions};
    use dregg_turn::{
        Action, Authorization, CallForest, CommitmentMode, DelegationMode, PendingTurnRegistry,
        ResolutionCondition, Turn,
    };

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

    fn factory_bytes(epoch: u64) -> Vec<u8> {
        FactoryRegistrySnapshot {
            current_epoch: epoch,
            ..FactoryRegistrySnapshot::default()
        }
        .to_canonical_bytes()
        .unwrap()
    }

    fn registry_bytes(entries: u8) -> Vec<u8> {
        let mut registry = PendingTurnRegistry::new();
        for tag in 0..entries {
            let agent = CellId::from_bytes([tag.wrapping_add(1); 32]);
            let action = Action {
                target: agent,
                method: [0; 32],
                args: Vec::new(),
                authorization: Authorization::Unchecked,
                preconditions: Preconditions::default(),
                effects: Vec::new(),
                may_delegate: DelegationMode::None,
                commitment_mode: CommitmentMode::Full,
                balance_change: None,
                witness_blobs: Vec::new(),
            };
            let mut call_forest = CallForest::new();
            call_forest.add_root(action);
            let turn = Turn {
                agent,
                nonce: u64::from(tag),
                call_forest,
                fee: 0,
                memo: None,
                valid_until: None,
                depends_on: Vec::new(),
                conservation_proof: None,
                sovereign_witnesses: std::collections::HashMap::new(),
                previous_receipt_hash: None,
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            };
            registry.submit_pending(
                turn,
                ResolutionCondition::AwaitReceipt {
                    turn_hash: [tag.wrapping_add(0xa0); 32],
                    federation_id: None,
                },
                100 + u64::from(tag),
            );
        }
        registry.to_canonical_bytes().unwrap()
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
            factory_registry_snapshot: Some(factory_bytes(7)),
            reactive_registry: ReactiveRegistryCasV1::default(),
            reactive_nullifiers: ReactiveNullifierCasV1::default(),
            promise_resolutions: Vec::new(),
        }
    }

    fn state_two(rate: Option<&[u8]>) -> FinalizedExecutorConsensusState {
        let mut state = state_one(rate);
        state.factory_registry_snapshot = Some(factory_bytes(8));
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

    fn reactive_state_one(rate: Option<&[u8]>) -> FinalizedExecutorConsensusState {
        let mut state = state_one(rate);
        state.reactive_registry = ReactiveRegistryCasV1::new(
            reactive_registry_commitment(EMPTY_REACTIVE_REGISTRY_V1),
            registry_bytes(1),
        );
        state.reactive_nullifiers =
            ReactiveNullifierCasV1::new(reactive_nullifier_commitment(&[]), vec![[0x71; 32]]);
        state
    }

    fn reactive_state_two(rate: Option<&[u8]>) -> FinalizedExecutorConsensusState {
        let mut state = state_two(rate);
        let predecessor = registry_bytes(1);
        state.reactive_registry = ReactiveRegistryCasV1::new(
            reactive_registry_commitment(&predecessor),
            registry_bytes(2),
        );
        state.reactive_nullifiers = ReactiveNullifierCasV1::new(
            reactive_nullifier_commitment(&[[0x71; 32]]),
            vec![[0x71; 32], [0x72; 32]],
        );
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
        assert_eq!(
            store.load_latest_factory_registry_snapshot_bytes().unwrap(),
            state.factory_registry_snapshot
        );
        assert_eq!(
            store
                .load_latest_factory_registry_snapshot()
                .unwrap()
                .unwrap()
                .current_epoch,
            7
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
        let preexisting_factory = factory_bytes(99);
        {
            let write = store.db.begin_write().unwrap();
            {
                let mut factories = write
                    .open_table(tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1)
                    .unwrap();
                factories.insert(0, preexisting_factory.as_slice()).unwrap();
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
        assert_eq!(
            store.load_latest_factory_registry_snapshot_bytes().unwrap(),
            None
        );
        let read = store.db.begin_read().unwrap();
        let rates = read
            .open_table(tables::EXECUTOR_RATE_LIMIT_SNAPSHOTS_V1)
            .unwrap();
        assert!(rates.get(0).unwrap().is_none());
        let factories = read
            .open_table(tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1)
            .unwrap();
        assert_eq!(
            factories.get(0).unwrap().unwrap().value(),
            preexisting_factory.as_slice()
        );
        drop(factories);
        drop(read);
        assert!(store.load_reactive_nullifier_keys().unwrap().is_empty());
        assert_eq!(
            store
                .load_latest_reactive_registry_snapshot_bytes()
                .unwrap(),
            EMPTY_REACTIVE_REGISTRY_V1
        );
    }

    #[test]
    fn reactive_state_is_restart_durable_exact_on_replay_and_domain_separated() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("reactive-state.redb");
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let first_record = record(0, empty_root);
        let state = reactive_state_one(None);
        {
            let store = PersistentStore::open(&path).unwrap();
            store
                .commit_finalized_turn_with_executor_state(0, &first_record, &[[1; 32]], &state)
                .unwrap();
            assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
        }

        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(
            store.load_reactive_nullifier_keys().unwrap(),
            vec![[0x71; 32]]
        );
        assert_eq!(
            store
                .load_latest_reactive_registry_snapshot_bytes()
                .unwrap(),
            state.reactive_registry.successor_bytes
        );
        assert!(store.load_faithful_nullifier_records().unwrap().is_empty());
        assert!(
            !store
                .commit_finalized_turn_with_executor_state(0, &first_record, &[[1; 32]], &state)
                .unwrap()
                .freshly_committed
        );

        let mut wrong_replay = state.clone();
        wrong_replay.reactive_nullifiers.successor_keys = vec![[0x72; 32]];
        assert!(
            store
                .commit_finalized_turn_with_executor_state(
                    0,
                    &first_record,
                    &[[1; 32]],
                    &wrong_replay,
                )
                .is_err()
        );
        let mut wrong_registry_successor = state.clone();
        wrong_registry_successor.reactive_registry.successor_bytes = registry_bytes(2);
        assert!(
            store
                .commit_finalized_turn_with_executor_state(
                    0,
                    &first_record,
                    &[[1; 32]],
                    &wrong_registry_successor,
                )
                .is_err()
        );
        let mut wrong_reactive_predecessor = state.clone();
        wrong_reactive_predecessor
            .reactive_nullifiers
            .expected_pre_commitment = [0x99; 32];
        assert!(
            store
                .commit_finalized_turn_with_executor_state(
                    0,
                    &first_record,
                    &[[1; 32]],
                    &wrong_reactive_predecessor,
                )
                .is_err()
        );
        let mut wrong_registry_predecessor = state.clone();
        wrong_registry_predecessor
            .reactive_registry
            .expected_pre_commitment = [0x98; 32];
        assert!(
            store
                .commit_finalized_turn_with_executor_state(
                    0,
                    &first_record,
                    &[[1; 32]],
                    &wrong_registry_predecessor,
                )
                .is_err()
        );

        let mut cross_domain = reactive_state_two(None);
        cross_domain.reactive_nullifiers = ReactiveNullifierCasV1::new(
            reactive_registry_commitment(EMPTY_REACTIVE_REGISTRY_V1),
            vec![[0x71; 32], [0x72; 32]],
        );
        assert_ne!(
            reactive_registry_commitment(EMPTY_REACTIVE_REGISTRY_V1),
            reactive_nullifier_commitment(&[[0x71; 32]])
        );
        assert!(
            store
                .commit_finalized_turn_with_executor_state(
                    1,
                    &record(1, empty_root),
                    &[[4; 32]],
                    &cross_domain,
                )
                .is_err()
        );
        assert_eq!(
            store.load_reactive_nullifier_keys().unwrap(),
            vec![[0x71; 32]]
        );

        // A caller that hashes a corrupt durable predecessor must not be able
        // to CAS over it and thereby hide the corruption under a valid successor.
        let corrupt_predecessor = b"DPRG1-not-canonical";
        let write = store.db.begin_write().unwrap();
        {
            let mut registries = write
                .open_table(tables::EXECUTOR_REACTIVE_REGISTRY_SNAPSHOTS_V1)
                .unwrap();
            registries
                .insert(0, corrupt_predecessor.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        let mut hides_corruption = reactive_state_two(None);
        hides_corruption.reactive_registry.expected_pre_commitment =
            reactive_registry_commitment(corrupt_predecessor);
        assert!(
            store
                .commit_finalized_turn_with_executor_state(
                    1,
                    &record(1, empty_root),
                    &[[4; 32]],
                    &hides_corruption,
                )
                .is_err()
        );
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
        let mut wrong_factory = state.clone();
        wrong_factory.factory_registry_snapshot = Some(factory_bytes(8));
        assert!(
            store
                .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &wrong_factory)
                .is_err()
        );
        let mut omitted_factory = state.clone();
        omitted_factory.factory_registry_snapshot = None;
        assert!(
            store
                .commit_finalized_turn_with_executor_state(0, &record, &[[1; 32]], &omitted_factory)
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
        let mut invalid_factory = state_one(None);
        invalid_factory.factory_registry_snapshot = Some(b"not-a-factory-registry".to_vec());
        let store = PersistentStore::open_in_memory().unwrap();
        let write = store.db.begin_write().unwrap();
        assert!(validate_sparse_snapshot_envelope(&write, 0, &invalid_factory).is_err());

        let canonical_factory = factory_bytes(1);
        let mut oversized = state_one(None);
        oversized.rate_limit_snapshot = Some(vec![
            0;
            MAX_DURABLE_EXECUTOR_SNAPSHOT_BYTES
                - canonical_factory.len()
                + 1
        ]);
        oversized.factory_registry_snapshot = Some(canonical_factory);
        assert!(validate_sparse_snapshot_envelope(&write, 0, &oversized).is_err());
        drop(write);

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
        let first = reactive_state_one(Some(b"rate-one"));
        let second = reactive_state_two(Some(b"rate-two"));
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
        assert_eq!(
            store.load_latest_factory_registry_snapshot_bytes().unwrap(),
            first.factory_registry_snapshot
        );
        assert_eq!(
            store.load_reactive_nullifier_keys().unwrap(),
            first.reactive_nullifiers.successor_keys
        );
        assert_eq!(
            store
                .load_latest_reactive_registry_snapshot_bytes()
                .unwrap(),
            first.reactive_registry.successor_bytes
        );
        let read = store.db.begin_read().unwrap();
        let factories = read
            .open_table(tables::EXECUTOR_FACTORY_REGISTRY_SNAPSHOTS_V1)
            .unwrap();
        assert!(factories.get(1).unwrap().is_none());
    }
}
