//! Durable, typed promise-resolution notifications.
//!
//! The finalized-turn commit log remains the authority. This append-only
//! observer journal is staged in the *same redb transaction* as its source
//! commit and executor-state successor. It gives WebSocket, polling, Discord,
//! Telegram, and game clients a durable resume cursor without a crash window
//! in which consensus commits but the notification disappears.

use redb::ReadableTable;
use serde::{Deserialize, Serialize};

use crate::{PersistentStore, Result, StoreError, tables};

const EVENT_ID_DOMAIN_V1: &str = "dregg-promise-resolution-event-v1";
const BATCH_DIGEST_DOMAIN_V1: &str = "dregg-promise-resolution-batch-v1";

/// A single finalized turn cannot publish an unbounded cascade to observers.
pub const MAX_PROMISE_RESOLUTIONS_PER_BATCH: usize = 4_096;
/// Public reads are deliberately bounded independently of caller input.
pub const MAX_PROMISE_RESOLUTION_QUERY: usize = 1_000;
/// Bounds persisted operator text originating in a rejected/broken dependency.
pub const MAX_PROMISE_BROKEN_REASON_BYTES: usize = 16 * 1024;

/// Stable public shape of a broken promise.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PromiseBrokenReasonV1 {
    TurnRejected { reason: String },
    Timeout,
    FederationUnreachable,
    DependencyBroken { cause: Box<PromiseBrokenReasonV1> },
}

/// Typed observer outcome. `ReadyToExecute` intentionally contains no `Turn`:
/// the dependent is unsigned and this surface is notification-only.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PromiseResolutionKindV1 {
    Resolved { receipt_hash: [u8; 32] },
    ReadyToExecute,
    Broken { reason: PromiseBrokenReasonV1 },
}

/// Candidate prepared from a finalized executor's resolution events.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromiseResolutionCandidateV1 {
    pub source_commit_ordinal: u64,
    pub source_receipt_hash: [u8; 32],
    pub event_index: u32,
    pub pending_id: [u8; 32],
    pub outcome: PromiseResolutionKindV1,
}

impl PromiseResolutionCandidateV1 {
    pub fn event_id(&self) -> [u8; 32] {
        *blake3::Hasher::new_derive_key(EVENT_ID_DOMAIN_V1)
            .update(&self.source_commit_ordinal.to_le_bytes())
            .update(&self.source_receipt_hash)
            .update(&self.event_index.to_le_bytes())
            .finalize()
            .as_bytes()
    }

    fn validate(&self) -> Result<()> {
        fn validate_broken(reason: &PromiseBrokenReasonV1, depth: usize) -> Result<()> {
            if depth > 64 {
                return Err(StoreError::Integrity(
                    "promise broken-reason nesting exceeds 64".to_string(),
                ));
            }
            match reason {
                PromiseBrokenReasonV1::TurnRejected { reason } => {
                    if reason.len() > MAX_PROMISE_BROKEN_REASON_BYTES {
                        return Err(StoreError::Integrity(
                            "promise broken-reason text exceeds durable bound".to_string(),
                        ));
                    }
                }
                PromiseBrokenReasonV1::DependencyBroken { cause } => {
                    validate_broken(cause, depth + 1)?;
                }
                PromiseBrokenReasonV1::Timeout | PromiseBrokenReasonV1::FederationUnreachable => {}
            }
            Ok(())
        }

        if let PromiseResolutionKindV1::Broken { reason } = &self.outcome {
            validate_broken(reason, 0)?;
        }
        Ok(())
    }
}

/// Stored row with a dense, resumable observer cursor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DurablePromiseResolutionV1 {
    pub sequence: u64,
    pub event_id: [u8; 32],
    pub source_commit_ordinal: u64,
    pub source_receipt_hash: [u8; 32],
    pub event_index: u32,
    pub pending_id: [u8; 32],
    pub outcome: PromiseResolutionKindV1,
}

impl DurablePromiseResolutionV1 {
    fn from_candidate(sequence: u64, candidate: PromiseResolutionCandidateV1) -> Self {
        Self {
            sequence,
            event_id: candidate.event_id(),
            source_commit_ordinal: candidate.source_commit_ordinal,
            source_receipt_hash: candidate.source_receipt_hash,
            event_index: candidate.event_index,
            pending_id: candidate.pending_id,
            outcome: candidate.outcome,
        }
    }

    fn candidate(&self) -> PromiseResolutionCandidateV1 {
        PromiseResolutionCandidateV1 {
            source_commit_ordinal: self.source_commit_ordinal,
            source_receipt_hash: self.source_receipt_hash,
            event_index: self.event_index,
            pending_id: self.pending_id,
            outcome: self.outcome.clone(),
        }
    }

    pub fn matches_candidate(&self, candidate: &PromiseResolutionCandidateV1) -> bool {
        self.candidate() == *candidate && self.event_id == candidate.event_id()
    }

    fn validate(&self, key: u64) -> Result<()> {
        if self.sequence != key {
            return Err(StoreError::Integrity(format!(
                "promise-resolution row key {key} disagrees with sequence {}",
                self.sequence
            )));
        }
        self.candidate().validate()?;
        if self.event_id != self.candidate().event_id() {
            return Err(StoreError::Integrity(
                "promise-resolution event id is not canonical".to_string(),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PromiseResolutionBatchManifestV1 {
    source_receipt_hash: [u8; 32],
    first_sequence: u64,
    event_count: u32,
    batch_digest: [u8; 32],
}

fn canonical_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    postcard::to_stdvec(value).map_err(|error| StoreError::Serialization(error.to_string()))
}

fn decode_canonical<T>(bytes: &[u8], what: &str) -> Result<T>
where
    T: for<'de> Deserialize<'de> + Serialize,
{
    let decoded: T = postcard::from_bytes(bytes)
        .map_err(|error| StoreError::Integrity(format!("{what} decode failed: {error}")))?;
    let encoded = canonical_bytes(&decoded)?;
    if encoded != bytes {
        return Err(StoreError::Integrity(format!("{what} is not canonical")));
    }
    Ok(decoded)
}

fn batch_digest(candidates: &[PromiseResolutionCandidateV1]) -> Result<[u8; 32]> {
    let bytes = canonical_bytes(&candidates)?;
    Ok(*blake3::Hasher::new_derive_key(BATCH_DIGEST_DOMAIN_V1)
        .update(&bytes)
        .finalize()
        .as_bytes())
}

fn dense_cursor(table: &impl ReadableTable<u64, &'static [u8]>, what: &str) -> Result<u64> {
    let count = table.len()?;
    match (count, table.last()?) {
        (0, None) => Ok(0),
        (0, Some((key, _))) => Err(StoreError::Integrity(format!(
            "{what} has key {} but reports zero rows",
            key.value()
        ))),
        (count, Some((key, _))) if key.value() == count - 1 => Ok(count),
        (count, Some((key, _))) => Err(StoreError::Integrity(format!(
            "{what} is not dense: {count} rows, terminal key {}",
            key.value()
        ))),
        (count, None) => Err(StoreError::Integrity(format!(
            "{what} reports {count} rows but has no terminal key"
        ))),
    }
}

fn validate_candidates(
    source: &crate::CommitRecord,
    candidates: &[PromiseResolutionCandidateV1],
) -> Result<[u8; 32]> {
    if candidates.len() > MAX_PROMISE_RESOLUTIONS_PER_BATCH {
        return Err(StoreError::Integrity(format!(
            "promise-resolution batch has {} events (maximum {})",
            candidates.len(),
            MAX_PROMISE_RESOLUTIONS_PER_BATCH
        )));
    }
    for (index, candidate) in candidates.iter().enumerate() {
        candidate.validate()?;
        let expected_index = u32::try_from(index).map_err(|_| {
            StoreError::Integrity("promise-resolution event index overflows u32".to_string())
        })?;
        if candidate.source_commit_ordinal != source.ordinal
            || candidate.source_receipt_hash != source.receipt_hash
            || candidate.event_index != expected_index
        {
            return Err(StoreError::Integrity(
                "promise-resolution batch disagrees with its source commit or has non-dense event indexes"
                    .to_string(),
            ));
        }
    }
    batch_digest(candidates)
}

fn load_manifest_from_table(
    batches: &impl ReadableTable<u64, &'static [u8]>,
    ordinal: u64,
) -> Result<Option<PromiseResolutionBatchManifestV1>> {
    let bytes = {
        let guard = batches.get(ordinal)?;
        guard.map(|value| value.value().to_vec())
    };
    bytes
        .map(|bytes| decode_canonical(&bytes, "promise-resolution batch manifest"))
        .transpose()
}

fn load_manifest_records(
    records: &impl ReadableTable<u64, &'static [u8]>,
    manifest: &PromiseResolutionBatchManifestV1,
) -> Result<Vec<DurablePromiseResolutionV1>> {
    let mut out = Vec::with_capacity(manifest.event_count as usize);
    for offset in 0..u64::from(manifest.event_count) {
        let key = manifest.first_sequence.checked_add(offset).ok_or_else(|| {
            StoreError::Integrity("promise-resolution sequence overflow".to_string())
        })?;
        let guard = records.get(key)?.ok_or_else(|| {
            StoreError::Integrity(
                "promise-resolution batch manifest points at a missing row".to_string(),
            )
        })?;
        let bytes = guard.value().to_vec();
        drop(guard);
        let record: DurablePromiseResolutionV1 =
            decode_canonical(&bytes, "promise-resolution row")?;
        record.validate(key)?;
        out.push(record);
    }
    Ok(out)
}

/// Stage the complete observer batch inside the caller's fresh finalized-turn
/// writer. Empty batches are manifested too, so replay cannot invent events.
pub(crate) fn stage_fresh_promise_resolution_batch_in(
    write: &redb::WriteTransaction,
    source: &crate::CommitRecord,
    candidates: &[PromiseResolutionCandidateV1],
) -> Result<Vec<DurablePromiseResolutionV1>> {
    let digest = validate_candidates(source, candidates)?;
    let mut records = write.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
    let mut batches = write.open_table(tables::PROMISE_RESOLUTION_BATCHES_V1)?;
    if load_manifest_from_table(&batches, source.ordinal)?.is_some() {
        return Err(StoreError::Integrity(
            "fresh promise-resolution source already has a durable batch".to_string(),
        ));
    }
    let cursor = dense_cursor(&records, "promise-resolution journal")?;
    let event_count = u32::try_from(candidates.len()).map_err(|_| {
        StoreError::Integrity("promise-resolution event count overflows u32".to_string())
    })?;
    let manifest = PromiseResolutionBatchManifestV1 {
        source_receipt_hash: source.receipt_hash,
        first_sequence: cursor,
        event_count,
        batch_digest: digest,
    };
    let mut durable = Vec::with_capacity(candidates.len());
    for (offset, candidate) in candidates.iter().cloned().enumerate() {
        let sequence = cursor.checked_add(offset as u64).ok_or_else(|| {
            StoreError::Integrity("promise-resolution sequence overflow".to_string())
        })?;
        let record = DurablePromiseResolutionV1::from_candidate(sequence, candidate);
        let bytes = canonical_bytes(&record)?;
        records.insert(sequence, bytes.as_slice())?;
        durable.push(record);
    }
    let manifest_bytes = canonical_bytes(&manifest)?;
    batches.insert(source.ordinal, manifest_bytes.as_slice())?;
    Ok(durable)
}

/// Exact replay tooth for the observer side of executor consensus state.
pub(crate) fn verify_replayed_promise_resolution_batch_in(
    write: &redb::WriteTransaction,
    source: &crate::CommitRecord,
    candidates: &[PromiseResolutionCandidateV1],
) -> Result<Vec<DurablePromiseResolutionV1>> {
    let digest = validate_candidates(source, candidates)?;
    let records = write.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
    let batches = write.open_table(tables::PROMISE_RESOLUTION_BATCHES_V1)?;
    let manifest = load_manifest_from_table(&batches, source.ordinal)?.ok_or_else(|| {
        StoreError::Integrity(
            "replayed finalized turn is missing its promise-resolution batch".to_string(),
        )
    })?;
    let event_count = u32::try_from(candidates.len()).map_err(|_| {
        StoreError::Integrity("promise-resolution event count overflows u32".to_string())
    })?;
    if manifest.source_receipt_hash != source.receipt_hash
        || manifest.event_count != event_count
        || manifest.batch_digest != digest
    {
        return Err(StoreError::Integrity(
            "promise-resolution replay disagrees with durable source batch".to_string(),
        ));
    }
    let durable = load_manifest_records(&records, &manifest)?;
    for (record, candidate) in durable.iter().zip(candidates.iter().cloned()) {
        if *record != DurablePromiseResolutionV1::from_candidate(record.sequence, candidate) {
            return Err(StoreError::Integrity(
                "promise-resolution replay row differs from its durable manifest".to_string(),
            ));
        }
    }
    Ok(durable)
}

impl PersistentStore {
    /// Load one source commit's exact durable observer batch.
    pub fn promise_resolution_batch_for_commit_v1(
        &self,
        ordinal: u64,
    ) -> Result<Option<Vec<DurablePromiseResolutionV1>>> {
        let read = self.db.begin_read()?;
        let records = read.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
        let batches = read.open_table(tables::PROMISE_RESOLUTION_BATCHES_V1)?;
        load_manifest_from_table(&batches, ordinal)?
            .map(|manifest| load_manifest_records(&records, &manifest))
            .transpose()
    }

    /// Load the next bounded page after an exclusive durable sequence cursor.
    pub fn promise_resolutions_after_v1(
        &self,
        after: Option<u64>,
        limit: usize,
    ) -> Result<Vec<DurablePromiseResolutionV1>> {
        let limit = limit.min(MAX_PROMISE_RESOLUTION_QUERY);
        if limit == 0 {
            return Ok(Vec::new());
        }
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
        // Validate density even for a short page: a truncated interior journal
        // must never silently look like "no game events".
        let _ = dense_cursor(&table, "promise-resolution journal")?;
        let start = after.map_or(0, |cursor| cursor.saturating_add(1));
        let mut out = Vec::with_capacity(limit);
        for entry in table.range(start..)? {
            let (key, value) = entry?;
            let key = key.value();
            let bytes = value.value();
            let record: DurablePromiseResolutionV1 =
                decode_canonical(bytes, "promise-resolution row")?;
            record.validate(key)?;
            out.push(record);
            if out.len() == limit {
                break;
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn store() -> (TempDir, PersistentStore) {
        let dir = TempDir::new().unwrap();
        let store = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        (dir, store)
    }

    fn candidates(ordinal: u64) -> Vec<PromiseResolutionCandidateV1> {
        vec![
            PromiseResolutionCandidateV1 {
                source_commit_ordinal: ordinal,
                source_receipt_hash: [0x11; 32],
                event_index: 0,
                pending_id: [0x21; 32],
                outcome: PromiseResolutionKindV1::Resolved {
                    receipt_hash: [0x31; 32],
                },
            },
            PromiseResolutionCandidateV1 {
                source_commit_ordinal: ordinal,
                source_receipt_hash: [0x11; 32],
                event_index: 1,
                pending_id: [0x22; 32],
                outcome: PromiseResolutionKindV1::ReadyToExecute,
            },
        ]
    }

    fn record(ordinal: u64) -> crate::CommitRecord {
        crate::CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [ordinal as u8; 32],
            block_executed_up_to: ordinal,
            turn_hash: [0x41u8.wrapping_add(ordinal as u8); 32],
            creator: [0x51; 32],
            receipt_hash: [0x11; 32],
            ledger_root: [0x61u8.wrapping_add(ordinal as u8); 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn state(ordinal: u64) -> crate::FinalizedExecutorConsensusState {
        crate::FinalizedExecutorConsensusState {
            promise_resolutions: candidates(ordinal),
            ..Default::default()
        }
    }

    #[test]
    fn batch_is_atomic_with_source_commit_and_exact_on_replay() {
        let (_dir, store) = store();
        let first = store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &state(0))
            .unwrap();
        assert!(first.freshly_committed);
        let durable = store
            .promise_resolution_batch_for_commit_v1(0)
            .unwrap()
            .unwrap();
        assert_eq!(durable.len(), 2);

        let replay = store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &state(0))
            .unwrap();
        assert!(!replay.freshly_committed);
        assert_eq!(
            store.promise_resolutions_after_v1(None, 100).unwrap(),
            durable
        );
    }

    #[test]
    fn changed_replay_is_refused_without_extending_journal() {
        let (_dir, store) = store();
        store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &state(0))
            .unwrap();
        let mut forged = state(0);
        forged.promise_resolutions[1].pending_id = [0x99; 32];
        let error = store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &forged)
            .unwrap_err();
        assert!(error.to_string().contains("replay disagrees"));
        assert_eq!(
            store.promise_resolutions_after_v1(None, 100).unwrap().len(),
            2
        );
    }

    #[test]
    fn crash_after_atomic_commit_before_publication_recovers_complete_outbox() {
        let (dir, store) = store();
        store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &state(0))
            .unwrap();
        // Simulate process death before NodeEvent/WS publication: only the
        // atomic finalized writer has run.
        drop(store);
        let reopened = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        assert!(reopened.commit_record_at(0).unwrap().is_some());
        let recovered = reopened
            .promise_resolution_batch_for_commit_v1(0)
            .unwrap()
            .unwrap();
        assert_eq!(recovered.len(), 2);
        assert_eq!(recovered[0].source_commit_ordinal, 0);
        assert_eq!(
            recovered[1].outcome,
            PromiseResolutionKindV1::ReadyToExecute
        );
    }

    #[test]
    fn query_is_exclusive_cursor_bounded_and_survives_reopen() {
        let (dir, store) = store();
        store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &state(0))
            .unwrap();
        store
            .commit_finalized_turn_with_executor_state(1, &record(1), &[], &state(1))
            .unwrap();
        assert_eq!(
            store.promise_resolutions_after_v1(Some(0), 2).unwrap()[0].sequence,
            1
        );
        drop(store);
        let reopened = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        let page = reopened.promise_resolutions_after_v1(Some(1), 1).unwrap();
        assert_eq!(page.len(), 1);
        assert_eq!(page[0].sequence, 2);
    }

    #[test]
    fn malformed_or_noncanonical_row_fails_closed() {
        let (_dir, store) = store();
        store
            .commit_finalized_turn_with_executor_state(0, &record(0), &[], &state(0))
            .unwrap();
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)
                .unwrap();
            table.insert(0, &[0xff, 0x00][..]).unwrap();
        }
        write.commit().unwrap();
        assert!(store.promise_resolutions_after_v1(None, 10).is_err());
    }

    #[test]
    fn aborted_finalized_writer_leaves_neither_source_nor_outbox() {
        let (_dir, store) = store();
        let write = store.db.begin_write().unwrap();
        stage_fresh_promise_resolution_batch_in(&write, &record(0), &candidates(0)).unwrap();
        // Crash/abort before the finalized writer commits.
        drop(write);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert!(
            store
                .promise_resolutions_after_v1(None, 10)
                .unwrap()
                .is_empty()
        );
    }
}
