//! Private, durable custody for already-signed dependent turns.
//!
//! Public promise-resolution rows deliberately contain no `Turn`.  This table
//! is the private half: an AEAD-sealed signed envelope is bound to the pending
//! turn hash and the stable `ReadyToExecute` expectation.  A release is an
//! atomic, destructive claim against a real durable resolution row.  The seal
//! is removed from redb before control returns to the caller, so a crash can
//! lose a claimed delivery but can never release it twice (at-most-once).

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use crate::{
    DurablePromiseResolutionV1, PersistentStore, PromiseResolutionCandidateV1,
    PromiseResolutionKindV1, Result, StoreError, tables,
};

const READY_DIGEST_DOMAIN_V1: &str = "dregg-private-dependent-ready-v1";
const CURSOR_META_KEY_V1: &str = "private_dependent_scheduler_cursor_v1";

pub const MAX_PRIVATE_DEPENDENT_TURNS: usize = 4_096;
pub const MAX_PRIVATE_DEPENDENT_SEAL_BYTES: usize = 256 * 1024 + 64;
pub const MAX_PRIVATE_DEPENDENT_ROW_BYTES: usize = MAX_PRIVATE_DEPENDENT_SEAL_BYTES + 4 * 1024;
pub const MAX_PRIVATE_DEPENDENT_TOTAL_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES: usize = 4 * 1024;

/// Stable expectation committed before the promise becomes ready.
pub fn private_dependent_ready_digest_v1(
    promise_id: [u8; 32],
    signed_turn_hash: [u8; 32],
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(READY_DIGEST_DOMAIN_V1)
        .update(&promise_id)
        .update(&signed_turn_hash)
        .update(b"ready_to_execute")
        .finalize()
        .as_bytes()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrivateDependentTurnStatusV1 {
    Armed,
    Claimed {
        ready_sequence: u64,
        event_id: [u8; 32],
    },
    Submitted {
        ready_sequence: u64,
        event_id: [u8; 32],
        ingress_id: [u8; 32],
    },
    Refused {
        ready_sequence: u64,
        event_id: [u8; 32],
        reason: String,
    },
    Cancelled,
    Expired {
        ready_sequence: u64,
    },
}

impl PrivateDependentTurnStatusV1 {
    pub const fn is_terminal(&self) -> bool {
        matches!(
            self,
            Self::Submitted { .. } | Self::Refused { .. } | Self::Cancelled | Self::Expired { .. }
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateDependentTurnSnapshotV1 {
    pub promise_id: [u8; 32],
    pub signed_turn_hash: [u8; 32],
    pub expected_resolution_digest: [u8; 32],
    pub expires_at_sequence_exclusive: u64,
    pub status: PrivateDependentTurnStatusV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimedPrivateDependentTurnV1 {
    pub promise_id: [u8; 32],
    pub signed_turn_hash: [u8; 32],
    pub expected_resolution_digest: [u8; 32],
    pub ready_sequence: u64,
    pub event_id: [u8; 32],
    pub sealed_signed_turn: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateDependentTurnFinishV1 {
    Submitted { ingress_id: [u8; 32] },
    Refused { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PrivateDependentTurnRecordV1 {
    promise_id: [u8; 32],
    signed_turn_hash: [u8; 32],
    expected_resolution_digest: [u8; 32],
    expires_at_sequence_exclusive: u64,
    status: PrivateDependentTurnStatusV1,
    /// Present only while Armed. A destructive claim clears it in the same
    /// transaction that records the unique durable Ready event.
    sealed_signed_turn: Vec<u8>,
}

impl PrivateDependentTurnRecordV1 {
    fn validate(&self, key: &[u8]) -> Result<()> {
        if key != self.promise_id {
            return Err(StoreError::Integrity(
                "private dependent-turn key disagrees with promise id".to_string(),
            ));
        }
        if self.promise_id != self.signed_turn_hash {
            return Err(StoreError::Integrity(
                "private dependent turn is not bound to its promise id".to_string(),
            ));
        }
        if self.expected_resolution_digest
            != private_dependent_ready_digest_v1(self.promise_id, self.signed_turn_hash)
        {
            return Err(StoreError::Integrity(
                "private dependent-turn resolution expectation is not canonical".to_string(),
            ));
        }
        match &self.status {
            PrivateDependentTurnStatusV1::Armed => {
                if self.sealed_signed_turn.is_empty()
                    || self.sealed_signed_turn.len() > MAX_PRIVATE_DEPENDENT_SEAL_BYTES
                {
                    return Err(StoreError::Integrity(
                        "private dependent-turn armed seal is empty or oversized".to_string(),
                    ));
                }
            }
            PrivateDependentTurnStatusV1::Refused { reason, .. } => {
                if reason.len() > MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES {
                    return Err(StoreError::Integrity(
                        "private dependent-turn refusal text is oversized".to_string(),
                    ));
                }
                if !self.sealed_signed_turn.is_empty() {
                    return Err(StoreError::Integrity(
                        "terminal private dependent turn retained its private seal".to_string(),
                    ));
                }
            }
            _ if !self.sealed_signed_turn.is_empty() => {
                return Err(StoreError::Integrity(
                    "non-armed private dependent turn retained its private seal".to_string(),
                ));
            }
            _ => {}
        }
        Ok(())
    }

    fn snapshot(&self) -> PrivateDependentTurnSnapshotV1 {
        PrivateDependentTurnSnapshotV1 {
            promise_id: self.promise_id,
            signed_turn_hash: self.signed_turn_hash,
            expected_resolution_digest: self.expected_resolution_digest,
            expires_at_sequence_exclusive: self.expires_at_sequence_exclusive,
            status: self.status.clone(),
        }
    }
}

fn canonical_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    postcard::to_stdvec(value).map_err(|error| StoreError::Serialization(error.to_string()))
}

fn decode_record(bytes: &[u8], key: &[u8]) -> Result<PrivateDependentTurnRecordV1> {
    if bytes.len() > MAX_PRIVATE_DEPENDENT_ROW_BYTES {
        return Err(StoreError::Integrity(format!(
            "private dependent-turn row is {} bytes (maximum {})",
            bytes.len(),
            MAX_PRIVATE_DEPENDENT_ROW_BYTES
        )));
    }
    let record: PrivateDependentTurnRecordV1 = postcard::from_bytes(bytes).map_err(|error| {
        StoreError::Integrity(format!("private dependent-turn row decode failed: {error}"))
    })?;
    record.validate(key)?;
    if canonical_bytes(&record)?.as_slice() != bytes {
        return Err(StoreError::Integrity(
            "private dependent-turn row is non-canonical".to_string(),
        ));
    }
    Ok(record)
}

fn decode_resolution(bytes: &[u8], sequence: u64) -> Result<DurablePromiseResolutionV1> {
    if bytes.len() > crate::promise_resolutions::MAX_PROMISE_RESOLUTION_ROW_BYTES {
        return Err(StoreError::Integrity(
            "private dependent-turn release found an oversized resolution row".to_string(),
        ));
    }
    let row: DurablePromiseResolutionV1 = postcard::from_bytes(bytes).map_err(|error| {
        StoreError::Integrity(format!(
            "private dependent-turn resolution decode failed: {error}"
        ))
    })?;
    if canonical_bytes(&row)?.as_slice() != bytes || row.sequence != sequence {
        return Err(StoreError::Integrity(
            "private dependent-turn release found a non-canonical resolution row".to_string(),
        ));
    }
    let candidate = PromiseResolutionCandidateV1 {
        source_commit_ordinal: row.source_commit_ordinal,
        source_receipt_hash: row.source_receipt_hash,
        event_index: row.event_index,
        pending_id: row.pending_id,
        outcome: row.outcome.clone(),
    };
    if row.event_id != candidate.event_id() {
        return Err(StoreError::Integrity(
            "private dependent-turn release found a forged resolution event id".to_string(),
        ));
    }
    Ok(row)
}

impl PersistentStore {
    /// Store one already-AEAD-sealed signed turn. Exact repeats are idempotent;
    /// a same-promise substitution is refused.
    pub fn arm_private_dependent_turn_v1(
        &self,
        promise_id: [u8; 32],
        signed_turn_hash: [u8; 32],
        sealed_signed_turn: Vec<u8>,
        expires_at_sequence_exclusive: u64,
    ) -> Result<bool> {
        let record = PrivateDependentTurnRecordV1 {
            promise_id,
            signed_turn_hash,
            expected_resolution_digest: private_dependent_ready_digest_v1(
                promise_id,
                signed_turn_hash,
            ),
            expires_at_sequence_exclusive,
            status: PrivateDependentTurnStatusV1::Armed,
            sealed_signed_turn,
        };
        record.validate(&promise_id)?;
        let bytes = canonical_bytes(&record)?;
        if bytes.len() > MAX_PRIVATE_DEPENDENT_ROW_BYTES {
            return Err(StoreError::Integrity(
                "private dependent-turn custody row exceeds its durable bound".to_string(),
            ));
        }

        let write = self.db.begin_write()?;
        {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            if let Some(existing) = table.get(&promise_id)? {
                let existing_bytes = existing.value();
                let _ = decode_record(existing_bytes, &promise_id)?;
                if existing_bytes == bytes.as_slice() {
                    return Ok(false);
                }
                return Err(StoreError::Integrity(
                    "private dependent-turn promise id already has different custody".to_string(),
                ));
            }
            if table.len()? as usize >= MAX_PRIVATE_DEPENDENT_TURNS {
                return Err(StoreError::Integrity(format!(
                    "private dependent-turn table is full (maximum {MAX_PRIVATE_DEPENDENT_TURNS})"
                )));
            }
            let mut total = 0usize;
            for entry in table.iter()? {
                let (key, value) = entry?;
                let _ = decode_record(value.value(), key.value())?;
                total = total.checked_add(value.value().len()).ok_or_else(|| {
                    StoreError::Integrity(
                        "private dependent-turn storage accounting overflow".to_string(),
                    )
                })?;
            }
            if total.saturating_add(bytes.len()) > MAX_PRIVATE_DEPENDENT_TOTAL_BYTES {
                return Err(StoreError::Integrity(format!(
                    "private dependent-turn custody exceeds {} byte total bound",
                    MAX_PRIVATE_DEPENDENT_TOTAL_BYTES
                )));
            }
            table.insert(&promise_id, bytes.as_slice())?;
        }
        write.commit()?;
        Ok(true)
    }

    /// Atomically and destructively release the private seal only when the
    /// named durable observer row is the canonical Ready event for this promise.
    pub fn claim_private_dependent_turn_v1(
        &self,
        promise_id: [u8; 32],
        ready_sequence: u64,
    ) -> Result<Option<ClaimedPrivateDependentTurnV1>> {
        let write = self.db.begin_write()?;
        let claimed = {
            let resolutions = write.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
            let resolution_bytes = resolutions.get(ready_sequence)?.ok_or_else(|| {
                StoreError::Integrity(
                    "private dependent-turn release requires a durable resolution row".to_string(),
                )
            })?;
            let resolution = decode_resolution(resolution_bytes.value(), ready_sequence)?;
            if resolution.pending_id != promise_id
                || resolution.outcome != PromiseResolutionKindV1::ReadyToExecute
            {
                return Err(StoreError::Integrity(
                    "private dependent-turn release row is not its promised ReadyToExecute"
                        .to_string(),
                ));
            }

            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let Some(current) = table.get(&promise_id)? else {
                return Ok(None);
            };
            let mut record = decode_record(current.value(), &promise_id)?;
            drop(current);
            if record.status != PrivateDependentTurnStatusV1::Armed {
                return Ok(None);
            }
            if ready_sequence >= record.expires_at_sequence_exclusive {
                record.status = PrivateDependentTurnStatusV1::Expired { ready_sequence };
                record.sealed_signed_turn.clear();
                let bytes = canonical_bytes(&record)?;
                table.insert(&promise_id, bytes.as_slice())?;
                None
            } else {
                let expected = private_dependent_ready_digest_v1(
                    resolution.pending_id,
                    record.signed_turn_hash,
                );
                if expected != record.expected_resolution_digest {
                    return Err(StoreError::Integrity(
                        "private dependent-turn Ready digest disagrees with custody".to_string(),
                    ));
                }
                let seal = core::mem::take(&mut record.sealed_signed_turn);
                record.status = PrivateDependentTurnStatusV1::Claimed {
                    ready_sequence,
                    event_id: resolution.event_id,
                };
                let bytes = canonical_bytes(&record)?;
                table.insert(&promise_id, bytes.as_slice())?;
                Some(ClaimedPrivateDependentTurnV1 {
                    promise_id,
                    signed_turn_hash: record.signed_turn_hash,
                    expected_resolution_digest: record.expected_resolution_digest,
                    ready_sequence,
                    event_id: resolution.event_id,
                    sealed_signed_turn: seal,
                })
            }
        };
        write.commit()?;
        Ok(claimed)
    }

    pub fn finish_private_dependent_turn_v1(
        &self,
        promise_id: [u8; 32],
        ready_sequence: u64,
        event_id: [u8; 32],
        outcome: PrivateDependentTurnFinishV1,
    ) -> Result<()> {
        let write = self.db.begin_write()?;
        {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let current = table.get(&promise_id)?.ok_or_else(|| {
                StoreError::Integrity("claimed private dependent turn is missing".to_string())
            })?;
            let mut record = decode_record(current.value(), &promise_id)?;
            drop(current);
            if record.status
                != (PrivateDependentTurnStatusV1::Claimed {
                    ready_sequence,
                    event_id,
                })
            {
                return Err(StoreError::Integrity(
                    "private dependent-turn finish does not match its durable claim".to_string(),
                ));
            }
            record.status = match outcome {
                PrivateDependentTurnFinishV1::Submitted { ingress_id } => {
                    PrivateDependentTurnStatusV1::Submitted {
                        ready_sequence,
                        event_id,
                        ingress_id,
                    }
                }
                PrivateDependentTurnFinishV1::Refused { reason } => {
                    if reason.len() > MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES {
                        return Err(StoreError::Integrity(
                            "private dependent-turn refusal text exceeds bound".to_string(),
                        ));
                    }
                    PrivateDependentTurnStatusV1::Refused {
                        ready_sequence,
                        event_id,
                        reason,
                    }
                }
            };
            let bytes = canonical_bytes(&record)?;
            table.insert(&promise_id, bytes.as_slice())?;
        }
        write.commit()?;
        Ok(())
    }

    /// Cancel only an unclaimed custody item. Once claimed, at-most-once release
    /// has begun and cancellation cannot race it back to Armed.
    pub fn cancel_private_dependent_turn_v1(&self, promise_id: [u8; 32]) -> Result<bool> {
        let write = self.db.begin_write()?;
        let cancelled = {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let Some(current) = table.get(&promise_id)? else {
                return Ok(false);
            };
            let mut record = decode_record(current.value(), &promise_id)?;
            drop(current);
            if record.status != PrivateDependentTurnStatusV1::Armed {
                false
            } else {
                record.status = PrivateDependentTurnStatusV1::Cancelled;
                record.sealed_signed_turn.clear();
                let bytes = canonical_bytes(&record)?;
                table.insert(&promise_id, bytes.as_slice())?;
                true
            }
        };
        write.commit()?;
        Ok(cancelled)
    }

    pub fn private_dependent_turn_status_v1(
        &self,
        promise_id: [u8; 32],
    ) -> Result<Option<PrivateDependentTurnSnapshotV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
        let Some(value) = table.get(&promise_id)? else {
            return Ok(None);
        };
        Ok(Some(decode_record(value.value(), &promise_id)?.snapshot()))
    }

    /// Bounded restart reconciliation surface. It exposes no sealed bytes.
    pub fn claimed_private_dependent_turns_v1(
        &self,
    ) -> Result<Vec<PrivateDependentTurnSnapshotV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
        let mut claimed = Vec::new();
        for entry in table.iter()? {
            let (key, value) = entry?;
            let record = decode_record(value.value(), key.value())?;
            if matches!(record.status, PrivateDependentTurnStatusV1::Claimed { .. }) {
                claimed.push(record.snapshot());
            }
        }
        Ok(claimed)
    }

    /// Explicit bounded-storage cleanup. Armed/Claimed records can never be
    /// forgotten through this API.
    pub fn forget_terminal_private_dependent_turn_v1(&self, promise_id: [u8; 32]) -> Result<bool> {
        let write = self.db.begin_write()?;
        let removed = {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let Some(value) = table.get(&promise_id)? else {
                return Ok(false);
            };
            let record = decode_record(value.value(), &promise_id)?;
            drop(value);
            if !record.status.is_terminal() {
                false
            } else {
                table.remove(&promise_id)?.is_some()
            }
        };
        write.commit()?;
        Ok(removed)
    }

    pub fn private_dependent_scheduler_cursor_v1(&self) -> Result<Option<u64>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::METADATA)?;
        Ok(table.get(CURSOR_META_KEY_V1)?.map(|value| value.value()))
    }

    pub fn advance_private_dependent_scheduler_cursor_v1(&self, sequence: u64) -> Result<()> {
        let write = self.db.begin_write()?;
        {
            let mut table = write.open_table(tables::METADATA)?;
            if table
                .get(CURSOR_META_KEY_V1)?
                .is_some_and(|current| current.value() >= sequence)
            {
                return Ok(());
            }
            table.insert(CURSOR_META_KEY_V1, sequence)?;
        }
        write.commit()?;
        Ok(())
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

    fn source(ordinal: u64, receipt_hash: [u8; 32]) -> crate::CommitRecord {
        crate::CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [ordinal as u8; 32],
            block_executed_up_to: ordinal,
            turn_hash: [0x41; 32],
            creator: [0x51; 32],
            receipt_hash,
            ledger_root: [0x61; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn commit_ready(store: &PersistentStore, promise_id: [u8; 32]) {
        let receipt_hash = [0x11; 32];
        let mut state = crate::FinalizedExecutorConsensusState::default();
        state.promise_resolutions = vec![PromiseResolutionCandidateV1 {
            source_commit_ordinal: 0,
            source_receipt_hash: receipt_hash,
            event_index: 0,
            pending_id: promise_id,
            outcome: PromiseResolutionKindV1::ReadyToExecute,
        }];
        store
            .commit_finalized_turn_with_executor_state(0, &source(0, receipt_hash), &[], &state)
            .unwrap();
    }

    #[test]
    fn durable_ready_destructively_claims_exactly_once() {
        let (_dir, store) = store();
        let promise = [7; 32];
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![9; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let first = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        assert_eq!(first.sealed_signed_turn, vec![9; 80]);
        assert!(
            store
                .claim_private_dependent_turn_v1(promise, 0)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn crash_after_claim_never_releases_again() {
        let (dir, store) = store();
        let promise = [8; 32];
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![3; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        drop(store);
        let reopened = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        assert!(
            reopened
                .claim_private_dependent_turn_v1(promise, 0)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            reopened
                .private_dependent_turn_status_v1(promise)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Claimed { .. }
        ));
    }

    #[test]
    fn wrong_promise_substitution_and_non_ready_release_fail_closed() {
        let (_dir, store) = store();
        let promise = [4; 32];
        let attacker = [5; 32];
        assert!(
            store
                .arm_private_dependent_turn_v1(promise, attacker, vec![1; 80], 10)
                .is_err()
        );
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![1; 80], 10)
            .unwrap();
        commit_ready(&store, attacker);
        assert!(store.claim_private_dependent_turn_v1(promise, 0).is_err());
        assert!(matches!(
            store
                .private_dependent_turn_status_v1(promise)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Armed
        ));
    }

    #[test]
    fn cancellation_and_sequence_expiry_destroy_private_seal() {
        let (_dir, store) = store();
        let cancelled = [2; 32];
        store
            .arm_private_dependent_turn_v1(cancelled, cancelled, vec![1; 80], 10)
            .unwrap();
        assert!(store.cancel_private_dependent_turn_v1(cancelled).unwrap());
        assert!(
            store
                .forget_terminal_private_dependent_turn_v1(cancelled)
                .unwrap()
        );

        let expired = [3; 32];
        store
            .arm_private_dependent_turn_v1(expired, expired, vec![1; 80], 0)
            .unwrap();
        commit_ready(&store, expired);
        assert!(
            store
                .claim_private_dependent_turn_v1(expired, 0)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            store
                .private_dependent_turn_status_v1(expired)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Expired { ready_sequence: 0 }
        ));
    }

    #[test]
    fn oversized_seal_and_mismatched_finish_are_refused() {
        let (_dir, store) = store();
        let promise = [6; 32];
        assert!(
            store
                .arm_private_dependent_turn_v1(
                    promise,
                    promise,
                    vec![0; MAX_PRIVATE_DEPENDENT_SEAL_BYTES + 1],
                    10,
                )
                .is_err()
        );
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![7; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let claim = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        assert!(
            store
                .finish_private_dependent_turn_v1(
                    promise,
                    claim.ready_sequence,
                    [0xff; 32],
                    PrivateDependentTurnFinishV1::Submitted {
                        ingress_id: [1; 32],
                    },
                )
                .is_err()
        );
    }

    #[test]
    fn exact_arm_is_idempotent_but_seal_substitution_is_refused() {
        let (_dir, store) = store();
        let promise = [0x72; 32];
        assert!(
            store
                .arm_private_dependent_turn_v1(promise, promise, vec![1; 80], 10)
                .unwrap()
        );
        assert!(
            !store
                .arm_private_dependent_turn_v1(promise, promise, vec![1; 80], 10)
                .unwrap()
        );
        assert!(
            store
                .arm_private_dependent_turn_v1(promise, promise, vec![2; 80], 10)
                .is_err()
        );
    }

    #[test]
    fn oversized_private_row_is_rejected_before_decode() {
        let (_dir, store) = store();
        let promise = [0x73; 32];
        let oversized = vec![0u8; MAX_PRIVATE_DEPENDENT_ROW_BYTES + 1];
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)
                .unwrap();
            table.insert(&promise, oversized.as_slice()).unwrap();
        }
        write.commit().unwrap();
        let error = store.private_dependent_turn_status_v1(promise).unwrap_err();
        assert!(error.to_string().contains("maximum"));
    }
}
