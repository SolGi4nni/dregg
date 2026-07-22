//! Capture and fail-closed reconstruction of executor-owned accumulators.
//!
//! Production executors are intentionally short-lived. These helpers keep the
//! note-create, revocation, and inbound-bridge frontiers continuous across that
//! constructor boundary and process restart. They build the complete successor
//! off to the side and publish only after every durable record has validated.

use dregg_persist::{
    ExecutorAccumulatorSnapshot, ExecutorNoteCommitmentRecord, ExecutorRevocationRecord,
    PersistentStore,
};
use dregg_turn::TurnExecutor;

pub(crate) fn capture_executor_accumulators(
    executor: &TurnExecutor,
) -> Result<ExecutorAccumulatorSnapshot, String> {
    let commitments = executor
        .note_commitments
        .lock()
        .map_err(|_| "executor note-commitment mutex is poisoned".to_string())?;
    let note_commitments = commitments
        .iter_in_append_order()
        .map(|(commitment, value, seq)| ExecutorNoteCommitmentRecord {
            commitment,
            value,
            seq,
        })
        .collect();
    drop(commitments);

    let revoked = executor
        .note_revoked
        .lock()
        .map_err(|_| "executor revocation mutex is poisoned".to_string())?;
    let revocations = revoked
        .iter_in_append_order()
        .map(|(key, height, seq)| ExecutorRevocationRecord { key, height, seq })
        .collect();
    drop(revoked);

    let bridged = executor
        .bridged_nullifiers
        .lock()
        .map_err(|_| "executor bridged-nullifier mutex is poisoned".to_string())?;
    let bridged_nullifiers = bridged.iter().copied().collect();
    drop(bridged);

    let snapshot = ExecutorAccumulatorSnapshot {
        note_commitments,
        revocations,
        bridged_nullifiers,
    };
    snapshot
        .validate_canonical()
        .map_err(|error| format!("executor accumulator snapshot is malformed: {error}"))?;
    Ok(snapshot)
}

pub(crate) fn restore_executor_accumulators(
    executor: &TurnExecutor,
    store: &PersistentStore,
) -> Result<(), String> {
    let snapshot = store
        .load_executor_accumulator_snapshot()
        .map_err(|error| format!("could not load durable executor accumulators: {error}"))?;

    // Construct and validate every successor before acquiring a mutable guard.
    // A corrupt revocation/bridge suffix therefore cannot leave commitments
    // partially installed on the fresh executor.
    let commitments = dregg_cell::commitment_set::CommitmentSet::from_records(
        snapshot
            .note_commitments
            .iter()
            .map(|record| (record.commitment, record.value, record.seq)),
    )
    .map_err(|error| format!("durable note-commitment sequence is malformed: {error}"))?;
    let revoked = dregg_cell::revoked_set::RevokedSet::from_records(
        snapshot
            .revocations
            .iter()
            .map(|record| (record.key, record.height, record.seq)),
    )
    .map_err(|error| format!("durable revocation sequence is malformed: {error}"))?;
    let mut bridged = dregg_cell_crypto::note_bridge::BridgedNullifierSet::new();
    for nullifier in snapshot.bridged_nullifiers {
        bridged
            .insert(nullifier)
            .map_err(|error| format!("durable bridged-nullifier gate is malformed: {error}"))?;
    }

    // Acquire every guard before publishing any field. The executor is fresh,
    // but this also makes mutex poisoning a no-partial-seed failure.
    let mut commitment_guard = executor
        .note_commitments
        .lock()
        .map_err(|_| "executor note-commitment mutex is poisoned".to_string())?;
    let mut revoked_guard = executor
        .note_revoked
        .lock()
        .map_err(|_| "executor revocation mutex is poisoned".to_string())?;
    let mut bridged_guard = executor
        .bridged_nullifiers
        .lock()
        .map_err(|_| "executor bridged-nullifier mutex is poisoned".to_string())?;
    *commitment_guard = commitments;
    *revoked_guard = revoked;
    *bridged_guard = bridged;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::note::NoteCommitment;
    use dregg_persist::{CommitRecord, FinalizedExecutorConsensusState};

    fn record(root: [u8; 32]) -> CommitRecord {
        CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [11; 32],
            block_executed_up_to: 1,
            turn_hash: [12; 32],
            creator: [13; 32],
            receipt_hash: [14; 32],
            ledger_root: root,
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    #[test]
    fn restart_restores_exact_roots_sequences_and_refusal_gates() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("executor-accumulators.redb");
        let source = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        source
            .note_commitments
            .lock()
            .unwrap()
            .insert(NoteCommitment([1; 32]), 101)
            .unwrap();
        source
            .note_revoked
            .lock()
            .unwrap()
            .insert([2; 32], 17)
            .unwrap();
        source
            .bridged_nullifiers
            .lock()
            .unwrap()
            .insert([3; 32])
            .unwrap();
        let snapshot = capture_executor_accumulators(&source).unwrap();
        let source_commitment_root = source.note_commitments.lock().unwrap().root8();
        let source_revocation_root = source.note_revoked.lock().unwrap().root8();

        {
            let store = PersistentStore::open(&path).unwrap();
            let state = FinalizedExecutorConsensusState {
                accumulators: snapshot,
                rate_limit_snapshot: None,
            };
            store
                .commit_finalized_turn_with_executor_state(
                    0,
                    &record(dregg_persist::canonical_ledger_root(
                        &dregg_cell::Ledger::new(),
                    )),
                    &[[1; 32]],
                    &state,
                )
                .unwrap();
        }

        let store = PersistentStore::open(&path).unwrap();
        let restored = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        restore_executor_accumulators(&restored, &store).unwrap();
        assert_eq!(
            restored.note_commitments.lock().unwrap().root8(),
            source_commitment_root
        );
        assert_eq!(
            restored.note_revoked.lock().unwrap().root8(),
            source_revocation_root
        );
        assert!(
            restored
                .note_commitments
                .lock()
                .unwrap()
                .insert(NoteCommitment([1; 32]), 101)
                .is_err()
        );
        assert!(
            restored
                .note_revoked
                .lock()
                .unwrap()
                .insert([2; 32], 18)
                .is_err()
        );
        assert!(
            restored
                .bridged_nullifiers
                .lock()
                .unwrap()
                .insert([3; 32])
                .is_err()
        );
        let next = NoteCommitment([9; 32]);
        restored
            .note_commitments
            .lock()
            .unwrap()
            .insert(next, 102)
            .unwrap();
        assert_eq!(
            restored.note_commitments.lock().unwrap().seq_of(&next),
            Some(1)
        );
        restored
            .note_revoked
            .lock()
            .unwrap()
            .insert([8; 32], 19)
            .unwrap();
        assert_eq!(
            restored.note_revoked.lock().unwrap().seq_of(&[8; 32]),
            Some(1)
        );
    }

    #[test]
    fn malformed_store_does_not_partially_seed_fresh_executor() {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("legacy.redb")).unwrap();
        store
            .store_note_commitment(&NoteCommitment([7; 32]))
            .unwrap();

        let executor = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        executor
            .note_commitments
            .lock()
            .unwrap()
            .insert(NoteCommitment([99; 32]), 5)
            .unwrap();
        executor
            .note_revoked
            .lock()
            .unwrap()
            .insert([98; 32], 6)
            .unwrap();
        executor
            .bridged_nullifiers
            .lock()
            .unwrap()
            .insert([97; 32])
            .unwrap();

        assert!(restore_executor_accumulators(&executor, &store).is_err());
        assert!(
            executor
                .note_commitments
                .lock()
                .unwrap()
                .contains(&NoteCommitment([99; 32]))
        );
        assert!(executor.note_revoked.lock().unwrap().contains(&[98; 32]));
        assert!(
            executor
                .bridged_nullifiers
                .lock()
                .unwrap()
                .contains(&[97; 32])
        );
    }
}
