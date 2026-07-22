//! Capture and fail-closed reconstruction of executor-owned consensus state.
//!
//! Production executors are intentionally short-lived. These helpers keep the
//! note-create, revocation, inbound-bridge, rate-limit, and factory-registry
//! frontiers continuous across that constructor boundary and process restart.
//! They build each complete successor off to the side and publish only after
//! every durable record has validated.

use dregg_persist::{
    ExecutorAccumulatorSnapshot, ExecutorNoteCommitmentRecord, ExecutorRevocationRecord,
    FinalizedExecutorConsensusState, PersistentStore, ReactiveNullifierCasV1,
    ReactiveRegistryCasV1,
};
use dregg_turn::TurnExecutor;

/// Domain-separated predecessor commitments captured before isolated execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ReactivePredecessors {
    pub registry: [u8; 32],
    pub nullifiers: [u8; 32],
}

/// Canonical successor images captured after isolated execution and resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReactiveSuccessors {
    pub registry: Vec<u8>,
    pub nullifiers: Vec<[u8; 32]>,
}

/// Complete pre-execution image needed to make sparse snapshots and CAS
/// predecessors explicit at the finalized transaction boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExecutorConsensusPredecessors {
    rate_limits: Vec<u8>,
    factory_registry: Vec<u8>,
    pub reactive: ReactivePredecessors,
}

pub(crate) fn capture_executor_consensus_predecessors(
    executor: &TurnExecutor,
) -> Result<ExecutorConsensusPredecessors, String> {
    Ok(ExecutorConsensusPredecessors {
        rate_limits: capture_executor_rate_limits(executor)?,
        factory_registry: capture_executor_factory_registry(executor)?,
        reactive: capture_reactive_predecessors(executor)?,
    })
}

/// Capture one complete post-execution side-state image for the redb commit.
/// Policy snapshots stay sparse; the two reactive domains always carry exact
/// predecessor/successor pairs.
pub(crate) fn capture_finalized_executor_consensus_state(
    executor: &TurnExecutor,
    predecessor: &ExecutorConsensusPredecessors,
) -> Result<FinalizedExecutorConsensusState, String> {
    let rate_limits = capture_executor_rate_limits(executor)?;
    let factory_registry = capture_executor_factory_registry(executor)?;
    let reactive = capture_reactive_successors(executor)?;
    Ok(FinalizedExecutorConsensusState {
        accumulators: capture_executor_accumulators(executor)?,
        rate_limit_snapshot: (rate_limits != predecessor.rate_limits).then_some(rate_limits),
        factory_registry_snapshot: (factory_registry != predecessor.factory_registry)
            .then_some(factory_registry),
        reactive_registry: ReactiveRegistryCasV1::new(
            predecessor.reactive.registry,
            reactive.registry,
        ),
        reactive_nullifiers: ReactiveNullifierCasV1::new(
            predecessor.reactive.nullifiers,
            reactive.nullifiers,
        ),
        promise_resolutions: Vec::new(),
    })
}

pub(crate) fn capture_reactive_predecessors(
    executor: &TurnExecutor,
) -> Result<ReactivePredecessors, String> {
    Ok(ReactivePredecessors {
        registry: executor
            .reactive_registry_commitment()
            .map_err(|error| format!("executor pending registry is malformed: {error}"))?,
        nullifiers: executor.reactive_nullifier_commitment(),
    })
}

pub(crate) fn capture_reactive_successors(
    executor: &TurnExecutor,
) -> Result<ReactiveSuccessors, String> {
    Ok(ReactiveSuccessors {
        registry: executor
            .reactive_registry_canonical_bytes()
            .map_err(|error| format!("executor pending registry is malformed: {error}"))?,
        nullifiers: executor.reactive_nullifier_keys(),
    })
}

/// Publish only the durable outcome of promise resolution to operator logs.
///
/// `ReadyToExecute` deliberately remains informational: it contains an
/// unsigned `Turn` and therefore cannot be inserted into the signed consensus
/// queue. FOLLOW-UP: add a typed durable PromiseResolution query/NodeEvent
/// surface so Discord, Telegram, and web clients can notify without treating
/// transient candidate events as authority.
pub(crate) fn trace_durable_resolution_events(events: &[dregg_turn::ResolutionEvent]) {
    for event in events {
        match event {
            dregg_turn::ResolutionEvent::Resolved { turn_hash, .. } => {
                tracing::info!(
                    pending_id = %dregg_types::hex_encode(turn_hash),
                    outcome = "resolved",
                    "durable promise resolution published"
                );
            }
            dregg_turn::ResolutionEvent::ReadyToExecute { turn_hash, .. } => {
                tracing::info!(
                    pending_id = %dregg_types::hex_encode(turn_hash),
                    outcome = "ready_to_execute",
                    "durable promise resolution published; unsigned dependent is not auto-executed"
                );
            }
            dregg_turn::ResolutionEvent::Broken { turn_hash, reason } => {
                tracing::warn!(
                    pending_id = %dregg_types::hex_encode(turn_hash),
                    outcome = "broken",
                    reason = %reason,
                    "durable promise resolution published"
                );
            }
        }
    }
}

/// Restore both React authority images only after each has decoded completely.
pub(crate) fn restore_executor_reactive_state(
    executor: &TurnExecutor,
    store: &PersistentStore,
) -> Result<(), String> {
    let registry_bytes = store
        .load_latest_reactive_registry_snapshot_bytes()
        .map_err(|error| format!("could not load durable pending registry: {error}"))?;
    let registry = dregg_turn::PendingTurnRegistry::from_canonical_bytes(&registry_bytes)
        .map_err(|error| format!("durable pending registry is malformed: {error}"))?;
    let nullifier_keys = store
        .load_reactive_nullifier_keys()
        .map_err(|error| format!("could not load durable React replay gate: {error}"))?;
    let nullifiers = dregg_turn::ReactiveNullifierSet::from_canonical_keys(&nullifier_keys)
        .map_err(|error| format!("durable React replay gate is malformed: {error}"))?;

    executor.set_reactive_registry(registry);
    executor.set_reactive_nullifiers(nullifiers);
    Ok(())
}

/// Capture the exact canonical factory descriptor/quota frontier.
pub(crate) fn capture_executor_factory_registry(
    executor: &TurnExecutor,
) -> Result<Vec<u8>, String> {
    let registry = executor
        .factory_registry
        .try_borrow()
        .map_err(|_| "executor factory registry is already mutably borrowed".to_string())?;
    registry
        .snapshot()
        .to_canonical_bytes()
        .map_err(|error| format!("executor factory-registry snapshot is malformed: {error}"))
}

fn restore_executor_factory_registry_bytes(
    executor: &TurnExecutor,
    bytes: Option<&[u8]>,
) -> Result<(), String> {
    let snapshot = match bytes {
        Some(bytes) => dregg_cell::factory::FactoryRegistrySnapshot::from_canonical_bytes(bytes)
            .map_err(|error| format!("durable factory-registry state is malformed: {error}"))?,
        None => dregg_cell::factory::FactoryRegistrySnapshot::default(),
    };
    executor
        .factory_registry
        .try_borrow_mut()
        .map_err(|_| "executor factory registry is already borrowed".to_string())?
        .restore_snapshot(&snapshot)
        .map_err(|error| format!("could not seed durable factory-registry state: {error}"))
}

/// Restore the latest durable factory registry into a fresh executor.
///
/// Absence is the canonical empty registry. Present bytes must survive the
/// strict cell-layer codec before the live `RefCell` is borrowed mutably, so a
/// corrupt image cannot partially replace descriptors or quota counters.
pub(crate) fn restore_executor_factory_registry(
    executor: &TurnExecutor,
    store: &PersistentStore,
) -> Result<(), String> {
    let bytes = store
        .load_latest_factory_registry_snapshot_bytes()
        .map_err(|error| format!("could not load durable factory-registry state: {error}"))?;
    restore_executor_factory_registry_bytes(executor, bytes.as_deref())
}

/// Capture the strict, versioned post-execution rate frontier.
///
/// Persistence treats these bytes opaquely to avoid a `persist -> turn` crate
/// cycle.  Encoding at the node boundary ensures only the canonical form can be
/// welded into a finalized transaction.
pub(crate) fn capture_executor_rate_limits(executor: &TurnExecutor) -> Result<Vec<u8>, String> {
    executor
        .rate_limit_state_snapshot()
        .to_canonical_bytes()
        .map_err(|error| format!("executor rate-limit snapshot is malformed: {error}"))
}

/// Restore the latest durable rate frontier into a fresh executor.
///
/// A missing sparse replacement is the canonical empty state.  Present bytes
/// must decode canonically before either map is replaced; corrupt/unknown data
/// is a store-integrity failure, never an empty fallback.
pub(crate) fn restore_executor_rate_limits(
    executor: &TurnExecutor,
    store: &PersistentStore,
) -> Result<(), String> {
    let snapshot = match store
        .load_latest_rate_limit_snapshot_bytes()
        .map_err(|error| format!("could not load durable rate-limit state: {error}"))?
    {
        Some(bytes) => {
            dregg_turn::executor::RateLimitStateSnapshot::from_canonical_bytes(&bytes)
                .map_err(|error| format!("durable rate-limit state is malformed: {error}"))?
        }
        None => dregg_turn::executor::RateLimitStateSnapshot::default(),
    };
    executor
        .restore_rate_limit_state(&snapshot)
        .map_err(|error| format!("could not seed durable rate-limit state: {error}"))
}

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
    use dregg_cell::{CellMode, FactoryDescriptor, note::NoteCommitment};
    use dregg_persist::CommitRecord;

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
        let consensus_predecessor = capture_executor_consensus_predecessors(&source).unwrap();
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
        source
            .rate_limit_counters
            .lock()
            .unwrap()
            .insert((dregg_cell::CellId([4; 32]), [5; 32], 6), 7);
        source.rate_limit_sum_counters.lock().unwrap().insert(
            (dregg_cell::CellId([8; 32]), 9, 10),
            u64::from(u32::MAX) + 11,
        );
        source.set_reactive_nullifiers(
            dregg_turn::ReactiveNullifierSet::from_canonical_keys(&[[0x71; 32]]).unwrap(),
        );
        let factory_vk = {
            let mut factories = source.factory_registry.borrow_mut();
            let factory_vk = factories.deploy(FactoryDescriptor {
                factory_vk: [0xf1; 32],
                child_program_vk: Some([0xc1; 32]),
                child_vk_strategy: None,
                allowed_cap_templates: Vec::new(),
                field_constraints: Vec::new(),
                state_constraints: Vec::new(),
                default_mode: CellMode::Hosted,
                creation_budget: Some(2),
            });
            factories.record_creation(&factory_vk).unwrap();
            factory_vk
        };
        let state =
            capture_finalized_executor_consensus_state(&source, &consensus_predecessor).unwrap();
        let reactive_successors = capture_reactive_successors(&source).unwrap();
        let source_commitment_root = source.note_commitments.lock().unwrap().root8();
        let source_revocation_root = source.note_revoked.lock().unwrap().root8();

        {
            let store = PersistentStore::open(&path).unwrap();
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
        restore_executor_rate_limits(&restored, &store).unwrap();
        restore_executor_factory_registry(&restored, &store).unwrap();
        restore_executor_reactive_state(&restored, &store).unwrap();
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
        assert_eq!(
            restored.rate_limit_state_snapshot(),
            source.rate_limit_state_snapshot()
        );
        assert_eq!(
            restored.factory_registry.borrow().snapshot(),
            source.factory_registry.borrow().snapshot()
        );
        assert_eq!(
            capture_reactive_successors(&restored).unwrap(),
            reactive_successors
        );
        {
            let mut factories = restored.factory_registry.borrow_mut();
            assert_eq!(factories.get(&factory_vk).unwrap().creation_budget, Some(2));
            factories.record_creation(&factory_vk).unwrap();
            assert!(factories.record_creation(&factory_vk).is_err());
        }
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

    #[test]
    fn malformed_rate_snapshot_refuses_without_partial_seed() {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("bad-rate.redb")).unwrap();
        let state = FinalizedExecutorConsensusState {
            rate_limit_snapshot: Some(b"not-a-canonical-rate-snapshot".to_vec()),
            ..Default::default()
        };
        store
            .commit_finalized_turn_with_executor_state(
                0,
                &record(dregg_persist::canonical_ledger_root(
                    &dregg_cell::Ledger::new(),
                )),
                &[],
                &state,
            )
            .unwrap();

        let executor = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        executor
            .rate_limit_counters
            .lock()
            .unwrap()
            .insert((dregg_cell::CellId([21; 32]), [22; 32], 23), 24);
        let before = executor.rate_limit_state_snapshot();

        assert!(restore_executor_rate_limits(&executor, &store).is_err());
        assert_eq!(executor.rate_limit_state_snapshot(), before);
    }

    #[test]
    fn malformed_factory_snapshot_refuses_without_partial_seed() {
        let executor = TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        executor
            .factory_registry
            .borrow_mut()
            .deploy(FactoryDescriptor {
                factory_vk: [0xaa; 32],
                child_program_vk: None,
                child_vk_strategy: None,
                allowed_cap_templates: Vec::new(),
                field_constraints: Vec::new(),
                state_constraints: Vec::new(),
                default_mode: CellMode::Sovereign,
                creation_budget: Some(9),
            });
        let before = executor.factory_registry.borrow().snapshot();

        assert!(
            restore_executor_factory_registry_bytes(
                &executor,
                Some(b"not-a-canonical-factory-registry")
            )
            .is_err()
        );
        assert_eq!(executor.factory_registry.borrow().snapshot(), before);
    }
}
