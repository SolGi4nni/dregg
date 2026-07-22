//! Non-live executor state machine for the exact FNSP-v3 nullifier accumulator.
//!
//! This module is intentionally additive.  Nothing in `apply`, `execute`, persistence, or node
//! setup calls it yet, so the deployed FNSP-v2 route remains unchanged.  It exists to make the
//! eventual cutover transactional instead of asking callers to coordinate a proof candidate and
//! an [`ExactNullifierAafi`] mutation by convention.
//!
//! The protocol is a small optimistic transaction:
//!
//! 1. [`ExactFnspV3ExecutorState::prepare_append`] constructs and independently validates a
//!    complete exact AAFI witness.  The owned state is not mutated.
//! 2. Expensive proof construction may happen without holding the executor mutex.
//! 3. [`ExactFnspV3ExecutorState::compare_and_commit`] compares the typed prior-state token with
//!    the state now under the mutex, revalidates the witness, and invokes AAFI's transactional
//!    O(depth) apply only after every comparison succeeds.
//!
//! Thus an intervening append makes an old candidate stale, and every error path preserves both
//! the accumulator and its canonical durable-record image.  Proof verification and durable
//! persistence still have to be composed around this seam before it can become live authority.
//! In particular, the node currently constructs separate submit/verify executors; this mutex
//! serializes one executor instance only.  Live promotion must seed each instance from durable
//! append records and use a store-level compare-and-swap/finalization transaction (or one shared
//! node-global exact state) to arbitrate candidates prepared by different executor instances.

use std::error::Error;
use std::fmt;

use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactAafiError, ExactAafiWitness, ExactAppendRecord, ExactNullifierAafi,
    ValidatedExactAafiTransition, validate_exact_aafi_witness,
};

use super::TurnExecutor;

/// Typed compare-and-commit token for one exact-nullifier prior state.
///
/// Its constructor and fields are private: callers can retain a token returned by preparation,
/// but cannot assemble an alleged prior state from unrelated root/count/generation components.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV3StateToken {
    generation: u64,
    prior_root: Digest8,
    prior_count: u64,
    prior_fns3: Digest8,
}

impl ExactFnspV3StateToken {
    pub fn generation(self) -> u64 {
        self.generation
    }

    pub fn prior_root(self) -> Digest8 {
        self.prior_root
    }

    pub fn prior_count(self) -> u64 {
        self.prior_count
    }

    pub fn prior_fns3(self) -> Digest8 {
        self.prior_fns3
    }
}

/// Prepared, non-mutating candidate for one exact FNSP-v3 nullifier append.
///
/// The transition internals remain private so a caller cannot substitute a witness, append
/// record, or successor anchor after preparation. Read-only accessors expose what the proof
/// producer needs; a durable writer must wait for [`CommittedExactFnspV3Append`] rather than
/// persisting this speculative record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedExactFnspV3Append {
    prior: ExactFnspV3StateToken,
    append_record: ExactAppendRecord,
    witness: ExactAafiWitness,
    validated: ValidatedExactAafiTransition,
    successor_root: Digest8,
    successor_count: u64,
    successor_fns3: Digest8,
}

impl PreparedExactFnspV3Append {
    pub fn prior(&self) -> ExactFnspV3StateToken {
        self.prior
    }

    pub fn append_record(&self) -> ExactAppendRecord {
        self.append_record
    }

    pub fn witness(&self) -> &ExactAafiWitness {
        &self.witness
    }

    pub fn validated(&self) -> &ValidatedExactAafiTransition {
        &self.validated
    }

    pub fn successor_root(&self) -> Digest8 {
        self.successor_root
    }

    pub fn successor_count(&self) -> u64 {
        self.successor_count
    }

    pub fn successor_fns3(&self) -> Digest8 {
        self.successor_fns3
    }
}

/// Receipt for a successful in-memory exact-state commit.
///
/// Persistence is deliberately outside this type.  The caller can durably write
/// [`Self::append_record`] and seed a restart with
/// [`ExactFnspV3ExecutorState::from_append_records`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommittedExactFnspV3Append {
    append_record: ExactAppendRecord,
    head: ExactFnspV3StateToken,
}

impl CommittedExactFnspV3Append {
    pub fn append_record(self) -> ExactAppendRecord {
        self.append_record
    }

    pub fn head(self) -> ExactFnspV3StateToken {
        self.head
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFnspV3StateError {
    Accumulator(ExactAafiError),
    StaleGeneration { prepared: u64, current: u64 },
    PriorRootMismatch,
    PriorCountMismatch,
    PriorFns3Mismatch,
    CandidateMismatch(&'static str),
    AppendRecordCapacity,
    GenerationOverflow,
    MutexPoisoned,
}

impl fmt::Display for ExactFnspV3StateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accumulator(error) => write!(f, "exact AAFI refused transition: {error}"),
            Self::StaleGeneration { prepared, current } => write!(
                f,
                "exact FNSP-v3 candidate generation {prepared} is stale; current generation is {current}"
            ),
            Self::PriorRootMismatch => {
                write!(f, "exact FNSP-v3 candidate prior root is not current")
            }
            Self::PriorCountMismatch => {
                write!(f, "exact FNSP-v3 candidate prior count is not current")
            }
            Self::PriorFns3Mismatch => {
                write!(f, "exact FNSP-v3 candidate prior FNS3 is not current")
            }
            Self::CandidateMismatch(which) => {
                write!(f, "exact FNSP-v3 prepared candidate mismatch: {which}")
            }
            Self::AppendRecordCapacity => {
                write!(f, "exact FNSP-v3 append-record capacity allocation failed")
            }
            Self::GenerationOverflow => write!(f, "exact FNSP-v3 generation overflow"),
            Self::MutexPoisoned => write!(f, "exact FNSP-v3 executor mutex is poisoned"),
        }
    }
}

impl TurnExecutor {
    /// Snapshot the typed exact-nullifier head under the executor-owned mutex.
    pub fn exact_fnsp_v3_head(&self) -> Result<ExactFnspV3StateToken, ExactFnspV3StateError> {
        self.exact_fnsp_v3_state
            .lock()
            .map_err(|_| ExactFnspV3StateError::MutexPoisoned)
            .map(|state| state.head())
    }

    /// Snapshot the canonical durable record image under the executor-owned mutex.
    ///
    /// The clone is intentional at this persistence boundary: it lets a writer release the
    /// in-memory authority lock before filesystem/database work. Normal append preparation and
    /// commit remain O(depth) and do not clone the accumulator.
    pub fn exact_fnsp_v3_append_records(
        &self,
    ) -> Result<Vec<ExactAppendRecord>, ExactFnspV3StateError> {
        self.exact_fnsp_v3_state
            .lock()
            .map_err(|_| ExactFnspV3StateError::MutexPoisoned)
            .map(|state| state.append_records().to_vec())
    }

    /// Prepare without retaining the executor lock during later proof construction.
    pub fn prepare_exact_fnsp_v3_append(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> Result<PreparedExactFnspV3Append, ExactFnspV3StateError> {
        self.exact_fnsp_v3_state
            .lock()
            .map_err(|_| ExactFnspV3StateError::MutexPoisoned)?
            .prepare_append(raw, value)
    }

    /// Reacquire the executor lock and compare-and-commit one previously prepared candidate.
    pub fn compare_and_commit_exact_fnsp_v3_append(
        &self,
        prepared: PreparedExactFnspV3Append,
    ) -> Result<CommittedExactFnspV3Append, ExactFnspV3StateError> {
        self.exact_fnsp_v3_state
            .lock()
            .map_err(|_| ExactFnspV3StateError::MutexPoisoned)?
            .compare_and_commit(prepared)
    }
}

impl Error for ExactFnspV3StateError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Accumulator(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ExactAafiError> for ExactFnspV3StateError {
    fn from(value: ExactAafiError) -> Self {
        Self::Accumulator(value)
    }
}

/// Executor-owned exact accumulator plus its canonical durable append-record image.
///
/// `TurnExecutor` stores this type under one mutex.  Methods require `&mut self`, making the
/// comparison and final swap indivisible while that guard is held.  The state is currently
/// unreachable from turn dispatch and therefore carries no live consensus authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV3ExecutorState {
    accumulator: ExactNullifierAafi,
    append_records: Vec<ExactAppendRecord>,
    generation: u64,
}

impl Default for ExactFnspV3ExecutorState {
    fn default() -> Self {
        Self::new()
    }
}

impl ExactFnspV3ExecutorState {
    /// Canonical BOT-only genesis.  Its count is one and it contains zero durable REAL records.
    pub fn new() -> Self {
        Self {
            accumulator: ExactNullifierAafi::new(),
            append_records: Vec::new(),
            generation: 0,
        }
    }

    /// Rebuild from durable zero-based append records in arbitrary storage iteration order.
    ///
    /// The accumulator validates dense sequencing and uniqueness.  The retained image is sorted
    /// by sequence so [`Self::append_records`] is immediately suitable for deterministic replay.
    pub fn from_append_records(
        records: impl IntoIterator<Item = ExactAppendRecord>,
    ) -> Result<Self, ExactFnspV3StateError> {
        let mut append_records: Vec<_> = records.into_iter().collect();
        let accumulator = ExactNullifierAafi::from_append_records(append_records.iter().copied())?;
        append_records.sort_unstable_by_key(|record| record.seq);
        let generation = u64::try_from(append_records.len())
            .map_err(|_| ExactFnspV3StateError::GenerationOverflow)?;
        Ok(Self {
            accumulator,
            append_records,
            generation,
        })
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn root(&self) -> Digest8 {
        self.accumulator.root()
    }

    /// Exact occupied-leaf count, including the permanent BOT leaf.
    pub fn count(&self) -> u64 {
        self.accumulator.count()
    }

    pub fn fns3(&self) -> Digest8 {
        self.accumulator.state_commit()
    }

    pub fn append_records(&self) -> &[ExactAppendRecord] {
        &self.append_records
    }

    pub fn head(&self) -> ExactFnspV3StateToken {
        ExactFnspV3StateToken {
            generation: self.generation,
            prior_root: self.root(),
            prior_count: self.count(),
            prior_fns3: self.fns3(),
        }
    }

    /// Prepare and independently validate one append without mutating the owned state.
    pub fn prepare_append(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> Result<PreparedExactFnspV3Append, ExactFnspV3StateError> {
        let prior = self.head();
        let witness = self.accumulator.prepare_insert(raw, value)?;
        let validated = validate_exact_aafi_witness(&witness)?;
        let append_record = ExactAppendRecord {
            // Count includes BOT; durable REAL sequence zero corresponds to physical slot one.
            seq: prior.prior_count.checked_sub(1).ok_or(
                ExactFnspV3StateError::CandidateMismatch("canonical BOT count underflow"),
            )?,
            raw,
            value,
        };

        if validated.inserted_raw() != append_record.raw
            || validated.inserted_value() != append_record.value
            || validated.prior_root() != prior.prior_root
            || validated.prior_count() != prior.prior_count
            || witness.prior_state_commit != prior.prior_fns3
            || validated.successor_root() != witness.successor_root
            || validated.successor_count() != witness.successor_count
        {
            return Err(ExactFnspV3StateError::CandidateMismatch(
                "preparation replay anchors",
            ));
        }
        let successor_root = witness.successor_root;
        let successor_count = witness.successor_count;
        let successor_fns3 = witness.successor_state_commit;

        Ok(PreparedExactFnspV3Append {
            prior,
            append_record,
            witness,
            validated,
            successor_root,
            successor_count,
            successor_fns3,
        })
    }

    /// Compare a prepared prior-state token and atomically commit its independently replayed
    /// candidate in O(depth), without cloning the accumulator's historical maps.
    ///
    /// Every fallible operation happens against locals.  `self` changes only after the token,
    /// record, semantic transition, witness replay, successor anchors, and next generation have
    /// all been checked.
    pub fn compare_and_commit(
        &mut self,
        prepared: PreparedExactFnspV3Append,
    ) -> Result<CommittedExactFnspV3Append, ExactFnspV3StateError> {
        let current = self.head();
        if prepared.prior.generation != current.generation {
            return Err(ExactFnspV3StateError::StaleGeneration {
                prepared: prepared.prior.generation,
                current: current.generation,
            });
        }
        if prepared.prior.prior_root != current.prior_root {
            return Err(ExactFnspV3StateError::PriorRootMismatch);
        }
        if prepared.prior.prior_count != current.prior_count {
            return Err(ExactFnspV3StateError::PriorCountMismatch);
        }
        if prepared.prior.prior_fns3 != current.prior_fns3 {
            return Err(ExactFnspV3StateError::PriorFns3Mismatch);
        }

        let expected_seq =
            current
                .prior_count
                .checked_sub(1)
                .ok_or(ExactFnspV3StateError::CandidateMismatch(
                    "canonical BOT count underflow",
                ))?;
        if prepared.append_record.seq != expected_seq
            || prepared.validated.inserted_raw() != prepared.append_record.raw
            || prepared.validated.inserted_value() != prepared.append_record.value
            || prepared.validated.prior_root() != current.prior_root
            || prepared.validated.prior_count() != current.prior_count
            || prepared.witness.prior_state_commit != current.prior_fns3
        {
            return Err(ExactFnspV3StateError::CandidateMismatch(
                "prior transition or append record",
            ));
        }

        let independently_validated = validate_exact_aafi_witness(&prepared.witness)?;
        if independently_validated != prepared.validated
            || prepared.witness.successor_root != prepared.successor_root
            || prepared.witness.successor_count != prepared.successor_count
            || prepared.witness.successor_state_commit != prepared.successor_fns3
        {
            return Err(ExactFnspV3StateError::CandidateMismatch(
                "independent successor replay",
            ));
        }
        let next_generation = self
            .generation
            .checked_add(1)
            .ok_or(ExactFnspV3StateError::GenerationOverflow)?;
        self.append_records
            .try_reserve(1)
            .map_err(|_| ExactFnspV3StateError::AppendRecordCapacity)?;

        // `ExactNullifierAafi::apply_witness` checks every runtime/root/path invariant before its
        // O(depth) overlays mutate state.  No recoverable operation follows a successful apply:
        // the Vec capacity and generation were prepared above, so push + scalar assignment are
        // the commit point under the executor mutex.
        let committed_validated = self.accumulator.apply_witness(&prepared.witness)?;
        assert_eq!(committed_validated, prepared.validated);
        let next_head = ExactFnspV3StateToken {
            generation: next_generation,
            prior_root: self.accumulator.root(),
            prior_count: self.accumulator.count(),
            prior_fns3: self.accumulator.state_commit(),
        };

        // Commit point. No recoverable operation follows these assignments.
        self.append_records.push(prepared.append_record);
        self.generation = next_generation;

        Ok(CommittedExactFnspV3Append {
            append_record: prepared.append_record,
            head: next_head,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::ComputronCosts;

    fn raw(first: u8) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0] = first;
        out
    }

    #[test]
    fn exact_fnsp_v3_prepare_is_non_mutating_and_duplicate_refuses() {
        let mut state = ExactFnspV3ExecutorState::new();
        let before = state.clone();
        let prepared = state.prepare_append(raw(7), 70).expect("prepare");
        assert_eq!(state, before, "preparation must not mutate authority");
        let committed = state.compare_and_commit(prepared).expect("commit");
        assert_eq!(committed.append_record().seq, 0);

        let after = state.clone();
        assert_eq!(
            state.prepare_append(raw(7), 700),
            Err(ExactFnspV3StateError::Accumulator(
                ExactAafiError::Duplicate
            ))
        );
        assert_eq!(state, after, "duplicate refusal must roll back completely");
    }

    #[test]
    fn exact_fnsp_v3_stale_token_refuses_after_intervening_commit_under_executor_mutex() {
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let stale = executor
            .prepare_exact_fnsp_v3_append(raw(20), 200)
            .expect("stale candidate");
        let intervening = executor
            .prepare_exact_fnsp_v3_append(raw(10), 100)
            .expect("intervening candidate");
        executor
            .compare_and_commit_exact_fnsp_v3_append(intervening)
            .expect("intervening commit");

        let before_refusal = executor.exact_fnsp_v3_head().expect("head");
        assert_eq!(
            executor.compare_and_commit_exact_fnsp_v3_append(stale),
            Err(ExactFnspV3StateError::StaleGeneration {
                prepared: 0,
                current: 1,
            })
        );
        assert_eq!(executor.exact_fnsp_v3_head().expect("head"), before_refusal);
    }

    #[test]
    fn exact_fnsp_v3_forged_candidate_refuses_without_partial_mutation() {
        let mut state = ExactFnspV3ExecutorState::new();
        let mut forged = state.prepare_append(raw(9), 90).expect("prepare");
        forged.append_record.value = 91;
        let before = state.clone();
        assert_eq!(
            state.compare_and_commit(forged),
            Err(ExactFnspV3StateError::CandidateMismatch(
                "prior transition or append record"
            ))
        );
        assert_eq!(state, before);

        let mut forged_successor = state.prepare_append(raw(9), 90).expect("prepare");
        forged_successor.successor_count += 1;
        assert_eq!(
            state.compare_and_commit(forged_successor),
            Err(ExactFnspV3StateError::CandidateMismatch(
                "independent successor replay"
            ))
        );
        assert_eq!(state, before);
    }

    #[test]
    fn exact_fnsp_v3_append_record_replay_has_identical_root_count_and_fns3() {
        let mut state = ExactFnspV3ExecutorState::new();
        for (key, value) in [(30, 300), (5, 50), (255, 2_550), (0, 1)] {
            let prepared = state.prepare_append(raw(key), value).expect("prepare");
            state.compare_and_commit(prepared).expect("commit");
        }

        let replayed = ExactFnspV3ExecutorState::from_append_records(
            state.append_records().iter().rev().copied(),
        )
        .expect("replay from shuffled storage order");
        assert_eq!(replayed.root(), state.root());
        assert_eq!(replayed.count(), state.count());
        assert_eq!(replayed.fns3(), state.fns3());
        assert_eq!(replayed.generation(), state.generation());
        assert_eq!(replayed.append_records(), state.append_records());
    }
}
