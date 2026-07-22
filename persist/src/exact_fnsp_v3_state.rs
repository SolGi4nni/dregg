//! Durable, non-live store authority for the exact FNSP-v3 accumulator.
//!
//! The in-memory exact accumulator can prepare a transition efficiently, but submit and verify
//! executors are distinct instances and therefore cannot use an executor-local mutex as consensus
//! authority.  This module closes that boundary behind one durable-store owner:
//!
//! * every REAL append has one canonical, fixed-width record keyed by its dense sequence;
//! * one canonical head binds `(generation, root8, count, FNS3)`;
//! * every load replays the complete dense record image and requires byte-for-byte agreement with
//!   the head; and
//! * compare-and-commit rereads that authority under redb's serialized writer transaction,
//!   independently applies the proposed append, then writes the record and head in the **same**
//!   transaction.
//!
//! A stale concurrent writer, duplicate nullifier, forged successor, missing/trailing record,
//! truncated wire, non-canonical field lane, or head/record disagreement fails before commit.
//! The public API is deliberately not wired into turn dispatch or the predicate registry yet.
//! [`PersistentStore::commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame`](crate::PersistentStore::commit_finalized_turn_with_faithful_root_and_exact_fnsp_v3_frame)
//! invokes the consuming CAS from the finalized-turn transaction, so the commit record, receipt,
//! note-root edge, attested state, exact append row, signed frame row, and both heads share one
//! crash boundary.  That transaction-owned substrate does not by itself register v3 live.
//!
//! The BLAKE3 seals below detect accidental/torn byte corruption; they are not signatures.  A
//! hostile actor able to rewrite the entire redb image can recompute them or roll the whole store
//! back.  Independent rollback resistance remains the job of authenticated finality/checkpoints.

use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactAafiError, ExactAppendRecord, ExactNullifierAafi, TREE_CAPACITY,
    ValidatedExactAafiTransition, exact_state_commit,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use redb::{ReadTransaction, ReadableTable, TableDefinition, WriteTransaction};
use std::error::Error;
use std::fmt;

use crate::{PersistentStore, Result as StoreResult, StoreError};

const HEAD_MAGIC: [u8; 4] = *b"F3SH";
const RECORD_MAGIC: [u8; 4] = *b"F3AR";
const WIRE_VERSION: u8 = 1;
const WIRE_HEADER_LEN: usize = 8;

const HEAD_GENERATION_OFFSET: usize = WIRE_HEADER_LEN;
const HEAD_COUNT_OFFSET: usize = HEAD_GENERATION_OFFSET + 8;
const HEAD_ROOT_OFFSET: usize = HEAD_COUNT_OFFSET + 8;
const HEAD_FNS3_OFFSET: usize = HEAD_ROOT_OFFSET + 8 * 4;
const HEAD_SEAL_OFFSET: usize = HEAD_FNS3_OFFSET + 8 * 4;

const RECORD_SEQ_OFFSET: usize = WIRE_HEADER_LEN;
const RECORD_RAW_OFFSET: usize = RECORD_SEQ_OFFSET + 8;
const RECORD_VALUE_OFFSET: usize = RECORD_RAW_OFFSET + 32;
const RECORD_SEAL_OFFSET: usize = RECORD_VALUE_OFFSET + 8;

/// Exact size of the canonical `F3SH` v1 authority-head wire.
pub const EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN: usize = HEAD_SEAL_OFFSET + 32;
/// Exact size of the canonical `F3AR` v1 append-record wire.
pub const EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN: usize = RECORD_SEAL_OFFSET + 32;

const HEAD_KEY: u8 = 0;

/// The single exact FNSP-v3 authority head.
pub(crate) const EXACT_FNSP_V3_STATE_HEAD: TableDefinition<u8, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_state_head_v1");
/// Dense exact FNSP-v3 append image: zero-based sequence -> strict `F3AR` bytes.
pub(crate) const EXACT_FNSP_V3_APPEND_RECORDS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_append_records_v1");

/// Strict failures at the exact durable-state boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFnspV3StateStoreError {
    WireLength {
        wire: &'static str,
        expected: usize,
        actual: usize,
    },
    WrongMagic(&'static str),
    UnsupportedVersion {
        wire: &'static str,
        version: u8,
    },
    NonZeroReserved(&'static str),
    SealMismatch(&'static str),
    NonCanonicalLane {
        component: &'static str,
        lane: usize,
        value: u32,
    },
    EmptyCount,
    CountExceedsCapacity(u64),
    GenerationCountMismatch,
    Fns3Mismatch,
    GenerationOverflow,
    RecordKeyMismatch {
        key: u64,
        encoded: u64,
    },
    RecordGap {
        expected: u64,
        found: u64,
    },
    RecordCountMismatch {
        generation: u64,
        records: u64,
    },
    HeadTableCardinality(u64),
    RecordsWithoutHead,
    HeadReplayMismatch,
    AppendSequence {
        expected: u64,
        actual: u64,
    },
    CompareMismatch,
    CandidateSuccessorMismatch,
    CandidateReplayMismatch,
    Uninitialized,
    AlreadyInitialized,
    Accumulator(String),
}

impl fmt::Display for ExactFnspV3StateStoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WireLength {
                wire,
                expected,
                actual,
            } => write!(
                f,
                "exact FNSP-v3 {wire} wire length {actual}, expected {expected}"
            ),
            Self::WrongMagic(wire) => write!(f, "exact FNSP-v3 {wire} wire has wrong magic"),
            Self::UnsupportedVersion { wire, version } => {
                write!(f, "unsupported exact FNSP-v3 {wire} version {version}")
            }
            Self::NonZeroReserved(wire) => {
                write!(f, "exact FNSP-v3 {wire} reserved bytes are nonzero")
            }
            Self::SealMismatch(wire) => {
                write!(f, "exact FNSP-v3 {wire} integrity seal mismatch")
            }
            Self::NonCanonicalLane {
                component,
                lane,
                value,
            } => write!(
                f,
                "exact FNSP-v3 {component} lane {lane} is non-canonical: {value}"
            ),
            Self::EmptyCount => write!(f, "exact FNSP-v3 state omits the permanent BOT leaf"),
            Self::CountExceedsCapacity(count) => {
                write!(f, "exact FNSP-v3 count {count} exceeds tree capacity")
            }
            Self::GenerationCountMismatch => {
                write!(
                    f,
                    "exact FNSP-v3 generation is not count minus permanent BOT"
                )
            }
            Self::Fns3Mismatch => write!(f, "exact FNSP-v3 FNS3 does not bind root/count"),
            Self::GenerationOverflow => write!(f, "exact FNSP-v3 generation overflow"),
            Self::RecordKeyMismatch { key, encoded } => write!(
                f,
                "exact FNSP-v3 record key {key} disagrees with encoded sequence {encoded}"
            ),
            Self::RecordGap { expected, found } => write!(
                f,
                "exact FNSP-v3 record sequence is not dense: expected {expected}, found {found}"
            ),
            Self::RecordCountMismatch {
                generation,
                records,
            } => write!(
                f,
                "exact FNSP-v3 head generation {generation} disagrees with {records} records"
            ),
            Self::HeadTableCardinality(count) => write!(
                f,
                "exact FNSP-v3 head table contains {count} rows instead of exactly one"
            ),
            Self::RecordsWithoutHead => {
                write!(
                    f,
                    "exact FNSP-v3 append records exist without an authority head"
                )
            }
            Self::HeadReplayMismatch => {
                write!(f, "exact FNSP-v3 durable head disagrees with record replay")
            }
            Self::AppendSequence { expected, actual } => write!(
                f,
                "exact FNSP-v3 append sequence {actual}, expected {expected}"
            ),
            Self::CompareMismatch => write!(f, "exact FNSP-v3 durable compare token is stale"),
            Self::CandidateSuccessorMismatch => write!(
                f,
                "exact FNSP-v3 candidate successor disagrees with independent append replay"
            ),
            Self::CandidateReplayMismatch => write!(
                f,
                "exact FNSP-v3 replay candidate disagrees with the durable append prefix"
            ),
            Self::Uninitialized => write!(f, "exact FNSP-v3 durable state is not initialized"),
            Self::AlreadyInitialized => {
                write!(f, "exact FNSP-v3 durable state is already initialized")
            }
            Self::Accumulator(message) => {
                write!(
                    f,
                    "exact FNSP-v3 accumulator refused durable state: {message}"
                )
            }
        }
    }
}

impl Error for ExactFnspV3StateStoreError {}

impl From<ExactAafiError> for ExactFnspV3StateStoreError {
    fn from(value: ExactAafiError) -> Self {
        Self::Accumulator(value.to_string())
    }
}

/// Canonical durable exact-state authority.
///
/// The generation is the number of durable REAL records.  Count includes the permanent BOT leaf,
/// hence `count == generation + 1`.  All field lanes remain canonical on wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV3StateHeadV1 {
    generation: u64,
    root: [u32; 8],
    count: u64,
    fns3: [u32; 8],
}

impl ExactFnspV3StateHeadV1 {
    /// Construct a head from independently reconstructed accumulator coordinates.
    pub fn try_from_runtime(
        generation: u64,
        root: Digest8,
        count: u64,
        fns3: Digest8,
    ) -> std::result::Result<Self, ExactFnspV3StateStoreError> {
        let head = Self {
            generation,
            root: digest_to_canonical_lanes("root", root)?,
            count,
            fns3: digest_to_canonical_lanes("FNS3", fns3)?,
        };
        head.validate()?;
        Ok(head)
    }

    fn from_accumulator(
        generation: u64,
        accumulator: &ExactNullifierAafi,
    ) -> std::result::Result<Self, ExactFnspV3StateStoreError> {
        Self::try_from_runtime(
            generation,
            accumulator.root(),
            accumulator.count(),
            accumulator.state_commit(),
        )
    }

    pub fn generation(self) -> u64 {
        self.generation
    }

    pub fn root(self) -> Digest8 {
        lanes_to_digest(self.root)
    }

    pub fn count(self) -> u64 {
        self.count
    }

    pub fn fns3(self) -> Digest8 {
        lanes_to_digest(self.fns3)
    }

    pub fn encode(self) -> [u8; EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN] {
        let mut out = [0u8; EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN];
        out[..4].copy_from_slice(&HEAD_MAGIC);
        out[4] = WIRE_VERSION;
        out[HEAD_GENERATION_OFFSET..HEAD_COUNT_OFFSET]
            .copy_from_slice(&self.generation.to_le_bytes());
        out[HEAD_COUNT_OFFSET..HEAD_ROOT_OFFSET].copy_from_slice(&self.count.to_le_bytes());
        encode_lanes(&mut out[HEAD_ROOT_OFFSET..HEAD_FNS3_OFFSET], self.root);
        encode_lanes(&mut out[HEAD_FNS3_OFFSET..HEAD_SEAL_OFFSET], self.fns3);
        let seal = head_seal(&out[..HEAD_SEAL_OFFSET]);
        out[HEAD_SEAL_OFFSET..].copy_from_slice(&seal);
        out
    }

    pub fn decode(bytes: &[u8]) -> std::result::Result<Self, ExactFnspV3StateStoreError> {
        check_frame(
            "head",
            bytes,
            EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN,
            HEAD_MAGIC,
            HEAD_SEAL_OFFSET,
            head_seal,
        )?;
        let head = Self {
            generation: decode_u64(&bytes[HEAD_GENERATION_OFFSET..HEAD_COUNT_OFFSET]),
            count: decode_u64(&bytes[HEAD_COUNT_OFFSET..HEAD_ROOT_OFFSET]),
            root: decode_lanes(&bytes[HEAD_ROOT_OFFSET..HEAD_FNS3_OFFSET]),
            fns3: decode_lanes(&bytes[HEAD_FNS3_OFFSET..HEAD_SEAL_OFFSET]),
        };
        head.validate()?;
        Ok(head)
    }

    fn validate(self) -> std::result::Result<(), ExactFnspV3StateStoreError> {
        if self.count == 0 {
            return Err(ExactFnspV3StateStoreError::EmptyCount);
        }
        if self.count > TREE_CAPACITY {
            return Err(ExactFnspV3StateStoreError::CountExceedsCapacity(self.count));
        }
        if self.generation.checked_add(1) != Some(self.count) {
            return Err(ExactFnspV3StateStoreError::GenerationCountMismatch);
        }
        validate_lanes("root", self.root)?;
        validate_lanes("FNS3", self.fns3)?;
        if digest_to_canonical_lanes(
            "FNS3",
            exact_state_commit(lanes_to_digest(self.root), self.count),
        )? != self.fns3
        {
            return Err(ExactFnspV3StateStoreError::Fns3Mismatch);
        }
        Ok(())
    }
}

/// Canonical fixed-width append record stored in the dense authority table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StoredExactFnspV3AppendRecordV1(ExactAppendRecord);

impl StoredExactFnspV3AppendRecordV1 {
    fn encode(self) -> [u8; EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN] {
        let mut out = [0u8; EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN];
        out[..4].copy_from_slice(&RECORD_MAGIC);
        out[4] = WIRE_VERSION;
        out[RECORD_SEQ_OFFSET..RECORD_RAW_OFFSET].copy_from_slice(&self.0.seq.to_le_bytes());
        out[RECORD_RAW_OFFSET..RECORD_VALUE_OFFSET].copy_from_slice(&self.0.raw);
        out[RECORD_VALUE_OFFSET..RECORD_SEAL_OFFSET].copy_from_slice(&self.0.value.to_le_bytes());
        let seal = record_seal(&out[..RECORD_SEAL_OFFSET]);
        out[RECORD_SEAL_OFFSET..].copy_from_slice(&seal);
        out
    }

    fn decode(bytes: &[u8]) -> std::result::Result<Self, ExactFnspV3StateStoreError> {
        check_frame(
            "append-record",
            bytes,
            EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN,
            RECORD_MAGIC,
            RECORD_SEAL_OFFSET,
            record_seal,
        )?;
        let mut raw = [0u8; 32];
        raw.copy_from_slice(&bytes[RECORD_RAW_OFFSET..RECORD_VALUE_OFFSET]);
        Ok(Self(ExactAppendRecord {
            seq: decode_u64(&bytes[RECORD_SEQ_OFFSET..RECORD_RAW_OFFSET]),
            raw,
            value: decode_u64(&bytes[RECORD_VALUE_OFFSET..RECORD_SEAL_OFFSET]),
        }))
    }
}

/// Store-prepared append candidate usable across distinct submit/verify executor instances.
///
/// Its fields are private.  More importantly, the durable commit path does not trust the value:
/// it replays the append independently against the record image read under the writer lock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV3StateCasV1 {
    expected: ExactFnspV3StateHeadV1,
    successor: ExactFnspV3StateHeadV1,
    append_record: ExactAppendRecord,
}

/// One store-snapshot-owned exact transition for proof acceptance and the later writer CAS.
///
/// The validated semantic transition and CAS coordinates are derived by the same accumulator
/// replay.  Callers therefore cannot accidentally verify a proof against one read snapshot and
/// commit coordinates reconstructed from another.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedExactFnspV3StateTransitionV1 {
    cas: ExactFnspV3StateCasV1,
    validated: ValidatedExactAafiTransition,
}

impl PreparedExactFnspV3StateTransitionV1 {
    pub fn cas(&self) -> ExactFnspV3StateCasV1 {
        self.cas
    }

    pub fn validated(&self) -> &ValidatedExactAafiTransition {
        &self.validated
    }
}

impl ExactFnspV3StateCasV1 {
    pub fn expected(self) -> ExactFnspV3StateHeadV1 {
        self.expected
    }

    pub fn successor(self) -> ExactFnspV3StateHeadV1 {
        self.successor
    }

    pub fn append_record(self) -> ExactAppendRecord {
        self.append_record
    }

    fn validate_shape(self) -> std::result::Result<(), ExactFnspV3StateStoreError> {
        self.expected.validate()?;
        self.successor.validate()?;
        let successor_generation = self
            .expected
            .generation
            .checked_add(1)
            .ok_or(ExactFnspV3StateStoreError::GenerationOverflow)?;
        if self.successor.generation != successor_generation
            || self.append_record.seq != self.expected.generation
        {
            return Err(ExactFnspV3StateStoreError::AppendSequence {
                expected: self.expected.generation,
                actual: self.append_record.seq,
            });
        }
        Ok(())
    }
}

#[derive(Debug)]
struct ValidatedSnapshot {
    head: ExactFnspV3StateHeadV1,
    records: Vec<ExactAppendRecord>,
    accumulator: ExactNullifierAafi,
}

impl PersistentStore {
    /// Read and fully replay the durable exact authority.
    ///
    /// `None` means this non-live v3 authority has never been seeded.  Any partial seeding,
    /// missing/trailing/corrupt record, or head disagreement is an integrity error.
    pub fn exact_fnsp_v3_state_head(&self) -> StoreResult<Option<ExactFnspV3StateHeadV1>> {
        let read = self.db.begin_read()?;
        load_snapshot_from_read(&read).map(|snapshot| snapshot.map(|value| value.head))
    }

    /// Return the complete canonical append image after replay validation.
    pub fn exact_fnsp_v3_append_records(&self) -> StoreResult<Option<Vec<ExactAppendRecord>>> {
        let read = self.db.begin_read()?;
        load_snapshot_from_read(&read).map(|snapshot| snapshot.map(|value| value.records))
    }

    /// Atomically seed the non-live authority from a complete canonical append image.
    ///
    /// This is migration/test infrastructure, not live dispatch.  The records are fully replayed,
    /// sorted by their encoded sequence, then installed with the corresponding head in one redb
    /// transaction.  Existing or partial authority refuses rather than being overwritten.
    ///
    /// Test-only because accepting caller-supplied records can create an exact prefix unrelated to
    /// the live faithful nullifier image.  Production bootstrap is owned by
    /// `initialize_exact_fnsp_v3_state_from_faithful_nullifiers`, which derives every record from
    /// the validated durable legacy authority.
    #[cfg(test)]
    pub(crate) fn initialize_exact_fnsp_v3_state(
        &self,
        records: impl IntoIterator<Item = ExactAppendRecord>,
    ) -> StoreResult<ExactFnspV3StateHeadV1> {
        let write = self.db.begin_write()?;
        let (write, head) = initialize_exact_fnsp_v3_state_in(write, records)?;
        write.commit()?;
        Ok(head)
    }

    /// Prepare one candidate from the durable authority without mutating it.
    ///
    /// Two distinct executors may prepare concurrently.  Only the candidate whose complete prior
    /// head still matches at durable commit can win.
    pub fn prepare_exact_fnsp_v3_append(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> StoreResult<ExactFnspV3StateCasV1> {
        let read = self.db.begin_read()?;
        let snapshot = load_snapshot_from_read(&read)?
            .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))?;
        prepare_from_snapshot(snapshot, raw, value).map_err(integrity)
    }

    /// Prepare either the next fresh append or the immutable coordinates of a durable replay.
    ///
    /// Finalized-turn recovery cannot infer which case applies from the current head: after a
    /// restart an old append remains in the dense record image while later turns may already have
    /// advanced the authority.  This method fully validates that image first, then returns the
    /// current-tail candidate only when `raw` is absent.  When `raw` is already present, its value
    /// and dense sequence must agree and the original expected/successor heads are reconstructed
    /// from the historical prefixes.  A duplicate raw with a different value fails closed.
    pub fn prepare_exact_fnsp_v3_append_or_replay(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> StoreResult<ExactFnspV3StateCasV1> {
        let read = self.db.begin_read()?;
        let snapshot = load_snapshot_from_read(&read)?
            .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))?;
        match snapshot.records.iter().position(|record| record.raw == raw) {
            Some(index) => reconstruct_replay_from_snapshot(snapshot, index, raw, value),
            None => prepare_from_snapshot(snapshot, raw, value).map_err(integrity),
        }
    }

    /// Prepare the proof-facing validated transition and writer-facing CAS from one snapshot.
    ///
    /// This is the live exact-v3 pre-execution seam.  A historical replay receives the original
    /// immutable transition; a fresh append receives the current tail transition.  The later
    /// redb writer still independently compares/replays `cas` before committing.
    pub fn prepare_exact_fnsp_v3_transition_or_replay(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> StoreResult<PreparedExactFnspV3StateTransitionV1> {
        let read = self.db.begin_read()?;
        let snapshot = load_snapshot_from_read(&read)?
            .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))?;
        match snapshot.records.iter().position(|record| record.raw == raw) {
            Some(index) => reconstruct_prepared_replay_from_snapshot(snapshot, index, raw, value),
            None => prepare_transition_from_snapshot(snapshot, raw, value).map_err(integrity),
        }
    }

    /// Reconstruct the immutable CAS coordinates for an already durable historical append.
    ///
    /// Restart/idempotent replay cannot call [`Self::prepare_exact_fnsp_v3_append`]: the current
    /// accumulator correctly reports the historical nullifier as a duplicate.  This method locates
    /// the exact durable record, rebuilds only its predecessor prefix, and independently prepares
    /// the same append again.  Missing keys, changed values, gaps, or mismatching coordinates fail
    /// closed.  It performs no mutation.
    pub fn reconstruct_exact_fnsp_v3_replay_candidate(
        &self,
        raw: [u8; 32],
        value: u64,
    ) -> StoreResult<ExactFnspV3StateCasV1> {
        let read = self.db.begin_read()?;
        let snapshot = load_snapshot_from_read(&read)?
            .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))?;
        let index = snapshot
            .records
            .iter()
            .position(|record| record.raw == raw)
            .ok_or_else(|| integrity(ExactFnspV3StateStoreError::CandidateReplayMismatch))?;
        reconstruct_replay_from_snapshot(snapshot, index, raw, value)
    }

    /// Atomically compare the durable head, replay the append, and commit record plus successor.
    ///
    /// This closes store-level cross-executor races.  It deliberately does not make v3 live; the
    /// finalized-turn route uses the crate-private consuming helper below instead of this separate
    /// transaction convenience API.
    #[cfg(test)]
    pub(crate) fn compare_and_commit_exact_fnsp_v3_append(
        &self,
        candidate: ExactFnspV3StateCasV1,
    ) -> StoreResult<ExactFnspV3StateHeadV1> {
        let write = self.db.begin_write()?;
        let (write, successor) = compare_and_commit_exact_fnsp_v3_append_in(write, candidate)?;
        write.commit()?;
        Ok(successor)
    }
}

/// Seed the first head and complete append image inside a caller-owned transaction.
pub(crate) fn initialize_exact_fnsp_v3_state_in(
    write: WriteTransaction,
    records: impl IntoIterator<Item = ExactAppendRecord>,
) -> StoreResult<(WriteTransaction, ExactFnspV3StateHeadV1)> {
    crate::exact_fnsp_v3_frame_head::ensure_frame_authority_absent_in_write(&write)?;
    if load_snapshot_from_write(&write)?.is_some() {
        return Err(integrity(ExactFnspV3StateStoreError::AlreadyInitialized));
    }

    let mut records: Vec<_> = records.into_iter().collect();
    records.sort_unstable_by_key(|record| record.seq);
    for (expected, record) in (0u64..).zip(&records) {
        if record.seq != expected {
            return Err(integrity(ExactFnspV3StateStoreError::RecordGap {
                expected,
                found: record.seq,
            }));
        }
    }
    let accumulator = ExactNullifierAafi::from_append_records(records.iter().copied())
        .map_err(ExactFnspV3StateStoreError::from)
        .map_err(integrity)?;
    let generation = u64::try_from(records.len())
        .map_err(|_| integrity(ExactFnspV3StateStoreError::GenerationOverflow))?;
    let head =
        ExactFnspV3StateHeadV1::from_accumulator(generation, &accumulator).map_err(integrity)?;

    // Open both tables before the first mutation. More importantly, this helper owns `write` and
    // returns it only on complete success. Any error path drops/aborts the transaction, so a caller
    // cannot catch a late table/storage error and commit a record-only or head-only seed.
    {
        let mut head_table = write.open_table(EXACT_FNSP_V3_STATE_HEAD)?;
        let mut record_table = write.open_table(EXACT_FNSP_V3_APPEND_RECORDS)?;
        for record in records {
            let encoded = StoredExactFnspV3AppendRecordV1(record).encode();
            record_table.insert(record.seq, encoded.as_slice())?;
        }
        let encoded = head.encode();
        head_table.insert(HEAD_KEY, encoded.as_slice())?;
    }
    Ok((write, head))
}

/// Durable CAS/finalization seam for the caller-owned finalized-turn transaction.
///
/// No head-only helper exists: this function independently validates/replays the current prefix
/// and proposed append, then inserts the record and head under one writer transaction.
pub(crate) fn compare_and_commit_exact_fnsp_v3_append_in(
    write: WriteTransaction,
    candidate: ExactFnspV3StateCasV1,
) -> StoreResult<(WriteTransaction, ExactFnspV3StateHeadV1)> {
    candidate.validate_shape().map_err(integrity)?;
    let snapshot = load_snapshot_from_write(&write)?
        .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))?;
    if snapshot.head != candidate.expected {
        return Err(integrity(ExactFnspV3StateStoreError::CompareMismatch));
    }

    let independently_prepared = prepare_from_snapshot(
        snapshot,
        candidate.append_record.raw,
        candidate.append_record.value,
    )
    .map_err(integrity)?;
    if independently_prepared.append_record != candidate.append_record
        || independently_prepared.successor != candidate.successor
    {
        return Err(integrity(
            ExactFnspV3StateStoreError::CandidateSuccessorMismatch,
        ));
    }

    // One redb writer transaction is the commit boundary for both authorities.  If either insert
    // or the caller's later finalized-turn writes fail, dropping/aborting the transaction exposes
    // neither row.
    // Open both tables before the first mutation. Ownership is load-bearing: `write` is returned
    // only after both inserts succeed. On any error it is dropped here, so even a caller that
    // catches the error has no transaction left to commit.
    {
        let mut heads = write.open_table(EXACT_FNSP_V3_STATE_HEAD)?;
        let mut records = write.open_table(EXACT_FNSP_V3_APPEND_RECORDS)?;
        if records.get(candidate.append_record.seq)?.is_some() {
            return Err(integrity(ExactFnspV3StateStoreError::AppendSequence {
                expected: candidate.expected.generation,
                actual: candidate.append_record.seq,
            }));
        }
        let encoded = StoredExactFnspV3AppendRecordV1(candidate.append_record).encode();
        records.insert(candidate.append_record.seq, encoded.as_slice())?;
        let encoded = candidate.successor.encode();
        heads.insert(HEAD_KEY, encoded.as_slice())?;
    }
    Ok((write, candidate.successor))
}

/// Verify that a previously committed finalized turn already owns this exact append.
///
/// A replay may arrive after later turns advanced the exact authority, so comparing `candidate`
/// with the current head would be wrong.  Instead, replay the durable prefix immediately before
/// and after the candidate's sequence and require both historical heads plus the exact record to
/// match.  This is read-only and is intended for the idempotent branch of the caller-owned
/// finalized-turn transaction.
pub(crate) fn verify_replayed_exact_fnsp_v3_append_in(
    write: &WriteTransaction,
    candidate: ExactFnspV3StateCasV1,
) -> StoreResult<()> {
    candidate.validate_shape().map_err(integrity)?;
    let snapshot = load_snapshot_from_write(write)?
        .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))?;
    let index = usize::try_from(candidate.append_record.seq)
        .map_err(|_| integrity(ExactFnspV3StateStoreError::CandidateReplayMismatch))?;
    if snapshot.records.get(index).copied() != Some(candidate.append_record) {
        return Err(integrity(
            ExactFnspV3StateStoreError::CandidateReplayMismatch,
        ));
    }

    let prior = ExactNullifierAafi::from_append_records(snapshot.records[..index].iter().copied())
        .map_err(ExactFnspV3StateStoreError::from)
        .map_err(integrity)?;
    let expected = ExactFnspV3StateHeadV1::from_accumulator(candidate.append_record.seq, &prior)
        .map_err(integrity)?;

    let successor_generation = candidate
        .append_record
        .seq
        .checked_add(1)
        .ok_or_else(|| integrity(ExactFnspV3StateStoreError::GenerationOverflow))?;
    let successor =
        ExactNullifierAafi::from_append_records(snapshot.records[..=index].iter().copied())
            .map_err(ExactFnspV3StateStoreError::from)
            .and_then(|accumulator| {
                ExactFnspV3StateHeadV1::from_accumulator(successor_generation, &accumulator)
            })
            .map_err(integrity)?;

    if expected != candidate.expected || successor != candidate.successor {
        return Err(integrity(
            ExactFnspV3StateStoreError::CandidateReplayMismatch,
        ));
    }
    Ok(())
}

/// Load the complete exact append image from a caller-owned writer after full head/record replay.
///
/// This is the cross-authority prefix seam used by finalized-turn bootstrap and dual-write.  An
/// absent, partial, corrupt, or head-disagreeing exact authority is an error, never an empty prefix.
pub(crate) fn exact_fnsp_v3_append_records_in(
    write: &WriteTransaction,
) -> StoreResult<Vec<ExactAppendRecord>> {
    load_snapshot_from_write(write)?
        .map(|snapshot| snapshot.records)
        .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))
}

/// Load the exact accumulator head through the caller-owned writer after full replay validation.
///
/// The durable frame-head lane uses this to bind an activation and every exact receipt frame to
/// the same writer-owned accumulator snapshot.  It intentionally returns no unchecked table row.
pub(crate) fn exact_fnsp_v3_state_head_in(
    write: &WriteTransaction,
) -> StoreResult<ExactFnspV3StateHeadV1> {
    load_snapshot_from_write(write)?
        .map(|snapshot| snapshot.head)
        .ok_or_else(|| integrity(ExactFnspV3StateStoreError::Uninitialized))
}

fn prepare_from_snapshot(
    snapshot: ValidatedSnapshot,
    raw: [u8; 32],
    value: u64,
) -> std::result::Result<ExactFnspV3StateCasV1, ExactFnspV3StateStoreError> {
    prepare_transition_from_snapshot(snapshot, raw, value).map(|prepared| prepared.cas)
}

fn prepare_transition_from_snapshot(
    mut snapshot: ValidatedSnapshot,
    raw: [u8; 32],
    value: u64,
) -> std::result::Result<PreparedExactFnspV3StateTransitionV1, ExactFnspV3StateStoreError> {
    let witness = snapshot.accumulator.prepare_insert(raw, value)?;
    let validated = snapshot.accumulator.apply_witness(&witness)?;
    let successor_generation = snapshot
        .head
        .generation
        .checked_add(1)
        .ok_or(ExactFnspV3StateStoreError::GenerationOverflow)?;
    let successor =
        ExactFnspV3StateHeadV1::from_accumulator(successor_generation, &snapshot.accumulator)?;
    let candidate = ExactFnspV3StateCasV1 {
        expected: snapshot.head,
        successor,
        append_record: ExactAppendRecord {
            seq: snapshot.head.generation,
            raw,
            value,
        },
    };
    candidate.validate_shape()?;
    Ok(PreparedExactFnspV3StateTransitionV1 {
        cas: candidate,
        validated,
    })
}

fn reconstruct_replay_from_snapshot(
    snapshot: ValidatedSnapshot,
    index: usize,
    raw: [u8; 32],
    value: u64,
) -> StoreResult<ExactFnspV3StateCasV1> {
    reconstruct_prepared_replay_from_snapshot(snapshot, index, raw, value)
        .map(|prepared| prepared.cas)
}

fn reconstruct_prepared_replay_from_snapshot(
    snapshot: ValidatedSnapshot,
    index: usize,
    raw: [u8; 32],
    value: u64,
) -> StoreResult<PreparedExactFnspV3StateTransitionV1> {
    let target = snapshot.records[index];
    if target.raw != raw || target.value != value || usize::try_from(target.seq).ok() != Some(index)
    {
        return Err(integrity(
            ExactFnspV3StateStoreError::CandidateReplayMismatch,
        ));
    }

    let records = snapshot.records[..index].to_vec();
    let accumulator = ExactNullifierAafi::from_append_records(records.iter().copied())
        .map_err(ExactFnspV3StateStoreError::from)
        .map_err(integrity)?;
    let generation = u64::try_from(index)
        .map_err(|_| integrity(ExactFnspV3StateStoreError::GenerationOverflow))?;
    let head =
        ExactFnspV3StateHeadV1::from_accumulator(generation, &accumulator).map_err(integrity)?;
    let prepared = prepare_transition_from_snapshot(
        ValidatedSnapshot {
            head,
            records,
            accumulator,
        },
        raw,
        value,
    )
    .map_err(integrity)?;
    if prepared.cas.append_record != target {
        return Err(integrity(
            ExactFnspV3StateStoreError::CandidateReplayMismatch,
        ));
    }
    Ok(prepared)
}

fn load_snapshot_from_read(read: &ReadTransaction) -> StoreResult<Option<ValidatedSnapshot>> {
    let (head_rows, record_rows) = {
        let heads = read.open_table(EXACT_FNSP_V3_STATE_HEAD)?;
        let records = read.open_table(EXACT_FNSP_V3_APPEND_RECORDS)?;
        (collect_heads(&heads)?, collect_records(&records)?)
    };
    validate_snapshot(head_rows, record_rows).map_err(integrity)
}

/// Load the exact head through a caller-owned reader after complete record replay validation.
pub(crate) fn load_state_head_from_read(
    read: &ReadTransaction,
) -> StoreResult<Option<ExactFnspV3StateHeadV1>> {
    load_snapshot_from_read(read).map(|snapshot| snapshot.map(|snapshot| snapshot.head))
}

fn load_snapshot_from_write(write: &WriteTransaction) -> StoreResult<Option<ValidatedSnapshot>> {
    let (head_rows, record_rows) = {
        let heads = write.open_table(EXACT_FNSP_V3_STATE_HEAD)?;
        let records = write.open_table(EXACT_FNSP_V3_APPEND_RECORDS)?;
        (collect_heads(&heads)?, collect_records(&records)?)
    };
    validate_snapshot(head_rows, record_rows).map_err(integrity)
}

fn collect_heads(table: &impl ReadableTable<u8, &'static [u8]>) -> StoreResult<Vec<(u8, Vec<u8>)>> {
    let mut rows = Vec::new();
    for entry in table.iter()? {
        let (key, value) = entry?;
        rows.push((key.value(), value.value().to_vec()));
    }
    Ok(rows)
}

fn collect_records(
    table: &impl ReadableTable<u64, &'static [u8]>,
) -> StoreResult<Vec<(u64, Vec<u8>)>> {
    let mut rows = Vec::new();
    for entry in table.iter()? {
        let (key, value) = entry?;
        rows.push((key.value(), value.value().to_vec()));
    }
    Ok(rows)
}

fn validate_snapshot(
    head_rows: Vec<(u8, Vec<u8>)>,
    record_rows: Vec<(u64, Vec<u8>)>,
) -> std::result::Result<Option<ValidatedSnapshot>, ExactFnspV3StateStoreError> {
    if head_rows.is_empty() {
        if record_rows.is_empty() {
            return Ok(None);
        }
        return Err(ExactFnspV3StateStoreError::RecordsWithoutHead);
    }
    if head_rows.len() != 1 || head_rows[0].0 != HEAD_KEY {
        return Err(ExactFnspV3StateStoreError::HeadTableCardinality(
            head_rows.len() as u64,
        ));
    }
    let head = ExactFnspV3StateHeadV1::decode(&head_rows[0].1)?;
    let record_count = u64::try_from(record_rows.len())
        .map_err(|_| ExactFnspV3StateStoreError::GenerationOverflow)?;
    if record_count != head.generation {
        return Err(ExactFnspV3StateStoreError::RecordCountMismatch {
            generation: head.generation,
            records: record_count,
        });
    }

    let mut decoded = Vec::with_capacity(record_rows.len());
    for (expected, (key, bytes)) in (0u64..).zip(record_rows) {
        if key != expected {
            return Err(ExactFnspV3StateStoreError::RecordGap {
                expected,
                found: key,
            });
        }
        let stored = StoredExactFnspV3AppendRecordV1::decode(&bytes)?.0;
        if stored.seq != key {
            return Err(ExactFnspV3StateStoreError::RecordKeyMismatch {
                key,
                encoded: stored.seq,
            });
        }
        decoded.push(stored);
    }

    let accumulator = ExactNullifierAafi::from_append_records(decoded.iter().copied())?;
    let replayed = ExactFnspV3StateHeadV1::from_accumulator(head.generation, &accumulator)?;
    if replayed != head {
        return Err(ExactFnspV3StateStoreError::HeadReplayMismatch);
    }
    Ok(Some(ValidatedSnapshot {
        head,
        records: decoded,
        accumulator,
    }))
}

fn check_frame(
    wire: &'static str,
    bytes: &[u8],
    expected_len: usize,
    magic: [u8; 4],
    seal_offset: usize,
    seal: fn(&[u8]) -> [u8; 32],
) -> std::result::Result<(), ExactFnspV3StateStoreError> {
    if bytes.len() != expected_len {
        return Err(ExactFnspV3StateStoreError::WireLength {
            wire,
            expected: expected_len,
            actual: bytes.len(),
        });
    }
    if bytes[..4] != magic {
        return Err(ExactFnspV3StateStoreError::WrongMagic(wire));
    }
    if bytes[4] != WIRE_VERSION {
        return Err(ExactFnspV3StateStoreError::UnsupportedVersion {
            wire,
            version: bytes[4],
        });
    }
    if bytes[5..WIRE_HEADER_LEN] != [0; WIRE_HEADER_LEN - 5] {
        return Err(ExactFnspV3StateStoreError::NonZeroReserved(wire));
    }
    if bytes[seal_offset..] != seal(&bytes[..seal_offset]) {
        return Err(ExactFnspV3StateStoreError::SealMismatch(wire));
    }
    Ok(())
}

fn integrity(error: ExactFnspV3StateStoreError) -> StoreError {
    StoreError::Integrity(error.to_string())
}

fn head_seal(prefix: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key("dregg-exact-fnsp-v3-state-head-v1")
        .update(prefix)
        .finalize()
        .as_bytes()
}

fn record_seal(prefix: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key("dregg-exact-fnsp-v3-append-record-v1")
        .update(prefix)
        .finalize()
        .as_bytes()
}

fn digest_to_canonical_lanes(
    component: &'static str,
    digest: Digest8,
) -> std::result::Result<[u32; 8], ExactFnspV3StateStoreError> {
    let lanes = digest.map(BabyBear::as_u32);
    validate_lanes(component, lanes)?;
    Ok(lanes)
}

fn validate_lanes(
    component: &'static str,
    lanes: [u32; 8],
) -> std::result::Result<(), ExactFnspV3StateStoreError> {
    for (lane, value) in lanes.into_iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(ExactFnspV3StateStoreError::NonCanonicalLane {
                component,
                lane,
                value,
            });
        }
    }
    Ok(())
}

fn lanes_to_digest(lanes: [u32; 8]) -> Digest8 {
    lanes.map(BabyBear::from_canonical)
}

fn encode_lanes(out: &mut [u8], lanes: [u32; 8]) {
    for (chunk, lane) in out.chunks_exact_mut(4).zip(lanes) {
        chunk.copy_from_slice(&lane.to_le_bytes());
    }
}

fn decode_lanes(bytes: &[u8]) -> [u32; 8] {
    std::array::from_fn(|lane| {
        let offset = lane * 4;
        u32::from_le_bytes(
            bytes[offset..offset + 4]
                .try_into()
                .expect("four-byte lane"),
        )
    })
}

fn decode_u64(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes.try_into().expect("eight-byte integer"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw(first: u8) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0] = first;
        out
    }

    fn genesis() -> ExactFnspV3StateHeadV1 {
        ExactFnspV3StateHeadV1::from_accumulator(0, &ExactNullifierAafi::new())
            .expect("canonical genesis")
    }

    fn assert_integrity_contains<T: fmt::Debug>(result: StoreResult<T>, needle: &str) {
        assert!(
            matches!(result, Err(StoreError::Integrity(ref message)) if message.contains(needle)),
            "expected integrity error containing {needle:?}, got {result:?}"
        );
    }

    #[test]
    fn exact_head_and_record_wires_are_strict_and_canonical() {
        let head = genesis();
        let encoded = head.encode();
        assert_eq!(encoded.len(), EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN);
        assert_eq!(&encoded[..4], b"F3SH");
        assert_eq!(ExactFnspV3StateHeadV1::decode(&encoded), Ok(head));
        assert_eq!(head.generation(), 0);
        assert_eq!(head.count(), 1);
        assert_eq!(head.fns3(), exact_state_commit(head.root(), 1));

        let record = ExactAppendRecord {
            seq: 7,
            raw: raw(9),
            value: u64::MAX,
        };
        let encoded_record = StoredExactFnspV3AppendRecordV1(record).encode();
        assert_eq!(
            encoded_record.len(),
            EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN
        );
        assert_eq!(&encoded_record[..4], b"F3AR");
        assert_eq!(
            StoredExactFnspV3AppendRecordV1::decode(&encoded_record),
            Ok(StoredExactFnspV3AppendRecordV1(record))
        );

        assert!(matches!(
            ExactFnspV3StateHeadV1::decode(&encoded[..encoded.len() - 1]),
            Err(ExactFnspV3StateStoreError::WireLength { wire: "head", .. })
        ));
        assert!(matches!(
            StoredExactFnspV3AppendRecordV1::decode(&encoded_record[..encoded_record.len() - 1]),
            Err(ExactFnspV3StateStoreError::WireLength {
                wire: "append-record",
                ..
            })
        ));
        let mut trailing = encoded_record.to_vec();
        trailing.push(0);
        assert!(matches!(
            StoredExactFnspV3AppendRecordV1::decode(&trailing),
            Err(ExactFnspV3StateStoreError::WireLength { .. })
        ));

        let mut noncanonical = encoded;
        noncanonical[HEAD_ROOT_OFFSET..HEAD_ROOT_OFFSET + 4]
            .copy_from_slice(&BABYBEAR_P.to_le_bytes());
        let seal = head_seal(&noncanonical[..HEAD_SEAL_OFFSET]);
        noncanonical[HEAD_SEAL_OFFSET..].copy_from_slice(&seal);
        assert!(matches!(
            ExactFnspV3StateHeadV1::decode(&noncanonical),
            Err(ExactFnspV3StateStoreError::NonCanonicalLane {
                component: "root",
                lane: 0,
                value: BABYBEAR_P,
            })
        ));
    }

    #[test]
    fn durable_append_restarts_to_identical_generation_root_count_fns3_and_records() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("exact-v3.redb");
        let final_head;
        let expected_records;
        {
            let store = PersistentStore::open(&path).expect("open");
            assert_eq!(store.exact_fnsp_v3_state_head().expect("unseeded"), None);
            assert_eq!(
                store
                    .initialize_exact_fnsp_v3_state(std::iter::empty())
                    .expect("seed genesis"),
                genesis()
            );
            for (key, value) in [(30, 300), (5, 50), (255, 2_550), (0, 1)] {
                let prepared = store
                    .prepare_exact_fnsp_v3_append(raw(key), value)
                    .expect("prepare");
                store
                    .compare_and_commit_exact_fnsp_v3_append(prepared)
                    .expect("commit");
            }
            final_head = store
                .exact_fnsp_v3_state_head()
                .expect("head")
                .expect("seeded");
            expected_records = store
                .exact_fnsp_v3_append_records()
                .expect("records")
                .expect("seeded");
        }

        let reopened = PersistentStore::open(&path).expect("reopen");
        assert_eq!(
            reopened.exact_fnsp_v3_state_head().expect("replayed head"),
            Some(final_head)
        );
        assert_eq!(
            reopened
                .exact_fnsp_v3_append_records()
                .expect("replayed records"),
            Some(expected_records.clone())
        );
        let replayed = ExactNullifierAafi::from_append_records(expected_records).expect("replay");
        assert_eq!(final_head.generation(), 4);
        assert_eq!(final_head.root(), replayed.root());
        assert_eq!(final_head.count(), replayed.count());
        assert_eq!(final_head.fns3(), replayed.state_commit());
    }

    #[test]
    fn append_or_replay_recovers_historical_coordinates_after_restart_and_later_append() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("exact-v3-replay.redb");
        let first;
        let second;
        {
            let store = PersistentStore::open(&path).expect("open");
            store
                .initialize_exact_fnsp_v3_state(std::iter::empty())
                .expect("seed");
            first = store
                .prepare_exact_fnsp_v3_append_or_replay(raw(31), 310)
                .expect("prepare first");
            store
                .compare_and_commit_exact_fnsp_v3_append(first)
                .expect("commit first");
            second = store
                .prepare_exact_fnsp_v3_append_or_replay(raw(32), 320)
                .expect("prepare second");
            store
                .compare_and_commit_exact_fnsp_v3_append(second)
                .expect("commit second");
        }

        let reopened = PersistentStore::open(&path).expect("reopen");
        assert_eq!(
            reopened
                .prepare_exact_fnsp_v3_append_or_replay(raw(31), 310)
                .expect("recover historical first"),
            first
        );
        assert_eq!(
            reopened
                .prepare_exact_fnsp_v3_append_or_replay(raw(32), 320)
                .expect("recover historical second"),
            second
        );
        assert_integrity_contains(
            reopened.prepare_exact_fnsp_v3_append_or_replay(raw(31), 311),
            "durable append prefix",
        );

        let fresh = reopened
            .prepare_exact_fnsp_v3_append_or_replay(raw(33), 330)
            .expect("absent raw prepares current-tail append");
        assert_eq!(fresh.expected(), second.successor());
        assert_eq!(fresh.append_record().seq, 2);

        // Full snapshot validation precedes both branches: a corrupt head cannot be used to
        // reconstruct an old append or to prepare a new one.
        {
            let write = reopened.db.begin_write().expect("corrupt writer");
            write
                .open_table(EXACT_FNSP_V3_STATE_HEAD)
                .expect("heads")
                .insert(HEAD_KEY, &[0u8; 7][..])
                .expect("truncate head");
            write.commit().expect("commit corruption");
        }
        assert_integrity_contains(
            reopened.prepare_exact_fnsp_v3_append_or_replay(raw(31), 310),
            "wire length 7",
        );
        assert_integrity_contains(
            reopened.prepare_exact_fnsp_v3_append_or_replay(raw(34), 340),
            "wire length 7",
        );
    }

    #[test]
    fn proof_transition_and_writer_cas_share_one_validated_snapshot() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        let prepared = store
            .prepare_exact_fnsp_v3_transition_or_replay(raw(41), 410)
            .expect("prepare transition");
        let cas = prepared.cas();
        assert_eq!(prepared.validated().prior_root(), cas.expected().root());
        assert_eq!(prepared.validated().prior_count(), cas.expected().count());
        assert_eq!(
            prepared.validated().successor_root(),
            cas.successor().root()
        );
        assert_eq!(
            prepared.validated().successor_count(),
            cas.successor().count()
        );
        store
            .compare_and_commit_exact_fnsp_v3_append(cas)
            .expect("commit");

        let replay = store
            .prepare_exact_fnsp_v3_transition_or_replay(raw(41), 410)
            .expect("replay transition");
        assert_eq!(replay.cas(), cas);
        assert_eq!(replay.validated(), prepared.validated());
    }

    #[test]
    fn competing_writer_and_duplicate_refuse_without_mutation() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        let first = store
            .prepare_exact_fnsp_v3_append(raw(8), 80)
            .expect("first");
        let stale = store
            .prepare_exact_fnsp_v3_append(raw(9), 90)
            .expect("stale");
        let committed = store
            .compare_and_commit_exact_fnsp_v3_append(first)
            .expect("first wins");
        let records = store.exact_fnsp_v3_append_records().expect("records");

        assert_integrity_contains(
            store.compare_and_commit_exact_fnsp_v3_append(stale),
            "stale",
        );
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("head"),
            Some(committed)
        );
        assert_eq!(
            store.exact_fnsp_v3_append_records().expect("records"),
            records
        );

        assert_integrity_contains(
            store.prepare_exact_fnsp_v3_append(raw(8), 8_000),
            "already exists",
        );
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("head"),
            Some(committed)
        );
        assert_eq!(
            store.exact_fnsp_v3_append_records().expect("records"),
            records
        );
    }

    #[test]
    fn record_and_head_share_one_abort_and_commit_boundary() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        let initial = genesis();
        let aborted = store
            .prepare_exact_fnsp_v3_append(raw(1), 10)
            .expect("prepare abort");
        {
            let write = store.db.begin_write().expect("write");
            let (write, _) = compare_and_commit_exact_fnsp_v3_append_in(write, aborted)
                .expect("stage both rows");
            write.abort().expect("abort");
        }
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("head"),
            Some(initial)
        );
        assert_eq!(
            store.exact_fnsp_v3_append_records().expect("records"),
            Some(Vec::new())
        );

        let committed = store
            .prepare_exact_fnsp_v3_append(raw(2), 20)
            .expect("prepare commit");
        let successor = store
            .compare_and_commit_exact_fnsp_v3_append(committed)
            .expect("commit");
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("head"),
            Some(successor)
        );
        assert_eq!(
            store.exact_fnsp_v3_append_records().expect("records"),
            Some(vec![committed.append_record()])
        );
    }

    #[test]
    fn replay_verifier_checks_the_historical_prefix_after_later_appends() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        let first = store
            .prepare_exact_fnsp_v3_append(raw(11), 110)
            .expect("first");
        store
            .compare_and_commit_exact_fnsp_v3_append(first)
            .expect("commit first");
        let second = store
            .prepare_exact_fnsp_v3_append(raw(12), 120)
            .expect("second");
        store
            .compare_and_commit_exact_fnsp_v3_append(second)
            .expect("commit second");

        let write = store.db.begin_write().expect("replay snapshot");
        verify_replayed_exact_fnsp_v3_append_in(&write, first)
            .expect("old turn still owns its exact historical prefix");
        verify_replayed_exact_fnsp_v3_append_in(&write, second)
            .expect("new turn owns its exact tail");

        let mut forged = first;
        forged.append_record.value ^= 1;
        assert_integrity_contains(
            verify_replayed_exact_fnsp_v3_append_in(&write, forged),
            "durable append prefix",
        );
        write.abort().expect("read-only writer abort");
    }

    #[test]
    fn forged_successor_is_independently_replayed_and_refused() {
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        let mut forged = store
            .prepare_exact_fnsp_v3_append(raw(3), 30)
            .expect("prepare");
        let alternate = ExactNullifierAafi::from_append_records([ExactAppendRecord {
            seq: 0,
            raw: raw(4),
            value: 40,
        }])
        .expect("alternate state");
        forged.successor =
            ExactFnspV3StateHeadV1::from_accumulator(1, &alternate).expect("alternate head");
        assert_integrity_contains(
            store.compare_and_commit_exact_fnsp_v3_append(forged),
            "independent append replay",
        );
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("head"),
            Some(genesis())
        );
        assert_eq!(
            store.exact_fnsp_v3_append_records().expect("records"),
            Some(Vec::new())
        );
    }

    #[test]
    fn truncation_corruption_and_split_rows_fail_closed() {
        // Missing record under a generation-one head is truncation, not a shorter accepted prefix.
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        let prepared = store
            .prepare_exact_fnsp_v3_append(raw(5), 50)
            .expect("prepare");
        store
            .compare_and_commit_exact_fnsp_v3_append(prepared)
            .expect("commit");
        {
            let write = store.db.begin_write().expect("write");
            write
                .open_table(EXACT_FNSP_V3_APPEND_RECORDS)
                .expect("records")
                .remove(0)
                .expect("remove");
            write.commit().expect("commit corruption");
        }
        assert_integrity_contains(store.exact_fnsp_v3_state_head(), "disagrees with 0 records");

        // A record without a head is likewise refused rather than treated as uninitialized.
        let split = PersistentStore::open_in_memory().expect("split store");
        {
            let write = split.db.begin_write().expect("write");
            let encoded = StoredExactFnspV3AppendRecordV1(ExactAppendRecord {
                seq: 0,
                raw: raw(6),
                value: 60,
            })
            .encode();
            write
                .open_table(EXACT_FNSP_V3_APPEND_RECORDS)
                .expect("records")
                .insert(0, encoded.as_slice())
                .expect("insert split record");
            write.commit().expect("commit split record");
        }
        assert_integrity_contains(
            split.exact_fnsp_v3_state_head(),
            "without an authority head",
        );

        // Exact wire truncation is detected before semantic replay.
        let truncated = PersistentStore::open_in_memory().expect("truncated store");
        truncated
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("seed");
        {
            let write = truncated.db.begin_write().expect("write");
            write
                .open_table(EXACT_FNSP_V3_STATE_HEAD)
                .expect("heads")
                .insert(HEAD_KEY, &[0u8; 7][..])
                .expect("truncate");
            write.commit().expect("commit truncation");
        }
        assert_integrity_contains(truncated.exact_fnsp_v3_state_head(), "wire length 7");
    }
}
