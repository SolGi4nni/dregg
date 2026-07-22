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
//! Live promotion still has to invoke [`compare_and_commit_exact_fnsp_v3_append_in`] from the
//! finalized-turn transaction so the commit record, receipt, note-root edge, attested state, exact
//! append row, and exact head share one crash boundary.
//!
//! The BLAKE3 seals below detect accidental/torn byte corruption; they are not signatures.  A
//! hostile actor able to rewrite the entire redb image can recompute them or roll the whole store
//! back.  Independent rollback resistance remains the job of authenticated finality/checkpoints.

use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactAafiError, ExactAppendRecord, ExactNullifierAafi, TREE_CAPACITY,
    exact_state_commit,
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
    pub fn initialize_exact_fnsp_v3_state(
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

    /// Atomically compare the durable head, replay the append, and commit record plus successor.
    ///
    /// This closes store-level cross-executor races.  It deliberately does not make v3 live or
    /// join the wider finalized-turn transaction; that later weld must call the crate-private
    /// transaction helper below.
    pub fn compare_and_commit_exact_fnsp_v3_append(
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

/// Durable CAS/finalization seam for a future caller-owned finalized-turn transaction.
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

fn prepare_from_snapshot(
    mut snapshot: ValidatedSnapshot,
    raw: [u8; 32],
    value: u64,
) -> std::result::Result<ExactFnspV3StateCasV1, ExactFnspV3StateStoreError> {
    let witness = snapshot.accumulator.prepare_insert(raw, value)?;
    snapshot.accumulator.apply_witness(&witness)?;
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
    Ok(candidate)
}

fn load_snapshot_from_read(read: &ReadTransaction) -> StoreResult<Option<ValidatedSnapshot>> {
    let (head_rows, record_rows) = {
        let heads = read.open_table(EXACT_FNSP_V3_STATE_HEAD)?;
        let records = read.open_table(EXACT_FNSP_V3_APPEND_RECORDS)?;
        (collect_heads(&heads)?, collect_records(&records)?)
    };
    validate_snapshot(head_rows, record_rows).map_err(integrity)
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
