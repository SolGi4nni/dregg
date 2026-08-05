//! Generic append-only durability for Lean-authored Path of Angels aggregates.
//!
//! This module deliberately knows no game rules.  Native Lean supplies an exact
//! event digest, payload digest, opaque payload wire, and opaque successor
//! projection.  Rust provides only crash-safe framing: aggregate/version/sequence
//! CAS, immutable rows, binding to the carrying [`CommitRecord`], replay identity,
//! and full-chain corruption audit.  Projections are restart caches, never an
//! alternate semantic judge.

use redb::{ReadableTable, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

pub(crate) const POA_EVENT_HEADS_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("poa_event_heads_v1");
pub(crate) const POA_EVENTS_V1: TableDefinition<&[u8; 40], &[u8]> =
    TableDefinition::new("poa_events_v1");
pub(crate) const POA_EVENT_BY_COMMIT_ORDINAL_V1: TableDefinition<u64, &[u8; 40]> =
    TableDefinition::new("poa_event_by_commit_ordinal_v1");

const HEAD_MAGIC: [u8; 4] = *b"PEHD";
const EVENT_MAGIC: [u8; 4] = *b"PEVT";
const FRAME_VERSION: u8 = 1;
const FRAME_HEADER_LEN: usize = 12;
const FRAME_SEAL_LEN: usize = 32;

/// Maximum size of any one Lean-authored payload or projection wire.
pub const MAX_POA_EVENT_COMPONENT_BYTES_V1: usize = 16 * 1024 * 1024;
/// Conservative limit for the opaque canonical encoding of an aggregate kind
/// or schema version.  These are bytes rather than Rust integers so the store
/// does not silently narrow Lean's `Nat`-level identity space.
pub const MAX_POA_EVENT_TAG_BYTES_V1: usize = 4096;
/// Maximum canonical postcard payload inside either sealed frame.  An event
/// contains three independently bounded component wires (payload plus two
/// nested heads), while the fourth component and tag allowance keep this a
/// deliberately conservative format bound rather than an accidental property
/// of today's postcard layout.
const MAX_POA_EVENT_FRAME_PAYLOAD_BYTES_V1: usize =
    4 * MAX_POA_EVENT_COMPONENT_BYTES_V1 + 4 * MAX_POA_EVENT_TAG_BYTES_V1 + 4096;

/// Exact identity of one independently replayable game aggregate.
///
/// `kind` is the canonical Lean adapter wire for the aggregate-kind value.  It
/// remains opaque here; the storage key is its domain-separated digest together
/// with the namespace and instance key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaAggregateIdV1 {
    namespace_id: [u8; 32],
    kind: Vec<u8>,
    key: [u8; 32],
}

impl PoaAggregateIdV1 {
    pub fn new(namespace_id: [u8; 32], kind: Vec<u8>, key: [u8; 32]) -> Result<Self> {
        let aggregate = Self {
            namespace_id,
            kind,
            key,
        };
        aggregate.validate()?;
        Ok(aggregate)
    }

    pub const fn namespace_id(&self) -> [u8; 32] {
        self.namespace_id
    }

    pub fn kind(&self) -> &[u8] {
        &self.kind
    }

    pub const fn key(&self) -> [u8; 32] {
        self.key
    }

    /// Stable storage identity for this exact aggregate wire.
    pub fn digest(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"dregg-poa-aggregate-id-v1\0");
        hasher.update(self.namespace_id);
        hasher.update((self.kind.len() as u64).to_le_bytes());
        hasher.update(&self.kind);
        hasher.update(self.key);
        hasher.finalize().into()
    }

    fn validate(&self) -> Result<()> {
        validate_tag(&self.kind, "PoA aggregate kind")
    }
}

/// Current cached projection and append cursor for one aggregate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaEventHeadV1 {
    aggregate: PoaAggregateIdV1,
    schema_version: Vec<u8>,
    sequence: u64,
    semantic_head: [u8; 32],
    projection_digest: [u8; 32],
    projection: Vec<u8>,
}

impl PoaEventHeadV1 {
    /// Build the exact zero-event projection emitted by the native Lean adapter.
    pub fn genesis(
        aggregate: PoaAggregateIdV1,
        schema_version: Vec<u8>,
        genesis_semantic_head: [u8; 32],
        projection: Vec<u8>,
    ) -> Result<Self> {
        let head = Self {
            aggregate,
            schema_version,
            sequence: 0,
            semantic_head: genesis_semantic_head,
            projection_digest: sha256(&projection),
            projection,
        };
        head.validate()?;
        Ok(head)
    }

    pub const fn aggregate(&self) -> &PoaAggregateIdV1 {
        &self.aggregate
    }

    pub fn schema_version(&self) -> &[u8] {
        &self.schema_version
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Exact Lean stream head: `StreamSpec.genesisHead` at sequence zero and
    /// the prior `EventStatement.eventDigest` thereafter.
    pub const fn semantic_head(&self) -> [u8; 32] {
        self.semantic_head
    }

    pub const fn projection_digest(&self) -> [u8; 32] {
        self.projection_digest
    }

    /// Storage identity of the `(AggregateId, SchemaVersion)` stream.
    pub fn stream_digest(&self) -> [u8; 32] {
        stream_digest(&self.aggregate, &self.schema_version)
    }

    pub fn projection(&self) -> &[u8] {
        &self.projection
    }

    /// Digest used by the exact predecessor compare-and-swap.
    pub fn digest(&self) -> [u8; 32] {
        sha256_domain(
            b"dregg-poa-event-head-digest-v1\0",
            &self.encode().expect("validated PoA event head"),
        )
    }

    fn validate(&self) -> Result<()> {
        self.aggregate.validate()?;
        validate_tag(&self.schema_version, "PoA event schema version")?;
        validate_component(&self.projection, "PoA event projection")?;
        if self.projection_digest != sha256(&self.projection) {
            return Err(integrity("PoA event head projection digest mismatch"));
        }
        Ok(())
    }

    fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        encode_frame(HEAD_MAGIC, b"dregg-poa-event-head-frame-v1\0", self)
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        let head: Self = decode_frame(
            bytes,
            HEAD_MAGIC,
            b"dregg-poa-event-head-frame-v1\0",
            "PoA event head",
        )?;
        head.validate()?;
        Ok(head)
    }
}

/// O(1) projection resume coordinate.  Consumers must still replay/audit the
/// immutable history before treating the projection as semantically valid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaProjectionCursorV1 {
    aggregate_digest: [u8; 32],
    schema_version: Vec<u8>,
    sequence: u64,
    head_digest: [u8; 32],
    semantic_head: [u8; 32],
    projection_digest: [u8; 32],
}

impl PoaProjectionCursorV1 {
    pub const fn aggregate_digest(&self) -> [u8; 32] {
        self.aggregate_digest
    }
    pub fn schema_version(&self) -> &[u8] {
        &self.schema_version
    }
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }
    pub const fn head_digest(&self) -> [u8; 32] {
        self.head_digest
    }
    pub const fn semantic_head(&self) -> [u8; 32] {
        self.semantic_head
    }
    pub const fn projection_digest(&self) -> [u8; 32] {
        self.projection_digest
    }
}

/// Structurally prepared append emitted only after native Lean has judged the
/// game event and produced its exact successor projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaEventEnvelopeV1 {
    aggregate: PoaAggregateIdV1,
    schema_version: Vec<u8>,
    sequence: u64,
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    expected_predecessor_head_digest: [u8; 32],
    semantic_predecessor: [u8; 32],
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    payload: Vec<u8>,
    successor_projection: Vec<u8>,
    genesis_projection: Option<Vec<u8>>,
    event_index: u32,
}

impl PreparedPoaEventEnvelopeV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        aggregate: PoaAggregateIdV1,
        schema_version: Vec<u8>,
        sequence: u64,
        commit_ordinal: u64,
        turn_hash: [u8; 32],
        receipt_hash: [u8; 32],
        expected_predecessor_head_digest: [u8; 32],
        semantic_predecessor: [u8; 32],
        event_digest: [u8; 32],
        payload_digest: [u8; 32],
        payload: Vec<u8>,
        successor_projection: Vec<u8>,
        genesis_projection: Option<Vec<u8>>,
        event_index: u32,
    ) -> Result<Self> {
        let candidate = Self {
            aggregate,
            schema_version,
            sequence,
            commit_ordinal,
            turn_hash,
            receipt_hash,
            expected_predecessor_head_digest,
            semantic_predecessor,
            event_digest,
            payload_digest,
            payload,
            successor_projection,
            genesis_projection,
            event_index,
        };
        candidate.validate()?;
        Ok(candidate)
    }

    pub const fn aggregate(&self) -> &PoaAggregateIdV1 {
        &self.aggregate
    }
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }
    pub const fn commit_ordinal(&self) -> u64 {
        self.commit_ordinal
    }
    pub const fn expected_predecessor_head_digest(&self) -> [u8; 32] {
        self.expected_predecessor_head_digest
    }
    /// Exact `EventStatement.predecessor` supplied by Lean.  This is the prior
    /// semantic event digest, not the Rust head-wire CAS digest.
    pub const fn semantic_predecessor(&self) -> [u8; 32] {
        self.semantic_predecessor
    }

    fn validate(&self) -> Result<()> {
        self.aggregate.validate()?;
        validate_tag(&self.schema_version, "PoA event schema version")?;
        validate_component(&self.payload, "PoA event payload")?;
        validate_component(&self.successor_projection, "PoA successor projection")?;
        if let Some(genesis) = &self.genesis_projection {
            validate_component(genesis, "PoA genesis projection")?;
        }
        if self.sequence == 0 {
            return Err(integrity("PoA event sequence zero is reserved for genesis"));
        }
        if self.event_index != 0 {
            return Err(integrity(
                "PoA event envelope v1 permits exactly event index zero per finalized turn",
            ));
        }
        Ok(())
    }
}

/// One immutable event row.  Semantic digests are opaque Lean boundary values;
/// the additional storage digest and frame seal only detect byte corruption.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaEventEnvelopeV1 {
    aggregate: PoaAggregateIdV1,
    schema_version: Vec<u8>,
    sequence: u64,
    commit_ordinal: u64,
    block_id: [u8; 32],
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    event_index: u32,
    introduced_stream: bool,
    predecessor_head_digest: [u8; 32],
    semantic_predecessor: [u8; 32],
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    storage_payload_digest: [u8; 32],
    successor_projection_digest: [u8; 32],
    predecessor_head: Vec<u8>,
    successor_head: Vec<u8>,
    payload: Vec<u8>,
}

impl PoaEventEnvelopeV1 {
    pub const fn aggregate(&self) -> &PoaAggregateIdV1 {
        &self.aggregate
    }
    pub fn schema_version(&self) -> &[u8] {
        &self.schema_version
    }
    pub const fn sequence(&self) -> u64 {
        self.sequence
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
    pub const fn semantic_predecessor(&self) -> [u8; 32] {
        self.semantic_predecessor
    }
    pub const fn event_digest(&self) -> [u8; 32] {
        self.event_digest
    }
    pub const fn payload_digest(&self) -> [u8; 32] {
        self.payload_digest
    }
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
    pub fn predecessor_head(&self) -> Result<PoaEventHeadV1> {
        PoaEventHeadV1::decode(&self.predecessor_head)
    }
    pub fn successor_head(&self) -> Result<PoaEventHeadV1> {
        PoaEventHeadV1::decode(&self.successor_head)
    }

    fn key(&self) -> [u8; 40] {
        event_key(
            stream_digest(&self.aggregate, &self.schema_version),
            self.sequence,
        )
    }

    fn validate(&self) -> Result<()> {
        self.aggregate.validate()?;
        validate_tag(&self.schema_version, "PoA event schema version")?;
        validate_component(&self.payload, "PoA event payload")?;
        if self.sequence == 0 || self.event_index != 0 {
            return Err(integrity(
                "PoA stored event has invalid sequence/event index",
            ));
        }
        if self.storage_payload_digest != sha256(&self.payload) {
            return Err(integrity("PoA event storage payload digest mismatch"));
        }
        let predecessor = self.predecessor_head()?;
        let successor = self.successor_head()?;
        if predecessor.aggregate != self.aggregate
            || successor.aggregate != self.aggregate
            || predecessor.schema_version != self.schema_version
            || successor.schema_version != self.schema_version
            || predecessor.sequence.checked_add(1) != Some(self.sequence)
            || successor.sequence != self.sequence
            || predecessor.digest() != self.predecessor_head_digest
            || predecessor.semantic_head != self.semantic_predecessor
            || successor.semantic_head != self.event_digest
            || successor.projection_digest != self.successor_projection_digest
        {
            return Err(integrity("PoA event predecessor/successor chain mismatch"));
        }
        if self.introduced_stream != (self.sequence == 1) {
            return Err(integrity("PoA event stream-introduction marker mismatch"));
        }
        Ok(())
    }

    fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        encode_frame(EVENT_MAGIC, b"dregg-poa-event-frame-v1\0", self)
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        let event: Self = decode_frame(
            bytes,
            EVENT_MAGIC,
            b"dregg-poa-event-frame-v1\0",
            "PoA event",
        )?;
        event.validate()?;
        Ok(event)
    }
}

/// Immutable structurally audited replay snapshot for the native Lean adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaEventHistoryV1 {
    genesis: PoaEventHeadV1,
    current: PoaEventHeadV1,
    events: Vec<PoaEventEnvelopeV1>,
}

impl PoaEventHistoryV1 {
    pub const fn genesis(&self) -> &PoaEventHeadV1 {
        &self.genesis
    }
    pub const fn current(&self) -> &PoaEventHeadV1 {
        &self.current
    }
    pub fn events(&self) -> &[PoaEventEnvelopeV1] {
        &self.events
    }
}

impl PersistentStore {
    pub fn load_poa_event_head(
        &self,
        aggregate: &PoaAggregateIdV1,
        schema_version: &[u8],
    ) -> Result<Option<PoaEventHeadV1>> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(POA_EVENT_HEADS_V1)?;
        validate_tag(schema_version, "PoA event schema version")?;
        let key = stream_digest(aggregate, schema_version);
        let Some(bytes) = heads.get(&key)? else {
            return Ok(None);
        };
        let head = PoaEventHeadV1::decode(bytes.value())?;
        if head.aggregate != *aggregate
            || head.schema_version != schema_version
            || head.stream_digest() != key
        {
            return Err(integrity("PoA event head key/aggregate mismatch"));
        }
        Ok(Some(head))
    }

    pub fn load_poa_projection_cursor(
        &self,
        aggregate: &PoaAggregateIdV1,
        schema_version: &[u8],
    ) -> Result<Option<PoaProjectionCursorV1>> {
        Ok(self
            .load_poa_event_head(aggregate, schema_version)?
            .map(|head| PoaProjectionCursorV1 {
                aggregate_digest: head.aggregate.digest(),
                schema_version: head.schema_version.clone(),
                sequence: head.sequence,
                head_digest: head.digest(),
                semantic_head: head.semantic_head,
                projection_digest: head.projection_digest,
            }))
    }

    pub fn load_poa_event(
        &self,
        aggregate: &PoaAggregateIdV1,
        schema_version: &[u8],
        sequence: u64,
    ) -> Result<Option<PoaEventEnvelopeV1>> {
        validate_tag(schema_version, "PoA event schema version")?;
        let key = event_key(stream_digest(aggregate, schema_version), sequence);
        let read = self.db.begin_read()?;
        let events = read.open_table(POA_EVENTS_V1)?;
        let Some(bytes) = events.get(&key)? else {
            return Ok(None);
        };
        let event = PoaEventEnvelopeV1::decode(bytes.value())?;
        if event.key() != key
            || event.aggregate != *aggregate
            || event.schema_version != schema_version
        {
            return Err(integrity("PoA event key/wire mismatch"));
        }
        Ok(Some(event))
    }

    /// Validate every row, every intermediate chain edge, every reverse-index
    /// entry, and every still-retained generic commit carrier.
    pub fn audit_poa_event_store(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(POA_EVENT_HEADS_V1)?;
        let events = read.open_table(POA_EVENTS_V1)?;
        let by_ordinal = read.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        let metadata = read.open_table(tables::METADATA)?;
        let compacted_ids = read.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        validate_tables(
            &heads,
            &events,
            &by_ordinal,
            &commits,
            &metadata,
            &compacted_ids,
        )
    }

    pub fn load_poa_event_history(
        &self,
        aggregate: &PoaAggregateIdV1,
        schema_version: &[u8],
    ) -> Result<Option<PoaEventHistoryV1>> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(POA_EVENT_HEADS_V1)?;
        let events = read.open_table(POA_EVENTS_V1)?;
        let by_ordinal = read.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        let metadata = read.open_table(tables::METADATA)?;
        let compacted_ids = read.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        validate_tables(
            &heads,
            &events,
            &by_ordinal,
            &commits,
            &metadata,
            &compacted_ids,
        )?;
        validate_tag(schema_version, "PoA event schema version")?;
        let aggregate_key = stream_digest(aggregate, schema_version);
        let Some(bytes) = heads.get(&aggregate_key)? else {
            return Ok(None);
        };
        let current = PoaEventHeadV1::decode(bytes.value())?;
        if current.aggregate != *aggregate || current.schema_version != schema_version {
            return Err(integrity("PoA event history key/aggregate mismatch"));
        }
        let capacity = usize::try_from(current.sequence)
            .map_err(|_| integrity("PoA event history exceeds usize"))?;
        let mut ordered = Vec::with_capacity(capacity);
        for sequence in 1..=current.sequence {
            let key = event_key(aggregate_key, sequence);
            let row = events
                .get(&key)?
                .ok_or_else(|| integrity("PoA event history has a sequence gap"))?;
            let event = PoaEventEnvelopeV1::decode(row.value())?;
            if event.key() != key {
                return Err(integrity("PoA event history key/wire mismatch"));
            }
            ordered.push(event);
        }
        let genesis = ordered
            .first()
            .ok_or_else(|| integrity("PoA event head exists without an event"))?
            .predecessor_head()?;
        if genesis.sequence != 0 {
            return Err(integrity("PoA event history does not start at genesis"));
        }
        Ok(Some(PoaEventHistoryV1 {
            genesis,
            current,
            events: ordered,
        }))
    }
}

pub(crate) fn initialize_poa_event_tables_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_EVENT_HEADS_V1)?;
    let _ = write.open_table(POA_EVENTS_V1)?;
    let _ = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
    Ok(())
}

pub(crate) fn stage_fresh_poa_event_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: &PreparedPoaEventEnvelopeV1,
) -> Result<()> {
    candidate.validate()?;
    if record.ordinal != commit_ordinal {
        return Err(integrity("PoA event carrying commit ordinal mismatch"));
    }
    if candidate.commit_ordinal != commit_ordinal
        || candidate.turn_hash != record.turn_hash
        || candidate.receipt_hash != record.receipt_hash
    {
        return Err(integrity(
            "PoA prepared event disagrees with carrying commit coordinates",
        ));
    }
    {
        let reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        if reverse.get(commit_ordinal)?.is_some() {
            return Err(integrity(
                "fresh commit ordinal already carries a PoA event",
            ));
        }
    }
    let aggregate_key = stream_digest(&candidate.aggregate, &candidate.schema_version);
    let (predecessor, predecessor_bytes, introduced_stream) = {
        let heads = write.open_table(POA_EVENT_HEADS_V1)?;
        match heads.get(&aggregate_key)? {
            Some(bytes) => {
                if candidate.genesis_projection.is_some() {
                    return Err(integrity(
                        "existing PoA event stream supplied a new genesis",
                    ));
                }
                let bytes = bytes.value().to_vec();
                (PoaEventHeadV1::decode(&bytes)?, bytes, false)
            }
            None => {
                let genesis_projection = candidate.genesis_projection.clone().ok_or_else(|| {
                    integrity("new PoA event stream omitted its Lean-authored genesis projection")
                })?;
                let head = PoaEventHeadV1::genesis(
                    candidate.aggregate.clone(),
                    candidate.schema_version.clone(),
                    candidate.semantic_predecessor,
                    genesis_projection,
                )?;
                let bytes = head.encode()?;
                (head, bytes, true)
            }
        }
    };
    let event = plan_event(
        predecessor,
        predecessor_bytes,
        introduced_stream,
        commit_ordinal,
        record,
        candidate,
    )?;
    let key = event.key();
    let encoded = event.encode()?;
    {
        let events = write.open_table(POA_EVENTS_V1)?;
        if events.get(&key)?.is_some() {
            return Err(integrity("PoA event sequence already exists"));
        }
    }
    {
        let mut events = write.open_table(POA_EVENTS_V1)?;
        events.insert(&key, encoded.as_slice())?;
        let mut reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        reverse.insert(commit_ordinal, &key)?;
        let mut heads = write.open_table(POA_EVENT_HEADS_V1)?;
        heads.insert(&aggregate_key, event.successor_head.as_slice())?;
    }
    Ok(())
}

pub(crate) fn verify_replayed_poa_event_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: Option<&PreparedPoaEventEnvelopeV1>,
) -> Result<()> {
    let indexed = {
        let reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        reverse.get(commit_ordinal)?.map(|entry| *entry.value())
    };
    let (Some(candidate), Some(key)) = (candidate, indexed) else {
        return match (candidate.is_some(), indexed.is_some()) {
            (false, false) => Ok(()),
            _ => Err(integrity(
                "replayed finalized turn omitted or invented its PoA event weld",
            )),
        };
    };
    let stored_bytes = {
        let events = write.open_table(POA_EVENTS_V1)?;
        events
            .get(&key)?
            .ok_or_else(|| integrity("PoA event reverse index points to no row"))?
            .value()
            .to_vec()
    };
    let stored = PoaEventEnvelopeV1::decode(&stored_bytes)?;
    if stored.key() != key
        || stored.commit_ordinal != commit_ordinal
        || stored.turn_hash != record.turn_hash
        || stored.receipt_hash != record.receipt_hash
        || stored.aggregate != candidate.aggregate
    {
        return Err(integrity(
            "replayed PoA event disagrees with commit coordinates",
        ));
    }
    let predecessor = stored.predecessor_head()?;
    let expected = plan_event(
        predecessor,
        stored.predecessor_head.clone(),
        stored.introduced_stream,
        commit_ordinal,
        record,
        candidate,
    )?;
    if expected.encode()? != stored_bytes {
        return Err(integrity("replayed PoA event is not byte-identical"));
    }
    Ok(())
}

/// Regress all game streams over a truncated generic commit-log tail.
pub(crate) fn truncate_poa_event_store_in(
    write: &WriteTransaction,
    new_cursor: u64,
) -> Result<u64> {
    // Recovery runs after the generic doomed commit records have been removed
    // from this still-uncommitted transaction, so carrier validation cannot run
    // here.  The complete PoA graph itself must nevertheless be sound before
    // any mutation: enumerating only the reverse-index tail would let a missing
    // hostile index entry strand an event whose carrier is about to disappear.
    let decoded_events = {
        let reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        let events = write.open_table(POA_EVENTS_V1)?;
        decode_indexed_events(&events, &reverse)?
    };
    {
        let heads = write.open_table(POA_EVENT_HEADS_V1)?;
        validate_stream_heads(&heads, &decoded_events)?;
    }
    let mut doomed: Vec<(u64, [u8; 40], PoaEventEnvelopeV1)> = decoded_events
        .into_iter()
        .filter_map(|(key, event)| {
            (event.commit_ordinal >= new_cursor).then_some((event.commit_ordinal, key, event))
        })
        .collect();
    doomed.sort_by_key(|(ordinal, _, _)| *ordinal);
    if doomed.is_empty() {
        return Ok(0);
    }
    let mut rewind: BTreeMap<[u8; 32], (u64, Vec<u8>, bool)> = BTreeMap::new();
    for (_, _, event) in &doomed {
        rewind
            .entry(stream_digest(&event.aggregate, &event.schema_version))
            .and_modify(|(sequence, bytes, introduced)| {
                if event.sequence < *sequence {
                    *sequence = event.sequence;
                    *bytes = event.predecessor_head.clone();
                    *introduced = event.introduced_stream;
                }
            })
            .or_insert_with(|| {
                (
                    event.sequence,
                    event.predecessor_head.clone(),
                    event.introduced_stream,
                )
            });
    }
    {
        let mut events = write.open_table(POA_EVENTS_V1)?;
        let mut reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        for (ordinal, key, _) in &doomed {
            events.remove(key)?;
            reverse.remove(*ordinal)?;
        }
        let mut heads = write.open_table(POA_EVENT_HEADS_V1)?;
        for (aggregate_key, (_, predecessor, introduced)) in rewind {
            if introduced {
                heads.remove(&aggregate_key)?;
            } else {
                heads.insert(&aggregate_key, predecessor.as_slice())?;
            }
        }
    }
    // Check the exact surviving graph while all edits are still rollback-able.
    // This is intentionally independent of generic carriers; those are audited
    // by the caller once recovery has published its lower cursor.
    {
        let events = write.open_table(POA_EVENTS_V1)?;
        let reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1)?;
        let survivors = decode_indexed_events(&events, &reverse)?;
        let heads = write.open_table(POA_EVENT_HEADS_V1)?;
        validate_stream_heads(&heads, &survivors)?;
    }
    u64::try_from(doomed.len()).map_err(|_| integrity("PoA event rewind count exceeds u64"))
}

fn plan_event(
    predecessor: PoaEventHeadV1,
    predecessor_bytes: Vec<u8>,
    introduced_stream: bool,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: &PreparedPoaEventEnvelopeV1,
) -> Result<PoaEventEnvelopeV1> {
    candidate.validate()?;
    if predecessor.aggregate != candidate.aggregate
        || predecessor.schema_version != candidate.schema_version
        || predecessor.sequence.checked_add(1) != Some(candidate.sequence)
        || predecessor.digest() != candidate.expected_predecessor_head_digest
        || predecessor.semantic_head != candidate.semantic_predecessor
        || introduced_stream != (candidate.sequence == 1)
        || introduced_stream != candidate.genesis_projection.is_some()
        || candidate.commit_ordinal != commit_ordinal
        || candidate.turn_hash != record.turn_hash
        || candidate.receipt_hash != record.receipt_hash
    {
        return Err(integrity(
            "PoA event aggregate/version/sequence/predecessor CAS mismatch",
        ));
    }
    let successor = PoaEventHeadV1 {
        aggregate: candidate.aggregate.clone(),
        schema_version: candidate.schema_version.clone(),
        sequence: candidate.sequence,
        semantic_head: candidate.event_digest,
        projection_digest: sha256(&candidate.successor_projection),
        projection: candidate.successor_projection.clone(),
    };
    successor.validate()?;
    let event = PoaEventEnvelopeV1 {
        aggregate: candidate.aggregate.clone(),
        schema_version: candidate.schema_version.clone(),
        sequence: candidate.sequence,
        commit_ordinal,
        block_id: record.block_id,
        turn_hash: record.turn_hash,
        receipt_hash: record.receipt_hash,
        event_index: candidate.event_index,
        introduced_stream,
        predecessor_head_digest: predecessor.digest(),
        semantic_predecessor: candidate.semantic_predecessor,
        event_digest: candidate.event_digest,
        payload_digest: candidate.payload_digest,
        storage_payload_digest: sha256(&candidate.payload),
        successor_projection_digest: successor.projection_digest,
        predecessor_head: predecessor_bytes,
        successor_head: successor.encode()?,
        payload: candidate.payload.clone(),
    };
    event.validate()?;
    Ok(event)
}

fn validate_tables(
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
    events: &impl ReadableTable<&'static [u8; 40], &'static [u8]>,
    by_ordinal: &impl ReadableTable<u64, &'static [u8; 40]>,
    commits: &impl ReadableTable<u64, &'static [u8]>,
    metadata: &impl ReadableTable<&'static str, u64>,
    compacted_ids: &impl ReadableTable<&'static [u8; 32], ()>,
) -> Result<()> {
    let compacted_floor = metadata
        .get(tables::META_COMMIT_COMPACTED)?
        .map(|value| value.value())
        .unwrap_or(0);
    let decoded_events = decode_indexed_events(events, by_ordinal)?;
    for event in decoded_events.values() {
        match commits.get(event.commit_ordinal)? {
            Some(commit_bytes) => {
                let commit = crate::commit_log::decode_commit_record(commit_bytes.value())?;
                if commit.ordinal != event.commit_ordinal
                    || commit.block_id != event.block_id
                    || commit.turn_hash != event.turn_hash
                    || commit.receipt_hash != event.receipt_hash
                {
                    return Err(integrity("PoA event disagrees with generic commit carrier"));
                }
            }
            None if event.commit_ordinal < compacted_floor => {
                if compacted_ids.get(&event.block_id)?.is_none() {
                    return Err(integrity(
                        "PoA event's compacted generic carrier has no retained block id",
                    ));
                }
            }
            None => return Err(integrity("PoA event has no generic commit carrier")),
        }
    }
    validate_stream_heads(heads, &decoded_events)
}

/// Decode every immutable row and prove the reverse index is an exact
/// one-to-one image of it.  This deliberately has no generic commit dependency
/// so recovery can invoke it after removing an uncommitted divergent tail.
fn decode_indexed_events(
    events: &impl ReadableTable<&'static [u8; 40], &'static [u8]>,
    by_ordinal: &impl ReadableTable<u64, &'static [u8; 40]>,
) -> Result<BTreeMap<[u8; 40], PoaEventEnvelopeV1>> {
    let mut decoded_events = BTreeMap::new();
    let mut seen_ordinals = BTreeSet::new();
    for entry in events.iter()? {
        let (key, value) = entry?;
        let key = *key.value();
        let event = PoaEventEnvelopeV1::decode(value.value())?;
        if event.key() != key {
            return Err(integrity("PoA event table key/wire mismatch"));
        }
        if !seen_ordinals.insert(event.commit_ordinal) {
            return Err(integrity("multiple PoA events share one commit ordinal"));
        }
        let indexed = by_ordinal
            .get(event.commit_ordinal)?
            .ok_or_else(|| integrity("PoA event is absent from reverse index"))?;
        if indexed.value() != &key {
            return Err(integrity("PoA event reverse index points to another row"));
        }
        decoded_events.insert(key, event);
    }
    let decoded_event_count = u64::try_from(decoded_events.len())
        .map_err(|_| integrity("PoA event row count exceeds u64"))?;
    if by_ordinal.len()? != decoded_event_count {
        return Err(integrity("PoA event reverse index cardinality mismatch"));
    }
    for entry in by_ordinal.iter()? {
        let (ordinal, key) = entry?;
        let key = *key.value();
        let event = decoded_events
            .get(&key)
            .ok_or_else(|| integrity("PoA reverse index points to no event"))?;
        if event.commit_ordinal != ordinal.value() {
            return Err(integrity("PoA reverse index ordinal/wire mismatch"));
        }
    }
    Ok(decoded_events)
}

fn validate_stream_heads(
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
    decoded_events: &BTreeMap<[u8; 40], PoaEventEnvelopeV1>,
) -> Result<()> {
    let decoded_event_count = u64::try_from(decoded_events.len())
        .map_err(|_| integrity("PoA event row count exceeds u64"))?;
    let mut expected_event_count = 0u64;
    for entry in heads.iter()? {
        let (key, value) = entry?;
        let aggregate_key = *key.value();
        let current = PoaEventHeadV1::decode(value.value())?;
        if current.stream_digest() != aggregate_key || current.sequence == 0 {
            return Err(integrity("PoA event head key/sequence mismatch"));
        }
        // Reject impossible counters before entering a sequence-sized loop.
        // A sealed-but-hostile `u64::MAX` head must be an O(1) refusal, not a
        // practically unbounded audit.
        if current.sequence > decoded_event_count {
            return Err(integrity(
                "PoA event head sequence exceeds stored row count",
            ));
        }
        expected_event_count = expected_event_count
            .checked_add(current.sequence)
            .ok_or_else(|| integrity("PoA event count overflow"))?;
        if expected_event_count > decoded_event_count {
            return Err(integrity("PoA event heads claim more rows than exist"));
        }
        let mut prior_successor: Option<Vec<u8>> = None;
        let mut prior_semantic_head = None;
        let mut prior_commit_ordinal = None;
        for sequence in 1..=current.sequence {
            let key = event_key(aggregate_key, sequence);
            let event = decoded_events
                .get(&key)
                .ok_or_else(|| integrity("PoA event chain has a sequence gap"))?;
            if event.aggregate != current.aggregate
                || event.schema_version != current.schema_version
                || (sequence == 1) != event.introduced_stream
            {
                return Err(integrity("PoA event chain aggregate/version mismatch"));
            }
            if sequence == 1 {
                let genesis = event.predecessor_head()?;
                if genesis.sequence != 0
                    || genesis.aggregate != current.aggregate
                    || genesis.schema_version != current.schema_version
                    || genesis.stream_digest() != aggregate_key
                {
                    return Err(integrity(
                        "PoA event chain has the wrong semantic genesis head",
                    ));
                }
                prior_semantic_head = Some(genesis.semantic_head);
            }
            if prior_semantic_head != Some(event.semantic_predecessor) {
                return Err(integrity("PoA event semantic predecessor chain mismatch"));
            }
            if let Some(prior) = prior_successor.as_ref()
                && prior != &event.predecessor_head
            {
                return Err(integrity("PoA event intermediate head link mismatch"));
            }
            if prior_commit_ordinal.is_some_and(|ordinal| event.commit_ordinal <= ordinal) {
                return Err(integrity(
                    "PoA event commit ordinals do not increase within the stream",
                ));
            }
            prior_successor = Some(event.successor_head.clone());
            prior_semantic_head = Some(event.event_digest);
            prior_commit_ordinal = Some(event.commit_ordinal);
        }
        if prior_successor.as_deref() != Some(value.value()) {
            return Err(integrity(
                "PoA event current head is not the final successor",
            ));
        }
    }
    if expected_event_count != decoded_event_count {
        return Err(integrity(
            "PoA event rows exist outside published aggregate heads",
        ));
    }
    Ok(())
}

fn event_key(aggregate_digest: [u8; 32], sequence: u64) -> [u8; 40] {
    let mut key = [0u8; 40];
    key[..32].copy_from_slice(&aggregate_digest);
    key[32..].copy_from_slice(&sequence.to_be_bytes());
    key
}

fn stream_digest(aggregate: &PoaAggregateIdV1, schema_version: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"dregg-poa-event-stream-v1\0");
    hasher.update(aggregate.digest());
    hasher.update((schema_version.len() as u64).to_le_bytes());
    hasher.update(schema_version);
    hasher.finalize().into()
}

fn encode_frame<T: Serialize>(magic: [u8; 4], domain: &[u8], value: &T) -> Result<Vec<u8>> {
    let payload = postcard::to_stdvec(value)?;
    if payload.len() > MAX_POA_EVENT_FRAME_PAYLOAD_BYTES_V1 {
        return Err(integrity("PoA event frame exceeds storage bound"));
    }
    let payload_len = u32::try_from(payload.len())
        .map_err(|_| integrity("PoA event frame exceeds u32 length"))?;
    let frame_len = FRAME_HEADER_LEN
        .checked_add(payload.len())
        .and_then(|n| n.checked_add(FRAME_SEAL_LEN))
        .ok_or_else(|| integrity("PoA event frame length overflow"))?;
    let mut out = Vec::with_capacity(frame_len);
    out.extend_from_slice(&magic);
    out.push(FRAME_VERSION);
    out.extend_from_slice(&[0; 3]);
    out.extend_from_slice(&payload_len.to_le_bytes());
    out.extend_from_slice(&payload);
    out.extend_from_slice(&sha256_domain(domain, &out));
    Ok(out)
}

fn decode_frame<T: for<'de> Deserialize<'de> + Serialize>(
    bytes: &[u8],
    magic: [u8; 4],
    domain: &[u8],
    what: &str,
) -> Result<T> {
    if bytes.len() < FRAME_HEADER_LEN + FRAME_SEAL_LEN {
        return Err(integrity(format!("{what} frame is truncated")));
    }
    if bytes[..4] != magic || bytes[4] != FRAME_VERSION || bytes[5..8] != [0; 3] {
        return Err(integrity(format!(
            "{what} frame has wrong magic/version/reserved bytes"
        )));
    }
    let mut len = [0u8; 4];
    len.copy_from_slice(&bytes[8..12]);
    let payload_len = u32::from_le_bytes(len) as usize;
    if payload_len > MAX_POA_EVENT_FRAME_PAYLOAD_BYTES_V1 {
        return Err(integrity(format!("{what} frame exceeds storage bound")));
    }
    let expected = FRAME_HEADER_LEN
        .checked_add(payload_len)
        .and_then(|n| n.checked_add(FRAME_SEAL_LEN))
        .ok_or_else(|| integrity(format!("{what} frame length overflow")))?;
    if expected != bytes.len() {
        return Err(integrity(format!(
            "{what} frame has trailing or missing bytes"
        )));
    }
    let payload_end = bytes.len() - FRAME_SEAL_LEN;
    if sha256_domain(domain, &bytes[..payload_end]) != bytes[payload_end..] {
        return Err(integrity(format!("{what} frame seal mismatch")));
    }
    let payload = &bytes[FRAME_HEADER_LEN..payload_end];
    let decoded: T = postcard::from_bytes(payload)?;
    if postcard::to_stdvec(&decoded)? != payload {
        return Err(integrity(format!("{what} frame is not canonical")));
    }
    Ok(decoded)
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn sha256_domain(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    hasher.finalize().into()
}

fn validate_tag(bytes: &[u8], what: &str) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_POA_EVENT_TAG_BYTES_V1 {
        return Err(integrity(format!(
            "{what} must contain 1..={MAX_POA_EVENT_TAG_BYTES_V1} bytes"
        )));
    }
    Ok(())
}

fn validate_component(bytes: &[u8], what: &str) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_POA_EVENT_COMPONENT_BYTES_V1 {
        return Err(integrity(format!(
            "{what} must contain 1..={MAX_POA_EVENT_COMPONENT_BYTES_V1} bytes"
        )));
    }
    Ok(())
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aggregate() -> PoaAggregateIdV1 {
        PoaAggregateIdV1::new([0x11; 32], vec![0], [0x22; 32]).unwrap()
    }

    fn record(ordinal: u64) -> CommitRecord {
        CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [ordinal as u8 + 1; 32],
            block_executed_up_to: ordinal,
            turn_hash: [ordinal as u8 + 2; 32],
            creator: [0x44; 32],
            receipt_hash: [ordinal as u8 + 3; 32],
            ledger_root: [ordinal as u8 + 4; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn first_candidate() -> PreparedPoaEventEnvelopeV1 {
        first_candidate_for_schema(1, 0xa1, 0)
    }

    fn first_candidate_for_schema(
        schema_byte: u8,
        event_byte: u8,
        commit_ordinal: u64,
    ) -> PreparedPoaEventEnvelopeV1 {
        let aggregate = aggregate();
        let schema = vec![schema_byte];
        let genesis_projection = vec![b'g', schema_byte];
        let genesis = PoaEventHeadV1::genesis(
            aggregate.clone(),
            schema.clone(),
            [0x50 + schema_byte; 32],
            genesis_projection.clone(),
        )
        .unwrap();
        PreparedPoaEventEnvelopeV1::new(
            aggregate,
            schema,
            1,
            commit_ordinal,
            record(commit_ordinal).turn_hash,
            record(commit_ordinal).receipt_hash,
            genesis.digest(),
            genesis.semantic_head(),
            [event_byte; 32],
            [event_byte.wrapping_add(0x10); 32],
            vec![b'e', schema_byte],
            vec![b'p', schema_byte],
            Some(genesis_projection),
            0,
        )
        .unwrap()
    }

    fn next_candidate(head: &PoaEventHeadV1, commit_ordinal: u64) -> PreparedPoaEventEnvelopeV1 {
        PreparedPoaEventEnvelopeV1::new(
            head.aggregate.clone(),
            head.schema_version.clone(),
            head.sequence + 1,
            commit_ordinal,
            record(commit_ordinal).turn_hash,
            record(commit_ordinal).receipt_hash,
            head.digest(),
            head.semantic_head(),
            [0xa2; 32],
            [0xb2; 32],
            b"lean-envelope:two".to_vec(),
            b"projection:two".to_vec(),
            None,
            0,
        )
        .unwrap()
    }

    fn commit_two_events(store: &PersistentStore) -> (PoaEventHeadV1, PoaEventHeadV1) {
        store
            .commit_finalized_turn_with_poa_event(0, &record(0), &first_candidate())
            .unwrap();
        let first_head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        store
            .commit_finalized_turn_with_poa_event(1, &record(1), &next_candidate(&first_head, 1))
            .unwrap();
        let second_head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        (first_head, second_head)
    }

    #[test]
    fn poa_event_store_enforces_component_tag_and_frame_boundaries() {
        let maximal_aggregate = PoaAggregateIdV1::new(
            [0x11; 32],
            vec![0x33; MAX_POA_EVENT_TAG_BYTES_V1],
            [0x22; 32],
        )
        .unwrap();
        assert!(
            PoaAggregateIdV1::new(
                [0x11; 32],
                vec![0x33; MAX_POA_EVENT_TAG_BYTES_V1 + 1],
                [0x22; 32],
            )
            .is_err()
        );

        let maximal_head = PoaEventHeadV1::genesis(
            maximal_aggregate,
            vec![1],
            [0x44; 32],
            vec![0x55; MAX_POA_EVENT_COMPONENT_BYTES_V1],
        )
        .unwrap();
        // The maximum semantic component must remain encodable by the enclosing
        // storage format; this guards against its frame limit drifting lower.
        maximal_head.encode().unwrap();
        drop(maximal_head);
        assert!(
            PoaEventHeadV1::genesis(
                aggregate(),
                vec![1],
                [0x44; 32],
                vec![0x55; MAX_POA_EVENT_COMPONENT_BYTES_V1 + 1],
            )
            .is_err()
        );

        // A hostile declared length is rejected before seal verification or
        // postcard decoding and does not require allocating the claimed frame.
        let mut oversized = vec![0u8; FRAME_HEADER_LEN + FRAME_SEAL_LEN];
        oversized[..4].copy_from_slice(&HEAD_MAGIC);
        oversized[4] = FRAME_VERSION;
        let declared = u32::try_from(MAX_POA_EVENT_FRAME_PAYLOAD_BYTES_V1 + 1).unwrap();
        oversized[8..12].copy_from_slice(&declared.to_le_bytes());
        let error = decode_frame::<PoaEventHeadV1>(
            &oversized,
            HEAD_MAGIC,
            b"dregg-poa-event-head-frame-v1\0",
            "PoA event head",
        )
        .unwrap_err();
        assert!(
            matches!(error, StoreError::Integrity(message) if message.contains("storage bound"))
        );
    }

    #[test]
    fn poa_event_store_appends_replays_and_exposes_projection_cursor() {
        let store = PersistentStore::open_in_memory().unwrap();
        let first = first_candidate();
        let rec0 = record(0);
        let outcome = store
            .commit_finalized_turn_with_poa_event(0, &rec0, &first)
            .unwrap();
        assert!(outcome.freshly_committed);
        let replay = store
            .commit_finalized_turn_with_poa_event(0, &rec0, &first)
            .unwrap();
        assert!(!replay.freshly_committed);

        let head1 = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        let second = next_candidate(&head1, 1);
        store
            .commit_finalized_turn_with_poa_event(1, &record(1), &second)
            .unwrap();
        store.audit_poa_event_store().unwrap();

        let history = store
            .load_poa_event_history(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        assert_eq!(history.genesis().sequence(), 0);
        assert_eq!(history.genesis().semantic_head(), [0x51; 32]);
        assert_eq!(history.current().projection(), b"projection:two");
        assert_eq!(history.events().len(), 2);
        assert_eq!(history.events()[0].payload(), [b'e', 1]);
        let cursor = store
            .load_poa_projection_cursor(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        assert_eq!(cursor.sequence(), 2);
        assert_eq!(cursor.head_digest(), history.current().digest());
        assert_eq!(cursor.projection_digest(), sha256(b"projection:two"));
    }

    #[test]
    fn poa_event_store_refuses_omission_invention_and_stale_cas_atomically() {
        let store = PersistentStore::open_in_memory().unwrap();
        let first = first_candidate();
        let rec0 = record(0);
        store
            .commit_finalized_turn_with_poa_event(0, &rec0, &first)
            .unwrap();
        assert!(store.commit_finalized_turn(0, &rec0).is_err());

        let rec1 = record(1);
        let head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        let mut wrong_ordinal = next_candidate(&head, 1);
        wrong_ordinal.commit_ordinal = 9;
        assert!(
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &wrong_ordinal)
                .is_err()
        );
        let mut wrong_turn = next_candidate(&head, 1);
        wrong_turn.turn_hash = [0x97; 32];
        assert!(
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &wrong_turn)
                .is_err()
        );
        let mut wrong_receipt = next_candidate(&head, 1);
        wrong_receipt.receipt_hash = [0x96; 32];
        assert!(
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &wrong_receipt)
                .is_err()
        );
        let mut wrong_semantic_predecessor = next_candidate(&head, 1);
        wrong_semantic_predecessor.semantic_predecessor = [0x98; 32];
        assert!(
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &wrong_semantic_predecessor,)
                .is_err()
        );
        assert_eq!(store.commit_cursor().unwrap(), 1);
        store.commit_finalized_turn(1, &rec1).unwrap();
        let invented = next_candidate(&head, 1);
        assert!(
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &invented)
                .is_err()
        );

        let mut stale = next_candidate(&head, 2);
        stale.expected_predecessor_head_digest = [0x99; 32];
        let rec2 = record(2);
        assert!(
            store
                .commit_finalized_turn_with_poa_event(2, &rec2, &stale)
                .is_err()
        );
        assert_eq!(store.commit_cursor().unwrap(), 2);
        assert!(store.commit_record_at(2).unwrap().is_none());
        assert!(
            store
                .load_poa_event(&aggregate(), &[1], 2)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn poa_event_store_stream_identity_includes_schema_version() {
        let store = PersistentStore::open_in_memory().unwrap();
        let v1 = first_candidate_for_schema(1, 0xa1, 0);
        let v2 = first_candidate_for_schema(2, 0xa2, 1);
        let mut rec0 = record(0);
        rec0.ledger_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let rec1 = record(1); // deliberately divergent so recovery removes only v2
        store
            .commit_finalized_turn_with_poa_event(0, &rec0, &v1)
            .unwrap();
        store
            .commit_finalized_turn_with_poa_event(1, &rec1, &v2)
            .unwrap();
        store.audit_poa_event_store().unwrap();
        let head_v1 = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        let head_v2 = store
            .load_poa_event_head(&aggregate(), &[2])
            .unwrap()
            .unwrap();
        assert_ne!(head_v1.stream_digest(), head_v2.stream_digest());
        assert_eq!(head_v1.projection(), [b'p', 1]);
        assert_eq!(head_v2.projection(), [b'p', 2]);
        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert!(
            store
                .load_poa_event_head(&aggregate(), &[1])
                .unwrap()
                .is_some()
        );
        assert!(
            store
                .load_poa_event_head(&aggregate(), &[2])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn poa_event_store_rejects_canonical_cross_schema_head_substitution() {
        let store = PersistentStore::open_in_memory().unwrap();
        let v1 = first_candidate_for_schema(1, 0xa1, 0);
        let v2 = first_candidate_for_schema(2, 0xa2, 1);
        store
            .commit_finalized_turn_with_poa_event(0, &record(0), &v1)
            .unwrap();
        store
            .commit_finalized_turn_with_poa_event(1, &record(1), &v2)
            .unwrap();
        store.audit_poa_event_store().unwrap();

        let v1_key = stream_digest(&aggregate(), &[1]);
        let v2_key = stream_digest(&aggregate(), &[2]);
        let write = store.db.begin_write().unwrap();
        {
            let mut heads = write.open_table(POA_EVENT_HEADS_V1).unwrap();
            let v1_bytes = heads.get(&v1_key).unwrap().unwrap().value().to_vec();
            let v2_bytes = heads.get(&v2_key).unwrap().unwrap().value().to_vec();
            // Both values remain canonical and correctly sealed; only their
            // schema-version namespace placement is hostile.
            heads.insert(&v1_key, v2_bytes.as_slice()).unwrap();
            heads.insert(&v2_key, v1_bytes.as_slice()).unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_event_store().is_err());
    }

    #[test]
    fn poa_event_store_recovery_truncates_tail_and_restores_exact_head() {
        let store = PersistentStore::open_in_memory().unwrap();
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let mut rec0 = record(0);
        rec0.ledger_root = empty_root;
        let first = first_candidate();
        store
            .commit_finalized_turn_with_poa_event(0, &rec0, &first)
            .unwrap();
        let durable_head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();

        let rec1 = record(1); // deliberately false ledger root: divergent tail
        let second = next_candidate(&durable_head, 1);
        store
            .commit_finalized_turn_with_poa_event(1, &rec1, &second)
            .unwrap();
        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(
            store
                .load_poa_event_head(&aggregate(), &[1])
                .unwrap()
                .unwrap(),
            durable_head
        );
        assert!(
            store
                .load_poa_event(&aggregate(), &[1], 2)
                .unwrap()
                .is_none()
        );
        store.audit_poa_event_store().unwrap();
    }

    #[test]
    fn poa_event_store_recovery_refuses_corrupt_index_without_partial_truncation() {
        let store = PersistentStore::open_in_memory().unwrap();
        let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
        let mut rec0 = record(0);
        rec0.ledger_root = empty_root;
        store
            .commit_finalized_turn_with_poa_event(0, &rec0, &first_candidate())
            .unwrap();
        let first_head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        let rec1 = record(1); // divergent tail, so recovery will attempt rewind
        store
            .commit_finalized_turn_with_poa_event(1, &rec1, &next_candidate(&first_head, 1))
            .unwrap();
        let second_head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();

        let write = store.db.begin_write().unwrap();
        {
            let mut reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1).unwrap();
            reverse.remove(1).unwrap();
        }
        write.commit().unwrap();

        assert!(store.recover_to_last_consistent().is_err());
        // Generic tail deletion happens earlier inside the same redb write
        // transaction.  The PoA refusal must roll all of it back.
        assert_eq!(store.commit_cursor().unwrap(), 2);
        assert!(store.commit_record_at(1).unwrap().is_some());
        assert!(
            store
                .load_poa_event(&aggregate(), &[1], 2)
                .unwrap()
                .is_some()
        );
        assert_eq!(
            store
                .load_poa_event_head(&aggregate(), &[1])
                .unwrap()
                .unwrap(),
            second_head
        );
    }

    #[test]
    fn poa_event_store_compacted_carrier_reopens_and_audits() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("poa-events-compacted.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
            let mut rec0 = record(0);
            rec0.ledger_root = empty_root;
            store
                .commit_finalized_turn_with_poa_event(0, &rec0, &first_candidate())
                .unwrap();
            let head = store
                .load_poa_event_head(&aggregate(), &[1])
                .unwrap()
                .unwrap();
            let mut rec1 = record(1);
            rec1.ledger_root = empty_root;
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &next_candidate(&head, 1))
                .unwrap();
            store
                .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                    height: 2,
                    cells: Vec::new(),
                    sovereign_commitments: Vec::new(),
                    sovereign_registrations: Vec::new(),
                })
                .unwrap();
            assert_eq!(store.compact_below(2).unwrap(), 1);
            store.audit_poa_event_store().unwrap();
        }
        let reopened = PersistentStore::open(&path).unwrap();
        reopened.audit_poa_event_store().unwrap();
        assert_eq!(reopened.commit_compacted_floor().unwrap(), 1);
        assert_eq!(
            reopened
                .load_poa_event_history(&aggregate(), &[1])
                .unwrap()
                .unwrap()
                .events()
                .len(),
            2
        );
    }

    #[test]
    fn poa_event_store_reopen_rejects_missing_compacted_carrier_identity() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("poa-events-corrupt-compacted-carrier.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            let empty_root = crate::canonical_ledger_root(&dregg_cell::Ledger::new());
            let mut rec0 = record(0);
            rec0.ledger_root = empty_root;
            store
                .commit_finalized_turn_with_poa_event(0, &rec0, &first_candidate())
                .unwrap();
            let head = store
                .load_poa_event_head(&aggregate(), &[1])
                .unwrap()
                .unwrap();
            let mut rec1 = record(1);
            rec1.ledger_root = empty_root;
            store
                .commit_finalized_turn_with_poa_event(1, &rec1, &next_candidate(&head, 1))
                .unwrap();
            store
                .store_ledger_checkpoint_snapshot(&crate::LedgerCheckpoint {
                    height: 2,
                    cells: Vec::new(),
                    sovereign_commitments: Vec::new(),
                    sovereign_registrations: Vec::new(),
                })
                .unwrap();
            assert_eq!(store.compact_below(2).unwrap(), 1);

            let write = store.db.begin_write().unwrap();
            {
                let mut compacted_ids = write
                    .open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)
                    .unwrap();
                compacted_ids.remove(&rec0.block_id).unwrap();
            }
            write.commit().unwrap();
        }
        // Opening a durable database runs the store audit, so the missing
        // compacted carrier must prevent the image from reopening at all.
        assert!(PersistentStore::open(&path).is_err());
    }

    #[test]
    fn poa_event_store_audit_rejects_reverse_index_cardinality_and_mapping() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_two_events(&store);
        store.audit_poa_event_store().unwrap();
        let key0 = event_key(stream_digest(&aggregate(), &[1]), 1);
        let key1 = event_key(stream_digest(&aggregate(), &[1]), 2);

        let write = store.db.begin_write().unwrap();
        {
            let mut reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1).unwrap();
            reverse.insert(99, &key0).unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_event_store().is_err());

        let write = store.db.begin_write().unwrap();
        {
            let mut reverse = write.open_table(POA_EVENT_BY_COMMIT_ORDINAL_V1).unwrap();
            reverse.remove(99).unwrap();
            // Preserve cardinality while swapping both coordinates.
            reverse.insert(0, &key1).unwrap();
            reverse.insert(1, &key0).unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_event_store().is_err());
    }

    #[test]
    fn poa_event_store_audit_rejects_hostile_max_sequence_in_constant_time() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut hostile =
            PoaEventHeadV1::genesis(aggregate(), vec![1], [0x51; 32], b"projection".to_vec())
                .unwrap();
        hostile.sequence = u64::MAX;
        let key = hostile.stream_digest();
        let encoded = hostile.encode().unwrap();
        let write = store.db.begin_write().unwrap();
        {
            let mut heads = write.open_table(POA_EVENT_HEADS_V1).unwrap();
            heads.insert(&key, encoded.as_slice()).unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_event_store().is_err());
    }

    #[test]
    fn poa_event_store_audit_checks_intermediate_rows_not_only_tail() {
        let store = PersistentStore::open_in_memory().unwrap();
        let first = first_candidate();
        store
            .commit_finalized_turn_with_poa_event(0, &record(0), &first)
            .unwrap();
        let head = store
            .load_poa_event_head(&aggregate(), &[1])
            .unwrap()
            .unwrap();
        let second = next_candidate(&head, 1);
        store
            .commit_finalized_turn_with_poa_event(1, &record(1), &second)
            .unwrap();
        store.audit_poa_event_store().unwrap();

        let write = store.db.begin_write().unwrap();
        {
            let mut events = write.open_table(POA_EVENTS_V1).unwrap();
            let key = event_key(stream_digest(&aggregate(), &[1]), 1);
            let mut bytes = events.get(&key).unwrap().unwrap().value().to_vec();
            let offset = FRAME_HEADER_LEN + 1;
            bytes[offset] ^= 1;
            events.insert(&key, bytes.as_slice()).unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_event_store().is_err());
    }
}
