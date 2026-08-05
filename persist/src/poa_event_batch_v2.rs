//! Atomic multi-aggregate durability for Lean-authored Path of Angels batches.
//!
//! V1 intentionally permits one PoA event at `event_index = 0` for each generic
//! `CommitRecord`.  That cannot represent one finalized turn which advances
//! Canon, a daily, an attendant, custody, and a market projection together.
//! This isolated V2 module supplies the missing storage transaction:
//!
//! * one manifest per finalized commit ordinal;
//! * dense `(commit_ordinal, event_index)` immutable rows;
//! * exact per-stream predecessor CAS and successor projections;
//! * repeated streams only when each later event explicitly continues the
//!   successor produced by the earlier indexed event;
//! * exact idempotent replay of the complete Lean-prepared batch;
//! * full graph/carrier audit and tail rewind.
//!
//! Rust does not judge game semantics or recompute Lean's `batch_digest`.
//! Registration must call `stage_fresh_poa_event_batch_in` from the same outer
//! writer which appends the full generic receipt/commit row, and must call
//! `verify_replayed_poa_event_batch_in` on the idempotent replay branch.

use redb::{ReadableTable, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

pub(crate) const POA_EVENT_BATCH_MANIFESTS_V2: TableDefinition<u64, &[u8]> =
    TableDefinition::new("poa_event_batch_manifests_v2");
pub(crate) const POA_EVENT_BATCH_EVENTS_V2: TableDefinition<&[u8; 12], &[u8]> =
    TableDefinition::new("poa_event_batch_events_v2");
pub(crate) const POA_EVENT_BATCH_HEADS_V2: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("poa_event_batch_heads_v2");

const MANIFEST_MAGIC: [u8; 4] = *b"PBM2";
const EVENT_MAGIC: [u8; 4] = *b"PBE2";
const HEAD_MAGIC: [u8; 4] = *b"PBH2";
const FRAME_VERSION: u8 = 2;
const FRAME_HEADER_LEN: usize = 12;
const FRAME_SEAL_LEN: usize = 32;

pub const MAX_POA_BATCH_EVENTS_V2: usize = 4096;
pub const MAX_POA_BATCH_COMPONENT_BYTES_V2: usize = 16 * 1024 * 1024;
pub const MAX_POA_BATCH_FRAME_BYTES_V2: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PoaWorldIdentityV2 {
    federation_id: [u8; 32],
    content_root: [u8; 32],
    activation_digest: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
}

impl PoaWorldIdentityV2 {
    pub fn new(
        federation_id: [u8; 32],
        content_root: [u8; 32],
        activation_digest: [u8; 32],
        content_session: [u8; 32],
        content_epoch: u64,
    ) -> Result<Self> {
        let world = Self {
            federation_id,
            content_root,
            activation_digest,
            content_session,
            content_epoch,
        };
        world.validate()?;
        Ok(world)
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn content_root(&self) -> [u8; 32] {
        self.content_root
    }

    pub const fn activation_digest(&self) -> [u8; 32] {
        self.activation_digest
    }

    pub const fn content_session(&self) -> [u8; 32] {
        self.content_session
    }

    pub const fn content_epoch(&self) -> u64 {
        self.content_epoch
    }

    fn validate(&self) -> Result<()> {
        if self.federation_id == [0; 32]
            || self.content_root == [0; 32]
            || self.activation_digest == [0; 32]
            || self.content_session == [0; 32]
            || self.content_epoch == 0
        {
            return Err(integrity("PoA world identity has a zero component"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalizedTurnCoordinateV2 {
    world: PoaWorldIdentityV2,
    commit_ordinal: u64,
    block_id: [u8; 32],
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    actor_root: [u8; 32],
    signer: [u8; 32],
}

impl FinalizedTurnCoordinateV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        world: PoaWorldIdentityV2,
        commit_ordinal: u64,
        block_id: [u8; 32],
        turn_hash: [u8; 32],
        receipt_hash: [u8; 32],
        actor_root: [u8; 32],
        signer: [u8; 32],
    ) -> Result<Self> {
        let coordinate = Self {
            world,
            commit_ordinal,
            block_id,
            turn_hash,
            receipt_hash,
            actor_root,
            signer,
        };
        coordinate.validate()?;
        Ok(coordinate)
    }

    pub const fn commit_ordinal(&self) -> u64 {
        self.commit_ordinal
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        &self.world
    }

    pub const fn block_id(&self) -> [u8; 32] {
        self.block_id
    }

    pub const fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }

    pub const fn receipt_hash(&self) -> [u8; 32] {
        self.receipt_hash
    }

    /// Claimed native-judge actor root.  The generic `CommitRecord` does not
    /// carry this field, so callers must bind it to their validated judge
    /// carrier before this prepared batch reaches the persistence apex.
    pub const fn actor_root(&self) -> [u8; 32] {
        self.actor_root
    }

    /// Claimed native-judge signer.  This is deliberately not inferred from a
    /// holder label or wallet address; the authority adapter must supply and
    /// validate the deployment's explicit actor derivation.
    pub const fn signer(&self) -> [u8; 32] {
        self.signer
    }

    fn validate(&self) -> Result<()> {
        self.world.validate()?;
        if self.block_id == [0; 32]
            || self.turn_hash == [0; 32]
            || self.receipt_hash == [0; 32]
            || self.actor_root == [0; 32]
            || self.signer == [0; 32]
        {
            return Err(integrity(
                "PoA V2 finalized coordinate has a zero identity component",
            ));
        }
        Ok(())
    }

    fn matches_carrier(&self, ordinal: u64, record: &CommitRecord) -> bool {
        self.commit_ordinal == ordinal
            && record.ordinal == ordinal
            && self.block_id == record.block_id
            && self.turn_hash == record.turn_hash
            && self.receipt_hash == record.receipt_hash
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PoaBatchStreamIdV2 {
    world: PoaWorldIdentityV2,
    kind: u64,
    key: [u8; 32],
    schema_version: u64,
}

impl PoaBatchStreamIdV2 {
    pub fn new(
        world: PoaWorldIdentityV2,
        kind: u64,
        key: [u8; 32],
        schema_version: u64,
    ) -> Result<Self> {
        let stream = Self {
            world,
            kind,
            key,
            schema_version,
        };
        stream.validate()?;
        Ok(stream)
    }

    pub fn digest(&self) -> [u8; 32] {
        let encoded = postcard::to_stdvec(self).expect("validated PoA V2 stream identity");
        sha256_domain(b"dregg-poa-event-batch-world-stream-v2\0", &encoded)
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        &self.world
    }

    pub const fn kind(&self) -> u64 {
        self.kind
    }

    pub const fn key(&self) -> [u8; 32] {
        self.key
    }

    pub const fn schema_version(&self) -> u64 {
        self.schema_version
    }

    fn validate(&self) -> Result<()> {
        self.world.validate()?;
        if self.kind == 0 || self.key == [0; 32] || self.schema_version == 0 {
            return Err(integrity("PoA V2 stream identity has a zero component"));
        }
        Ok(())
    }
}

/// Durable CAS authority.  This public read carrier deliberately implements
/// neither `Serialize` nor `Deserialize`; serde would otherwise bypass the
/// crate-private validated constructors despite the private fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaBatchStreamHeadV2 {
    stream: PoaBatchStreamIdV2,
    sequence: u64,
    semantic_head: [u8; 32],
    projection_digest: [u8; 32],
    projection: Vec<u8>,
}

impl PoaBatchStreamHeadV2 {
    /// Construct the exact sequence-zero CAS head for a newly deployed
    /// aggregate stream.  A Lean authority adapter uses its digest as the
    /// first event's expected storage predecessor; persistence still refuses
    /// it if a durable head for the stream already exists.
    pub(crate) fn genesis(
        stream: PoaBatchStreamIdV2,
        semantic_head: [u8; 32],
        projection_digest: [u8; 32],
        projection: Vec<u8>,
    ) -> Result<Self> {
        let head = Self {
            stream,
            sequence: 0,
            semantic_head,
            projection_digest,
            projection,
        };
        head.validate()?;
        Ok(head)
    }

    /// Construct the exact native successor head whose framed digest is
    /// supplied to the Lean planner as authenticated event authority.  This
    /// stays crate-private: only sealed persistence adapters may manufacture
    /// native CAS authority, and callers cannot use sequence zero as a second
    /// genesis path.
    pub(crate) fn successor(
        stream: PoaBatchStreamIdV2,
        sequence: u64,
        semantic_head: [u8; 32],
        projection_digest: [u8; 32],
        projection: Vec<u8>,
    ) -> Result<Self> {
        if sequence == 0 {
            return Err(integrity("PoA V2 successor head has zero sequence"));
        }
        let head = Self {
            stream,
            sequence,
            semantic_head,
            projection_digest,
            projection,
        };
        head.validate()?;
        Ok(head)
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    pub const fn semantic_head(&self) -> [u8; 32] {
        self.semantic_head
    }

    pub const fn stream(&self) -> &PoaBatchStreamIdV2 {
        &self.stream
    }

    pub const fn projection_digest(&self) -> [u8; 32] {
        self.projection_digest
    }

    pub fn projection(&self) -> &[u8] {
        &self.projection
    }

    pub fn digest(&self) -> [u8; 32] {
        sha256_domain(
            b"dregg-poa-event-batch-head-digest-v2\0",
            &self.encode().expect("validated PoA V2 head"),
        )
    }

    fn validate(&self) -> Result<()> {
        self.stream.validate()?;
        validate_component(&self.projection, "PoA projection")?;
        if self.semantic_head == [0; 32] || self.projection_digest == [0; 32] {
            return Err(integrity("PoA V2 stream head has a zero semantic digest"));
        }
        Ok(())
    }

    fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        encode_frame(
            HEAD_MAGIC,
            b"dregg-poa-event-batch-head-frame-v2\0",
            &PoaBatchStreamHeadWireV2::from(self),
        )
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        let wire: PoaBatchStreamHeadWireV2 = decode_frame(
            bytes,
            HEAD_MAGIC,
            b"dregg-poa-event-batch-head-frame-v2\0",
            "PoA V2 head",
        )?;
        let head = Self {
            stream: wire.stream,
            sequence: wire.sequence,
            semantic_head: wire.semantic_head,
            projection_digest: wire.projection_digest,
            projection: wire.projection,
        };
        head.validate()?;
        Ok(head)
    }
}

/// Private serde image for the native stream-head frame.  Keeping this type
/// private preserves durable decoding without exposing a downstream authority
/// constructor on [`PoaBatchStreamHeadV2`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PoaBatchStreamHeadWireV2 {
    stream: PoaBatchStreamIdV2,
    sequence: u64,
    semantic_head: [u8; 32],
    projection_digest: [u8; 32],
    projection: Vec<u8>,
}

impl From<&PoaBatchStreamHeadV2> for PoaBatchStreamHeadWireV2 {
    fn from(head: &PoaBatchStreamHeadV2) -> Self {
        Self {
            stream: head.stream.clone(),
            sequence: head.sequence,
            semantic_head: head.semantic_head,
            projection_digest: head.projection_digest,
            projection: head.projection.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaBatchEventV2 {
    event_index: u32,
    stream: PoaBatchStreamIdV2,
    sequence: u64,
    expected_predecessor_head_digest: [u8; 32],
    semantic_predecessor: [u8; 32],
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    payload: Vec<u8>,
    successor_projection_digest: [u8; 32],
    successor_projection: Vec<u8>,
    genesis_projection_digest: Option<[u8; 32]>,
    genesis_projection: Option<Vec<u8>>,
}

impl PreparedPoaBatchEventV2 {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        event_index: u32,
        stream: PoaBatchStreamIdV2,
        sequence: u64,
        expected_predecessor_head_digest: [u8; 32],
        semantic_predecessor: [u8; 32],
        event_digest: [u8; 32],
        payload_digest: [u8; 32],
        payload: Vec<u8>,
        successor_projection_digest: [u8; 32],
        successor_projection: Vec<u8>,
        genesis_projection_digest: Option<[u8; 32]>,
        genesis_projection: Option<Vec<u8>>,
    ) -> Result<Self> {
        let event = Self {
            event_index,
            stream,
            sequence,
            expected_predecessor_head_digest,
            semantic_predecessor,
            event_digest,
            payload_digest,
            payload,
            successor_projection_digest,
            successor_projection,
            genesis_projection_digest,
            genesis_projection,
        };
        event.validate()?;
        Ok(event)
    }

    pub const fn event_index(&self) -> u32 {
        self.event_index
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    pub const fn event_digest(&self) -> [u8; 32] {
        self.event_digest
    }

    pub const fn payload_digest(&self) -> [u8; 32] {
        self.payload_digest
    }

    pub fn stream_digest(&self) -> [u8; 32] {
        self.stream.digest()
    }

    pub const fn stream(&self) -> &PoaBatchStreamIdV2 {
        &self.stream
    }

    pub const fn expected_predecessor_head_digest(&self) -> [u8; 32] {
        self.expected_predecessor_head_digest
    }

    pub const fn semantic_predecessor(&self) -> [u8; 32] {
        self.semantic_predecessor
    }

    pub fn payload(&self) -> &[u8] {
        &self.payload
    }

    pub fn successor_projection(&self) -> &[u8] {
        &self.successor_projection
    }

    pub const fn successor_projection_digest(&self) -> [u8; 32] {
        self.successor_projection_digest
    }

    pub fn genesis_projection(&self) -> Option<&[u8]> {
        self.genesis_projection.as_deref()
    }

    pub const fn genesis_projection_digest(&self) -> Option<[u8; 32]> {
        self.genesis_projection_digest
    }

    fn validate(&self) -> Result<()> {
        self.stream.validate()?;
        if self.sequence == 0 {
            return Err(integrity(
                "PoA V2 event sequence zero is reserved for genesis",
            ));
        }
        validate_component(&self.payload, "PoA event payload")?;
        validate_component(&self.successor_projection, "PoA successor projection")?;
        if self.expected_predecessor_head_digest == [0; 32]
            || self.semantic_predecessor == [0; 32]
            || self.event_digest == [0; 32]
            || self.payload_digest == [0; 32]
            || self.successor_projection_digest == [0; 32]
        {
            return Err(integrity(
                "PoA V2 event has a zero semantic or predecessor digest",
            ));
        }
        if let Some(genesis) = &self.genesis_projection {
            validate_component(genesis, "PoA genesis projection")?;
        }
        match (
            self.genesis_projection_digest,
            self.genesis_projection.as_ref(),
        ) {
            (Some(digest), Some(_)) if digest != [0; 32] => {}
            (None, None) => {}
            _ => {
                return Err(integrity(
                    "PoA V2 genesis projection and semantic digest disagree",
                ));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaEventBatchV2 {
    coordinate: FinalizedTurnCoordinateV2,
    lean_statement: Vec<u8>,
    batch_digest: [u8; 32],
    events: Vec<PreparedPoaBatchEventV2>,
}

/// One immutable event recovered from the durable `(ordinal, event_index)`
/// journal.  The coordinate is retained per event so an aggregate replay can
/// prove exactly which finalized turn supplied each transition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaRecordedBatchEventV2 {
    coordinate: FinalizedTurnCoordinateV2,
    event: PreparedPoaBatchEventV2,
}

impl PoaRecordedBatchEventV2 {
    pub const fn coordinate(&self) -> &FinalizedTurnCoordinateV2 {
        &self.coordinate
    }

    pub const fn event(&self) -> &PreparedPoaBatchEventV2 {
        &self.event
    }
}

/// Complete replay material for one aggregate stream.  Projections are caches,
/// but retaining the exact genesis, ordered payloads, finalized coordinates,
/// and published successor makes rebuild-and-compare possible without trusting
/// a process-local game image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaEventBatchHistoryV2 {
    stream: PoaBatchStreamIdV2,
    genesis_head: PoaBatchStreamHeadV2,
    events: Vec<PoaRecordedBatchEventV2>,
    current_head: PoaBatchStreamHeadV2,
}

impl PoaEventBatchHistoryV2 {
    pub const fn stream(&self) -> &PoaBatchStreamIdV2 {
        &self.stream
    }

    pub const fn genesis_head(&self) -> &PoaBatchStreamHeadV2 {
        &self.genesis_head
    }

    pub fn events(&self) -> &[PoaRecordedBatchEventV2] {
        &self.events
    }

    pub const fn current_head(&self) -> &PoaBatchStreamHeadV2 {
        &self.current_head
    }
}

impl PreparedPoaEventBatchV2 {
    pub(crate) fn new(
        coordinate: FinalizedTurnCoordinateV2,
        lean_statement: Vec<u8>,
        batch_digest: [u8; 32],
        events: Vec<PreparedPoaBatchEventV2>,
    ) -> Result<Self> {
        let batch = Self {
            coordinate,
            lean_statement,
            batch_digest,
            events,
        };
        batch.validate()?;
        Ok(batch)
    }

    pub const fn coordinate(&self) -> &FinalizedTurnCoordinateV2 {
        &self.coordinate
    }

    pub const fn batch_digest(&self) -> [u8; 32] {
        self.batch_digest
    }

    pub fn events(&self) -> &[PreparedPoaBatchEventV2] {
        &self.events
    }

    fn validate(&self) -> Result<()> {
        self.coordinate.validate()?;
        validate_component(&self.lean_statement, "Lean PoA batch statement")?;
        if self.batch_digest == [0; 32] {
            return Err(integrity("PoA V2 batch digest is zero"));
        }
        if self.events.is_empty() || self.events.len() > MAX_POA_BATCH_EVENTS_V2 {
            return Err(integrity("PoA V2 batch must contain 1..=4096 events"));
        }
        for (expected, event) in self.events.iter().enumerate() {
            event.validate()?;
            let expected =
                u32::try_from(expected).map_err(|_| integrity("PoA V2 event index exceeds u32"))?;
            if event.event_index != expected {
                return Err(integrity("PoA V2 event indices are not dense and ordered"));
            }
            if event.stream.world != self.coordinate.world {
                return Err(integrity("PoA V2 event belongs to another world"));
            }
        }
        let wire = postcard::to_stdvec(&PreparedPoaEventBatchWireV2::from(self))?;
        if wire.len() > MAX_POA_BATCH_FRAME_BYTES_V2 {
            return Err(integrity("PoA V2 prepared batch exceeds total wire bound"));
        }
        Ok(())
    }
}

/// Private serde image for one prepared event.  The public authority carrier
/// deliberately implements neither `Serialize` nor `Deserialize`: field
/// privacy is not a type wall when serde can construct the value directly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PreparedPoaBatchEventWireV2 {
    event_index: u32,
    stream: PoaBatchStreamIdV2,
    sequence: u64,
    expected_predecessor_head_digest: [u8; 32],
    semantic_predecessor: [u8; 32],
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    payload: Vec<u8>,
    successor_projection_digest: [u8; 32],
    successor_projection: Vec<u8>,
    genesis_projection_digest: Option<[u8; 32]>,
    genesis_projection: Option<Vec<u8>>,
}

impl From<&PreparedPoaBatchEventV2> for PreparedPoaBatchEventWireV2 {
    fn from(event: &PreparedPoaBatchEventV2) -> Self {
        Self {
            event_index: event.event_index,
            stream: event.stream.clone(),
            sequence: event.sequence,
            expected_predecessor_head_digest: event.expected_predecessor_head_digest,
            semantic_predecessor: event.semantic_predecessor,
            event_digest: event.event_digest,
            payload_digest: event.payload_digest,
            payload: event.payload.clone(),
            successor_projection_digest: event.successor_projection_digest,
            successor_projection: event.successor_projection.clone(),
            genesis_projection_digest: event.genesis_projection_digest,
            genesis_projection: event.genesis_projection.clone(),
        }
    }
}

impl TryFrom<PreparedPoaBatchEventWireV2> for PreparedPoaBatchEventV2 {
    type Error = StoreError;

    fn try_from(event: PreparedPoaBatchEventWireV2) -> Result<Self> {
        Self::new(
            event.event_index,
            event.stream,
            event.sequence,
            event.expected_predecessor_head_digest,
            event.semantic_predecessor,
            event.event_digest,
            event.payload_digest,
            event.payload,
            event.successor_projection_digest,
            event.successor_projection,
            event.genesis_projection_digest,
            event.genesis_projection,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PreparedPoaEventBatchWireV2 {
    coordinate: FinalizedTurnCoordinateV2,
    lean_statement: Vec<u8>,
    batch_digest: [u8; 32],
    events: Vec<PreparedPoaBatchEventWireV2>,
}

impl From<&PreparedPoaEventBatchV2> for PreparedPoaEventBatchWireV2 {
    fn from(batch: &PreparedPoaEventBatchV2) -> Self {
        Self {
            coordinate: batch.coordinate.clone(),
            lean_statement: batch.lean_statement.clone(),
            batch_digest: batch.batch_digest,
            events: batch.events.iter().map(Into::into).collect(),
        }
    }
}

impl TryFrom<PreparedPoaEventBatchWireV2> for PreparedPoaEventBatchV2 {
    type Error = StoreError;

    fn try_from(batch: PreparedPoaEventBatchWireV2) -> Result<Self> {
        let events = batch
            .events
            .into_iter()
            .map(TryInto::try_into)
            .collect::<Result<Vec<_>>>()?;
        Self::new(
            batch.coordinate,
            batch.lean_statement,
            batch.batch_digest,
            events,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PoaEventBatchManifestWireV2 {
    prepared: PreparedPoaEventBatchWireV2,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PoaEventBatchManifestV2 {
    prepared: PreparedPoaEventBatchV2,
}

impl PoaEventBatchManifestV2 {
    fn encode(&self) -> Result<Vec<u8>> {
        self.prepared.validate()?;
        let wire = PoaEventBatchManifestWireV2 {
            prepared: PreparedPoaEventBatchWireV2::from(&self.prepared),
        };
        encode_frame(
            MANIFEST_MAGIC,
            b"dregg-poa-event-batch-manifest-frame-v2\0",
            &wire,
        )
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        let manifest: PoaEventBatchManifestWireV2 = decode_frame(
            bytes,
            MANIFEST_MAGIC,
            b"dregg-poa-event-batch-manifest-frame-v2\0",
            "PoA V2 batch manifest",
        )?;
        let prepared: PreparedPoaEventBatchV2 = manifest.prepared.try_into()?;
        prepared.validate()?;
        Ok(Self { prepared })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PoaBatchEventEnvelopeWireV2 {
    coordinate: FinalizedTurnCoordinateV2,
    event: PreparedPoaBatchEventWireV2,
    predecessor_head: Vec<u8>,
    successor_head: Vec<u8>,
    storage_payload_digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PoaBatchEventEnvelopeV2 {
    coordinate: FinalizedTurnCoordinateV2,
    event: PreparedPoaBatchEventV2,
    predecessor_head: Vec<u8>,
    successor_head: Vec<u8>,
    storage_payload_digest: [u8; 32],
}

impl PoaBatchEventEnvelopeV2 {
    fn key(&self) -> [u8; 12] {
        event_key(self.coordinate.commit_ordinal, self.event.event_index)
    }

    fn predecessor(&self) -> Result<PoaBatchStreamHeadV2> {
        PoaBatchStreamHeadV2::decode(&self.predecessor_head)
    }

    fn successor(&self) -> Result<PoaBatchStreamHeadV2> {
        PoaBatchStreamHeadV2::decode(&self.successor_head)
    }

    fn validate(&self) -> Result<()> {
        self.coordinate.validate()?;
        self.event.validate()?;
        if self.event.stream.world != self.coordinate.world {
            return Err(integrity(
                "PoA V2 event coordinate disagrees with its world-scoped stream",
            ));
        }
        if self.storage_payload_digest != sha256(&self.event.payload) {
            return Err(integrity("PoA V2 event storage payload digest mismatch"));
        }
        let predecessor = self.predecessor()?;
        let successor = self.successor()?;
        if predecessor.stream != self.event.stream
            || successor.stream != self.event.stream
            || predecessor.sequence.checked_add(1) != Some(self.event.sequence)
            || successor.sequence != self.event.sequence
            || predecessor.digest() != self.event.expected_predecessor_head_digest
            || predecessor.semantic_head != self.event.semantic_predecessor
            || successor.semantic_head != self.event.event_digest
            || successor.projection_digest != self.event.successor_projection_digest
            || successor.projection != self.event.successor_projection
        {
            return Err(integrity("PoA V2 event predecessor/successor mismatch"));
        }
        Ok(())
    }

    fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let wire = PoaBatchEventEnvelopeWireV2 {
            coordinate: self.coordinate.clone(),
            event: PreparedPoaBatchEventWireV2::from(&self.event),
            predecessor_head: self.predecessor_head.clone(),
            successor_head: self.successor_head.clone(),
            storage_payload_digest: self.storage_payload_digest,
        };
        encode_frame(
            EVENT_MAGIC,
            b"dregg-poa-event-batch-event-frame-v2\0",
            &wire,
        )
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        let wire: PoaBatchEventEnvelopeWireV2 = decode_frame(
            bytes,
            EVENT_MAGIC,
            b"dregg-poa-event-batch-event-frame-v2\0",
            "PoA V2 batch event",
        )?;
        let event = Self {
            coordinate: wire.coordinate,
            event: wire.event.try_into()?,
            predecessor_head: wire.predecessor_head,
            successor_head: wire.successor_head,
            storage_payload_digest: wire.storage_payload_digest,
        };
        event.validate()?;
        Ok(event)
    }
}

struct PlannedBatchV2 {
    manifest: Vec<u8>,
    events: Vec<([u8; 12], Vec<u8>)>,
    final_heads: BTreeMap<[u8; 32], Vec<u8>>,
}

pub(crate) fn initialize_poa_event_batch_tables_v2_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
    let _ = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
    let _ = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
    Ok(())
}

pub(crate) fn load_poa_event_batch_v2_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
) -> Result<Option<PreparedPoaEventBatchV2>> {
    let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
    manifests
        .get(commit_ordinal)?
        .map(|bytes| {
            PoaEventBatchManifestV2::decode(bytes.value()).map(|manifest| manifest.prepared)
        })
        .transpose()
}

pub(crate) fn audit_poa_event_batch_store_v2_in(write: &WriteTransaction) -> Result<()> {
    let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
    let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
    let heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
    let commits = write.open_table(tables::COMMIT_LOG)?;
    let metadata = write.open_table(tables::METADATA)?;
    let compacted_ids = write.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
    validate_tables(
        &manifests,
        &events,
        &heads,
        &commits,
        &metadata,
        &compacted_ids,
    )
}

/// Stage one complete batch.  The caller must keep this in the generic commit
/// writer; this function validates everything before its first mutation.
pub(crate) fn stage_fresh_poa_event_batch_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: &PreparedPoaEventBatchV2,
) -> Result<()> {
    candidate.validate()?;
    if !candidate.coordinate.matches_carrier(commit_ordinal, record) {
        return Err(integrity("PoA V2 batch disagrees with carrying commit"));
    }
    {
        let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        if manifests.get(commit_ordinal)?.is_some() {
            return Err(integrity(
                "fresh commit ordinal already carries a PoA V2 batch",
            ));
        }
        let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        for entry in events.iter()? {
            let (key, _) = entry?;
            if ordinal_from_event_key(key.value()) == commit_ordinal {
                return Err(integrity("PoA V2 batch has orphan rows at fresh ordinal"));
            }
        }
    }

    let plan = plan_batch(write, candidate)?;
    {
        let mut manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        manifests.insert(commit_ordinal, plan.manifest.as_slice())?;
        let mut events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        for (key, bytes) in &plan.events {
            if events.get(key)?.is_some() {
                return Err(integrity("PoA V2 event key already exists"));
            }
            events.insert(key, bytes.as_slice())?;
        }
        let mut heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        for (stream, bytes) in &plan.final_heads {
            heads.insert(stream, bytes.as_slice())?;
        }
    }
    Ok(())
}

/// Exact idempotent replay verification.  A replay never patches a missing
/// manifest/event/head and never accepts a merely similar batch digest.
pub(crate) fn verify_replayed_poa_event_batch_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: Option<&PreparedPoaEventBatchV2>,
) -> Result<()> {
    let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
    let stored = manifests.get(commit_ordinal)?;
    match (stored, candidate) {
        (None, None) => Ok(()),
        (Some(_), None) => Err(integrity("replayed turn omitted its PoA V2 batch")),
        (None, Some(_)) => Err(integrity("replayed turn invented a PoA V2 batch")),
        (Some(bytes), Some(candidate)) => {
            candidate.validate()?;
            if !candidate.coordinate.matches_carrier(commit_ordinal, record) {
                return Err(integrity("replayed PoA V2 batch disagrees with commit"));
            }
            let manifest = PoaEventBatchManifestV2::decode(bytes.value())?;
            if manifest.prepared != *candidate {
                return Err(integrity(
                    "replayed PoA V2 batch is not byte-semantic exact",
                ));
            }
            let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
            for prepared in &candidate.events {
                let key = event_key(commit_ordinal, prepared.event_index);
                let row = events
                    .get(&key)?
                    .ok_or_else(|| integrity("replayed PoA V2 batch event is missing"))?;
                let event = PoaBatchEventEnvelopeV2::decode(row.value())?;
                if event.coordinate != candidate.coordinate || event.event != *prepared {
                    return Err(integrity("replayed PoA V2 event is not exact"));
                }
            }
            Ok(())
        }
    }
}

fn plan_batch(
    write: &WriteTransaction,
    candidate: &PreparedPoaEventBatchV2,
) -> Result<PlannedBatchV2> {
    let heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
    let mut working: BTreeMap<[u8; 32], (PoaBatchStreamHeadV2, Vec<u8>)> = BTreeMap::new();
    let mut planned_events = Vec::with_capacity(candidate.events.len());

    for prepared in &candidate.events {
        let stream_key = prepared.stream.digest();
        let (predecessor, predecessor_bytes) = match working.get(&stream_key) {
            Some((head, bytes)) => {
                if prepared.genesis_projection.is_some() {
                    return Err(integrity("repeated PoA V2 stream supplied a new genesis"));
                }
                (head.clone(), bytes.clone())
            }
            None => match heads.get(&stream_key)? {
                Some(bytes) => {
                    if prepared.genesis_projection.is_some() {
                        return Err(integrity("existing PoA V2 stream supplied a new genesis"));
                    }
                    let bytes = bytes.value().to_vec();
                    (PoaBatchStreamHeadV2::decode(&bytes)?, bytes)
                }
                None => {
                    let genesis_projection =
                        prepared.genesis_projection.clone().ok_or_else(|| {
                            integrity("new PoA V2 stream omitted its Lean genesis projection")
                        })?;
                    let head = PoaBatchStreamHeadV2::genesis(
                        prepared.stream.clone(),
                        prepared.semantic_predecessor,
                        prepared.genesis_projection_digest.ok_or_else(|| {
                            integrity(
                                "new PoA V2 stream omitted its Lean genesis projection digest",
                            )
                        })?,
                        genesis_projection,
                    )?;
                    let bytes = head.encode()?;
                    (head, bytes)
                }
            },
        };
        if predecessor.stream != prepared.stream
            || predecessor.sequence.checked_add(1) != Some(prepared.sequence)
            || predecessor.digest() != prepared.expected_predecessor_head_digest
            || predecessor.semantic_head != prepared.semantic_predecessor
        {
            return Err(integrity(
                "PoA V2 batch stream sequence/predecessor CAS mismatch",
            ));
        }
        let successor = PoaBatchStreamHeadV2::successor(
            prepared.stream.clone(),
            prepared.sequence,
            prepared.event_digest,
            prepared.successor_projection_digest,
            prepared.successor_projection.clone(),
        )?;
        let successor_bytes = successor.encode()?;
        let stored = PoaBatchEventEnvelopeV2 {
            coordinate: candidate.coordinate.clone(),
            event: prepared.clone(),
            predecessor_head: predecessor_bytes,
            successor_head: successor_bytes.clone(),
            storage_payload_digest: sha256(&prepared.payload),
        };
        planned_events.push((stored.key(), stored.encode()?));
        working.insert(stream_key, (successor, successor_bytes));
    }

    let manifest = PoaEventBatchManifestV2 {
        prepared: candidate.clone(),
    }
    .encode()?;
    Ok(PlannedBatchV2 {
        manifest,
        events: planned_events,
        final_heads: working
            .into_iter()
            .map(|(stream, (_, bytes))| (stream, bytes))
            .collect(),
    })
}

fn load_poa_event_batch_history_v2_from_tables(
    events_table: &impl ReadableTable<&'static [u8; 12], &'static [u8]>,
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
    stream: &PoaBatchStreamIdV2,
) -> Result<Option<PoaEventBatchHistoryV2>> {
    stream.validate()?;
    let mut envelopes = Vec::new();
    for entry in events_table.iter()? {
        let (_, bytes) = entry?;
        let envelope = PoaBatchEventEnvelopeV2::decode(bytes.value())?;
        if envelope.event.stream == *stream {
            envelopes.push(envelope);
        }
    }

    let stream_key = stream.digest();
    let published = heads.get(&stream_key)?;
    if envelopes.is_empty() {
        if published.is_some() {
            return Err(integrity("PoA V2 stream head has no replay events"));
        }
        return Ok(None);
    }
    let published =
        published.ok_or_else(|| integrity("PoA V2 replay events have no published head"))?;
    let published = PoaBatchStreamHeadV2::decode(published.value())?;
    if published.stream != *stream {
        return Err(integrity("PoA V2 stream digest aliases another stream"));
    }

    let genesis = envelopes[0].predecessor()?;
    if genesis.stream != *stream || genesis.sequence != 0 {
        return Err(integrity("PoA V2 replay does not begin at stream genesis"));
    }
    let mut expected_predecessor = envelopes[0].predecessor_head.clone();
    let mut prior_coordinate: Option<(u64, u32)> = None;
    let mut recorded = Vec::with_capacity(envelopes.len());
    for envelope in envelopes {
        if envelope.predecessor_head != expected_predecessor {
            return Err(integrity("PoA V2 replay stream has a broken edge"));
        }
        let coordinate = (
            envelope.coordinate.commit_ordinal,
            envelope.event.event_index,
        );
        if prior_coordinate.is_some_and(|prior| prior >= coordinate) {
            return Err(integrity(
                "PoA V2 replay finalized coordinates do not increase",
            ));
        }
        expected_predecessor = envelope.successor_head.clone();
        prior_coordinate = Some(coordinate);
        recorded.push(PoaRecordedBatchEventV2 {
            coordinate: envelope.coordinate,
            event: envelope.event,
        });
    }
    let final_successor = PoaBatchStreamHeadV2::decode(&expected_predecessor)?;
    if final_successor != published {
        return Err(integrity(
            "PoA V2 replay final successor is not the published head",
        ));
    }
    Ok(Some(PoaEventBatchHistoryV2 {
        stream: stream.clone(),
        genesis_head: genesis,
        events: recorded,
        current_head: published,
    }))
}

pub(crate) fn load_poa_event_batch_history_v2_in(
    write: &WriteTransaction,
    stream: &PoaBatchStreamIdV2,
) -> Result<Option<PoaEventBatchHistoryV2>> {
    let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
    let heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
    load_poa_event_batch_history_v2_from_tables(&events, &heads, stream)
}

impl PersistentStore {
    pub fn load_poa_event_batch_v2(
        &self,
        commit_ordinal: u64,
    ) -> Result<Option<PreparedPoaEventBatchV2>> {
        let read = self.db.begin_read()?;
        let manifests = read.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        manifests
            .get(commit_ordinal)?
            .map(|bytes| PoaEventBatchManifestV2::decode(bytes.value()).map(|m| m.prepared))
            .transpose()
    }

    /// Load the current durable cursor/projection for a stream.  New event
    /// producers use this exact head as their compare-and-swap predecessor.
    pub fn load_poa_event_batch_head_v2(
        &self,
        stream: &PoaBatchStreamIdV2,
    ) -> Result<Option<PoaBatchStreamHeadV2>> {
        stream.validate()?;
        let read = self.db.begin_read()?;
        let heads = read.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        let stream_key = stream.digest();
        let Some(bytes) = heads.get(&stream_key)? else {
            return Ok(None);
        };
        let head = PoaBatchStreamHeadV2::decode(bytes.value())?;
        if head.stream != *stream {
            return Err(integrity("PoA V2 stream digest aliases another stream"));
        }
        Ok(Some(head))
    }

    /// Recover a complete aggregate journal in finalized order.  This checks
    /// every stored predecessor/successor edge and the published head before
    /// returning replay material; it never treats a snapshot as authority.
    pub fn load_poa_event_batch_history_v2(
        &self,
        stream: &PoaBatchStreamIdV2,
    ) -> Result<Option<PoaEventBatchHistoryV2>> {
        let read = self.db.begin_read()?;
        let events_table = read.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        let heads = read.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        load_poa_event_batch_history_v2_from_tables(&events_table, &heads, stream)
    }

    pub fn audit_poa_event_batch_store_v2(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let manifests = read.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        let events = read.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        let heads = read.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        let metadata = read.open_table(tables::METADATA)?;
        let compacted_ids = read.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        validate_tables(
            &manifests,
            &events,
            &heads,
            &commits,
            &metadata,
            &compacted_ids,
        )
    }
}

fn validate_tables(
    manifests: &impl ReadableTable<u64, &'static [u8]>,
    events: &impl ReadableTable<&'static [u8; 12], &'static [u8]>,
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
    commits: &impl ReadableTable<u64, &'static [u8]>,
    metadata: &impl ReadableTable<&'static str, u64>,
    compacted_ids: &impl ReadableTable<&'static [u8; 32], ()>,
) -> Result<()> {
    let compacted_floor = metadata
        .get(tables::META_COMMIT_COMPACTED)?
        .map(|value| value.value())
        .unwrap_or(0);
    let decoded_manifests = validate_structural_tables(manifests, events, heads)?;
    for (ordinal, manifest) in &decoded_manifests {
        match commits.get(*ordinal)? {
            Some(commit_bytes) => {
                let record = crate::commit_log::decode_commit_record(commit_bytes.value())?;
                if !manifest
                    .prepared
                    .coordinate
                    .matches_carrier(*ordinal, &record)
                {
                    return Err(integrity("PoA V2 manifest disagrees with commit carrier"));
                }
            }
            None if *ordinal < compacted_floor => {
                if compacted_ids
                    .get(&manifest.prepared.coordinate.block_id)?
                    .is_none()
                {
                    return Err(integrity(
                        "compacted PoA V2 carrier lacks retained block id",
                    ));
                }
            }
            None => return Err(integrity("PoA V2 manifest has no generic commit carrier")),
        }
    }
    Ok(())
}

fn validate_structural_tables(
    manifests: &impl ReadableTable<u64, &'static [u8]>,
    events: &impl ReadableTable<&'static [u8; 12], &'static [u8]>,
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
) -> Result<BTreeMap<u64, PoaEventBatchManifestV2>> {
    let mut decoded_manifests = BTreeMap::new();
    for entry in manifests.iter()? {
        let (ordinal, bytes) = entry?;
        let manifest = PoaEventBatchManifestV2::decode(bytes.value())?;
        if manifest.prepared.coordinate.commit_ordinal != ordinal.value() {
            return Err(integrity("PoA V2 manifest key/coordinate mismatch"));
        }
        decoded_manifests.insert(ordinal.value(), manifest);
    }
    let mut decoded_events = BTreeMap::new();
    let mut seen_manifest_indices: BTreeSet<(u64, u32)> = BTreeSet::new();
    for entry in events.iter()? {
        let (key, bytes) = entry?;
        let key = *key.value();
        let ordinal = ordinal_from_event_key(&key);
        let index = index_from_event_key(&key);
        let event = PoaBatchEventEnvelopeV2::decode(bytes.value())?;
        if event.key() != key {
            return Err(integrity("PoA V2 event key/wire mismatch"));
        }
        let manifest = decoded_manifests
            .get(&ordinal)
            .ok_or_else(|| integrity("PoA V2 event has no batch manifest"))?;
        let prepared = manifest
            .prepared
            .events
            .get(index as usize)
            .ok_or_else(|| integrity("PoA V2 event index exceeds manifest"))?;
        if event.coordinate != manifest.prepared.coordinate || event.event != *prepared {
            return Err(integrity("PoA V2 event disagrees with manifest"));
        }
        if !seen_manifest_indices.insert((ordinal, index)) {
            return Err(integrity("duplicate PoA V2 ordinal/event index"));
        }
        decoded_events.insert(key, event);
    }
    let expected_count: usize = decoded_manifests
        .values()
        .map(|manifest| manifest.prepared.events.len())
        .sum();
    if expected_count != decoded_events.len() {
        return Err(integrity("PoA V2 manifests/events cardinality mismatch"));
    }
    validate_stream_heads(heads, &decoded_events)?;
    Ok(decoded_manifests)
}

fn validate_stream_heads(
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
    events: &BTreeMap<[u8; 12], PoaBatchEventEnvelopeV2>,
) -> Result<()> {
    let mut streams: BTreeMap<[u8; 32], Vec<&PoaBatchEventEnvelopeV2>> = BTreeMap::new();
    for event in events.values() {
        streams
            .entry(event.event.stream.digest())
            .or_default()
            .push(event);
    }
    if heads.len()? != u64::try_from(streams.len()).map_err(|_| integrity("too many streams"))? {
        return Err(integrity("PoA V2 stream-head cardinality mismatch"));
    }
    for (stream_key, stream_events) in streams {
        let mut prior_successor: Option<Vec<u8>> = None;
        let mut prior_coordinate: Option<(u64, u32)> = None;
        for event in stream_events {
            if let Some(prior) = &prior_successor
                && prior != &event.predecessor_head
            {
                return Err(integrity("PoA V2 intermediate stream edge mismatch"));
            }
            let coordinate = (event.coordinate.commit_ordinal, event.event.event_index);
            if prior_coordinate.is_some_and(|prior| prior >= coordinate) {
                return Err(integrity("PoA V2 stream coordinates do not increase"));
            }
            prior_successor = Some(event.successor_head.clone());
            prior_coordinate = Some(coordinate);
        }
        let published = heads
            .get(&stream_key)?
            .ok_or_else(|| integrity("PoA V2 stream has no published head"))?;
        if prior_successor.as_deref() != Some(published.value()) {
            return Err(integrity("PoA V2 published head is not final successor"));
        }
        let decoded = PoaBatchStreamHeadV2::decode(published.value())?;
        if decoded.stream.digest() != stream_key {
            return Err(integrity("PoA V2 head key/stream mismatch"));
        }
    }
    Ok(())
}

/// Regress every V2 stream over a removed generic commit-log tail.  The caller
/// invokes this before publishing the lower generic cursor, in the same writer.
pub(crate) fn truncate_poa_event_batch_store_v2_in(
    write: &WriteTransaction,
    new_cursor: u64,
) -> Result<u64> {
    {
        let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        let heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        validate_structural_tables(&manifests, &events, &heads)?;
    }
    let mut doomed_ordinals = Vec::new();
    {
        let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        for entry in manifests.iter()? {
            let (ordinal, _) = entry?;
            if ordinal.value() >= new_cursor {
                doomed_ordinals.push(ordinal.value());
            }
        }
    }
    if doomed_ordinals.is_empty() {
        return Ok(0);
    }
    let doomed: BTreeSet<u64> = doomed_ordinals.iter().copied().collect();
    let mut doomed_events = Vec::new();
    {
        let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        for entry in events.iter()? {
            let (key, bytes) = entry?;
            if doomed.contains(&ordinal_from_event_key(key.value())) {
                doomed_events.push((
                    *key.value(),
                    PoaBatchEventEnvelopeV2::decode(bytes.value())?,
                ));
            }
        }
    }
    let mut rewind: BTreeMap<[u8; 32], (u64, Vec<u8>)> = BTreeMap::new();
    for (_, event) in &doomed_events {
        let stream = event.event.stream.digest();
        rewind
            .entry(stream)
            .and_modify(|(sequence, predecessor)| {
                if event.event.sequence < *sequence {
                    *sequence = event.event.sequence;
                    *predecessor = event.predecessor_head.clone();
                }
            })
            .or_insert((event.event.sequence, event.predecessor_head.clone()));
    }
    {
        let mut events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        for (key, _) in &doomed_events {
            events.remove(key)?;
        }
        let mut manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        for ordinal in doomed_ordinals {
            manifests.remove(ordinal)?;
        }
        let mut heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        for (stream, (sequence, predecessor)) in rewind {
            if sequence == 1 {
                heads.remove(&stream)?;
            } else {
                heads.insert(&stream, predecessor.as_slice())?;
            }
        }
    }
    {
        let manifests = write.open_table(POA_EVENT_BATCH_MANIFESTS_V2)?;
        let events = write.open_table(POA_EVENT_BATCH_EVENTS_V2)?;
        let heads = write.open_table(POA_EVENT_BATCH_HEADS_V2)?;
        validate_structural_tables(&manifests, &events, &heads)?;
    }
    u64::try_from(doomed_events.len()).map_err(|_| integrity("PoA V2 rewind exceeds u64"))
}

fn event_key(ordinal: u64, index: u32) -> [u8; 12] {
    let mut key = [0u8; 12];
    key[..8].copy_from_slice(&ordinal.to_be_bytes());
    key[8..].copy_from_slice(&index.to_be_bytes());
    key
}

fn ordinal_from_event_key(key: &[u8; 12]) -> u64 {
    let mut ordinal = [0u8; 8];
    ordinal.copy_from_slice(&key[..8]);
    u64::from_be_bytes(ordinal)
}

fn index_from_event_key(key: &[u8; 12]) -> u32 {
    let mut index = [0u8; 4];
    index.copy_from_slice(&key[8..]);
    u32::from_be_bytes(index)
}

fn encode_frame<T: Serialize>(magic: [u8; 4], domain: &[u8], value: &T) -> Result<Vec<u8>> {
    let payload = postcard::to_stdvec(value)?;
    if payload.is_empty() || payload.len() > MAX_POA_BATCH_FRAME_BYTES_V2 {
        return Err(integrity("PoA V2 frame exceeds storage bound"));
    }
    let payload_len =
        u32::try_from(payload.len()).map_err(|_| integrity("PoA V2 frame exceeds u32 length"))?;
    let mut out = Vec::with_capacity(FRAME_HEADER_LEN + payload.len() + FRAME_SEAL_LEN);
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
        return Err(integrity(format!("{what} frame has wrong magic/version")));
    }
    let mut len = [0u8; 4];
    len.copy_from_slice(&bytes[8..12]);
    let payload_len = u32::from_le_bytes(len) as usize;
    let expected = FRAME_HEADER_LEN
        .checked_add(payload_len)
        .and_then(|n| n.checked_add(FRAME_SEAL_LEN))
        .ok_or_else(|| integrity(format!("{what} frame length overflow")))?;
    if payload_len == 0 || payload_len > MAX_POA_BATCH_FRAME_BYTES_V2 || expected != bytes.len() {
        return Err(integrity(format!("{what} frame length mismatch")));
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

fn validate_component(bytes: &[u8], what: &str) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_POA_BATCH_COMPONENT_BYTES_V2 {
        return Err(integrity(format!("{what} has invalid length")));
    }
    Ok(())
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

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;

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

    fn world() -> PoaWorldIdentityV2 {
        PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [4; 32], 1).unwrap()
    }

    fn coordinate(ordinal: u64) -> FinalizedTurnCoordinateV2 {
        coordinate_in_world(ordinal, world())
    }

    fn coordinate_in_world(ordinal: u64, world: PoaWorldIdentityV2) -> FinalizedTurnCoordinateV2 {
        let record = record(ordinal);
        FinalizedTurnCoordinateV2::new(
            world,
            ordinal,
            record.block_id,
            record.turn_hash,
            record.receipt_hash,
            [5; 32],
            [6; 32],
        )
        .unwrap()
    }

    fn stream(kind: u8, key: u8) -> PoaBatchStreamIdV2 {
        stream_in_world(world(), kind, key)
    }

    fn stream_in_world(world: PoaWorldIdentityV2, kind: u8, key: u8) -> PoaBatchStreamIdV2 {
        PoaBatchStreamIdV2::new(world, u64::from(kind), [key; 32], 1).unwrap()
    }

    fn first_event(
        index: u32,
        stream: PoaBatchStreamIdV2,
        genesis: u8,
        event: u8,
    ) -> PreparedPoaBatchEventV2 {
        let genesis_projection = vec![b'g', genesis];
        let head = PoaBatchStreamHeadV2::genesis(
            stream.clone(),
            [genesis; 32],
            [genesis.wrapping_add(1); 32],
            genesis_projection.clone(),
        )
        .unwrap();
        PreparedPoaBatchEventV2::new(
            index,
            stream,
            1,
            head.digest(),
            head.semantic_head,
            [event; 32],
            [event.wrapping_add(1); 32],
            vec![b'e', event],
            [event.wrapping_add(2); 32],
            vec![b'p', event],
            Some(head.projection_digest()),
            Some(genesis_projection),
        )
        .unwrap()
    }

    fn batch(ordinal: u64) -> PreparedPoaEventBatchV2 {
        batch_in_world(ordinal, world())
    }

    fn batch_in_world(ordinal: u64, world: PoaWorldIdentityV2) -> PreparedPoaEventBatchV2 {
        PreparedPoaEventBatchV2::new(
            coordinate_in_world(ordinal, world.clone()),
            b"lean:event-batch-v2".to_vec(),
            [0xaa; 32],
            vec![
                first_event(0, stream_in_world(world.clone(), 2, 20), 30, 40),
                first_event(1, stream_in_world(world, 10, 21), 31, 41),
            ],
        )
        .unwrap()
    }

    #[test]
    fn public_stream_head_has_no_serde_authority_constructor() {
        trait AmbiguousIfDeserialize<Marker> {
            fn assert_not_deserializable() {}
        }
        impl<T: ?Sized> AmbiguousIfDeserialize<()> for T {}
        struct ImplementsDeserialize;
        impl<T: ?Sized + serde::de::DeserializeOwned> AmbiguousIfDeserialize<ImplementsDeserialize> for T {}

        <PoaBatchStreamHeadV2 as AmbiguousIfDeserialize<_>>::assert_not_deserializable();
    }

    #[test]
    fn v2_batch_requires_dense_indices_and_one_federation() {
        let mut events = batch(0).events;
        events[1].event_index = 4;
        assert!(PreparedPoaEventBatchV2::new(coordinate(0), vec![1], [2; 32], events).is_err());
        let mut events = batch(0).events;
        events[1].stream.world.activation_digest = [99; 32];
        assert!(PreparedPoaEventBatchV2::new(coordinate(0), vec![1], [2; 32], events).is_err());
    }

    #[test]
    fn v2_world_and_stream_identity_components_are_nonzero() {
        assert!(PoaWorldIdentityV2::new([0; 32], [2; 32], [3; 32], [4; 32], 1).is_err());
        assert!(PoaWorldIdentityV2::new([1; 32], [0; 32], [3; 32], [4; 32], 1).is_err());
        assert!(PoaWorldIdentityV2::new([1; 32], [2; 32], [0; 32], [4; 32], 1).is_err());
        assert!(PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [0; 32], 1).is_err());
        assert!(PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [4; 32], 0).is_err());
        assert!(PoaBatchStreamIdV2::new(world(), 0, [1; 32], 1).is_err());
        assert!(PoaBatchStreamIdV2::new(world(), 1, [0; 32], 1).is_err());
        assert!(PoaBatchStreamIdV2::new(world(), 1, [1; 32], 0).is_err());
        assert!(
            FinalizedTurnCoordinateV2::new(world(), 0, [0; 32], [2; 32], [3; 32], [4; 32], [5; 32])
                .is_err()
        );
    }

    #[test]
    fn v2_successor_head_builder_refuses_a_second_genesis_path() {
        assert!(
            PoaBatchStreamHeadV2::successor(stream(1, 9), 0, [10; 32], [11; 32], vec![12],)
                .is_err()
        );
        assert!(
            PoaBatchStreamHeadV2::successor(stream(1, 9), 1, [10; 32], [11; 32], vec![12],).is_ok()
        );
    }

    #[test]
    fn v2_stream_digest_commits_activation_session_and_epoch() {
        let base = world();
        let activation = PoaWorldIdentityV2::new([1; 32], [2; 32], [9; 32], [4; 32], 1).unwrap();
        let session = PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [9; 32], 1).unwrap();
        let epoch = PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [4; 32], 2).unwrap();
        let base = stream_in_world(base, 2, 20).digest();
        assert_ne!(stream_in_world(activation, 2, 20).digest(), base);
        assert_ne!(stream_in_world(session, 2, 20).digest(), base);
        assert_ne!(stream_in_world(epoch, 2, 20).digest(), base);
    }

    #[test]
    fn v2_rollback_world_cannot_reuse_current_stream_or_head() {
        let store = PersistentStore::open_in_memory().unwrap();
        let current_world = PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [4; 32], 2).unwrap();
        let current = batch_in_world(0, current_world.clone());
        let write = store.db.begin_write().unwrap();
        initialize_poa_event_batch_tables_v2_in(&write).unwrap();
        stage_fresh_poa_event_batch_in(&write, 0, &record(0), &current).unwrap();
        write.commit().unwrap();

        let rollback_world = world();
        let mut reused_event = current.events[0].clone();
        assert!(
            PreparedPoaEventBatchV2::new(
                coordinate_in_world(1, rollback_world.clone()),
                vec![1],
                [2; 32],
                vec![reused_event.clone()],
            )
            .is_err()
        );

        reused_event.stream = stream_in_world(rollback_world.clone(), 2, 20);
        let rollback = PreparedPoaEventBatchV2::new(
            coordinate_in_world(1, rollback_world),
            vec![1],
            [2; 32],
            vec![reused_event],
        )
        .unwrap();
        let write = store.db.begin_write().unwrap();
        assert!(stage_fresh_poa_event_batch_in(&write, 1, &record(1), &rollback).is_err());
        write.abort().unwrap();
    }

    #[test]
    fn v2_stage_is_atomic_across_two_streams_and_replay_is_exact() {
        let store = PersistentStore::open_in_memory().unwrap();
        let candidate = batch(0);
        let write = store.db.begin_write().unwrap();
        initialize_poa_event_batch_tables_v2_in(&write).unwrap();
        stage_fresh_poa_event_batch_in(&write, 0, &record(0), &candidate).unwrap();
        write.commit().unwrap();

        let write = store.db.begin_write().unwrap();
        verify_replayed_poa_event_batch_in(&write, 0, &record(0), Some(&candidate)).unwrap();
        let mut hostile = candidate.clone();
        hostile.events[1].payload[0] ^= 1;
        assert!(verify_replayed_poa_event_batch_in(&write, 0, &record(0), Some(&hostile)).is_err());
        write.abort().unwrap();

        let canon_stream = candidate.events[0].stream.clone();
        let history = store
            .load_poa_event_batch_history_v2(&canon_stream)
            .unwrap()
            .expect("canon history");
        assert_eq!(history.genesis_head.sequence(), 0);
        assert_eq!(history.events.len(), 1);
        assert_eq!(history.events[0].coordinate.commit_ordinal(), 0);
        assert_eq!(history.events[0].event.event_index(), 0);
        assert_eq!(history.current_head.sequence(), 1);
        assert_eq!(
            store.load_poa_event_batch_head_v2(&canon_stream).unwrap(),
            Some(history.current_head.clone())
        );
        assert_eq!(
            store
                .load_poa_event_batch_history_v2(&stream(99, 99))
                .unwrap(),
            None
        );
        assert_eq!(store.load_poa_event_batch_v2(0).unwrap(), Some(candidate));
    }

    #[test]
    fn v2_repeated_stream_must_continue_in_batch_order() {
        let store = PersistentStore::open_in_memory().unwrap();
        let first = first_event(0, stream(2, 20), 30, 40);
        let first_successor = PoaBatchStreamHeadV2 {
            stream: first.stream.clone(),
            sequence: 1,
            semantic_head: first.event_digest,
            projection_digest: first.successor_projection_digest,
            projection: first.successor_projection.clone(),
        };
        let second = PreparedPoaBatchEventV2::new(
            1,
            first.stream.clone(),
            2,
            first_successor.digest(),
            first.event_digest,
            [41; 32],
            [42; 32],
            vec![2],
            [43; 32],
            vec![3],
            None,
            None,
        )
        .unwrap();
        let candidate =
            PreparedPoaEventBatchV2::new(coordinate(0), vec![1], [2; 32], vec![first, second])
                .unwrap();
        let write = store.db.begin_write().unwrap();
        initialize_poa_event_batch_tables_v2_in(&write).unwrap();
        stage_fresh_poa_event_batch_in(&write, 0, &record(0), &candidate).unwrap();
        write.commit().unwrap();

        let history = store
            .load_poa_event_batch_history_v2(&candidate.events[0].stream)
            .unwrap()
            .expect("repeated stream history");
        assert_eq!(
            history
                .events()
                .iter()
                .map(|recorded| recorded.event().sequence())
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
        assert_eq!(history.current_head().sequence(), 2);

        let store = PersistentStore::open_in_memory().unwrap();
        let mut hostile = candidate;
        hostile.events[1].semantic_predecessor = [99; 32];
        let write = store.db.begin_write().unwrap();
        initialize_poa_event_batch_tables_v2_in(&write).unwrap();
        assert!(stage_fresh_poa_event_batch_in(&write, 0, &record(0), &hostile).is_err());
        write.abort().unwrap();
    }

    #[test]
    fn v2_truncation_rewinds_all_streams_in_the_batch() {
        let store = PersistentStore::open_in_memory().unwrap();
        let candidate = batch(0);
        let write = store.db.begin_write().unwrap();
        initialize_poa_event_batch_tables_v2_in(&write).unwrap();
        stage_fresh_poa_event_batch_in(&write, 0, &record(0), &candidate).unwrap();
        assert_eq!(truncate_poa_event_batch_store_v2_in(&write, 0).unwrap(), 2);
        write.commit().unwrap();
        assert_eq!(store.load_poa_event_batch_v2(0).unwrap(), None);
    }

    #[test]
    fn v2_audit_checks_every_manifest_event_and_carrier() {
        let store = PersistentStore::open_in_memory().unwrap();
        let carrier = record(0);
        store.commit_finalized_turn(0, &carrier).unwrap();
        let candidate = batch(0);
        let write = store.db.begin_write().unwrap();
        initialize_poa_event_batch_tables_v2_in(&write).unwrap();
        stage_fresh_poa_event_batch_in(&write, 0, &carrier, &candidate).unwrap();
        write.commit().unwrap();
        store.audit_poa_event_batch_store_v2().unwrap();

        let write = store.db.begin_write().unwrap();
        {
            let mut events = write.open_table(POA_EVENT_BATCH_EVENTS_V2).unwrap();
            events.remove(&event_key(0, 1)).unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_event_batch_store_v2().is_err());
    }
}
