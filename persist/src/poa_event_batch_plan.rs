//! Strict native decoder for the one Lean-authored PoA EventBatch V2 plan.
//!
//! `PoaEventBatchPlan` is opaque evidence that the native Lean export returned
//! a nonempty string.  It is not, by itself, native finalization authority: the
//! privileged caller must also supply the exact finalized coordinate, initial
//! durable heads, and game-judge/storage bindings from which it constructed the
//! planner input.  This module re-welds those values, requires the byte-exact
//! canonical `POA-EVENT-BATCH-PREPARED-3` JSON emitted by Lean, performs the
//! structural stream-head fold, and only then constructs persistence carriers.
//!
//! Rust does not compute a payload, event, projection, or batch semantic
//! digest here.  Those remain Lean-owned values.  Native storage-head digests
//! arrive in the authenticated event bindings and are checked again by the V2
//! persistence codec when the prepared batch is staged.

use std::collections::BTreeSet;

use serde::Deserialize;

use crate::{
    FinalizedTurnCoordinateV2, MAX_POA_BATCH_COMPONENT_BYTES_V2, MAX_POA_BATCH_EVENTS_V2,
    MAX_POA_BATCH_FRAME_BYTES_V2, PoaBatchStreamHeadV2, PoaBatchStreamIdV2, PoaWorldIdentityV2,
    PreparedPoaBatchEventV2, PreparedPoaEventBatchV2, Result, StoreError,
};

const PREPARED_FORMAT_V2: &str = "POA-EVENT-BATCH-PREPARED-3";

/// Whether an initial native stream head was loaded from durable history or
/// provisioned as the sequence-zero head for a new aggregate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaEventBatchInitialHeadOriginV2 {
    Existing,
    Genesis,
}

/// One exact initial native head supplied to the Lean planner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaEventBatchPlanInitialHeadV2 {
    head: PoaBatchStreamHeadV2,
    origin: PoaEventBatchInitialHeadOriginV2,
}

impl PoaEventBatchPlanInitialHeadV2 {
    pub(crate) fn existing(head: PoaBatchStreamHeadV2) -> Self {
        Self {
            head,
            origin: PoaEventBatchInitialHeadOriginV2::Existing,
        }
    }

    pub(crate) fn genesis(head: PoaBatchStreamHeadV2) -> Result<Self> {
        if head.sequence() != 0 {
            return Err(integrity(
                "PoA EventBatch planner genesis authority has nonzero sequence",
            ));
        }
        Ok(Self {
            head,
            origin: PoaEventBatchInitialHeadOriginV2::Genesis,
        })
    }

    pub const fn head(&self) -> &PoaBatchStreamHeadV2 {
        &self.head
    }

    pub const fn origin(&self) -> PoaEventBatchInitialHeadOriginV2 {
        self.origin
    }
}

/// Exact per-event authority retained from the finalized native/game-judge
/// seam.  In particular, the successor storage digest is not authored by Lean:
/// it is the native V2 head-codec digest that the host supplied to the planner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaEventBatchPlanEventAuthorityV2 {
    event_index: u32,
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    successor_projection_digest: [u8; 32],
    successor_storage_head_digest: [u8; 32],
}

impl PoaEventBatchPlanEventAuthorityV2 {
    pub(crate) fn new(
        event_index: u32,
        event_digest: [u8; 32],
        payload_digest: [u8; 32],
        successor_projection_digest: [u8; 32],
        successor_storage_head_digest: [u8; 32],
    ) -> Result<Self> {
        for (label, digest) in [
            ("event", event_digest),
            ("payload", payload_digest),
            ("successor projection", successor_projection_digest),
            ("successor storage head", successor_storage_head_digest),
        ] {
            require_nonzero_digest(digest, label)?;
        }
        Ok(Self {
            event_index,
            event_digest,
            payload_digest,
            successor_projection_digest,
            successor_storage_head_digest,
        })
    }
}

/// Native authority which must match the opaque Lean plan exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaEventBatchPlanAuthorityV2 {
    coordinate: FinalizedTurnCoordinateV2,
    initial_heads: Vec<PoaEventBatchPlanInitialHeadV2>,
    events: Vec<PoaEventBatchPlanEventAuthorityV2>,
}

impl PoaEventBatchPlanAuthorityV2 {
    pub(crate) fn new(
        coordinate: FinalizedTurnCoordinateV2,
        initial_heads: Vec<PoaEventBatchPlanInitialHeadV2>,
        events: Vec<PoaEventBatchPlanEventAuthorityV2>,
    ) -> Result<Self> {
        if initial_heads.is_empty() || initial_heads.len() > MAX_POA_BATCH_EVENTS_V2 {
            return Err(integrity(
                "PoA EventBatch planner authority has invalid initial-head count",
            ));
        }
        if events.is_empty() || events.len() > MAX_POA_BATCH_EVENTS_V2 {
            return Err(integrity(
                "PoA EventBatch planner authority has invalid event count",
            ));
        }
        let world = coordinate.world();
        let mut streams = BTreeSet::new();
        for initial in &initial_heads {
            if initial.head.stream().world() != world
                || !streams.insert(initial.head.stream().clone())
            {
                return Err(integrity(
                    "PoA EventBatch planner authority has a duplicate or foreign initial stream",
                ));
            }
            require_nonzero_digest(initial.head.semantic_head(), "initial semantic head")?;
            require_nonzero_digest(initial.head.projection_digest(), "initial projection")?;
            require_nonzero_digest(initial.head.digest(), "initial storage head")?;
            validate_component(initial.head.projection(), "initial projection")?;
        }
        for (expected, event) in events.iter().enumerate() {
            let expected = u32::try_from(expected)
                .map_err(|_| integrity("PoA EventBatch authority index exceeds u32"))?;
            if event.event_index != expected {
                return Err(integrity(
                    "PoA EventBatch planner authority event indices are not dense",
                ));
            }
        }
        Ok(Self {
            coordinate,
            initial_heads,
            events,
        })
    }

    pub const fn coordinate(&self) -> &FinalizedTurnCoordinateV2 {
        &self.coordinate
    }
}

/// Strictly decode the exact native Lean plan and construct the only durable
/// EventBatch V2 candidate admitted by this boundary.
pub fn prepare_poa_event_batch_v2_from_lean_plan(
    plan: &dregg_lean_ffi::poa_event_batch_ffi::PoaEventBatchPlan,
    authority: &PoaEventBatchPlanAuthorityV2,
) -> Result<PreparedPoaEventBatchV2> {
    decode_plan_str(plan.as_str(), authority)
}

fn decode_plan_str(
    encoded: &str,
    authority: &PoaEventBatchPlanAuthorityV2,
) -> Result<PreparedPoaEventBatchV2> {
    if encoded.is_empty() || encoded.len() > MAX_POA_BATCH_FRAME_BYTES_V2 {
        return Err(integrity(
            "Lean PoA EventBatch plan has invalid total length",
        ));
    }
    let wire: PreparedBatchWire = serde_json::from_str(encoded)
        .map_err(|_| integrity("Lean PoA EventBatch plan is not strict typed JSON"))?;
    validate_wire_shape(&wire)?;
    if encode_prepared_batch(&wire) != encoded {
        return Err(integrity(
            "Lean PoA EventBatch plan is not byte-exact canonical JSON",
        ));
    }

    let coordinate = decode_coordinate(&wire.coordinate)?;
    if &coordinate != authority.coordinate() {
        return Err(integrity(
            "Lean PoA EventBatch plan disagrees with finalized coordinate authority",
        ));
    }
    if wire.events.len() != authority.events.len() {
        return Err(integrity(
            "Lean PoA EventBatch plan event count disagrees with native authority",
        ));
    }

    let expected_statement = encode_semantic_statement(&wire.coordinate, &wire.events);
    let lean_statement = decode_component(&wire.lean_statement_hex, "Lean batch statement")?;
    if lean_statement != expected_statement.as_bytes() {
        return Err(integrity(
            "Lean PoA EventBatch statement bytes disagree with decoded plan",
        ));
    }
    let batch_digest = decode_digest(&wire.batch_digest, "batch digest")?;

    let mut working: Vec<WorkingHead> = authority
        .initial_heads
        .iter()
        .map(WorkingHead::from_initial)
        .collect();
    let mut used_streams = BTreeSet::new();
    let mut prepared = Vec::with_capacity(wire.events.len());
    for (expected_index, (event, binding)) in
        wire.events.iter().zip(authority.events.iter()).enumerate()
    {
        let expected_index = u32::try_from(expected_index)
            .map_err(|_| integrity("Lean PoA EventBatch event index exceeds u32"))?;
        if event.event_index != expected_index || binding.event_index != expected_index {
            return Err(integrity(
                "Lean PoA EventBatch plan event indices are not dense",
            ));
        }
        let stream = decode_stream(&event.stream)?;
        if stream.world() != coordinate.world() {
            return Err(integrity(
                "Lean PoA EventBatch plan event belongs to another world",
            ));
        }
        let event_digest = decode_digest(&event.event_digest, "event digest")?;
        let payload_digest = decode_digest(&event.payload_digest, "payload digest")?;
        let successor_projection_digest = decode_digest(
            &event.successor_projection_digest,
            "successor projection digest",
        )?;
        if event_digest != binding.event_digest
            || payload_digest != binding.payload_digest
            || successor_projection_digest != binding.successor_projection_digest
        {
            return Err(integrity(
                "Lean PoA EventBatch plan event disagrees with native judge authority",
            ));
        }

        let head_index = working
            .iter()
            .position(|head| head.stream == stream)
            .ok_or_else(|| integrity("Lean PoA EventBatch plan names an unknown stream"))?;
        let before = &working[head_index];
        let expected_predecessor = decode_digest(
            &event.expected_predecessor_head_digest,
            "expected predecessor storage head",
        )?;
        let semantic_predecessor =
            decode_digest(&event.semantic_predecessor, "semantic predecessor")?;
        if before.sequence.checked_add(1) != Some(event.sequence)
            || before.storage_head_digest != expected_predecessor
            || before.semantic_head != semantic_predecessor
        {
            return Err(integrity(
                "Lean PoA EventBatch plan stream predecessor fold disagrees with native heads",
            ));
        }

        let payload = decode_component(&event.payload_hex, "event payload")?;
        let successor_projection =
            decode_component(&event.successor_projection_hex, "successor projection")?;
        let genesis_projection_digest = event
            .genesis_projection_digest
            .as_deref()
            .map(|digest| decode_digest(digest, "genesis projection digest"))
            .transpose()?;
        let genesis_projection = event
            .genesis_projection_hex
            .as_deref()
            .map(|bytes| decode_component(bytes, "genesis projection"))
            .transpose()?;
        let first_use = used_streams.insert(stream.clone());
        match (
            first_use,
            before.origin,
            genesis_projection_digest,
            genesis_projection.as_deref(),
        ) {
            (true, PoaEventBatchInitialHeadOriginV2::Genesis, Some(digest), Some(bytes))
                if digest == before.projection_digest && bytes == before.projection.as_slice() => {}
            (true, PoaEventBatchInitialHeadOriginV2::Existing, None, None)
            | (false, _, None, None) => {}
            _ => {
                return Err(integrity(
                    "Lean PoA EventBatch plan genesis projection disagrees with native head origin",
                ));
            }
        }

        let candidate = PreparedPoaBatchEventV2::new(
            event.event_index,
            stream.clone(),
            event.sequence,
            expected_predecessor,
            semantic_predecessor,
            event_digest,
            payload_digest,
            payload,
            successor_projection_digest,
            successor_projection.clone(),
            genesis_projection_digest,
            genesis_projection,
        )?;
        working[head_index] = WorkingHead {
            stream,
            sequence: event.sequence,
            semantic_head: event_digest,
            storage_head_digest: binding.successor_storage_head_digest,
            projection_digest: successor_projection_digest,
            projection: successor_projection,
            origin: PoaEventBatchInitialHeadOriginV2::Existing,
        };
        prepared.push(candidate);
    }

    if wire.successor_heads.len() != working.len() {
        return Err(integrity(
            "Lean PoA EventBatch successor-head count disagrees with structural fold",
        ));
    }
    for (wire_head, expected) in wire.successor_heads.iter().zip(&working) {
        if !wire_head.matches(expected)? {
            return Err(integrity(
                "Lean PoA EventBatch successor heads disagree with structural fold",
            ));
        }
    }

    PreparedPoaEventBatchV2::new(coordinate, lean_statement, batch_digest, prepared)
}

#[derive(Clone, Debug)]
struct WorkingHead {
    stream: PoaBatchStreamIdV2,
    sequence: u64,
    semantic_head: [u8; 32],
    storage_head_digest: [u8; 32],
    projection_digest: [u8; 32],
    projection: Vec<u8>,
    origin: PoaEventBatchInitialHeadOriginV2,
}

impl WorkingHead {
    fn from_initial(initial: &PoaEventBatchPlanInitialHeadV2) -> Self {
        Self {
            stream: initial.head.stream().clone(),
            sequence: initial.head.sequence(),
            semantic_head: initial.head.semantic_head(),
            storage_head_digest: initial.head.digest(),
            projection_digest: initial.head.projection_digest(),
            projection: initial.head.projection().to_vec(),
            origin: initial.origin,
        }
    }
}

const fn origin_name(origin: PoaEventBatchInitialHeadOriginV2) -> &'static str {
    match origin {
        PoaEventBatchInitialHeadOriginV2::Existing => "existing",
        PoaEventBatchInitialHeadOriginV2::Genesis => "genesis",
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct PreparedBatchWire {
    format: String,
    coordinate: CoordinateWire,
    lean_statement_hex: String,
    batch_digest: String,
    events: Vec<PreparedEventWire>,
    successor_heads: Vec<HeadWire>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct WorldWire {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CoordinateWire {
    world: WorldWire,
    commit_ordinal: u64,
    block_id: String,
    turn_hash: String,
    receipt_hash: String,
    actor_root: String,
    signer: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct StreamWire {
    world: WorldWire,
    kind: u64,
    key: String,
    version: u64,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct PreparedEventWire {
    event_index: u32,
    stream: StreamWire,
    sequence: u64,
    expected_predecessor_head_digest: String,
    semantic_predecessor: String,
    event_digest: String,
    payload_digest: String,
    payload_hex: String,
    successor_projection_digest: String,
    successor_projection_hex: String,
    genesis_projection_digest: Option<String>,
    genesis_projection_hex: Option<String>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeadWire {
    stream: StreamWire,
    sequence: u64,
    semantic_head: String,
    storage_head_digest: String,
    projection_hex: String,
    origin: String,
}

impl HeadWire {
    fn matches(&self, expected: &WorkingHead) -> Result<bool> {
        Ok(decode_stream(&self.stream)? == expected.stream
            && self.sequence == expected.sequence
            && decode_digest(&self.semantic_head, "successor semantic head")?
                == expected.semantic_head
            && decode_digest(&self.storage_head_digest, "successor storage head")?
                == expected.storage_head_digest
            && decode_component(&self.projection_hex, "successor head projection")?
                == expected.projection
            && self.origin == origin_name(expected.origin))
    }
}

fn validate_wire_shape(wire: &PreparedBatchWire) -> Result<()> {
    if wire.format != PREPARED_FORMAT_V2 {
        return Err(integrity("wrong Lean PoA EventBatch prepared format"));
    }
    if wire.events.is_empty() || wire.events.len() > MAX_POA_BATCH_EVENTS_V2 {
        return Err(integrity(
            "Lean PoA EventBatch plan has invalid event count",
        ));
    }
    if wire.successor_heads.is_empty() || wire.successor_heads.len() > MAX_POA_BATCH_EVENTS_V2 {
        return Err(integrity(
            "Lean PoA EventBatch plan has invalid successor-head count",
        ));
    }
    decode_coordinate(&wire.coordinate)?;
    decode_digest(&wire.batch_digest, "batch digest")?;
    decode_component(&wire.lean_statement_hex, "Lean batch statement")?;
    for event in &wire.events {
        decode_stream(&event.stream)?;
        decode_digest(
            &event.expected_predecessor_head_digest,
            "expected predecessor storage head",
        )?;
        decode_digest(&event.semantic_predecessor, "semantic predecessor")?;
        decode_digest(&event.event_digest, "event digest")?;
        decode_digest(&event.payload_digest, "payload digest")?;
        decode_component(&event.payload_hex, "event payload")?;
        decode_digest(
            &event.successor_projection_digest,
            "successor projection digest",
        )?;
        decode_component(&event.successor_projection_hex, "successor projection")?;
        match (
            event.genesis_projection_digest.as_deref(),
            event.genesis_projection_hex.as_deref(),
        ) {
            (Some(digest), Some(bytes)) => {
                decode_digest(digest, "genesis projection digest")?;
                decode_component(bytes, "genesis projection")?;
            }
            (None, None) => {}
            _ => {
                return Err(integrity(
                    "Lean PoA EventBatch genesis projection fields disagree",
                ));
            }
        }
    }
    for head in &wire.successor_heads {
        decode_stream(&head.stream)?;
        decode_digest(&head.semantic_head, "successor semantic head")?;
        decode_digest(&head.storage_head_digest, "successor storage head")?;
        decode_component(&head.projection_hex, "successor head projection")?;
        if head.origin != "existing" && head.origin != "genesis" {
            return Err(integrity("unknown Lean PoA EventBatch head origin"));
        }
        if head.origin == "genesis" && head.sequence != 0 {
            return Err(integrity(
                "Lean PoA EventBatch genesis successor has nonzero sequence",
            ));
        }
    }
    Ok(())
}

fn decode_coordinate(wire: &CoordinateWire) -> Result<FinalizedTurnCoordinateV2> {
    let world = decode_world(&wire.world)?;
    FinalizedTurnCoordinateV2::new(
        world,
        wire.commit_ordinal,
        decode_digest(&wire.block_id, "block id")?,
        decode_digest(&wire.turn_hash, "turn hash")?,
        decode_digest(&wire.receipt_hash, "receipt hash")?,
        decode_digest(&wire.actor_root, "actor root")?,
        decode_digest(&wire.signer, "signer")?,
    )
}

fn decode_world(wire: &WorldWire) -> Result<PoaWorldIdentityV2> {
    PoaWorldIdentityV2::new(
        decode_digest(&wire.federation_id, "world federation")?,
        decode_digest(&wire.content_root, "world content root")?,
        decode_digest(&wire.activation_digest, "world activation")?,
        decode_digest(&wire.content_session, "world content session")?,
        wire.content_epoch,
    )
}

fn decode_stream(wire: &StreamWire) -> Result<PoaBatchStreamIdV2> {
    PoaBatchStreamIdV2::new(
        decode_world(&wire.world)?,
        wire.kind,
        decode_digest(&wire.key, "stream key")?,
        wire.version,
    )
}

fn decode_digest(encoded: &str, label: &str) -> Result<[u8; 32]> {
    if encoded.len() != 64
        || !encoded
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(integrity(format!(
            "Lean PoA EventBatch {label} is not exactly 64 lowercase hexadecimal digits"
        )));
    }
    let mut digest = [0u8; 32];
    for (index, pair) in encoded.as_bytes().chunks_exact(2).enumerate() {
        digest[index] = (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]);
    }
    require_nonzero_digest(digest, label)?;
    Ok(digest)
}

fn decode_component(encoded: &str, label: &str) -> Result<Vec<u8>> {
    if encoded.is_empty()
        || encoded.len() % 2 != 0
        || encoded.len() > MAX_POA_BATCH_COMPONENT_BYTES_V2.saturating_mul(2)
        || !encoded
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(integrity(format!(
            "Lean PoA EventBatch {label} is not bounded canonical lowercase hex"
        )));
    }
    Ok(encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]))
        .collect())
}

fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => unreachable!("caller validated lowercase hexadecimal"),
    }
}

fn require_nonzero_digest(digest: [u8; 32], label: &str) -> Result<()> {
    if digest == [0; 32] {
        return Err(integrity(format!("Lean PoA EventBatch {label} is zero")));
    }
    Ok(())
}

fn validate_component(bytes: &[u8], label: &str) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_POA_BATCH_COMPONENT_BYTES_V2 {
        return Err(integrity(format!(
            "PoA EventBatch authority {label} has invalid length"
        )));
    }
    Ok(())
}

fn encode_prepared_batch(wire: &PreparedBatchWire) -> String {
    format!(
        "{{\"format\":{},\"coordinate\":{},\"lean_statement_hex\":{},\"batch_digest\":{},\"events\":[{}],\"successor_heads\":[{}]}}",
        json_string(&wire.format),
        encode_coordinate(&wire.coordinate),
        json_string(&wire.lean_statement_hex),
        json_string(&wire.batch_digest),
        wire.events
            .iter()
            .map(encode_event)
            .collect::<Vec<_>>()
            .join(","),
        wire.successor_heads
            .iter()
            .map(encode_head)
            .collect::<Vec<_>>()
            .join(","),
    )
}

fn encode_world(wire: &WorldWire) -> String {
    format!(
        "{{\"federation_id\":{},\"content_root\":{},\"activation_digest\":{},\"content_session\":{},\"content_epoch\":{}}}",
        json_string(&wire.federation_id),
        json_string(&wire.content_root),
        json_string(&wire.activation_digest),
        json_string(&wire.content_session),
        wire.content_epoch,
    )
}

fn encode_coordinate(wire: &CoordinateWire) -> String {
    format!(
        "{{\"world\":{},\"commit_ordinal\":{},\"block_id\":{},\"turn_hash\":{},\"receipt_hash\":{},\"actor_root\":{},\"signer\":{}}}",
        encode_world(&wire.world),
        wire.commit_ordinal,
        json_string(&wire.block_id),
        json_string(&wire.turn_hash),
        json_string(&wire.receipt_hash),
        json_string(&wire.actor_root),
        json_string(&wire.signer),
    )
}

fn encode_stream(wire: &StreamWire) -> String {
    format!(
        "{{\"world\":{},\"kind\":{},\"key\":{},\"version\":{}}}",
        encode_world(&wire.world),
        wire.kind,
        json_string(&wire.key),
        wire.version,
    )
}

fn encode_event(wire: &PreparedEventWire) -> String {
    format!(
        "{{\"event_index\":{},\"stream\":{},\"sequence\":{},\"expected_predecessor_head_digest\":{},\"semantic_predecessor\":{},\"event_digest\":{},\"payload_digest\":{},\"payload_hex\":{},\"successor_projection_digest\":{},\"successor_projection_hex\":{},\"genesis_projection_digest\":{},\"genesis_projection_hex\":{}}}",
        wire.event_index,
        encode_stream(&wire.stream),
        wire.sequence,
        json_string(&wire.expected_predecessor_head_digest),
        json_string(&wire.semantic_predecessor),
        json_string(&wire.event_digest),
        json_string(&wire.payload_digest),
        json_string(&wire.payload_hex),
        json_string(&wire.successor_projection_digest),
        json_string(&wire.successor_projection_hex),
        option_json_string(wire.genesis_projection_digest.as_deref()),
        option_json_string(wire.genesis_projection_hex.as_deref()),
    )
}

fn encode_head(wire: &HeadWire) -> String {
    format!(
        "{{\"stream\":{},\"sequence\":{},\"semantic_head\":{},\"storage_head_digest\":{},\"projection_hex\":{},\"origin\":{}}}",
        encode_stream(&wire.stream),
        wire.sequence,
        json_string(&wire.semantic_head),
        json_string(&wire.storage_head_digest),
        json_string(&wire.projection_hex),
        json_string(&wire.origin),
    )
}

fn encode_semantic_statement(coordinate: &CoordinateWire, events: &[PreparedEventWire]) -> String {
    let events = events
        .iter()
        .map(|event| {
            format!(
                "{{\"event_index\":{},\"statement\":{{\"namespace_id\":{},\"kind\":{},\"key\":{},\"version\":{},\"sequence\":{},\"predecessor\":{},\"payload_digest\":{}}},\"event_digest\":{}}}",
                event.event_index,
                json_string(&event.stream.world.federation_id),
                event.stream.kind,
                json_string(&event.stream.key),
                event.stream.version,
                event.sequence,
                json_string(&event.semantic_predecessor),
                json_string(&event.payload_digest),
                json_string(&event.event_digest),
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"coordinate\":{},\"events\":[{}]}}",
        encode_coordinate(coordinate),
        events
    )
}

fn json_string(value: &str) -> String {
    serde_json::to_string(value).expect("serializing a string cannot fail")
}

fn option_json_string(value: Option<&str>) -> String {
    value.map(json_string).unwrap_or_else(|| "null".to_owned())
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Write as _;

    struct Fixture {
        encoded: String,
        authority: PoaEventBatchPlanAuthorityV2,
    }

    fn digest(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn hex(bytes: &[u8]) -> String {
        let mut output = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
        }
        output
    }

    fn fixture() -> Fixture {
        let world =
            PoaWorldIdentityV2::new(digest(1), digest(2), digest(3), digest(4), 5).expect("world");
        let coordinate = FinalizedTurnCoordinateV2::new(
            world.clone(),
            7,
            digest(8),
            digest(9),
            digest(10),
            digest(11),
            digest(12),
        )
        .expect("coordinate");
        let stream = PoaBatchStreamIdV2::new(world, 2, digest(20), 1).expect("stream");
        let initial =
            PoaBatchStreamHeadV2::genesis(stream.clone(), digest(30), digest(32), vec![0x20, 0x21])
                .expect("head");
        let binding = PoaEventBatchPlanEventAuthorityV2::new(
            0,
            digest(40),
            digest(41),
            digest(42),
            digest(50),
        )
        .expect("binding");
        let authority = PoaEventBatchPlanAuthorityV2::new(
            coordinate,
            vec![PoaEventBatchPlanInitialHeadV2::genesis(initial.clone()).expect("genesis")],
            vec![binding],
        )
        .expect("authority");

        let coordinate_wire = CoordinateWire {
            world: WorldWire {
                federation_id: hex(&digest(1)),
                content_root: hex(&digest(2)),
                activation_digest: hex(&digest(3)),
                content_session: hex(&digest(4)),
                content_epoch: 5,
            },
            commit_ordinal: 7,
            block_id: hex(&digest(8)),
            turn_hash: hex(&digest(9)),
            receipt_hash: hex(&digest(10)),
            actor_root: hex(&digest(11)),
            signer: hex(&digest(12)),
        };
        let stream_wire = StreamWire {
            world: coordinate_wire.world.clone(),
            kind: 2,
            key: hex(&digest(20)),
            version: 1,
        };
        let event = PreparedEventWire {
            event_index: 0,
            stream: stream_wire.clone(),
            sequence: 1,
            expected_predecessor_head_digest: hex(&initial.digest()),
            semantic_predecessor: hex(&digest(30)),
            event_digest: hex(&digest(40)),
            payload_digest: hex(&digest(41)),
            payload_hex: "010203".to_owned(),
            successor_projection_digest: hex(&digest(42)),
            successor_projection_hex: "0a0b".to_owned(),
            genesis_projection_digest: Some(hex(&digest(32))),
            genesis_projection_hex: Some("2021".to_owned()),
        };
        let statement = encode_semantic_statement(&coordinate_wire, std::slice::from_ref(&event));
        let wire = PreparedBatchWire {
            format: PREPARED_FORMAT_V2.to_owned(),
            coordinate: coordinate_wire,
            lean_statement_hex: hex(statement.as_bytes()),
            batch_digest: hex(&digest(60)),
            events: vec![event],
            successor_heads: vec![HeadWire {
                stream: stream_wire,
                sequence: 1,
                semantic_head: hex(&digest(40)),
                storage_head_digest: hex(&digest(50)),
                projection_hex: "0a0b".to_owned(),
                origin: "existing".to_owned(),
            }],
        };
        Fixture {
            encoded: encode_prepared_batch(&wire),
            authority,
        }
    }

    #[test]
    fn canonical_plan_constructs_exact_private_persistence_carrier() {
        let fixture = fixture();
        let prepared = decode_plan_str(&fixture.encoded, &fixture.authority).expect("prepared");
        assert_eq!(prepared.coordinate(), fixture.authority.coordinate());
        assert_eq!(prepared.batch_digest(), digest(60));
        assert_eq!(prepared.events().len(), 1);
        assert_eq!(prepared.events()[0].stream().kind(), 2);
        assert_eq!(prepared.events()[0].stream().schema_version(), 1);
        assert_eq!(prepared.events()[0].payload(), [1, 2, 3]);
    }

    #[test]
    fn noncanonical_unknown_uppercase_and_unpaired_genesis_refuse() {
        let fixture = fixture();
        assert!(decode_plan_str(&(fixture.encoded.clone() + " "), &fixture.authority).is_err());
        assert!(
            decode_plan_str(
                &fixture
                    .encoded
                    .replacen("\"format\":", "\"unknown\":0,\"format\":", 1,),
                &fixture.authority,
            )
            .is_err()
        );
        assert!(
            decode_plan_str(
                &fixture.encoded.replacen("2828", "A828", 1),
                &fixture.authority
            )
            .is_err()
        );
        assert!(
            decode_plan_str(
                &fixture.encoded.replacen(
                    "\"genesis_projection_hex\":\"2021\"",
                    "\"genesis_projection_hex\":null",
                    1
                ),
                &fixture.authority,
            )
            .is_err()
        );
    }

    #[test]
    fn coordinate_authority_and_successor_fold_substitution_refuse() {
        let fixture = fixture();
        assert!(
            decode_plan_str(
                &fixture
                    .encoded
                    .replacen(&hex(&digest(11)), &hex(&digest(99)), 1),
                &fixture.authority,
            )
            .is_err()
        );
        let substituted_event = fixture
            .encoded
            .replacen(&hex(&digest(40)), &hex(&digest(98)), 1);
        assert!(decode_plan_str(&substituted_event, &fixture.authority).is_err());
        let substituted_successor = fixture.encoded.rsplit_once(&hex(&digest(50))).map_or_else(
            || panic!("fixture successor digest"),
            |(prefix, suffix)| format!("{prefix}{}{suffix}", hex(&digest(97))),
        );
        assert!(decode_plan_str(&substituted_successor, &fixture.authority).is_err());
    }

    #[test]
    fn typed_u64_and_dense_event_teeth_refuse_alternate_shapes() {
        let fixture = fixture();
        assert!(
            decode_plan_str(
                &fixture.encoded.replacen("\"kind\":2", "\"kind\":\"2\"", 1),
                &fixture.authority,
            )
            .is_err()
        );
        assert!(
            decode_plan_str(
                &fixture
                    .encoded
                    .replacen("\"event_index\":0", "\"event_index\":1", 1),
                &fixture.authority,
            )
            .is_err()
        );
    }

    #[test]
    fn activation_session_epoch_stream_reuse_refuses() {
        let fixture = fixture();
        for field in ["activation_digest", "content_session"] {
            let mut wire: PreparedBatchWire =
                serde_json::from_str(&fixture.encoded).expect("fixture wire");
            let world = &mut wire.events[0].stream.world;
            match field {
                "activation_digest" => world.activation_digest = hex(&digest(90)),
                "content_session" => world.content_session = hex(&digest(91)),
                _ => unreachable!(),
            }
            assert!(decode_plan_str(&encode_prepared_batch(&wire), &fixture.authority).is_err());
        }
        let mut wire: PreparedBatchWire =
            serde_json::from_str(&fixture.encoded).expect("fixture wire");
        wire.events[0].stream.world.content_epoch = 4;
        assert!(decode_plan_str(&encode_prepared_batch(&wire), &fixture.authority).is_err());
    }

    #[test]
    fn zero_world_identity_component_refuses() {
        let fixture = fixture();
        let hostile = fixture
            .encoded
            .replacen(&hex(&digest(3)), &hex(&[0; 32]), 1);
        assert!(decode_plan_str(&hostile, &fixture.authority).is_err());
    }
}
