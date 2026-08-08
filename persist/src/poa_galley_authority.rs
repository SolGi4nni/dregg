//! Persistence-owned authority seam for one finalized Galley public-play event.
//!
//! This module deliberately stops at opaque preparation.  It does not register a
//! node route or widen the generic commit apex.  The caller must present two
//! carriers which cannot be manufactured outside `dregg-persist`:
//!
//! * an exact finalized-turn authority produced only after the signed Galley
//!   carrier has been parsed and joined to its durable receipt; and
//! * an authenticated policy carrier produced only after exact content inclusion
//!   beneath the installed active-world `content_root` has been verified.
//!
//! Both producers now exist below the public API wall: the finalized-turn carrier
//! is joined inside the central writer, while the policy carrier can only be made
//! from a sealed, same-writer-audited activated-content member. Raw JSON, public
//! actor headers, SDK enums, and scalar coordinate fields cannot call this seam.
//! Preparation audits the installed world and complete V2 event store, reconstructs the exact Galley history,
//! invokes native Lean for both the current view and requested transition,
//! derives the successor storage-head digest through the persistence codec,
//! invokes the native Lean EventBatch planner, strictly decodes its complete
//! plan, and returns an opaque prepared carrier.
//!
//! Holder sponsorship is not an enum variant here.  Its separate native export
//! needs a consumed wallet-bound capability in the same atomic writer; until that
//! authority adapter exists it is structurally unavailable rather than silently
//! downgraded to public play.

use std::collections::{BTreeMap, BTreeSet};

use dregg_lean_ffi::{
    poa_event_batch_ffi::{
        PoaEventBatchInitialHeadsDigestVerdict, PoaEventBatchPlanVerdict,
        digest_poa_event_batch_initial_heads, plan_poa_event_batch,
    },
    poa_galley_ffi::{PoaGalleyVerdict, judge_poa_galley_daily},
};
use dregg_turn::poa_galley_carrier::{
    GalleyPlayerCommandV1, command_from_exact_galley_signed_turn, galley_player_cell,
};
use dregg_turn::{Effect, Finality, SignedTurn, TurnReceipt};
use redb::{ReadableTable, ReadableTableMetadata, WriteTransaction};
use serde::{Deserialize, Serialize};

use crate::poa_activated_content::PreparedPoaActivatedGalleyPolicyV1;
use crate::{
    CommitRecord, FinalizedTurnCoordinateV2, PersistentStore, PoaBatchStreamHeadV2,
    PoaBatchStreamIdV2, PoaEventBatchPlanAuthorityV2, PoaEventBatchPlanEventAuthorityV2,
    PoaEventBatchPlanInitialHeadV2, PoaWorldIdentityV2, PreparedPoaEventBatchV2, Result,
    StoreError, prepare_poa_event_batch_v2_from_lean_plan,
};

const GALLEY_INPUT_FORMAT: &str = "POA-GALLEY-DAILY-IN-1";
const GALLEY_OUTPUT_FORMAT: &str = "POA-GALLEY-DAILY-OUT-1";
const EVENT_BATCH_INPUT_FORMAT: &str = "POA-EVENT-BATCH-RUNTIME-IN-2";
const EVENT_BATCH_INITIAL_HEADS_INPUT_FORMAT: &str = "POA-EVENT-BATCH-INITIAL-HEADS-IN-1";
const EVENT_BATCH_INITIAL_HEADS_OUTPUT_FORMAT: &str = "POA-EVENT-BATCH-INITIAL-HEADS-DIGEST-1";
const GALLEY_STREAM_KIND: u64 = 9;
const GALLEY_STREAM_VERSION: u64 = 1;
const MAX_GALLEY_EVENTS: usize = 64;
const MAX_GALLEY_ACTIONS: usize = 2;
const MAX_COMPONENT_BYTES: usize = 16 * 1024 * 1024;
// Until the canonical receipt chain grows a hash -> dense-index table, the
// public Galley projection resolves at most this many exact receipt frames in
// the SAME read/write snapshot as its audited event prefix.  Crossing the cap
// refuses observability instead of silently returning unverifiable receipts.
const MAX_GALLEY_RECEIPT_SCAN: u64 = 65_536;

/// Persistence-owned, replay-audited public Galley observation.
///
/// All fields are private and there is no constructor: a caller cannot turn
/// JSON, a claimed head, or an `audited: bool` into an authoritative view.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaGalleyObservationV1 {
    world: PoaWorldIdentityV2,
    deployment_id: [u8; 32],
    daily_id: [u8; 32],
    public_action_content_id: [u8; 32],
    sequence: u64,
    semantic_head: [u8; 32],
    projection_digest: [u8; 32],
    projection_json: Vec<u8>,
    actions: Vec<PoaGalleyObservedActionV1>,
    events: Vec<PoaGalleyObservedEventV1>,
}

impl PoaGalleyObservationV1 {
    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        &self.world
    }
    pub const fn deployment_id(&self) -> [u8; 32] {
        self.deployment_id
    }
    pub const fn daily_id(&self) -> [u8; 32] {
        self.daily_id
    }
    pub const fn public_action_content_id(&self) -> [u8; 32] {
        self.public_action_content_id
    }
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }
    pub const fn semantic_head(&self) -> [u8; 32] {
        self.semantic_head
    }
    pub const fn projection_digest(&self) -> [u8; 32] {
        self.projection_digest
    }
    pub fn projection_json(&self) -> &[u8] {
        &self.projection_json
    }
    pub fn actions(&self) -> &[PoaGalleyObservedActionV1] {
        &self.actions
    }
    pub fn events(&self) -> &[PoaGalleyObservedEventV1] {
        &self.events
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaGalleyObservedActionV1 {
    token: [u8; 32],
    expires_after_sequence: u64,
}

impl PoaGalleyObservedActionV1 {
    pub const fn token(&self) -> [u8; 32] {
        self.token
    }
    pub const fn expires_after_sequence(&self) -> u64 {
        self.expires_after_sequence
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaGalleyObservedEventV1 {
    coordinate: FinalizedTurnCoordinateV2,
    sequence: u64,
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    payload_json: Vec<u8>,
    receipt_index: u64,
    receipt_postcard: Vec<u8>,
}

/// Exact active-world/head token established by persistence's native Lean
/// view before a finalized public `Perform` executes off-lock.
///
/// The node compares a second independently minted value after re-acquiring
/// its global state lock.  There is no public constructor and no caller-authored
/// head/sequence field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaGalleyPublicPerformPreflightV1 {
    world: PoaWorldIdentityV2,
    signer: [u8; 32],
    action_token: [u8; 32],
    action_content_id: [u8; 32],
    sequence: u64,
    semantic_head: [u8; 32],
}

/// Typed preflight disposition.  Authority/configuration failures remain
/// retryable at node finality; an exact carrier whose action is absent from a
/// successfully reconstructed native view is a deterministic stale payload.
#[derive(Debug)]
pub enum PoaGalleyPublicPerformPreflightErrorV1 {
    AuthorityUnavailable(StoreError),
    StaleAction(&'static str),
}

impl std::fmt::Display for PoaGalleyPublicPerformPreflightErrorV1 {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AuthorityUnavailable(error) => {
                write!(formatter, "Galley authority unavailable: {error}")
            }
            Self::StaleAction(reason) => write!(formatter, "stale Galley action: {reason}"),
        }
    }
}

impl std::error::Error for PoaGalleyPublicPerformPreflightErrorV1 {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::AuthorityUnavailable(error) => Some(error),
            Self::StaleAction(_) => None,
        }
    }
}

impl PoaGalleyObservedEventV1 {
    pub const fn coordinate(&self) -> &FinalizedTurnCoordinateV2 {
        &self.coordinate
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
    pub fn payload_json(&self) -> &[u8] {
        &self.payload_json
    }
    pub const fn receipt_index(&self) -> u64 {
        self.receipt_index
    }
    pub fn receipt_postcard(&self) -> &[u8] {
        &self.receipt_postcard
    }
}

/// Exact finalized public `Perform` authority.
///
/// This type is intentionally neither `Clone` nor `Deserialize`.  Its
/// crate-private constructor is reserved for the future parser which consumes
/// the exact signed turn plus finalized receipt.  In particular, no network
/// caller can assemble one from a signer, token, or receipt hash.
pub struct PreparedPoaFinalizedTurnAuthorityV1 {
    coordinate: FinalizedTurnCoordinateV2,
    player_cell: [u8; 32],
    action_token: [u8; 32],
    action_content_id: [u8; 32],
}

impl PreparedPoaFinalizedTurnAuthorityV1 {
    pub(crate) fn from_exact_public_perform(
        coordinate: FinalizedTurnCoordinateV2,
        player_cell: [u8; 32],
        action_token: [u8; 32],
        action_content_id: [u8; 32],
    ) -> Result<Self> {
        if player_cell == [0; 32] || action_token == [0; 32] || action_content_id == [0; 32] {
            return Err(integrity(
                "finalized Galley public-play carrier has a zero identity component",
            ));
        }
        Ok(Self {
            coordinate,
            player_cell,
            action_token,
            action_content_id,
        })
    }

    pub const fn coordinate(&self) -> &FinalizedTurnCoordinateV2 {
        &self.coordinate
    }
}

/// Private facts recovered from one exact signed public `Perform` and its
/// canonical finalized receipt/commit record.
///
/// This is deliberately not itself finality authority. It can be produced from
/// untrusted objects and becomes useful only when
/// [`derive_poa_finalized_public_perform_v1`] joins it to the unforgeable marker
/// minted inside the central finalized-turn writer.
struct VerifiedPoaGalleyPublicPerformFactsV1 {
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    actor_root: [u8; 32],
    signer: [u8; 32],
    player_cell: [u8; 32],
    action_token: [u8; 32],
    action_content_id: [u8; 32],
}

/// Verify every fact persistence can recover from an untrusted Galley carrier,
/// receipt, record, and authenticated policy.
///
/// A present PQ envelope is always checked and a partial or forged envelope
/// fails closed. Absence is not treated here as evidence that classical-only
/// admission was permitted: mandatory-PQ enrollment is node-finality policy and
/// remains a named blocker until the same-writer marker also carries the node's
/// independently enrolled PQ-identity admission. There is intentionally no
/// caller-supplied `require_pq` boolean.
fn verify_poa_public_perform_facts_v1(
    policy: &AuthenticatedPoaGalleyPolicyV1,
    signed: &SignedTurn,
    receipt: &TurnReceipt,
    record: &CommitRecord,
) -> Result<VerifiedPoaGalleyPublicPerformFactsV1> {
    let command = command_from_exact_galley_signed_turn(signed).map_err(|error| {
        integrity(format!(
            "finalized Galley SignedTurn is not the exact signed carrier: {error}"
        ))
    })?;
    let GalleyPlayerCommandV1::Perform {
        action_token,
        action_content_id,
    } = command
    else {
        return Err(integrity(
            "finalized Galley public-play carrier is not a public Perform command",
        ));
    };

    let has_pq_signature = !signed.pq_signature.is_empty();
    let has_pq_signer = !signed.pq_signer.is_empty();
    if has_pq_signature != has_pq_signer {
        return Err(integrity(
            "finalized Galley SignedTurn has an incomplete PQ envelope",
        ));
    }
    let turn_hash = signed.turn.hash();
    if has_pq_signature
        && !dregg_turn::pq::ml_dsa_verify(&signed.pq_signer, &turn_hash, &signed.pq_signature)
    {
        return Err(integrity(
            "finalized Galley SignedTurn has an invalid PQ signature",
        ));
    }

    let player_cell = galley_player_cell(&signed.signer.0);
    let receipt_hash = receipt.receipt_hash();
    if record.turn_hash != turn_hash
        || receipt.turn_hash != turn_hash
        || record.receipt_hash != receipt_hash
        || record.creator != player_cell.0
        || receipt.agent != player_cell
        || receipt.federation_id != policy.world.federation_id()
    {
        return Err(integrity(
            "finalized Galley turn/receipt/record signer, player, or world binding disagrees",
        ));
    }
    if receipt.finality != Finality::Final {
        return Err(integrity(
            "finalized Galley receipt is not marked Final inside the validated finality weld",
        ));
    }
    if receipt.forest_hash != signed.turn.call_forest.compute_hash()
        || receipt.action_count != signed.turn.call_forest.action_count()
        || receipt.previous_receipt_hash != signed.turn.previous_receipt_hash
    {
        return Err(integrity(
            "finalized Galley receipt does not bind the exact call forest or predecessor",
        ));
    }

    let root = &signed.turn.call_forest.roots[0];
    let effect = &root.action.effects[0];
    let Effect::EmitEvent { cell, event } = effect else {
        return Err(integrity(
            "exact Galley carrier unexpectedly lost its event effect",
        ));
    };
    let expected_effects_hash = *blake3::hash(&effect.hash()).as_bytes();
    let exact_emitted_event = receipt.emitted_events.len() == 1
        && receipt.emitted_events[0].cell == *cell
        && receipt.emitted_events[0].topic == event.topic
        && receipt.emitted_events[0].data == event.data;
    if receipt.effects_hash != expected_effects_hash
        || !exact_emitted_event
        || !receipt.routing_directives.is_empty()
        || !receipt.introduction_exports.is_empty()
        || !receipt.derivation_records.is_empty()
        || !receipt.consumed_capabilities.is_empty()
        || receipt.was_burn
    {
        return Err(integrity(
            "finalized Galley receipt contains effects or authority artifacts outside the exact public Perform",
        ));
    }
    if action_content_id != decode_hex32(&policy.policy.public_action_content_id)? {
        return Err(integrity(
            "finalized Galley Perform does not name the authenticated public action content",
        ));
    }

    Ok(VerifiedPoaGalleyPublicPerformFactsV1 {
        turn_hash,
        receipt_hash,
        actor_root: receipt.pre_state_hash,
        signer: signed.signer.0,
        player_cell: player_cell.0,
        action_token: action_token.to_bytes(),
        action_content_id,
    })
}

/// Join an exact public `Perform` to the central writer's already-validated
/// finality weld and mint the opaque persistence authority.
///
/// This is crate-private and returns a carrier whose fields remain private. The
/// `Finality::Final` receipt discriminant is checked only for consistency; it is
/// never authority. Authority comes from `finality`, which has no constructor
/// outside `commit_log` and is minted only after faithful/executor/receipt
/// validation inside the same writer.
pub(crate) fn derive_poa_finalized_public_perform_v1(
    policy: &AuthenticatedPoaGalleyPolicyV1,
    finality: &crate::commit_log::ValidatedPoaGalleyFinalityWeldV1,
    signed: &SignedTurn,
    receipt: &TurnReceipt,
    record: &CommitRecord,
) -> Result<PreparedPoaFinalizedTurnAuthorityV1> {
    let verified = verify_poa_public_perform_facts_v1(policy, signed, receipt, record)?;
    if finality.ordinal() != record.ordinal
        || finality.block_id() != record.block_id
        || finality.turn_hash() != record.turn_hash
        || finality.turn_hash() != verified.turn_hash
        || finality.receipt_hash() != record.receipt_hash
        || finality.receipt_hash() != verified.receipt_hash
    {
        return Err(integrity(
            "Galley carrier does not match the central writer's validated finality weld",
        ));
    }
    let coordinate = FinalizedTurnCoordinateV2::new(
        policy.world.clone(),
        record.ordinal,
        record.block_id,
        verified.turn_hash,
        verified.receipt_hash,
        verified.actor_root,
        verified.signer,
    )?;
    PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
        coordinate,
        verified.player_cell,
        verified.action_token,
        verified.action_content_id,
    )
}

/// Exact Galley policy bytes plus their sequence-zero projection.
///
/// Production construction consumes the non-serializable activated-content
/// carrier. Raw component bytes cannot cross this boundary by assertion.
pub struct AuthenticatedPoaGalleyPolicyV1 {
    world: PoaWorldIdentityV2,
    manifest_root: [u8; 32],
    component_sha256: [u8; 32],
    policy: GalleyPolicyWire,
    policy_json: Vec<u8>,
    genesis_projection_json: Vec<u8>,
}

impl AuthenticatedPoaGalleyPolicyV1 {
    pub(crate) fn from_activated_content(
        prepared: PreparedPoaActivatedGalleyPolicyV1,
    ) -> Result<Self> {
        let (world, policy_json, genesis_projection_json, manifest_root, component_sha256) =
            prepared.into_parts();
        if manifest_root != world.content_root() || component_sha256 == [0; 32] {
            return Err(integrity(
                "activated Galley member lost its exact root or component digest",
            ));
        }
        Self::from_exact_parts(
            world,
            manifest_root,
            component_sha256,
            policy_json,
            genesis_projection_json,
        )
    }

    fn from_exact_parts(
        world: PoaWorldIdentityV2,
        manifest_root: [u8; 32],
        component_sha256: [u8; 32],
        policy_json: Vec<u8>,
        genesis_projection_json: Vec<u8>,
    ) -> Result<Self> {
        let policy: GalleyPolicyWire = strict_json(&policy_json, "Galley policy")?;
        let projection: GalleyProjectionWire =
            strict_json(&genesis_projection_json, "Galley genesis projection")?;
        validate_policy_digests(&policy)?;
        validate_projection_digests(&projection)?;
        if policy.federation_id != hex(world.federation_id())
            || policy.content_epoch != world.content_epoch()
            || policy.deployment_id == zero_hex()
            || policy.daily_id == zero_hex()
            || policy.genesis_head == zero_hex()
            || policy.public_action_content_id == zero_hex()
        {
            return Err(integrity(
                "Galley policy identity disagrees with its authenticated world",
            ));
        }
        if projection.sequence != 0
            || !projection.public_players.is_empty()
            || !projection.sponsors.is_empty()
            || !projection.spent_grant_nullifiers.is_empty()
            || projection.public_play_count != 0
            || projection.sponsorship_count != 0
            || projection.local_service_total != 0
            || projection.power_root != policy.power_root
            || projection.loot_root != policy.loot_root
            || projection.canon_root != policy.canon_root
            || projection.canon_revision != policy.canon_revision
        {
            return Err(integrity(
                "Galley sequence-zero projection is not the policy genesis projection",
            ));
        }
        Ok(Self {
            world,
            manifest_root,
            component_sha256,
            policy,
            policy_json,
            genesis_projection_json,
        })
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        &self.world
    }

    pub const fn manifest_root(&self) -> [u8; 32] {
        self.manifest_root
    }

    pub const fn component_sha256(&self) -> [u8; 32] {
        self.component_sha256
    }

    #[cfg(test)]
    pub(crate) fn from_verified_content_inclusion(
        world: PoaWorldIdentityV2,
        policy_json: Vec<u8>,
        genesis_projection_json: Vec<u8>,
    ) -> Result<Self> {
        Self::from_exact_parts(
            world.clone(),
            world.content_root(),
            [0xc1; 32],
            policy_json,
            genesis_projection_json,
        )
    }
}

/// Opaque output of the full active-world/history/Lean/planner braid.
///
/// No public accessor exposes planner JSON or lets a caller replace one digest.
/// The eventual same-writer commit adapter consumes this carrier inside the
/// persistence crate.
#[derive(Clone)]
pub struct PreparedPoaGalleyEventBatchV1 {
    batch: PreparedPoaEventBatchV2,
}

impl PreparedPoaGalleyEventBatchV1 {
    pub const fn coordinate(&self) -> &FinalizedTurnCoordinateV2 {
        self.batch.coordinate()
    }

    pub const fn batch_digest(&self) -> [u8; 32] {
        self.batch.batch_digest()
    }

    pub fn event_count(&self) -> usize {
        self.batch.events().len()
    }

    pub(crate) fn into_event_batch(self) -> PreparedPoaEventBatchV2 {
        self.batch
    }
}

impl PersistentStore {
    /// Prepare one public Galley transition from installed authority only.
    ///
    /// This does not mutate the store.  The final commit apex must re-check the
    /// exact active world in its writer immediately before staging this batch.
    pub fn prepare_poa_galley_public_event_batch_v1(
        &self,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        finalized: PreparedPoaFinalizedTurnAuthorityV1,
    ) -> Result<PreparedPoaGalleyEventBatchV1> {
        let write = self.db.begin_write()?;
        let prepared =
            self.prepare_poa_galley_public_event_batch_v1_in(&write, policy, finalized)?;
        write.abort()?;
        Ok(prepared)
    }

    /// Same-snapshot planner used by the finalized-turn writer. Every durable
    /// authority read and storage-head predecessor comes from `write`.
    pub(crate) fn prepare_poa_galley_public_event_batch_v1_in(
        &self,
        write: &WriteTransaction,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        finalized: PreparedPoaFinalizedTurnAuthorityV1,
    ) -> Result<PreparedPoaGalleyEventBatchV1> {
        crate::poa_world_activation::require_poa_active_world_exact_in(write, &policy.world)?;
        if finalized.coordinate.world() != &policy.world {
            return Err(integrity(
                "Galley policy or finalized carrier is not in the exact active world",
            ));
        }
        if finalized.action_content_id != decode_hex32(&policy.policy.public_action_content_id)? {
            return Err(integrity(
                "finalized Galley action content is not the activated public action",
            ));
        }

        crate::poa_event_batch_v2::audit_poa_event_batch_store_v2_in(write)?;
        if crate::poa_event_batch_v2::load_poa_event_batch_v2_in(
            write,
            finalized.coordinate.commit_ordinal(),
        )?
        .is_some()
        {
            return Err(integrity(
                "Galley preparation found an existing finalized batch; exact replay belongs at the commit apex",
            ));
        }

        let stream = PoaBatchStreamIdV2::new(
            policy.world.clone(),
            GALLEY_STREAM_KIND,
            decode_hex32(&policy.policy.daily_id)?,
            GALLEY_STREAM_VERSION,
        )?;
        let snapshot = self.load_galley_snapshot_in(write, policy, stream)?;

        let view_input = galley_input(
            policy,
            &snapshot,
            finalized.coordinate.signer(),
            finalized.player_cell,
            "view",
            "none",
            [0; 32],
        )?;
        let view = call_galley(&view_input)?;
        validate_view(policy, &snapshot, finalized.coordinate.signer(), &view)?;
        if view
            .view
            .available_actions
            .iter()
            .filter(|action| {
                action.kind == "public-play"
                    && action.token == hex(finalized.action_token)
                    && action.actor == hex(finalized.coordinate.signer())
                    && action.beneficiary == hex(finalized.coordinate.signer())
                    && action.expires_after_sequence == snapshot.sequence
            })
            .count()
            != 1
        {
            return Err(integrity(
                "finalized Galley action was not exactly offered by native Lean at this head",
            ));
        }

        let initial_head = match &snapshot.initial_head {
            InitialGalleyHead::Existing(head) => {
                if head.projection_digest() != decode_hex32(&view.replay.projection_digest)? {
                    return Err(integrity(
                        "native Lean Galley view disagrees with durable projection digest",
                    ));
                }
                PoaEventBatchPlanInitialHeadV2::existing(head.clone())
            }
            InitialGalleyHead::Genesis {
                stream,
                semantic_head,
                projection,
            } => PoaEventBatchPlanInitialHeadV2::genesis(PoaBatchStreamHeadV2::genesis(
                stream.clone(),
                *semantic_head,
                decode_hex32(&view.replay.projection_digest)?,
                projection.clone(),
            )?)?,
        };

        let command_input = galley_input(
            policy,
            &snapshot,
            finalized.coordinate.signer(),
            finalized.player_cell,
            "command",
            "public-play",
            finalized.action_token,
        )?;
        let command = call_galley(&command_input)?;
        let judged = validate_command(policy, &snapshot, finalized.coordinate.signer(), &command)?;

        let successor_head = PoaBatchStreamHeadV2::successor(
            initial_head.head().stream().clone(),
            judged.statement.sequence,
            judged.event_digest,
            judged.successor_projection_digest,
            judged.successor_projection.clone(),
        )?;
        let event_authority = PoaEventBatchPlanEventAuthorityV2::new(
            0,
            judged.event_digest,
            judged.payload_digest,
            judged.successor_projection_digest,
            successor_head.digest(),
        )?;
        let initial_wire = event_batch_head_wire(initial_head.head(), initial_head.origin());
        let authority = PoaEventBatchPlanAuthorityV2::new(
            clone_coordinate(finalized.coordinate()),
            vec![initial_head],
            vec![event_authority],
        )?;

        let coordinate_wire = event_batch_coordinate_wire(finalized.coordinate());
        let initial_heads_digest =
            initial_heads_digest_from_native(coordinate_wire.clone(), vec![initial_wire.clone()])?;
        let event = EventBatchCandidateWire {
            event_index: 0,
            statement: EventBatchStatementWire {
                namespace_id: judged.statement.namespace_id.clone(),
                kind: judged.statement.kind,
                key: judged.statement.key.clone(),
                version: judged.statement.version,
                sequence: judged.statement.sequence,
                predecessor: judged.statement.predecessor.clone(),
                payload_digest: judged.statement.payload_digest.clone(),
            },
            event_digest: judged.event_digest_hex,
            payload_hex: hex(&judged.payload),
            successor_projection_digest: judged.successor_projection_digest_hex,
            successor_projection_hex: hex(&judged.successor_projection),
        };
        let binding = EventBatchBindingWire {
            event_index: 0,
            receipt_hash: hex(finalized.coordinate.receipt_hash()),
            actor_root: hex(finalized.coordinate.actor_root()),
            signer: hex(finalized.coordinate.signer()),
            event_digest: event.event_digest.clone(),
            payload_digest: event.statement.payload_digest.clone(),
            successor_projection_digest: event.successor_projection_digest.clone(),
            successor_storage_head_digest: hex(successor_head.digest()),
        };
        let input = EventBatchInputWire {
            format: EVENT_BATCH_INPUT_FORMAT,
            authority: EventBatchHostAuthorityWire {
                coordinate: coordinate_wire.clone(),
                initial_heads_digest: hex(initial_heads_digest),
                events: vec![binding],
            },
            coordinate: coordinate_wire,
            initial_heads: vec![initial_wire],
            events: vec![event],
        };
        let input_json = serde_json::to_string(&input)
            .map_err(|error| integrity(format!("EventBatch input JSON failed: {error}")))?;
        let plan = match plan_poa_event_batch(&input_json)
            .map_err(|error| integrity(format!("native Lean EventBatch planner failed: {error}")))?
        {
            PoaEventBatchPlanVerdict::Planned(plan) => plan,
            PoaEventBatchPlanVerdict::Rejected => {
                return Err(integrity(
                    "native Lean EventBatch planner refused Galley event",
                ));
            }
        };
        let batch = prepare_poa_event_batch_v2_from_lean_plan(&plan, &authority)?;
        Ok(PreparedPoaGalleyEventBatchV1 { batch })
    }

    /// Test-only fixture producer which still traverses the real native view,
    /// command, initial-head digest, EventBatch planner, and sealed decoder.
    /// It exists so the commit-log apex can be exercised without exposing an
    /// authority constructor or an inner prepared-batch accessor.
    #[cfg(test)]
    pub(crate) fn prepare_poa_galley_public_event_batch_for_commit_test(
        &self,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        coordinate: FinalizedTurnCoordinateV2,
        player_cell: [u8; 32],
    ) -> Result<PreparedPoaGalleyEventBatchV1> {
        let write = self.db.begin_write()?;
        let stream = PoaBatchStreamIdV2::new(
            policy.world.clone(),
            GALLEY_STREAM_KIND,
            decode_hex32(&policy.policy.daily_id)?,
            GALLEY_STREAM_VERSION,
        )?;
        let snapshot = self.load_galley_snapshot_in(&write, policy, stream)?;
        let signer = coordinate.signer();
        let view_input = galley_input(
            policy,
            &snapshot,
            signer,
            player_cell,
            "view",
            "none",
            [0; 32],
        )?;
        let view = call_galley(&view_input)?;
        validate_view(policy, &snapshot, signer, &view)?;
        let token = view
            .view
            .available_actions
            .iter()
            .find(|action| {
                action.kind == "public-play"
                    && action.actor == hex(signer)
                    && action.beneficiary == hex(signer)
                    && action.expires_after_sequence == snapshot.sequence
            })
            .ok_or_else(|| integrity("native Lean did not offer the commit-test public action"))?;
        let finalized = PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
            coordinate,
            player_cell,
            decode_hex32(&token.token)?,
            decode_hex32(&policy.policy.public_action_content_id)?,
        )?;
        let prepared =
            self.prepare_poa_galley_public_event_batch_v1_in(&write, policy, finalized)?;
        write.abort()?;
        Ok(prepared)
    }

    /// Observe the exact native action token offered by the current Galley
    /// snapshot for an end-to-end persistence test. This does not prepare or
    /// confer authority; production must recover the token from a genuine
    /// signed command and validate it again inside the commit writer.
    #[cfg(test)]
    pub(crate) fn offered_poa_galley_public_token_for_commit_test(
        &self,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        signer: [u8; 32],
        player_cell: [u8; 32],
    ) -> Result<[u8; 32]> {
        let write = self.db.begin_write()?;
        let stream = PoaBatchStreamIdV2::new(
            policy.world.clone(),
            GALLEY_STREAM_KIND,
            decode_hex32(&policy.policy.daily_id)?,
            GALLEY_STREAM_VERSION,
        )?;
        let snapshot = self.load_galley_snapshot_in(&write, policy, stream)?;
        let view_input = galley_input(
            policy,
            &snapshot,
            signer,
            player_cell,
            "view",
            "none",
            [0; 32],
        )?;
        let view = call_galley(&view_input)?;
        validate_view(policy, &snapshot, signer, &view)?;
        let token = view
            .view
            .available_actions
            .iter()
            .find(|action| {
                action.kind == "public-play"
                    && action.actor == hex(signer)
                    && action.beneficiary == hex(signer)
                    && action.expires_after_sequence == snapshot.sequence
            })
            .ok_or_else(|| integrity("native Lean did not offer the requested public action"))?;
        let token = decode_hex32(&token.token)?;
        write.abort()?;
        Ok(token)
    }

    /// Reconstruct the current public Galley view from the sealed active
    /// content member and complete audited V2 journal in one database snapshot.
    ///
    /// `signer` personalizes the public Lean view only.  It confers no write or
    /// finality authority; the only mutating path consumes a separately signed,
    /// PQ-admitted `SignedTurn` at the node finalization apex.
    pub fn observe_active_poa_galley_v1(&self, signer: [u8; 32]) -> Result<PoaGalleyObservationV1> {
        if signer == [0; 32] {
            return Err(integrity("Galley observation signer is zero"));
        }
        let write = self.db.begin_write()?;
        let prepared =
            crate::poa_activated_content::prepare_active_poa_galley_policy_v1_in(&write)?;
        let policy = AuthenticatedPoaGalleyPolicyV1::from_activated_content(prepared)?;
        let daily_id = decode_hex32(&policy.policy.daily_id)?;
        let stream = PoaBatchStreamIdV2::new(
            policy.world.clone(),
            GALLEY_STREAM_KIND,
            daily_id,
            GALLEY_STREAM_VERSION,
        )?;
        let snapshot = self.load_galley_snapshot_in(&write, &policy, stream)?;
        if snapshot.history.len() > MAX_GALLEY_EVENTS {
            return Err(integrity(
                "durable Galley history exceeds native replay bound",
            ));
        }
        let player_cell = galley_player_cell(&signer).0;
        let input = galley_input(
            &policy,
            &snapshot,
            signer,
            player_cell,
            "view",
            "none",
            [0; 32],
        )?;
        let view = call_galley(&input)?;
        validate_view(&policy, &snapshot, signer, &view)?;
        let projection_digest = decode_hex32(&view.replay.projection_digest)?;
        let actions = view
            .view
            .available_actions
            .iter()
            .map(|action| {
                if action.kind != "public-play"
                    || action.actor != hex(signer)
                    || action.beneficiary != hex(signer)
                    || action.expires_after_sequence != snapshot.sequence
                {
                    return Err(integrity(
                        "native Galley exposed an action outside public observation authority",
                    ));
                }
                Ok(PoaGalleyObservedActionV1 {
                    token: decode_hex32(&action.token)?,
                    expires_after_sequence: action.expires_after_sequence,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let receipt_frames = load_galley_receipts_in(&write, &snapshot.history)?;
        let events = snapshot
            .history
            .iter()
            .map(|recorded| {
                let (receipt_index, receipt_postcard) = receipt_frames
                    .get(&recorded.coordinate.receipt_hash())
                    .ok_or_else(|| integrity("Galley event has no exact durable receipt frame"))?;
                Ok(PoaGalleyObservedEventV1 {
                    coordinate: recorded.coordinate.clone(),
                    sequence: recorded.sequence,
                    event_digest: recorded.event_digest,
                    payload_digest: recorded.payload_digest,
                    payload_json: recorded.payload_json.clone(),
                    receipt_index: *receipt_index,
                    receipt_postcard: receipt_postcard.clone(),
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let observation = PoaGalleyObservationV1 {
            world: policy.world.clone(),
            deployment_id: decode_hex32(&policy.policy.deployment_id)?,
            daily_id,
            public_action_content_id: decode_hex32(&policy.policy.public_action_content_id)?,
            sequence: snapshot.sequence,
            semantic_head: snapshot.semantic_head,
            projection_digest,
            projection_json: snapshot.projection.clone(),
            actions,
            events,
        };
        write.abort()?;
        Ok(observation)
    }

    /// Validate one exact signed public `Perform` against the active sealed
    /// policy and native Lean view, returning a persistence-minted CAS token.
    /// No finality is asserted and no state is mutated.
    pub fn preflight_active_poa_galley_public_perform_v1(
        &self,
        signed: &SignedTurn,
    ) -> std::result::Result<
        PoaGalleyPublicPerformPreflightV1,
        PoaGalleyPublicPerformPreflightErrorV1,
    > {
        use PoaGalleyPublicPerformPreflightErrorV1::{AuthorityUnavailable, StaleAction};

        let command = command_from_exact_galley_signed_turn(signed)
            .map_err(|_| StaleAction("signed carrier is not exact"))?;
        let GalleyPlayerCommandV1::Perform {
            action_token,
            action_content_id,
        } = command
        else {
            return Err(StaleAction("command has no registered public writer"));
        };
        let signer = signed.signer.0;
        if signer == [0; 32] {
            return Err(StaleAction("signer is zero"));
        }
        let write = self
            .db
            .begin_write()
            .map_err(|error| AuthorityUnavailable(error.into()))?;
        let result = (|| {
            let prepared =
                crate::poa_activated_content::prepare_active_poa_galley_policy_v1_in(&write)
                    .map_err(AuthorityUnavailable)?;
            let policy = AuthenticatedPoaGalleyPolicyV1::from_activated_content(prepared)
                .map_err(AuthorityUnavailable)?;
            let expected_content = decode_hex32(&policy.policy.public_action_content_id)
                .map_err(AuthorityUnavailable)?;
            if action_content_id != expected_content {
                return Err(StaleAction("action content is not active"));
            }
            let stream = PoaBatchStreamIdV2::new(
                policy.world.clone(),
                GALLEY_STREAM_KIND,
                decode_hex32(&policy.policy.daily_id).map_err(AuthorityUnavailable)?,
                GALLEY_STREAM_VERSION,
            )
            .map_err(AuthorityUnavailable)?;
            let snapshot = self
                .load_galley_snapshot_in(&write, &policy, stream)
                .map_err(AuthorityUnavailable)?;
            let player_cell = galley_player_cell(&signer).0;
            let input = galley_input(
                &policy,
                &snapshot,
                signer,
                player_cell,
                "view",
                "none",
                [0; 32],
            )
            .map_err(AuthorityUnavailable)?;
            let view = call_galley(&input).map_err(AuthorityUnavailable)?;
            validate_view(&policy, &snapshot, signer, &view).map_err(AuthorityUnavailable)?;
            if view
                .view
                .available_actions
                .iter()
                .filter(|offered| {
                    offered.kind == "public-play"
                        && offered.token == hex(action_token.to_bytes())
                        && offered.actor == hex(signer)
                        && offered.beneficiary == hex(signer)
                        && offered.expires_after_sequence == snapshot.sequence
                })
                .count()
                != 1
            {
                return Err(StaleAction(
                    "action token is absent from the current native view",
                ));
            }
            Ok(PoaGalleyPublicPerformPreflightV1 {
                world: policy.world,
                signer,
                action_token: action_token.to_bytes(),
                action_content_id,
                sequence: snapshot.sequence,
                semantic_head: snapshot.semantic_head,
            })
        })();
        write
            .abort()
            .map_err(|error| AuthorityUnavailable(error.into()))?;
        result
    }

    fn load_galley_snapshot_in(
        &self,
        write: &WriteTransaction,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        stream: PoaBatchStreamIdV2,
    ) -> Result<GalleySnapshot> {
        let Some(history) =
            crate::poa_event_batch_v2::load_poa_event_batch_history_v2_in(write, &stream)?
        else {
            return Ok(GalleySnapshot {
                sequence: 0,
                semantic_head: decode_hex32(&policy.policy.genesis_head)?,
                projection: policy.genesis_projection_json.clone(),
                history: Vec::new(),
                initial_head: InitialGalleyHead::Genesis {
                    stream,
                    semantic_head: decode_hex32(&policy.policy.genesis_head)?,
                    projection: policy.genesis_projection_json.clone(),
                },
            });
        };
        if history.stream() != &stream
            || history.genesis_head().stream() != &stream
            || history.current_head().stream() != &stream
            || history.genesis_head().sequence() != 0
            || history.genesis_head().semantic_head() != decode_hex32(&policy.policy.genesis_head)?
            || history.genesis_head().projection() != policy.genesis_projection_json
            || usize::try_from(history.current_head().sequence()).ok()
                != Some(history.events().len())
        {
            return Err(integrity(
                "durable Galley history disagrees with authenticated policy genesis",
            ));
        }
        strict_json::<GalleyProjectionWire>(
            history.current_head().projection(),
            "durable Galley projection",
        )?;
        if history.events().len() > MAX_GALLEY_EVENTS {
            return Err(integrity(
                "durable Galley history exceeds native replay bound",
            ));
        }
        let mut events = Vec::with_capacity(history.events().len());
        for recorded in history.events() {
            if recorded.coordinate().world() != &policy.world
                || recorded.event().stream() != &stream
            {
                return Err(integrity(
                    "durable Galley event belongs to another world or stream",
                ));
            }
            let payload: GalleyPayloadWire =
                strict_json(recorded.event().payload(), "durable Galley payload")?;
            let event = GalleyEventWire {
                statement: GalleyStatementWire {
                    namespace_id: hex(policy.world.federation_id()),
                    kind: GALLEY_STREAM_KIND,
                    key: policy.policy.daily_id.clone(),
                    version: GALLEY_STREAM_VERSION,
                    sequence: recorded.event().sequence(),
                    predecessor: hex(recorded.event().semantic_predecessor()),
                    payload_digest: hex(recorded.event().payload_digest()),
                },
                payload,
                event_digest: hex(recorded.event().event_digest()),
            };
            let event_json = serde_json::to_vec(&event)
                .map_err(|error| integrity(format!("Galley event JSON failed: {error}")))?;
            events.push(GalleySnapshotEvent {
                coordinate: recorded.coordinate().clone(),
                sequence: recorded.event().sequence(),
                event_digest: recorded.event().event_digest(),
                payload_digest: recorded.event().payload_digest(),
                payload_json: recorded.event().payload().to_vec(),
                event_json,
            });
        }
        Ok(GalleySnapshot {
            sequence: history.current_head().sequence(),
            semantic_head: history.current_head().semantic_head(),
            projection: history.current_head().projection().to_vec(),
            history: events,
            initial_head: InitialGalleyHead::Existing(history.current_head().clone()),
        })
    }

    #[cfg(test)]
    fn load_galley_snapshot(
        &self,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        stream: PoaBatchStreamIdV2,
    ) -> Result<GalleySnapshot> {
        let write = self.db.begin_write()?;
        let snapshot = self.load_galley_snapshot_in(&write, policy, stream)?;
        write.abort()?;
        Ok(snapshot)
    }
}

struct GalleySnapshot {
    sequence: u64,
    semantic_head: [u8; 32],
    projection: Vec<u8>,
    history: Vec<GalleySnapshotEvent>,
    initial_head: InitialGalleyHead,
}

struct GalleySnapshotEvent {
    coordinate: FinalizedTurnCoordinateV2,
    sequence: u64,
    event_digest: [u8; 32],
    payload_digest: [u8; 32],
    payload_json: Vec<u8>,
    event_json: Vec<u8>,
}

fn load_galley_receipts_in(
    write: &WriteTransaction,
    events: &[GalleySnapshotEvent],
) -> Result<BTreeMap<[u8; 32], (u64, Vec<u8>)>> {
    if events.is_empty() {
        return Ok(BTreeMap::new());
    }
    let targets = events
        .iter()
        .map(|event| (event.coordinate.receipt_hash(), event))
        .collect::<BTreeMap<_, _>>();
    if targets.len() != events.len() {
        return Err(integrity(
            "two Galley events claim the same finalized receipt hash",
        ));
    }
    let table = write.open_table(crate::tables::RECEIPT_CHAIN)?;
    let count = table.len()?;
    if count > MAX_GALLEY_RECEIPT_SCAN {
        return Err(integrity(format!(
            "receipt chain length {count} exceeds Galley observation scan bound {MAX_GALLEY_RECEIPT_SCAN}"
        )));
    }
    let mut expected_index = 0u64;
    let mut found = BTreeMap::new();
    for row in table.iter()? {
        let (key, value) = row?;
        let index = key.value();
        if index != expected_index {
            return Err(integrity(format!(
                "receipt log gap during Galley observation: expected {expected_index}, found {index}"
            )));
        }
        expected_index = expected_index
            .checked_add(1)
            .ok_or_else(|| integrity("receipt index overflow during Galley observation"))?;
        let bytes = value.value();
        let (receipt, remainder): (TurnReceipt, &[u8]) = postcard::take_from_bytes(bytes)
            .map_err(|error| integrity(format!("Galley receipt postcard failed: {error}")))?;
        if !remainder.is_empty()
            || postcard::to_stdvec(&receipt)
                .map_err(|error| integrity(format!("Galley receipt reencode failed: {error}")))?
                != bytes
        {
            return Err(integrity(
                "receipt chain contains a noncanonical Galley observation frame",
            ));
        }
        let receipt_hash = receipt.receipt_hash();
        let Some(event) = targets.get(&receipt_hash) else {
            continue;
        };
        if receipt.turn_hash != event.coordinate.turn_hash()
            || receipt.pre_state_hash != event.coordinate.actor_root()
            || receipt.agent.0 != galley_player_cell(&event.coordinate.signer()).0
            || receipt.federation_id != event.coordinate.world().federation_id()
            || receipt.finality != Finality::Final
        {
            return Err(integrity(
                "Galley journal coordinate disagrees with its canonical receipt",
            ));
        }
        if found
            .insert(receipt_hash, (index, bytes.to_vec()))
            .is_some()
        {
            return Err(integrity(
                "receipt chain repeats a Galley event receipt hash",
            ));
        }
    }
    if found.len() != targets.len() {
        return Err(integrity(
            "Galley journal references a receipt absent from the canonical chain",
        ));
    }
    Ok(found)
}

enum InitialGalleyHead {
    Existing(PoaBatchStreamHeadV2),
    Genesis {
        stream: PoaBatchStreamIdV2,
        semantic_head: [u8; 32],
        projection: Vec<u8>,
    },
}

fn galley_input(
    policy: &AuthenticatedPoaGalleyPolicyV1,
    snapshot: &GalleySnapshot,
    signer: [u8; 32],
    player_cell: [u8; 32],
    mode: &'static str,
    action_kind: &'static str,
    action_token: [u8; 32],
) -> Result<String> {
    let policy = std::str::from_utf8(&policy.policy_json)
        .map_err(|_| integrity("authenticated Galley policy is not UTF-8"))?;
    let projection = std::str::from_utf8(&snapshot.projection)
        .map_err(|_| integrity("durable Galley projection is not UTF-8"))?;
    let mut history = Vec::with_capacity(snapshot.history.len());
    for event in &snapshot.history {
        history.push(
            std::str::from_utf8(&event.event_json)
                .map_err(|_| integrity("durable Galley event is not UTF-8"))?,
        );
    }
    let input = format!(
        "{{\"format\":\"{GALLEY_INPUT_FORMAT}\",\"mode\":\"{mode}\",\"policy\":{policy},\"history\":[{}],\"claimed_projection\":{projection},\"viewer\":{{\"player\":\"{}\",\"player_cell\":\"{}\",\"sponsor_beneficiary\":\"{}\"}},\"action\":{{\"kind\":\"{action_kind}\",\"token\":\"{}\"}}}}",
        history.join(","),
        hex(signer),
        hex(player_cell),
        hex(signer),
        hex(action_token),
    );
    if input.len() > dregg_lean_ffi::poa_galley_ffi::MAX_POA_GALLEY_WIRE_BYTES {
        return Err(integrity("Galley native input exceeds transport bound"));
    }
    Ok(input)
}

fn call_galley(input: &str) -> Result<GalleyOutputWire> {
    let output = match judge_poa_galley_daily(input)
        .map_err(|error| integrity(format!("native Lean Galley judge failed: {error}")))?
    {
        PoaGalleyVerdict::Accepted(output) => output,
        PoaGalleyVerdict::Rejected => return Err(integrity("native Lean Galley judge refused")),
    };
    strict_json(output.as_bytes(), "native Lean Galley output")
}

fn validate_view(
    policy: &AuthenticatedPoaGalleyPolicyV1,
    snapshot: &GalleySnapshot,
    signer: [u8; 32],
    output: &GalleyOutputWire,
) -> Result<()> {
    if output.format != GALLEY_OUTPUT_FORMAT
        || output.event.is_some()
        || output.receipt.is_some()
        || output.replay.history_length != snapshot.sequence
        || output.replay.before_sequence != snapshot.sequence
        || output.replay.after_sequence != snapshot.sequence
        || output.projection.sequence != snapshot.sequence
        || output.replay.before_head != hex(snapshot.semantic_head)
        || output.replay.after_head != hex(snapshot.semantic_head)
        || output.view.available_actions.len() > MAX_GALLEY_ACTIONS
        || output.projection != strict_json(snapshot.projection.as_slice(), "Galley projection")?
    {
        return Err(integrity(
            "native Lean Galley view disagrees with durable history",
        ));
    }
    validate_output_shape(policy, signer, output)
}

struct JudgedGalleyEvent {
    statement: GalleyStatementWire,
    event_digest: [u8; 32],
    event_digest_hex: String,
    payload_digest: [u8; 32],
    payload: Vec<u8>,
    successor_projection_digest: [u8; 32],
    successor_projection_digest_hex: String,
    successor_projection: Vec<u8>,
}

fn validate_command(
    policy: &AuthenticatedPoaGalleyPolicyV1,
    snapshot: &GalleySnapshot,
    signer: [u8; 32],
    output: &GalleyOutputWire,
) -> Result<JudgedGalleyEvent> {
    validate_output_shape(policy, signer, output)?;
    let event = output
        .event
        .as_ref()
        .ok_or_else(|| integrity("native Lean Galley command omitted event"))?;
    let receipt = output
        .receipt
        .as_ref()
        .ok_or_else(|| integrity("native Lean Galley command omitted receipt"))?;
    let next = snapshot
        .sequence
        .checked_add(1)
        .ok_or_else(|| integrity("Galley sequence overflow"))?;
    if output.format != GALLEY_OUTPUT_FORMAT
        || output.replay.history_length != snapshot.sequence
        || output.replay.before_sequence != snapshot.sequence
        || output.replay.after_sequence != next
        || output.projection.sequence != next
        || output.replay.before_head != hex(snapshot.semantic_head)
        || event.statement.namespace_id != hex(policy.world.federation_id())
        || event.statement.kind != GALLEY_STREAM_KIND
        || event.statement.key != policy.policy.daily_id
        || event.statement.version != GALLEY_STREAM_VERSION
        || event.statement.sequence != next
        || event.statement.predecessor != hex(snapshot.semantic_head)
        || event.payload.kind != "public-play"
        || event.payload.actor != hex(signer)
        || event.payload.beneficiary != hex(signer)
        || event.payload.activity_id != policy.policy.public_activity_id
        || event.payload.grant_nullifier != zero_hex()
        || event.payload.authority_commitment != zero_hex()
        || event.payload.local_service != policy.policy.public_service
        || receipt.kind != "public-play"
        || receipt.actor != hex(signer)
        || receipt.beneficiary != hex(signer)
        || receipt.sequence != next
        || receipt.local_service != event.payload.local_service
        || receipt.consumed_grant_nullifier != event.payload.grant_nullifier
        || receipt.authority_commitment != event.payload.authority_commitment
        || receipt.power_delta != 0
        || receipt.loot_delta != 0
        || receipt.canon_revision_delta != 0
        || output.replay.after_head != event.event_digest
    {
        return Err(integrity(
            "native Lean Galley command disagrees with finalized public-play authority",
        ));
    }
    let payload = serde_json::to_vec(&event.payload)
        .map_err(|error| integrity(format!("Galley payload JSON failed: {error}")))?;
    let successor_projection = serde_json::to_vec(&output.projection)
        .map_err(|error| integrity(format!("Galley projection JSON failed: {error}")))?;
    Ok(JudgedGalleyEvent {
        statement: GalleyStatementWire {
            namespace_id: event.statement.namespace_id.clone(),
            kind: event.statement.kind,
            key: event.statement.key.clone(),
            version: event.statement.version,
            sequence: event.statement.sequence,
            predecessor: event.statement.predecessor.clone(),
            payload_digest: event.statement.payload_digest.clone(),
        },
        event_digest: decode_hex32(&event.event_digest)?,
        event_digest_hex: event.event_digest.clone(),
        payload_digest: decode_hex32(&event.statement.payload_digest)?,
        payload,
        successor_projection_digest: decode_hex32(&output.replay.projection_digest)?,
        successor_projection_digest_hex: output.replay.projection_digest.clone(),
        successor_projection,
    })
}

fn validate_output_shape(
    policy: &AuthenticatedPoaGalleyPolicyV1,
    signer: [u8; 32],
    output: &GalleyOutputWire,
) -> Result<()> {
    decode_hex32(&output.input_digest)?;
    decode_hex32(&output.policy_digest)?;
    decode_hex32(&output.replay.projection_digest)?;
    decode_hex32(&output.replay.before_head)?;
    decode_hex32(&output.replay.after_head)?;
    validate_projection_digests(&output.projection)?;
    if output.projection.public_players.len() > MAX_GALLEY_EVENTS
        || output.projection.sponsors.len() > MAX_GALLEY_EVENTS
        || output.projection.spent_grant_nullifiers.len() > MAX_GALLEY_EVENTS
        || output.event.is_some() != output.receipt.is_some()
        || output.view.available_actions.len() > MAX_GALLEY_ACTIONS
        || output.view.progress_current > output.view.progress_target
        || output.projection.power_root != policy.policy.power_root
        || output.projection.loot_root != policy.policy.loot_root
        || output.projection.canon_root != policy.policy.canon_root
        || output.projection.canon_revision != policy.policy.canon_revision
    {
        return Err(integrity("native Lean Galley output has incoherent shape"));
    }
    let mut tokens = BTreeSet::new();
    for action in &output.view.available_actions {
        let token = decode_hex32(&action.token)?;
        if !tokens.insert(token) || action.kind != "public-play" || action.actor != hex(signer) {
            return Err(integrity(
                "native Lean Galley output has invalid action set",
            ));
        }
    }
    Ok(())
}

fn validate_policy_digests(policy: &GalleyPolicyWire) -> Result<()> {
    for value in [
        &policy.deployment_id,
        &policy.federation_id,
        &policy.daily_id,
        &policy.genesis_head,
        &policy.event_id,
        &policy.rules_digest,
        &policy.public_activity_id,
        &policy.scene_content_id,
        &policy.public_action_content_id,
        &policy.sponsor_action_content_id,
        &policy.complete_content_id,
        &policy.power_root,
        &policy.loot_root,
        &policy.canon_root,
    ] {
        decode_hex32(value)?;
    }
    Ok(())
}

fn validate_projection_digests(projection: &GalleyProjectionWire) -> Result<()> {
    for value in projection
        .public_players
        .iter()
        .chain(&projection.sponsors)
        .chain(&projection.spent_grant_nullifiers)
        .chain([
            &projection.power_root,
            &projection.loot_root,
            &projection.canon_root,
        ])
    {
        decode_hex32(value)?;
    }
    Ok(())
}

fn initial_heads_digest_from_native(
    coordinate: EventBatchCoordinateWire,
    initial_heads: Vec<EventBatchHeadWire>,
) -> Result<[u8; 32]> {
    let input = EventBatchInitialHeadsDigestInputWire {
        format: EVENT_BATCH_INITIAL_HEADS_INPUT_FORMAT,
        coordinate,
        initial_heads,
    };
    let input_json = serde_json::to_string(&input).map_err(|error| {
        integrity(format!(
            "EventBatch initial-head digest input JSON failed: {error}"
        ))
    })?;
    let output = match digest_poa_event_batch_initial_heads(&input_json).map_err(|error| {
        integrity(format!(
            "native Lean EventBatch initial-head digest failed: {error}"
        ))
    })? {
        PoaEventBatchInitialHeadsDigestVerdict::Digested(output) => output,
        PoaEventBatchInitialHeadsDigestVerdict::Rejected => {
            return Err(integrity(
                "native Lean EventBatch initial-head digest refused Galley head set",
            ));
        }
    };
    let wire: EventBatchInitialHeadsDigestOutputWire = strict_json(
        output.as_str().as_bytes(),
        "EventBatch initial-head digest output",
    )?;
    if wire.format != EVENT_BATCH_INITIAL_HEADS_OUTPUT_FORMAT {
        return Err(integrity(
            "native Lean EventBatch initial-head digest returned wrong format",
        ));
    }
    decode_hex32(&wire.initial_heads_digest)
}

fn strict_json<T>(bytes: &[u8], label: &str) -> Result<T>
where
    T: for<'de> Deserialize<'de> + Serialize,
{
    if bytes.is_empty() || bytes.len() > MAX_COMPONENT_BYTES || bytes.contains(&0) {
        return Err(integrity(format!("{label} has invalid length or NUL")));
    }
    let value: T = serde_json::from_slice(bytes)
        .map_err(|_| integrity(format!("{label} is not strict typed JSON")))?;
    let reencoded = serde_json::to_vec(&value)
        .map_err(|error| integrity(format!("{label} JSON failed: {error}")))?;
    if reencoded != bytes {
        return Err(integrity(format!(
            "{label} is not byte-exact canonical JSON"
        )));
    }
    Ok(value)
}

fn clone_coordinate(value: &FinalizedTurnCoordinateV2) -> FinalizedTurnCoordinateV2 {
    // `FinalizedTurnCoordinateV2` is an ordinary immutable value; authority is
    // carried by its sealed parent, not by making coordinate fields secret.
    value.clone()
}

fn decode_hex32(value: &str) -> Result<[u8; 32]> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(integrity(
            "digest is not exactly 64 lowercase hexadecimal digits",
        ));
    }
    let mut out = [0u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        out[index] = (hex_nibble(pair[0])? << 4) | hex_nibble(pair[1])?;
    }
    Ok(out)
}

fn hex_nibble(value: u8) -> Result<u8> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err(integrity("invalid lowercase hexadecimal digit")),
    }
}

fn hex(value: impl AsRef<[u8]>) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let value = value.as_ref();
    let mut out = String::with_capacity(value.len() * 2);
    for byte in value {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    out
}

fn zero_hex() -> String {
    "00".repeat(32)
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyPolicyWire {
    deployment_id: String,
    federation_id: String,
    daily_id: String,
    genesis_head: String,
    dregg_mint: u64,
    snapshot_slot: u64,
    content_epoch: u64,
    event_id: String,
    rules_digest: String,
    public_activity_id: String,
    scene_content_id: String,
    public_action_content_id: String,
    sponsor_action_content_id: String,
    complete_content_id: String,
    public_service: u64,
    sponsor_service: u64,
    service_target: u64,
    power_root: String,
    loot_root: String,
    canon_root: String,
    canon_revision: u64,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct GalleyProjectionWire {
    sequence: u64,
    public_players: Vec<String>,
    sponsors: Vec<String>,
    spent_grant_nullifiers: Vec<String>,
    public_play_count: u64,
    sponsorship_count: u64,
    local_service_total: u64,
    power_root: String,
    loot_root: String,
    canon_root: String,
    canon_revision: u64,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyReplayWire {
    history_length: u64,
    before_sequence: u64,
    before_head: String,
    after_sequence: u64,
    after_head: String,
    projection_digest: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyActionWire {
    kind: String,
    token: String,
    actor: String,
    beneficiary: String,
    expires_after_sequence: u64,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyViewWire {
    phase: String,
    scene_content_id: String,
    status_content_id: String,
    progress_current: u64,
    progress_target: u64,
    public_play_count: u64,
    sponsorship_count: u64,
    available_actions: Vec<GalleyActionWire>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyStatementWire {
    namespace_id: String,
    kind: u64,
    key: String,
    version: u64,
    sequence: u64,
    predecessor: String,
    payload_digest: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyPayloadWire {
    kind: String,
    actor: String,
    beneficiary: String,
    activity_id: String,
    grant_nullifier: String,
    authority_commitment: String,
    local_service: u64,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyEventWire {
    statement: GalleyStatementWire,
    payload: GalleyPayloadWire,
    event_digest: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyReceiptWire {
    kind: String,
    actor: String,
    beneficiary: String,
    sequence: u64,
    local_service: u64,
    consumed_grant_nullifier: String,
    authority_commitment: String,
    power_delta: u64,
    loot_delta: u64,
    canon_revision_delta: u64,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GalleyOutputWire {
    format: String,
    input_digest: String,
    policy_digest: String,
    replay: GalleyReplayWire,
    projection: GalleyProjectionWire,
    view: GalleyViewWire,
    event: Option<GalleyEventWire>,
    receipt: Option<GalleyReceiptWire>,
}

#[derive(Clone, Serialize)]
struct EventBatchWorldWire {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
}

#[derive(Clone, Serialize)]
struct EventBatchCoordinateWire {
    world: EventBatchWorldWire,
    commit_ordinal: u64,
    block_id: String,
    turn_hash: String,
    receipt_hash: String,
    actor_root: String,
    signer: String,
}

#[derive(Clone, Serialize)]
struct EventBatchStreamWire {
    world: EventBatchWorldWire,
    kind: u64,
    key: String,
    version: u64,
}

#[derive(Clone, Serialize)]
struct EventBatchHeadWire {
    stream: EventBatchStreamWire,
    sequence: u64,
    semantic_head: String,
    storage_head_digest: String,
    projection_hex: String,
    origin: &'static str,
}

#[derive(Serialize)]
struct EventBatchStatementWire {
    namespace_id: String,
    kind: u64,
    key: String,
    version: u64,
    sequence: u64,
    predecessor: String,
    payload_digest: String,
}

#[derive(Serialize)]
struct EventBatchCandidateWire {
    event_index: u32,
    statement: EventBatchStatementWire,
    event_digest: String,
    payload_hex: String,
    successor_projection_digest: String,
    successor_projection_hex: String,
}

#[derive(Serialize)]
struct EventBatchBindingWire {
    event_index: u32,
    receipt_hash: String,
    actor_root: String,
    signer: String,
    event_digest: String,
    payload_digest: String,
    successor_projection_digest: String,
    successor_storage_head_digest: String,
}

#[derive(Serialize)]
struct EventBatchHostAuthorityWire {
    coordinate: EventBatchCoordinateWire,
    initial_heads_digest: String,
    events: Vec<EventBatchBindingWire>,
}

#[derive(Serialize)]
struct EventBatchInputWire {
    format: &'static str,
    authority: EventBatchHostAuthorityWire,
    coordinate: EventBatchCoordinateWire,
    initial_heads: Vec<EventBatchHeadWire>,
    events: Vec<EventBatchCandidateWire>,
}

#[derive(Serialize)]
struct EventBatchInitialHeadsDigestInputWire {
    format: &'static str,
    coordinate: EventBatchCoordinateWire,
    initial_heads: Vec<EventBatchHeadWire>,
}

#[derive(Deserialize, Serialize)]
struct EventBatchInitialHeadsDigestOutputWire {
    format: String,
    initial_heads_digest: String,
}

fn event_batch_world_wire(world: &PoaWorldIdentityV2) -> EventBatchWorldWire {
    EventBatchWorldWire {
        federation_id: hex(world.federation_id()),
        content_root: hex(world.content_root()),
        activation_digest: hex(world.activation_digest()),
        content_session: hex(world.content_session()),
        content_epoch: world.content_epoch(),
    }
}

fn event_batch_coordinate_wire(coordinate: &FinalizedTurnCoordinateV2) -> EventBatchCoordinateWire {
    EventBatchCoordinateWire {
        world: event_batch_world_wire(coordinate.world()),
        commit_ordinal: coordinate.commit_ordinal(),
        block_id: hex(coordinate.block_id()),
        turn_hash: hex(coordinate.turn_hash()),
        receipt_hash: hex(coordinate.receipt_hash()),
        actor_root: hex(coordinate.actor_root()),
        signer: hex(coordinate.signer()),
    }
}

fn event_batch_head_wire(
    head: &PoaBatchStreamHeadV2,
    origin: crate::PoaEventBatchInitialHeadOriginV2,
) -> EventBatchHeadWire {
    EventBatchHeadWire {
        stream: EventBatchStreamWire {
            world: event_batch_world_wire(head.stream().world()),
            kind: head.stream().kind(),
            key: hex(head.stream().key()),
            version: head.stream().schema_version(),
        },
        sequence: head.sequence(),
        semantic_head: hex(head.semantic_head()),
        storage_head_digest: hex(head.digest()),
        projection_hex: hex(head.projection()),
        origin: match origin {
            crate::PoaEventBatchInitialHeadOriginV2::Existing => "existing",
            crate::PoaEventBatchInitialHeadOriginV2::Genesis => "genesis",
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        PoaWorldActivationKindV1, PoaWorldActivationStatementV1, SignedPoaWorldActivationEnvelopeV1,
    };
    use dregg_lean_ffi::{
        poa_activated_content_ffi::poa_activated_content_runtime_available,
        poa_event_batch_ffi::{
            poa_event_batch_initial_heads_digest_available, poa_event_batch_runtime_available,
        },
        poa_galley_ffi::poa_galley_daily_available,
        poa_world_activation_ffi::poa_world_activation_available,
    };
    use ed25519_dalek::{Signer, SigningKey};

    fn world(root: u8) -> PoaWorldIdentityV2 {
        PoaWorldIdentityV2::new([2; 32], [root; 32], [0x52; 32], [0x53; 32], 7)
            .expect("fixture world")
    }

    fn policy_json() -> Vec<u8> {
        format!(
            "{{\"deployment_id\":\"{}\",\"federation_id\":\"{}\",\"daily_id\":\"{}\",\"genesis_head\":\"{}\",\"dregg_mint\":5,\"snapshot_slot\":6,\"content_epoch\":7,\"event_id\":\"{}\",\"rules_digest\":\"{}\",\"public_activity_id\":\"{}\",\"scene_content_id\":\"{}\",\"public_action_content_id\":\"{}\",\"sponsor_action_content_id\":\"{}\",\"complete_content_id\":\"{}\",\"public_service\":3,\"sponsor_service\":2,\"service_target\":10,\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",\"canon_revision\":18}}",
            hex([1; 32]),
            hex([2; 32]),
            hex([3; 32]),
            hex([4; 32]),
            hex([9; 32]),
            hex([10; 32]),
            hex([10; 32]),
            hex([11; 32]),
            hex([12; 32]),
            hex([13; 32]),
            hex([14; 32]),
            hex([15; 32]),
            hex([16; 32]),
            hex([17; 32]),
        )
        .into_bytes()
    }

    fn genesis_projection_json() -> Vec<u8> {
        format!(
            "{{\"sequence\":0,\"public_players\":[],\"sponsors\":[],\"spent_grant_nullifiers\":[],\"public_play_count\":0,\"sponsorship_count\":0,\"local_service_total\":0,\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",\"canon_revision\":18}}",
            hex([15; 32]),
            hex([16; 32]),
            hex([17; 32]),
        )
        .into_bytes()
    }

    fn policy(world: PoaWorldIdentityV2) -> AuthenticatedPoaGalleyPolicyV1 {
        AuthenticatedPoaGalleyPolicyV1::from_verified_content_inclusion(
            world,
            policy_json(),
            genesis_projection_json(),
        )
        .expect("fixture policy")
    }

    fn coordinate(world: PoaWorldIdentityV2, ordinal: u64) -> FinalizedTurnCoordinateV2 {
        FinalizedTurnCoordinateV2::new(
            world, ordinal, [0x61; 32], [0x62; 32], [0x63; 32], [0x64; 32], [0x65; 32],
        )
        .expect("fixture coordinate")
    }

    fn install_world(store: &PersistentStore, world: PoaWorldIdentityV2) {
        let key = SigningKey::from_bytes(&[0x71; 32]);
        store
            .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
            .expect("curator pin");
        let statement = PoaWorldActivationStatementV1::new(
            world,
            1,
            [0; 32],
            PoaWorldActivationKindV1::Advance,
            None,
        )
        .expect("activation statement");
        let signature = key.sign(&statement.signing_message().expect("signing message"));
        let envelope = SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            key.verifying_key().to_bytes(),
            signature.to_bytes(),
        )
        .expect("signed envelope");
        store
            .install_poa_world_activation_v1(envelope)
            .expect("installed world");
    }

    /// ⚑ **ARMED GUARD** (2026-08-08) — see `poa_world_activation::tests::require_native`. Absent
    /// export ⇒ PANIC naming the capability, never a silent `return` that prints `ok`.
    fn native_available() -> bool {
        dregg_lean_ffi::demand_lean(
            poa_world_activation_available()
                && poa_galley_daily_available()
                && poa_event_batch_runtime_available()
                && poa_event_batch_initial_heads_digest_available(),
            "the PoA Galley authority path (world-activation + galley-daily + event-batch runtime \
             + initial-heads digest)",
        )
    }

    fn activated_manifest_for_fixture() -> (PoaWorldIdentityV2, Vec<u8>) {
        use sha2::{Digest as _, Sha256};

        let policy = String::from_utf8(policy_json()).expect("policy UTF-8");
        let component_digest: [u8; 32] = Sha256::digest(policy.as_bytes()).into();
        let manifest = format!(
            concat!(
                "{{\"format\":\"POA-ACTIVATED-CONTENT-MANIFEST-1\",",
                "\"scope\":{{\"federation_id\":\"{}\",\"content_session\":\"{}\",",
                "\"content_epoch\":7}},\"legacy_whole_pack_sha256\":null,",
                "\"components\":[{{\"name\":\"poa.galley-maintenance-daily.policy.v1\",",
                "\"sha256\":\"{}\",\"bytes_utf8\":{}}}]}}"
            ),
            hex([2; 32]),
            hex([0x53; 32]),
            hex(component_digest),
            serde_json::to_string(&policy).expect("quoted policy"),
        )
        .into_bytes();
        let world = PoaWorldIdentityV2::new(
            [2; 32],
            Sha256::digest(&manifest).into(),
            [0x52; 32],
            [0x53; 32],
            7,
        )
        .expect("manifest world");
        (world, manifest)
    }

    fn offered_public_token(
        store: &PersistentStore,
        policy: &AuthenticatedPoaGalleyPolicyV1,
        signer: [u8; 32],
        player_cell: [u8; 32],
    ) -> [u8; 32] {
        let stream = PoaBatchStreamIdV2::new(
            policy.world.clone(),
            GALLEY_STREAM_KIND,
            decode_hex32(&policy.policy.daily_id).expect("daily id"),
            GALLEY_STREAM_VERSION,
        )
        .expect("Galley stream");
        let snapshot = store
            .load_galley_snapshot(policy, stream)
            .expect("Galley snapshot");
        let input = galley_input(
            policy,
            &snapshot,
            signer,
            player_cell,
            "view",
            "none",
            [0; 32],
        )
        .expect("view input");
        let output = call_galley(&input).expect("native view");
        validate_view(policy, &snapshot, signer, &output).expect("valid native view");
        let action = output
            .view
            .available_actions
            .iter()
            .find(|action| action.kind == "public-play")
            .expect("public action");
        decode_hex32(&action.token).expect("action token")
    }

    fn finalized_perform_fixture(
        authenticated: &AuthenticatedPoaGalleyPolicyV1,
        action_content_id: [u8; 32],
    ) -> (SignedTurn, TurnReceipt, CommitRecord) {
        let key = SigningKey::from_bytes(&[0x41; 32]);
        let signer = dregg_types::PublicKey(key.verifying_key().to_bytes());
        let mut turn = dregg_turn::poa_galley_carrier::galley_player_command_turn(
            &signer.0,
            8,
            Some([0x31; 32]),
            GalleyPlayerCommandV1::Perform {
                action_token: dregg_turn::poa_galley_carrier::GalleyActionToken::from_bytes(
                    [0x32; 32],
                ),
                action_content_id,
            },
        );
        // Pin the cached hashes to their canonical values as the normal signing
        // path does before the receipt is produced.
        turn.call_forest.hash();
        let turn_hash = turn.hash();
        let signed = SignedTurn {
            turn,
            signature: dregg_types::Signature(key.sign(&turn_hash).to_bytes()),
            signer,
            pq_signature: Vec::new(),
            pq_signer: Vec::new(),
        };
        let Effect::EmitEvent { cell, event } = &signed.turn.call_forest.roots[0].action.effects[0]
        else {
            panic!("fixture is exact EmitEvent")
        };
        let effect_hash = signed.turn.call_forest.roots[0].action.effects[0].hash();
        let receipt = TurnReceipt {
            turn_hash,
            forest_hash: signed.turn.call_forest.compute_hash(),
            pre_state_hash: [0x33; 32],
            post_state_hash: [0x34; 32],
            effects_hash: *blake3::hash(&effect_hash).as_bytes(),
            action_count: 1,
            previous_receipt_hash: signed.turn.previous_receipt_hash,
            agent: signed.turn.agent,
            federation_id: authenticated.world.federation_id(),
            emitted_events: vec![dregg_turn::EmittedEvent {
                cell: *cell,
                topic: event.topic,
                data: event.data.clone(),
            }],
            finality: Finality::Final,
            ..TurnReceipt::default()
        };
        let record = CommitRecord {
            ordinal: 5,
            height: 9,
            block_id: [0x35; 32],
            block_executed_up_to: 9,
            turn_hash,
            creator: signed.turn.agent.0,
            receipt_hash: receipt.receipt_hash(),
            ledger_root: [0x36; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        (signed, receipt, record)
    }

    #[test]
    fn exact_signed_perform_receipt_and_record_recover_private_facts() {
        let authenticated = policy(world(0x51));
        let (signed, receipt, record) = finalized_perform_fixture(&authenticated, [12; 32]);
        let verified =
            verify_poa_public_perform_facts_v1(&authenticated, &signed, &receipt, &record)
                .expect("exact public Perform facts");
        assert_eq!(verified.turn_hash, record.turn_hash);
        assert_eq!(verified.receipt_hash, record.receipt_hash);
        assert_eq!(verified.actor_root, receipt.pre_state_hash);
        assert_eq!(verified.signer, signed.signer.0);
        assert_eq!(verified.player_cell, signed.turn.agent.0);
        assert_eq!(verified.action_token, [0x32; 32]);
        assert_eq!(verified.action_content_id, [12; 32]);
    }

    #[test]
    fn signed_turn_and_receipt_postcard_require_complete_canonical_frames() {
        let authenticated = policy(world(0x51));
        let (signed, receipt, _) = finalized_perform_fixture(&authenticated, [12; 32]);
        let signed_wire = postcard::to_stdvec(&signed).expect("SignedTurn postcard");
        let signed_roundtrip: SignedTurn =
            postcard::from_bytes(&signed_wire).expect("canonical SignedTurn");
        assert_eq!(
            postcard::to_stdvec(&signed_roundtrip).expect("SignedTurn re-encode"),
            signed_wire
        );
        let mut signed_with_suffix = signed_wire;
        signed_with_suffix.extend_from_slice(&[0x00, 0x01]);
        let (_, signed_remainder): (SignedTurn, &[u8]) =
            postcard::take_from_bytes(&signed_with_suffix).expect("prefix still decodes");
        assert_eq!(signed_remainder, &[0x00, 0x01]);

        let receipt_wire = postcard::to_stdvec(&receipt).expect("TurnReceipt postcard");
        let receipt_roundtrip: TurnReceipt =
            postcard::from_bytes(&receipt_wire).expect("canonical TurnReceipt");
        assert_eq!(
            postcard::to_stdvec(&receipt_roundtrip).expect("TurnReceipt re-encode"),
            receipt_wire
        );
        let mut receipt_with_suffix = receipt_wire;
        receipt_with_suffix.push(0);
        let (_, receipt_remainder): (TurnReceipt, &[u8]) =
            postcard::take_from_bytes(&receipt_with_suffix).expect("prefix still decodes");
        assert_eq!(receipt_remainder, &[0]);
    }

    #[test]
    fn public_perform_fact_verifier_refuses_hostile_substitutions() {
        let authenticated = policy(world(0x51));
        let (signed, receipt, record) = finalized_perform_fixture(&authenticated, [12; 32]);

        let mut bad_signature = signed.clone();
        bad_signature.signature.0[0] ^= 0x80;
        assert!(
            verify_poa_public_perform_facts_v1(&authenticated, &bad_signature, &receipt, &record,)
                .is_err()
        );

        let mut partial_pq = signed.clone();
        partial_pq.pq_signature.push(1);
        assert!(
            verify_poa_public_perform_facts_v1(&authenticated, &partial_pq, &receipt, &record,)
                .is_err()
        );

        let (_, wrong_content_receipt, wrong_content_record) =
            finalized_perform_fixture(&authenticated, [13; 32]);
        let (wrong_content, _, _) = finalized_perform_fixture(&authenticated, [13; 32]);
        assert!(
            verify_poa_public_perform_facts_v1(
                &authenticated,
                &wrong_content,
                &wrong_content_receipt,
                &wrong_content_record,
            )
            .is_err()
        );

        let mut tentative = receipt.clone();
        tentative.finality = Finality::Tentative;
        let mut tentative_record = record.clone();
        tentative_record.receipt_hash = tentative.receipt_hash();
        assert!(
            verify_poa_public_perform_facts_v1(
                &authenticated,
                &signed,
                &tentative,
                &tentative_record,
            )
            .is_err()
        );

        let mut wrong_event = receipt.clone();
        wrong_event.emitted_events[0].data[1][0] ^= 1;
        let mut wrong_event_record = record.clone();
        wrong_event_record.receipt_hash = wrong_event.receipt_hash();
        assert!(
            verify_poa_public_perform_facts_v1(
                &authenticated,
                &signed,
                &wrong_event,
                &wrong_event_record,
            )
            .is_err()
        );

        let mut wrong_record = record.clone();
        wrong_record.creator[0] ^= 1;
        assert!(
            verify_poa_public_perform_facts_v1(&authenticated, &signed, &receipt, &wrong_record,)
                .is_err()
        );

        let mut wrong_world_receipt = receipt.clone();
        wrong_world_receipt.federation_id[0] ^= 1;
        let mut wrong_world_record = record;
        wrong_world_record.receipt_hash = wrong_world_receipt.receipt_hash();
        assert!(
            verify_poa_public_perform_facts_v1(
                &authenticated,
                &signed,
                &wrong_world_receipt,
                &wrong_world_record,
            )
            .is_err()
        );
    }

    #[test]
    fn sealed_carriers_refuse_zero_and_noncanonical_inputs() {
        let coordinate = coordinate(world(0x51), 0);
        assert!(
            PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
                coordinate, [0; 32], [1; 32], [12; 32],
            )
            .is_err()
        );

        let mut padded = policy_json();
        padded.push(b'\n');
        assert!(
            AuthenticatedPoaGalleyPolicyV1::from_verified_content_inclusion(
                world(0x51),
                padded,
                genesis_projection_json(),
            )
            .is_err()
        );

        let mut wrong_projection = genesis_projection_json();
        let needle = b"\"sequence\":0";
        let index = wrong_projection
            .windows(needle.len())
            .position(|window| window == needle)
            .expect("sequence field");
        wrong_projection[index + needle.len() - 1] = b'1';
        assert!(
            AuthenticatedPoaGalleyPolicyV1::from_verified_content_inclusion(
                world(0x51),
                policy_json(),
                wrong_projection,
            )
            .is_err()
        );
    }

    #[test]
    fn preparation_refuses_absent_or_substituted_active_world_before_play() {
        let store = PersistentStore::open_in_memory().expect("store");
        let authenticated = policy(world(0x51));
        let finalized = PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
            coordinate(world(0x51), 0),
            [0x66; 32],
            [0x67; 32],
            [12; 32],
        )
        .expect("finalized carrier");
        assert!(
            store
                .prepare_poa_galley_public_event_batch_v1(&authenticated, finalized)
                .is_err()
        );

        // ⛑ ARMED (2026-08-08). The `is_err()` leg above runs on an EMPTY store, so it passes
        // for the trivial reason "no world is installed at all". Everything below is the
        // SUBSTITUTED-world leg — the other half of this test's name — and it used to be skipped
        // in silence, so on an archive-less lane this test checked half of what it claims.
        if !dregg_lean_ffi::demand_lean(
            poa_world_activation_available(),
            "the SUBSTITUTED-active-world leg of poa_galley_authority preparation",
        ) {
            return;
        }
        install_world(&store, world(0x59));
        let finalized = PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
            coordinate(world(0x51), 0),
            [0x66; 32],
            [0x67; 32],
            [12; 32],
        )
        .expect("finalized carrier");
        assert!(
            store
                .prepare_poa_galley_public_event_batch_v1(&authenticated, finalized)
                .is_err()
        );
    }

    #[test]
    fn native_public_play_prepares_one_opaque_event_and_stale_token_refuses() {
        if !native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let active_world = world(0x51);
        install_world(&store, active_world.clone());
        let authenticated = policy(active_world.clone());
        let signer = [0x65; 32];
        let player_cell = [0x66; 32];
        let token = offered_public_token(&store, &authenticated, signer, player_cell);

        let stale = PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
            coordinate(active_world.clone(), 0),
            player_cell,
            [0x7f; 32],
            [12; 32],
        )
        .expect("stale finalized carrier");
        assert!(
            store
                .prepare_poa_galley_public_event_batch_v1(&authenticated, stale)
                .is_err()
        );

        let finalized = PreparedPoaFinalizedTurnAuthorityV1::from_exact_public_perform(
            coordinate(active_world, 0),
            player_cell,
            token,
            [12; 32],
        )
        .expect("finalized carrier");
        let prepared = store
            .prepare_poa_galley_public_event_batch_v1(&authenticated, finalized)
            .expect("opaque Galley batch");
        assert_eq!(prepared.event_count(), 1);
        assert_eq!(prepared.coordinate().commit_ordinal(), 0);
        assert_ne!(prepared.batch_digest(), [0; 32]);
    }

    #[test]
    fn active_observation_is_minted_from_sealed_content_and_native_replay() {
        if !native_available()
            || !dregg_lean_ffi::demand_lean(
                poa_activated_content_runtime_available(),
                "the PoA activated-content runtime (native replay leg)",
            )
        {
            return;
        }
        let store = PersistentStore::open_in_memory().expect("store");
        let (world, manifest) = activated_manifest_for_fixture();
        install_world(&store, world.clone());
        store
            .install_poa_activated_content_v1(manifest)
            .expect("activated Galley content");

        let player_key = SigningKey::from_bytes(&[0x65; 32]);
        let signer = player_key.verifying_key().to_bytes();
        let observed = store
            .observe_active_poa_galley_v1(signer)
            .expect("audited active observation");
        assert_eq!(observed.world(), &world);
        assert_eq!(observed.daily_id(), [3; 32]);
        assert_eq!(observed.public_action_content_id(), [12; 32]);
        assert_eq!(observed.sequence(), 0);
        assert_eq!(observed.events(), &[]);
        assert_eq!(observed.actions().len(), 1);
        assert_eq!(observed.actions()[0].expires_after_sequence(), 0);
        assert_ne!(observed.actions()[0].token(), [0; 32]);
        assert_eq!(observed.projection_json(), genesis_projection_json());
        assert_ne!(observed.projection_digest(), [0; 32]);

        let signed_perform = |token: [u8; 32]| {
            let mut turn = dregg_turn::poa_galley_carrier::galley_player_command_turn(
                &signer,
                0,
                None,
                GalleyPlayerCommandV1::Perform {
                    action_token: dregg_turn::poa_galley_carrier::GalleyActionToken::from_bytes(
                        token,
                    ),
                    action_content_id: observed.public_action_content_id(),
                },
            );
            turn.call_forest.hash();
            let turn_hash = turn.hash();
            SignedTurn {
                turn,
                signature: dregg_types::Signature(player_key.sign(&turn_hash).to_bytes()),
                signer: dregg_types::PublicKey(signer),
                pq_signature: Vec::new(),
                pq_signer: Vec::new(),
            }
        };
        let exact = signed_perform(observed.actions()[0].token());
        let first = store
            .preflight_active_poa_galley_public_perform_v1(&exact)
            .expect("exact active preflight");
        let retry = store
            .preflight_active_poa_galley_public_perform_v1(&exact)
            .expect("exact retry preflight");
        assert_eq!(first, retry);
        let stale = signed_perform([0xee; 32]);
        assert!(matches!(
            store.preflight_active_poa_galley_public_perform_v1(&stale),
            Err(PoaGalleyPublicPerformPreflightErrorV1::StaleAction(_))
        ));
    }

    #[test]
    fn observed_receipt_join_is_dense_canonical_and_coordinate_exact() {
        let store = PersistentStore::open_in_memory().expect("store");
        let signer = [0x65; 32];
        let world = world(0x51);
        let mut receipt = TurnReceipt {
            turn_hash: [0x62; 32],
            pre_state_hash: [0x64; 32],
            agent: galley_player_cell(&signer),
            federation_id: world.federation_id(),
            finality: Finality::Final,
            ..TurnReceipt::default()
        };
        // Keep every hash-bound field fixed before deriving the coordinate.
        receipt.post_state_hash = [0x70; 32];
        let bytes = postcard::to_stdvec(&receipt).expect("canonical receipt");
        store
            .append_receipt_chain_entry(0, &bytes)
            .expect("receipt chain append");
        let coordinate = FinalizedTurnCoordinateV2::new(
            world,
            0,
            [0x61; 32],
            receipt.turn_hash,
            receipt.receipt_hash(),
            receipt.pre_state_hash,
            signer,
        )
        .expect("coordinate");
        let event = GalleySnapshotEvent {
            coordinate,
            sequence: 1,
            event_digest: [0x71; 32],
            payload_digest: [0x72; 32],
            payload_json: b"{}".to_vec(),
            event_json: b"{}".to_vec(),
        };
        let write = store.db.begin_write().expect("writer");
        let joined = load_galley_receipts_in(&write, &[event]).expect("exact receipt join");
        write.abort().expect("abort read-only writer");
        assert_eq!(joined.get(&receipt.receipt_hash()), Some(&(0, bytes)));
    }
}
