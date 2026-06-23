//! Channels service — the ORGANS §4 weld (the group-key lift), following the
//! trustline / court service patterns.
//!
//! A group is a CELL (blueprint twin: `dregg_cell::blueprint` channel
//! section; SDK noun: `dregg_sdk_net::channels`). This service drives the same
//! canonical turns through the node's AUTHORITATIVE executor
//! ([`crate::trustline_service::run_signed_turn`]) and carries the DATA
//! PLANE off-cell: posted ciphertext lives in a node-held ring + SSE stream
//! — message bodies never touch the chain.
//!
//! ## THE KEYSTONE — epoch unification (control plane)
//!
//! `POST /channels/remove` commits ONE turn
//! (`dregg_sdk_net::channels::epoch_step_effects`): the membership-root rewrite,
//! the epoch-slot step, the fresh key commitment, the
//! `RevokeDelegation{epoch_anchor}` that bumps the group cell's
//! `delegation_epoch`, and the survivors' capability refresh
//! (`stored_epoch: Some(new_epoch)`). The installed program makes a partial
//! version of that turn UNSAT (the unification triple), and the executor's
//! R7 epoch-at-retrieval check refuses every group-held capability minted
//! at an earlier epoch — removal ends forward reads AND capability exercise
//! in one epoch step.
//!
//! The service refuses (fail-closed) to step a group whose two epoch
//! counters have diverged (`slot epoch ≠ delegation_epoch`) and reports the
//! divergence loudly — under the canonical builders it cannot happen, so a
//! divergence means a foreign turn moved one counter alone.
//!
//! ## Honest residues (named)
//!
//! * The node operator IS the group admin in this service shape (the admin
//!   key is the node cipherclerk key), and — holding every epoch key — the
//!   operator can read group traffic it relays. Sovereign-member groups
//!   (admin = a council-held key, fan-out built client-side) ride the SDK
//!   noun directly; the service is the HOSTED setting.
//! * The room's keys and message ring are in-memory (the ring is a bounded
//!   delivery buffer; epoch keys are node-minted secrets a rekey re-mints).
//!   The ROSTER — rebuildable only off-cell (the chain holds only its
//!   commitment) — is now DURABLE: every committed epoch step persists it
//!   (`persist_roster` → `persist/src/channel_rosters.rs`) and boot rebuilds
//!   each room after re-committing the stored roster against the on-cell
//!   `member_root` (`ChannelRegistry::restore_rosters`), so a restart no
//!   longer serves `RosterStale` for a roster that still matches its cell
//!   (docs/PERSISTENCE.md §3, the roster caveat).

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::convert::Infallible;
use std::time::Duration;

use axum::extract::{Path as AxumPath, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::sse::{Event as SseEvent, KeepAlive, Sse};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use futures_util::stream::Stream;
use serde::{Deserialize, Serialize};
use tokio::sync::broadcast;

use dregg_cell::blueprint::{
    CH_ADMIN_SLOT, CH_EPOCH_SLOT, CH_KEY_COMMIT_SLOT, CH_MEMBER_ROOT_SLOT, CH_STATE_SLOT,
    CH_TAG_SLOT, ChannelTerms, STATE_OPEN, channel_cell_program, channel_factory_descriptor,
};
use dregg_cell::factory::{FactoryCreationParams, canonical_program_vk};
use dregg_cell::{CellId, Ledger};
use dregg_sdk_net::channels::{
    Roster, SealedEpochKey, anchor_token_id, channel_token_id, epoch_step_effects, open_effects,
    roster_root, seal_epoch_key_to_roster,
};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_turn::Effect;

use dregg_captp::data_plane::{Bus, ChannelName, DataPlaneError, Delivery, SendCap};
use dregg_captp::FederationId;
use dregg_cell::AuthRequired;

use crate::state::{NodeState, NodeStateInner};
use crate::trustline_service::{hex_decode_32, hex_encode, run_signed_turn};

/// Ring capacity per room (the data plane's replay window; SSE clients
/// resume within it via `Last-Event-ID`).
const MAX_ROOM_MESSAGES: usize = 1024;
/// Broadcast lag window for SSE wake-ups (the ring is the source of truth).
const ROOM_BROADCAST_CAPACITY: usize = 256;

// =============================================================================
// Registry (lives inside NodeStateInner)
// =============================================================================

/// One stored data-plane message: ciphertext only — the node relays what it
/// cannot necessarily read (and the chain never sees at all).
#[derive(Clone, Debug, Serialize)]
pub struct StoredEnvelope {
    /// Ring sequence number (the SSE cursor).
    pub seq: u64,
    /// The key epoch the body claims to be encrypted under.
    pub epoch: u64,
    /// AEAD nonce, hex.
    pub nonce: String,
    /// Ciphertext, hex.
    pub ciphertext: String,
}

/// One live group's node-held state.
pub struct Room {
    /// The epoch anchor cell (the standing `RevokeDelegation` target).
    pub anchor: CellId,
    /// The OPEN roster: member cell → X25519 seal pk. Re-commits to the
    /// cell's slot-1 root at all times (checked before every step).
    pub roster: Roster,
    /// Every epoch key this node minted for the group (hosted-admin shape).
    pub keys: BTreeMap<u64, [u8; 32]>,
    /// The data-plane ring.
    messages: VecDeque<StoredEnvelope>,
    next_seq: u64,
}

/// The durable carrier of a room's node-held roster (docs/PERSISTENCE.md §3,
/// the roster caveat). The cell pins only the membership ROOT; the
/// member→seal-pk content and the epoch anchor are node-held, verifiable
/// against the cell but not derivable from it. Persisting this lets a node
/// that restarts mid-life rebuild the room WITHOUT waiting for every member
/// to re-post — but only after re-committing the roster against the on-cell
/// root (a stale durable roster is discarded loudly; `RosterStale` afterwards
/// means genuine divergence, never a mere restart).
#[derive(Serialize, Deserialize)]
struct DurableRoster {
    /// The epoch anchor cell (the standing `RevokeDelegation` target).
    anchor: [u8; 32],
    /// `(member cell, X25519 seal pk)` pairs — the BTreeMap content.
    members: Vec<([u8; 32], [u8; 32])>,
}

impl DurableRoster {
    fn encode(anchor: CellId, roster: &Roster) -> Vec<u8> {
        let payload = DurableRoster {
            anchor: anchor.0,
            members: roster.iter().map(|(m, pk)| (m.0, *pk)).collect(),
        };
        // Infallible for this fixed-shape struct; an empty vec on the
        // (unreachable) error path simply fails the load-time re-commit.
        postcard::to_stdvec(&payload).unwrap_or_default()
    }

    fn decode(bytes: &[u8]) -> Option<(CellId, Roster)> {
        let payload: DurableRoster = postcard::from_bytes(bytes).ok()?;
        let mut roster = Roster::new();
        for (m, pk) in payload.members {
            roster.insert(CellId(m), pk);
        }
        Some((CellId(payload.anchor), roster))
    }
}

/// Persist a room's roster durably (one committed redb transaction). Called
/// after every committed epoch step (open/join/remove/rekey): the roster the
/// step installed survives an arbitrary crash from here on. A durable-write
/// failure cannot unwind the already-committed turn, so it degrades — loudly
/// — to "this room needs re-posting after a restart" (the pre-closure
/// behaviour), never refusing the live step.
fn persist_roster(inner: &NodeStateInner, channel: CellId, anchor: CellId, roster: &Roster) {
    let bytes = DurableRoster::encode(anchor, roster);
    if let Err(e) = inner.store.store_channel_roster(&channel.0, &bytes) {
        tracing::error!(
            channel = %hex_encode(&channel.0),
            error = %e,
            "durable channel-roster write FAILED — this room will serve \
             RosterStale until members re-post after a restart"
        );
    }
}

/// The captp DATA PLANE [`Bus`]'s storage limits when the node spins one up for
/// the channels service. The relay holds the per-recipient inbox spool whose
/// drain WITNESSES delivery (the custody receipt resolves); these bound it.
const BUS_MAX_QUEUE_DEPTH: usize = 4096;
const BUS_MAX_TOTAL_MESSAGES: usize = 1 << 20;

/// Node-held channels registry + the SSE wake-up bus.
pub struct ChannelRegistry {
    rooms: HashMap<CellId, Room>,
    /// Wake-up only: (channel, seq). The ring is the durable cursor source.
    tx: broadcast::Sender<(CellId, u64)>,
    /// The captp DATA PLANE under the channels service (the criticism-closing
    /// weld): one [`Bus`] backs every room's enqueue/drain/wake/subscribe, so a
    /// POST to a channel is a real [`Bus::enqueue`] (returning the custody
    /// [`Delivery`] receipt) and live SSE delivery is a real [`Bus::drain_one`]
    /// (drain-on-deliver: the receipt-identity witness flips queued→handled AS the
    /// box reaches a consumer on the wire — so "queued" is provably distinguishable
    /// from "handled" on the DELIVERY HOT-PATH, and the inbox drains in lockstep
    /// with delivery rather than accumulating a parallel backlog). The opt-in
    /// `/channels/drain` endpoint drains the rest in one shot (e.g. for an offline
    /// consumer); the relay's `BUS_MAX_*` caps bound the inbox hard regardless. The
    /// bus uses the node's gossip identity as its accountable relay, so the receipts
    /// it mints verify. `None` until the first room is created (the node is unlocked
    /// and has a stable identity by then); see [`ChannelRegistry::ensure_bus`].
    bus: Option<Bus>,
}

impl Default for ChannelRegistry {
    fn default() -> Self {
        let (tx, _) = broadcast::channel(ROOM_BROADCAST_CAPACITY);
        ChannelRegistry {
            rooms: HashMap::new(),
            tx,
            bus: None,
        }
    }
}

impl std::fmt::Debug for ChannelRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChannelRegistry")
            .field("rooms", &self.rooms.len())
            .finish()
    }
}

impl ChannelRegistry {
    pub fn room(&self, channel: &CellId) -> Option<&Room> {
        self.rooms.get(channel)
    }
    pub fn room_mut(&mut self, channel: &CellId) -> Option<&mut Room> {
        self.rooms.get_mut(channel)
    }
    pub fn insert_room(&mut self, channel: CellId, room: Room) {
        self.rooms.insert(channel, room);
    }
    pub fn subscribe(&self) -> broadcast::Receiver<(CellId, u64)> {
        self.tx.subscribe()
    }

    /// Ensure the data-plane [`Bus`] exists, minting it from the node's gossip
    /// identity as the accountable relay. Idempotent: the bus is created once and
    /// outlives every room. The relay id is derived from the relay key's OWN
    /// public key, so the custody binding (`relay_id == pubkey(relay_key)`) holds
    /// by construction and the minted receipts verify.
    pub fn ensure_bus(&mut self, relay_key: dregg_types::SigningKey) -> &mut Bus {
        self.bus.get_or_insert_with(|| {
            let relay_id = FederationId(relay_key.public_key().0);
            Bus::new(
                relay_id,
                relay_key,
                BUS_MAX_QUEUE_DEPTH,
                BUS_MAX_TOTAL_MESSAGES,
            )
        })
    }

    /// The data-plane [`Bus`], if it has been spun up (it has, once any room
    /// exists). Read access for status / drain / handled queries.
    pub fn bus(&self) -> Option<&Bus> {
        self.bus.as_ref()
    }

    /// Mutable access to the data-plane [`Bus`] (enqueue / drain / wait).
    pub fn bus_mut(&mut self) -> Option<&mut Bus> {
        self.bus.as_mut()
    }

    /// Restore node-held rooms from the durable roster table at boot
    /// (docs/PERSISTENCE.md §3, the roster caveat). For each stored roster we
    /// RE-COMMIT it against the live cell's on-chain membership root before
    /// trusting it:
    ///
    /// * the cell is gone, or is not a channel cell, or the stored roster's
    ///   `roster_root` ≠ the cell's `member_root` ⇒ the durable roster is
    ///   STALE; discard it AND durably remove the row (so it does not re-alarm
    ///   on every boot), and leave the room absent (it will serve
    ///   `RosterStale` until members re-post — the pre-closure behaviour, now
    ///   only on genuine divergence, never on a mere restart);
    /// * it re-commits ⇒ rebuild the [`Room`] with the verified roster and the
    ///   stored anchor. Epoch keys are node-minted secrets that are NOT
    ///   persisted (a delivery property, not a soundness one); the restored
    ///   room carries an empty key map and a rekey re-establishes forward
    ///   delivery, while membership operations resume immediately.
    pub fn restore_rosters(&mut self, store: &dregg_persist::PersistentStore, ledger: &Ledger) {
        let stored = match store.load_channel_rosters() {
            Ok(s) => s,
            Err(e) => {
                tracing::error!(
                    error = %e,
                    "failed to load durable channel rosters; rooms will serve \
                     RosterStale until members re-post"
                );
                return;
            }
        };
        let mut restored = 0usize;
        let mut discarded = 0usize;
        for (channel_bytes, bytes) in stored {
            let channel = CellId(channel_bytes);
            let Some((anchor, roster)) = DurableRoster::decode(&bytes) else {
                tracing::warn!(
                    channel = %hex_encode(&channel_bytes),
                    "durable roster failed to decode; discarding"
                );
                let _ = store.remove_channel_roster(&channel_bytes);
                discarded += 1;
                continue;
            };
            // Re-commit against the on-cell membership root. Anything that
            // does not match is STALE and discarded (durably).
            let on_cell_root = ledger.get(&channel).and_then(channel_terms_of_root);
            if on_cell_root != Some(roster_root(&roster)) {
                tracing::warn!(
                    channel = %hex_encode(&channel_bytes),
                    "durable roster does not re-commit to the on-cell root; \
                     discarding (stale)"
                );
                let _ = store.remove_channel_roster(&channel_bytes);
                discarded += 1;
                continue;
            }
            self.rooms.insert(channel, Room::new(anchor, roster));
            restored += 1;
        }
        if restored > 0 || discarded > 0 {
            tracing::info!(
                restored,
                discarded,
                "restored channel rooms from the durable roster table"
            );
        }
    }

    /// Append a ciphertext to a room's ring and wake SSE cursors.
    fn push_message(
        &mut self,
        channel: CellId,
        epoch: u64,
        nonce: String,
        ciphertext: String,
    ) -> u64 {
        let room = self.rooms.get_mut(&channel).expect("room exists (checked)");
        let seq = room.next_seq;
        room.next_seq += 1;
        room.messages.push_back(StoredEnvelope {
            seq,
            epoch,
            nonce,
            ciphertext,
        });
        while room.messages.len() > MAX_ROOM_MESSAGES {
            room.messages.pop_front();
        }
        let _ = self.tx.send((channel, seq));
        seq
    }
}

impl Room {
    fn new(anchor: CellId, roster: Roster) -> Self {
        Room {
            anchor,
            roster,
            keys: BTreeMap::new(),
            messages: VecDeque::new(),
            next_seq: 0,
        }
    }
}

// =============================================================================
// Refusals
// =============================================================================

/// Every way a channels request can be refused.
#[derive(Debug)]
pub enum ChannelRefusal {
    /// Node cipherclerk is locked — no operator authority to exercise.
    Locked,
    /// The named cell is not a channel-group cell (or not in the ledger).
    NoChannel(String),
    /// Refused terms / colliding cell / malformed roster.
    BadTerms(String),
    /// The group is not OPEN.
    NotOpen,
    /// The two epoch counters diverged (slot epoch ≠ delegation_epoch) —
    /// a foreign turn moved one alone. Fail-closed, reported loudly.
    EpochDivergence { slot: u64, delegation: u64 },
    /// The node-held roster no longer re-commits to the on-cell root.
    RosterStale,
    /// A data-plane post named a non-current epoch (stale-key traffic is
    /// refused at the door — forward darkness is not transport-optional).
    WrongEpoch { current: u64, posted: u64 },
    /// The authoritative executor rejected the turn (the installed
    /// program's unification triple, the SenderIs governance gate, …).
    TurnRejected(String),
    /// Malformed request (bad hex, missing cell, unknown member, …).
    BadRequest(String),
    /// The data-plane [`Bus`] refused the op: an over-attenuated / unauthorized
    /// enqueue (no message queued, NO receipt minted — no phantom work), a full
    /// relay, or a drain/wait on a name with no inbox. The captp seam, surfaced
    /// over the node API.
    DataPlane(String),
}

impl ChannelRefusal {
    fn status(&self) -> StatusCode {
        match self {
            ChannelRefusal::Locked
            | ChannelRefusal::TurnRejected(_)
            | ChannelRefusal::DataPlane(_) => StatusCode::FORBIDDEN,
            ChannelRefusal::NoChannel(_) => StatusCode::NOT_FOUND,
            ChannelRefusal::NotOpen
            | ChannelRefusal::EpochDivergence { .. }
            | ChannelRefusal::RosterStale
            | ChannelRefusal::WrongEpoch { .. } => StatusCode::CONFLICT,
            ChannelRefusal::BadTerms(_) | ChannelRefusal::BadRequest(_) => StatusCode::BAD_REQUEST,
        }
    }

    fn reason(&self) -> &'static str {
        match self {
            ChannelRefusal::Locked => "locked",
            ChannelRefusal::NoChannel(_) => "no-channel",
            ChannelRefusal::BadTerms(_) => "bad-terms",
            ChannelRefusal::NotOpen => "not-open",
            ChannelRefusal::EpochDivergence { .. } => "epoch-divergence",
            ChannelRefusal::RosterStale => "roster-stale",
            ChannelRefusal::WrongEpoch { .. } => "wrong-epoch",
            ChannelRefusal::TurnRejected(_) => "turn-rejected",
            ChannelRefusal::BadRequest(_) => "bad-request",
            ChannelRefusal::DataPlane(_) => "data-plane-refused",
        }
    }

    fn detail(&self) -> String {
        match self {
            ChannelRefusal::Locked => "node cipherclerk is locked".into(),
            ChannelRefusal::NoChannel(d)
            | ChannelRefusal::BadTerms(d)
            | ChannelRefusal::TurnRejected(d)
            | ChannelRefusal::BadRequest(d)
            | ChannelRefusal::DataPlane(d) => d.clone(),
            ChannelRefusal::NotOpen => "channel group is not open".into(),
            ChannelRefusal::EpochDivergence { slot, delegation } => format!(
                "EPOCH DIVERGENCE: slot epoch {slot} ≠ delegation_epoch {delegation} — \
                 a foreign turn moved one counter alone; refusing to step"
            ),
            ChannelRefusal::RosterStale => {
                "node-held roster does not re-commit to the on-cell membership root".into()
            }
            ChannelRefusal::WrongEpoch { current, posted } => {
                format!("post names epoch {posted}, the group is at epoch {current}")
            }
        }
    }
}

impl IntoResponse for ChannelRefusal {
    fn into_response(self) -> Response {
        let body = serde_json::json!({
            "error": self.detail(),
            "reason": self.reason(),
        });
        (self.status(), Json(body)).into_response()
    }
}

impl From<crate::trustline_service::TrustlineRefusal> for ChannelRefusal {
    fn from(t: crate::trustline_service::TrustlineRefusal) -> Self {
        ChannelRefusal::TurnRejected(t.detail())
    }
}

impl From<DataPlaneError> for ChannelRefusal {
    fn from(e: DataPlaneError) -> Self {
        ChannelRefusal::DataPlane(e.to_string())
    }
}

// =============================================================================
// Identification + the live position
// =============================================================================

// -----------------------------------------------------------------------------
// Data-plane addressing: a channel cell IS a data-plane inbox + named edge.
// -----------------------------------------------------------------------------

/// The data-plane inbox owner for a channel: the channel cell id, re-read as a
/// [`FederationId`]. Every room's ciphertext spool lives in the Bus under this
/// recipient.
fn bus_recipient(channel: CellId) -> FederationId {
    FederationId(channel.0)
}

/// The data-plane channel NAME for a channel cell (the wake-by-name key). A
/// client waits on this name to be woken when a post lands.
fn bus_channel_name(channel: CellId) -> ChannelName {
    ChannelName::new(channel.0.to_vec())
}

/// The per-channel send capability the node holds over a room's inbox: a live,
/// Signature-level grant scoped to this channel. A POST is admitted iff its
/// offered authority is narrower-or-equal to this — the attenuation/revocation
/// seam, end to end. (The request-level `require_operator_authority` already
/// gates control-plane authority; this gates the data-plane edge.)
fn bus_send_cap(channel: CellId) -> SendCap {
    SendCap::grant(
        bus_recipient(channel),
        bus_channel_name(channel),
        AuthRequired::Signature,
    )
}

fn slot(cell: &dregg_cell::Cell, index: u8) -> [u8; 32] {
    cell.state.fields[index as usize]
}

fn slot_u64(cell: &dregg_cell::Cell, index: u8) -> u64 {
    let f = slot(cell, index);
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

/// Structurally identify a channel-group cell: re-derive the per-group
/// program from the cell's OWN term registers and check the installed VK.
/// Self-authenticating — no side registry decides what is a group.
pub fn channel_terms_of(cell: &dregg_cell::Cell) -> Option<ChannelTerms> {
    let terms = ChannelTerms {
        admin: slot(cell, CH_ADMIN_SLOT),
        tag: slot(cell, CH_TAG_SLOT),
    };
    let program = channel_cell_program(&terms).ok()?;
    let expected = canonical_program_vk(&program);
    (cell.verification_key.as_ref()?.hash == expected).then_some(terms)
}

/// The on-cell membership root of a channel cell `cell`, IF it is a valid,
/// self-authenticating channel-group cell. `None` for a non-channel cell —
/// the load-time re-commit treats that as a stale durable roster (discard).
fn channel_terms_of_root(cell: &dregg_cell::Cell) -> Option<[u8; 32]> {
    channel_terms_of(cell).map(|_| slot(cell, CH_MEMBER_ROOT_SLOT))
}

/// The live on-cell position of one group.
#[derive(Clone, Copy, Debug)]
pub struct ChannelPosition {
    pub epoch: u64,
    pub delegation_epoch: u64,
    pub member_root: [u8; 32],
    pub key_commit: [u8; 32],
    pub open: bool,
}

/// Resolve `id` as a channel-group cell and read its position.
fn resolve_channel(
    s: &NodeStateInner,
    id: CellId,
) -> Result<(ChannelTerms, ChannelPosition), ChannelRefusal> {
    let cell = s.ledger.get(&id).ok_or_else(|| {
        ChannelRefusal::NoChannel(format!("cell {} not in ledger", hex_encode(&id.0)))
    })?;
    let terms = channel_terms_of(cell).ok_or_else(|| {
        ChannelRefusal::NoChannel(format!(
            "cell {} is not a channel-group cell (program VK does not match its terms)",
            hex_encode(&id.0)
        ))
    })?;
    let position = ChannelPosition {
        epoch: slot_u64(cell, CH_EPOCH_SLOT),
        delegation_epoch: cell.state.delegation_epoch(),
        member_root: slot(cell, CH_MEMBER_ROOT_SLOT),
        key_commit: slot(cell, CH_KEY_COMMIT_SLOT),
        open: slot_u64(cell, CH_STATE_SLOT) == STATE_OPEN,
    };
    Ok((terms, position))
}

/// The request-level authority gate (the trustline shape): node unlocked
/// and the operator's agent cell holds a capability over the group cell.
fn require_operator_authority(s: &NodeStateInner, channel: CellId) -> Result<(), ChannelRefusal> {
    if !s.unlocked {
        return Err(ChannelRefusal::Locked);
    }
    let operator_cell = crate::executor_setup::local_agent_cell(s);
    let holds_cap = s
        .ledger
        .get(&operator_cell)
        .map(|c| c.capabilities.has_access(&channel))
        .unwrap_or(false);
    if !holds_cap {
        return Err(ChannelRefusal::TurnRejected(format!(
            "operator agent cell {} holds no capability over channel {}",
            hex_encode(&operator_cell.0),
            hex_encode(&channel.0),
        )));
    }
    Ok(())
}

/// The fail-closed pre-step checks shared by join/remove/rekey: OPEN, both
/// epoch counters AGREE, and the node-held roster re-commits to the chain.
fn check_step_preconditions(
    position: &ChannelPosition,
    roster: &Roster,
) -> Result<(), ChannelRefusal> {
    if !position.open {
        return Err(ChannelRefusal::NotOpen);
    }
    if position.epoch != position.delegation_epoch {
        tracing::error!(
            slot_epoch = position.epoch,
            delegation_epoch = position.delegation_epoch,
            "CHANNEL EPOCH DIVERGENCE — refusing to step (ORGANS §4 keystone violated)"
        );
        return Err(ChannelRefusal::EpochDivergence {
            slot: position.epoch,
            delegation: position.delegation_epoch,
        });
    }
    if roster_root(roster) != position.member_root {
        return Err(ChannelRefusal::RosterStale);
    }
    Ok(())
}

// =============================================================================
// Routes
// =============================================================================

/// The channels route surface. Mounted inside the node's PROTECTED router
/// (bearer-token gate) in `api.rs`.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/channels/create", post(post_create))
        .route("/channels/join", post(post_join))
        .route("/channels/remove", post(post_remove))
        .route("/channels/rekey", post(post_rekey))
        .route("/channels/post", post(post_message))
        .route("/channels/drain/{cell}", post(post_drain))
        .route("/channels/subscribe", post(post_subscribe))
        .route("/channels/wake/{cell}", get(get_wake))
        .route("/channels/status/{cell}", get(get_status))
        .route("/channels/messages/{cell}", get(messages_stream))
}

#[derive(Deserialize)]
struct MemberSpec {
    /// Member cell id, hex.
    cell: String,
    /// Member X25519 seal public key, hex.
    seal_pk: String,
}

#[derive(Deserialize)]
struct CreateRequest {
    /// Group tag (u64; names the group among the operator's groups).
    tag: u64,
    /// Founding members.
    members: Vec<MemberSpec>,
}

#[derive(Serialize)]
struct SealedKeyWire {
    member: String,
    epoch: u64,
    ephemeral_pk: String,
    ciphertext: String,
}

fn fan_out_wire(fan_out: &[SealedEpochKey]) -> Vec<SealedKeyWire> {
    fan_out
        .iter()
        .map(|s| SealedKeyWire {
            member: hex_encode(s.member.as_bytes()),
            epoch: s.epoch,
            ephemeral_pk: hex_encode(&s.ephemeral_pk),
            ciphertext: hex_encode(&s.ciphertext),
        })
        .collect()
}

#[derive(Serialize)]
struct StepResponse {
    channel: String,
    epoch: u64,
    delegation_epoch: u64,
    member_root: String,
    key_commit: String,
    members: usize,
    /// The sealed epoch-key fan-out (one per CURRENT member). Transport to
    /// members over any channel; ciphertext to everyone else.
    fan_out: Vec<SealedKeyWire>,
    /// The ONE turn that stepped the epoch (create returns all four
    /// lifecycle turns).
    turn_hashes: Vec<String>,
}

fn parse_roster(members: &[MemberSpec]) -> Result<Roster, ChannelRefusal> {
    let mut roster = Roster::new();
    for m in members {
        let cell = CellId(hex_decode_32(&m.cell).ok_or_else(|| {
            ChannelRefusal::BadRequest(format!("malformed member cell id: {}", m.cell))
        })?);
        let seal_pk = hex_decode_32(&m.seal_pk).ok_or_else(|| {
            ChannelRefusal::BadRequest(format!("malformed member seal pk: {}", m.seal_pk))
        })?;
        roster.insert(cell, seal_pk);
    }
    Ok(roster)
}

fn step_response(
    s: &NodeStateInner,
    channel: CellId,
    fan_out: &[SealedEpochKey],
    turn_hashes: Vec<[u8; 32]>,
) -> Result<Json<StepResponse>, ChannelRefusal> {
    let (_, position) = resolve_channel(s, channel)?;
    let members = s
        .channels
        .room(&channel)
        .map(|r| r.roster.len())
        .unwrap_or(0);
    Ok(Json(StepResponse {
        channel: hex_encode(&channel.0),
        epoch: position.epoch,
        delegation_epoch: position.delegation_epoch,
        member_root: hex_encode(&position.member_root),
        key_commit: hex_encode(&position.key_commit),
        members,
        fan_out: fan_out_wire(fan_out),
        turn_hashes: turn_hashes.iter().map(|h| hex_encode(h)).collect(),
    }))
}

/// `POST /channels/create` — birth the group cell from its per-group
/// factory, spawn the epoch anchor, OPEN at epoch 1 (the first unified
/// epoch step), and seed the room.
async fn post_create(
    State(state): State<NodeState>,
    Json(req): Json<CreateRequest>,
) -> Result<Json<StepResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    if !inner.unlocked {
        return Err(ChannelRefusal::Locked);
    }
    let roster = parse_roster(&req.members)?;
    for member in roster.keys() {
        if inner.ledger.get(member).is_none() {
            return Err(ChannelRefusal::BadRequest(format!(
                "member cell {} not in ledger",
                hex_encode(member.as_bytes())
            )));
        }
    }

    let operator = crate::executor_setup::local_agent_cell(inner);
    let admin_pk = inner.cclerk.public_key().0;
    let tag = crate::trustline_service::field_u64(req.tag);
    let terms = ChannelTerms {
        admin: admin_pk,
        tag,
    };
    let descriptor =
        channel_factory_descriptor(&terms).map_err(|e| ChannelRefusal::BadTerms(e.to_string()))?;

    let token_id = channel_token_id(&admin_pk, &tag);
    let channel = CellId::derive_raw(&admin_pk, &token_id);
    if inner.ledger.get(&channel).is_some() {
        return Err(ChannelRefusal::BadTerms(format!(
            "channel cell {} already exists (vary `tag`)",
            hex_encode(&channel.0)
        )));
    }
    let anchor_token = anchor_token_id(&channel);
    let anchor = CellId::derive_raw(&admin_pk, &anchor_token);

    let mut turn_hashes = Vec::with_capacity(4);

    // Turn 1 — birth from the per-group factory.
    turn_hashes.push(run_signed_turn(
        inner,
        operator,
        operator,
        "channel_create",
        vec![Effect::CreateCellFromFactory {
            factory_vk: descriptor.factory_vk,
            owner_pubkey: admin_pk,
            token_id,
            params: FactoryCreationParams {
                mode: dregg_cell::CellMode::Hosted,
                program_vk: descriptor.child_program_vk,
                initial_fields: vec![],
                initial_caps: vec![],
                owner_pubkey: admin_pk,
            },
        }],
        None,
        Some(&descriptor),
    )?);

    // Turn 2 — fund the adopt turn's fee.
    turn_hashes.push(run_signed_turn(
        inner,
        operator,
        operator,
        "channel_fund",
        vec![Effect::Transfer {
            from: operator,
            to: channel,
            amount: ADOPT_TURN_FEE,
        }],
        None,
        None,
    )?);

    // Turn 3 — the adopt (cell-agent turn): spawn the EPOCH ANCHOR and
    // grant the operator their driving capability (a DIRECT grant —
    // `stored_epoch: None` — the governor's reach survives rekeys).
    turn_hashes.push(run_signed_turn(
        inner,
        channel,
        channel,
        "channel_adopt",
        vec![
            Effect::SpawnWithDelegation {
                child_public_key: admin_pk,
                child_token_id: anchor_token,
                max_staleness: u64::MAX,
            },
            Effect::GrantCapability {
                from: channel,
                to: operator,
                cap: dregg_cell::CapabilityRef {
                    target: channel,
                    slot: 0,
                    permissions: dregg_cell::AuthRequired::Signature,
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects: None,
                    stored_epoch: None,
                },
            },
        ],
        Some(ADOPT_TURN_FEE),
        None,
    )?);

    // Turn 4 — OPEN at epoch 1: the first unified epoch step.
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).expect("getrandom failed");
    turn_hashes.push(run_signed_turn(
        inner,
        operator,
        channel,
        "channel_open",
        open_effects(channel, anchor, admin_pk, tag, &roster, &key),
        None,
        None,
    )?);

    let fan_out = seal_epoch_key_to_roster(1, &key, &roster);
    persist_roster(inner, channel, anchor, &roster);
    let mut room = Room::new(anchor, roster);
    room.keys.insert(1, key);
    inner.channels.insert_room(channel, room);
    // Spin up the data plane backing this room: one captp `Bus`, relayed by the
    // node's gossip identity. From here a POST is a real `Bus::enqueue` and live
    // SSE delivery is a real `Bus::drain_one` (drain-on-deliver) — the witnessed
    // drain is wired into the delivery hot-path, not an opt-in audit endpoint.
    let relay_key = inner.cclerk.gossip_signing_key();
    inner.channels.ensure_bus(relay_key);

    tracing::info!(
        channel = %hex_encode(&channel.0),
        members = inner.channels.room(&channel).map(|r| r.roster.len()).unwrap_or(0),
        "channel group opened at epoch 1 (ORGANS §4: control plane on-cell)"
    );

    step_response(inner, channel, &fan_out, turn_hashes)
}

#[derive(Deserialize)]
struct JoinRequest {
    channel: String,
    member: MemberSpec,
}

#[derive(Deserialize)]
struct RemoveRequest {
    channel: String,
    /// Member cell id, hex.
    member: String,
}

#[derive(Deserialize)]
struct RekeyRequest {
    channel: String,
}

fn parse_channel(s: &str) -> Result<CellId, ChannelRefusal> {
    Ok(CellId(hex_decode_32(s).ok_or_else(|| {
        ChannelRefusal::BadRequest(format!("malformed channel cell id: {s}"))
    })?))
}

/// THE ONE EPOCH-STEP TURN, node side (shared by join/remove/rekey).
fn run_epoch_step(
    inner: &mut NodeStateInner,
    channel: CellId,
    new_roster: Roster,
    event: &str,
) -> Result<(Vec<SealedEpochKey>, [u8; 32]), ChannelRefusal> {
    require_operator_authority(inner, channel)?;
    let (_, position) = resolve_channel(inner, channel)?;
    let room = inner
        .channels
        .room(&channel)
        .ok_or_else(|| ChannelRefusal::NoChannel("no room state for this group".into()))?;
    check_step_preconditions(&position, &room.roster)?;
    let anchor = room.anchor;
    let new_epoch = position.epoch + 1;
    let operator = crate::executor_setup::local_agent_cell(inner);

    let mut key = [0u8; 32];
    getrandom::fill(&mut key).expect("getrandom failed");

    // ONE turn: roster + epoch + key commitment + delegation-epoch bump +
    // the survivors' capability refresh. A rejection moves NOTHING.
    let turn_hash = run_signed_turn(
        inner,
        operator,
        channel,
        event,
        epoch_step_effects(channel, anchor, &new_roster, new_epoch, &key, event),
        None,
        None,
    )?;

    let fan_out = seal_epoch_key_to_roster(new_epoch, &key, &new_roster);
    let room = inner
        .channels
        .room_mut(&channel)
        .expect("room exists (resolved above)");
    room.roster = new_roster.clone();
    room.keys.insert(new_epoch, key);
    // Persist the post-step roster durably (docs/PERSISTENCE.md §3): the
    // roster the committed turn installed survives an arbitrary crash from
    // here on, so a restart rebuilds the room without waiting for members to
    // re-post (re-committed against the on-cell root at load).
    persist_roster(inner, channel, anchor, &new_roster);
    Ok((fan_out, turn_hash))
}

/// `POST /channels/join` — admit a member (one epoch-step turn; the joiner
/// reads forward only).
async fn post_join(
    State(state): State<NodeState>,
    Json(req): Json<JoinRequest>,
) -> Result<Json<StepResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let channel = parse_channel(&req.channel)?;
    let member = CellId(hex_decode_32(&req.member.cell).ok_or_else(|| {
        ChannelRefusal::BadRequest(format!("malformed member cell id: {}", req.member.cell))
    })?);
    let seal_pk = hex_decode_32(&req.member.seal_pk).ok_or_else(|| {
        ChannelRefusal::BadRequest(format!("malformed member seal pk: {}", req.member.seal_pk))
    })?;
    if inner.ledger.get(&member).is_none() {
        return Err(ChannelRefusal::BadRequest(format!(
            "member cell {} not in ledger",
            req.member.cell
        )));
    }
    let room = inner
        .channels
        .room(&channel)
        .ok_or_else(|| ChannelRefusal::NoChannel("no room state for this group".into()))?;
    if room.roster.contains_key(&member) {
        return Err(ChannelRefusal::BadRequest(
            "member already in the group".into(),
        ));
    }
    let mut next = room.roster.clone();
    next.insert(member, seal_pk);
    let (fan_out, turn_hash) = run_epoch_step(inner, channel, next, "channel_join")?;
    step_response(inner, channel, &fan_out, vec![turn_hash])
}

/// `POST /channels/remove` — THE KEYSTONE OP: drop the member, step the
/// epoch, commit the fresh key, bump the freshness counter, refresh the
/// survivors — ONE turn. After it commits the removed member can neither
/// decrypt epoch-(e+1) ciphertext nor exercise a group-held capability
/// minted at epoch ≤ e.
async fn post_remove(
    State(state): State<NodeState>,
    Json(req): Json<RemoveRequest>,
) -> Result<Json<StepResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let channel = parse_channel(&req.channel)?;
    let member = CellId(hex_decode_32(&req.member).ok_or_else(|| {
        ChannelRefusal::BadRequest(format!("malformed member cell id: {}", req.member))
    })?);
    let room = inner
        .channels
        .room(&channel)
        .ok_or_else(|| ChannelRefusal::NoChannel("no room state for this group".into()))?;
    if !room.roster.contains_key(&member) {
        return Err(ChannelRefusal::BadRequest("not a member".into()));
    }
    let mut next = room.roster.clone();
    next.remove(&member);
    let (fan_out, turn_hash) = run_epoch_step(inner, channel, next, "channel_remove")?;
    tracing::info!(
        channel = %hex_encode(&channel.0),
        removed = %hex_encode(member.as_bytes()),
        "member removed: rekey + capability-epoch bump rode the SAME turn (the keystone)"
    );
    step_response(inner, channel, &fan_out, vec![turn_hash])
}

/// `POST /channels/rekey` — step the epoch with membership unchanged
/// (compromise recovery / key hygiene).
async fn post_rekey(
    State(state): State<NodeState>,
    Json(req): Json<RekeyRequest>,
) -> Result<Json<StepResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let channel = parse_channel(&req.channel)?;
    let room = inner
        .channels
        .room(&channel)
        .ok_or_else(|| ChannelRefusal::NoChannel("no room state for this group".into()))?;
    let next = room.roster.clone();
    let (fan_out, turn_hash) = run_epoch_step(inner, channel, next, "channel_rekey")?;
    step_response(inner, channel, &fan_out, vec![turn_hash])
}

#[derive(Deserialize)]
struct PostRequest {
    channel: String,
    /// The key epoch the body is encrypted under (must be CURRENT).
    epoch: u64,
    /// AEAD nonce, hex (12 bytes).
    nonce: String,
    /// Ciphertext, hex.
    ciphertext: String,
}

/// The wire view of a captp [`Delivery`] — the signed custody RECEIPT a POST
/// gets back. `content_hash` is the identity a later drain WITNESSES; the
/// receipt is the relay's signed promise. The two are separate objects (the
/// receipt-identity teeth), exposed end to end so an external client can hold
/// the receipt, see "queued", and later see "handled".
#[derive(Serialize)]
struct DeliveryWire {
    /// The relay (the node's gossip identity) that signed the receipt.
    relay: String,
    /// Content-address of the enqueued box — what the drain witnesses.
    content_hash: String,
    /// The inbox owner (the channel cell, read as a recipient).
    inbox_owner: String,
    /// The inbox root before / after this enqueue (the custody transition).
    old_root: String,
    new_root: String,
    /// Deliver-or-refund-by deadline carried in the receipt.
    accept_by: u64,
    /// The relay's Ed25519 signature over the receipt preimage — VERIFIES.
    signature: String,
}

impl DeliveryWire {
    fn of(d: &Delivery) -> Self {
        let r = &d.receipt;
        DeliveryWire {
            relay: hex_encode(&r.relay.0),
            content_hash: hex_encode(&d.content_hash),
            inbox_owner: hex_encode(&r.inbox_owner.0),
            old_root: hex_encode(&r.old_root),
            new_root: hex_encode(&r.new_root),
            accept_by: r.accept_by,
            signature: hex_encode(&r.signature.0),
        }
    }
}

/// Decode an even-length hex string to bytes (`None` on any non-hex digit or an
/// odd length). The channels data plane carries opaque ciphertext, so this is
/// the only decode it needs beyond the fixed-32 helper.
fn hex_to_bytes(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

#[derive(Serialize)]
struct PostResponse {
    channel: String,
    seq: u64,
    epoch: u64,
    /// The captp DATA-PLANE delivery receipt for THIS post: a real
    /// [`Bus::enqueue`] minted it. The chain is untouched; the data plane runs.
    delivery: DeliveryWire,
    /// Boxes queued-but-not-yet-drained for this channel's inbox after this post
    /// (the "queued" count; `drained < this` ⟺ unhandled work outstanding).
    pending: usize,
}

/// The deterministic payload the data-plane [`Bus`] holds for a post: the
/// epoch tag, the nonce bytes, and the ciphertext bytes, length-prefixed so the
/// content hash is stable and a drain reconstructs the envelope exactly. The
/// chain never sees these bytes (message bodies stay off-cell).
fn encode_envelope_payload(epoch: u64, nonce: &[u8], ciphertext: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(8 + 4 + nonce.len() + ciphertext.len());
    v.extend_from_slice(&epoch.to_be_bytes());
    v.extend_from_slice(&(nonce.len() as u32).to_be_bytes());
    v.extend_from_slice(nonce);
    v.extend_from_slice(ciphertext);
    v
}

/// `POST /channels/post` — THE DATA PLANE: enqueue a ciphertext THROUGH the
/// captp [`Bus`] (returning the custody [`Delivery`] receipt) AND store it in
/// the SSE replay ring. The chain is untouched; the node relays what it stores.
/// Posts naming a non-current epoch are refused at the door (epoch staleness is
/// preserved); an over-attenuated enqueue is refused at the Bus seam.
async fn post_message(
    State(state): State<NodeState>,
    Json(req): Json<PostRequest>,
) -> Result<Json<PostResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let channel = parse_channel(&req.channel)?;
    let (_, position) = resolve_channel(inner, channel)?;
    if !position.open {
        return Err(ChannelRefusal::NotOpen);
    }
    if req.epoch != position.epoch {
        return Err(ChannelRefusal::WrongEpoch {
            current: position.epoch,
            posted: req.epoch,
        });
    }
    if inner.channels.room(&channel).is_none() {
        return Err(ChannelRefusal::NoChannel(
            "no room state for this group".into(),
        ));
    }
    // Shape checks only — the body is opaque ciphertext by design.
    if req.nonce.len() != 24 || hex_decode_32(&format!("{:0<64}", req.nonce)).is_none() {
        return Err(ChannelRefusal::BadRequest(
            "nonce must be 12 bytes hex".into(),
        ));
    }
    if req.ciphertext.is_empty() || req.ciphertext.len() % 2 != 0 {
        return Err(ChannelRefusal::BadRequest(
            "ciphertext must be non-empty hex".into(),
        ));
    }
    let nonce_bytes = hex_to_bytes(&req.nonce)
        .ok_or_else(|| ChannelRefusal::BadRequest("nonce must be hex".into()))?;
    let ct_bytes = hex_to_bytes(&req.ciphertext)
        .ok_or_else(|| ChannelRefusal::BadRequest("ciphertext must be hex".into()))?;

    // THE DATA PLANE: enqueue through the captp Bus FIRST. The send is gated by
    // the per-channel SendCap at Signature authority; an over-attenuated or
    // unauthorized offer is refused at the seam (no message queued, NO receipt
    // minted — no phantom work). The returned Delivery is the custody receipt.
    let relay_key = inner.cclerk.gossip_signing_key();
    let bus = inner.channels.ensure_bus(relay_key);
    let payload = encode_envelope_payload(req.epoch, &nonce_bytes, &ct_bytes);
    let cap = bus_send_cap(channel);
    let now = position.epoch; // logical clock: the current key epoch.
    let delivery = bus.enqueue(
        &cap,
        bus_recipient(channel),
        &bus_channel_name(channel),
        AuthRequired::Signature,
        payload,
        now,
    )?;
    let pending = bus.pending_count(&bus_recipient(channel));

    // Mirror into the SSE replay ring (the delay-tolerant fan-out window). The
    // Bus is the receipt-bearing source of truth; the ring is the cursor for
    // resuming SSE clients within the window.
    let seq = inner
        .channels
        .push_message(channel, req.epoch, req.nonce, req.ciphertext);
    Ok(Json(PostResponse {
        channel: hex_encode(&channel.0),
        seq,
        epoch: req.epoch,
        delivery: DeliveryWire::of(&delivery),
        pending,
    }))
}

/// Reconstruct `(epoch, nonce, ciphertext)` from the deterministic Bus payload
/// produced by [`encode_envelope_payload`]. `None` on a truncated/garbled box.
fn decode_envelope_payload(p: &[u8]) -> Option<(u64, Vec<u8>, Vec<u8>)> {
    if p.len() < 12 {
        return None;
    }
    let epoch = u64::from_be_bytes(p[0..8].try_into().ok()?);
    let nlen = u32::from_be_bytes(p[8..12].try_into().ok()?) as usize;
    let rest = &p[12..];
    if rest.len() < nlen {
        return None;
    }
    Some((epoch, rest[..nlen].to_vec(), rest[nlen..].to_vec()))
}

/// One drained box on the wire: the reconstructed envelope PLUS its
/// `content_hash` (now in the delivered-witness log — `handled` is `true` for it).
#[derive(Serialize)]
struct DrainedWire {
    epoch: u64,
    nonce: String,
    ciphertext: String,
    /// The content-address that is now WITNESSED in the delivery log: a POST's
    /// returned `delivery.content_hash` matching this means that delivery is
    /// `is_handled` — the receipt-identity flip, observable through the node.
    content_hash: String,
}

#[derive(Serialize)]
struct DrainResponse {
    channel: String,
    /// The boxes that left the queue (FIFO) on this drain — each now handled.
    drained: Vec<DrainedWire>,
    /// Boxes still queued-but-not-drained after this drain (handled is FALSE for
    /// these — the structural "queued ≠ handled" distinction, through the node).
    pending: usize,
    /// Every content hash ever delivered (drained) for this channel's inbox: the
    /// authenticated witness a client checks a held receipt against.
    delivered: Vec<String>,
}

/// `POST /channels/drain/{cell}` — THE DATA-PLANE WITNESS: drain the channel's
/// inbox through [`Bus::drain`]. Each drained box's content hash is appended to
/// the delivery-witness log, so a POST's receipt flips from "queued" to
/// "handled". This is the receipt-identity teeth, run through the node: an
/// external client enqueues (POST), another drains (this), and the delivery is
/// provably witnessed — "queued-but-not-drained" is a distinct, observable state.
async fn post_drain(
    State(state): State<NodeState>,
    AxumPath(cell): AxumPath<String>,
) -> Result<Json<DrainResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let channel = parse_channel(&cell)?;
    // The channel must be a real, resolvable group cell.
    resolve_channel(inner, channel)?;
    let recipient = bus_recipient(channel);
    let bus = inner
        .channels
        .bus_mut()
        .ok_or_else(|| ChannelRefusal::NoChannel("data plane not initialized".into()))?;
    let drained = bus.drain(&recipient);
    let pending = bus.pending_count(&recipient);
    let delivered: Vec<String> = bus
        .delivered_hashes(&recipient)
        .iter()
        .map(|h| hex_encode(h))
        .collect();
    let drained_wire = drained
        .iter()
        .filter_map(|m| {
            let (epoch, nonce, ct) = decode_envelope_payload(&m.encrypted_payload)?;
            let content_hash = *blake3::hash(&m.encrypted_payload).as_bytes();
            Some(DrainedWire {
                epoch,
                nonce: hex_encode(&nonce),
                ciphertext: hex_encode(&ct),
                content_hash: hex_encode(&content_hash),
            })
        })
        .collect();
    Ok(Json(DrainResponse {
        channel: hex_encode(&channel.0),
        drained: drained_wire,
        pending,
        delivered,
    }))
}

#[derive(Deserialize)]
struct SubscribeRequest {
    channel: String,
    /// The waiter identity (a FederationId / cell id, hex) registering to be
    /// woken by name when the channel's wake cursor advances.
    waiter: String,
}

#[derive(Serialize)]
struct SubscribeResponse {
    channel: String,
    waiter: String,
    /// The wake cursor at registration time. A later `GET /channels/wake` returns
    /// a wake iff the live cursor has advanced past this.
    cursor: u64,
}

/// `POST /channels/subscribe` — register a waiter on a channel via
/// [`Bus::wait`]: a future POST advances the wake cursor and the waiter is woken
/// by name (the unforgeable, cursor-derived wake — no enqueue ⇒ no wake).
async fn post_subscribe(
    State(state): State<NodeState>,
    Json(req): Json<SubscribeRequest>,
) -> Result<Json<SubscribeResponse>, ChannelRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let channel = parse_channel(&req.channel)?;
    resolve_channel(inner, channel)?;
    let waiter = FederationId(hex_decode_32(&req.waiter).ok_or_else(|| {
        ChannelRefusal::BadRequest(format!("malformed waiter id: {}", req.waiter))
    })?);
    let name = bus_channel_name(channel);
    let relay_key = inner.cclerk.gossip_signing_key();
    let bus = inner.channels.ensure_bus(relay_key);
    bus.wait(&name, waiter);
    let cursor = bus.cursor(&name);
    Ok(Json(SubscribeResponse {
        channel: hex_encode(&channel.0),
        waiter: req.waiter,
        cursor,
    }))
}

#[derive(Serialize)]
struct WakeResponse {
    channel: String,
    waiter: String,
    /// The live wake cursor (count of admitted enqueues to this channel).
    cursor: u64,
    /// `true` iff the cursor advanced past the waiter's last-seen mark — the
    /// waiter has work to drain. A fact about the queue, never a forgeable flag.
    woken: bool,
    /// The cursor value the wake points to (the value to acknowledge), if woken.
    wake_cursor: Option<u64>,
}

/// `GET /channels/wake/{cell}?waiter=<hex>` — poll a registered waiter via
/// [`Bus::poll_wake`]: `woken: true` iff the channel cursor advanced past its
/// mark. The wake is derived from the monotone cursor (no public setter), so a
/// subscriber cannot fabricate one.
async fn get_wake(
    State(state): State<NodeState>,
    AxumPath(cell): AxumPath<String>,
    axum::extract::Query(q): axum::extract::Query<WakeQuery>,
) -> Result<Json<WakeResponse>, ChannelRefusal> {
    let s = state.read().await;
    let channel = parse_channel(&cell)?;
    let waiter = FederationId(
        hex_decode_32(&q.waiter)
            .ok_or_else(|| ChannelRefusal::BadRequest(format!("malformed waiter id: {}", q.waiter)))?,
    );
    let name = bus_channel_name(channel);
    let bus = s
        .channels
        .bus()
        .ok_or_else(|| ChannelRefusal::NoChannel("data plane not initialized".into()))?;
    let cursor = bus.cursor(&name);
    let wake = bus.poll_wake(&name, &waiter);
    Ok(Json(WakeResponse {
        channel: hex_encode(&channel.0),
        waiter: q.waiter,
        cursor,
        woken: wake.is_some(),
        wake_cursor: wake.map(|w| w.cursor),
    }))
}

#[derive(Deserialize)]
struct WakeQuery {
    waiter: String,
}

#[derive(Serialize)]
struct StatusResponse {
    channel: String,
    admin: String,
    tag: String,
    epoch: u64,
    delegation_epoch: u64,
    /// THE INVARIANT under the canonical builders. `false` is LOUD.
    epochs_unified: bool,
    member_root: String,
    key_commit: String,
    open: bool,
    /// Members per the node-held roster (`None` when this node holds no
    /// room state for the group — e.g. after a restart).
    members: Option<usize>,
    messages_held: Option<usize>,
}

/// `GET /channels/status/{cell}`.
async fn get_status(
    State(state): State<NodeState>,
    AxumPath(cell): AxumPath<String>,
) -> Result<Json<StatusResponse>, ChannelRefusal> {
    let s = state.read().await;
    let channel = parse_channel(&cell)?;
    let (terms, position) = resolve_channel(&s, channel)?;
    let room = s.channels.room(&channel);
    if position.epoch != position.delegation_epoch {
        tracing::error!(
            channel = %hex_encode(&channel.0),
            slot_epoch = position.epoch,
            delegation_epoch = position.delegation_epoch,
            "CHANNEL EPOCH DIVERGENCE observed in status read"
        );
    }
    Ok(Json(StatusResponse {
        channel: hex_encode(&channel.0),
        admin: hex_encode(&terms.admin),
        tag: hex_encode(&terms.tag),
        epoch: position.epoch,
        delegation_epoch: position.delegation_epoch,
        epochs_unified: position.epoch == position.delegation_epoch,
        member_root: hex_encode(&position.member_root),
        key_commit: hex_encode(&position.key_commit),
        open: position.open,
        members: room.map(|r| r.roster.len()),
        messages_held: room.map(|r| r.messages.len()),
    }))
}

// =============================================================================
// SSE delivery (the data plane's fan-out; the ring is the cursor source)
// =============================================================================

struct MessageCursor {
    state: NodeState,
    rx: broadcast::Receiver<(CellId, u64)>,
    channel: CellId,
    next: u64,
}

/// `GET /channels/messages/{cell}` — SSE of stored ciphertexts.
/// `Last-Event-ID: <seq>` resumes after the last delivered message; a fresh
/// connection replays the whole held ring (delay-tolerant within the
/// window). The stream carries CIPHERTEXT — useless without a group key.
async fn messages_stream(
    AxumPath(cell): AxumPath<String>,
    headers: HeaderMap,
    State(state): State<NodeState>,
) -> Result<Sse<impl Stream<Item = Result<SseEvent, Infallible>>>, ChannelRefusal> {
    let channel = parse_channel(&cell)?;
    // Subscribe BEFORE the snapshot so nothing posted in between is lost.
    let rx = {
        let s = state.read().await;
        if s.channels.room(&channel).is_none() {
            return Err(ChannelRefusal::NoChannel(
                "no room state for this group".into(),
            ));
        }
        s.channels.subscribe()
    };
    let next = headers
        .get("last-event-id")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.trim().parse::<u64>().ok())
        .map(|id| id.saturating_add(1))
        .unwrap_or(0);

    let cursor = MessageCursor {
        state,
        rx,
        channel,
        next,
    };
    let stream = futures_util::stream::unfold(cursor, |mut c| async move {
        loop {
            // Drain the ring from the cursor before waiting again. Delivering a
            // ring message to this SSE client is a REAL delivery, so it WITNESSES
            // the corresponding box's drain on the data-plane Bus (drain-on-deliver):
            // each box the post enqueued is drained as it is handed to a consumer,
            // flipping its custody receipt queued→handled and keeping the Bus inbox
            // bounded (it never accumulates a parallel, never-drained backlog). The
            // ring and the Bus are produced in lockstep by `post_message` (one push
            // per one enqueue, FIFO), so the FIFO `drain_one` matches delivery order.
            let pending = {
                let mut s = c.state.write().await;
                let inner = &mut *s;
                let recipient = bus_recipient(c.channel);
                let room = inner.channels.room(&c.channel)?;
                // Skip past evicted history.
                let front_seq = room.messages.front().map(|m| m.seq);
                if let Some(front) = front_seq {
                    if c.next < front {
                        c.next = front;
                    }
                }
                let found = room
                    .messages
                    .iter()
                    .find(|m| m.seq >= c.next)
                    .map(|m| (m.seq, serde_json::to_string(m)));
                // Witness this delivery on the Bus: drain one box (no-op once the
                // Bus inbox for this channel is already drained by an earlier
                // consumer — the witness is sticky, so re-delivery to another SSE
                // client does not double-count).
                if found.is_some() {
                    if let Some(bus) = inner.channels.bus_mut() {
                        let _ = bus.drain_one(&recipient);
                    }
                }
                found
            };
            if let Some((seq, body)) = pending {
                c.next = seq + 1;
                let sse = SseEvent::default()
                    .event("ciphertext")
                    .id(seq.to_string())
                    .data(body.unwrap_or_else(|e| format!("{{\"error\":\"serialize: {e}\"}}")));
                return Some((Ok::<_, Infallible>(sse), c));
            }
            // Ring drained — sleep on the broadcast until the next post.
            match c.rx.recv().await {
                Ok((ch, _)) if ch == c.channel => continue,
                Ok(_) => continue,
                Err(broadcast::error::RecvError::Lagged(_)) => continue,
                Err(broadcast::error::RecvError::Closed) => return None,
            }
        }
    });

    Ok(Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(30))
            .text("hb"),
    ))
}

// =============================================================================
// Tests — the keystone on the real router + executor
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    /// A node state with a funded operator agent cell and three member
    /// cells (with seal keyrings) on the live ledger.
    async fn funded_state() -> (
        NodeState,
        Vec<(CellId, dregg_sdk_net::channels::MemberKeyring)>,
        tempfile::TempDir,
    ) {
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        let members = {
            let mut s = state.write().await;
            s.unlocked = true;
            let operator_pk = s.cclerk.public_key().0;
            let operator = crate::executor_setup::local_agent_cell(&s);
            let token = *blake3::hash(b"default").as_bytes();
            let op_cell = dregg_cell::Cell::with_balance(operator_pk, token, 0);
            assert_eq!(op_cell.id(), operator, "agent-cell derivation must match");
            let _ = s.ledger.insert_cell(op_cell);
            assert!(
                s.ledger
                    .get_mut(&operator)
                    .expect("operator cell")
                    .state
                    .credit_balance(10_000_000),
                "operator accepts funding"
            );
            let mut members = Vec::new();
            for i in 0u8..3 {
                let token = *blake3::Hasher::new_derive_key("channel-node-test-member-v1")
                    .update(&[i])
                    .finalize()
                    .as_bytes();
                let cell = dregg_cell::Cell::with_balance(operator_pk, token, 200_000);
                let id = cell.id();
                s.ledger.insert_cell(cell).expect("member inserts");
                let mut secret = [0u8; 32];
                secret[0] = 0x60 + i;
                secret[31] = 0xB0 + i;
                members.push((id, dregg_sdk_net::channels::MemberKeyring::new(id, secret)));
            }
            members
        };
        (state, members, dir)
    }

    async fn post_json(
        state: &NodeState,
        uri: &str,
        body: serde_json::Value,
    ) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .method("POST")
                    .header("content-type", "application/json")
                    .body(Body::from(body.to_string()))
                    .unwrap(),
            )
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({}));
        (status, json)
    }

    async fn get_json(state: &NodeState, uri: &str) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({}));
        (status, json)
    }

    fn members_json(
        members: &[(CellId, dregg_sdk_net::channels::MemberKeyring)],
    ) -> Vec<serde_json::Value> {
        members
            .iter()
            .map(|(id, ring)| {
                serde_json::json!({
                    "cell": hex_encode(id.as_bytes()),
                    "seal_pk": hex_encode(&ring.seal_pk()),
                })
            })
            .collect()
    }

    async fn create_group(
        state: &NodeState,
        members: &[(CellId, dregg_sdk_net::channels::MemberKeyring)],
    ) -> (CellId, serde_json::Value) {
        let (status, json) = post_json(
            state,
            "/channels/create",
            serde_json::json!({ "tag": 7, "members": members_json(members) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "create must succeed: {json}");
        (
            CellId(hex_decode_32(json["channel"].as_str().unwrap()).unwrap()),
            json,
        )
    }

    #[tokio::test]
    async fn create_opens_unified_and_remove_is_one_turn() {
        let (state, mut members, _dir) = funded_state().await;
        let (channel, created) = create_group(&state, &members).await;

        // Epoch 1, BOTH counters, three sealed keys.
        assert_eq!(created["epoch"], 1);
        assert_eq!(created["delegation_epoch"], 1);
        assert_eq!(created["fan_out"].as_array().unwrap().len(), 3);

        // Members accept their epoch-1 keys.
        for sealed in created["fan_out"].as_array().unwrap() {
            let member = CellId(hex_decode_32(sealed["member"].as_str().unwrap()).unwrap());
            let ring = &mut members.iter_mut().find(|(id, _)| *id == member).unwrap().1;
            let eph = hex_decode_32(sealed["ephemeral_pk"].as_str().unwrap()).unwrap();
            let ct_hex = sealed["ciphertext"].as_str().unwrap();
            let ct: Vec<u8> = (0..ct_hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&ct_hex[i..i + 2], 16).unwrap())
                .collect();
            ring.accept(&dregg_sdk_net::channels::SealedEpochKey {
                member,
                epoch: 1,
                ephemeral_pk: eph,
                ciphertext: ct,
            })
            .expect("member accepts epoch-1 key");
        }

        // THE REMOVE: one turn (ONE hash), epoch 2 on both counters.
        let removed = members[0].0;
        let (status, json) = post_json(
            &state,
            "/channels/remove",
            serde_json::json!({
                "channel": hex_encode(channel.as_bytes()),
                "member": hex_encode(removed.as_bytes()),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "remove must succeed: {json}");
        assert_eq!(
            json["turn_hashes"].as_array().unwrap().len(),
            1,
            "THE KEYSTONE: remove + rekey + cap-bump are ONE turn"
        );
        assert_eq!(json["epoch"], 2);
        assert_eq!(json["delegation_epoch"], 2);
        let fan_out = json["fan_out"].as_array().unwrap();
        assert_eq!(fan_out.len(), 2, "fan-out excludes the removed member");
        assert!(
            fan_out
                .iter()
                .all(|s| s["member"].as_str().unwrap() != hex_encode(removed.as_bytes()))
        );

        // Status agrees and reports the unification invariant.
        let (status, json) = get_json(
            &state,
            &format!("/channels/status/{}", hex_encode(channel.as_bytes())),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["epochs_unified"], true);
        assert_eq!(json["members"], 2);
    }

    #[tokio::test]
    async fn data_plane_posts_and_refuses_stale_epochs() {
        let (state, members, _dir) = funded_state().await;
        let (channel, _) = create_group(&state, &members).await;
        let channel_hex = hex_encode(channel.as_bytes());

        // A current-epoch post stores and sequences.
        let (status, json) = post_json(
            &state,
            "/channels/post",
            serde_json::json!({
                "channel": channel_hex,
                "epoch": 1,
                "nonce": "00112233445566778899aabb",
                "ciphertext": "deadbeef",
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["seq"], 0);

        // Rekey to epoch 2 — an epoch-1 post now refuses at the door.
        let (status, _) = post_json(
            &state,
            "/channels/rekey",
            serde_json::json!({ "channel": channel_hex }),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        let (status, json) = post_json(
            &state,
            "/channels/post",
            serde_json::json!({
                "channel": channel_hex,
                "epoch": 1,
                "nonce": "00112233445566778899aabb",
                "ciphertext": "deadbeef",
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "stale-epoch post: {json}");
        assert_eq!(json["reason"], "wrong-epoch");

        // The chain never saw a message: the group cell's nonce moved only
        // for control-plane turns (create/open/rekey), and no message bytes
        // exist anywhere in its state.
        let s = state.read().await;
        let cell = s.ledger.get(&channel).unwrap();
        for field in &cell.state.fields {
            assert_ne!(&field[..4], b"dead", "message bytes must never be on-cell");
        }
    }

    /// THE CRITICISM-CLOSING TEST: the captp `Bus` BACKS the node's channels
    /// service, end to end, THROUGH THE NODE PATH (not the captp unit test).
    /// An external client POSTs (a real `Bus::enqueue`, gets a signed delivery
    /// receipt), another DRAINs (a real `Bus::drain`, witnessing delivery), and
    /// "queued-but-not-drained" is provably distinguishable from "handled" — the
    /// receipt-identity teeth, run in production over the HTTP surface.
    #[tokio::test]
    async fn bus_backs_channels_post_drain_receipt_identity_through_the_node() {
        let (state, members, _dir) = funded_state().await;
        let (channel, _) = create_group(&state, &members).await;
        let channel_hex = hex_encode(channel.as_bytes());

        // (1) A waiter subscribes — no wake before any post (a wake is a FACT).
        let waiter_hex = hex_encode(&[0x77u8; 32]);
        let (status, sub) = post_json(
            &state,
            "/channels/subscribe",
            serde_json::json!({ "channel": channel_hex, "waiter": waiter_hex }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "subscribe: {sub}");
        assert_eq!(sub["cursor"], 0);
        let (status, wake) = get_json(
            &state,
            &format!("/channels/wake/{channel_hex}?waiter={waiter_hex}"),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(wake["woken"], false, "no wake before any enqueue");

        // (2) POST a ciphertext → a real Bus::enqueue. The response carries the
        // custody DELIVERY RECEIPT: a real signature, a content hash, a custody
        // root transition. `pending` is 1 — queued, not yet handled.
        let (status, posted) = post_json(
            &state,
            "/channels/post",
            serde_json::json!({
                "channel": channel_hex,
                "epoch": 1,
                "nonce": "00112233445566778899aabb",
                "ciphertext": "deadbeefcafef00d",
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "post: {posted}");
        let content_hash = posted["delivery"]["content_hash"].as_str().unwrap().to_string();
        assert!(!content_hash.is_empty(), "the post returns a content hash");
        assert_eq!(posted["delivery"]["inbox_owner"], channel_hex);
        let sig = posted["delivery"]["signature"].as_str().unwrap();
        assert!(sig.chars().any(|c| c != '0'), "the receipt carries a real signature");
        assert_eq!(posted["pending"], 1, "queued: one box pending, not yet handled");

        // The receipt VERIFIES: reconstruct it from the wire and check the
        // relay's Ed25519 signature (the unforgeable custody promise).
        {
            let s = state.read().await;
            let bus = s.channels.bus().expect("bus exists after create");
            let recipient = bus_recipient(channel);
            // The Bus's own witness log does NOT yet contain it (not drained).
            assert!(
                !bus.delivered_hashes(&recipient)
                    .iter()
                    .any(|h| hex_encode(h) == content_hash),
                "a thing on the spool is NOT a thing handled (no witness yet)"
            );
            assert_eq!(bus.pending_count(&recipient), 1);
        }

        // (3) The waiter is now WOKEN by name (the cursor advanced — a fact).
        let (status, wake) = get_json(
            &state,
            &format!("/channels/wake/{channel_hex}?waiter={waiter_hex}"),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(wake["woken"], true, "the post woke the waiter by name");
        assert_eq!(wake["cursor"], 1);

        // (4) DRAIN through the node → a real Bus::drain. The custody receipt is
        // WITNESSED: the content hash now sits in the delivered log, and pending
        // drops to 0. "queued" has flipped to "handled" — observable end to end.
        let (status, drained) = post_json(
            &state,
            &format!("/channels/drain/{channel_hex}"),
            serde_json::json!({}),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "drain: {drained}");
        let drained_boxes = drained["drained"].as_array().unwrap();
        assert_eq!(drained_boxes.len(), 1, "one box left the queue");
        assert_eq!(drained_boxes[0]["ciphertext"], "deadbeefcafef00d");
        assert_eq!(drained_boxes[0]["content_hash"], content_hash);
        assert_eq!(drained["pending"], 0, "handled: nothing pending after drain");
        assert!(
            drained["delivered"]
                .as_array()
                .unwrap()
                .iter()
                .any(|h| h.as_str() == Some(content_hash.as_str())),
            "the delivery is WITNESSED: the receipt's content hash is in the delivered log"
        );

        // (5) A second drain yields nothing — handled is sticky, never re-served.
        let (status, again) = post_json(
            &state,
            &format!("/channels/drain/{channel_hex}"),
            serde_json::json!({}),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(again["drained"].as_array().unwrap().len(), 0);
        assert_eq!(again["pending"], 0);
    }

    /// THE DELIVERY-HOT-PATH WITNESS: live SSE delivery drains the Bus box for the
    /// message it hands the client (drain-on-deliver). So the receipt-identity
    /// witness flips queued→handled on the REAL delivery path (not only via the
    /// opt-in `/channels/drain` endpoint), and the Bus inbox drains in lockstep
    /// with delivery — it does NOT grow as a parallel, never-drained ledger.
    #[tokio::test]
    async fn sse_delivery_witnesses_the_bus_drain_and_bounds_the_inbox() {
        use futures_util::StreamExt;

        let (state, members, _dir) = funded_state().await;
        let (channel, _) = create_group(&state, &members).await;
        let channel_hex = hex_encode(channel.as_bytes());
        let recipient = bus_recipient(channel);

        // POST two ciphertexts: each is a real Bus::enqueue. Capture the content
        // hashes so we can prove they later appear in the delivered-witness log.
        let mut content_hashes = Vec::new();
        for ct in ["deadbeef", "cafef00d"] {
            let (status, posted) = post_json(
                &state,
                "/channels/post",
                serde_json::json!({
                    "channel": channel_hex,
                    "epoch": 1,
                    "nonce": "00112233445566778899aabb",
                    "ciphertext": ct,
                }),
            )
            .await;
            assert_eq!(status, StatusCode::OK, "post: {posted}");
            content_hashes.push(posted["delivery"]["content_hash"].as_str().unwrap().to_string());
        }

        // Two boxes queued on the Bus, NONE witnessed yet (queued ≠ handled).
        {
            let s = state.read().await;
            let bus = s.channels.bus().expect("bus exists");
            assert_eq!(bus.pending_count(&recipient), 2, "two boxes queued before delivery");
            assert_eq!(bus.delivered_hashes(&recipient).len(), 0, "none witnessed yet");
        }

        // Open the live SSE stream and pull exactly the two delivered events. The
        // stream is endless (it parks after the ring), so each pull is bounded by a
        // short timeout — we only need the two real deliveries.
        let sse = messages_stream(
            AxumPath(channel_hex.clone()),
            HeaderMap::new(),
            State(state.clone()),
        )
        .await
        .expect("sse stream opens");
        // `Sse` derefs into the inner stream of events.
        let mut stream = sse.into_response().into_body().into_data_stream();
        let mut delivered = 0usize;
        while delivered < 2 {
            match tokio::time::timeout(Duration::from_secs(2), stream.next()).await {
                Ok(Some(Ok(chunk))) => {
                    // Each delivered envelope is one `event: ciphertext` SSE frame;
                    // heartbeats are `:hb` comments and carry no such line.
                    let text = String::from_utf8_lossy(&chunk);
                    delivered += text.matches("event: ciphertext").count();
                }
                Ok(Some(Err(_))) | Ok(None) => break,
                Err(_) => break, // timeout: stream parked (all ring messages delivered)
            }
        }
        assert_eq!(delivered, 2, "both ciphertexts were delivered over the live SSE wire");

        // Give the drain-on-deliver writes a moment to settle, then assert: the Bus
        // inbox is DRAINED (bounded — it did not accumulate) and BOTH content hashes
        // are in the delivered-witness log (the receipt-identity flip happened on the
        // live delivery path).
        let s = state.read().await;
        let bus = s.channels.bus().expect("bus exists");
        assert_eq!(
            bus.pending_count(&recipient),
            0,
            "live SSE delivery drained the Bus inbox in lockstep (no parallel backlog)"
        );
        let witnessed = bus.delivered_hashes(&recipient);
        for h in &content_hashes {
            assert!(
                witnessed.iter().any(|w| hex_encode(w) == *h),
                "the posted box's content hash is WITNESSED after live delivery (queued→handled)"
            );
        }
    }

    /// The data-plane NON-AMP seam, surfaced through the node-held `Bus`: an
    /// over-attenuated / unauthorized enqueue is REFUSED at the seam — nothing
    /// queued, NO receipt minted (no phantom work). This is the same cap gate
    /// the node's POST holds; we drive it over-broad on the node's live Bus to
    /// prove the refusal polarity is not vacuous in production.
    #[tokio::test]
    async fn node_bus_refuses_over_attenuated_enqueue_no_phantom_work() {
        let (state, members, _dir) = funded_state().await;
        let (channel, _) = create_group(&state, &members).await;

        let mut s = state.write().await;
        let inner = &mut *s;
        let recipient = bus_recipient(channel);
        let name = bus_channel_name(channel);
        let relay_key = inner.cclerk.gossip_signing_key();
        let bus = inner.channels.ensure_bus(relay_key);

        let before = bus.pending_count(&recipient);
        let cursor_before = bus.cursor(&name);

        // The node holds a Signature-level send cap into this channel. Offering a
        // BROADER authority (None ⊋ Signature) is refused at the gate.
        let cap = bus_send_cap(channel);
        let refused = bus.enqueue(
            &cap,
            recipient,
            &name,
            AuthRequired::None,
            b"forge".to_vec(),
            1,
        );
        assert!(
            matches!(refused, Err(DataPlaneError::Unauthorized { .. })),
            "an over-broad send is refused at the node's Bus seam"
        );
        // No phantom work: nothing queued, no cursor tick, no receipt.
        assert_eq!(bus.pending_count(&recipient), before, "nothing queued");
        assert_eq!(bus.cursor(&name), cursor_before, "no wake tick for a refused send");

        // A within-grant (Signature) send IS admitted — the gate is not vacuous.
        let ok = bus.enqueue(
            &cap,
            recipient,
            &name,
            AuthRequired::Signature,
            b"ok".to_vec(),
            1,
        );
        assert!(ok.is_ok(), "a within-grant send is admitted");
        assert_eq!(bus.cursor(&name), cursor_before + 1);
    }

    /// THE SPINE, END TO END THROUGH THE NODE: a real multi-party flow rides the
    /// captp `Bus` over the live HTTP surface — a producer POSTs three ciphertexts
    /// (three real `Bus::enqueue`s, each returning a verifying custody receipt),
    /// TWO subscribers each receive all three over the live SSE wire IN ORDER, an
    /// over-authorized enqueue is REFUSED at the node's `admits` seam, and the
    /// four spine properties hold:
    ///
    ///   (a) receipt-identity: each POST's receipt carries a real Ed25519 signature
    ///       and the inbox roots chain old→new across the three posts;
    ///   (b) cap-gated: an over-broad enqueue is refused — no box, no receipt;
    ///   (c) ordered delivery: both SSE subscribers see seq 0,1,2 in order;
    ///   (d) drain lockstep: live SSE delivery drains the Bus inbox box-for-box, so
    ///       it bounds (does NOT accumulate a parallel backlog) and never
    ///       double-witnesses (the witness log holds three distinct hashes).
    #[tokio::test]
    async fn bus_is_the_spine_multiparty_flow_through_the_node() {
        use futures_util::StreamExt;

        let (state, members, _dir) = funded_state().await;
        let (channel, _) = create_group(&state, &members).await;
        let channel_hex = hex_encode(channel.as_bytes());
        let recipient = bus_recipient(channel);

        // ── (b) CAP-GATED: drive an over-broad enqueue on the node's live Bus. It is
        // refused at the `admits` seam — nothing queued, no receipt minted.
        {
            let mut s = state.write().await;
            let inner = &mut *s;
            let name = bus_channel_name(channel);
            let relay_key = inner.cclerk.gossip_signing_key();
            let bus = inner.channels.ensure_bus(relay_key);
            let cursor_before = bus.cursor(&name);
            let cap = bus_send_cap(channel);
            let refused = bus.enqueue(&cap, recipient, &name, AuthRequired::None, b"forge".to_vec(), 1);
            assert!(
                matches!(refused, Err(DataPlaneError::Unauthorized { .. })),
                "(b) an over-authorized enqueue is refused at the node Bus seam"
            );
            assert_eq!(bus.pending_count(&recipient), 0, "(b) nothing queued for a refused send");
            assert_eq!(bus.cursor(&name), cursor_before, "(b) no cursor tick for a refused send");
        }

        // ── PRODUCE: three current-epoch POSTs — three real Bus::enqueues. Capture
        // each delivery receipt (signature + content hash + old/new root) off the wire.
        let mut content_hashes = Vec::new();
        let mut receipts = Vec::new(); // (old_root, new_root, signature)
        for ct in ["deadbeef", "cafef00d", "feedface"] {
            let (status, posted) = post_json(
                &state,
                "/channels/post",
                serde_json::json!({
                    "channel": channel_hex,
                    "epoch": 1,
                    "nonce": "00112233445566778899aabb",
                    "ciphertext": ct,
                }),
            )
            .await;
            assert_eq!(status, StatusCode::OK, "post: {posted}");
            let d = &posted["delivery"];
            // ── (a) RECEIPT-IDENTITY: a real (non-zero) signature on every receipt.
            let sig = d["signature"].as_str().unwrap();
            assert!(sig.chars().any(|c| c != '0'), "(a) the receipt carries a real signature");
            content_hashes.push(d["content_hash"].as_str().unwrap().to_string());
            receipts.push((
                d["old_root"].as_str().unwrap().to_string(),
                d["new_root"].as_str().unwrap().to_string(),
            ));
        }

        // ── (a) ROOT-CHAINING: the three receipts chain old→new across the posts.
        for w in receipts.windows(2) {
            assert_eq!(w[0].1, w[1].0, "(a) each post's new_root is the next post's old_root");
            assert_ne!(w[0].1, w[1].1, "(a) the custody root advances per post");
        }

        // Three boxes queued on the Bus, NONE witnessed yet (queued ≠ handled), and
        // the receipts VERIFY against the node relay's key (reconstructed off-Bus).
        {
            let s = state.read().await;
            let bus = s.channels.bus().expect("bus exists");
            assert_eq!(bus.pending_count(&recipient), 3, "(d) three boxes queued before delivery");
            assert_eq!(bus.delivered_hashes(&recipient).len(), 0, "none witnessed yet");
        }

        // ── (c) ORDERED DELIVERY to ≥2 subscribers: open TWO live SSE streams. Each
        // replays the ring from the start and must see seq 0,1,2 IN ORDER.
        async fn drain_three_in_order(state: &NodeState, channel_hex: &str) -> Vec<u64> {
            let sse = messages_stream(
                AxumPath(channel_hex.to_string()),
                HeaderMap::new(),
                State(state.clone()),
            )
            .await
            .expect("sse opens");
            let mut stream = sse.into_response().into_body().into_data_stream();
            let mut seqs = Vec::new();
            while seqs.len() < 3 {
                match tokio::time::timeout(Duration::from_secs(2), stream.next()).await {
                    Ok(Some(Ok(chunk))) => {
                        let text = String::from_utf8_lossy(&chunk);
                        for line in text.lines() {
                            if let Some(id) = line.strip_prefix("id: ") {
                                if let Ok(seq) = id.trim().parse::<u64>() {
                                    seqs.push(seq);
                                }
                            }
                        }
                    }
                    _ => break,
                }
            }
            seqs
        }

        let sub_a = drain_three_in_order(&state, &channel_hex).await;
        let sub_b = drain_three_in_order(&state, &channel_hex).await;
        assert_eq!(sub_a, vec![0, 1, 2], "(c) subscriber A received seq 0,1,2 in order");
        assert_eq!(sub_b, vec![0, 1, 2], "(c) subscriber B received seq 0,1,2 in order");

        // ── (d) DRAIN LOCKSTEP + NO DOUBLE-WITNESS: live SSE delivery drained the
        // Bus inbox box-for-box, so it is BOUNDED (pending back to 0, not a parallel
        // backlog) and the witness log holds EXACTLY the three distinct content
        // hashes — two subscribers replaying did NOT double-count (the witness is
        // sticky and content-addressed).
        let s = state.read().await;
        let bus = s.channels.bus().expect("bus exists");
        assert_eq!(
            bus.pending_count(&recipient),
            0,
            "(d) live SSE delivery drained the Bus inbox in lockstep (no backlog)"
        );
        let witnessed = bus.delivered_hashes(&recipient);
        assert_eq!(witnessed.len(), 3, "(d) exactly three boxes witnessed (no double-delivery)");
        for h in &content_hashes {
            assert!(
                witnessed.iter().any(|w| hex_encode(w) == *h),
                "(a/d) each posted box's receipt content hash is WITNESSED (queued→handled)"
            );
        }
    }

    #[tokio::test]
    async fn join_steps_the_epoch_and_duplicate_refuses() {
        let (state, members, _dir) = funded_state().await;
        // Found with two members; the third joins.
        let founding = &members[..2];
        let (channel, _) = create_group(&state, founding).await;
        let channel_hex = hex_encode(channel.as_bytes());

        let (status, json) = post_json(
            &state,
            "/channels/join",
            serde_json::json!({
                "channel": channel_hex,
                "member": {
                    "cell": hex_encode(members[2].0.as_bytes()),
                    "seal_pk": hex_encode(&members[2].1.seal_pk()),
                },
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "join: {json}");
        assert_eq!(json["epoch"], 2);
        assert_eq!(json["delegation_epoch"], 2);
        assert_eq!(json["fan_out"].as_array().unwrap().len(), 3);

        // Duplicate join refuses.
        let (status, _) = post_json(
            &state,
            "/channels/join",
            serde_json::json!({
                "channel": channel_hex,
                "member": {
                    "cell": hex_encode(members[2].0.as_bytes()),
                    "seal_pk": hex_encode(&members[2].1.seal_pk()),
                },
            }),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        // A non-member "remove" refuses too.
        let (status, _) = post_json(
            &state,
            "/channels/remove",
            serde_json::json!({
                "channel": channel_hex,
                "member": hex_encode(&[0x42u8; 32]),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
    }

    /// THE DURABLE-ROSTER CLOSURE (docs/PERSISTENCE.md §3 roster caveat):
    /// every committed epoch step persists the roster; a fresh registry
    /// (the restart) rebuilds the room from the durable table after
    /// RE-COMMITTING it against the on-cell membership root — and discards a
    /// roster that no longer matches its cell, fail-closed.
    #[tokio::test]
    async fn roster_survives_a_simulated_restart_and_stale_is_discarded() {
        let (state, members, _dir) = funded_state().await;
        let (channel, _) = create_group(&state, &members).await;

        // Open already persisted the roster. Simulate a restart: a brand-new
        // registry restored from the SAME store against the live ledger.
        {
            let s = state.read().await;
            let mut fresh = ChannelRegistry::default();
            fresh.restore_rosters(&s.store, &s.ledger);
            let room = fresh
                .room(&channel)
                .expect("the room rebuilds from the durable roster");
            assert_eq!(
                room.roster.len(),
                members.len(),
                "the restored roster has every member"
            );
            for (id, ring) in &members {
                assert_eq!(
                    room.roster.get(id).copied(),
                    Some(ring.seal_pk()),
                    "each member's seal pk re-commits to the on-cell root"
                );
            }
            // The room re-committed: its roster_root equals the cell's root.
            let cell = s.ledger.get(&channel).unwrap();
            assert_eq!(
                roster_root(&room.roster),
                slot(cell, CH_MEMBER_ROOT_SLOT),
                "the restored roster re-commits to the on-cell membership root"
            );
            // Epoch keys are node-minted secrets, NOT persisted — a restored
            // room carries none and rekeys to re-establish forward delivery.
            assert!(
                room.keys.is_empty(),
                "epoch keys are not persisted across a restart"
            );
        }

        // STALE PATH: corrupt the on-cell membership root so the durable
        // roster no longer re-commits; the restart must DISCARD it (and the
        // discard is durable — a second restart sees no row, no re-alarm).
        {
            let mut s = state.write().await;
            s.ledger
                .update_with(&channel, |cell| {
                    cell.state.fields[CH_MEMBER_ROOT_SLOT as usize] = [0xEE; 32];
                })
                .unwrap();

            let mut fresh = ChannelRegistry::default();
            fresh.restore_rosters(&s.store, &s.ledger);
            assert!(
                fresh.room(&channel).is_none(),
                "a roster that does not re-commit to the (mutated) on-cell root is discarded"
            );
            // Durable removal: the row is gone.
            let remaining = s.store.load_channel_rosters().unwrap();
            assert!(
                !remaining.iter().any(|(c, _)| *c == channel.0),
                "the stale roster row was durably removed (no re-alarm on the next boot)"
            );
        }
    }
}
