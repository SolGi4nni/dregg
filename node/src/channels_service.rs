//! Channels service — the ORGANS §4 weld (the group-key lift), following the
//! trustline / court service patterns.
//!
//! A group is a CELL (blueprint twin: `dregg_cell::blueprint` channel
//! section; SDK noun: `dregg_sdk::channels`). This service drives the same
//! canonical turns through the node's AUTHORITATIVE executor
//! ([`crate::trustline_service::run_signed_turn`]) and carries the DATA
//! PLANE off-cell: posted ciphertext lives in a node-held ring + SSE stream
//! — message bodies never touch the chain.
//!
//! ## THE KEYSTONE — epoch unification (control plane)
//!
//! `POST /channels/remove` commits ONE turn
//! (`dregg_sdk::channels::epoch_step_effects`): the membership-root rewrite,
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

use dregg_cell::{CellId, Ledger};
use dregg_cell::blueprint::{
    CH_ADMIN_SLOT, CH_EPOCH_SLOT, CH_KEY_COMMIT_SLOT, CH_MEMBER_ROOT_SLOT, CH_STATE_SLOT,
    CH_TAG_SLOT, ChannelTerms, STATE_OPEN, channel_cell_program, channel_factory_descriptor,
};
use dregg_cell::factory::{FactoryCreationParams, canonical_program_vk};
use dregg_sdk::channels::{
    Roster, SealedEpochKey, anchor_token_id, channel_token_id, epoch_step_effects, open_effects,
    roster_root, seal_epoch_key_to_roster,
};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_turn::Effect;

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

/// Node-held channels registry + the SSE wake-up bus.
pub struct ChannelRegistry {
    rooms: HashMap<CellId, Room>,
    /// Wake-up only: (channel, seq). The ring is the durable cursor source.
    tx: broadcast::Sender<(CellId, u64)>,
}

impl Default for ChannelRegistry {
    fn default() -> Self {
        let (tx, _) = broadcast::channel(ROOM_BROADCAST_CAPACITY);
        ChannelRegistry {
            rooms: HashMap::new(),
            tx,
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
    pub fn restore_rosters(
        &mut self,
        store: &dregg_persist::PersistentStore,
        ledger: &Ledger,
    ) {
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
            let on_cell_root = ledger
                .get(&channel)
                .and_then(channel_terms_of_root);
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
}

impl ChannelRefusal {
    fn status(&self) -> StatusCode {
        match self {
            ChannelRefusal::Locked | ChannelRefusal::TurnRejected(_) => StatusCode::FORBIDDEN,
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
        }
    }

    fn detail(&self) -> String {
        match self {
            ChannelRefusal::Locked => "node cipherclerk is locked".into(),
            ChannelRefusal::NoChannel(d)
            | ChannelRefusal::BadTerms(d)
            | ChannelRefusal::TurnRejected(d)
            | ChannelRefusal::BadRequest(d) => d.clone(),
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

// =============================================================================
// Identification + the live position
// =============================================================================

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
fn require_operator_authority(
    s: &NodeStateInner,
    channel: CellId,
) -> Result<(), ChannelRefusal> {
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
    let terms = ChannelTerms { admin: admin_pk, tag };
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
        return Err(ChannelRefusal::BadRequest("member already in the group".into()));
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

#[derive(Serialize)]
struct PostResponse {
    channel: String,
    seq: u64,
    epoch: u64,
}

/// `POST /channels/post` — THE DATA PLANE: store + fan out a ciphertext.
/// The chain is untouched; the node relays what it stores. Posts naming a
/// non-current epoch are refused at the door.
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
        return Err(ChannelRefusal::NoChannel("no room state for this group".into()));
    }
    // Shape checks only — the body is opaque ciphertext by design.
    if req.nonce.len() != 24 || hex_decode_32(&format!("{:0<64}", req.nonce)).is_none() {
        return Err(ChannelRefusal::BadRequest("nonce must be 12 bytes hex".into()));
    }
    if req.ciphertext.is_empty() || req.ciphertext.len() % 2 != 0 {
        return Err(ChannelRefusal::BadRequest("ciphertext must be non-empty hex".into()));
    }
    let seq = inner
        .channels
        .push_message(channel, req.epoch, req.nonce, req.ciphertext);
    Ok(Json(PostResponse {
        channel: hex_encode(&channel.0),
        seq,
        epoch: req.epoch,
    }))
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
            return Err(ChannelRefusal::NoChannel("no room state for this group".into()));
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
            // Drain the ring from the cursor before waiting again.
            let pending = {
                let s = c.state.read().await;
                let room = s.channels.room(&c.channel)?;
                // Skip past evicted history.
                if let Some(front) = room.messages.front() {
                    if c.next < front.seq {
                        c.next = front.seq;
                    }
                }
                room.messages
                    .iter()
                    .find(|m| m.seq >= c.next)
                    .map(|m| (m.seq, serde_json::to_string(m)))
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
        Vec<(CellId, dregg_sdk::channels::MemberKeyring)>,
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
                members.push((id, dregg_sdk::channels::MemberKeyring::new(id, secret)));
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
        members: &[(CellId, dregg_sdk::channels::MemberKeyring)],
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
        members: &[(CellId, dregg_sdk::channels::MemberKeyring)],
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
            let ring = &mut members
                .iter_mut()
                .find(|(id, _)| *id == member)
                .unwrap()
                .1;
            let eph = hex_decode_32(sealed["ephemeral_pk"].as_str().unwrap()).unwrap();
            let ct_hex = sealed["ciphertext"].as_str().unwrap();
            let ct: Vec<u8> = (0..ct_hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&ct_hex[i..i + 2], 16).unwrap())
                .collect();
            ring.accept(&dregg_sdk::channels::SealedEpochKey {
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
