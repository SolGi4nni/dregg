//! DKG ceremony service — the ORGANS §6 upgrade path ("DKG replaces the
//! dealer"), following the channels / trustline / court service patterns.
//!
//! The ceremony state is a CELL (blueprint twin: `dregg_cell::blueprint` DKG
//! section); the protocol math is `dregg_federation::dkg` (joint-Feldman);
//! the transport/agreement layer is `dregg_federation::dkg_ceremony` (signed
//! round messages, seal-pair private shares, the deterministic common view).
//! This service drives the round-CLOSING turns through the node's
//! AUTHORITATIVE executor ([`crate::trustline_service::run_signed_turn`])
//! and relays the signed round messages + sealed shares:
//!
//! * **Rounds ride turns** — each round close is ONE turn pinning that
//!   round's agreed-view root into its write-once slot, admitted only past
//!   the round's published deadline (`TemporalGate`) and only from the
//!   coordinator (`SenderIs`) — the installed program refuses everything
//!   else, so the phase machine on-cell IS the ceremony schedule.
//! * **Messages are attributable** — every dealing/ack/complaint/reveal is
//!   a `SignedCeremonyMsg`; the view verifies the signature against the
//!   roster (pinned on-cell via the roster-root term) before recording, so
//!   nothing unauthenticated ever enters a pinned root.
//! * **Private shares ride seal-pairs** — `SealedShare` ciphertexts
//!   (ephemeral X25519 → ChaCha20-Poly1305, ceremony/dealer/recipient bound
//!   into the payload) are held for pickup; the node relays what it cannot
//!   read.
//! * **Complaints are SLASHABLE** — the deterministic witness-first
//!   attribution (`CeremonyView::offenses`: a verifying reveal convicts the
//!   complainer, an unanswered complaint convicts the dealer, conflicting
//!   signed dealings convict the equivocator) is surfaced on every status
//!   read; an offense is the evidence the court/obligation lane
//!   (`equivocation_court_service` precedent, ORGANS §5) slashes a
//!   participant's bond over.
//!
//! ## Honest residues (named, loud)
//!
//! * The node sequences the broadcast (the messages are signed, the roots
//!   are recomputable by every participant — a node that drops or reorders
//!   is CAUGHT by root comparison, but full BFT-agreed carriage is the
//!   blocklace lane; the view layer is already deterministic in the agreed
//!   sequence, so the swap touches transport only).
//! * The offense→bond-slash composition (participants post obligation cells
//!   at enrollment; finalize files the slash moves) is the adjudication
//!   lane; this service produces and publishes the attributable evidence.
//! * The room registry (view + sealed ciphertexts) is in-memory, like the
//!   channels rooms; the chain holds the roots. Persistence rides the same
//!   lane as the relay/coordinator state.

use std::collections::HashMap;

use axum::extract::{Path as AxumPath, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};

use dregg_cell::CellId;
use dregg_cell::blueprint::{
    DKG_ADMIN_SLOT, DKG_COMPLAINT_DEADLINE_SLOT, DKG_DEALING_DEADLINE_SLOT, DKG_DEALINGS_ROOT_SLOT,
    DKG_OUTPUT_SLOT, DKG_PARAMS_SLOT, DKG_PHASE_ABORTED, DKG_PHASE_COMPLAINT, DKG_PHASE_DEALING,
    DKG_PHASE_FINAL, DKG_PHASE_REVEAL, DKG_PHASE_SLOT, DKG_RESPONSES_ROOT_SLOT,
    DKG_REVEAL_DEADLINE_SLOT, DKG_REVEALS_ROOT_SLOT, DKG_ROSTER_SLOT, DKG_TAG_SLOT,
    DkgCeremonyTerms, dkg_ceremony_cell_program, dkg_ceremony_factory_descriptor,
    dkg_ceremony_token_id, dkg_params_field, dkg_params_from_field, dkg_participant_leaf,
    dkg_roster_root,
};
use dregg_cell::factory::{FactoryCreationParams, canonical_program_vk};
use dregg_federation::dkg::DkgParams;
use dregg_federation::dkg_ceremony::{
    CeremonyError, CeremonyMsg, CeremonyRoster, CeremonyView, Recorded, RosterEntry, SealedShare,
    SignedCeremonyMsg,
};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_turn::Effect;

use crate::state::{NodeState, NodeStateInner};
use crate::trustline_service::{field_u64, hex_decode_32, hex_encode, run_signed_turn};

// =============================================================================
// Registry (lives inside NodeStateInner, the channels-room shape)
// =============================================================================

/// One live ceremony's node-held state: the common view (the node's copy of
/// the agreed message sets) and the sealed-share ciphertexts held for
/// pickup. The chain holds the pinned round roots; the view re-derives them.
pub struct CeremonyRoom {
    /// The deterministic agreed-view accumulator (verifies signatures
    /// against the pinned roster before recording anything).
    pub view: CeremonyView,
    /// Sealed private shares held for recipient pickup (ciphertext to
    /// everyone but the addressee).
    pub sealed: Vec<SealedShare>,
}

/// Node-held DKG registry.
#[derive(Default)]
pub struct DkgRegistry {
    ceremonies: HashMap<CellId, CeremonyRoom>,
}

impl std::fmt::Debug for DkgRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DkgRegistry")
            .field("ceremonies", &self.ceremonies.len())
            .finish()
    }
}

impl DkgRegistry {
    /// The room for one ceremony cell.
    pub fn room(&self, ceremony: &CellId) -> Option<&CeremonyRoom> {
        self.ceremonies.get(ceremony)
    }
    /// Mutable access.
    pub fn room_mut(&mut self, ceremony: &CellId) -> Option<&mut CeremonyRoom> {
        self.ceremonies.get_mut(ceremony)
    }
    /// Register a freshly started ceremony.
    pub fn insert_room(&mut self, ceremony: CellId, room: CeremonyRoom) {
        self.ceremonies.insert(ceremony, room);
    }
}

// =============================================================================
// Refusals
// =============================================================================

/// Every way a DKG request can be refused.
#[derive(Debug)]
pub enum DkgRefusal {
    /// Node cipherclerk is locked.
    Locked,
    /// The named cell is not a DKG-ceremony cell (or not in the ledger /
    /// no room state held).
    NoCeremony(String),
    /// Refused terms / colliding cell / malformed roster.
    BadTerms(String),
    /// The message kind does not belong to the ceremony's CURRENT phase.
    WrongPhase {
        /// The on-cell phase code.
        at: u64,
        /// What the request needed.
        needed: &'static str,
    },
    /// A round close (or finalize) attempted before its published deadline.
    TooEarly {
        /// The deadline height.
        deadline: u64,
        /// The height the close turn would run at.
        height: u64,
    },
    /// A conflicting signed dealing — REFUSED as a contribution, RETAINED
    /// as slashable evidence (visible in status `offenses`).
    Equivocation {
        /// The equivocating dealer.
        dealer: usize,
    },
    /// The ceremony/transport layer refused (bad signature, author
    /// mismatch, malformed message, …).
    Ceremony(CeremonyError),
    /// The authoritative executor rejected a turn (the installed program's
    /// teeth: deadline gate, write-once roots, SenderIs, …).
    TurnRejected(String),
    /// Malformed request.
    BadRequest(String),
}

impl DkgRefusal {
    fn status(&self) -> StatusCode {
        match self {
            DkgRefusal::Locked | DkgRefusal::TurnRejected(_) => StatusCode::FORBIDDEN,
            DkgRefusal::NoCeremony(_) => StatusCode::NOT_FOUND,
            DkgRefusal::WrongPhase { .. }
            | DkgRefusal::TooEarly { .. }
            | DkgRefusal::Equivocation { .. } => StatusCode::CONFLICT,
            DkgRefusal::BadTerms(_) | DkgRefusal::Ceremony(_) | DkgRefusal::BadRequest(_) => {
                StatusCode::BAD_REQUEST
            }
        }
    }

    fn reason(&self) -> &'static str {
        match self {
            DkgRefusal::Locked => "locked",
            DkgRefusal::NoCeremony(_) => "no-ceremony",
            DkgRefusal::BadTerms(_) => "bad-terms",
            DkgRefusal::WrongPhase { .. } => "wrong-phase",
            DkgRefusal::TooEarly { .. } => "too-early",
            DkgRefusal::Equivocation { .. } => "equivocation",
            DkgRefusal::Ceremony(_) => "ceremony-refused",
            DkgRefusal::TurnRejected(_) => "turn-rejected",
            DkgRefusal::BadRequest(_) => "bad-request",
        }
    }

    fn detail(&self) -> String {
        match self {
            DkgRefusal::Locked => "node cipherclerk is locked".into(),
            DkgRefusal::NoCeremony(d)
            | DkgRefusal::BadTerms(d)
            | DkgRefusal::TurnRejected(d)
            | DkgRefusal::BadRequest(d) => d.clone(),
            DkgRefusal::WrongPhase { at, needed } => {
                format!("ceremony is at phase {at}; this request needs {needed}")
            }
            DkgRefusal::TooEarly { deadline, height } => {
                format!("round closes at height {deadline}; the close turn would run at {height}")
            }
            DkgRefusal::Equivocation { dealer } => format!(
                "CONFLICTING dealing from dealer {dealer}: refused as a contribution, \
                 RETAINED as slashable evidence (see status offenses)"
            ),
            DkgRefusal::Ceremony(e) => e.to_string(),
        }
    }
}

impl IntoResponse for DkgRefusal {
    fn into_response(self) -> Response {
        let body = serde_json::json!({
            "error": self.detail(),
            "reason": self.reason(),
        });
        (self.status(), Json(body)).into_response()
    }
}

impl From<crate::trustline_service::TrustlineRefusal> for DkgRefusal {
    fn from(t: crate::trustline_service::TrustlineRefusal) -> Self {
        DkgRefusal::TurnRejected(t.detail())
    }
}

impl From<CeremonyError> for DkgRefusal {
    fn from(e: CeremonyError) -> Self {
        DkgRefusal::Ceremony(e)
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

/// Structurally identify a DKG-ceremony cell: re-derive the per-ceremony
/// program from the cell's OWN term registers and check the installed VK.
/// Self-authenticating — no side registry decides what is a ceremony.
pub fn dkg_terms_of(cell: &dregg_cell::Cell) -> Option<DkgCeremonyTerms> {
    let (n, t) = dkg_params_from_field(&slot(cell, DKG_PARAMS_SLOT));
    let terms = DkgCeremonyTerms {
        n,
        t,
        roster_root: slot(cell, DKG_ROSTER_SLOT),
        admin: slot(cell, DKG_ADMIN_SLOT),
        tag: slot(cell, DKG_TAG_SLOT),
        dealing_deadline: slot_u64(cell, DKG_DEALING_DEADLINE_SLOT),
        complaint_deadline: slot_u64(cell, DKG_COMPLAINT_DEADLINE_SLOT),
        reveal_deadline: slot_u64(cell, DKG_REVEAL_DEADLINE_SLOT),
    };
    let program = dkg_ceremony_cell_program(&terms).ok()?;
    let expected = canonical_program_vk(&program);
    (cell.verification_key.as_ref()?.hash == expected).then_some(terms)
}

/// The live on-cell position of one ceremony.
#[derive(Clone, Copy, Debug)]
pub struct CeremonyPosition {
    /// Phase code (the blueprint constants).
    pub phase: u64,
    /// Pinned round roots (zero until the round closes).
    pub dealings_root: [u8; 32],
    /// See [`CeremonyPosition::dealings_root`].
    pub responses_root: [u8; 32],
    /// See [`CeremonyPosition::dealings_root`].
    pub reveals_root: [u8; 32],
    /// The output commitment (zero unless FINAL).
    pub output: [u8; 32],
}

fn phase_name(phase: u64) -> &'static str {
    match phase {
        p if p == DKG_PHASE_DEALING => "dealing",
        p if p == DKG_PHASE_COMPLAINT => "complaint",
        p if p == DKG_PHASE_REVEAL => "reveal",
        p if p == DKG_PHASE_FINAL => "final",
        p if p == DKG_PHASE_ABORTED => "aborted",
        0 => "uninit",
        _ => "unknown",
    }
}

/// Resolve `id` as a ceremony cell and read its terms + position.
fn resolve_ceremony(
    s: &NodeStateInner,
    id: CellId,
) -> Result<(DkgCeremonyTerms, CeremonyPosition), DkgRefusal> {
    let cell = s.ledger.get(&id).ok_or_else(|| {
        DkgRefusal::NoCeremony(format!("cell {} not in ledger", hex_encode(&id.0)))
    })?;
    let terms = dkg_terms_of(cell).ok_or_else(|| {
        DkgRefusal::NoCeremony(format!(
            "cell {} is not a DKG-ceremony cell (program VK does not match its terms)",
            hex_encode(&id.0)
        ))
    })?;
    let position = CeremonyPosition {
        phase: slot_u64(cell, DKG_PHASE_SLOT),
        dealings_root: slot(cell, DKG_DEALINGS_ROOT_SLOT),
        responses_root: slot(cell, DKG_RESPONSES_ROOT_SLOT),
        reveals_root: slot(cell, DKG_REVEALS_ROOT_SLOT),
        output: slot(cell, DKG_OUTPUT_SLOT),
    };
    Ok((terms, position))
}

/// The height the NEXT turn would execute at (the executor runs closes in
/// `BlockHeightMode::Next`); the program's `TemporalGate` re-checks this
/// authoritatively — the pre-check just refuses with a better message.
fn next_turn_height(s: &NodeStateInner) -> u64 {
    crate::executor_setup::attested_block_height(s).saturating_add(1)
}

// =============================================================================
// The round-closing turns
// =============================================================================

/// Close every round whose deadline has passed, up to (but not into) the
/// terminal phases, stopping at `target`. Each close is ONE operator turn
/// pinning that round's agreed-view root; the installed program enforces
/// the deadline, the root nonzero-ness, the write-once window, and the
/// coordinator gate — a refused turn moves NOTHING.
fn advance_to(inner: &mut NodeStateInner, ceremony: CellId, target: u64) -> Result<(), DkgRefusal> {
    loop {
        let (terms, position) = resolve_ceremony(inner, ceremony)?;
        if position.phase >= target {
            return Ok(());
        }
        let (deadline, root_slot, root, next_phase) = {
            let room = inner
                .ceremonies_room(ceremony)
                .ok_or_else(|| DkgRefusal::NoCeremony("no room state for this ceremony".into()))?;
            match position.phase {
                p if p == DKG_PHASE_DEALING => (
                    terms.dealing_deadline,
                    DKG_DEALINGS_ROOT_SLOT,
                    room.view.dealings_root(),
                    DKG_PHASE_COMPLAINT,
                ),
                p if p == DKG_PHASE_COMPLAINT => (
                    terms.complaint_deadline,
                    DKG_RESPONSES_ROOT_SLOT,
                    room.view.responses_root(),
                    DKG_PHASE_REVEAL,
                ),
                p => {
                    return Err(DkgRefusal::WrongPhase {
                        at: p,
                        needed: "a live round to advance",
                    });
                }
            }
        };
        let height = next_turn_height(inner);
        if height < deadline {
            return Err(DkgRefusal::TooEarly { deadline, height });
        }
        if !inner.unlocked {
            return Err(DkgRefusal::Locked);
        }
        let operator = crate::executor_setup::local_agent_cell(inner);
        run_signed_turn(
            inner,
            operator,
            ceremony,
            "dkg_round_close",
            vec![
                Effect::SetField {
                    cell: ceremony,
                    index: root_slot as usize,
                    value: root,
                },
                Effect::SetField {
                    cell: ceremony,
                    index: DKG_PHASE_SLOT as usize,
                    value: field_u64(next_phase),
                },
            ],
            None,
            None,
        )?;
        tracing::info!(
            ceremony = %hex_encode(&ceremony.0),
            phase = phase_name(next_phase),
            "DKG round closed: agreed-view root pinned on-cell"
        );
    }
}

// NodeStateInner convenience: the borrow-friendly room reader used above.
impl NodeStateInner {
    fn ceremonies_room(&self, ceremony: CellId) -> Option<&CeremonyRoom> {
        self.dkg.room(&ceremony)
    }
}

// =============================================================================
// Routes
// =============================================================================

/// The DKG route surface. Mounted inside the node's PROTECTED router
/// (bearer-token gate) in `api.rs`.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/dkg/start", post(post_start))
        .route("/dkg/contribute", post(post_contribute))
        .route("/dkg/complain", post(post_complain))
        .route("/dkg/finalize", post(post_finalize))
        .route("/dkg/status/{cell}", get(get_status))
}

fn hex_decode(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

#[derive(Deserialize)]
struct ParticipantSpec {
    /// Participant cell id, hex.
    cell: String,
    /// X25519 seal public key, hex (private shares are sealed to it).
    seal_pk: String,
    /// ed25519 public key, hex (round messages are verified against it).
    auth_pk: String,
}

#[derive(Deserialize)]
struct StartRequest {
    /// Ceremony tag (u64; names this ceremony among the coordinator's).
    tag: u64,
    /// Threshold t. Committee size n = participants.len().
    t: u64,
    /// Participants, in INDEX ORDER (entry k is participant k+1).
    participants: Vec<ParticipantSpec>,
    /// Block height the dealing round may close at.
    dealing_deadline: u64,
    /// Block height the complaint round may close at.
    complaint_deadline: u64,
    /// Block height the reveal round may close at (the finalize gate).
    reveal_deadline: u64,
}

#[derive(Serialize)]
struct StartResponse {
    ceremony: String,
    phase: &'static str,
    n: u64,
    t: u64,
    dealing_deadline: u64,
    complaint_deadline: u64,
    reveal_deadline: u64,
    turn_hashes: Vec<String>,
}

fn parse_roster(participants: &[ParticipantSpec]) -> Result<CeremonyRoster, DkgRefusal> {
    let mut roster = CeremonyRoster::new();
    for (k, p) in participants.iter().enumerate() {
        let index = k + 1;
        let cell = hex_decode_32(&p.cell)
            .ok_or_else(|| DkgRefusal::BadRequest(format!("malformed cell id: {}", p.cell)))?;
        let seal_pk = hex_decode_32(&p.seal_pk)
            .ok_or_else(|| DkgRefusal::BadRequest(format!("malformed seal pk: {}", p.seal_pk)))?;
        let auth_pk = hex_decode_32(&p.auth_pk)
            .ok_or_else(|| DkgRefusal::BadRequest(format!("malformed auth pk: {}", p.auth_pk)))?;
        roster.insert(
            index,
            RosterEntry {
                index,
                cell,
                seal_pk,
                auth_pk,
            },
        );
    }
    Ok(roster)
}

fn roster_commitment(roster: &CeremonyRoster) -> [u8; 32] {
    let leaves = roster
        .values()
        .map(|e| dkg_participant_leaf(e.index as u64, &e.cell, &e.seal_pk, &e.auth_pk))
        .collect();
    dkg_roster_root(&leaves)
}

/// `POST /dkg/start` — birth the ceremony cell from its per-ceremony
/// factory, grant the coordinator its driving capability, and OPEN into the
/// dealing phase (the terms turn).
async fn post_start(
    State(state): State<NodeState>,
    Json(req): Json<StartRequest>,
) -> Result<Json<StartResponse>, DkgRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    if !inner.unlocked {
        return Err(DkgRefusal::Locked);
    }
    let roster = parse_roster(&req.participants)?;
    for entry in roster.values() {
        if inner.ledger.get(&CellId(entry.cell)).is_none() {
            return Err(DkgRefusal::BadRequest(format!(
                "participant cell {} not in ledger",
                hex_encode(&entry.cell)
            )));
        }
    }

    let operator = crate::executor_setup::local_agent_cell(inner);
    let admin_pk = inner.cclerk.public_key().0;
    let tag = field_u64(req.tag);
    let n = roster.len() as u64;
    let terms = DkgCeremonyTerms {
        n,
        t: req.t,
        roster_root: roster_commitment(&roster),
        admin: admin_pk,
        tag,
        dealing_deadline: req.dealing_deadline,
        complaint_deadline: req.complaint_deadline,
        reveal_deadline: req.reveal_deadline,
    };
    let descriptor =
        dkg_ceremony_factory_descriptor(&terms).map_err(|e| DkgRefusal::BadTerms(e.to_string()))?;
    let params = DkgParams {
        n: n as usize,
        t: req.t as usize,
    };

    let token_id = dkg_ceremony_token_id(&admin_pk, &tag, &terms.roster_root);
    let ceremony = CellId::derive_raw(&admin_pk, &token_id);
    if inner.ledger.get(&ceremony).is_some() {
        return Err(DkgRefusal::BadTerms(format!(
            "ceremony cell {} already exists (vary `tag`)",
            hex_encode(&ceremony.0)
        )));
    }
    let view = CeremonyView::new(ceremony.0, params, roster)
        .map_err(|e| DkgRefusal::BadTerms(e.to_string()))?;

    let mut turn_hashes = Vec::with_capacity(4);

    // Turn 1 — birth from the per-ceremony factory.
    turn_hashes.push(run_signed_turn(
        inner,
        operator,
        operator,
        "dkg_create",
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
        "dkg_fund",
        vec![Effect::Transfer {
            from: operator,
            to: ceremony,
            amount: ADOPT_TURN_FEE,
        }],
        None,
        None,
    )?);

    // Turn 3 — the adopt (cell-agent turn): grant the coordinator its
    // driving capability (a DIRECT grant — no epoch machinery here).
    turn_hashes.push(run_signed_turn(
        inner,
        ceremony,
        ceremony,
        "dkg_adopt",
        vec![Effect::GrantCapability {
            from: ceremony,
            to: operator,
            cap: dregg_cell::CapabilityRef {
                target: ceremony,
                slot: 0,
                permissions: dregg_cell::AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        }],
        Some(ADOPT_TURN_FEE),
        None,
    )?);

    // Turn 4 — OPEN: write every term and enter the dealing phase.
    turn_hashes.push(run_signed_turn(
        inner,
        operator,
        ceremony,
        "dkg_open",
        vec![
            Effect::SetField {
                cell: ceremony,
                index: DKG_PARAMS_SLOT as usize,
                value: dkg_params_field(terms.n, terms.t),
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_ROSTER_SLOT as usize,
                value: terms.roster_root,
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_ADMIN_SLOT as usize,
                value: terms.admin,
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_TAG_SLOT as usize,
                value: terms.tag,
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_DEALING_DEADLINE_SLOT as usize,
                value: field_u64(terms.dealing_deadline),
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_COMPLAINT_DEADLINE_SLOT as usize,
                value: field_u64(terms.complaint_deadline),
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_REVEAL_DEADLINE_SLOT as usize,
                value: field_u64(terms.reveal_deadline),
            },
            Effect::SetField {
                cell: ceremony,
                index: DKG_PHASE_SLOT as usize,
                value: field_u64(DKG_PHASE_DEALING),
            },
        ],
        None,
        None,
    )?);

    inner.dkg.insert_room(
        ceremony,
        CeremonyRoom {
            view,
            sealed: Vec::new(),
        },
    );

    tracing::info!(
        ceremony = %hex_encode(&ceremony.0),
        n,
        t = req.t,
        "DKG ceremony opened (ORGANS §6: the ceremony state is a cell)"
    );

    Ok(Json(StartResponse {
        ceremony: hex_encode(&ceremony.0),
        phase: "dealing",
        n,
        t: req.t,
        dealing_deadline: req.dealing_deadline,
        complaint_deadline: req.complaint_deadline,
        reveal_deadline: req.reveal_deadline,
        turn_hashes: turn_hashes.iter().map(|h| hex_encode(h)).collect(),
    }))
}

#[derive(Deserialize, Serialize)]
struct SealedShareWire {
    dealer: usize,
    recipient: usize,
    /// Sender's ephemeral X25519 public key, hex.
    ephemeral_pk: String,
    /// Sealed payload, hex.
    ciphertext: String,
}

impl SealedShareWire {
    fn to_sealed(&self, ceremony: [u8; 32]) -> Result<SealedShare, DkgRefusal> {
        Ok(SealedShare {
            ceremony,
            dealer: self.dealer,
            recipient: self.recipient,
            ephemeral_pk: hex_decode_32(&self.ephemeral_pk)
                .ok_or_else(|| DkgRefusal::BadRequest("malformed ephemeral_pk".into()))?,
            ciphertext: hex_decode(&self.ciphertext)
                .ok_or_else(|| DkgRefusal::BadRequest("malformed ciphertext".into()))?,
        })
    }

    fn from_sealed(s: &SealedShare) -> Self {
        SealedShareWire {
            dealer: s.dealer,
            recipient: s.recipient,
            ephemeral_pk: hex_encode(&s.ephemeral_pk),
            ciphertext: hex_encode(&s.ciphertext),
        }
    }
}

#[derive(Deserialize)]
struct ContributeRequest {
    /// Ceremony cell id, hex.
    ceremony: String,
    /// A `SignedCeremonyMsg` (wire bytes), hex. Dealings belong to the
    /// dealing phase; acks to the complaint phase; reveals to the reveal
    /// phase. Complaints go to `/dkg/complain`.
    message: String,
    /// Dealing only: the sealed private shares to hold for pickup.
    #[serde(default)]
    sealed_shares: Vec<SealedShareWire>,
}

#[derive(Serialize)]
struct ContributeResponse {
    ceremony: String,
    kind: &'static str,
    recorded: &'static str,
    phase: &'static str,
    sealed_held: usize,
}

fn parse_ceremony(s: &str) -> Result<CellId, DkgRefusal> {
    Ok(CellId(hex_decode_32(s).ok_or_else(|| {
        DkgRefusal::BadRequest(format!("malformed ceremony cell id: {s}"))
    })?))
}

fn parse_signed(message: &str) -> Result<SignedCeremonyMsg, DkgRefusal> {
    let bytes =
        hex_decode(message).ok_or_else(|| DkgRefusal::BadRequest("message must be hex".into()))?;
    SignedCeremonyMsg::from_bytes(&bytes)
        .map_err(|_| DkgRefusal::BadRequest("malformed signed ceremony message".into()))
}

/// Record one verified message into the room's view (signature checked by
/// the view itself, against the roster the chain pins).
fn record_message(
    inner: &mut NodeStateInner,
    ceremony: CellId,
    signed: &SignedCeremonyMsg,
) -> Result<&'static str, DkgRefusal> {
    let room = inner
        .dkg
        .room_mut(&ceremony)
        .ok_or_else(|| DkgRefusal::NoCeremony("no room state for this ceremony".into()))?;
    match room.view.record(signed)? {
        Recorded::Fresh => Ok("fresh"),
        Recorded::Duplicate => Ok("duplicate"),
        Recorded::Equivocation(e) => Err(DkgRefusal::Equivocation { dealer: e.dealer }),
    }
}

/// `POST /dkg/contribute` — file a signed round message: a DEALING (with
/// its sealed shares), an ACK, or a REVEAL. The phase windows: dealings
/// while the cell is DEALING; acks once the dealing set is pinned (the
/// COMPLAINT window — the first ack/complaint past the dealing deadline
/// triggers the round-closing turn); reveals in the REVEAL window likewise.
async fn post_contribute(
    State(state): State<NodeState>,
    Json(req): Json<ContributeRequest>,
) -> Result<Json<ContributeResponse>, DkgRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let ceremony = parse_ceremony(&req.ceremony)?;
    let signed = parse_signed(&req.message)?;

    let (kind, needed_phase) = match &signed.msg {
        CeremonyMsg::Dealing(_) => ("dealing", DKG_PHASE_DEALING),
        CeremonyMsg::Response(dregg_federation::dkg::ShareResponse::Ack { .. }) => {
            ("ack", DKG_PHASE_COMPLAINT)
        }
        CeremonyMsg::Response(dregg_federation::dkg::ShareResponse::Complaint(_)) => {
            return Err(DkgRefusal::BadRequest(
                "complaints go to /dkg/complain".into(),
            ));
        }
        CeremonyMsg::Reveal(_) => ("reveal", DKG_PHASE_REVEAL),
    };

    if needed_phase > DKG_PHASE_DEALING {
        // Close any due earlier rounds (the program enforces the deadline).
        advance_to(inner, ceremony, needed_phase)?;
    }
    let (_, position) = resolve_ceremony(inner, ceremony)?;
    if position.phase != needed_phase {
        return Err(DkgRefusal::WrongPhase {
            at: position.phase,
            needed: kind,
        });
    }

    // Dealings carry sealed shares; validate their addressing up front.
    let mut sealed = Vec::new();
    if let CeremonyMsg::Dealing(d) = &signed.msg {
        for wire in &req.sealed_shares {
            let share = wire.to_sealed(ceremony.0)?;
            if share.dealer != d.dealer {
                return Err(DkgRefusal::BadRequest(format!(
                    "sealed share claims dealer {} inside dealer {}'s contribution",
                    share.dealer, d.dealer
                )));
            }
            sealed.push(share);
        }
    } else if !req.sealed_shares.is_empty() {
        return Err(DkgRefusal::BadRequest(
            "sealed shares ride dealings only".into(),
        ));
    }

    let recorded = record_message(inner, ceremony, &signed)?;
    let sealed_held = sealed.len();
    if recorded == "fresh" && !sealed.is_empty() {
        let room = inner
            .dkg
            .room_mut(&ceremony)
            .expect("room exists (recorded above)");
        room.sealed.extend(sealed);
    }

    Ok(Json(ContributeResponse {
        ceremony: hex_encode(&ceremony.0),
        kind,
        recorded,
        phase: phase_name(needed_phase),
        sealed_held,
    }))
}

#[derive(Deserialize)]
struct ComplainRequest {
    /// Ceremony cell id, hex.
    ceremony: String,
    /// A `SignedCeremonyMsg` (wire bytes) whose body is a COMPLAINT, hex.
    /// Signed by the complainer — complaints are on-record and SLASHABLE
    /// in both directions (a false complaint convicts the complainer once
    /// the dealer's reveal verifies; an unanswered one convicts the dealer).
    message: String,
}

/// `POST /dkg/complain` — file a signed complaint (the COMPLAINT window).
async fn post_complain(
    State(state): State<NodeState>,
    Json(req): Json<ComplainRequest>,
) -> Result<Json<ContributeResponse>, DkgRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let ceremony = parse_ceremony(&req.ceremony)?;
    let signed = parse_signed(&req.message)?;
    if !matches!(
        &signed.msg,
        CeremonyMsg::Response(dregg_federation::dkg::ShareResponse::Complaint(_))
    ) {
        return Err(DkgRefusal::BadRequest(
            "/dkg/complain takes a signed complaint".into(),
        ));
    }
    advance_to(inner, ceremony, DKG_PHASE_COMPLAINT)?;
    let (_, position) = resolve_ceremony(inner, ceremony)?;
    if position.phase != DKG_PHASE_COMPLAINT {
        return Err(DkgRefusal::WrongPhase {
            at: position.phase,
            needed: "complaint",
        });
    }
    let recorded = record_message(inner, ceremony, &signed)?;
    Ok(Json(ContributeResponse {
        ceremony: hex_encode(&ceremony.0),
        kind: "complaint",
        recorded,
        phase: "complaint",
        sealed_held: 0,
    }))
}

#[derive(Deserialize)]
struct FinalizeRequest {
    /// Ceremony cell id, hex.
    ceremony: String,
}

#[derive(Serialize)]
struct FinalizeResponse {
    ceremony: String,
    phase: &'static str,
    /// The qualified dealer set (FINAL only).
    qual: Vec<usize>,
    /// The output commitment pinned on-cell (FINAL only), hex.
    commitment: Option<String>,
    /// The `DkgPublicView`-compatible public surface bytes (FINAL only),
    /// hex — threshold ‖ group public key ‖ share publics; feeds
    /// `DkgPublicView::from_bytes` / beacon-committee bootstrap directly.
    public_view: Option<String>,
    /// The deterministic offense attribution over the agreed view — the
    /// slashable record (court/obligation lane input), present either way.
    offenses: Vec<serde_json::Value>,
    turn_hash: String,
}

/// `POST /dkg/finalize` — close any due rounds, then settle the ceremony:
/// |QUAL| ≥ t pins the output commitment and enters FINAL; below threshold
/// ABORTS loudly (output stays zero — the program refuses a fake finish
/// either way). Offenses are published in both outcomes.
async fn post_finalize(
    State(state): State<NodeState>,
    Json(req): Json<FinalizeRequest>,
) -> Result<Json<FinalizeResponse>, DkgRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;
    let ceremony = parse_ceremony(&req.ceremony)?;

    advance_to(inner, ceremony, DKG_PHASE_REVEAL)?;
    let (terms, position) = resolve_ceremony(inner, ceremony)?;
    if position.phase != DKG_PHASE_REVEAL {
        return Err(DkgRefusal::WrongPhase {
            at: position.phase,
            needed: "the reveal phase",
        });
    }
    let height = next_turn_height(inner);
    if height < terms.reveal_deadline {
        return Err(DkgRefusal::TooEarly {
            deadline: terms.reveal_deadline,
            height,
        });
    }
    if !inner.unlocked {
        return Err(DkgRefusal::Locked);
    }

    let (reveals_root, outcome, offenses) = {
        let room = inner
            .dkg
            .room(&ceremony)
            .ok_or_else(|| DkgRefusal::NoCeremony("no room state for this ceremony".into()))?;
        let offenses: Vec<serde_json::Value> = room
            .view
            .offenses()
            .iter()
            .map(|o| {
                serde_json::json!({
                    "offender": o.offender(),
                    "offense": serde_json::to_value(o).unwrap_or(serde_json::Value::Null),
                })
            })
            .collect();
        (
            room.view.reveals_root(),
            room.view.public_output(),
            offenses,
        )
    };

    let operator = crate::executor_setup::local_agent_cell(inner);
    match outcome {
        Ok(output) => {
            let commitment = output.commitment();
            let turn_hash = run_signed_turn(
                inner,
                operator,
                ceremony,
                "dkg_finalize",
                vec![
                    Effect::SetField {
                        cell: ceremony,
                        index: DKG_REVEALS_ROOT_SLOT as usize,
                        value: reveals_root,
                    },
                    Effect::SetField {
                        cell: ceremony,
                        index: DKG_OUTPUT_SLOT as usize,
                        value: commitment,
                    },
                    Effect::SetField {
                        cell: ceremony,
                        index: DKG_PHASE_SLOT as usize,
                        value: field_u64(DKG_PHASE_FINAL),
                    },
                ],
                None,
                None,
            )?;
            tracing::info!(
                ceremony = %hex_encode(&ceremony.0),
                qual = ?output.qual,
                "DKG ceremony FINAL: output commitment pinned (no party ever held f(0))"
            );
            Ok(Json(FinalizeResponse {
                ceremony: hex_encode(&ceremony.0),
                phase: "final",
                qual: output.qual.clone(),
                commitment: Some(hex_encode(&commitment)),
                public_view: Some(hex_encode(&output.public_view_bytes())),
                offenses,
                turn_hash: hex_encode(&turn_hash),
            }))
        }
        Err(e) => {
            // |QUAL| < t: abort loudly — finishing would let a smaller
            // coalition reconstruct f(0). The reveal record still pins
            // (the slash evidence survives the failure).
            let turn_hash = run_signed_turn(
                inner,
                operator,
                ceremony,
                "dkg_abort",
                vec![
                    Effect::SetField {
                        cell: ceremony,
                        index: DKG_REVEALS_ROOT_SLOT as usize,
                        value: reveals_root,
                    },
                    Effect::SetField {
                        cell: ceremony,
                        index: DKG_PHASE_SLOT as usize,
                        value: field_u64(DKG_PHASE_ABORTED),
                    },
                ],
                None,
                None,
            )?;
            tracing::warn!(
                ceremony = %hex_encode(&ceremony.0),
                reason = %e,
                "DKG ceremony ABORTED (insufficient QUAL); offenses published"
            );
            Ok(Json(FinalizeResponse {
                ceremony: hex_encode(&ceremony.0),
                phase: "aborted",
                qual: vec![],
                commitment: None,
                public_view: None,
                offenses,
                turn_hash: hex_encode(&turn_hash),
            }))
        }
    }
}

#[derive(Serialize)]
struct StatusResponse {
    ceremony: String,
    phase: &'static str,
    n: u64,
    t: u64,
    admin: String,
    tag: String,
    dealing_deadline: u64,
    complaint_deadline: u64,
    reveal_deadline: u64,
    next_turn_height: u64,
    /// On-cell pinned roots (hex; zero until the round closes).
    pinned_dealings_root: String,
    pinned_responses_root: String,
    pinned_reveals_root: String,
    /// The node-held view's CURRENT roots — any participant recomputes
    /// these from the published messages; pinned ≠ recomputed-at-close is
    /// LOUD evidence against the coordinator.
    view_dealings_root: Option<String>,
    view_responses_root: Option<String>,
    view_reveals_root: Option<String>,
    dealings: Option<usize>,
    acks: Option<usize>,
    complaints: Option<usize>,
    reveals: Option<usize>,
    /// QUAL over the current view (meaningful once the dealing set is
    /// pinned; final once REVEAL closes).
    qual: Option<Vec<usize>>,
    /// The slashable record (deterministic witness-first attribution).
    offenses: Vec<serde_json::Value>,
    /// Sealed private shares held for pickup (ciphertext to everyone but
    /// each addressee).
    sealed_shares: Vec<SealedShareWire>,
    /// The on-cell output commitment (FINAL only), hex.
    output: Option<String>,
}

/// `GET /dkg/status/{cell}`.
async fn get_status(
    State(state): State<NodeState>,
    AxumPath(cell): AxumPath<String>,
) -> Result<Json<StatusResponse>, DkgRefusal> {
    let s = state.read().await;
    let ceremony = parse_ceremony(&cell)?;
    let (terms, position) = resolve_ceremony(&s, ceremony)?;
    let room = s.dkg.room(&ceremony);
    let offenses = room
        .map(|r| {
            r.view
                .offenses()
                .iter()
                .map(|o| {
                    serde_json::json!({
                        "offender": o.offender(),
                        "offense": serde_json::to_value(o).unwrap_or(serde_json::Value::Null),
                    })
                })
                .collect()
        })
        .unwrap_or_default();
    Ok(Json(StatusResponse {
        ceremony: hex_encode(&ceremony.0),
        phase: phase_name(position.phase),
        n: terms.n,
        t: terms.t,
        admin: hex_encode(&terms.admin),
        tag: hex_encode(&terms.tag),
        dealing_deadline: terms.dealing_deadline,
        complaint_deadline: terms.complaint_deadline,
        reveal_deadline: terms.reveal_deadline,
        next_turn_height: next_turn_height(&s),
        pinned_dealings_root: hex_encode(&position.dealings_root),
        pinned_responses_root: hex_encode(&position.responses_root),
        pinned_reveals_root: hex_encode(&position.reveals_root),
        view_dealings_root: room.map(|r| hex_encode(&r.view.dealings_root())),
        view_responses_root: room.map(|r| hex_encode(&r.view.responses_root())),
        view_reveals_root: room.map(|r| hex_encode(&r.view.reveals_root())),
        dealings: room.map(|r| r.view.dealing_count()),
        acks: room.map(|r| r.view.acks().len()),
        complaints: room.map(|r| r.view.complaints().len()),
        reveals: room.map(|r| r.view.reveals().len()),
        qual: room.map(|r| r.view.qual().into_iter().collect()),
        offenses,
        sealed_shares: room
            .map(|r| r.sealed.iter().map(SealedShareWire::from_sealed).collect())
            .unwrap_or_default(),
        output: (position.phase == DKG_PHASE_FINAL).then(|| hex_encode(&position.output)),
    }))
}

// =============================================================================
// Tests — the ceremony end-to-end on the real router + executor
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use dregg_federation::dkg_ceremony::CeremonyDriver;
    use ed25519_dalek::SigningKey;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    struct TestMember {
        cell: CellId,
        sign_sk: [u8; 32],
        seal_sk: [u8; 32],
        seal_pk: [u8; 32],
        auth_pk: [u8; 32],
    }

    /// A node state with a funded operator agent cell and `n` member cells.
    async fn funded_state(n: usize) -> (NodeState, Vec<TestMember>, tempfile::TempDir) {
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
            for i in 0..n {
                let token = *blake3::Hasher::new_derive_key("dkg-node-test-member-v1")
                    .update(&[i as u8])
                    .finalize()
                    .as_bytes();
                let cell = dregg_cell::Cell::with_balance(operator_pk, token, 200_000);
                let id = cell.id();
                s.ledger.insert_cell(cell).expect("member inserts");
                let sign_sk = [0x21 + i as u8; 32];
                let auth_pk = SigningKey::from_bytes(&sign_sk).verifying_key().to_bytes();
                let (seal_sk, seal_pk) = dregg_captp::store_forward::generate_x25519_keypair();
                members.push(TestMember {
                    cell: id,
                    sign_sk,
                    seal_sk,
                    seal_pk,
                    auth_pk,
                });
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

    fn participants_json(members: &[TestMember]) -> Vec<serde_json::Value> {
        members
            .iter()
            .map(|m| {
                serde_json::json!({
                    "cell": hex_encode(m.cell.as_bytes()),
                    "seal_pk": hex_encode(&m.seal_pk),
                    "auth_pk": hex_encode(&m.auth_pk),
                })
            })
            .collect()
    }

    fn client_roster(members: &[TestMember]) -> CeremonyRoster {
        members
            .iter()
            .enumerate()
            .map(|(k, m)| {
                (
                    k + 1,
                    RosterEntry {
                        index: k + 1,
                        cell: m.cell.0,
                        seal_pk: m.seal_pk,
                        auth_pk: m.auth_pk,
                    },
                )
            })
            .collect()
    }

    /// Start a ceremony with all deadlines at height 1 (closable on demand;
    /// the windows still gate ORDER — see the too-early test for real gates).
    async fn start_ceremony(
        state: &NodeState,
        members: &[TestMember],
        t: u64,
        tag: u64,
    ) -> (CellId, serde_json::Value) {
        let (status, json) = post_json(
            state,
            "/dkg/start",
            serde_json::json!({
                "tag": tag,
                "t": t,
                "participants": participants_json(members),
                "dealing_deadline": 1,
                "complaint_deadline": 1,
                "reveal_deadline": 1,
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "start must succeed: {json}");
        (
            CellId(hex_decode_32(json["ceremony"].as_str().unwrap()).unwrap()),
            json,
        )
    }

    fn sealed_wire(sealed: &[SealedShare], dealer: usize) -> Vec<serde_json::Value> {
        sealed
            .iter()
            .filter(|s| s.dealer == dealer)
            .map(|s| serde_json::to_value(SealedShareWire::from_sealed(s)).unwrap())
            .collect()
    }

    #[tokio::test]
    async fn full_ceremony_start_contribute_finalize() {
        let (state, members, _dir) = funded_state(3).await;
        let (ceremony, started) = start_ceremony(&state, &members, 2, 7).await;
        assert_eq!(started["phase"], "dealing");
        let ceremony_hex = hex_encode(ceremony.as_bytes());
        let params = DkgParams { n: 3, t: 2 };
        let roster = client_roster(&members);

        // Each member deals client-side and contributes over the wire.
        let mut drivers = Vec::new();
        let mut dealings = Vec::new();
        let mut sealed_all = Vec::new();
        for (k, m) in members.iter().enumerate() {
            let (d, signed, sealed) = CeremonyDriver::new(
                ceremony.0,
                params,
                k + 1,
                m.sign_sk,
                m.seal_sk,
                roster.clone(),
            )
            .unwrap();
            let (status, json) = post_json(
                &state,
                "/dkg/contribute",
                serde_json::json!({
                    "ceremony": ceremony_hex,
                    "message": hex_encode(&signed.to_bytes()),
                    "sealed_shares": sealed_wire(&sealed, k + 1),
                }),
            )
            .await;
            assert_eq!(status, StatusCode::OK, "dealing {k}: {json}");
            assert_eq!(json["recorded"], "fresh");
            assert_eq!(json["sealed_held"], 3);
            drivers.push(d);
            dealings.push(signed);
            sealed_all.extend(sealed);
        }
        // Drivers observe each other's dealings (as relayed bytes).
        for signed in &dealings {
            for d in drivers.iter_mut() {
                if d.index() != signed.signer {
                    d.observe(signed).unwrap();
                }
            }
        }
        // Members pick their sealed shares from STATUS (the pickup path)
        // and ack; the first ack closes the dealing round (deadline 1).
        let (status, st) = get_json(&state, &format!("/dkg/status/{ceremony_hex}")).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(st["dealings"], 3);
        assert_eq!(st["sealed_shares"].as_array().unwrap().len(), 9);
        let mut acks = Vec::new();
        for wire in st["sealed_shares"].as_array().unwrap() {
            let wire: SealedShareWire = serde_json::from_value(wire.clone()).unwrap();
            let recipient = wire.recipient;
            let sealed = wire.to_sealed(ceremony.0).unwrap();
            let ack = drivers[recipient - 1].accept_share(&sealed).unwrap();
            acks.push(ack);
        }
        for ack in &acks {
            let (status, json) = post_json(
                &state,
                "/dkg/contribute",
                serde_json::json!({
                    "ceremony": ceremony_hex,
                    "message": hex_encode(&ack.to_bytes()),
                }),
            )
            .await;
            assert_eq!(status, StatusCode::OK, "ack: {json}");
            for d in drivers.iter_mut() {
                if d.index() != ack.signer {
                    d.observe(ack).unwrap();
                }
            }
        }

        // Finalize: closes the complaint round, settles FINAL, full QUAL.
        let (status, fin) = post_json(
            &state,
            "/dkg/finalize",
            serde_json::json!({ "ceremony": ceremony_hex }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "finalize: {fin}");
        assert_eq!(fin["phase"], "final");
        assert_eq!(fin["qual"], serde_json::json!([1, 2, 3]));
        assert!(fin["offenses"].as_array().unwrap().is_empty());

        // The committed output is exactly what every participant recomputes
        // from their own view — and their secret shares agree with it.
        let local = drivers[0].view().public_output().unwrap();
        assert_eq!(
            fin["commitment"].as_str().unwrap(),
            hex_encode(&local.commitment())
        );
        assert_eq!(
            fin["public_view"].as_str().unwrap(),
            hex_encode(&local.public_view_bytes())
        );
        let outs: Vec<_> = drivers.iter().map(|d| d.finalize().unwrap()).collect();
        for o in &outs[1..] {
            assert_eq!(o.group_public(), outs[0].group_public());
        }
        assert_eq!(&local.group_public, outs[0].group_public());

        // The chain agrees: phase FINAL, output slot = the commitment, and
        // the pinned dealing root equals the recomputed one.
        let (status, st) = get_json(&state, &format!("/dkg/status/{ceremony_hex}")).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(st["phase"], "final");
        assert_eq!(st["output"], fin["commitment"]);
        assert_eq!(st["pinned_dealings_root"], st["view_dealings_root"]);
        assert_eq!(st["qual"], serde_json::json!([1, 2, 3]));

        // Terminal is inert: a second finalize refuses (wrong phase).
        let (status, json) = post_json(
            &state,
            "/dkg/finalize",
            serde_json::json!({ "ceremony": ceremony_hex }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "wrong-phase");
    }

    #[tokio::test]
    async fn equivocating_dealing_is_refused_and_evidence_retained() {
        let (state, members, _dir) = funded_state(3).await;
        let (ceremony, _) = start_ceremony(&state, &members, 2, 8).await;
        let ceremony_hex = hex_encode(ceremony.as_bytes());
        let params = DkgParams { n: 3, t: 2 };
        let roster = client_roster(&members);

        // Dealer 1 deals TWICE (same identity, fresh polynomial).
        let (_d1, first, sealed1) = CeremonyDriver::new(
            ceremony.0,
            params,
            1,
            members[0].sign_sk,
            members[0].seal_sk,
            roster.clone(),
        )
        .unwrap();
        let (_d2, second, _) = CeremonyDriver::new(
            ceremony.0,
            params,
            1,
            members[0].sign_sk,
            members[0].seal_sk,
            roster,
        )
        .unwrap();
        let (status, _) = post_json(
            &state,
            "/dkg/contribute",
            serde_json::json!({
                "ceremony": ceremony_hex,
                "message": hex_encode(&first.to_bytes()),
                "sealed_shares": sealed_wire(&sealed1, 1),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        let (status, json) = post_json(
            &state,
            "/dkg/contribute",
            serde_json::json!({
                "ceremony": ceremony_hex,
                "message": hex_encode(&second.to_bytes()),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "equivocation");

        // The evidence is on the slashable record; the first dealing stands.
        let (_, st) = get_json(&state, &format!("/dkg/status/{ceremony_hex}")).await;
        assert_eq!(st["dealings"], 1);
        let offenses = st["offenses"].as_array().unwrap();
        assert_eq!(offenses.len(), 1);
        assert_eq!(offenses[0]["offender"], 1);
    }

    #[tokio::test]
    async fn windows_gate_kinds_and_deadlines_gate_closes() {
        let (state, members, _dir) = funded_state(3).await;
        // FAR deadlines: the dealing round cannot close yet.
        let (status, json) = post_json(
            &state,
            "/dkg/start",
            serde_json::json!({
                "tag": 9,
                "t": 2,
                "participants": participants_json(&members),
                "dealing_deadline": 1000,
                "complaint_deadline": 2000,
                "reveal_deadline": 3000,
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let ceremony = CellId(hex_decode_32(json["ceremony"].as_str().unwrap()).unwrap());
        let ceremony_hex = hex_encode(ceremony.as_bytes());
        let params = DkgParams { n: 3, t: 2 };
        let roster = client_roster(&members);

        let (mut d1, dealing, sealed) = CeremonyDriver::new(
            ceremony.0,
            params,
            1,
            members[0].sign_sk,
            members[0].seal_sk,
            roster,
        )
        .unwrap();
        // A reveal during the dealing phase refuses at the window.
        let to_self = sealed.iter().find(|s| s.recipient == 1).unwrap();
        let _ack = d1.accept_share(to_self).unwrap();
        // (Use the ack as the out-of-window message — phase is DEALING and
        //  the dealing round cannot close before height 1000.)
        let (status, json) = post_json(
            &state,
            "/dkg/contribute",
            serde_json::json!({
                "ceremony": ceremony_hex,
                "message": hex_encode(&_ack.to_bytes()),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "too-early");

        // Finalize likewise refuses: the rounds cannot close early.
        let (status, json) = post_json(
            &state,
            "/dkg/finalize",
            serde_json::json!({ "ceremony": ceremony_hex }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "too-early");

        // A dealing in-window records fine.
        let (status, json) = post_json(
            &state,
            "/dkg/contribute",
            serde_json::json!({
                "ceremony": ceremony_hex,
                "message": hex_encode(&dealing.to_bytes()),
                "sealed_shares": sealed_wire(&sealed, 1),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");

        // An unauthenticated (tampered-signature) message refuses.
        let mut bad = dealing.clone();
        bad.signature[0] ^= 1;
        let (status, json) = post_json(
            &state,
            "/dkg/contribute",
            serde_json::json!({
                "ceremony": ceremony_hex,
                "message": hex_encode(&bad.to_bytes()),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST, "{json}");
        assert_eq!(json["reason"], "ceremony-refused");
    }

    #[tokio::test]
    async fn silent_dealer_is_disqualified_and_offense_published() {
        let (state, members, _dir) = funded_state(3).await;
        let (ceremony, _) = start_ceremony(&state, &members, 2, 11).await;
        let ceremony_hex = hex_encode(ceremony.as_bytes());
        let params = DkgParams { n: 3, t: 2 };
        let roster = client_roster(&members);

        let mut drivers = Vec::new();
        let mut dealings = Vec::new();
        let mut sealed_all = Vec::new();
        for (k, m) in members.iter().enumerate() {
            let (d, signed, sealed) = CeremonyDriver::new(
                ceremony.0,
                params,
                k + 1,
                m.sign_sk,
                m.seal_sk,
                roster.clone(),
            )
            .unwrap();
            // Dealer 2 WITHHOLDS the share for member 3 (delivers the rest).
            let kept: Vec<SealedShare> = sealed
                .into_iter()
                .filter(|s| !(s.dealer == 2 && s.recipient == 3))
                .collect();
            let wire: Vec<serde_json::Value> = kept
                .iter()
                .filter(|s| s.dealer == k + 1)
                .map(|s| serde_json::to_value(SealedShareWire::from_sealed(s)).unwrap())
                .collect();
            let (status, _) = post_json(
                &state,
                "/dkg/contribute",
                serde_json::json!({
                    "ceremony": ceremony_hex,
                    "message": hex_encode(&signed.to_bytes()),
                    "sealed_shares": wire,
                }),
            )
            .await;
            assert_eq!(status, StatusCode::OK);
            drivers.push(d);
            dealings.push(signed);
            sealed_all.extend(kept);
        }
        for signed in &dealings {
            for d in drivers.iter_mut() {
                if d.index() != signed.signer {
                    d.observe(signed).unwrap();
                }
            }
        }
        // Deliver what exists; member 3 then complains about dealer 2.
        let mut responses = Vec::new();
        for sealed in &sealed_all {
            responses.push(drivers[sealed.recipient - 1].accept_share(sealed).unwrap());
        }
        for resp in &responses {
            let (status, _) = post_json(
                &state,
                "/dkg/contribute",
                serde_json::json!({
                    "ceremony": ceremony_hex,
                    "message": hex_encode(&resp.to_bytes()),
                }),
            )
            .await;
            assert_eq!(status, StatusCode::OK);
            for d in drivers.iter_mut() {
                if d.index() != resp.signer {
                    d.observe(resp).unwrap();
                }
            }
        }
        let complaints = drivers[2].missing_share_complaints();
        assert_eq!(complaints.len(), 1);
        let (status, json) = post_json(
            &state,
            "/dkg/complain",
            serde_json::json!({
                "ceremony": ceremony_hex,
                "message": hex_encode(&complaints[0].to_bytes()),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["recorded"], "fresh");

        // Dealer 2 stays SILENT through the reveal window. Finalize:
        // disqualified (QUAL = {1,3} ≥ t=2), FINAL, the offense published.
        let (status, fin) = post_json(
            &state,
            "/dkg/finalize",
            serde_json::json!({ "ceremony": ceremony_hex }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{fin}");
        assert_eq!(fin["phase"], "final");
        assert_eq!(fin["qual"], serde_json::json!([1, 3]));
        let offenses = fin["offenses"].as_array().unwrap();
        assert_eq!(offenses.len(), 1);
        assert_eq!(offenses[0]["offender"], 2, "the silent dealer is convicted");
    }
}
