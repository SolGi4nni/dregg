//! Trustline service — the ORGANS §1 weld (docs/TRUSTLINES.md).
//!
//! The Stingray bounded-counter machinery existed end to end and was
//! stillborn at exactly one joint: `init_budget_coordinator`
//! (`state.rs`) had ZERO callers, so `budget_coordinators` was always empty,
//! the executor's per-turn `BudgetGate` seeding (`blocklace_sync.rs`) never
//! fired, and the settlement edges (`collect_spending_certificates` /
//! `rebalance_budgets`) dangled uncalled. This module is the weld, three
//! parts:
//!
//! * **(a) THE BIRTH EDGE** — `POST /trustline/open` births a trustline cell
//!   from the per-line content-addressed factory
//!   (`dregg_cell::blueprint::trustline_factory_descriptor`, Lean twin
//!   `Dregg2.Apps.Trustline`), funds it with a REAL ledger debit (the issuer
//!   escrows the full line — an ordinary conserving `Transfer` through the
//!   authoritative executor, never a mint), and calls
//!   [`crate::state::NodeStateInner::init_budget_coordinator`] to seed the
//!   shared counter. From that moment the agent's per-turn `BudgetGate`
//!   seeding and the MCP check/debit tools are live.
//! * **(b) THE BILATERAL SHAPE** — "I extend you a line of N" is an
//!   attenuated capability: at birth the cell grants the HOLDER a c-list
//!   capability over itself, and every draw debits the shared counter
//!   (`StingrayCounter::try_debit_fresh` — `Slice.tryDebit` + the anti-replay
//!   leg, Lean `draw_fires_iff_tryDebit`) AND commits an executor turn
//!   against the cell whose installed program (`drawn ≤ ceiling` for life)
//!   is the enforcement tooth — the StorageGatewayMandate volume-budget
//!   pattern on the credit counter.
//! * **(c) SETTLEMENT** — `POST /trustline/settle` is the first real caller
//!   of `collect_spending_certificates` + `rebalance_budgets`; each returned
//!   `(agent, total_spent)` entry is applied back to the ledger as an
//!   ordinary `Transfer` (escrow → holder, balance-neutral, so the
//!   conservation keystone lifts free) together with the cell's monotone
//!   `settled` register march.
//!
//! ## Design rule (docs/TRUSTLINES.md §2): the cell is the truth; the
//! coordinator is a derived shadow.
//!
//! The coordinator can always be REBUILT from the cell's registers
//! ([`ensure_coordinator`]): `total_balance = line − settled`, with the
//! outstanding `drawn − settled` re-debited. The two draw gates are
//! equivalent by construction — coordinator remaining = `line − drawn` =
//! the cell's remaining line — and the tests assert the agreement.
//!
//! ## Honest residues (named, with their lanes)
//!
//! * The coordinator + the draw-digest registry are in-memory (rebuilt from
//!   the cell on restart; digests within the live epoch are also carried by
//!   the slice's `debits` list, but a restart narrows anti-replay to the
//!   rebuilt shadow). Persistence rides the same lane as the rest of the
//!   budget layer.
//! * Remote-silo pubkey registration from federation membership is out of
//!   scope (state.rs marks it); n = 1 collapses it (single-machine principle).
//! * This weld implements the fullReserve (payment-channel) point of the
//!   collateral axis; the pureCredit point (draws as issuer-moves against a
//!   negative-capable well — the wells exist, `register_issuer_well`) is the
//!   named next setting.

use std::collections::{HashMap, HashSet};

use axum::extract::{Path as AxumPath, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};

use dregg_cell::CellId;
use dregg_cell::blueprint::{
    STATE_OPEN, TL_CEILING_SLOT, TL_DIGEST_SLOT, TL_DRAWN_SLOT, TL_HOLDER_SLOT, TL_ISSUER_SLOT,
    TL_SETTLED_SLOT, TL_STATE_CLOSED, TL_STATE_SLOT, TrustlineCollateral, TrustlineTerms,
    trustline_cell_program_collateral, trustline_factory_descriptor_collateral,
};
use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor, canonical_program_vk};
use dregg_coord::budget::BudgetError;
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_turn::action::{Event, symbol};
use dregg_turn::{CallForest, Effect, Turn, TurnResult};

use crate::state::{NodeState, NodeStateInner};

// =============================================================================
// Service state (lives inside NodeStateInner)
// =============================================================================

/// Node-held trustline registry: the FOREVER draw-digest anti-replay set
/// (Lean `no_double_draw_forever` — the Stingray slice's `debits` list resets
/// at each rebalance epoch, so the forever-property needs this carrier).
#[derive(Debug, Default)]
pub struct TrustlineRegistry {
    digests: HashMap<CellId, HashSet<[u8; 32]>>,
}

impl TrustlineRegistry {
    /// Rebuild the registry from the durable forever-digest table at boot
    /// (`docs/PERSISTENCE.md`): every digest ever burned on this node is
    /// reloaded, so a replayed draw refuses identically across restarts —
    /// the deployed counterpart of Lean `draw_replay_refused_across_epochs`
    /// holds across process lifetimes, not only rebalance epochs.
    pub fn load(store: &dregg_persist::PersistentStore) -> Self {
        let mut registry = Self::default();
        match store.load_forever_digests(dregg_persist::tables::NS_TRUSTLINE_DIGEST) {
            Ok(pairs) => {
                let count = pairs.len();
                for (scope, digest) in pairs {
                    registry
                        .digests
                        .entry(CellId(scope))
                        .or_default()
                        .insert(digest);
                }
                if count > 0 {
                    tracing::info!(
                        digests = count,
                        "restored trustline forever-digest registry"
                    );
                }
            }
            Err(e) => {
                // Fail LOUDLY: an unreadable digest table narrows anti-replay
                // to this process lifetime — a real degradation, named.
                tracing::error!(
                    error = %e,
                    "failed to load durable trustline digests; \
                     forever anti-replay narrowed to this process lifetime"
                );
            }
        }
        registry
    }

    /// Whether `digest` has ever committed a draw against `trustline`.
    pub fn digest_seen(&self, trustline: &CellId, digest: &[u8; 32]) -> bool {
        self.digests
            .get(trustline)
            .is_some_and(|set| set.contains(digest))
    }

    /// Burn a digest (called only after the draw turn COMMITS).
    pub fn record_digest(&mut self, trustline: CellId, digest: [u8; 32]) {
        self.digests.entry(trustline).or_default().insert(digest);
    }
}

/// Burn a digest FOREVER: durable first (one committed redb transaction —
/// the digest survives an arbitrary crash from here on), then the in-memory
/// registry the hot refusal path reads. A durable-write failure cannot unwind
/// the already-committed turn, so it degrades (loudly) to in-memory-only
/// rather than refusing: the live process still refuses replays; only the
/// restart carrier is narrowed, and the error names it.
pub fn record_digest_durable(s: &mut NodeStateInner, trustline: CellId, digest: [u8; 32]) {
    if let Err(e) = s.store.record_forever_digest(
        dregg_persist::tables::NS_TRUSTLINE_DIGEST,
        trustline.as_bytes(),
        &digest,
    ) {
        tracing::error!(
            trustline = %hex_encode(trustline.as_bytes()),
            error = %e,
            "durable digest burn FAILED — forever anti-replay for this digest \
             is narrowed to this process lifetime"
        );
    }
    s.trustlines.record_digest(trustline, digest);
}

// =============================================================================
// Refusals (fail-closed admission outcomes)
// =============================================================================

/// Every way a trustline request can be refused.
#[derive(Debug)]
pub enum TrustlineRefusal {
    /// Node cipherclerk is locked — no operator authority to exercise.
    Locked,
    /// The named cell is not a trustline cell (or not in the ledger).
    NoTrustline(String),
    /// The operator's agent cell holds no capability over the trustline cell.
    NoCapability(String),
    /// Refused trustline terms (zero line / zero party) or a colliding cell.
    BadTerms(String),
    /// The line is not OPEN.
    NotOpen,
    /// A draw digest was replayed (no-double-draw, Lean `draw_replay_refused`).
    DuplicateDraw,
    /// The draw exceeds the remaining line (Lean `over_line_draw_refused`).
    OverLine { remaining: u64, requested: u64 },
    /// The repay exceeds the outstanding unsettled draw
    /// (Lean `over_repay_refused`, strengthened by the settled floor).
    OverRepay { outstanding: u64, requested: u64 },
    /// A pureCredit close was requested over an outstanding draw (closing
    /// cannot debit the holder — settle or repay first).
    OutstandingAtClose { outstanding: u64 },
    /// The Stingray counter refused the debit (slice exhausted / replay /
    /// unknown silo) — the `Slice.tryDebit` gate.
    Counter(String),
    /// The authoritative executor rejected the turn (the cell-program
    /// enforcement tooth: `drawn ≤ ceiling`, monotone `settled`, term pins).
    TurnRejected(String),
    /// Malformed request (bad hex, missing cell, …).
    BadRequest(String),
}

impl TrustlineRefusal {
    fn status(&self) -> StatusCode {
        match self {
            TrustlineRefusal::Locked
            | TrustlineRefusal::NoCapability(_)
            | TrustlineRefusal::NotOpen
            | TrustlineRefusal::TurnRejected(_) => StatusCode::FORBIDDEN,
            TrustlineRefusal::NoTrustline(_) => StatusCode::NOT_FOUND,
            TrustlineRefusal::DuplicateDraw => StatusCode::CONFLICT,
            TrustlineRefusal::OverLine { .. }
            | TrustlineRefusal::OverRepay { .. }
            | TrustlineRefusal::OutstandingAtClose { .. }
            | TrustlineRefusal::Counter(_) => StatusCode::PAYMENT_REQUIRED,
            TrustlineRefusal::BadTerms(_) | TrustlineRefusal::BadRequest(_) => {
                StatusCode::BAD_REQUEST
            }
        }
    }

    fn reason(&self) -> &'static str {
        match self {
            TrustlineRefusal::Locked => "locked",
            TrustlineRefusal::NoTrustline(_) => "no-trustline",
            TrustlineRefusal::NoCapability(_) => "no-capability",
            TrustlineRefusal::BadTerms(_) => "bad-terms",
            TrustlineRefusal::NotOpen => "not-open",
            TrustlineRefusal::DuplicateDraw => "duplicate-draw",
            TrustlineRefusal::OverLine { .. } => "over-line",
            TrustlineRefusal::OverRepay { .. } => "over-repay",
            TrustlineRefusal::OutstandingAtClose { .. } => "outstanding-at-close",
            TrustlineRefusal::Counter(_) => "counter-refused",
            TrustlineRefusal::TurnRejected(_) => "turn-rejected",
            TrustlineRefusal::BadRequest(_) => "bad-request",
        }
    }

    pub(crate) fn detail(&self) -> String {
        match self {
            TrustlineRefusal::Locked => "node cipherclerk is locked".into(),
            TrustlineRefusal::NoTrustline(d)
            | TrustlineRefusal::NoCapability(d)
            | TrustlineRefusal::BadTerms(d)
            | TrustlineRefusal::Counter(d)
            | TrustlineRefusal::TurnRejected(d)
            | TrustlineRefusal::BadRequest(d) => d.clone(),
            TrustlineRefusal::NotOpen => "trustline is not open".into(),
            TrustlineRefusal::DuplicateDraw => {
                "draw digest already committed against this line (no-double-draw)".into()
            }
            TrustlineRefusal::OverLine {
                remaining,
                requested,
            } => format!("draw {requested} exceeds remaining line {remaining}"),
            TrustlineRefusal::OverRepay {
                outstanding,
                requested,
            } => format!("repay {requested} exceeds outstanding unsettled draw {outstanding}"),
            TrustlineRefusal::OutstandingAtClose { outstanding } => format!(
                "pureCredit close refused: {outstanding} outstanding — settle or repay first \
                 (closing cannot debit the holder)"
            ),
        }
    }
}

impl IntoResponse for TrustlineRefusal {
    fn into_response(self) -> Response {
        let body = serde_json::json!({
            "error": self.detail(),
            "reason": self.reason(),
        });
        (self.status(), Json(body)).into_response()
    }
}

// =============================================================================
// Slot / hex helpers
// =============================================================================

pub(crate) fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

pub(crate) fn hex_decode_32(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

fn slot(cell: &dregg_cell::Cell, index: u8) -> [u8; 32] {
    cell.state.fields[index as usize]
}

fn slot_u64(cell: &dregg_cell::Cell, index: u8) -> u64 {
    let f = slot(cell, index);
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

pub(crate) fn field_u64(value: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&value.to_be_bytes());
    f
}

// =============================================================================
// Trustline identification + the live position
// =============================================================================

/// The live position of one trustline cell.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct TrustlinePosition {
    pub line: u64,
    pub drawn: u64,
    pub settled: u64,
    pub remaining: u64,
    pub escrow: u64,
    pub open: bool,
}

/// Structurally identify a trustline cell AND its collateral point:
/// re-derive the per-line program from the cell's OWN term registers (trying
/// each point of the collateral axis — the mode is content-addressed into
/// the program VK, never read from a tamper-able slot) and check the
/// installed VK matches. Self-authenticating — no side registry decides
/// what is a trustline.
pub fn trustline_terms_of(
    cell: &dregg_cell::Cell,
) -> Option<(TrustlineTerms, TrustlineCollateral)> {
    let terms = TrustlineTerms {
        line: slot_u64(cell, TL_CEILING_SLOT),
        issuer: slot(cell, TL_ISSUER_SLOT),
        holder: slot(cell, TL_HOLDER_SLOT),
    };
    let installed = cell.verification_key.as_ref()?.hash;
    for collateral in [
        TrustlineCollateral::FullReserve,
        TrustlineCollateral::PureCredit,
    ] {
        if let Ok(program) = trustline_cell_program_collateral(&terms, collateral)
            && canonical_program_vk(&program) == installed
        {
            return Some((terms, collateral));
        }
    }
    None
}

/// Resolve `id` as a trustline cell and read its position + terms + the
/// collateral point of its line.
fn resolve_trustline(
    s: &NodeStateInner,
    id: CellId,
) -> Result<(TrustlineTerms, TrustlineCollateral, TrustlinePosition), TrustlineRefusal> {
    let cell = s.ledger.get(&id).ok_or_else(|| {
        TrustlineRefusal::NoTrustline(format!("cell {} not in ledger", hex_encode(&id.0)))
    })?;
    let (terms, collateral) = trustline_terms_of(cell).ok_or_else(|| {
        TrustlineRefusal::NoTrustline(format!(
            "cell {} is not a trustline cell (program VK does not match its terms)",
            hex_encode(&id.0)
        ))
    })?;
    let drawn = slot_u64(cell, TL_DRAWN_SLOT);
    let settled = slot_u64(cell, TL_SETTLED_SLOT);
    let position = TrustlinePosition {
        line: terms.line,
        drawn,
        settled,
        remaining: terms.line.saturating_sub(drawn),
        escrow: u64::try_from(cell.state.balance()).unwrap_or(0),
        open: slot_u64(cell, TL_STATE_SLOT) == STATE_OPEN,
    };
    Ok((terms, collateral, position))
}

/// The wire name of a collateral point (requests + responses).
fn collateral_name(c: TrustlineCollateral) -> &'static str {
    match c {
        TrustlineCollateral::FullReserve => "fullReserve",
        TrustlineCollateral::PureCredit => "pureCredit",
    }
}

/// Parse a request's collateral string (absent = the deployed default).
///
/// TODO(collateral-axis): the node `OpenRequest` does not yet carry a
/// collateral field, so the HTTP open path is fullReserve-only (its turn-2
/// funded birth escrows the full line unconditionally). This parser is the
/// request-side half of the pureCredit open lane; wiring it requires an
/// `OpenRequest.collateral` field AND a pureCredit funding branch that escrows
/// nothing (cf. `dregg_sdk::trustline::open_with_collateral`). Kept (not
/// deleted) to preserve the migration's intent; currently unreached.
#[allow(dead_code)] // Retained pureCredit-open request parser; not yet wired.
fn parse_collateral(s: Option<&str>) -> Result<TrustlineCollateral, TrustlineRefusal> {
    match s {
        None | Some("fullReserve") => Ok(TrustlineCollateral::FullReserve),
        Some("pureCredit") => Ok(TrustlineCollateral::PureCredit),
        Some(other) => Err(TrustlineRefusal::BadRequest(format!(
            "unknown collateral mode {other:?} (expected \"fullReserve\" or \"pureCredit\")"
        ))),
    }
}

/// The request-level authority gate (the storage-weld shape): node unlocked
/// and the operator's agent cell holds a c-list capability over the
/// trustline cell (granted by the adopt turn at open).
fn require_operator_authority(
    s: &NodeStateInner,
    trustline: CellId,
) -> Result<(), TrustlineRefusal> {
    if !s.unlocked {
        return Err(TrustlineRefusal::Locked);
    }
    let operator_cell = crate::executor_setup::local_agent_cell(s);
    let holds_cap = s
        .ledger
        .get(&operator_cell)
        .map(|c| c.capabilities.has_access(&trustline))
        .unwrap_or(false);
    if !holds_cap {
        return Err(TrustlineRefusal::NoCapability(format!(
            "operator agent cell {} holds no capability over trustline {}",
            hex_encode(&operator_cell.0),
            hex_encode(&trustline.0),
        )));
    }
    Ok(())
}

// =============================================================================
// The executor turn (shared commit shape)
// =============================================================================

/// Build, sign, and execute ONE turn through the node's authoritative
/// executor path (`new_submit_executor` over the live ledger). `agent` pays
/// the fee and supplies the replay nonce; operator-agent turns link into and
/// extend the cipherclerk receipt chain, cell-agent turns (the one-time
/// adopt) do not (the receipt belongs to the cell's history — the
/// `AgentRuntime::execute_as` semantics).
pub(crate) fn run_signed_turn(
    s: &mut NodeStateInner,
    agent: CellId,
    target: CellId,
    method: &str,
    effects: Vec<Effect>,
    fixed_fee: Option<u64>,
    deploy: Option<&FactoryDescriptor>,
) -> Result<[u8; 32], TrustlineRefusal> {
    let federation_id = crate::executor_setup::federation_id_for_executor(s);
    let operator_cell = crate::executor_setup::local_agent_cell(s);
    let is_operator_turn = agent == operator_cell;

    let action = s
        .cclerk
        .make_action(target, method, effects, &federation_id);
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    let previous_receipt_hash = if is_operator_turn {
        s.cclerk.receipt_chain().last().map(|r| r.receipt_hash())
    } else {
        None
    };
    let nonce = s.ledger.get(&agent).map(|c| c.state.nonce()).unwrap_or(0);

    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let mut turn = Turn {
        agent,
        nonce,
        fee: 0,
        memo: None,
        valid_until: Some(now + 3600),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let mut executor = crate::executor_setup::new_submit_executor(s);
    if let Some(descriptor) = deploy {
        executor.deploy_factory(descriptor.clone());
    }
    // The fee IS the computron budget; the agent cell pays it from its
    // balance (an unfunded agent refuses fail-closed — fund via the faucet).
    turn.fee = fixed_fee.unwrap_or_else(|| executor.estimate_cost(&turn));
    let turn_hash = turn.hash();

    if is_operator_turn && let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent, head);
    }

    match executor.execute(&turn, &mut s.ledger) {
        TurnResult::Committed { receipt, .. } => {
            if is_operator_turn {
                s.cclerk.append_receipt(receipt).map_err(|e| {
                    TrustlineRefusal::TurnRejected(format!("receipt chain mismatch: {e}"))
                })?;
            }
            Ok(turn_hash)
        }
        TurnResult::Rejected { reason, .. } => {
            Err(TrustlineRefusal::TurnRejected(reason.to_string()))
        }
        TurnResult::Expired => Err(TrustlineRefusal::TurnRejected("turn expired".into())),
        TurnResult::Pending => Err(TrustlineRefusal::TurnRejected("turn pending".into())),
    }
}

// =============================================================================
// The coordinator shadow (THE BIRTH EDGE + the rebuild rule)
// =============================================================================

/// The deterministic digest the shadow rebuild re-debits the outstanding
/// position under. Pure over `(trustline, drawn, settled)` so a test (or a
/// second rebuild at the same position) derives the identical digest.
fn shadow_rebuild_digest(trustline: &CellId, drawn: u64, settled: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-trustline-shadow-rebuild-v1");
    hasher.update(trustline.as_bytes());
    hasher.update(&drawn.to_le_bytes());
    hasher.update(&settled.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// The deterministic digest a settle-rejection compensation re-debits the
/// unapplied settlement under (see `post_trustline_settle`). Includes the
/// post-rebalance epoch version so repeated failures across epochs derive
/// distinct digests.
fn settle_unapplied_digest(trustline: &CellId, amount: u64, version: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-trustline-settle-unapplied-v1");
    hasher.update(trustline.as_bytes());
    hasher.update(&amount.to_le_bytes());
    hasher.update(&version.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Ensure the Stingray coordinator shadow exists for `trustline`, REBUILDING
/// it from the cell's registers when absent (restart, or a line opened
/// before this node joined): `total_balance = line − settled`, then the
/// outstanding `drawn − settled` is re-debited under a deterministic
/// rebuild digest so the counter agrees with the cell truth.
///
/// Coordinator remaining = `(line − settled) − (drawn − settled)` =
/// `line − drawn` = the cell's remaining line: the two draw gates agree at
/// every reachable state.
///
/// The rebuild digest is recorded in the FOREVER registry too (not only in
/// the rebuilt slice's `debits`), so registry ⊇ slice-debits is a real
/// invariant and a client draw replaying the rebuild digest refuses
/// identically across rebalance epochs and further rebuilds.
pub fn ensure_coordinator(
    s: &mut NodeStateInner,
    trustline: CellId,
    position: &TrustlinePosition,
) -> Result<(), TrustlineRefusal> {
    if s.budget_coordinators.contains_key(&trustline) {
        return Ok(());
    }
    let backing = position.line.saturating_sub(position.settled);
    s.init_budget_coordinator(trustline, backing, vec![s.silo_id], 0)
        .map_err(|e| TrustlineRefusal::Counter(format!("coordinator init failed: {e}")))?;
    let outstanding = position.drawn.saturating_sub(position.settled);
    if outstanding > 0 {
        let digest = shadow_rebuild_digest(&trustline, position.drawn, position.settled);
        let silo = s.silo_id;
        if let Some(coordinator) = s.budget_coordinators.get_mut(&trustline) {
            coordinator
                .try_debit_fresh(silo, outstanding, digest)
                .map_err(|e| {
                    TrustlineRefusal::Counter(format!("coordinator shadow rebuild failed: {e}"))
                })?;
        }
        // Burn the rebuild digest in the forever registry, exactly as a
        // committed draw's digest is burned: the slice's debit list resets
        // at every rebalance epoch, the registry does not.
        record_digest_durable(s, trustline, digest);
        tracing::info!(
            trustline = %hex_encode(trustline.as_bytes()),
            outstanding,
            "rebuilt trustline coordinator shadow from the cell registers"
        );
    }
    Ok(())
}

// =============================================================================
// Routes
// =============================================================================

/// The trustline route surface. Mounted inside the node's PROTECTED router
/// (bearer-token gate) in `api.rs`.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/trustline/open", post(post_trustline_open))
        .route("/trustline/draw", post(post_trustline_draw))
        .route("/trustline/repay", post(post_trustline_repay))
        .route("/trustline/settle", post(post_trustline_settle))
        .route("/trustline/close", post(post_trustline_close))
        .route("/trustline/status/{cell}", get(get_trustline_status))
}

#[derive(Deserialize)]
pub(crate) struct OpenRequest {
    /// Holder (counterparty) cell id, hex.
    pub(crate) holder: String,
    /// The line N to extend (escrowed in full at open — fullReserve).
    pub(crate) line: u64,
    /// Optional salt disambiguating multiple lines to the same holder.
    #[serde(default)]
    pub(crate) salt: Option<String>,
}

#[derive(Serialize)]
pub(crate) struct OpenResponse {
    pub(crate) trustline: String,
    pub(crate) issuer: String,
    pub(crate) holder: String,
    pub(crate) line: u64,
    pub(crate) escrow: u64,
    pub(crate) coordinator_remaining: u64,
    pub(crate) turn_hashes: Vec<String>,
}

#[derive(Deserialize)]
struct DrawRequest {
    trustline: String,
    amount: u64,
    /// Draw digest (hex). Defaults to a hash over (trustline, drawn, amount,
    /// time) — supply one for client-side replay protection across retries.
    #[serde(default)]
    digest: Option<String>,
}

#[derive(Serialize)]
struct DrawResponse {
    trustline: String,
    digest: String,
    amount: u64,
    drawn: u64,
    remaining: u64,
    coordinator_remaining: u64,
    turn_hash: String,
}

#[derive(Deserialize)]
struct RepayRequest {
    trustline: String,
    amount: u64,
}

#[derive(Serialize)]
struct RepayResponse {
    trustline: String,
    amount: u64,
    drawn: u64,
    remaining: u64,
    coordinator_remaining: u64,
    turn_hash: String,
}

#[derive(Deserialize)]
struct CloseRequest {
    trustline: String,
}

#[derive(Serialize)]
struct CloseResponse {
    trustline: String,
    /// `"fullReserve"` | `"pureCredit"`.
    collateral: String,
    /// Outstanding draw settled to the holder at close (fullReserve only;
    /// pureCredit requires a clean position, so always 0 there).
    settled_to_holder: u64,
    /// Residual escrow returned to the issuer (`escrow − outstanding`;
    /// pureCredit has no escrow, so always 0).
    residual_to_issuer: u64,
    turn_hash: String,
}

#[derive(Serialize)]
struct SettlementEntry {
    trustline: String,
    holder: String,
    amount: u64,
    turn_hash: String,
}

#[derive(Serialize)]
struct SettleResponse {
    epoch: u64,
    certificates: usize,
    settlements: Vec<SettlementEntry>,
    /// Settlement entries the ledger application FAILED for — a non-empty
    /// list is a counter↔ledger divergence and is also logged loudly. Each
    /// rejected move is compensated in the same request (the unapplied
    /// amount is re-carried by the counter and re-attempted next settle);
    /// a compensation failure appends a second entry here.
    failures: Vec<String>,
}

#[derive(Serialize)]
struct StatusResponse {
    trustline: String,
    issuer: String,
    holder: String,
    /// The collateral point of the line (`"fullReserve"` | `"pureCredit"`).
    collateral: String,
    #[serde(flatten)]
    position: TrustlinePosition,
    coordinator_remaining: Option<u64>,
    coordinator_version: Option<u64>,
}

/// `POST /trustline/open` — (a) THE BIRTH EDGE.
async fn post_trustline_open(
    State(state): State<NodeState>,
    Json(req): Json<OpenRequest>,
) -> Result<Json<OpenResponse>, TrustlineRefusal> {
    let mut s = state.write().await;
    open_trustline(&mut s, req).await.map(Json)
}

/// The trustline birth lifecycle, callable in-process (the HTTP route above
/// AND the `dregg_extend_trustline` MCP tool both drive it): birth from the
/// per-line factory → funded birth (the issuer is REALLY debited the full
/// line) → adopt (grant operator + holder their line capability) → open
/// (pin the terms, step UNINIT → OPEN) → seed the bounded-counter shadow.
/// Returns the same [`OpenResponse`] the route serializes.
pub(crate) async fn open_trustline(
    inner: &mut NodeStateInner,
    req: OpenRequest,
) -> Result<OpenResponse, TrustlineRefusal> {
    if !inner.unlocked {
        return Err(TrustlineRefusal::Locked);
    }

    let holder = CellId(hex_decode_32(&req.holder).ok_or_else(|| {
        TrustlineRefusal::BadRequest(format!("malformed holder cell id: {}", req.holder))
    })?);
    if inner.ledger.get(&holder).is_none() {
        return Err(TrustlineRefusal::BadRequest(format!(
            "holder cell {} not in ledger (settlement needs a real target)",
            req.holder
        )));
    }

    let issuer = crate::executor_setup::local_agent_cell(inner);
    let operator_pk = inner.cclerk.public_key().0;

    let terms = TrustlineTerms {
        line: req.line,
        issuer: *issuer.as_bytes(),
        holder: *holder.as_bytes(),
    };
    // The open flow is the fullReserve point of the collateral axis: turn 2
    // below escrows the full line unconditionally, so the cell is solvent by
    // construction. fullReserve's descriptor is byte-identical to the
    // historical (pre-axis) descriptor, so already-born lines are untouched.
    // pureCredit lines are constructed by their own (DERIVED-leg) flow.
    let descriptor =
        trustline_factory_descriptor_collateral(&terms, TrustlineCollateral::FullReserve)
            .map_err(|e| TrustlineRefusal::BadTerms(e.to_string()))?;

    // Per-line token id: deterministic over the terms + caller salt + the
    // issuer's current replay nonce (a fresh nonce per committed turn, so
    // re-opening the same terms yields a fresh cell unless salted).
    let issuer_nonce = inner
        .ledger
        .get(&issuer)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    let mut hasher = blake3::Hasher::new_derive_key("dregg-trustline-token-v1");
    hasher.update(issuer.as_bytes());
    hasher.update(holder.as_bytes());
    hasher.update(&req.line.to_le_bytes());
    hasher.update(&issuer_nonce.to_le_bytes());
    if let Some(salt) = &req.salt {
        hasher.update(salt.as_bytes());
    }
    let token_id = *hasher.finalize().as_bytes();
    let trustline = CellId::derive_raw(&operator_pk, &token_id);
    if inner.ledger.get(&trustline).is_some() {
        return Err(TrustlineRefusal::BadTerms(format!(
            "trustline cell {} already exists (vary `salt`)",
            hex_encode(&trustline.0)
        )));
    }

    let mut turn_hashes = Vec::with_capacity(4);

    // Turn 1 — birth from the per-line factory.
    let params = FactoryCreationParams {
        mode: dregg_cell::CellMode::Hosted,
        program_vk: descriptor.child_program_vk,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: operator_pk,
    };
    turn_hashes.push(run_signed_turn(
        inner,
        issuer,
        issuer,
        "trustline_create",
        vec![Effect::CreateCellFromFactory {
            factory_vk: descriptor.factory_vk,
            owner_pubkey: operator_pk,
            token_id,
            params,
        }],
        None,
        Some(&descriptor),
    )?);

    // Turn 2 — THE FUNDED BIRTH: the issuer is REALLY debited; the full line
    // is escrowed in the trustline cell's own balance (an ordinary move —
    // conservation holds because it is a move, not a mint). ADOPT_TURN_FEE
    // extra is burned by turn 3, leaving exactly `line` escrowed.
    turn_hashes.push(run_signed_turn(
        inner,
        issuer,
        issuer,
        "trustline_fund",
        vec![Effect::Transfer {
            from: issuer,
            to: trustline,
            amount: req.line + ADOPT_TURN_FEE,
        }],
        None,
        None,
    )?);

    // Turn 3 — the adopt (cell-agent turn): the cell grants the operator
    // driving reach AND the holder their line capability — the bilateral
    // shape: the line IS a granted, attenuatable capability.
    let self_cap = |to: CellId| Effect::GrantCapability {
        from: trustline,
        to,
        cap: dregg_cell::CapabilityRef {
            target: trustline,
            slot: 0,
            permissions: dregg_cell::AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    };
    turn_hashes.push(run_signed_turn(
        inner,
        trustline,
        trustline,
        "trustline_adopt",
        vec![self_cap(issuer), self_cap(holder)],
        Some(ADOPT_TURN_FEE),
        None,
    )?);

    // Turn 4 — open: write the terms (the program pins them for life) and
    // step UNINIT → OPEN.
    let set = |index: u8, value: [u8; 32]| Effect::SetField {
        cell: trustline,
        index: index as usize,
        value,
    };
    turn_hashes.push(run_signed_turn(
        inner,
        issuer,
        trustline,
        "trustline_open",
        vec![
            set(TL_CEILING_SLOT, field_u64(req.line)),
            set(TL_ISSUER_SLOT, *issuer.as_bytes()),
            set(TL_HOLDER_SLOT, *holder.as_bytes()),
            set(TL_STATE_SLOT, field_u64(STATE_OPEN)),
            Effect::EmitEvent {
                cell: trustline,
                event: Event::new(
                    symbol("trustline-opened"),
                    vec![field_u64(req.line), *issuer.as_bytes(), *holder.as_bytes()],
                ),
            },
        ],
        None,
        None,
    )?);

    // (a) THE BIRTH EDGE — the first real caller of init_budget_coordinator:
    // seed the shared bounded counter from the just-committed funded birth.
    inner
        .init_budget_coordinator(trustline, req.line, vec![inner.silo_id], 0)
        .map_err(|e| TrustlineRefusal::Counter(format!("coordinator init failed: {e}")))?;

    let silo = inner.silo_id;
    let coordinator_remaining = inner
        .budget_coordinators
        .get(&trustline)
        .and_then(|c| c.remaining(&silo))
        .unwrap_or(0);
    let escrow = inner
        .ledger
        .get(&trustline)
        .map(|c| u64::try_from(c.state.balance()).unwrap_or(0))
        .unwrap_or(0);

    tracing::info!(
        trustline = %hex_encode(&trustline.0),
        holder = %req.holder,
        line = req.line,
        "trustline opened: escrow funded, coordinator seeded (ORGANS §1 birth edge)"
    );

    Ok(OpenResponse {
        trustline: hex_encode(&trustline.0),
        issuer: hex_encode(&issuer.0),
        holder: req.holder,
        line: req.line,
        escrow,
        coordinator_remaining,
        turn_hashes: turn_hashes.iter().map(|h| hex_encode(h)).collect(),
    })
}

/// `POST /trustline/draw` — (b) exercise the line: the Stingray counter gate
/// (`try_debit_fresh` = `Slice.tryDebit` + anti-replay) AND the executor's
/// installed-program tooth, in that order; a turn rejection unwinds the
/// counter reservation exactly (net counter unmoved on refusal).
async fn post_trustline_draw(
    State(state): State<NodeState>,
    Json(req): Json<DrawRequest>,
) -> Result<Json<DrawResponse>, TrustlineRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let trustline = CellId(hex_decode_32(&req.trustline).ok_or_else(|| {
        TrustlineRefusal::BadRequest(format!("malformed trustline cell id: {}", req.trustline))
    })?);
    require_operator_authority(inner, trustline)?;
    let (terms, _collateral, position) = resolve_trustline(inner, trustline)?;
    if !position.open {
        return Err(TrustlineRefusal::NotOpen);
    }
    // The holder must (still) hold their line capability — the bilateral
    // shape's exercise condition.
    let holder = CellId(terms.holder);
    if !inner
        .ledger
        .get(&holder)
        .map(|c| c.capabilities.has_access(&trustline))
        .unwrap_or(false)
    {
        return Err(TrustlineRefusal::NoCapability(
            "holder cell no longer holds the line capability".into(),
        ));
    }

    let digest = match &req.digest {
        Some(hex) => hex_decode_32(hex)
            .ok_or_else(|| TrustlineRefusal::BadRequest(format!("malformed draw digest: {hex}")))?,
        None => {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0);
            let mut hasher = blake3::Hasher::new_derive_key("dregg-trustline-draw-digest-v1");
            hasher.update(trustline.as_bytes());
            hasher.update(&position.drawn.to_le_bytes());
            hasher.update(&req.amount.to_le_bytes());
            hasher.update(&now.to_le_bytes());
            *hasher.finalize().as_bytes()
        }
    };

    // No-double-draw, FOREVER (Lean `no_double_draw_forever`): the node
    // registry carries digests across settle epochs (the slice's own
    // registry resets at rebalance).
    if inner.trustlines.digest_seen(&trustline, &digest) {
        return Err(TrustlineRefusal::DuplicateDraw);
    }
    // Route mirror of the line bound (the executor independently enforces).
    if req.amount > position.remaining {
        return Err(TrustlineRefusal::OverLine {
            remaining: position.remaining,
            requested: req.amount,
        });
    }

    // Gate 1 — the Stingray counter: Slice.tryDebit + the anti-replay leg
    // (Lean `draw_fires_iff_tryDebit`). Reserves the amount.
    ensure_coordinator(inner, trustline, &position)?;
    let silo = inner.silo_id;
    {
        let coordinator = inner
            .budget_coordinators
            .get_mut(&trustline)
            .expect("ensure_coordinator just installed it");
        coordinator
            .try_debit_fresh(silo, req.amount, digest)
            .map_err(|e| match e {
                BudgetError::DuplicateDebit { .. } => TrustlineRefusal::DuplicateDraw,
                other => TrustlineRefusal::Counter(other.to_string()),
            })?;
    }

    // Gate 2 — the executor tooth: the committed turn moves the cell's drawn
    // register under the installed program (`drawn ≤ ceiling` for life).
    let new_drawn = position.drawn + req.amount;
    let turn = run_signed_turn(
        inner,
        crate::executor_setup::local_agent_cell(inner),
        trustline,
        "trustline_draw",
        vec![
            Effect::SetField {
                cell: trustline,
                index: TL_DRAWN_SLOT as usize,
                value: field_u64(new_drawn),
            },
            Effect::SetField {
                cell: trustline,
                index: TL_DIGEST_SLOT as usize,
                value: digest,
            },
            Effect::EmitEvent {
                cell: trustline,
                event: Event::new(
                    symbol("trustline-draw"),
                    vec![digest, field_u64(req.amount), field_u64(new_drawn)],
                ),
            },
        ],
        None,
        None,
    );
    let turn_hash = match turn {
        Ok(h) => h,
        Err(refusal) => {
            // Unwind the counter reservation exactly (amount + digest): the
            // executor refused, so nothing committed and the digest stays
            // fresh for a retried draw.
            if let Some(coordinator) = inner.budget_coordinators.get_mut(&trustline) {
                let _ = coordinator.unwind_debit(silo, req.amount, &digest);
            }
            return Err(refusal);
        }
    };
    // Burn the digest FOREVER only after commit (durable-then-in-memory).
    record_digest_durable(inner, trustline, digest);

    let coordinator_remaining = inner
        .budget_coordinators
        .get(&trustline)
        .and_then(|c| c.remaining(&silo))
        .unwrap_or(0);
    // The two gates agree by construction; check it loudly.
    debug_assert_eq!(
        coordinator_remaining,
        terms.line - new_drawn,
        "coordinator remaining diverged from the cell's remaining line"
    );

    drop(s);
    Ok(Json(DrawResponse {
        trustline: req.trustline,
        digest: hex_encode(&digest),
        amount: req.amount,
        drawn: new_drawn,
        remaining: terms.line.saturating_sub(new_drawn),
        coordinator_remaining,
        turn_hash: hex_encode(&turn_hash),
    }))
}

/// `POST /trustline/repay` — restore the line: drawn down (never below the
/// settled floor — settled credit is hard money and cannot be repaid back),
/// counter refunded, digests stay burned (Lean `draw_repay_roundtrip` +
/// `repay_draws_fixed`).
async fn post_trustline_repay(
    State(state): State<NodeState>,
    Json(req): Json<RepayRequest>,
) -> Result<Json<RepayResponse>, TrustlineRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let trustline = CellId(hex_decode_32(&req.trustline).ok_or_else(|| {
        TrustlineRefusal::BadRequest(format!("malformed trustline cell id: {}", req.trustline))
    })?);
    require_operator_authority(inner, trustline)?;
    let (terms, _collateral, position) = resolve_trustline(inner, trustline)?;
    if !position.open {
        return Err(TrustlineRefusal::NotOpen);
    }
    let outstanding = position.drawn.saturating_sub(position.settled);
    if req.amount > outstanding {
        return Err(TrustlineRefusal::OverRepay {
            outstanding,
            requested: req.amount,
        });
    }

    let new_drawn = position.drawn - req.amount;
    let turn_hash = run_signed_turn(
        inner,
        crate::executor_setup::local_agent_cell(inner),
        trustline,
        "trustline_repay",
        vec![
            Effect::SetField {
                cell: trustline,
                index: TL_DRAWN_SLOT as usize,
                value: field_u64(new_drawn),
            },
            Effect::EmitEvent {
                cell: trustline,
                event: Event::new(
                    symbol("trustline-repay"),
                    vec![field_u64(req.amount), field_u64(new_drawn)],
                ),
            },
        ],
        None,
        None,
    )?;

    // The counter leg of repay: spent restores (digests stay burned).
    ensure_coordinator(inner, trustline, &position)?;
    let silo = inner.silo_id;
    if let Some(coordinator) = inner.budget_coordinators.get_mut(&trustline) {
        let _ = coordinator.refund(silo, req.amount);
    }
    let coordinator_remaining = inner
        .budget_coordinators
        .get(&trustline)
        .and_then(|c| c.remaining(&silo))
        .unwrap_or(0);
    debug_assert_eq!(
        coordinator_remaining,
        terms.line - new_drawn,
        "coordinator remaining diverged from the cell's remaining line"
    );

    drop(s);
    Ok(Json(RepayResponse {
        trustline: req.trustline,
        amount: req.amount,
        drawn: new_drawn,
        remaining: terms.line.saturating_sub(new_drawn),
        coordinator_remaining,
        turn_hash: hex_encode(&turn_hash),
    }))
}

/// `POST /trustline/settle` — (c) SETTLEMENT: the epoch close. The first
/// real caller of `collect_spending_certificates` + `rebalance_budgets`;
/// every returned `(agent, total_spent)` entry is applied back to the ledger
/// as an ordinary `Transfer` (escrow → holder) plus the cell's monotone
/// `settled` march. Balance-neutral: the hard pair is exactly conserved
/// (Lean `settlePay_conserves_hard`), and solvency is the program's
/// `settled ≤ drawn ≤ ceiling` teeth against the escrowed line.
///
/// A move the executor REJECTS after the rebalance is surfaced loudly AND
/// compensated in the same request (`StingrayCounter::restore_unapplied`):
/// the counter re-carries the unapplied amount so the two gates re-agree
/// immediately and the next settle re-attempts the payout.
async fn post_trustline_settle(
    State(state): State<NodeState>,
) -> Result<Json<SettleResponse>, TrustlineRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    if !inner.unlocked {
        return Err(TrustlineRefusal::Locked);
    }

    // 1. Epoch boundary: gather this silo's signed spending summaries.
    let certificates = inner.collect_spending_certificates();
    // 2. Reconcile and redistribute (version bump re-arms the per-turn
    //    BudgetGate seeding at the new epoch).
    let settlements = inner.rebalance_budgets(&certificates);

    // 3. Apply each settlement as a LEDGER MOVE.
    let mut applied = Vec::new();
    let mut failures = Vec::new();
    for (agent, total_spent) in settlements {
        let (terms, _collateral, position) = match resolve_trustline(inner, agent) {
            Ok(t) => t,
            Err(e) => {
                // A coordinator that is not a trustline cell settles outside
                // this organ (none exist today) — named, not silently eaten.
                failures.push(format!(
                    "agent {} spent {total_spent}: not a trustline cell ({})",
                    hex_encode(agent.as_bytes()),
                    e.detail()
                ));
                continue;
            }
        };
        let holder = CellId(terms.holder);
        let new_settled = position.settled + total_spent;
        match run_signed_turn(
            inner,
            crate::executor_setup::local_agent_cell(inner),
            agent,
            "trustline_settle",
            vec![
                Effect::SetField {
                    cell: agent,
                    index: TL_SETTLED_SLOT as usize,
                    value: field_u64(new_settled),
                },
                Effect::Transfer {
                    from: agent,
                    to: holder,
                    amount: total_spent,
                },
                Effect::EmitEvent {
                    cell: agent,
                    event: Event::new(
                        symbol("trustline-settle"),
                        vec![field_u64(total_spent), field_u64(new_settled)],
                    ),
                },
            ],
            None,
            None,
        ) {
            Ok(turn_hash) => {
                tracing::info!(
                    trustline = %hex_encode(agent.as_bytes()),
                    holder = %hex_encode(holder.as_bytes()),
                    amount = total_spent,
                    "trustline settlement applied as a ledger move (ORGANS §1 settlement edge)"
                );
                applied.push(SettlementEntry {
                    trustline: hex_encode(agent.as_bytes()),
                    holder: hex_encode(holder.as_bytes()),
                    amount: total_spent,
                    turn_hash: hex_encode(&turn_hash),
                });
            }
            Err(e) => {
                // Counter and ledger diverged — a REAL soundness finding,
                // surfaced loudly, never papered.
                tracing::error!(
                    trustline = %hex_encode(agent.as_bytes()),
                    amount = total_spent,
                    error = %e.detail(),
                    "trustline settlement move REJECTED after rebalance — counter/ledger divergence"
                );
                failures.push(format!(
                    "trustline {} settlement of {total_spent} rejected: {}",
                    hex_encode(agent.as_bytes()),
                    e.detail()
                ));
                // COMPENSATE in the SAME request (the cell is the truth; the
                // shadow resyncs): the rebalance recorded a settlement the
                // ledger refused, so void the counter-side record — restore
                // the unapplied amount to the counter's balance and re-debit
                // it into the fresh epoch slice. This lands the counter in
                // exactly the §10b rebuild shape (Lean `epochSlice`:
                // balance = line − settled(cell), spent = drawn − settled(cell))
                // a restart would produce, and the NEXT settle re-attempts
                // the move instead of silently dropping the holder's payout.
                let silo = inner.silo_id;
                match inner.budget_coordinators.get_mut(&agent) {
                    Some(coordinator) => {
                        let digest =
                            settle_unapplied_digest(&agent, total_spent, coordinator.version);
                        match coordinator.restore_unapplied(silo, total_spent, digest) {
                            Ok(()) => {
                                // Registry ⊇ slice-debits: the compensation
                                // digest is burned forever like any other.
                                record_digest_durable(inner, agent, digest);
                                tracing::warn!(
                                    trustline = %hex_encode(agent.as_bytes()),
                                    amount = total_spent,
                                    "rejected settlement compensated: unapplied amount re-carried \
                                     by the counter; settlement will be re-attempted next epoch"
                                );
                            }
                            Err(err) => {
                                tracing::error!(
                                    trustline = %hex_encode(agent.as_bytes()),
                                    amount = total_spent,
                                    error = %err,
                                    "settlement compensation FAILED — counter/ledger divergence \
                                     persists until a restart rebuild"
                                );
                                failures.push(format!(
                                    "trustline {} compensation of {total_spent} failed: {err}",
                                    hex_encode(agent.as_bytes()),
                                ));
                            }
                        }
                    }
                    None => failures.push(format!(
                        "trustline {} compensation of {total_spent} skipped: no coordinator",
                        hex_encode(agent.as_bytes()),
                    )),
                }
                // The two-gates identity, restored within this request: the
                // failed turn moved nothing on the cell, so the pre-settle
                // position still reads the cell truth.
                debug_assert_eq!(
                    inner
                        .budget_coordinators
                        .get(&agent)
                        .and_then(|c| c.remaining(&silo)),
                    Some(terms.line - position.drawn),
                    "coordinator remaining diverged from the cell's remaining line \
                     after settle-rejection compensation"
                );
            }
        }
    }

    let epoch = inner.budget_epoch;
    drop(s);
    Ok(Json(SettleResponse {
        epoch,
        certificates: certificates.len(),
        settlements: applied,
        failures,
    }))
}

/// `POST /trustline/close` — (d) THE TERMINAL EDGE: settle-then-return, one
/// turn, then the line is INERT (the program's transition table has no row out
/// of `TL_STATE_CLOSED`, so every later touch refuses).
///
/// * **fullReserve**: any outstanding draw (`drawn − settled`) is settled to
///   the holder (`settled := drawn` + escrow → holder), the RESIDUAL escrow
///   (`escrow − outstanding`) returns to the issuer, and the state slot steps
///   to [`TL_STATE_CLOSED`]. The hard column is exactly conserved (two moves,
///   no mint).
/// * **pureCredit**: there is no escrow to return; closing demands a clean
///   position (`outstanding == 0`) — the issuer cannot debit the holder as a
///   side effect of closing. Settle/repay first.
///
/// The coordinator shadow is retired with the line (the cell is the truth and
/// is now inert).
async fn post_trustline_close(
    State(state): State<NodeState>,
    Json(req): Json<CloseRequest>,
) -> Result<Json<CloseResponse>, TrustlineRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let trustline = CellId(hex_decode_32(&req.trustline).ok_or_else(|| {
        TrustlineRefusal::BadRequest(format!("malformed trustline cell id: {}", req.trustline))
    })?);
    require_operator_authority(inner, trustline)?;
    let (terms, collateral, position) = resolve_trustline(inner, trustline)?;
    if !position.open {
        return Err(TrustlineRefusal::NotOpen);
    }
    let outstanding = position.drawn.saturating_sub(position.settled);

    let mut effects: Vec<Effect> = Vec::new();
    let (settled_to_holder, residual_to_issuer) = match collateral {
        TrustlineCollateral::FullReserve => {
            if outstanding > 0 {
                effects.push(Effect::SetField {
                    cell: trustline,
                    index: TL_SETTLED_SLOT as usize,
                    value: field_u64(position.drawn),
                });
                effects.push(Effect::Transfer {
                    from: trustline,
                    to: CellId(terms.holder),
                    amount: outstanding,
                });
            }
            let residual = position.escrow.saturating_sub(outstanding);
            if residual > 0 {
                effects.push(Effect::Transfer {
                    from: trustline,
                    to: CellId(terms.issuer),
                    amount: residual,
                });
            }
            (outstanding, residual)
        }
        TrustlineCollateral::PureCredit => {
            if outstanding > 0 {
                return Err(TrustlineRefusal::OutstandingAtClose { outstanding });
            }
            (0, 0)
        }
    };
    effects.push(Effect::SetField {
        cell: trustline,
        index: TL_STATE_SLOT as usize,
        value: field_u64(TL_STATE_CLOSED),
    });
    effects.push(Effect::EmitEvent {
        cell: trustline,
        event: Event::new(
            symbol("trustline-closed"),
            vec![field_u64(settled_to_holder), field_u64(residual_to_issuer)],
        ),
    });

    let turn_hash = run_signed_turn(
        inner,
        crate::executor_setup::local_agent_cell(inner),
        trustline,
        "trustline_close",
        effects,
        None,
        None,
    )?;

    // The line is terminal: retire its bounded-counter shadow (the inert cell
    // is the truth from here, and no further draw/settle can occur).
    inner.budget_coordinators.remove(&trustline);

    tracing::info!(
        trustline = %hex_encode(&trustline.0),
        collateral = collateral_name(collateral),
        settled_to_holder,
        residual_to_issuer,
        "trustline closed: settled then returned residual; line is inert (ORGANS §1 terminal edge)"
    );

    drop(s);
    Ok(Json(CloseResponse {
        trustline: req.trustline,
        collateral: collateral_name(collateral).to_string(),
        settled_to_holder,
        residual_to_issuer,
        turn_hash: hex_encode(&turn_hash),
    }))
}

/// `GET /trustline/status/{cell}` — the live position + the counter shadow.
async fn get_trustline_status(
    State(state): State<NodeState>,
    AxumPath(cell_hex): AxumPath<String>,
) -> Result<Json<StatusResponse>, TrustlineRefusal> {
    let s = state.write().await;
    let inner = &*s;

    let trustline = CellId(hex_decode_32(&cell_hex).ok_or_else(|| {
        TrustlineRefusal::BadRequest(format!("malformed trustline cell id: {cell_hex}"))
    })?);
    let (terms, collateral, position) = resolve_trustline(inner, trustline)?;
    let silo = inner.silo_id;
    let coordinator = inner.budget_coordinators.get(&trustline);
    Ok(Json(StatusResponse {
        trustline: cell_hex,
        issuer: hex_encode(&terms.issuer),
        holder: hex_encode(&terms.holder),
        collateral: collateral_name(collateral).to_string(),
        position,
        coordinator_remaining: coordinator.and_then(|c| c.remaining(&silo)),
        coordinator_version: coordinator.map(|c| c.version),
    }))
}

// =============================================================================
// Tests — the e2e weld on the real router + executor + Stingray coordinator
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    const LINE: u64 = 100;

    /// A node state with a funded operator agent cell and a holder cell on
    /// the live ledger (the same shape a faucet-funded devnet node has).
    async fn funded_state() -> (NodeState, CellId, tempfile::TempDir) {
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        let holder = {
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
            let holder_pk = blake3::derive_key("trustline-node-test-v1", b"holder");
            let holder_cell = dregg_cell::Cell::with_balance(holder_pk, [0u8; 32], 500);
            let holder = holder_cell.id();
            s.ledger.insert_cell(holder_cell).expect("holder inserts");
            holder
        };
        (state, holder, dir)
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

    async fn open_line(state: &NodeState, holder: CellId, line: u64) -> CellId {
        let (status, json) = post_json(
            state,
            "/trustline/open",
            serde_json::json!({ "holder": hex_encode(&holder.0), "line": line }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "open must succeed: {json}");
        CellId(hex_decode_32(json["trustline"].as_str().unwrap()).unwrap())
    }

    async fn balance(state: &NodeState, cell: CellId) -> i128 {
        let s = state.write().await;
        s.ledger
            .get(&cell)
            .map(|c| c.state.balance() as i128)
            .unwrap_or(0)
    }

    async fn tl_slot(state: &NodeState, cell: CellId, index: u8) -> u64 {
        let s = state.write().await;
        slot_u64(s.ledger.get(&cell).expect("trustline cell"), index)
    }

    async fn coordinator_remaining(state: &NodeState, cell: CellId) -> Option<u64> {
        let s = state.write().await;
        let silo = s.silo_id;
        s.budget_coordinators
            .get(&cell)
            .and_then(|c| c.remaining(&silo))
    }

    /// THE INVARIANT (the code's own two-gates debug_assert, made total over
    /// the §10b epochSlice shape): at every settle outcome the coordinator
    /// shadow ≡ the cell truth —
    ///   coordinator.total_balance == line − settled(cell)
    ///   coordinator remaining     == line − drawn(cell)
    /// (for f=0/n=1 the two together pin ceiling == line − settled and
    /// spent == drawn − settled, i.e. Lean `SLine.epochSlice` exactly).
    async fn assert_shadow_matches_cell(state: &NodeState, tl: CellId) {
        let s = state.write().await;
        let silo = s.silo_id;
        let cell = s.ledger.get(&tl).expect("trustline cell");
        let line = slot_u64(cell, TL_CEILING_SLOT);
        let drawn = slot_u64(cell, TL_DRAWN_SLOT);
        let settled = slot_u64(cell, TL_SETTLED_SLOT);
        let coordinator = s.budget_coordinators.get(&tl).expect("coordinator");
        assert_eq!(
            coordinator.total_balance,
            line - settled,
            "coordinator balance must equal line − settled(cell)"
        );
        assert_eq!(
            coordinator.remaining(&silo),
            Some(line - drawn),
            "coordinator remaining must equal line − drawn(cell): the two gates agree"
        );
    }

    /// Restart-shaped rebuild: drop the in-memory shadow (exactly what a
    /// process restart loses) and let `ensure_coordinator` rebuild it from
    /// the cell registers.
    async fn restart_shaped_rebuild(state: &NodeState, tl: CellId) {
        let mut s = state.write().await;
        s.budget_coordinators.remove(&tl);
        let (_, _, position) = resolve_trustline(&s, tl).expect("trustline resolves");
        ensure_coordinator(&mut s, tl, &position).expect("rebuild succeeds");
    }

    fn digest_hex(n: u64) -> String {
        hex_encode(
            blake3::Hasher::new_derive_key("trustline-node-test-digest-v1")
                .update(&n.to_le_bytes())
                .finalize()
                .as_bytes(),
        )
    }

    // ── (a) the birth edge: funded open seeds the coordinator ───────────────

    #[tokio::test]
    async fn open_escrows_line_seeds_coordinator_and_grants_holder() {
        let (state, holder, _dir) = funded_state().await;
        let operator = {
            let s = state.write().await;
            crate::executor_setup::local_agent_cell(&s)
        };
        let funder_before = balance(&state, operator).await;

        let tl = open_line(&state, holder, LINE).await;

        // THE FUNDER IS DEBITED (a real ledger move, not a mint) and the
        // escrow holds exactly the line.
        assert_eq!(balance(&state, tl).await, LINE as i128);
        let funder_after = balance(&state, operator).await;
        assert!(
            funder_before - funder_after >= (LINE + ADOPT_TURN_FEE) as i128,
            "funder must be debited the escrow + adopt fee"
        );

        // THE BIRTH EDGE: init_budget_coordinator was CALLED — the stillborn
        // joint is welded. The counter agrees with the cell.
        assert_eq!(coordinator_remaining(&state, tl).await, Some(LINE));

        // THE BILATERAL SHAPE: the holder holds the line as a capability.
        {
            let s = state.write().await;
            assert!(
                s.ledger.get(&holder).unwrap().capabilities.has_access(&tl),
                "holder must hold the line capability"
            );
        }
        assert_eq!(tl_slot(&state, tl, TL_CEILING_SLOT).await, LINE);
        assert_eq!(tl_slot(&state, tl, TL_STATE_SLOT).await, STATE_OPEN);
    }

    // ── (b) draw: within line / over line / double-draw ─────────────────────

    #[tokio::test]
    async fn draw_within_line_over_line_and_replay() {
        let (state, holder, _dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;
        let tl_hex = hex_encode(&tl.0);

        // Within the line: succeeds; cell register and counter both move.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 30, "digest": digest_hex(1) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["drawn"].as_u64(), Some(30));
        assert_eq!(json["coordinator_remaining"].as_u64(), Some(70));
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);

        // Beyond the line: refused, both counters unmoved.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 80, "digest": digest_hex(2) }),
        )
        .await;
        assert_eq!(status, StatusCode::PAYMENT_REQUIRED, "{json}");
        assert_eq!(json["reason"], "over-line");
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);
        assert_eq!(coordinator_remaining(&state, tl).await, Some(70));

        // Double-draw of the SAME digest: refused, counters unmoved.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 5, "digest": digest_hex(1) }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "duplicate-draw");
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);
        assert_eq!(coordinator_remaining(&state, tl).await, Some(70));

        // The boundary draw (exactly the remaining 70) admits — tight bound.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 70, "digest": digest_hex(3) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["remaining"].as_u64(), Some(0));
        assert_eq!(coordinator_remaining(&state, tl).await, Some(0));
    }

    // ── repay then redraw ────────────────────────────────────────────────────

    #[tokio::test]
    async fn repay_restores_line_redraw_succeeds_digests_stay_burned() {
        let (state, holder, _dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;
        let tl_hex = hex_encode(&tl.0);

        let (status, _) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 30, "digest": digest_hex(1) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK);

        // Repay 10: line restores, counter refunds.
        let (status, json) = post_json(
            &state,
            "/trustline/repay",
            serde_json::json!({ "trustline": tl_hex, "amount": 10 }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["drawn"].as_u64(), Some(20));
        assert_eq!(json["remaining"].as_u64(), Some(80));
        assert_eq!(coordinator_remaining(&state, tl).await, Some(80));

        // Redraw on the restored line succeeds (fresh digest)…
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 80, "digest": digest_hex(2) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["drawn"].as_u64(), Some(100));

        // …but the spent digest stays burned even after repayment.
        let (status, json) = post_json(
            &state,
            "/trustline/repay",
            serde_json::json!({ "trustline": tl_hex, "amount": 100 }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 5, "digest": digest_hex(1) }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");

        // Over-repay is refused (nothing outstanding).
        let (status, json) = post_json(
            &state,
            "/trustline/repay",
            serde_json::json!({ "trustline": tl_hex, "amount": 1 }),
        )
        .await;
        assert_eq!(status, StatusCode::PAYMENT_REQUIRED, "{json}");
        assert_eq!(json["reason"], "over-repay");
    }

    // ── (c) settlement: rebalance applied back to the ledger as moves ───────

    #[tokio::test]
    async fn settle_applies_net_position_as_ledger_move_conserved() {
        let (state, holder, _dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;
        let tl_hex = hex_encode(&tl.0);

        // Net position: draw 30, repay 10 → 20 outstanding.
        let (s1, _) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 30, "digest": digest_hex(1) }),
        )
        .await;
        let (s2, _) = post_json(
            &state,
            "/trustline/repay",
            serde_json::json!({ "trustline": tl_hex, "amount": 10 }),
        )
        .await;
        assert_eq!((s1, s2), (StatusCode::OK, StatusCode::OK));

        let escrow_before = balance(&state, tl).await;
        let holder_before = balance(&state, holder).await;

        // THE SETTLEMENT EDGE: collect_spending_certificates +
        // rebalance_budgets get their first real caller, and the result is
        // applied back to the ledger as an ordinary move.
        let (status, json) = post_json(&state, "/trustline/settle", serde_json::json!({})).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["certificates"].as_u64(), Some(1));
        assert_eq!(
            json["failures"].as_array().map(Vec::len),
            Some(0),
            "no counter/ledger divergence: {json}"
        );
        let settlements = json["settlements"].as_array().unwrap();
        assert_eq!(settlements.len(), 1);
        assert_eq!(settlements[0]["amount"].as_u64(), Some(20));
        assert_eq!(settlements[0]["holder"], hex_encode(&holder.0));

        // The ledger move MATCHES the net position and the pair conserves.
        let escrow_after = balance(&state, tl).await;
        let holder_after = balance(&state, holder).await;
        assert_eq!(holder_after - holder_before, 20, "holder receives net");
        assert_eq!(escrow_before - escrow_after, 20, "escrow pays net");
        assert_eq!(
            escrow_after + holder_after,
            escrow_before + holder_before,
            "total conserved across the settlement move"
        );
        assert_eq!(tl_slot(&state, tl, TL_SETTLED_SLOT).await, 20);

        // Post-settle the counter re-arms at the new epoch and still agrees
        // with the cell: remaining = line − drawn.
        assert_eq!(coordinator_remaining(&state, tl).await, Some(LINE - 20));
        assert_shadow_matches_cell(&state, tl).await;
        {
            let s = state.write().await;
            assert_eq!(s.budget_coordinators.get(&tl).unwrap().version, 1);
        }

        // Settled credit cannot be repaid back.
        let (status, json) = post_json(
            &state,
            "/trustline/repay",
            serde_json::json!({ "trustline": tl_hex, "amount": 1 }),
        )
        .await;
        assert_eq!(status, StatusCode::PAYMENT_REQUIRED, "{json}");

        // A second settle with no new spending is a clean no-op.
        let (status, json) = post_json(&state, "/trustline/settle", serde_json::json!({})).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["settlements"].as_array().map(Vec::len), Some(0));
        assert_shadow_matches_cell(&state, tl).await;

        // The line keeps working across epochs: a post-settle draw debits
        // the fresh slice and the cell agrees.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 50, "digest": digest_hex(2) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["drawn"].as_u64(), Some(70));
        assert_eq!(coordinator_remaining(&state, tl).await, Some(LINE - 70));
        assert_shadow_matches_cell(&state, tl).await;
    }

    // ── the executor tooth, exercised directly ───────────────────────────────

    #[tokio::test]
    async fn executor_rejects_over_line_debit_directly_counter_unmoved() {
        let (state, holder, _dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;

        let mut s = state.write().await;
        let operator = crate::executor_setup::local_agent_cell(&s);
        // A raw turn writing drawn = ceiling + 1 violates the installed
        // program (drawn ≤ ceiling) and is REJECTED by the authoritative
        // executor — independent of any route admission.
        let over = run_signed_turn(
            &mut s,
            operator,
            tl,
            "trustline_draw",
            vec![Effect::SetField {
                cell: tl,
                index: TL_DRAWN_SLOT as usize,
                value: field_u64(LINE + 1),
            }],
            None,
            None,
        );
        match over {
            Err(TrustlineRefusal::TurnRejected(_)) => {}
            other => panic!("executor must reject over-line debit, got {other:?}"),
        }
        assert_eq!(
            slot_u64(s.ledger.get(&tl).unwrap(), TL_DRAWN_SLOT),
            0,
            "rejected turn must not move the counter"
        );

        // The ceiling register is immutable (ceiling_immutable_forever).
        let tamper = run_signed_turn(
            &mut s,
            operator,
            tl,
            "trustline_tamper",
            vec![Effect::SetField {
                cell: tl,
                index: TL_CEILING_SLOT as usize,
                value: field_u64(LINE * 10),
            }],
            None,
            None,
        );
        assert!(matches!(tamper, Err(TrustlineRefusal::TurnRejected(_))));
        assert_eq!(slot_u64(s.ledger.get(&tl).unwrap(), TL_CEILING_SLOT), LINE);
    }

    #[tokio::test]
    async fn draw_against_non_trustline_cell_refused() {
        let (state, holder, _dir) = funded_state().await;
        // The holder cell is a perfectly ordinary cell — not a trustline.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({
                "trustline": hex_encode(&holder.0),
                "amount": 1,
                "digest": digest_hex(1)
            }),
        )
        .await;
        // The operator holds no capability over it → fail-closed before any
        // trustline interpretation is even attempted.
        assert_eq!(status, StatusCode::FORBIDDEN, "{json}");
        assert_eq!(json["reason"], "no-capability");
    }

    // ── RESIDUE 1 closed: the rebuild digest enters the FOREVER registry ─────

    #[tokio::test]
    async fn rebuild_digest_enters_forever_registry_and_refuses_identically() {
        let (state, holder, _dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;
        let tl_hex = hex_encode(&tl.0);

        // An outstanding position to rebuild: draw 30.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 30, "digest": digest_hex(1) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");

        // Restart-shaped rebuild #1: the shadow is rebuilt from the cell
        // (drawn = 30, settled = 0) under the deterministic rebuild digest.
        restart_shaped_rebuild(&state, tl).await;
        let d_rebuild = shadow_rebuild_digest(&tl, 30, 0);
        {
            let s = state.write().await;
            assert!(
                s.trustlines.digest_seen(&tl, &d_rebuild),
                "the rebuild digest must enter the forever registry at rebuild time"
            );
            // The closed invariant: registry ⊇ slice-debits.
            let silo = s.silo_id;
            let slice = &s.budget_coordinators.get(&tl).unwrap().silo_states[&silo];
            for d in &slice.debits {
                assert!(
                    s.trustlines.digest_seen(&tl, d),
                    "forever registry must cover every slice debit"
                );
            }
        }
        assert_shadow_matches_cell(&state, tl).await;

        // A client draw replaying the rebuild digest refuses DuplicateDraw,
        // counters unmoved.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({
                "trustline": tl_hex, "amount": 5, "digest": hex_encode(&d_rebuild)
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "duplicate-draw");
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);
        assert_eq!(coordinator_remaining(&state, tl).await, Some(70));

        // Restart-shaped rebuild #2 (same position → the SAME digest): the
        // refusal is IDENTICAL after further rebuilds.
        restart_shaped_rebuild(&state, tl).await;
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({
                "trustline": tl_hex, "amount": 5, "digest": hex_encode(&d_rebuild)
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "duplicate-draw");
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);
        assert_eq!(coordinator_remaining(&state, tl).await, Some(70));

        // And ACROSS a settle epoch (the slice's own debit list resets at
        // rebalance — only the forever registry carries the digest): still
        // the identical refusal.
        let (status, json) = post_json(&state, "/trustline/settle", serde_json::json!({})).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["failures"].as_array().map(Vec::len), Some(0));
        assert_shadow_matches_cell(&state, tl).await;
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({
                "trustline": tl_hex, "amount": 5, "digest": hex_encode(&d_rebuild)
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "duplicate-draw");
        assert_shadow_matches_cell(&state, tl).await;
    }

    // ── RESIDUE 2 closed: a rejected settle move is compensated in-request ───

    #[tokio::test]
    async fn settle_rejected_move_compensates_counter_and_reattempts_next_epoch() {
        let (state, holder, _dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;
        let tl_hex = hex_encode(&tl.0);

        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 30, "digest": digest_hex(1) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_shadow_matches_cell(&state, tl).await;

        // Tamper the escrow below the settle amount (the harness shape of the
        // executor-tooth test): the escrow→holder move MUST be rejected.
        {
            let mut s = state.write().await;
            s.ledger.get_mut(&tl).unwrap().state.set_balance(5);
        }
        let holder_before = balance(&state, holder).await;

        // TOTAL-FAILURE settle: loud failure surfaced, nothing applied, the
        // cell truth unmoved — and the counter compensated IN THIS REQUEST.
        let (status, json) = post_json(&state, "/trustline/settle", serde_json::json!({})).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(
            json["settlements"].as_array().map(Vec::len),
            Some(0),
            "no settlement applied: {json}"
        );
        let failures = json["failures"].as_array().unwrap();
        assert_eq!(failures.len(), 1, "the loud failure surface stays: {json}");
        assert!(failures[0].as_str().unwrap().contains("rejected"), "{json}");
        // The cell truth is unmoved (the rejected turn committed nothing).
        assert_eq!(tl_slot(&state, tl, TL_SETTLED_SLOT).await, 0);
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);
        assert_eq!(balance(&state, holder).await, holder_before);
        // THE INVARIANT, restored in the same request (without compensation
        // the counter's balance would read line − drawn = 70 ≠ line − settled).
        assert_shadow_matches_cell(&state, tl).await;
        // The compensation digest is burned in the forever registry and the
        // epoch did not regress.
        {
            let s = state.write().await;
            let coordinator = s.budget_coordinators.get(&tl).unwrap();
            assert_eq!(coordinator.version, 1, "epoch advanced exactly once");
            let d_comp = settle_unapplied_digest(&tl, 30, 1);
            assert!(
                s.trustlines.digest_seen(&tl, &d_comp),
                "compensation digest must enter the forever registry"
            );
        }
        // A client draw replaying the compensation digest refuses.
        let d_comp = settle_unapplied_digest(&tl, 30, 1);
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({
                "trustline": tl_hex, "amount": 5, "digest": hex_encode(&d_comp)
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "duplicate-draw");
        assert_shadow_matches_cell(&state, tl).await;

        // Heal the escrow; the NEXT settle RE-ATTEMPTS the unapplied move
        // (the counter re-carried it) and it now applies.
        {
            let mut s = state.write().await;
            s.ledger
                .get_mut(&tl)
                .unwrap()
                .state
                .set_balance(LINE as i64);
        }
        let escrow_before = balance(&state, tl).await;
        let (status, json) = post_json(&state, "/trustline/settle", serde_json::json!({})).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(
            json["failures"].as_array().map(Vec::len),
            Some(0),
            "re-attempt applies cleanly: {json}"
        );
        let settlements = json["settlements"].as_array().unwrap();
        assert_eq!(settlements.len(), 1, "{json}");
        assert_eq!(settlements[0]["amount"].as_u64(), Some(30));
        // SUCCESS branch of the invariant + the ledger pair conserves.
        assert_eq!(tl_slot(&state, tl, TL_SETTLED_SLOT).await, 30);
        assert_eq!(balance(&state, holder).await, holder_before + 30);
        assert_eq!(balance(&state, tl).await, escrow_before - 30);
        assert_shadow_matches_cell(&state, tl).await;

        // PARTIAL-OUTCOME epoch: new spending settles normally afterwards —
        // the compensation machinery left no residue.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 10, "digest": digest_hex(2) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_shadow_matches_cell(&state, tl).await;
        let (status, json) = post_json(&state, "/trustline/settle", serde_json::json!({})).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["failures"].as_array().map(Vec::len), Some(0));
        let settlements = json["settlements"].as_array().unwrap();
        assert_eq!(settlements.len(), 1, "{json}");
        assert_eq!(settlements[0]["amount"].as_u64(), Some(10));
        assert_eq!(tl_slot(&state, tl, TL_SETTLED_SLOT).await, 40);
        assert_shadow_matches_cell(&state, tl).await;
    }

    // ── persistence: the forever registry survives the restart ──────────────

    /// THE RESTART TEST (docs/PERSISTENCE.md): a committed draw digest is
    /// burned durably, so a brand-new process over the same data dir still
    /// refuses the replay — the deployed counterpart of Lean
    /// `draw_replay_refused_across_epochs` holds across process lifetimes,
    /// not only within one.
    #[tokio::test]
    async fn draw_digest_refused_across_restart() {
        let (state, holder, dir) = funded_state().await;
        let tl = open_line(&state, holder, LINE).await;
        let tl_hex = hex_encode(&tl.0);
        let digest = hex_decode_32(&digest_hex(9)).unwrap();

        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 30, "digest": digest_hex(9) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");

        // Capture the cells: the test ledger has no checkpoint, so the reborn
        // node reseeds them (the registries are the subject here, the ledger
        // recovery path has its own tests + Lean twin CrashRecovery.lean).
        let (tl_cell, holder_cell, op_cell) = {
            let s = state.write().await;
            let operator = crate::executor_setup::local_agent_cell(&s);
            (
                s.ledger.get(&tl).expect("trustline cell").clone(),
                s.ledger.get(&holder).expect("holder cell").clone(),
                s.ledger.get(&operator).expect("operator cell").clone(),
            )
        };

        // THE RESTART: every in-memory registry dies with the process.
        drop(state);

        let state = NodeState::new(dir.path(), vec![]).expect("reborn node state");
        {
            let mut s = state.write().await;
            s.unlocked = true;
            // The registry was reloaded from the durable forever-digest table.
            assert!(
                s.trustlines.digest_seen(&tl, &digest),
                "burned digest must survive the restart in the registry"
            );
            assert!(
                s.store
                    .forever_digest_seen(
                        dregg_persist::tables::NS_TRUSTLINE_DIGEST,
                        tl.as_bytes(),
                        &digest,
                    )
                    .expect("durable lookup"),
                "burned digest must be in the durable table"
            );
            let _ = s.ledger.insert_cell(tl_cell);
            let _ = s.ledger.insert_cell(holder_cell);
            let _ = s.ledger.insert_cell(op_cell);
        }

        // The replayed draw refuses END TO END through the reborn node.
        let (status, json) = post_json(
            &state,
            "/trustline/draw",
            serde_json::json!({ "trustline": tl_hex, "amount": 5, "digest": digest_hex(9) }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "duplicate-draw");
        // And the refusal changed nothing: drawn register unmoved.
        assert_eq!(tl_slot(&state, tl, TL_DRAWN_SLOT).await, 30);
    }
}
