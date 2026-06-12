//! Equivocation court service — the node-side half of the ORGANS §5
//! adjudication weld (CONSENSUS-FLEX §7: slash as a MOVE from the bond well).
//!
//! The federation legs already exist: the evidence wire value
//! (`blocklace/src/evidence.rs`), the `validEquivocation` predicate atom and
//! the registry-level court (`federation/src/court.rs` —
//! [`EquivocationCourt::resolve`] slashes [`AdmissionRegistry`] bonds and
//! burns the order-insensitive evidence digest). What dead-ended was the
//! VALUE leg: the registry's `amount` was a number with no cell behind it,
//! so "slash" burned bookkeeping, not stake. This module is that weld:
//!
//! * **BOND AS ESCROW** (`POST /court/bond`): posting a bond escrows the
//!   stake in a real BOND CELL on the live ledger (an ordinary conserving
//!   `Transfer` from the operator's agent cell through the authoritative
//!   executor — the trustline funded-birth shape), registers the SIGNED
//!   [`Bond`] in the court's [`AdmissionRegistry`] (a forged signature
//!   refuses before any value moves), and binds strand-key → bond-cell in
//!   the [`CourtLedger`]. Invariant: bond-cell escrow == registry
//!   `bond_amount` at every reachable state.
//! * **SLASH AS A MOVE** (`POST /court/evidence`): a verifying exhibit
//!   ([`EvidenceOfEquivocation`], witness-first — the exhibit IS the
//!   authority, no vote, no unlock requirement) drives ONE executor turn
//!   moving the whole bond out of the bond cell (conserved: to the
//!   genesis fee well when configured, else to the canonical UNSPENDABLE
//!   slash sink — a cell whose "public key" is a hash output nobody holds
//!   a scalar for), and only after that turn COMMITS does
//!   [`EquivocationCourt::resolve`] burn the digest + slash the registry.
//!   No-double-resolve: the burned digest refuses re-submission in either
//!   block order (the trustline forever-registry discipline). Every
//!   refusal — malformed/forged evidence, already-resolved, nothing at
//!   stake, executor rejection — changes NO state.
//! * **THE GOSSIP HOOK** ([`slash_from_proof`]): lace-detected fork
//!   evidence propagated by `blocklace_sync` no longer stops at
//!   constitution auto-evict — every retained [`EquivocationProof`] is
//!   reduced to the wire value and fed through the SAME slash path, so a
//!   bonded equivocator caught by ANY peer's push loses its stake on this
//!   node without an operator in the loop.
//!
//! The predicate atom is installed on every node executor
//! (`executor_setup::configure_turn_executor` calls
//! [`dregg_federation::court::register_equivocation_court`]), so cell
//! programs / turn admission can gate on `validEquivocation(ev, strand)`
//! independently of these routes.
//!
//! ## Honest residues (named, with their lanes)
//!
//! * The bond cell is a plain operator-owned cell (the trustline escrow
//!   shape), not yet an obligation-factory cell with a program tooth
//!   pinning "only the slash turn may move this balance" — that uplift
//!   rides the obligation-blueprint lane (`cell/src/blueprint.rs`).
//! * The court ledger (burned digests + registry + bindings) is in-memory,
//!   like the trustline registry; persistence rides the same lane.
//! * The court's registry is the BOND/value leg of admission. tau-side
//!   exclusion of equivocators already flows through the constitution's
//!   auto-evict (`blocklace_sync`); collapsing the two admission carriers
//!   into one is the ORGANS §5 / CONSENSUS-FLEX §5 membership-cell lane.

use std::collections::HashMap;

use axum::extract::{Path as AxumPath, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};

use dregg_blocklace::evidence::EvidenceOfEquivocation;
use dregg_blocklace::finality::EquivocationProof;
use dregg_cell::CellId;
use dregg_federation::admission::{AdmissionRegistry, Bond};
use dregg_federation::court::EquivocationCourt;
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_turn::Effect;
use dregg_turn::action::{Event, symbol};

use crate::state::{NodeState, NodeStateInner};
use crate::trustline_service::{field_u64, hex_decode_32, hex_encode, run_signed_turn};

// =============================================================================
// The court ledger (lives inside NodeStateInner)
// =============================================================================

/// The default minimum-bond floor for the node court's admission registry
/// (the STAKE path threshold; a smaller bond is still escrowed and slashable,
/// it just does not admit).
pub const DEFAULT_MIN_BOND: u64 = 100;

/// Domain for the deterministic bond-cell token id (one bond cell per
/// (operator, strand) pair — re-bonding after a slash reuses the cell).
const BOND_CELL_DOMAIN: &str = "dregg-court-bond-cell-v1";

/// Domain for the canonical slash sink (the conserved-but-unspendable burn
/// well used when no genesis fee well is configured).
const SLASH_SINK_DOMAIN: &str = "dregg-court-slash-sink-v1";

/// Node-held adjudication state: the witness-first court (burned evidence
/// digests), the slashable admission registry (the bonds the court resolves
/// against), and the strand-key → bond-cell bindings that give each
/// registry bond its VALUE carrier on the live ledger.
#[derive(Debug)]
pub struct CourtLedger {
    /// The federation court: burned (resolved) evidence digests — the
    /// forever no-double-resolve set.
    pub court: EquivocationCourt,
    /// The slashable bonds (and the admission verdicts they buy). Seeds
    /// empty: the node court tracks ECONOMIC standing only; tau membership
    /// is the constitution's (see module doc, residue 3).
    pub registry: AdmissionRegistry,
    /// strand key → the cell escrowing that strand's bond.
    bond_cells: HashMap<[u8; 32], CellId>,
}

impl Default for CourtLedger {
    fn default() -> Self {
        Self {
            court: EquivocationCourt::new(),
            // vouch_threshold 1 with no vouches fed ⇒ the vouch path is
            // inert (0 ≥ 1 is false); admission here is purely bond-backed.
            registry: AdmissionRegistry::new([], 1, DEFAULT_MIN_BOND),
            bond_cells: HashMap::new(),
        }
    }
}

impl CourtLedger {
    /// The bond cell bound to `strand` (if a bond was ever posted here).
    pub fn bond_cell_of(&self, strand: &[u8; 32]) -> Option<CellId> {
        self.bond_cells.get(strand).copied()
    }
}

/// The deterministic bond-cell id for `strand` under this node's operator:
/// `derive_raw(operator_pk, blake3_derive(BOND_CELL_DOMAIN, strand))`. The
/// cell's public key is the OPERATOR's, so the operator-signed slash turn
/// has signature authority over it (the trustline escrow shape).
pub fn bond_cell_id(operator_pk: &[u8; 32], strand: &[u8; 32]) -> CellId {
    let token = blake3::derive_key(BOND_CELL_DOMAIN, strand);
    CellId::derive_raw(operator_pk, &token)
}

/// The canonical slash sink: `(public_key, token_id)` for the
/// conserved-but-unspendable burn well. The "public key" is a domain-hashed
/// byte string — nobody holds (or can find) a signing scalar for it, so
/// value moved here is burned WITHOUT a mint-shaped hole in conservation.
pub fn slash_sink_components() -> ([u8; 32], [u8; 32]) {
    (
        blake3::derive_key(SLASH_SINK_DOMAIN, b"unspendable-pubkey"),
        blake3::derive_key(SLASH_SINK_DOMAIN, b"token"),
    )
}

/// The canonical slash-sink cell id.
pub fn slash_sink_cell_id() -> CellId {
    let (pk, token) = slash_sink_components();
    CellId::derive_raw(&pk, &token)
}

// =============================================================================
// Refusals (fail-closed admission outcomes)
// =============================================================================

/// Every way a court request can be refused. A refusal changes NO state.
#[derive(Debug)]
pub enum CourtServiceRefusal {
    /// The exhibit does not verify (malformed bytes / forged signature /
    /// not a same-slot conflicting pair).
    BadEvidence(String),
    /// This evidence digest was already resolved (no-double-resolve) —
    /// re-submission in either block order lands here.
    AlreadyResolved,
    /// The accused strand holds no bond here — nothing at stake. NOT
    /// burned: evidence never expires; a bond posted later is still
    /// slashable by the same exhibit.
    NothingAtStake,
    /// The bond's owner signature does not verify (forged posting).
    ForgedBond,
    /// The strand already holds a live bond (escrow == bond invariant:
    /// top-ups are not modeled; slash first, then re-bond).
    AlreadyBonded { existing: u64 },
    /// A third-party bond posting without the owner's signature.
    SignatureRequired,
    /// The authoritative executor rejected the turn.
    TurnRejected(String),
    /// Malformed request (bad hex, wrong lengths, …).
    BadRequest(String),
}

impl CourtServiceRefusal {
    fn status(&self) -> StatusCode {
        match self {
            CourtServiceRefusal::BadEvidence(_) => StatusCode::UNPROCESSABLE_ENTITY,
            CourtServiceRefusal::AlreadyResolved | CourtServiceRefusal::AlreadyBonded { .. } => {
                StatusCode::CONFLICT
            }
            CourtServiceRefusal::NothingAtStake => StatusCode::PAYMENT_REQUIRED,
            CourtServiceRefusal::ForgedBond | CourtServiceRefusal::TurnRejected(_) => {
                StatusCode::FORBIDDEN
            }
            CourtServiceRefusal::SignatureRequired | CourtServiceRefusal::BadRequest(_) => {
                StatusCode::BAD_REQUEST
            }
        }
    }

    fn reason(&self) -> &'static str {
        match self {
            CourtServiceRefusal::BadEvidence(_) => "bad-evidence",
            CourtServiceRefusal::AlreadyResolved => "already-resolved",
            CourtServiceRefusal::NothingAtStake => "nothing-at-stake",
            CourtServiceRefusal::ForgedBond => "forged-bond",
            CourtServiceRefusal::AlreadyBonded { .. } => "already-bonded",
            CourtServiceRefusal::SignatureRequired => "signature-required",
            CourtServiceRefusal::TurnRejected(_) => "turn-rejected",
            CourtServiceRefusal::BadRequest(_) => "bad-request",
        }
    }

    fn detail(&self) -> String {
        match self {
            CourtServiceRefusal::BadEvidence(d) => format!("exhibit does not verify: {d}"),
            CourtServiceRefusal::AlreadyResolved => {
                "evidence digest already resolved (no-double-resolve)".into()
            }
            CourtServiceRefusal::NothingAtStake => {
                "accused strand holds no bond on this node".into()
            }
            CourtServiceRefusal::ForgedBond => {
                "bond signature does not verify against the strand key".into()
            }
            CourtServiceRefusal::AlreadyBonded { existing } => {
                format!("strand already holds a live bond of {existing} (slash or re-bond after)")
            }
            CourtServiceRefusal::SignatureRequired => {
                "bonding a third-party strand requires the owner's bond signature".into()
            }
            CourtServiceRefusal::TurnRejected(d) | CourtServiceRefusal::BadRequest(d) => d.clone(),
        }
    }
}

impl IntoResponse for CourtServiceRefusal {
    fn into_response(self) -> Response {
        let body = serde_json::json!({
            "error": self.detail(),
            "reason": self.reason(),
        });
        (self.status(), Json(body)).into_response()
    }
}

fn hex_decode(hex: &str) -> Option<Vec<u8>> {
    if hex.len() % 2 != 0 {
        return None;
    }
    (0..hex.len() / 2)
        .map(|i| u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok())
        .collect()
}

fn hex_decode_64(hex: &str) -> Option<[u8; 64]> {
    let bytes = hex_decode(hex)?;
    bytes.try_into().ok()
}

// =============================================================================
// THE SLASH (verified evidence → one conserved executor move + digest burn)
// =============================================================================

/// A successful witness-first slash, executed on the live ledger.
#[derive(Clone, Debug, Serialize)]
pub struct SlashOutcome {
    /// The slashed strand key (hex).
    pub strand: String,
    /// The burned evidence digest (hex) — the no-double-resolve key.
    pub digest: String,
    /// The bond value moved out of the bond cell.
    pub burned: u64,
    /// The debited bond cell (hex).
    pub bond_cell: String,
    /// Where the slashed value moved (fee well or the canonical sink).
    pub destination: String,
    /// The committed slash turn.
    pub turn_hash: String,
    /// Whether the strand still clears the court registry's admission gate
    /// after the slash (a bond-only strand does not).
    pub admitted_after: bool,
}

/// WITNESS-FIRST, end to end: verify the exhibit, execute the slash as ONE
/// ordinary conserved executor move from the bonded cell, then burn the
/// evidence digest + slash the registry. Fail-closed at every leg; nothing
/// is burned and no value moves on any refusal. The digest burns ONLY after
/// the move COMMITS, so an executor rejection leaves the exhibit fresh.
pub fn execute_slash(
    s: &mut NodeStateInner,
    ev: &EvidenceOfEquivocation,
) -> Result<SlashOutcome, CourtServiceRefusal> {
    // 1. The cryptographic core (re-verified here — the court never assumes).
    ev.verify()
        .map_err(|e| CourtServiceRefusal::BadEvidence(e.to_string()))?;
    let digest = ev.digest();

    // 2. No-double-resolve: a burned digest refuses in either block order.
    if s.equivocation_court.court.is_resolved(&digest) {
        return Err(CourtServiceRefusal::AlreadyResolved);
    }

    // 3. Something at stake: a registered bond AND its bound value cell.
    let strand = dregg_types::PublicKey(ev.creator);
    let burned = s.equivocation_court.registry.bond_amount(&strand);
    if burned == 0 {
        return Err(CourtServiceRefusal::NothingAtStake);
    }
    let bond_cell = s
        .equivocation_court
        .bond_cell_of(&ev.creator)
        .ok_or(CourtServiceRefusal::NothingAtStake)?;

    // 4. THE MOVE: bond cell → fee well (genesis-configured) or the
    //    canonical unspendable sink. An ordinary conserving Transfer through
    //    the authoritative executor — the slash IS a move, never a mint or
    //    an out-of-band balance edit.
    let mut effects = Vec::with_capacity(3);
    let destination = match s.fee_well {
        Some(well) => well,
        None => {
            let sink = slash_sink_cell_id();
            if s.ledger.get(&sink).is_none() {
                let (pk, token) = slash_sink_components();
                effects.push(Effect::CreateCell {
                    public_key: pk,
                    token_id: token,
                    balance: 0,
                });
            }
            sink
        }
    };
    effects.push(Effect::Transfer {
        from: bond_cell,
        to: destination,
        amount: burned,
    });
    effects.push(Effect::EmitEvent {
        cell: bond_cell,
        event: Event::new(
            symbol("equivocation-slash"),
            vec![digest, ev.creator, field_u64(burned)],
        ),
    });
    let operator = crate::executor_setup::local_agent_cell(s);
    let turn_hash = run_signed_turn(
        s,
        operator,
        bond_cell,
        "equivocation_slash",
        effects,
        None,
        None,
    )
    .map_err(|e| CourtServiceRefusal::TurnRejected(e.detail()))?;

    // 5. The verdict: burn the digest + slash the registry (the federation
    //    court's resolve — preconditions all re-checked under this same
    //    exclusive borrow, so this cannot refuse after the move committed;
    //    if it somehow does, surface LOUDLY: value moved, ledger truth wins,
    //    and the registry divergence is a finding, never papered).
    let CourtLedger {
        court, registry, ..
    } = &mut s.equivocation_court;
    let verdict = court.resolve(registry, ev).map_err(|refusal| {
        tracing::error!(
            strand = %hex_encode(&ev.creator),
            digest = %hex_encode(&digest),
            burned,
            %refusal,
            "slash move COMMITTED but the court refused to resolve — \
             registry/ledger divergence"
        );
        CourtServiceRefusal::TurnRejected(format!(
            "slash move committed but the court refused the verdict: {refusal}"
        ))
    })?;
    debug_assert_eq!(verdict.burned, burned);

    let admitted_after = s.equivocation_court.registry.admitted(&strand);
    tracing::warn!(
        strand = %hex_encode(&ev.creator),
        digest = %hex_encode(&digest),
        burned,
        bond_cell = %hex_encode(bond_cell.as_bytes()),
        "equivocation slashed: bond moved out of the bond cell as a conserved \
         turn (ORGANS §5 adjudication weld)"
    );
    Ok(SlashOutcome {
        strand: hex_encode(&ev.creator),
        digest: hex_encode(&digest),
        burned,
        bond_cell: hex_encode(bond_cell.as_bytes()),
        destination: hex_encode(destination.as_bytes()),
        turn_hash: hex_encode(&turn_hash),
        admitted_after,
    })
}

/// THE GOSSIP HOOK: lace-detected fork evidence reaches the slash path.
/// Called from `blocklace_sync::handle_push` for every retained
/// [`EquivocationProof`] (after constitution auto-evict). Same-slot forks
/// reduce to the wire value and adjudicate; different-seq incomparable
/// forks stay on the membership path (the evidence module's named scope).
/// Outcomes are logged, never propagated as errors — gossip handling must
/// not fail on an unbonded or already-resolved equivocator.
pub async fn slash_from_proof(state: &NodeState, proof: &EquivocationProof) {
    let ev = match EvidenceOfEquivocation::from_proof(proof) {
        Ok(ev) => ev,
        Err(e) => {
            tracing::debug!(
                creator = %hex_encode(&proof.creator[..4]),
                error = %e,
                "fork proof is not same-slot-certifiable wire evidence; \
                 membership auto-evict already handled it"
            );
            return;
        }
    };
    let mut s = state.write().await;
    match execute_slash(&mut s, &ev) {
        Ok(outcome) => {
            tracing::warn!(
                strand = %outcome.strand,
                burned = outcome.burned,
                "gossip-propagated equivocation evidence slashed the bonded cell"
            );
        }
        Err(CourtServiceRefusal::NothingAtStake) => {
            tracing::debug!(
                strand = %hex_encode(&ev.creator),
                "equivocator holds no bond here; evidence stays fresh (never expires)"
            );
        }
        Err(CourtServiceRefusal::AlreadyResolved) => {
            tracing::debug!(
                strand = %hex_encode(&ev.creator),
                "equivocation evidence already resolved (no-double-resolve)"
            );
        }
        Err(e) => {
            tracing::warn!(
                strand = %hex_encode(&ev.creator),
                reason = e.reason(),
                detail = %e.detail(),
                "gossip-propagated equivocation evidence refused"
            );
        }
    }
}

// =============================================================================
// Routes
// =============================================================================

/// The court route surface. Mounted inside the node's PROTECTED router
/// (bearer-token gate) in `api.rs`.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/court/bond", post(post_court_bond))
        .route("/court/evidence", post(post_court_evidence))
        .route("/court/status/{strand}", get(get_court_status))
}

#[derive(Deserialize)]
struct BondRequest {
    /// Strand pubkey (hex, 64 chars). Omit to bond this node's OWN strand
    /// (the cipherclerk gossip key — the key its blocks are signed with).
    #[serde(default)]
    strand: Option<String>,
    /// The stake to escrow (slashable in full on equivocation).
    amount: u64,
    /// The owner's Ed25519 signature over `Bond::signing_message(owner,
    /// amount)` (hex, 128 chars). Required for a third-party strand; the
    /// node self-signs its own.
    #[serde(default)]
    signature: Option<String>,
}

#[derive(Serialize)]
struct BondResponse {
    strand: String,
    bond_cell: String,
    amount: u64,
    /// Whether the bond clears the registry's admission floor.
    admitted: bool,
    /// The committed turns: the funded birth (+ the one-time adopt turn
    /// granting the operator driving reach over the bond cell).
    turn_hashes: Vec<String>,
}

#[derive(Deserialize)]
struct EvidenceRequest {
    /// The wire-encoded [`EvidenceOfEquivocation`] (hex of the postcard
    /// bytes — `EvidenceOfEquivocation::to_bytes`).
    evidence: String,
}

#[derive(Serialize)]
struct StatusResponse {
    strand: String,
    /// The registered slashable bond (0 if none / already slashed).
    bond: u64,
    /// The bound bond cell and its live escrow, when a bond was posted here.
    bond_cell: Option<String>,
    escrow: Option<u64>,
    /// The court registry's admission verdict (the bond/value leg only).
    admitted: bool,
}

/// `POST /court/bond` — escrow a slashable stake in a real bond cell and
/// register the signed bond. The registry entry lands ONLY after the
/// funding turn commits (escrow == bond at every reachable state).
async fn post_court_bond(
    State(state): State<NodeState>,
    Json(req): Json<BondRequest>,
) -> Result<Json<BondResponse>, CourtServiceRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    if req.amount == 0 {
        return Err(CourtServiceRefusal::BadRequest(
            "a zero bond stakes nothing".into(),
        ));
    }

    // Resolve the strand + a VERIFYING signed Bond (forgery refuses here,
    // before any value moves).
    let own_key = inner.cclerk.gossip_signing_key();
    let own_strand = own_key.public_key();
    let bond = match &req.strand {
        None => Bond::post(&own_key, req.amount),
        Some(hex) => {
            let strand_bytes = hex_decode_32(hex).ok_or_else(|| {
                CourtServiceRefusal::BadRequest(format!("malformed strand key: {hex}"))
            })?;
            let owner = dregg_types::PublicKey(strand_bytes);
            if owner == own_strand {
                Bond::post(&own_key, req.amount)
            } else {
                let sig_hex = req
                    .signature
                    .as_deref()
                    .ok_or(CourtServiceRefusal::SignatureRequired)?;
                let sig = hex_decode_64(sig_hex).ok_or_else(|| {
                    CourtServiceRefusal::BadRequest(format!(
                        "malformed bond signature: {sig_hex}"
                    ))
                })?;
                Bond {
                    owner,
                    amount: req.amount,
                    signature: dregg_types::Signature(sig),
                }
            }
        }
    };
    if !bond.verify_sig() {
        return Err(CourtServiceRefusal::ForgedBond);
    }
    let strand_bytes = *bond.owner.as_bytes();

    // Escrow == bond invariant: no top-ups while a live bond stands.
    let existing = inner.equivocation_court.registry.bond_amount(&bond.owner);
    if existing > 0 {
        return Err(CourtServiceRefusal::AlreadyBonded { existing });
    }

    // THE ESCROW: create the bond cell (deterministic per strand, reused
    // across a slash → re-bond cycle) and fund it with a REAL ledger debit
    // of the operator's agent cell — an ordinary conserving move. A fresh
    // cell also gets the one-time ADOPT turn (the trustline shape): the
    // cell grants the operator agent driving reach over itself, which is
    // what authorizes the future SLASH turn to target it. The adopt fee is
    // pre-funded on top of the stake and burned by the adopt turn, leaving
    // exactly `amount` escrowed.
    let operator = crate::executor_setup::local_agent_cell(inner);
    let operator_pk = inner.cclerk.public_key().0;
    let bond_cell = bond_cell_id(&operator_pk, &strand_bytes);
    let needs_adopt = !inner
        .ledger
        .get(&operator)
        .map(|c| c.capabilities.has_access(&bond_cell))
        .unwrap_or(false);
    let mut turn_hashes = Vec::with_capacity(2);
    let mut effects = Vec::with_capacity(3);
    if inner.ledger.get(&bond_cell).is_none() {
        let token = blake3::derive_key(BOND_CELL_DOMAIN, &strand_bytes);
        effects.push(Effect::CreateCell {
            public_key: operator_pk,
            token_id: token,
            balance: 0,
        });
    }
    effects.push(Effect::Transfer {
        from: operator,
        to: bond_cell,
        amount: req.amount + if needs_adopt { ADOPT_TURN_FEE } else { 0 },
    });
    effects.push(Effect::EmitEvent {
        cell: bond_cell,
        event: Event::new(
            symbol("court-bond-posted"),
            vec![strand_bytes, field_u64(req.amount)],
        ),
    });
    turn_hashes.push(
        run_signed_turn(
            inner,
            operator,
            operator,
            "court_bond",
            effects,
            None,
            None,
        )
        .map_err(|e| CourtServiceRefusal::TurnRejected(e.detail()))?,
    );
    if needs_adopt {
        // The adopt (cell-agent turn): the bond cell grants the operator
        // its driving capability; the pre-funded fee burns here.
        turn_hashes.push(
            run_signed_turn(
                inner,
                bond_cell,
                bond_cell,
                "court_bond_adopt",
                vec![Effect::GrantCapability {
                    from: bond_cell,
                    to: operator,
                    cap: dregg_cell::CapabilityRef {
                        target: bond_cell,
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
            )
            .map_err(|e| CourtServiceRefusal::TurnRejected(e.detail()))?,
        );
    }

    // Registry truth follows the committed escrow.
    if !inner.equivocation_court.registry.add_bond(bond.clone()) {
        // Unreachable (verify_sig checked above), but never assume: the
        // escrow committed, so surface the divergence loudly.
        tracing::error!(
            strand = %hex_encode(&strand_bytes),
            "bond escrow committed but the registry refused the bond signature"
        );
        return Err(CourtServiceRefusal::ForgedBond);
    }
    inner
        .equivocation_court
        .bond_cells
        .insert(strand_bytes, bond_cell);

    let admitted = inner.equivocation_court.registry.admitted(&bond.owner);
    tracing::info!(
        strand = %hex_encode(&strand_bytes),
        bond_cell = %hex_encode(bond_cell.as_bytes()),
        amount = req.amount,
        admitted,
        "court bond posted: stake escrowed in the bond cell (ORGANS §5)"
    );
    drop(s);
    Ok(Json(BondResponse {
        strand: hex_encode(&strand_bytes),
        bond_cell: hex_encode(bond_cell.as_bytes()),
        amount: req.amount,
        admitted,
        turn_hashes: turn_hashes.iter().map(|h| hex_encode(h)).collect(),
    }))
}

/// `POST /court/evidence` — the witness-first slash: a verifying exhibit
/// decides; the bond moves out of the bonded cell as ONE conserved executor
/// turn and the evidence digest burns forever. No unlock requirement: the
/// exhibit is the authority (the route still sits behind the bearer gate).
async fn post_court_evidence(
    State(state): State<NodeState>,
    Json(req): Json<EvidenceRequest>,
) -> Result<Json<SlashOutcome>, CourtServiceRefusal> {
    let bytes = hex_decode(&req.evidence)
        .ok_or_else(|| CourtServiceRefusal::BadRequest("malformed evidence hex".into()))?;
    let ev = EvidenceOfEquivocation::from_bytes(&bytes)
        .ok_or_else(|| CourtServiceRefusal::BadEvidence("malformed evidence bytes".into()))?;
    let mut s = state.write().await;
    let outcome = execute_slash(&mut s, &ev)?;
    drop(s);
    Ok(Json(outcome))
}

/// `GET /court/status/{strand}` — the live bond position.
async fn get_court_status(
    State(state): State<NodeState>,
    AxumPath(strand_hex): AxumPath<String>,
) -> Result<Json<StatusResponse>, CourtServiceRefusal> {
    let strand_bytes = hex_decode_32(&strand_hex).ok_or_else(|| {
        CourtServiceRefusal::BadRequest(format!("malformed strand key: {strand_hex}"))
    })?;
    let s = state.read().await;
    let strand = dregg_types::PublicKey(strand_bytes);
    let bond_cell = s.equivocation_court.bond_cell_of(&strand_bytes);
    let escrow = bond_cell
        .and_then(|c| s.ledger.get(&c))
        .map(|c| u64::try_from(c.state.balance()).unwrap_or(0));
    Ok(Json(StatusResponse {
        strand: strand_hex,
        bond: s.equivocation_court.registry.bond_amount(&strand),
        bond_cell: bond_cell.map(|c| hex_encode(c.as_bytes())),
        escrow,
        admitted: s.equivocation_court.registry.admitted(&strand),
    }))
}

// =============================================================================
// Tests — the e2e weld on the real router + executor + court
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use dregg_blocklace::finality::{Block, Payload};
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    const STAKE: u64 = 250;

    /// A node state with a funded operator agent cell (the trustline test
    /// shape — the same shape a faucet-funded devnet node has).
    async fn funded_state() -> (NodeState, tempfile::TempDir) {
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        {
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
        }
        (state, dir)
    }

    /// A strand whose dalek key signs blocks and whose typed key signs
    /// bonds — SAME seed, same Ed25519 keypair, same public key (the
    /// court.rs differential discipline).
    fn strand(seed: u8) -> (ed25519_dalek::SigningKey, dregg_types::SigningKey, [u8; 32]) {
        let dalek = ed25519_dalek::SigningKey::from_bytes(&[seed; 32]);
        let typed = dregg_types::SigningKey::from_bytes(&[seed; 32]);
        let pk = *typed.public_key().as_bytes();
        assert_eq!(&pk, &dalek.verifying_key().to_bytes());
        (dalek, typed, pk)
    }

    fn fork_evidence(dalek: &ed25519_dalek::SigningKey, seq: u64) -> EvidenceOfEquivocation {
        let a = Block::new(dalek, seq, Payload::Data(b"story A".to_vec()), vec![]);
        let b = Block::new(dalek, seq, Payload::Data(b"story B".to_vec()), vec![]);
        EvidenceOfEquivocation::from_blocks(&a, &b).expect("real fork certifies")
    }

    async fn request(
        state: &NodeState,
        method: &str,
        uri: &str,
        body: Option<serde_json::Value>,
    ) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let mut builder = Request::builder().uri(uri).method(method);
        let req = match body {
            Some(json) => {
                builder = builder.header("content-type", "application/json");
                builder.body(Body::from(json.to_string())).unwrap()
            }
            None => builder.body(Body::empty()).unwrap(),
        };
        let resp = app.oneshot(req).await.unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({}));
        (status, json)
    }

    async fn post_json(
        state: &NodeState,
        uri: &str,
        body: serde_json::Value,
    ) -> (StatusCode, serde_json::Value) {
        request(state, "POST", uri, Some(body)).await
    }

    async fn balance(state: &NodeState, cell: CellId) -> i128 {
        let s = state.read().await;
        s.ledger
            .get(&cell)
            .map(|c| c.state.balance() as i128)
            .unwrap_or(0)
    }

    /// Post a third-party bond through the route (owner-signed).
    async fn post_bond(
        state: &NodeState,
        typed: &dregg_types::SigningKey,
        amount: u64,
    ) -> (StatusCode, serde_json::Value) {
        let owner = typed.public_key();
        let sig = dregg_types::sign(typed, &Bond::signing_message(&owner, amount));
        post_json(
            state,
            "/court/bond",
            serde_json::json!({
                "strand": hex_encode(owner.as_bytes()),
                "amount": amount,
                "signature": hex_encode(&sig.0),
            }),
        )
        .await
    }

    // ── bond: the escrow leg ─────────────────────────────────────────────────

    #[tokio::test]
    async fn bond_escrows_stake_in_a_real_cell_as_a_conserved_move() {
        let (state, _dir) = funded_state().await;
        let (_dalek, typed, pk) = strand(41);
        let operator = {
            let s = state.read().await;
            crate::executor_setup::local_agent_cell(&s)
        };
        let operator_before = balance(&state, operator).await;

        let (status, json) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let bond_cell = CellId(hex_decode_32(json["bond_cell"].as_str().unwrap()).unwrap());

        // THE ESCROW IS REAL: the bond cell holds the stake, the operator
        // was debited (a move, never a mint), the registry agrees.
        assert_eq!(balance(&state, bond_cell).await, STAKE as i128);
        assert!(
            operator_before - balance(&state, operator).await >= STAKE as i128,
            "the funder must be debited the escrow"
        );
        {
            let s = state.read().await;
            assert_eq!(
                s.equivocation_court
                    .registry
                    .bond_amount(&dregg_types::PublicKey(pk)),
                STAKE,
                "escrow == registry bond"
            );
            assert_eq!(s.equivocation_court.bond_cell_of(&pk), Some(bond_cell));
        }
        assert_eq!(json["admitted"], true, "{STAKE} clears the admission floor");

        // Escrow == bond invariant: a second posting refuses.
        let (status, json) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "already-bonded");
        assert_eq!(balance(&state, bond_cell).await, STAKE as i128);
    }

    #[tokio::test]
    async fn forged_bond_signature_refuses_before_any_value_moves() {
        let (state, _dir) = funded_state().await;
        let (_dalek, _typed, victim_pk) = strand(43);
        let attacker = dregg_types::SigningKey::from_bytes(&[99u8; 32]);
        // The attacker signs a bond it CLAIMS is the victim's.
        let msg = Bond::signing_message(&dregg_types::PublicKey(victim_pk), STAKE);
        let sig = dregg_types::sign(&attacker, &msg);
        let (status, json) = post_json(
            &state,
            "/court/bond",
            serde_json::json!({
                "strand": hex_encode(&victim_pk),
                "amount": STAKE,
                "signature": hex_encode(&sig.0),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN, "{json}");
        assert_eq!(json["reason"], "forged-bond");
        let s = state.read().await;
        assert_eq!(
            s.equivocation_court
                .registry
                .bond_amount(&dregg_types::PublicKey(victim_pk)),
            0
        );
        assert!(s.equivocation_court.bond_cell_of(&victim_pk).is_none());
    }

    // ── THE SLASH: evidence → one conserved move, exactly once ──────────────

    #[tokio::test]
    async fn valid_evidence_slashes_the_bonded_cell_exactly_once() {
        let (state, _dir) = funded_state().await;
        let (dalek, typed, pk) = strand(47);
        let (status, json) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let bond_cell = CellId(hex_decode_32(json["bond_cell"].as_str().unwrap()).unwrap());

        let ev = fork_evidence(&dalek, 7);
        let sink = slash_sink_cell_id();
        let sink_before = balance(&state, sink).await;

        // THE EXHIBIT DECIDES: the whole bond moves out of the bond cell.
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(&ev.to_bytes()) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["burned"].as_u64(), Some(STAKE));
        assert_eq!(json["admitted_after"], false, "slashed strand loses admission");

        // CONSERVED: bond cell debited the exact stake, the sink credited it.
        assert_eq!(balance(&state, bond_cell).await, 0, "bonded cell debited");
        assert_eq!(
            balance(&state, sink).await - sink_before,
            STAKE as i128,
            "the slash is a MOVE: the sink holds exactly what the bond cell lost"
        );
        {
            let s = state.read().await;
            let strand = dregg_types::PublicKey(pk);
            assert_eq!(s.equivocation_court.registry.bond_amount(&strand), 0);
            assert!(!s.equivocation_court.registry.admitted(&strand));
            assert!(s.equivocation_court.court.is_resolved(&ev.digest()));
        }

        // NO-DOUBLE-RESOLVE: re-submission refuses with no state change…
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(&ev.to_bytes()) }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(json["reason"], "already-resolved");
        // …in EITHER block order (the digest is order-insensitive).
        let flipped = EvidenceOfEquivocation {
            creator: ev.creator,
            header_a: ev.header_b.clone(),
            header_b: ev.header_a.clone(),
        };
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(&flipped.to_bytes()) }),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{json}");
        assert_eq!(balance(&state, bond_cell).await, 0);
        assert_eq!(balance(&state, sink).await - sink_before, STAKE as i128);
    }

    #[tokio::test]
    async fn forged_and_malformed_evidence_refuse_with_no_state_change() {
        let (state, _dir) = funded_state().await;
        let (dalek, typed, pk) = strand(53);
        let (status, json) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let bond_cell = CellId(hex_decode_32(json["bond_cell"].as_str().unwrap()).unwrap());

        // FORGED: an attacker signs "the strand's" second header.
        let attacker = ed25519_dalek::SigningKey::from_bytes(&[99u8; 32]);
        let a = Block::new(&dalek, 3, Payload::Data(b"x".to_vec()), vec![]);
        let mut b = Block::new(&attacker, 3, Payload::Data(b"y".to_vec()), vec![]);
        b.creator = a.creator;
        let forged = EvidenceOfEquivocation {
            creator: a.creator,
            header_a: dregg_blocklace::evidence::EvidenceHeader::from_block(&a),
            header_b: dregg_blocklace::evidence::EvidenceHeader::from_block(&b),
        };
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(&forged.to_bytes()) }),
        )
        .await;
        assert_eq!(status, StatusCode::UNPROCESSABLE_ENTITY, "{json}");
        assert_eq!(json["reason"], "bad-evidence");

        // MALFORMED: garbage bytes and garbage hex.
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(b"not evidence") }),
        )
        .await;
        assert_eq!(status, StatusCode::UNPROCESSABLE_ENTITY, "{json}");
        let (status, _) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": "zz-not-hex" }),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        // NOTHING CHANGED: escrow, registry, and the burn set are untouched.
        assert_eq!(balance(&state, bond_cell).await, STAKE as i128);
        let s = state.read().await;
        assert_eq!(
            s.equivocation_court
                .registry
                .bond_amount(&dregg_types::PublicKey(pk)),
            STAKE
        );
        assert!(!s.equivocation_court.court.is_resolved(&forged.digest()));
    }

    #[tokio::test]
    async fn unbonded_strand_is_nothing_at_stake_and_slashable_later() {
        let (state, _dir) = funded_state().await;
        let (dalek, typed, _pk) = strand(59);
        let ev = fork_evidence(&dalek, 1);

        // No bond yet: refuse, burn nothing — evidence never expires.
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(&ev.to_bytes()) }),
        )
        .await;
        assert_eq!(status, StatusCode::PAYMENT_REQUIRED, "{json}");
        assert_eq!(json["reason"], "nothing-at-stake");
        {
            let s = state.read().await;
            assert!(!s.equivocation_court.court.is_resolved(&ev.digest()));
        }

        // Bond posted later: the SAME exhibit slashes.
        let (status, json) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let (status, json) = post_json(
            &state,
            "/court/evidence",
            serde_json::json!({ "evidence": hex_encode(&ev.to_bytes()) }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["burned"].as_u64(), Some(STAKE));
    }

    // ── the gossip hook: propagated proofs reach the same slash path ─────────

    #[tokio::test]
    async fn lace_retained_proof_reaches_the_slash_path() {
        let (state, _dir) = funded_state().await;
        let (dalek, typed, pk) = strand(61);
        let (status, json) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        let bond_cell = CellId(hex_decode_32(json["bond_cell"].as_str().unwrap()).unwrap());

        // The live pipe: the lace detects the fork and retains the proof
        // (exactly what blocklace_sync's outcome.equivocations carries).
        let a = Block::new(&dalek, 1, Payload::Data(b"story A".to_vec()), vec![]);
        let b = Block::new(&dalek, 1, Payload::Data(b"story B".to_vec()), vec![]);
        let mut lace = dregg_blocklace::finality::Blocklace::new_simple(
            ed25519_dalek::SigningKey::from_bytes(&[1u8; 32]),
        );
        lace.receive_block(a).expect("first block inserts");
        let err = lace.receive_block(b).expect_err("fork detected");
        let dregg_blocklace::finality::BlockError::Equivocation { proof, .. } = err else {
            panic!("expected equivocation, got {err:?}");
        };

        slash_from_proof(&state, &proof).await;

        assert_eq!(
            balance(&state, bond_cell).await,
            0,
            "the propagated proof slashed the bonded cell"
        );
        let s = state.read().await;
        assert_eq!(
            s.equivocation_court
                .registry
                .bond_amount(&dregg_types::PublicKey(pk)),
            0
        );
        // Idempotent on replay (no-double-resolve): a second delivery of
        // the same proof is a logged no-op.
        drop(s);
        slash_from_proof(&state, &proof).await;
        assert_eq!(balance(&state, bond_cell).await, 0);
    }

    // ── status + the predicate atom on the live executor ────────────────────

    #[tokio::test]
    async fn status_reports_the_live_position() {
        let (state, _dir) = funded_state().await;
        let (_dalek, typed, pk) = strand(67);
        let (status, _) = post_bond(&state, &typed, STAKE).await;
        assert_eq!(status, StatusCode::OK);

        let uri = format!("/court/status/{}", hex_encode(&pk));
        let (status, json) = request(&state, "GET", &uri, None).await;
        assert_eq!(status, StatusCode::OK, "{json}");
        assert_eq!(json["bond"].as_u64(), Some(STAKE));
        assert_eq!(json["escrow"].as_u64(), Some(STAKE));
        assert_eq!(json["admitted"], true);
    }

    /// The court's `validEquivocation` atom is INSTALLED on the node's
    /// authoritative executors (configure_turn_executor registers it), so a
    /// turn can gate on the exhibit through the witnessed-predicate
    /// machinery — the CONSENSUS-FLEX §7 item 2 weld, live.
    #[tokio::test]
    async fn equivocation_predicate_atom_is_live_on_node_executors() {
        use dregg_cell::predicate::{InputRef, PredicateInput, WitnessedPredicate};
        let (state, _dir) = funded_state().await;
        let (dalek, _typed, pk) = strand(71);
        let ev = fork_evidence(&dalek, 9);

        let s = state.read().await;
        let executor = crate::executor_setup::new_submit_executor(&s);
        let registry = executor
            .witnessed_registry
            .as_ref()
            .expect("node executors carry a witnessed-predicate registry");
        let wp = WitnessedPredicate::custom(
            dregg_federation::court::equivocation_predicate_vk(),
            pk,
            InputRef::Witness { index: 0 },
            1,
        );
        registry
            .verify(&wp, &PredicateInput::Bytes(&ev.digest()), &ev.to_bytes())
            .expect("the live executor registry dispatches the court atom");
        assert!(
            registry
                .verify(&wp, &PredicateInput::Bytes(&[0xAB; 32]), &ev.to_bytes())
                .is_err(),
            "a wrong digest still refuses through the live registry"
        );
    }
}
