//! Data models — the node's wire contract, mirrored.
//!
//! These structs are deliberate copies of the node's JSON response types
//! (`node/src/api.rs`, `node/src/events.rs`). The native shell is a CLIENT: it
//! speaks HTTP+SSE to a dregg node and never links the executor or the Lean
//! archive. Mirroring the wire types (rather than linking `dregg-sdk`, which
//! pulls `libdregg_lean.a` on native) keeps this crate light and its
//! dependency on the node a *protocol* dependency, not a *code* dependency.
//!
//! INVARIANT to maintain: when `node/src/api.rs` changes a response shape, the
//! mirror here must follow. A future build-out lane (docs/STARBRIDGE-V2.md
//! §"Build-out lanes") can replace these hand-mirrors with a shared
//! `dregg-wire-types` crate so the contract is single-sourced.

use serde::{Deserialize, Serialize};

/// `GET /status` — node liveness + the SWAP producer surface.
/// Mirrors `api::StatusResponse`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NodeStatus {
    pub healthy: bool,
    pub peer_count: usize,
    pub latest_height: u64,
    pub dag_height: u64,
    pub block_count: usize,
    pub consensus_live: bool,
    pub federation_mode: String,
    pub public_key: String,
    /// `"lean"` or `"rust"` — the authoritative state producer on the commit
    /// path. The shell surfaces this honestly: a node running the legacy Rust
    /// producer is visibly NOT running the verified semantics.
    pub state_producer: String,
    pub lean_producer: bool,
    pub full_turn_proving: bool,
    pub producer_covered_effects: usize,
}

/// `GET /api/cells` entry. Mirrors `api::CellListEntry`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct CellListEntry {
    pub id: String,
    /// THE EPOCH: signed (issuer wells carry −supply).
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub has_program: bool,
    pub found: bool,
}

/// `GET /api/cell/{id}` — the inspector's per-cell detail.
/// Mirrors the load-bearing fields of `api::CellDetailResponse` (the
/// `program` field, a rich `CellProgramView`, is rendered from its JSON form
/// rather than mirrored as a typed struct in the scaffold).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct CellDetail {
    pub id: String,
    pub found: bool,
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub delegate: Option<String>,
    pub has_program: bool,
    pub public_key: String,
    pub token_id: String,
    pub proved_state: bool,
    pub delegation_epoch: u64,
    pub state_commitment: String,
    pub program_kind: String,
    /// Raw `[FieldElement; 16]` slots, hex-encoded (64 chars each).
    #[serde(default)]
    pub fields: Vec<String>,
    /// The self-describing program view, kept as raw JSON in the scaffold.
    #[serde(default)]
    pub program: Option<serde_json::Value>,
}

/// `GET /api/receipts` entry. Mirrors `api::ReceiptInfo`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ReceiptInfo {
    pub chain_index: u64,
    pub chain_head: bool,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub agent: String,
    pub pre_state: String,
    pub post_state: String,
    pub timestamp: i64,
    pub computrons_used: u64,
    pub action_count: usize,
    pub previous_receipt_hash: Option<String>,
    pub finality: String,
    pub was_encrypted: bool,
    pub was_burn: bool,
    pub has_proof: bool,
    pub executor_signed: bool,
    pub has_witness: bool,
    pub witness_count: usize,
}

/// One committed receipt off the SSE stream `GET /api/events/stream`.
/// Mirrors the summary fields of `events::ReceiptEvent` (the embedded full
/// canonical `TurnReceipt` is left as raw JSON — the shell renders summaries
/// and drills into the raw form in the inspector).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ReceiptEvent {
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    #[serde(default)]
    pub cells: Vec<String>,
    #[serde(default)]
    pub kinds: Vec<String>,
    pub height: u64,
    pub has_proof: bool,
    pub finality: String,
    pub timestamp: i64,
}

/// `GET /api/federations` entry. Mirrors `api::FederationInfo`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct FederationInfo {
    pub id: String,
    pub federation_id: String,
    pub committee_epoch: u64,
    pub threshold: u32,
    pub member_count: usize,
    #[serde(default)]
    pub members: Vec<String>,
    pub is_local: bool,
    pub latest_height: u64,
    pub latest_root: Option<String>,
    pub num_finalized_roots: usize,
}

/// A block in the blocklace DAG. Mirrors the relevant subset of
/// `GET /api/blocklace/blocks`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct BlockInfo {
    #[serde(default)]
    pub height: u64,
    #[serde(default)]
    pub hash: String,
    #[serde(default)]
    pub creator: String,
    #[serde(default)]
    pub seq: u64,
}

// ===========================================================================
// TURN COMPOSITION — the `POST /turn/submit` request shape.
//
// Mirrors `api::SubmitTurnRequest` / `TurnActionSpec` / `TurnEffectSpec`.
// The TurnComposer view builds these; submission is a build-out lane (it
// needs local key custody to sign, OR routes through the node's operator
// cipherclerk for the thin-client effects below).
// ===========================================================================

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SubmitTurnRequest {
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
    #[serde(default)]
    pub actions: Vec<TurnActionSpec>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TurnActionSpec {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    pub effects: Vec<TurnEffectSpec>,
}

/// The JSON-friendly projection of the on-chain `Effect` enum that a thin
/// HTTP client can drive. Mirrors `api::TurnEffectSpec`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TurnEffectSpec {
    SetField {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cell: Option<String>,
        index: usize,
        value: String,
    },
    Transfer {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        from: Option<String>,
        to: String,
        amount: u64,
    },
    EmitEvent {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cell: Option<String>,
        topic: String,
        #[serde(default)]
        data: Vec<String>,
    },
    IncrementNonce {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cell: Option<String>,
    },
}

impl TurnEffectSpec {
    /// Short human label for the composer's effect list.
    pub fn label(&self) -> String {
        match self {
            TurnEffectSpec::SetField { index, .. } => format!("set_field[{index}]"),
            TurnEffectSpec::Transfer { to, amount, .. } => {
                format!("transfer {amount} → {}", short_id(to))
            }
            TurnEffectSpec::EmitEvent { topic, .. } => format!("emit {topic}"),
            TurnEffectSpec::IncrementNonce { .. } => "increment_nonce".to_string(),
        }
    }
}

/// Trim a 64-char hex id to `abcd…wxyz` for display.
pub fn short_id(id: &str) -> String {
    if id.len() <= 12 {
        id.to_string()
    } else {
        format!("{}…{}", &id[..6], &id[id.len() - 4..])
    }
}

/// `POST /cipherclerk/unlock` response. Mirrors `api::UnlockResponse`.
///
/// Unlocking the node's operator cipherclerk is what lets the cockpit submit
/// turns it will commit: the node signs every operator turn as its own cell
/// (confused-deputy hardening), so "local key custody" on the cockpit side is
/// the operator passphrase + the returned bearer token, which `require_auth`
/// then checks on every write route (incl. `/turn/submit`).
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct UnlockResponse {
    pub success: bool,
    /// The API bearer token the cockpit attaches as `Authorization: Bearer …`
    /// on every subsequent write (the node derives it from the passphrase seed).
    #[serde(default)]
    pub bearer_token: Option<String>,
    #[serde(default)]
    pub error: Option<String>,
}

/// `POST /turn/submit` response. Mirrors `api::SubmitTurnResponse`.
///
/// `accepted` is the truth of whether the node's verified executor COMMITTED the
/// turn to its ledger (the same `gateOK`/conservation/authority path the node
/// uses for every turn). A refusal carries the reason in `error` / `turn_hash`
/// (the handler reports refusals in-band with a 200 body), so the cockpit can
/// surface an honest "the node refused this save: …" instead of a silent drop.
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct SubmitTurnResponse {
    pub accepted: bool,
    #[serde(default)]
    pub turn_hash: Option<String>,
    #[serde(default)]
    pub proof_status: Option<String>,
    #[serde(default)]
    pub has_witness: bool,
    #[serde(default)]
    pub witness_count: usize,
    #[serde(default)]
    pub error: Option<String>,
}
