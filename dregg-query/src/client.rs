//! The node-API surface this crate consumes — transport-agnostic: typed
//! request/response mirrors + path builders, so any HTTP stack (the SDK's
//! client, `curl`, the shell) can drive it. No HTTP dependency lives in this
//! leaf crate.
//!
//! ## What the node serves TODAY (existing routes, node/src/api.rs)
//!
//! - `GET /api/receipts` → `Vec<ReceiptInfo>` — chain_index, receipt_hash,
//!   agent, timestamps, finality. NO height, NO per-effect detail.
//! - `GET /api/events?cell=&kind=` (+ `/api/events/stream` SSE,
//!   node/src/events.rs) → `ReceiptEvent` rows — adds `height`, effect-KIND
//!   summary strings, and the full canonical `TurnReceipt`.
//!
//! [`receipt_record_from_event`] maps a `ReceiptEvent` JSON row into a
//! [`ReceiptRecord`]; effect detail beyond kind strings awaits the
//! enrichment below.
//!
//! ## COMMENT-SPEC — the node-side attested-index handlers (DO NOT yet exist)
//!
//! The node already holds the log (`s.cclerk.receipt_chain()`, dense by
//! `chain_index`) and the leaf values (`TurnReceipt::receipt_hash()`); the
//! MMR prover in [`crate::mmr`] is the missing index. The handlers to add in
//! `node/src/api.rs` (axum, same router as `/api/receipts`):
//!
//! ```text
//! .route("/api/receipts/index/root",  get(get_receipt_index_root))
//! .route("/api/receipts/index/range", get(get_receipt_index_range))
//! ```
//!
//! ```rust,ignore
//! /// GET /api/receipts/index/root → IndexRootResponse
//! ///
//! /// The MMR root over the node's receipt chain: leaf i = the 32-byte
//! /// `receipt_hash()` of chain entry i, hashed and bagged per
//! /// `dregg_query::mmr::Blake3Mmr` (domain tags `dregg-query-mmr-v1:*`).
//! /// Maintain incrementally: push on every commit path that appends to the
//! /// cipherclerk receipt chain (the same tap NodeEvent broadcasts from),
//! /// holding the chain lock so root and len are mutually consistent.
//! async fn get_receipt_index_root(State(state): State<NodeState>)
//!     -> Json<IndexRootResponse>
//! {
//!     let s = state.inner.read();
//!     let mmr = Mmr::from_values(
//!         Blake3Mmr,
//!         s.cclerk.receipt_chain().iter().map(|r| r.receipt_hash()).collect(),
//!     );
//!     Json(IndexRootResponse { root: hex::encode(mmr.root()), len: mmr.len() })
//! }
//!
//! /// GET /api/receipts/index/range?lo=&hi= → IndexRangeResponse
//! ///
//! /// The certified slice: the receipt rows at dense positions [lo, hi]
//! /// (clipped to the chain length) + the RangeOpening, assembled with
//! /// `Mmr::open_range` — the honest prover whose output always verifies
//! /// (`exact_range_verifies`). Effect summaries come from the commit
//! /// record (`s.event_log`) joined by turn_hash — the ENRICHMENT: extend
//! /// `CommittedEvent.effects` from kind strings to the typed
//! /// `EffectSummary` (from/to/asset/amount for Transfer, holder/cap for
//! /// Granted/Revoked, post-state Balance observations for touched cells),
//! /// recorded at commit time where the executor still has the decoded
//! /// effects in hand. Cap the range span (e.g. 1024) like other list
//! /// endpoints.
//! async fn get_receipt_index_range(
//!     State(state): State<NodeState>,
//!     Query(q): Query<RangeParams>,
//! ) -> Result<Json<IndexRangeResponse>, StatusCode> { ... }
//! ```
//!
//! ## The trust anchor (today vs after THE ROTATION)
//!
//! Today the trusted root is obtained out-of-band (operator channel, or
//! TOFU-pinned and watched for consistency). The standing rotation item
//! ("iroot bound into recStateCommit", HORIZONLOG; `CommitBindsMMR` in
//! `Dregg2/Lightclient/MMR.lean` §6) welds the MMR root into the per-turn
//! state commitment as its LAST sponge limb — after which the root is pinned
//! by the IVC aggregate and one light-client check
//! (`light_client_position_non_omission`) anchors every certificate over the
//! whole history. This crate's verifier takes the root as a parameter
//! exactly so that swap is a caller-side change only. The precise close — the
//! hash-floor swap (blake3 → Poseidon2, non-VK, caller-side) and the EPOCH
//! limb weld (VK-affecting, gated to the rotation) — is designed in
//! `docs/deos/COMMIT-BINDS-MMR.md`.

use serde::{Deserialize, Serialize};

use crate::attested::{AttestedSlice, RangeCertificate};
use crate::mmr::RangeOpening;
use crate::receipt::{EffectSummary, ReceiptRecord};

/// `GET /api/receipts/index/root` response (comment-spec'd handler above).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndexRootResponse {
    /// Hex-encoded 32-byte MMR root.
    pub root: String,
    /// The committed log length (redundant with the root via the peak
    /// heights — served for UX; the verifier never trusts it).
    pub len: u64,
}

/// `GET /api/receipts/index/range` query parameters.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeParams {
    pub lo: u64,
    pub hi: u64,
}

/// `GET /api/receipts/index/range` response: the slice + its opening.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndexRangeResponse {
    pub receipts: Vec<ReceiptRecord>,
    pub root: String,
    pub lo: u64,
    pub hi: u64,
    pub opening: RangeOpening,
}

impl IndexRangeResponse {
    /// Assemble the verifiable [`AttestedSlice`] from the wire response.
    pub fn into_slice(self) -> Result<AttestedSlice, hex::FromHexError> {
        let root_v = hex::decode(&self.root)?;
        let root: [u8; 32] = root_v
            .try_into()
            .map_err(|_| hex::FromHexError::InvalidStringLength)?;
        Ok(AttestedSlice {
            receipts: self.receipts,
            cert: RangeCertificate {
                root,
                lo: self.lo,
                hi: self.hi,
                opening: self.opening,
            },
        })
    }
}

/// Path builders (relative to the node's API base).
pub fn receipts_path() -> &'static str {
    "/api/receipts"
}
pub fn events_path() -> &'static str {
    "/api/events"
}
pub fn index_root_path() -> &'static str {
    "/api/receipts/index/root"
}
pub fn index_range_path(lo: u64, hi: u64) -> String {
    format!("/api/receipts/index/range?lo={lo}&hi={hi}")
}

/// The subset of `node/src/events.rs::ReceiptEvent` this crate reads —
/// deserialize a `/api/events` row into this, then map with
/// [`receipt_record_from_event`].
#[derive(Clone, Debug, Deserialize)]
pub struct ReceiptEventRow {
    pub chain_index: u64,
    pub receipt_hash: String,
    /// Block height at commit; 0 when unknown.
    #[serde(default)]
    pub height: u64,
    /// Cells touched; first entry is the agent cell.
    #[serde(default)]
    pub cells: Vec<String>,
    /// Effect-KIND summary strings from the commit record (today's wire —
    /// no payloads, hence `EffectSummary::Other`).
    #[serde(default)]
    pub kinds: Vec<String>,
}

/// Map today's `/api/events` row to a [`ReceiptRecord`]. Until the
/// enrichment lands, effect kinds map to [`EffectSummary::Other`] — enough
/// for membership/provenance queries, NOT for transfer/balance facts (those
/// need the comment-spec'd typed effects).
pub fn receipt_record_from_event(ev: ReceiptEventRow) -> ReceiptRecord {
    ReceiptRecord {
        chain_index: ev.chain_index,
        receipt_hash: ev.receipt_hash,
        height: ev.height,
        agent: ev.cells.first().cloned().unwrap_or_default(),
        effects: ev
            .kinds
            .into_iter()
            .map(|kind| EffectSummary::Other { name: kind })
            .collect(),
    }
}
