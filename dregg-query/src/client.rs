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
//! [`ReceiptRecord`]; typed effect detail is carried by the enrichment
//! (`push_committed_event_enriched`, node/src/api.rs).
//!
//! ## The node-side attested-index handlers (SERVED — this spec is discharged)
//!
//! Implemented in `node/src/api.rs` (axum, same router as `/api/receipts`),
//! backed by the node's receipt chain (`s.cclerk.receipt_chain()`, dense by
//! `chain_index`) and the incrementally-synced MMR index
//! (`sync_receipt_index`). The spec below is kept as the contract the
//! handlers mirror:
//!
//! ```text
//! .route("/api/receipts/index/root",  get(get_receipt_index_root))
//! .route("/api/receipts/index/range", get(get_receipt_index_range))
//! ```
//!
//! ```ignore
//! // IGNORED: this is the NODE's source, quoted. The handlers live in `node/src/api.rs`
//! // and are written against `axum` (`State`, `Query`, `Json`) over `NodeState` — none of
//! // which is a dependency of this leaf crate, and none of which can become one: `node`
//! // depends on `dregg-query`, so naming those types here would close a cycle. Kept as
//! // Rust (not `text`) because it is Rust and reads as the handler contract it mirrors.
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

/// `GET /api/receipts/index/root` response (handler: `node/src/api.rs::get_receipt_index_root`).
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
pub fn index_head_path() -> &'static str {
    "/api/receipts/index/head"
}

/// Domain tag for the SIGNED index head ([`index_head_signing_message`]).
/// A v2 (hybrid ML-DSA half, as the finalization votes carry) would bump it.
pub const INDEX_HEAD_DOMAIN_V1: &[u8] = b"dregg-receipt-index-head-v1";

/// The exact bytes the node signs for `GET /api/receipts/index/head` — the
/// SINGLE source of truth for the head preimage (node signer and any client
/// verifier reconstruct byte-identical messages by construction, the same
/// discipline as `dregg_types::finalization_vote_signing_message`).
///
/// Layout: `domain || federation_id || (0x01||block_id | 0x00) || height_le
/// || merkle_root || len_le || mroot`. The ANCHOR half (`block_id`,
/// `height`, `merkle_root`) is the latest attested root's quorum-pinned
/// coordinates; the CLAIM half is the index head. The MMR root is
/// deliberately the LAST 32 bytes — the same root-last layout the model's
/// `CommitBindsMMR` obligation proves against (`commit = hash (limbs ++
/// [mroot])`), so this rung, the vote-v3 rung, and THE ROTATION's sponge
/// limb all pin one shape (docs/deos/CONSENSUS-BINDS-INDEX.md).
pub fn index_head_signing_message(
    federation_id: &[u8; 32],
    block_id: Option<&[u8; 32]>,
    height: u64,
    merkle_root: &[u8; 32],
    len: u64,
    root: &[u8; 32],
) -> Vec<u8> {
    let mut msg = Vec::with_capacity(INDEX_HEAD_DOMAIN_V1.len() + 32 + 33 + 8 + 32 + 8 + 32);
    msg.extend_from_slice(INDEX_HEAD_DOMAIN_V1);
    msg.extend_from_slice(federation_id);
    // 0x00 / 0x01||32-byte option framing, as `AttestedRoot::signing_message`
    // frames its optional roots — a missing anchor is unambiguous bytes.
    match block_id {
        Some(id) => {
            msg.push(0x01);
            msg.extend_from_slice(id);
        }
        None => msg.push(0x00),
    }
    msg.extend_from_slice(&height.to_le_bytes());
    msg.extend_from_slice(merkle_root);
    msg.extend_from_slice(&len.to_le_bytes());
    msg.extend_from_slice(root);
    msg
}

/// `GET /api/receipts/index/head` response — the node's receipt-index MMR
/// head, SIGNED by the node's federation key and anchored to the latest
/// consensus-attested coordinates.
///
/// TRUST LABEL (precise): a NODE-BOUND, CONSENSUS-ANCHORED claim — NOT a
/// quorum-signed root and NOT the `CommitBindsMMR` IVC weld. Over the bare
/// `/index/root` claim the signature buys: (1) non-repudiation — the root is
/// attributable to the node's federation key; (2) anchoring — the preimage
/// binds the `(block_id, height, merkle_root)` the committee's finalization
/// quorum pins, positioning the claim in verified history; (3) fork
/// evidence — two DIFFERENT heads signed at the SAME anchor by one key are
/// portable proof of index equivocation. The committee does NOT vouch for
/// the root itself: the receipt chain is per-node (receipt hashes absorb the
/// executing node's wall clock; node-local turns interleave), so a quorum
/// cannot co-sign it — the honest rung ladder toward that is
/// `docs/deos/CONSENSUS-BINDS-INDEX.md`.
///
/// A client verifies `signature` (ed25519, `verify_strict`) over
/// [`index_head_signing_message`] under a `signer` key it independently
/// trusts for this federation (genesis/operator roster), then uses `root` as
/// the `trusted_root` for [`AttestedSlice::verify`]. This ADDS a check to
/// the existing TOFU root pin; it does not replace watching.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedIndexHead {
    /// Hex 32-byte MMR root (the same value `/index/root` serves).
    pub root: String,
    /// The indexed log length at signing (redundant with the root via the
    /// peak heights; the verifier never trusts it).
    pub len: u64,
    /// Hex 32-byte blocklace block id of the latest attested root; `None`
    /// on a fresh node with no attested root yet.
    pub block_id: Option<String>,
    /// Height of the latest attested root (0 when unanchored).
    pub height: u64,
    /// Hex 32-byte canonical ledger root of the latest attested root — the
    /// quorum-pinned coordinate (all-zero when unanchored).
    pub merkle_root: String,
    /// Hex 32-byte federation id the node signs under.
    pub federation_id: String,
    /// Hex 32-byte ed25519 public key: the node's federation identity (the
    /// same key that signs its `AttestedRoot` quorum signatures).
    pub signer: String,
    /// Hex 64-byte ed25519 signature over [`index_head_signing_message`].
    pub signature: String,
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

#[cfg(test)]
mod index_head_tests {
    use super::*;

    const FED: [u8; 32] = [1; 32];
    const BLK: [u8; 32] = [2; 32];
    const LEDGER: [u8; 32] = [3; 32];
    const ROOT: [u8; 32] = [4; 32];

    fn base() -> Vec<u8> {
        index_head_signing_message(&FED, Some(&BLK), 7, &LEDGER, 42, &ROOT)
    }

    #[test]
    fn preimage_binds_every_field() {
        let m = base();
        let cases = [
            index_head_signing_message(&[9; 32], Some(&BLK), 7, &LEDGER, 42, &ROOT),
            index_head_signing_message(&FED, Some(&[9; 32]), 7, &LEDGER, 42, &ROOT),
            index_head_signing_message(&FED, Some(&BLK), 8, &LEDGER, 42, &ROOT),
            index_head_signing_message(&FED, Some(&BLK), 7, &[9; 32], 42, &ROOT),
            index_head_signing_message(&FED, Some(&BLK), 7, &LEDGER, 43, &ROOT),
            index_head_signing_message(&FED, Some(&BLK), 7, &LEDGER, 42, &[9; 32]),
        ];
        for (i, c) in cases.iter().enumerate() {
            assert_ne!(&m, c, "field {i} must be bound into the preimage");
        }
    }

    #[test]
    fn preimage_option_framing_is_unambiguous() {
        // An unanchored head (fresh node) vs an anchor whose block id is
        // all-zero MUST be distinct bytes (0x00 vs 0x01||zeros framing).
        let none = index_head_signing_message(&FED, None, 0, &[0; 32], 42, &ROOT);
        let zero = index_head_signing_message(&FED, Some(&[0; 32]), 0, &[0; 32], 42, &ROOT);
        assert_ne!(none, zero);
    }

    #[test]
    fn preimage_ends_with_the_mmr_root() {
        // Root-LAST mirrors the model layout `commit = hash (limbs ++
        // [mroot])` (`CommitBindsMMR`): the bound root is the final 32 bytes.
        let m = base();
        assert_eq!(&m[m.len() - 32..], &ROOT);
    }
}
