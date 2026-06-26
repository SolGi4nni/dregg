//! The receipt row `dregg-query` consumes — a JSON-friendly mirror of what
//! the node serves, plus the offline form tests construct directly.
//!
//! ## Where each field comes from on the live node
//!
//! - `GET /api/receipts` (node/src/api.rs `ReceiptInfo`): `chain_index`,
//!   `receipt_hash`, `agent`, timestamps — but NO per-effect detail and no
//!   height.
//! - `GET /api/events` (node/src/events.rs `ReceiptEvent`): adds `height`
//!   and `kinds: Vec<String>` (effect-KIND summaries from the commit record)
//!   plus the full canonical `dregg_turn::TurnReceipt` — whose
//!   `derivation_records` carry capability grants and whose `emitted_events`
//!   carry app-level events, but transfer endpoints/amounts are only inside
//!   `effects_hash` (not disclosed per-effect).
//!
//! So TODAY the node can populate `chain_index`/`receipt_hash`/`agent`/
//! `height` and grant-shaped effects; `transfer`/`balance` rows need the
//! enrichment spec'd in [`crate::client`] (the `effects` array below IS that
//! wire shape). Offline mode constructs `ReceiptRecord`s directly.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::fact::{Fact, FactBase, Height};

/// A typed effect summary — the per-effect disclosure the fact extractor
/// reads. This is the wire shape the node-side enrichment (comment-spec in
/// [`crate::client`]) serves; today's `/api/events` only carries the KIND
/// strings, which map to `Other`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EffectSummary {
    /// A cell came into being (factory birth / create).
    Created { agent: String, cell: String },
    /// A value transfer between cells.
    Transfer {
        from: String,
        to: String,
        asset: String,
        amount: u64,
    },
    /// A post-state balance observation for a touched cell (stamped, not a
    /// mutable register — see the schema note in [`crate::fact`]).
    Balance {
        cell: String,
        asset: String,
        amount: u64,
    },
    /// A capability grant (node source: `TurnReceipt::derivation_records`).
    Granted {
        from: String,
        to: String,
        cap: String,
    },
    /// A capability revocation.
    Revoked { cap: String },
    /// A provable supply reduction (`Effect::Burn`): the cell's balance is cut
    /// with no destination credit. Distinct from `Transfer` precisely because
    /// no `to` is credited — the supply of `asset` strictly decreases.
    Burned {
        cell: String,
        asset: String,
        amount: u64,
    },
    /// A state-field write (`Effect::SetField`): slot `index` of `cell` was set
    /// to `value` (hex of the 32-byte field element).
    Field {
        cell: String,
        index: u64,
        value: String,
    },
    /// A cell lifecycle transition (`state` ∈ `sealed` / `unsealed` /
    /// `destroyed` / `sovereign`).
    Lifecycle { cell: String, state: String },
    /// Any effect kind the schema does not extract facts from (kept so the
    /// row remains a faithful summary; extraction skips it). The `name`
    /// field carries the underlying effect-kind string (it cannot be called
    /// `kind` — that key is the internal discriminator tag).
    Other { name: String },
}

/// One receipt row: the dense MMR position (`chain_index`), the receipt
/// commitment (`receipt_hash`, hex of the 32-byte blake3 `dregg-receipt-v3`
/// digest computed by `dregg_turn::TurnReceipt::receipt_hash`), the commit
/// height, the acting agent, and the per-effect summaries.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptRecord {
    /// Position in the node's receipt chain — the DENSE key the MMR commits.
    pub chain_index: u64,
    /// Hex-encoded 32-byte receipt hash (the MMR leaf value).
    pub receipt_hash: String,
    /// Block height at commit (0 when unknown — solo-mode tentative rows).
    pub height: Height,
    /// Hex-encoded agent cell id.
    pub agent: String,
    /// Per-effect summaries (the fact extractor's input).
    #[serde(default)]
    pub effects: Vec<EffectSummary>,
}

#[derive(Debug, Error)]
pub enum ReceiptError {
    #[error("receipt_hash is not 32 hex-encoded bytes: {0}")]
    BadHash(String),
}

impl ReceiptRecord {
    /// The 32-byte receipt commitment — the value the MMR leaf hashes.
    pub fn receipt_hash_bytes(&self) -> Result<[u8; 32], ReceiptError> {
        let v = hex::decode(&self.receipt_hash)
            .map_err(|_| ReceiptError::BadHash(self.receipt_hash.clone()))?;
        v.try_into()
            .map_err(|_| ReceiptError::BadHash(self.receipt_hash.clone()))
    }
}

/// Extract the ground facts of one receipt. Heights come from the receipt's
/// commit height; positional provenance (`chain_index`) stays on the record
/// (the certificate layer binds it — see [`crate::attested`]).
pub fn extract_receipt_facts(r: &ReceiptRecord, out: &mut FactBase) {
    let h = r.height;
    for e in &r.effects {
        match e {
            EffectSummary::Created { agent, cell } => {
                out.add(Fact::created(agent.clone(), cell.clone(), h));
            }
            EffectSummary::Transfer {
                from,
                to,
                asset,
                amount,
            } => {
                out.add(Fact::transfer(
                    from.clone(),
                    to.clone(),
                    asset.clone(),
                    *amount,
                    h,
                ));
            }
            EffectSummary::Balance {
                cell,
                asset,
                amount,
            } => {
                out.add(Fact::balance(cell.clone(), asset.clone(), *amount, h));
            }
            EffectSummary::Granted { from, to, cap } => {
                out.add(Fact::granted(from.clone(), to.clone(), cap.clone(), h));
            }
            EffectSummary::Revoked { cap } => {
                out.add(Fact::revoked(cap.clone(), h));
            }
            EffectSummary::Burned {
                cell,
                asset,
                amount,
            } => {
                out.add(Fact::burned(cell.clone(), asset.clone(), *amount, h));
            }
            EffectSummary::Field { cell, index, value } => {
                out.add(Fact::field(cell.clone(), *index, value.clone(), h));
            }
            EffectSummary::Lifecycle { cell, state } => {
                out.add(Fact::lifecycle(cell.clone(), state.clone(), h));
            }
            EffectSummary::Other { .. } => {}
        }
    }
}

/// Extract the whole fact base of a receipt slice (offline mode's entry:
/// a `Vec<ReceiptRecord>` IS the database).
pub fn extract_facts(receipts: &[ReceiptRecord]) -> FactBase {
    let mut base = FactBase::new();
    for r in receipts {
        extract_receipt_facts(r, &mut base);
    }
    base
}
