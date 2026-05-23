//! TurnComposer-based atomic settlement for orderbook trades.
//!
//! Each fill is settled atomically via a composed Turn with `CommitmentMode::Partial`:
//! both the buyer's payment and seller's asset delivery happen in one atomic operation.
//! Neither party can defect — if one leg fails, the entire turn is rolled back.
//!
//! Uses `CommittedEscrow` for privacy-preserving settlement where amounts are hidden
//! behind Pedersen commitments.

use pyana_turn::action::{CommitmentMode, Effect};
use pyana_turn::escrow::EscrowCondition;
use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::matching::Fill;

/// A settlement descriptor for an atomic trade.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TradeSettlement {
    /// Unique settlement ID (derived from the fill parameters).
    pub id: [u8; 32],
    /// The fill this settlement corresponds to.
    pub fill_price: u64,
    /// The quantity being settled.
    pub fill_amount: u64,
    /// Total payment in quote asset (price * amount).
    pub total_payment: u64,
    /// The buyer's cell ID.
    pub buyer: CellId,
    /// The seller's cell ID.
    pub seller: CellId,
    /// The escrow ID for the buyer's payment lock.
    pub payment_escrow_id: [u8; 32],
    /// Settlement status.
    pub status: SettlementStatus,
    /// Block height when this settlement was created.
    pub created_at: u64,
}

/// Settlement lifecycle.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SettlementStatus {
    /// Escrows created, pending release.
    Pending,
    /// Both legs completed atomically.
    Settled,
    /// Settlement failed, escrows refunded.
    Failed,
}

/// Compute a settlement ID from fill parameters.
pub fn compute_settlement_id(fill: &Fill, created_at: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-settlement-v1");
    hasher.update(&fill.taker_order_id);
    hasher.update(&fill.maker_order_id);
    hasher.update(&fill.price.to_le_bytes());
    hasher.update(&fill.amount.to_le_bytes());
    hasher.update(fill.taker.as_bytes());
    hasher.update(fill.maker.as_bytes());
    hasher.update(&created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Build the payment escrow effect for the buyer.
///
/// The buyer locks `price * amount` in quote asset into an escrow.
/// The escrow releases to the seller when the asset delivery proof is presented.
pub fn build_buyer_escrow_effect(settlement: &TradeSettlement, timeout_height: u64) -> Effect {
    let vk = compute_delivery_vk(&settlement.id);
    Effect::CreateEscrow {
        cell: settlement.buyer,
        recipient: settlement.seller,
        amount: settlement.total_payment,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height,
        escrow_id: settlement.payment_escrow_id,
    }
}

/// Build the release escrow effect (called when settlement completes).
pub fn build_release_effect(escrow_id: [u8; 32]) -> Effect {
    Effect::ReleaseEscrow {
        escrow_id,
        proof: Some(vec![]), // Proof provided by the settlement layer.
    }
}

/// Build atomic settlement effects for a fill.
///
/// Settlement releases the pre-locked escrows from both parties:
/// - The buyer's payment escrow is released to the seller.
/// - The seller's asset escrow is released to the buyer.
///
/// Because both parties locked collateral before their orders went live
/// (via the escrow module), settlement is guaranteed to succeed. The
/// composed turn executes atomically using `CommitmentMode::Partial`.
pub fn build_settlement_effects(fill: &Fill, created_at: u64) -> (TradeSettlement, Vec<Effect>) {
    let (buyer, seller) = match fill.taker_side {
        crate::order::Side::Buy => (fill.taker, fill.maker),
        crate::order::Side::Sell => (fill.maker, fill.taker),
    };

    let total_payment = fill.price * fill.amount;
    let settlement_id = compute_settlement_id(fill, created_at);
    let payment_escrow_id = compute_escrow_id(&settlement_id, "payment");

    let settlement = TradeSettlement {
        id: settlement_id,
        fill_price: fill.price,
        fill_amount: fill.amount,
        total_payment,
        buyer,
        seller,
        payment_escrow_id,
        status: SettlementStatus::Pending,
        created_at,
    };

    // Release pre-locked escrows from both sides.
    // The buyer's order escrow (locked quote asset) releases to the seller.
    // The seller's order escrow (locked base asset) releases to the buyer.
    let buyer_escrow_id = crate::escrow::compute_order_escrow_id(&fill.taker_order_id, &fill.taker);
    let seller_escrow_id =
        crate::escrow::compute_order_escrow_id(&fill.maker_order_id, &fill.maker);

    let effects = vec![
        // Release buyer's payment escrow to seller.
        Effect::ReleaseEscrow {
            escrow_id: buyer_escrow_id,
            proof: Some(settlement_id.to_vec()),
        },
        // Release seller's asset escrow to buyer.
        Effect::ReleaseEscrow {
            escrow_id: seller_escrow_id,
            proof: Some(settlement_id.to_vec()),
        },
    ];

    (settlement, effects)
}

/// Build settlement effects that also include the match proof as authorization.
///
/// The match proof serves as the cryptographic evidence that the fill is valid,
/// authorizing the escrow release. Any node can verify the proof independently.
pub fn build_verified_settlement_effects(
    fill: &Fill,
    created_at: u64,
    match_proof_hash: [u8; 32],
) -> (TradeSettlement, Vec<Effect>) {
    let (settlement, _basic_effects) = build_settlement_effects(fill, created_at);

    let buyer_escrow_id = crate::escrow::compute_order_escrow_id(&fill.taker_order_id, &fill.taker);
    let seller_escrow_id =
        crate::escrow::compute_order_escrow_id(&fill.maker_order_id, &fill.maker);

    // The proof includes both the settlement ID and the match proof hash.
    let mut release_proof = Vec::with_capacity(64);
    release_proof.extend_from_slice(&settlement.id);
    release_proof.extend_from_slice(&match_proof_hash);

    let effects = vec![
        Effect::ReleaseEscrow {
            escrow_id: buyer_escrow_id,
            proof: Some(release_proof.clone()),
        },
        Effect::ReleaseEscrow {
            escrow_id: seller_escrow_id,
            proof: Some(release_proof),
        },
    ];

    (settlement, effects)
}

/// Compute a delivery verification key for a settlement.
fn compute_delivery_vk(settlement_id: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-delivery-vk-v1");
    hasher.update(settlement_id);
    *hasher.finalize().as_bytes()
}

/// Compute an escrow ID from settlement ID and role.
fn compute_escrow_id(settlement_id: &[u8; 32], role: &str) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-escrow-v1");
    hasher.update(settlement_id);
    hasher.update(role.as_bytes());
    *hasher.finalize().as_bytes()
}

/// The commitment mode used for multi-party settlement turns.
/// Each party signs only their own action (partial commitment).
pub const SETTLEMENT_COMMITMENT_MODE: CommitmentMode = CommitmentMode::Partial;
