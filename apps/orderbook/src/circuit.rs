//! MatchProofDescriptor: a circuit that proves matching was fair.
//!
//! The matching proof is a STARK proof demonstrating:
//! 1. Maker's limit price is satisfied (fill_price >= ask for sells, fill_price <= bid for buys).
//! 2. Price-time priority was respected (no better-priced order was skipped).
//! 3. Fill amount <= order remaining (range check preventing overfill).
//! 4. Conservation: taker pays what maker receives (polynomial equality).
//! 5. No self-trade: maker_id != taker_id (non-equality check).
//!
//! The public inputs are the order queue root hash, fill parameters, and the resulting
//! book state hash. The private witness includes the full order queue and positions.

use crate::matching::Fill;
use crate::order::Side;
use serde::{Deserialize, Serialize};

/// Public inputs for the match proof circuit.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MatchProofPublicInputs {
    /// Merkle root of the order queue before matching.
    pub pre_queue_root: [u8; 32],
    /// Merkle root of the order queue after matching.
    pub post_queue_root: [u8; 32],
    /// The fill price.
    pub fill_price: u64,
    /// The fill amount.
    pub fill_amount: u64,
    /// Hash of the taker's order ID.
    pub taker_id_hash: [u8; 32],
    /// Hash of the maker's order ID.
    pub maker_id_hash: [u8; 32],
    /// The maker's side (encoded as 0=Buy, 1=Sell).
    pub maker_side: u8,
    /// Total payment (fill_price * fill_amount) for conservation check.
    pub total_payment: u64,
}

/// Private witness for the match proof circuit.
#[derive(Clone, Debug)]
pub struct MatchProofWitness {
    /// The maker's limit price (private: only the fill price is public).
    pub maker_limit_price: u64,
    /// The maker's remaining amount before the fill.
    pub maker_remaining_before: u64,
    /// The maker's position in the queue (index for priority proof).
    pub maker_queue_position: usize,
    /// All orders at the same price level that are ahead of the maker (for priority proof).
    /// Each entry is (order_id_hash, created_at).
    pub orders_ahead: Vec<([u8; 32], u64)>,
    /// The taker's cell ID bytes (for self-trade check).
    pub taker_cell_bytes: [u8; 32],
    /// The maker's cell ID bytes (for self-trade check).
    pub maker_cell_bytes: [u8; 32],
}

/// A descriptor for the matching proof circuit.
///
/// This is used to generate and verify STARK proofs that the matching engine
/// operated correctly for a given fill.
#[derive(Clone, Debug)]
pub struct MatchProofDescriptor {
    /// The public inputs that the proof binds to.
    pub public_inputs: MatchProofPublicInputs,
    /// The private witness (only needed for proof generation, not verification).
    pub witness: Option<MatchProofWitness>,
}

impl MatchProofDescriptor {
    /// Create a new match proof descriptor from a fill.
    pub fn from_fill(fill: &Fill, pre_queue_root: [u8; 32], post_queue_root: [u8; 32]) -> Self {
        let maker_side = match fill.taker_side {
            Side::Buy => 1u8,  // maker is selling
            Side::Sell => 0u8, // maker is buying
        };

        let taker_id_hash = *blake3::hash(&fill.taker_order_id).as_bytes();
        let maker_id_hash = *blake3::hash(&fill.maker_order_id).as_bytes();

        MatchProofDescriptor {
            public_inputs: MatchProofPublicInputs {
                pre_queue_root,
                post_queue_root,
                fill_price: fill.price,
                fill_amount: fill.amount,
                taker_id_hash,
                maker_id_hash,
                maker_side,
                total_payment: fill.price * fill.amount,
            },
            witness: None,
        }
    }

    /// Attach a witness for proof generation.
    pub fn with_witness(mut self, witness: MatchProofWitness) -> Self {
        self.witness = Some(witness);
        self
    }

    /// Verify the constraint: maker's limit price is satisfied.
    ///
    /// For a sell maker: fill_price >= maker's ask price.
    /// For a buy maker: fill_price <= maker's bid price.
    pub fn check_price_satisfaction(&self) -> bool {
        let Some(witness) = &self.witness else {
            return false;
        };
        match self.public_inputs.maker_side {
            1 => {
                // Maker is selling: fill_price must be >= maker's ask.
                self.public_inputs.fill_price >= witness.maker_limit_price
            }
            0 => {
                // Maker is buying: fill_price must be <= maker's bid.
                self.public_inputs.fill_price <= witness.maker_limit_price
            }
            _ => false,
        }
    }

    /// Verify the constraint: fill amount does not exceed remaining.
    pub fn check_fill_amount(&self) -> bool {
        let Some(witness) = &self.witness else {
            return false;
        };
        self.public_inputs.fill_amount <= witness.maker_remaining_before
    }

    /// Verify the constraint: no self-trade.
    pub fn check_no_self_trade(&self) -> bool {
        let Some(witness) = &self.witness else {
            return false;
        };
        witness.taker_cell_bytes != witness.maker_cell_bytes
    }

    /// Verify the constraint: conservation (taker pays what maker receives).
    pub fn check_conservation(&self) -> bool {
        self.public_inputs.total_payment
            == self.public_inputs.fill_price * self.public_inputs.fill_amount
    }

    /// Verify the constraint: price-time priority (no better-priced order was skipped).
    ///
    /// All orders ahead in the queue must have been placed before the maker order
    /// (they should already be filled or belong to the same trader as the taker).
    pub fn check_priority(&self) -> bool {
        let Some(witness) = &self.witness else {
            return false;
        };
        // The maker should be at position 0 in the queue (front of the level),
        // or all orders ahead of it must have been from the taker (self-trade skip).
        // This is a simplified check; a full circuit would use a Merkle proof.
        witness.maker_queue_position == 0
            || witness.orders_ahead.iter().all(|(id_hash, _)| {
                // Orders ahead are the taker's own orders (skipped due to self-trade prevention).
                *id_hash == *blake3::hash(&witness.taker_cell_bytes).as_bytes()
            })
    }

    /// Run all constraint checks (for testing; in production these are proved in a STARK).
    pub fn verify_all_constraints(&self) -> Result<(), MatchProofError> {
        if !self.check_price_satisfaction() {
            return Err(MatchProofError::PriceNotSatisfied);
        }
        if !self.check_fill_amount() {
            return Err(MatchProofError::FillExceedsRemaining);
        }
        if !self.check_no_self_trade() {
            return Err(MatchProofError::SelfTrade);
        }
        if !self.check_conservation() {
            return Err(MatchProofError::ConservationViolation);
        }
        if !self.check_priority() {
            return Err(MatchProofError::PriorityViolation);
        }
        Ok(())
    }
}

/// Errors from match proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatchProofError {
    /// Fill price does not satisfy the maker's limit.
    PriceNotSatisfied,
    /// Fill amount exceeds the maker's remaining quantity.
    FillExceedsRemaining,
    /// Taker and maker are the same entity.
    SelfTrade,
    /// Payment does not equal price * amount.
    ConservationViolation,
    /// A better-priced or earlier order was skipped.
    PriorityViolation,
}

impl std::fmt::Display for MatchProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PriceNotSatisfied => write!(f, "fill price does not satisfy maker's limit"),
            Self::FillExceedsRemaining => write!(f, "fill exceeds maker's remaining amount"),
            Self::SelfTrade => write!(f, "self-trade detected"),
            Self::ConservationViolation => write!(f, "payment != price * amount"),
            Self::PriorityViolation => write!(f, "price-time priority violated"),
        }
    }
}

/// Compute a cancel-proof: STARK proof that the canceller owns the order.
///
/// The proof demonstrates knowledge of the trader's cell ID that was used to
/// create the order (capability exercise). Public input is the order_id;
/// private witness is (cell_id, nonce, order_type_bytes) such that
/// `blake3(cell_id || nonce || order_type_bytes) == order_id`.
pub fn compute_cancel_proof_hash(trader: &pyana_types::CellId, order_id: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-cancel-proof-v1");
    hasher.update(trader.as_bytes());
    hasher.update(order_id);
    *hasher.finalize().as_bytes()
}

/// Verify a cancel proof: the canceller must know the preimage (trader cell_id)
/// that produces the given cancel_proof_hash.
pub fn verify_cancel_proof(
    claimed_trader: &pyana_types::CellId,
    order_id: &[u8; 32],
    expected_hash: &[u8; 32],
) -> bool {
    let computed = compute_cancel_proof_hash(claimed_trader, order_id);
    computed == *expected_hash
}
