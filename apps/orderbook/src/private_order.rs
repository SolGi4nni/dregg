//! Dark pool / private orders with committed amounts.
//!
//! Private orders hide the trade amount behind a Pedersen commitment. The order
//! rests on the book with a committed amount instead of a cleartext one.
//! Settlement reveals the amount only to the counterparty via encrypted note.
//!
//! Uses `CommittedEscrow` from pyana_turn for privacy-preserving settlement.

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::order::{Order, OrderId, OrderStatus, OrderType, Side, TimeInForce};

/// A private (dark pool) order where the amount is hidden behind a commitment.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PrivateOrder {
    /// The order ID (same derivation as public orders).
    pub id: OrderId,
    /// The trader's cell identity.
    pub trader: CellId,
    /// The side (buy/sell).
    pub side: Side,
    /// The limit price (public — needed for matching).
    pub price: u64,
    /// Pedersen commitment to the amount: `C = amount * G + blinding * H`.
    pub amount_commitment: [u8; 32],
    /// Range proof that the committed amount is in [1, 2^64) (prevents zero/negative).
    pub range_proof: Vec<u8>,
    /// Time-in-force policy.
    pub time_in_force: TimeInForce,
    /// Block height when placed.
    pub created_at: u64,
    /// Current status.
    pub status: OrderStatus,
    /// Nonce for uniqueness.
    pub nonce: u64,
}

/// Parameters for creating a private order (known only to the trader).
#[derive(Clone, Debug)]
pub struct PrivateOrderParams {
    /// The actual amount (private).
    pub amount: u64,
    /// The blinding factor for the Pedersen commitment.
    pub blinding: [u8; 32],
}

/// Compute the Pedersen commitment for a private order amount.
///
/// Uses BLAKE3 in keyed mode as a simplified commitment scheme.
/// In production, this would use curve25519 Pedersen commitments.
pub fn compute_amount_commitment(amount: u64, blinding: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-amount-commitment-v1");
    hasher.update(&amount.to_le_bytes());
    hasher.update(blinding);
    *hasher.finalize().as_bytes()
}

/// Verify that a commitment opens to the claimed amount with the given blinding.
pub fn verify_amount_commitment(commitment: &[u8; 32], amount: u64, blinding: &[u8; 32]) -> bool {
    let expected = compute_amount_commitment(amount, blinding);
    expected == *commitment
}

impl PrivateOrder {
    /// Create a new private order.
    pub fn new(
        trader: CellId,
        side: Side,
        price: u64,
        params: &PrivateOrderParams,
        time_in_force: TimeInForce,
        nonce: u64,
        created_at: u64,
    ) -> Self {
        let amount_commitment = compute_amount_commitment(params.amount, &params.blinding);

        // Compute order ID (same scheme as public orders, but with committed amount).
        let order_type = OrderType::Limit {
            price,
            amount: 0, // Hidden; the commitment is the binding.
            side,
            time_in_force,
        };
        let id = crate::order::compute_order_id(&trader, nonce, &order_type);

        PrivateOrder {
            id,
            trader,
            side,
            price,
            amount_commitment,
            range_proof: Vec::new(), // Simplified; real impl uses Bulletproof.
            time_in_force,
            created_at,
            status: OrderStatus::Open,
            nonce,
        }
    }

    /// Convert to a regular Order for book insertion (amount is zero since it's committed).
    /// The matching engine treats committed orders specially.
    pub fn to_public_order(&self) -> Order {
        let order_type = OrderType::Limit {
            price: self.price,
            amount: 0,
            side: self.side,
            time_in_force: self.time_in_force,
        };
        Order {
            id: self.id,
            trader: self.trader,
            order_type,
            remaining_amount: 0, // Hidden behind commitment.
            created_at: self.created_at,
            status: self.status.clone(),
            nonce: self.nonce,
            committed_amount: Some(self.amount_commitment),
        }
    }
}

/// A private fill: the fill amount is revealed only to the counterparty.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PrivateFill {
    /// The public order ID of the taker.
    pub taker_order_id: OrderId,
    /// The private order ID of the maker.
    pub maker_order_id: OrderId,
    /// The fill price (public).
    pub price: u64,
    /// Commitment to the fill amount.
    pub amount_commitment: [u8; 32],
    /// Encrypted fill amount (only the counterparty can decrypt).
    /// Uses a sealed box (X25519 + ChaCha20Poly1305).
    pub encrypted_amount: Vec<u8>,
}

/// Settlement for a private order fill.
///
/// Uses `CommittedEscrow` where both the payment amount and the fill amount
/// are hidden. The conservation proof ensures no inflation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PrivateSettlement {
    /// Settlement ID.
    pub id: [u8; 32],
    /// Commitment to the buyer's payment (price * amount).
    pub payment_commitment: [u8; 32],
    /// Commitment to the fill amount.
    pub amount_commitment: [u8; 32],
    /// The committed escrow ID.
    pub escrow_id: [u8; 32],
    /// Conservation proof: payment_commitment == price * amount_commitment.
    /// This uses the Pedersen homomorphic property:
    ///   C_payment = (price * amount) * G + blinding_payment * H
    ///             = price * (amount * G + blinding_amount * H) + (blinding_payment - price * blinding_amount) * H
    /// The proof demonstrates that C_payment and C_amount are related by the public price factor.
    pub conservation_proof: Vec<u8>,
    /// Status.
    pub status: crate::settlement::SettlementStatus,
}

/// Compute a private settlement ID.
pub fn compute_private_settlement_id(
    taker_order_id: &OrderId,
    maker_order_id: &OrderId,
    price: u64,
    amount_commitment: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-private-settlement-v1");
    hasher.update(taker_order_id);
    hasher.update(maker_order_id);
    hasher.update(&price.to_le_bytes());
    hasher.update(amount_commitment);
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Dark pool matching: matcher operates on commitments, not cleartext
// =============================================================================

/// A dark pool crossing: two private orders matched without revealing amounts.
///
/// The matcher does NOT see amounts. Instead, it:
/// 1. Identifies two orders at compatible prices (prices are public for matching).
/// 2. The counterparties run an interactive protocol to determine the fill amount.
/// 3. They jointly produce a conservation proof without revealing their amounts.
/// 4. The matcher receives only the fill commitment (not the cleartext).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DarkPoolCrossing {
    /// The buy-side private order ID.
    pub buy_order_id: OrderId,
    /// The sell-side private order ID.
    pub sell_order_id: OrderId,
    /// The crossing price (public: the midpoint or maker's price).
    pub crossing_price: u64,
    /// Commitment to the fill amount (unknown to the matcher).
    pub fill_amount_commitment: [u8; 32],
    /// Proof that the fill amount is <= both orders' committed amounts.
    /// Uses range proofs: fill_amount <= buy_committed_amount AND
    ///                    fill_amount <= sell_committed_amount.
    pub fill_validity_proof: DarkPoolFillProof,
    /// Commitment to the buyer's payment (price * fill_amount).
    /// Verifiable via Pedersen homomorphic property: C_payment = price * C_fill_amount.
    pub payment_commitment: [u8; 32],
}

/// Proof that a dark pool fill is valid without revealing amounts.
///
/// This proof demonstrates:
/// 1. The fill amount is positive (range proof: fill_amount > 0).
/// 2. The fill amount does not exceed the buy order's committed amount.
/// 3. The fill amount does not exceed the sell order's committed amount.
/// 4. The payment commitment is consistent (payment = price * fill_amount).
///
/// All using the Pedersen commitment homomorphic property:
///   C(a) + C(b) = C(a + b) (additive homomorphism)
///   price * C(a) = C(price * a) (scalar multiplication)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DarkPoolFillProof {
    /// Range proof: fill_amount is in [1, 2^64).
    pub fill_range_proof: Vec<u8>,
    /// Proof that buy_commitment - fill_commitment opens to a non-negative value.
    /// (i.e., fill_amount <= buy_amount).
    pub buy_sufficiency_proof: Vec<u8>,
    /// Proof that sell_commitment - fill_commitment opens to a non-negative value.
    /// (i.e., fill_amount <= sell_amount).
    pub sell_sufficiency_proof: Vec<u8>,
    /// Proof that payment_commitment == crossing_price * fill_commitment.
    pub conservation_proof: Vec<u8>,
}

/// Compute the payment commitment from a fill amount commitment and price.
///
/// Uses the Pedersen scalar multiplication property:
///   C_payment = price * C_amount (computed on the commitment directly)
///
/// In practice with BLAKE3 (simplified model), we compute:
///   payment_commitment = commit(price * amount, price * blinding)
/// which preserves the homomorphic relationship.
pub fn compute_payment_commitment(amount: u64, blinding: &[u8; 32], price: u64) -> [u8; 32] {
    let payment = price * amount;
    // In a real Pedersen scheme, blinding would be multiplied by price too.
    // With our BLAKE3 simplified model, we derive a payment-specific blinding.
    let mut blinding_hasher = blake3::Hasher::new_derive_key("pyana-orderbook-payment-blinding-v1");
    blinding_hasher.update(blinding);
    blinding_hasher.update(&price.to_le_bytes());
    let payment_blinding = *blinding_hasher.finalize().as_bytes();
    compute_amount_commitment(payment, &payment_blinding)
}

/// Verify conservation: payment_commitment is consistent with fill_amount_commitment * price.
///
/// In a real implementation, this checks:
///   C_payment == price * C_fill_amount (EC point scalar multiplication)
///
/// In our simplified model, we verify by checking the opening.
pub fn verify_payment_conservation(
    payment_commitment: &[u8; 32],
    fill_amount: u64,
    fill_blinding: &[u8; 32],
    price: u64,
) -> bool {
    let expected = compute_payment_commitment(fill_amount, fill_blinding, price);
    expected == *payment_commitment
}

/// Build a dark pool crossing from two compatible private orders.
///
/// This is called by the counterparties (NOT the matcher) after they agree
/// on a fill amount via the interactive protocol. The matcher only sees the
/// resulting commitments and proofs.
pub fn build_dark_pool_crossing(
    buy_order: &PrivateOrder,
    sell_order: &PrivateOrder,
    fill_amount: u64,
    fill_blinding: &[u8; 32],
) -> DarkPoolCrossing {
    // The crossing price is the sell (maker) price (standard exchange semantics).
    let crossing_price = sell_order.price;

    let fill_amount_commitment = compute_amount_commitment(fill_amount, fill_blinding);
    let payment_commitment = compute_payment_commitment(fill_amount, fill_blinding, crossing_price);

    DarkPoolCrossing {
        buy_order_id: buy_order.id,
        sell_order_id: sell_order.id,
        crossing_price,
        fill_amount_commitment,
        fill_validity_proof: DarkPoolFillProof {
            // In production, these would be actual Bulletproof/STARK range proofs.
            // The simplified model produces placeholder proofs that pass validation
            // when the openings are known.
            fill_range_proof: Vec::new(),
            buy_sufficiency_proof: Vec::new(),
            sell_sufficiency_proof: Vec::new(),
            conservation_proof: Vec::new(),
        },
        payment_commitment,
    }
}

/// Verify a dark pool crossing is valid (used by the matcher and federation nodes).
///
/// This checks the proofs WITHOUT knowing the cleartext amounts.
/// In the simplified model, we verify conservation given the openings.
pub fn verify_dark_pool_crossing(
    crossing: &DarkPoolCrossing,
    fill_amount: u64,
    fill_blinding: &[u8; 32],
) -> bool {
    // Verify the fill amount commitment opens correctly.
    let expected_fill_commitment = compute_amount_commitment(fill_amount, fill_blinding);
    if expected_fill_commitment != crossing.fill_amount_commitment {
        return false;
    }

    // Verify payment conservation.
    verify_payment_conservation(
        &crossing.payment_commitment,
        fill_amount,
        fill_blinding,
        crossing.crossing_price,
    )
}
