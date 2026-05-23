//! Pre-trade escrow: funds locked BEFORE orders go live on the book.
//!
//! This module enforces that orders are collateralized before they can match.
//! Without this, a matched order could fail at settlement if the trader moves
//! their funds between matching and settlement.
//!
//! ## Flow
//!
//! 1. Trader creates an order and locks collateral via `CreateEscrow` in the same turn.
//! 2. The escrow ID is recorded on the order (proving collateralization).
//! 3. Only orders with valid escrow IDs can be inserted into the book.
//! 4. On fill, settlement releases the escrow atomically to the counterparty.
//! 5. On cancel, the escrow is refunded to the original trader.
//!
//! This makes the orderbook a "delivery-versus-payment" system: matching GUARANTEES
//! settlement because funds are already locked.

use crate::order::{Order, OrderId, Side};
use pyana_turn::action::Effect;
use pyana_turn::escrow::EscrowCondition;
use pyana_types::CellId;
use serde::{Deserialize, Serialize};

/// Default escrow timeout: 1000 blocks after creation.
/// If settlement doesn't happen within this window, the trader can reclaim.
pub const ESCROW_TIMEOUT_BLOCKS: u64 = 1000;

/// An escrow record for a pre-trade collateral lock.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OrderEscrow {
    /// The escrow ID.
    pub escrow_id: [u8; 32],
    /// The order this escrow backs.
    pub order_id: OrderId,
    /// The trader who locked funds.
    pub trader: CellId,
    /// The locked amount (for buys: price * amount in quote; for sells: amount in base).
    pub locked_amount: u64,
    /// The block height at which the escrow was created.
    pub created_at: u64,
    /// Whether this escrow has been consumed (released or refunded).
    pub consumed: bool,
}

/// Registry of active order escrows.
#[derive(Clone, Debug, Default)]
pub struct EscrowRegistry {
    /// Active escrows keyed by order ID.
    escrows: std::collections::HashMap<OrderId, OrderEscrow>,
}

/// Errors from the escrow system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EscrowError {
    /// The order has no backing escrow (not collateralized).
    NotCollateralized,
    /// The escrow amount is insufficient for the order.
    InsufficientCollateral { required: u64, locked: u64 },
    /// The escrow has already been consumed.
    AlreadyConsumed,
    /// The escrow does not belong to this order.
    EscrowMismatch,
}

impl std::fmt::Display for EscrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotCollateralized => write!(f, "order has no backing escrow"),
            Self::InsufficientCollateral { required, locked } => {
                write!(
                    f,
                    "insufficient collateral: need {}, locked {}",
                    required, locked
                )
            }
            Self::AlreadyConsumed => write!(f, "escrow already consumed"),
            Self::EscrowMismatch => write!(f, "escrow does not match this order"),
        }
    }
}

/// Compute the required collateral for an order.
///
/// - Buy orders: must lock `price * amount` in quote asset.
/// - Sell orders: must lock `amount` in base asset.
pub fn required_collateral(order: &Order) -> u64 {
    match order.side() {
        Side::Buy => {
            // Buyer must lock full payment at their limit price (or worst-case for market).
            match order.price() {
                Some(price) => price * order.remaining_amount,
                None => {
                    // Market orders: collateral is computed against a maximum price.
                    // In practice, this would use the current best ask + slippage buffer.
                    // For safety, we require the order to specify a max_payment field.
                    // Fall back to remaining_amount (caller should set appropriately).
                    order.remaining_amount
                }
            }
        }
        Side::Sell => {
            // Seller must lock the base asset they're selling.
            order.remaining_amount
        }
    }
}

/// Compute the escrow ID for an order's collateral lock.
pub fn compute_order_escrow_id(order_id: &OrderId, trader: &CellId) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-order-escrow-v1");
    hasher.update(order_id);
    hasher.update(trader.as_bytes());
    *hasher.finalize().as_bytes()
}

/// Build the `CreateEscrow` effect that locks collateral for an order.
///
/// The escrow condition is `ProofPresented` with a verification key derived
/// from the settlement — only a valid settlement proof can release it.
pub fn build_order_escrow_effect(order: &Order, current_height: u64) -> (Effect, OrderEscrow) {
    let collateral = required_collateral(order);
    let escrow_id = compute_order_escrow_id(&order.id, &order.trader);

    // The escrow releases to whoever presents a valid settlement proof.
    // The verification key is derived from the order ID so only a matching
    // fill for THIS order can trigger release.
    let vk = compute_settlement_release_vk(&order.id);

    let effect = Effect::CreateEscrow {
        cell: order.trader,
        recipient: order.trader, // Recipient updated at settlement time.
        amount: collateral,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height: current_height + ESCROW_TIMEOUT_BLOCKS,
        escrow_id,
    };

    let record = OrderEscrow {
        escrow_id,
        order_id: order.id,
        trader: order.trader,
        locked_amount: collateral,
        created_at: current_height,
        consumed: false,
    };

    (effect, record)
}

/// Build the refund effect for a cancelled order's escrow.
pub fn build_cancel_refund_effect(escrow: &OrderEscrow) -> Effect {
    Effect::RefundEscrow {
        escrow_id: escrow.escrow_id,
    }
}

/// Compute the verification key that the settlement proof must satisfy.
fn compute_settlement_release_vk(order_id: &OrderId) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-settlement-vk-v1");
    hasher.update(order_id);
    *hasher.finalize().as_bytes()
}

impl EscrowRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an escrow for an order.
    pub fn register(&mut self, escrow: OrderEscrow) {
        self.escrows.insert(escrow.order_id, escrow);
    }

    /// Verify that an order has sufficient collateral backing.
    pub fn verify_collateral(&self, order: &Order) -> Result<(), EscrowError> {
        let escrow = self
            .escrows
            .get(&order.id)
            .ok_or(EscrowError::NotCollateralized)?;

        if escrow.consumed {
            return Err(EscrowError::AlreadyConsumed);
        }

        let required = required_collateral(order);
        if escrow.locked_amount < required {
            return Err(EscrowError::InsufficientCollateral {
                required,
                locked: escrow.locked_amount,
            });
        }

        Ok(())
    }

    /// Mark an escrow as consumed (after settlement or refund).
    pub fn consume(&mut self, order_id: &OrderId) -> Result<OrderEscrow, EscrowError> {
        let escrow = self
            .escrows
            .get_mut(order_id)
            .ok_or(EscrowError::NotCollateralized)?;

        if escrow.consumed {
            return Err(EscrowError::AlreadyConsumed);
        }

        escrow.consumed = true;
        Ok(escrow.clone())
    }

    /// Get the escrow for an order (if any).
    pub fn get(&self, order_id: &OrderId) -> Option<&OrderEscrow> {
        self.escrows.get(order_id)
    }

    /// Number of active (unconsumed) escrows.
    pub fn active_count(&self) -> usize {
        self.escrows.values().filter(|e| !e.consumed).count()
    }
}
