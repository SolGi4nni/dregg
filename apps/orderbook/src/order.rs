//! Order types for the financial trading orderbook.
//!
//! Supports limit orders, market orders, stop-loss orders, and various
//! time-in-force policies (GTC, GTD, IOC, FOK).

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

/// Unique identifier for an order, derived from `blake3(trader_cell_id, nonce, params)`.
pub type OrderId = [u8; 32];

/// Which side of the book the order is on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Side {
    /// Buying the base asset (bid).
    Buy,
    /// Selling the base asset (ask).
    Sell,
}

/// Time-in-force policy controlling how long an order remains active.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TimeInForce {
    /// Good-Till-Cancelled: remains on the book until explicitly cancelled or filled.
    GTC,
    /// Good-Till-Date: remains on the book until `expiry_height` is reached.
    GTD { expiry_height: u64 },
    /// Immediate-Or-Cancel: execute immediately (partial fills OK), cancel any unfilled remainder.
    IOC,
    /// Fill-Or-Kill: execute entirely in one match or reject entirely.
    FOK,
}

/// The type of order being placed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderType {
    /// Limit order: trade at a specified price or better.
    Limit {
        /// Price per unit of the base asset (in quote asset smallest denomination).
        price: u64,
        /// Quantity of base asset to trade.
        amount: u64,
        /// Buy or sell.
        side: Side,
        /// Time-in-force policy.
        time_in_force: TimeInForce,
    },
    /// Market order: trade immediately at the best available price.
    Market {
        /// Quantity of base asset to trade.
        amount: u64,
        /// Buy or sell.
        side: Side,
        /// Maximum acceptable slippage in basis points from the best price.
        slippage_bps: u16,
    },
    /// Stop-loss order: becomes a market order when the oracle price crosses the trigger.
    /// Implemented as a `ConditionalTurn` that activates on price condition.
    StopLoss {
        /// Price at which the stop triggers.
        trigger_price: u64,
        /// Quantity of base asset to trade when triggered.
        amount: u64,
        /// Buy or sell (typically sell for stop-loss, buy for stop-buy).
        side: Side,
    },
}

/// An order on the book.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Order {
    /// Content-addressed order ID: `blake3(trader_cell_id || nonce || order_type_bytes)`.
    pub id: OrderId,
    /// The trader's cell identity.
    pub trader: CellId,
    /// The type of order with its parameters.
    pub order_type: OrderType,
    /// Remaining unfilled amount (decreases as partial fills occur).
    pub remaining_amount: u64,
    /// Block height when this order was placed.
    pub created_at: u64,
    /// Current lifecycle status.
    pub status: OrderStatus,
    /// Nonce for uniqueness (provided by the trader).
    pub nonce: u64,
    /// Optional: Pedersen commitment to the amount (for private/dark pool orders).
    /// When set, `remaining_amount` is 0 and the true amount is hidden.
    pub committed_amount: Option<[u8; 32]>,
}

/// Order lifecycle status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderStatus {
    /// Active on the book, waiting for a match.
    Open,
    /// Partially filled; residual remains on the book.
    PartiallyFilled { filled_amount: u64 },
    /// Completely filled.
    Filled,
    /// Cancelled by the owner.
    Cancelled,
    /// Expired (GTD time-in-force exceeded).
    Expired,
    /// Stop-loss: waiting for trigger price to be hit.
    Pending,
}

/// Compute a content-addressed order ID.
pub fn compute_order_id(trader: &CellId, nonce: u64, order_type: &OrderType) -> OrderId {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-order-v1");
    hasher.update(trader.as_bytes());
    hasher.update(&nonce.to_le_bytes());
    let type_bytes = postcard::to_allocvec(order_type).unwrap_or_default();
    hasher.update(&type_bytes);
    *hasher.finalize().as_bytes()
}

impl Order {
    /// Create a new order from its parameters.
    pub fn new(trader: CellId, order_type: OrderType, nonce: u64, created_at: u64) -> Self {
        let id = compute_order_id(&trader, nonce, &order_type);
        let remaining_amount = match &order_type {
            OrderType::Limit { amount, .. } => *amount,
            OrderType::Market { amount, .. } => *amount,
            OrderType::StopLoss { amount, .. } => *amount,
        };
        let status = match &order_type {
            OrderType::StopLoss { .. } => OrderStatus::Pending,
            _ => OrderStatus::Open,
        };
        Order {
            id,
            trader,
            order_type,
            remaining_amount,
            created_at,
            status,
            nonce,
            committed_amount: None,
        }
    }

    /// The side of this order (buy or sell).
    pub fn side(&self) -> Side {
        match &self.order_type {
            OrderType::Limit { side, .. } => *side,
            OrderType::Market { side, .. } => *side,
            OrderType::StopLoss { side, .. } => *side,
        }
    }

    /// The limit price of this order (None for market orders).
    pub fn price(&self) -> Option<u64> {
        match &self.order_type {
            OrderType::Limit { price, .. } => Some(*price),
            OrderType::Market { .. } => None,
            OrderType::StopLoss { .. } => None,
        }
    }

    /// The time-in-force policy for this order.
    pub fn time_in_force(&self) -> TimeInForce {
        match &self.order_type {
            OrderType::Limit { time_in_force, .. } => *time_in_force,
            // Market orders are implicitly IOC.
            OrderType::Market { .. } => TimeInForce::IOC,
            // Stop-loss orders are GTC until triggered.
            OrderType::StopLoss { .. } => TimeInForce::GTC,
        }
    }

    /// Whether this order is still active (can participate in matching).
    pub fn is_active(&self) -> bool {
        matches!(
            self.status,
            OrderStatus::Open | OrderStatus::PartiallyFilled { .. }
        )
    }
}
