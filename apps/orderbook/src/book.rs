//! OrderBook: price levels with FIFO queues, best bid/ask tracking.
//!
//! The book maintains two sides (bids and asks) as sorted structures.
//! Each price level is a FIFO queue of orders at that price.
//! Price-time priority is enforced: within a price level, earlier orders fill first.

use std::collections::{BTreeMap, VecDeque};

use crate::order::{Order, OrderId, OrderStatus, Side, TimeInForce};

/// A single price level: a FIFO queue of orders all at the same price.
#[derive(Clone, Debug)]
pub struct PriceLevel {
    /// The price for this level.
    pub price: u64,
    /// Orders at this price, in time-priority order (front = oldest).
    pub orders: VecDeque<Order>,
}

impl PriceLevel {
    /// Create a new empty price level.
    pub fn new(price: u64) -> Self {
        PriceLevel {
            price,
            orders: VecDeque::new(),
        }
    }

    /// Total quantity available at this price level.
    pub fn total_quantity(&self) -> u64 {
        self.orders.iter().map(|o| o.remaining_amount).sum()
    }

    /// Whether this price level has any orders.
    pub fn is_empty(&self) -> bool {
        self.orders.is_empty()
    }
}

/// A trading pair identifier.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TradingPair {
    /// The base asset identifier (what you're buying/selling).
    pub base: String,
    /// The quote asset identifier (what you're pricing in).
    pub quote: String,
}

use serde::{Deserialize, Serialize};

impl TradingPair {
    pub fn new(base: impl Into<String>, quote: impl Into<String>) -> Self {
        TradingPair {
            base: base.into(),
            quote: quote.into(),
        }
    }
}

impl std::fmt::Display for TradingPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.base, self.quote)
    }
}

/// The order book for a single trading pair.
///
/// Bids are sorted descending (highest price first — best bid at the top).
/// Asks are sorted ascending (lowest price first — best ask at the top).
#[derive(Clone, Debug)]
pub struct OrderBook {
    /// The trading pair this book is for.
    pub pair: TradingPair,
    /// Bid (buy) side: price -> FIFO queue. BTreeMap sorted ascending, we iterate in reverse.
    bids: BTreeMap<u64, PriceLevel>,
    /// Ask (sell) side: price -> FIFO queue. BTreeMap sorted ascending, best ask = first entry.
    asks: BTreeMap<u64, PriceLevel>,
    /// Lookup table: order_id -> (side, price) for O(1) cancellation.
    order_index: std::collections::HashMap<OrderId, (Side, u64)>,
}

impl OrderBook {
    /// Create a new empty order book for the given trading pair.
    pub fn new(pair: TradingPair) -> Self {
        OrderBook {
            pair,
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            order_index: std::collections::HashMap::new(),
        }
    }

    /// Best bid price (highest buy price), or None if no bids.
    pub fn best_bid(&self) -> Option<u64> {
        self.bids.keys().next_back().copied()
    }

    /// Best ask price (lowest sell price), or None if no asks.
    pub fn best_ask(&self) -> Option<u64> {
        self.asks.keys().next().copied()
    }

    /// The spread (difference between best ask and best bid), or None if either side is empty.
    pub fn spread(&self) -> Option<u64> {
        match (self.best_bid(), self.best_ask()) {
            (Some(bid), Some(ask)) if ask > bid => Some(ask - bid),
            (Some(_), Some(_)) => Some(0), // crossed book
            _ => None,
        }
    }

    /// Total number of active orders on the book.
    pub fn order_count(&self) -> usize {
        self.order_index.len()
    }

    /// Add a limit order to the book (resting, no immediate match).
    /// This does NOT perform matching — call the matching engine for that.
    pub fn insert_order(&mut self, order: Order) {
        let price = order
            .price()
            .expect("only limit orders can rest on the book");
        let side = order.side();
        let id = order.id;

        let levels = match side {
            Side::Buy => &mut self.bids,
            Side::Sell => &mut self.asks,
        };

        levels
            .entry(price)
            .or_insert_with(|| PriceLevel::new(price))
            .orders
            .push_back(order);

        self.order_index.insert(id, (side, price));
    }

    /// Remove an order from the book by its ID. Returns the order if found.
    pub fn remove_order(&mut self, order_id: &OrderId) -> Option<Order> {
        let (side, price) = self.order_index.remove(order_id)?;

        let levels = match side {
            Side::Buy => &mut self.bids,
            Side::Sell => &mut self.asks,
        };

        if let Some(level) = levels.get_mut(&price) {
            let pos = level.orders.iter().position(|o| o.id == *order_id);
            if let Some(idx) = pos {
                let order = level.orders.remove(idx).unwrap();
                if level.is_empty() {
                    levels.remove(&price);
                }
                return Some(order);
            }
        }
        None
    }

    /// Get the best ask orders (front of the lowest-priced ask level).
    /// Returns an iterator over ask price levels from best (lowest) to worst (highest).
    pub fn ask_levels(&self) -> impl Iterator<Item = &PriceLevel> {
        self.asks.values()
    }

    /// Get the best bid orders (front of the highest-priced bid level).
    /// Returns an iterator over bid price levels from best (highest) to worst (lowest).
    pub fn bid_levels(&self) -> impl Iterator<Item = &PriceLevel> {
        self.bids.values().rev()
    }

    /// Get a mutable reference to ask levels for the matching engine.
    pub(crate) fn asks_mut(&mut self) -> &mut BTreeMap<u64, PriceLevel> {
        &mut self.asks
    }

    /// Get a mutable reference to bid levels for the matching engine.
    pub(crate) fn bids_mut(&mut self) -> &mut BTreeMap<u64, PriceLevel> {
        &mut self.bids
    }

    /// Remove the order from the index (used by the matching engine after fills).
    pub(crate) fn remove_from_index(&mut self, order_id: &OrderId) {
        self.order_index.remove(order_id);
    }

    /// Check if an order exists on the book.
    pub fn contains_order(&self, order_id: &OrderId) -> bool {
        self.order_index.contains_key(order_id)
    }

    /// Look up which side and price an order is at.
    pub fn order_location(&self, order_id: &OrderId) -> Option<(Side, u64)> {
        self.order_index.get(order_id).copied()
    }

    /// Get a reference to a resting order by its ID.
    pub fn get_order(&self, order_id: &OrderId) -> Option<&Order> {
        let (side, price) = self.order_index.get(order_id)?;
        let levels = match side {
            Side::Buy => &self.bids,
            Side::Sell => &self.asks,
        };
        levels
            .get(price)
            .and_then(|level| level.orders.iter().find(|o| o.id == *order_id))
    }

    /// Remove all expired orders (GTD whose expiry_height <= current_height).
    pub fn expire_orders(&mut self, current_height: u64) -> Vec<Order> {
        let mut expired = Vec::new();

        // Collect IDs to expire.
        let to_expire: Vec<OrderId> = self
            .order_index
            .keys()
            .filter(|id| {
                if let Some(order) = self.get_order(id) {
                    if let TimeInForce::GTD { expiry_height } = order.time_in_force() {
                        return current_height >= expiry_height;
                    }
                }
                false
            })
            .copied()
            .collect();

        for id in to_expire {
            if let Some(mut order) = self.remove_order(&id) {
                order.status = OrderStatus::Expired;
                expired.push(order);
            }
        }

        expired
    }

    /// Clean up empty price levels (called after matching).
    pub(crate) fn clean_empty_levels(&mut self) {
        self.bids.retain(|_, level| !level.is_empty());
        self.asks.retain(|_, level| !level.is_empty());
    }
}
