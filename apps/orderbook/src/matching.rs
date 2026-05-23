//! MatchingEngine: price-time priority matching with partial fills.
//!
//! The engine takes an incoming order and matches it against the opposite side of
//! the book. It enforces:
//! - Price priority: best-priced resting orders fill first.
//! - Time priority: within a price level, earliest order fills first (FIFO).
//! - Partial fills: an incoming order can partially fill against multiple resting orders.
//! - Slippage protection: market orders reject if slippage exceeds the configured limit.
//! - Self-trade prevention: orders from the same trader are skipped.

use crate::book::OrderBook;
use crate::order::{Order, OrderId, OrderStatus, OrderType, Side, TimeInForce};
use pyana_types::CellId;

/// A single fill event representing a trade between a taker and a maker.
#[derive(Clone, Debug)]
pub struct Fill {
    /// The taker order ID.
    pub taker_order_id: OrderId,
    /// The maker (resting) order ID.
    pub maker_order_id: OrderId,
    /// The price at which the fill occurred (always the maker's limit price).
    pub price: u64,
    /// The quantity filled.
    pub amount: u64,
    /// The taker's cell ID.
    pub taker: CellId,
    /// The maker's cell ID.
    pub maker: CellId,
    /// Which side the taker is on.
    pub taker_side: Side,
}

/// Result of matching an incoming order against the book.
#[derive(Clone, Debug)]
pub struct MatchResult {
    /// All fills that occurred.
    pub fills: Vec<Fill>,
    /// The residual order (if the incoming order was not fully filled and should rest).
    /// None if the order was fully filled, or was IOC/FOK and got cancelled/rejected.
    pub residual: Option<Order>,
    /// Whether the incoming order was fully filled.
    pub fully_filled: bool,
    /// Total quantity filled across all fills.
    pub total_filled: u64,
}

/// Errors from the matching engine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatchError {
    /// Fill-or-Kill order cannot be fully satisfied.
    FillOrKillRejected { available: u64, required: u64 },
    /// Market order slippage exceeds the configured limit.
    SlippageExceeded {
        best_price: u64,
        worst_fill_price: u64,
        limit_bps: u16,
    },
    /// Self-trade prevention: the only available liquidity is the taker's own orders.
    SelfTradeOnly,
    /// No liquidity on the opposite side.
    NoLiquidity,
}

impl std::fmt::Display for MatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FillOrKillRejected {
                available,
                required,
            } => {
                write!(
                    f,
                    "FOK rejected: {} available, {} required",
                    available, required
                )
            }
            Self::SlippageExceeded {
                best_price,
                worst_fill_price,
                limit_bps,
            } => {
                write!(
                    f,
                    "slippage exceeded: best={}, worst_fill={}, limit={}bps",
                    best_price, worst_fill_price, limit_bps
                )
            }
            Self::SelfTradeOnly => write!(f, "self-trade prevention: only own orders available"),
            Self::NoLiquidity => write!(f, "no liquidity on opposite side"),
        }
    }
}

/// The matching engine: processes incoming orders against the book.
pub struct MatchingEngine;

impl MatchingEngine {
    /// Match an incoming order against the book.
    ///
    /// This is the core matching algorithm:
    /// 1. Walk the opposite side of the book in price-time priority order.
    /// 2. Skip orders from the same trader (self-trade prevention).
    /// 3. For each matchable resting order, compute the fill amount.
    /// 4. Record the fill and update the resting order's remaining amount.
    /// 5. Continue until the incoming order is fully filled or no more matches exist.
    /// 6. Handle time-in-force: IOC cancels remainder, FOK rejects if not fully filled,
    ///    GTC/GTD posts the remainder to the book.
    pub fn match_order(book: &mut OrderBook, incoming: Order) -> Result<MatchResult, MatchError> {
        let taker_side = incoming.side();
        let taker_id = incoming.id;
        let taker_trader = incoming.trader;
        let time_in_force = incoming.time_in_force();

        // For FOK, pre-check: is there enough liquidity to fill entirely?
        if time_in_force == TimeInForce::FOK {
            let available = Self::available_liquidity(book, taker_side, &taker_trader, &incoming);
            if available < incoming.remaining_amount {
                return Err(MatchError::FillOrKillRejected {
                    available,
                    required: incoming.remaining_amount,
                });
            }
        }

        let mut fills = Vec::new();
        let mut remaining = incoming.remaining_amount;
        let mut orders_to_remove: Vec<OrderId> = Vec::new();
        let mut worst_fill_price: Option<u64> = None;

        // Walk the opposite side in price-time priority.
        // For a buy taker, walk asks (lowest first). For a sell taker, walk bids (highest first).
        let prices_to_walk: Vec<u64> = match taker_side {
            Side::Buy => book.asks_mut().keys().copied().collect(),
            Side::Sell => book.bids_mut().keys().rev().copied().collect(),
        };

        'price_loop: for price in prices_to_walk {
            // Price compatibility check for limit orders.
            if let Some(limit_price) = incoming.price() {
                match taker_side {
                    Side::Buy => {
                        if price > limit_price {
                            break 'price_loop; // asks above our limit, stop
                        }
                    }
                    Side::Sell => {
                        if price < limit_price {
                            break 'price_loop; // bids below our limit, stop
                        }
                    }
                }
            }

            // Slippage check for market orders.
            if let OrderType::Market {
                slippage_bps, side, ..
            } = &incoming.order_type
            {
                if let Some(first_price) = worst_fill_price.or_else(|| match side {
                    Side::Buy => book.best_ask(),
                    Side::Sell => book.best_bid(),
                }) {
                    let slippage = if *side == Side::Buy {
                        // For buys, slippage is (current - best) / best
                        if price > first_price {
                            ((price - first_price) * 10_000) / first_price
                        } else {
                            0
                        }
                    } else {
                        // For sells, slippage is (best - current) / best
                        if first_price > price {
                            ((first_price - price) * 10_000) / first_price
                        } else {
                            0
                        }
                    };
                    if slippage > *slippage_bps as u64 {
                        // Stop matching at this price level (slippage exceeded).
                        break 'price_loop;
                    }
                }
            }

            let levels = match taker_side {
                Side::Buy => book.asks_mut(),
                Side::Sell => book.bids_mut(),
            };

            let level = match levels.get_mut(&price) {
                Some(l) => l,
                None => continue,
            };

            for maker_order in level.orders.iter_mut() {
                if remaining == 0 {
                    break 'price_loop;
                }

                // Self-trade prevention: skip orders from the same trader.
                if maker_order.trader == taker_trader {
                    continue;
                }

                // Skip non-active orders.
                if !maker_order.is_active() {
                    continue;
                }

                // Compute fill amount.
                let fill_amount = remaining.min(maker_order.remaining_amount);

                // Record the fill.
                fills.push(Fill {
                    taker_order_id: taker_id,
                    maker_order_id: maker_order.id,
                    price,
                    amount: fill_amount,
                    taker: taker_trader,
                    maker: maker_order.trader,
                    taker_side,
                });

                // Update state.
                remaining -= fill_amount;
                maker_order.remaining_amount -= fill_amount;
                worst_fill_price = Some(price);

                if maker_order.remaining_amount == 0 {
                    maker_order.status = OrderStatus::Filled;
                    orders_to_remove.push(maker_order.id);
                } else {
                    let filled = match &maker_order.order_type {
                        OrderType::Limit { amount, .. } => amount - maker_order.remaining_amount,
                        _ => fill_amount,
                    };
                    maker_order.status = OrderStatus::PartiallyFilled {
                        filled_amount: filled,
                    };
                }
            }
        }

        // Remove fully-filled maker orders from the index.
        for id in &orders_to_remove {
            book.remove_from_index(id);
        }
        book.clean_empty_levels();

        // Check slippage constraint for market orders (post-match).
        if let OrderType::Market {
            slippage_bps, side, ..
        } = &incoming.order_type
        {
            if !fills.is_empty() {
                let best_price = match side {
                    Side::Buy => fills.first().map(|f| f.price).unwrap_or(0),
                    Side::Sell => fills.first().map(|f| f.price).unwrap_or(0),
                };
                if let Some(worst) = worst_fill_price {
                    let slippage = if *side == Side::Buy {
                        if worst > best_price && best_price > 0 {
                            ((worst - best_price) * 10_000) / best_price
                        } else {
                            0
                        }
                    } else {
                        if best_price > worst && best_price > 0 {
                            ((best_price - worst) * 10_000) / best_price
                        } else {
                            0
                        }
                    };
                    if slippage > *slippage_bps as u64 {
                        return Err(MatchError::SlippageExceeded {
                            best_price,
                            worst_fill_price: worst,
                            limit_bps: *slippage_bps,
                        });
                    }
                }
            }
        }

        let total_filled = incoming.remaining_amount - remaining;
        let fully_filled = remaining == 0;

        // Handle time-in-force for the residual.
        let residual = if fully_filled {
            None
        } else {
            match time_in_force {
                TimeInForce::IOC => {
                    // Cancel unfilled portion.
                    None
                }
                TimeInForce::FOK => {
                    // Should not reach here (pre-checked above), but just in case.
                    return Err(MatchError::FillOrKillRejected {
                        available: total_filled,
                        required: incoming.remaining_amount,
                    });
                }
                TimeInForce::GTC | TimeInForce::GTD { .. } => {
                    // Post residual to the book.
                    if incoming.price().is_some() {
                        let mut residual_order = incoming.clone();
                        residual_order.remaining_amount = remaining;
                        if total_filled > 0 {
                            residual_order.status = OrderStatus::PartiallyFilled {
                                filled_amount: total_filled,
                            };
                        }
                        book.insert_order(residual_order.clone());
                        Some(residual_order)
                    } else {
                        // Market orders cannot rest on the book.
                        None
                    }
                }
            }
        };

        // If no fills occurred and no liquidity available (for non-resting orders).
        if fills.is_empty() && residual.is_none() && !fully_filled {
            if incoming.price().is_none() {
                return Err(MatchError::NoLiquidity);
            }
            // Limit order with no immediate match: post to book.
            if matches!(time_in_force, TimeInForce::GTC | TimeInForce::GTD { .. }) {
                let mut resting = incoming;
                resting.status = OrderStatus::Open;
                book.insert_order(resting.clone());
                return Ok(MatchResult {
                    fills: vec![],
                    residual: Some(resting),
                    fully_filled: false,
                    total_filled: 0,
                });
            }
        }

        Ok(MatchResult {
            fills,
            residual,
            fully_filled,
            total_filled,
        })
    }

    /// Calculate available liquidity on the opposite side that matches the incoming order,
    /// excluding the taker's own orders (self-trade prevention).
    fn available_liquidity(
        book: &OrderBook,
        taker_side: Side,
        taker_trader: &CellId,
        incoming: &Order,
    ) -> u64 {
        let mut total = 0u64;

        let check_level = |level: &crate::book::PriceLevel, total: &mut u64| -> bool {
            // Price compatibility check.
            if let Some(limit_price) = incoming.price() {
                match taker_side {
                    Side::Buy => {
                        if level.price > limit_price {
                            return false; // stop
                        }
                    }
                    Side::Sell => {
                        if level.price < limit_price {
                            return false; // stop
                        }
                    }
                }
            }

            for order in &level.orders {
                if order.trader != *taker_trader && order.is_active() {
                    *total += order.remaining_amount;
                }
            }
            true // continue
        };

        match taker_side {
            Side::Buy => {
                for level in book.ask_levels() {
                    if !check_level(level, &mut total) {
                        break;
                    }
                }
            }
            Side::Sell => {
                for level in book.bid_levels() {
                    if !check_level(level, &mut total) {
                        break;
                    }
                }
            }
        }

        total
    }
}
