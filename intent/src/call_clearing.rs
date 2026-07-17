//! Uniform-price call clearing — the DrEX rung-4 price-discovery primitive as a
//! small, pure function over a two-sided book.
//!
//! The ring solver (`solver.rs`) clears **Coincidences of Wants** — asset cycles
//! with per-leg rate *bounds*, no common numéraire, no single price. Some
//! callers instead need the one thing a ring does not by itself yield: a **single
//! uniform clearing price** discovered by a two-sided book of bids and asks. That
//! is the Budish FBA / CoW UDCP discipline the DrEX design names as its fairness
//! apex (`docs/deos/DREX-DESIGN.md` §3 #4, rung 4): all matched participants
//! trade at ONE price, so intra-batch ordering is economically irrelevant.
//!
//! This module is that call auction, standalone and allocation-free: it does not
//! move value (no ledger, no `settleRing`), it only **discovers the price** a
//! separate conserving settlement then charges. `dregg-pay` consumes it to price
//! a run credit by market clearing instead of a hardcoded constant — the cleared
//! price feeds a single conserving `Effect::Transfer`, and the settlement's
//! conservation is unaffected by where the *scalar* came from.
//!
//! ## The clearing rule (a real crossing, not a stub)
//!
//! Bids are the demand curve (sorted by price **descending** — the most a buyer
//! will pay), asks the supply curve (sorted **ascending** — the least a seller
//! will accept). We walk both cumulatively and match units while the marginal
//! bid still meets the marginal ask (`bid_price >= ask_price`). The equilibrium
//! quantity is where the curves cross; the **uniform price** is the midpoint of
//! the last-matched bid and ask, which is guaranteed to lie in the interval
//! `[marginal_ask, marginal_bid]` — a price every matched buyer accepts (it is
//! ≤ their bid) and every matched seller accepts (it is ≥ their ask).
//!
//! ## Fail-closed
//!
//! A book that does not cross — every bid strictly below every ask, or an empty
//! side — clears **nothing** ([`clear_uniform_price`] returns `None`). It never
//! invents a price. The caller decides the fallback (dregg-pay falls back to its
//! fixed default rather than charge a garbage price).

/// A buy order: a participant willing to buy up to `qty` units at any unit price
/// **at or below** `max_price`. The demand side of the book.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bid {
    /// The most this buyer will pay per unit (the reservation price).
    pub max_price: u64,
    /// How many units this buyer wants at that price.
    pub qty: u64,
}

impl Bid {
    /// A bid for `qty` units at a reservation price of `max_price` per unit.
    pub fn new(max_price: u64, qty: u64) -> Self {
        Self { max_price, qty }
    }
}

/// A sell order: a participant willing to sell up to `qty` units at any unit price
/// **at or above** `min_price`. The supply side of the book.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ask {
    /// The least this seller will accept per unit (the reservation price).
    pub min_price: u64,
    /// How many units this seller offers at that price.
    pub qty: u64,
}

impl Ask {
    /// An ask for `qty` units at a reservation price of `min_price` per unit.
    pub fn new(min_price: u64, qty: u64) -> Self {
        Self { min_price, qty }
    }
}

/// The result of a crossing: the single uniform price all matched participants
/// trade at, and the total quantity cleared at that price.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClearingResult {
    /// The uniform clearing price. Lies in `[marginal_ask, marginal_bid]`: every
    /// matched buyer pays ≤ its bid, every matched seller receives ≥ its ask.
    pub price: u64,
    /// The total number of units that cleared at [`ClearingResult::price`].
    pub cleared_qty: u64,
}

/// **Clear a two-sided book at a single uniform price.**
///
/// Returns `Some(ClearingResult)` when the demand and supply curves cross — i.e.
/// there is at least one unit whose marginal bid meets its marginal ask. Returns
/// `None` when the book does not cross (a bid strictly below every ask, or an
/// empty side): a non-crossing book **clears nothing and invents no price**.
///
/// The inputs are not mutated; the sort is on local copies.
pub fn clear_uniform_price(bids: &[Bid], asks: &[Ask]) -> Option<ClearingResult> {
    if bids.is_empty() || asks.is_empty() {
        return None;
    }

    // Demand descending (highest willingness-to-pay first), supply ascending
    // (lowest ask first) — the standard call-auction curves.
    let mut bids: Vec<Bid> = bids.iter().copied().filter(|b| b.qty > 0).collect();
    let mut asks: Vec<Ask> = asks.iter().copied().filter(|a| a.qty > 0).collect();
    if bids.is_empty() || asks.is_empty() {
        return None;
    }
    bids.sort_by(|a, b| b.max_price.cmp(&a.max_price));
    asks.sort_by(|a, b| a.min_price.cmp(&b.min_price));

    let (mut i, mut j) = (0usize, 0usize);
    let mut bid_rem = bids[0].qty;
    let mut ask_rem = asks[0].qty;
    let mut cleared_qty: u64 = 0;
    // The last matched marginal prices bracket the equilibrium.
    let mut marginal_bid = 0u64;
    let mut marginal_ask = 0u64;

    while i < bids.len() && j < asks.len() {
        let bid_price = bids[i].max_price;
        let ask_price = asks[j].min_price;
        // The crossing ends the moment the marginal bid can no longer meet the
        // marginal ask. This is the equilibrium quantity.
        if bid_price < ask_price {
            break;
        }
        let m = bid_rem.min(ask_rem);
        cleared_qty = cleared_qty.saturating_add(m);
        marginal_bid = bid_price;
        marginal_ask = ask_price;
        bid_rem -= m;
        ask_rem -= m;
        if bid_rem == 0 {
            i += 1;
            if i < bids.len() {
                bid_rem = bids[i].qty;
            }
        }
        if ask_rem == 0 {
            j += 1;
            if j < asks.len() {
                ask_rem = asks[j].qty;
            }
        }
    }

    if cleared_qty == 0 {
        return None;
    }

    // Uniform price = midpoint of the two marginal reservation prices, which
    // satisfies marginal_ask <= price <= marginal_bid (we only matched while
    // marginal_bid >= marginal_ask). Averaging without overflow.
    let price = marginal_ask + (marginal_bid - marginal_ask) / 2;
    Some(ClearingResult { price, cleared_qty })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A crossing book clears at a uniform price inside `[marginal_ask, marginal_bid]`.
    #[test]
    fn crossing_book_clears_uniform() {
        // Buyer will pay up to 12, seller accepts down to 8 → they cross.
        let bids = [Bid::new(12, 5)];
        let asks = [Ask::new(8, 5)];
        let r = clear_uniform_price(&bids, &asks).expect("a crossing book clears");
        assert!(r.price >= 8 && r.price <= 12, "price {} in [8,12]", r.price);
        assert_eq!(r.price, 10, "midpoint of 8 and 12");
        assert_eq!(r.cleared_qty, 5);
    }

    /// A bid strictly below the ask does NOT clear — the crossing is real, not a stub.
    #[test]
    fn bid_below_ask_does_not_clear() {
        let bids = [Bid::new(5, 10)];
        let asks = [Ask::new(10, 10)];
        assert_eq!(clear_uniform_price(&bids, &asks), None);
    }

    /// An empty side clears nothing (fail-closed, no invented price).
    #[test]
    fn empty_side_clears_nothing() {
        assert_eq!(clear_uniform_price(&[], &[Ask::new(1, 1)]), None);
        assert_eq!(clear_uniform_price(&[Bid::new(1, 1)], &[]), None);
        assert_eq!(clear_uniform_price(&[], &[]), None);
    }

    /// The clearing quantity stops at the crossing: extra out-of-the-money orders
    /// on either side do not inflate the cleared quantity or move the price out of
    /// the in-the-money bracket.
    #[test]
    fn quantity_stops_at_the_crossing() {
        // In-the-money: bid 20 for 3 meets ask 10 for 3. Out-of-the-money: a
        // second bid at 5 cannot meet the next ask at 30.
        let bids = [Bid::new(20, 3), Bid::new(5, 100)];
        let asks = [Ask::new(10, 3), Ask::new(30, 100)];
        let r = clear_uniform_price(&bids, &asks).expect("the in-the-money units cross");
        assert_eq!(r.cleared_qty, 3, "only the crossing units clear");
        assert_eq!(r.price, 15, "midpoint of the marginal 20 and 10");
    }

    /// Multiple orders on each side aggregate into cumulative curves; the price is
    /// set by the marginal (last-matched) pair.
    #[test]
    fn cumulative_curves_price_at_the_margin() {
        // Demand: 4 units @≤30, then 4 @≤14. Supply: 4 @≥6, then 4 @≥12.
        // Units 1-4 cross (30≥6). Units 5-8: marginal bid 14 ≥ marginal ask 12 → cross.
        let bids = [Bid::new(30, 4), Bid::new(14, 4)];
        let asks = [Ask::new(6, 4), Ask::new(12, 4)];
        let r = clear_uniform_price(&bids, &asks).expect("both tranches cross");
        assert_eq!(r.cleared_qty, 8);
        assert_eq!(
            r.price, 13,
            "midpoint of marginal bid 14 and marginal ask 12"
        );
    }

    /// Zero-quantity orders are ignored (they carry no demand/supply).
    #[test]
    fn zero_quantity_orders_ignored() {
        let bids = [Bid::new(100, 0)];
        let asks = [Ask::new(1, 1)];
        assert_eq!(clear_uniform_price(&bids, &asks), None);
    }
}
