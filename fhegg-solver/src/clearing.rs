//! Uniform-price aggregation clearing — the fhEgg kernel at T=1.
//!
//! A batch uniform-price call auction is an AGGREGATION, not a matching
//! (`docs/deos/FHEGG-KERNEL.md` §0, §2). Orders fold into a price-indexed
//! supply/demand curve (a commutative-monoid fold of per-order increments =
//! a histogram + a prefix/suffix scan), and clearing is a SINGLE monotone
//! crossing of that curve. The expensive part of "private matching" (oblivious
//! sort, O(N log²N) bootstraps) never appears: the N-dependent work is O(N)
//! additions into K buckets, the crossing is O(K) and N-independent.
//!
//! This is the UNTRUSTED plaintext solver: it sees every order. Privacy is the
//! STARK-ZK/FHE stage. Correctness here is what the STARK-over-the-fold attests.
//!
//! ## The fold (FHEGG-KERNEL §2.1b)
//!
//! A limit order `(side, qty, limit ℓ)` is one curve increment. On the bid side
//! it adds `qty` to every bucket `p ≤ ℓ` (you buy at any price at or below your
//! limit); on the ask side it adds `qty` to every bucket `p ≥ ℓ` (you sell at
//! any price at or above your limit). We realise the range-add via a per-limit
//! histogram + a scan:
//!
//! ```text
//!   bid_hist[ℓ] = Σ qty over bids with limit == ℓ
//!   ask_hist[ℓ] = Σ qty over asks with limit == ℓ
//!   D(j) = Σ_{ℓ ≥ j} bid_hist[ℓ]   (SUFFIX scan — cumulative demand, non-increasing in j)
//!   S(j) = Σ_{ℓ ≤ j} ask_hist[ℓ]   (PREFIX scan — cumulative supply, non-decreasing in j)
//! ```
//!
//! ## The crossing (FHEGG-KERNEL §2.1c / §1.4)
//!
//! The uniform-price rule picks the price that MAXIMISES traded volume. At price
//! level `j` the matchable volume is `min(D(j), S(j))` (only the smaller side can
//! trade), so
//!
//! ```text
//!   p* = argmax_j min( D(j), S(j) )       (the volume-maximising clearing price)
//!   V* = min( D(p*), S(p*) )              (the cleared uniform-price volume)
//! ```
//!
//! Because `D` is non-increasing and `S` non-decreasing, `min(D, S)` is unimodal
//! (rises then falls), so its peak is the crossing. When the curves genuinely
//! cross in the interior — `∃ j. D(j) ≤ S(j)` with positive overlap — `p*`
//! coincides with the least fixed point of the monotone update
//! `F(j) = j if D(pⱼ) ≤ S(pⱼ) else min(j+1, K)` (FHEGG-KERNEL §1.4 / §2.1c). The
//! volume-max form is the robust general rule: it handles the demand- and
//! supply-dominated regimes (where one curve dominates the other across the whole
//! overlap) and the no-overlap regime (peak volume 0 ⇒ `crossed = false`) that
//! the bare `first-j-with-D≤S` operator mis-reads. Ties in the peak resolve to the
//! LOWEST price index (a deterministic convention).

use serde::Serialize;

/// Which side of the book an order sits on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Side {
    /// A buyer: fills at any price ≤ `limit`.
    Bid,
    /// A seller: fills at any price ≥ `limit`.
    Ask,
}

/// A sealed limit order. `limit` is a price-LEVEL INDEX in `[0, K)`, not a raw
/// price — the public price grid `P = {p₀ < … < p_{K-1}}` maps indices to
/// prices (FHEGG-KERNEL §2.1a). `qty` is an integer amount (exact; no rounding).
#[derive(Clone, Copy, Debug)]
pub struct Order {
    pub side: Side,
    pub qty: u64,
    pub limit: u32,
}

impl Order {
    pub fn bid(qty: u64, limit: u32) -> Self {
        Self {
            side: Side::Bid,
            qty,
            limit,
        }
    }
    pub fn ask(qty: u64, limit: u32) -> Self {
        Self {
            side: Side::Ask,
            qty,
            limit,
        }
    }
}

/// The cleared market: the aggregate curves, the crossing, the allocation.
#[derive(Clone, Debug, Serialize)]
pub struct Clearing {
    pub k: usize,
    /// Cumulative demand `D(j)` over the price grid (non-increasing).
    pub demand: Vec<u64>,
    /// Cumulative supply `S(j)` over the price grid (non-decreasing).
    pub supply: Vec<u64>,
    /// Whether a crossing exists (`∃ j. D(j) ≤ S(j)`).
    pub crossed: bool,
    /// The clearing price INDEX `p*` (valid iff `crossed`).
    pub clearing_price: usize,
    /// The cleared uniform-price volume `V* = min(D(p*), S(p*))`.
    pub cleared_volume: u64,
}

/// Fold N orders into the aggregate curves via the per-limit histogram + scan.
///
/// O(N) additions (the fold) + O(K) scan. This is the CPU reference; `gpu.rs`
/// carries the wgpu histogram path benchmarked against it.
pub fn fold_curves(orders: &[Order], k: usize) -> (Vec<u64>, Vec<u64>) {
    let mut bid_hist = vec![0u64; k];
    let mut ask_hist = vec![0u64; k];
    for o in orders {
        let l = (o.limit as usize).min(k - 1);
        match o.side {
            Side::Bid => bid_hist[l] += o.qty,
            Side::Ask => ask_hist[l] += o.qty,
        }
    }
    scan_curves(&bid_hist, &ask_hist)
}

/// Scan a pair of per-limit histograms into cumulative demand/supply curves.
/// `D` = suffix sum of `bid_hist`, `S` = prefix sum of `ask_hist`.
pub fn scan_curves(bid_hist: &[u64], ask_hist: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let k = bid_hist.len();
    let mut demand = vec![0u64; k];
    let mut supply = vec![0u64; k];
    // Suffix scan for demand.
    let mut acc = 0u64;
    for j in (0..k).rev() {
        acc += bid_hist[j];
        demand[j] = acc;
    }
    // Prefix scan for supply.
    let mut acc = 0u64;
    for j in 0..k {
        acc += ask_hist[j];
        supply[j] = acc;
    }
    (demand, supply)
}

/// Find the crossing: the volume-maximising price `argmax_j min(D(j), S(j))`.
/// Returns `(crossed, p*, V*)` where `crossed = V* > 0`. Ties resolve to the
/// lowest index.
pub fn crossing(demand: &[u64], supply: &[u64]) -> (bool, usize, u64) {
    let k = demand.len();
    let mut best_j = 0usize;
    let mut best_v = 0u64;
    for j in 0..k {
        let v = demand[j].min(supply[j]);
        if v > best_v {
            best_v = v;
            best_j = j;
        }
    }
    (best_v > 0, best_j, best_v)
}

/// The full clearing: fold + scan + crossing.
pub fn clear(orders: &[Order], k: usize) -> Clearing {
    assert!(k >= 1, "price grid must have at least one level");
    let (demand, supply) = fold_curves(orders, k);
    let (crossed, clearing_price, cleared_volume) = crossing(&demand, &supply);
    Clearing {
        k,
        demand,
        supply,
        crossed,
        clearing_price,
        cleared_volume,
    }
}

/// A conserving per-order allocation at the clearing price.
///
/// The short side fills fully; the long side is rationed pro-rata to the qty of
/// its active orders, with a largest-remainder pass so the integer fills sum
/// EXACTLY to `V*` on both sides (conservation: Σ buy fills = Σ sell fills = V*).
#[derive(Clone, Debug, Serialize)]
pub struct Allocation {
    /// Fill amount per order, index-aligned with the input `orders` slice.
    pub fills: Vec<u64>,
    pub buy_volume: u64,
    pub sell_volume: u64,
}

impl Allocation {
    /// True iff the two sides moved equal volume (value-conservation).
    pub fn conserves(&self) -> bool {
        self.buy_volume == self.sell_volume
    }
}

/// Compute the conserving allocation for `orders` given a cleared market.
pub fn allocate(orders: &[Order], clearing: &Clearing) -> Allocation {
    let mut fills = vec![0u64; orders.len()];
    if !clearing.crossed || clearing.cleared_volume == 0 {
        return Allocation {
            fills,
            buy_volume: 0,
            sell_volume: 0,
        };
    }
    let p = clearing.clearing_price as u32;
    let vstar = clearing.cleared_volume;

    // Active orders at p*: bids with limit ≥ p*, asks with limit ≤ p*.
    let active_bids: Vec<usize> = orders
        .iter()
        .enumerate()
        .filter(|(_, o)| o.side == Side::Bid && o.limit >= p)
        .map(|(i, _)| i)
        .collect();
    let active_asks: Vec<usize> = orders
        .iter()
        .enumerate()
        .filter(|(_, o)| o.side == Side::Ask && o.limit <= p)
        .map(|(i, _)| i)
        .collect();

    // The SHORT side (smaller cumulative at p*) fills fully; the long side is
    // rationed pro-rata to V*. `ration` fills fully when the active total ≤
    // target and pro-ratas otherwise, so passing target = V* to both sides does
    // the right thing whichever side is short.
    let buy = ration(orders, &active_bids, vstar);
    let sell = ration(orders, &active_asks, vstar);
    for (i, f) in buy.iter() {
        fills[*i] = *f;
    }
    for (i, f) in sell.iter() {
        fills[*i] = *f;
    }
    let buy_volume: u64 = buy.iter().map(|(_, f)| *f).sum();
    let sell_volume: u64 = sell.iter().map(|(_, f)| *f).sum();
    Allocation {
        fills,
        buy_volume,
        sell_volume,
    }
}

/// Distribute exactly `min(target, total active qty)` across `active` orders.
/// If the active orders' total qty ≤ target (the SHORT side), every order fills
/// fully; otherwise pro-rata by qty with a largest-remainder pass so the sum is
/// EXACTLY `target` (the long side).
fn ration(orders: &[Order], active: &[usize], target: u64) -> Vec<(usize, u64)> {
    let total: u64 = active.iter().map(|&i| orders[i].qty).sum();
    if total == 0 {
        return active.iter().map(|&i| (i, 0u64)).collect();
    }
    if total <= target {
        // Short side: everyone fills fully.
        return active.iter().map(|&i| (i, orders[i].qty)).collect();
    }
    // Pro-rata by qty. Floor each share, then hand out the leftover units to the
    // largest fractional remainders (deterministic largest-remainder method).
    let mut base: Vec<(usize, u64, u128)> = active
        .iter()
        .map(|&i| {
            let q = orders[i].qty as u128;
            let num = q * target as u128;
            let floor = (num / total as u128) as u64;
            let rem = num % total as u128;
            (i, floor, rem)
        })
        .collect();
    let assigned: u64 = base.iter().map(|(_, f, _)| *f).sum();
    let mut leftover = target.saturating_sub(assigned);
    // Sort by remainder descending, tie-break by index for determinism.
    base.sort_by(|a, b| b.2.cmp(&a.2).then(a.0.cmp(&b.0)));
    let len = base.len();
    let mut idx = 0;
    while leftover > 0 && len > 0 {
        base[idx % len].1 += 1;
        leftover -= 1;
        idx += 1;
    }
    base.into_iter().map(|(i, f, _)| (i, f)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    // A genuine two-sided clear: bids at high limits, asks at low limits, they
    // overlap → a crossing exists, volume clears, allocation conserves.
    #[test]
    fn genuine_clear_bids_meet_asks() {
        // K = 10 price levels. Bids willing up to level 7 and 6; asks from 3, 4.
        let orders = vec![
            Order::bid(100, 7),
            Order::bid(50, 6),
            Order::ask(80, 3),
            Order::ask(40, 4),
        ];
        let c = clear(&orders, 10);
        assert!(c.crossed, "overlapping book must clear");
        // Supply cumulative: S(j) rises from level 3. Demand falls as j rises.
        // Crossing is the first j with D(j) ≤ S(j).
        assert!(c.cleared_volume > 0);
        let alloc = allocate(&orders, &c);
        assert!(alloc.conserves(), "buy volume must equal sell volume");
        assert_eq!(alloc.buy_volume, c.cleared_volume);
        // Total fills never exceed the order's own quantity.
        for (o, f) in orders.iter().zip(alloc.fills.iter()) {
            assert!(*f <= o.qty, "fill cannot exceed order qty");
        }
    }

    // Opposite polarity: supply-heavy book. Lots of asks, few bids — demand is
    // the binding short side; still clears and conserves.
    #[test]
    fn supply_heavy_polarity_clears() {
        let orders = vec![
            Order::bid(30, 8),
            Order::ask(100, 2),
            Order::ask(100, 3),
            Order::ask(100, 4),
        ];
        let c = clear(&orders, 10);
        assert!(c.crossed);
        assert_eq!(c.cleared_volume, 30, "demand (30) is the short side");
        let alloc = allocate(&orders, &c);
        assert!(alloc.conserves());
        assert_eq!(alloc.buy_volume, 30);
        assert_eq!(alloc.sell_volume, 30);
    }

    // Demand-heavy polarity: lots of bids, few asks — supply is the short side.
    #[test]
    fn demand_heavy_polarity_clears() {
        let orders = vec![
            Order::bid(100, 8),
            Order::bid(100, 7),
            Order::bid(100, 6),
            Order::ask(45, 2),
        ];
        let c = clear(&orders, 10);
        assert!(c.crossed);
        assert_eq!(c.cleared_volume, 45, "supply (45) is the short side");
        let alloc = allocate(&orders, &c);
        assert!(alloc.conserves());
        assert_eq!(alloc.sell_volume, 45);
        assert_eq!(alloc.buy_volume, 45);
    }

    // NON-CONSERVING / non-clearing input handled: bids all sit BELOW every ask
    // (no price both a buyer and a seller accept). No crossing → V*=0, no trade,
    // empty allocation, still "conserves" trivially (0 == 0).
    #[test]
    fn no_overlap_does_not_clear() {
        let orders = vec![
            Order::bid(100, 2), // buyer won't pay above level 2
            Order::bid(50, 1),
            Order::ask(80, 7), // seller won't sell below level 7
            Order::ask(40, 8),
        ];
        let c = clear(&orders, 10);
        assert!(!c.crossed, "disjoint book must NOT clear");
        assert_eq!(c.cleared_volume, 0);
        let alloc = allocate(&orders, &c);
        assert_eq!(alloc.buy_volume, 0);
        assert_eq!(alloc.sell_volume, 0);
        assert!(alloc.conserves());
        assert!(alloc.fills.iter().all(|&f| f == 0));
    }

    // Pro-rata rationing on the long side sums EXACTLY to V* (largest-remainder,
    // no unit lost or created).
    #[test]
    fn pro_rata_conserves_exactly() {
        // Three asks with awkward quantities share a demand of 100.
        let orders = vec![
            Order::bid(100, 9),
            Order::ask(33, 1),
            Order::ask(33, 1),
            Order::ask(34, 1),
        ];
        let c = clear(&orders, 10);
        assert!(c.crossed);
        assert_eq!(c.cleared_volume, 100);
        let alloc = allocate(&orders, &c);
        assert_eq!(alloc.sell_volume, 100, "rationed fills sum exactly to V*");
        assert_eq!(alloc.buy_volume, 100);
        assert!(alloc.conserves());
    }

    // The curves have the right monotonicity and the clearing price is the
    // (first) volume-maximising price.
    #[test]
    fn curves_monotone_and_price_maximises_volume() {
        let orders = vec![
            Order::bid(60, 5),
            Order::bid(40, 7),
            Order::ask(50, 2),
            Order::ask(50, 6),
        ];
        let c = clear(&orders, 10);
        // Demand non-increasing.
        for j in 1..c.k {
            assert!(c.demand[j] <= c.demand[j - 1]);
        }
        // Supply non-decreasing.
        for j in 1..c.k {
            assert!(c.supply[j] >= c.supply[j - 1]);
        }
        assert!(c.crossed);
        // V* == min(D(p*), S(p*)), and it is the global max of min(D, S).
        assert_eq!(
            c.cleared_volume,
            c.demand[c.clearing_price].min(c.supply[c.clearing_price])
        );
        for j in 0..c.k {
            assert!(
                c.demand[j].min(c.supply[j]) <= c.cleared_volume,
                "V* is the max matchable volume"
            );
        }
        // First argmax: no earlier index attains V*.
        for j in 0..c.clearing_price {
            assert!(
                c.demand[j].min(c.supply[j]) < c.cleared_volume,
                "p* is the FIRST argmax"
            );
        }
    }
}
