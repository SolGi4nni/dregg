//! # `fhegg_uniform` — the fhEgg uniform-price call auction as a thin JSON CLI (the crossing-curve wire)
//!
//! ```text
//! echo '<uniform-book-json>' | fhegg_uniform
//! ```
//!
//! The COMPANION to `fhegg_clear` (the circulation route). Where `fhegg_clear`
//! clears a multi-asset barter ring through the Cert-F convex circulation,
//! `fhegg_uniform` clears a SINGLE-PAIR uniform-price call auction — the fhEgg
//! kernel at T=1 (`docs/deos/FHEGG-KERNEL.md`): fold the sealed bids/asks into a
//! price-indexed demand/supply curve (a commutative-monoid histogram + scan) and
//! cross ONCE at the volume-maximising price `p* = argmax_j min(D(j), S(j))`.
//!
//! This runs the REAL `fhegg_solver::clearing` engine — `fold_curves` → `crossing`
//! → `allocate` — and emits the aggregate curves, the crossing, the conserving
//! per-order allocation, and the per-order active/fill flags as JSON, so the web
//! crossing-curve visualization renders the ACTUAL fold output, not a mirror.
//!
//! ## Input shape
//!
//! ```json
//! { "pair": "GOLD/ART", "k": 10, "priceGrid": ["…"],
//!   "orders": [ {"trader":"Ada","side":"bid","qty":100,"limit":7}, … ] }
//! ```
//!
//! `limit` is a price-LEVEL INDEX in `[0, k)` (the public price grid maps indices
//! to prices). `priceGrid` is optional cosmetic labels for the K levels. If `k` is
//! omitted it defaults to `max(limit)+1`. Bids fill at any price ≤ their limit;
//! asks fill at any price ≥ their limit. This is the untrusted plaintext solver
//! (it sees every order); privacy is the STARK-ZK/FHE stage, exactly as in
//! `fhegg_clear` — the two tiers below say so.

use std::io::Read;

use fhegg_solver::clearing::{allocate, clear, Order, Side};

use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct OrderIn {
    #[serde(default)]
    trader: String,
    side: String,
    qty: u64,
    limit: u32,
}

#[derive(Deserialize)]
struct BookIn {
    #[serde(default)]
    pair: String,
    #[serde(default)]
    k: Option<usize>,
    #[serde(rename = "priceGrid", default)]
    price_grid: Vec<String>,
    orders: Vec<OrderIn>,
}

#[derive(Serialize)]
struct OrderOut {
    trader: String,
    side: String,
    qty: u64,
    /// The price-level INDEX this order limits at.
    limit: u32,
    /// This order's price-grid LABEL (from `priceGrid`, or the bare index).
    #[serde(rename = "limitLabel")]
    limit_label: String,
    /// Filled quantity at the clearing price, read off the conserving allocation.
    fill: u64,
    /// Active at `p*` (bid with limit ≥ p*, ask with limit ≤ p*).
    active: bool,
    /// Fully / partially / not filled.
    filled: bool,
}

#[derive(Serialize)]
struct Curves {
    /// Cumulative demand `D(j)` over the grid (non-increasing).
    demand: Vec<u64>,
    /// Cumulative supply `S(j)` over the grid (non-decreasing).
    supply: Vec<u64>,
    /// The matchable volume `min(D(j), S(j))` at each level — its argmax is `p*`.
    matchable: Vec<u64>,
}

#[derive(Serialize)]
struct Tier {
    tier: String,
    sees: String,
}

#[derive(Serialize)]
struct UniformOut {
    engine: String,
    mechanism: String,
    pair: String,
    k: usize,
    #[serde(rename = "priceGrid")]
    price_grid: Vec<String>,
    curves: Curves,
    crossed: bool,
    #[serde(rename = "clearingPriceIndex")]
    clearing_price_index: usize,
    #[serde(rename = "clearingPriceLabel")]
    clearing_price_label: String,
    #[serde(rename = "clearedVolume")]
    cleared_volume: u64,
    #[serde(rename = "buyVolume")]
    buy_volume: u64,
    #[serde(rename = "sellVolume")]
    sell_volume: u64,
    conserves: bool,
    orders: Vec<OrderOut>,
    tiers: Vec<Tier>,
}

fn main() {
    let mut buf = String::new();
    if std::io::stdin().read_to_string(&mut buf).is_err() {
        eprintln!("fhegg_uniform: failed to read stdin");
        std::process::exit(2);
    }
    let book: BookIn = match serde_json::from_str(&buf) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("fhegg_uniform: bad book JSON: {e}");
            std::process::exit(2);
        }
    };
    if book.orders.is_empty() {
        eprintln!("fhegg_uniform: empty book");
        std::process::exit(2);
    }

    // Grid size K: given, else max limit + 1 (at least 1 level).
    let max_limit = book.orders.iter().map(|o| o.limit).max().unwrap_or(0) as usize;
    let k = book.k.unwrap_or(max_limit + 1).max(1);

    // Price-grid labels: given, else the bare index. Pad/truncate to K.
    let label = |j: usize| -> String {
        book.price_grid
            .get(j)
            .cloned()
            .unwrap_or_else(|| j.to_string())
    };

    // Map the input to the real clearing::Order shape.
    let mut orders: Vec<Order> = Vec::with_capacity(book.orders.len());
    for o in &book.orders {
        let side = match o.side.to_ascii_lowercase().as_str() {
            "bid" | "buy" | "b" => Side::Bid,
            "ask" | "sell" | "a" | "s" => Side::Ask,
            other => {
                eprintln!("fhegg_uniform: bad side '{other}' (want bid|ask)");
                std::process::exit(2);
            }
        };
        orders.push(match side {
            Side::Bid => Order::bid(o.qty, o.limit),
            Side::Ask => Order::ask(o.qty, o.limit),
        });
    }

    // ---- run the REAL fold + crossing + conserving allocation. ----
    let c = clear(&orders, k);
    let alloc = allocate(&orders, &c);

    let p = c.clearing_price as u32;
    let matchable: Vec<u64> = (0..k).map(|j| c.demand[j].min(c.supply[j])).collect();

    let orders_out: Vec<OrderOut> = book
        .orders
        .iter()
        .zip(orders.iter())
        .enumerate()
        .map(|(i, (raw, ord))| {
            let fill = *alloc.fills.get(i).unwrap_or(&0);
            let active = c.crossed
                && match ord.side {
                    Side::Bid => ord.limit >= p,
                    Side::Ask => ord.limit <= p,
                };
            OrderOut {
                trader: raw.trader.clone(),
                side: match ord.side {
                    Side::Bid => "bid".to_string(),
                    Side::Ask => "ask".to_string(),
                },
                qty: raw.qty,
                limit: raw.limit,
                limit_label: label(raw.limit as usize),
                fill,
                active,
                filled: fill > 0,
            }
        })
        .collect();

    let out = UniformOut {
        engine: "fhEgg uniform-price call auction (fhegg-solver::clearing: fold + one crossing)".to_string(),
        mechanism: "uniform-price aggregation  p* = argmax_j min(D(j), S(j)),  V* = min(D(p*), S(p*))  (the fhEgg kernel at T=1; an aggregation, not a matching)".to_string(),
        pair: if book.pair.is_empty() { "PAIR".to_string() } else { book.pair.clone() },
        k,
        price_grid: (0..k).map(label).collect(),
        curves: Curves {
            demand: c.demand.clone(),
            supply: c.supply.clone(),
            matchable,
        },
        crossed: c.crossed,
        clearing_price_index: c.clearing_price,
        clearing_price_label: label(c.clearing_price),
        cleared_volume: c.cleared_volume,
        buy_volume: alloc.buy_volume,
        sell_volume: alloc.sell_volume,
        conserves: alloc.conserves(),
        orders: orders_out,
        tiers: vec![
            Tier {
                tier: "solver-sees (Stage-1, untrusted)".to_string(),
                sees: "the plaintext book — every sealed bid/ask, folded into the curves".to_string(),
            },
            Tier {
                tier: "world-sees (the shielded output)".to_string(),
                sees: "only the proof + the public clearing price p* and volume V* — never who bid what (once the STARK/FHE stage is wired)".to_string(),
            },
        ],
    };

    match serde_json::to_string(&out) {
        Ok(s) => println!("{s}"),
        Err(e) => {
            eprintln!("fhegg_uniform: serialize failed: {e}");
            std::process::exit(1);
        }
    }
}
