//! Wire-stable settlement types for the uniform-price clearing — the SDK
//! surface of the plaintext verify-not-find engine (FHEGG-SDK-READINESS §4.1b).
//!
//! `clearing.rs` is the RULE (fold → crossing → conserving allocation, held to
//! `metatheory/Market/FhEggAllocation.lean` by golden vectors). This module is
//! the WIRE: versioned, ID-bearing, serde-round-trippable types plus the
//! tick↔bucket mapping that turns the abstract price-LEVEL INDEX into a real
//! integer price, so a settlement can leave the process and settle a market.
//!
//! ## Design decisions (all deliberate, all refusable-by-construction)
//!
//! * **Version pinned.** Every book and settlement carries `version`; anything
//!   but [`WIRE_VERSION`] is refused. Unknown JSON fields are refused
//!   (`deny_unknown_fields`) — in a settlement format a typo'd field silently
//!   ignored is a money bug, so v1 is strict; forward-compat is a new version.
//! * **Prices are exact integers on a grid.** [`TickGrid`] maps bucket `j` to
//!   the integer price `base + j·tick` (in quote units scaled by
//!   `10^price_exponent`, e.g. `-2` = cents). An order's `price` MUST be
//!   exactly on-grid and in-range — off-grid prices are REFUSED, never
//!   silently rounded (rounding an ask down or a bid up would fabricate
//!   willingness the trader never expressed — the same class as the
//!   out-of-domain-ask clamp bug). Quantization policy belongs to the caller.
//! * **Orders bear opaque unique IDs**; fills come back keyed by those IDs,
//!   index-aligned with the input book (zero fills included, so the vector is
//!   exhaustive — every order is accounted for, filled or not).
//! * **Rationing convention (named, not hidden):** the long side is rationed
//!   pro-rata by qty across ALL its active orders (largest-remainder,
//!   input-index tie-break) — the rule `clearing::allocate` implements and
//!   `FhEggAllocation.lean` proves conserving/capped/±1-fair. This is the
//!   pro-rata-overall convention, NOT the price-priority convention (where
//!   infra-marginal orders fill fully and only the marginal price level is
//!   rationed). A price-priority policy would be a NEW versioned field, never
//!   a silent change of meaning under `version: 1`.
//! * **Verify-not-find at the wire level.** [`Settlement::verify`] re-derives
//!   the whole settlement from the book and refuses any deviation — an SDK
//!   consumer can gate on it instead of trusting the producer. [`settle`]
//!   itself refuses to emit an allocation that fails the from-scratch
//!   invariant re-check `Allocation::validate`.
//! * **Bounded resources.** Total quantity is checked-summed (so the fold's
//!   `u64` accumulations cannot wrap — each curve entry is bounded by the
//!   grand total) and `k` is capped at [`MAX_GRID_LEVELS`], refusing
//!   OOM-shaped grids.
//!
//! This wires the SOLVER-side engine only. The `fhegg-fhe` research types
//! (`fhe_clear`, the BFV fold, the MPC crossing) are deliberately NOT given a
//! wire surface — READINESS §4 rule: do not surface the FHE path in an SDK
//! until its trust story is real.

use std::collections::HashSet;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::clearing::{allocate, clear, Allocation, Clearing, Order};

/// The wire format version this module produces and accepts.
pub const WIRE_VERSION: u32 = 1;

/// Refuse grids with more than this many price levels (allocation bound: the
/// curves are `k`-length `u64` vectors; 2^20 levels ≈ 8 MiB per curve).
pub const MAX_GRID_LEVELS: u32 = 1 << 20;

/// Everything the wire layer refuses, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireError {
    /// `version` is not [`WIRE_VERSION`].
    UnsupportedVersion { got: u32 },
    /// JSON parse / shape failure (message from serde).
    Json(String),
    /// The grid is malformed: zero tick, zero levels, too many levels, or
    /// `base + (k-1)·tick` overflows `u64`.
    BadGrid(&'static str),
    /// A book with no orders settles nothing; refuse it loudly.
    EmptyBook,
    /// Order IDs must be non-empty and unique within a book.
    EmptyOrderId,
    /// Two orders share this ID.
    DuplicateOrderId(String),
    /// An order priced off-grid or out of the grid's range (never rounded).
    OffGridPrice { id: String, price: u64 },
    /// A zero-quantity order is not an order.
    ZeroQty { id: String },
    /// The book's total quantity overflows `u64` (would wrap the curve fold).
    QtyOverflow,
    /// The produced allocation failed the from-scratch invariant re-check
    /// (`Allocation::validate`) — never expected; refused rather than emitted.
    AllocationInvalid,
    /// `Settlement::verify`: the settlement does not match re-derivation.
    Mismatch(&'static str),
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WireError::UnsupportedVersion { got } => {
                write!(
                    f,
                    "unsupported wire version {got} (this build speaks {WIRE_VERSION})"
                )
            }
            WireError::Json(m) => write!(f, "bad JSON: {m}"),
            WireError::BadGrid(m) => write!(f, "bad tick grid: {m}"),
            WireError::EmptyBook => write!(f, "empty book"),
            WireError::EmptyOrderId => write!(f, "empty order id"),
            WireError::DuplicateOrderId(id) => write!(f, "duplicate order id '{id}'"),
            WireError::OffGridPrice { id, price } => {
                write!(f, "order '{id}': price {price} is not on the tick grid (off-grid prices are refused, never rounded)")
            }
            WireError::ZeroQty { id } => write!(f, "order '{id}': zero quantity"),
            WireError::QtyOverflow => write!(f, "total book quantity overflows u64"),
            WireError::AllocationInvalid => {
                write!(
                    f,
                    "internal: allocation failed its own invariant re-check; refusing to emit"
                )
            }
            WireError::Mismatch(m) => write!(f, "settlement does not match re-derivation: {m}"),
        }
    }
}

impl std::error::Error for WireError {}

/// The exact tick↔bucket mapping: bucket `j ∈ [0, k)` ↔ integer price
/// `base + j·tick`, in quote units scaled by `10^price_exponent`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TickGrid {
    /// Integer price of bucket 0.
    pub base: u64,
    /// Tick size (must be > 0).
    pub tick: u64,
    /// Number of price levels K (must be ≥ 1 and ≤ [`MAX_GRID_LEVELS`]).
    pub k: u32,
    /// Decimal scale of `base`/`tick`/prices: real price = value × 10^this.
    /// (e.g. `-2` with quote currency USD means prices are in cents.)
    pub price_exponent: i8,
}

impl TickGrid {
    /// Check the grid is well-formed (nonzero tick, `1 ≤ k ≤` cap, top-of-grid
    /// price representable in `u64`).
    pub fn validate(&self) -> Result<(), WireError> {
        if self.tick == 0 {
            return Err(WireError::BadGrid("tick must be > 0"));
        }
        if self.k == 0 {
            return Err(WireError::BadGrid("k must be >= 1"));
        }
        if self.k > MAX_GRID_LEVELS {
            return Err(WireError::BadGrid("k exceeds MAX_GRID_LEVELS"));
        }
        // Top-of-grid price must not overflow: base + (k-1)*tick.
        let span = self
            .tick
            .checked_mul(u64::from(self.k - 1))
            .and_then(|s| self.base.checked_add(s));
        if span.is_none() {
            return Err(WireError::BadGrid("base + (k-1)*tick overflows u64"));
        }
        Ok(())
    }

    /// The real integer price of bucket `j`. Errors on `j ≥ k`.
    /// (Grid must be validated; arithmetic cannot overflow after `validate`.)
    pub fn price_of_bucket(&self, j: u32) -> Result<u64, WireError> {
        if j >= self.k {
            return Err(WireError::BadGrid("bucket index out of range"));
        }
        Ok(self.base + u64::from(j) * self.tick)
    }

    /// The bucket of an EXACTLY on-grid, in-range price. Off-grid or
    /// out-of-range prices are refused, never rounded.
    pub fn bucket_of_price(&self, price: u64) -> Option<u32> {
        let off = price.checked_sub(self.base)?;
        if off % self.tick != 0 {
            return None;
        }
        let j = off / self.tick;
        if j >= u64::from(self.k) {
            return None;
        }
        Some(j as u32)
    }
}

/// Order side on the wire (`"bid"` / `"ask"`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum WireSide {
    Bid,
    Ask,
}

/// A sealed limit order on the wire: opaque unique ID, side, quantity, and a
/// REAL limit price (must be exactly on the book's [`TickGrid`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WireOrder {
    pub id: String,
    pub side: WireSide,
    pub qty: u64,
    /// Limit price in grid units (see `TickGrid::price_exponent`).
    pub price: u64,
}

/// A versioned order book: the input to [`settle`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WireBook {
    /// Must equal [`WIRE_VERSION`].
    pub version: u32,
    /// Opaque market identifier, echoed into the settlement.
    pub market_id: String,
    pub grid: TickGrid,
    pub orders: Vec<WireOrder>,
}

impl WireBook {
    /// Parse a book from JSON, refusing unknown fields and wrong versions.
    pub fn from_json(json: &str) -> Result<Self, WireError> {
        let book: WireBook =
            serde_json::from_str(json).map_err(|e| WireError::Json(e.to_string()))?;
        if book.version != WIRE_VERSION {
            return Err(WireError::UnsupportedVersion { got: book.version });
        }
        Ok(book)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string(self).expect("WireBook serialization cannot fail")
    }
}

/// One order's fill in the settlement, keyed by the order's ID and
/// index-aligned with the input book (zero fills included).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WireFill {
    pub order_id: String,
    pub qty: u64,
}

/// The versioned settlement: the crossing (as index AND real price) plus the
/// exhaustive, conserving per-order fill vector.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Settlement {
    /// Equals [`WIRE_VERSION`].
    pub version: u32,
    /// Echo of the book's market ID.
    pub market_id: String,
    /// Echo of the book's grid (so the settlement is self-describing).
    pub grid: TickGrid,
    /// Whether the book crossed (positive matchable volume).
    pub crossed: bool,
    /// The clearing price as a bucket index — `null` when `!crossed` (no bogus
    /// zero price on a book that never traded).
    pub clearing_price_index: Option<u32>,
    /// The clearing price as a REAL grid price — `null` when `!crossed`.
    pub clearing_price: Option<u64>,
    /// The cleared uniform-price volume `V*` (0 when `!crossed`).
    pub cleared_volume: u64,
    /// Σ bid fills — equals `cleared_volume` (conservation, buy side).
    pub buy_volume: u64,
    /// Σ ask fills — equals `cleared_volume` (conservation, sell side).
    pub sell_volume: u64,
    /// One entry per input order, in input order, zero fills included.
    pub fills: Vec<WireFill>,
}

impl Settlement {
    pub fn from_json(json: &str) -> Result<Self, WireError> {
        let s: Settlement =
            serde_json::from_str(json).map_err(|e| WireError::Json(e.to_string()))?;
        if s.version != WIRE_VERSION {
            return Err(WireError::UnsupportedVersion { got: s.version });
        }
        Ok(s)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string(self).expect("Settlement serialization cannot fail")
    }

    /// Verify-not-find: re-derive the settlement from the book and refuse ANY
    /// deviation (crossing, prices, volumes, every fill, ID alignment). An SDK
    /// consumer can gate on this instead of trusting whoever produced the
    /// settlement. The clearing rule is deterministic, so re-derivation is an
    /// exact check, and the re-derivation itself passes through the same
    /// from-scratch invariant gate (`Allocation::validate`) as `settle`.
    pub fn verify(&self, book: &WireBook) -> Result<(), WireError> {
        let expected = settle(book)?;
        if *self != expected {
            // Name the first divergence for the caller.
            if self.version != expected.version {
                return Err(WireError::Mismatch("version"));
            }
            if self.market_id != expected.market_id {
                return Err(WireError::Mismatch("marketId"));
            }
            if self.grid != expected.grid {
                return Err(WireError::Mismatch("grid"));
            }
            if self.crossed != expected.crossed {
                return Err(WireError::Mismatch("crossed"));
            }
            if self.clearing_price_index != expected.clearing_price_index
                || self.clearing_price != expected.clearing_price
            {
                return Err(WireError::Mismatch("clearing price"));
            }
            if self.cleared_volume != expected.cleared_volume
                || self.buy_volume != expected.buy_volume
                || self.sell_volume != expected.sell_volume
            {
                return Err(WireError::Mismatch("volumes"));
            }
            return Err(WireError::Mismatch("fills"));
        }
        Ok(())
    }
}

/// Validate a book and lower it to the clearing engine's `Order` shape.
/// Returns the orders bucket-indexed on the book's grid.
fn lower_book(book: &WireBook) -> Result<Vec<Order>, WireError> {
    if book.version != WIRE_VERSION {
        return Err(WireError::UnsupportedVersion { got: book.version });
    }
    book.grid.validate()?;
    if book.orders.is_empty() {
        return Err(WireError::EmptyBook);
    }
    let mut seen: HashSet<&str> = HashSet::with_capacity(book.orders.len());
    let mut total: u64 = 0;
    let mut lowered = Vec::with_capacity(book.orders.len());
    for o in &book.orders {
        if o.id.is_empty() {
            return Err(WireError::EmptyOrderId);
        }
        if !seen.insert(o.id.as_str()) {
            return Err(WireError::DuplicateOrderId(o.id.clone()));
        }
        if o.qty == 0 {
            return Err(WireError::ZeroQty { id: o.id.clone() });
        }
        // Checked grand total: every curve entry the fold accumulates is
        // bounded by this sum, so the fold's u64 adds cannot wrap.
        total = total.checked_add(o.qty).ok_or(WireError::QtyOverflow)?;
        let bucket = book
            .grid
            .bucket_of_price(o.price)
            .ok_or_else(|| WireError::OffGridPrice {
                id: o.id.clone(),
                price: o.price,
            })?;
        lowered.push(match o.side {
            WireSide::Bid => Order::bid(o.qty, bucket),
            WireSide::Ask => Order::ask(o.qty, bucket),
        });
    }
    Ok(lowered)
}

/// Settle a book: validate → lower to buckets → fold + crossing + conserving
/// allocation (`clearing::{clear, allocate}`) → gate on the from-scratch
/// invariant re-check → emit the versioned settlement.
pub fn settle(book: &WireBook) -> Result<Settlement, WireError> {
    let orders = lower_book(book)?;
    let k = book.grid.k as usize;
    let clearing: Clearing = clear(&orders, k);
    let alloc: Allocation = allocate(&orders, &clearing);
    if !alloc.validate(&orders, &clearing) {
        return Err(WireError::AllocationInvalid);
    }
    let (clearing_price_index, clearing_price) = if clearing.crossed {
        let j = clearing.clearing_price as u32;
        (Some(j), Some(book.grid.price_of_bucket(j)?))
    } else {
        (None, None)
    };
    let fills = book
        .orders
        .iter()
        .zip(alloc.fills.iter())
        .map(|(o, &f)| WireFill {
            order_id: o.id.clone(),
            qty: f,
        })
        .collect();
    Ok(Settlement {
        version: WIRE_VERSION,
        market_id: book.market_id.clone(),
        grid: book.grid.clone(),
        crossed: clearing.crossed,
        clearing_price_index,
        clearing_price,
        cleared_volume: if clearing.crossed {
            clearing.cleared_volume
        } else {
            0
        },
        buy_volume: alloc.buy_volume,
        sell_volume: alloc.sell_volume,
        fills,
    })
}

/// JSON-in/JSON-out settle, for FFI/CLI shells.
pub fn settle_json(book_json: &str) -> Result<String, WireError> {
    let book = WireBook::from_json(book_json)?;
    Ok(settle(&book)?.to_json())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Lean `workBook` golden vector (`FhEggClearing.lean` /
    /// `lean_workbook_golden_vector` in clearing.rs) lifted onto a REAL price
    /// grid: base 100, tick 5, K=3 → prices {100, 105, 110} (exponent -2 ⇒
    /// dollars-and-cents: $1.00/$1.05/$1.10).
    fn workbook() -> WireBook {
        WireBook {
            version: WIRE_VERSION,
            market_id: "GOLD/ART".to_string(),
            grid: TickGrid {
                base: 100,
                tick: 5,
                k: 3,
                price_exponent: -2,
            },
            orders: vec![
                WireOrder {
                    id: "b1".into(),
                    side: WireSide::Bid,
                    qty: 6,
                    price: 110,
                },
                WireOrder {
                    id: "b2".into(),
                    side: WireSide::Bid,
                    qty: 4,
                    price: 105,
                },
                WireOrder {
                    id: "a1".into(),
                    side: WireSide::Ask,
                    qty: 3,
                    price: 100,
                },
                WireOrder {
                    id: "a2".into(),
                    side: WireSide::Ask,
                    qty: 5,
                    price: 105,
                },
            ],
        }
    }

    // The workBook golden vector THROUGH the wire: real prices in, the
    // Lean-proven crossing (p*=1 ⇒ price 105, V*=8) and the deterministic
    // largest-remainder fills (5,3,3,5) out, keyed by order ID.
    #[test]
    fn workbook_settles_through_the_wire() {
        let s = settle(&workbook()).unwrap();
        assert!(s.crossed);
        assert_eq!(s.clearing_price_index, Some(1));
        assert_eq!(
            s.clearing_price,
            Some(105),
            "index 1 maps to the REAL price 105"
        );
        assert_eq!(s.cleared_volume, 8);
        assert_eq!((s.buy_volume, s.sell_volume), (8, 8));
        let fills: Vec<(&str, u64)> = s
            .fills
            .iter()
            .map(|f| (f.order_id.as_str(), f.qty))
            .collect();
        assert_eq!(fills, vec![("b1", 5), ("b2", 3), ("a1", 3), ("a2", 5)]);
        s.verify(&workbook()).unwrap();
    }

    // GOLDEN JSON SNAPSHOT — pins the exact field names and layout of v1.
    // If this test breaks, the wire format changed: that is a NEW version,
    // not an edit to this string.
    #[test]
    fn settlement_json_snapshot_is_wire_stable() {
        let s = settle(&workbook()).unwrap();
        let expected = concat!(
            r#"{"version":1,"marketId":"GOLD/ART","#,
            r#""grid":{"base":100,"tick":5,"k":3,"priceExponent":-2},"#,
            r#""crossed":true,"clearingPriceIndex":1,"clearingPrice":105,"#,
            r#""clearedVolume":8,"buyVolume":8,"sellVolume":8,"#,
            r#""fills":[{"orderId":"b1","qty":5},{"orderId":"b2","qty":3},"#,
            r#"{"orderId":"a1","qty":3},{"orderId":"a2","qty":5}]}"#,
        );
        assert_eq!(s.to_json(), expected);
        // And the snapshot parses back to the same settlement (round-trip).
        assert_eq!(Settlement::from_json(expected).unwrap(), s);
    }

    #[test]
    fn book_round_trips_through_json() {
        let b = workbook();
        let b2 = WireBook::from_json(&b.to_json()).unwrap();
        assert_eq!(b, b2);
    }

    #[test]
    fn wrong_version_is_refused() {
        let mut b = workbook();
        b.version = 2;
        assert_eq!(settle(&b), Err(WireError::UnsupportedVersion { got: 2 }));
        let json = b.to_json();
        assert_eq!(
            WireBook::from_json(&json),
            Err(WireError::UnsupportedVersion { got: 2 })
        );
    }

    #[test]
    fn unknown_fields_are_refused() {
        let json =
            workbook()
                .to_json()
                .replacen("\"marketId\"", "\"marketid_typo\":1,\"marketId\"", 1);
        assert!(matches!(
            WireBook::from_json(&json),
            Err(WireError::Json(_))
        ));
    }

    #[test]
    fn bad_ids_are_refused() {
        let mut b = workbook();
        b.orders[1].id = "b1".into(); // duplicate
        assert_eq!(settle(&b), Err(WireError::DuplicateOrderId("b1".into())));
        let mut b = workbook();
        b.orders[0].id = String::new();
        assert_eq!(settle(&b), Err(WireError::EmptyOrderId));
    }

    #[test]
    fn off_grid_and_out_of_range_prices_are_refused_not_rounded() {
        // 103 is between ticks (100, 105, 110).
        let mut b = workbook();
        b.orders[0].price = 103;
        assert_eq!(
            settle(&b),
            Err(WireError::OffGridPrice {
                id: "b1".into(),
                price: 103
            })
        );
        // 95 is below base.
        let mut b = workbook();
        b.orders[2].price = 95;
        assert_eq!(
            settle(&b),
            Err(WireError::OffGridPrice {
                id: "a1".into(),
                price: 95
            })
        );
        // 115 is on-tick but ABOVE the grid (k=3 tops out at 110) — refused for
        // BOTH sides: an above-grid ask clamped in would fabricate supply below
        // its limit (the out-of-domain-ask bug class); a bid the caller can
        // express as top-of-grid explicitly.
        for i in [0usize, 2] {
            let mut b = workbook();
            b.orders[i].price = 115;
            let id = b.orders[i].id.clone();
            assert_eq!(settle(&b), Err(WireError::OffGridPrice { id, price: 115 }));
        }
    }

    #[test]
    fn zero_qty_and_empty_book_are_refused() {
        let mut b = workbook();
        b.orders[3].qty = 0;
        assert_eq!(settle(&b), Err(WireError::ZeroQty { id: "a2".into() }));
        let mut b = workbook();
        b.orders.clear();
        assert_eq!(settle(&b), Err(WireError::EmptyBook));
    }

    #[test]
    fn qty_overflow_is_refused() {
        let mut b = workbook();
        b.orders[0].qty = u64::MAX;
        b.orders[1].qty = u64::MAX;
        assert_eq!(settle(&b), Err(WireError::QtyOverflow));
    }

    #[test]
    fn malformed_grids_are_refused() {
        let mut b = workbook();
        b.grid.tick = 0;
        assert!(matches!(settle(&b), Err(WireError::BadGrid(_))));
        let mut b = workbook();
        b.grid.k = 0;
        assert!(matches!(settle(&b), Err(WireError::BadGrid(_))));
        let mut b = workbook();
        b.grid.k = MAX_GRID_LEVELS + 1;
        assert!(matches!(settle(&b), Err(WireError::BadGrid(_))));
        // Top-of-grid price overflows u64.
        let mut b = workbook();
        b.grid.base = u64::MAX - 1;
        b.grid.tick = 2;
        assert!(matches!(settle(&b), Err(WireError::BadGrid(_))));
    }

    // A book that never crosses: clearing price is null (no bogus zero
    // price), every fill zero but PRESENT (exhaustive), verify passes.
    #[test]
    fn uncrossed_book_settles_to_null_price_and_zero_fills() {
        let b = WireBook {
            version: WIRE_VERSION,
            market_id: "M".into(),
            grid: TickGrid {
                base: 10,
                tick: 1,
                k: 10,
                price_exponent: 0,
            },
            orders: vec![
                WireOrder {
                    id: "b".into(),
                    side: WireSide::Bid,
                    qty: 5,
                    price: 11,
                },
                WireOrder {
                    id: "a".into(),
                    side: WireSide::Ask,
                    qty: 5,
                    price: 17,
                },
            ],
        };
        let s = settle(&b).unwrap();
        assert!(!s.crossed);
        assert_eq!(s.clearing_price_index, None);
        assert_eq!(s.clearing_price, None);
        assert_eq!(s.cleared_volume, 0);
        assert_eq!(s.fills.len(), 2, "zero fills are still listed");
        assert!(s.fills.iter().all(|f| f.qty == 0));
        s.verify(&b).unwrap();
        // JSON: the nulls are literal.
        assert!(s.to_json().contains("\"clearingPriceIndex\":null"));
    }

    // verify() has teeth: tamper with any load-bearing field → refused.
    #[test]
    fn verify_refuses_tampered_settlements() {
        let b = workbook();
        let good = settle(&b).unwrap();
        good.verify(&b).unwrap();

        // Steal one unit between buyers (sides still balance).
        let mut t = good.clone();
        t.fills[0].qty -= 1;
        t.fills[1].qty += 1;
        assert_eq!(t.verify(&b), Err(WireError::Mismatch("fills")));

        // Swap two fill IDs (quantities intact).
        let mut t = good.clone();
        t.fills.swap(2, 3);
        assert_eq!(t.verify(&b), Err(WireError::Mismatch("fills")));

        // Lie about the clearing price.
        let mut t = good.clone();
        t.clearing_price = Some(110);
        assert_eq!(t.verify(&b), Err(WireError::Mismatch("clearing price")));

        // Lie about the volume.
        let mut t = good.clone();
        t.cleared_volume += 1;
        assert_eq!(t.verify(&b), Err(WireError::Mismatch("volumes")));

        // Re-brand the market.
        let mut t = good.clone();
        t.market_id = "TIN/ART".into();
        assert_eq!(t.verify(&b), Err(WireError::Mismatch("marketId")));
    }

    // PROPERTY: seeded-random books — every settlement conserves (both side
    // sums equal V*), is individually rational AT THE REAL PRICE (a bid never
    // fills with limit below p*, an ask never above), never over-fills an
    // order, is deterministic byte-for-byte, and passes verify().
    // Checked FROM SCRATCH here against the wire types — not by re-calling
    // the allocator's own validate.
    #[test]
    fn random_books_conserve_and_are_rational_at_real_prices() {
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xF4E66);
        let mut crossed_seen = 0u32;
        let mut rationed_seen = 0u32;
        for case in 0..300 {
            let k: u32 = rng.gen_range(1..=12);
            let base: u64 = rng.gen_range(0..1000);
            let tick: u64 = rng.gen_range(1..50);
            let n = rng.gen_range(1..=20);
            let orders: Vec<WireOrder> = (0..n)
                .map(|i| WireOrder {
                    id: format!("o{i}"),
                    side: if rng.gen_bool(0.5) {
                        WireSide::Bid
                    } else {
                        WireSide::Ask
                    },
                    qty: rng.gen_range(1..500),
                    price: base + u64::from(rng.gen_range(0..k)) * tick,
                })
                .collect();
            let b = WireBook {
                version: WIRE_VERSION,
                market_id: format!("case{case}"),
                grid: TickGrid {
                    base,
                    tick,
                    k,
                    price_exponent: -2,
                },
                orders,
            };
            let s = settle(&b).expect("well-formed random book must settle");
            s.verify(&b).unwrap();

            // Determinism: settle twice, identical bytes.
            assert_eq!(s.to_json(), settle(&b).unwrap().to_json());

            // From-scratch conservation + IR + caps against the WIRE types.
            let mut buy = 0u64;
            let mut sell = 0u64;
            assert_eq!(s.fills.len(), b.orders.len());
            for (o, f) in b.orders.iter().zip(s.fills.iter()) {
                assert_eq!(o.id, f.order_id, "fills are ID-aligned with the book");
                assert!(f.qty <= o.qty, "no order over-fills");
                match o.side {
                    WireSide::Bid => buy += f.qty,
                    WireSide::Ask => sell += f.qty,
                }
                if f.qty > 0 {
                    let p = s.clearing_price.expect("a fill implies a crossing");
                    match o.side {
                        WireSide::Bid => assert!(o.price >= p, "bid filled above its limit"),
                        WireSide::Ask => assert!(o.price <= p, "ask filled below its limit"),
                    }
                }
            }
            assert_eq!(buy, s.cleared_volume, "buy side sums to V*");
            assert_eq!(sell, s.cleared_volume, "sell side sums to V*");
            if s.crossed {
                crossed_seen += 1;
                // p* index ↔ real price agree under the grid.
                assert_eq!(
                    s.clearing_price.unwrap(),
                    b.grid
                        .price_of_bucket(s.clearing_price_index.unwrap())
                        .unwrap()
                );
                // Did rationing actually happen (long side not fully filled)?
                let active_short_total: u64 = b
                    .orders
                    .iter()
                    .zip(s.fills.iter())
                    .filter(|(o, _)| match o.side {
                        WireSide::Bid => o.price >= s.clearing_price.unwrap(),
                        WireSide::Ask => o.price <= s.clearing_price.unwrap(),
                    })
                    .map(|(o, _)| o.qty)
                    .sum::<u64>();
                if active_short_total > 2 * s.cleared_volume {
                    rationed_seen += 1;
                }
            }
        }
        // The generator must actually exercise the interesting regimes.
        assert!(
            crossed_seen >= 50,
            "generator produced too few crossings: {crossed_seen}"
        );
        assert!(
            rationed_seen >= 10,
            "generator produced too few rationed books: {rationed_seen}"
        );
    }

    // The rationing convention on the wire is the documented one: pro-rata by
    // qty across ALL active long-side orders, largest-remainder, index
    // tie-break — exact expected fills, exhaustive (sums EXACTLY to V*).
    #[test]
    fn long_side_rationing_is_deterministic_and_exhaustive() {
        // Demand 100 at the top; three asks (33, 33, 34) at the bottom would
        // supply 100 — make demand the LONG side instead: one ask of 10,
        // five bids of 3 → V*=10, bids ration 15→10.
        let b = WireBook {
            version: WIRE_VERSION,
            market_id: "R".into(),
            grid: TickGrid {
                base: 0,
                tick: 1,
                k: 4,
                price_exponent: 0,
            },
            orders: vec![
                WireOrder {
                    id: "a".into(),
                    side: WireSide::Ask,
                    qty: 10,
                    price: 0,
                },
                WireOrder {
                    id: "b0".into(),
                    side: WireSide::Bid,
                    qty: 3,
                    price: 3,
                },
                WireOrder {
                    id: "b1".into(),
                    side: WireSide::Bid,
                    qty: 3,
                    price: 3,
                },
                WireOrder {
                    id: "b2".into(),
                    side: WireSide::Bid,
                    qty: 3,
                    price: 3,
                },
                WireOrder {
                    id: "b3".into(),
                    side: WireSide::Bid,
                    qty: 3,
                    price: 3,
                },
                WireOrder {
                    id: "b4".into(),
                    side: WireSide::Bid,
                    qty: 3,
                    price: 3,
                },
            ],
        };
        let s = settle(&b).unwrap();
        assert_eq!(s.cleared_volume, 10);
        // Pro-rata: each bid's share is 3·10/15 = 2 exactly (remainder 0), so
        // floors sum to 10 — no leftover pass needed; every bid fills 2.
        let fills: Vec<u64> = s.fills.iter().map(|f| f.qty).collect();
        assert_eq!(fills, vec![10, 2, 2, 2, 2, 2]);
        let total: u64 = fills[1..].iter().sum();
        assert_eq!(
            total, 10,
            "rationing is exhaustive: fills sum EXACTLY to V*"
        );

        // Uneven case: qtys (7, 5, 3) share 10 → floors (4,3,2)=9, remainders
        // (10,5,0)/15 → the one leftover unit goes to the LARGEST remainder
        // (b0) → (5,3,2). Deterministic, documented, exact.
        let b2 = WireBook {
            version: WIRE_VERSION,
            market_id: "R2".into(),
            grid: TickGrid {
                base: 0,
                tick: 1,
                k: 4,
                price_exponent: 0,
            },
            orders: vec![
                WireOrder {
                    id: "a".into(),
                    side: WireSide::Ask,
                    qty: 10,
                    price: 0,
                },
                WireOrder {
                    id: "b0".into(),
                    side: WireSide::Bid,
                    qty: 7,
                    price: 3,
                },
                WireOrder {
                    id: "b1".into(),
                    side: WireSide::Bid,
                    qty: 5,
                    price: 3,
                },
                WireOrder {
                    id: "b2".into(),
                    side: WireSide::Bid,
                    qty: 3,
                    price: 3,
                },
            ],
        };
        let s2 = settle(&b2).unwrap();
        let fills2: Vec<u64> = s2.fills.iter().map(|f| f.qty).collect();
        assert_eq!(fills2, vec![10, 5, 3, 2]);
        s2.verify(&b2).unwrap();
    }

    // settle_json is a working JSON-in/JSON-out shell (the CLI/FFI shape).
    #[test]
    fn settle_json_round_trip() {
        let out = settle_json(&workbook().to_json()).unwrap();
        let s = Settlement::from_json(&out).unwrap();
        assert_eq!(s.cleared_volume, 8);
        assert!(matches!(
            settle_json("{\"version\":9}"),
            Err(WireError::Json(_)) | Err(WireError::UnsupportedVersion { .. })
        ));
    }

    // Tick mapping unit teeth.
    #[test]
    fn tick_grid_mapping_is_exact() {
        let g = TickGrid {
            base: 100,
            tick: 5,
            k: 3,
            price_exponent: -2,
        };
        g.validate().unwrap();
        assert_eq!(g.price_of_bucket(0).unwrap(), 100);
        assert_eq!(g.price_of_bucket(2).unwrap(), 110);
        assert!(g.price_of_bucket(3).is_err());
        assert_eq!(g.bucket_of_price(105), Some(1));
        assert_eq!(g.bucket_of_price(104), None);
        assert_eq!(g.bucket_of_price(99), None);
        assert_eq!(g.bucket_of_price(115), None);
        // Round-trip over the whole grid.
        for j in 0..g.k {
            assert_eq!(g.bucket_of_price(g.price_of_bucket(j).unwrap()), Some(j));
        }
    }
}
