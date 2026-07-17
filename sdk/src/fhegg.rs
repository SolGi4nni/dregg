//! # fhEgg plaintext clearing — EXPERIMENTAL demo surface (`feature = "fhegg"`)
//!
//! Clear a sealed-order book at a uniform price and verify a settlement you did
//! NOT produce. This is a thin, honest wrapper over
//! [`fhegg_solver::wire`] — the versioned wire layer of the fhEgg Stage-1
//! solver's uniform-price clearing (`fhegg_solver::clearing`, held to
//! `metatheory/Market/FhEggAllocation.lean` by golden vectors).
//!
//! ## What this IS (and is not) — read before depending on it
//!
//! * **EXPERIMENTAL.** The surface may change; treat `WIRE_VERSION` as the only
//!   stability promise (a wrong version is refused, never reinterpreted).
//! * **PLAINTEXT.** The clearing engine sees every order in the clear. There is
//!   **NO FHE and NO privacy** on this path — despite the crate family's name,
//!   nothing here encrypts, blinds, or hides anything. Do not present this
//!   surface as private clearing.
//! * **DEMO-SCALE.** Sized for demonstration books, not production load; no
//!   benchmarking claim is made here.
//! * **UNTRUSTED-SOLVER, SELF-CHECKABLE.** The value proposition is
//!   verify-not-find at the wire level: [`verify_settlement`]
//!   ([`Settlement::verify`]) re-derives the entire settlement from the book
//!   and refuses ANY deviation, so a consumer can gate on the check instead of
//!   trusting whoever ran [`clear_book`]. Note the check's authority is
//!   re-derivation by the SAME deterministic rule — it defends against a
//!   tampered or buggy *producer*, not against a bug in the shared rule itself.
//! * **The VERIFIED path is elsewhere.** The Cert-F STARK-verified clearing
//!   (Lean-emitted descriptor, BabyBear+FRI proof) covers the registered
//!   ring-3 and market4 program shapes only — see
//!   `circuit-prove/src/cert_f_air.rs` and `metatheory/Market/CertFDescriptor.lean`.
//!   Nothing in THIS module carries that assurance; do not conflate the two.
//!
//! ## Shape
//!
//! A [`WireBook`] (versioned; exact integer prices on a [`TickGrid`], off-grid
//! prices refused, never rounded) goes in; a [`Settlement`] (versioned;
//! crossing as index AND real price, exhaustive ID-keyed fills, conservation
//! totals) comes out. JSON forms of both are strict (`deny_unknown_fields`).
//!
//! ```no_run
//! use dregg_sdk::fhegg::{self, TickGrid, WireBook, WireOrder, WireSide, WIRE_VERSION};
//!
//! let book = WireBook {
//!     version: WIRE_VERSION,
//!     market_id: "GOLD/ART".into(),
//!     grid: TickGrid { base: 100, tick: 5, k: 3, price_exponent: -2 },
//!     orders: vec![
//!         WireOrder { id: "b1".into(), side: WireSide::Bid, qty: 6, price: 110 },
//!         WireOrder { id: "a1".into(), side: WireSide::Ask, qty: 3, price: 100 },
//!     ],
//! };
//! let settlement = fhegg::clear_book(&book).unwrap();
//! // A consumer that RECEIVED the settlement gates on the self-check:
//! fhegg::verify_settlement(&settlement, &book).unwrap();
//! ```
//!
//! The CLI twin of this surface is `fhegg-solver/src/bin/fhegg_settle.rs`
//! (`fhegg_settle`: book JSON in → settle + self-verify → settlement JSON out;
//! `fhegg_settle verify`: `{book, settlement}` in → accept/refuse).

pub use fhegg_solver::wire::{
    MAX_GRID_LEVELS, Settlement, TickGrid, WIRE_VERSION, WireBook, WireError, WireFill, WireOrder,
    WireSide,
};

/// Clear a book: validate → lower to price buckets → the uniform-price fold +
/// crossing + conserving allocation → refuse-or-emit the versioned
/// [`Settlement`]. Thin alias of [`fhegg_solver::wire::settle`]; refusal cases
/// are enumerated on [`WireError`].
pub fn clear_book(book: &WireBook) -> Result<Settlement, WireError> {
    fhegg_solver::wire::settle(book)
}

/// JSON-in/JSON-out [`clear_book`] (strict parse: unknown fields and wrong
/// versions refused). Thin alias of [`fhegg_solver::wire::settle_json`].
pub fn clear_book_json(book_json: &str) -> Result<String, WireError> {
    fhegg_solver::wire::settle_json(book_json)
}

/// Verify-not-find: check a settlement (typically produced by an UNTRUSTED
/// party) against the book by full re-derivation; any deviation is refused
/// with the first divergent field named ([`WireError::Mismatch`]).
pub fn verify_settlement(settlement: &Settlement, book: &WireBook) -> Result<(), WireError> {
    settlement.verify(book)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Lean `workBook` golden vector on a real price grid (same book the
    /// wire-layer tests pin: p* = 105, V* = 8, fills b1=5 b2=3 a1=3 a2=5).
    fn workbook() -> WireBook {
        WireBook {
            version: WIRE_VERSION,
            market_id: "GOLD/ART".into(),
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

    // Round trip THROUGH the SDK surface: typed clear → verify, and the JSON
    // path (book JSON → settlement JSON → parse → verify) — the exact flow an
    // SDK consumer would run.
    #[test]
    fn sdk_round_trip_clear_then_verify() {
        let book = workbook();
        let s = clear_book(&book).expect("golden book settles");
        assert!(s.crossed);
        assert_eq!(s.clearing_price, Some(105));
        assert_eq!(s.cleared_volume, 8);
        verify_settlement(&s, &book).expect("own settlement verifies");

        let out_json = clear_book_json(&book.to_json()).expect("json path settles");
        let s2 = Settlement::from_json(&out_json).expect("emitted settlement parses");
        assert_eq!(s2, s, "typed and JSON paths agree byte-for-value");
        verify_settlement(&s2, &book).expect("parsed settlement verifies");
    }

    // Tamper refusal: a doctored settlement is REFUSED by verify, with the
    // divergent field named. Covers a stolen unit (side sums intact), a price
    // lie, and a volume lie.
    #[test]
    fn sdk_verify_refuses_doctored_settlement() {
        let book = workbook();
        let good = clear_book(&book).unwrap();

        // Steal one unit between the two bids (totals still balance).
        let mut t = good.clone();
        t.fills[0].qty -= 1;
        t.fills[1].qty += 1;
        assert_eq!(
            verify_settlement(&t, &book),
            Err(WireError::Mismatch("fills"))
        );

        // Lie about the clearing price.
        let mut t = good.clone();
        t.clearing_price = Some(110);
        t.clearing_price_index = Some(2);
        assert_eq!(
            verify_settlement(&t, &book),
            Err(WireError::Mismatch("clearing price"))
        );

        // Inflate the cleared volume.
        let mut t = good.clone();
        t.cleared_volume += 1;
        t.buy_volume += 1;
        t.sell_volume += 1;
        assert_eq!(
            verify_settlement(&t, &book),
            Err(WireError::Mismatch("volumes"))
        );

        // And the undoctored one still passes (the test can fail both ways).
        verify_settlement(&good, &book).unwrap();
    }

    // Version discipline holds through the SDK JSON path.
    #[test]
    fn sdk_json_path_refuses_wrong_version() {
        let mut book = workbook();
        book.version = 2;
        assert_eq!(
            clear_book_json(&book.to_json()),
            Err(WireError::UnsupportedVersion { got: 2 })
        );
    }
}
