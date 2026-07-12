//! [`otc_quote`] — the friendly over-the-counter desk: a user brings USDC and buys
//! `$DREGG` out of the treasury's pile at a discount.
//!
//! # The economics
//!
//! The pile ([`Treasury::dregg_balance`](crate::treasury::Treasury::dregg_balance))
//! accumulates from `$DREGG`-paid runs and is otherwise illiquid. The OTC desk turns
//! it into a service: a user brings `usdc_in` USDC and receives `$DREGG` priced at the
//! live oracle rate MINUS [`PayConfig::otc_discount_bps`] (default 10%) — i.e. the
//! user buys `$DREGG` cheaper than market, a friendly fill that also refuels the
//! treasury with the incoming USDC.
//!
//! `dregg_out = usd_in / (oracle_price × (1 − otc_discount))`
//!
//! # Scope — quote + accounting only
//!
//! [`otc_quote`] computes the fill and checks the pile can cover it (a precise refusal
//! otherwise). It does **not** move funds. The actual `$DREGG` transfer to the buyer
//! executes behind the operator's signer — the deferred [`crate::sweeper::SolanaSweeper`]
//! /operator-signed settlement (`otc_settle`, a follow-up). Custody is the seed/signer.

use crate::config::PayConfig;
use crate::pricing::{PriceError, PriceOracle, discount_factor};

/// A computed OTC fill: bring `usdc_in`, receive `dregg_out`, at the discounted rate.
#[derive(Clone, Debug, PartialEq)]
pub struct OtcQuote {
    /// Atomic USDC the user brings in (fuels the treasury).
    pub usdc_in: u64,
    /// Atomic `$DREGG` the user receives out of the pile.
    pub dregg_out: u64,
    /// The oracle mid price (USD per whole `$DREGG`) the quote was fed from.
    pub oracle_price_usd: f64,
    /// The OTC discount applied, in basis points.
    pub discount_bps: u32,
    /// The effective price per whole `$DREGG` the user pays (`oracle × (1 − disc)`).
    pub effective_price_usd: f64,
    /// The pile balance (atomic `$DREGG`) the quote was checked against.
    pub pile_balance: u64,
}

/// Why an OTC quote could not be filled.
#[derive(Clone, Debug, PartialEq)]
pub enum OtcError {
    /// The price oracle was unavailable / invalid — no fill can be priced.
    PriceUnavailable(PriceError),
    /// The pile cannot cover the fill — a precise refusal (need vs have).
    InsufficientPile {
        /// Atomic `$DREGG` the fill requires.
        needed: u64,
        /// Atomic `$DREGG` currently in the pile.
        available: u64,
    },
}

impl std::fmt::Display for OtcError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OtcError::PriceUnavailable(e) => write!(f, "OTC price unavailable: {e}"),
            OtcError::InsufficientPile { needed, available } => write!(
                f,
                "OTC pile short: need {needed} atomic $DREGG, pile has {available}"
            ),
        }
    }
}

impl std::error::Error for OtcError {}

impl From<PriceError> for OtcError {
    fn from(e: PriceError) -> Self {
        OtcError::PriceUnavailable(e)
    }
}

/// The `$DREGG`-out (atomic) a `usdc_in` (atomic) fill yields at the discounted rate —
/// the pure pricing, without the pile check. Floors to whole atomic units.
pub fn otc_dregg_out(usdc_in: u64, oracle_price: f64, config: &PayConfig) -> u64 {
    let usd_in = usdc_in as f64 / 10f64.powi(config.usdc_decimals as i32);
    let effective_price = oracle_price * discount_factor(config.otc_discount_bps);
    if !(effective_price.is_finite() && effective_price > 0.0) {
        return 0;
    }
    let dregg_out_whole = usd_in / effective_price;
    let dregg_out_atomic = dregg_out_whole * 10f64.powi(config.dregg_decimals as i32);
    dregg_out_atomic.floor().max(0.0) as u64
}

/// Quote an OTC fill: a user brings `usdc_in` atomic USDC and buys `$DREGG` out of the
/// pile (`pile_balance` atomic `$DREGG`) at the oracle price minus the OTC discount.
///
/// Fails closed: an unavailable price → [`OtcError::PriceUnavailable`]; a pile that
/// cannot cover the fill → [`OtcError::InsufficientPile`] with the exact shortfall.
/// This is QUOTE + ACCOUNTING only — the `$DREGG` transfer executes behind the
/// operator's signer (the deferred `otc_settle`).
pub fn otc_quote(
    usdc_in: u64,
    pile_balance: u64,
    oracle: &dyn PriceOracle,
    config: &PayConfig,
) -> Result<OtcQuote, OtcError> {
    let oracle_price = oracle.dregg_usd_price()?;
    let effective_price_usd = oracle_price * discount_factor(config.otc_discount_bps);
    let dregg_out = otc_dregg_out(usdc_in, oracle_price, config);
    if dregg_out > pile_balance {
        return Err(OtcError::InsufficientPile {
            needed: dregg_out,
            available: pile_balance,
        });
    }
    Ok(OtcQuote {
        usdc_in,
        dregg_out,
        oracle_price_usd: oracle_price,
        discount_bps: config.otc_discount_bps,
        effective_price_usd,
        pile_balance,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::DepositAddress;
    use crate::pricing::MockOracle;

    fn cfg() -> PayConfig {
        PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            [0x11u8; 32],
            DepositAddress([0xEEu8; 32]),
            1_000_000,
        )
    }

    #[test]
    fn quote_gives_dregg_out_at_ten_percent_off() {
        let c = cfg(); // otc_discount_bps = 1000 (10%)
        let oracle = MockOracle::new(0.005); // $0.005 per whole $DREGG
        // Bring $1.00 = 1_000_000 atomic USDC. Effective price = 0.005 * 0.9 = 0.0045.
        // dregg_out_whole = 1.00 / 0.0045 = 222.222…  → 222_222_222 atomic (6 dp).
        let pile = 1_000_000_000u64; // plenty
        let q = otc_quote(1_000_000, pile, &oracle, &c).unwrap();
        assert!((q.effective_price_usd - 0.0045).abs() < 1e-9);
        assert_eq!(q.dregg_out, 222_222_222);
        // Sanity: without the discount it would be 200_000_000 — the buyer gets MORE.
        let at_market = (1.0 / 0.005 * 1_000_000.0) as u64;
        assert_eq!(at_market, 200_000_000);
        assert!(
            q.dregg_out > at_market,
            "discount gives the buyer more $DREGG"
        );
    }

    #[test]
    fn quote_refused_precisely_when_pile_short() {
        let c = cfg();
        let oracle = MockOracle::new(0.005);
        // Same $1.00 wants 222_222_222 atomic; pile has only 100_000_000.
        let err = otc_quote(1_000_000, 100_000_000, &oracle, &c).unwrap_err();
        assert_eq!(
            err,
            OtcError::InsufficientPile {
                needed: 222_222_222,
                available: 100_000_000
            }
        );
    }

    #[test]
    fn quote_fails_closed_on_bad_price() {
        let c = cfg();
        let bad = MockOracle::new(0.0);
        assert!(matches!(
            otc_quote(1_000_000, u64::MAX, &bad, &c),
            Err(OtcError::PriceUnavailable(_))
        ));
    }
}
