//! [`Treasury`] — the two-balance treasury at the heart of ember's dual-asset
//! economics.
//!
//! Two piles, two jobs:
//!
//! * **`usdc_balance` — the FUEL.** Every real-AI run burns real USD (inference on
//!   Bedrock etc.). That cost is drawn from here via [`Treasury::spend_inference_usd`],
//!   which **fails closed** when the tank is dry — the "must refuel" signal the
//!   operator acts on. USDC payments land here.
//! * **`dregg_balance` — the PILE.** `$DREGG` payments accumulate here. `$DREGG` is
//!   illiquid and is *not* spent on inference; it is the holding the operator later
//!   converts to fuel behind the signer (the deferred swap) and the inventory the OTC
//!   desk sells from.
//!
//! Both balances are in **atomic token units** (USDC atomic, `$DREGG` atomic). The
//! USD-denominated inference cost is converted to atomic USDC using the treasury's
//! configured USDC decimals.
//!
//! Persistable via [`TreasuryStore`] (mirrors [`CreditStore`](crate::ledger::CreditStore)'s
//! shape): an [`InMemoryTreasuryStore`] for tests / single-process, a sqlite impl for
//! the bot.

use std::sync::Mutex;

use crate::config::Asset;

/// The pluggable two-balance store. All methods take `&self` (interior mutability)
/// so a [`Treasury`] can be shared. Balances are atomic token units.
pub trait TreasuryStore {
    /// Current USDC balance (the fuel), in atomic USDC units.
    fn usdc_balance(&self) -> u64;
    /// Current `$DREGG` balance (the pile), in atomic `$DREGG` units.
    fn dregg_balance(&self) -> u64;
    /// Set the USDC balance.
    fn set_usdc_balance(&self, v: u64);
    /// Set the `$DREGG` balance.
    fn set_dregg_balance(&self, v: u64);
}

/// A thread-safe in-memory [`TreasuryStore`] for tests and single-process
/// deployments.
#[derive(Default)]
pub struct InMemoryTreasuryStore {
    usdc: Mutex<u64>,
    dregg: Mutex<u64>,
}

impl InMemoryTreasuryStore {
    /// A fresh treasury store, both balances zero.
    pub fn new() -> Self {
        Self::default()
    }
}

impl TreasuryStore for InMemoryTreasuryStore {
    fn usdc_balance(&self) -> u64 {
        *self.usdc.lock().unwrap()
    }
    fn dregg_balance(&self) -> u64 {
        *self.dregg.lock().unwrap()
    }
    fn set_usdc_balance(&self, v: u64) {
        *self.usdc.lock().unwrap() = v;
    }
    fn set_dregg_balance(&self, v: u64) {
        *self.dregg.lock().unwrap() = v;
    }
}

/// Why a treasury draw-down failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TreasuryError {
    /// The USDC fuel tank does not cover the inference cost — the "must refuel"
    /// signal. Fail closed: no run is funded on an empty tank.
    InsufficientFuel {
        /// Atomic USDC units needed for this inference.
        needed: u64,
        /// Atomic USDC units available.
        available: u64,
    },
}

impl std::fmt::Display for TreasuryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TreasuryError::InsufficientFuel { needed, available } => write!(
                f,
                "insufficient USDC fuel: need {needed} atomic USDC, have {available} — refuel the treasury"
            ),
        }
    }
}

impl std::error::Error for TreasuryError {}

/// The two-balance treasury over a pluggable [`TreasuryStore`]. Carries the USDC
/// decimals so it can convert a USD-denominated inference cost to atomic USDC.
pub struct Treasury<S: TreasuryStore> {
    store: S,
    usdc_decimals: u8,
}

impl<S: TreasuryStore> Treasury<S> {
    /// New treasury. `usdc_decimals` is the USDC token decimals (from
    /// [`PayConfig::usdc_decimals`](crate::config::PayConfig::usdc_decimals)).
    pub fn new(store: S, usdc_decimals: u8) -> Self {
        Treasury {
            store,
            usdc_decimals,
        }
    }

    /// Borrow the underlying store.
    pub fn store(&self) -> &S {
        &self.store
    }

    /// The fuel balance (atomic USDC).
    pub fn usdc_balance(&self) -> u64 {
        self.store.usdc_balance()
    }

    /// The pile balance (atomic `$DREGG`).
    pub fn dregg_balance(&self) -> u64 {
        self.store.dregg_balance()
    }

    /// Route a received payment to the matching balance: USDC → the fuel tank,
    /// `$DREGG` → the pile. `amount` is atomic units of `asset`. Returns the new
    /// balance of that asset. (Saturating add — a treasury balance never wraps.)
    pub fn record_payment(&self, asset: Asset, amount: u64) -> u64 {
        match asset {
            Asset::Usdc => {
                let next = self.store.usdc_balance().saturating_add(amount);
                self.store.set_usdc_balance(next);
                next
            }
            Asset::Dregg => {
                let next = self.store.dregg_balance().saturating_add(amount);
                self.store.set_dregg_balance(next);
                next
            }
        }
    }

    /// Add `$DREGG` directly to the pile (e.g. operator top-up / seeding OTC
    /// inventory). Returns the new pile balance.
    pub fn deposit_dregg(&self, amount: u64) -> u64 {
        self.record_payment(Asset::Dregg, amount)
    }

    /// Add USDC directly to the fuel tank (e.g. an operator refuel). Returns the new
    /// fuel balance.
    pub fn deposit_usdc(&self, amount: u64) -> u64 {
        self.record_payment(Asset::Usdc, amount)
    }

    /// Convert a USD cost to atomic USDC, rounding UP (never under-charge the fuel).
    pub fn usd_to_atomic_usdc(&self, cost_usd: f64) -> u64 {
        let atomic = cost_usd.max(0.0) * 10f64.powi(self.usdc_decimals as i32);
        atomic.ceil() as u64
    }

    /// Draw down the fuel tank for one inference costing `cost_usd` (real USD). Fails
    /// closed with [`TreasuryError::InsufficientFuel`] when the tank cannot cover it —
    /// the "must refuel" signal. Returns the remaining fuel (atomic USDC) on success.
    ///
    /// This is called for EVERY run regardless of how it was paid: a `$DREGG`-paid run
    /// still burns USD inference (fuel out) while only the pile grew — the structural
    /// reason the pile must eventually be converted to fuel.
    pub fn spend_inference_usd(&self, cost_usd: f64) -> Result<u64, TreasuryError> {
        let needed = self.usd_to_atomic_usdc(cost_usd);
        let available = self.store.usdc_balance();
        if needed > available {
            return Err(TreasuryError::InsufficientFuel { needed, available });
        }
        let remaining = available - needed;
        self.store.set_usdc_balance(remaining);
        Ok(remaining)
    }

    /// Draw down the pile by `amount` atomic `$DREGG` (the accounting side of an OTC
    /// fill or a swap; the on-chain transfer executes behind the operator's signer).
    /// Fails closed if the pile is short.
    pub fn withdraw_dregg(&self, amount: u64) -> Result<u64, TreasuryError> {
        let available = self.store.dregg_balance();
        if amount > available {
            // Reuse the fuel error shape's spirit via a dedicated pile shortfall.
            return Err(TreasuryError::InsufficientFuel {
                needed: amount,
                available,
            });
        }
        let remaining = available - amount;
        self.store.set_dregg_balance(remaining);
        Ok(remaining)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn treasury() -> Treasury<InMemoryTreasuryStore> {
        Treasury::new(InMemoryTreasuryStore::new(), 6)
    }

    #[test]
    fn payments_route_to_the_right_balance() {
        let t = treasury();
        // A USDC payment fuels the tank; a $DREGG payment grows the pile.
        t.record_payment(Asset::Usdc, 1_000_000); // $1.00
        t.record_payment(Asset::Dregg, 500_000_000);
        assert_eq!(t.usdc_balance(), 1_000_000);
        assert_eq!(t.dregg_balance(), 500_000_000);
        // Cross-contamination would be a bug: a USDC payment must not touch the pile.
        assert_eq!(t.dregg_balance(), 500_000_000);
    }

    #[test]
    fn inference_draws_down_fuel_and_fails_closed_when_empty() {
        let t = treasury();
        t.deposit_usdc(30_000); // $0.03 of fuel
        // Two $0.01 inferences are fine.
        assert_eq!(t.spend_inference_usd(0.01).unwrap(), 20_000);
        assert_eq!(t.spend_inference_usd(0.01).unwrap(), 10_000);
        assert_eq!(t.spend_inference_usd(0.01).unwrap(), 0);
        // The tank is dry → the "must refuel" signal.
        let err = t.spend_inference_usd(0.01).unwrap_err();
        assert_eq!(
            err,
            TreasuryError::InsufficientFuel {
                needed: 10_000,
                available: 0
            }
        );
    }

    #[test]
    fn dregg_run_burns_fuel_but_only_grows_the_pile() {
        // The structural asymmetry: paid in $DREGG, but inference is still USD.
        let t = treasury();
        t.deposit_usdc(100_000); // pre-funded fuel
        t.record_payment(Asset::Dregg, 100_000_000); // a $DREGG-paid run's payment
        let fuel_before = t.usdc_balance();
        t.spend_inference_usd(0.01).unwrap(); // the run still burns USD
        assert!(t.usdc_balance() < fuel_before, "fuel went down");
        assert_eq!(t.dregg_balance(), 100_000_000, "pile only grew");
    }

    #[test]
    fn withdraw_pile_fails_closed_when_short() {
        let t = treasury();
        t.deposit_dregg(1_000);
        assert_eq!(t.withdraw_dregg(600).unwrap(), 400);
        assert!(t.withdraw_dregg(500).is_err());
        assert_eq!(t.dregg_balance(), 400, "failed withdraw changed nothing");
    }
}
