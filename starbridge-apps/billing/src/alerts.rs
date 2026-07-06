//! **Budget alerts** — threshold notifications (50% / 80% / 100% by default)
//! layered over the proven [`crate::cap::SpendCap`].
//!
//! The operated billing layer's `limits.rs` shipped two things: the hard spend
//! cap (ported here as [`crate::cap`], re-homed onto the forge-detecting
//! allowance capacity) and the **alert-threshold bookkeeping** — a
//! [`BudgetAlert`] record fired when an account's accrued spend first crosses
//! each configured percentage of the cap, for a console / notification surface
//! to render. The cap half was ported; THIS module ports the alert half, as a
//! thin observer over [`SpendCap`] (no ceiling arithmetic of its own — the cap
//! cell's committed `spent_this_epoch` is the only spend truth read here).
//!
//! Semantics (pinned by the tests, matching the operated original):
//! - each threshold fires **at most once** on the way up;
//! - one big charge can cross **several** thresholds at once (e.g. 40% → 85%
//!   fires both 50 and 80);
//! - a **refused** charge (the 402) fires nothing — spend did not move;
//! - alerts are **records returned to the caller**, not side effects.
//!
//! ## Wiring (deliberately unwired at port time)
//!
//! New file only. To activate: `starbridge-apps/billing/src/lib.rs` add
//! `pub mod alerts;` (+ optionally
//! `pub use alerts::{AlertingCap, BudgetAlert, ChargeOutcome, SpendLimit};`).
//! No new dependencies.

use dregg_types::CellId;

use crate::cap::{CapError, SpendCap, SpendDecision};

/// An alert raised when an account's accrued spend crosses a budget threshold.
/// A record for a console / notification surface — emitting it is the caller's
/// job.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetAlert {
    /// The account (cap-cell owner) whose spend crossed the threshold.
    pub account: CellId,
    /// The threshold crossed, in percent of the cap (e.g. `80`).
    pub threshold_pct: u8,
    /// The accrued spend at the moment the threshold fired.
    pub spent_units: i64,
    /// The hard spend cap (the per-period ceiling).
    pub cap_units: i64,
}

/// A per-account spend cap + the alert thresholds to fire on the way up.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpendLimit {
    /// The hard cap: spend beyond this is refused (enforced by the proven
    /// allowance ceiling, not by this module).
    pub cap_units: i64,
    /// The thresholds (percent of the cap) that fire an alert when first
    /// crossed, e.g. `[50, 80, 100]`. Order-independent; each fires at most
    /// once.
    pub alert_thresholds_pct: Vec<u8>,
}

impl SpendLimit {
    /// A spend cap of `cap_units` with the default `[50, 80, 100]` alert
    /// thresholds.
    pub fn new(cap_units: i64) -> SpendLimit {
        SpendLimit {
            cap_units,
            alert_thresholds_pct: vec![50, 80, 100],
        }
    }

    /// A spend cap with explicit alert thresholds.
    pub fn with_thresholds(cap_units: i64, alert_thresholds_pct: Vec<u8>) -> SpendLimit {
        SpendLimit {
            cap_units,
            alert_thresholds_pct,
        }
    }
}

/// The outcome of one charge through an [`AlertingCap`]: the proven cap's
/// [`SpendDecision`] plus any alert thresholds newly crossed by this charge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChargeOutcome {
    /// The underlying cap decision (admitted-and-drawn, or the 402 refusal).
    pub decision: SpendDecision,
    /// Alerts newly fired by this charge (empty on a refusal — spend did not
    /// move; possibly several at once for a big admitted charge).
    pub alerts: Vec<BudgetAlert>,
}

impl ChargeOutcome {
    /// Whether the charge was admitted.
    pub fn is_admitted(&self) -> bool {
        self.decision.is_admitted()
    }
}

/// A [`SpendCap`] with alert-threshold bookkeeping: the hard stop is the
/// proven allowance ceiling (the cap cell's committed counter, fail-closed);
/// this wrapper only watches the committed spend and reports which configured
/// thresholds each admitted charge newly crossed.
pub struct AlertingCap {
    account: CellId,
    cap: SpendCap,
    limit: SpendLimit,
    /// Thresholds already alerted (each fires at most once on the way up).
    fired: Vec<u8>,
}

impl AlertingCap {
    /// Open an alerting cap for `account` over `asset`, enforcing `limit`
    /// (the cap becomes the allowance ceiling; the period begins at block
    /// `start`). Rejects a non-positive cap ([`CapError::IllFormedTerms`]).
    pub fn open(
        account: CellId,
        asset: CellId,
        limit: SpendLimit,
        start: i64,
    ) -> Result<AlertingCap, CapError> {
        let cap = SpendCap::open(account, asset, limit.cap_units, start)?;
        Ok(AlertingCap {
            account,
            cap,
            limit,
            fired: Vec::new(),
        })
    }

    /// The account this cap bills.
    pub fn account(&self) -> CellId {
        self.account
    }

    /// The accrued spend within the period (the committed `spent_this_epoch`).
    pub fn spent(&self) -> i64 {
        self.cap.spent()
    }

    /// The remaining headroom under the cap at `at_block`.
    pub fn remaining(&self, at_block: i64) -> i64 {
        self.cap.remaining(at_block)
    }

    /// The hard cap.
    pub fn cap(&self) -> i64 {
        self.limit.cap_units
    }

    /// The underlying proven cap (for commitment / cell reads).
    pub fn spend_cap(&self) -> &SpendCap {
        &self.cap
    }

    /// Charge `amount` against the account at `at_block`. Admitted charges
    /// route through the proven [`SpendCap::charge`] (drawing the committed
    /// counter) and fire any alert thresholds newly crossed; refused charges
    /// (the 402) fire nothing. A rejection that is not the ceiling (a forged
    /// counter / stale epoch) surfaces as [`CapError`].
    pub fn charge(&mut self, amount: i64, at_block: i64) -> Result<ChargeOutcome, CapError> {
        let before = self.cap.spent();
        let decision = self.cap.charge(amount, at_block)?;
        let alerts = match &decision {
            SpendDecision::Admitted { spent_units, .. } => {
                self.cross_thresholds(before, *spent_units)
            }
            SpendDecision::Refused { .. } => Vec::new(),
        };
        Ok(ChargeOutcome { decision, alerts })
    }

    /// The thresholds newly crossed moving the committed spend from `before`
    /// to `after`, each recorded as fired so it never re-fires.
    fn cross_thresholds(&mut self, before: i64, after: i64) -> Vec<BudgetAlert> {
        let cap = self.limit.cap_units.max(0);
        if cap == 0 || after <= before {
            return Vec::new();
        }
        let mut alerts = Vec::new();
        let mut thresholds = self.limit.alert_thresholds_pct.clone();
        thresholds.sort_unstable();
        for pct in thresholds {
            if self.fired.contains(&pct) {
                continue;
            }
            // The threshold value in units, rounding the way the operated
            // original did: crossed when spend REACHES pct% of the cap.
            let bar = cap.saturating_mul(pct as i64) / 100;
            if before < bar && after >= bar {
                self.fired.push(pct);
                alerts.push(BudgetAlert {
                    account: self.account,
                    threshold_pct: pct,
                    spent_units: after,
                    cap_units: cap,
                });
            }
        }
        alerts
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    /// Account 1, asset 9, cap 100, defaults [50, 80, 100], period from 1000.
    fn guard() -> AlertingCap {
        AlertingCap::open(cid(1), cid(9), SpendLimit::new(100), 1000).unwrap()
    }

    #[test]
    fn under_threshold_charges_fire_nothing() {
        let mut g = guard();
        let out = g.charge(40, 1500).unwrap();
        assert!(out.is_admitted());
        assert!(out.alerts.is_empty(), "40% crosses no default threshold");
        assert_eq!(g.spent(), 40);
    }

    #[test]
    fn crossing_a_threshold_fires_once() {
        let mut g = guard();
        g.charge(40, 1500).unwrap();
        // 40 → 55 crosses 50%.
        let out = g.charge(15, 1600).unwrap();
        assert_eq!(out.alerts.len(), 1);
        assert_eq!(out.alerts[0].threshold_pct, 50);
        assert_eq!(out.alerts[0].spent_units, 55);
        assert_eq!(out.alerts[0].cap_units, 100);
        assert_eq!(out.alerts[0].account, cid(1));
        // Staying above 50% fires nothing more for that threshold.
        let out2 = g.charge(5, 1700).unwrap();
        assert!(out2.alerts.is_empty(), "each threshold fires at most once");
    }

    #[test]
    fn one_big_charge_can_fire_several_thresholds() {
        let mut g = guard();
        g.charge(40, 1500).unwrap();
        // 40 → 85 crosses both 50 and 80 in one charge.
        let out = g.charge(45, 1600).unwrap();
        let pcts: Vec<u8> = out.alerts.iter().map(|a| a.threshold_pct).collect();
        assert_eq!(pcts, vec![50, 80]);
    }

    #[test]
    fn reaching_the_cap_fires_the_100_and_the_next_unit_is_refused() {
        let mut g = guard();
        let out = g.charge(100, 1500).unwrap();
        assert!(out.is_admitted());
        let pcts: Vec<u8> = out.alerts.iter().map(|a| a.threshold_pct).collect();
        assert_eq!(pcts, vec![50, 80, 100]);

        // The very next unit is the 402: refused by the PROVEN ceiling, and no
        // alert fires (spend did not move).
        let refused = g.charge(1, 1600).unwrap();
        assert!(!refused.is_admitted());
        assert!(refused.alerts.is_empty());
        assert_eq!(g.spent(), 100, "the refusal drew nothing");
    }

    #[test]
    fn refused_charges_never_fire_alerts() {
        let mut g = guard();
        g.charge(49, 1500).unwrap();
        // 49 + 60 > 100 → refused; 50% must NOT fire even though the attempt
        // would have crossed it.
        let out = g.charge(60, 1600).unwrap();
        assert!(!out.is_admitted());
        assert!(out.alerts.is_empty());
        // A later admitted crossing still fires it exactly once.
        let out2 = g.charge(2, 1700).unwrap();
        assert_eq!(out2.alerts.len(), 1);
        assert_eq!(out2.alerts[0].threshold_pct, 50);
    }

    #[test]
    fn custom_thresholds_are_honored() {
        let mut g = AlertingCap::open(
            cid(1),
            cid(9),
            SpendLimit::with_thresholds(200, vec![25, 90]),
            1000,
        )
        .unwrap();
        // 0 → 50 crosses 25% (bar = 50).
        let out = g.charge(50, 1500).unwrap();
        assert_eq!(
            out.alerts
                .iter()
                .map(|a| a.threshold_pct)
                .collect::<Vec<_>>(),
            vec![25]
        );
        // 50 → 180 crosses 90% (bar = 180).
        let out2 = g.charge(130, 1600).unwrap();
        assert_eq!(
            out2.alerts
                .iter()
                .map(|a| a.threshold_pct)
                .collect::<Vec<_>>(),
            vec![90]
        );
    }

    #[test]
    fn a_zero_cap_is_ill_formed() {
        assert!(matches!(
            AlertingCap::open(cid(1), cid(9), SpendLimit::new(0), 1000),
            Err(CapError::IllFormedTerms)
        ));
    }

    #[test]
    fn the_hard_stop_is_the_committed_cell_not_this_wrapper() {
        // The wrapper adds bookkeeping ONLY: the underlying cap cell's
        // commitment moves on an admitted charge (the proven capacity is the
        // enforcement point).
        let mut g = guard();
        let before = g.spend_cap().cell.state_commitment();
        g.charge(10, 1500).unwrap();
        assert_ne!(before, g.spend_cap().cell.state_commitment());
    }
}
