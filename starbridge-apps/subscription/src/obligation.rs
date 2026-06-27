//! # subscription — the recurring BILLING core on the proven `StandingObligation` capacity.
//!
//! The rest of this crate (`lib.rs`, [`crate::service`], [`crate::card`]) models a
//! publish/consume **feed** — a message queue whose head/tail cursors are flat
//! `SetField` slots. That is the *delivery* half of a subscription. This module is the
//! **billing** half, and it is the half the protocol-frontier census
//! (`docs/deos/PROTOCOL-FRONTIER-FOR-APPS.md` §1) names: *a subscription IS a standing
//! obligation* — a recurring per-period payment that must be discharged each period or
//! lapses — and the proven [`StandingObligation`](dregg_cell::obligation_standing)
//! house-capacity was **UNUSED** by any app. This module makes it USED.
//!
//! ## Not hand-rolled slot arithmetic — the proven capacity
//!
//! A naive billing model would track "paid through period N" as a counter slot and
//! compare it to `(now - start) / period` by hand. That hand-rolled arithmetic is
//! exactly what the [`StandingObligation`](dregg_cell::obligation_standing) capacity
//! replaces with a *forge-rejecting, committed* core, proven in
//! `metatheory/Dregg2/Deos/StandingObligation.lean`:
//!
//!  * the per-period **temporal cursor** (`next_due = start + k·period`) is committed in
//!    the cell's sorted-Poseidon2 heap and advances **strictly** one period per payment
//!    (the StrictMonotonic-slot discipline — `cursor_strict_mono`);
//!  * a payment is **one-shot per period** (`replay_rejected`): paying period `k` twice
//!    is refused because the cursor has already advanced past it;
//!  * a payment is **never early** (`early_discharge_rejected`): the schedule clock must
//!    have reached the period's due block;
//!  * a payment is **never over/under** (`over_discharge_rejected`): the amount must
//!    equal the committed price;
//!  * a **missed period lapses** (`behind_schedule_rejected`): a subscription whose
//!    committed paid-count lags the number of periods the schedule demands by `now` is
//!    detectably behind — the lapse is not a hand-set flag, it is computed against the
//!    committed cursor.
//!
//! So this module is a thin, honest NAMING of the proven capacity in subscription
//! vocabulary: a [`BillingPlan`] *is* an `ObligationTerms`, a [`Subscription`] *is* an
//! obligation cell, `pay` *is* `discharge`, and `is_lapsed` *is* the obligation
//! `audit`. No billing arithmetic lives here that the capacity does not prove.
//!
//! ## The honest seam (the named next slice, NOT closed here)
//!
//! The proven capacity is an **executor-witnessed** cell object: it operates on a
//! [`dregg_cell::Cell`]'s committed heap, and a re-executing validator that holds the
//! cell + terms sees every forge rejected. What it is NOT *yet* is an **EffectVM
//! effect** — there is no `Effect::DischargeObligation` gate, so a light client
//! verifying a *batch* does not yet witness "due ∧ not-paid ⟹ paid ∧ cursor advanced"
//! as part of the proven kernel transition. That circuit weld is the VK-affecting next
//! slice named in `StandingObligation.lean` §"The named follow-up" and
//! `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`; it is deliberately NOT forged from
//! the app layer. The **value move** of each period, however, IS a real conserved
//! kernel effect today: [`Subscription::pay_transfer_effect`] is an
//! [`Effect::Transfer`] — the same one the [`Payable`](dregg_app_framework::Payable)
//! DSI desugars to — so the per-period money genuinely moves obligor → beneficiary
//! under the kernel's per-asset Σδ=0 conservation, while the *schedule* is enforced by
//! the proven obligation core.

use dregg_app_framework::Effect;
use dregg_cell::Cell;
use dregg_cell::CellId;
use dregg_cell::obligation_standing::{
    Discharge, ObligationError, ObligationState, ObligationTerms, discharge, is_obligation,
    open_obligation,
};
use dregg_cell::obligation_standing::{KEY_TERMS_DIGEST, OBLIGATION_COLL};

/// A subscription **billing plan** — the recurring agreement, expressed directly as the
/// proven [`ObligationTerms`]. A plan says: the `subscriber` owes `price` of `asset` to
/// the `provider` every `period_blocks`, starting at `first_due_block`, for
/// `term_periods` periods (`0` = perpetual / until cancelled).
///
/// This is the subscription vocabulary over the capacity's terms; [`Self::terms`] is the
/// identity map into the proven type, so a plan and the obligation it seals are the same
/// object under two names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BillingPlan {
    /// The subscriber — who pays each period (the obligation's `obligor`).
    pub subscriber: CellId,
    /// The provider — who is paid each period (the obligation's `beneficiary`).
    pub provider: CellId,
    /// The asset each period is denominated in.
    pub asset: CellId,
    /// The price charged each period. Must be `> 0`.
    pub price: i64,
    /// The period length in blocks — the stride of the temporal cursor. Must be `> 0`.
    pub period_blocks: i64,
    /// The block at which the first period falls due (the obligation `start`).
    pub first_due_block: i64,
    /// The bounded number of periods, or `0` for a perpetual subscription.
    pub term_periods: i64,
}

impl BillingPlan {
    /// A new monthly-style plan: `subscriber` owes `price` of `asset` to `provider`
    /// every `period_blocks`, first due at `first_due_block`, for `term_periods`
    /// (`0` = perpetual).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        subscriber: CellId,
        provider: CellId,
        asset: CellId,
        price: i64,
        period_blocks: i64,
        first_due_block: i64,
        term_periods: i64,
    ) -> Self {
        BillingPlan {
            subscriber,
            provider,
            asset,
            price,
            period_blocks,
            first_due_block,
            term_periods,
        }
    }

    /// The proven [`ObligationTerms`] this plan seals — the identity map into the
    /// capacity. A plan IS its obligation terms.
    pub fn terms(&self) -> ObligationTerms {
        ObligationTerms::new(
            self.subscriber,
            self.provider,
            self.asset,
            self.price,
            self.period_blocks,
            self.first_due_block,
            self.term_periods,
        )
    }

    /// The block at which period `k` (0-indexed) falls due — the temporal cursor value.
    pub fn due_block(&self, k: i64) -> i64 {
        self.terms().due_block(k)
    }

    /// Whether the plan is well-formed (positive price + period). Ill-formed plans
    /// cannot open a subscription.
    pub fn is_well_formed(&self) -> bool {
        self.terms().is_well_formed()
    }
}

/// A live **subscription** — a [`dregg_cell::Cell`] carrying the proven standing
/// obligation, plus the [`BillingPlan`] it was opened under and an app-level
/// `cancelled` lifecycle label.
///
/// Every state-changing method routes through the proven capacity
/// ([`open_obligation`] / [`discharge`] / [`ObligationState::audit`]); the only state
/// not in the proven core is the `cancelled` label, which is honest app lifecycle on
/// TOP of the capacity (cancellation re-seals the term to the periods already paid, so
/// the proven `Completed`/`audit` semantics then close the obligation).
#[derive(Clone, Debug)]
pub struct Subscription {
    /// The contract cell carrying the committed obligation ledger (terms digest,
    /// `next_due` cursor, paid count, paid total — all in the sorted-Poseidon2 heap).
    pub cell: Cell,
    /// The plan currently in force. Updated by [`Self::renew`] / [`Self::cancel`] so it
    /// always matches the cell's committed terms digest.
    pub plan: BillingPlan,
    /// App-level lifecycle: set by [`Self::cancel`]. The on-cell effect of cancelling is
    /// the term-cap re-seal; this label records that it was a cancellation (vs a natural
    /// bounded completion).
    pub cancelled: bool,
}

/// Why a subscription billing operation was refused. Wraps the proven capacity's
/// [`ObligationError`] so callers see the exact forge/skip rejection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BillingError {
    /// The plan is ill-formed (non-positive price or period).
    IllFormedPlan,
    /// The subscription has been cancelled; no further period is owed.
    Cancelled,
    /// A proven-capacity rejection: early payment, double payment, wrong amount,
    /// completed term, or behind schedule.
    Obligation(ObligationError),
}

impl std::fmt::Display for BillingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BillingError::IllFormedPlan => write!(f, "billing plan is not well-formed"),
            BillingError::Cancelled => write!(f, "subscription is cancelled"),
            BillingError::Obligation(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for BillingError {}

/// A read-only **status** of a subscription at a given schedule clock — everything a
/// card or service face surfaces. Every field is derived from the committed obligation
/// state and the proven schedule; nothing is hand-tracked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubscriptionStatus {
    /// The committed `next_due` cursor — the block at which the next unpaid period falls
    /// due.
    pub next_due_block: i64,
    /// The period index the cursor currently expects (`0`-based).
    pub period_index: i64,
    /// How many periods have been paid (the committed discharged count).
    pub periods_paid: i64,
    /// The cumulative amount paid (the committed discharged total).
    pub total_paid: i64,
    /// How many periods the schedule says MUST be paid by `clock`.
    pub periods_due_by_now: i64,
    /// Whether the subscription is **lapsed** — a due period went unpaid (the committed
    /// paid-count is behind the schedule). The proven `audit` tooth.
    pub lapsed: bool,
    /// Whether a bounded term has been fully discharged.
    pub completed: bool,
    /// Whether the subscription was cancelled (app lifecycle).
    pub cancelled: bool,
}

impl SubscriptionStatus {
    /// Whether the subscription is **active**: configured, not lapsed, not completed,
    /// not cancelled — i.e. a paying subscriber in good standing.
    pub fn is_active(&self) -> bool {
        !self.lapsed && !self.completed && !self.cancelled
    }
}

impl Subscription {
    /// **Subscribe** — open a fresh standing obligation on a new contract cell under
    /// `plan`. Seals the plan's terms digest and initializes the temporal cursor to the
    /// first due block (`open_obligation`), with zero periods paid. Rejects an
    /// ill-formed plan.
    ///
    /// The contract cell's `token_id` is the plan's `asset` and its public key is the
    /// subscriber — a self-contained obligation-bearing cell. (In a deployment the
    /// obligation rides the subscriber↔provider relationship cell; here we mint a
    /// dedicated contract cell so the obligation is testable end-to-end.)
    pub fn subscribe(plan: BillingPlan) -> Result<Subscription, BillingError> {
        if !plan.is_well_formed() {
            return Err(BillingError::IllFormedPlan);
        }
        let mut cell = Cell::with_balance(*plan.subscriber.as_bytes(), *plan.asset.as_bytes(), 0);
        open_obligation(&mut cell, &plan.terms()).map_err(BillingError::Obligation)?;
        Ok(Subscription {
            cell,
            plan,
            cancelled: false,
        })
    }

    /// Whether this cell genuinely carries a standing obligation (a terms digest in the
    /// reserved heap collection).
    pub fn is_obligation(&self) -> bool {
        is_obligation(&self.cell)
    }

    /// The period index the committed cursor currently expects — derived from the
    /// committed `next_due`, NOT trusted from any input.
    pub fn expected_period(&self) -> i64 {
        let state = ObligationState::read(&self.cell).expect("subscription carries an obligation");
        (state.next_due - self.plan.first_due_block) / self.plan.period_blocks
    }

    /// **Pay the current period** at schedule clock `clock` — discharge the obligation.
    /// Routes entirely through the proven [`discharge`]: the temporal cursor must have
    /// reached this period's due block (no early pay), the period must be the cursor's
    /// current one (no double pay / no skip), and the amount paid is exactly the plan
    /// price. On accept the committed cursor advances strictly by one period, the
    /// paid-count increments, and the paid-total grows. Returns the amount moved (the
    /// price), which [`Self::pay_transfer_effect`] turns into the real value move.
    ///
    /// Nothing is mutated on a rejection (the proven capacity is fail-closed).
    pub fn pay(&mut self, clock: i64) -> Result<i64, BillingError> {
        if self.cancelled {
            return Err(BillingError::Cancelled);
        }
        let step = Discharge {
            period_index: self.expected_period(),
            amount: self.plan.price,
            clock,
        };
        discharge(&mut self.cell, &self.plan.terms(), &step).map_err(BillingError::Obligation)
    }

    /// The **real value move** of one period — the conserved kernel [`Effect::Transfer`]
    /// of the plan price from the subscriber to the provider. This is exactly the effect
    /// the [`Payable`](dregg_app_framework::Payable) DSI desugars `pay` to
    /// ([`dregg_app_framework::pay_effects`]), so the per-period money crosses the app
    /// boundary under per-asset Σδ=0 conservation. Pair it with [`Self::pay`]: the
    /// schedule is enforced by the proven obligation, the value by the conserved
    /// transfer.
    pub fn pay_transfer_effect(&self) -> Effect {
        Effect::Transfer {
            from: self.plan.subscriber,
            to: self.plan.provider,
            amount: self.plan.price.max(0) as u64,
        }
    }

    /// Whether the subscription is **lapsed** at `clock` — a due period went unpaid. The
    /// proven `audit` tooth: a subscription whose committed paid-count is behind the
    /// number of periods the schedule demands by `clock` is detectably behind. A
    /// cancelled subscription is never "lapsed" (it is closed, not delinquent).
    pub fn is_lapsed(&self, clock: i64) -> bool {
        if self.cancelled {
            return false;
        }
        let state = ObligationState::read(&self.cell).expect("subscription carries an obligation");
        matches!(
            state.audit(&self.plan.terms(), clock),
            Err(ObligationError::BehindSchedule { .. })
        )
    }

    /// The full [`SubscriptionStatus`] at `clock` — the read every face surfaces. All
    /// fields are derived from the committed obligation state and the proven schedule.
    pub fn status(&self, clock: i64) -> SubscriptionStatus {
        let terms = self.plan.terms();
        let state = ObligationState::read(&self.cell).expect("subscription carries an obligation");
        let period_index = self.expected_period();
        let periods_due_by_now = terms.periods_due_by(clock);
        let lapsed = self.is_lapsed(clock);
        let completed = terms.count > 0 && period_index >= terms.count;
        SubscriptionStatus {
            next_due_block: state.next_due,
            period_index,
            periods_paid: state.discharged_count,
            total_paid: state.discharged_total,
            periods_due_by_now,
            lapsed,
            completed,
            cancelled: self.cancelled,
        }
    }

    /// **Renew** — extend a bounded subscription by `additional_periods` more periods (or
    /// turn a bounded plan perpetual with `additional_periods` large enough). Re-seals
    /// the obligation's terms digest to the renewed plan while PRESERVING the committed
    /// cursor, paid-count, and paid-total — the renewal is a continuation, not a reset.
    ///
    /// A perpetual plan (`term_periods == 0`) never completes, so renewing it is a no-op
    /// that returns `Ok` unchanged. Renewing past the bound on a bounded plan lets the
    /// next period be paid where it would previously have been `Completed`.
    pub fn renew(&mut self, additional_periods: i64) -> Result<(), BillingError> {
        if self.cancelled {
            return Err(BillingError::Cancelled);
        }
        if self.plan.term_periods == 0 || additional_periods <= 0 {
            return Ok(());
        }
        let renewed = BillingPlan {
            term_periods: self.plan.term_periods + additional_periods,
            ..self.plan.clone()
        };
        self.reseal_terms(&renewed)?;
        self.plan = renewed;
        Ok(())
    }

    /// **Cancel** — close the subscription at `clock`. Re-seals the obligation's term to
    /// exactly the periods already paid, so the proven `Completed`/`audit` semantics then
    /// hold: no further period is owed and the subscription is never "behind" again. Sets
    /// the app-level cancelled label.
    ///
    /// This is faithful lifecycle on the proven capacity — cancellation does not delete
    /// the obligation, it caps its bounded term to the paid history, which the capacity's
    /// own `periods_due_by` (capped at `count`) and `Completed` check then enforce.
    pub fn cancel(&mut self) -> Result<(), BillingError> {
        if self.cancelled {
            return Ok(());
        }
        let state = ObligationState::read(&self.cell).expect("subscription carries an obligation");
        let capped = BillingPlan {
            term_periods: state.discharged_count,
            ..self.plan.clone()
        };
        self.reseal_terms(&capped)?;
        self.plan = capped;
        self.cancelled = true;
        Ok(())
    }

    /// Re-seal the obligation's `KEY_TERMS_DIGEST` (in the capacity's reserved
    /// `OBLIGATION_COLL`) to `new_plan`'s terms, preserving the committed cursor/count/
    /// total. The same heap write `open_obligation` performs for the digest, with a new
    /// digest — a genuine re-agreement, not a reset.
    fn reseal_terms(&mut self, new_plan: &BillingPlan) -> Result<(), BillingError> {
        if !new_plan.is_well_formed() {
            return Err(BillingError::IllFormedPlan);
        }
        self.cell
            .state
            .set_heap(OBLIGATION_COLL, KEY_TERMS_DIGEST, new_plan.terms().digest());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    /// Subscriber cell 1 owes 50 of asset 9 to provider cell 2, every 100 blocks,
    /// starting at block 1000, perpetual.
    fn sample_plan() -> BillingPlan {
        BillingPlan::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0)
    }

    // ── the temporal cursor + per-period discharge (the proven core) ──────────

    /// THE HONEST PATH: subscribing opens the cursor at the first due block; paying the
    /// current period on schedule advances the temporal cursor strictly by one period,
    /// increments the paid count, and grows the paid total — the proven discharge.
    #[test]
    fn subscribe_then_pay_advances_the_temporal_cursor() {
        let plan = sample_plan();
        let mut sub = Subscription::subscribe(plan).unwrap();
        assert!(sub.is_obligation());

        let s0 = sub.status(999);
        assert_eq!(
            s0.next_due_block, 1000,
            "cursor opens at the first due block"
        );
        assert_eq!(s0.periods_paid, 0);
        assert!(
            s0.is_active(),
            "before the first period is due, the subscription is active"
        );
        // At the exact due block, the unpaid period 0 is already owed — lapsed until paid.
        assert!(
            sub.status(1000).lapsed,
            "an unpaid due period is behind schedule"
        );

        // Pay period 0, due at 1000, at clock 1000.
        assert_eq!(sub.pay(1000), Ok(50), "on-schedule payment accepts");
        let s1 = sub.status(1050);
        assert_eq!(
            s1.next_due_block, 1100,
            "cursor advances strictly one period"
        );
        assert_eq!(s1.periods_paid, 1);
        assert_eq!(s1.total_paid, 50);
        assert_eq!(s1.period_index, 1);
        assert!(s1.is_active());

        // Pay period 1, due at 1100.
        assert_eq!(sub.pay(1100), Ok(50));
        assert_eq!(sub.status(1100).next_due_block, 1200);
        assert_eq!(sub.status(1100).periods_paid, 2);
    }

    /// The temporal cursor is ENFORCED: paying before the period's due block is refused
    /// (the proven no-early tooth). Period 0 is due at 1000; a payment at 999 is rejected.
    #[test]
    fn early_payment_is_rejected_by_the_temporal_cursor() {
        let mut sub = Subscription::subscribe(sample_plan()).unwrap();
        assert_eq!(
            sub.pay(999),
            Err(BillingError::Obligation(ObligationError::NotYetDue {
                due_block: 1000,
                clock: 999,
            })),
            "cannot pay a period before its due block"
        );
        // nothing moved.
        assert_eq!(sub.status(999).periods_paid, 0);
        // and the same period pays fine once due.
        assert_eq!(sub.pay(1000), Ok(50));
    }

    /// A period is ONE-SHOT (the proven cursor advance): after paying period 0 the cursor
    /// expects period 1, so re-paying period 0 is refused — no double-charge.
    #[test]
    fn double_payment_of_one_period_is_rejected() {
        let mut sub = Subscription::subscribe(sample_plan()).unwrap();
        assert_eq!(sub.pay(1000), Ok(50));
        // A second payment "for the same period" is now a payment of period 1 (the
        // cursor advanced); at clock 1000 period 1 (due 1100) is not yet due.
        assert_eq!(
            sub.pay(1000),
            Err(BillingError::Obligation(ObligationError::NotYetDue {
                due_block: 1100,
                clock: 1000,
            })),
            "the cursor advanced — there is no second period-0 payment"
        );
        assert_eq!(sub.status(1000).periods_paid, 1, "still exactly one paid");
    }

    // ── the lapse (the proven audit tooth) ────────────────────────────────────

    /// A MISSED period LAPSES: by block 1250 the schedule demands 3 periods paid
    /// (0@1000, 1@1100, 2@1200). A subscriber who paid only period 0 is behind — lapsed.
    /// An on-schedule subscriber is active. The proven `audit` tooth.
    #[test]
    fn missed_period_lapses_the_subscription() {
        let mut behind = Subscription::subscribe(sample_plan()).unwrap();
        behind.pay(1000).unwrap(); // only period 0.

        let s = behind.status(1250);
        assert_eq!(
            s.periods_due_by_now, 3,
            "schedule demands 3 periods by 1250"
        );
        assert_eq!(s.periods_paid, 1);
        assert!(s.lapsed, "a subscriber behind the schedule is lapsed");
        assert!(!s.is_active());

        // An on-schedule subscriber that paid all three is active at the same clock.
        let mut current = Subscription::subscribe(sample_plan()).unwrap();
        current.pay(1000).unwrap();
        current.pay(1100).unwrap();
        current.pay(1200).unwrap();
        let s2 = current.status(1250);
        assert!(!s2.lapsed, "an on-schedule subscriber is not lapsed");
        assert!(s2.is_active());
        assert_eq!(s2.periods_paid, 3);
    }

    // ── over/under-charge rejection ───────────────────────────────────────────

    /// The price is committed: a payment whose amount differs from the plan price is
    /// rejected (the proven no-over/under tooth). We drive `check_discharge` directly to
    /// witness an over- and under-statement, since `pay` always uses the plan price.
    #[test]
    fn over_or_under_charge_is_rejected() {
        let sub = Subscription::subscribe(sample_plan()).unwrap();
        let terms = sub.plan.terms();
        let state = ObligationState::read(&sub.cell).unwrap();
        assert_eq!(
            state.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50),
            "exact price accepts"
        );
        assert!(matches!(
            state.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 9_999,
                    clock: 1000
                }
            ),
            Err(ObligationError::AmountMismatch {
                owed: 50,
                presented: 9_999
            })
        ));
        assert!(matches!(
            state.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 1,
                    clock: 1000
                }
            ),
            Err(ObligationError::AmountMismatch {
                owed: 50,
                presented: 1
            })
        ));
    }

    // ── the value move (the real conserved Effect::Transfer) ──────────────────

    /// Each period's value move is a real conserved kernel `Effect::Transfer` of the
    /// plan price from subscriber to provider — the Payable DSI desugaring.
    #[test]
    fn pay_transfer_effect_is_a_conserved_transfer() {
        let sub = Subscription::subscribe(sample_plan()).unwrap();
        let eff = sub.pay_transfer_effect();
        match eff {
            Effect::Transfer { from, to, amount } => {
                assert_eq!(from, cid(1), "from the subscriber");
                assert_eq!(to, cid(2), "to the provider");
                assert_eq!(amount, 50, "the period price");
            }
            other => panic!("expected Effect::Transfer, got {other:?}"),
        }
        // It IS the Payable DSI desugaring (Effect has no PartialEq, so match the shape).
        let dsi = dregg_app_framework::pay_effects(cid(1), cid(2), 50);
        assert_eq!(dsi.len(), 1);
        assert!(matches!(
            dsi[0],
            Effect::Transfer { from, to, amount } if from == cid(1) && to == cid(2) && amount == 50
        ));
    }

    /// Paying re-seals the cell commitment — a light client sees the cursor advance, so
    /// a forge (a rewound cursor reopening a paid period) cannot hide.
    #[test]
    fn paying_moves_the_committed_state() {
        let mut sub = Subscription::subscribe(sample_plan()).unwrap();
        let before = sub.cell.state_commitment();
        sub.pay(1000).unwrap();
        let after = sub.cell.state_commitment();
        assert_ne!(
            before, after,
            "discharging a period re-seals the commitment"
        );
    }

    // ── bounded terms, renew, cancel (the lifecycle) ──────────────────────────

    /// A bounded subscription COMPLETES: a 2-period plan pays periods 0 and 1, then the
    /// third payment is refused as completed — the proven bounded-count tooth.
    #[test]
    fn bounded_subscription_completes() {
        let plan = BillingPlan::new(cid(1), cid(2), cid(9), 50, 100, 1000, 2);
        let mut sub = Subscription::subscribe(plan).unwrap();
        assert_eq!(sub.pay(1000), Ok(50));
        assert_eq!(sub.pay(1100), Ok(50));
        assert_eq!(
            sub.pay(1200),
            Err(BillingError::Obligation(ObligationError::Completed {
                count: 2
            })),
            "a fully-discharged bounded term is complete"
        );
        let s = sub.status(1200);
        assert!(s.completed);
        assert!(!s.lapsed, "a completed bounded subscription is not behind");
    }

    /// RENEW extends a bounded term while preserving paid history: a 1-period plan
    /// completes after period 0, but renewing for one more period lets period 1 be paid.
    #[test]
    fn renew_extends_a_bounded_term_preserving_history() {
        let plan = BillingPlan::new(cid(1), cid(2), cid(9), 50, 100, 1000, 1);
        let mut sub = Subscription::subscribe(plan).unwrap();
        assert_eq!(sub.pay(1000), Ok(50));
        // Without renewing, period 1 is past the bounded term.
        assert_eq!(
            sub.pay(1100),
            Err(BillingError::Obligation(ObligationError::Completed {
                count: 1
            })),
        );
        // Renew for one more period — paid history (1 period, total 50) is preserved.
        sub.renew(1).unwrap();
        assert_eq!(
            sub.status(1100).periods_paid,
            1,
            "renew preserves paid history"
        );
        assert_eq!(sub.status(1100).total_paid, 50);
        // Now period 1 pays.
        assert_eq!(sub.pay(1100), Ok(50), "renewed period now pays");
        assert_eq!(sub.status(1100).periods_paid, 2);
    }

    /// CANCEL closes the subscription: it caps the term to the paid periods, so no
    /// further period is owed and the subscription is never "behind" again — even as the
    /// clock runs far past where unpaid periods would have made it lapse.
    #[test]
    fn cancel_closes_the_subscription() {
        let mut sub = Subscription::subscribe(sample_plan()).unwrap();
        sub.pay(1000).unwrap(); // period 0 paid, then cancel.
        sub.cancel().unwrap();
        assert!(sub.cancelled);

        // Far past where an active subscriber would be 100s of periods behind:
        let s = sub.status(1_000_000);
        assert!(!s.lapsed, "a cancelled subscription is not delinquent");
        assert!(!s.is_active(), "a cancelled subscription is not active");
        assert!(s.completed, "the term is capped at the paid periods");

        // No further period can be paid.
        assert_eq!(sub.pay(1_000_000), Err(BillingError::Cancelled));
    }

    /// Renewing a perpetual plan is a no-op (it never completes), and an ill-formed plan
    /// cannot open a subscription.
    #[test]
    fn perpetual_renew_is_noop_and_illformed_is_rejected() {
        let mut sub = Subscription::subscribe(sample_plan()).unwrap();
        assert_eq!(sub.renew(5), Ok(()), "renewing a perpetual plan is a no-op");
        assert_eq!(sub.plan.term_periods, 0, "still perpetual");

        let bad = BillingPlan::new(cid(1), cid(2), cid(9), 0, 100, 1000, 0);
        assert!(matches!(
            Subscription::subscribe(bad),
            Err(BillingError::IllFormedPlan)
        ));
    }

    /// `expected_period` tracks the committed cursor, not any input.
    #[test]
    fn expected_period_tracks_the_committed_cursor() {
        let mut sub = Subscription::subscribe(sample_plan()).unwrap();
        assert_eq!(sub.expected_period(), 0);
        sub.pay(1000).unwrap();
        assert_eq!(sub.expected_period(), 1);
        sub.pay(1100).unwrap();
        assert_eq!(sub.expected_period(), 2);
    }
}
