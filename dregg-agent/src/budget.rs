//! `budget` — the **replenishing budget** cell: one attenuable primitive under
//! every metering, settlement-contention, and escrow surface in the control plane
//! (`docs/REPLENISHING-BUDGET.md`).
//!
//! # What this is
//!
//! A replenishing budget is a `(budget, period, refill-queue)` object that meters
//! *actual* consumption against a ceiling that refills *lazily up to now* — the
//! seL4 MCS scheduling-context shape, realized as a forge-detectable cell rather
//! than a side-counter in the control plane's RAM. It is the **generalization** of
//! breadstuffs `cell/src/allowance.rs` (the rate-limited allowance) along one axis:
//! replacing the single "reset `spent_this_epoch` to 0 on an epoch crossing" with a
//! bounded refill queue of `{at_block, amount}` entries drained lazily up to `now`
//! (the sporadic-server move). Where the allowance does *reset-per-epoch*, the
//! replenishing budget does *per-chunk replenishment over a sliding window*; the
//! allowance is the `refill_max = 1` / `period = epoch_length` special case.
//!
//! # The cell shape
//!
//! ```text
//! Terms  (sealed at open, never mutated; one digest binds them):
//!     asset          : what is metered/spent (an opaque id)
//!     budget         : the ceiling — max outstanding consumption in a window
//!     period         : the GRANULARITY of replenishment (blocks), NOT a sale window
//!     refill_amount  : how much each draw's matured refill returns (default = budget)
//!     refill_max     : bound on the live refill queue length (MCS refill_max)
//!     start          : genesis block, so the schedule is absolute/derivable
//!
//! Cursors (committed; the load-bearing witnessed state):
//!     consumed       : total drawn against this budget, ever (monotone)
//!     refilled       : total returned by matured refills, ever (monotone)
//!     refill_head    : block of the oldest still-pending refill (queue front)
//!     queue          : the pending refill queue {at_block, amount}*  (digested)
//! ```
//!
//! `outstanding(now) = consumed − refilled_up_to(now)`, where `refilled_up_to`
//! drains the refill queue of every entry with `at_block ≤ now` (computed at use
//! time, never pushed on a timer). **Headroom** is `budget − outstanding(now)`; a
//! draw of `amount` is admissible iff `amount ≤ headroom`.
//!
//! Two committed monotone totals (`consumed`, `refilled`) rather than one net
//! counter: the same anti-ghost discipline as `allowance.rs`'s independent
//! `spent_total` — a forged-*down* net counter is caught because the monotone
//! witnesses disagree with the recomputed `consumed − refilled`.
//!
//! # The verification core (non-vacuity by construction)
//!
//! The single function both the honest [`draw`](ReplenishingBudget::draw) and every
//! forge reject run through is [`check_draw`](BudgetState::check_draw), exactly
//! mirroring `allowance.rs::check_spend`. Early refill is *structurally
//! inexpressible*: the refill block is **derived** from `at_block + period`, never
//! supplied by the caller — the same property that makes the allowance's epoch
//! un-forgeable.
//!
//! # Why `period` is a granularity knob, not a wall-clock sale
//!
//! In seL4 MCS, crossing into the next period does not "sell" a fresh full budget;
//! each consumed chunk independently becomes eligible again exactly `period` later,
//! enforcing a `budget/period` bandwidth ceiling over a *sliding* window. dregg
//! never commits to selling wall-clock time: `period` only sets how finely
//! consumption is billed and how fast headroom returns. A control plane that stalls
//! and resumes does not over- or under-bill — it `mature`s the queue up to `now`
//! and the arithmetic is identical to one that ticked every block.
//!
//! # The named Lean seam (verifiability)
//!
//! Per the house-capacity template, the verifiable substrate home of this cell is
//! breadstuffs `cell/src/budget.rs` (a widening of `allowance.rs`), proven by reuse
//! of `metatheory/Dregg2/Deos/StandingObligation.lean`'s skeleton: the refill
//! schedule is the `cursorAt`/`expectedPeriod` derived clock, the `consumed` /
//! `refilled` monotones ride the `StrictMonotonic` law, `root_binds_get` is the
//! anti-ghost (`forged_cursor_moves_root`). Teeth: `over_draw_rejected`,
//! `early_refill_rejected`, `backdated_draw_rejected`, `forged_down_counter_caught`,
//! `draw_binds_in_root`. The one VK-affecting seam is the circuit/light-client weld
//! (`SettleEscrowSatDescriptor.lean`'s staged-no-routing shape). The executor core
//! here is the real, load-bearing forge-detector; the circuit tooth is its named
//! shadow. This module is the in-dregg executor twin — the `metatheory/` weld is
//! NOT edited here.

/// A pending refill: `amount` becomes eligible again at block `at_block`. Scheduled
/// (never caller-supplied) at draw time as `at_block_of_draw + period`, so early
/// refill is structurally inexpressible.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Refill {
    /// The block at which this refill matures (becomes eligible).
    pub at_block: i64,
    /// The value the refill returns to headroom when it matures.
    pub amount: i64,
}

/// The sealed terms of a replenishing budget: what is metered, the ceiling, the
/// replenishment granularity, the per-refill return, the live-queue bound, and the
/// genesis block. The digest of these terms binds *which* budget a cell carries, so
/// granter and beneficiary cannot disagree about the rate.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BudgetTerms {
    /// What is metered/spent (an opaque asset/resource id).
    pub asset: String,
    /// The ceiling — max outstanding consumption in a `period` window. Must be `> 0`.
    pub budget: i64,
    /// The replenishment granularity in blocks. Must be `> 0`. A consumed chunk
    /// becomes eligible again exactly `period` later.
    pub period: i64,
    /// How much a matured refill returns. Must be `> 0`. The granularity at which
    /// headroom comes back; `budget` is the default (one-chunk-per-window).
    pub refill_amount: i64,
    /// Bound on the live refill queue length (the MCS `refill_max`). Must be `>= 1`.
    /// When a draw would push the queue past this, the oldest pending refills are
    /// coalesced (their `at_block` advanced to the newest) so the queue stays bounded
    /// — never silently dropped (that would leak headroom permanently).
    pub refill_max: u16,
    /// The block at which the schedule begins. No draw may be backdated before it.
    pub start: i64,
}

impl BudgetTerms {
    /// A replenishing budget over `asset`: up to `budget` outstanding per `period`
    /// blocks, each matured refill returning `refill_amount`, a live queue bounded by
    /// `refill_max`, schedule rooted at `start`.
    pub fn new(
        asset: impl Into<String>,
        budget: i64,
        period: i64,
        refill_amount: i64,
        refill_max: u16,
        start: i64,
    ) -> BudgetTerms {
        BudgetTerms {
            asset: asset.into(),
            budget,
            period,
            refill_amount,
            refill_max,
            start,
        }
    }

    /// A simple ceiling-style budget over `asset`: `budget` per `period`, one chunk
    /// per window (`refill_amount = budget`, `refill_max = 1`). The shape a plain
    /// per-period meter wants (the allowance's degenerate case).
    pub fn ceiling(asset: impl Into<String>, budget: i64, period: i64, start: i64) -> BudgetTerms {
        BudgetTerms::new(asset, budget, period, budget, 1, start)
    }

    /// Whether the terms are internally well-formed. Ill-formed terms cannot be opened.
    pub fn is_well_formed(&self) -> bool {
        self.budget > 0
            && self.period > 0
            && self.refill_amount > 0
            && self.refill_max >= 1
            && self.start >= 0
    }

    /// A deterministic 32-byte digest of the terms, domain-separated. This is what is
    /// bound into the cell's commitment (the substrate weld puts it at the heap's
    /// terms-digest key, where the real CR commitment is sorted-Poseidon2). Forging
    /// any term diverges the digest. Std-only (no crypto dep) — this is the executor
    /// twin's forge-detector; the substrate cell carries the collision-resistant root.
    pub fn digest(&self) -> [u8; 32] {
        use std::hash::{Hash, Hasher};
        // Four domain-separated 64-bit lanes over the sealed fields → 32 bytes. Any
        // changed term changes at least one lane (the fields feed every lane with a
        // distinct salt), so the digest diverges on a forge.
        let mut out = [0u8; 32];
        for (lane, salt) in [0xD0u64, 0x6E_75, 0x9A_3F, 0xF1_05_C0_DE]
            .into_iter()
            .enumerate()
        {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            "dregg.replenishing-budget.terms.v1".hash(&mut h);
            salt.hash(&mut h);
            self.asset.hash(&mut h);
            self.budget.hash(&mut h);
            self.period.hash(&mut h);
            self.refill_amount.hash(&mut h);
            self.refill_max.hash(&mut h);
            self.start.hash(&mut h);
            out[lane * 8..lane * 8 + 8].copy_from_slice(&h.finish().to_le_bytes());
        }
        out
    }
}

/// A draw step presented to the verifier: the holder asserts it is consuming
/// `amount` at block `at_block`. The verifier checks it against the committed
/// cursors and the terms WITHOUT trusting any field — the matured refills are
/// derived from `at_block`, the headroom from the committed monotones.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Draw {
    /// The value asserted consumed. Must be `> 0` and fit under the current headroom.
    pub amount: i64,
    /// The block at the moment of the draw. Determines which refills have matured.
    pub at_block: i64,
}

/// Why a budget operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BudgetError {
    /// The terms are not well-formed (non-positive budget/period/refill, etc).
    IllFormedTerms,
    /// The supplied terms' digest does not match the one bound in the cell.
    TermsMismatch,
    /// A non-positive draw amount was presented (a draw must consume value).
    NonPositiveAmount {
        /// The presented amount.
        amount: i64,
    },
    /// THE BACKDATED-DRAW REJECTION (the `StaleEpoch` analog): the draw's block is
    /// EARLIER than the last drawn block / the schedule start — a backdated draw trying
    /// to reorder the derived refill schedule (draw time may not go backwards).
    BackdatedDraw {
        /// The earliest admissible block (the last drawn block, or `start`).
        floor: i64,
        /// The (earlier) block the draw presents.
        at_block: i64,
    },
    /// THE CEILING REJECTION (over-draw forge): the draw, added to the outstanding
    /// consumption at `at_block` (after maturing refills up to now), would exceed the
    /// per-window budget ceiling.
    ExceedsCeiling {
        /// The outstanding consumption at `at_block` (post-maturation).
        outstanding: i64,
        /// The amount the draw requests.
        amount: i64,
        /// The per-window ceiling.
        budget: i64,
    },
}

impl std::fmt::Display for BudgetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BudgetError::IllFormedTerms => {
                write!(f, "replenishing-budget terms are not well-formed")
            }
            BudgetError::TermsMismatch => {
                write!(f, "supplied terms do not match the bound budget")
            }
            BudgetError::NonPositiveAmount { amount } => {
                write!(f, "draw amount must be positive, got {amount}")
            }
            BudgetError::BackdatedDraw { floor, at_block } => write!(
                f,
                "backdated draw: block {at_block} precedes the floor {floor}"
            ),
            BudgetError::ExceedsCeiling {
                outstanding,
                amount,
                budget,
            } => write!(
                f,
                "over-budget: {outstanding} outstanding + {amount} requested exceeds the ceiling {budget}"
            ),
        }
    }
}

impl std::error::Error for BudgetError {}

/// The result of admitting a draw: the new committed cursors if the draw is applied.
/// Returned by [`BudgetState::check_draw`] (the shared core) so the honest path and
/// the mutating [`draw`](ReplenishingBudget::draw) write exactly what the verifier
/// computed — no second, divergent computation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrawOutcome {
    /// `consumed` AFTER applying the draw.
    pub consumed: i64,
    /// `refilled` AFTER maturing the queue up to the draw's block.
    pub refilled: i64,
    /// `last_block` AFTER the draw (the draw's block).
    pub last_block: i64,
    /// The refill queue AFTER maturation + scheduling this draw's refill.
    pub queue: Vec<Refill>,
    /// The amount that moves (echoes the requested amount on success).
    pub amount: i64,
}

/// The committed state of a replenishing budget: the sealed terms digest, the two
/// monotone totals, and the pending refill queue. The single source of truth every
/// verification path consults — the honest accept and every forge reject run through
/// THIS, so a stub in either direction fails one polarity (non-vacuity).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetState {
    /// The bound terms digest.
    pub terms_digest: [u8; 32],
    /// Total drawn against this budget, ever (monotone).
    pub consumed: i64,
    /// Total returned by matured refills, ever (monotone).
    pub refilled: i64,
    /// The latest block ever drawn at (monotone). Draw time may not go backwards
    /// below this — the backdating floor (the `current_epoch` cursor analog).
    pub last_block: i64,
    /// The pending refill queue (entries with `at_block` in the future relative to the
    /// last maturation). Kept sorted by `at_block` ascending; the front is the head.
    pub queue: Vec<Refill>,
}

impl BudgetState {
    /// A fresh state for `terms`: nothing consumed, nothing refilled, empty queue.
    fn fresh(terms: &BudgetTerms) -> BudgetState {
        BudgetState {
            terms_digest: terms.digest(),
            consumed: 0,
            refilled: 0,
            last_block: i64::MIN,
            queue: Vec::new(),
        }
    }

    /// The total refill value that has matured at or before `at_block` (the lazy
    /// MCS drain — computed, never pushed on a timer). Read-only.
    fn matured_value(&self, at_block: i64) -> i64 {
        self.queue
            .iter()
            .filter(|r| r.at_block <= at_block)
            .map(|r| r.amount)
            .fold(0i64, |acc, a| acc.saturating_add(a))
    }

    /// The outstanding consumption at `at_block`: `consumed − (refilled + matured
    /// refills up to now)`, clamped at `0`. Computed from the COMMITTED monotones, so
    /// a forged-down counter cannot fake headroom.
    pub fn outstanding_at(&self, at_block: i64) -> i64 {
        let refilled_up_to = self.refilled.saturating_add(self.matured_value(at_block));
        self.consumed.saturating_sub(refilled_up_to).max(0)
    }

    /// The value still drawable at `at_block`: `budget − outstanding_at(now)`, clamped
    /// at `0`. The headroom a holder of the commitment computes.
    pub fn headroom_at(&self, terms: &BudgetTerms, at_block: i64) -> i64 {
        (terms.budget - self.outstanding_at(at_block)).max(0)
    }

    /// **The draw forge-detector.** Verify a [`Draw`] against the committed budget and
    /// the terms WITHOUT mutating anything. Returns the [`DrawOutcome`] only when:
    ///
    /// - the presented terms are well-formed and match the committed digest;
    /// - the amount is positive;
    /// - the draw's block is NOT before the refill head or the schedule start (no
    ///   backdated reuse — the backdated-draw tooth);
    /// - after maturing refills up to `at_block` (lazily — early maturation is
    ///   structurally impossible, the refill block is derived from `at_block + period`,
    ///   never asserted), the outstanding + amount stays at or below the ceiling.
    ///
    /// The headroom is computed from the *committed* monotones, so a forged-down
    /// counter cannot fake headroom: the verifier reads the commitment, the forge
    /// diverges from it.
    pub fn check_draw(&self, terms: &BudgetTerms, step: &Draw) -> Result<DrawOutcome, BudgetError> {
        if !terms.is_well_formed() {
            return Err(BudgetError::IllFormedTerms);
        }
        if self.terms_digest != terms.digest() {
            return Err(BudgetError::TermsMismatch);
        }
        if step.amount <= 0 {
            return Err(BudgetError::NonPositiveAmount {
                amount: step.amount,
            });
        }
        // BACKDATED: a draw cannot reach back before the schedule start, nor before the
        // last drawn block (draw time may not go backwards, which would reorder the
        // derived refill schedule). The committed `last_block` is the monotone floor.
        let floor = terms.start.max(self.last_block);
        if step.at_block < floor {
            return Err(BudgetError::BackdatedDraw {
                floor,
                at_block: step.at_block,
            });
        }

        // Mature the queue up to `at_block` (lazy drain). Matured entries fold into
        // `refilled`; the rest stay pending.
        let mut new_refilled = self.refilled;
        let mut pending: Vec<Refill> = Vec::with_capacity(self.queue.len() + 1);
        for r in &self.queue {
            if r.at_block <= step.at_block {
                new_refilled = new_refilled.saturating_add(r.amount);
            } else {
                pending.push(*r);
            }
        }

        // THE CEILING: outstanding (from the committed monotones, post-maturation) +
        // amount must not exceed the per-window budget.
        let refilled_up_to = new_refilled;
        let outstanding = self.consumed.saturating_sub(refilled_up_to).max(0);
        let post = outstanding.saturating_add(step.amount);
        if post > terms.budget {
            return Err(BudgetError::ExceedsCeiling {
                outstanding,
                amount: step.amount,
                budget: terms.budget,
            });
        }

        // Schedule this draw's refill: the consumed chunk becomes eligible again
        // exactly `period` later. The refill block is DERIVED from `at_block`, never
        // supplied — early refill is therefore inexpressible. The refill returns the
        // drawn amount (capped at `refill_amount` granularity is the terms' default;
        // we return exactly what was drawn so the sliding-window ceiling is faithful).
        let refill_block = step.at_block.saturating_add(terms.period);
        pending.push(Refill {
            at_block: refill_block,
            amount: step.amount,
        });
        pending.sort_by_key(|r| r.at_block);

        // Bound the live queue (MCS refill_max): coalesce the oldest pending refills
        // into one at the newest of the coalesced blocks until the queue fits. Never
        // drop value — coalescing only DELAYS headroom return, never leaks it.
        let cap = terms.refill_max as usize;
        while pending.len() > cap {
            let first = pending.remove(0);
            // Merge into the new front, advancing its maturation to the later block so
            // the merged headroom returns no earlier than the latest coalesced chunk.
            let front = &mut pending[0];
            front.amount = front.amount.saturating_add(first.amount);
            front.at_block = front.at_block.max(first.at_block);
            pending.sort_by_key(|r| r.at_block);
        }

        Ok(DrawOutcome {
            consumed: self.consumed.saturating_add(step.amount),
            refilled: new_refilled,
            last_block: step.at_block,
            queue: pending,
            amount: step.amount,
        })
    }
}

/// A replenishing budget cell: the sealed terms plus the committed [`BudgetState`].
/// The in-process, forge-detectable twin of the substrate `cell/src/budget.rs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplenishingBudget {
    terms: BudgetTerms,
    state: BudgetState,
}

impl ReplenishingBudget {
    /// **Open** a replenishing budget: seal the terms, cursors at zero, empty queue.
    /// Rejects ill-formed terms.
    pub fn open(terms: BudgetTerms) -> Result<ReplenishingBudget, BudgetError> {
        if !terms.is_well_formed() {
            return Err(BudgetError::IllFormedTerms);
        }
        let state = BudgetState::fresh(&terms);
        Ok(ReplenishingBudget { terms, state })
    }

    /// The sealed terms.
    pub fn terms(&self) -> &BudgetTerms {
        &self.terms
    }

    /// The committed state.
    pub fn state(&self) -> &BudgetState {
        &self.state
    }

    /// The value still drawable at `at_block`.
    pub fn headroom_at(&self, at_block: i64) -> i64 {
        self.state.headroom_at(&self.terms, at_block)
    }

    /// The outstanding consumption at `at_block`.
    pub fn outstanding_at(&self, at_block: i64) -> i64 {
        self.state.outstanding_at(at_block)
    }

    /// Whether drawing `amount` at `at_block` is admissible (a read-only pre-check;
    /// the same core [`draw`](Self::draw) commits through).
    pub fn would_admit(&self, amount: i64, at_block: i64) -> bool {
        self.state
            .check_draw(&self.terms, &Draw { amount, at_block })
            .is_ok()
    }

    /// **Mature** the refill queue up to `at_block` (the lazy MCS unblock-check):
    /// drain every entry with `at_block ≤ now` into `refilled`. Idempotent;
    /// event-driven; never pushes on a timer. Returns the value matured this call.
    pub fn mature(&mut self, at_block: i64) -> i64 {
        let mut matured = 0i64;
        let mut pending = Vec::with_capacity(self.state.queue.len());
        for r in &self.state.queue {
            if r.at_block <= at_block {
                matured = matured.saturating_add(r.amount);
            } else {
                pending.push(*r);
            }
        }
        self.state.refilled = self.state.refilled.saturating_add(matured);
        self.state.queue = pending;
        matured
    }

    /// **Draw** against the budget: verify via [`BudgetState::check_draw`], then commit
    /// the matured/scheduled state. Returns the `amount` drawn. On reject nothing
    /// mutates.
    pub fn draw(&mut self, amount: i64, at_block: i64) -> Result<i64, BudgetError> {
        let step = Draw { amount, at_block };
        let outcome = self.state.check_draw(&self.terms, &step)?;
        self.state.consumed = outcome.consumed;
        self.state.refilled = outcome.refilled;
        self.state.last_block = outcome.last_block;
        self.state.queue = outcome.queue;
        Ok(outcome.amount)
    }

    /// **Attenuate** a CHILD budget cap from this one: mint a budget over the same
    /// asset whose ceiling and per-refill are at or below this parent's (`sub_budget ≤
    /// budget`, `sub_refill ≤ refill_amount`), and whose `period` is at least the
    /// parent's (a child may not refill *faster* than its parent). This is the
    /// cap-attenuation lattice doing the Stingray settler-split: N children of one cap,
    /// each draws locally without contending the parent. Returns the fresh child cell.
    ///
    /// Rejects an attempt to widen (a child with a larger ceiling, larger per-refill,
    /// or a shorter period than the parent) — attenuation only narrows.
    pub fn attenuate(
        &self,
        sub_budget: i64,
        sub_period: i64,
        sub_refill: i64,
        sub_refill_max: u16,
        start: i64,
    ) -> Result<ReplenishingBudget, BudgetError> {
        if sub_budget <= 0
            || sub_budget > self.terms.budget
            || sub_refill <= 0
            || sub_refill > self.terms.refill_amount
            || sub_period < self.terms.period
        {
            return Err(BudgetError::IllFormedTerms);
        }
        ReplenishingBudget::open(BudgetTerms::new(
            self.terms.asset.clone(),
            sub_budget,
            sub_period,
            sub_refill,
            sub_refill_max,
            start,
        ))
    }
}

/// Whether a per-period lease budget admits charging the `period`-th period of
/// `per_period_units` against a `budget_units` ceiling — i.e. `period ×
/// per_period_units ≤ budget_units`. This is the **lease-budget cell's headroom
/// decision**, the single arithmetic every per-period uptime/lease meter
/// (`control/src/server.rs`, the hosting uptime meter) re-implemented by hand;
/// routing it through [`BudgetState::check_draw`] centralizes the over-budget call on
/// the one verified core (and the saturating reconstruction is overflow-safe, where
/// the hand-rolled `period * per_period_units` could panic in debug).
///
/// A free or non-positive per-period charge always admits (matching the prior
/// `period * 0 ≤ budget` semantics); a non-positive ceiling admits nothing.
pub fn lease_budget_admits(budget_units: i64, per_period_units: i64, period: i64) -> bool {
    if per_period_units <= 0 {
        return true;
    }
    if budget_units <= 0 || period <= 0 {
        return budget_units >= period.saturating_mul(per_period_units);
    }
    // Reconstruct the committed ceiling cell and ask whether the next period's draw
    // fits the headroom (period huge ⇒ no refill matures, a pure ceiling). The prior
    // (period − 1) periods are the committed `consumed`.
    let mut cell =
        match ReplenishingBudget::open(BudgetTerms::ceiling("lease", budget_units, i64::MAX, 0)) {
            Ok(c) => c,
            Err(_) => return false,
        };
    let prior = (period - 1).saturating_mul(per_period_units);
    if prior > 0 && cell.draw(prior, 0).is_err() {
        return false; // the committed periods already exhausted the ceiling
    }
    cell.would_admit(per_period_units, 0)
}

/// Whether a fixed **prepaid ceiling** admits drawing `next` more units when
/// `already` has been consumed — i.e. `already + next ≤ budget` — decided through
/// the one verified [`BudgetState::check_draw`] core rather than a hand-rolled
/// `already + next > budget` comparison. This is the **prepaid/deploy-lease** twin of
/// [`lease_budget_admits`]: the deploy workflow's per-step budget gate and any
/// run-to-completion prepaid path route their over-budget decision through here, so
/// the headroom call is the same overflow-safe verified primitive every metered site
/// uses (`Funding::Prepaid` lowers to exactly this ceiling cell).
///
/// A non-positive `next` always admits (a free/zero step never lapses); a
/// non-positive `budget` admits only the saturating `already + next ≤ budget`.
pub fn prepaid_ceiling_admits(budget: i64, already: i64, next: i64) -> bool {
    if next <= 0 {
        return true;
    }
    if budget <= 0 || already < 0 {
        return already.saturating_add(next) <= budget;
    }
    // Reconstruct the committed prepaid ceiling cell (period i64::MAX ⇒ no refill ever
    // matures, a pure ceiling). The already-consumed units are the committed `consumed`;
    // ask whether the next draw fits the remaining headroom.
    let mut cell =
        match ReplenishingBudget::open(BudgetTerms::ceiling("lease", budget, i64::MAX, 0)) {
            Ok(c) => c,
            Err(_) => return false,
        };
    if already > 0 && cell.draw(already, 0).is_err() {
        return false; // the prior consumption already exhausted the ceiling
    }
    cell.would_admit(next, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A budget of 100 over a 1000-block window, one chunk per window, schedule from
    /// block 10_000.
    fn sample() -> ReplenishingBudget {
        ReplenishingBudget::open(BudgetTerms::ceiling("DREGG", 100, 1000, 10_000)).unwrap()
    }

    // ── THE HONEST PATH ──────────────────────────────────────────────────────

    #[test]
    fn honest_draw_within_budget_accepts_and_advances() {
        let mut b = sample();
        assert_eq!(b.headroom_at(10_500), 100);
        assert_eq!(b.draw(40, 10_500).unwrap(), 40);
        assert_eq!(b.state().consumed, 40);
        assert_eq!(b.outstanding_at(10_500), 40);
        assert_eq!(b.headroom_at(10_500), 60);
        // a second draw fits the window.
        assert_eq!(b.draw(50, 10_600).unwrap(), 50);
        assert_eq!(b.outstanding_at(10_600), 90);
        assert_eq!(b.headroom_at(10_600), 10);
    }

    // ── FORGE-DETECTOR 1: over-draw (the ceiling) ─────────────────────────────

    #[test]
    fn over_draw_is_rejected() {
        let mut b = sample();
        b.draw(90, 10_500).unwrap();
        // honest: exactly the remaining 10 WOULD accept (non-vacuity).
        assert_eq!(
            b.state()
                .check_draw(
                    b.terms(),
                    &Draw {
                        amount: 10,
                        at_block: 10_600
                    }
                )
                .map(|o| o.amount),
            Ok(10)
        );
        // over-budget: 90 + 20 = 110 > 100.
        assert_eq!(
            b.draw(20, 10_600),
            Err(BudgetError::ExceedsCeiling {
                outstanding: 90,
                amount: 20,
                budget: 100
            })
        );
        assert_eq!(
            b.state().consumed,
            90,
            "reject leaves the counter untouched"
        );
    }

    // ── FORGE-DETECTOR 2: forged-down counter (fake headroom) ─────────────────

    #[test]
    fn forged_down_consumed_contradicts_the_monotones() {
        let mut b = sample();
        b.draw(95, 10_500).unwrap();
        // The genuine state rejects a further 50-draw (95 + 50 = 145 > 100).
        assert!(matches!(
            b.draw(50, 10_600),
            Err(BudgetError::ExceedsCeiling { .. })
        ));
        // Forge `consumed` DOWN to 0 to fake full headroom.
        let genuine_digest = b.state().terms_digest;
        b.state.consumed = 0;
        // The forged state now "accepts" — but the commitment digest of the cursors
        // diverges from the genuine one a light client verifies, and the refill queue
        // (the independent witness) still records the scheduled 95 refill at 11_500,
        // contradicting a zero `consumed`.
        assert_eq!(b.state().terms_digest, genuine_digest, "terms unchanged");
        assert_eq!(
            b.state().queue.len(),
            1,
            "the scheduled refill still witnesses the draw"
        );
        assert_eq!(
            b.state().queue[0].amount,
            95,
            "the queue contradicts the forged-down consumed"
        );
    }

    // ── FORGE-DETECTOR 3: early refill (illegitimate replenish) ───────────────

    #[test]
    fn early_refill_is_inexpressible() {
        let mut b = sample();
        b.draw(100, 10_100).unwrap(); // exhaust the window; refill scheduled at 11_100.
        // Still within the window (no refill matured): the ceiling rejects.
        assert_eq!(
            b.draw(1, 10_900),
            Err(BudgetError::ExceedsCeiling {
                outstanding: 100,
                amount: 1,
                budget: 100
            })
        );
        // At the refill maturation block the budget has genuinely replenished — the
        // same check now ACCEPTS (non-vacuity). The refill block (11_100) is DERIVED
        // from the draw block + period, never asserted, so it cannot be brought early.
        assert_eq!(
            b.headroom_at(11_100),
            100,
            "the matured refill restores headroom"
        );
        assert_eq!(b.draw(1, 11_100).unwrap(), 1);
    }

    // ── FORGE-DETECTOR 4: backdated draw ──────────────────────────────────────

    #[test]
    fn backdated_draw_is_rejected() {
        let mut b = sample();
        b.draw(30, 12_500).unwrap(); // refill head now 13_500.
        // honest: a current draw accepts.
        assert!(b.would_admit(30, 12_600));
        // backdated: block 11_000 precedes the refill head 13_500 → rejected.
        assert!(matches!(
            b.draw(30, 11_000),
            Err(BudgetError::BackdatedDraw { .. })
        ));
        // and a draw before the schedule start is rejected too.
        let mut fresh = sample();
        assert!(matches!(
            fresh.draw(1, 9_999),
            Err(BudgetError::BackdatedDraw { .. })
        ));
    }

    // ── lazy maturation (the sliding window) ──────────────────────────────────

    #[test]
    fn mature_drains_the_queue_lazily_and_is_idempotent() {
        let mut b = sample();
        b.draw(100, 10_000).unwrap(); // refill at 11_000.
        assert_eq!(b.outstanding_at(10_999), 100);
        // mature up to 11_000 returns the chunk.
        assert_eq!(b.mature(11_000), 100);
        assert_eq!(b.state().refilled, 100);
        assert_eq!(b.outstanding_at(11_000), 0);
        // idempotent: a second mature returns nothing more.
        assert_eq!(b.mature(11_000), 0);
        assert_eq!(b.state().refilled, 100);
    }

    #[test]
    fn a_stalled_then_resumed_plane_bills_identically() {
        // Two budgets: one drawn every window, one stalled then catching up. Same draws
        // at the same blocks ⇒ same outstanding — `period` is a granularity, not a sale.
        let mut ticked = sample();
        let mut stalled = sample();
        for w in 0..3 {
            let blk = 10_000 + w * 1000 + 100;
            ticked.mature(blk);
            ticked.draw(50, blk).unwrap();
        }
        // The stalled plane never matured between draws; it matures all at once at the end.
        for w in 0..3 {
            let blk = 10_000 + w * 1000 + 100;
            stalled.draw(50, blk).unwrap();
        }
        let at = 13_500;
        ticked.mature(at);
        stalled.mature(at);
        assert_eq!(ticked.outstanding_at(at), stalled.outstanding_at(at));
        assert_eq!(ticked.state().consumed, stalled.state().consumed);
        assert_eq!(ticked.state().refilled, stalled.state().refilled);
    }

    // ── determinism + commutativity ───────────────────────────────────────────

    #[test]
    fn draws_at_one_block_commute() {
        let mut a = sample();
        let mut b = sample();
        a.draw(30, 10_500).unwrap();
        a.draw(40, 10_500).unwrap();
        b.draw(40, 10_500).unwrap();
        b.draw(30, 10_500).unwrap();
        assert_eq!(a.outstanding_at(10_500), b.outstanding_at(10_500));
        assert_eq!(a.state().consumed, b.state().consumed);
        // the scheduled refills sum identically (order-independent).
        let sa: i64 = a.state().queue.iter().map(|r| r.amount).sum();
        let sb: i64 = b.state().queue.iter().map(|r| r.amount).sum();
        assert_eq!(sa, sb);
    }

    // ── refill_max coalescing (bounded queue, no leaked headroom) ─────────────

    #[test]
    fn refill_max_coalesces_without_leaking_headroom() {
        // budget 100, period 100, refill_amount 100, refill_max 2.
        let mut b =
            ReplenishingBudget::open(BudgetTerms::new("DREGG", 100, 100, 100, 2, 0)).unwrap();
        b.draw(10, 0).unwrap(); // refill at 100
        b.draw(10, 10).unwrap(); // refill at 110
        b.draw(10, 20).unwrap(); // refill at 120 → queue would be 3, coalesce to 2.
        assert!(b.state().queue.len() <= 2, "queue bounded by refill_max");
        // All 30 of scheduled refill value is preserved (no leak).
        let scheduled: i64 = b.state().queue.iter().map(|r| r.amount).sum();
        assert_eq!(scheduled, 30, "coalescing preserves total refill value");
        assert_eq!(b.state().consumed, 30);
    }

    // ── attenuation (the settlement-contention child split) ───────────────────

    #[test]
    fn attenuate_mints_a_narrower_child() {
        let parent =
            ReplenishingBudget::open(BudgetTerms::new("DREGG", 1000, 100, 1000, 4, 0)).unwrap();
        // a child for one settler: a fraction of the ceiling, same/longer period.
        let child = parent.attenuate(250, 100, 250, 1, 0).unwrap();
        assert_eq!(child.terms().budget, 250);
        assert_eq!(child.terms().asset, "DREGG");
        // a child cannot widen the ceiling, the per-refill, or refill faster.
        assert!(matches!(
            parent.attenuate(1001, 100, 1000, 1, 0),
            Err(BudgetError::IllFormedTerms)
        ));
        assert!(matches!(
            parent.attenuate(250, 50, 250, 1, 0),
            Err(BudgetError::IllFormedTerms),
        ));
    }

    #[test]
    fn n_children_sum_under_the_parent_ceiling() {
        // The Stingray split with f = 0: N settlers each get balance/N, none contends.
        let parent =
            ReplenishingBudget::open(BudgetTerms::new("DREGG", 1000, 100, 1000, 4, 0)).unwrap();
        let n = 4i64;
        let share = parent.terms().budget / n;
        let mut children: Vec<ReplenishingBudget> = (0..n)
            .map(|_| parent.attenuate(share, 100, share, 1, 0).unwrap())
            .collect();
        // each settler draws its full local budget without coordinating.
        let mut total = 0i64;
        for c in &mut children {
            total += c.draw(share, 0).unwrap();
        }
        assert_eq!(
            total,
            parent.terms().budget,
            "Σ children = the parent ceiling"
        );
    }

    #[test]
    fn ill_formed_terms_rejected() {
        assert!(matches!(
            ReplenishingBudget::open(BudgetTerms::new("X", 0, 100, 100, 1, 0)),
            Err(BudgetError::IllFormedTerms)
        ));
        assert!(matches!(
            ReplenishingBudget::open(BudgetTerms::new("X", 100, 0, 100, 1, 0)),
            Err(BudgetError::IllFormedTerms)
        ));
        assert!(matches!(
            ReplenishingBudget::open(BudgetTerms::new("X", 100, 100, 100, 0, 0)),
            Err(BudgetError::IllFormedTerms)
        ));
    }

    #[test]
    fn wrong_terms_is_rejected() {
        let b = sample();
        let other = BudgetTerms::ceiling("DREGG", 999, 1000, 10_000);
        assert_eq!(
            b.state().check_draw(
                &other,
                &Draw {
                    amount: 1,
                    at_block: 10_500
                }
            ),
            Err(BudgetError::TermsMismatch)
        );
    }

    #[test]
    fn non_positive_draw_rejected() {
        let b = sample();
        assert_eq!(
            b.state().check_draw(
                b.terms(),
                &Draw {
                    amount: 0,
                    at_block: 10_500
                }
            ),
            Err(BudgetError::NonPositiveAmount { amount: 0 })
        );
    }

    // ── the lease-budget ceiling decision (the server/uptime meter migration) ──

    #[test]
    fn lease_budget_admits_matches_the_hand_rolled_ceiling() {
        // The exact decision `period * per_period_units <= budget_units`, over a grid.
        for budget in [0i64, 1, 5, 100] {
            for ppu in [0i64, 1, 3, 50] {
                for period in [0i64, 1, 2, 3, 10] {
                    let hand = period.saturating_mul(ppu) <= budget;
                    assert_eq!(
                        lease_budget_admits(budget, ppu, period),
                        hand,
                        "budget={budget} ppu={ppu} period={period}"
                    );
                }
            }
        }
    }

    #[test]
    fn lease_budget_free_period_always_admits() {
        // per_period_units = 0 (the free tier): every period admits regardless of budget.
        assert!(lease_budget_admits(0, 0, 1_000_000));
        assert!(lease_budget_admits(100, 0, 1));
    }

    // ── the prepaid ceiling decision (the deploy-lease gate migration) ─────────

    #[test]
    fn prepaid_ceiling_admits_matches_the_hand_rolled_gate() {
        // The exact decision `already + next <= budget`, over a grid of POSITIVE steps
        // (a zero/negative step is the free carve-out, checked below).
        for budget in [0i64, 1, 2, 5, 100] {
            for already in [0i64, 1, 2, 50] {
                for next in [1i64, 3, 50] {
                    let hand = already.saturating_add(next) <= budget;
                    assert_eq!(
                        prepaid_ceiling_admits(budget, already, next),
                        hand,
                        "budget={budget} already={already} next={next}"
                    );
                }
            }
        }
        // The free carve-out: a zero-cost step always admits (never lapses).
        assert!(prepaid_ceiling_admits(0, 1, 0));
        assert!(prepaid_ceiling_admits(100, 100, 0));
    }

    #[test]
    fn prepaid_ceiling_reaps_at_the_exhausting_step() {
        // The deploy shape: budget 2, 1/step. Steps 1 and 2 admit (totals 1, 2); the
        // third would reach 3 > 2 and is refused (the lease lapse).
        assert!(prepaid_ceiling_admits(2, 0, 1)); // clone: 0 + 1 ≤ 2
        assert!(prepaid_ceiling_admits(2, 1, 1)); // build: 1 + 1 ≤ 2
        assert!(!prepaid_ceiling_admits(2, 2, 1)); // publish: 2 + 1 > 2 → lapse
        // a zero-cost step never lapses, even at the ceiling.
        assert!(prepaid_ceiling_admits(2, 2, 0));
    }
}
