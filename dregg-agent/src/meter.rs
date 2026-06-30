//! `meter` — the unified **`Meter`** trait.
//!
//! `Settlement` is the clean *sink* seam: where a metered period becomes a
//! conserving value flow. `Meter` is its *source* twin: a uniform metering interface
//! backed by the [`ReplenishingBudget`](crate::budget::ReplenishingBudget) cell. The
//! control plane re-implemented metering 5–6× (the `exec` host-API call meter, the
//! `control` uptime meter, the `control` hosting meter, the `webapp` bandwidth
//! meter, the `durable` settle side); each hand-rolled its own period / dedup /
//! over-budget / lapse logic. `Meter` collapses that to ONE interface over ONE
//! verified primitive:
//!
//! - a [`draw`](Meter::draw) charges *actual* consumption against the headroom the
//!   budget has matured up to `now`;
//! - over-budget fails **closed**, in-band — the [`MeterError::OverBudget`] every
//!   caller surfaces as a `402` *before* the work commits (the HB-1 / SRV / host-API
//!   shape);
//! - a draw is **exactly-once** per `(key, period)` — a replay (a crash
//!   re-dispatch, a sweep retried) returns the recorded receipt and moves nothing,
//!   exactly as `Settlement` is exactly-once per `(lease, period)`;
//! - `period` is a **billing-granularity knob**, not wall-clock-sold time (the
//!   replenishing-budget reframing): a stalled-then-resumed plane bills identically.
//!
//! The agent-budget tie-in (the Verifiable Agent Cloud): an autonomous agent's
//! `invoke` / cell budget IS a replenishing-budget cell drawn through this trait —
//! `agent_budget` below is the worked shape, so a runaway agent's spend rate is
//! bounded by the same primitive that bounds a lease's compute.

use std::collections::HashMap;
use std::sync::Mutex;

use crate::budget::{BudgetError, BudgetTerms, ReplenishingBudget};

/// The idempotency key of a draw: which metered subject (a lease, a site, a service)
/// and which period ordinal within it. The `(key, period)` pair is the exactly-once
/// nullifier — re-drawing it moves nothing (the `Settlement` `(lease, period)` twin).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MeterKey {
    /// The metered subject (e.g. `host:bandwidth:blog`, a `server_id`, an agent id).
    pub subject: String,
    /// The period ordinal within the subject (a publish seq, an uptime period, a
    /// bandwidth roll-up counter). Half of the exactly-once key.
    pub period: i64,
}

impl MeterKey {
    /// A key for `subject` at `period`.
    pub fn new(subject: impl Into<String>, period: i64) -> MeterKey {
        MeterKey {
            subject: subject.into(),
            period,
        }
    }
}

/// The receipt of one admitted draw — what the budget cursors became.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MeterReceipt {
    /// The subject drawn against.
    pub subject: String,
    /// The period ordinal (the exactly-once half).
    pub period: i64,
    /// The units drawn.
    pub units: i64,
    /// The subject's outstanding consumption after the draw (at the draw's block).
    pub outstanding: i64,
    /// The subject's remaining headroom after the draw (at the draw's block).
    pub headroom: i64,
    /// `true` if `(subject, period)` was already drawn and no units moved this call.
    pub replayed: bool,
}

/// Why a draw was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MeterError {
    /// THE IN-BAND `402`: the draw would exceed the subject's matured headroom. The
    /// caller refuses the operation *before* it commits (a publish/cert/build aborts;
    /// a served request is refused `402`; a lapsing site stops serving).
    OverBudget {
        /// The metered subject.
        subject: String,
        /// The units the draw requested.
        units: i64,
        /// The headroom available at the draw's block.
        headroom: i64,
    },
    /// The same `(subject, period)` was already drawn with *different* units — a
    /// programming error (the idempotency key must identify a unique draw).
    Conflict {
        /// The subject.
        subject: String,
        /// The period.
        period: i64,
    },
    /// No budget is open for this subject (it was never [`open`](Meter::open)ed).
    NoBudget {
        /// The subject.
        subject: String,
    },
    /// The underlying budget refused for a structural reason (ill-formed terms, a
    /// backdated block, a non-positive amount).
    Budget(BudgetError),
}

impl std::fmt::Display for MeterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MeterError::OverBudget {
                subject,
                units,
                headroom,
            } => write!(
                f,
                "over-budget: drawing {units} for `{subject}` exceeds the {headroom} headroom (402)"
            ),
            MeterError::Conflict { subject, period } => write!(
                f,
                "period {period} of `{subject}` already drawn with different units"
            ),
            MeterError::NoBudget { subject } => {
                write!(f, "no replenishing budget open for `{subject}`")
            }
            MeterError::Budget(e) => write!(f, "budget refused: {e}"),
        }
    }
}

impl std::error::Error for MeterError {}

/// The metering source — where actual consumption is charged against a replenishing
/// budget, fail-closed over the matured headroom.
///
/// This is the single seam the control plane drives, the source twin of
/// A conserving settlement ledger. An implementation MUST be:
/// - **fail-closed** — an over-budget draw is refused [`MeterError::OverBudget`]
///   (the in-band `402`) *before* any commit, never after a partial effect;
/// - **exactly-once** — drawing the same `(subject, period)` twice charges only once
///   (the second call returns the recorded receipt with `replayed`).
pub trait Meter: Send + Sync {
    /// Open a replenishing budget for `terms.asset`-denominated `subject`. Re-opening
    /// an existing subject is a no-op (the budget is sealed once).
    fn open(&self, subject: &str, terms: BudgetTerms) -> Result<(), MeterError>;

    /// Draw `units` of actual consumption against `key.subject`'s budget, matured to
    /// `at_block`, keyed exactly-once by `key`. Fail-closed over the headroom.
    fn draw(&self, key: &MeterKey, units: i64, at_block: i64) -> Result<MeterReceipt, MeterError>;

    /// The headroom `subject` has at `at_block` (the in-band serving gate reads this:
    /// `headroom >= request_cost` ⇒ admit). `0` for an unknown subject (fail-closed).
    fn headroom(&self, subject: &str, at_block: i64) -> i64;

    /// The total units drawn against `subject` across all its periods.
    fn drawn_total(&self, subject: &str) -> i64;
}

/// A [`Meter`] over per-subject [`ReplenishingBudget`] cells, with an exactly-once
/// `(subject, period)` dedup record — the faithful in-process realization of the
/// metering source.
#[derive(Default)]
pub struct ReplenishingMeter {
    /// subject → its replenishing budget cell.
    budgets: Mutex<HashMap<String, ReplenishingBudget>>,
    /// `(subject, period) → the receipt drawn for it` — the idempotency record.
    drawn: Mutex<HashMap<(String, i64), MeterReceipt>>,
}

impl ReplenishingMeter {
    /// A fresh meter with no budgets open.
    pub fn new() -> ReplenishingMeter {
        ReplenishingMeter::default()
    }

    /// Read a snapshot of `subject`'s budget cell (for inspection / attenuation).
    pub fn budget_of(&self, subject: &str) -> Option<ReplenishingBudget> {
        self.budgets
            .lock()
            .expect("meter poisoned")
            .get(subject)
            .cloned()
    }

    /// **Attenuate** a child budget off `parent`'s cell and open it under `child` — the
    /// settlement-contention split (Use B): N settlers each hold a locally-drawn child
    /// of one hot-account budget, so they never serialize on the parent. Returns the
    /// child's terms.
    pub fn attenuate_child(
        &self,
        parent: &str,
        child: &str,
        sub_budget: i64,
        sub_period: i64,
        sub_refill: i64,
        sub_refill_max: u16,
        start: i64,
    ) -> Result<BudgetTerms, MeterError> {
        let child_cell = {
            let budgets = self.budgets.lock().expect("meter poisoned");
            let p = budgets.get(parent).ok_or_else(|| MeterError::NoBudget {
                subject: parent.to_string(),
            })?;
            p.attenuate(sub_budget, sub_period, sub_refill, sub_refill_max, start)
                .map_err(MeterError::Budget)?
        };
        let terms = child_cell.terms().clone();
        self.budgets
            .lock()
            .expect("meter poisoned")
            .entry(child.to_string())
            .or_insert(child_cell);
        Ok(terms)
    }
}

impl Meter for ReplenishingMeter {
    fn open(&self, subject: &str, terms: BudgetTerms) -> Result<(), MeterError> {
        let cell = ReplenishingBudget::open(terms).map_err(MeterError::Budget)?;
        self.budgets
            .lock()
            .expect("meter poisoned")
            .entry(subject.to_string())
            .or_insert(cell);
        Ok(())
    }

    fn draw(&self, key: &MeterKey, units: i64, at_block: i64) -> Result<MeterReceipt, MeterError> {
        // Exactly-once + the draw are ONE critical section (lock ordering `drawn` →
        // `budgets`, the only path taking both), so two concurrent draws of the same
        // `(subject, period)` cannot both pass the not-yet-drawn check and both consume.
        let dedup_key = (key.subject.clone(), key.period);
        let mut drawn = self.drawn.lock().expect("meter poisoned");
        if let Some(prior) = drawn.get(&dedup_key) {
            if prior.units != units {
                return Err(MeterError::Conflict {
                    subject: key.subject.clone(),
                    period: key.period,
                });
            }
            let mut replay = prior.clone();
            replay.replayed = true;
            return Ok(replay);
        }

        let mut budgets = self.budgets.lock().expect("meter poisoned");
        let cell = budgets
            .get_mut(&key.subject)
            .ok_or_else(|| MeterError::NoBudget {
                subject: key.subject.clone(),
            })?;
        // Mature lazily up to now, then draw fail-closed over the headroom.
        cell.mature(at_block);
        match cell.draw(units, at_block) {
            Ok(amount) => {
                let receipt = MeterReceipt {
                    subject: key.subject.clone(),
                    period: key.period,
                    units: amount,
                    outstanding: cell.outstanding_at(at_block),
                    headroom: cell.headroom_at(at_block),
                    replayed: false,
                };
                drawn.insert(dedup_key, receipt.clone());
                Ok(receipt)
            }
            Err(BudgetError::ExceedsCeiling {
                budget,
                outstanding,
                ..
            }) => Err(MeterError::OverBudget {
                subject: key.subject.clone(),
                units,
                headroom: (budget - outstanding).max(0),
            }),
            Err(e) => Err(MeterError::Budget(e)),
        }
    }

    fn headroom(&self, subject: &str, at_block: i64) -> i64 {
        self.budgets
            .lock()
            .expect("meter poisoned")
            .get(subject)
            .map(|c| c.headroom_at(at_block))
            .unwrap_or(0)
    }

    fn drawn_total(&self, subject: &str) -> i64 {
        self.drawn
            .lock()
            .expect("meter poisoned")
            .iter()
            .filter(|((s, _), _)| s == subject)
            .map(|(_, r)| r.units)
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn meter_with(subject: &str, budget: i64, period: i64) -> ReplenishingMeter {
        let m = ReplenishingMeter::new();
        m.open(subject, BudgetTerms::ceiling("DREGG", budget, period, 0))
            .unwrap();
        m
    }

    #[test]
    fn honest_draw_charges_actual_consumption() {
        let m = meter_with("lease-1", 100, 1000);
        let r = m.draw(&MeterKey::new("lease-1", 1), 40, 500).unwrap();
        assert!(!r.replayed);
        assert_eq!(r.units, 40);
        assert_eq!(r.outstanding, 40);
        assert_eq!(r.headroom, 60);
        assert_eq!(m.drawn_total("lease-1"), 40);
    }

    #[test]
    fn draw_is_exactly_once_per_key_period() {
        let m = meter_with("lease-1", 100, 1000);
        let first = m.draw(&MeterKey::new("lease-1", 1), 10, 100).unwrap();
        assert!(!first.replayed);
        // re-drawing the SAME (subject, period) moves nothing and reports the replay.
        let again = m.draw(&MeterKey::new("lease-1", 1), 10, 100).unwrap();
        assert!(again.replayed);
        assert_eq!(m.drawn_total("lease-1"), 10, "only one draw landed");
        // a different period accumulates.
        m.draw(&MeterKey::new("lease-1", 2), 5, 200).unwrap();
        assert_eq!(m.drawn_total("lease-1"), 15);
    }

    #[test]
    fn over_budget_is_refused_in_band_before_commit() {
        let m = meter_with("lease-1", 100, 1000);
        m.draw(&MeterKey::new("lease-1", 1), 90, 100).unwrap();
        // honest: exactly the remaining 10 admits (non-vacuity).
        assert!(m.draw(&MeterKey::new("lease-1", 2), 10, 200).is_ok());
        // over-budget: refused 402, nothing drawn for this key.
        match m.draw(&MeterKey::new("lease-1", 3), 1, 300) {
            Err(MeterError::OverBudget { headroom, .. }) => assert_eq!(headroom, 0),
            other => panic!("expected an over-budget refusal, got {other:?}"),
        }
        assert_eq!(
            m.drawn_total("lease-1"),
            100,
            "the refused draw charged nothing"
        );
    }

    #[test]
    fn replenishment_returns_headroom_at_the_derived_block() {
        let m = meter_with("lease-1", 100, 1000);
        m.draw(&MeterKey::new("lease-1", 1), 100, 100).unwrap(); // refill at 1100
        // within the window: over-budget.
        assert!(matches!(
            m.draw(&MeterKey::new("lease-1", 2), 1, 900),
            Err(MeterError::OverBudget { .. })
        ));
        // past the derived refill block: headroom restored, the draw admits.
        assert_eq!(m.headroom("lease-1", 1100), 100);
        assert!(m.draw(&MeterKey::new("lease-1", 3), 1, 1100).is_ok());
    }

    #[test]
    fn no_budget_open_fails_closed() {
        let m = ReplenishingMeter::new();
        assert!(matches!(
            m.draw(&MeterKey::new("ghost", 1), 1, 0),
            Err(MeterError::NoBudget { .. })
        ));
        assert_eq!(m.headroom("ghost", 0), 0, "unknown subject has no headroom");
    }

    // ── Use B: the settlement-contention child split ──────────────────────────

    #[test]
    fn attenuated_children_draw_without_contending_the_parent() {
        let m = ReplenishingMeter::new();
        // a hot provider account with a 1000-unit budget.
        m.open(
            "hot-account",
            BudgetTerms::new("DREGG", 1000, 100, 1000, 4, 0),
        )
        .unwrap();
        // mint one child per settler (the Stingray split, f = 0 ⇒ balance/N).
        for i in 0..4 {
            m.attenuate_child("hot-account", &format!("settler-{i}"), 250, 100, 250, 1, 0)
                .unwrap();
        }
        // each settler draws its full local budget — no lock on the parent.
        let mut total = 0i64;
        for i in 0..4 {
            let r = m
                .draw(&MeterKey::new(format!("settler-{i}"), 1), 250, 0)
                .unwrap();
            total += r.units;
        }
        assert_eq!(
            total, 1000,
            "Σ child draws = the parent ceiling, no contention"
        );
        // a child cannot over-draw past its attenuated ceiling.
        assert!(matches!(
            m.draw(&MeterKey::new("settler-0", 2), 1, 0),
            Err(MeterError::OverBudget { .. })
        ));
    }

    // ── the agent-budget tie-in (the Verifiable Agent Cloud) ──────────────────

    /// An autonomous agent's spend budget IS a replenishing-budget cell drawn through
    /// the same `Meter`: a runaway agent's invoke rate is bounded by the primitive that
    /// bounds a lease's compute — and a sub-agent gets an attenuated child of it.
    #[test]
    fn an_agent_budget_bounds_a_runaway_and_attenuates_to_a_subagent() {
        let m = ReplenishingMeter::new();
        m.open(
            "agent:cafef00d",
            BudgetTerms::new("DREGG", 50, 1000, 50, 2, 0),
        )
        .unwrap();
        // the agent makes calls until its rate is exhausted; further calls refuse 402.
        let mut admitted = 0;
        for call in 0..100 {
            match m.draw(&MeterKey::new("agent:cafef00d", call), 10, 100) {
                Ok(_) => admitted += 1,
                Err(MeterError::OverBudget { .. }) => break,
                other => panic!("unexpected {other:?}"),
            }
        }
        assert_eq!(
            admitted, 5,
            "the agent's spend rate is bounded to budget/period"
        );
        // hand a sub-agent a bounded child budget.
        m.attenuate_child("agent:cafef00d", "agent:subagent", 20, 1000, 20, 1, 0)
            .unwrap();
        assert!(m.draw(&MeterKey::new("agent:subagent", 1), 20, 100).is_ok());
        assert!(matches!(
            m.draw(&MeterKey::new("agent:subagent", 2), 1, 100),
            Err(MeterError::OverBudget { .. })
        ));
    }
}
