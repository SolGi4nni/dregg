//! `meter` — where a step's charge lands, exactly-once.
//!
//! Each durable step schedules a `MeterTick` that charges `amount` units for its
//! period against the workflow's lease. Because the tick is a durable activity,
//! duroxide runs it at-most-once per logical step and replays a checkpointed
//! result without re-running — so each period charges **exactly once**, even
//! across a crash + resume.
//!
//! Two backends, selected when the registries are built:
//!
//! - [`MeterBackend::InProcess`] — a process-local observability tally. The
//!   always-available offline default; the on-disk crash-resume proof runs over it.
//! - [`MeterBackend::Postgres`] (feature `pg`) — the **transactional outbox**:
//!   each charge is written to the shared `hosted_meter` table on a `PgPool`,
//!   idempotent on `(lease_id, period)`. This reuses `hosted_durable`'s outbox
//!   writer verbatim (not a second copy), so the charges this engine records are
//!   exactly the rows the `hosted-durable` conserving settlement rail reads and
//!   settles. Durable metering and durable settlement meet on one table.

/// One lease meter charge — the input to a `MeterTick`.
///
/// `period` is the step ordinal within the lease (1-based); `amount` is the units
/// to debit. `(lease_id, period)` — where `lease_id` is the workflow instance id
/// — is the idempotency key, so a crash re-run never charges the same period twice.
#[derive(Debug, Clone, Copy, serde::Serialize, serde::Deserialize)]
pub struct MeterCharge {
    pub period: i64,
    pub amount: i64,
}

// ---------------------------------------------------------------------------
// In-process observability tally — per (instance, key) counters.
// ---------------------------------------------------------------------------

mod tally {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    fn store() -> &'static Mutex<HashMap<(String, String), i64>> {
        static S: OnceLock<Mutex<HashMap<(String, String), i64>>> = OnceLock::new();
        S.get_or_init(|| Mutex::new(HashMap::new()))
    }

    pub(crate) fn add(instance: &str, key: &str, delta: i64) -> i64 {
        let mut g = store().lock().expect("meter tally poisoned");
        let e = g
            .entry((instance.to_string(), key.to_string()))
            .or_insert(0);
        *e += delta;
        *e
    }

    pub(crate) fn get(instance: &str, key: &str) -> i64 {
        *store()
            .lock()
            .expect("meter tally poisoned")
            .get(&(instance.to_string(), key.to_string()))
            .unwrap_or(&0)
    }
}

/// Observable counters for a workflow instance (the in-process tally). A thin view
/// callers and tests use to witness exactly-once and the meter total without
/// re-reading the durable store.
pub mod metrics {
    /// Increment `(instance, key)` by `delta`, returning the new value.
    pub(crate) fn add(instance: &str, key: &str, delta: i64) -> i64 {
        super::tally::add(instance, key, delta)
    }

    /// Read a counter for an instance (`0` if never touched).
    pub fn get(instance: &str, key: &str) -> i64 {
        super::tally::get(instance, key)
    }

    /// How many times the `RunWorkload` activity actually executed for a step
    /// label on this instance. Exactly-once means this stays `1` across a crash +
    /// resume (a replayed step returns its recorded result without re-running).
    pub fn run_calls(instance: &str, label: &str) -> i64 {
        get(instance, &format!("run:{label}"))
    }

    /// The meter units charged against the lease for this instance.
    pub fn meter_units(instance: &str) -> i64 {
        get(instance, "meter_units")
    }
}

// ---------------------------------------------------------------------------
// The backend a built workflow charges into.
// ---------------------------------------------------------------------------

/// Where a `MeterTick` charge lands. Selected once when the registries are built;
/// the workflow code is identical across backends — only the charge sink changes.
#[derive(Clone)]
pub enum MeterBackend {
    /// Process-local observability tally. The always-available offline path.
    InProcess,
    /// The Postgres transactional outbox on the shared `hosted_meter` table
    /// (`hosted_durable`'s writer, reused).
    #[cfg(feature = "pg")]
    Postgres(std::sync::Arc<sqlx::PgPool>),
}

impl MeterBackend {
    /// Charge `amount` units for `period` against `lease_id`, returning the running
    /// total after this charge. Idempotent on `(lease_id, period)`: charging the
    /// same period twice (a crash re-running the activity) returns the recorded
    /// total without a second write. `Err` leaves no charge committed.
    pub(crate) async fn charge(&self, lease_id: &str, charge: MeterCharge) -> Result<i64, String> {
        match self {
            MeterBackend::InProcess => {
                // duroxide runs an activity at most once per logical step and
                // replays a checkpointed result without re-running, so the
                // in-process path needs no extra idempotency guard: each period
                // charges exactly once.
                Ok(metrics::add(lease_id, "meter_units", charge.amount))
            }
            #[cfg(feature = "pg")]
            MeterBackend::Postgres(pool) => {
                // Reuse the shared outbox writer: the SAME `hosted_meter` rows the
                // conserving settlement rail reads. `charge_outbox` is one Postgres
                // transaction, `ON CONFLICT (lease_id, period) DO NOTHING`.
                let hd_charge = hosted_durable::MeterCharge {
                    period: charge.period,
                    amount: charge.amount,
                };
                let total =
                    hosted_durable::pg_outbox::charge_outbox(pool, lease_id, hd_charge).await?;
                // Mirror into this crate's tally only on the committed charge.
                metrics::add(lease_id, "meter_units", charge.amount);
                Ok(total)
            }
        }
    }
}

/// Whether a step at 1-based `period`, each step costing `cost_per_step`, still
/// fits under `budget_units` — the replenishing-lease admission decision, pure and
/// replay-safe. The projected total after this step is `cost_per_step * period`;
/// the step is admitted iff that does not exceed the budget. Overflow ⇒ refuse.
pub fn lease_budget_admits(budget_units: i64, cost_per_step: i64, period: i64) -> bool {
    match cost_per_step.checked_mul(period) {
        Some(projected) => projected <= budget_units,
        None => false,
    }
}

#[cfg(feature = "pg")]
pub use hosted_durable::pg_outbox::{ensure_meter_schema, read_meter_outbox, MeterRow};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn budget_admits_up_to_the_ceiling() {
        assert!(lease_budget_admits(10, 3, 1)); // 3 <= 10
        assert!(lease_budget_admits(10, 3, 3)); // 9 <= 10
        assert!(!lease_budget_admits(10, 3, 4)); // 12 > 10
        assert!(!lease_budget_admits(i64::MAX, i64::MAX, 2)); // overflow ⇒ refuse
    }
}
