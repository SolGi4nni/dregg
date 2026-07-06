//! `pg_outbox` — the Postgres transactional-outbox meter: **exactly-once durable
//! metering across restart** (the double-charge race fix).
//!
//! Ported dregg-native from the retired operated layer's durable meter
//! (the prior operated layer, `mod pg`) — the one piece of the deferred
//! durable-workflow follow-up that is workflow-runtime-independent: a charge
//! lands in the [`crate::METER_TABLE`] outbox in ONE Postgres transaction,
//! idempotent on the `(lease_id, period)` key, so a crash re-run of an
//! already-charged period commits nothing new. This is the property the old
//! multi-tenant workload harness caught a real double-charge race against
//! (`racing_settle_on_one_key_charges_exactly_once`).
//!
//! The settlement rail reads the recorded charges back with
//! [`read_meter_outbox`] and settles each as one conserving `Effect::Transfer`
//! (see [`crate::payable`]).
//!
//! WIRING (not yet applied):
//! - `hosted-durable/Cargo.toml`: add
//!   `sqlx = { version = "0.8", optional = true, default-features = false, features = ["runtime-tokio", "postgres"] }`
//!   and `anyhow = { version = "1", optional = true }`, plus a feature
//!   `pg = ["dep:sqlx", "dep:anyhow"]`.
//! - `hosted-durable/src/lib.rs`: `#[cfg(feature = "pg")] pub mod pg_outbox;`
//! - a `#[ignore]`-by-default pg test porting the old
//!   `durable_workflow_charges_the_outbox_exactly_once_per_step_across_a_crash`
//!   tooth (the prior operated layer) against
//!   `DATABASE_URL`.

use anyhow::Result;
use serde::{Deserialize, Serialize};
use sqlx::{PgPool, Row};

use crate::{METER_TABLE, MeterCharge};

/// One recorded charge row in the [`METER_TABLE`] outbox.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MeterRow {
    pub lease_id: String,
    pub period: i64,
    pub amount: i64,
    pub running_total: i64,
}

/// Create the [`METER_TABLE`] outbox table if it does not exist. Idempotent —
/// safe to call on every startup.
pub async fn ensure_meter_schema(pool: &PgPool) -> Result<()> {
    // `CREATE TABLE IF NOT EXISTS` is not concurrency-safe against the system
    // catalogs: two connections can both pass the existence check and then
    // collide inserting the table's implicit row type into `pg_type`. Serialize
    // creators with a transaction-scoped advisory lock so concurrent callers
    // (e.g. parallel tests) are safe. The lock key is an arbitrary fixed
    // constant for this table.
    let mut tx = pool.begin().await?;
    sqlx::query("SELECT pg_advisory_xact_lock($1)")
        .bind(0x6452_6547_4d54_5230_i64) // "dRegMTR0" — a stable per-table lock key
        .execute(&mut *tx)
        .await?;
    sqlx::query(&format!(
        "CREATE TABLE IF NOT EXISTS {METER_TABLE} (
             lease_id      TEXT        NOT NULL,
             period        BIGINT      NOT NULL,
             amount        BIGINT      NOT NULL,
             running_total BIGINT      NOT NULL,
             charged_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
             PRIMARY KEY (lease_id, period)
         )"
    ))
    .execute(&mut *tx)
    .await?;
    tx.commit().await?;
    Ok(())
}

/// Charge one period for a lease into the outbox, in **one Postgres
/// transaction**, and return the running total after this charge.
///
/// The transaction reads the prior running total, computes the new one, and
/// inserts the row `ON CONFLICT (lease_id, period) DO NOTHING` — so a re-run of
/// an already-charged period commits nothing new and returns the recorded
/// total. The budget gate lives in the caller *before* this is scheduled, so an
/// over-budget step never reaches here and no partial charge can land.
pub async fn charge_outbox(
    pool: &PgPool,
    lease_id: &str,
    charge: MeterCharge,
) -> Result<i64, String> {
    let mut tx = pool
        .begin()
        .await
        .map_err(|e| format!("MeterTick: begin: {e}"))?;

    // Idempotency: if this period is already charged, return its recorded total.
    let existing: Option<i64> = sqlx::query_scalar(&format!(
        "SELECT running_total FROM {METER_TABLE} WHERE lease_id = $1 AND period = $2"
    ))
    .bind(lease_id)
    .bind(charge.period)
    .fetch_optional(&mut *tx)
    .await
    .map_err(|e| format!("MeterTick: select existing: {e}"))?;
    if let Some(total) = existing {
        tx.rollback().await.ok();
        return Ok(total);
    }

    // running_total is monotonic per period, so MAX is the latest total for the lease.
    let prior: i64 = sqlx::query_scalar(&format!(
        "SELECT COALESCE(MAX(running_total), 0) FROM {METER_TABLE} WHERE lease_id = $1"
    ))
    .bind(lease_id)
    .fetch_one(&mut *tx)
    .await
    .map_err(|e| format!("MeterTick: select prior: {e}"))?;
    let running_total = prior + charge.amount;

    sqlx::query(&format!(
        "INSERT INTO {METER_TABLE} (lease_id, period, amount, running_total)
             VALUES ($1, $2, $3, $4)
         ON CONFLICT (lease_id, period) DO NOTHING"
    ))
    .bind(lease_id)
    .bind(charge.period)
    .bind(charge.amount)
    .bind(running_total)
    .execute(&mut *tx)
    .await
    .map_err(|e| format!("MeterTick: insert charge: {e}"))?;

    tx.commit()
        .await
        .map_err(|e| format!("MeterTick: commit: {e}"))?;

    // Mirror into the in-process observability tally only on a genuine new
    // charge, so a replayed/idempotent re-run never inflates the observable
    // counter.
    crate::meter::tally_add(lease_id, "meter_units", charge.amount);
    Ok(running_total)
}

/// Read the recorded charges for a lease from the outbox, in period order.
///
/// This is the **settlement wire**: a real dregg `Payable` settlement (the
/// [`crate::payable`] rail, or `pg-dregg` in the same database) reads these rows
/// to settle the lease against the charges this durable layer committed.
pub async fn read_meter_outbox(pool: &PgPool, lease_id: &str) -> Result<Vec<MeterRow>> {
    let rows = sqlx::query(&format!(
        "SELECT lease_id, period, amount, running_total
             FROM {METER_TABLE} WHERE lease_id = $1 ORDER BY period"
    ))
    .bind(lease_id)
    .fetch_all(pool)
    .await?;
    Ok(rows
        .into_iter()
        .map(|r| MeterRow {
            lease_id: r.get("lease_id"),
            period: r.get("period"),
            amount: r.get("amount"),
            running_total: r.get("running_total"),
        })
        .collect())
}
