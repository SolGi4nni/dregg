//! The settlement WELD, exercised end to end against a real Postgres: the durable
//! workflow's meter charges land in the shared `hosted_meter` outbox the
//! `hosted-durable` conserving settlement rail reads — idempotent on
//! `(lease_id, period)`, read back as the settlement wire.
//!
//! This is the test the crate was missing: the headline "durable metering meets
//! durable settlement on one table" used to be asserted by construction only. It runs
//! only when `DATABASE_URL` points at a Postgres (else it prints a skip and returns),
//! so `cargo test --features pg` is green offline and this becomes a real assertion
//! wherever a database is available.
//!
//! Run it:  `DATABASE_URL=postgres://localhost/dregg_test cargo test --features pg`

#![cfg(feature = "pg")]

use std::sync::Arc;

use durable_workflow::meter::{connect_meter_pool, read_meter_outbox};
use durable_workflow::{
    build_registries, ExprRunner, MeterBackend, WorkflowOutput, WorkloadRun, WorkloadSpec,
    ORCHESTRATION_WORKLOAD_RUN,
};

/// Drive a `WorkloadRun` on an in-memory duroxide store whose meter backend is the
/// shared Postgres `hosted_meter` outbox, awaiting completion.
async fn run_on_pg(
    pool: Arc<durable_workflow::meter::PgPool>,
    input: &WorkloadRun,
    instance: &str,
) -> Result<WorkflowOutput, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};
    use std::time::Duration;

    let store = Arc::new(SqliteProvider::new_in_memory().await.unwrap());
    let (activities, orchestrations) =
        build_registries(Arc::new(ExprRunner), MeterBackend::Postgres(pool));
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());
    client
        .start_orchestration(
            instance,
            ORCHESTRATION_WORKLOAD_RUN,
            serde_json::to_string(input).unwrap(),
        )
        .await
        .map_err(|e| e.to_string())?;
    let status = client
        .wait_for_orchestration(instance, Duration::from_secs(30))
        .await
        .map_err(|e| e.to_string())?;
    rt.shutdown(None).await;
    match status {
        OrchestrationStatus::Completed { output, .. } => Ok(serde_json::from_str(&output).unwrap()),
        OrchestrationStatus::Failed { details, .. } => Err(details.display_message()),
        other => Err(format!("unexpected: {other:?}")),
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn meter_charges_land_in_the_settlement_outbox_idempotently() {
    let Ok(url) = std::env::var("DATABASE_URL") else {
        eprintln!("pg_weld: DATABASE_URL unset — skipping the live-Postgres WELD test");
        return;
    };
    let pool = connect_meter_pool(&url)
        .await
        .expect("connect + ensure schema");

    // Unique lease id per run so repeated test runs do not collide on the table.
    let instance = format!("wf-weld-{}", std::process::id());
    let run = WorkloadRun::new(
        1_000,
        1,
        vec![
            WorkloadSpec::expr("add", "40 + 2").with_cost(3),
            WorkloadSpec::expr("double", "42 * 2").with_cost(7),
        ],
    );

    // First run: two steps charge 3 then 7 into the outbox.
    let out = run_on_pg(pool.clone(), &run, &instance).await.unwrap();
    assert_eq!(out.meter_units, 10);

    // The settlement wire: the conserving rail reads exactly these rows.
    let rows = read_meter_outbox(&pool, &instance).await.unwrap();
    assert_eq!(rows.len(), 2, "one row per period");
    assert_eq!(
        (rows[0].period, rows[0].amount, rows[0].running_total),
        (1, 3, 3)
    );
    assert_eq!(
        (rows[1].period, rows[1].amount, rows[1].running_total),
        (2, 7, 10)
    );

    // Re-run the SAME instance id: idempotent on (lease_id, period) — no new rows, no
    // double charge. (A crash-resume replays the ticks; this models charging the same
    // periods again.)
    let out2 = run_on_pg(pool.clone(), &run, &instance).await.unwrap();
    assert_eq!(out2.meter_units, 10, "deterministic total unchanged");
    let rows2 = read_meter_outbox(&pool, &instance).await.unwrap();
    assert_eq!(rows2.len(), 2, "no duplicate rows on re-charge");
    assert_eq!(
        rows2, rows,
        "settlement read-back is stable across re-charge"
    );
}
