//! `crash_worker` — a helper binary for the cross-process durability test.
//!
//! It runs the first step of a two-step workflow to a durable checkpoint on the
//! on-disk store, then **hard-exits** (no graceful shutdown) with step 2 still
//! pending — a genuine process crash, in a genuine separate OS process, so its
//! in-process meter static dies with it. `tests/cross_process_meter.rs` then resumes
//! the same on-disk instance in a *different* process and checks that the reported
//! meter total is correct across the real process boundary (the bug the old
//! same-process crash test could not catch).
//!
//! argv: `<db_path> <instance>`.

use std::sync::Arc;

use durable_workflow::{
    build_registries, metrics, ExprRunner, MeterBackend, WorkloadRun, WorkloadSpec,
    ORCHESTRATION_WORKLOAD_RUN,
};

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: crash_worker <db_path> <instance>");
        std::process::exit(2);
    }
    let db = std::path::PathBuf::from(&args[1]);
    let instance = args[2].clone();

    // Two-step chain, parked after step 1 so step 2 stays pending when we crash.
    let run = WorkloadRun::new(
        1_000,
        1,
        vec![
            WorkloadSpec::expr("add", "40 + 2"),
            WorkloadSpec::expr("double", "42 * 2"),
        ],
    )
    .with_pause(1, "resume-signal");

    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::Client;

    let db_url = format!("sqlite:{}?mode=rwc", db.display());
    let store = Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .expect("open store"),
    );
    let (activities, orchestrations) =
        build_registries(Arc::new(ExprRunner), MeterBackend::InProcess);
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());
    client
        .start_orchestration(
            &instance,
            ORCHESTRATION_WORKLOAD_RUN,
            serde_json::to_string(&run).expect("encode run"),
        )
        .await
        .expect("start orchestration");

    // Wait until step 1 is metered (the in-process static reflects it in THIS process),
    // i.e. the workflow has checkpointed step 1 and parked on the wait before step 2.
    let mut metered = false;
    for _ in 0..400 {
        if metrics::meter_units(&instance) >= 1 {
            metered = true;
            break;
        }
        tokio::time::sleep(std::time::Duration::from_millis(25)).await;
    }
    if !metered {
        eprintln!("crash_worker: step 1 never metered");
        std::process::exit(3);
    }
    // Give duroxide a beat to flush step 1's checkpoint + the parked wait to disk,
    // then CRASH: exit without shutting the runtime down. Step 2 is still pending.
    tokio::time::sleep(std::time::Duration::from_millis(800)).await;
    let _ = &rt; // keep the runtime alive until we exit
    std::process::exit(0);
}
