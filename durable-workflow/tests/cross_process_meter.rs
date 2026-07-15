//! The meter total is correct across a REAL process boundary.
//!
//! The old crash-resume test "crashes" by dropping one runtime and starting another in
//! the *same* process, so the in-process meter static survives the "crash" and hides a
//! real bug: the running total used to be read from that process-global static, which a
//! genuine restart wipes — under-counting `meter_units` on resume. This test crashes in
//! a separate OS process (`crash_worker`) whose static dies with it, then resumes here,
//! and asserts the total is right. It passes only because the orchestration now derives
//! the total deterministically from durable history, not from the static.

use std::sync::Arc;
use std::time::Duration;

use durable_workflow::{
    build_registries, metrics, ExprRunner, MeterBackend, WorkflowOutput, ORCHESTRATION_WORKLOAD_RUN,
};
use tempfile::tempdir;

async fn attach(db: &std::path::Path) -> (Arc<duroxide::runtime::Runtime>, duroxide::Client) {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::Client;

    let db_url = format!("sqlite:{}?mode=rwc", db.display());
    let store = Arc::new(SqliteProvider::new(&db_url, None).await.unwrap());
    let (activities, orchestrations) =
        build_registries(Arc::new(ExprRunner), MeterBackend::InProcess);
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store);
    (rt, client)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn meter_units_correct_across_a_real_process_boundary() {
    use duroxide::OrchestrationStatus;

    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let instance = "inst-xproc";

    // --- Phase 1: a SEPARATE OS process runs + checkpoints step 1, then hard-exits
    //     with step 2 pending. Its in-process meter static dies with the process. ---
    let worker = env!("CARGO_BIN_EXE_crash_worker");
    let status = std::process::Command::new(worker)
        .arg(&db)
        .arg(instance)
        .status()
        .expect("spawn crash_worker");
    assert!(status.success(), "crash_worker failed: {status:?}");

    // This (resuming) process never ran step 1 — its static is empty. If the reported
    // total came from this static it would under-count to 1 on resume.
    assert_eq!(
        metrics::meter_units(instance),
        0,
        "the resuming process must start with an empty meter static"
    );

    // --- Phase 2: resume the on-disk instance HERE and complete it. ---
    let out: WorkflowOutput = {
        let (rt, client) = attach(&db).await;
        let mut done = None;
        for _ in 0..40 {
            client
                .raise_event(instance, "resume-signal", "")
                .await
                .unwrap();
            if let Ok(s) = client
                .wait_for_orchestration(instance, Duration::from_secs(3))
                .await
            {
                done = Some(s);
                break;
            }
        }
        rt.shutdown(None).await;
        match done.expect("resume did not complete") {
            OrchestrationStatus::Completed { output, .. } => serde_json::from_str(&output).unwrap(),
            other => panic!("resume did not complete: {other:?}"),
        }
    };

    // The deterministic derivation gives the correct total across the real restart.
    assert_eq!(
        out.meter_units, 2,
        "meter_units under-counted across a real process boundary"
    );
    assert_eq!(out.outputs, vec!["42".to_string(), "84".to_string()]);
    let _ = ORCHESTRATION_WORKLOAD_RUN;
}
