//! The durable-execution guarantees, exercised end to end over the on-disk store:
//! a workflow runs, meters exactly-once, resumes exactly-once after a "crash", and
//! refuses an over-budget step before it runs.

use std::sync::Arc;

use durable_workflow::{
    build_registries, metrics, run_expr_workflow_on_disk, ExprRunner, MeterBackend, WorkflowOutput,
    WorkloadRun, WorkloadSpec,
};
use tempfile::tempdir;

/// A two-step dependency chain: `40 + 2 = 42`, then `42 * 2 = 84`. Step 2's source
/// is built from step 1's recorded output, so the workflow is a real chain.
fn add_then_double() -> WorkloadRun {
    WorkloadRun::new(
        1_000,
        1,
        vec![
            WorkloadSpec::expr("add", "40 + 2"),
            WorkloadSpec::expr("double", "42 * 2"),
        ],
    )
}

#[test]
fn runs_to_completion_metered_on_disk() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let out = run_expr_workflow_on_disk(&add_then_double(), "inst-complete", &db).unwrap();
    assert_eq!(
        out,
        WorkflowOutput {
            outputs: vec!["42".to_string(), "84".to_string()],
            meter_units: 2,
        }
    );
    // The observable tally agrees with the durable output.
    assert_eq!(metrics::meter_units("inst-complete"), 2);
    assert_eq!(metrics::run_calls("inst-complete", "add"), 1);
    assert_eq!(metrics::run_calls("inst-complete", "double"), 1);
}

/// Open the on-disk store at `db` and start a runtime + client over the durable
/// workload registries (ExprRunner, in-process meter). The runtime auto-resumes any
/// in-flight instance already present in the store.
async fn attach(
    db: &std::path::Path,
) -> (std::sync::Arc<duroxide::runtime::Runtime>, duroxide::Client) {
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

/// A durable workflow interrupted mid-flight resumes on a fresh runtime and completes
/// **exactly-once**: the already-checkpointed step is replayed (not re-executed) and
/// its charge is not doubled. We drive duroxide directly so the "crash" is a runtime
/// shutdown with step 2 still pending — not a graceful completion.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn resumes_exactly_once_after_a_crash() {
    use duroxide::OrchestrationStatus;
    use std::time::Duration;

    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let instance = "inst-crash";

    // --- Run 1: start with a pause after step 1, let step 1 checkpoint + meter,
    //     then "crash" (shut the runtime down) while step 2 is still pending. ---
    let paused = add_then_double().with_pause(1, "resume-signal");
    {
        let (rt, client) = attach(&db).await;
        client
            .start_orchestration(
                instance,
                durable_workflow::ORCHESTRATION_WORKLOAD_RUN,
                serde_json::to_string(&paused).unwrap(),
            )
            .await
            .unwrap();
        // Wait until step 1 is durably metered (meter_units == 1) — i.e. the workflow
        // has checkpointed step 1 and parked on the wait, before step 2.
        let mut parked = false;
        for _ in 0..200 {
            if metrics::meter_units(instance) >= 1 {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
        assert!(parked, "step 1 was not metered before the crash");
        // Crash: drop the runtime without raising the resume event. The on-disk store
        // holds step 1's checkpoint + charge; step 2 never ran.
        rt.shutdown(None).await;
    }

    let after_crash_add = metrics::run_calls(instance, "add");
    let after_crash_units = metrics::meter_units(instance);
    assert_eq!(after_crash_add, 1, "step 1 ran once before the crash");
    assert_eq!(
        after_crash_units, 1,
        "only step 1 was charged before the crash"
    );

    // --- Run 2: a fresh runtime attaches to the SAME db and auto-resumes the parked
    //     instance. Raise the resume event so step 2 runs to completion. ---
    let out = {
        let (rt, client) = attach(&db).await;
        // The parked instance auto-resumes; raise the resume event. Retry the raise:
        // the wait subscription may be (re)created a beat after resume, and a raise
        // that lands before it exists is not buffered — so raise until it completes.
        let mut done = None;
        for _ in 0..20 {
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
        match done.expect("resume did not complete within the retry budget") {
            OrchestrationStatus::Completed { output, .. } => {
                serde_json::from_str::<WorkflowOutput>(&output).unwrap()
            }
            other => panic!("resume did not complete: {other:?}"),
        }
    };

    assert_eq!(
        out,
        WorkflowOutput {
            outputs: vec!["42".to_string(), "84".to_string()],
            meter_units: 2,
        }
    );
    // Exactly-once across the crash: step 1 executed ONCE total (run 2 replayed its
    // recorded result, never re-ran it), and the meter total is 2, not 3.
    assert_eq!(
        metrics::run_calls(instance, "add"),
        1,
        "step 1 must not re-execute on resume"
    );
    assert_eq!(metrics::run_calls(instance, "double"), 1);
    assert_eq!(
        metrics::meter_units(instance),
        2,
        "no double-charge on resume"
    );
}

#[test]
fn over_budget_step_fails_before_running() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    // Budget 1, cost 1/step: step 1 fits (1 <= 1), step 2 would reach 2 > 1 → reap.
    let run = WorkloadRun::new(
        1,
        1,
        vec![
            WorkloadSpec::expr("s1", "1 + 1"),
            WorkloadSpec::expr("s2", "2 + 2"),
        ],
    );
    let res = run_expr_workflow_on_disk(&run, "inst-budget", &db);
    let err = res.expect_err("an over-budget workflow must fail");
    assert!(
        err.contains("execution-lease exhausted"),
        "unexpected: {err}"
    );
    // Step 2 never ran (reaped before its work); step 1 did.
    assert_eq!(metrics::run_calls("inst-budget", "s1"), 1);
    assert_eq!(metrics::run_calls("inst-budget", "s2"), 0);
}
