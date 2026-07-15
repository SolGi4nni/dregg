//! Unhappy paths the engine now handles: transient retry-with-backoff, permanent
//! fast-fail, a step-timeout safety net for a hung runner, a mid-workflow step failure
//! aborting the rest, and a malformed orchestration input failing cleanly.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use durable_workflow::{
    metrics, run_workflow_in_memory_blocking, RetryPolicy, StepError, StepRunner, WorkloadRun,
    WorkloadSpec,
};

/// Fails transiently its first `fail_transient_before` calls, then succeeds — a shared
/// call counter proves how many real attempts ran.
struct FlakyRunner {
    fail_transient_before: usize,
    calls: Arc<AtomicUsize>,
}
impl StepRunner for FlakyRunner {
    fn run(&self, spec: &WorkloadSpec) -> Result<String, StepError> {
        let n = self.calls.fetch_add(1, Ordering::SeqCst);
        if n < self.fail_transient_before {
            Err(StepError::transient(format!(
                "flaky: attempt {n} lost the isolate"
            )))
        } else {
            Ok(spec.source.trim().to_string())
        }
    }
}

/// Always fails permanently — retrying must not help.
struct AlwaysPermanent {
    calls: Arc<AtomicUsize>,
}
impl StepRunner for AlwaysPermanent {
    fn run(&self, _spec: &WorkloadSpec) -> Result<String, StepError> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        Err(StepError::permanent("bad program: will never succeed"))
    }
}

/// Blocks past any reasonable step timeout — the hung runner the safety net catches.
struct SlowRunner;
impl StepRunner for SlowRunner {
    fn run(&self, _spec: &WorkloadSpec) -> Result<String, StepError> {
        std::thread::sleep(Duration::from_secs(1));
        Ok("eventually".to_string())
    }
}

#[test]
fn transient_failure_is_retried_then_succeeds() {
    let calls = Arc::new(AtomicUsize::new(0));
    let runner = Arc::new(FlakyRunner {
        fail_transient_before: 2,
        calls: calls.clone(),
    });
    let run = WorkloadRun::new(100, 1, vec![WorkloadSpec::echo("s", "ok")]).with_retry(
        RetryPolicy::retrying(4, Duration::from_millis(5), Duration::from_millis(20)),
    );
    let out = run_workflow_in_memory_blocking(&run, "inst-retry-ok", runner).unwrap();
    assert_eq!(out.outputs, vec!["ok".to_string()]);
    assert_eq!(out.meter_units, 1);
    // Two transient failures + one success = three real attempts.
    assert_eq!(calls.load(Ordering::SeqCst), 3);
}

#[test]
fn transient_failure_exhausts_the_retry_budget() {
    let calls = Arc::new(AtomicUsize::new(0));
    let runner = Arc::new(FlakyRunner {
        fail_transient_before: 10, // never succeeds within the budget
        calls: calls.clone(),
    });
    let run = WorkloadRun::new(100, 1, vec![WorkloadSpec::echo("s", "ok")]).with_retry(
        RetryPolicy::retrying(3, Duration::from_millis(1), Duration::from_millis(4)),
    );
    let err = run_workflow_in_memory_blocking(&run, "inst-retry-exhaust", runner)
        .expect_err("should fail after exhausting retries");
    assert!(err.contains("after 3 attempt"), "got: {err}");
    assert_eq!(
        calls.load(Ordering::SeqCst),
        3,
        "exactly max_attempts real tries"
    );
}

#[test]
fn permanent_failure_fails_fast_without_retry() {
    let calls = Arc::new(AtomicUsize::new(0));
    let runner = Arc::new(AlwaysPermanent {
        calls: calls.clone(),
    });
    // A generous retry budget must NOT be spent on a permanent fault.
    let run = WorkloadRun::new(100, 1, vec![WorkloadSpec::echo("s", "x")]).with_retry(
        RetryPolicy::retrying(5, Duration::from_millis(1), Duration::from_millis(4)),
    );
    let err = run_workflow_in_memory_blocking(&run, "inst-perm", runner).expect_err("must fail");
    assert!(err.contains("permanent"), "classification lost: {err}");
    assert_eq!(
        calls.load(Ordering::SeqCst),
        1,
        "a permanent fault must not retry"
    );
}

#[test]
fn a_hung_runner_is_cut_off_by_the_step_timeout() {
    let runner = Arc::new(SlowRunner);
    let run = WorkloadRun::new(100, 1, vec![WorkloadSpec::echo("s", "slow")])
        .with_retry(RetryPolicy::default().with_step_timeout(Duration::from_millis(150)));
    let start = std::time::Instant::now();
    let err = run_workflow_in_memory_blocking(&run, "inst-timeout", runner)
        .expect_err("the hung step must time out");
    // The workflow fails on the timeout, well before the runner's 1s would elapse
    // across a real deployment (the safety net cut it off).
    assert!(err.contains("step-timeout"), "got: {err}");
    assert!(start.elapsed() < Duration::from_secs(5));
}

#[test]
fn a_mid_workflow_permanent_failure_aborts_the_rest() {
    // Step 1 (echo) succeeds; step 2 (lang the ExprRunner cannot run) permanently
    // fails — the workflow aborts and step 3 never runs.
    let run = WorkloadRun::new(
        100,
        1,
        vec![
            WorkloadSpec::echo("first", "one"),
            WorkloadSpec {
                label: "second".into(),
                lang: "wasm".into(),
                source: String::new(),
                tier: String::new(),
                cost: None,
            },
            WorkloadSpec::echo("third", "three"),
        ],
    );
    let err = run_workflow_in_memory_blocking(
        &run,
        "inst-midfail",
        Arc::new(durable_workflow::ExprRunner),
    )
    .expect_err("mid-workflow failure must abort");
    assert!(
        err.contains("second"),
        "error should name the failing step: {err}"
    );
    // Step 1 ran once; step 3 never ran.
    assert_eq!(metrics::run_calls("inst-midfail", "first"), 1);
    assert_eq!(metrics::run_calls("inst-midfail", "third"), 0);
}

/// A malformed orchestration input fails the workflow cleanly (no panic, a clear
/// error), driven through duroxide directly since the typed entry points can't
/// construct bad input.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn malformed_orchestration_input_fails_cleanly() {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};

    let store = Arc::new(SqliteProvider::new_in_memory().await.unwrap());
    let (activities, orchestrations) = durable_workflow::build_registries(
        Arc::new(durable_workflow::ExprRunner),
        durable_workflow::MeterBackend::InProcess,
    );
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    client
        .start_orchestration(
            "inst-badinput",
            durable_workflow::ORCHESTRATION_WORKLOAD_RUN,
            "{ this is not a WorkloadRun".to_string(),
        )
        .await
        .unwrap();
    let status = client
        .wait_for_orchestration("inst-badinput", Duration::from_secs(10))
        .await
        .unwrap();
    rt.shutdown(None).await;
    match status {
        OrchestrationStatus::Failed { details, .. } => {
            assert!(
                details.display_message().contains("bad WorkloadRun"),
                "unexpected failure: {}",
                details.display_message()
            );
        }
        other => panic!("expected a clean Failed, got {other:?}"),
    }
}
