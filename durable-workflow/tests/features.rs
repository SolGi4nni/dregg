//! Variable per-step metering and continue-as-new history rolling.

use durable_workflow::{metrics, run_expr_workflow_on_disk, WorkloadRun, WorkloadSpec};
use tempfile::tempdir;

#[test]
fn variable_per_step_cost_is_metered() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let run = WorkloadRun::new(
        100,
        1, // default cost, overridden per step below
        vec![
            WorkloadSpec::echo("cheap", "a").with_cost(3),
            WorkloadSpec::echo("dear", "b").with_cost(7),
        ],
    );
    let out = run_expr_workflow_on_disk(&run, "inst-varcost-ok", &db).unwrap();
    assert_eq!(out.outputs, vec!["a".to_string(), "b".to_string()]);
    // 3 + 7, not a flat 2 * cost_per_step.
    assert_eq!(out.meter_units, 10);
}

#[test]
fn cumulative_cost_admission_reaps_the_over_budget_step() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    // Budget 10; three steps at cost 4: 4, 8 fit; the third would reach 12 > 10.
    let run = WorkloadRun::new(
        10,
        1,
        vec![
            WorkloadSpec::echo("a", "1").with_cost(4),
            WorkloadSpec::echo("b", "2").with_cost(4),
            WorkloadSpec::echo("c", "3").with_cost(4),
        ],
    );
    let err = run_expr_workflow_on_disk(&run, "inst-varcost-reap", &db)
        .expect_err("the third step is over budget");
    assert!(err.contains("execution-lease exhausted"), "got: {err}");
    assert_eq!(metrics::run_calls("inst-varcost-reap", "a"), 1);
    assert_eq!(metrics::run_calls("inst-varcost-reap", "b"), 1);
    assert_eq!(metrics::run_calls("inst-varcost-reap", "c"), 0);
}

#[test]
fn continue_as_new_bounds_history_and_preserves_the_total() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let steps: Vec<WorkloadSpec> = (0..5)
        .map(|i| WorkloadSpec::echo(format!("s{i}"), format!("v{i}")))
        .collect();
    // Roll the durable history every 2 steps: the 5-step workflow spans 3 executions
    // but completes as one instance with the full output and total carried across.
    let run = WorkloadRun::new(100, 1, steps).with_history_roll(2);
    let out = run_expr_workflow_on_disk(&run, "inst-can", &db).unwrap();
    assert_eq!(
        out.outputs,
        vec![
            "v0".to_string(),
            "v1".to_string(),
            "v2".to_string(),
            "v3".to_string(),
            "v4".to_string()
        ]
    );
    assert_eq!(out.meter_units, 5);
}
