//! The real subprocess isolate driving durable workflow steps end to end: each step
//! runs in its own OS process under its tier's limits, checkpointed + metered like any
//! other step.

#![cfg(unix)]

use std::sync::Arc;

use durable_workflow::{run_workflow_on_disk_blocking, ProcessRunner, WorkloadRun, WorkloadSpec};
use tempfile::tempdir;

#[test]
fn process_steps_run_isolated_and_metered_on_disk() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let run = WorkloadRun::new(
        100,
        2,
        vec![
            // An isolated shell step: env scrubbed, cwd confined, rlimits applied.
            WorkloadSpec::process("emit", "printf '%s' forty-two", "isolated"),
            // A sandboxed step: arithmetic expansion, no external binary needed.
            WorkloadSpec::process("count", "printf '%s' $(( 6 * 7 ))", "sandboxed"),
        ],
    );
    let out =
        run_workflow_on_disk_blocking(&run, "inst-proc", &db, Arc::new(ProcessRunner::default()))
            .unwrap();
    assert_eq!(out.outputs, vec!["forty-two".to_string(), "42".to_string()]);
    assert_eq!(out.meter_units, 4);
}

#[test]
fn a_failing_process_step_fails_the_workflow() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let run = WorkloadRun::new(
        100,
        1,
        vec![WorkloadSpec::process(
            "boom",
            "echo nope >&2; exit 7",
            "isolated",
        )],
    );
    let err = run_workflow_on_disk_blocking(
        &run,
        "inst-proc-fail",
        &db,
        Arc::new(ProcessRunner::default()),
    )
    .expect_err("a nonzero-exit step must fail the workflow");
    assert!(err.contains("exited 7"), "got: {err}");
}

#[test]
fn a_confined_step_runs_in_its_own_working_directory() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    // The isolated step's cwd is a fresh temp dir, not the caller's cwd — a file it
    // writes lands there and is cleaned up, and `pwd` is not the test's directory.
    let run = WorkloadRun::new(
        100,
        1,
        vec![WorkloadSpec::process(
            "cwd",
            "echo scratch > f.txt && printf '%s' \"$(cat f.txt)\"",
            "isolated",
        )],
    );
    let out = run_workflow_on_disk_blocking(
        &run,
        "inst-proc-cwd",
        &db,
        Arc::new(ProcessRunner::default()),
    )
    .unwrap();
    assert_eq!(out.outputs, vec!["scratch".to_string()]);
}
