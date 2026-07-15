//! The identity/capability gate: a workload runs only under a verified, funded lease
//! grant. Naming an instance is no longer enough to run and charge it.

use std::sync::Arc;

use durable_workflow::{
    admission, run_workflow_authenticated_on_disk, ExprRunner, LeaseAuthority, LeaseGrant,
    SignedGrant, WorkloadRun, WorkloadSpec,
};
use tempfile::tempdir;

fn a_run(budget: i64) -> WorkloadRun {
    WorkloadRun::new(
        budget,
        1,
        vec![
            WorkloadSpec::expr("add", "40 + 2"),
            WorkloadSpec::expr("double", "42 * 2"),
        ],
    )
}

fn grant(lease: &str, budget: i64, not_after: u64) -> LeaseGrant {
    LeaseGrant {
        lease_id: lease.into(),
        budget_units: budget,
        not_after_unix: not_after,
        nonce: "grant-1".into(),
    }
}

#[test]
fn a_valid_grant_runs_under_the_granted_lease() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let auth = LeaseAuthority::from_key([9u8; 32]);
    let sg = auth.issue(grant("inst-authed", 1_000, u64::MAX));

    let out =
        run_workflow_authenticated_on_disk(&auth, &sg, &a_run(1_000), &db, Arc::new(ExprRunner))
            .unwrap();
    assert_eq!(out.outputs, vec!["42".to_string(), "84".to_string()]);
    assert_eq!(out.meter_units, 2);
}

#[test]
fn a_forged_grant_is_refused_before_running() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    // The issuer and the host hold DIFFERENT keys: the host cannot verify the issuer's
    // MAC, so the grant is treated as forged.
    let issuer = LeaseAuthority::from_key([1u8; 32]);
    let host = LeaseAuthority::from_key([2u8; 32]);
    let sg = issuer.issue(grant("inst-forged", 1_000, u64::MAX));

    let err =
        run_workflow_authenticated_on_disk(&host, &sg, &a_run(1_000), &db, Arc::new(ExprRunner))
            .expect_err("a forged grant must be refused");
    assert!(err.contains("admission refused"), "got: {err}");
    assert!(err.contains("signature"), "got: {err}");
}

#[test]
fn an_over_budget_workload_is_refused() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let auth = LeaseAuthority::from_key([9u8; 32]);
    // Grant funds only 5 units; the workload declares a budget of 1000.
    let sg = auth.issue(grant("inst-ob", 5, u64::MAX));

    let err =
        run_workflow_authenticated_on_disk(&auth, &sg, &a_run(1_000), &db, Arc::new(ExprRunner))
            .expect_err("declaring more budget than the grant funds must be refused");
    assert!(err.contains("admission refused"), "got: {err}");
    assert!(err.contains("budget"), "got: {err}");
}

#[test]
fn an_expired_grant_is_refused() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("wf.db");
    let auth = LeaseAuthority::from_key([9u8; 32]);
    // not_after in the past relative to wall clock.
    let past = admission::now_unix().saturating_sub(3600);
    let sg = auth.issue(grant("inst-exp", 1_000, past));

    let err =
        run_workflow_authenticated_on_disk(&auth, &sg, &a_run(1_000), &db, Arc::new(ExprRunner))
            .expect_err("an expired grant must be refused");
    assert!(err.contains("admission refused"), "got: {err}");
    assert!(err.contains("expired"), "got: {err}");
}

#[test]
fn a_grant_cannot_authorize_a_different_lease() {
    // The instance is taken from the verified grant, so a grant for "a" runs "a" — a
    // caller cannot smuggle a different instance name past admission (there is no
    // unauthenticated entry point that accepts a bare instance name + a grant for
    // another). Verified directly at the admission gate:
    let auth = LeaseAuthority::from_key([9u8; 32]);
    let sg: SignedGrant = auth.issue(grant("inst-a", 1_000, u64::MAX));
    let err = durable_workflow::admit(&auth, &sg, "inst-b", 1_000, 0).unwrap_err();
    assert!(matches!(
        err,
        durable_workflow::AdmissionError::LeaseMismatch { .. }
    ));
}
