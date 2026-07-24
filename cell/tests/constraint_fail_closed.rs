//! Constraint-oracle subset twin (#2): NON-DEGRADATION proof, over the real `evaluate` path.
//!
//! `evaluate_constraint_full` used to decide the Lean-evaluated `StateConstraint` subset in a
//! hand-written Rust `match` whenever no constraint oracle was installed — the fail-OPEN the audit
//! found (a native node that forgot `install_constraint_oracle` silently ran the Rust twin). That is
//! now closed: on a native **release** (deployed) build with no oracle, a Lean-subset constraint FAILS
//! CLOSED (`ProgramError::ConstraintOracleUnavailable`) instead of being decided in unverified Rust.
//!
//! The gate is RELEASE-only (`not(debug_assertions)` — cell's own "production" convention, the same
//! one the `test-stubs` accept-path guard uses), because `dregg-cell` is a pervasive shared
//! dependency: a plain `not(test)` fail-closed would refuse VALID turns for every programmed cell
//! across the whole workspace's DEBUG test builds. So:
//!   * the fail-closed DECISION LOGIC is unit-tested directly in `eval.rs`
//!     (`constraint_oracle_fail_closed_tests`);
//!   * the gate WIRING is pinned by `cargo check --release -p dregg-cell` (cell forbids release *test*
//!     builds via the `test-stubs` invariant, so it cannot be a runtime test);
//!   * THIS test pins NON-DEGRADATION: in a debug build the real `CellProgram::evaluate` path still
//!     runs the guest evaluator and admits a satisfied subset constraint — the workspace suite is not
//!     regressed by the change.

use dregg_cell::{CellProgram, CellState, StateConstraint, field_from_u64};

#[test]
fn debug_guest_evaluator_still_admits_a_satisfied_subset_constraint() {
    // A Lean-subset constraint (`FieldEquals`, pure) asserting field[0] == 7, satisfied.
    let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(7),
    }]);
    let mut state = CellState::new(0);
    state.fields[0] = field_from_u64(7);

    let result = program.evaluate(&state, None, None);

    // In this DEBUG test build the release fail-closed gate is inactive, so the guest evaluator runs
    // and admits the satisfied constraint. (A deployed RELEASE node with no oracle fails closed on the
    // same input — pinned by the `eval.rs` unit tests + `cargo check --release`.)
    assert!(
        result.is_ok(),
        "the guest evaluator must still admit a satisfied subset constraint in a debug build \
         (non-degradation); got {result:?}"
    );
}
