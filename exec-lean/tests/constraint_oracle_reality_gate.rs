//! END-TO-END REALITY-GATE (game-proof LARP-audit collapse).
//!
//! Installs the Lean-backed constraint oracle and then drives the REAL deployed evaluator entry
//! `dregg_cell::CellProgram::evaluate` (`cell/src/program/eval.rs`) — proving the admission decision
//! for the pure subset is COMPUTED BY the verified Lean `dregg_constraint_admits`
//! (`Dregg2.Exec.DeployedConstraint.admits`), through the actual `eval.rs` path a deployed turn takes,
//! not the FFI in isolation.
//!
//! ── THE CANARY ──────────────────────────────────────────────────────────────────────────────────
//! `field_gte_equal_admits_through_lean` asserts a `FieldGte` on an EQUAL value ADMITS (`>=` is
//! non-strict). Flip `Dregg2.Exec.DeployedConstraint.lean`'s `fieldGte` from `if v ≤ x` to `if v < x`,
//! rebuild + re-run — this test FLIPS RED: `eval.rs`'s decision changed because ONLY the Lean source
//! changed. That is the proof `eval.rs` goes through Lean, end to end.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::{CellProgram, CollPred, ElemPredAtom, ProgramError};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint, field_from_u64};
use dregg_exec_lean::register_constraint_oracle;

/// ⚑ **A REFUSAL IS NOT A VERDICT UNTIL YOU SAY WHICH ONE.**
///
/// Every refuse leg below used to assert `is_err()`. That is satisfied by the caveat refusing —
/// and equally by `ConstraintOracleUnavailable` (no oracle), by
/// `ConstraintOracleWireMalformed` (the Lean side could not read the admission wire this binary
/// built), and by anything else `eval.rs` can return. Which matters concretely here: for a week
/// this whole seam was answering on wires the evaluator never parsed, and `is_err()` would have
/// stayed green through all of it.
///
/// So each refuse leg names the `ProgramError` it means. `ConstraintViolated` is the caveat's own
/// refusal; everything else is the machinery's, and the machinery's must never read as the
/// caveat's.
#[track_caller]
fn refused_by_the_caveat(r: Result<(), ProgramError>, what: &str) {
    match r {
        Err(ProgramError::ConstraintViolated { .. }) => {}
        Err(other) => panic!(
            "{what}: refused, but NOT by the constraint — {other:?}. A machinery refusal (absent \
             oracle, unreadable admission wire) passing as a caveat refusal is exactly the \
             vacuity this file exists to avoid."
        ),
        Ok(()) => panic!("{what}: ADMITTED, and it must refuse"),
    }
}

/// Install once for this test binary (`OnceLock`; the whole file shares one process).
///
/// ── WHY THIS IS `demand_lean` AND NOT A BARE `return false` ─────────────────────────────────────
/// Every test below opens `if !ensure_oracle() { return; }`. A `#[test]` that returns early because
/// a precondition is missing is INDISTINGUISHABLE from a test that ran and passed — cargo prints
/// `ok` either way. That is not hypothetical here: commit `7ebe7b7d4b` dropped build.rs's
/// `cargo:rustc-cfg=dregg_constraint_admits_present`, `constraint_admits_available()` went
/// permanently false, and all five gates below self-skipped to green for 4d17h.
///
/// So BOTH exits are now loud, and both are ARMED by `DREGG_TEST_REQUIRE_LEAN=1` (the repo's
/// existing hard-mode env, honoured by `dregg_lean_ffi::demand_lean`):
///   * export absent   -> `demand_lean` prints, and PANICS when armed.
///   * oracle uninstalled after `register_constraint_oracle()` -> this used to return `false` with
///     NO message at all, which would have turned a real installation regression into five green
///     no-ops. It now prints, and panics when armed.
fn ensure_oracle() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the Lean-backed constraint oracle)",
    ) {
        return false;
    }
    // `register` may have already run in an earlier test fn of this binary; either way the oracle is
    // installed afterward. (`OnceLock::set` returns false on the second call — still installed.)
    let _ = register_constraint_oracle();
    dregg_lean_ffi::demand_lean(
        dregg_cell::program::constraint_oracle_installed(),
        "installed constraint oracle (register_constraint_oracle ran but \
         dregg_cell::program::constraint_oracle_installed() is still false)",
    )
}

fn state_with_reg0(v: u64) -> CellState {
    let mut s = CellState::default();
    s.fields[0] = field_from_u64(v);
    s
}

#[test]
fn field_gte_equal_admits_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let new = state_with_reg0(5);
    let prog = CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(5),
    }]);
    // 5 >= 5 ⇒ admit. THE CANARY: a strict flip in the Lean source makes this refuse.
    assert!(
        prog.evaluate(&new, None, None).is_ok(),
        "FieldGte(5,5) must ADMIT through the Lean evaluator"
    );
}

#[test]
fn field_gte_below_refuses_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let new = state_with_reg0(3);
    let prog = CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(5),
    }]);
    // 3 >= 5 is false ⇒ refuse (through Lean), and refuse AS A CONSTRAINT VIOLATION.
    refused_by_the_caveat(
        prog.evaluate(&new, None, None),
        "FieldGte(3,5) must REFUSE through the Lean evaluator",
    );
}

#[test]
fn sum_equals_routes_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let mut new = CellState::default();
    new.fields[0] = field_from_u64(3);
    new.fields[1] = field_from_u64(4);
    let ok = CellProgram::Predicate(vec![StateConstraint::SumEquals {
        indices: vec![0, 1],
        value: field_from_u64(7),
    }]);
    assert!(ok.evaluate(&new, None, None).is_ok(), "sum(3,4)=7 admits");
    let bad = CellProgram::Predicate(vec![StateConstraint::SumEquals {
        indices: vec![0, 1],
        value: field_from_u64(8),
    }]);
    refused_by_the_caveat(bad.evaluate(&new, None, None), "sum(3,4)!=8 refuses");
}

/// ── THE NEWLY-COVERED-ARM CANARY ────────────────────────────────────────────────────────────────
/// `CollectionAggregate` is one of the arms this widening moved into the Lean subset. Drive it through
/// the REAL `CellProgram::evaluate` path with the oracle installed: the council `mOfNDistinct` gate
/// admits two DISTINCT approving keys and REFUSES the duplicate-padded forge. The `mOfNDistinct`
/// distinctness lives ONLY in `Dregg2.Exec.DeployedConstraint.DCollPred.eval` — flip its `m` to 1 (or
/// drop the `filterMap`/dedup) and rebuild, and the forge case FLIPS to admit through `eval.rs`. That
/// is the proof the deployed executor's decision for this arm is COMPUTED BY the Lean source.
#[test]
fn collection_aggregate_council_routes_through_lean() {
    if !ensure_oracle() {
        return;
    }
    // A heap `(collection_id=4)` collection of stride-2 elements: (key, approved-flag).
    let coll = |elems: &[(u64, u64)]| -> CellState {
        let mut s = CellState::default();
        for (i, (k, flag)) in elems.iter().enumerate() {
            s.set_heap(4, (i * 2) as u32, field_from_u64(*k));
            s.set_heap(4, (i * 2 + 1) as u32, field_from_u64(*flag));
        }
        s
    };
    let council = StateConstraint::CollectionAggregate {
        collection_id: 4,
        stride: 2,
        fuel: 3,
        pred: CollPred::MOfNDistinct {
            m: 2,
            key_offset: 0,
            approved: ElemPredAtom::FieldEquals {
                offset: 1,
                value: field_from_u64(1),
            },
        },
    };
    // Two DISTINCT approving keys (7, 9) ⇒ admit.
    assert!(
        CellProgram::Predicate(vec![council.clone()])
            .evaluate(&coll(&[(7, 1), (9, 1)]), None, None)
            .is_ok(),
        "two distinct approving keys satisfy the 2-of-N council"
    );
    // THE DUPLICATE-PADDED FORGE: three approvals, ONE identity ⇒ refuse (the distinctness tooth).
    refused_by_the_caveat(
        CellProgram::Predicate(vec![council]).evaluate(
            &coll(&[(7, 1), (7, 1), (7, 1)]),
            None,
            None,
        ),
        "the duplicate-padded forge collapses to one distinct key and REFUSES",
    );
}

/// A second newly-covered arm: `RateLimit` reads the executor-held `sender_epoch_count`. Under a cap
/// of 3, two mutations admit and three refuse; an absent context fails CLOSED. The comparison lives in
/// `Dregg2.Exec.DeployedConstraint.admits`'s `rateLimit` arm — flip its `≥` to `>` and the boundary
/// case (`count == max`) flips through `eval.rs`.
#[test]
fn rate_limit_routes_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let ctx = |count: u64| EvalContext {
        block_height: 0,
        timestamp: 0,
        current_epoch: 0,
        sender: None,
        sender_epoch_count: count,
        revealed_preimage: None,
    };
    let rl = StateConstraint::RateLimit {
        max_per_epoch: 3,
        epoch_duration: 10,
    };
    let new = CellState::default();
    assert!(
        CellProgram::Predicate(vec![rl.clone()])
            .evaluate(&new, None, Some(&ctx(2)))
            .is_ok(),
        "2 mutations under a cap of 3 admits"
    );
    refused_by_the_caveat(
        CellProgram::Predicate(vec![rl.clone()]).evaluate(&new, None, Some(&ctx(3))),
        "3 mutations at the cap refuses (>=)",
    );
    // ⚑ FAIL-CLOSED: no context ⇒ the count is executor-held, so a refusal, never a silent admit.
    // Pinned to the verdict it MEANS: `MissingContextField`, the Lean `missingContext 3` arm. An
    // `is_err()` here would also have been satisfied by the wire never parsing.
    match CellProgram::Predicate(vec![rl]).evaluate(&new, None, None) {
        Err(ProgramError::MissingContextField { field }) => assert_eq!(
            field, "sender_epoch_count",
            "the fail-closed refusal must name the context field the executor holds"
        ),
        other => panic!(
            "an absent context must fail closed as MissingContextField(sender_epoch_count), got              {other:?}"
        ),
    }
}
