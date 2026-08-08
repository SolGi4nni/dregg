//! **THE MARSHALLING ENVELOPE MUST ADMIT EVERY CONSTRAINT A DEPLOYED CELL PROGRAM DECLARES.**
//!
//! `dregg_cell::program::eval` routes the Lean-evaluated `StateConstraint` subset through the
//! installed oracle and, when the oracle answers `None`, `undecided_subset_disposition` REFUSES
//! with `ConstraintOracleUnavailable` rather than handing the decision back to the unverified Rust
//! twin. That is the right disposition. Its consequence is that **an out-of-envelope subset
//! constraint is a total refusal of the turn**, not a fallback — so the marshaller's envelope is
//! not a wire budget any more, it is a liveness gate on every programmed cell in the tree.
//!
//! ⚑ **THE OUTAGE THIS TOOTH EXISTS TO CATCH, MEASURED 2026-08-08.** `coll_cell_count` capped
//! `fuel × stride + anchor + 1` at `MAX_COLL_CELLS = 8192`. Both deployed M-of-N map councils —
//! `starbridge-polis`'s `large_council::quorum_gate` and `starbridge-governed-namespace`'s
//! `committee_board::quorum_gate` — pinned `fuel` at their own 4096 ceiling for EVERY charter, so
//! a FIVE-member council resolved to 8193 cells and was declined by **one cell**. On a native
//! release node
//! that is `ConstraintOracleUnavailable` on the certification turn of every large council and
//! every committee board: the same shape as the `collective-choice` poll outage
//! `constraint_in_lean_subset`'s docblock already records, one app along.
//!
//! ⚠ **AND IT WAS INVISIBLE TO EVERY SUITE IN THE TREE**, because the fail-closed call site is
//! `not(debug_assertions)`-gated: `sdk/tests/polis_large_council_e2e.rs` is green in debug (the
//! Rust guest evaluator runs) and red only in `--release`, the profile nothing routinely runs it
//! in. This tooth is deliberately **profile-independent**: it asks the MARSHALLER whether it can
//! decide the constraint, which is the same question in both profiles and on every target.
//!
//! It walks the REAL program object (`large_council_cell_program`), not a transcription of it —
//! a mirror of the shape would drift from the app exactly as the bound drifted from the app.

use dregg_cell::CellState;
use dregg_cell::program::{
    CellProgram, ConstraintOracle, StateConstraint, TransitionMeta, constraint_in_lean_subset,
    field_from_u64,
};
use dregg_exec_lean::LeanConstraintOracle;
use starbridge_polis::large_council::{LargeCouncilCharter, large_council_cell_program};

/// Every `StateConstraint` a `CellProgram` can present to the evaluator, flattened out of the
/// `Cases` / `Predicate` shape.
fn constraints_of(program: &CellProgram) -> Vec<StateConstraint> {
    match program {
        // A circuit program declares no `StateConstraint`s for the evaluator to route.
        CellProgram::None | CellProgram::Circuit { .. } => Vec::new(),
        CellProgram::Predicate(cs) => cs.clone(),
        CellProgram::Cases(cases) => cases
            .iter()
            .flat_map(|c| c.constraints.iter().cloned())
            .collect(),
    }
}

/// The deployed large-council program, at the size the app's own tests deploy it.
fn deployed_large_council_program() -> CellProgram {
    let charter = LargeCouncilCharter::new((1..=5u64).map(field_from_u64).collect(), 3);
    large_council_cell_program(&charter).expect("the 5-member 3-of-5 charter is valid")
}

/// **THE TOOTH.** For every constraint the deployed large-council program declares, the Lean
/// constraint oracle must return a DECISION (`Some`) — admit or refuse, but a decision. A `None`
/// here is the marshaller declining, and on a native release node a decline is
/// `ConstraintOracleUnavailable`: the turn is refused and the cell cannot be governed at all.
#[test]
fn the_oracle_decides_every_constraint_the_large_council_program_declares() {
    let program = deployed_large_council_program();
    let constraints = constraints_of(&program);
    assert!(
        constraints.len() >= 2,
        "the large-council program must carry its invariants AND its quorum gate; got {}",
        constraints.len()
    );

    let state = CellState::new(1_000);
    let meta = TransitionMeta::wildcard();
    let oracle = LeanConstraintOracle;

    let mut undecided: Vec<String> = Vec::new();
    for c in &constraints {
        // Class-c (the named trusted-Rust slot: witness / crypto / executor-state) legitimately
        // answers `None` and falls through to the Rust evaluator WITHOUT refusing — that is what
        // `undecided_subset_disposition` distinguishes. Only a LEAN-SUBSET constraint that the
        // oracle cannot decide is an outage, so ask the same question `eval` asks.
        if !constraint_in_lean_subset(c) {
            continue;
        }
        if oracle
            .admits(c, &state, Some(&state), None, &meta)
            .is_none()
        {
            undecided.push(format!("{c:?}"));
        }
    }

    assert!(
        undecided.is_empty(),
        "the Lean constraint oracle DECLINED {} Lean-subset constraint(s) of the deployed \
         large-council program. On a native release build `dregg_cell`'s \
         `undecided_subset_disposition` turns each of these into `ConstraintOracleUnavailable`, so \
         EVERY turn touching such a cell is refused — the council cannot be certified, ever. \
         Declined:\n  {}",
        undecided.len(),
        undecided.join("\n  ")
    );
}

/// **THE UPPER EDGE, AND IT IS THE POLE THAT KEEPS THE CONSTANT HONEST.**
///
/// `dregg_cell::program::MAX_AGGREGATE_CELLS` claims the verified evaluator can decide an
/// aggregate of that size. Assert it — at the largest `fuel` the published derivation hands an
/// app. The failure mode being pinned is not a wrong answer: measured 2026-08-08, an aggregate
/// past the evaluator's capacity dies with `fatal runtime error: stack overflow, aborting`, i.e.
/// SIGABRT, i.e. a dead node process. The old envelope (`MAX_COLL_CELLS = 8192`) sat ABOVE that
/// point, so a program declaring `stride = 2, fuel = 4095` was admitted straight into the abort.
///
/// ⚠ A raise of `MAX_AGGREGATE_CELLS` that has not been re-measured turns this red, which is the
/// entire point: the constant is a MEASUREMENT, and nothing else in the tree can check it.
#[test]
fn the_evaluator_survives_and_decides_at_the_published_capacity() {
    use dregg_cell::program::{CollPred, ElemPredAtom, max_aggregate_fuel};
    const STRIDE: u32 = 2;
    const ANCHOR: u32 = 0;
    let gate = StateConstraint::FieldsCollectionAggregate {
        base: 16,
        stride: STRIDE,
        fuel: max_aggregate_fuel(STRIDE, ANCHOR),
        pred: CollPred::MOfNDistinct {
            m: 3,
            key_offset: ANCHOR,
            approved: ElemPredAtom::FieldEquals {
                offset: 1,
                value: field_from_u64(1),
            },
        },
    };
    let state = CellState::new(1_000);
    let decision = LeanConstraintOracle.admits(
        &gate,
        &state,
        Some(&state),
        None,
        &TransitionMeta::wildcard(),
    );
    assert!(
        decision.is_some(),
        "the marshaller declined an aggregate at exactly the capacity `MAX_AGGREGATE_CELLS` \
         publishes — the constant and the envelope disagree, so an app that derives its ceiling \
         from the constant ships a cell that can never be certified"
    );
}

/// The same question asked of the QUORUM GATE alone, so a failure names the collection-aggregate
/// envelope rather than "something in the program". This is the constraint whose `fuel × stride`
/// grid is exactly the envelope's declared-grid bound.
#[test]
fn the_oracle_decides_the_map_borne_quorum_gate() {
    let gate = starbridge_polis::large_council::quorum_gate(5, 3);
    assert!(
        constraint_in_lean_subset(&gate),
        "the dynamic-N quorum gate is a Lean-subset constraint — if it ever becomes class-c this \
         tooth is asking the wrong question and must be rewritten, not deleted"
    );
    let state = CellState::new(1_000);
    let decision = LeanConstraintOracle.admits(
        &gate,
        &state,
        Some(&state),
        None,
        &TransitionMeta::wildcard(),
    );
    assert!(
        decision.is_some(),
        "the marshaller DECLINED the deployed `MOfNDistinct` quorum gate, so a native release node \
         refuses every certification turn against a large council or a committee board. The grid \
         it declares (`fuel × stride + anchor + 1`) must be inside \
         `dregg_cell::program::MAX_AGGREGATE_CELLS`: {gate:?}"
    );
}
