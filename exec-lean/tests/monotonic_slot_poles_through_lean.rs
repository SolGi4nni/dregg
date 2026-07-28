//! `Monotonic` ON A BALANCE-SHAPED SLOT, BOTH POLES, THROUGH THE **DEPLOYED** RESOLVE.
//!
//! `dregg-tests`'s `gamma2_bilateral_binding::bilateral_with_layered_slot_caveats_evaluation_order`
//! proves the same property in the resolve where **no constraint oracle is installed**: a debug
//! test binary, where `cell/src/program/eval.rs` runs its own Rust guest-path `match`. That is not
//! the resolve a node runs. A native RELEASE node installs the Lean-backed oracle
//! (`AgentRuntime::new` -> `dregg_exec_lean::register_constraint_oracle`), and from that moment the
//! admission decision for the whole Lean-evaluated subset — `Monotonic` included — is computed by
//! `Dregg2.Exec.DeployedConstraint.admitsTop`, NOT by the Rust arm those tests exercise.
//!
//! So "a decreasing write is refused" had been proven for exactly one of the two decision
//! procedures the tree ships, and the other one is the deployed one.
//! `constraint_oracle_differential.rs` does pin `Monotonic`'s two poles — but at the `admits`
//! surface, on a hand-built `CellState` pair. Between `admits` and a committed turn sit
//! `evaluate_cell_program_for_executor`'s skip list, the touched-cell snapshot map, and the
//! `old_state == None` initialization exemption; none of those are exercised by a direct `admits`
//! call. This file drives a REAL `TurnExecutor::execute` with the oracle installed, so the object
//! under test is the turn, not the predicate.
//!
//! ## The three legs, and why the third one is what makes the first two mean something
//!
//! * **ADMIT** — 100 -> 110 commits. Without it a refusal proves nothing (every leg would be red
//!   for any reason at all, e.g. a fixture the executor rejects before it ever reaches a program).
//! * **REFUSE** — 100 -> 90 is rejected, and rejected with `ProgramViolation` naming the cell that
//!   carries the caveat. A bare `Rejected { .. }` would also be satisfied by
//!   `ConstraintOracleUnavailable`, by a budget refusal, by a capability refusal — the assertion
//!   has to name the refusal it wants.
//! * **ABLATION** — the SAME decreasing turn, with `Monotonic` deleted from the program and
//!   nothing else changed, COMMITS. This is the standing red-proof: it is what says the refusal
//!   above is attributable to the `Monotonic` caveat and not to some other property of the
//!   fixture. Delete the `Monotonic` arm from `Dregg2.Exec.DeployedConstraint` (or from
//!   `eval.rs`'s Rust twin) and the REFUSE leg flips red while this one stays green.
//!
//! ## The cross-cell leg
//!
//! `bilateral_with_layered_slot_caveats_evaluation_order`'s sharp shape is layered caveats: a
//! `BoundDelta` that the peer SATISFIES sitting on the same slot as a `Monotonic` the local cell
//! VIOLATES. The executor evaluates those in two different places — `BoundDelta` is skipped by
//! `evaluate_cell_program_for_executor` and enforced by `validate_bound_delta_program`, `Monotonic`
//! goes through the oracle — so a short-circuit on the satisfied cross-cell pass would commit a
//! decrease. That shape is reproduced here under the oracle.

use dregg_cell::program::DeltaRelation;
use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, Ledger, Permissions, StateConstraint, field_from_u64,
};
use dregg_exec_lean::register_constraint_oracle;
use dregg_turn::{ActionBuilder, ComputronCosts, Effect, TurnBuilder, TurnExecutor, TurnResult};

/// Install once for this binary (`OnceLock`; the whole file shares one process).
///
/// Both exits are LOUD and both are armed by `DREGG_TEST_REQUIRE_LEAN=1` — a `#[test]` that
/// returns early on a missing precondition is indistinguishable from one that ran and passed, and
/// that exact silence once kept five oracle gates green for 4d17h (see
/// `constraint_oracle_reality_gate.rs`).
fn ensure_oracle() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the Lean-backed constraint oracle)",
    ) {
        return false;
    }
    let _ = register_constraint_oracle();
    dregg_lean_ffi::demand_lean(
        dregg_cell::program::constraint_oracle_installed(),
        "installed constraint oracle (register_constraint_oracle ran but \
         dregg_cell::program::constraint_oracle_installed() is still false)",
    )
}

fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(11);
    let mut c = Cell::with_balance(pk, [0u8; 32], balance);
    c.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    c
}

/// The layered fixture: Alice carries `BoundDelta`(peer = Bob) plus, optionally, `Monotonic` on the
/// same slot; Bob carries only `BoundDelta`, so the cross-cell pass is always satisfiable and only
/// Alice's `Monotonic` can be the discriminator. One action moves value AND writes both slots.
fn run_layered(alice_new: u64, bob_new: u64, alice_monotonic: bool) -> TurnResult {
    let mut alice = open_cell(0xA1, 1_000);
    let mut bob = open_cell(0xB2, 1_000);
    let alice_id = alice.id();
    let bob_id = bob.id();

    let mut alice_constraints = vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: bob_id,
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }];
    if alice_monotonic {
        alice_constraints.push(StateConstraint::Monotonic { index: 0 });
    }
    alice.program = CellProgram::Predicate(alice_constraints);
    bob.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: alice_id,
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);
    alice.state.fields[0] = field_from_u64(100);
    bob.state.fields[0] = field_from_u64(100);
    alice
        .capabilities
        .grant(bob_id, AuthRequired::None)
        .unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(alice).unwrap();
    ledger.insert_cell(bob).unwrap();

    let action = ActionBuilder::new_unchecked_for_tests(alice_id, "layered", alice_id)
        .effect_transfer(alice_id, bob_id, 10)
        .effect(Effect::SetField {
            cell: alice_id,
            index: 0,
            value: field_from_u64(alice_new),
        })
        .effect(Effect::SetField {
            cell: bob_id,
            index: 0,
            value: field_from_u64(bob_new),
        })
        .build();
    let mut builder = TurnBuilder::new(alice_id, 0);
    builder.add_action(action);
    TurnExecutor::new(ComputronCosts::zero()).execute(&builder.fee(0).build(), &mut ledger)
}

/// The isolated single-cell shape: one programmed cell, one `SetField`, no peer and no value
/// movement — so nothing but the caveat can be the reason for a refusal.
fn run_solo(new_value: u64, monotonic: bool) -> (TurnResult, CellId) {
    let mut cell = open_cell(0xC3, 1_000);
    let id = cell.id();
    cell.program = if monotonic {
        CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }])
    } else {
        CellProgram::Predicate(vec![])
    };
    cell.state.fields[0] = field_from_u64(100);
    // A nonzero nonce, deliberately: `Monotonic`'s `old_state == None` arm ADMITS when the
    // post-state nonce is 0 (the documented cell-initialization path). Pinning the nonce above 0
    // means a fixture that somehow loses the old-state snapshot fails CLOSED
    // (`TransitionCheckRequiresOldState`) instead of silently satisfying this test. The turn's own
    // nonce has to follow the cell's, or the executor refuses on `NonceReplay` before any program
    // runs — which is itself a refusal this file must never mistake for the caveat's.
    let _ = cell.state.increment_nonce();
    let turn_nonce = cell.state.nonce();

    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let action = ActionBuilder::new_unchecked_for_tests(id, "solo", id)
        .effect(Effect::SetField {
            cell: id,
            index: 0,
            value: field_from_u64(new_value),
        })
        .build();
    let mut builder = TurnBuilder::new(id, turn_nonce);
    builder.add_action(action);
    (
        TurnExecutor::new(ComputronCosts::zero()).execute(&builder.fee(0).build(), &mut ledger),
        id,
    )
}

fn assert_program_violation(result: &TurnResult, cell: CellId, what: &str) {
    match result {
        TurnResult::Rejected {
            reason: dregg_turn::TurnError::ProgramViolation { cell: c, reason },
            ..
        } => {
            assert_eq!(
                *c, cell,
                "{what}: the refusal must name the cell carrying the caveat, got {c} (reason: \
                 {reason})"
            );
            assert!(
                !reason.contains("oracle"),
                "{what}: refused by an ABSENT/declining oracle \
                 (`ConstraintOracleUnavailable`), not by the caveat — this test would be vacuous: \
                 {reason}"
            );
        }
        other => panic!("{what}: expected ProgramViolation, got {other:?}"),
    }
}

/// SOLO, ADMIT POLE. 100 -> 110 under `Monotonic` commits with the Lean oracle deciding.
#[test]
fn solo_monotonic_increase_commits_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let (result, _) = run_solo(110, true);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "an increasing write under Monotonic must COMMIT through the Lean oracle, got: {result:?}"
    );
}

/// SOLO, REFUSE POLE. 100 -> 90 is refused, by the caveat, naming the cell.
#[test]
fn solo_monotonic_decrease_refused_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let (result, id) = run_solo(90, true);
    assert_program_violation(&result, id, "solo Monotonic decrease");
}

/// SOLO, ABLATION (the standing red-proof). The SAME decreasing turn with `Monotonic` deleted from
/// the program COMMITS — so the refusal above is the caveat's, and nothing else in this fixture
/// would have stopped a balance slot going 100 -> 90.
#[test]
fn solo_decrease_without_the_caveat_commits() {
    if !ensure_oracle() {
        return;
    }
    let (result, _) = run_solo(90, false);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "ABLATION: with Monotonic removed the identical decreasing turn must COMMIT — if it does \
         not, the refuse-pole above is not attributable to the caveat: {result:?}"
    );
}

/// LAYERED, ADMIT POLE. `BoundDelta` satisfied (Alice -10 / Bob +10) AND `Monotonic` satisfied
/// (Alice 100 -> 110, Bob 100 -> 90) commits.
#[test]
fn layered_both_satisfied_commits_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let result = run_layered(110, 90, true);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "BoundDelta OK + Monotonic OK must commit through the Lean oracle, got: {result:?}"
    );
}

/// LAYERED, THE ORDERING TOOTH. `BoundDelta` SATISFIED (Alice -10 / Bob +10 are still
/// equal-and-opposite) while Alice's `Monotonic` is VIOLATED (100 -> 90). The two live in
/// different executor passes; a short-circuit on the satisfied cross-cell pass commits a decrease.
#[test]
fn layered_satisfied_bound_delta_does_not_excuse_a_violated_monotonic() {
    if !ensure_oracle() {
        return;
    }
    let alice_id = open_cell(0xA1, 1_000).id();
    let result = run_layered(90, 110, true);
    assert_program_violation(
        &result,
        alice_id,
        "layered Monotonic under a satisfied BoundDelta",
    );
}

/// LAYERED, ABLATION. The identical decreasing turn with Alice's `Monotonic` removed COMMITS —
/// which is exactly why the leg above matters: the cross-cell pass is satisfied either way, so
/// `Monotonic` is the only thing standing between this turn and a committed decrease.
#[test]
fn layered_decrease_without_the_caveat_commits() {
    if !ensure_oracle() {
        return;
    }
    let result = run_layered(90, 110, false);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "ABLATION: BoundDelta alone admits Alice 100 -> 90 (it is equal-and-opposite to Bob's \
         +10), so the refusal in the previous test is the Monotonic caveat's: {result:?}"
    );
}
