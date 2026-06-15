//! Executor-path enforcement tests for `StateConstraint` variants.
//!
//! Each test installs a `CellProgram::Predicate(vec![<constraint>])` on
//! the agent's primary cell in an `EmbeddedExecutor`, then submits:
//!   1. An action that SATISFIES the constraint  → asserts `Ok` commit.
//!   2. An action that VIOLATES the constraint   → asserts `Err` rejection.
//!
//! All tests drive real `EmbeddedExecutor::submit_action` — no test
//! merely builds a value without executing it.
//!
//! Skipped variants (not testable via the executor without external
//! wiring): `Monotonic`, `MonotonicSequence` (already confirmed),
//! `CapabilityUniqueness` (evaluator always returns Ok — structural
//! declaration only), `BoundDelta` (cross-cell wiring not yet available),
//! `TemporalPredicate` / `Witnessed` / `Renounced` / `Custom`
//! (require a `WitnessedPredicateRegistry` with a real verifier wired for
//! the relevant kind; the `Custom` threshold-sig kind is still unwired).
//!
//! `SenderAuthorized { PublicRoot }` is NOW COVERED (below): the embedded
//! executor defaults to `registry_with_real_verifiers()`, whose real
//! Poseidon2 `MerkleMembership` STARK verifier enforces it — an honest member
//! commits with a `single_member_membership_proof` witness, a non-member is
//! rejected at the circuit level. (It was previously skipped as "no verifier
//! wired"; the wiring landed.)

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor};
use dregg_cell::program::{BoundBranch, CollPred, ElemPredAtom, SimpleStateConstraint};
use dregg_cell::{CellProgram, StateConstraint, field_from_u64};
use dregg_turn::action::{Effect, WitnessBlob, WitnessKind};

// ─────────────────────────────────────────────────────────────────────────────
// Test harness helpers
// ─────────────────────────────────────────────────────────────────────────────

fn fresh(seed: u8) -> (EmbeddedExecutor, AppCipherclerk) {
    let cc = AppCipherclerk::new(AgentCipherclerk::from_seed([seed; 64]), [42u8; 32]);
    let ex = EmbeddedExecutor::new(&cc, "default");
    (ex, cc)
}

/// Build a SetField action on the agent's own cell, slot `index` → `value`.
fn set_field(
    ex: &EmbeddedExecutor,
    cc: &AppCipherclerk,
    index: usize,
    value: [u8; 32],
) -> dregg_turn::action::Action {
    cc.make_self_action(
        "set",
        vec![Effect::SetField {
            cell: ex.cell_id(),
            index,
            value,
        }],
    )
}

/// Build a SetField action and attach a Preimage32 witness blob (for
/// `PreimageGate` tests).
fn set_field_with_preimage(
    ex: &EmbeddedExecutor,
    cc: &AppCipherclerk,
    index: usize,
    value: [u8; 32],
    preimage: [u8; 32],
) -> dregg_turn::action::Action {
    let mut action = set_field(ex, cc, index, value);
    action.witness_blobs = vec![WitnessBlob {
        kind: WitnessKind::Preimage32,
        bytes: preimage.to_vec(),
    }];
    // Re-sign after mutating the witness blob so the signature covers it.
    cc.sign_action(action)
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. FieldEquals
// ─────────────────────────────────────────────────────────────────────────────

/// `FieldEquals`: slot[0] must equal 42.
/// Accept: set slot[0] = 42. Reject: set slot[0] = 99.
#[test]
fn field_equals_accept_and_reject() {
    let (ex, cc) = fresh(1);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(42),
        }]),
    );

    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(42)));
    assert!(ok.is_ok(), "FieldEquals accept failed: {ok:?}");

    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(99)));
    assert!(err.is_err(), "FieldEquals did not reject wrong value");
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. FieldGte
// ─────────────────────────────────────────────────────────────────────────────

/// `FieldGte`: slot[1] >= 100.
/// Accept: set slot[1] = 200. Reject: set slot[1] = 50.
#[test]
fn field_gte_accept_and_reject() {
    let (ex, cc) = fresh(2);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        }]),
    );

    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 1, field_from_u64(200)));
    assert!(ok.is_ok(), "FieldGte accept failed: {ok:?}");

    let err = ex.submit_action(&cc, set_field(&ex, &cc, 1, field_from_u64(50)));
    assert!(err.is_err(), "FieldGte did not reject value below minimum");
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. FieldLte
// ─────────────────────────────────────────────────────────────────────────────

/// `FieldLte`: slot[2] <= 100.
/// Accept: set slot[2] = 50. Reject: set slot[2] = 200.
#[test]
fn field_lte_accept_and_reject() {
    let (ex, cc) = fresh(3);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::FieldLte {
            index: 2,
            value: field_from_u64(100),
        }]),
    );

    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 2, field_from_u64(50)));
    assert!(ok.is_ok(), "FieldLte accept failed: {ok:?}");

    let err = ex.submit_action(&cc, set_field(&ex, &cc, 2, field_from_u64(200)));
    assert!(err.is_err(), "FieldLte did not reject value above maximum");
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. FieldLteField
// ─────────────────────────────────────────────────────────────────────────────

/// `FieldLteField`: slot[0] <= slot[1].
/// Accept: set slot[0]=10 slot[1]=20 in one turn (via two effects); then
/// try slot[0]=30 with slot[1] still 20 → reject.
///
/// Because a single `make_self_action` carries multiple effects, both
/// slots are set atomically and the program sees the post-state.
#[test]
fn field_lte_field_accept_and_reject() {
    let (ex, cc) = fresh(4);
    let cell = ex.cell_id();
    ex.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::FieldLteField {
            left_index: 0,
            right_index: 1,
        }]),
    );

    // Accept: slot[0]=10, slot[1]=20 → 10 <= 20.
    let accept_action = cc.make_self_action(
        "set-both",
        vec![
            Effect::SetField {
                cell,
                index: 0,
                value: field_from_u64(10),
            },
            Effect::SetField {
                cell,
                index: 1,
                value: field_from_u64(20),
            },
        ],
    );
    let ok = ex.submit_action(&cc, accept_action);
    assert!(ok.is_ok(), "FieldLteField accept failed: {ok:?}");

    // Reject: slot[0]=30, slot[1] is still 20 → 30 > 20.
    // We only need to set slot[0] because slot[1]=20 from the previous turn.
    let reject_action = cc.make_self_action(
        "set-left",
        vec![Effect::SetField {
            cell,
            index: 0,
            value: field_from_u64(30),
        }],
    );
    let err = ex.submit_action(&cc, reject_action);
    assert!(err.is_err(), "FieldLteField did not reject left > right");
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. WriteOnce
// ─────────────────────────────────────────────────────────────────────────────

/// `WriteOnce`: slot[3] can only be written when it is zero.
/// Accept: first write (old=0 → new=7). Reject: second write (old=7 → new=99).
#[test]
fn write_once_accept_and_reject() {
    let (ex, cc) = fresh(5);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 3 }]),
    );

    // Accept: slot[3] starts at zero → write 7.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 3, field_from_u64(7)));
    assert!(ok.is_ok(), "WriteOnce first write failed: {ok:?}");

    // Reject: slot[3] is now 7 (non-zero) → changing it must be rejected.
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 3, field_from_u64(99)));
    assert!(err.is_err(), "WriteOnce did not block second write");
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. Immutable
// ─────────────────────────────────────────────────────────────────────────────

/// `Immutable`: slot[0] must never change after its initial state.
/// Accept: an action that touches slot[1] but leaves slot[0] at its
/// current value (0 == 0). Reject: an action that changes slot[0].
#[test]
fn immutable_accept_and_reject() {
    let (ex, cc) = fresh(6);
    let cell = ex.cell_id();
    ex.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::Immutable { index: 0 }]),
    );

    // Accept: change slot[1], leave slot[0] intact (old[0]=0 == new[0]=0).
    let ok = ex.submit_action(
        &cc,
        cc.make_self_action(
            "touch-slot1",
            vec![Effect::SetField {
                cell,
                index: 1,
                value: field_from_u64(1),
            }],
        ),
    );
    assert!(
        ok.is_ok(),
        "Immutable accept (no change to slot[0]) failed: {ok:?}"
    );

    // Reject: attempt to change slot[0].
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(99)));
    assert!(err.is_err(), "Immutable did not block mutation of slot[0]");
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. StrictMonotonic
// ─────────────────────────────────────────────────────────────────────────────

/// `StrictMonotonic`: slot[0] must strictly increase on every transition.
/// Accept: 0 → 5 (5 > 0). Reject: 5 → 3 (3 < 5, not strictly increasing).
#[test]
fn strict_monotonic_accept_and_reject() {
    let (ex, cc) = fresh(7);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::StrictMonotonic { index: 0 }]),
    );

    // Accept: 0 → 5.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(5)));
    assert!(ok.is_ok(), "StrictMonotonic accept (0→5) failed: {ok:?}");

    // Reject: 5 → 3 (decreases).
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(3)));
    assert!(
        err.is_err(),
        "StrictMonotonic did not reject decrease (5→3)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 8. FieldDelta
// ─────────────────────────────────────────────────────────────────────────────

/// `FieldDelta`: slot[0] must advance by exactly delta=10 each transition.
/// Accept: 0 → 10. Reject: 10 → 25 (delta=15, not 10).
#[test]
fn field_delta_accept_and_reject() {
    let (ex, cc) = fresh(8);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::FieldDelta {
            index: 0,
            delta: field_from_u64(10),
        }]),
    );

    // Accept: 0 → 10 (delta = 10).
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(10)));
    assert!(ok.is_ok(), "FieldDelta accept (0→10) failed: {ok:?}");

    // Reject: 10 → 25 (delta = 15 ≠ 10).
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(25)));
    assert!(
        err.is_err(),
        "FieldDelta did not reject wrong delta (10→25 != +10)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 9. FieldDeltaInRange
// ─────────────────────────────────────────────────────────────────────────────

/// `FieldDeltaInRange`: slot[0] must advance by [5, 15] each transition.
/// Accept: 0 → 10 (delta=10, in [5,15]). Reject: 10 → 12 (delta=2, < 5).
#[test]
fn field_delta_in_range_accept_and_reject() {
    let (ex, cc) = fresh(9);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::FieldDeltaInRange {
            index: 0,
            min_delta: field_from_u64(5),
            max_delta: field_from_u64(15),
        }]),
    );

    // Accept: 0 → 10 (delta=10, in [5,15]).
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(10)));
    assert!(
        ok.is_ok(),
        "FieldDeltaInRange accept (delta=10) failed: {ok:?}"
    );

    // Reject: 10 → 12 (delta=2, below min_delta=5).
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(12)));
    assert!(
        err.is_err(),
        "FieldDeltaInRange did not reject delta below minimum (delta=2)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 10. BoundedBy
// ─────────────────────────────────────────────────────────────────────────────

/// `BoundedBy { index: 0, witness_index: 1 }`: slot[0] may only change if
/// slot[1] (the witness guard slot) is non-zero.
///
/// Accept: first set slot[1]=1 (arm the guard), then change slot[0].
/// Reject: clear slot[1] back to 0, then try to change slot[0].
#[test]
fn bounded_by_accept_and_reject() {
    let (ex, cc) = fresh(10);
    let cell = ex.cell_id();
    ex.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::BoundedBy {
            index: 0,
            witness_index: 1,
        }]),
    );

    // Arm the guard: set slot[1]=1. Slot[0] is unchanged (0==0) → BoundedBy
    // only fires when slot[0] *changes*, so this action is fine regardless.
    let arm = cc.make_self_action(
        "arm",
        vec![Effect::SetField {
            cell,
            index: 1,
            value: field_from_u64(1),
        }],
    );
    ex.submit_action(&cc, arm)
        .expect("arming guard slot must succeed");

    // Accept: slot[1]=1 (armed), change slot[0]=99 → guard is non-zero → ok.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(99)));
    assert!(ok.is_ok(), "BoundedBy accept (guard armed) failed: {ok:?}");

    // Disarm the guard: set slot[1]=0. Slot[0] is unchanged → ok.
    let disarm = cc.make_self_action(
        "disarm",
        vec![Effect::SetField {
            cell,
            index: 1,
            value: field_from_u64(0),
        }],
    );
    ex.submit_action(&cc, disarm)
        .expect("disarming guard slot must succeed");

    // Reject: slot[1]=0 (disarmed), try to change slot[0] → rejected.
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(77)));
    assert!(
        err.is_err(),
        "BoundedBy did not reject change when guard is zero"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 11. SumEquals
// ─────────────────────────────────────────────────────────────────────────────

/// `SumEquals { indices: [0, 1], value: 100 }`: sum of slot[0]+slot[1] must equal 100.
/// Accept: slot[0]=60, slot[1]=40 → sum=100. Reject: slot[0]=60, slot[1]=50 → sum=110.
#[test]
fn sum_equals_accept_and_reject() {
    let (ex, cc) = fresh(11);
    let cell = ex.cell_id();
    ex.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::SumEquals {
            indices: vec![0, 1],
            value: field_from_u64(100),
        }]),
    );

    // Accept: slot[0]=60, slot[1]=40, sum=100.
    let ok = ex.submit_action(
        &cc,
        cc.make_self_action(
            "set-sum",
            vec![
                Effect::SetField {
                    cell,
                    index: 0,
                    value: field_from_u64(60),
                },
                Effect::SetField {
                    cell,
                    index: 1,
                    value: field_from_u64(40),
                },
            ],
        ),
    );
    assert!(ok.is_ok(), "SumEquals accept (sum=100) failed: {ok:?}");

    // Reject: slot[0]=60 (unchanged), slot[1]=50 → sum=110 ≠ 100.
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 1, field_from_u64(50)));
    assert!(
        err.is_err(),
        "SumEquals did not reject wrong sum (110 ≠ 100)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 12. SumEqualsAcross
// ─────────────────────────────────────────────────────────────────────────────

/// `SumEqualsAcross { input_fields: [0], output_fields: [1] }`:
/// intra-cell conservation: `new[0] == old[0] + new[1]`.
///
/// Initial state: slot[0]=100, slot[1]=0.
/// Accept: slot[0]=120, slot[1]=20 → new[0]=120 == old[0](100) + new[1](20)=120 ✓
/// Reject: slot[0]=130, slot[1]=20 → new[0]=130 ≠ old[0](120)+new[1](20)=140 ✗
#[test]
fn sum_equals_across_accept_and_reject() {
    let (ex, cc) = fresh(12);
    let cell = ex.cell_id();
    ex.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::SumEqualsAcross {
            input_fields: vec![0],
            output_fields: vec![1],
        }]),
    );

    // Prime the cell: set slot[0]=100, slot[1]=0 in a single action so
    // that the SumEqualsAcross invariant holds for the first transition:
    // new[0]=100, old[0]=0, new[1]=0 → 100 == 0 + 0 is false.
    //
    // We need to seed a valid initial state. The constraint says
    // sum(new[inputs]) == sum(old[inputs]) + sum(new[outputs]).
    // On the very first action from zero state:
    //   new[0] = 100, old[0] = 0, new[1] = 0
    //   100 == 0 + 0 → false → rejects!
    //
    // So we need a two-step approach: first set slot[0] alone (output=slot[1]=0):
    //   new[0]=100 == old[0](0) + new[1](0) = 0 → false still.
    //
    // The constraint enforces conservation: Δinput = new_output.
    // From zero: new[0]=Δ, new[1]=Δ satisfies if new[0]=new[1].
    // Let's use: new[0]=20, new[1]=20: 20 == 0+20 = 20 ✓.
    let ok = ex.submit_action(
        &cc,
        cc.make_self_action(
            "conserve",
            vec![
                Effect::SetField {
                    cell,
                    index: 0,
                    value: field_from_u64(20),
                },
                Effect::SetField {
                    cell,
                    index: 1,
                    value: field_from_u64(20),
                },
            ],
        ),
    );
    assert!(
        ok.is_ok(),
        "SumEqualsAcross accept (20==0+20) failed: {ok:?}"
    );

    // Reject: new[0]=50, new[1]=20 → 50 ≠ old[0](20)+new[1](20) = 40.
    let err = ex.submit_action(
        &cc,
        cc.make_self_action(
            "conserve-bad",
            vec![
                Effect::SetField {
                    cell,
                    index: 0,
                    value: field_from_u64(50),
                },
                Effect::SetField {
                    cell,
                    index: 1,
                    value: field_from_u64(20),
                },
            ],
        ),
    );
    assert!(
        err.is_err(),
        "SumEqualsAcross did not reject conservation violation (50≠40)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 13. AllowedTransitions
// ─────────────────────────────────────────────────────────────────────────────

/// `AllowedTransitions`: slot[0] may only go 0→1, 1→2.
/// Accept: 0→1. Reject: 0→99 (not in allow-list).
#[test]
fn allowed_transitions_accept_and_reject() {
    let (ex, cc) = fresh(13);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::AllowedTransitions {
            slot_index: 0,
            allowed: vec![
                (field_from_u64(0), field_from_u64(1)),
                (field_from_u64(1), field_from_u64(2)),
            ],
        }]),
    );

    // Accept: 0 → 1.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
    assert!(ok.is_ok(), "AllowedTransitions accept (0→1) failed: {ok:?}");

    // Reject: 1 → 99 (not in list).
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(99)));
    assert!(err.is_err(), "AllowedTransitions did not reject 1→99");
}

// ─────────────────────────────────────────────────────────────────────────────
// 14. TemporalGate
// ─────────────────────────────────────────────────────────────────────────────

/// `TemporalGate { not_before: None, not_after: Some(1000) }`:
/// mutation is only valid while block_height <= 1000.
///
/// The embedded executor starts at block_height=0, so the window [0, 1000]
/// is open → accept. A gate with `not_before: Some(500)` at height=0 → reject.
#[test]
fn temporal_gate_accept_and_reject() {
    // Accept test: gate open at height 0 (not_after=1000 is in the future).
    {
        let (ex, cc) = fresh(14);
        ex.install_program(
            ex.cell_id(),
            CellProgram::Predicate(vec![StateConstraint::TemporalGate {
                not_before: None,
                not_after: Some(1000),
            }]),
        );
        let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
        assert!(
            ok.is_ok(),
            "TemporalGate accept (height=0, not_after=1000) failed: {ok:?}"
        );
    }

    // Reject test: gate requires not_before=500 but height=0 → too early.
    {
        let (ex, cc) = fresh(15);
        ex.install_program(
            ex.cell_id(),
            CellProgram::Predicate(vec![StateConstraint::TemporalGate {
                not_before: Some(500),
                not_after: None,
            }]),
        );
        let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
        assert!(
            err.is_err(),
            "TemporalGate did not reject when height=0 < not_before=500"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 15. RateLimit
// ─────────────────────────────────────────────────────────────────────────────

/// `RateLimit { max_per_epoch: 1, epoch_duration: 1024 }`:
/// at most 1 mutation per epoch.
///
/// First submission: executor counter = 0 < 1 → accept, then counter becomes 1.
/// Second submission same epoch: counter = 1 >= 1 → reject.
#[test]
fn rate_limit_accept_and_reject() {
    let (ex, cc) = fresh(16);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::RateLimit {
            max_per_epoch: 1,
            epoch_duration: 1024,
        }]),
    );

    // Accept: first mutation this epoch (counter=0 < 1).
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
    assert!(
        ok.is_ok(),
        "RateLimit accept (first mutation) failed: {ok:?}"
    );

    // Reject: second mutation this epoch (counter=1 >= 1).
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(2)));
    assert!(
        err.is_err(),
        "RateLimit did not reject second mutation in same epoch"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 16. RateLimitBySum
// ─────────────────────────────────────────────────────────────────────────────

/// `RateLimitBySum { slot_index: 0, max_sum_per_epoch: 100, epoch_duration: 1024 }`:
/// the sum of increments to slot[0] per epoch cannot exceed 100.
///
/// First action: 0 → 60 (delta=60, window_sum=60 ≤ 100 → accept).
/// Second action: 60 → 120 (delta=60, window_sum=120 > 100 → reject).
#[test]
fn rate_limit_by_sum_accept_and_reject() {
    let (ex, cc) = fresh(17);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 100,
            epoch_duration: 1024,
        }]),
    );

    // Accept: delta=60, window_sum=0+60=60 ≤ 100.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(60)));
    assert!(
        ok.is_ok(),
        "RateLimitBySum accept (delta=60) failed: {ok:?}"
    );

    // Reject: delta=60 again, window_sum=60+60=120 > 100.
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(120)));
    assert!(
        err.is_err(),
        "RateLimitBySum did not reject when window_sum would exceed 100"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 17. PreimageGate
// ─────────────────────────────────────────────────────────────────────────────

/// `PreimageGate { commitment_index: 0, hash_kind: Blake3 }`:
/// slot[0] holds blake3(preimage); the action must reveal the preimage.
///
/// Setup: set slot[0] = blake3(secret) via a no-program action first.
/// Accept: action carries correct preimage in witness_blobs.
/// Reject: action carries wrong preimage.
#[test]
fn preimage_gate_accept_and_reject() {
    let secret: [u8; 32] = [0xABu8; 32];
    let commitment: [u8; 32] = *blake3::hash(&secret).as_bytes();

    // Step 1: seed slot[0] = commitment with no program installed yet.
    let (ex, cc) = fresh(18);
    let seed_action = set_field(&ex, &cc, 0, commitment);
    ex.submit_action(&cc, seed_action)
        .expect("seeding commitment must succeed (no program yet)");

    // Step 2: install the PreimageGate program.
    use dregg_cell::program::HashKind;
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::PreimageGate {
            commitment_index: 0,
            hash_kind: HashKind::Blake3,
        }]),
    );

    // Accept: carry the correct preimage; the gate checks blake3(secret)==slot[0].
    // We also set slot[1] to trigger the program evaluation (the program fires
    // on any cell touch; slot[0] holds the commitment and must not change).
    let ok = ex.submit_action(
        &cc,
        set_field_with_preimage(&ex, &cc, 1, field_from_u64(1), secret),
    );
    assert!(
        ok.is_ok(),
        "PreimageGate accept (correct preimage) failed: {ok:?}"
    );

    // Reject: carry a wrong preimage.
    let wrong: [u8; 32] = [0xCDu8; 32];
    let err = ex.submit_action(
        &cc,
        set_field_with_preimage(&ex, &cc, 1, field_from_u64(2), wrong),
    );
    assert!(err.is_err(), "PreimageGate did not reject wrong preimage");
}

// ─────────────────────────────────────────────────────────────────────────────
// 18. AnyOf
// ─────────────────────────────────────────────────────────────────────────────

/// `AnyOf { variants: [FieldEquals{0, 10}, FieldEquals{0, 20}] }`:
/// slot[0] must be 10 OR 20.
/// Accept: set slot[0] = 20 (second branch). Reject: set slot[0] = 99.
#[test]
fn any_of_accept_and_reject() {
    let (ex, cc) = fresh(19);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(10),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(20),
                },
            ],
        }]),
    );

    // Accept: 20 matches the second branch.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(20)));
    assert!(ok.is_ok(), "AnyOf accept (value=20) failed: {ok:?}");

    // Reject: 99 matches neither branch.
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(99)));
    assert!(
        err.is_err(),
        "AnyOf did not reject value matching no branch"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 18b. AnyOfBound (§11.3 — witnessed branches under ⊔; here the cheap-branch
//      disjunction exercised through the executor commit path)
// ─────────────────────────────────────────────────────────────────────────────

/// `AnyOfBound { branches: [Simple(FieldEquals{0,10}), Simple(FieldEquals{0,20})] }`:
/// slot[0] must be 10 OR 20 — the same disjunction as AnyOf, but over the
/// witnessed-capable `BoundBranch` carrier. (The anti-strip soundness of a
/// *witnessed* branch is pinned in Lean — `anyOfBound_stripped_proof_branch_fails`
/// — and in the cell-lib unit suite; here we confirm the executor enforces the
/// disjunction on the real commit path.)
/// Accept: set slot[0] = 20 (second branch). Reject: set slot[0] = 99.
#[test]
fn any_of_bound_accept_and_reject() {
    let (ex, cc) = fresh(20);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::AnyOfBound {
            branches: vec![
                BoundBranch::Simple(SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(10),
                }),
                BoundBranch::Simple(SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(20),
                }),
            ],
        }]),
    );

    // Accept: 20 matches the second branch.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(20)));
    assert!(ok.is_ok(), "AnyOfBound accept (value=20) failed: {ok:?}");

    // Reject: 99 matches neither branch (and no witnessed branch can rescue it).
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(99)));
    assert!(
        err.is_err(),
        "AnyOfBound did not reject value matching no branch"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 19. CapabilityUniqueness — structural declaration only (no reject path)
// ─────────────────────────────────────────────────────────────────────────────

/// `CapabilityUniqueness`: SECURITY (audit item 1) — the scalar evaluator can
/// no longer silently accept this variant (it fails closed with
/// `CapabilityUniquenessRequiresExecutor`); real enforcement lives in the
/// executor's `validate_capability_uniqueness`, which binds the declared
/// cap-set-root slot to `compute_canonical_capability_root(&cell.capabilities)`
/// and rejects a zero/empty root. Pre-fix this was a structural no-op that let
/// a cell *declare* NFT-uniqueness while enforcing nothing.
///
/// Here the cell has no capabilities and slot 0 holds the zero default, so the
/// executor must REJECT (a unique-cap commitment cannot be empty) rather than
/// wave the transition through.
#[test]
fn capability_uniqueness_executor_fails_closed_on_empty_root() {
    let (ex, cc) = fresh(20);
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
            cap_set_root_slot: 0,
        }]),
    );
    let res = ex.submit_action(&cc, set_field(&ex, &cc, 1, field_from_u64(1)));
    assert!(
        res.is_err(),
        "CapabilityUniqueness must NOT silently accept; executor must fail closed on an \
         empty/zero cap-set root, got: {res:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 20. SenderIs — the turn sender must equal a bound identity (pk).
// ─────────────────────────────────────────────────────────────────────────────

/// `SenderIs { pk }`: the authorizing sender (`ctx.sender`, the signature pk)
/// must equal the bound `pk`.
/// Accept: bind to the agent's own pk (it signs the action). Reject: bind to a
/// different pk so the same agent's signature no longer matches.
#[test]
fn sender_is_accept_and_reject() {
    let (ex, cc) = fresh(21);
    let agent_pk = cc.public_key().0;

    // Accept: the predicate binds the agent's own pk; the agent signs, so
    // ctx.sender == agent_pk.
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::SenderIs { pk: agent_pk }]),
    );
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
    assert!(
        ok.is_ok(),
        "SenderIs accept (bound to own pk) failed: {ok:?}"
    );

    // Reject: bind to a different identity; the agent's sender no longer matches.
    let mut other_pk = agent_pk;
    other_pk[0] ^= 0xFF;
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::SenderIs { pk: other_pk }]),
    );
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(2)));
    assert!(
        err.is_err(),
        "SenderIs did not reject a sender that is not the bound identity"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 21. SenderInSlot — the turn sender must equal the identity held in slot[i].
// ─────────────────────────────────────────────────────────────────────────────

/// `SenderInSlot { index }`: `ctx.sender` must equal the (post-state) value in
/// slot[index].
/// Accept: write the agent's own pk into the slot in the same turn. Reject:
/// write different bytes so the post-state slot no longer holds the sender.
#[test]
fn sender_in_slot_accept_and_reject() {
    let (ex, cc) = fresh(22);
    let agent_pk = cc.public_key().0;

    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::SenderInSlot { index: 0 }]),
    );

    // Accept: the SetField writes the sender's pk into slot[0], so the
    // post-state slot equals ctx.sender.
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, agent_pk));
    assert!(
        ok.is_ok(),
        "SenderInSlot accept (slot[0] := sender pk) failed: {ok:?}"
    );

    // Reject: write a different value into slot[0]; it no longer holds the sender.
    let mut not_pk = agent_pk;
    not_pk[0] ^= 0xFF;
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, not_pk));
    assert!(
        err.is_err(),
        "SenderInSlot did not reject when slot[0] does not hold the sender"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 22. BalanceGte — the cell's (post-state) balance must be >= a floor.
// ─────────────────────────────────────────────────────────────────────────────

/// `BalanceGte { min }`: the cell balance must be at least `min`. The embedded
/// agent cell is seeded with 1_000_000 computrons and a SetField does not move
/// balance, so the unchanged balance is what is checked.
/// Accept: floor below the balance. Reject: floor above it.
#[test]
fn balance_gte_accept_and_reject() {
    let (ex, cc) = fresh(23);

    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::BalanceGte { min: 500_000 }]),
    );
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
    assert!(
        ok.is_ok(),
        "BalanceGte accept (1_000_000 >= 500_000) failed: {ok:?}"
    );

    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::BalanceGte { min: 2_000_000 }]),
    );
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(2)));
    assert!(
        err.is_err(),
        "BalanceGte did not reject a balance below the required minimum"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 23. BalanceLte — the cell's (post-state) balance must be <= a ceiling.
// ─────────────────────────────────────────────────────────────────────────────

/// `BalanceLte { max }`: the cell balance must be at most `max`.
/// Accept: ceiling above the balance. Reject: ceiling below it.
#[test]
fn balance_lte_accept_and_reject() {
    let (ex, cc) = fresh(24);

    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::BalanceLte { max: 2_000_000 }]),
    );
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
    assert!(
        ok.is_ok(),
        "BalanceLte accept (1_000_000 <= 2_000_000) failed: {ok:?}"
    );

    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::BalanceLte { max: 500_000 }]),
    );
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(2)));
    assert!(
        err.is_err(),
        "BalanceLte did not reject a balance above the allowed maximum"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 24. ObservedFieldEquals — the §11.2 cross-cell verified-observation atom,
//     now reachable to ACCEPT through the embedded executor's real
//     `FinalizedRootAuthority` (built from its committed view of the peer
//     cell's finalized state in the shared ledger).
// ─────────────────────────────────────────────────────────────────────────────

/// Build a SetField action on the agent's own cell and attach a `MerklePath`
/// witness blob at index 0 — the Merkle-open proof the `ObservedFieldEquals`
/// evaluator requires at `proof_witness_index`. Re-signs so the signature
/// covers the blob.
fn set_field_with_merkle_open(
    ex: &EmbeddedExecutor,
    cc: &AppCipherclerk,
    index: usize,
    value: [u8; 32],
) -> dregg_turn::action::Action {
    let mut action = set_field(ex, cc, index, value);
    action.witness_blobs = vec![WitnessBlob {
        kind: WitnessKind::MerklePath,
        bytes: vec![0u8; 1],
    }];
    cc.sign_action(action)
}

/// `ObservedFieldEquals { local_field: 0, source_cell: <peer>, source_field: 1,
/// at_root: <peer's finalized commitment>, proof_witness_index: 0 }`: slot[0]
/// MUST equal the peer cell's finalized `source_field` value.
///
/// The embedded executor builds a real `FinalizedRootAuthority` from its
/// committed view of the peer cell in the shared ledger (the peer's genuine
/// `state_commitment()` opens `source_field` to its current field value). So:
///   - Accept: set slot[0] = the peer's finalized value (42) → the binding is
///     genuine and the local field agrees, the turn COMMITS.
///   - Reject: set slot[0] = a divergent value (99) while the peer's finalized
///     value is still 42 → the mismatch tooth REJECTS on the commit path.
///
/// Both checked through `EmbeddedExecutor::submit_action` (the executor commit
/// path), so the §11.2 atom is now executor-enforced for an ACCEPT, not only a
/// fail-closed REJECT.
#[test]
fn observed_field_equals_accept_and_reject() {
    let (ex, cc) = fresh(25);

    // The peer (oracle) cell: a distinct cipherclerk's cell, inserted into the
    // SAME embedded ledger, with its finalized `source_field` (slot 1) set to
    // 42. Its genuine `state_commitment()` is what the executor's authority
    // binds — no forged root can satisfy the atom.
    let peer_pk = [0x11u8; 32];
    let peer_token = *blake3::hash(b"oracle").as_bytes();
    let finalized_price = field_from_u64(42);
    let mut peer = dregg_cell::Cell::with_balance(peer_pk, peer_token, 1_000_000);
    peer.state.set_field(1, finalized_price);
    let peer_id = peer.id();
    ex.ensure_cell(peer).expect("insert peer (oracle) cell");

    // Read the peer's GENUINE finalized commitment back out of the committed
    // ledger — this is exactly the `at_root` the executor's authority will
    // confirm for `source_cell` at submit time.
    let peer_root = ex.with_ledger_mut(|ledger| {
        ledger
            .get(&peer_id)
            .expect("peer cell present after ensure_cell")
            .state_commitment()
    });

    // The market cell program: local slot[0] MUST equal the oracle's finalized
    // price (slot 1) at the oracle's finalized commitment.
    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::ObservedFieldEquals {
            local_field: 0,
            source_cell: *peer_id.as_bytes(),
            source_field: 1,
            at_root: peer_root,
            proof_witness_index: 0,
        }]),
    );

    // ACCEPT: set slot[0] = 42, exactly the oracle's finalized price. The
    // executor's authority confirms the genuine root + binds the value, and the
    // local field agrees → the turn COMMITS.
    let ok = ex.submit_action(
        &cc,
        set_field_with_merkle_open(&ex, &cc, 0, finalized_price),
    );
    assert!(
        ok.is_ok(),
        "ObservedFieldEquals accept (slot[0] == peer's finalized field) failed: {ok:?}"
    );

    // REJECT (the mismatch tooth): set slot[0] = 99 while the peer's finalized
    // value is still 42 — the binding is real, the turn cannot diverge its
    // local field from the observed finalized value.
    let err = ex.submit_action(
        &cc,
        set_field_with_merkle_open(&ex, &cc, 0, field_from_u64(99)),
    );
    assert!(
        err.is_err(),
        "ObservedFieldEquals did not reject a local field diverging from the peer's finalized value"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 25. CollectionAggregate — the named-collection aggregate gate (the
//     heap/layout rung), enforced through the executor commit path against
//     the cell's own `(collection_id, key)` heap collection.
// ─────────────────────────────────────────────────────────────────────────────

/// Seed a single-field-per-element collection (`stride = 1`) under
/// `collection_id` into the agent cell's heap: element `i`'s anchor/value
/// lives at heap key `(collection_id, i)`. Re-seals `heap_root` (via
/// `set_heap`) so the commitment stays consistent.
fn seed_collection(ex: &EmbeddedExecutor, collection_id: u32, values: &[[u8; 32]]) {
    let cell = ex.cell_id();
    ex.with_ledger_mut(|ledger| {
        let c = ledger
            .get_mut(&cell)
            .expect("agent cell present in embedded ledger");
        for (i, v) in values.iter().enumerate() {
            c.state.set_heap(collection_id, i as u32, *v);
        }
    });
}

/// `CollectionAggregate { collection_id: 7, stride: 1, fuel: 4,
/// pred: CountSatGe { m: 2, p: FieldGte { offset: 0, value: 100 } } }`: at
/// least two elements of collection 7 must have value >= 100.
///
/// The collection lives in the cell's OWN heap (`heap_map`), read end-to-end
/// by `collection_id` on the commit path. A SetField turn touches the cell, so
/// the program re-evaluates the aggregate against the seeded heap:
///   - Accept: seed [150, 200, 50] → two elements >= 100, the CountSatGe
///     statistic is met → the submitted turn COMMITS.
///   - Reject: re-seed element 1 down to 50 → only one element >= 100, the
///     statistic fails → the submitted turn is REJECTED on commit.
///
/// Both checked through `EmbeddedExecutor::submit_action` (the executor commit
/// path), with the collection read out of `heap_map` on each side.
#[test]
fn collection_aggregate_accept_and_reject() {
    let (ex, cc) = fresh(26);
    let collection_id = 7u32;

    ex.install_program(
        ex.cell_id(),
        CellProgram::Predicate(vec![StateConstraint::CollectionAggregate {
            collection_id,
            stride: 1,
            fuel: 4,
            pred: CollPred::CountSatGe {
                m: 2,
                p: ElemPredAtom::FieldGte {
                    offset: 0,
                    value: field_from_u64(100),
                },
            },
        }]),
    );

    // ACCEPT: two of the three elements (150, 200) clear the >= 100 floor, so
    // CountSatGe { m: 2 } is met and the SetField turn COMMITS.
    seed_collection(
        &ex,
        collection_id,
        &[field_from_u64(150), field_from_u64(200), field_from_u64(50)],
    );
    let ok = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(1)));
    assert!(
        ok.is_ok(),
        "CollectionAggregate accept (2 elements >= 100) failed: {ok:?}"
    );

    // REJECT: drop element 1 to 50 — now only one element (150) clears the
    // floor, the CountSatGe { m: 2 } statistic fails, and the turn is REJECTED.
    seed_collection(
        &ex,
        collection_id,
        &[field_from_u64(150), field_from_u64(50), field_from_u64(50)],
    );
    let err = ex.submit_action(&cc, set_field(&ex, &cc, 0, field_from_u64(2)));
    assert!(
        err.is_err(),
        "CollectionAggregate did not reject a collection failing the CountSatGe statistic"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 26. SenderAuthorized { PublicRoot } — the actor-membership gate, enforced
//     through the executor commit path by the REAL Poseidon2 `MerkleMembership`
//     STARK verifier (the embedded executor defaults to
//     `registry_with_real_verifiers()`). Previously skipped as "no verifier
//     wired"; the wiring landed, so it is covered here.
// ─────────────────────────────────────────────────────────────────────────────

/// Build a SetField action carrying a `MerklePath` membership witness for the
/// signer's own public key (the candidate `SenderAuthorized` compresses to a
/// leaf). Re-signs after attaching the blob so the signature covers the action;
/// the membership witness itself is carved out of the signing message (the
/// witness-circularity carve-out), so a stolen proof cannot re-bind a different
/// sender.
fn set_field_with_membership(
    ex: &EmbeddedExecutor,
    cc: &AppCipherclerk,
    index: usize,
    value: [u8; 32],
    member_pk: &[u8; 32],
) -> dregg_turn::action::Action {
    let mut action = set_field(ex, cc, index, value);
    action.witness_blobs = vec![WitnessBlob {
        kind: WitnessKind::MerklePath,
        bytes: dregg_turn::executor::single_member_membership_proof(member_pk),
    }];
    cc.sign_action(action)
}

/// `SenderAuthorized { PublicRoot { set_root_index: 5 } }`: the action's sender
/// must be a member of the authorized set committed at slot[5].
///
/// Accept: seed slot[5] with the single-member root of the SIGNER's own pubkey
/// and attach the matching membership proof → the real Poseidon2 STARK verifies
/// a Merkle path from `compress(signer_pk)` to the committed root → the turn
/// COMMITS.
///
/// Reject: seed slot[5] with a DIFFERENT member's root (a stranger), so the
/// signer is not a leaf under it — no Merkle path exists (Poseidon2 collision
/// resistance), the STARK fails, and `SenderAuthorized` rejects even though the
/// signer presents a genuine proof for its own (wrong-root) tree.
#[test]
fn sender_authorized_public_root_accept_and_reject() {
    let (ex, cc) = fresh(27);
    let cell = ex.cell_id();
    let signer_pk = cc.public_key().0;
    let set_root_index = 5u8;

    ex.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
            set: dregg_cell::program::AuthorizedSet::PublicRoot { set_root_index },
        }]),
    );

    // ACCEPT: slot[5] = the signer's own single-member root; witness = the
    // signer's membership proof. The real MerkleMembership STARK admits it.
    ex.with_ledger_mut(|ledger| {
        let c = ledger.get_mut(&cell).expect("agent cell present");
        c.state.set_field(
            set_root_index as usize,
            dregg_turn::executor::single_member_authorized_root(&signer_pk),
        );
    });
    let ok = ex.submit_action(
        &cc,
        set_field_with_membership(&ex, &cc, 0, field_from_u64(1), &signer_pk),
    );
    assert!(
        ok.is_ok(),
        "SenderAuthorized accept (signer is the sole authorized member) failed: {ok:?}"
    );

    // REJECT: re-seed slot[5] to a STRANGER's root; the signer presents a
    // genuine proof for its OWN key, but there is no path to the stranger's
    // root → the STARK rejects (the non-forgeability tooth).
    let stranger_pk = [0x99u8; 32];
    ex.with_ledger_mut(|ledger| {
        let c = ledger.get_mut(&cell).expect("agent cell present");
        c.state.set_field(
            set_root_index as usize,
            dregg_turn::executor::single_member_authorized_root(&stranger_pk),
        );
    });
    let err = ex.submit_action(
        &cc,
        set_field_with_membership(&ex, &cc, 0, field_from_u64(2), &signer_pk),
    );
    assert!(
        err.is_err(),
        "SenderAuthorized did not reject a signer absent from the authorized-set root"
    );
}
