//! ONE INPUT, ONE VERDICT — the affine accumulator over the real `CellProgram::evaluate` path.
//!
//! `eval.rs::affine_sum` / `affine_delta_sum` accumulated `Σ kᵢ·xᵢ` in an `i128` with an
//! unchecked `sum += (k as i128) * x`. Outside `±2^127` that WRAPS, and a wrapped-negative sum
//! ADMITS an `AffineLe` that the Lean semantics REFUSE — on both levels of the Lean side:
//! `Dregg2/Exec/Program.lean::affineSum` (the abstract model) and
//! `Dregg2/Exec/DeployedConstraint.lean::affineSum` (the model the installed oracle actually
//! runs) are BOTH exact over unbounded `Int`.
//!
//! MEASURED 2026-07-28 on `AffineLe { terms: [(i64::MAX, 0), (i64::MAX, 1)], c: 0 }` with both
//! slots at `u64::MAX` — the input already pinned in `eval.rs` — one input, three verdicts:
//!
//! | build                                  | verdict BEFORE                  | AFTER    |
//! |----------------------------------------|---------------------------------|----------|
//! | wasm32-wasip1, release                 | **ADMIT**                       | REFUSE   |
//! | aarch64-apple-darwin, release          | `ConstraintOracleUnavailable`   | same     |
//! | aarch64-apple-darwin, debug             | **PANIC** (add with overflow)   | REFUSE   |
//!
//! Lean says REFUSE (the exact sum is `≈ 3.40·10^38 > 0`). The wasm row is not hypothetical: it
//! is the browser light client and the SP1 zkVM guest, which install no constraint oracle and so
//! run this evaluator for EVERY constraint, with no marshalling envelope in front of it.
//!
//! ## Why this binary is the guest path
//!
//! `dregg-cell`'s own integration tests install no oracle, and
//! `constraint_subset_fails_closed_without_oracle()` is `false` in a debug build — which is the
//! same disposition wasm32 and the zkVM guest have permanently. So these poles exercise exactly
//! the code the browser runs. The first assertion in each test PINS that, loudly, rather than
//! letting a differently-configured build pass vacuously.
//!
//! MUTATION CANARY: put the accumulator back to `i128` (`let mut sum: i128 = 0; sum += (*k as
//! i128) * x`) and `exploit_*` go red — as an overflow PANIC in a debug run, as an ADMIT under
//! `--release`/wasm. Make it a CHECKED `i128` instead and `intermediate_overflow_*` go red.

use dregg_cell::program::constraint_subset_fails_closed_without_oracle;
use dregg_cell::{CellProgram, CellState, ProgramError, StateConstraint, field_from_u64};

/// This binary must be the configuration in which the Rust guest evaluator DECIDES — the one
/// wasm32 and the SP1 zkVM guest are permanently in. If it ever is not, every pole below would
/// be answering a different question, so say so instead of passing.
fn assert_guest_path() {
    assert!(
        !constraint_subset_fails_closed_without_oracle(),
        "this test binary must be built where the Rust guest evaluator decides the Lean subset \
         (debug / wasm32 / zkVM). In a native RELEASE build the no-oracle gate refuses the whole \
         subset up front and these poles measure the gate, not the accumulator."
    );
    assert!(
        !dregg_cell::program::constraint_oracle_installed(),
        "no constraint oracle may be installed in this binary — the point is to exercise the \
         hand-written Rust accumulator that wasm32 and the zkVM guest run"
    );
}

fn state_with(vals: &[(usize, u64)]) -> CellState {
    let mut s = CellState::new(0);
    for (i, v) in vals {
        s.fields[*i] = field_from_u64(*v);
    }
    s
}

fn verdict(
    constraint: StateConstraint,
    old: &CellState,
    new: &CellState,
) -> Result<(), ProgramError> {
    CellProgram::Predicate(vec![constraint]).evaluate(new, Some(old), None)
}

fn assert_refused(what: &str, r: Result<(), ProgramError>) {
    match r {
        Err(ProgramError::ConstraintViolated { .. }) => {}
        other => {
            panic!("{what}: expected the Lean verdict REFUSE (ConstraintViolated), got {other:?}")
        }
    }
}

fn assert_admitted(what: &str, r: Result<(), ProgramError>) {
    assert!(
        r.is_ok(),
        "{what}: Lean ADMITS this constraint; the evaluator must too, got {r:?}"
    );
}

/// Eight `2^62` coefficients over eight `2^63` slots: the exact sum is `8·2^125 = 2^128`, which
/// an `i128` accumulator reduces to EXACTLY ZERO.
fn two_pow_128_terms() -> Vec<(i64, u8)> {
    (0..8u8).map(|i| (1i64 << 62, i)).collect()
}

fn two_pow_128_state() -> CellState {
    let vals: Vec<(usize, u64)> = (0..8).map(|i| (i, 1u64 << 63)).collect();
    state_with(&vals)
}

// ── REFUSE pole: the exact sum exceeds the bound, so Lean refuses ───────────────────────────

#[test]
fn exploit_affine_le_pinned_input_is_refused() {
    assert_guest_path();
    let new = state_with(&[(0, u64::MAX), (1, u64::MAX)]);
    assert_refused(
        "AffineLe [(i64::MAX,0),(i64::MAX,1)] <= 0 over two u64::MAX slots",
        verdict(
            StateConstraint::AffineLe {
                terms: vec![(i64::MAX, 0), (i64::MAX, 1)],
                c: 0,
            },
            &CellState::new(0),
            &new,
        ),
    );
}

#[test]
fn exploit_affine_le_two_pow_128_is_refused() {
    assert_guest_path();
    assert_refused(
        "AffineLe summing to exactly 2^128 <= 0",
        verdict(
            StateConstraint::AffineLe {
                terms: two_pow_128_terms(),
                c: 0,
            },
            &CellState::new(0),
            &two_pow_128_state(),
        ),
    );
}

#[test]
fn exploit_affine_eq_two_pow_128_is_refused() {
    assert_guest_path();
    // `2^128 == 0` only in `i128`. In ℤ it is not, so Lean refuses.
    assert_refused(
        "AffineEq summing to exactly 2^128 == 0",
        verdict(
            StateConstraint::AffineEq {
                terms: two_pow_128_terms(),
                c: 0,
            },
            &CellState::new(0),
            &two_pow_128_state(),
        ),
    );
}

#[test]
fn exploit_affine_delta_le_two_pow_128_is_refused() {
    assert_guest_path();
    // Same shape over the per-field DELTAS — the multi-field rate gate the Descent's
    // `DICE_BLOW_METHOD` and every treasury outflow budget ride on.
    assert_refused(
        "AffineDeltaLe whose delta sum is exactly 2^128 <= 0",
        verdict(
            StateConstraint::AffineDeltaLe {
                terms: two_pow_128_terms(),
                c: 0,
            },
            &CellState::new(0),
            &two_pow_128_state(),
        ),
    );
}

// ── ADMIT pole: a legitimate constraint must still be admitted ──────────────────────────────

#[test]
fn ordinary_affine_constraints_still_admit_and_still_refuse() {
    assert_guest_path();
    // Lean's own worked examples, `Dregg2/Exec/Program.lean:1027-1035` and `:1052`.
    assert_admitted(
        "price band 2*bid - ask <= 100 at bid=60 ask=40",
        verdict(
            StateConstraint::AffineLe {
                terms: vec![(2, 0), (-1, 1)],
                c: 100,
            },
            &CellState::new(0),
            &state_with(&[(0, 60), (1, 40)]),
        ),
    );
    assert_refused(
        "price band 2*bid - ask <= 100 at bid=90 ask=40",
        verdict(
            StateConstraint::AffineLe {
                terms: vec![(2, 0), (-1, 1)],
                c: 100,
            },
            &CellState::new(0),
            &state_with(&[(0, 90), (1, 40)]),
        ),
    );
    assert_admitted(
        "conservation inp - out == 0 at 7/7",
        verdict(
            StateConstraint::AffineEq {
                terms: vec![(1, 0), (-1, 1)],
                c: 0,
            },
            &CellState::new(0),
            &state_with(&[(0, 7), (1, 7)]),
        ),
    );
    assert_refused(
        "conservation inp - out == 0 at 7/6",
        verdict(
            StateConstraint::AffineEq {
                terms: vec![(1, 0), (-1, 1)],
                c: 0,
            },
            &CellState::new(0),
            &state_with(&[(0, 7), (1, 6)]),
        ),
    );
    assert_admitted(
        "combined outflow budget out_a + out_b <= 5 at deltas 2 + 3",
        verdict(
            StateConstraint::AffineDeltaLe {
                terms: vec![(1, 0), (1, 1)],
                c: 5,
            },
            &state_with(&[(0, 10), (1, 10)]),
            &state_with(&[(0, 12), (1, 13)]),
        ),
    );
    assert_refused(
        "combined outflow budget out_a + out_b <= 5 at deltas 4 + 3",
        verdict(
            StateConstraint::AffineDeltaLe {
                terms: vec![(1, 0), (1, 1)],
                c: 5,
            },
            &state_with(&[(0, 10), (1, 10)]),
            &state_with(&[(0, 14), (1, 13)]),
        ),
    );
}

#[test]
fn intermediate_overflow_with_an_in_range_total_is_still_admitted() {
    assert_guest_path();
    // THE POLE THAT RULES OUT "checked i128, refuse on overflow". The running total leaves
    // `i128` twice, but the exact sum is `−2·(2^64−1) ≤ 0`, which Lean ADMITS. A checker that
    // refuses this is as broken as one that wraps the exploit above — and saturating here would
    // INVENT an answer on precisely the shape (`AffineLe` over balance-like slots) where an
    // invented answer moves value.
    let wide = vec![(i64::MAX, 0), (i64::MAX, 1), (i64::MIN, 2), (i64::MIN, 3)];
    let saturated = state_with(&[(0, u64::MAX), (1, u64::MAX), (2, u64::MAX), (3, u64::MAX)]);
    assert_admitted(
        "AffineLe whose i128 intermediates overflow but whose exact sum is negative",
        verdict(
            StateConstraint::AffineLe {
                terms: wide.clone(),
                c: 0,
            },
            &CellState::new(0),
            &saturated,
        ),
    );
    assert_admitted(
        "AffineDeltaLe whose i128 intermediates overflow but whose exact delta sum is negative",
        verdict(
            StateConstraint::AffineDeltaLe { terms: wide, c: 0 },
            &CellState::new(0),
            &saturated,
        ),
    );
}

// ── The sibling in the same family: MonotonicSequence's diagnostic ──────────────────────────

#[test]
fn monotonic_sequence_at_u64_max_refuses_instead_of_panicking() {
    assert_guest_path();
    // `DeployedConstraint.lean`'s `monotonicSequence` arm is `n ≠ (o + 1) % two64`, so the
    // successor IS modular and `u64::MAX → 0` is the admitted step. But the REFUSAL path used a
    // bare `old_seq + 1` to build its message, which panicked under `overflow-checks` (every
    // debug build) at exactly this `old_seq` — the same three-verdict family as the accumulator.
    let old = state_with(&[(0, u64::MAX)]);
    assert_refused(
        "MonotonicSequence u64::MAX -> 5",
        verdict(
            StateConstraint::MonotonicSequence { seq_index: 0 },
            &old,
            &state_with(&[(0, 5)]),
        ),
    );
    assert_admitted(
        "MonotonicSequence u64::MAX -> 0 (the Lean-sanctioned modular successor)",
        verdict(
            StateConstraint::MonotonicSequence { seq_index: 0 },
            &old,
            &state_with(&[(0, 0)]),
        ),
    );
}
