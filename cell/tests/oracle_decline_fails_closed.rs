//! Constraint-oracle subset twin (#2), the DECLINE half: an installed oracle that returns `None`
//! must NOT hand a Lean-subset decision back to the unverified Rust `match`.
//!
//! `evaluate_constraint_full` used to read `admits(..) == None` as "a class-c
//! witness/crypto/executor-state variant" and fall straight through to the 77-arm Rust evaluator. That
//! reading is FALSE. `dregg-exec-lean::constraint_oracle` returns `None` from six places, only one of
//! which is class-c:
//!
//!   * `encode_terms` — affine terms outside the `i128`-exact envelope (`MAX_AFFINE_TERMS` = 1024,
//!     `MAX_AFFINE_COEFF` = 2^32);
//!   * `encode_u64_list` / `encode_u8_list` / the inline `len() > MAX_LIST` guards — an over-long
//!     allowlist, edge set, transition table or member set;
//!   * `coll_cell_count` — a collection read past `MAX_COLL_CELLS`;
//!   * `encode_branches` — an `AnyOf`/`AllOf` branch the wire cannot carry (a `HeapField` branch);
//!   * `Err(_) => None` in `LeanConstraintOracle::admits` — the FFI call itself failed;
//!   * `decode_verdict`'s `_ => None` — an unparsed verdict;
//!   * and only LAST, the eleven named class-c arms, which genuinely belong to the trusted-Rust slot.
//!
//! The first six are Lean-SUBSET constraints, so falling through ran the twin. The sharpest case is
//! `AffineLe`: `eval.rs::affine_sum` accumulates with an unchecked `sum += (k as i128) * x`, so
//! outside the envelope the sum WRAPS, and a wrapped-negative sum admits an `AffineLe` that Lean's
//! `affineSum` (over unbounded `Int`) refuses. The envelope's own comment in `constraint_oracle.rs`
//! reads "no silent disagreement, no wrapped-sum admit" — it described exactly what it caused.
//!
//! This test installs a DECLINING oracle (every `admits` returns `None`, the shape every one of those
//! six paths produces) and pins that the Lean subset now fails closed. It is its own integration
//! binary because `install_constraint_oracle` is a process-wide `OnceLock`.
//!
//! MUTATION CANARY: restore the old fall-through (delete the `undecided_subset_disposition` call in
//! the oracle-installed branch of `evaluate_constraint_full`) and both `fails_closed` tests below go
//! RED — the satisfied `FieldEquals` is admitted by the Rust twin, and the out-of-envelope `AffineLe`
//! reaches `affine_sum` and panics on `i128` overflow in this debug build (it WRAPS AND ADMITS in the
//! release build a node actually runs).

use std::sync::atomic::{AtomicUsize, Ordering};

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::{
    ConstraintOracle, RenouncedSet, TransitionMeta, install_constraint_oracle,
};
use dregg_cell::{CellProgram, CellState, ProgramError, StateConstraint, field_from_u64};

/// Counts how many times the oracle was consulted, so a test cannot pass because the constraint never
/// reached the oracle seam at all.
static CONSULTED: AtomicUsize = AtomicUsize::new(0);

/// An oracle that is INSTALLED but declines everything — the shape produced by an envelope decline, an
/// FFI failure, or an unparsed verdict.
struct DecliningOracle;

impl ConstraintOracle for DecliningOracle {
    fn admits(
        &self,
        _constraint: &StateConstraint,
        _new_state: &CellState,
        _old_state: Option<&CellState>,
        _ctx: Option<&EvalContext>,
        _meta: &TransitionMeta,
    ) -> Option<Result<(), ProgramError>> {
        CONSULTED.fetch_add(1, Ordering::SeqCst);
        None
    }
}

fn install() {
    // `OnceLock`: the first caller wins, later ones get `Err`. Both are fine here — all tests in this
    // binary want the same declining oracle installed.
    let _ = install_constraint_oracle(Box::new(DecliningOracle));
    assert!(
        dregg_cell::program::constraint_oracle_installed(),
        "the declining oracle must be installed, or this test proves nothing"
    );
}

#[test]
fn declined_lean_subset_constraint_fails_closed() {
    install();
    let before = CONSULTED.load(Ordering::SeqCst);

    // A SATISFIED, pure, Lean-subset constraint. The Rust twin admits it; only Lean is allowed to.
    let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(7),
    }]);
    let mut state = CellState::new(0);
    state.fields[0] = field_from_u64(7);

    let result = program.evaluate(&state, None, None);

    assert!(
        CONSULTED.load(Ordering::SeqCst) > before,
        "the oracle seam was never reached — this test would pass vacuously"
    );
    assert!(
        matches!(
            result,
            Err(ProgramError::ConstraintOracleUnavailable { .. })
        ),
        "an installed oracle that DECLINED a Lean-subset constraint must fail closed, not fall \
         through to the unverified Rust match; got {result:?}"
    );
}

#[test]
fn declined_out_of_envelope_affine_fails_closed_instead_of_wrapping() {
    install();
    let before = CONSULTED.load(Ordering::SeqCst);

    // THE DIVERGENCE. Two terms at `i64::MAX` over two `u64::MAX` slots: the true sum is ~2^128, so
    // `AffineLe { c: 0 }` is FALSE and Lean's unbounded-`Int` `affineSum` refuses. `|k| > 2^32` puts
    // it outside the marshalling envelope, so the oracle declines — and the Rust `affine_sum`
    // accumulator overflows `i128`, wrapping to a NEGATIVE sum that satisfies `sum <= 0` and ADMITS.
    let program = CellProgram::Predicate(vec![StateConstraint::AffineLe {
        terms: vec![(i64::MAX, 0), (i64::MAX, 1)],
        c: 0,
    }]);
    let mut state = CellState::new(0);
    state.fields[0] = field_from_u64(u64::MAX);
    state.fields[1] = field_from_u64(u64::MAX);

    let result = program.evaluate(&state, None, None);

    assert!(
        CONSULTED.load(Ordering::SeqCst) > before,
        "the oracle seam was never reached — this test would pass vacuously"
    );
    assert!(
        matches!(
            result,
            Err(ProgramError::ConstraintOracleUnavailable { .. })
        ),
        "an out-of-envelope AffineLe must fail closed before it can reach the wrapping Rust \
         accumulator; got {result:?}"
    );
}

#[test]
fn declined_class_c_constraint_still_falls_through_to_the_trusted_rust_slot() {
    install();
    let before = CONSULTED.load(Ordering::SeqCst);

    // NON-DEGRADATION: the eleven class-c arms are the NAMED trusted-Rust slot and must keep reaching
    // the hand-written evaluator when the oracle declines them. `Renounced` needs a witness the empty
    // bundle does not carry, so the Rust evaluator's own fail-closed sentinel is what we must see —
    // NOT `ConstraintOracleUnavailable`, which would mean the subset gate had swallowed class-c too.
    let program = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::PublicRoot { set_root_index: 0 },
    }]);
    let state = CellState::new(0);

    let result = program.evaluate(&state, None, None);

    assert!(
        CONSULTED.load(Ordering::SeqCst) > before,
        "the oracle seam was never reached — this test would pass vacuously"
    );
    assert!(
        !matches!(
            result,
            Err(ProgramError::ConstraintOracleUnavailable { .. })
        ),
        "a class-c constraint must fall through to the trusted Rust slot, not hit the subset \
         fail-closed gate; got {result:?}"
    );
}
