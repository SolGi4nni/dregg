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
//!   * `encode_branches` — an `AnyOf`/`AllOf` branch the wire cannot carry (a `HeapField` branch,
//!     whose per-branch heap key the one-key-pair header cannot resolve);
//!   * `Err(_) => None` in `LeanConstraintOracle::admits` — the FFI call itself failed;
//!   * `decode_verdict`'s `_ => None` — an unparsed verdict;
//!   * and only LAST, the eleven named class-c arms, which genuinely belong to the trusted-Rust slot
//!     — INCLUDING when one of them appears as an `AnyOf`/`AllOf` BRANCH (`lift_simple` declines
//!     `PreimageGate` / `CountGe` by name, which declines the whole combinator).
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
    ConstraintOracle, RenouncedSet, SimpleStateConstraint, TransitionMeta,
    install_constraint_oracle,
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

/// `collective-choice`'s poll program: the sound quorum gate, gated behind `Immutable{RESOLVED}` so
/// a tally-bump turn (which leaves `RESOLVED` untouched and carries no witness) passes on the cheap
/// branch. `CountGe` is class-c on both sides, so `encode_branches` declines the whole combinator —
/// exactly the `None` this declining oracle produces.
fn poll_quorum_gate() -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable {
                index: RESOLVED_SLOT,
            },
            SimpleStateConstraint::CountGe {
                threshold: 2,
                set_commitment_slot: VOTER_SET_COMMITMENT_SLOT,
            },
        ],
    }
}

/// The poll cell's `RESOLVED` flag slot (`collective_choice::RESOLVED_SLOT`). Restated rather than
/// imported: `dregg-cell` sits far below `collective-choice` and must not depend on it. The value is
/// incidental to what this pins — the CLASS of the combinator, not the poll's slot map.
const RESOLVED_SLOT: u8 = 7;
/// The poll cell's voter-set commitment slot (`collective_choice::VOTER_SET_COMMITMENT_SLOT`).
const VOTER_SET_COMMITMENT_SLOT: u8 = 1;

/// ⚑ **THE COMBINATOR ITSELF REACHES THE TRUSTED-RUST SLOT.** Before the branch recursion in
/// `constraint_in_lean_subset`, this shape was claimed for the Lean subset, the marshaller declined
/// it (no `countGe` branch atom exists on the deployed wire), and the disposition refused it
/// `ConstraintOracleUnavailable` **naming the whole `AnyOf`** — which is why the live DreggNet
/// Council opened proposals (its own cell program is `Monotonic` + `WriteOnce`, all Lean-routed) and
/// then refused every ballot cast against the poll cell.
///
/// ⚠ WHAT THIS BINARY CAN AND CANNOT SAY. The oracle here declines EVERYTHING, so each branch atom
/// is also declined — and `Immutable` is a genuine Lean-subset constraint, so it fails closed on its
/// own, correctly. This test therefore pins the CLASS of the combinator, not the ballot's outcome:
/// the disjunction is not refused as an undecided subset constraint. That the ballot LANDS is pinned
/// against the REAL Lean oracle in `exec-lean/tests/combinator_class_c_branch_poles.rs`, and on the
/// live surface by `dreggnet-web/tests/catalog.rs::a_council_propose_vote_enact_plays_through_the_catalog`.
#[test]
fn a_combinator_over_a_class_c_branch_is_not_refused_as_an_undecided_subset() {
    install();
    let before = CONSULTED.load(Ordering::SeqCst);

    let gate = poll_quorum_gate();
    let program = CellProgram::Predicate(vec![gate.clone()]);
    let mut old = CellState::new(0);
    old.fields[RESOLVED_SLOT as usize] = field_from_u64(0);
    let mut new = CellState::new(0);
    new.fields[RESOLVED_SLOT as usize] = field_from_u64(0);
    // A tally bump on another slot — the ballot's real effect.
    new.fields[8] = field_from_u64(1);

    let result = program.evaluate(&new, Some(&old), None);

    assert!(
        CONSULTED.load(Ordering::SeqCst) > before,
        "the oracle seam was never reached — this test would pass vacuously"
    );
    assert!(
        !matches!(
            &result,
            Err(ProgramError::ConstraintOracleUnavailable { constraint }) if constraint == &gate
        ),
        "the AnyOf carrying a class-c CountGe branch must reach the Rust disjunction evaluator (the \
         trusted-Rust slot, exactly as AnyOfBound does), never be refused as a Lean-subset \
         constraint the marshaller declined; got {result:?}"
    );
}

/// ⚑ **POLE B — AND AN UNEARNED RESOLVE IS STILL REFUSED.** Falling through to the trusted-Rust slot
/// is not a blanket admit: flip `RESOLVED` (closing the `Immutable` branch) with no exhibited voter
/// set and the disjunction has no open path, so the turn is REFUSED. If this ever reads `Ok`, the
/// fall-through has become the permissive fallback it must never be.
#[test]
fn the_same_combinator_still_refuses_a_resolve_with_no_exhibited_voter_set() {
    install();
    let before = CONSULTED.load(Ordering::SeqCst);

    let program = CellProgram::Predicate(vec![poll_quorum_gate()]);
    let mut old = CellState::new(0);
    old.fields[RESOLVED_SLOT as usize] = field_from_u64(0);
    let mut new = CellState::new(1);
    // The forgery: arm RESOLVED without exhibiting a distinct-voter set.
    new.fields[RESOLVED_SLOT as usize] = field_from_u64(1);

    let result = program.evaluate(&new, Some(&old), None);

    assert!(
        CONSULTED.load(Ordering::SeqCst) > before,
        "the oracle seam was never reached — this test would pass vacuously"
    );
    assert!(
        result.is_err(),
        "arming RESOLVED with no exhibited voter set must be REFUSED — the trusted-Rust slot \
         decides this constraint, it does not wave it through; got {result:?}"
    );
}
