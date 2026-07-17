//! `DslComparisonRangeSoundnessResidual` — the decisive experiment (2026-07-17, board/lane-C).
//!
//! QUESTION (from the corrected `dregg-dsl/src/lib.rs` doc): the DSL's surviving
//! comparison path — is a field-wrapped negative difference UNSATISFIABLE, or can a
//! wrapped value satisfy it?
//!
//! GROUND TRUTH ESTABLISHED FROM CODE, then pinned here:
//!
//! 1. `gen_air`'s `Constraint::RangeCheck { diff_col, bit_col }` is a TOPOLOGY
//!    DESCRIPTOR (`dregg_dsl_runtime::AirConstraintSet`). NOTHING proves it: its only
//!    consumers are `air_runner.rs` (variant-shape match, then a NATIVE u64
//!    re-derivation via `check_le`) and structural token tests. There is no
//!    `AirConstraintSet -> CircuitDescriptor` converter anywhere in the repo. A
//!    single `bit_col` could not range-check a ~31-bit field difference anyway.
//!
//! 2. The ONLY place a DSL comparison reaches a REAL prover is
//!    `plonky3_runner::drive_inequality`, which hand-builds a `CircuitDescriptor`
//!    ("diff-le") and proves it through the PRODUCTION interpreter
//!    (`dregg_circuit::dsl::dsl_p3_air`). Its constraint system is:
//!        C1: bigger - smaller - diff == 0        (mod p — always satisfiable!)
//!        C2: indicator * (indicator - 1) == 0    (indicator is boolean)
//!        C3: indicator == 0
//!    NO constraint links `indicator` to `diff`, and NO bit decomposition bounds
//!    `diff`. The comparison truth lives entirely in the HONEST WITNESS GENERATOR
//!    (which computes `ir_ok = smaller <= bigger` in native u64 and deliberately
//!    submits an invalid witness to force rejection when false).
//!
//! THE FINDING (proven by `wrapped_negative_difference_forgery_is_ACCEPTED` below):
//! a malicious prover claiming `5 <= 3` with witness `diff = (3 - 5) mod p = p - 2`,
//! `indicator = 0` satisfies ALL constraints — the production p3 prover+verifier
//! ACCEPT the false statement. **The lowering does NOT range-check; a field-wrapped
//! negative difference is SATISFIABLE.** This refutes, at the circuit level, the
//! in-file comment "we cap the diffs to a 30-bit range where this encoding stays
//! sound" — the forgery below uses tiny (far sub-30-bit) operands.
//!
//! Severity scoping (why this is a NAMED soundness gap, not a live production
//! forgery): production circuits that need order comparisons do a genuine 30-bit
//! decomposition with binary-pinned bits and a zeroed top bit
//! (`circuit/src/dsl/committed_threshold.rs`, `derivation.rs` C17/C22,
//! `descriptors.rs` non-membership ordering). The unsound lowering is the
//! DIFFERENTIAL HARNESS's — meaning the harness's Plonky3 "agreement vote" on
//! inequalities validates the witness generator, not the constraints.
//!
//! TEETH CONTRACT:
//! - `honest_le_accepts_through_production_p3` / `honest_false_le_is_rejected_by_harness`
//!   pin that the pipeline is real (non-vacuous) and the harness verdicts track u64 truth.
//! - `wrapped_negative_difference_forgery_is_ACCEPTED` is a CHARACTERIZATION PIN of
//!   the named bug: it asserts the forgery IS accepted today. If someone fixes the
//!   lowering (adds a real bit-decomposition), this test goes RED — that is the
//!   signal to flip this pin into a rejection tooth and upgrade the doc in
//!   `dregg-dsl/src/lib.rs` from NAMED-UNSOUND to PROVEN-SOUND. Do NOT "fix" this
//!   test by deleting it.

use dregg_circuit::dsl::circuit::DslCircuit;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_dsl_differential::plonky3_runner::{Verdict, prove_and_verify};
use dregg_dsl_differential::predicates::Requirement;
use dregg_dsl_runtime::circuit::{
    CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

/// The EXACT "diff-le" descriptor `plonky3_runner::drive_inequality` builds
/// (columns [smaller, bigger, diff, indicator]; constraints C1/C2/C3 as in the
/// module doc above). Reproduced here because the harness keeps its builder
/// private; if the harness's lowering changes shape, update this copy from
/// `plonky3_runner.rs` — the honest-accept test below will catch a divergence
/// that breaks provability.
fn diff_le_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "diff-le".to_string(),
        trace_width: 4,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "smaller".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "bigger".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "diff".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "indicator".into(),
                index: 3,
                kind: ColumnKind::Binary,
            },
        ],
        constraints: vec![
            // C1: bigger - smaller - diff == 0 (mod p)
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![1],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![2],
                    },
                ],
            },
            // C2: indicator is boolean
            ConstraintExpr::Binary { col: 3 },
            // C3: indicator == 0
            ConstraintExpr::Polynomial {
                terms: vec![PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![3],
                }],
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

fn prove_diff_le(smaller: u64, bigger: u64, diff: BabyBear) -> Result<(), String> {
    let dsl = DslCircuit::new(diff_le_descriptor());
    let row = vec![
        BabyBear::from_u64(smaller),
        BabyBear::from_u64(bigger),
        diff,
        BabyBear::ZERO, // indicator = 0: "the subtraction did not wrap" claim
    ];
    let trace = vec![row.clone(), row];
    let pi = vec![BabyBear::from_u64(smaller), BabyBear::from_u64(bigger)];
    // The p3 prover panics on an unsatisfiable trace (the harness catches this
    // the same way); treat a panic as rejection.
    let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_dsl_p3(&dsl, &trace, &pi)
    }));
    match proved {
        Ok(Ok(proof)) => verify_dsl_p3(&dsl, &proof, &pi).map_err(|e| format!("verify: {e}")),
        Ok(Err(e)) => Err(format!("prove: {e}")),
        Err(_) => Err("prove panicked (unsatisfiable trace)".to_string()),
    }
}

/// Non-vacuity pin: the honest lowering of a TRUE `3 <= 5` proves and verifies
/// through the production p3 interpreter.
#[test]
fn honest_le_accepts_through_production_p3() {
    prove_diff_le(3, 5, BabyBear::from_u64(2))
        .expect("honest 3 <= 5 must prove+verify through production dsl_p3_air");
}

/// NON-VACUITY of the forgery rig itself: `prove_diff_le` is NOT an
/// accept-everything harness. An inconsistent `diff` (claiming `3 <= 5` with
/// `diff = 7`, violating C1 `bigger - smaller - diff == 0`) IS rejected. So the
/// acceptance in `wrapped_negative_difference_forgery_is_accepted_known_unsound`
/// is a real property of the constraint system, not a broken test.
#[test]
fn rig_is_not_vacuous_inconsistent_diff_is_rejected() {
    let res = prove_diff_le(3, 5, BabyBear::from_u64(7)); // 5 - 3 != 7
    assert!(
        res.is_err(),
        "the rig must reject a diff violating C1; if this passes, the forgery pin proves nothing"
    );
}

/// Harness-verdict pin: the harness REJECTS a false `5 <= 3` — but note WHY
/// (established from code): its honest witness generator submits a deliberately
/// invalid witness (diff=0, indicator=1), NOT because the constraints encode the
/// comparison. The forgery test below proves the constraints do not.
#[test]
fn honest_false_le_is_rejected_by_harness() {
    let verdict = prove_and_verify(&[Requirement::LessEqualU64(5, 3)])
        .expect("inequality shape is expressible");
    assert!(
        matches!(verdict, Verdict::Reject),
        "harness must reject a false 5 <= 3, got {verdict:?}"
    );
}

/// ⚠ THE CHARACTERIZATION PIN — `DslComparisonRangeSoundnessResidual` is a REAL
/// constraint-level soundness gap, proven live:
///
/// Claim `5 <= 3` with the field-wrapped witness `diff = (3 - 5) mod p = p - 2`,
/// `indicator = 0`. Every constraint (C1 mod-p subtraction, C2 boolean, C3
/// indicator=0) is satisfied, so the PRODUCTION p3 prover+verifier ACCEPT the
/// false statement. There is no bit decomposition bounding `diff` and no
/// algebraic link from `indicator` to `diff`.
///
/// If this test goes RED, the lowering was fixed: flip it into a rejection
/// tooth (assert `is_err`) and upgrade `dregg-dsl/src/lib.rs`'s range-check
/// section from NAMED-UNSOUND to PROVEN. Do not delete.
#[test]
fn wrapped_negative_difference_forgery_is_accepted_known_unsound() {
    let wrapped = BabyBear::new(BABYBEAR_P - 2); // (3 - 5) mod p
    let res = prove_diff_le(5, 3, wrapped);
    assert!(
        res.is_ok(),
        "KNOWN-UNSOUND pin drifted: the wrapped-diff forgery of `5 <= 3` was REJECTED \
         ({res:?}). If the lowering now range-checks, flip this pin into a rejection \
         tooth and upgrade the dregg-dsl doc from NAMED to PROVEN."
    );
}
