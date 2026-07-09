//! # The emit-from-Lean ROUND-TRIP GATE — arithmetic COMPARISON predicates `≤`/`>`/`<`/`≠`/InRange.
//!
//! The `≥` sibling gate is `predicates_arithmetic_emit_gate.rs`. The hand-STARK deletion left the
//! five comparison ops with NO emitted descriptor (fail-closed); their descriptors are AUTHORED and
//! byte-pinned in `metatheory/Dregg2/Circuit/Emit/Predicates{Le,Gt,Lt,Neq,InRange}Emit.lean`
//! (`emitVmJson2` `#guard`), served from the same `#guard`-pinned goldens via
//! `dregg_circuit::descriptor_by_name`. This gate drives each through the REAL
//! `prove_vm_descriptor2` / `verify_vm_descriptor2`:
//!
//!   * an HONEST witness (built by the production `predicate_comparison_witness` builders) proves and
//!     re-verifies — ACCEPT;
//!   * a VIOLATING witness (comparison false) is REFUSED — the load-bearing range tooth (`≤`/`>`/`<`/
//!     InRange) or nonzero-inverse tooth (`≠`) bites (real UNSAT, non-vacuous);
//!   * a FORGED public input (`threshold`/`lo`/`hi`/`fact_commitment`) is REFUSED at verify (the PI
//!     pins C1/C2).
//!
//! This is the Rust face of the Lean Rung-2 no-forgery theorems
//! (`{le,gt,lt}Bad_not_satisfies`, `neqBad_not_satisfies`, `inBad_not_satisfies`).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::predicate_comparison_witness::{
    PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_INRANGE_NAME, PREDICATE_ARITH_LE_NAME,
    PREDICATE_ARITH_LT_NAME, PREDICATE_ARITH_NEQ_NAME, predicate_gt_witness,
    predicate_inrange_witness, predicate_le_witness, predicate_lt_witness, predicate_neq_witness,
};

/// `true` iff `(trace, pis)` is ACCEPTED end-to-end (prove AND verify succeed).
fn accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Ok(Ok(())))
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR verify fails).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

const HEIGHT: usize = 4;

#[test]
fn le_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_LE_NAME).expect("≤ dispatches");
    assert_eq!(desc.trace_width, 5);
    assert_eq!(desc.public_input_count, 2);
    let fact = BabyBear::new(12345);
    // ACCEPT: 40 ≤ 100.
    let (t, p) = predicate_le_witness(40, 100, fact, HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "40 ≤ 100 must prove+verify");
    // REJECT: 110 > 100 (range tooth).
    let (bt, bp) = predicate_le_witness(110, 100, fact, HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "110 ≤ 100 must REJECT");
    // REJECT: forged public threshold (C1).
    assert!(
        rejects(&desc, &t, &[BabyBear::new(41), fact]),
        "forged threshold must REJECT (C1)"
    );
    // REJECT: forged public fact_commitment (C2).
    assert!(
        rejects(&desc, &t, &[BabyBear::new(100), BabyBear::new(999)]),
        "forged fact must REJECT (C2)"
    );
}

#[test]
fn gt_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_GT_NAME).expect("> dispatches");
    let fact = BabyBear::new(777);
    let (t, p) = predicate_gt_witness(101, 40, fact, HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "101 > 40 must prove+verify");
    // equality is NOT strictly greater.
    let (bt, bp) = predicate_gt_witness(40, 40, fact, HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "40 > 40 must REJECT");
    // below rejects.
    let (bt2, bp2) = predicate_gt_witness(30, 40, fact, HEIGHT).unwrap();
    assert!(rejects(&desc, &bt2, &bp2), "30 > 40 must REJECT");
}

#[test]
fn lt_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_LT_NAME).expect("< dispatches");
    let fact = BabyBear::new(888);
    let (t, p) = predicate_lt_witness(40, 101, fact, HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "40 < 101 must prove+verify");
    let (bt, bp) = predicate_lt_witness(101, 101, fact, HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "101 < 101 must REJECT");
    let (bt2, bp2) = predicate_lt_witness(150, 101, fact, HEIGHT).unwrap();
    assert!(rejects(&desc, &bt2, &bp2), "150 < 101 must REJECT");
}

#[test]
fn neq_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NEQ_NAME).expect("≠ dispatches");
    assert_eq!(desc.trace_width, 6);
    let fact = BabyBear::new(4242);
    // ACCEPT: genuine inequalities (real field inverse).
    let (t, p) = predicate_neq_witness(41, 40, fact, HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "41 ≠ 40 must prove+verify");
    let (t2, p2) = predicate_neq_witness(1_000_000, 7, fact, HEIGHT).unwrap();
    assert!(accepts(&desc, &t2, &p2), "1000000 ≠ 7 must prove+verify");
    // REJECT: equal value has diff = 0, no inverse (nonzero tooth UNSAT).
    let (bt, bp) = predicate_neq_witness(40, 40, fact, HEIGHT).unwrap();
    assert!(
        rejects(&desc, &bt, &bp),
        "40 ≠ 40 must REJECT (nonzero tooth)"
    );
}

#[test]
fn inrange_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_INRANGE_NAME).expect("InRange dispatches");
    assert_eq!(desc.trace_width, 7);
    assert_eq!(desc.public_input_count, 3);
    let fact = BabyBear::new(55);
    // ACCEPT: interior and both inclusive boundaries.
    let (t, p) = predicate_inrange_witness(40, 10, 100, fact, HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "10 ≤ 40 ≤ 100 must prove+verify");
    let (lo_t, lo_p) = predicate_inrange_witness(10, 10, 100, fact, HEIGHT).unwrap();
    assert!(
        accepts(&desc, &lo_t, &lo_p),
        "value = lo must ACCEPT (inclusive)"
    );
    let (hi_t, hi_p) = predicate_inrange_witness(100, 10, 100, fact, HEIGHT).unwrap();
    assert!(
        accepts(&desc, &hi_t, &hi_p),
        "value = hi must ACCEPT (inclusive)"
    );
    // REJECT: below lo (low tooth) and above hi (high tooth).
    let (bt, bp) = predicate_inrange_witness(5, 10, 100, fact, HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "5 < 10 must REJECT (low tooth)");
    let (bt2, bp2) = predicate_inrange_witness(150, 10, 100, fact, HEIGHT).unwrap();
    assert!(
        rejects(&desc, &bt2, &bp2),
        "150 > 100 must REJECT (high tooth)"
    );
    // REJECT: forged public lo / hi (C1lo / C1hi).
    assert!(
        rejects(&desc, &t, &[BabyBear::new(41), BabyBear::new(100), fact]),
        "forged lo must REJECT (C1lo)"
    );
    assert!(
        rejects(&desc, &t, &[BabyBear::new(10), BabyBear::new(39), fact]),
        "forged hi must REJECT (C1hi)"
    );
}
