//! # The emit-from-Lean ROUND-TRIP GATE — arithmetic COMPARISON predicates `≤`/`>`/`<`/`≠`/InRange.
//!
//! The `≥` sibling gate is `predicates_arithmetic_emit_gate.rs`. Their descriptors are AUTHORED and
//! byte-pinned in `metatheory/Dregg2/Circuit/Emit/Predicates{Le,Gt,Lt,Neq,InRange}Emit.lean`
//! (`emitVmJson2` `#guard`), regenerated onto disk by `scripts/emit-descriptors.sh` (via
//! `EmitByName.lean`), and served from those exact bytes by `dregg_circuit::descriptor_by_name`.
//! This gate drives each through the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2`:
//!
//!   * the DISPATCHED bytes carry the Lean-emitted WELDED shape — the welded width AND both Poseidon2
//!     value↔fact weld legs (the structural anti-fork gate);
//!   * an HONEST witness (built by the production `predicate_comparison_witness` builders) proves and
//!     re-verifies — ACCEPT;
//!   * a VIOLATING witness (comparison false) is REFUSED — the load-bearing range tooth (`≤`/`>`/`<`/
//!     InRange) or nonzero-inverse tooth (`≠`) bites (real UNSAT, non-vacuous);
//!   * a FORGED public input (`threshold`/`lo`/`hi`/`fact_commitment`) is REFUSED at verify (the PI
//!     pins C1/C2).
//!
//! The value↔fact FORGERY falsifier (a forged value presented against an honest commitment) lives in
//! `circuit/tests/predicate_comparison_fact_weld_canary.rs`.
//!
//! This is the Rust face of the Lean Rung-2 no-forgery theorems
//! (`{le,gt,lt}Bad_not_satisfies`, `neqBad_not_satisfies`, `inBad_not_satisfies`) and the weld
//! theorems (`predicate{Le,Gt,Lt,Neq,InRange}_value_forge_rejected`).

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TID_P2, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding};
use dregg_circuit::predicate_comparison_witness::{
    IR_WIDTH, NEQ_WIDTH, OS_WIDTH, PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_INRANGE_NAME,
    PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME, PREDICATE_ARITH_NEQ_NAME,
    predicate_gt_witness, predicate_inrange_witness, predicate_le_witness, predicate_lt_witness,
    predicate_neq_witness,
};
use std::panic::AssertUnwindSafe;

/// The fact identity shared by every test here.
fn fact() -> FactBinding {
    FactBinding {
        predicate_sym: BabyBear::new(0x9E),
        term1: BabyBear::new(0x11),
        term2: BabyBear::new(0x22),
        state_root: BabyBear::new(0x57A7E),
    }
}

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

/// The number of Poseidon2 chip lookups in a dispatched descriptor (the two weld legs).
fn weld_legs(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count()
}

const HEIGHT: usize = 4;

/// A REAL, non-zero per-presentation blinding — the DEFAULT every witness here is built under, so
/// the round-trips run in the deployed (blinded) posture. Not a `const` because `BabyBear::new` is
/// not a `const fn`.
fn test_blinding() -> Blinding {
    Blinding(BabyBear::new(0xB11D1))
}

/// THE STRUCTURAL ANTI-FORK GATE: every dispatched sibling carries the Lean-emitted welded shape.
/// A prose claim that these descriptors are welded is what let the family sit unwelded while every
/// by-name test stayed green; this asserts it on the SERVED bytes.
#[test]
fn every_sibling_dispatches_with_both_weld_legs() {
    for (name, width, pis) in [
        (PREDICATE_ARITH_LE_NAME, OS_WIDTH, 2),
        (PREDICATE_ARITH_GT_NAME, OS_WIDTH, 2),
        (PREDICATE_ARITH_LT_NAME, OS_WIDTH, 2),
        (PREDICATE_ARITH_NEQ_NAME, NEQ_WIDTH, 2),
        (PREDICATE_ARITH_INRANGE_NAME, IR_WIDTH, 3),
    ] {
        let desc = descriptor_by_name(name).unwrap_or_else(|| panic!("{name} dispatches"));
        assert_eq!(desc.name, name);
        assert_eq!(desc.trace_width, width, "{name}: Lean-emitted welded width");
        assert_eq!(desc.public_input_count, pis, "{name}: PI count");
        assert_eq!(
            weld_legs(&desc),
            2,
            "{name}: the deployed descriptor must carry BOTH weld legs (leg 1: hash_fact -> \
             FACT_HASH, leg 2: hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0]) -> \
             FACT_COMMITMENT) — without \
             them the predicate proof does not bind the compared value to the committed fact"
        );
    }
}

#[test]
fn le_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_LE_NAME).expect("≤ dispatches");
    assert_eq!(desc.trace_width, OS_WIDTH);
    assert_eq!(desc.public_input_count, 2);
    // ACCEPT: 40 ≤ 100.
    let (t, p) = predicate_le_witness(40, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "40 ≤ 100 must prove+verify");
    // REJECT: 110 > 100 (range tooth).
    let (bt, bp) = predicate_le_witness(110, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "110 ≤ 100 must REJECT");
    // REJECT: forged public threshold (C1).
    assert!(
        rejects(&desc, &t, &[BabyBear::new(41), p[1]]),
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
    let (t, p) = predicate_gt_witness(101, 40, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "101 > 40 must prove+verify");
    // equality is NOT strictly greater.
    let (bt, bp) = predicate_gt_witness(40, 40, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "40 > 40 must REJECT");
    // below also rejects.
    let (bt2, bp2) = predicate_gt_witness(30, 40, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(rejects(&desc, &bt2, &bp2), "30 > 40 must REJECT");
}

#[test]
fn lt_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_LT_NAME).expect("< dispatches");
    let (t, p) = predicate_lt_witness(40, 101, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "40 < 101 must prove+verify");
    let (bt, bp) = predicate_lt_witness(101, 101, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "101 < 101 must REJECT");
    let (bt2, bp2) = predicate_lt_witness(150, 101, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(rejects(&desc, &bt2, &bp2), "150 < 101 must REJECT");
}

#[test]
fn neq_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NEQ_NAME).expect("≠ dispatches");
    assert_eq!(desc.trace_width, NEQ_WIDTH);
    // ACCEPT: genuine inequalities (real field inverse).
    let (t, p) = predicate_neq_witness(41, 40, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "41 ≠ 40 must prove+verify");
    let (t2, p2) = predicate_neq_witness(1_000_000, 7, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(accepts(&desc, &t2, &p2), "1000000 ≠ 7 must prove+verify");
    // REJECT: equal value has diff = 0, no inverse (nonzero tooth UNSAT).
    let (bt, bp) = predicate_neq_witness(40, 40, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(
        rejects(&desc, &bt, &bp),
        "40 ≠ 40 must REJECT (nonzero tooth)"
    );
}

#[test]
fn inrange_round_trip() {
    let desc = descriptor_by_name(PREDICATE_ARITH_INRANGE_NAME).expect("InRange dispatches");
    assert_eq!(desc.trace_width, IR_WIDTH);
    assert_eq!(desc.public_input_count, 3);
    // ACCEPT: interior and both inclusive boundaries.
    let (t, p) = predicate_inrange_witness(40, 10, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(accepts(&desc, &t, &p), "10 ≤ 40 ≤ 100 must prove+verify");
    let (lo_t, lo_p) =
        predicate_inrange_witness(10, 10, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(
        accepts(&desc, &lo_t, &lo_p),
        "value = lo must ACCEPT (inclusive)"
    );
    let (hi_t, hi_p) =
        predicate_inrange_witness(100, 10, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(
        accepts(&desc, &hi_t, &hi_p),
        "value = hi must ACCEPT (inclusive)"
    );
    // REJECT: below lo (low tooth) and above hi (high tooth).
    let (bt, bp) = predicate_inrange_witness(5, 10, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(rejects(&desc, &bt, &bp), "5 < 10 must REJECT (low tooth)");
    let (bt2, bp2) =
        predicate_inrange_witness(150, 10, 100, fact(), test_blinding(), HEIGHT).unwrap();
    assert!(
        rejects(&desc, &bt2, &bp2),
        "150 > 100 must REJECT (high tooth)"
    );
    // REJECT: forged public lo / hi (C1lo / C1hi).
    assert!(
        rejects(&desc, &t, &[BabyBear::new(41), BabyBear::new(100), p[2]]),
        "forged lo must REJECT (C1lo)"
    );
    assert!(
        rejects(&desc, &t, &[BabyBear::new(10), BabyBear::new(39), p[2]]),
        "forged hi must REJECT (C1hi)"
    );
}
