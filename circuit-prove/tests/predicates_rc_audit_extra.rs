//! ADVERSARIAL extras for the RELATIONAL predicate AIR — the isolation teeth the shipped
//! `predicates_relational_compound_emit_gate.rs` does not carry.
//!
//! ⚑ RE-WELDED 2026-07-26. This file carried a 91-constraint / 59-column copy of the relational
//! descriptor. `127a0d2d9` closed the relational `>=` RANGE field-wrap forgery by bounding
//! VALUE_A/VALUE_B < 2^29 — 91 constraints -> 219, 59 columns -> 119 — and updated the shipped
//! gate and `circuit/src/dsl/predicates/relational.rs` while leaving this sibling on the
//! pre-fix bytes. So these teeth were biting a descriptor with the forgery still open, and
//! `scripts/check-emit-gate-weld.py` said so. The golden below is now byte-identical to the Lean
//! `#guard` in `metatheory/Dregg2/Circuit/Emit/PredicatesRelationalCompoundEmit.lean`, and the
//! witness carries the value-bit decompositions the fix added.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_2_to_1;

/// Read from the emitted artifact. ⚑ The line this replaces said "there is no descriptor artifact
/// for this name to `include_str!`" — true when written, false since 2026-08-06, when
/// `relational-predicate.json` was routed through `EmitByName.lean`. `check-emit-gate-weld.py`
/// welded the two copies to each other; there is now one object, so there is nothing to weld.
const RELATIONAL_GOLDEN: &str =
    include_str!("../../circuit/descriptors/by-name/relational-predicate.json");

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

/// The honest relational witness: `value_a >= value_b` (100 >= 40, diff = 60, range mode).
/// Columns follow the shipped gate's `relational_row`: diff bits at 5..35, and — added by the
/// field-wrap fix — the value_a / value_b bit decompositions at 45..75 and 75..105 that bound
/// both operands below 2^29.
fn relational_row() -> Vec<BabyBear> {
    let (va, ba, vb, bb) = (100u32, 7u32, 40u32, 9u32);
    let diff = va - vb; // 60, GreaterOrEqual
    let mut r = vec![BabyBear::ZERO; 119];
    r[0] = BabyBear::new(va);
    r[1] = BabyBear::new(ba);
    r[2] = BabyBear::new(vb);
    r[3] = BabyBear::new(bb);
    r[4] = BabyBear::new(diff);
    for i in 0..30 {
        r[5 + i] = BabyBear::new((diff >> i) & 1);
        r[45 + i] = BabyBear::new((va >> i) & 1);
        r[75 + i] = BabyBear::new((vb >> i) & 1);
    }
    r[36] = BabyBear::ONE; // result_bit
    r[37] = BabyBear::ONE; // range_flag
    r[41] = hash_2_to_1(BabyBear::new(va), BabyBear::new(ba)); // commitment_a
    r[42] = hash_2_to_1(BabyBear::new(vb), BabyBear::new(bb)); // commitment_b
    r[43] = BabyBear::ONE; // commit_verify_flag (deployed posture)
    r
}

/// Honest baseline: proves and verifies (non-vacuity floor for THIS tamper).
#[test]
fn extra_relational_honest_accepts() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let r = relational_row();
    assert_eq!(
        desc.trace_width,
        r.len(),
        "the golden and this witness must agree on trace width"
    );
    let trace = vec![r.clone(), r.clone(), r.clone(), r.clone()];
    let pis = vec![r[41], r[42], BabyBear::ONE];
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest relational must accept"
    );
}

/// C7 ISOLATION: flip diff_bit_0 (col 5) from 0 to 1. diff=60 has bit0=0, so the recomposition
/// Sum 2^i*bit_i becomes 61 != 60 = diff -> C7 bites. The bit stays binary (C6 holds), the high bit
/// stays clear (C8 holds), diff itself unchanged (C9/C10 gated off). ONLY C7 can reject.
#[test]
fn extra_relational_broken_recomposition_refuses() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let base = relational_row();
    // sanity: bit 0 of diff (60) is 0, so setting it to 1 is a genuine recomposition break.
    assert_eq!(base[5], BabyBear::ZERO, "diff_bit_0 of 60 must be 0");
    let mut bad = base.clone();
    bad[5] = BabyBear::ONE; // recompose -> 61, diff still 60
    let trace = vec![bad.clone(), bad.clone(), bad.clone(), bad.clone()];
    let pis = vec![base[41], base[42], BabyBear::ONE];
    assert!(
        rejects(&desc, &trace, &pis),
        "a bit-decomposition that does not recompose to diff must be REJECTED (C7)"
    );
}
