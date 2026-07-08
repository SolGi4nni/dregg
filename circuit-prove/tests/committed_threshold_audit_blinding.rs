//! AUDIT-ONLY extra canary (additive): tamper the `blinding` column (col 2), which feeds
//! EXACTLY the arity-2 chip lookup input and NOTHING else (not c3, c4, recomp, bits, or the
//! pins). The genuine `poseidon2_result`/commitment/pi are left as the honest
//! `hash_2_to_1(threshold, blinding_old)`, so the tuple names a chip row for
//! `hash_2_to_1(threshold, blinding_new)` while out0 stays the OLD digest → LogUp UNSAT.
//! This is an isolation the implementer's `forged_poseidon2_result` canary does NOT cover
//! (that one tampered out0/col36; this tampers a chip INPUT).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_2_to_1;

const PRIVATE_VALUE: usize = 0;
const THRESHOLD: usize = 1;
const BLINDING: usize = 2;
const DIFF: usize = 3;
const DIFF_BITS_START: usize = 4;
const COMMITTED_DIFF_BITS: usize = 30;
const THRESHOLD_COMMITMENT: usize = DIFF_BITS_START + COMMITTED_DIFF_BITS; // 34
const FACT_COMMITMENT: usize = THRESHOLD_COMMITMENT + 1; // 35
const POSEIDON2_RESULT: usize = FACT_COMMITMENT + 1; // 36
// value<->fact weld columns (see committed_threshold_emit_gate.rs / CommittedThresholdEmit.lean).
const PREDICATE_SYM: usize = 44;
const STATE_ROOT: usize = 47;
const FACT_HASH: usize = 48;
const FACT_MARK: u32 = 0xFACF;
const CT_WIDTH: usize = 63;

const GOLDEN_JSON: &str = include_str!("committed_threshold_golden.json");

fn honest_row(
    value: BabyBear,
    threshold: BabyBear,
    blinding: BabyBear,
    _ignored_fact_commitment: BabyBear,
) -> (Vec<BabyBear>, [BabyBear; 2]) {
    let diff = value - threshold;
    let commitment = hash_2_to_1(threshold, blinding);
    let pred = BabyBear::new(42);
    let sr = BabyBear::new(99_999);
    let fact_hash = chip_absorb_all_lanes(
        7,
        &[
            pred,
            value,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(FACT_MARK),
            BabyBear::ONE,
        ],
    )[0];
    let fact_commitment = hash_2_to_1(fact_hash, sr);
    let mut row = vec![BabyBear::ZERO; CT_WIDTH];
    row[PRIVATE_VALUE] = value;
    row[THRESHOLD] = threshold;
    row[BLINDING] = blinding;
    row[DIFF] = diff;
    let dv = diff.as_u32();
    for i in 0..COMMITTED_DIFF_BITS {
        row[DIFF_BITS_START + i] = BabyBear::new((dv >> i) & 1);
    }
    row[THRESHOLD_COMMITMENT] = commitment;
    row[FACT_COMMITMENT] = fact_commitment;
    row[POSEIDON2_RESULT] = commitment;
    row[PREDICATE_SYM] = pred;
    row[STATE_ROOT] = sr;
    row[FACT_HASH] = fact_hash;
    (row, [commitment, fact_commitment])
}

fn honest_trace(
    value: BabyBear,
    threshold: BabyBear,
    blinding: BabyBear,
    fc: BabyBear,
) -> (Vec<Vec<BabyBear>>, [BabyBear; 2]) {
    let (row, pis) = honest_row(value, threshold, blinding, fc);
    (vec![row.clone(), row.clone(), row.clone(), row], pis)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

/// The NEW isolating tamper: perturb ONLY the chip-input `blinding` column, keeping the
/// committed digest/pi honest. The chip lookup must break (out0 no longer equals
/// `hash_2_to_1(threshold, blinding_new)`), and NOTHING else.
#[test]
fn tampered_blinding_input_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = (
        BabyBear::new(750),
        BabyBear::new(700),
        BabyBear::new(12345),
        BabyBear::new(9_999_991),
    );
    // Non-vacuity: honest accepts.
    let (ok_trace, ok_pis) = honest_trace(value, threshold, blinding, fc);
    assert!(!rejects(&desc, &ok_trace, &ok_pis), "honest must accept");

    // Tamper: bump blinding only; leave digest/commitment/pi at the honest hash.
    let (mut trace, pis) = honest_trace(value, threshold, blinding, fc);
    for row in &mut trace {
        row[BLINDING] += BabyBear::ONE;
    }
    assert!(
        rejects(&desc, &trace, &pis),
        "a blinding inconsistent with the committed digest must be REJECTED (chip hash binding)"
    );
}
