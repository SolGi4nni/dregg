//! ADVERSARIAL boundary audit for the arithmetic-predicate GTE range tooth.
//!
//! The shipped gate's C6 canary uses a `value < threshold` witness whose `diff` wraps to
//! `p - 10` (~2^31) — far outside `[0, 2^29)`. That proves the range refuses a HUGE value, but
//! does NOT pin the boundary: it would also pass if the mechanism enforced `< 2^30` or `< 2^31`.
//! This audit pins the boundary EXACTLY at 2^29 with a legit (non-wrapping) `diff`:
//!   - diff = 2^29 - 1 (the max in-range value)  => ACCEPT
//!   - diff = 2^29     (the first out-of-range)   => REJECT (range tooth), C3/C5 both consistent

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const GOLDEN_JSON: &str = r#"{"name":"dregg-predicate-arith-ge::threshold-v1","ir":2,"trace_width":5,"public_input_count":2,"tables":[{"id":2,"name":"range","arity":1,"sem":"range","bits":29}],"constraints":[{"t":"pi_binding","row":"first","col":2,"pi_index":0},{"t":"pi_binding","row":"first","col":4,"pi_index":1},{"t":"gate","body":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}}},"r":{"t":"var","v":2}}},{"t":"lookup","table":2,"tuple":[{"t":"var","v":3}]}],"hash_sites":[],"ranges":[]}"#;

const INPUT: usize = 0;
const SLOT_A: usize = 1;
const THRESHOLD: usize = 2;
const DIFF: usize = 3;
const FACT_COMMITMENT: usize = 4;
const PRED_WIDTH: usize = 5;

/// An honest-shaped 4-row trace where value/threshold are chosen so diff == `diff_val` with NO
/// field wrap (value = diff_val + threshold as a real u32). C3 (slot==input) and C5
/// (diff - slot + threshold == 0) both hold; only the range constraint on diff can fire.
fn consistent_trace(diff_val: u32, threshold: u32, fact: u32) -> Vec<Vec<BabyBear>> {
    let value = diff_val + threshold;
    let mut row = vec![BabyBear::ZERO; PRED_WIDTH];
    row[INPUT] = BabyBear::new(value);
    row[SLOT_A] = BabyBear::new(value);
    row[THRESHOLD] = BabyBear::new(threshold);
    row[DIFF] = BabyBear::new(value) - BabyBear::new(threshold);
    row[FACT_COMMITMENT] = BabyBear::new(fact);
    vec![row.clone(), row.clone(), row.clone(), row]
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], public: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, public, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, public)
    }));
    !matches!(r, Ok(Ok(())))
}

#[test]
fn range_boundary_is_exactly_2_pow_29() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let two29: u32 = 1 << 29;

    // max in-range diff accepts (non-vacuity: the range genuinely admits large-but-in-range diffs)
    assert!(
        !rejects(&desc, &consistent_trace(two29 - 1, 40, 12345), &pis(40, 12345)),
        "diff = 2^29 - 1 (max in-range, C3/C5 consistent) must be ACCEPTED"
    );

    // first out-of-range diff rejects — pins the boundary at 2^29 (not 2^30/2^31)
    assert!(
        rejects(&desc, &consistent_trace(two29, 40, 12345), &pis(40, 12345)),
        "diff = 2^29 (first out-of-range, C3/C5 consistent) must be REJECTED by the range tooth"
    );
}

fn pis(threshold: u32, fact: u32) -> Vec<BabyBear> {
    vec![BabyBear::new(threshold), BabyBear::new(fact)]
}
