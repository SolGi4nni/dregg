//! ADVERSARIAL AUDIT canary (additive, non-authoritative): isolates the ONE constraint the
//! shipped gate never canaried — `firstStepIsOne` (row-0 `step == 1`, ivc.rs:653-658). The four
//! shipped canaries bite lastNewHashBind / firstSeedBind / lastStepBind / perRowHash, leaving the
//! first-row step boundary unexercised. This builds a FULLY GENUINE hash chain whose step index
//! starts at 2 (not 1) — every chip lookup passes (real hashes), the seed pin passes, the last-row
//! step/hash pins pass (PIs set consistently) — so the ONLY violated constraint is the first-row
//! step==1 boundary. It must be rejected, and the honest (step-starts-at-1) twin must be accepted.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc::{extend_accumulated_hash, initial_accumulated_hash};

const STEP: usize = 0;
const OLD_HASH: usize = 1;
const NEW_ROOT: usize = 2;
const NEW_HASH: usize = 3;
const IVC_WIDTH: usize = 11;

const GOLDEN_JSON: &str = r#"{"name":"dregg-ivc-state-transition-v2","ir":2,"trace_width":11,"public_input_count":4,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":4},{"t":"const","v":1230390016},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10}]},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"first","col":1,"pi_index":0},{"t":"pi_binding","row":"last","col":0,"pi_index":2},{"t":"pi_binding","row":"last","col":3,"pi_index":3}],"hash_sites":[],"ranges":[]}"#;

fn honest_row(step: u32, old_hash: BabyBear, new_root: BabyBear) -> Vec<BabyBear> {
    let new_hash = extend_accumulated_hash(old_hash, new_root, step);
    let mut row = vec![BabyBear::ZERO; IVC_WIDTH];
    row[STEP] = BabyBear::new(step);
    row[OLD_HASH] = old_hash;
    row[NEW_ROOT] = new_root;
    row[NEW_HASH] = new_hash;
    row
}

/// A genuine 3-step chain whose FIRST step index is `start_step` (chained honestly, so every chip
/// lookup and every chain link is real). PIs are set so seed / step_count / acc_hash all pin
/// correctly — the first-row `step==1` boundary is the only thing that can differ.
fn genuine_trace_from(start_step: u32) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let initial_root = BabyBear::new(777);
    let new_roots = [BabyBear::new(111), BabyBear::new(222), BabyBear::new(333)];
    let seed_hash = initial_accumulated_hash(initial_root);
    let mut current = seed_hash;
    let mut trace: Vec<Vec<BabyBear>> = Vec::new();
    let mut last_step = 0u32;
    for (i, &new_root) in new_roots.iter().enumerate() {
        let step = start_step + i as u32;
        last_step = step;
        let row = honest_row(step, current, new_root);
        current = row[NEW_HASH];
        trace.push(row);
    }
    let acc_hash = current;
    let final_root = *new_roots.last().unwrap();
    let target = trace.len().next_power_of_two().max(2);
    let last = trace.last().unwrap().clone();
    while trace.len() < target {
        trace.push(last.clone());
    }
    // step_count pinned to the ACTUAL last step so lastStepBind is satisfied regardless of offset.
    let pis = vec![seed_hash, final_root, BabyBear::new(last_step), acc_hash];
    (trace, pis)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    !matches!(r, Ok(Ok(())))
}

#[test]
fn first_row_step_not_one_is_rejected() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");

    // Non-vacuity: the genuine step-starts-at-1 twin ACCEPTS (isolates the boundary as the cause).
    let (ok_trace, ok_pis) = genuine_trace_from(1);
    assert!(
        !rejects(&desc, &ok_trace, &ok_pis),
        "genuine step-starts-at-1 chain must be accepted"
    );

    // The ONLY difference: row-0 step is 2, not 1 (everything else genuine + consistently pinned).
    let (bad_trace, bad_pis) = genuine_trace_from(2);
    assert_eq!(bad_trace[0][STEP], BabyBear::new(2));
    assert!(
        rejects(&desc, &bad_trace, &bad_pis),
        "a genuine chain whose first step != 1 must be REJECTED by the first-row step boundary"
    );
}
