//! AUDIT-ADDED isolating tampers for the FOLD emit (additive; does not touch the shipped gate).
//! Two teeth the shipped 6 canaries never exercise:
//!   A. `new_root` constancy window  — forge NEW_ROOT on a non-first removal row.
//!   B. last-row `REMOVAL_COUNT == pi[2]` boundary — forge pi[2].
//! Each first asserts the honest witness is ACCEPTED (non-vacuity anchor), then that the single-
//! coordinate perturbation is REJECTED.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;

const GOLDEN_JSON: &str = r#"{"name":"dregg-fold-step-v2","ir":2,"trace_width":21,"public_input_count":6,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":1},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20}]},{"t":"pi_binding","row":"first","col":3,"pi_index":0},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":3}}}},{"t":"pi_binding","row":"first","col":4,"pi_index":1},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}},"r":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":12}}}}},{"t":"pi_binding","row":"last","col":13,"pi_index":4},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":13}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":13}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"last","col":5,"pi_index":2},{"t":"pi_binding","row":"last","col":6,"pi_index":3},{"t":"pi_binding","row":"last","col":2,"pi_index":4}],"hash_sites":[],"ranges":[]}"#;

const ROW_TYPE: usize = 0;
const FACT_HASH: usize = 1;
const MEMBERSHIP_ROOT: usize = 2;
const OLD_ROOT: usize = 3;
const NEW_ROOT: usize = 4;
const REMOVAL_COUNT: usize = 5;
const CHECK_COUNT: usize = 6;
const FACT_PRED: usize = 7;
const FACT_TERM0: usize = 8;
const FACT_TERM1: usize = 9;
const FACT_TERM2: usize = 10;
const HASH_VALID: usize = 11;
const REMOVAL_COUNT_PLUS_ONE: usize = 12;
const PI4_CARRIER: usize = 13;
const FOLD_WIDTH: usize = 21;

const OLD_ROOT_V: u32 = 111_111;
const NEW_ROOT_V: u32 = 222_222;
const NUM_CHECKS: u32 = 3;
const TRANSITION_HASH: u32 = 909_090;

fn facts() -> [(BabyBear, [BabyBear; 3]); 2] {
    [
        (BabyBear::new(10), [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO]),
        (BabyBear::new(110), [BabyBear::new(120), BabyBear::new(130), BabyBear::ZERO]),
    ]
}

fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let facts = facts();
    let n = facts.len() as u32;
    let old_root = BabyBear::new(OLD_ROOT_V);
    let new_root = BabyBear::new(NEW_ROOT_V);
    let t = BabyBear::new(TRANSITION_HASH);
    let zero_fact_hash = hash_fact(BabyBear::ZERO, &[BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]);

    let mut trace: Vec<Vec<BabyBear>> = Vec::new();
    for (i, (pred, terms)) in facts.iter().enumerate() {
        let mut row = vec![BabyBear::ZERO; FOLD_WIDTH];
        row[ROW_TYPE] = BabyBear::ZERO;
        row[FACT_HASH] = hash_fact(*pred, terms);
        row[MEMBERSHIP_ROOT] = old_root;
        row[OLD_ROOT] = old_root;
        row[NEW_ROOT] = new_root;
        row[REMOVAL_COUNT] = BabyBear::new((i + 1) as u32);
        row[CHECK_COUNT] = BabyBear::new(NUM_CHECKS);
        row[FACT_PRED] = *pred;
        row[FACT_TERM0] = terms[0];
        row[FACT_TERM1] = terms[1];
        row[FACT_TERM2] = terms[2];
        row[HASH_VALID] = BabyBear::ONE;
        let is_last_removal = (i + 1) as u32 == n;
        row[REMOVAL_COUNT_PLUS_ONE] =
            if is_last_removal { BabyBear::new(n) } else { BabyBear::new((i + 2) as u32) };
        row[PI4_CARRIER] = t;
        trace.push(row);
    }
    let mut summary = vec![BabyBear::ZERO; FOLD_WIDTH];
    summary[ROW_TYPE] = BabyBear::ONE;
    summary[FACT_HASH] = zero_fact_hash;
    summary[MEMBERSHIP_ROOT] = t;
    summary[OLD_ROOT] = old_root;
    summary[NEW_ROOT] = new_root;
    summary[REMOVAL_COUNT] = BabyBear::new(n);
    summary[CHECK_COUNT] = BabyBear::new(NUM_CHECKS);
    summary[HASH_VALID] = BabyBear::ONE;
    summary[REMOVAL_COUNT_PLUS_ONE] = BabyBear::new(n);
    summary[PI4_CARRIER] = t;
    trace.push(summary.clone());
    while !trace.len().is_power_of_two() {
        trace.push(summary.clone());
    }
    let pis = vec![
        old_root,
        new_root,
        BabyBear::new(n),
        BabyBear::new(NUM_CHECKS),
        t,
        BabyBear::new(777),
    ];
    (trace, pis)
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

/// AUDIT-A — the `new_root` constancy window (untouched by the shipped 6). Forge NEW_ROOT on the
/// second removal row (non-first) so `loc NEW_ROOT != nxt NEW_ROOT`. The constancy window breaks.
/// This isolates to that tooth: NEW_ROOT is otherwise read only by the first-row pin (row 0
/// unchanged), so the rejection cannot come from elsewhere.
#[test]
fn audit_forged_new_root_constancy_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest must be accepted — else vacuous");
    let mut bad = trace.clone();
    bad[1][NEW_ROOT] += BabyBear::ONE;
    assert!(rejects(&desc, &bad, &pis), "a non-constant NEW_ROOT must be REJECTED");
}

/// AUDIT-B — the last-row `REMOVAL_COUNT == pi[2]` boundary (untouched by the shipped 6). Honest
/// trace, but forge pi[2]. pi[2] feeds ONLY that last-row PiBinding, so the rejection isolates to it.
#[test]
fn audit_forged_removal_count_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest must be accepted — else vacuous");
    let mut forged = pis.clone();
    forged[2] += BabyBear::ONE;
    assert!(rejects(&desc, &trace, &forged), "a mismatched removal-count pi must be REJECTED");
}
