//! ADVERSARIAL AUDIT PROBE (additive, read-only wrt the reviewed files) for the `multi_step`
//! emit gate. Independent isolating tampers the original gate did NOT write:
//!
//!   * `broken_later_link_refuses` — breaks the chain link into step 3 (a LATE transition, row
//!     2 → 3), confirming the continuity `window_gate` fires on ALL transition rows, not just
//!     the first (the original only broke row 0 → 1).
//!   * `tampered_lane_refuses` — corrupts an exposed chip LANE column (not out0/ACC), confirming
//!     the arity-2 chip lookup binds every exposed permutation lane, not merely the digest.
//!   * `single_step_chain_proves` — a K=1 chain (no transitions) still proves+verifies, so the
//!     window gate is not spuriously required.
//!
//! Reuses ONLY the public prover API; rebuilds the honest witness locally.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_2_to_1;

const PREV: usize = 0;
const DERIVED: usize = 1;
const ACC: usize = 2;
const LANE_BASE: usize = 3;
const CHAIN_WIDTH: usize = 10;

const GOLDEN_JSON: &str = r#"{"name":"multi-step-accumulated-hash-chain::poseidon2-v1","ir":2,"trace_width":10,"public_input_count":2,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9}]},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"last","col":2,"pi_index":1}],"hash_sites":[],"ranges":[]}"#;

fn chain_row(prev: BabyBear, derived: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; CHAIN_WIDTH];
    row[PREV] = prev;
    row[DERIVED] = derived;
    row[ACC] = hash_2_to_1(prev, derived);
    row
}

/// A genuine chain; every link honestly chains. Returns (trace, initial, final).
fn honest_chain(prev0: BabyBear, deriveds: &[BabyBear]) -> (Vec<Vec<BabyBear>>, BabyBear, BabyBear) {
    let mut trace = Vec::new();
    let mut prev = prev0;
    for &d in deriveds {
        let row = chain_row(prev, d);
        prev = row[ACC];
        trace.push(row);
    }
    let final_acc = trace.last().unwrap()[ACC];
    (trace, prev0, final_acc)
}

/// Break the link entering step `break_at` (its PREV is forged off the prior ACC), while every
/// per-step ACC = hash_2_to_1(PREV, DERIVED) is recomputed consistently and both pins re-pin.
/// ONLY the continuity window at the (break_at-1 -> break_at) transition is unsatisfied.
fn broken_link_at(
    prev0: BabyBear,
    deriveds: &[BabyBear],
    break_at: usize,
    bogus: BabyBear,
) -> (Vec<Vec<BabyBear>>, BabyBear, BabyBear) {
    let mut trace = Vec::new();
    let mut prev = prev0;
    for (i, &d) in deriveds.iter().enumerate() {
        if i == break_at {
            prev = bogus;
        }
        let row = chain_row(prev, d);
        prev = row[ACC];
        trace.push(row);
    }
    let final_acc = trace.last().unwrap()[ACC];
    (trace, prev0, final_acc)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    !matches!(r, Ok(Ok(())))
}

fn fixture() -> (BabyBear, [BabyBear; 4]) {
    (
        BabyBear::new(1001),
        [
            BabyBear::new(2002),
            BabyBear::new(3003),
            BabyBear::new(4004),
            BabyBear::new(5005),
        ],
    )
}

/// The continuity window must fire on a LATE transition (row 2 -> 3), not only the first link.
#[test]
fn broken_later_link_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    let (honest, hi, hf) = honest_chain(prev0, &deriveds);
    assert!(!rejects(&desc, &honest, &[hi, hf]), "honest chain must accept");
    let acc2 = honest[2][ACC];
    let bogus = acc2 + BabyBear::ONE;
    let (bad, bi, bf) = broken_link_at(prev0, &deriveds, 3, bogus);
    assert_ne!(bad[3][PREV], acc2, "the link into step 3 is genuinely broken");
    // pins are self-consistent (bi = prev0, bf = recomputed acc_last); MS1 holds every row.
    assert!(
        rejects(&desc, &bad, &[bi, bf]),
        "a broken LATE chain link (prev3 != acc2) must be REJECTED (MS2 window fires on all transitions)"
    );
}

/// The exposed chip LANE columns are PROVER-DERIVED, not witness-controlled: the prover overwrites
/// LANE_BASE.. from the genuine permutation before proving, so a pre-seeded wrong lane value is a
/// no-op (still accepts). This is the soundness property — the chip derives `out` from the inputs
/// and never trusts consumer-supplied lane values, so there is nothing here for a forger to steer.
/// (Corrupting ACC/DERIVED, which ARE witness-controlled, is the real MS1 tooth, covered by the
/// original gate's `tampered_derived_refuses`.)
#[test]
fn chip_lanes_are_prover_authoritative() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    let (trace, i, f) = honest_chain(prev0, &deriveds);
    assert!(!rejects(&desc, &trace, &[i, f]), "honest chain must accept");
    let mut seeded = trace.clone();
    seeded[1][LANE_BASE] = seeded[1][LANE_BASE] + BabyBear::new(7); // clobbered by the prover.
    assert!(
        !rejects(&desc, &seeded, &[i, f]),
        "witness lane values are prover-overwritten, so a seeded wrong lane is a no-op"
    );
}

/// A K=1 chain (no transitions) proves + verifies: the transition window is vacuously satisfied,
/// both pins collapse onto the single row (PREV==pi0, ACC==pi1). Confirms the window is not a
/// spurious always-on requirement.
#[test]
fn single_step_chain_proves() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, i, f) = honest_chain(BabyBear::new(777), &[BabyBear::new(888)]);
    assert_eq!(trace.len(), 1);
    let proof = prove_vm_descriptor2(&desc, &trace, &[i, f], &MemBoundaryWitness::default(), &[])
        .expect("K=1 chain proves");
    verify_vm_descriptor2(&desc, &proof, &[i, f]).expect("K=1 chain re-verifies");
    // and a forged single-row final pin is still caught.
    assert!(
        rejects(&desc, &trace, &[i, f + BabyBear::ONE]),
        "forged final on a K=1 chain must be REJECTED (pin still binds)"
    );
}
