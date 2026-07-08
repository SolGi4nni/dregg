//! ADVERSARIAL AUDIT (additive, read-only w.r.t. the emit): isolating tampers the
//! `non_revocation_emit_gate` suite did NOT write. Reuses the byte-identical GOLDEN_JSON and the
//! same helpers, independently. Purpose: probe whether the 30-bit range on `HALF - diff` actually
//! gates non-membership at the BOUNDARY (x == R, x == L), and whether the continuity gate bites.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::poseidon2::hash_2_to_1;

const GOLDEN_JSON: &str = r#"{"name":"dregg-non-revocation-sorted-tree::poseidon2-v1","ir":2,"trace_width":27,"public_input_count":2,"tables":[{"id":2,"name":"range","arity":1,"sem":"range","bits":30}],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":1},{"t":"var","v":2},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":9},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":10},{"t":"var","v":11},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":12},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23},{"t":"var","v":24},{"t":"var","v":25},{"t":"var","v":26}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"var","v":1}},"r":{"t":"const","v":1}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}},"r":{"t":"var","v":0}},"r":{"t":"const","v":1}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":7},"r":{"t":"var","v":5}},"r":{"t":"const","v":-1006632959}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":8},"r":{"t":"var","v":6}},"r":{"t":"const","v":-1006632959}}},{"t":"lookup","table":2,"tuple":[{"t":"var","v":7}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":8}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":5}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":6}]},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"first","col":12,"pi_index":0},{"t":"pi_binding","row":"first","col":0,"pi_index":1}],"hash_sites":[],"ranges":[]}"#;

const X: usize = 0;
const LEAF_L: usize = 1;
const LEAF_R: usize = 2;
const LPOS: usize = 3;
const RPOS: usize = 4;
const DIFF_L: usize = 5;
const DIFF_R: usize = 6;
const RL: usize = 7;
const RR: usize = 8;
const PAR0: usize = 9;
const CUR1: usize = 10;
const SIB1: usize = 11;
const PAR1: usize = 12;
const NONREV_WIDTH: usize = 27;
const HALF_P_MINUS_1: u32 = 1_006_632_959;

fn consistent_row(
    x: BabyBear,
    l: BabyBear,
    r: BabyBear,
    lpos: u32,
    rpos: u32,
    sib1: BabyBear,
) -> (Vec<BabyBear>, BabyBear) {
    let par0 = hash_2_to_1(l, r);
    let root = hash_2_to_1(par0, sib1);
    let diff_l = x - l - BabyBear::ONE;
    let diff_r = r - x - BabyBear::ONE;
    let half = BabyBear::new(HALF_P_MINUS_1);
    let mut row = vec![BabyBear::ZERO; NONREV_WIDTH];
    row[X] = x;
    row[LEAF_L] = l;
    row[LEAF_R] = r;
    row[LPOS] = BabyBear::new(lpos);
    row[RPOS] = BabyBear::new(rpos);
    row[DIFF_L] = diff_l;
    row[DIFF_R] = diff_r;
    row[RL] = half - diff_l;
    row[RR] = half - diff_r;
    row[PAR0] = par0;
    row[CUR1] = par0;
    row[SIB1] = sib1;
    row[PAR1] = root;
    (row, root)
}

fn trace_of(row: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    vec![row.to_vec(), row.to_vec(), row.to_vec(), row.to_vec()]
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

/// THE CENTRAL PROBE: x == R (=300). Item 300 is LEAF_R — a genuine committed MEMBER. A sound
/// non-membership descriptor MUST reject a proof claiming a member is fresh. Here diff_right =
/// R - x - 1 = -1 = p-1; RR = HALF - (p-1) mod p = 1006632960 < 2^30, so the right range lookup
/// ACCEPTS (spurious wrap window). If this trace proves+verifies, the range tooth does NOT gate
/// non-membership at the right boundary.
#[test]
fn x_equals_R_member_claimed_fresh() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let l = BabyBear::new(100);
    let r = BabyBear::new(300);
    let x = r; // x == R, a member
    let (row, root) = consistent_row(x, l, r, 0, 1, BabyBear::new(777_777));
    eprintln!(
        "x==R: RL={} (<2^30? {}), RR={} (<2^30? {})",
        row[RL].as_u32(),
        row[RL].as_u32() < (1u32 << 30),
        row[RR].as_u32(),
        row[RR].as_u32() < (1u32 << 30),
    );
    let rejected = rejects(&desc, &trace_of(&row), &[root, x]);
    eprintln!("x==R rejected? {rejected}");
    assert!(
        rejected,
        "SOUNDNESS: item x==R (a committed member) claimed fresh MUST be rejected — if accepted, the \
         range tooth does not gate non-membership at the boundary"
    );
}

/// x == L (=100), the LEFT boundary mirror: item 100 is LEAF_L, a member. diff_left = x-L-1 = -1;
/// RL = HALF - (p-1) = 1006632960 < 2^30 → left range spuriously accepts.
#[test]
fn x_equals_L_member_claimed_fresh() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let l = BabyBear::new(100);
    let r = BabyBear::new(300);
    let x = l; // x == L, a member
    let (row, root) = consistent_row(x, l, r, 0, 1, BabyBear::new(777_777));
    eprintln!(
        "x==L: RL={} (<2^30? {}), RR={} (<2^30? {})",
        row[RL].as_u32(),
        row[RL].as_u32() < (1u32 << 30),
        row[RR].as_u32(),
        row[RR].as_u32() < (1u32 << 30),
    );
    let rejected = rejects(&desc, &trace_of(&row), &[root, x]);
    eprintln!("x==L rejected? {rejected}");
    assert!(
        rejected,
        "SOUNDNESS: item x==L (a committed member) claimed fresh MUST be rejected"
    );
}

/// x strictly ABOVE R (x = R + 5): not bracketed at all, yet diff_right = R-x-1 = -6 = p-6 is in the
/// spurious window, so RR < 2^30. An item above the right neighbor claimed "between L and R".
#[test]
fn x_above_R_not_bracketed() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let l = BabyBear::new(100);
    let r = BabyBear::new(300);
    let x = BabyBear::new(305); // above R
    let (row, root) = consistent_row(x, l, r, 0, 1, BabyBear::new(777_777));
    eprintln!(
        "x>R: RR={} (<2^30? {})",
        row[RR].as_u32(),
        row[RR].as_u32() < (1u32 << 30),
    );
    let rejected = rejects(&desc, &trace_of(&row), &[root, x]);
    eprintln!("x>R rejected? {rejected}");
    assert!(rejected, "SOUNDNESS: an item above R (not bracketed) claimed fresh MUST be rejected");
}

/// CONTINUITY-GATE isolation (the emit-gate suite never tests it): break CUR1 != PAR0, recompute the
/// root as hash(CUR1, SIB1) and pin THAT root. All chip lookups + root pin + queried pin stay
/// consistent; ONLY the continuity gate (CUR1 - PAR0 = 0) is violated. Confirms the gate bites.
#[test]
fn continuity_gate_isolated_bite() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let l = BabyBear::new(100);
    let r = BabyBear::new(300);
    let x = BabyBear::new(200);
    let sib1 = BabyBear::new(777_777);
    let par0 = hash_2_to_1(l, r);
    let cur1 = par0 + BabyBear::ONE; // break continuity
    let root = hash_2_to_1(cur1, sib1); // level1 lookup stays consistent with cur1
    let diff_l = x - l - BabyBear::ONE;
    let diff_r = r - x - BabyBear::ONE;
    let half = BabyBear::new(HALF_P_MINUS_1);
    let mut row = vec![BabyBear::ZERO; NONREV_WIDTH];
    row[X] = x;
    row[LEAF_L] = l;
    row[LEAF_R] = r;
    row[LPOS] = BabyBear::new(0);
    row[RPOS] = BabyBear::new(1);
    row[DIFF_L] = diff_l;
    row[DIFF_R] = diff_r;
    row[RL] = half - diff_l;
    row[RR] = half - diff_r;
    row[PAR0] = par0;
    row[CUR1] = cur1; // != par0
    row[SIB1] = sib1;
    row[PAR1] = root;
    let rejected = rejects(&desc, &trace_of(&row), &[root, x]);
    eprintln!("continuity-break rejected? {rejected}");
    assert!(rejected, "the continuity gate (CUR1 == PAR0) must bite when broken");
}

/// SANITY: the honest witness (x=200 strictly bracketed) proves+verifies, so a rejection above is
/// attributable to the tamper, not a dead descriptor.
#[test]
fn honest_still_accepts_sanity() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let l = BabyBear::new(100);
    let r = BabyBear::new(300);
    let (row, root) = consistent_row(BabyBear::new(200), l, r, 0, 1, BabyBear::new(777_777));
    assert!(!rejects(&desc, &trace_of(&row), &[root, row[X]]), "honest witness must accept");
}
