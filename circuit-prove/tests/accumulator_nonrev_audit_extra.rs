//! ADVERSARIAL AUDIT — one additional isolating tamper the shipped gate did NOT write.
//!
//! The shipped `accumulator_nonrev_emit_gate.rs` isolates the *alpha_aux* constancy window gate
//! (`tampered_alpha_aux_drift_refuses`) but never isolates the TWIN *acc_aux* constancy window
//! gate. Without the acc_aux constancy, a prover could drift `acc_aux` on a non-first row and
//! (since `sum==acc_aux` is only a per-row equality, and `sum==pi[ACC]` is pinned on the FIRST row
//! only) claim a DIFFERENT accumulator on later rows — the exact hand-AIR gap the emit closes.
//!
//! This test builds a fully self-consistent middle row whose ONLY deviation is a drifted
//! `acc_aux = Acc + 1` (so `sum==acc_aux`, C1..C4, `check==1` all hold on that row, and the row-0
//! acc_aux pin is untouched). The SOLE constraint that can bite is the `acc_aux` constancy
//! `.windowGate`. Non-vacuity control: the same construction with the TRUE Acc (no drift) is
//! ACCEPTED. Drives the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2`.

use std::panic::AssertUnwindSafe;

use dregg_circuit::accumulator_types::{
    AccumulatorNonMembershipWitness, AccumulatorNonRevocationWitness, ExtElem, compute_accumulator,
    derive_alpha,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::dsl::accumulator::generate_accumulator_trace;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;

const HASH: usize = 0;
const QUOTIENT: usize = 4;
const REMAINDER: usize = 8;
const DIFF: usize = 12;
const PRODUCT: usize = 16;
const SUM: usize = 20;
const V_INV: usize = 24;
const CHECK: usize = 28;
const ALPHA_AUX: usize = 32;
const ACC_AUX: usize = 36;
const WIDTH: usize = 40;

// The exact golden the Lean file byte-pins (copied from the shipped gate).
const GOLDEN_JSON: &str = include_str!("accumulator_nonrev_golden.json");

fn make_hash(seed: u32) -> BabyBear {
    hash_many(&[BabyBear::new(seed), BabyBear::new(0xCAFE)])
}

fn honest_fixture() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, ExtElem, ExtElem) {
    let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
    let alpha = derive_alpha(&revocation_set);
    let acc = compute_accumulator(&revocation_set, alpha);
    let ancestors: Vec<BabyBear> = (1..=3).map(|i| make_hash(i * 7777)).collect();
    let mut anc_w = Vec::new();
    for &h in &ancestors {
        assert!(!revocation_set.contains(&h));
        let mut rem_base = BabyBear::ONE;
        for &rh in &revocation_set {
            rem_base = rem_base * (h - rh);
        }
        let remainder = ExtElem::from_base(rem_base);
        let diff = alpha.sub(ExtElem::from_base(h));
        let quotient = acc
            .sub(remainder)
            .mul(diff.inverse().expect("diff invertible"));
        anc_w.push(AccumulatorNonMembershipWitness {
            ancestor_hash: h,
            quotient,
            remainder,
        });
    }
    let witness = AccumulatorNonRevocationWitness { ancestors: anc_w };
    let (trace, pis) = generate_accumulator_trace(&witness, acc, alpha);
    (trace, pis, acc, alpha)
}

/// A row self-consistent for `(alpha, h, v, acc_written)`: `diff=alpha-h`, `w=(acc_written-v)/diff`,
/// `prod=w*diff`, `sum=prod+v=acc_written`, `check=v*v^-1=1`, `alpha_aux=alpha`, `acc_aux=acc_written`.
/// Every per-row relation holds by construction; the sole knob is which `acc` gets written into SUM
/// and ACC_AUX.
fn self_consistent_row(
    alpha: ExtElem,
    h: BabyBear,
    v: ExtElem,
    acc_written: ExtElem,
) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; WIDTH];
    let diff = alpha.sub(ExtElem::from_base(h));
    let w = acc_written
        .sub(v)
        .mul(diff.inverse().expect("diff invertible"));
    let prod = w.mul(diff);
    let sum = prod.add(v);
    let v_inv = v.inverse().expect("v nonzero");
    let check = v.mul(v_inv);
    ExtElem::from_base(h).write_to(&mut row, HASH);
    w.write_to(&mut row, QUOTIENT);
    v.write_to(&mut row, REMAINDER);
    diff.write_to(&mut row, DIFF);
    prod.write_to(&mut row, PRODUCT);
    sum.write_to(&mut row, SUM);
    v_inv.write_to(&mut row, V_INV);
    check.write_to(&mut row, CHECK);
    alpha.write_to(&mut row, ALPHA_AUX);
    acc_written.write_to(&mut row, ACC_AUX);
    row
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

/// CANARY (acc_aux constancy — the UNTESTED twin tooth). Drift `acc_aux` (and its self-consistent
/// `sum`) to `Acc + 1` on a middle row. C1..C4, `sum==acc_aux`, `check==1` all hold on that row;
/// the row-0 acc_aux pin is untouched; alpha_aux is constant. The ONLY constraint that can catch
/// the drift is the `acc_aux` constancy window gate. REJECTED.
#[test]
fn tampered_acc_aux_drift_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (base_trace, pis, acc, alpha) = honest_fixture();

    let h_pick = BabyBear::new(0x1234_5678);
    let v_pick = ExtElem::from_base(BabyBear::new(9)); // nonzero remainder
    let delta = ExtElem::from_base(BabyBear::ONE);

    // Non-vacuity control: same construction, TRUE Acc → accepted.
    let mut ok_trace = base_trace.clone();
    ok_trace[1] = self_consistent_row(alpha, h_pick, v_pick, acc);
    assert!(
        !rejects(&desc, &ok_trace, &pis),
        "a self-consistent row carrying the TRUE Acc must be accepted"
    );

    // Malicious row: drifted acc_aux/sum = Acc + 1. Only acc_aux constancy can bite.
    let mut bad_trace = base_trace.clone();
    bad_trace[1] = self_consistent_row(alpha, h_pick, v_pick, acc.add(delta));
    assert!(
        rejects(&desc, &bad_trace, &pis),
        "a drifted acc_aux (claiming a different accumulator on a later row) must be REJECTED \
         by the acc_aux constancy window gate"
    );
}
