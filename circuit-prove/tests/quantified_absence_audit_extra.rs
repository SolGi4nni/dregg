//! ADVERSARIAL AUDIT ADDENDUM (additive, new file) for the `quantified_absence` emit.
//!
//! The implementer's six canaries each tamper a value that feeds a LIMB-0 gate (elem→C1₀,
//! w→C2₀…, v→C3₀) or a whole-vector forge. The Lean `_zero_iff` lemmas only prove LIMB 0 of
//! each gate. The residual vacuity risk this addendum closes: are the HIGHER-limb gates
//! (C2 limb 2, and a limb-3 boundary pin) actually structurally correct and enforced, or could
//! a forgery that keeps limb 0 consistent slip through a bogus higher-limb gate?
//!
//! Two NEW isolating tampers, each proven to be REJECTED BY ONE SPECIFIC higher-limb constraint:
//!   (A) forge PRODUCT limb 2 only, and repair C3₂ + boundary₂ so ONLY the C2 limb-2 ext-mult
//!       gate can fire — a clean single-constraint bite on a NON-limb-0 gate.
//!   (B) forge Acc_all PI at limb 3 only → the limb-3 boundary pin bites (not limb 0).

use std::panic::AssertUnwindSafe;

use dregg_circuit::accumulator_types::ExtElem;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const E0: usize = 0;
const Q0: usize = 4;
const V0: usize = 8;
const D0: usize = 12;
const P0: usize = 16;
const S0: usize = 20;
const A0: usize = 24;
const QACC_WIDTH: usize = 28;
const PI_ACC0: usize = 0;

// Byte-identical to QuantifiedAbsenceEmit.lean's emitVmJson2 #guard.
const GOLDEN_JSON: &str = include_str!("quantified_absence_golden.json");

fn limbs(e: ExtElem) -> [BabyBear; 4] {
    e.0
}
fn put(row: &mut [BabyBear], off: usize, e: ExtElem) {
    row[off..off + 4].copy_from_slice(&limbs(e));
}
fn fixture() -> (ExtElem, ExtElem, ExtElem, ExtElem) {
    (
        ExtElem([
            BabyBear::new(1_000_003),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ]),
        ExtElem([
            BabyBear::new(31),
            BabyBear::new(37),
            BabyBear::new(41),
            BabyBear::new(43),
        ]),
        ExtElem([
            BabyBear::new(97),
            BabyBear::new(89),
            BabyBear::new(83),
            BabyBear::new(79),
        ]),
        ExtElem([
            BabyBear::new(500_009),
            BabyBear::new(600_011),
            BabyBear::new(700_019),
            BabyBear::new(800_023),
        ]),
    )
}
fn honest_row(elem: ExtElem, w: ExtElem, v: ExtElem, alpha: ExtElem) -> (Vec<BabyBear>, ExtElem) {
    let diff = alpha.sub(elem);
    let prod = w.mul(diff);
    let sum = prod.add(v);
    let mut row = vec![BabyBear::ZERO; QACC_WIDTH];
    put(&mut row, E0, elem);
    put(&mut row, Q0, w);
    put(&mut row, V0, v);
    put(&mut row, D0, diff);
    put(&mut row, P0, prod);
    put(&mut row, S0, sum);
    put(&mut row, A0, alpha);
    (row, sum)
}
fn pis(acc_all: ExtElem, alpha: ExtElem) -> Vec<BabyBear> {
    let mut p = Vec::new();
    p.extend_from_slice(&limbs(acc_all));
    p.extend_from_slice(&limbs(alpha));
    p
}
fn trace_of(row: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    vec![row.to_vec(), row.to_vec(), row.to_vec(), row.to_vec()]
}
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pv: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pv, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pv)
    }));
    !matches!(r, Ok(Ok(())))
}

/// (A) A forgery consistent on limb 0 but broken on the C2 limb-2 gate: bump PRODUCT limb 2 by 1,
/// repair SUM limb 2 (= prod+v) and Acc_all limb 2 (= sum) so C3₂ and boundary₂ stay satisfied.
/// The ONLY constraint left unsatisfiable is C2 limb 2 (`prod₂ == (w·diff)₂`). If that higher-limb
/// gate were vacuous/structurally wrong, this would be ACCEPTED.
#[test]
fn forged_product_limb2_bites_c2_limb2() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    // non-vacuity: honest accepts.
    assert!(
        !rejects(&desc, &trace_of(&row), &pis(acc_all, alpha)),
        "non-vacuity"
    );

    let mut bad = row.clone();
    // bump prod limb 2 only.
    bad[P0 + 2] = bad[P0 + 2] + BabyBear::ONE;
    // repair sum limb 2 = prod2_wrong + v2, keeping C3 limb 2 satisfied.
    bad[S0 + 2] = bad[S0 + 2] + BabyBear::ONE;
    // repair Acc_all PI limb 2 = sum2, keeping the boundary pin limb 2 satisfied.
    let mut acc_bad = limbs(acc_all);
    acc_bad[2] = acc_bad[2] + BabyBear::ONE;
    let pv = pis(ExtElem(acc_bad), alpha);

    assert!(
        rejects(&desc, &trace_of(&bad), &pv),
        "a product wrong on limb 2 (all other limbs/constraints repaired) must be REJECTED by the \
         C2 limb-2 ext-mult gate — proving the higher-limb gate is live, not vacuous"
    );
}

/// (B) Forge Acc_all at limb 3 only → the limb-3 boundary pin (SUM₃ == Acc_all₃) bites. Confirms the
/// boundary is pinned on every limb, not just limb 0.
#[test]
fn forged_acc_all_limb3_bites_boundary_limb3() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let trace = trace_of(&row);
    assert!(!rejects(&desc, &trace, &pis(acc_all, alpha)), "non-vacuity");
    let mut forged = pis(acc_all, alpha);
    forged[PI_ACC0 + 3] = forged[PI_ACC0 + 3] + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged Acc_all limb 3 must be REJECTED by the limb-3 boundary pin"
    );
}
