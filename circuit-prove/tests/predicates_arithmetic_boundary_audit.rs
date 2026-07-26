//! ADVERSARIAL boundary audit for the arithmetic-predicate GTE range tooth.
//!
//! The shipped gate's C6 canary uses a `value < threshold` witness whose `diff` wraps to
//! `p - 10` (~2^31) — far outside `[0, 2^29)`. That proves the range refuses a HUGE value, but
//! does NOT pin the boundary: it would also pass if the mechanism enforced `< 2^30` or `< 2^31`.
//! This audit pins the boundary EXACTLY at 2^29 with a legit (non-wrapping) `diff`:
//!   - diff = 2^29 - 1 (the max in-range value)  => ACCEPT
//!   - diff = 2^29     (the first out-of-range)   => REJECT (range tooth), C3/C5 both consistent
//!
//! ⚑ RE-WELDED 2026-07-26. This file carried its own `r#"…"#` copy of the descriptor and its own
//! `PRED_WIDTH = 5` column layout. Both were the PRE-WELD shape: `53273ec65` / `ad848b492` added
//! the in-circuit value<->fact weld (two Poseidon2 chip legs, 5 columns -> 25), updated
//! `predicates_arithmetic_emit_gate.rs`, and left this sibling behind — so the boundary claim was
//! being made against a descriptor production no longer serves, and `scripts/check-emit-gate-weld.py`
//! said so. The golden is now the same `include_str!` of the deployed artifact the shipped gate
//! uses, and the layout is IMPORTED from the production witness builder rather than re-declared:
//! a test that spells its own column indices forks the layout and starts checking its own world.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_4_to_1, hash_fact};

/// The DEPLOYED descriptor bytes — the same file `predicates_arithmetic_emit_gate.rs` decodes and
/// `circuit/src/descriptor_by_name.rs` serves at verify time. Not a local copy: a local copy is
/// exactly how this audit drifted 14 constraints and 20 columns behind the thing it audits.
const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/predicate-arith.json");

// Column layout, IMPORTED. See the note above.
use dregg_circuit::predicate_arith_witness::{
    BLINDING, DIFF, FACT_COMMITMENT, FACT_HASH, INPUT, PRED_WIDTH, PREDICATE_SYM, SLOT_A,
    STATE_ROOT, THRESHOLD,
};

/// The fixed fact context, matching `predicates_arithmetic_emit_gate.rs` so both gates drive the
/// same deployed (BLINDED) posture.
const FIXED_PRED: u32 = 42;
const FIXED_STATE_ROOT: u32 = 99_999;
const FACT_MARK: u32 = 0xFACF;
const FIXED_BLINDING: u32 = 0xB11D1;

/// The credentialed fact commitment for a fact whose value is `value` — the out-of-circuit
/// binding (`compute_arithmetic_fact_commitment`) the weld's arity-4 leg reproduces in-circuit.
fn derived_fact(value: u32) -> BabyBear {
    let fh = hash_fact(
        BabyBear::new(FIXED_PRED),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    hash_4_to_1(&[
        fh,
        BabyBear::new(FIXED_STATE_ROOT),
        BabyBear::new(FIXED_BLINDING),
        BabyBear::ZERO,
    ])
}

/// An honest-shaped row where value/threshold are chosen so `diff == diff_val` with NO field wrap
/// (value = diff_val + threshold as a real u32). C3 (slot == input) and C5
/// (diff - slot + threshold == 0) both hold, and BOTH weld legs are satisfied — the fact hash and
/// the fact commitment are the genuine images of this row's own value. So the only tooth that can
/// fire is the range constraint on `diff`, which is what the boundary claim needs.
fn consistent_row(diff_val: u32, threshold: u32) -> Vec<BabyBear> {
    let value = diff_val + threshold;
    let pred = BabyBear::new(FIXED_PRED);
    let sr = BabyBear::new(FIXED_STATE_ROOT);
    let v = BabyBear::new(value);
    let fact_hash = chip_absorb_all_lanes(
        7,
        &[
            pred,
            v,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(FACT_MARK),
            BabyBear::ONE,
        ],
    )[0];
    let blinding = BabyBear::new(FIXED_BLINDING);
    let fact_commitment = hash_4_to_1(&[fact_hash, sr, blinding, BabyBear::ZERO]);
    let mut row = vec![BabyBear::ZERO; PRED_WIDTH];
    row[INPUT] = v;
    row[SLOT_A] = v;
    row[THRESHOLD] = BabyBear::new(threshold);
    row[DIFF] = v - BabyBear::new(threshold);
    row[FACT_COMMITMENT] = fact_commitment;
    row[PREDICATE_SYM] = pred;
    row[STATE_ROOT] = sr;
    row[FACT_HASH] = fact_hash;
    row[BLINDING] = blinding;
    row
}

fn consistent_trace(diff_val: u32, threshold: u32) -> Vec<Vec<BabyBear>> {
    let row = consistent_row(diff_val, threshold);
    vec![row.clone(), row.clone(), row.clone(), row]
}

/// The honest public inputs for that row: `[threshold, the genuine fact commitment]`.
fn pis(diff_val: u32, threshold: u32) -> Vec<BabyBear> {
    vec![BabyBear::new(threshold), derived_fact(diff_val + threshold)]
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
    assert_eq!(
        desc.trace_width, PRED_WIDTH,
        "the deployed descriptor and the production witness layout must agree on width"
    );
    let two29: u32 = 1 << 29;

    // max in-range diff accepts (non-vacuity: the range genuinely admits large-but-in-range diffs)
    assert!(
        !rejects(&desc, &consistent_trace(two29 - 1, 40), &pis(two29 - 1, 40)),
        "diff = 2^29 - 1 (max in-range, C3/C5 and both weld legs consistent) must be ACCEPTED"
    );

    // first out-of-range diff rejects — pins the boundary at 2^29 (not 2^30/2^31)
    assert!(
        rejects(&desc, &consistent_trace(two29, 40), &pis(two29, 40)),
        "diff = 2^29 (first out-of-range, C3/C5 and both weld legs consistent) must be REJECTED \
         by the range tooth"
    );
}
