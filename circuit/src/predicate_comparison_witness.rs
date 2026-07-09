//! Rust witness builders for the emitted **arithmetic COMPARISON** descriptors — the `≤` / `>` / `<`
//! / `≠` / `InRange` siblings of [`crate::predicate_arith_witness`] (`≥`). The hand-STARK deletion
//! left these five ops with NO emitted descriptor (fail-closed); their Lean descriptors are authored
//! and byte-pinned in `metatheory/Dregg2/Circuit/Emit/Predicates{Le,Gt,Lt,Neq,InRange}Emit.lean`
//! and dispatched through [`crate::descriptor_by_name::descriptor_by_name`]. This module is the
//! production witness producer for each — the analog of [`crate::predicate_arith_witness`].
//!
//! ## The one mechanism, five DIFF variations
//!
//! Every comparison rides ONE tooth: a `diff` that lands in the range table `[0, 2^29)` iff the
//! comparison holds (a violating value wraps `diff` below zero — out of range — UNSAT). The `≠`
//! case swaps the range tooth for a nonzero-inverse gadget (`diff · diff_inv = 1 ⟺ diff ≠ 0`).
//!
//! | op        | layout width | diff(s)                                    | judge tooth        |
//! |-----------|--------------|--------------------------------------------|--------------------|
//! | `≤` (le)  | 5            | `diff = threshold − value`                 | range `[0,2^29)`   |
//! | `>` (gt)  | 5            | `diff = value − threshold − 1`             | range `[0,2^29)`   |
//! | `<` (lt)  | 5            | `diff = threshold − value − 1`             | range `[0,2^29)`   |
//! | `≠` (neq) | 6            | `diff = value − threshold`, `diff_inv`     | `diff·diff_inv = 1`|
//! | InRange   | 7            | `diff_lo = value − lo`, `diff_hi = hi − value` | two range checks |
//!
//! Each builder is purely MECHANICAL (like `predicate_arith_witness`): it computes the field diffs
//! and lets the DESCRIPTOR be the judge. C3 (`slot = input`) and the C5 diff gate(s) hold BY
//! CONSTRUCTION on every emitted row (so a violating witness isolates the range / nonzero tooth); the
//! PI pins (C1 / C2) refuse a forged public `(threshold|lo|hi, fact_commitment)` at verify.

use crate::field::BabyBear;

/// The range-tooth width shared by the one-sided ops and InRange (`arithmetic.rs` @736: 29 bits).
pub const DIFF_BITS: usize = 29;

/// Dispatched AIR-names (the [`crate::descriptor_by_name`] keys), one per emitted descriptor.
pub const PREDICATE_ARITH_LE_NAME: &str = "dregg-predicate-arith-le::threshold-v1";
pub const PREDICATE_ARITH_GT_NAME: &str = "dregg-predicate-arith-gt::threshold-v1";
pub const PREDICATE_ARITH_LT_NAME: &str = "dregg-predicate-arith-lt::threshold-v1";
pub const PREDICATE_ARITH_NEQ_NAME: &str = "dregg-predicate-arith-neq::threshold-v1";
pub const PREDICATE_ARITH_INRANGE_NAME: &str = "dregg-predicate-arith-inrange::bounds-v1";

/// Reject a non-power-of-two / `< 2` height at build time (the trace-height requirement).
fn check_height(height: usize) -> Result<(), String> {
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "predicate-comparison trace height {height} must be a power of two ≥ 2"
        ));
    }
    Ok(())
}

/// Repeat one logical row to `height` and pair with the public-input vector.
fn spread(
    row: Vec<BabyBear>,
    pis: Vec<BabyBear>,
    height: usize,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    (vec![row; height], pis)
}

// ---- Shared one-sided layout (le / gt / lt): [INPUT, SLOT_A, THRESHOLD, DIFF, FACT_COMMITMENT]. ----
const OS_INPUT: usize = 0;
const OS_SLOT_A: usize = 1;
const OS_THRESHOLD: usize = 2;
const OS_DIFF: usize = 3;
const OS_FACT: usize = 4;
const OS_WIDTH: usize = 5;

fn one_sided_row(value: u64, threshold: u64, diff: BabyBear, fact: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; OS_WIDTH];
    row[OS_INPUT] = BabyBear::from_u64(value);
    row[OS_SLOT_A] = BabyBear::from_u64(value);
    row[OS_THRESHOLD] = BabyBear::from_u64(threshold);
    row[OS_DIFF] = diff;
    row[OS_FACT] = fact;
    row
}

/// **`≤`** — build the trace + PIs `[threshold, fact_commitment]` for `dregg-predicate-arith-le`.
/// `diff = threshold − value`; an honest `value ≤ threshold` lands `diff ∈ [0, 2^29)` and verifies,
/// a `value > threshold` wraps `diff` out of range and the descriptor rejects it.
pub fn predicate_le_witness(
    value: u64,
    threshold: u64,
    fact_commitment: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let diff = BabyBear::from_u64(threshold) - BabyBear::from_u64(value);
    let fact = fact_commitment;
    Ok(spread(
        one_sided_row(value, threshold, diff, fact),
        vec![BabyBear::from_u64(threshold), fact],
        height,
    ))
}

/// **`>`** — `diff = value − threshold − 1`. Honest `value > threshold` ⟹ `diff ≥ 0`.
pub fn predicate_gt_witness(
    value: u64,
    threshold: u64,
    fact_commitment: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let diff = BabyBear::from_u64(value) - BabyBear::from_u64(threshold) - BabyBear::ONE;
    let fact = fact_commitment;
    Ok(spread(
        one_sided_row(value, threshold, diff, fact),
        vec![BabyBear::from_u64(threshold), fact],
        height,
    ))
}

/// **`<`** — `diff = threshold − value − 1`. Honest `value < threshold` ⟹ `diff ≥ 0`.
pub fn predicate_lt_witness(
    value: u64,
    threshold: u64,
    fact_commitment: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let diff = BabyBear::from_u64(threshold) - BabyBear::from_u64(value) - BabyBear::ONE;
    let fact = fact_commitment;
    Ok(spread(
        one_sided_row(value, threshold, diff, fact),
        vec![BabyBear::from_u64(threshold), fact],
        height,
    ))
}

// ---- `≠` layout: [INPUT, SLOT_A, THRESHOLD, DIFF, DIFF_INV, FACT_COMMITMENT]. ----
const NEQ_WIDTH: usize = 6;

/// **`≠`** — `diff = value − threshold`, `diff_inv = diff⁻¹` (field inverse; `0` if `diff = 0`, which
/// makes the nonzero gate `diff·diff_inv = 1` UNSAT — exactly the refusal of `value = threshold`).
pub fn predicate_neq_witness(
    value: u64,
    threshold: u64,
    fact_commitment: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let diff = BabyBear::from_u64(value) - BabyBear::from_u64(threshold);
    // The field inverse when diff ≠ 0; ZERO otherwise (a `value = threshold` witness cannot satisfy
    // `diff·diff_inv = 1` — the nonzero tooth bites).
    let diff_inv = diff.inverse().unwrap_or(BabyBear::ZERO);
    let mut row = vec![BabyBear::ZERO; NEQ_WIDTH];
    row[0] = BabyBear::from_u64(value); // INPUT
    row[1] = BabyBear::from_u64(value); // SLOT_A
    row[2] = BabyBear::from_u64(threshold); // THRESHOLD
    row[3] = diff; // DIFF
    row[4] = diff_inv; // DIFF_INV
    row[5] = fact_commitment; // FACT_COMMITMENT
    Ok(spread(
        row,
        vec![BabyBear::from_u64(threshold), fact_commitment],
        height,
    ))
}

// ---- InRange layout: [INPUT, SLOT_A, LO, HI, DIFF_LO, DIFF_HI, FACT_COMMITMENT]. ----
const IR_WIDTH: usize = 7;

/// **InRange** — build the trace + PIs `[lo, hi, fact_commitment]`. `diff_lo = value − lo`,
/// `diff_hi = hi − value`; both land in `[0, 2^29)` iff `lo ≤ value ≤ hi`. A `value < lo` wraps
/// `diff_lo` out of range; a `value > hi` wraps `diff_hi` out of range — either rejects.
pub fn predicate_inrange_witness(
    value: u64,
    lo: u64,
    hi: u64,
    fact_commitment: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let diff_lo = BabyBear::from_u64(value) - BabyBear::from_u64(lo);
    let diff_hi = BabyBear::from_u64(hi) - BabyBear::from_u64(value);
    let mut row = vec![BabyBear::ZERO; IR_WIDTH];
    row[0] = BabyBear::from_u64(value); // INPUT
    row[1] = BabyBear::from_u64(value); // SLOT_A
    row[2] = BabyBear::from_u64(lo); // LO
    row[3] = BabyBear::from_u64(hi); // HI
    row[4] = diff_lo; // DIFF_LO
    row[5] = diff_hi; // DIFF_HI
    row[6] = fact_commitment; // FACT_COMMITMENT
    Ok(spread(
        row,
        vec![
            BabyBear::from_u64(lo),
            BabyBear::from_u64(hi),
            fact_commitment,
        ],
        height,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use std::panic::AssertUnwindSafe;

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        matches!(r, Err(_) | Ok(Err(_)))
    }

    /// `true` iff `(trace, pis)` is ACCEPTED end-to-end (prove AND verify succeed).
    fn accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        matches!(r, Ok(Ok(())))
    }

    /// All five names dispatch to a well-shaped descriptor with the right width / PI count.
    #[test]
    fn all_comparison_names_dispatch_with_expected_shape() {
        for (name, w, pi) in [
            (PREDICATE_ARITH_LE_NAME, 5, 2),
            (PREDICATE_ARITH_GT_NAME, 5, 2),
            (PREDICATE_ARITH_LT_NAME, 5, 2),
            (PREDICATE_ARITH_NEQ_NAME, 6, 2),
            (PREDICATE_ARITH_INRANGE_NAME, 7, 3),
        ] {
            let desc = descriptor_by_name(name).unwrap_or_else(|| panic!("{name} must dispatch"));
            assert_eq!(desc.name, name);
            assert_eq!(desc.trace_width, w, "{name} width");
            assert_eq!(desc.public_input_count, pi, "{name} PI count");
        }
    }

    #[test]
    fn le_honest_accepts_violation_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_LE_NAME).expect("dispatch");
        let fact = BabyBear::new(12345);
        // honest: 40 ≤ 100 accepts.
        let (t, p) = predicate_le_witness(40, 100, fact, 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "40 ≤ 100 must ACCEPT");
        // violation: 110 > 100 rejects (diff wraps out of range).
        let (bt, bp) = predicate_le_witness(110, 100, fact, 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "110 ≤ 100 must REJECT");
        // forged PI: honest trace, forged threshold rejects (C1).
        let forged = vec![BabyBear::new(99), fact];
        assert!(
            rejects(&desc, &t, &forged),
            "forged threshold must REJECT (C1)"
        );
    }

    #[test]
    fn gt_honest_accepts_violation_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_GT_NAME).expect("dispatch");
        let fact = BabyBear::new(777);
        let (t, p) = predicate_gt_witness(101, 40, fact, 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "101 > 40 must ACCEPT");
        // equal value is NOT strictly greater — rejects (diff = -1 wraps).
        let (bt, bp) = predicate_gt_witness(40, 40, fact, 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "40 > 40 must REJECT");
        // below also rejects.
        let (bt2, bp2) = predicate_gt_witness(30, 40, fact, 4).expect("witness");
        assert!(rejects(&desc, &bt2, &bp2), "30 > 40 must REJECT");
    }

    #[test]
    fn lt_honest_accepts_violation_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_LT_NAME).expect("dispatch");
        let fact = BabyBear::new(888);
        let (t, p) = predicate_lt_witness(40, 101, fact, 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "40 < 101 must ACCEPT");
        let (bt, bp) = predicate_lt_witness(101, 101, fact, 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "101 < 101 must REJECT");
        let (bt2, bp2) = predicate_lt_witness(150, 101, fact, 4).expect("witness");
        assert!(rejects(&desc, &bt2, &bp2), "150 < 101 must REJECT");
    }

    #[test]
    fn neq_honest_accepts_equal_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NEQ_NAME).expect("dispatch");
        let fact = BabyBear::new(4242);
        // honest: 41 ≠ 40 accepts (diff = 1 has an inverse).
        let (t, p) = predicate_neq_witness(41, 40, fact, 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "41 ≠ 40 must ACCEPT");
        // a larger genuine inequality also accepts (real field inverse).
        let (t2, p2) = predicate_neq_witness(1000, 7, fact, 4).expect("witness");
        assert!(accepts(&desc, &t2, &p2), "1000 ≠ 7 must ACCEPT");
        // violation: 40 = 40 rejects (diff = 0, no inverse → nonzero gate UNSAT).
        let (bt, bp) = predicate_neq_witness(40, 40, fact, 4).expect("witness");
        assert!(
            rejects(&desc, &bt, &bp),
            "40 ≠ 40 must REJECT (nonzero tooth)"
        );
    }

    #[test]
    fn inrange_honest_accepts_out_of_range_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_INRANGE_NAME).expect("dispatch");
        let fact = BabyBear::new(55);
        // honest: 10 ≤ 40 ≤ 100 accepts.
        let (t, p) = predicate_inrange_witness(40, 10, 100, fact, 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "10 ≤ 40 ≤ 100 must ACCEPT");
        // below lo: 5 < 10 rejects (diff_lo wraps).
        let (bt, bp) = predicate_inrange_witness(5, 10, 100, fact, 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "5 < 10 must REJECT (low tooth)");
        // above hi: 150 > 100 rejects (diff_hi wraps).
        let (bt2, bp2) = predicate_inrange_witness(150, 10, 100, fact, 4).expect("witness");
        assert!(
            rejects(&desc, &bt2, &bp2),
            "150 > 100 must REJECT (high tooth)"
        );
        // boundary inclusivity: value = lo and value = hi accept.
        let (lo_t, lo_p) = predicate_inrange_witness(10, 10, 100, fact, 4).expect("witness");
        assert!(
            accepts(&desc, &lo_t, &lo_p),
            "value = lo must ACCEPT (inclusive)"
        );
        let (hi_t, hi_p) = predicate_inrange_witness(100, 10, 100, fact, 4).expect("witness");
        assert!(
            accepts(&desc, &hi_t, &hi_p),
            "value = hi must ACCEPT (inclusive)"
        );
    }

    #[test]
    fn malformed_heights_refuse() {
        let fact = BabyBear::new(1);
        assert!(predicate_le_witness(1, 2, fact, 3).is_err());
        assert!(predicate_gt_witness(1, 2, fact, 1).is_err());
        assert!(predicate_neq_witness(1, 2, fact, 0).is_err());
        assert!(predicate_inrange_witness(1, 0, 2, fact, 6).is_err()); // 6 not a power of two
        assert!(predicate_inrange_witness(1, 0, 2, fact, 8).is_ok()); // 8 is
    }
}
