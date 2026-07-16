//! Rust witness builders for the emitted **arithmetic COMPARISON** descriptors — the `≤` / `>` / `<`
//! / `≠` / `InRange` siblings of [`crate::predicate_arith_witness`] (`≥`). Their Lean descriptors are
//! authored and byte-pinned in `metatheory/Dregg2/Circuit/Emit/Predicates{Le,Gt,Lt,Neq,InRange}Emit.lean`
//! and dispatched through [`crate::descriptor_by_name::descriptor_by_name`]. This module is the
//! production witness producer for each — the analog of [`crate::predicate_arith_witness`].
//!
//! ## Each descriptor proves a CONJUNCTION with a shared variable
//!
//! A comparison alone (`value ≤ threshold`) is worthless: it is a claim about a number the prover
//! chose. What makes it a claim about TOKEN STATE is the second conjunct —
//! `fact_commitment = hash_4_to_1([hash_fact(pred, [value, t1, t2]), state_root, blinding, 0])` — and
//! the variable the two conjuncts share is `INPUT` (col 0). Both are in the circuit.
//!
//! The commitment is BLINDED by a private witness column, and that costs the weld nothing: blinding
//! moves the commitment's `blinding` slot, the weld pins its `fact_hash` slot. Two showings of the
//! same fact are unlinkable; both still open to the value compared. Privacy and soundness here are
//! independent, not traded. See [`crate::predicate_arith_witness::Blinding`].
//!
//! **These five descriptors used to carry only the first conjunct.** `fact_commitment` was a
//! pass-through public input in a constraint set DISJOINT from the compared column, so a prover could
//! satisfy the comparison on a value of its choosing while presenting the honest, verifier-expected
//! commitment for an UNRELATED value — the exact forgery the `≥` weld closed in M13, which the whole
//! family shared (`descriptor_by_name.rs` named it a follow-up). M14 welds the family.
//!
//! ## The one comparison mechanism, five DIFF variations — plus the uniform weld
//!
//! Every comparison rides ONE tooth: a `diff` that lands in the range table `[0, 2^29)` iff the
//! comparison holds (a violating value wraps `diff` below zero — out of range — UNSAT). The `≠` case
//! swaps the range tooth for a nonzero-inverse gadget (`diff · diff_inv = 1 ⟺ diff ≠ 0`).
//!
//! | op        | welded width | diff(s)                                        | judge tooth        |
//! |-----------|--------------|------------------------------------------------|--------------------|
//! | `≤` (le)  | 25           | `diff = threshold − value`                     | range `[0,2^29)`   |
//! | `>` (gt)  | 25           | `diff = value − threshold − 1`                 | range `[0,2^29)`   |
//! | `<` (lt)  | 25           | `diff = threshold − value − 1`                 | range `[0,2^29)`   |
//! | `≠` (neq) | 26           | `diff = value − threshold`, `diff_inv`         | `diff·diff_inv = 1`|
//! | InRange   | 27           | `diff_lo = value − lo`, `diff_hi = hi − value` | two range checks   |
//!
//! (Each width is one MORE than its pre-blinding value: the last column is `BLINDING`.)
//!
//! On TOP of that tooth every one of them now carries the **VALUE↔FACT WELD**: two Poseidon2 chip
//! lookups forcing `FACT_HASH = hash_fact(PREDICATE_SYM, [INPUT, TERM1, TERM2])` over the SAME
//! `INPUT` the comparison bounds, and
//! `FACT_COMMITMENT = hash_4_to_1([FACT_HASH, STATE_ROOT, BLINDING, 0])`. The `≤`/`>`/`<` layouts are
//! byte-identical to `≥` (weld cols 5..23, `BLINDING` at 24); `≠` carries `DIFF_INV` so its weld
//! starts at col 6; InRange carries `LO`/`HI`/`DIFF_LO`/`DIFF_HI` so its weld starts at col 7.
//!
//! Accordingly the fact commitment is **not an argument to these builders — it is an OUTPUT.** A
//! caller supplies the fact's identity ([`FactBinding`]) and the value; the commitment is COMPUTED.
//! There is no signature through which "the value I compare" and "the commitment I present" can
//! disagree: the forgery is unrepresentable at the API, not merely refused.
//!
//! Each builder stays purely MECHANICAL: it computes the field diffs and lets the DESCRIPTOR be the
//! judge. C3 (`slot = input`) and the C5 diff gate(s) hold BY CONSTRUCTION on every emitted row (so a
//! violating witness isolates the range / nonzero tooth); the PI pins (C1 / C2) refuse a forged public
//! `(threshold|lo|hi, fact_commitment)` at verify. The 2×7 chip LANE columns are left zero — the
//! prover's `trace_with_chip_lanes` fills them (`descriptor_ir2.rs::fill_chip_lanes`). What a producer
//! MUST fill is the two DIGEST columns (`FACT_COMMITMENT` and `FACT_HASH`); those are this module's
//! job, and they are the weld.

use crate::field::BabyBear;
use crate::predicate_arith_witness::{Blinding, FactBinding};

/// The range-tooth width shared by the one-sided ops and InRange (`arithmetic.rs` @736: 29 bits).
pub const DIFF_BITS: usize = 29;

/// Dispatched AIR-names (the [`crate::descriptor_by_name`] keys), one per emitted descriptor.
pub const PREDICATE_ARITH_LE_NAME: &str = "dregg-predicate-arith-le::threshold-v1";
pub const PREDICATE_ARITH_GT_NAME: &str = "dregg-predicate-arith-gt::threshold-v1";
pub const PREDICATE_ARITH_LT_NAME: &str = "dregg-predicate-arith-lt::threshold-v1";
pub const PREDICATE_ARITH_NEQ_NAME: &str = "dregg-predicate-arith-neq::threshold-v1";
pub const PREDICATE_ARITH_INRANGE_NAME: &str = "dregg-predicate-arith-inrange::bounds-v1";

// ---- Shared ONE-SIDED welded layout (le / gt / lt) — identical geometry to the `≥` descriptor.
// Must match `Predicates{Le,Gt,Lt}Emit.lean` §1.
/// The private compared value; ALSO `terms[0]` of the hashed fact (the weld's leg-1 input).
pub const OS_INPUT: usize = 0;
/// The compiled expression-A result slot (`= INPUT` for a bare-`Input` expression, C3).
pub const OS_SLOT_A: usize = 1;
/// The public comparison target, PI-bound to PI slot 0.
pub const OS_THRESHOLD: usize = 2;
/// The comparison difference, range-proved into `[0, 2^29)`.
pub const OS_DIFF: usize = 3;
/// The fact commitment, PI-bound to PI slot 1 AND forced by the weld's leg 2.
pub const OS_FACT_COMMITMENT: usize = 4;
/// The predicate symbol entering `hash_fact` (the weld's leg-1 input 0).
pub const OS_PREDICATE_SYM: usize = 5;
/// The fact's second term.
pub const OS_TERM1: usize = 6;
/// The fact's third term.
pub const OS_TERM2: usize = 7;
/// The token state root the commitment covers (the weld's leg-2 input 1).
pub const OS_STATE_ROOT: usize = 8;
/// `hash_fact(PREDICATE_SYM, [INPUT, TERM1, TERM2])` — leg 1's digest, leg 2's input 0.
pub const OS_FACT_HASH: usize = 9;
/// The welded one-sided base-trace width (5 predicate + 5 fact witness + 2×7 chip lanes).
/// The commitment BLINDING factor — a PRIVATE witness column, the weld's leg-2 input 2
/// (`le` / `gt` / `lt` layout). See [`crate::predicate_arith_witness::Blinding`].
pub const OS_BLINDING: usize = 24;
/// The welded one-sided base-trace width, incl. the blinding factor.
pub const OS_WIDTH: usize = 25;

// ---- `≠` welded layout: the one-sided layout with `DIFF_INV` inserted at col 4.
pub const NEQ_INPUT: usize = 0;
pub const NEQ_SLOT_A: usize = 1;
pub const NEQ_THRESHOLD: usize = 2;
pub const NEQ_DIFF: usize = 3;
/// The claimed inverse of `DIFF`; the degree-2 gate `DIFF · DIFF_INV = 1` forces `DIFF ≠ 0`.
pub const NEQ_DIFF_INV: usize = 4;
pub const NEQ_FACT_COMMITMENT: usize = 5;
pub const NEQ_PREDICATE_SYM: usize = 6;
pub const NEQ_TERM1: usize = 7;
pub const NEQ_TERM2: usize = 8;
pub const NEQ_STATE_ROOT: usize = 9;
pub const NEQ_FACT_HASH: usize = 10;
/// The welded `≠` base-trace width (6 predicate + 5 fact witness + 2×7 chip lanes).
/// The commitment BLINDING factor — a PRIVATE witness column (`neq` layout).
pub const NEQ_BLINDING: usize = 25;
/// The welded `≠` base-trace width, incl. the blinding factor.
pub const NEQ_WIDTH: usize = 26;

// ---- InRange welded layout: two bounds + two diffs, so the weld starts at col 7.
pub const IR_INPUT: usize = 0;
pub const IR_SLOT_A: usize = 1;
pub const IR_LO: usize = 2;
pub const IR_HI: usize = 3;
pub const IR_DIFF_LO: usize = 4;
pub const IR_DIFF_HI: usize = 5;
pub const IR_FACT_COMMITMENT: usize = 6;
pub const IR_PREDICATE_SYM: usize = 7;
pub const IR_TERM1: usize = 8;
pub const IR_TERM2: usize = 9;
pub const IR_STATE_ROOT: usize = 10;
pub const IR_FACT_HASH: usize = 11;
/// The commitment BLINDING factor — a PRIVATE witness column (`InRange` layout).
pub const IR_BLINDING: usize = 26;
/// The welded InRange base-trace width (7 predicate + 5 fact witness + 2×7 chip lanes + blinding).
pub const IR_WIDTH: usize = 27;

/// Reject a non-power-of-two / `< 2` height at build time (the trace-height requirement).
fn check_height(height: usize) -> Result<(), String> {
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "predicate-comparison trace height {height} must be a power of two ≥ 2"
        ));
    }
    Ok(())
}

/// The column indices of one descriptor's five fact-witness columns + its commitment digest.
struct WeldCols {
    fact_commitment: usize,
    predicate_sym: usize,
    term1: usize,
    term2: usize,
    state_root: usize,
    fact_hash: usize,
    blinding: usize,
}

/// **THE WELD, producer side.** Write the five fact-witness columns and BOTH digest columns the two
/// Poseidon2 chip lookups bind, computing them from `value_f` — which is what makes the commitment a
/// statement ABOUT the compared number. Returns the computed fact commitment (the PI the verifier
/// independently derives from trusted token state).
///
/// Byte-equal to the production out-of-circuit binding
/// ([`crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment`] over
/// [`crate::poseidon2::hash_fact`]) — pinned by KAT asserts in this module's tests, so the in-circuit
/// chip image and the production binding are proven equal rather than assumed.
fn fill_weld(
    row: &mut [BabyBear],
    value_f: BabyBear,
    fact: FactBinding,
    blinding: Blinding,
    c: WeldCols,
) -> BabyBear {
    let fact_hash = fact.fact_hash_of(value_f);
    let fact_commitment = fact.commitment_of(value_f, blinding);
    // THE BLINDING FACTOR REACHES THE PROOF: leg 2 is an arity-4 chip lookup over
    // `[FACT_HASH, STATE_ROOT, BLINDING, 0]`, so this column is a constrained input to the
    // permutation. Leaving it zero while committing under a nonzero blinding makes the lookup image
    // disagree with the commitment column — REFUSED, never silently unblinded.
    row[c.blinding] = blinding.as_field();
    row[c.fact_commitment] = fact_commitment;
    row[c.predicate_sym] = fact.predicate_sym;
    row[c.term1] = fact.term1;
    row[c.term2] = fact.term2;
    row[c.state_root] = fact.state_root;
    row[c.fact_hash] = fact_hash;
    fact_commitment
}

/// The one-sided weld column map (le / gt / lt).
fn os_weld_cols() -> WeldCols {
    WeldCols {
        fact_commitment: OS_FACT_COMMITMENT,
        predicate_sym: OS_PREDICATE_SYM,
        term1: OS_TERM1,
        term2: OS_TERM2,
        state_root: OS_STATE_ROOT,
        fact_hash: OS_FACT_HASH,
        blinding: OS_BLINDING,
    }
}

/// Build a welded one-sided row: the comparison columns + the value↔fact weld. Returns the row and
/// the COMPUTED fact commitment.
fn one_sided_row(
    value: u64,
    threshold: u64,
    diff: BabyBear,
    fact: FactBinding,
    blinding: Blinding,
) -> (Vec<BabyBear>, BabyBear) {
    let value_f = BabyBear::from_u64(value);
    let mut row = vec![BabyBear::ZERO; OS_WIDTH];
    row[OS_INPUT] = value_f;
    row[OS_SLOT_A] = value_f;
    row[OS_THRESHOLD] = BabyBear::from_u64(threshold);
    row[OS_DIFF] = diff;
    let fact_commitment = fill_weld(&mut row, value_f, fact, blinding, os_weld_cols());
    // Cols 10..=23 (the 2×7 chip out-lanes) stay zero: the prover's `fill_chip_lanes` fills them.
    (row, fact_commitment)
}

/// Assemble a one-sided witness: repeat the logical row to `height`, PIs `[threshold, commitment]`.
fn one_sided_witness(
    value: u64,
    threshold: u64,
    diff: BabyBear,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let (row, fact_commitment) = one_sided_row(value, threshold, diff, fact, blinding);
    let pis = vec![BabyBear::from_u64(threshold), fact_commitment];
    Ok((vec![row; height], pis))
}

/// **`≤`** — build the trace + PIs `[threshold, fact_commitment]` for `dregg-predicate-arith-le`.
/// `diff = threshold − value`; an honest `value ≤ threshold` lands `diff ∈ [0, 2^29)` and verifies,
/// a `value > threshold` wraps `diff` out of range and the descriptor rejects it. The fact commitment
/// is COMPUTED from `value` and `fact` and returned as `pis[1]`.
pub fn predicate_le_witness(
    value: u64,
    threshold: u64,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let diff = BabyBear::from_u64(threshold) - BabyBear::from_u64(value);
    one_sided_witness(value, threshold, diff, fact, blinding, height)
}

/// **`>`** — `diff = value − threshold − 1`. Honest `value > threshold` ⟹ `diff ≥ 0`.
pub fn predicate_gt_witness(
    value: u64,
    threshold: u64,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let diff = BabyBear::from_u64(value) - BabyBear::from_u64(threshold) - BabyBear::ONE;
    one_sided_witness(value, threshold, diff, fact, blinding, height)
}

/// **`<`** — `diff = threshold − value − 1`. Honest `value < threshold` ⟹ `diff ≥ 0`.
pub fn predicate_lt_witness(
    value: u64,
    threshold: u64,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let diff = BabyBear::from_u64(threshold) - BabyBear::from_u64(value) - BabyBear::ONE;
    one_sided_witness(value, threshold, diff, fact, blinding, height)
}

/// **`≠`** — `diff = value − threshold`, `diff_inv = diff⁻¹` (field inverse; `0` if `diff = 0`, which
/// makes the nonzero gate `diff·diff_inv = 1` UNSAT — exactly the refusal of `value = threshold`).
/// The fact commitment is COMPUTED and returned as `pis[1]`.
pub fn predicate_neq_witness(
    value: u64,
    threshold: u64,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let value_f = BabyBear::from_u64(value);
    let diff = value_f - BabyBear::from_u64(threshold);
    // The field inverse when diff ≠ 0; ZERO otherwise (a `value = threshold` witness cannot satisfy
    // `diff·diff_inv = 1` — the nonzero tooth bites).
    let diff_inv = diff.inverse().unwrap_or(BabyBear::ZERO);
    let mut row = vec![BabyBear::ZERO; NEQ_WIDTH];
    row[NEQ_INPUT] = value_f;
    row[NEQ_SLOT_A] = value_f;
    row[NEQ_THRESHOLD] = BabyBear::from_u64(threshold);
    row[NEQ_DIFF] = diff;
    row[NEQ_DIFF_INV] = diff_inv;
    let fact_commitment = fill_weld(
        &mut row,
        value_f,
        fact,
        blinding,
        WeldCols {
            fact_commitment: NEQ_FACT_COMMITMENT,
            predicate_sym: NEQ_PREDICATE_SYM,
            term1: NEQ_TERM1,
            term2: NEQ_TERM2,
            state_root: NEQ_STATE_ROOT,
            fact_hash: NEQ_FACT_HASH,
            blinding: NEQ_BLINDING,
        },
    );
    let pis = vec![BabyBear::from_u64(threshold), fact_commitment];
    Ok((vec![row; height], pis))
}

/// **InRange** — build the trace + PIs `[lo, hi, fact_commitment]`. `diff_lo = value − lo`,
/// `diff_hi = hi − value`; both land in `[0, 2^29)` iff `lo ≤ value ≤ hi`. A `value < lo` wraps
/// `diff_lo` out of range; a `value > hi` wraps `diff_hi` out of range — either rejects. The fact
/// commitment is COMPUTED and returned as `pis[2]`.
pub fn predicate_inrange_witness(
    value: u64,
    lo: u64,
    hi: u64,
    fact: FactBinding,
    blinding: Blinding,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    check_height(height)?;
    let value_f = BabyBear::from_u64(value);
    let mut row = vec![BabyBear::ZERO; IR_WIDTH];
    row[IR_INPUT] = value_f;
    row[IR_SLOT_A] = value_f;
    row[IR_LO] = BabyBear::from_u64(lo);
    row[IR_HI] = BabyBear::from_u64(hi);
    row[IR_DIFF_LO] = value_f - BabyBear::from_u64(lo);
    row[IR_DIFF_HI] = BabyBear::from_u64(hi) - value_f;
    let fact_commitment = fill_weld(
        &mut row,
        value_f,
        fact,
        blinding,
        WeldCols {
            fact_commitment: IR_FACT_COMMITMENT,
            predicate_sym: IR_PREDICATE_SYM,
            term1: IR_TERM1,
            term2: IR_TERM2,
            state_root: IR_STATE_ROOT,
            fact_hash: IR_FACT_HASH,
            blinding: IR_BLINDING,
        },
    );
    let pis = vec![
        BabyBear::from_u64(lo),
        BabyBear::from_u64(hi),
        fact_commitment,
    ];
    Ok((vec![row; height], pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, TID_P2, VmConstraint2, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::refusal::{Outcome, classify};

    /// A REAL, non-zero per-presentation blinding — the DEFAULT these tests are driven under, so
    /// every tooth below is exercised in the deployed (blinded) posture rather than at the
    /// degenerate `Blinding::NONE`. Not a `const` because `BabyBear::new` is not a `const fn`.
    fn test_blinding() -> Blinding {
        Blinding(BabyBear::new(0xB11D1))
    }

    /// The scenario's fact identity, shared by the tests below.
    fn fact() -> FactBinding {
        FactBinding {
            predicate_sym: BabyBear::new(0x9E),
            term1: BabyBear::new(0x11),
            term2: BabyBear::new(0x22),
            state_root: BabyBear::new(0x57A7E),
        }
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
    /// `classify` REDs on any panic that is NOT the p3 debug prover's documented unsat verdict, so a
    /// stray unwrap can never launder itself as a refusal.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// `true` iff `(trace, pis)` is ACCEPTED end-to-end (prove AND verify succeed).
    fn accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        !rejects(desc, trace, pis)
    }

    /// All five names dispatch to the LEAN-EMITTED WELDED shape: the welded width, the right PI
    /// count, and **both Poseidon2 weld legs**.
    ///
    /// The `poseidon2_lookups == 2` assert is the structural anti-fork gate. Its predecessor asserted
    /// widths 5/6/7 with no chip check — which RATIFIED the absence of the weld, so restoring the
    /// Lean descriptor would have turned a green test red. A shape assert must pin the shape the
    /// SOURCE OF TRUTH emits, never the shape that happens to be on disk.
    #[test]
    fn all_comparison_names_dispatch_with_welded_shape() {
        for (name, w, pi) in [
            (PREDICATE_ARITH_LE_NAME, OS_WIDTH, 2),
            (PREDICATE_ARITH_GT_NAME, OS_WIDTH, 2),
            (PREDICATE_ARITH_LT_NAME, OS_WIDTH, 2),
            (PREDICATE_ARITH_NEQ_NAME, NEQ_WIDTH, 2),
            (PREDICATE_ARITH_INRANGE_NAME, IR_WIDTH, 3),
        ] {
            let desc = descriptor_by_name(name).unwrap_or_else(|| panic!("{name} must dispatch"));
            assert_eq!(desc.name, name);
            assert_eq!(desc.trace_width, w, "{name} welded width");
            assert_eq!(desc.public_input_count, pi, "{name} PI count");
            let poseidon2_lookups = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count();
            assert_eq!(
                poseidon2_lookups, 2,
                "{name}: the VALUE<->FACT WELD — leg 1 (fact hash) + leg 2 (fact commitment)"
            );
        }
    }

    /// THE KAT: the commitment each builder computes for the in-circuit weld is byte-equal to the
    /// production out-of-circuit binding a verifier derives from token state. Without this, the
    /// circuit could be self-consistently welded to a hash nobody else computes.
    #[test]
    fn computed_commitments_match_production_binding() {
        let f = fact();
        let expected = f.commitment_of(BabyBear::from_u64(40), test_blinding());
        let (_, p) = predicate_le_witness(40, 100, f, test_blinding(), 4).expect("le witness");
        assert_eq!(
            p[1], expected,
            "le commitment must be the production binding"
        );
        let (_, p) = predicate_lt_witness(40, 101, f, test_blinding(), 4).expect("lt witness");
        assert_eq!(
            p[1], expected,
            "lt commitment must be the production binding"
        );
        let (_, p) =
            predicate_inrange_witness(40, 10, 100, f, test_blinding(), 4).expect("inrange witness");
        assert_eq!(
            p[2], expected,
            "inrange commitment must be the production binding"
        );
        let (_, p) = predicate_neq_witness(40, 7, f, test_blinding(), 4).expect("neq witness");
        assert_eq!(
            p[1], expected,
            "neq commitment must be the production binding"
        );
        let (_, p) = predicate_gt_witness(101, 40, f, test_blinding(), 4).expect("gt witness");
        assert_eq!(
            p[1],
            f.commitment_of(BabyBear::from_u64(101), test_blinding()),
            "gt commitment must be the production binding"
        );
    }

    #[test]
    fn le_honest_accepts_violation_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_LE_NAME).expect("dispatch");
        let f = fact();
        // honest: 40 ≤ 100 accepts.
        let (t, p) = predicate_le_witness(40, 100, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "40 ≤ 100 must ACCEPT");
        // violation: 110 > 100 rejects (diff wraps out of range).
        let (bt, bp) = predicate_le_witness(110, 100, f, test_blinding(), 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "110 ≤ 100 must REJECT");
        // forged PI: honest trace, forged threshold rejects (C1).
        assert!(
            rejects(&desc, &t, &[BabyBear::new(99), p[1]]),
            "forged threshold must REJECT (C1)"
        );
        // forged PI: forged fact commitment rejects (C2).
        assert!(
            rejects(&desc, &t, &[BabyBear::new(100), BabyBear::new(999)]),
            "forged fact commitment must REJECT (C2)"
        );
    }

    #[test]
    fn gt_honest_accepts_violation_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_GT_NAME).expect("dispatch");
        let f = fact();
        let (t, p) = predicate_gt_witness(101, 40, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "101 > 40 must ACCEPT");
        // equal value is NOT strictly greater — rejects (diff = -1 wraps).
        let (bt, bp) = predicate_gt_witness(40, 40, f, test_blinding(), 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "40 > 40 must REJECT");
        let (bt2, bp2) = predicate_gt_witness(30, 40, f, test_blinding(), 4).expect("witness");
        assert!(rejects(&desc, &bt2, &bp2), "30 > 40 must REJECT");
    }

    #[test]
    fn lt_honest_accepts_violation_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_LT_NAME).expect("dispatch");
        let f = fact();
        let (t, p) = predicate_lt_witness(40, 101, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "40 < 101 must ACCEPT");
        let (bt, bp) = predicate_lt_witness(101, 101, f, test_blinding(), 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "101 < 101 must REJECT");
        let (bt2, bp2) = predicate_lt_witness(150, 101, f, test_blinding(), 4).expect("witness");
        assert!(rejects(&desc, &bt2, &bp2), "150 < 101 must REJECT");
    }

    #[test]
    fn neq_honest_accepts_equal_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NEQ_NAME).expect("dispatch");
        let f = fact();
        // honest: 41 ≠ 40 accepts (diff = 1 has an inverse).
        let (t, p) = predicate_neq_witness(41, 40, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "41 ≠ 40 must ACCEPT");
        // a larger genuine inequality also accepts (real field inverse).
        let (t2, p2) = predicate_neq_witness(1000, 7, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &t2, &p2), "1000 ≠ 7 must ACCEPT");
        // violation: 40 = 40 rejects (diff = 0, no inverse → nonzero gate UNSAT).
        let (bt, bp) = predicate_neq_witness(40, 40, f, test_blinding(), 4).expect("witness");
        assert!(
            rejects(&desc, &bt, &bp),
            "40 ≠ 40 must REJECT (nonzero tooth)"
        );
    }

    #[test]
    fn inrange_honest_accepts_out_of_range_rejects() {
        let desc = descriptor_by_name(PREDICATE_ARITH_INRANGE_NAME).expect("dispatch");
        let f = fact();
        // honest: 10 ≤ 40 ≤ 100 accepts.
        let (t, p) =
            predicate_inrange_witness(40, 10, 100, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &t, &p), "10 ≤ 40 ≤ 100 must ACCEPT");
        // below lo: 5 < 10 rejects (diff_lo wraps).
        let (bt, bp) =
            predicate_inrange_witness(5, 10, 100, f, test_blinding(), 4).expect("witness");
        assert!(rejects(&desc, &bt, &bp), "5 < 10 must REJECT (low tooth)");
        // above hi: 150 > 100 rejects (diff_hi wraps).
        let (bt2, bp2) =
            predicate_inrange_witness(150, 10, 100, f, test_blinding(), 4).expect("witness");
        assert!(
            rejects(&desc, &bt2, &bp2),
            "150 > 100 must REJECT (high tooth)"
        );
        // boundary inclusivity: value = lo and value = hi accept.
        let (lo_t, lo_p) =
            predicate_inrange_witness(10, 10, 100, f, test_blinding(), 4).expect("witness");
        assert!(
            accepts(&desc, &lo_t, &lo_p),
            "value = lo must ACCEPT (inclusive)"
        );
        let (hi_t, hi_p) =
            predicate_inrange_witness(100, 10, 100, f, test_blinding(), 4).expect("witness");
        assert!(
            accepts(&desc, &hi_t, &hi_p),
            "value = hi must ACCEPT (inclusive)"
        );
    }

    /// THE WELD, leg 1 (le): a tampered `FACT_HASH` that is not `hash_fact(pred, [input, ..])` breaks
    /// the arity-7 chip lookup → REJECTED. The tamper is propagated to the commitment column and the
    /// PI so leg 2 stays self-consistent, isolating leg 1 as the only violated relation.
    #[test]
    fn tampered_fact_hash_refuses_on_weld_leg1() {
        let desc = descriptor_by_name(PREDICATE_ARITH_LE_NAME).expect("dispatch");
        let f = fact();
        let (mut trace, pis) =
            predicate_le_witness(40, 100, f, test_blinding(), 4).expect("witness");
        assert!(accepts(&desc, &trace, &pis), "honest accepts (non-vacuity)");

        let forged_hash = BabyBear::new(0xBADF00D);
        let forged_commit = crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment(
            forged_hash,
            f.state_root,
            test_blinding().as_field(),
        );
        for row in &mut trace {
            row[OS_FACT_HASH] = forged_hash;
            row[OS_FACT_COMMITMENT] = forged_commit;
        }
        assert!(
            rejects(&desc, &trace, &[pis[0], forged_commit]),
            "a FACT_HASH that is not hash_fact(PREDICATE_SYM, [INPUT, TERM1, TERM2]) must be \
             REJECTED (weld leg 1)"
        );
    }

    #[test]
    fn malformed_heights_refuse() {
        let f = fact();
        assert!(predicate_le_witness(1, 2, f, test_blinding(), 3).is_err());
        assert!(predicate_gt_witness(1, 2, f, test_blinding(), 1).is_err());
        assert!(predicate_neq_witness(1, 2, f, test_blinding(), 0).is_err());
        assert!(predicate_inrange_witness(1, 0, 2, f, test_blinding(), 6).is_err()); // 6 not a power of two
        assert!(predicate_inrange_witness(1, 0, 2, f, test_blinding(), 8).is_ok()); // 8 is
    }
}
