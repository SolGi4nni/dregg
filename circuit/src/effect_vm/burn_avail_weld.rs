//! # `burn_avail_weld` — the IN-AIR BURN AVAILABILITY gates with an OVERFLOW-SAFE MULTI-LIMB
//! BORROW SUBTRACTION (the GAP #4 BURN twin — the WELL-SUPPLY-INFLATION forgery close).
//!
//! Faithful Rust twin of the Lean `Dregg2.Circuit.Emit.EffectVmEmitBurn` §8¾ availability weld
//! (`burnVmDescriptorAvail`, `burnAvailGates`, `burnAvailRanges`, `burnAvail_derives_availability`).
//! The bare burn descriptor range-checks ONLY the AFTER balance limbs; its debit gate admits the
//! underflow-wrap forgery (`before=1, amount=1006632961, after=1006632961`: `after − before +
//! amount = p ≡ 0`, `after < 2^30`) that OVER-BURNS ~10^9 — and (the audit's finding,
//! `docs/FINDING-modp-wrap-forgery-audit.md` §2) burn's ledger frame credits the WELL `(a, a)` by
//! the same forged amount, so burn-to-negative INFLATES WELL SUPPLY: mint-from-nothing into the
//! well, STRICTLY WORSE than the transfer twin.
//!
//! ## The fix — the `transfer_avail_weld` borrow chain, UNGATED
//!
//! Decompose `before.bal_lo` / `after.bal_lo` / the burn `amount` (`param::BURN_AMOUNT_LO`) into
//! two 15-bit limbs each (range-checked, bounding every operand to `[0, 2^30) ⊂ [0, p)`) and run
//! the 2-limb BORROW SUBTRACTION `before − amount = after`:
//!
//!  * limb 0: `bef0 − am0 + bb0·2^15 − aft0 = 0`     (`bb0` boolean)
//!  * limb 1: `bef1 − am1 − bb0 + bb1·2^15 − aft1 = 0` (`bb1` boolean)
//!  * NO FINAL BORROW: `bb1 = 0`   ⟺   `before ≥ amount` (AVAILABILITY)
//!
//! Burn has NO credit direction (a burn row ALWAYS debits; there is no `DIRECTION` param), so the
//! borrow gates are UNGATED — the whole debit surface is the forgery surface, and burn needs no
//! credit carry twin (8 witness columns, not the transfer's 10). Every borrow-gate residual stays
//! `< 2^16 < p`, so no residual ever reaches `p` — the wrap is STRUCTURALLY impossible. The
//! previously UNRANGED burn `amount` is now decomposed + range-checked.
//!
//! The LIVE wire object is the Lean-emitted `burnVmDescriptorAvail` lifted through
//! `v3OfFrozenWide` (its 15-bit teeth lower into the width-tagged 15-bit range table); this module
//! is the producer aux-fill + the structural drift twin, byte-for-byte the Lean §8¾ `EmittedExpr`
//! trees.

use super::columns::{
    EFFECT_VM_WIDTH, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, param, state,
};
use crate::lean_descriptor_air::{LeanExpr, RangeSpec, VmConstraint};

/// Limb width: 15 bits keeps every borrow-gate polynomial `< 2^16 < p` (the `vault_weld` payoff).
pub const LIMB_BITS: usize = 15;
const TWO15: i64 = 1 << LIMB_BITS;

// --- availability-weld witness columns (past the base width; Lean `EffectVmEmitBurn.AVAIL_BASE`) ---
/// Base of the burn availability-weld witness block.
pub const AVAIL_BASE: usize = EFFECT_VM_WIDTH; // 188
/// `before.bal_lo` low/high 15-bit limbs.
pub const BEF0: usize = AVAIL_BASE;
pub const BEF1: usize = AVAIL_BASE + 1;
/// `after.bal_lo` low/high 15-bit limbs.
pub const AFT0: usize = AVAIL_BASE + 2;
pub const AFT1: usize = AVAIL_BASE + 3;
/// burn `amount` (`param::BURN_AMOUNT_LO`) low/high 15-bit limbs.
pub const AM0: usize = AVAIL_BASE + 4;
pub const AM1: usize = AVAIL_BASE + 5;
/// The two borrow bits (`BRW1` = the final borrow; `0` ⟺ `before ≥ amount`).
pub const BRW0: usize = AVAIL_BASE + 6;
pub const BRW1: usize = AVAIL_BASE + 7;
/// The widened trace width the hardened burn descriptor declares (borrow chain only — burn has no
/// credit twin, so 8 witness columns, not the transfer's 10). Lean `EffectVmEmitBurn.AVAIL_WIDTH`.
pub const AVAIL_WIDTH: usize = AVAIL_BASE + 8; // 196

/// Absolute before/after `bal_lo` + burn-amount columns the assembly + borrow gates read.
const BEFORE_BAL_LO: usize = STATE_BEFORE_BASE + state::BALANCE_LO;
const AFTER_BAL_LO: usize = STATE_AFTER_BASE + state::BALANCE_LO;
const AMOUNT_COL: usize = PARAM_BASE + param::BURN_AMOUNT_LO;

// --- gate-body builders (byte-for-byte the Lean §8¾ EmittedExpr trees) ---

fn var(c: usize) -> LeanExpr {
    LeanExpr::var(c)
}
fn k(c: i64) -> LeanExpr {
    LeanExpr::constant(c)
}
fn add(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::add(a, b)
}
fn mul(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::mul(a, b)
}
/// Lean `eSub a b = .add a (.mul (.const (-1)) b)`.
fn sub(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    add(a, mul(k(-1), b))
}
fn gate(body: LeanExpr) -> VmConstraint {
    VmConstraint::Gate(body)
}

/// Operand assembly gate: `operand = lo + 2^15·hi` (Lean `gAsmBefore`/`gAsmAfter`/`gAsmAmount`).
fn assembly_gate(operand: usize, lo: usize, hi: usize) -> VmConstraint {
    gate(sub(var(operand), add(var(lo), mul(k(TWO15), var(hi)))))
}
/// Booleanity gate: `b·(b − 1)` (Lean `gBrw0Bool`/`gBrw1Bool`).
fn bool_gate(b: usize) -> VmConstraint {
    gate(mul(var(b), add(var(b), k(-1))))
}

/// **THE BURN AVAILABILITY-WELD GATES** — the exact list (order and all) the Lean `burnAvailGates`
/// builds: the three operand assemblies, the two borrow-bit booleanity gates, the two UNGATED
/// borrow-subtraction limbs, and the UNGATED NO-FINAL-BORROW gate. UNGATED because a burn row is
/// always a debit — the whole surface is the forgery surface.
pub fn burn_avail_gates() -> Vec<VmConstraint> {
    vec![
        assembly_gate(BEFORE_BAL_LO, BEF0, BEF1),
        assembly_gate(AFTER_BAL_LO, AFT0, AFT1),
        assembly_gate(AMOUNT_COL, AM0, AM1),
        bool_gate(BRW0),
        bool_gate(BRW1),
        // limb 0 (UNGATED): bef0 − am0 + bb0·2^15 − aft0
        gate(sub(
            add(sub(var(BEF0), var(AM0)), mul(k(TWO15), var(BRW0))),
            var(AFT0),
        )),
        // limb 1 (UNGATED): bef1 − am1 − bb0 + bb1·2^15 − aft1
        gate(sub(
            add(
                sub(sub(var(BEF1), var(AM1)), var(BRW0)),
                mul(k(TWO15), var(BRW1)),
            ),
            var(AFT1),
        )),
        // no final borrow (UNGATED): bb1  (⟹ before ≥ amount)
        gate(var(BRW1)),
    ]
}

/// **THE BURN AVAILABILITY-WELD RANGE CHECKS** — the operand + amount 15-bit limbs (Lean
/// `burnAvailRanges`). Bounds every operand to `[0, 2^30) ⊂ [0, p)` AND ranges the burn `amount`,
/// closing the unranged-amount hole. Appended to the bare descriptor's ranges.
pub fn burn_avail_ranges() -> Vec<RangeSpec> {
    [BEF0, BEF1, AFT0, AFT1, AM0, AM1]
        .iter()
        .map(|&wire| RangeSpec {
            wire,
            bits: LIMB_BITS,
        })
        .collect()
}

/// **THE PRODUCER AUX-FILL (fallible).** Given one row's `before`/`after` `bal_lo` and the burn
/// `amount`, compute the availability-weld witness columns: the three operand limb decompositions
/// and the two borrow bits of the `before − amount` subtraction. On an honest row
/// (`before ≥ amount`, `before − amount = after`) the borrow chain closes with `bb1 = 0`.
///
/// Returns the eight `(column, value)` writes for the caller to lay into the trace. Errors (fails
/// closed, matching the descriptor's UNSAT) if an operand exceeds the 30-bit window or if the burn
/// over-debits (`amount > before` — the well-supply-inflation forgery has no borrow witness).
pub fn try_fill_burn_avail_aux(
    before_bal_lo: u32,
    after_bal_lo: u32,
    amount: u32,
) -> Result<[(usize, u32); 8], String> {
    for (what, v) in [
        ("before.bal_lo", before_bal_lo),
        ("after.bal_lo", after_bal_lo),
        ("burn amount", amount),
    ] {
        if v >= (1u32 << 30) {
            return Err(format!("{what} {v} exceeds the 30-bit operand window"));
        }
    }
    if before_bal_lo < amount {
        return Err(format!(
            "burn availability: amount {amount} exceeds pre-balance {before_bal_lo} — UNSAT \
             (no borrow witness; the well-supply-inflation forgery)"
        ));
    }

    let split = |v: u32| -> (u32, u32) { (v & 0x7fff, v >> 15) };
    let (bef0, bef1) = split(before_bal_lo);
    let (aft0, aft1) = split(after_bal_lo);
    let (am0, am1) = split(amount);

    let b0 = u32::from(bef0 < am0);
    // limb-1 minuend includes the incoming borrow b0
    let b1 = u32::from(bef1 < am1 + b0);

    Ok([
        (BEF0, bef0),
        (BEF1, bef1),
        (AFT0, aft0),
        (AFT1, aft1),
        (AM0, am0),
        (AM1, am1),
        (BRW0, b0),
        (BRW1, b1),
    ])
}

/// The panicking convenience wrapper of [`try_fill_burn_avail_aux`] (test/tooling ergonomics).
pub fn fill_burn_avail_aux(
    before_bal_lo: u32,
    after_bal_lo: u32,
    amount: u32,
) -> [(usize, u32); 8] {
    try_fill_burn_avail_aux(before_bal_lo, after_bal_lo, amount)
        .unwrap_or_else(|e| panic!("burn avail aux fill: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    /// Evaluate every burn-avail gate against a synthetic row.
    fn gates_hold(row: &[BabyBear]) -> bool {
        burn_avail_gates().iter().all(|c| match c {
            VmConstraint::Gate(body) => eval_lean_expr(body, row) == BabyBear::ZERO,
            other => panic!("unexpected burn-avail constraint kind: {other:?}"),
        })
    }

    fn make_row(before: u32, after: u32, amount: u32) -> Vec<BabyBear> {
        let mut row = vec![BabyBear::ZERO; AVAIL_WIDTH];
        row[BEFORE_BAL_LO] = BabyBear::new(before);
        row[AFTER_BAL_LO] = BabyBear::new(after);
        row[AMOUNT_COL] = BabyBear::new(amount);
        for (c, v) in fill_burn_avail_aux(before, after, amount) {
            row[c] = BabyBear::new(v);
        }
        row
    }

    #[test]
    fn honest_burn_closes_with_no_final_borrow() {
        // before=100, after=70, amount=30 — bb1 must be 0 (100 ≥ 30) and every gate holds.
        let w = fill_burn_avail_aux(100, 70, 30);
        assert_eq!(w[6], (BRW0, 0));
        assert_eq!(w[7], (BRW1, 0));
        assert!(gates_hold(&make_row(100, 70, 30)));
    }

    #[test]
    fn honest_burn_with_limb_borrow() {
        // before=2^15 (limbs (0,1)), amount=1 (limbs (1,0)), after=32767 (limbs (32767,0)).
        // low limb borrows: bef0=0 < am0=1 ⟹ bb0=1; high limb 1 ≥ 0+1 ⟹ bb1=0.
        let w = fill_burn_avail_aux(32768, 32767, 1);
        assert_eq!(w[6], (BRW0, 1));
        assert_eq!(w[7], (BRW1, 0));
        assert!(gates_hold(&make_row(32768, 32767, 1)));
    }

    #[test]
    fn zero_amount_padding_row_holds() {
        // A NoOp/padding row: before == after, amount == 0 — the UNGATED chain must be satisfied
        // (this is what keeps the weld complete over the whole power-of-two trace).
        assert!(gates_hold(&make_row(12345, 12345, 0)));
    }

    #[test]
    fn over_burn_forgery_is_unfillable() {
        // The audit's GAP #4 BURN forgery witness (well-supply inflation): before=1,
        // amount=1006632961 — no borrow witness exists.
        assert!(try_fill_burn_avail_aux(1, 1006632961, 1006632961).is_err());
    }

    #[test]
    fn forged_no_borrow_bit_is_unsat() {
        // Adversarial: lay the forgery operands and force bb1 = 0 anyway (the only value the
        // NO-FINAL-BORROW gate admits) — some borrow-chain gate must then be violated.
        let (before, after, amount) = (1u32, 1006632961u32, 1006632961u32);
        let split = |v: u32| -> (u32, u32) { (v & 0x7fff, v >> 15) };
        let (bef0, bef1) = split(before);
        let (aft0, aft1) = split(after);
        let (am0, am1) = split(amount);
        let mut row = vec![BabyBear::ZERO; AVAIL_WIDTH];
        row[BEFORE_BAL_LO] = BabyBear::new(before);
        row[AFTER_BAL_LO] = BabyBear::new(after);
        row[AMOUNT_COL] = BabyBear::new(amount);
        for (c, v) in [
            (BEF0, bef0),
            (BEF1, bef1),
            (AFT0, aft0),
            (AFT1, aft1),
            (AM0, am0),
            (AM1, am1),
            (BRW0, u32::from(bef0 < am0)),
            (BRW1, 0), // the forged availability claim
        ] {
            row[c] = BabyBear::new(v);
        }
        assert!(
            !gates_hold(&row),
            "the well-supply-inflation forgery must be UNSAT under the burn availability weld"
        );
    }

    #[test]
    fn gate_and_range_counts_match_lean() {
        assert_eq!(burn_avail_gates().len(), 8);
        assert_eq!(burn_avail_ranges().len(), 6);
        assert_eq!(AVAIL_WIDTH, 196);
        assert!(burn_avail_ranges().iter().all(|r| r.bits == 15));
    }
}
