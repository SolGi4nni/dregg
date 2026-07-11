//! # `transfer_avail_weld` — the IN-AIR TRANSFER-DEBIT AVAILABILITY gates with an OVERFLOW-SAFE
//! MULTI-LIMB BORROW SUBTRACTION (the GAP #4 close, STAGED).
//!
//! Faithful Rust twin of the Lean `Dregg2.Circuit.Emit.EffectVmEmitTransfer` §11.7 availability weld
//! (`transferVmDescriptorAvail`, `transferAvailGates`, `transferAvailRanges`,
//! `transferAvail_derives_availability`). The deployed bare transfer descriptor
//! (`dregg-effectvm-transfer-v1`) range-checks ONLY the AFTER balance limbs; its debit gate
//! `after.bal_lo ≡ before.bal_lo − amount [ZMOD p]` alone admits an UNDERFLOW WRAP — the audit's
//! witness `before=1, amount=1006632961, after=1006632961` satisfies `after − before + amount = p ≡ 0`
//! and `after < 2^30`, OVER-DEBITING ~10^9 (a value forgery). Range-checking a single 30-bit operand
//! does NOT close it (`p ≈ 2·2^30`, so the wrap window `[p−2^30, p)` overlaps `[0, 2^30)`).
//!
//! ## The fix — mirror `vault_weld`'s proven borrow comparison, at 15-bit limbs
//!
//! On a DEBIT row (`direction = 1`) the actor's balance move is `before = after + amount`. We prove it
//! over ℤ (no field wrap) by decomposing the three 30-bit operands into two 15-bit limbs each
//! (range-checked, so bounded to `[0, 2^30) ⊂ [0, p)`) and running a 2-limb BORROW SUBTRACTION:
//!
//!  * limb 0: `bef0 − am0 + bb0·2^15 − aft0 = 0`     (`bb0` boolean)
//!  * limb 1: `bef1 − am1 − bb0 + bb1·2^15 − aft1 = 0` (`bb1` boolean)
//!  * NO FINAL BORROW: `bb1 = 0`   ⟺   `before ≥ amount` (AVAILABILITY)
//!
//! Every borrow-gate polynomial stays `< 2^16 < p`, so no residual ever reaches `p` — the wrap is
//! STRUCTURALLY impossible. The borrow gates are `direction`-gated (multiplied by `param::DIRECTION`)
//! so they bite ONLY on the debit — the exact surface of the value forgery; an overflowing CREDIT
//! (`direction = 0`) destroys value rather than minting it and is not the forgery. The previously
//! UNRANGED `amount` is now decomposed + range-checked, closing the unranged-amount hole.
//!
//! ## STAGED — descriptor gates + producer aux-fill EXPORTED; the registry row + VK ride the big-bang
//!
//! The witness columns live PAST the base trace width (`≥ EFFECT_VM_WIDTH = 188`), so they are DISTINCT
//! from every base-layout column. What rides the ONE big-bang descriptor regen: the
//! `rotation-v3-staged-registry.tsv` row, the drift-gate FP pin, the widened VK commit + live
//! admission. Until the flip the LIVE registry still routes the bare `transferVmDescriptor2R24`.

use super::columns::{
    EFFECT_VM_WIDTH, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, param, state,
};
use crate::lean_descriptor_air::{LeanExpr, RangeSpec, VmConstraint};

/// Limb width: 15 bits keeps every borrow-gate polynomial `< 2^16 < p` (the `vault_weld` payoff).
pub const LIMB_BITS: usize = 15;
const TWO15: i64 = 1 << LIMB_BITS;

// --- availability-weld witness columns (past the base width, the vault/sysroots pattern) ---
/// Base of the availability-weld witness block.
pub const AVAIL_BASE: usize = EFFECT_VM_WIDTH; // 188
/// `before.bal_lo` low/high 15-bit limbs.
pub const BEF0: usize = AVAIL_BASE;
pub const BEF1: usize = AVAIL_BASE + 1;
/// `after.bal_lo` low/high 15-bit limbs.
pub const AFT0: usize = AVAIL_BASE + 2;
pub const AFT1: usize = AVAIL_BASE + 3;
/// `amount` low/high 15-bit limbs.
pub const AM0: usize = AVAIL_BASE + 4;
pub const AM1: usize = AVAIL_BASE + 5;
/// The two borrow bits (`BRW1` = the final borrow; `0` ⟺ `before ≥ amount`).
pub const BRW0: usize = AVAIL_BASE + 6;
pub const BRW1: usize = AVAIL_BASE + 7;
/// The two CREDIT-side carry bits (`CRY1` = the final carry; `0` ⟺ `before + amount` did NOT overflow
/// the 30-bit after limb — NO field wrap on the credit `new = old + amount`).
pub const CRY0: usize = AVAIL_BASE + 8;
pub const CRY1: usize = AVAIL_BASE + 9;
/// The widened trace width the hardened descriptor declares (borrow chain + credit carry chain).
pub const AVAIL_WIDTH: usize = AVAIL_BASE + 10;

/// Absolute before/after `bal_lo` + `amount`/`direction` columns the assembly + borrow gates read.
const BEFORE_BAL_LO: usize = STATE_BEFORE_BASE + state::BALANCE_LO;
const AFTER_BAL_LO: usize = STATE_AFTER_BASE + state::BALANCE_LO;
const AMOUNT_COL: usize = PARAM_BASE + param::AMOUNT;
const DIRECTION_COL: usize = PARAM_BASE + param::DIRECTION;

// --- gate-body builders (byte-for-byte the Lean §11.7 EmittedExpr trees) ---

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
fn neg(e: LeanExpr) -> LeanExpr {
    mul(k(-1), e)
}
fn sub(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    add(a, neg(b))
}
fn gate(body: LeanExpr) -> VmConstraint {
    VmConstraint::Gate(body)
}
/// `direction · body` — the debit-only selector-gate (mirror of the Lean `.mul (ePrm DIRECTION) …`).
fn dir_gate(body: LeanExpr) -> VmConstraint {
    gate(mul(var(DIRECTION_COL), body))
}
/// `(1 − direction) · body` — the credit-only selector-gate (mirror of the Lean `.mul eCreditSel …`).
fn credit_gate(body: LeanExpr) -> VmConstraint {
    gate(mul(sub(k(1), var(DIRECTION_COL)), body))
}

/// Operand assembly gate: `operand = lo + 2^15·hi` (Lean `gAsmBefore`/`gAsmAfter`/`gAsmAmount`).
fn assembly_gate(operand: usize, lo: usize, hi: usize) -> VmConstraint {
    gate(sub(var(operand), add(var(lo), mul(k(TWO15), var(hi)))))
}
/// Booleanity gate: `b·(b − 1)` (Lean `gBrw0Bool`/`gBrw1Bool`).
fn bool_gate(b: usize) -> VmConstraint {
    gate(mul(var(b), add(var(b), k(-1))))
}

/// **THE AVAILABILITY-WELD GATES** — the exact list (order and all) the Lean `transferAvailGates`
/// builds: the three operand assemblies, the two borrow-bit booleanity gates, the two `direction`-gated
/// borrow-subtraction limbs, and the `direction`-gated NO-FINAL-BORROW gate.
pub fn transfer_avail_gates() -> Vec<VmConstraint> {
    vec![
        assembly_gate(BEFORE_BAL_LO, BEF0, BEF1),
        assembly_gate(AFTER_BAL_LO, AFT0, AFT1),
        assembly_gate(AMOUNT_COL, AM0, AM1),
        bool_gate(BRW0),
        bool_gate(BRW1),
        // limb 0: dir·(bef0 − am0 + bb0·2^15 − aft0)
        dir_gate(sub(
            add(sub(var(BEF0), var(AM0)), mul(k(TWO15), var(BRW0))),
            var(AFT0),
        )),
        // limb 1: dir·(bef1 − am1 − bb0 + bb1·2^15 − aft1)
        dir_gate(sub(
            add(
                sub(sub(var(BEF1), var(AM1)), var(BRW0)),
                mul(k(TWO15), var(BRW1)),
            ),
            var(AFT1),
        )),
        // no final borrow: dir·bb1  (⟹ before ≥ amount)
        dir_gate(var(BRW1)),
        // --- CREDIT carry chain (dir = 0): `before + amount = after`, no overflow wrap ---
        bool_gate(CRY0),
        bool_gate(CRY1),
        // limb 0: (1−dir)·(bef0 + am0 − cry0·2^15 − aft0)
        credit_gate(sub(
            sub(add(var(BEF0), var(AM0)), mul(k(TWO15), var(CRY0))),
            var(AFT0),
        )),
        // limb 1: (1−dir)·(bef1 + am1 + cry0 − cry1·2^15 − aft1)
        credit_gate(sub(
            sub(
                add(add(var(BEF1), var(AM1)), var(CRY0)),
                mul(k(TWO15), var(CRY1)),
            ),
            var(AFT1),
        )),
        // no final carry: (1−dir)·cry1  (⟹ before + amount = after < 2^30, no wrap)
        credit_gate(var(CRY1)),
    ]
}

/// **THE AVAILABILITY-WELD RANGE CHECKS** — the operand + amount 15-bit limbs (Lean
/// `transferAvailRanges`). Bounds every operand to `[0, 2^30) ⊂ [0, p)` AND ranges `amount`, closing the
/// unranged-amount hole. Appended to the bare descriptor's two after-limb ranges.
pub fn transfer_avail_ranges() -> Vec<RangeSpec> {
    [BEF0, BEF1, AFT0, AFT1, AM0, AM1]
        .iter()
        .map(|&wire| RangeSpec {
            wire,
            bits: LIMB_BITS,
        })
        .collect()
}

/// **THE PRODUCER AUX-FILL.** Given the debited/credited cell's `before`/`after` `bal_lo`, the transfer
/// `amount`, and the `direction` bit, write the availability-weld witness columns of one row: the three
/// operand limb decompositions and the two borrow bits of the `before − amount` subtraction. On a DEBIT
/// row (`direction = 1`, honest `before ≥ amount`) the borrow chain closes with `bb1 = 0`; on a CREDIT
/// row the borrow gates are inert (the gate factor `direction = 0`), so the borrow bits are written `0`.
///
/// On a CREDIT row (`direction = 0`) the carry chain of `before + amount` is filled instead (the borrow
/// gates are `direction`-gated off); its NO-FINAL-CARRY bit `CRY1 = 0` witnesses `before + amount =
/// after < 2^30` (no field overflow wrap). On a DEBIT row the carry bits are written `0` (their gates
/// are `(1−direction)`-gated off).
///
/// Returns the ten `(column, value)` writes (limbs + borrow bits + carry bits) for the caller to lay
/// into the trace. Panics if an operand exceeds the 30-bit window, if a debit under-borrows, or if a
/// credit overflows (`before + amount ≥ 2^30`) — each fails closed, matching the descriptor's UNSAT.
pub fn fill_transfer_avail_aux(
    before_bal_lo: u32,
    after_bal_lo: u32,
    amount: u32,
    direction: u32,
) -> [(usize, u32); 10] {
    assert!(
        before_bal_lo < (1u32 << 30),
        "before.bal_lo exceeds the 30-bit operand window"
    );
    assert!(
        after_bal_lo < (1u32 << 30),
        "after.bal_lo exceeds the 30-bit operand window"
    );
    assert!(
        amount < (1u32 << 30),
        "amount exceeds the 30-bit operand window"
    );

    let split = |v: u32| -> (u32, u32) { (v & 0x7fff, v >> 15) };
    let (bef0, bef1) = split(before_bal_lo);
    let (aft0, aft1) = split(after_bal_lo);
    let (am0, am1) = split(amount);

    // The two-limb borrow bits of `before − amount` (only load-bearing on a debit; on a credit the
    // gates are `direction`-gated off, so any consistent value passes — we write the honest 0/0).
    let (brw0, brw1) = if direction == 1 {
        assert!(
            before_bal_lo >= amount,
            "debit availability: amount {amount} exceeds pre-balance {before_bal_lo} — UNSAT (no borrow witness)"
        );
        let b0 = if bef0 < am0 { 1u32 } else { 0 };
        // limb-1 minuend includes the incoming borrow b0
        let b1 = if bef1 < am1 + b0 { 1u32 } else { 0 };
        (b0, b1)
    } else {
        (0, 0)
    };

    // The two-limb carry bits of `before + amount` (only load-bearing on a credit; on a debit the
    // gates are `(1−direction)`-gated off, so we write the honest 0/0).
    let (cry0, cry1) = if direction == 0 {
        assert!(
            (before_bal_lo as u64) + (amount as u64) < (1u64 << 30),
            "credit no-overflow: pre-balance {before_bal_lo} + amount {amount} ≥ 2^30 — UNSAT (would field-wrap)"
        );
        let c0 = if bef0 + am0 >= (1u32 << 15) { 1u32 } else { 0 };
        // limb-1 addend includes the incoming carry c0
        let c1 = if bef1 + am1 + c0 >= (1u32 << 15) {
            1u32
        } else {
            0
        };
        (c0, c1)
    } else {
        (0, 0)
    };

    [
        (BEF0, bef0),
        (BEF1, bef1),
        (AFT0, aft0),
        (AFT1, aft1),
        (AM0, am0),
        (AM1, am1),
        (BRW0, brw0),
        (BRW1, brw1),
        (CRY0, cry0),
        (CRY1, cry1),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn honest_debit_closes_with_no_final_borrow() {
        // before=100, after=70, amount=30, debit — bb1 must be 0 (100 ≥ 30).
        let w = fill_transfer_avail_aux(100, 70, 30, 1);
        assert_eq!(w[6], (BRW0, 0));
        assert_eq!(w[7], (BRW1, 0));
        assert_eq!(w[0], (BEF0, 100));
        assert_eq!(w[2], (AFT0, 70));
        assert_eq!(w[4], (AM0, 30));
    }

    #[test]
    fn honest_debit_with_limb_borrow() {
        // before=2^15 (=32768, limbs (0,1)), amount=1 (limbs (1,0)), after=32767 (limbs (32767,0)).
        // low limb borrows: bef0=0 < am0=1 ⟹ bb0=1; high limb 1 ≥ 0+1 ⟹ bb1=0.
        let w = fill_transfer_avail_aux(32768, 32767, 1, 1);
        assert_eq!(w[6], (BRW0, 1));
        assert_eq!(w[7], (BRW1, 0));
    }

    #[test]
    #[should_panic(expected = "debit availability")]
    fn over_debit_forgery_is_unfillable() {
        // The audit's GAP #4 forgery witness: before=1, amount=1006632961 — no borrow witness exists.
        let _ = fill_transfer_avail_aux(1, 1006632961, 1006632961, 1);
    }

    #[test]
    fn honest_credit_closes_with_no_final_carry() {
        // before=100, after=130, amount=30, credit (dir=0) — cry1 must be 0 (100 + 30 = 130 < 2^30).
        let w = fill_transfer_avail_aux(100, 130, 30, 0);
        assert_eq!(w[8], (CRY0, 0));
        assert_eq!(w[9], (CRY1, 0));
    }

    #[test]
    fn honest_credit_with_limb_carry() {
        // before=32767 (limbs (32767,0)), amount=1 (limbs (1,0)), after=32768 (limbs (0,1)).
        // low limb carries: 32767+1 = 32768 ≥ 2^15 ⟹ cry0=1; high limb 0+0+1 < 2^15 ⟹ cry1=0.
        let w = fill_transfer_avail_aux(32767, 32768, 1, 0);
        assert_eq!(w[8], (CRY0, 1));
        assert_eq!(w[9], (CRY1, 0));
    }

    #[test]
    #[should_panic(expected = "credit no-overflow")]
    fn over_credit_forgery_is_unfillable() {
        // The GAP #4 CREDIT forgery witness: before=amount=1006632961 (both < 2^30), sum = 2013265922
        // ≥ p wraps to 1 mod p — no carry witness exists (before+amount ≥ 2^30).
        let _ = fill_transfer_avail_aux(1006632961, 1, 1006632961, 0);
    }

    #[test]
    fn gate_and_range_counts_match_lean() {
        assert_eq!(transfer_avail_gates().len(), 13);
        assert_eq!(transfer_avail_ranges().len(), 6);
        assert_eq!(AVAIL_WIDTH, 198);
    }
}
