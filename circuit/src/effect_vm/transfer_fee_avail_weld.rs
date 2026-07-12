//! # `transfer_fee_avail_weld` — the IN-AIR FEE'D-TRANSFER availability gates (the fee member of
//! the GAP #4 full-closure, STAGED).
//!
//! Faithful Rust twin of the Lean `Dregg2.Circuit.Emit.EffectVmEmitTransfer` §11.8 fee availability
//! weld (`transferFeeVmDescriptorAvail`, `transferFeeAvailGates`, `transferFeeAvailRanges`,
//! `transferFeeAvail_derives_availability_row`). The deployed fee'd transfer descriptor
//! (`dregg-effectvm-transfer-v1-fee`) debits BOTH the transfer amount AND the fee from `BALANCE_LO`
//! (`after ≡ before − amount·(1−2·dir) − fee [ZMOD p]`) and range-checks only the AFTER limbs + the
//! fee at 30 bits — the SAME underflow-wrap class as the bare transfer, open through EITHER debit
//! leg: the amount leg (`before=1, amount=1006632961, fee=0`) or the FEE leg (`before=1, amount=0,
//! fee=1006632961`: `after − before + fee = p ≡ 0` with `after < 2^30` passing the range).
//!
//! ## The fix — the `transfer_avail_weld` chains with one extra link
//!
//! ⚠ The transfer chain cannot be reused blind: its debit gates force `before = after + amount`
//! over ℤ, which against the fee'd gate would force `fee = 0` (a liveness break — every fee'd
//! transfer UNSAT). The fee weld chains through an intermediate MID witness (`mid` = the balance
//! after the transfer move, before the fee), all at 15-bit limbs:
//!
//!  * DEBIT (`dir = 1`):  borrow chain `before − amount = mid`, no final borrow ⟹ `amount ≤ before`;
//!  * CREDIT (`dir = 0`): carry chain `before + amount = mid`, no final carry ⟹ no overflow wrap;
//!  * BOTH directions:    UNGATED borrow chain `mid − fee = after`, no final borrow ⟹ `fee ≤ mid`
//!    (the fee'd gate is `after = mid − fee` in both directions, so this link needs no selector).
//!
//! On a debit row this forces `amount + fee ≤ before` (availability INCLUDING the fee) and the
//! exact ℤ move `after = before − amount − fee` — no residual ever reaches `p`, so both wrap
//! forgeries are STRUCTURALLY impossible (Lean `transferFeeAvail_forgery_unsat` /
//! `transferFeeAvail_fee_forgery_unsat`).
//!
//! ## STAGED — descriptor gates + producer aux-fill EXPORTED; the registry row + VK ride the big-bang
//!
//! The witness columns live PAST the base trace width (the §11.7 pattern: the transfer weld's 10
//! columns at the SAME indices — a different descriptor, no collision — plus 6 fee columns). Until
//! the flip the LIVE registry still routes the bare `transferFeeVmDescriptor2R24`.

use super::columns::{
    EFFECT_VM_WIDTH, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, param, state,
};
use super::transfer_avail_weld::{AFT0, AFT1, AM0, AM1, BEF0, BEF1, BRW0, BRW1, CRY0, CRY1};
use crate::lean_descriptor_air::{LeanExpr, RangeSpec, VmConstraint};

/// Limb width: 15 bits keeps every chain polynomial `< 2^16 < p` (the `vault_weld` payoff).
pub const LIMB_BITS: usize = 15;
const TWO15: i64 = 1 << LIMB_BITS;

// --- fee-weld witness columns (the §11.7 block + 6 more, Lean §11.8) ---
/// `mid` (`before − amount` on a debit / `before + amount` on a credit) low/high 15-bit limbs.
pub const MID0: usize = super::transfer_avail_weld::AVAIL_WIDTH; // 198
pub const MID1: usize = MID0 + 1;
/// `fee` (the `feeCol = after.RESERVED` carrier) low/high 15-bit limbs.
pub const FEE0: usize = MID0 + 2;
pub const FEE1: usize = MID0 + 3;
/// The fee-subtraction borrow bits (`FB1` = the final borrow; forced `0` ⟺ `fee ≤ mid`).
pub const FB0: usize = MID0 + 4;
pub const FB1: usize = MID0 + 5;
/// The widened trace width the hardened fee descriptor declares (Lean `FEE_AVAIL_WIDTH = 204`).
pub const FEE_AVAIL_WIDTH: usize = MID0 + 6;

/// Absolute v1 columns the assembly + chain gates read.
const BEFORE_BAL_LO: usize = STATE_BEFORE_BASE + state::BALANCE_LO;
const AFTER_BAL_LO: usize = STATE_AFTER_BASE + state::BALANCE_LO;
const AMOUNT_COL: usize = PARAM_BASE + param::AMOUNT;
const DIRECTION_COL: usize = PARAM_BASE + param::DIRECTION;
/// The fee carrier (`feeCol = saCol state.RESERVED`, col 89 — the fee'd descriptor's debit leg).
pub const FEE_COL: usize = STATE_AFTER_BASE + state::RESERVED;

// --- gate-body builders (byte-for-byte the Lean §11.8 EmittedExpr trees) ---

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
/// `direction · body` — the debit-only selector-gate (the Lean `.mul (ePrm DIRECTION) …`).
fn dir_gate(body: LeanExpr) -> VmConstraint {
    gate(mul(var(DIRECTION_COL), body))
}
/// `(1 − direction) · body` — the credit-only selector-gate (the Lean `.mul eCreditSel …`).
fn credit_gate(body: LeanExpr) -> VmConstraint {
    gate(mul(sub(k(1), var(DIRECTION_COL)), body))
}
/// Operand assembly gate: `operand = lo + 2^15·hi` (Lean `gAsmBefore`/…/`gAsmFee`).
fn assembly_gate(operand: usize, lo: usize, hi: usize) -> VmConstraint {
    gate(sub(var(operand), add(var(lo), mul(k(TWO15), var(hi)))))
}
/// Booleanity gate: `b·(b − 1)`.
fn bool_gate(b: usize) -> VmConstraint {
    gate(mul(var(b), add(var(b), k(-1))))
}

/// **THE FEE'D AVAILABILITY-WELD GATES** — the exact list (order and all) the Lean
/// `transferFeeAvailGates` builds: 4 operand assemblies, the `dir`-gated debit borrow chain to MID,
/// the `(1−dir)`-gated credit carry chain to MID, and the UNGATED fee-subtraction borrow chain
/// MID → AFTER with its no-final-borrow gate.
pub fn transfer_fee_avail_gates() -> Vec<VmConstraint> {
    vec![
        assembly_gate(BEFORE_BAL_LO, BEF0, BEF1),
        assembly_gate(AFTER_BAL_LO, AFT0, AFT1),
        assembly_gate(AMOUNT_COL, AM0, AM1),
        assembly_gate(FEE_COL, FEE0, FEE1),
        bool_gate(BRW0),
        bool_gate(BRW1),
        // debit limb 0: dir·(bef0 − am0 + bb0·2^15 − mid0)  (Lean `gFeeBorrow0`)
        dir_gate(sub(
            add(sub(var(BEF0), var(AM0)), mul(k(TWO15), var(BRW0))),
            var(MID0),
        )),
        // debit limb 1: dir·(bef1 − am1 − bb0 + bb1·2^15 − mid1)  (Lean `gFeeBorrow1`)
        dir_gate(sub(
            add(
                sub(sub(var(BEF1), var(AM1)), var(BRW0)),
                mul(k(TWO15), var(BRW1)),
            ),
            var(MID1),
        )),
        // no final borrow: dir·bb1  (⟹ amount ≤ before)
        dir_gate(var(BRW1)),
        bool_gate(CRY0),
        bool_gate(CRY1),
        // credit limb 0: (1−dir)·((bef0 + am0) − (mid0 + cry0·2^15))  (Lean `gFeeCarry0`)
        credit_gate(sub(
            add(var(BEF0), var(AM0)),
            add(var(MID0), mul(k(TWO15), var(CRY0))),
        )),
        // credit limb 1: (1−dir)·((bef1 + am1 + cry0) − (mid1 + cry1·2^15))  (Lean `gFeeCarry1`)
        credit_gate(sub(
            add(add(var(BEF1), var(AM1)), var(CRY0)),
            add(var(MID1), mul(k(TWO15), var(CRY1))),
        )),
        // no final carry: (1−dir)·cry1  (⟹ before + amount = mid < 2^30, no wrap)
        credit_gate(var(CRY1)),
        bool_gate(FB0),
        bool_gate(FB1),
        // fee limb 0 (UNGATED — `after = mid − fee` in BOTH directions): mid0 − fee0 + fb0·2^15 − aft0
        gate(sub(
            add(sub(var(MID0), var(FEE0)), mul(k(TWO15), var(FB0))),
            var(AFT0),
        )),
        // fee limb 1 (UNGATED): mid1 − fee1 − fb0 + fb1·2^15 − aft1
        gate(sub(
            add(
                sub(sub(var(MID1), var(FEE1)), var(FB0)),
                mul(k(TWO15), var(FB1)),
            ),
            var(AFT1),
        )),
        // no final fee borrow (UNGATED): fb1  (⟹ fee ≤ mid)
        gate(var(FB1)),
    ]
}

/// **THE FEE'D AVAILABILITY-WELD RANGE CHECKS** — every operand limb at 15 bits (Lean
/// `transferFeeAvailRanges`): before/after/amount as the transfer weld, PLUS the mid and fee limbs
/// (the fee is thereby decomposed + bounded, closing the fee-leg wrap window).
pub fn transfer_fee_avail_ranges() -> Vec<RangeSpec> {
    [BEF0, BEF1, AFT0, AFT1, AM0, AM1, MID0, MID1, FEE0, FEE1]
        .iter()
        .map(|&wire| RangeSpec {
            wire,
            bits: LIMB_BITS,
        })
        .collect()
}

/// **THE PRODUCER AUX-FILL.** Given the cell's `before`/`after` `bal_lo`, the transfer `amount`,
/// the debited `fee`, and the `direction` bit, write the fee-weld witness columns of one row: the
/// four operand limb decompositions, the MID intermediate (`before − amount` on a debit /
/// `before + amount` on a credit), the transfer-leg borrow/carry bits, and the fee-leg borrow bits
/// of `mid − fee`. Errors (fails closed, matching the descriptor's UNSAT) if an operand exceeds
/// the 30-bit window, a debit under-borrows (`amount > before`), a credit overflows
/// (`before + amount ≥ 2^30`), or the fee exceeds the post-move balance (`fee > mid` — the fee-leg
/// forgery, in EITHER direction).
///
/// Returns the sixteen `(column, value)` writes for the caller to lay into the trace.
pub fn try_fill_transfer_fee_avail_aux(
    before_bal_lo: u32,
    after_bal_lo: u32,
    amount: u32,
    fee: u32,
    direction: u32,
) -> Result<[(usize, u32); 16], String> {
    for (what, v) in [
        ("before.bal_lo", before_bal_lo),
        ("after.bal_lo", after_bal_lo),
        ("amount", amount),
        ("fee", fee),
    ] {
        if v >= (1u32 << 30) {
            return Err(format!("{what} {v} exceeds the 30-bit operand window"));
        }
    }

    let split = |v: u32| -> (u32, u32) { (v & 0x7fff, v >> 15) };
    let (bef0, bef1) = split(before_bal_lo);
    let (aft0, aft1) = split(after_bal_lo);
    let (am0, am1) = split(amount);
    let (fee0, fee1) = split(fee);

    // The MID intermediate + the transfer-leg chain bits (borrow on a debit, carry on a credit; the
    // other direction's gates are selector-gated off, so its bits are written honest 0/0).
    let (mid, brw0, brw1, cry0, cry1) = if direction == 1 {
        if before_bal_lo < amount {
            return Err(format!(
                "debit availability: amount {amount} exceeds pre-balance {before_bal_lo} — UNSAT \
                 (no borrow witness)"
            ));
        }
        let b0 = u32::from(bef0 < am0);
        let b1 = u32::from(bef1 < am1 + b0);
        (before_bal_lo - amount, b0, b1, 0, 0)
    } else {
        if (before_bal_lo as u64) + (amount as u64) >= (1u64 << 30) {
            return Err(format!(
                "credit no-overflow: pre-balance {before_bal_lo} + amount {amount} ≥ 2^30 — UNSAT \
                 (would field-wrap)"
            ));
        }
        let c0 = u32::from(bef0 + am0 >= (1u32 << 15));
        let c1 = u32::from(bef1 + am1 + c0 >= (1u32 << 15));
        (before_bal_lo + amount, 0, 0, c0, c1)
    };
    let (mid0, mid1) = split(mid);

    // The fee-leg borrow bits of `mid − fee` (UNGATED — load-bearing in BOTH directions).
    if mid < fee {
        return Err(format!(
            "fee availability: fee {fee} exceeds the post-move balance {mid} — UNSAT (no fee \
             borrow witness)"
        ));
    }
    let fb0 = u32::from(mid0 < fee0);
    let fb1 = u32::from(mid1 < fee1 + fb0);

    Ok([
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
        (MID0, mid0),
        (MID1, mid1),
        (FEE0, fee0),
        (FEE1, fee1),
        (FB0, fb0),
        (FB1, fb1),
    ])
}

/// The panicking convenience wrapper of [`try_fill_transfer_fee_avail_aux`] (test/tooling
/// ergonomics).
pub fn fill_transfer_fee_avail_aux(
    before_bal_lo: u32,
    after_bal_lo: u32,
    amount: u32,
    fee: u32,
    direction: u32,
) -> [(usize, u32); 16] {
    try_fill_transfer_fee_avail_aux(before_bal_lo, after_bal_lo, amount, fee, direction)
        .unwrap_or_else(|e| panic!("transfer fee avail aux fill: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn honest_fee_debit_closes_with_no_borrows() {
        // before=100, after=65, amount=30, fee=5, debit — mid=70, all chain bits 0.
        let w = fill_transfer_fee_avail_aux(100, 65, 30, 5, 1);
        assert_eq!(w[6], (BRW0, 0));
        assert_eq!(w[7], (BRW1, 0));
        assert_eq!(w[10], (MID0, 70));
        assert_eq!(w[11], (MID1, 0));
        assert_eq!(w[12], (FEE0, 5));
        assert_eq!(w[14], (FB0, 0));
        assert_eq!(w[15], (FB1, 0));
    }

    #[test]
    fn honest_fee_debit_with_fee_limb_borrow() {
        // before=32768 (limbs (0,1)), amount=0, fee=1, after=32767: mid=32768 (limbs (0,1)),
        // fee limb 0 borrows (mid0=0 < fee0=1 ⟹ fb0=1), high limb 1 ≥ 0+1 ⟹ fb1=0.
        let w = fill_transfer_fee_avail_aux(32768, 32767, 0, 1, 1);
        assert_eq!(w[14], (FB0, 1));
        assert_eq!(w[15], (FB1, 0));
    }

    #[test]
    #[should_panic(expected = "debit availability")]
    fn amount_leg_forgery_is_unfillable() {
        // The GAP #4 amount-leg witness against the fee'd member: before=1, amount=1006632961.
        let _ = fill_transfer_fee_avail_aux(1, 1006632961, 1006632961, 0, 1);
    }

    #[test]
    #[should_panic(expected = "fee availability")]
    fn fee_leg_forgery_is_unfillable() {
        // THE FEE-LEG WRAP WITNESS (the §11.8 tooth): before=1, amount=0, fee=1006632961 —
        // `after − before + fee = p ≡ 0` with after < 2^30 passes the BARE fee member; the
        // hardened member has no fee-borrow witness (fee > mid = 1).
        let _ = fill_transfer_fee_avail_aux(1, 1006632961, 0, 1006632961, 1);
    }

    #[test]
    fn honest_fee_credit_closes_clean() {
        // before=100, after=125, amount=30, fee=5, credit — mid=130, no carries, no fee borrows.
        let w = fill_transfer_fee_avail_aux(100, 125, 30, 5, 0);
        assert_eq!(w[8], (CRY0, 0));
        assert_eq!(w[9], (CRY1, 0));
        assert_eq!(w[10], (MID0, 130));
        assert_eq!(w[14], (FB0, 0));
        assert_eq!(w[15], (FB1, 0));
    }

    #[test]
    #[should_panic(expected = "credit no-overflow")]
    fn credit_overflow_forgery_is_unfillable() {
        // The credit twin: before=amount=1006632961 (both < 2^30), sum ≥ p wraps — no carry witness.
        let _ = fill_transfer_fee_avail_aux(1006632961, 1, 1006632961, 0, 0);
    }

    #[test]
    #[should_panic(expected = "fee availability")]
    fn credit_fee_underflow_is_unfillable() {
        // A credit whose fee exceeds the post-credit balance (fee > before + amount) has no
        // fee-borrow witness either — the fee-leg tooth bites in BOTH directions.
        let _ = fill_transfer_fee_avail_aux(10, 1, 20, 100, 0);
    }

    #[test]
    fn gate_and_range_counts_match_lean() {
        assert_eq!(transfer_fee_avail_gates().len(), 19);
        assert_eq!(transfer_fee_avail_ranges().len(), 10);
        assert_eq!(FEE_AVAIL_WIDTH, 204);
        assert_eq!(FEE_AVAIL_WIDTH - EFFECT_VM_WIDTH, 16);
    }
}
