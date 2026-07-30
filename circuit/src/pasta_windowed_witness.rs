//! # `pasta_windowed_witness` — WITNESS GENERATION for the Lean-authored windowed Pallas RCB AIR.
//!
//! ## Substrate, said out loud
//!
//! **The AIR is LEAN-AUTHORED.** Every constraint of `dregg-pasta-rcb-windowed::v1` is a `def`
//! in `metatheory/Dregg2/Circuit/Emit/PastaMsmWindowed.lean` (`rowGates ++ threadGates`, 45
//! entries), emitted to `circuit/descriptors/by-name/pasta-rcb-windowed.json` and parsed by the
//! deployed `descriptor_ir2` checker. **This module authors NO constraint, no gate, no builder
//! gadget and no `air_accepts` predicate.** It only fills trace CELLS: it computes the numbers
//! that make the Lean-emitted gate bodies vanish, and hands them to the deployed prover. If the
//! prover refuses a trace this module produced, the WITNESS is wrong — never the AIR.
//!
//! ## What a row is
//!
//! One row is ONE Renes–Costello–Batina complete addition on Pallas in projective coordinates
//! (`PastaCurveComplete.swCompleteAddGadget`, Algorithm 7 at `a = 0`, `b3 = 15`), threaded to
//! the next row by three `windowGate`s. The 33 SSA intermediates, 14 division quotients and 19
//! carry/borrow bits are exactly the gadget's witness slots, in the gadget's emission order.
//!
//! ## The arithmetic this module must do, and why it is EXACT over ℤ
//!
//! A Pasta field element is stored as 9 columns of 30 bits (`PastaField.numLimbs`/`limbBits`),
//! LSB-first: `value = Σ_{i<9} 2^(30·i)·col(base+i)`. The gate bodies are, over ℤ:
//!
//! * `fpMulHead x y z q`  = `xVal·yVal − p·qVal − zVal`
//! * `fpSMulHead m x z q` = `m·xVal − p·qVal − zVal`
//! * `fpAddHead x y z c`  = `xVal + yVal − zVal − c·p`
//! * `fpSubHead x y z c`  = `xVal − yVal − zVal + c·p`
//!
//! so the witness must carry the *exact integer* quotient / carry, not merely a congruence. This
//! module produces a witness that makes every body vanish **over the integers**; the deployed
//! prover then reads the same bodies in BabyBear, where they vanish a fortiori. (The converse —
//! that BabyBear-vanishing implies ℤ-vanishing — does NOT hold; that is the inherited K1 residual
//! named in `PastaMsmWindowed` §6.2, and producing a proof object does not close it.)
//!
//! ## Column layout (`PastaMsmWindowed` §1, `swCompleteAddGadget` at `fresh = 0`)
//!
//! ```text
//!   9·idx            0..296   33 SSA intermediates (idx 26 = X3, 29 = Y3, 32 = Z3)
//!   297 + 9·qidx   297..422   14 quotient groups
//!   423 + bidx     423..441   19 carry/borrow bits
//!   442, 451, 460             ACCX, ACCY, ACCZ — the accumulator INTO this row
//!   469, 478, 487             OPX, OPY, OPZ    — the selector's OUTPUT (the addend)
//!   496, 505, 514             SRCX, SRCY, SRCZ — the row's source point
//!   523                       BIT              — the conditional-add bit
//!   524                       DBL              — 1 iff this row doubles
//! ```

use crate::field::BabyBear;
use core::cmp::Ordering;

// ---------------------------------------------------------------------------------------------
// PART 0 — a 256-bit unsigned integer, enough for Pallas base-field arithmetic.
//
// Deliberately hand-rolled rather than pulling `num-bigint` into `dregg-circuit`: this crate is
// the VERIFY-LEVEL FLOOR (see `circuit/Cargo.toml`) and its dependency graph is kept deliberately
// small. What is needed is schoolbook multiply and one division by a fixed 255-bit modulus.
// ---------------------------------------------------------------------------------------------

/// A 256-bit unsigned integer, four `u64` limbs, least-significant first.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct U256(pub [u64; 4]);

impl PartialOrd for U256 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for U256 {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..4).rev() {
            match self.0[i].cmp(&other.0[i]) {
                Ordering::Equal => {}
                non_eq => return non_eq,
            }
        }
        Ordering::Equal
    }
}

impl U256 {
    /// Zero.
    pub const ZERO: U256 = U256([0; 4]);
    /// One.
    pub const ONE: U256 = U256([1, 0, 0, 0]);

    /// A small integer.
    pub fn from_u64(v: u64) -> U256 {
        U256([v, 0, 0, 0])
    }

    /// Parse a decimal literal. Panics on a non-digit or on overflow past 256 bits — this is a
    /// test/witness-construction helper for compile-time-known curve constants.
    pub fn from_dec(s: &str) -> U256 {
        let mut acc = U256::ZERO;
        for b in s.bytes() {
            assert!(b.is_ascii_digit(), "non-digit {b:?} in decimal literal");
            let (mul, ovf) = acc.mul_small(10);
            assert!(!ovf, "decimal literal overflows 256 bits");
            let (sum, carry) = mul.adc(&U256::from_u64(u64::from(b - b'0')));
            assert!(!carry, "decimal literal overflows 256 bits");
            acc = sum;
        }
        acc
    }

    /// `self + other`, with the carry OUT of bit 255.
    pub fn adc(&self, other: &U256) -> (U256, bool) {
        let mut out = [0u64; 4];
        let mut carry = 0u128;
        for i in 0..4 {
            let t = u128::from(self.0[i]) + u128::from(other.0[i]) + carry;
            out[i] = t as u64;
            carry = t >> 64;
        }
        (U256(out), carry != 0)
    }

    /// `self − other`, with the borrow OUT of bit 255 (i.e. `self < other`).
    pub fn sbb(&self, other: &U256) -> (U256, bool) {
        let mut out = [0u64; 4];
        let mut borrow = 0i128;
        for i in 0..4 {
            let t = i128::from(self.0[i]) - i128::from(other.0[i]) - borrow;
            out[i] = (t as u128) as u64;
            borrow = i128::from(t < 0);
        }
        (U256(out), borrow != 0)
    }

    /// `self * small`, with an overflow flag.
    fn mul_small(&self, small: u64) -> (U256, bool) {
        let mut out = [0u64; 4];
        let mut carry = 0u128;
        for i in 0..4 {
            let t = u128::from(self.0[i]) * u128::from(small) + carry;
            out[i] = t as u64;
            carry = t >> 64;
        }
        (U256(out), carry != 0)
    }

    /// `self >> 1`.
    fn shr1(&self) -> U256 {
        let mut out = [0u64; 4];
        for i in 0..4 {
            let hi = if i + 1 < 4 { self.0[i + 1] << 63 } else { 0 };
            out[i] = (self.0[i] >> 1) | hi;
        }
        U256(out)
    }

    /// Least-significant bit clear.
    fn is_even(&self) -> bool {
        self.0[0] & 1 == 0
    }

    /// `self << 1 | bit`. The caller guarantees `self < 2^255` so nothing is lost.
    fn shl1_or(&self, bit: u64) -> U256 {
        debug_assert!(self.0[3] >> 63 == 0, "shl1 would drop the top bit");
        let mut out = [0u64; 4];
        let mut carry = bit;
        for i in 0..4 {
            out[i] = (self.0[i] << 1) | carry;
            carry = self.0[i] >> 63;
        }
        U256(out)
    }

    /// The `i`-th 30-bit limb of the 9×30 encoding (`PastaField.limbOf`).
    pub fn limb30(&self, i: usize) -> u32 {
        debug_assert!(i < NUM_LIMBS);
        let bit = LIMB_BITS * i;
        let word = bit / 64;
        let off = bit % 64;
        let lo = self.0[word] >> off;
        // A 30-bit window straddles a u64 boundary only when `off > 34`.
        let hi = if off > 64 - LIMB_BITS && word + 1 < 4 {
            self.0[word + 1] << (64 - off)
        } else {
            0
        };
        ((lo | hi) & ((1u64 << LIMB_BITS) - 1)) as u32
    }

    /// Reassemble a value from its 9×30 limbs (the inverse of [`Self::limb30`] on canonical
    /// encodings). Used by the tests to read a trace row back.
    pub fn from_limbs30(limbs: &[u32; NUM_LIMBS]) -> U256 {
        let mut acc = U256::ZERO;
        for i in (0..NUM_LIMBS).rev() {
            // acc = acc * 2^30 + limb
            for _ in 0..LIMB_BITS {
                acc = acc.shl1_or(0);
            }
            let (sum, carry) = acc.adc(&U256::from_u64(u64::from(limbs[i])));
            debug_assert!(!carry);
            acc = sum;
        }
        acc
    }

    /// Bit `i` of the value, `0` past bit 255.
    pub fn bit(&self, i: usize) -> u32 {
        if i >= 256 {
            return 0;
        }
        ((self.0[i / 64] >> (i % 64)) & 1) as u32
    }

    /// Decimal rendering (test diagnostics).
    pub fn to_dec(&self) -> String {
        if *self == U256::ZERO {
            return "0".to_string();
        }
        let mut digits = Vec::new();
        let mut cur = *self;
        while cur != U256::ZERO {
            let mut rem = 0u128;
            let mut out = [0u64; 4];
            for i in (0..4).rev() {
                let t = (rem << 64) | u128::from(cur.0[i]);
                out[i] = (t / 10) as u64;
                rem = t % 10;
            }
            digits.push(b'0' + rem as u8);
            cur = U256(out);
        }
        digits.reverse();
        String::from_utf8(digits).expect("ascii digits")
    }
}

/// Limbs per Pasta field element (`PastaField.numLimbs`).
pub const NUM_LIMBS: usize = 9;
/// Bits per limb (`PastaField.limbBits`).
pub const LIMB_BITS: usize = 30;

/// The **Pallas base field** prime `p` (`PastaField.pN`), 255 bits.
pub const P_PASTA: U256 = U256([
    0x992d_30ed_0000_0001,
    0x2246_98fc_094c_f91b,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
]);

/// The **Pallas scalar field** prime `q` (`PastaField.qN`), 255 bits. This is the field the IPA
/// challenges and the s-vector live in — `PastaField.fqMulCore`'s modulus, and therefore the
/// modulus of the derivation chain `PastaMsmScalarDerive.chainGates` emits.
pub const Q_PASTA: U256 = U256([
    0x8c46_eb21_0000_0001,
    0x2246_98fc_0994_a8dd,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
]);

/// The RCB constant `b3 = 3·b = 15` (`PastaCurveComplete.curveB3`).
pub const CURVE_B3: u64 = 15;
/// The short-Weierstrass `b` coefficient (`PastaCurve.curveB`).
pub const CURVE_B: u64 = 5;

/// Schoolbook 256×256 → 512.
fn mul_wide(a: &U256, b: &U256) -> [u64; 8] {
    let mut out = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let t = u128::from(a.0[i]) * u128::from(b.0[j]) + u128::from(out[i + j]) + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + 4] = carry as u64;
    }
    out
}

/// `(x div m, x mod m)` by binary long division, for any 255-bit modulus `m`. `x < m²` is required
/// for the quotient to fit 256 bits (debug-asserted).
fn divrem_by(x: &[u64; 8], m: &U256) -> (U256, U256) {
    debug_assert!(m.0[3] >> 63 == 0, "modulus must be < 2^255");
    let mut msb = None;
    for i in (0..8).rev() {
        if x[i] != 0 {
            msb = Some(i * 64 + (63 - x[i].leading_zeros() as usize));
            break;
        }
    }
    let Some(msb) = msb else {
        return (U256::ZERO, U256::ZERO);
    };
    let mut quot = [0u64; 8];
    let mut rem = U256::ZERO;
    for i in (0..=msb).rev() {
        // `rem < m < 2^255`, so `2·rem + bit < 2m < 2^256` and one conditional subtraction
        // restores the invariant.
        let bit = (x[i / 64] >> (i % 64)) & 1;
        rem = rem.shl1_or(bit);
        if rem >= *m {
            let (r, borrow) = rem.sbb(m);
            debug_assert!(!borrow);
            rem = r;
            quot[i / 64] |= 1u64 << (i % 64);
        }
    }
    debug_assert!(
        quot[4] == 0 && quot[5] == 0 && quot[6] == 0 && quot[7] == 0,
        "quotient exceeds 256 bits (input was not < m²)"
    );
    (U256([quot[0], quot[1], quot[2], quot[3]]), rem)
}

/// `(x div p, x mod p)` — [`divrem_by`] at the Pallas BASE modulus.
fn divrem_p(x: &[u64; 8]) -> (U256, U256) {
    divrem_by(x, &P_PASTA)
}

/// `(x·y mod p, x·y div p)` — the reduced product and the `fpMulHead` quotient witness.
pub fn mul_mod_p(x: &U256, y: &U256) -> (U256, U256) {
    debug_assert!(*x < P_PASTA && *y < P_PASTA);
    let (q, r) = divrem_p(&mul_wide(x, y));
    (r, q)
}

/// `(x·y mod q, x·y div q)` — the reduced product and the `fqMulHead` quotient witness, at the
/// Pallas SCALAR modulus. This is the ONLY arithmetic the derivation chain needs: every step of
/// `PastaMsmScalarDerive.chainGates` is one `fqMulCore`.
pub fn mul_mod_q(x: &U256, y: &U256) -> (U256, U256) {
    debug_assert!(*x < Q_PASTA && *y < Q_PASTA);
    let (quot, rem) = divrem_by(&mul_wide(x, y), &Q_PASTA);
    (rem, quot)
}

/// `(k·x mod p, k·x div p)` — the reduced constant-multiple and the `fpSMulHead` quotient.
pub fn smul_mod_p(k: u64, x: &U256) -> (U256, U256) {
    debug_assert!(*x < P_PASTA);
    let (q, r) = divrem_p(&mul_wide(&U256::from_u64(k), x));
    (r, q)
}

/// `((x+y) mod p, carry)` — `carry = 1` exactly when `x + y ≥ p`, the `fpAddHead` witness.
pub fn add_mod_p(x: &U256, y: &U256) -> (U256, u8) {
    debug_assert!(*x < P_PASTA && *y < P_PASTA);
    let (sum, overflow) = x.adc(y);
    debug_assert!(!overflow, "x + y < 2p < 2^256");
    if sum >= P_PASTA {
        let (r, borrow) = sum.sbb(&P_PASTA);
        debug_assert!(!borrow);
        (r, 1)
    } else {
        (sum, 0)
    }
}

/// `((x−y) mod p, borrow)` — `borrow = 1` exactly when `x < y`, the `fpSubHead` witness.
pub fn sub_mod_p(x: &U256, y: &U256) -> (U256, u8) {
    debug_assert!(*x < P_PASTA && *y < P_PASTA);
    let (diff, borrow) = x.sbb(y);
    if borrow {
        let (r, overflow) = diff.adc(&P_PASTA);
        debug_assert!(overflow, "wrapped difference plus p re-crosses 2^256");
        (r, 1)
    } else {
        (diff, 0)
    }
}

/// `x⁻¹ mod p` for `0 < x < p`, by the binary extended Euclid (Kaliski) algorithm — `O(512)`
/// shift/add steps, against `O(2^255)` for a Fermat exponentiation through [`mul_mod_p`].
///
/// Every intermediate stays `< p`, and `x1 + p < 2p < 2^256`, so nothing overflows `U256`. Panics
/// on `x = 0`: the AIR's non-degeneracy gate is *exactly* the statement that no honest coordinate
/// is zero there, so a zero here means the SCHEDULE is wrong, not that a fallback is wanted.
pub fn inv_mod_p(x: &U256) -> U256 {
    assert!(*x != U256::ZERO, "0 has no inverse mod p (nonZeroHead)");
    debug_assert!(*x < P_PASTA);
    let half = |v: U256| -> U256 {
        if v.is_even() {
            v.shr1()
        } else {
            let (s, ovf) = v.adc(&P_PASTA);
            debug_assert!(!ovf, "v + p < 2p < 2^256");
            s.shr1()
        }
    };
    let (mut u, mut v) = (*x, P_PASTA);
    let (mut x1, mut x2) = (U256::ONE, U256::ZERO);
    while u != U256::ONE && v != U256::ONE {
        while u.is_even() {
            u = u.shr1();
            x1 = half(x1);
        }
        while v.is_even() {
            v = v.shr1();
            x2 = half(x2);
        }
        if u >= v {
            u = u.sbb(&v).0;
            x1 = sub_mod_p(&x1, &x2).0;
        } else {
            v = v.sbb(&u).0;
            x2 = sub_mod_p(&x2, &x1).0;
        }
    }
    if u == U256::ONE { x1 } else { x2 }
}

// ---------------------------------------------------------------------------------------------
// PART 1 — projective Pallas points and the RCB Algorithm 7 reference.
// ---------------------------------------------------------------------------------------------

/// A projective Pallas point `(X : Y : Z)` over `p`, coordinates kept canonically reduced.
/// The identity is `O = (0 : 1 : 0)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Pt {
    /// `X`.
    pub x: U256,
    /// `Y`.
    pub y: U256,
    /// `Z`.
    pub z: U256,
}

impl Pt {
    /// The projective identity `(0 : 1 : 0)` (`PastaCurveComplete.Oproj`).
    pub const INFINITY: Pt = Pt {
        x: U256::ZERO,
        y: U256::ONE,
        z: U256::ZERO,
    };

    /// An affine point `(x, y)` as `(x : y : 1)`.
    pub fn affine(x: U256, y: U256) -> Pt {
        assert!(x < P_PASTA && y < P_PASTA, "affine coords must be reduced");
        Pt { x, y, z: U256::ONE }
    }

    /// `Y²·Z ≡ X³ + b·Z³ (mod p)` — the projective curve equation (`projOnCurveM`). Not gated by
    /// the AIR (see `PastaMsmWindowed` §6.3); used by the tests to show the witness is on-curve.
    pub fn on_curve(&self) -> bool {
        let (yy, _) = mul_mod_p(&self.y, &self.y);
        let (lhs, _) = mul_mod_p(&yy, &self.z);
        let (xx, _) = mul_mod_p(&self.x, &self.x);
        let (x3, _) = mul_mod_p(&xx, &self.x);
        let (zz, _) = mul_mod_p(&self.z, &self.z);
        let (z3, _) = mul_mod_p(&zz, &self.z);
        let (bz3, _) = smul_mod_p(CURVE_B, &z3);
        let (rhs, _) = add_mod_p(&x3, &bz3);
        lhs == rhs
    }

    /// `Z ≡ 0 ∧ X ≡ 0` — the terminal "is the identity" predicate (`isInfM`).
    pub fn is_infinity(&self) -> bool {
        self.z == U256::ZERO && self.x == U256::ZERO
    }
}

/// Projective equality by cross-multiplication, no inversion (`projEqM`).
pub fn proj_eq(a: &Pt, b: &Pt) -> bool {
    let (l1, _) = mul_mod_p(&a.x, &b.z);
    let (r1, _) = mul_mod_p(&b.x, &a.z);
    let (l2, _) = mul_mod_p(&a.y, &b.z);
    let (r2, _) = mul_mod_p(&b.y, &a.z);
    l1 == r1 && l2 == r2
}

/// The **Pallas generator** (affine), `PastaCurve.Gp`.
pub fn pallas_generator() -> Pt {
    Pt::affine(
        U256::ONE,
        U256::from_dec(
            "12418654782883325593414442427049395787963493412651469444558597405572177144507",
        ),
    )
}

/// 33 SSA intermediates.
pub const NUM_INTERMEDIATES: usize = 33;
/// 14 division quotients.
pub const NUM_QUOTIENTS: usize = 14;
/// 19 carry/borrow bits.
pub const NUM_CARRY_BITS: usize = 19;
/// The row template's width (`PastaMsmWindowed.W`).
pub const TRACE_WIDTH: usize = 525;

/// Column bases (`PastaMsmWindowed` §1).
pub const COL_QUOT0: usize = 297;
/// First carry/borrow bit column.
pub const COL_BIT0: usize = 423;
/// `ACCX`.
pub const COL_ACCX: usize = 442;
/// `ACCY`.
pub const COL_ACCY: usize = 451;
/// `ACCZ`.
pub const COL_ACCZ: usize = 460;
/// `OPX`.
pub const COL_OPX: usize = 469;
/// `OPY`.
pub const COL_OPY: usize = 478;
/// `OPZ`.
pub const COL_OPZ: usize = 487;
/// `SRCX`.
pub const COL_SRCX: usize = 496;
/// `SRCY`.
pub const COL_SRCY: usize = 505;
/// `SRCZ`.
pub const COL_SRCZ: usize = 514;
/// `BIT`.
pub const COL_BIT: usize = 523;
/// `DBL`.
pub const COL_DBL: usize = 524;
/// The output `X3` group (`OUTX`, intermediate index 26).
pub const COL_OUTX: usize = 234;
/// The output `Y3` group (`OUTY`, intermediate index 29).
pub const COL_OUTY: usize = 261;
/// The output `Z3` group (`OUTZ`, intermediate index 32).
pub const COL_OUTZ: usize = 288;

/// Every cell a single RCB complete add needs: the 33 SSA intermediates in the gadget's
/// allocation order, the 14 quotients in the gadget's emission order, and the 19 carry/borrow
/// bits in the gadget's emission order.
#[derive(Clone, Debug)]
pub struct RcbWitness {
    /// The 33 SSA intermediates; index 26 is `X3`, 29 is `Y3`, 32 is `Z3`.
    pub vals: [U256; NUM_INTERMEDIATES],
    /// The 14 `mul`/`smul` quotients, `q0..q13`.
    pub quots: [U256; NUM_QUOTIENTS],
    /// The 19 add-carry / sub-borrow bits, `b0..b18`.
    pub bits: [u8; NUM_CARRY_BITS],
}

impl RcbWitness {
    /// The output point `(X3 : Y3 : Z3)` = `(X3g, Y3f, Z3c)` (`RcbT.out`).
    pub fn out(&self) -> Pt {
        Pt {
            x: self.vals[26],
            y: self.vals[29],
            z: self.vals[32],
        }
    }
}

/// **The RCB Algorithm 7 trace with its witness slots**, per-op reduced mod `p` — a transcription
/// of `PastaCurveComplete.rcbTraceM` / `rcbTraceZ` in `swCompleteAddGadget`'s emission order, with
/// each gate's quotient or carry captured alongside its output.
///
/// The `let` sequence below is line-for-line the 33-element gate list of `swCompleteAddGadget`;
/// the `q`/`b` index on each line is the witness slot that gate names.
pub fn rcb_add_witness(p1: &Pt, p2: &Pt) -> RcbWitness {
    let (x1, y1, z1) = (p1.x, p1.y, p1.z);
    let (x2, y2, z2) = (p2.x, p2.y, p2.z);

    let (t0a, q0) = mul_mod_p(&x1, &x2); //  1  mul  X1 X2   -> t0a  q0
    let (t1a, q1) = mul_mod_p(&y1, &y2); //  7  mul  Y1 Y2   -> t1a  q1
    let (t2a, q2) = mul_mod_p(&z1, &z2); //  8  mul  Z1 Z2   -> t2a  q2
    let (t3a, b0) = add_mod_p(&x1, &y1); //  4  add  X1 Y1   -> t3a  b0
    let (t4a, b1) = add_mod_p(&x2, &y2); //  5  add  X2 Y2   -> t4a  b1
    let (t3b, q3) = mul_mod_p(&t3a, &t4a); //  6  mul  t3a t4a -> t3b  q3
    let (t4b, b2) = add_mod_p(&t0a, &t1a); //  7  add  t0a t1a -> t4b  b2
    let (t3c, b3) = sub_mod_p(&t3b, &t4b); //  8  sub  t3b t4b -> t3c  b3
    let (t4c, b4) = add_mod_p(&y1, &z1); //  9  add  Y1 Z1   -> t4c  b4
    let (x3a, b5) = add_mod_p(&y2, &z2); // 10  add  Y2 Z2   -> X3a  b5
    let (t4d, q4) = mul_mod_p(&t4c, &x3a); // 11  mul  t4c X3a -> t4d  q4
    let (x3b, b6) = add_mod_p(&t1a, &t2a); // 12  add  t1a t2a -> X3b  b6
    let (t4e, b7) = sub_mod_p(&t4d, &x3b); // 13  sub  t4d X3b -> t4e  b7
    let (x3c, b8) = add_mod_p(&x1, &z1); // 14  add  X1 Z1   -> X3c  b8
    let (y3a, b9) = add_mod_p(&x2, &z2); // 15  add  X2 Z2   -> Y3a  b9
    let (x3d, q5) = mul_mod_p(&x3c, &y3a); // 16  mul  X3c Y3a -> X3d  q5
    let (y3b, b10) = add_mod_p(&t0a, &t2a); // 17  add  t0a t2a -> Y3b  b10
    let (y3c, b11) = sub_mod_p(&x3d, &y3b); // 18  sub  X3d Y3b -> Y3c  b11
    let (x3e, b12) = add_mod_p(&t0a, &t0a); // 19  add  t0a t0a -> X3e  b12
    let (t0b, b13) = add_mod_p(&x3e, &t0a); // 20  add  X3e t0a -> t0b  b13
    let (t2b, q6) = smul_mod_p(CURVE_B3, &t2a); // 21  smul 15 t2a  -> t2b  q6
    let (z3a, b14) = add_mod_p(&t1a, &t2b); // 22  add  t1a t2b -> Z3a  b14
    let (t1b, b15) = sub_mod_p(&t1a, &t2b); // 23  sub  t1a t2b -> t1b  b15
    let (y3d, q7) = smul_mod_p(CURVE_B3, &y3c); // 24  smul 15 Y3c  -> Y3d  q7
    let (x3f, q8) = mul_mod_p(&t4e, &y3d); // 25  mul  t4e Y3d -> X3f  q8
    let (t2c, q9) = mul_mod_p(&t3c, &t1b); // 26  mul  t3c t1b -> t2c  q9
    let (x3g, b16) = sub_mod_p(&t2c, &x3f); // 27  sub  t2c X3f -> X3g  b16
    let (y3e, q10) = mul_mod_p(&y3d, &t0b); // 28  mul  Y3d t0b -> Y3e  q10
    let (t1c, q11) = mul_mod_p(&t1b, &z3a); // 29  mul  t1b Z3a -> t1c  q11
    let (y3f, b17) = add_mod_p(&t1c, &y3e); // 30  add  t1c Y3e -> Y3f  b17
    let (t0c, q12) = mul_mod_p(&t0b, &t3c); // 31  mul  t0b t3c -> t0c  q12
    let (z3b, q13) = mul_mod_p(&z3a, &t4e); // 32  mul  Z3a t4e -> Z3b  q13
    let (z3c, b18) = add_mod_p(&z3b, &t0c); // 33  add  Z3b t0c -> Z3c  b18

    RcbWitness {
        vals: [
            t0a, t1a, t2a, t3a, t4a, t3b, t4b, t3c, t4c, x3a, t4d, x3b, t4e, x3c, y3a, x3d, y3b,
            y3c, x3e, t0b, t2b, z3a, t1b, y3d, x3f, t2c, x3g, y3e, t1c, y3f, t0c, z3b, z3c,
        ],
        quots: [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13],
        bits: [
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
        ],
    }
}

/// The RCB complete addition itself (`PastaCurveComplete.rcbAddM`). Strongly unified: feeding the
/// same point twice DOUBLES it, and `O` is handled without a case split.
pub fn rcb_add(p1: &Pt, p2: &Pt) -> Pt {
    rcb_add_witness(p1, p2).out()
}

/// `[k]P` by double-and-add over `rcb_add` (test helper — this is NOT what the AIR does; the AIR
/// does one add per row and the schedule decides which).
pub fn scalar_mul(k: u64, base: &Pt) -> Pt {
    let mut acc = Pt::INFINITY;
    let mut cur = *base;
    let mut n = k;
    while n > 0 {
        if n & 1 == 1 {
            acc = rcb_add(&acc, &cur);
        }
        cur = rcb_add(&cur, &cur);
        n >>= 1;
    }
    acc
}

// ---------------------------------------------------------------------------------------------
// PART 2 — trace cells.
// ---------------------------------------------------------------------------------------------

fn put_field(row: &mut [BabyBear], base: usize, v: &U256) {
    for i in 0..NUM_LIMBS {
        row[base + i] = BabyBear::new(v.limb30(i));
    }
}

/// Read a 9×30 field element back out of a trace row (test helper).
pub fn read_field(row: &[BabyBear], base: usize) -> U256 {
    let mut limbs = [0u32; NUM_LIMBS];
    for (i, limb) in limbs.iter_mut().enumerate() {
        *limb = row[base + i].as_u32();
    }
    U256::from_limbs30(&limbs)
}

/// Read a projective point back out of a trace row (test helper).
pub fn read_point(row: &[BabyBear], base_x: usize, base_y: usize, base_z: usize) -> Pt {
    Pt {
        x: read_field(row, base_x),
        y: read_field(row, base_y),
        z: read_field(row, base_z),
    }
}

/// **Fill one row** — exactly [`TRACE_WIDTH`] cells.
///
/// `acc` is the accumulator coming into the row, `src` its source point, `bit` the conditional-add
/// bit and `dbl` the doubling selector. On a doubling row the caller must pass `src == acc` and
/// `bit == true` (the Lean `dblPinGates` pin exactly that); this is asserted rather than silently
/// repaired, because a mismatch means the SCHEDULE is wrong.
pub fn fill_row(acc: &Pt, src: &Pt, bit: bool, dbl: bool) -> Vec<BabyBear> {
    if dbl {
        assert!(src == acc, "a DBL=1 row must have SRC == ACC (dblPinHead)");
        assert!(bit, "a DBL=1 row must have BIT == 1 (dblBitHead)");
    }
    // The selector's output: `condRef bit SRC`.
    let op = if bit { *src } else { Pt::INFINITY };
    let w = rcb_add_witness(acc, &op);

    let mut row = vec![BabyBear::new(0); TRACE_WIDTH];
    for (idx, v) in w.vals.iter().enumerate() {
        put_field(&mut row, NUM_LIMBS * idx, v);
    }
    for (qidx, q) in w.quots.iter().enumerate() {
        put_field(&mut row, COL_QUOT0 + NUM_LIMBS * qidx, q);
    }
    for (bidx, b) in w.bits.iter().enumerate() {
        row[COL_BIT0 + bidx] = BabyBear::new(u32::from(*b));
    }
    put_field(&mut row, COL_ACCX, &acc.x);
    put_field(&mut row, COL_ACCY, &acc.y);
    put_field(&mut row, COL_ACCZ, &acc.z);
    put_field(&mut row, COL_OPX, &op.x);
    put_field(&mut row, COL_OPY, &op.y);
    put_field(&mut row, COL_OPZ, &op.z);
    put_field(&mut row, COL_SRCX, &src.x);
    put_field(&mut row, COL_SRCY, &src.y);
    put_field(&mut row, COL_SRCZ, &src.z);
    row[COL_BIT] = BabyBear::new(u32::from(bit));
    row[COL_DBL] = BabyBear::new(u32::from(dbl));
    row
}

// ---------------------------------------------------------------------------------------------
// PART 2b — the ON-CURVE certificate block (`PastaMsmOnCurve.onCurveGates`).
//
// `PastaMsmOnCurve` emits 8 constraints per gated point; this fills the 135 witness columns that
// make their bodies vanish OVER ℤ. It authors no constraint. The layout is the Lean file's §1
// table, offset-for-offset.
// ---------------------------------------------------------------------------------------------

/// Columns one point's on-curve certificate occupies (`PastaMsmOnCurve.OC_COLS`).
pub const OC_COLS: usize = 135;
/// `PastaMsmOnCurve.OC_ACC` — the `ACC` point's certificate base (`PastaMsmBound.WB`).
pub const COL_OC_ACC: usize = 529;
/// `PastaMsmOnCurve.OC_SRC` — the `SRC` point's certificate base.
pub const COL_OC_SRC: usize = COL_OC_ACC + OC_COLS;
/// `PastaMsmOnCurve.WOC` — the curve-gated row template's width.
pub const ONCURVE_WIDTH: usize = COL_OC_ACC + 2 * OC_COLS;

/// **Fill one point's on-curve certificate** at `base`, in `PastaMsmOnCurve`'s slot order:
/// `XX, qXX, YY, qYY, ZZ, qZZ, X3, qX3, Z3, qZ3, BZ3, qBZ3, QC, YINV, qINV`.
///
/// `QC` is the curve head's reduction quotient. The head is
/// `YY·Z − X3 − BZ3 + 2p − p·QC`, so with `YY·Z = p·qS + rS` the honest witness is
/// `QC = qS + (rS + 2p − X3 − BZ3)/p`; the `+2p` is what makes that division exact and
/// non-negative for every honest input (`rS − X3 − BZ3 ∈ (−2p, p)`).
///
/// ⚠ Panics on `Y = 0`, which is precisely the state the emitted `nonZeroHead` refuses. A trace
/// that wants such a row is the ABSORBING-STATE forgery, and it has no honest witness — see
/// [`put_on_curve_block_forged`], which is what a test must use to build one.
pub fn put_on_curve_block(row: &mut [BabyBear], base: usize, pt: &Pt) {
    let y_inv = inv_mod_p(&pt.y);
    put_on_curve_block_with_inverse(row, base, pt, &y_inv);
}

/// [`put_on_curve_block`] with the inverse supplied — the seam a forgery test needs, because at
/// `Y = 0` no inverse exists and the point of the exercise is to watch the gate refuse the
/// best witness a prover could possibly write.
pub fn put_on_curve_block_with_inverse(row: &mut [BabyBear], base: usize, pt: &Pt, y_inv: &U256) {
    let (xx, q_xx) = mul_mod_p(&pt.x, &pt.x);
    let (yy, q_yy) = mul_mod_p(&pt.y, &pt.y);
    let (zz, q_zz) = mul_mod_p(&pt.z, &pt.z);
    let (x3, q_x3) = mul_mod_p(&xx, &pt.x);
    let (z3, q_z3) = mul_mod_p(&zz, &pt.z);
    let (bz3, q_bz3) = smul_mod_p(CURVE_B, &z3);
    // `YY·Z = p·q_s + r_s`
    let (r_s, q_s) = mul_mod_p(&yy, &pt.z);
    // `R = r_s + 2p − X3 − BZ3`, in `(0, 3p) ⊂ [0, 2^256)`.
    let mut r = r_s;
    for _ in 0..2 {
        let (t, ovf) = r.adc(&P_PASTA);
        debug_assert!(!ovf, "r_s + 2p < 3p < 2^256");
        r = t;
    }
    r = r.sbb(&x3).0;
    r = r.sbb(&bz3).0;
    // `R/p ∈ {0, 1, 2}` when the point is on the curve; on an OFF-curve point the remainder is
    // nonzero and the emitted head does not vanish — which is the refusal we want, not a bug.
    let mut extra = U256::ZERO;
    while r >= P_PASTA {
        r = r.sbb(&P_PASTA).0;
        extra = extra.adc(&U256::ONE).0;
    }
    let qc = q_s.adc(&extra).0;
    // `Y·YINV = 1 + p·q_inv`
    let (_, q_inv) = mul_mod_p(&pt.y, y_inv);

    let groups = [
        xx, q_xx, yy, q_yy, zz, q_zz, x3, q_x3, z3, q_z3, bz3, q_bz3, qc, *y_inv, q_inv,
    ];
    for (i, g) in groups.iter().enumerate() {
        put_field(row, base + NUM_LIMBS * i, g);
    }
}

/// The BEST on-curve witness a prover can write for a point the gate refuses — every derivable
/// slot honest, the inverse slot zero because none exists. Exists so a forgery test cannot be
/// dismissed as "the witness generator gave up".
pub fn put_on_curve_block_forged(row: &mut [BabyBear], base: usize, pt: &Pt) {
    put_on_curve_block_with_inverse(row, base, pt, &U256::ZERO);
}

/// Widen a 525-column windowed row to [`ONCURVE_WIDTH`] and stamp both certificates. The caller
/// stamps the four `PastaMsmSliced`/`PastaMsmBound` declaration/index columns itself.
pub fn put_row_certificates(row: &mut [BabyBear], acc: &Pt, src: &Pt) {
    put_on_curve_block(row, COL_OC_ACC, acc);
    put_on_curve_block(row, COL_OC_SRC, src);
}

// ---------------------------------------------------------------------------------------------
// PART 2c — the SCALAR-DERIVATION block (`PastaMsmScalarDerive.deriveGates`).
//
// `PastaMsmScalarDerive` emits `264 + 29·nb + 2·planes` constraints that RECOMPUTE the row's own
// s-vector entry from the challenge vector on the wire and certify that it is the CANONICAL
// representative of its class mod `q`. This fills the `265 + 37·nb + 2·planes` witness columns that
// make their bodies vanish over ℤ. It authors no constraint: the layout below is the Lean file's §1
// table, offset for offset, and the arithmetic is the same `fqMulCore` witness `mul_mod_q` produces
// for any other modular multiplication, plus one subtraction for the certificate.
// ---------------------------------------------------------------------------------------------

/// The column layout `PastaMsmScalarDerive` §1 declares, at a given challenge count and plane
/// count. Everything is appended above [`ONCURVE_WIDTH`]; not one existing column moves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeriveLayout {
    /// The challenge count (`nb`). 15 for a 2^15-point Wrap SRS.
    pub nb: usize,
    /// The bit-plane count (`planes`). 256 for a Pallas-scalar-sized s-vector entry.
    pub planes: usize,
}

impl DeriveLayout {
    /// `PastaMsmScalarDerive.DB` — the base of everything the derivation adds.
    pub const DB: usize = ONCURVE_WIDTH;

    /// `PIDX` — the row's bit-plane index.
    pub const PIDX: usize = Self::DB;

    /// `GBc j` — the `j`-th binary digit of `GIDX`.
    pub fn gb(&self, j: usize) -> usize {
        debug_assert!(j < self.nb);
        Self::DB + 1 + j
    }

    /// `CHc m` — challenge limb `m` (flat: `NUM_LIMBS·j + l`).
    pub fn ch(&self, m: usize) -> usize {
        Self::DB + 1 + self.nb + m
    }

    /// `MUc m` — selected-multiplier limb `m`.
    pub fn mu(&self, m: usize) -> usize {
        Self::DB + 1 + self.nb + NUM_LIMBS * self.nb + m
    }

    /// `PRc m` — running-product limb `m` (`nb + 1` blocks; block `nb` IS `s_GIDX`).
    pub fn pr(&self, m: usize) -> usize {
        Self::DB + 1 + self.nb + 2 * NUM_LIMBS * self.nb + m
    }

    /// `QUc m` — reduction-quotient limb `m`.
    pub fn qu(&self, m: usize) -> usize {
        Self::DB + 1 + self.nb + 2 * NUM_LIMBS * self.nb + NUM_LIMBS * (self.nb + 1) + m
    }

    /// `SBc p` — the `p`-th binary digit of the derived scalar, MSB-first.
    pub fn sb(&self, p: usize) -> usize {
        debug_assert!(p < self.planes);
        Self::DB + 1 + self.nb + 4 * NUM_LIMBS * self.nb + NUM_LIMBS + p
    }

    /// `SEc p` — the `p`-th plane selector.
    pub fn se(&self, p: usize) -> usize {
        debug_assert!(p < self.planes);
        Self::DB + 1 + self.nb + 4 * NUM_LIMBS * self.nb + NUM_LIMBS + self.planes + p
    }

    /// `CBc p` — the `p`-th bit of the canonicity certificate `q − 1 − s`, LSB-first.
    ///
    /// ⚠ Indexed by [`CBITS`], the CONSTANT 255 — never by `planes`. The two counts are
    /// independent and only one of them is a property of the field; see
    /// `PastaMsmScalarDerive.CBITS`.
    pub fn cb(&self, p: usize) -> usize {
        debug_assert!(p < CBITS);
        Self::DB + 1 + self.nb + 4 * NUM_LIMBS * self.nb + NUM_LIMBS + 2 * self.planes + p
    }

    /// `PastaMsmScalarDerive.WD` — the derived row template's width.
    pub fn width(&self) -> usize {
        Self::DB + 1 + self.nb + 4 * NUM_LIMBS * self.nb + NUM_LIMBS + 2 * self.planes + CBITS
    }

    /// `PastaMsmScalarDerive.PID` — the sliced 29 public inputs plus `NUM_LIMBS·nb` challenge
    /// limbs.
    pub fn pi_count(&self) -> usize {
        SLICED_PI_COUNT + NUM_LIMBS * self.nb
    }
}

/// `PastaMsmSliced.PI_COUNT` — `[lo, hi]` plus the 27 published partial limbs.
pub const SLICED_PI_COUNT: usize = 29;

/// `PastaMsmScalarDerive.CBITS` — the canonicity certificate's width. **The constant 255, never
/// `planes`**: `q < 2^255`, so `q − 1 − s` needs exactly 255 boolean places. Writing `planes` here
/// would make the gate refuse every honest trace at every small plane count.
pub const CBITS: usize = 255;

/// **The canonicity certificate for `s`**: `q − 1 − s`, which exists as a non-negative 255-bit
/// number exactly when `s < q` — i.e. exactly when `s` is a reduced Pallas scalar. There is no
/// search: the honest prover subtracts.
///
/// Panics if `s ≥ q`, which is the witness generator refusing to pretend a non-canonical value has
/// a certificate. That refusal is the point: `PastaMsmScalarDerive.canon_forces` proves no
/// satisfying assignment exists there, so a witness that produced one would be a bug in this file.
pub fn canonicity_certificate(s: &U256) -> U256 {
    assert!(*s < Q_PASTA, "no canonicity certificate exists for s >= q");
    let (qm1, b1) = Q_PASTA.sbb(&U256::ONE);
    debug_assert!(!b1);
    let (cert, b2) = qm1.sbb(s);
    debug_assert!(!b2);
    cert
}

/// **The tensor, in Rust**: `s_idx = ∏_j c_j^{bit_j(idx)}` in `ZMod q`, the same
/// `PastaMsmScalarBound.sAt` the manifest is built from — head challenge paired with the HIGH
/// index bit. Used to cross-check the DESCRIPTOR's digit column against the challenge vector, and
/// to fill the chain.
pub fn derive_scalar(chals: &[U256], idx: usize) -> U256 {
    let nb = chals.len();
    let mut acc = U256::ONE;
    for (j, c) in chals.iter().enumerate() {
        if (idx >> (nb - 1 - j)) & 1 == 1 {
            acc = mul_mod_q(&acc, c).0;
        }
    }
    acc
}

/// **Fill one row's derivation block**, returning the derived scalar the chain lands on.
///
/// ⚑ THE TWO CHALLENGE VECTORS ARE SEPARATE ON PURPOSE, and the separation IS the fourth tamper.
/// `wire` fills the `CHc` columns — the PI-bound, threaded vector, i.e. WHAT THE VERIFIER SUPPLIES.
/// `derived` fills the multiplier, quotient, product and digit columns — i.e. what the PROVER
/// claims the scalar is. An honest row passes the same slice twice; the forgery passes two
/// different blocks, and that is precisely `PastaMsmScalarDerive` §5's `katAsg cs ds`.
///
/// `gidx` is the ABSOLUTE generator index the row consumes — the value `PastaMsmBound`'s `GIDX`
/// thread already carries — and `plane` is the row's bit plane, the value the `PIDX` thread
/// carries. Both are read off the schedule, never invented.
///
/// ⚠ `gidx < 2^nb` is required — the emitted `gidxBitsGate` decomposes `GIDX` into exactly `nb`
/// binary digits, so a generator index past the s-vector's length has no witness at all. That is
/// the emitted object's own statement that the challenge count and the SRS size are the same
/// number, and it is asserted rather than silently truncated.
pub fn put_derive_block(
    row: &mut [BabyBear],
    lay: &DeriveLayout,
    wire: &[U256],
    derived: &[U256],
    gidx: usize,
    plane: usize,
) -> U256 {
    assert_eq!(wire.len(), lay.nb, "wire challenge count must be nb");
    assert_eq!(derived.len(), lay.nb, "derived challenge count must be nb");
    assert!(
        lay.nb >= 64 || gidx < (1usize << lay.nb),
        "GIDX {gidx} does not fit {} binary digits (gidxBitsGate)",
        lay.nb
    );
    assert!(plane < lay.planes, "PIDX {plane} is past the plane count");

    row[DeriveLayout::PIDX] = BabyBear::new(plane as u32);
    for j in 0..lay.nb {
        row[lay.gb(j)] = BabyBear::new(((gidx >> j) & 1) as u32);
    }
    for (j, c) in wire.iter().enumerate() {
        put_field(row, lay.ch(NUM_LIMBS * j), c);
    }

    // The chain: `PR 0 = 1`, `PR (j+1) ≡ PR j · MU j (mod q)`, with `MU j` the challenge selected
    // by index digit `nb − 1 − j` (`mulSelHead`'s pairing) and the field ONE otherwise.
    let mut prd = U256::ONE;
    put_field(row, lay.pr(0), &prd);
    for (j, c) in derived.iter().enumerate() {
        let selected = (gidx >> (lay.nb - 1 - j)) & 1 == 1;
        let mu = if selected { *c } else { U256::ONE };
        put_field(row, lay.mu(NUM_LIMBS * j), &mu);
        let (next, quot) = mul_mod_q(&prd, &mu);
        put_field(row, lay.qu(NUM_LIMBS * j), &quot);
        put_field(row, lay.pr(NUM_LIMBS * (j + 1)), &next);
        prd = next;
    }

    // The decomposition (MSB-first over `planes` planes) and the plane selector.
    for p in 0..lay.planes {
        row[lay.sb(p)] = BabyBear::new(prd.bit(lay.planes - 1 - p));
        row[lay.se(p)] = BabyBear::new(u32::from(p == plane));
    }
    // ⚑ The CANONICITY CERTIFICATE (`PastaMsmScalarDerive` §2.7): `q − 1 − s`, LSB-first over the
    // constant 255 places. `mul_mod_q` reduces, so `prd < q` always holds on an honest chain and
    // the certificate always exists — satisfiability of the new gate is structural here, not a
    // property of the particular challenge vector.
    let cert = canonicity_certificate(&prd);
    for p in 0..CBITS {
        row[lay.cb(p)] = BabyBear::new(cert.bit(p));
    }
    prd
}

/// What one row of the schedule asks for.
#[derive(Clone, Copy, Debug)]
pub enum RowSpec {
    /// `DBL = 1`: `SRC := ACC`, `BIT := 1`. The row doubles the accumulator, structurally
    /// (`PastaMsmWindowed.dblRow_forces` — the pins make it a doubling, it is not merely
    /// scheduled to be one).
    Double,
    /// `DBL = 0`: a conditional add of `src` under `bit`. On `bit = false` the selector replaces
    /// the addend with `O` and the row adds the identity.
    CondAdd {
        /// The row's source point.
        src: Pt,
        /// The conditional-add bit.
        bit: bool,
    },
}

/// **Build a threaded trace.**
///
/// Every row is an HONEST RCB complete add, threaded so that row `i+1`'s `ACC` group is row `i`'s
/// output group — the three `windowGate`s. The height is rounded UP to a power of two (the
/// prover requires that); the pad rows are `CondAdd { src: O, bit: false }`, i.e. real additions
/// of the identity, because `when_transition` exempts only the LAST row — every other row,
/// padding included, has all 45 constraints enforced.
///
/// Note that RCB Alg. 7 at `Q = O` returns `Y₁·(X₁, Y₁, Z₁)`: adding the identity rescales the
/// projective representative. That is the same POINT (Pallas is prime order, so `Y₁ ≠ 0` on any
/// real point), but the literal coordinates of a padded run differ from the unpadded one.
pub fn build_trace(acc0: &Pt, schedule: &[RowSpec]) -> Vec<Vec<BabyBear>> {
    let height = schedule.len().next_power_of_two().max(1);
    let mut acc = *acc0;
    let mut rows = Vec::with_capacity(height);
    for i in 0..height {
        let (src, bit, dbl) = match schedule.get(i) {
            Some(RowSpec::Double) => (acc, true, true),
            Some(RowSpec::CondAdd { src, bit }) => (*src, *bit, false),
            None => (Pt::INFINITY, false, false),
        };
        let row = fill_row(&acc, &src, bit, dbl);
        acc = read_point(&row, COL_OUTX, COL_OUTY, COL_OUTZ);
        rows.push(row);
    }
    rows
}

/// The reference the schedule computes — `PastaMsmWindowed.windowedRef`, folded in Rust so a test
/// can compare the trace's threaded accumulator against an independent walk of the same schedule.
pub fn fold_schedule(acc0: &Pt, schedule: &[RowSpec]) -> Pt {
    let mut acc = *acc0;
    for spec in schedule {
        let addend = match spec {
            RowSpec::Double => acc,
            RowSpec::CondAdd { src, bit } => {
                if *bit {
                    *src
                } else {
                    Pt::INFINITY
                }
            }
        };
        acc = rcb_add(&acc, &addend);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u256_decimal_roundtrip() {
        let s = "28948022309329048855892746252171976963363056481941560715954676764349967630337";
        assert_eq!(U256::from_dec(s), P_PASTA);
        assert_eq!(P_PASTA.to_dec(), s);
    }

    #[test]
    fn limb_encoding_matches_lean_kat() {
        // `PastaField` §0: `limbOf X 8 = 4660`, `limbOf X 0 = 645367961`.
        let x = U256::from_dec(
            "8234104123542484906572010032064808850921064262571995443881932229087025662105",
        );
        assert_eq!(x.limb30(8), 4660);
        assert_eq!(x.limb30(0), 645_367_961);
        let mut limbs = [0u32; NUM_LIMBS];
        for (i, l) in limbs.iter_mut().enumerate() {
            *l = x.limb30(i);
        }
        assert_eq!(U256::from_limbs30(&limbs), x);
    }

    #[test]
    fn mul_quotient_identity_is_exact() {
        let a = U256::from_dec(
            "8234104123542484906572010032064808850921064262571995443881932229087025662105",
        );
        let b = U256::from_dec(
            "6809518635040324971929803101472088575662782660641002711672773399993035656976",
        );
        let (z, q) = mul_mod_p(&a, &b);
        // a·b == p·q + z, checked in 512 bits.
        let lhs = mul_wide(&a, &b);
        let mut rhs = mul_wide(&P_PASTA, &q);
        let mut carry = 0u128;
        for i in 0..8 {
            let t = u128::from(rhs[i]) + u128::from(if i < 4 { z.0[i] } else { 0 }) + carry;
            rhs[i] = t as u64;
            carry = t >> 64;
        }
        assert_eq!(carry, 0);
        assert_eq!(lhs, rhs);
    }

    /// The `#guard` KATs of `PastaCurveComplete` §2, reproduced against this transcription.
    #[test]
    fn rcb_reference_matches_lean_guards() {
        let g = pallas_generator();
        assert!(g.on_curve());
        let g2 = rcb_add(&g, &g);
        assert!(g2.on_curve(), "doubling stays on curve");
        let g3 = rcb_add(&g2, &g);
        assert!(g3.on_curve(), "generic add stays on curve");
        // P + O = P and O + P = P.
        assert!(proj_eq(&rcb_add(&g, &Pt::INFINITY), &g));
        assert!(proj_eq(&rcb_add(&Pt::INFINITY, &g), &g));
        // P + (−P) = O; O + O = O.
        let neg_g = Pt {
            x: g.x,
            y: sub_mod_p(&U256::ZERO, &g.y).0,
            z: g.z,
        };
        assert!(rcb_add(&g, &neg_g).is_infinity());
        assert!(rcb_add(&Pt::INFINITY, &Pt::INFINITY).is_infinity());
        // A discriminating negative control: [2]G ≠ [3]G.
        assert!(!proj_eq(&g2, &g3));
        // Strong unification: double-and-add agrees with repeated addition.
        assert!(proj_eq(&scalar_mul(3, &g), &g3));
        assert!(proj_eq(&scalar_mul(5, &g), &rcb_add(&rcb_add(&g3, &g), &g)));
    }

    #[test]
    fn filled_row_has_the_declared_shape() {
        let g = pallas_generator();
        let row = fill_row(&g, &g, true, true);
        assert_eq!(row.len(), TRACE_WIDTH);
        // The doubling row's output group holds [2]G.
        let out = read_point(&row, COL_OUTX, COL_OUTY, COL_OUTZ);
        assert_eq!(out, rcb_add(&g, &g));
        // The selector passed the source through.
        assert_eq!(read_point(&row, COL_OPX, COL_OPY, COL_OPZ), g);
        assert_eq!(row[COL_BIT].as_u32(), 1);
        assert_eq!(row[COL_DBL].as_u32(), 1);
        // A bit = 0 row's addend is O.
        let row0 = fill_row(&g, &g, false, false);
        assert_eq!(read_point(&row0, COL_OPX, COL_OPY, COL_OPZ), Pt::INFINITY);
    }

    #[test]
    fn trace_threads_the_accumulator() {
        let g = pallas_generator();
        let schedule = [
            RowSpec::Double,
            RowSpec::CondAdd { src: g, bit: true },
            RowSpec::CondAdd { src: g, bit: false },
        ];
        let trace = build_trace(&g, &schedule);
        assert_eq!(trace.len(), 4, "rounded up to a power of two");
        for i in 0..trace.len() - 1 {
            let out = read_point(&trace[i], COL_OUTX, COL_OUTY, COL_OUTZ);
            let next_acc = read_point(&trace[i + 1], COL_ACCX, COL_ACCY, COL_ACCZ);
            assert_eq!(
                out,
                next_acc,
                "thread broken between rows {i} and {}",
                i + 1
            );
        }
        // Three scheduled rows: 2G, then +G = 3G, then +O = 3G (rescaled).
        let after_three = read_point(&trace[3], COL_ACCX, COL_ACCY, COL_ACCZ);
        assert!(proj_eq(&after_three, &scalar_mul(3, &g)));
        assert_eq!(after_three, fold_schedule(&g, &schedule));
    }
}
