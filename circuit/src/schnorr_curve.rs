//! Elliptic curve over BabyBear^8 for Schnorr signatures.
//!
//! Defines a short Weierstrass curve y^2 = x^3 + ax + b over BabyBear^8
//! (`= F_p[z]/(z^8 - 11)`, a genuine field — see [`crate::babybear8`]), with
//! affine point arithmetic suitable for STARK verification.
//!
//! # Curve Selection
//!
//! The curve is `y^2 = x^3 + (z+2)·x + (z^3+8)` over `F_{p^8}`. It is defined
//! *directly* over the degree-8 field (its coefficients involve `z`, not just
//! base-field constants), which is essential: any curve defined over the base
//! field `F_p` has `#E(F_{p^8})` divisible by the nested point-group orders
//! `#E(F_p)·#E(F_{p^2})·#E(F_{p^4})`, so it is never near-prime. This curve was
//! found by an SEA point-count search (PARI/GP) to have **prime order**
//!
//! ```text
//!   N = 269903886087112502248563194479599378757044855200285447932848137338699712099
//! ```
//!
//! a 248-bit prime with **cofactor h = 1** (`#E = N` exactly). A prime order
//! with cofactor 1 means *every* non-identity point generates the full group,
//! and the discrete-log problem has no small-subgroup (Pohlig–Hellman) shortcut.
//! The order is within the Hasse interval `|#E − (p^8+1)| ≤ 2·sqrt(p^8)`.
//! (Verified: `isprime(N)`, `ellcard(E) == N`, cofactor `== 1`.)
//!
//! # History
//!
//! An earlier version used a placeholder `y^2 = x^3 + 3` with generator `(1, 2)`
//! that lived in the base-field embedding `F_p ⊂ F_{p^8}`, whose order was the
//! composite 31-bit number `2013191319 = 3·331·2027383` — trivially broken by
//! Pohlig–Hellman/Pollard-rho. It also rode on the broken (non-field) BabyBear^8
//! tower. Both are now fixed.
//!
//! This curve is on the confidential-VALUE path (in-circuit Schnorr), NOT core
//! turn auth (that is Ed25519).
//!
//! # Security Target
//!
//! BabyBear^8 has field size `p^8 ≈ 2^248`; a prime-order curve over it provides
//! ~124-bit security against Pollard-rho attacks (`sqrt(N/2) ≈ 2^124`).
//!
//! # Point Representation
//!
//! Points are stored in affine coordinates (x, y) plus an `is_infinity` flag.
//! This is optimal for STARK verification where the "slope as witness" technique
//! allows the verifier to check point additions with degree-2 constraints.

use crate::babybear8::BabyBear8;
use crate::field::BabyBear;

// ============================================================================
// Curve Parameters — prime-order curve y^2 = x^3 + (z+2)x + (z^3+8) over F_{p^8}
// ============================================================================

/// Curve parameter `a = z + 2` (coefficient of x in y^2 = x^3 + ax + b).
///
/// In the power basis of `F_p[z]/(z^8 - 11)`, `z + 2` is `[2, 1, 0, …]`. `a ≠ 0`
/// here; the doubling formula carries the `+a` term in its numerator.
pub const CURVE_A: BabyBear8 = BabyBear8([
    BabyBear(2),
    BabyBear(1),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
]);

/// Curve parameter `b = z^3 + 8` (constant term in y^2 = x^3 + ax + b).
///
/// In the power basis, `z^3 + 8` is `[8, 0, 0, 1, 0, …]`.
pub const CURVE_B: BabyBear8 = BabyBear8([
    BabyBear(8),
    BabyBear(0),
    BabyBear(0),
    BabyBear(1),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
]);

/// Generator of the (full, prime-order) group.
///
/// With cofactor 1 and prime order `N`, every non-identity point generates the
/// whole group. This generator was produced by scanning base-field x-values for
/// one whose right-hand side is a square: at `x = 1`,
/// `1 + (z+2) + (z^3+8) = z^3 + z + 11` is a quadratic residue, and the chosen
/// `y` is its square root. (Verified on-curve and `N·G = O`, `2·G ≠ O`.)
pub const GENERATOR: CurvePoint = CurvePoint {
    x: BabyBear8([
        BabyBear(1),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
    ]),
    y: BabyBear8([
        BabyBear(417687251),
        BabyBear(1863107357),
        BabyBear(177749990),
        BabyBear(1036295843),
        BabyBear(398021929),
        BabyBear(450362472),
        BabyBear(1199411012),
        BabyBear(113045356),
    ]),
    is_infinity: false,
};

/// Group order `N` of the curve (= order of `GENERATOR`), stored as 8
/// little-endian u32 limbs.
///
/// `N = 269903886087112502248563194479599378757044855200285447932848137338699712099`
/// is a 248-bit prime; `#E(F_{p^8}) = N` exactly (cofactor 1). All scalars
/// (`sk`, nonces `k`, challenges `e`, responses `s`) are reduced mod `N` via the
/// full bigint arithmetic below.
pub const ORDER: [u32; 8] = [
    3630237283, 2285651324, 1488992648, 1932759141, 1148232707, 1275750001, 2335120239, 10011291,
];

// ============================================================================
// Point Type
// ============================================================================

/// A point on the elliptic curve over BabyBear^8, in affine coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CurvePoint {
    pub x: BabyBear8,
    pub y: BabyBear8,
    pub is_infinity: bool,
}

impl CurvePoint {
    /// The point at infinity (additive identity).
    pub const INFINITY: Self = Self {
        x: BabyBear8::ZERO,
        y: BabyBear8::ZERO,
        is_infinity: true,
    };

    /// Create a point from coordinates. Does NOT check if on curve.
    pub fn new(x: BabyBear8, y: BabyBear8) -> Self {
        Self {
            x,
            y,
            is_infinity: false,
        }
    }

    /// Check if this point lies on the curve y^2 = x^3 + ax + b.
    pub fn is_on_curve(&self) -> bool {
        if self.is_infinity {
            return true;
        }
        // y^2
        let y2 = self.y.square();
        // x^3 + a*x + b
        let x2 = self.x.square();
        let x3 = x2.mul(&self.x);
        let ax = CURVE_A.mul(&self.x);
        let rhs = x3.add(&ax).add(&CURVE_B);
        y2 == rhs
    }

    /// Negate a point (reflect across x-axis).
    pub fn negate(&self) -> Self {
        if self.is_infinity {
            return *self;
        }
        Self {
            x: self.x,
            y: self.y.neg(),
            is_infinity: false,
        }
    }

    /// Point doubling: 2*P.
    ///
    /// For y^2 = x^3 + ax + b:
    ///   lambda = (3*x^2 + a) / (2*y)
    ///   x3 = lambda^2 - 2*x
    ///   y3 = lambda*(x - x3) - y
    pub fn double(&self) -> Self {
        if self.is_infinity {
            return *self;
        }
        // If y = 0, the tangent is vertical => result is infinity
        if self.y.is_zero() {
            return Self::INFINITY;
        }

        let x = &self.x;
        let y = &self.y;

        // lambda = (3*x^2 + a) / (2*y)
        let x2 = x.square();
        let three = BabyBear8::from_base(BabyBear::new(3));
        let two = BabyBear8::from_base(BabyBear::new(2));
        let numerator = three.mul(&x2).add(&CURVE_A);
        let denominator = two.mul(y);
        let denom_inv = denominator.inverse().expect("2y should be non-zero");
        let lambda = numerator.mul(&denom_inv);

        // x3 = lambda^2 - 2*x
        let lambda2 = lambda.square();
        let x3 = lambda2.sub(&two.mul(x));

        // y3 = lambda*(x - x3) - y
        let y3 = lambda.mul(&x.sub(&x3)).sub(y);

        Self::new(x3, y3)
    }

    /// Point addition: P + Q.
    ///
    /// For distinct points:
    ///   lambda = (y2 - y1) / (x2 - x1)
    ///   x3 = lambda^2 - x1 - x2
    ///   y3 = lambda*(x1 - x3) - y1
    pub fn add(&self, other: &Self) -> Self {
        if self.is_infinity {
            return *other;
        }
        if other.is_infinity {
            return *self;
        }

        // Same x-coordinate
        if self.x == other.x {
            if self.y == other.y {
                // P == Q => double
                return self.double();
            } else {
                // P == -Q => infinity
                return Self::INFINITY;
            }
        }

        // General case: distinct x-coordinates
        let dx = other.x.sub(&self.x);
        let dy = other.y.sub(&self.y);
        let dx_inv = dx
            .inverse()
            .expect("dx should be non-zero for distinct points");
        let lambda = dy.mul(&dx_inv);

        // x3 = lambda^2 - x1 - x2
        let lambda2 = lambda.square();
        let x3 = lambda2.sub(&self.x).sub(&other.x);

        // y3 = lambda*(x1 - x3) - y1
        let y3 = lambda.mul(&self.x.sub(&x3)).sub(&self.y);

        Self::new(x3, y3)
    }

    /// Scalar multiplication via double-and-add.
    ///
    /// The scalar is represented as 8 little-endian u32 limbs (up to 256 bits).
    /// Skips processing of trailing zero limbs for efficiency.
    pub fn scalar_mul(&self, scalar: &[u32; 8]) -> Self {
        // Find the highest non-zero limb to avoid unnecessary doublings
        let effective_limbs = match scalar.iter().rposition(|&x| x != 0) {
            Some(pos) => pos + 1,
            None => return Self::INFINITY, // scalar is zero
        };

        let mut result = Self::INFINITY;
        let mut base = *self;

        for &limb in scalar.iter().take(effective_limbs) {
            let mut e = limb;
            for _ in 0..32 {
                if e & 1 == 1 {
                    result = result.add(&base);
                }
                base = base.double();
                e >>= 1;
            }
        }
        result
    }

    /// Scalar multiplication by a single u32 value (convenience).
    pub fn scalar_mul_small(&self, scalar: u32) -> Self {
        let mut limbs = [0u32; 8];
        limbs[0] = scalar;
        self.scalar_mul(&limbs)
    }
}

// ============================================================================
// Scalar Arithmetic (full 256-bit bigint, mod the 248-bit prime ORDER = N)
// ============================================================================
//
// Scalars are 8 little-endian u32 limbs (a 256-bit container; values live in
// [0, N)). Because N is a genuine 248-bit prime, every operation is real bigint
// arithmetic reduced mod N — there is no single-limb shortcut. Modular
// multiplication uses left-to-right double-and-add (`mul_mod`), which needs only
// `add_mod`/`double_mod` and is manifestly correct for reduced inputs; reduction
// of arbitrary 256-bit values (from hashes) is the same bit-fold against `ONE`.

/// 8-limb big integer (little-endian u32 limbs) representing scalars mod ORDER.
pub type Scalar = [u32; 8];

/// Add two 8-limb values, returning the 8-limb low result and the carry-out bit.
#[inline]
fn add_raw(a: &Scalar, b: &Scalar) -> (Scalar, u32) {
    let mut r = [0u32; 8];
    let mut carry: u64 = 0;
    for i in 0..8 {
        let s = a[i] as u64 + b[i] as u64 + carry;
        r[i] = s as u32;
        carry = s >> 32;
    }
    (r, carry as u32)
}

/// Subtract `b` from `a` (8-limb), returning the low result and the borrow-out.
#[inline]
fn sub_raw(a: &Scalar, b: &Scalar) -> (Scalar, u32) {
    let mut r = [0u32; 8];
    let mut borrow: u64 = 0;
    for i in 0..8 {
        let d = (a[i] as u64).wrapping_sub(b[i] as u64).wrapping_sub(borrow);
        r[i] = d as u32;
        borrow = (d >> 63) & 1; // 1 if it underflowed
    }
    (r, borrow as u32)
}

/// Compare a < b (both as unsigned 256-bit integers).
pub fn scalar_lt(a: &Scalar, b: &Scalar) -> bool {
    for i in (0..8).rev() {
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
    }
    false // equal
}

/// `a >= b` for 256-bit values.
#[inline]
fn ge(a: &Scalar, b: &Scalar) -> bool {
    !scalar_lt(a, b)
}

/// Subtract without borrowing (assumes a >= b). Public for cross-module use.
pub fn scalar_sub_no_borrow(a: &Scalar, b: &Scalar) -> Scalar {
    sub_raw(a, b).0
}

/// Reduce a value already known to be `< 2·N` into `[0, N)` (one conditional
/// subtraction).
#[inline]
fn cond_sub_n(x: Scalar, carry: u32) -> Scalar {
    // `x + carry·2^256` is `< 2·N` for our callers (sums of two reduced scalars,
    // and N > 2^247 so a carry implies the true value exceeds N). Subtract N if
    // the 257-bit value is >= N.
    if carry == 1 || ge(&x, &ORDER) {
        sub_raw(&x, &ORDER).0
    } else {
        x
    }
}

/// Add two scalars mod ORDER. Inputs must already be reduced (`< N`).
pub fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
    let (sum, carry) = add_raw(a, b);
    cond_sub_n(sum, carry)
}

/// `2·a mod ORDER`. Input must be reduced.
#[inline]
fn double_mod(a: &Scalar) -> Scalar {
    scalar_add(a, a)
}

/// Subtract two scalars mod ORDER (wraps around). Inputs must be reduced.
pub fn scalar_sub(a: &Scalar, b: &Scalar) -> Scalar {
    if ge(a, b) {
        sub_raw(a, b).0
    } else {
        // a - b + N  (= a + (N - b), with a < b < N so the result is in [0, N))
        let (diff, _) = sub_raw(b, a); // b - a, in (0, N)
        sub_raw(&ORDER, &diff).0 // N - (b - a)
    }
}

/// Multiply two scalars mod ORDER via left-to-right double-and-add.
///
/// `a·b mod N = Σ_i b_i · (2^i · a) mod N`, accumulated MSB→LSB:
/// `acc ← 2·acc (mod N); if bit set: acc ← acc + a (mod N)`. Inputs must be
/// reduced (`< N`); every intermediate stays reduced, so this is exact.
pub fn scalar_mul_mod(a: &Scalar, b: &Scalar) -> Scalar {
    let a_red = if ge(a, &ORDER) { reduce_mod_n(a) } else { *a };
    let b_red = if ge(b, &ORDER) { reduce_mod_n(b) } else { *b };
    let mut acc = [0u32; 8];
    for limb in (0..8).rev() {
        for bit in (0..32).rev() {
            acc = double_mod(&acc);
            if (b_red[limb] >> bit) & 1 == 1 {
                acc = scalar_add(&acc, &a_red);
            }
        }
    }
    acc
}

/// Reduce an arbitrary 256-bit value mod ORDER (`N`), bit-by-bit MSB→LSB.
///
/// `x mod N = Σ_i x_i · 2^i mod N`, built by `acc ← 2·acc (+1 if bit) (mod N)`.
/// Used to map hash/byte outputs (which can be any 256-bit value) into `[0, N)`.
pub fn reduce_mod_n(x: &Scalar) -> Scalar {
    let one: Scalar = {
        let mut o = [0u32; 8];
        o[0] = 1;
        o
    };
    let mut acc = [0u32; 8];
    for limb in (0..8).rev() {
        for bit in (0..32).rev() {
            acc = double_mod(&acc);
            if (x[limb] >> bit) & 1 == 1 {
                acc = scalar_add(&acc, &one);
            }
        }
    }
    acc
}

/// Convert 32 bytes (little-endian) to a Scalar, reduced mod ORDER.
pub fn scalar_from_bytes(bytes: &[u8; 32]) -> Scalar {
    let mut limbs = [0u32; 8];
    for i in 0..8 {
        limbs[i] = u32::from_le_bytes([
            bytes[i * 4],
            bytes[i * 4 + 1],
            bytes[i * 4 + 2],
            bytes[i * 4 + 3],
        ]);
    }
    reduce_mod_n(&limbs)
}

/// Convert a Scalar to 32 bytes (little-endian).
pub fn scalar_to_bytes(s: &Scalar) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for i in 0..8 {
        let b = s[i].to_le_bytes();
        bytes[i * 4..i * 4 + 4].copy_from_slice(&b);
    }
    bytes
}

/// Check if a scalar is zero.
pub fn scalar_is_zero(s: &Scalar) -> bool {
    s.iter().all(|&x| x == 0)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_is_on_curve() {
        assert!(GENERATOR.is_on_curve());
    }

    #[test]
    fn infinity_is_on_curve() {
        assert!(CurvePoint::INFINITY.is_on_curve());
    }

    #[test]
    fn add_infinity_identity() {
        let p = GENERATOR;
        assert_eq!(p.add(&CurvePoint::INFINITY), p);
        assert_eq!(CurvePoint::INFINITY.add(&p), p);
    }

    #[test]
    fn point_plus_negation_is_infinity() {
        let p = GENERATOR;
        let neg_p = p.negate();
        assert_eq!(p.add(&neg_p), CurvePoint::INFINITY);
    }

    #[test]
    fn double_is_on_curve() {
        let p2 = GENERATOR.double();
        assert!(p2.is_on_curve());
    }

    #[test]
    fn add_equals_double_for_same_point() {
        let p = GENERATOR;
        assert_eq!(p.add(&p), p.double());
    }

    #[test]
    fn scalar_mul_small_consistency() {
        let g = GENERATOR;
        let g2 = g.double();
        let g3 = g2.add(&g);
        let g4 = g3.add(&g);

        assert_eq!(g.scalar_mul_small(1), g);
        assert_eq!(g.scalar_mul_small(2), g2);
        assert_eq!(g.scalar_mul_small(3), g3);
        assert_eq!(g.scalar_mul_small(4), g4);
    }

    #[test]
    fn scalar_mul_zero_is_infinity() {
        assert_eq!(GENERATOR.scalar_mul_small(0), CurvePoint::INFINITY);
    }

    #[test]
    fn point_addition_associativity() {
        let g = GENERATOR;
        let g2 = g.double();
        let g3 = g2.add(&g);

        // (G + G) + G == G + (G + G)
        let lhs = g.add(&g).add(&g);
        let rhs = g.add(&g.add(&g));
        assert_eq!(lhs, rhs);
        assert_eq!(lhs, g3);
    }

    #[test]
    fn scalar_mul_points_on_curve() {
        let g = GENERATOR;
        for i in 1..20 {
            let p = g.scalar_mul_small(i);
            assert!(p.is_on_curve(), "{}*G is not on curve", i);
        }
    }

    #[test]
    fn scalar_add_mod_order() {
        let a: Scalar = [1, 0, 0, 0, 0, 0, 0, 0];
        let b: Scalar = [2, 0, 0, 0, 0, 0, 0, 0];
        let c = scalar_add(&a, &b);
        assert_eq!(c, [3, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn scalar_sub_mod_order() {
        let a: Scalar = [5, 0, 0, 0, 0, 0, 0, 0];
        let b: Scalar = [3, 0, 0, 0, 0, 0, 0, 0];
        let c = scalar_sub(&a, &b);
        assert_eq!(c, [2, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn scalar_sub_wraparound() {
        // 0 - 1 mod ORDER = ORDER - 1
        let a: Scalar = [0; 8];
        let b: Scalar = [1, 0, 0, 0, 0, 0, 0, 0];
        let c = scalar_sub(&a, &b);
        let expected = scalar_sub_no_borrow(&ORDER, &b);
        assert_eq!(c, expected);
    }

    #[test]
    fn scalar_mul_mod_small() {
        let a: Scalar = [7, 0, 0, 0, 0, 0, 0, 0];
        let b: Scalar = [11, 0, 0, 0, 0, 0, 0, 0];
        let c = scalar_mul_mod(&a, &b);
        assert_eq!(c, [77, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn scalar_from_bytes_reduces_mod_order() {
        let bytes = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 0,
        ];
        let s = scalar_from_bytes(&bytes);
        // Result must be a reduced scalar (< ORDER); it now spans all 8 limbs.
        assert!(scalar_lt(&s, &ORDER));
        // A small scalar round-trips through bytes unchanged.
        let small_bytes = scalar_to_bytes(&[42, 0, 0, 0, 0, 0, 0, 0]);
        let s2 = scalar_from_bytes(&small_bytes);
        assert_eq!(s2, [42, 0, 0, 0, 0, 0, 0, 0]);
    }

    // ---- Full-width bigint scalar arithmetic (mod the 248-bit prime N) ----

    /// A deterministic full-width (multi-limb) reduced scalar generator.
    fn rand_scalar(seed: u64) -> Scalar {
        let mut s = seed
            .wrapping_mul(0x9E3779B97F4A7C15)
            .wrapping_add(0xD1B54A32D192ED03);
        let mut limbs = [0u32; 8];
        for l in limbs.iter_mut() {
            s ^= s >> 12;
            s ^= s << 25;
            s ^= s >> 27;
            *l = (s.wrapping_mul(0x2545F4914F6CDD1D) >> 32) as u32;
        }
        reduce_mod_n(&limbs)
    }

    #[test]
    fn order_is_248_bit() {
        // ORDER occupies the high limb (value ~2^248), i.e. it is genuinely
        // multi-limb — not the old single-limb placeholder.
        assert_ne!(ORDER[7], 0, "ORDER must be a full ~248-bit value");
        // 247 < log2(N) <= 248.
        let hi = ORDER[7];
        assert_eq!(32 - hi.leading_zeros() + 7 * 32, 248);
    }

    /// DECIMAL PIN — the `ORDER` limbs are the exact `N` the module doc quotes
    /// (`schnorr_curve.rs:117`). The 8 little-endian u32 limbs are hand-authored;
    /// a transcription slip in any limb yields a *different* group order while
    /// every structural test (`generator_has_order_n`, primality below) would
    /// still pass against the wrong N. This nails the limbs to the documented
    /// decimal, base-2^32 reconstructed here so the assertion carries its own
    /// ground truth.
    #[test]
    fn order_limbs_equal_documented_decimal() {
        // N = 269903886087112502248563194479599378757044855200285447932848137338699712099
        // reconstructed as Σ limb_i · 2^(32 i) using u128 accumulation over the
        // decimal digits (schoolbook: value = value*10 + digit).
        const DECIMAL: &str =
            "269903886087112502248563194479599378757044855200285447932848137338699712099";
        // Reconstruct the limbs from the decimal by repeated division by 2^32.
        let mut digits: Vec<u64> = DECIMAL.bytes().map(|b| (b - b'0') as u64).collect();
        let mut got = [0u32; 8];
        for slot in got.iter_mut() {
            // Long division of the big-decimal by 2^32: quotient digits + remainder.
            // The remainder (< 2^32) is this little-endian limb.
            let mut rem: u64 = 0;
            let mut quotient = Vec::with_capacity(digits.len());
            for &d in &digits {
                let cur = rem * 10 + d;
                quotient.push(cur >> 32);
                rem = cur & 0xFFFF_FFFF;
            }
            // strip leading zeros of the quotient before the next round.
            let first_nz = quotient
                .iter()
                .position(|&x| x != 0)
                .unwrap_or(quotient.len());
            digits = quotient[first_nz..].to_vec();
            *slot = rem as u32;
        }
        assert_eq!(
            got, ORDER,
            "ORDER limbs drifted from the documented decimal N — a limb transcription error \
             would silently change the group order"
        );
        assert!(
            digits.is_empty(),
            "decimal exceeded 8 limbs — N does not fit the ORDER shape"
        );
    }

    /// PRIMALITY GATE — the module doc's central assumption is `N` PRIME with
    /// cofactor 1 (`schnorr_curve.rs:19-24`): "every non-identity point generates
    /// the full group". That claim is load-bearing for security AND for
    /// `generator_cofactor_is_one`'s inference (order divides prime N, is not 1,
    /// therefore equals N). But primality was asserted only in PROSE (a PARI
    /// `isprime(N)` run recorded in a comment) — nothing bit if `N` were composite.
    /// If `N = a·b`, the generator could have order `a`, a proper factor; `N·G = O`
    /// would STILL hold (a | N), so `generator_has_order_n` passes on a broken order
    /// and the cofactor-1 argument silently collapses along with the DL hardness the
    /// whole curve rests on. This is precisely the shape of the retired bug: the old
    /// base-field-embedded order was the composite `2013191319 = 3·331·2027383`
    /// (module header line 30).
    ///
    /// We rig a **Miller–Rabin** strong-probable-prime test over an INDEPENDENT
    /// modulus-parameterised bigint (not `scalar_mul_mod`, which is hard-wired to
    /// `ORDER`) — independence is deliberate: a bug in the deployed scalar
    /// arithmetic then cannot mask a composite `ORDER`. Miller–Rabin, not Fermat:
    /// a Fermat base-2 witness is blind to Carmichael numbers (`2^560 ≡ 1 mod 561`;
    /// verified 2026-07-16), and "the constant is a Carmichael number" is exactly
    /// the substitution a Fermat gate would wave through.
    ///
    /// This is a *witness*, not a proof: MR with fixed bases is a strong-probable-
    /// prime test (error ≤ 4^-k for random bases). It is sufficient for the
    /// assumption it rigs — that the pinned limbs never DRIFT to a composite — and
    /// the primality proof itself remains the Lean/PARI job.
    #[test]
    fn order_is_prime_miller_rabin() {
        assert!(
            miller_rabin_probably_prime(&ORDER),
            "the pinned ORDER is COMPOSITE (Miller-Rabin). The prime-order / cofactor-1 \
             assumption underpinning generator_cofactor_is_one — and the DL hardness of the \
             whole curve — is FALSE for this N."
        );
    }

    /// NON-VACUITY CONTROL — *proof the primality gate can FAIL.*
    ///
    /// A gate that never goes red is decoration. This points the SAME routine at
    /// known composites and requires rejection — most pointedly `2013191319`, the
    /// actual composite order of the retired base-field curve the module header
    /// records as "trivially broken": the exact regression the gate exists to catch.
    /// The Carmichael numbers are the sharp ones — they PASS a Fermat base-2 test,
    /// so their rejection here is what proves the gate is Miller-Rabin-strong and
    /// not merely Fermat-weak.
    #[test]
    fn primality_gate_is_non_vacuous_it_rejects_composites() {
        let small = |v: u32| {
            let mut s = [0u32; 8];
            s[0] = v;
            s
        };

        // (a) It ACCEPTS known primes — else it rejects everything and its verdict on
        //     ORDER carries no information.
        assert!(
            miller_rabin_probably_prime(&small(crate::field::BABYBEAR_P)),
            "must ACCEPT the known prime BABYBEAR_P (2^31 - 2^27 + 1)"
        );
        for prime in [3u32, 5, 97, 65537, 2027383] {
            assert!(
                miller_rabin_probably_prime(&small(prime)),
                "must ACCEPT the known prime {prime}"
            );
        }

        // (b) THE TOOTH: it REJECTS the retired composite curve order and its factors'
        //     products — the historical regression, and the Carmichael numbers that a
        //     Fermat witness would wave straight through.
        for (composite, why) in [
            (
                2013191319u32,
                "the RETIRED composite curve order 3*331*2027383 (module header:30)",
            ),
            (671063773, "331*2027383"),
            (561, "Carmichael 3*11*17 — PASSES a Fermat base-2 test"),
            (1105, "Carmichael 5*13*17 — PASSES a Fermat base-2 test"),
            (1729, "Carmichael 7*13*19 — PASSES a Fermat base-2 test"),
            (2465, "Carmichael 5*17*29 — PASSES a Fermat base-2 test"),
        ] {
            assert!(
                !miller_rabin_probably_prime(&small(composite)),
                "Miller-Rabin FAILED to reject {composite} ({why}). The primality gate cannot \
                 detect a composite ORDER and is decoration."
            );
        }
    }

    /// DIFFERENTIAL — the independent modulus-parameterised `mul_mod_m` used by the
    /// primality gate must agree with the DEPLOYED `scalar_mul_mod` on the `ORDER`
    /// modulus. Two implementations written from different shapes agreeing on random
    /// inputs is real evidence about the deployed scalar arithmetic that carries every
    /// Schnorr response `s = k - e*sk`.
    #[test]
    fn independent_mul_mod_agrees_with_deployed_scalar_mul_mod() {
        for s in 0u64..60 {
            let a = rand_scalar(s);
            let b = rand_scalar(s ^ 0x5EED);
            assert_eq!(
                mul_mod_m(&a, &b, &ORDER),
                scalar_mul_mod(&a, &b),
                "independent mul_mod_m disagrees with deployed scalar_mul_mod at seed {s}"
            );
        }
    }

    // ---- Independent (modulus-parameterised) bigint arithmetic backing the
    // ---- primality gate. Deliberately NOT built on `scalar_mul_mod` (which is
    // ---- hard-wired to ORDER) so a bug there cannot mask a composite ORDER.

    fn sub_m(a: &Scalar, m: &Scalar) -> Scalar {
        let mut d = [0u32; 8];
        let mut borrow = 0i64;
        for i in 0..8 {
            let t = a[i] as i64 - m[i] as i64 - borrow;
            if t < 0 {
                d[i] = (t + (1i64 << 32)) as u32;
                borrow = 1;
            } else {
                d[i] = t as u32;
                borrow = 0;
            }
        }
        d
    }

    /// `(a + b) mod m` for `a, b < m`. `m <= 2^248` so `a + b < 2^249` — no 8-limb overflow.
    fn add_mod_m(a: &Scalar, b: &Scalar, m: &Scalar) -> Scalar {
        let mut r = [0u32; 8];
        let mut carry = 0u64;
        for i in 0..8 {
            let s = a[i] as u64 + b[i] as u64 + carry;
            r[i] = s as u32;
            carry = s >> 32;
        }
        if !scalar_lt(&r, m) { sub_m(&r, m) } else { r }
    }

    /// `(a * b) mod m` via MSB->LSB double-and-add (no wide intermediate needed).
    fn mul_mod_m(a: &Scalar, b: &Scalar, m: &Scalar) -> Scalar {
        let mut acc = [0u32; 8];
        for limb in (0..8).rev() {
            for bit in (0..32).rev() {
                let dbl = add_mod_m(&acc, &acc, m);
                acc = dbl;
                if (b[limb] >> bit) & 1 == 1 {
                    acc = add_mod_m(&acc, a, m);
                }
            }
        }
        acc
    }

    /// `base^exp mod m` via MSB->LSB square-and-multiply.
    fn pow_mod_m(base: &Scalar, exp: &Scalar, m: &Scalar) -> Scalar {
        let mut acc = {
            let mut o = [0u32; 8];
            o[0] = 1;
            o
        };
        for limb in (0..8).rev() {
            for bit in (0..32).rev() {
                acc = mul_mod_m(&acc, &acc.clone(), m);
                if (exp[limb] >> bit) & 1 == 1 {
                    acc = mul_mod_m(&acc, base, m);
                }
            }
        }
        acc
    }

    fn shr1(a: &Scalar) -> Scalar {
        let mut r = [0u32; 8];
        for i in 0..8 {
            r[i] = a[i] >> 1;
            if i + 1 < 8 {
                r[i] |= a[i + 1] << 31;
            }
        }
        r
    }

    fn is_zero_s(a: &Scalar) -> bool {
        a.iter().all(|&l| l == 0)
    }

    /// Miller-Rabin strong-probable-prime test with fixed small bases.
    fn miller_rabin_probably_prime(n: &Scalar) -> bool {
        let one = {
            let mut o = [0u32; 8];
            o[0] = 1;
            o
        };
        let two = {
            let mut t = [0u32; 8];
            t[0] = 2;
            t
        };
        // n < 2 => not prime; n == 2 => prime; n even => composite.
        if scalar_lt(n, &two) {
            return false;
        }
        if *n == two {
            return true;
        }
        if n[0] & 1 == 0 {
            return false;
        }

        let n_minus_1 = sub_m(n, &one);
        // n - 1 = 2^s * d with d odd.
        let mut d = n_minus_1;
        let mut s = 0u32;
        while d[0] & 1 == 0 && !is_zero_s(&d) {
            d = shr1(&d);
            s += 1;
        }

        'bases: for b in [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
            let mut base = [0u32; 8];
            base[0] = b;
            // Skip bases >= n (only reachable for the tiny controls).
            if !scalar_lt(&base, n) {
                continue;
            }
            let mut x = pow_mod_m(&base, &d, n);
            if x == one || x == n_minus_1 {
                continue;
            }
            for _ in 1..s {
                x = mul_mod_m(&x, &x.clone(), n);
                if x == n_minus_1 {
                    continue 'bases;
                }
            }
            return false; // witness to compositeness
        }
        true
    }

    #[test]
    fn add_sub_are_inverse_full_width() {
        for s in 0u64..200 {
            let a = rand_scalar(s);
            let b = rand_scalar(s ^ 0xABCD);
            // (a + b) - b == a, all reduced mod N.
            assert!(scalar_lt(&a, &ORDER) && scalar_lt(&b, &ORDER));
            let sum = scalar_add(&a, &b);
            assert!(scalar_lt(&sum, &ORDER), "sum not reduced");
            assert_eq!(scalar_sub(&sum, &b), a, "add/sub mismatch at {s}");
        }
    }

    #[test]
    fn sub_wraparound_full_width() {
        // 0 - 1 ≡ N - 1.
        let zero = [0u32; 8];
        let one = {
            let mut o = [0u32; 8];
            o[0] = 1;
            o
        };
        let n_minus_1 = scalar_sub_no_borrow(&ORDER, &one);
        assert_eq!(scalar_sub(&zero, &one), n_minus_1);
        // (N-1) + 1 ≡ 0.
        assert_eq!(scalar_add(&n_minus_1, &one), zero);
    }

    #[test]
    fn mul_mod_matches_repeated_add() {
        // a * k (small k) by repeated modular addition equals scalar_mul_mod.
        for s in 0u64..40 {
            let a = rand_scalar(s);
            let k = (s % 17) + 1;
            let mut acc = [0u32; 8];
            for _ in 0..k {
                acc = scalar_add(&acc, &a);
            }
            let mut kbig = [0u32; 8];
            kbig[0] = k as u32;
            assert_eq!(scalar_mul_mod(&a, &kbig), acc, "mul!=repeated-add at {s}");
        }
    }

    #[test]
    fn mul_mod_commutes_and_distributes() {
        for s in 0u64..60 {
            let a = rand_scalar(s);
            let b = rand_scalar(s.wrapping_add(1));
            let c = rand_scalar(s.wrapping_add(2));
            // commutativity
            assert_eq!(scalar_mul_mod(&a, &b), scalar_mul_mod(&b, &a));
            // distributivity: a*(b+c) == a*b + a*c   (mod N)
            let lhs = scalar_mul_mod(&a, &scalar_add(&b, &c));
            let rhs = scalar_add(&scalar_mul_mod(&a, &b), &scalar_mul_mod(&a, &c));
            assert_eq!(lhs, rhs, "distributivity failed at {s}");
        }
    }

    #[test]
    fn mul_by_one_and_zero() {
        let one = {
            let mut o = [0u32; 8];
            o[0] = 1;
            o
        };
        for s in 0u64..30 {
            let a = rand_scalar(s);
            assert_eq!(scalar_mul_mod(&a, &one), a);
            assert_eq!(scalar_mul_mod(&a, &[0u32; 8]), [0u32; 8]);
        }
    }

    // ---------------- THE PRIME-ORDER GENERATOR PROOF ----------------

    /// `N · G == O` (the identity): the generator's order divides N. Combined
    /// with `N` prime and `G ≠ O`, this pins `ord(G) = N` exactly.
    #[test]
    fn generator_has_order_n() {
        let n_g = GENERATOR.scalar_mul(&ORDER);
        assert!(
            n_g.is_infinity,
            "N·G must be the point at infinity (G's order divides the prime N)"
        );
    }

    /// A small-cofactor / large-order check: `2·G ≠ O` (and a handful of small
    /// multiples are non-identity), so `ord(G)` is not a tiny factor. Since the
    /// full order divides the *prime* N and is not 1, it must equal N — i.e. the
    /// cofactor is 1 and G generates the whole group.
    #[test]
    fn generator_cofactor_is_one() {
        // `GENERATOR` is a constant, so "G is not the point at infinity" is a BUILD obligation —
        // and a decisive one: at `G = O` every multiple below is `O` too, so the loop's own
        // refusals would all fire for the wrong reason and this test would still be measuring
        // something. It stood as a runtime `assert!`.
        const _: () = assert!(!GENERATOR.is_infinity, "G must not be O");
        // No small multiple collapses to O.
        for k in 2u32..50 {
            let kp = GENERATOR.scalar_mul_small(k);
            assert!(
                !kp.is_infinity,
                "{k}·G hit infinity — G would have tiny order, contradicting prime N"
            );
            assert!(kp.is_on_curve(), "{k}·G left the curve");
        }
        // (N-1)·G == -G, hence (N-1)·G + G == O — a second confirmation that the
        // order is exactly N.
        let one = {
            let mut o = [0u32; 8];
            o[0] = 1;
            o
        };
        let n_minus_1 = scalar_sub_no_borrow(&ORDER, &one);
        let nm1_g = GENERATOR.scalar_mul(&n_minus_1);
        assert_eq!(nm1_g, GENERATOR.negate(), "(N-1)·G must equal -G");
        assert!(nm1_g.add(&GENERATOR).is_infinity);
    }

    /// Scalar multiplication respects modular reduction: `(s mod N)·G == s·G`
    /// for an unreduced `s`, because `N·G = O`. Concretely `(N + 5)·G == 5·G`.
    #[test]
    fn scalar_mul_respects_order() {
        let five = {
            let mut f = [0u32; 8];
            f[0] = 5;
            f
        };
        let (n_plus_5, _) = add_raw(&ORDER, &five);
        assert_eq!(
            GENERATOR.scalar_mul(&n_plus_5),
            GENERATOR.scalar_mul(&five),
            "(N+5)·G must equal 5·G since N·G = O"
        );
    }
}
