//! Elliptic curve over BabyBear^8 for Schnorr signatures.
//!
//! Defines a short Weierstrass curve y^2 = x^3 + ax + b over BabyBear^8,
//! with affine point arithmetic suitable for STARK verification.
//!
//! # Curve Selection
//!
//! We use the j=0 family (a=0), giving y^2 = x^3 + b. This simplifies the
//! addition formula (no `a` term in doubling). The parameter `b` is chosen
//! so that the curve has a large prime-order subgroup.
//!
//! **IMPORTANT**: The curve parameters below are PLACEHOLDER values for
//! prototyping. For production use, a proper curve search (Schoof/SEA algorithm
//! or CM method) must be performed to find b such that #E(BabyBear^8) is prime
//! or has a large prime factor. The current b is chosen to make arithmetic work
//! correctly; the group order is not verified to be prime.
//!
//! # Security Target
//!
//! BabyBear^8 has field size ~2^248. An elliptic curve over this field provides
//! ~124-bit security against Pollard-rho attacks (sqrt(field size / 2)).
//!
//! # Point Representation
//!
//! Points are stored in affine coordinates (x, y) plus an `is_infinity` flag.
//! This is optimal for STARK verification where the "slope as witness" technique
//! allows the verifier to check point additions with degree-2 constraints.

use crate::babybear8::BabyBear8;
use crate::field::BabyBear;

// ============================================================================
// Curve Parameters (PLACEHOLDER — see module docs)
// ============================================================================

/// Curve parameter `a` (coefficient of x in y^2 = x^3 + ax + b).
/// We use a=0 (j=0 curve family) for simpler doubling formulas.
pub const CURVE_A: BabyBear8 = BabyBear8::ZERO;

/// Curve parameter `b` (constant term in y^2 = x^3 + ax + b).
/// PLACEHOLDER: b = 3 embedded in BabyBear^8.
/// A production deployment must verify #E(F_{p^8}) with this b has prime order.
pub const CURVE_B: BabyBear8 = BabyBear8([
    BabyBear(3),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
    BabyBear(0),
]);

/// Generator point for the curve.
///
/// PLACEHOLDER: We derive a generator by finding a point on y^2 = x^3 + 3.
/// For x = 1: y^2 = 1 + 3 = 4, y = 2. So (1, 2) is on the curve over BabyBear
/// (embedded in BabyBear^8).
///
/// In production, this must be a generator of the prime-order subgroup, found
/// during the curve parameter selection process.
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
        BabyBear(2),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
        BabyBear(0),
    ]),
    is_infinity: false,
};

/// Group order of the generator point.
///
/// For the prototype using base-field-embedded points (GENERATOR = (1, 2) on
/// y^2 = x^3 + 3 over BabyBear), the point order is 2013191319 = 3 * 331 * 2027383.
///
/// This was computed by finding the smallest n > 0 such that n*G = infinity,
/// using the Hasse bound to narrow the search range.
///
/// In production over BabyBear^8 with a proper extension-field generator,
/// the order would be ~2^248 and prime (found via Schoof/SEA point counting).
///
/// Stored as 8 little-endian u32 limbs.
pub const ORDER: [u32; 8] = [
    2013191319, // 0x78000897 — actual order of (1,2) on y^2=x^3+3/BabyBear
    0, 0, 0, 0, 0, 0, 0,
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
// Scalar Arithmetic (mod ORDER)
// ============================================================================

/// 8-limb big integer (little-endian u32 limbs) representing scalars mod ORDER.
pub type Scalar = [u32; 8];

/// Add two scalars mod ORDER.
///
/// Since ORDER fits in one u32 limb, both inputs should already be reduced
/// (i.e., only limb[0] is non-zero). But we handle the general case for safety.
pub fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
    let av = scalar_to_u64(a);
    let bv = scalar_to_u64(b);
    let order = ORDER[0] as u64;
    let sum = (av + bv) % order;
    let mut result = [0u32; 8];
    result[0] = sum as u32;
    result
}

/// Subtract two scalars mod ORDER (wraps around).
pub fn scalar_sub(a: &Scalar, b: &Scalar) -> Scalar {
    let av = scalar_to_u64(a);
    let bv = scalar_to_u64(b);
    let order = ORDER[0] as u64;
    let diff = if av >= bv { av - bv } else { av + order - bv };
    let mut result = [0u32; 8];
    result[0] = (diff % order) as u32;
    result
}

/// Subtract without borrowing (assumes a >= b). Public for cross-module use.
pub fn scalar_sub_no_borrow(a: &Scalar, b: &Scalar) -> Scalar {
    let mut result = [0u32; 8];
    let mut borrow: u64 = 0;
    for i in 0..8 {
        let diff = a[i] as u64 + (1u64 << 32) - b[i] as u64 - borrow;
        result[i] = diff as u32;
        borrow = 1 - (diff >> 32);
    }
    result
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

/// Multiply two scalars mod ORDER using u64 arithmetic.
///
/// Since ORDER currently fits in a single u32 (2013191319), we reduce each scalar
/// to u64 first, multiply, and reduce the result. This is efficient and correct.
///
/// For a production ~248-bit ORDER, this would need full bigint multiplication.
pub fn scalar_mul_mod(a: &Scalar, b: &Scalar) -> Scalar {
    let a_reduced = scalar_to_u64(a);
    let b_reduced = scalar_to_u64(b);
    // Use u128 to avoid overflow in multiplication
    let product = (a_reduced as u128 * b_reduced as u128) % (ORDER[0] as u128);
    let mut result = [0u32; 8];
    result[0] = product as u32;
    result
}

/// Reduce a multi-limb scalar to a u64 value mod ORDER[0].
///
/// Since ORDER fits in one u32 limb, we can reduce by processing limbs
/// using Horner's method: value = sum(limb[i] * 2^(32*i)) mod ORDER[0].
pub fn scalar_to_u64(s: &Scalar) -> u64 {
    let order = ORDER[0] as u64;
    let mut result: u64 = 0;
    let base_mod = (1u64 << 32) % order; // 2^32 mod ORDER
    let mut power = 1u64; // (2^32)^i mod ORDER

    for &limb in s.iter() {
        result = (result + (limb as u64 % order) * power) % order;
        power = (power * base_mod) % order;
    }
    result
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
    // Reduce the full 256-bit value mod ORDER using scalar_to_u64
    let reduced = scalar_to_u64(&limbs);
    let mut result = [0u32; 8];
    result[0] = reduced as u32;
    result
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
        // Result should be < ORDER (only in first limb)
        assert!(s[0] < ORDER[0]);
        for i in 1..8 {
            assert_eq!(s[i], 0);
        }
        // Converting a small scalar to bytes and back should roundtrip
        let small_bytes = scalar_to_bytes(&[42, 0, 0, 0, 0, 0, 0, 0]);
        let s2 = scalar_from_bytes(&small_bytes);
        assert_eq!(s2, [42, 0, 0, 0, 0, 0, 0, 0]);
    }
}
