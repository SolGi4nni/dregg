//! BabyBear^8 extension field arithmetic.
//!
//! Constructed as a tower: BabyBear^8 = BabyBear^4[y] / (y^2 - W)
//! where BabyBear^4 = BabyBear[x] / (x^4 - 11) and we use the same non-residue
//! W = 11 for the quadratic extension on top.
//!
//! An element of BabyBear^8 is stored as [a0, a1, a2, a3, a4, a5, a6, a7] where
//! the "low" half [a0..a3] forms the BabyBear^4 coefficient of 1, and the "high"
//! half [a4..a7] forms the BabyBear^4 coefficient of y.
//!
//! Multiplication uses the Karatsuba-like formula for F[y]/(y^2 - W):
//!   (A + B*y)(C + D*y) = (A*C + W*B*D) + (A*D + B*C)*y
//!
//! This gives us a field of size p^8 ~ 2^248, providing ~124-bit Pollard-rho security
//! for the discrete log problem on an elliptic curve defined over this field.

use crate::field::BabyBear;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// The non-residue used for both extension layers: x^4 - W and y^2 - W.
/// W = 11 is a non-residue in BabyBear and in BabyBear^4.
const W: BabyBear = BabyBear(11);

/// An element of BabyBear^8.
///
/// Stored as 8 BabyBear coefficients representing:
///   a[0] + a[1]*x + a[2]*x^2 + a[3]*x^3 + a[4]*y + a[5]*x*y + a[6]*x^2*y + a[7]*x^3*y
///
/// Equivalently, (a[0..4] as ExtElem) + (a[4..8] as ExtElem) * y
/// in the tower BabyBear^4[y] / (y^2 - 11).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BabyBear8(pub [BabyBear; 8]);

impl BabyBear8 {
    /// The zero element.
    pub const ZERO: Self = Self([BabyBear::ZERO; 8]);

    /// The multiplicative identity.
    pub const ONE: Self = Self([
        BabyBear::ONE,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);

    /// Embed a base field element.
    pub fn from_base(x: BabyBear) -> Self {
        let mut r = Self::ZERO;
        r.0[0] = x;
        r
    }

    /// Embed a u32 (reduced mod p).
    pub fn from_u32(val: u32) -> Self {
        Self::from_base(BabyBear::new(val))
    }

    /// Check if this element is zero.
    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|x| *x == BabyBear::ZERO)
    }

    /// Get the "low" BabyBear^4 half (coefficients of 1).
    fn low(&self) -> [BabyBear; 4] {
        [self.0[0], self.0[1], self.0[2], self.0[3]]
    }

    /// Get the "high" BabyBear^4 half (coefficients of y).
    fn high(&self) -> [BabyBear; 4] {
        [self.0[4], self.0[5], self.0[6], self.0[7]]
    }

    /// Construct from low and high halves.
    fn from_halves(low: [BabyBear; 4], high: [BabyBear; 4]) -> Self {
        Self([
            low[0], low[1], low[2], low[3], high[0], high[1], high[2], high[3],
        ])
    }

    /// Component-wise addition.
    pub fn add(&self, other: &Self) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = self.0[i] + other.0[i];
        }
        Self(r)
    }

    /// Component-wise subtraction.
    pub fn sub(&self, other: &Self) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = self.0[i] - other.0[i];
        }
        Self(r)
    }

    /// Negation.
    pub fn neg(&self) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = -self.0[i];
        }
        Self(r)
    }

    /// Multiply two BabyBear^4 elements (internal helper).
    /// Uses the formula for F[x]/(x^4 - W):
    ///   c0 = a0*b0 + W*(a1*b3 + a2*b2 + a3*b1)
    ///   c1 = a0*b1 + a1*b0 + W*(a2*b3 + a3*b2)
    ///   c2 = a0*b2 + a1*b1 + a2*b0 + W*(a3*b3)
    ///   c3 = a0*b3 + a1*b2 + a2*b1 + a3*b0
    fn mul4(a: &[BabyBear; 4], b: &[BabyBear; 4]) -> [BabyBear; 4] {
        let w = W;
        let c0 = a[0] * b[0] + w * (a[1] * b[3] + a[2] * b[2] + a[3] * b[1]);
        let c1 = a[0] * b[1] + a[1] * b[0] + w * (a[2] * b[3] + a[3] * b[2]);
        let c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + w * (a[3] * b[3]);
        let c3 = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];
        [c0, c1, c2, c3]
    }

    /// Add two BabyBear^4 elements (internal helper).
    fn add4(a: &[BabyBear; 4], b: &[BabyBear; 4]) -> [BabyBear; 4] {
        [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]]
    }

    /// Subtract two BabyBear^4 elements (internal helper).
    fn sub4(a: &[BabyBear; 4], b: &[BabyBear; 4]) -> [BabyBear; 4] {
        [a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]
    }

    /// Multiply a BabyBear^4 element by the non-residue W (scalar multiply by 11).
    fn mul4_by_w(a: &[BabyBear; 4]) -> [BabyBear; 4] {
        [a[0] * W, a[1] * W, a[2] * W, a[3] * W]
    }

    /// Extension field multiplication using the tower structure.
    ///
    /// (A + B*y)(C + D*y) = (A*C + W*B*D) + (A*D + B*C)*y
    ///
    /// where A, B, C, D are BabyBear^4 elements and W = 11.
    pub fn mul(&self, other: &Self) -> Self {
        let a = self.low();
        let b = self.high();
        let c = other.low();
        let d = other.high();

        let ac = Self::mul4(&a, &c);
        let bd = Self::mul4(&b, &d);
        let ad = Self::mul4(&a, &d);
        let bc = Self::mul4(&b, &c);

        let w_bd = Self::mul4_by_w(&bd);
        let low = Self::add4(&ac, &w_bd);
        let high = Self::add4(&ad, &bc);

        Self::from_halves(low, high)
    }

    /// Square this element (slightly optimized over generic mul).
    pub fn square(&self) -> Self {
        let a = self.low();
        let b = self.high();

        // (A + By)^2 = (A^2 + W*B^2) + 2AB*y
        let a2 = Self::mul4(&a, &a);
        let b2 = Self::mul4(&b, &b);
        let ab = Self::mul4(&a, &b);

        let w_b2 = Self::mul4_by_w(&b2);
        let low = Self::add4(&a2, &w_b2);
        let high = Self::add4(&ab, &ab); // 2*ab

        Self::from_halves(low, high)
    }

    /// Multiply by a base field scalar.
    pub fn scale(&self, s: BabyBear) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = self.0[i] * s;
        }
        Self(r)
    }

    /// Inverse of a BabyBear^4 element via Gaussian elimination.
    /// Returns None if the element is zero.
    fn inv4(a: &[BabyBear; 4]) -> Option<[BabyBear; 4]> {
        if a.iter().all(|x| *x == BabyBear::ZERO) {
            return None;
        }

        let w = W;
        // Build the 4x5 augmented matrix for the multiplication-by-a map.
        // The multiplication matrix for (a0+a1*x+a2*x^2+a3*x^3) in F[x]/(x^4-W):
        //  Row 0: [a0, W*a3, W*a2, W*a1 | 1]
        //  Row 1: [a1, a0,   W*a3, W*a2 | 0]
        //  Row 2: [a2, a1,   a0,   W*a3 | 0]
        //  Row 3: [a3, a2,   a1,   a0   | 0]
        let mut mat = [[BabyBear::ZERO; 5]; 4];
        mat[0] = [a[0], w * a[3], w * a[2], w * a[1], BabyBear::ONE];
        mat[1] = [a[1], a[0], w * a[3], w * a[2], BabyBear::ZERO];
        mat[2] = [a[2], a[1], a[0], w * a[3], BabyBear::ZERO];
        mat[3] = [a[3], a[2], a[1], a[0], BabyBear::ZERO];

        for c in 0..4 {
            let mut pivot = None;
            for row in c..4 {
                if mat[row][c] != BabyBear::ZERO {
                    pivot = Some(row);
                    break;
                }
            }
            let pivot = pivot?;
            if pivot != c {
                mat.swap(c, pivot);
            }
            let inv_pivot = mat[c][c].inverse()?;
            for j in 0..5 {
                mat[c][j] = mat[c][j] * inv_pivot;
            }
            for row in 0..4 {
                if row == c {
                    continue;
                }
                let factor = mat[row][c];
                for j in 0..5 {
                    mat[row][j] = mat[row][j] - factor * mat[c][j];
                }
            }
        }

        Some([mat[0][4], mat[1][4], mat[2][4], mat[3][4]])
    }

    /// Compute the multiplicative inverse of this element.
    ///
    /// Uses the tower structure: for z = A + B*y, z^{-1} = (A - B*y) / (A^2 - W*B^2)
    /// where (A^2 - W*B^2) is computed and inverted in BabyBear^4.
    pub fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let a = self.low();
        let b = self.high();

        // norm = A^2 - W*B^2 in BabyBear^4
        let a2 = Self::mul4(&a, &a);
        let b2 = Self::mul4(&b, &b);
        let w_b2 = Self::mul4_by_w(&b2);
        let norm = Self::sub4(&a2, &w_b2);

        // Invert the norm in BabyBear^4
        let norm_inv = Self::inv4(&norm)?;

        // z^{-1} = (A - B*y) * norm_inv = (A*norm_inv) + (-B*norm_inv)*y
        let low = Self::mul4(&a, &norm_inv);
        let neg_b = [
            BabyBear::ZERO - b[0],
            BabyBear::ZERO - b[1],
            BabyBear::ZERO - b[2],
            BabyBear::ZERO - b[3],
        ];
        let high = Self::mul4(&neg_b, &norm_inv);

        Some(Self::from_halves(low, high))
    }

    /// Exponentiation by a u32 exponent (square-and-multiply).
    pub fn pow_u32(&self, mut exp: u32) -> Self {
        let mut base = *self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                result = Self::mul(&result, &base);
            }
            base = base.square();
            exp >>= 1;
        }
        result
    }

    /// Exponentiation by a multi-limb exponent (8 limbs, little-endian u32s).
    pub fn pow_multi(&self, exp: &[u32; 8]) -> Self {
        let mut base = *self;
        let mut result = Self::ONE;
        for &limb in exp {
            let mut e = limb;
            for _ in 0..32 {
                if e & 1 == 1 {
                    result = Self::mul(&result, &base);
                }
                base = base.square();
                e >>= 1;
            }
        }
        result
    }
}

impl fmt::Debug for BabyBear8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BB8({}, {}, {}, {}, {}, {}, {}, {})",
            self.0[0].0,
            self.0[1].0,
            self.0[2].0,
            self.0[3].0,
            self.0[4].0,
            self.0[5].0,
            self.0[6].0,
            self.0[7].0
        )
    }
}

impl fmt::Display for BabyBear8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Default for BabyBear8 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl Add for BabyBear8 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self::add(&self, &rhs)
    }
}

impl Sub for BabyBear8 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self::sub(&self, &rhs)
    }
}

impl Mul for BabyBear8 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::mul(&self, &rhs)
    }
}

impl Neg for BabyBear8 {
    type Output = Self;
    fn neg(self) -> Self {
        Self::neg(&self)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_and_one() {
        let z = BabyBear8::ZERO;
        let o = BabyBear8::ONE;
        assert!(z.is_zero());
        assert!(!o.is_zero());
        assert_eq!(z + o, o);
        assert_eq!(o - o, z);
    }

    #[test]
    fn addition_commutativity() {
        let a = BabyBear8([
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::new(6),
            BabyBear::new(7),
            BabyBear::new(8),
        ]);
        let b = BabyBear8([
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(50),
            BabyBear::new(60),
            BabyBear::new(70),
            BabyBear::new(80),
        ]);
        assert_eq!(a + b, b + a);
    }

    #[test]
    fn multiplication_identity() {
        let a = BabyBear8([
            BabyBear::new(17),
            BabyBear::new(42),
            BabyBear::new(99),
            BabyBear::new(7),
            BabyBear::new(13),
            BabyBear::new(55),
            BabyBear::new(3),
            BabyBear::new(100),
        ]);
        assert_eq!(a * BabyBear8::ONE, a);
        assert_eq!(BabyBear8::ONE * a, a);
    }

    #[test]
    fn multiplication_by_zero() {
        let a = BabyBear8([
            BabyBear::new(17),
            BabyBear::new(42),
            BabyBear::new(99),
            BabyBear::new(7),
            BabyBear::new(13),
            BabyBear::new(55),
            BabyBear::new(3),
            BabyBear::new(100),
        ]);
        assert_eq!(a * BabyBear8::ZERO, BabyBear8::ZERO);
    }

    #[test]
    fn multiplication_associativity() {
        let a = BabyBear8([
            BabyBear::new(3),
            BabyBear::new(7),
            BabyBear::new(11),
            BabyBear::new(13),
            BabyBear::new(17),
            BabyBear::new(19),
            BabyBear::new(23),
            BabyBear::new(29),
        ]);
        let b = BabyBear8([
            BabyBear::new(31),
            BabyBear::new(37),
            BabyBear::new(41),
            BabyBear::new(43),
            BabyBear::new(47),
            BabyBear::new(53),
            BabyBear::new(59),
            BabyBear::new(61),
        ]);
        let c = BabyBear8([
            BabyBear::new(67),
            BabyBear::new(71),
            BabyBear::new(73),
            BabyBear::new(79),
            BabyBear::new(83),
            BabyBear::new(89),
            BabyBear::new(97),
            BabyBear::new(101),
        ]);
        let ab_c = (a * b) * c;
        let a_bc = a * (b * c);
        assert_eq!(ab_c, a_bc);
    }

    #[test]
    fn multiplication_distributivity() {
        let a = BabyBear8([
            BabyBear::new(5),
            BabyBear::new(10),
            BabyBear::new(15),
            BabyBear::new(20),
            BabyBear::new(25),
            BabyBear::new(30),
            BabyBear::new(35),
            BabyBear::new(40),
        ]);
        let b = BabyBear8([
            BabyBear::new(2),
            BabyBear::new(4),
            BabyBear::new(6),
            BabyBear::new(8),
            BabyBear::new(10),
            BabyBear::new(12),
            BabyBear::new(14),
            BabyBear::new(16),
        ]);
        let c = BabyBear8([
            BabyBear::new(1),
            BabyBear::new(3),
            BabyBear::new(5),
            BabyBear::new(7),
            BabyBear::new(9),
            BabyBear::new(11),
            BabyBear::new(13),
            BabyBear::new(15),
        ]);
        // a*(b+c) == a*b + a*c
        let lhs = a * (b + c);
        let rhs = a * b + a * c;
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn inverse_correctness() {
        let a = BabyBear8([
            BabyBear::new(42),
            BabyBear::new(17),
            BabyBear::new(99),
            BabyBear::new(3),
            BabyBear::new(7),
            BabyBear::new(55),
            BabyBear::new(200),
            BabyBear::new(13),
        ]);
        let inv = a.inverse().unwrap();
        let product = a * inv;
        assert_eq!(product, BabyBear8::ONE);
    }

    #[test]
    fn inverse_of_one_is_one() {
        let inv = BabyBear8::ONE.inverse().unwrap();
        assert_eq!(inv, BabyBear8::ONE);
    }

    #[test]
    fn zero_has_no_inverse() {
        assert!(BabyBear8::ZERO.inverse().is_none());
    }

    #[test]
    fn square_equals_mul_self() {
        let a = BabyBear8([
            BabyBear::new(11),
            BabyBear::new(22),
            BabyBear::new(33),
            BabyBear::new(44),
            BabyBear::new(55),
            BabyBear::new(66),
            BabyBear::new(77),
            BabyBear::new(88),
        ]);
        assert_eq!(a.square(), a * a);
    }

    #[test]
    fn base_field_embed() {
        let x = BabyBear::new(42);
        let ext = BabyBear8::from_base(x);
        assert_eq!(ext.0[0], x);
        for i in 1..8 {
            assert_eq!(ext.0[i], BabyBear::ZERO);
        }
    }

    #[test]
    fn base_field_mul_commutes_with_embed() {
        let a = BabyBear::new(7);
        let b = BabyBear::new(13);
        let prod_base = a * b;
        let prod_ext = BabyBear8::from_base(a) * BabyBear8::from_base(b);
        assert_eq!(prod_ext, BabyBear8::from_base(prod_base));
    }

    #[test]
    fn negation_identity() {
        let a = BabyBear8([
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::new(6),
            BabyBear::new(7),
            BabyBear::new(8),
        ]);
        let neg_a = -a;
        assert_eq!(a + neg_a, BabyBear8::ZERO);
    }

    #[test]
    fn pow_u32_basic() {
        let a = BabyBear8::from_base(BabyBear::new(3));
        let a_cubed = a.pow_u32(3);
        assert_eq!(a_cubed, BabyBear8::from_base(BabyBear::new(27)));
    }

    #[test]
    fn pow_u32_zero() {
        let a = BabyBear8([
            BabyBear::new(42),
            BabyBear::new(17),
            BabyBear::new(99),
            BabyBear::new(3),
            BabyBear::new(7),
            BabyBear::new(55),
            BabyBear::new(200),
            BabyBear::new(13),
        ]);
        assert_eq!(a.pow_u32(0), BabyBear8::ONE);
    }
}
