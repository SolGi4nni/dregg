//! BabyBear^8 extension field arithmetic.
//!
//! Constructed as the **simple (non-towered) field** `F_p[z] / (z^8 - 11)`,
//! where `p` is the BabyBear prime. `z^8 - 11` is irreducible over BabyBear
//! (verified: it factors as a single degree-8 irreducible), so the quotient is a
//! genuine field of size `p^8 ≈ 2^248`, giving ~124-bit Pollard-rho security for
//! the discrete log on an elliptic curve defined over it.
//!
//! # Why this construction (and not the old tower)
//!
//! An earlier version built `F_{p^8}` as a *tower*
//! `F_p[x]/(x^4 - 11)` then `F_{p^4}[y]/(y^2 - 11)`, **reusing the same
//! non-residue `11` for both layers**. That is not a field: in
//! `F_p[x]/(x^4 - 11)` the element `x^2` already satisfies `(x^2)^2 = 11`, so
//! `11` is a square there and `y^2 - 11 = (y - x^2)(y + x^2)` *factors* — the
//! quotient is the product ring `F_{p^4} × F_{p^4}` with zero divisors (e.g.
//! `A = y - x^2 ≠ 0` yet `A·(y + x^2) = 0`, and `A` has no inverse). No
//! base-field constant works as a top non-residue either: every `c ∈ F_p*` is a
//! square in `F_{p^4}`. The fix is to extend by a genuine degree-8 irreducible
//! over `F_p` directly; `z^8 - 11` is the minimal "same flavor" choice.
//!
//! # Representation
//!
//! An element is stored as the 8 BabyBear coefficients `[c0, c1, …, c7]` of the
//! polynomial
//!
//! ```text
//!   c0 + c1·z + c2·z^2 + c3·z^3 + c4·z^4 + c5·z^5 + c6·z^6 + c7·z^7   (mod z^8 - 11)
//! ```
//!
//! i.e. `self.0[i]` is the coefficient of `z^i` (the natural power basis). This
//! is the same field as the towered presentation under the basis map `z = y`,
//! `x = z^2` (so the old `[1, x, x^2, x^3, y, xy, x^2y, x^3y]` coordinates are a
//! permutation of these power-basis coordinates); since every consumer treats an
//! element's coordinates as opaque field data, the power basis is used directly.
//!
//! # Arithmetic
//!
//! Multiplication is polynomial multiplication reduced modulo `z^8 - 11`, using
//! `z^8 = 11` (so a degree-`k` term with `k ≥ 8` folds back as `11·z^{k-8}`).
//! Inversion solves the 8×8 "multiply-by-self" linear system over BabyBear by
//! Gaussian elimination (`a · a^{-1} = 1`).

use crate::field::BabyBear;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// The non-residue of the defining polynomial `z^8 - W`. `W = 11` makes
/// `z^8 - 11` irreducible over BabyBear (a genuine degree-8 field extension).
const W: BabyBear = BabyBear(11);

/// An element of BabyBear^8, stored as the 8 power-basis coefficients
/// `[c0, …, c7]` of `c0 + c1·z + … + c7·z^7` in `F_p[z]/(z^8 - 11)`.
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

    /// Embed a base field element (the constant polynomial).
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

    /// Component-wise addition.
    // crypto index loops kept verbatim
    #[allow(clippy::needless_range_loop)]
    pub fn add(&self, other: &Self) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = self.0[i] + other.0[i];
        }
        Self(r)
    }

    /// Component-wise subtraction.
    // crypto index loops kept verbatim
    #[allow(clippy::needless_range_loop)]
    pub fn sub(&self, other: &Self) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = self.0[i] - other.0[i];
        }
        Self(r)
    }

    /// Negation.
    // crypto index loops kept verbatim
    #[allow(clippy::needless_range_loop)]
    pub fn neg(&self) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = -self.0[i];
        }
        Self(r)
    }

    /// Extension field multiplication: polynomial product reduced mod `z^8 - W`.
    ///
    /// The raw product `a·b` has coefficients of degree `0..=14`; using
    /// `z^8 = W` (so `z^{8+m} = W·z^m`), each high coefficient `conv[m+8]` folds
    /// back additively into `conv[m]` scaled by `W`.
    pub fn mul(&self, other: &Self) -> Self {
        let a = &self.0;
        let b = &other.0;

        // Schoolbook convolution. Degrees run 0..=14; index 15 stays zero so the
        // reduction below can read `conv[m + 8]` for all m in 0..8 uniformly.
        let mut conv = [BabyBear::ZERO; 16];
        for i in 0..8 {
            if a[i] == BabyBear::ZERO {
                continue;
            }
            for j in 0..8 {
                conv[i + j] += a[i] * b[j];
            }
        }

        // Reduce modulo z^8 - W:  result[m] = conv[m] + W·conv[m+8].
        let mut r = [BabyBear::ZERO; 8];
        for m in 0..8 {
            r[m] = conv[m] + W * conv[m + 8];
        }
        Self(r)
    }

    /// Square this element (via the generic multiply; the reduction dominates).
    pub fn square(&self) -> Self {
        self.mul(self)
    }

    /// Multiply by a base field scalar.
    // crypto index loops kept verbatim
    #[allow(clippy::needless_range_loop)]
    pub fn scale(&self, s: BabyBear) -> Self {
        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = self.0[i] * s;
        }
        Self(r)
    }

    /// Compute the multiplicative inverse of this element.
    ///
    /// Solves `self · x = 1` for `x` by Gaussian elimination over BabyBear on the
    /// 8×8 matrix `M` of the "multiply-by-self" map, where column `j` is the
    /// reduced coefficient vector of `self · z^j`. Returns `None` for zero.
    // crypto index loops kept verbatim
    #[allow(clippy::needless_range_loop)]
    pub fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let a = &self.0;

        // Build the augmented matrix [M | e0]. Column j of M is `a * z^j` reduced
        // mod z^8 - W: a_i contributes to row (i+j); if i+j >= 8 it wraps to row
        // (i+j-8) scaled by W.
        let mut mat = [[BabyBear::ZERO; 9]; 8];
        for j in 0..8 {
            for i in 0..8 {
                let deg = i + j;
                if deg < 8 {
                    mat[deg][j] += a[i];
                } else {
                    mat[deg - 8][j] += W * a[i];
                }
            }
        }
        // Right-hand side: the constant polynomial 1 (target a*x = 1).
        mat[0][8] = BabyBear::ONE;

        // Gauss–Jordan elimination.
        for c in 0..8 {
            // Find a nonzero pivot in column c at or below the diagonal.
            let mut pivot = None;
            for row in c..8 {
                if mat[row][c] != BabyBear::ZERO {
                    pivot = Some(row);
                    break;
                }
            }
            // A nonzero element always yields an invertible multiplication matrix
            // in a field; `?` is defensive (cannot fire for nonzero `self`).
            let pivot = pivot?;
            if pivot != c {
                mat.swap(c, pivot);
            }
            let inv_pivot = mat[c][c].inverse()?;
            for j in 0..9 {
                mat[c][j] *= inv_pivot;
            }
            for row in 0..8 {
                if row == c {
                    continue;
                }
                let factor = mat[row][c];
                if factor == BabyBear::ZERO {
                    continue;
                }
                for j in 0..9 {
                    mat[row][j] -= factor * mat[c][j];
                }
            }
        }

        let mut r = [BabyBear::ZERO; 8];
        for i in 0..8 {
            r[i] = mat[i][8];
        }
        Some(Self(r))
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
    use crate::field::BABYBEAR_P;

    /// A deterministic non-degenerate element generator for property tests.
    fn elem(seed: u64) -> BabyBear8 {
        let mut s = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
        let mut out = [BabyBear::ZERO; 8];
        for o in out.iter_mut() {
            s ^= s >> 12;
            s ^= s << 25;
            s ^= s >> 27;
            *o = BabyBear::new((s.wrapping_mul(0x2545F4914F6CDD1D) >> 33) as u32);
        }
        BabyBear8(out)
    }

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
        let a = elem(1);
        let b = elem(2);
        assert_eq!(a + b, b + a);
    }

    #[test]
    fn multiplication_identity() {
        let a = elem(3);
        assert_eq!(a * BabyBear8::ONE, a);
        assert_eq!(BabyBear8::ONE * a, a);
    }

    #[test]
    fn multiplication_commutativity() {
        let a = elem(11);
        let b = elem(12);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn multiplication_by_zero() {
        let a = elem(4);
        assert_eq!(a * BabyBear8::ZERO, BabyBear8::ZERO);
    }

    #[test]
    fn multiplication_associativity() {
        let a = elem(5);
        let b = elem(6);
        let c = elem(7);
        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn multiplication_distributivity() {
        let a = elem(8);
        let b = elem(9);
        let c = elem(10);
        assert_eq!(a * (b + c), a * b + a * c);
    }

    /// `z^8 = 11` — the defining reduction holds in the chosen basis.
    #[test]
    fn defining_relation_z8_eq_w() {
        // z = [0,1,0,0,0,0,0,0]; z^8 should equal the constant W = 11.
        let mut z = BabyBear8::ZERO;
        z.0[1] = BabyBear::ONE;
        let z8 = z.pow_u32(8);
        assert_eq!(z8, BabyBear8::from_base(W));
    }

    #[test]
    fn inverse_correctness() {
        let a = elem(13);
        let inv = a.inverse().unwrap();
        assert_eq!(a * inv, BabyBear8::ONE);
    }

    #[test]
    fn inverse_of_one_is_one() {
        assert_eq!(BabyBear8::ONE.inverse().unwrap(), BabyBear8::ONE);
    }

    #[test]
    fn zero_has_no_inverse() {
        assert!(BabyBear8::ZERO.inverse().is_none());
    }

    /// THE FIELD PROOF: this is a genuine field — *every* nonzero element is
    /// invertible (no zero divisors). In particular the old tower's
    /// zero-divisor witness `A = y - x^2` is GONE: in the power basis `y = z`,
    /// `x^2 = z^4`, so `A = z - z^4` is nonzero and now HAS an inverse, and
    /// `A·(y + x^2) = A·(z + z^4) ≠ 0`.
    #[test]
    fn is_a_field_no_zero_divisors() {
        // Sweep a large family of nonzero elements; all must be invertible.
        for s in 0u64..2000 {
            let a = elem(s);
            if a.is_zero() {
                continue;
            }
            let inv = a
                .inverse()
                .unwrap_or_else(|| panic!("nonzero element {s:?} had no inverse — not a field"));
            assert_eq!(a * inv, BabyBear8::ONE, "inverse wrong for seed {s}");
        }

        // The specific old zero-divisor: A = y - x^2 = z - z^4.
        let mut a = BabyBear8::ZERO;
        a.0[1] = BabyBear::ONE; // + z   (= y)
        a.0[4] = -BabyBear::ONE; // - z^4 (= x^2)
        assert!(!a.is_zero());
        let a_inv = a
            .inverse()
            .expect("the old zero-divisor A = y - x^2 must now be invertible");
        assert_eq!(a * a_inv, BabyBear8::ONE);

        // And A·(y + x^2) = (z - z^4)(z + z^4) is NOT zero (it was 0 in the
        // broken product ring).
        let mut b = BabyBear8::ZERO;
        b.0[1] = BabyBear::ONE; // + z   (= y)
        b.0[4] = BabyBear::ONE; // + z^4 (= x^2)
        assert!(!(a * b).is_zero(), "A·(y+x^2) must be nonzero in a field");
    }

    /// Fermat: for a field of size q = p^8, every nonzero a satisfies
    /// `a^(q-1) = 1`. We check the equivalent `a^q = a` via repeated p-th powers
    /// (Frobenius), avoiding a 248-bit exponent: a^(p^8) = Frob^8(a) = a.
    #[test]
    fn frobenius_order_eight() {
        let a = elem(17);
        // p-th power = Frobenius. Apply it 8 times; result must return to a.
        let p_limbs = {
            let mut l = [0u32; 8];
            l[0] = BABYBEAR_P;
            l
        };
        let mut cur = a;
        for _ in 0..8 {
            cur = cur.pow_multi(&p_limbs);
        }
        assert_eq!(cur, a, "a^(p^8) must equal a in F_{{p^8}}");
        // And one Frobenius step should NOT fix a generic element (a is not in F_p).
        assert_ne!(a.pow_multi(&p_limbs), a);
    }

    #[test]
    fn square_equals_mul_self() {
        let a = elem(18);
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
        let a = elem(19);
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
        let a = elem(20);
        assert_eq!(a.pow_u32(0), BabyBear8::ONE);
    }
}
