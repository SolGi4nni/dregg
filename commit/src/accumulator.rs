//! Polynomial-evaluation accumulator for O(1) non-membership proofs.
//!
//! Implements the STARK-native polynomial accumulator over BabyBear^4 (quartic extension
//! field, ~124-bit security via Schwartz-Zippel). Replaces the sorted-Merkle approach
//! with a single multiplication check per ancestor.
//!
//! # Construction
//!
//! Given a set S = {h_1, ..., h_n} of BabyBear field elements (revocation hashes)
//! and a public random challenge alpha in BabyBear^4:
//!
//! ```text
//! Acc = product(alpha - h_i) for all h_i in S
//! ```
//!
//! # Non-membership proof for element x NOT in S
//!
//! ```text
//! witness = Acc / (alpha - x)
//! Verification: witness * (alpha - x) == Acc
//! ```
//!
//! If x IS in S, then (alpha - x) divides Acc, but the "witness" would be
//! Acc/(alpha-x) which is a valid division — the key insight is that the prover
//! doesn't know x is absent; the verification equation holds trivially for members.
//! Non-membership is enforced by the protocol: the verifier checks that witness
//! was computed correctly from the public accumulator, and the prover demonstrates
//! they DON'T have a factor (alpha - x) in Acc by providing the remainder.
//!
//! Actually for non-membership with remainder:
//! ```text
//! Acc = witness * (alpha - x) + remainder
//! ```
//! where remainder != 0 proves x is NOT in S.
//! If x IS in S, (alpha - x) | Acc exactly, so remainder = 0.

use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::hash_many;

// ============================================================================
// BabyBear^4: Quartic extension field
// ============================================================================

/// An element of BabyBear^4, the quartic extension of BabyBear.
///
/// Represented as a degree-3 polynomial over BabyBear: a + b*X + c*X^2 + d*X^3
/// where X^4 = 11 (the irreducible polynomial X^4 - 11 over BabyBear).
///
/// The constant 11 is chosen because it is a non-residue in BabyBear, making
/// X^4 - 11 irreducible over the field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BabyBear4(pub [BabyBear; 4]);

/// The irreducible polynomial is X^4 - W where W = 11.
/// When multiplying, X^4 = W, so we reduce by replacing X^4 with W.
const IRREDUCIBLE_W: BabyBear = BabyBear(11);

impl BabyBear4 {
    /// The zero element of the extension field.
    pub const ZERO: Self = Self([
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);

    /// The one element (multiplicative identity).
    pub const ONE: Self = Self([
        BabyBear::ONE,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);

    /// Create from four base field elements.
    pub fn new(a: BabyBear, b: BabyBear, c: BabyBear, d: BabyBear) -> Self {
        Self([a, b, c, d])
    }

    /// Embed a base field element into the extension (as the constant coefficient).
    pub fn from_base(x: BabyBear) -> Self {
        Self([x, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO])
    }

    /// Check if this element is zero.
    pub fn is_zero(&self) -> bool {
        self.0[0] == BabyBear::ZERO
            && self.0[1] == BabyBear::ZERO
            && self.0[2] == BabyBear::ZERO
            && self.0[3] == BabyBear::ZERO
    }

    /// Addition in BabyBear^4 (component-wise).
    pub fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
        ])
    }

    /// Subtraction in BabyBear^4 (component-wise).
    pub fn sub(self, rhs: Self) -> Self {
        Self([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
        ])
    }

    /// Multiplication in BabyBear^4.
    ///
    /// Let a = a0 + a1*X + a2*X^2 + a3*X^3
    /// Let b = b0 + b1*X + b2*X^2 + b3*X^3
    ///
    /// Product c = a * b mod (X^4 - W):
    /// The schoolbook product has 7 terms (degree 0..6), and we reduce
    /// X^4 -> W, X^5 -> W*X, X^6 -> W*X^2, X^7 -> W*X^3.
    pub fn mul(self, rhs: Self) -> Self {
        let a = self.0;
        let b = rhs.0;
        let w = IRREDUCIBLE_W;

        // Schoolbook multiplication collecting terms by degree.
        // Degree 0: a0*b0 + W*(a1*b3 + a2*b2 + a3*b1)
        // Degree 1: a0*b1 + a1*b0 + W*(a2*b3 + a3*b2)
        // Degree 2: a0*b2 + a1*b1 + a2*b0 + W*(a3*b3)
        // Degree 3: a0*b3 + a1*b2 + a2*b1 + a3*b0

        let c0 = a[0] * b[0] + w * (a[1] * b[3] + a[2] * b[2] + a[3] * b[1]);
        let c1 = a[0] * b[1] + a[1] * b[0] + w * (a[2] * b[3] + a[3] * b[2]);
        let c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + w * (a[3] * b[3]);
        let c3 = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];

        Self([c0, c1, c2, c3])
    }

    /// Negation.
    pub fn neg(self) -> Self {
        Self([-self.0[0], -self.0[1], -self.0[2], -self.0[3]])
    }

    /// Compute the multiplicative inverse using the norm-based method.
    ///
    /// For extension field F_{p^4} with irreducible X^4 - W:
    /// We compute the inverse via the formula:
    ///   a^{-1} = a^{p^4 - 2} (Fermat's little theorem in the extension field)
    ///
    /// But that's expensive. Instead we use: inv(a) = conjugate(a) / norm(a)
    /// where norm maps to the base field and can be inverted cheaply.
    ///
    /// For practical purposes, we use the extended Euclidean algorithm approach:
    /// Represent the element as a polynomial, compute its inverse mod (X^4 - W).
    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // Use Fermat's little theorem: a^{-1} = a^{|F*| - 1} = a^{p^4 - 2}
        // But p^4 is huge. Instead, use the formula for quartic extension:
        //
        // For a in F_{p^4}, norm(a) = a * a^p * a^{p^2} * a^{p^3} is in F_p.
        // Then a^{-1} = (a^p * a^{p^2} * a^{p^3}) / norm(a).
        //
        // The Frobenius endomorphism x -> x^p is cheap: for X^4 - W,
        // frob(a0 + a1*X + a2*X^2 + a3*X^3) = a0 + a1*X^p + a2*X^{2p} + a3*X^{3p}
        // where X^p = X * W^{(p-1)/4} (since X^4 = W, X^p = X * (X^4)^{(p-1)/4} = X * W^{(p-1)/4}).
        //
        // For simplicity and correctness, we use the direct matrix inversion approach
        // for a 4x4 system, which is always correct but slightly more code:
        //
        // Actually, the cleanest correct approach: compute a^{p^4 - 2} via repeated squaring.
        // p^4 - 2 is large but the squaring is in the extension field (cheap per step).
        //
        // p = 2013265921, p^4 - 2 is a 124-bit number.
        // This takes ~124 squarings + ~62 multiplications = ~186 ext-field muls.
        // Each ext-field mul is 16 base muls. Total: ~3000 base muls. Fast enough.

        // Actually let's use a simpler approach: solve a*x = 1 in the extension directly.
        // Given a = [a0, a1, a2, a3], find x = [x0, x1, x2, x3] such that a*x = [1, 0, 0, 0].
        // This is a 4x4 linear system over BabyBear.
        //
        // The multiplication a * x gives:
        //   c0 = a0*x0 + W*(a1*x3 + a2*x2 + a3*x1) = 1
        //   c1 = a0*x1 + a1*x0 + W*(a2*x3 + a3*x2) = 0
        //   c2 = a0*x2 + a1*x1 + a2*x0 + W*(a3*x3) = 0
        //   c3 = a0*x3 + a1*x2 + a2*x1 + a3*x0 = 0
        //
        // Matrix form: M * [x0, x1, x2, x3]^T = [1, 0, 0, 0]^T
        // where M = [[a0, W*a3, W*a2, W*a1],
        //            [a1, a0, W*a3, W*a2],
        //            [a2, a1, a0, W*a3],
        //            [a3, a2, a1, a0]]
        //
        // This is a circulant-like matrix (actually a "twisted" circulant / negacyclic).
        // We solve via Gaussian elimination.

        let a = self.0;
        let w = IRREDUCIBLE_W;

        // Build the augmented matrix [M | I_col0]
        // M[i][j] gives the coefficient of x_j in equation i.
        let mut mat = [[BabyBear::ZERO; 5]; 4]; // 4x5 augmented matrix

        // Row 0: a0*x0 + W*a3*x1 + W*a2*x2 + W*a1*x3 = 1
        mat[0][0] = a[0];
        mat[0][1] = w * a[3];
        mat[0][2] = w * a[2];
        mat[0][3] = w * a[1];
        mat[0][4] = BabyBear::ONE;

        // Row 1: a1*x0 + a0*x1 + W*a3*x2 + W*a2*x3 = 0
        mat[1][0] = a[1];
        mat[1][1] = a[0];
        mat[1][2] = w * a[3];
        mat[1][3] = w * a[2];
        mat[1][4] = BabyBear::ZERO;

        // Row 2: a2*x0 + a1*x1 + a0*x2 + W*a3*x3 = 0
        mat[2][0] = a[2];
        mat[2][1] = a[1];
        mat[2][2] = a[0];
        mat[2][3] = w * a[3];
        mat[2][4] = BabyBear::ZERO;

        // Row 3: a3*x0 + a2*x1 + a1*x2 + a0*x3 = 0
        mat[3][0] = a[3];
        mat[3][1] = a[2];
        mat[3][2] = a[1];
        mat[3][3] = a[0];
        mat[3][4] = BabyBear::ZERO;

        // Gaussian elimination with partial pivoting.
        for col in 0..4 {
            // Find pivot.
            let mut pivot_row = None;
            for row in col..4 {
                if mat[row][col] != BabyBear::ZERO {
                    pivot_row = Some(row);
                    break;
                }
            }
            let pivot_row = pivot_row?; // If no pivot, element is not invertible.

            // Swap rows.
            if pivot_row != col {
                mat.swap(col, pivot_row);
            }

            // Scale pivot row.
            let inv_pivot = mat[col][col].inverse()?;
            for j in 0..5 {
                mat[col][j] = mat[col][j] * inv_pivot;
            }

            // Eliminate other rows.
            for row in 0..4 {
                if row == col {
                    continue;
                }
                let factor = mat[row][col];
                for j in 0..5 {
                    mat[row][j] = mat[row][j] - factor * mat[col][j];
                }
            }
        }

        Some(Self([mat[0][4], mat[1][4], mat[2][4], mat[3][4]]))
    }
}

// ============================================================================
// Polynomial Accumulator
// ============================================================================

/// A polynomial-evaluation accumulator over BabyBear^4.
///
/// Maintains `Acc = product(alpha - h_i)` for all elements h_i in the set.
/// Alpha is a public challenge derived via Fiat-Shamir from the set commitment.
#[derive(Clone, Debug)]
pub struct PolynomialAccumulator {
    /// The accumulator value: product(alpha - h_i) in BabyBear^4.
    pub value: BabyBear4,
    /// The public random challenge alpha in BabyBear^4.
    pub alpha: BabyBear4,
    /// The elements currently in the set (revocation hashes as base field elements).
    elements: Vec<BabyBear>,
}

/// A non-membership witness for the polynomial accumulator.
///
/// For element x NOT in the set S:
/// - `witness`: Acc / (alpha - x) — the quotient
/// - `remainder`: Always zero for a proper non-membership proof using this construction
///
/// Verification: witness * (alpha - x) == Acc
///
/// If x IS in S, then (alpha - x) is one of the factors of Acc, so
/// Acc / (alpha - x) = product of all OTHER factors. The verification
/// equation `witness * (alpha - x) == Acc` would succeed — which means
/// this is actually a MEMBERSHIP witness.
///
/// The protocol distinction: for NON-membership, we provide a witness such that
/// `witness * (alpha - x) == Acc`. This always succeeds if we compute it honestly.
/// The soundness comes from: if x IS in S, the prover CANNOT produce a witness
/// that makes verification fail (they'd have to find a different alpha or break
/// the Fiat-Shamir binding). And if x is NOT in S, the honest computation of
/// Acc / (alpha - x) gives a valid witness.
///
/// Wait — that's backwards. Let me reconsider the design doc's construction:
///
/// The CORRECT non-membership approach from the design doc uses polynomial division
/// with remainder:
///   Acc = witness * (alpha - x) + remainder
///   Non-membership: remainder != 0
///   Membership: remainder == 0
///
/// But for our use case (proving ancestor is NOT revoked), we need the simpler form:
/// Since we KNOW the element is not in the set (we're the honest prover), we compute:
///   witness = Acc / (alpha - x)
/// And verification checks: witness * (alpha - x) == Acc
///
/// The key insight: if x WERE in S, then alpha - x would be a factor of Acc,
/// and the division would be exact. But the CIRCUIT doesn't know whether x is in S;
/// it just checks the equation. The soundness comes from the Fiat-Shamir binding
/// of alpha to the set contents: the prover cannot choose alpha to make a false
/// statement verify.
///
/// Actually, re-reading the design doc more carefully: the simple form
/// `witness * (alpha - x) == Acc` works for BOTH membership and non-membership
/// (the equation is satisfiable in both cases). The difference is:
///
/// For our non-revocation use case, we use: `witness * (alpha - x) == Acc`
/// where witness = product(alpha - h_j) for j != the-index-of-x.
/// This proves x IS in the set (membership).
///
/// For NON-membership, we need the remainder form:
/// `witness * (alpha - x) + remainder == Acc` AND `remainder != 0`
///
/// Let me implement the remainder-based approach as specified in the design doc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccumulatorWitness {
    /// The quotient: (Acc - remainder) / (alpha - x).
    pub quotient: BabyBear4,
    /// The remainder: Acc mod (alpha - x) in the polynomial sense.
    /// For non-membership: remainder = Acc - quotient * (alpha - x) != 0.
    /// For membership: remainder = 0.
    ///
    /// Concretely: remainder = Acc evaluated at x's embedding = product(alpha - h_j)
    /// ... no, this is evaluation of the SET polynomial at (alpha - x).
    ///
    /// Actually from the doc: f(x) = product(x - h_i). Then:
    /// - Acc = f(alpha)
    /// - For non-membership of h: f(h) != 0
    /// - Witness: (w, v) where Acc = w * (alpha - h) + v
    /// - w = (Acc - v) / (alpha - h), v = f(h) = product(h - h_i) mapped to ext field
    ///
    /// Wait, f(h) is in the BASE field since all h_i are base field elements.
    /// But alpha is in the extension field, so Acc is in the extension field.
    /// v must be: product(h - h_i) for all h_i in S, computed in the extension.
    /// Actually h is also a base field element, so product(h - h_i) is a base field element.
    /// We embed it into the extension field for the constraint.
    pub remainder: BabyBear4,
}

impl PolynomialAccumulator {
    /// Create a new empty accumulator with the given alpha challenge.
    ///
    /// An empty set has accumulator value = 1 (empty product).
    pub fn new(alpha: BabyBear4) -> Self {
        Self {
            value: BabyBear4::ONE,
            alpha,
            elements: Vec::new(),
        }
    }

    /// Create an accumulator from a set of elements with a given alpha.
    pub fn from_set(elements: &[BabyBear], alpha: BabyBear4) -> Self {
        let mut acc = Self::new(alpha);
        for &elem in elements {
            acc.insert(elem);
        }
        acc
    }

    /// Derive alpha deterministically from a domain separator.
    ///
    /// Uses Poseidon2 hash of the domain separator elements to produce
    /// four BabyBear elements forming the alpha challenge.
    pub fn derive_alpha(domain: &[BabyBear]) -> BabyBear4 {
        // Hash domain to get 4 independent elements for the extension field.
        let h0 = hash_many(domain);
        let h1 = hash_many(&[h0, BabyBear::new(1)]);
        let h2 = hash_many(&[h0, BabyBear::new(2)]);
        let h3 = hash_many(&[h0, BabyBear::new(3)]);
        BabyBear4::new(h0, h1, h2, h3)
    }

    /// Insert an element into the accumulator.
    ///
    /// Updates: Acc_new = Acc_old * (alpha - element)
    pub fn insert(&mut self, element: BabyBear) {
        let elem_ext = BabyBear4::from_base(element);
        let factor = self.alpha.sub(elem_ext);
        self.value = self.value.mul(factor);
        self.elements.push(element);
    }

    /// Remove an element from the accumulator.
    ///
    /// Updates: Acc_new = Acc_old / (alpha - element)
    /// Returns false if the element was not in the set or division fails.
    pub fn remove(&mut self, element: BabyBear) -> bool {
        if let Some(pos) = self.elements.iter().position(|&e| e == element) {
            let elem_ext = BabyBear4::from_base(element);
            let factor = self.alpha.sub(elem_ext);
            if let Some(inv) = factor.inverse() {
                self.value = self.value.mul(inv);
                self.elements.swap_remove(pos);
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Compute a non-membership witness for an element NOT in the set.
    ///
    /// Returns `Some(witness)` where:
    /// - `witness.quotient * (alpha - x) + witness.remainder == Acc`
    /// - `witness.remainder != 0` (proves non-membership)
    ///
    /// Returns `None` if the element IS in the set (remainder would be zero).
    pub fn non_membership_witness(&self, element: BabyBear) -> Option<AccumulatorWitness> {
        // Check if element is in the set.
        if self.elements.contains(&element) {
            return None;
        }

        // Compute remainder: v = product(element - h_i) for all h_i in set.
        // This is the "set polynomial evaluated at element": f(element).
        // In base field since all values are base field elements.
        let mut remainder_base = BabyBear::ONE;
        for &h_i in &self.elements {
            remainder_base = remainder_base * (element - h_i);
        }

        // The remainder should be nonzero (element not in set).
        // If remainder is zero, it means element equals some h_i (hash collision
        // or element is in set). This shouldn't happen if we checked above.
        if remainder_base == BabyBear::ZERO {
            return None;
        }

        let remainder = BabyBear4::from_base(remainder_base);

        // Compute quotient: w = (Acc - remainder) / (alpha - element)
        let elem_ext = BabyBear4::from_base(element);
        let divisor = self.alpha.sub(elem_ext); // alpha - element
        let numerator = self.value.sub(remainder); // Acc - remainder

        let quotient = numerator.mul(divisor.inverse()?);

        Some(AccumulatorWitness {
            quotient,
            remainder,
        })
    }

    /// Compute a membership witness for an element that IS in the set.
    ///
    /// Returns `Some(witness)` where:
    /// - `witness.quotient * (alpha - x) == Acc` (remainder is zero)
    ///
    /// Returns `None` if element is NOT in the set.
    pub fn membership_witness(&self, element: BabyBear) -> Option<AccumulatorWitness> {
        if !self.elements.contains(&element) {
            return None;
        }

        // For membership, remainder = 0 and quotient = Acc / (alpha - element)
        let elem_ext = BabyBear4::from_base(element);
        let factor = self.alpha.sub(elem_ext);
        let quotient = self.value.mul(factor.inverse()?);

        Some(AccumulatorWitness {
            quotient,
            remainder: BabyBear4::ZERO,
        })
    }

    /// Verify a non-membership witness.
    ///
    /// Checks: `quotient * (alpha - element) + remainder == accumulator_value`
    /// AND `remainder != 0`.
    pub fn verify_non_membership(
        witness: &AccumulatorWitness,
        element: BabyBear,
        alpha: BabyBear4,
        accumulator: BabyBear4,
    ) -> bool {
        // remainder must be nonzero for non-membership
        if witness.remainder.is_zero() {
            return false;
        }

        let elem_ext = BabyBear4::from_base(element);
        let diff = alpha.sub(elem_ext); // alpha - element
        let product = witness.quotient.mul(diff); // quotient * (alpha - element)
        let lhs = product.add(witness.remainder); // + remainder

        lhs == accumulator
    }

    /// Verify a membership witness.
    ///
    /// Checks: `quotient * (alpha - element) == accumulator_value`
    /// (i.e., remainder is zero).
    pub fn verify_membership(
        witness: &AccumulatorWitness,
        element: BabyBear,
        alpha: BabyBear4,
        accumulator: BabyBear4,
    ) -> bool {
        if !witness.remainder.is_zero() {
            return false;
        }

        let elem_ext = BabyBear4::from_base(element);
        let diff = alpha.sub(elem_ext);
        let product = witness.quotient.mul(diff);

        product == accumulator
    }

    /// Get the current accumulator value.
    pub fn accumulator_value(&self) -> BabyBear4 {
        self.value
    }

    /// Get the alpha challenge.
    pub fn alpha(&self) -> BabyBear4 {
        self.alpha
    }

    /// Get the number of elements in the set.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Whether the accumulator set is empty.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Update a non-membership witness when a new element is added to the set.
    ///
    /// When h_new is added:
    /// - New accumulator: Acc_new = Acc_old * (alpha - h_new)
    /// - New remainder: v_new = v_old * (element - h_new)
    /// - New quotient: w_new = (Acc_new - v_new) / (alpha - element)
    pub fn update_witness_for_insert(
        witness: &AccumulatorWitness,
        element: BabyBear,
        new_element: BabyBear,
        alpha: BabyBear4,
        old_accumulator: BabyBear4,
    ) -> Option<(AccumulatorWitness, BabyBear4)> {
        // New accumulator
        let new_elem_ext = BabyBear4::from_base(new_element);
        let new_factor = alpha.sub(new_elem_ext);
        let new_accumulator = old_accumulator.mul(new_factor);

        // New remainder: v_new = v_old * (element - new_element) in base field
        let remainder_factor = BabyBear4::from_base(element - new_element);
        let new_remainder = witness.remainder.mul(remainder_factor);

        // New quotient: w_new = (Acc_new - v_new) / (alpha - element)
        let elem_ext = BabyBear4::from_base(element);
        let divisor = alpha.sub(elem_ext);
        let numerator = new_accumulator.sub(new_remainder);
        let new_quotient = numerator.mul(divisor.inverse()?);

        Some((
            AccumulatorWitness {
                quotient: new_quotient,
                remainder: new_remainder,
            },
            new_accumulator,
        ))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Derive a test alpha from a simple seed.
    fn test_alpha() -> BabyBear4 {
        PolynomialAccumulator::derive_alpha(&[BabyBear::new(0x1234), BabyBear::new(0x5678)])
    }

    #[test]
    fn extension_field_mul_identity() {
        let a = BabyBear4::new(
            BabyBear::new(7),
            BabyBear::new(13),
            BabyBear::new(21),
            BabyBear::new(42),
        );
        // a * 1 = a
        assert_eq!(a.mul(BabyBear4::ONE), a);
        // 1 * a = a
        assert_eq!(BabyBear4::ONE.mul(a), a);
    }

    #[test]
    fn extension_field_mul_zero() {
        let a = BabyBear4::new(
            BabyBear::new(7),
            BabyBear::new(13),
            BabyBear::new(21),
            BabyBear::new(42),
        );
        assert_eq!(a.mul(BabyBear4::ZERO), BabyBear4::ZERO);
    }

    #[test]
    fn extension_field_inverse() {
        let a = BabyBear4::new(
            BabyBear::new(7),
            BabyBear::new(13),
            BabyBear::new(21),
            BabyBear::new(42),
        );
        let inv = a.inverse().unwrap();
        let product = a.mul(inv);
        assert_eq!(product, BabyBear4::ONE);
    }

    #[test]
    fn extension_field_inverse_base_element() {
        // A pure base field element embedded in the extension.
        let a = BabyBear4::from_base(BabyBear::new(17));
        let inv = a.inverse().unwrap();
        let product = a.mul(inv);
        assert_eq!(product, BabyBear4::ONE);

        // Should match base field inverse.
        let base_inv = BabyBear::new(17).inverse().unwrap();
        assert_eq!(inv.0[0], base_inv);
        assert_eq!(inv.0[1], BabyBear::ZERO);
        assert_eq!(inv.0[2], BabyBear::ZERO);
        assert_eq!(inv.0[3], BabyBear::ZERO);
    }

    #[test]
    fn empty_accumulator() {
        let alpha = test_alpha();
        let acc = PolynomialAccumulator::new(alpha);
        assert_eq!(acc.accumulator_value(), BabyBear4::ONE);
        assert_eq!(acc.len(), 0);
    }

    #[test]
    fn insert_single_element() {
        let alpha = test_alpha();
        let mut acc = PolynomialAccumulator::new(alpha);
        let elem = BabyBear::new(42);
        acc.insert(elem);

        // Acc should be (alpha - 42)
        let expected = alpha.sub(BabyBear4::from_base(elem));
        assert_eq!(acc.accumulator_value(), expected);
    }

    #[test]
    fn insert_multiple_elements() {
        let alpha = test_alpha();
        let mut acc = PolynomialAccumulator::new(alpha);

        let elems: Vec<BabyBear> = (1..=5).map(|i| BabyBear::new(i * 100)).collect();
        for &e in &elems {
            acc.insert(e);
        }

        // Manually compute expected value.
        let mut expected = BabyBear4::ONE;
        for &e in &elems {
            expected = expected.mul(alpha.sub(BabyBear4::from_base(e)));
        }
        assert_eq!(acc.accumulator_value(), expected);
    }

    #[test]
    fn non_membership_witness_valid() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=100).map(|i| BabyBear::new(i * 7)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        // Element 101*7 = 707 is NOT in the set (set contains 7, 14, ..., 700).
        let absent = BabyBear::new(707);
        assert!(!elems.contains(&absent));

        let witness = acc.non_membership_witness(absent).unwrap();

        // Verify: quotient * (alpha - absent) + remainder == Acc
        assert!(PolynomialAccumulator::verify_non_membership(
            &witness,
            absent,
            alpha,
            acc.accumulator_value(),
        ));

        // Remainder must be nonzero.
        assert!(!witness.remainder.is_zero());
    }

    #[test]
    fn non_membership_fails_for_member() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=100).map(|i| BabyBear::new(i * 7)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        // Element 50*7 = 350 IS in the set.
        let present = BabyBear::new(350);
        assert!(elems.contains(&present));

        // Should return None (can't produce non-membership witness for a member).
        assert!(acc.non_membership_witness(present).is_none());
    }

    #[test]
    fn membership_witness_valid() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i * 100)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        let member = BabyBear::new(500); // 5th element
        let witness = acc.membership_witness(member).unwrap();

        assert!(PolynomialAccumulator::verify_membership(
            &witness,
            member,
            alpha,
            acc.accumulator_value(),
        ));
    }

    #[test]
    fn membership_witness_fails_for_non_member() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i * 100)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        let absent = BabyBear::new(999);
        assert!(acc.membership_witness(absent).is_none());
    }

    #[test]
    fn verify_non_membership_rejects_fake_witness() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i * 100)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        // Fabricate a fake witness with random values.
        let fake_witness = AccumulatorWitness {
            quotient: BabyBear4::new(
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(3),
                BabyBear::new(4),
            ),
            remainder: BabyBear4::from_base(BabyBear::new(99)),
        };

        // Should fail verification.
        assert!(!PolynomialAccumulator::verify_non_membership(
            &fake_witness,
            BabyBear::new(999),
            alpha,
            acc.accumulator_value(),
        ));
    }

    #[test]
    fn verify_non_membership_rejects_zero_remainder() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i * 100)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        // Even if quotient is "correct", a zero remainder means membership, not non-membership.
        let member = BabyBear::new(500);
        let mem_witness = acc.membership_witness(member).unwrap();

        // Try to pass a membership witness as a non-membership witness.
        assert!(!PolynomialAccumulator::verify_non_membership(
            &mem_witness,
            member,
            alpha,
            acc.accumulator_value(),
        ));
    }

    #[test]
    fn remove_element() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=5).map(|i| BabyBear::new(i * 100)).collect();
        let mut acc = PolynomialAccumulator::from_set(&elems, alpha);

        let original_value = acc.accumulator_value();

        // Remove element 300.
        assert!(acc.remove(BabyBear::new(300)));
        assert_eq!(acc.len(), 4);

        // Re-insert it.
        acc.insert(BabyBear::new(300));
        assert_eq!(acc.len(), 5);
        assert_eq!(acc.accumulator_value(), original_value);
    }

    #[test]
    fn witness_update_on_insert() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=5).map(|i| BabyBear::new(i * 100)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        let absent = BabyBear::new(999);
        let witness = acc.non_membership_witness(absent).unwrap();

        // Add a new element.
        let new_elem = BabyBear::new(600);
        let (updated_witness, new_acc_value) = PolynomialAccumulator::update_witness_for_insert(
            &witness,
            absent,
            new_elem,
            alpha,
            acc.accumulator_value(),
        )
        .unwrap();

        // Verify the updated witness against the new accumulator.
        assert!(PolynomialAccumulator::verify_non_membership(
            &updated_witness,
            absent,
            alpha,
            new_acc_value,
        ));

        // Also verify by building the accumulator from scratch.
        let mut acc2 = PolynomialAccumulator::from_set(&elems, alpha);
        acc2.insert(new_elem);
        assert_eq!(new_acc_value, acc2.accumulator_value());
    }

    #[test]
    fn large_set_non_membership() {
        let alpha = test_alpha();
        // Insert 100 elements.
        let elems: Vec<BabyBear> = (1..=100).map(|i| BabyBear::new(i)).collect();
        let acc = PolynomialAccumulator::from_set(&elems, alpha);

        // Prove non-membership of element 101.
        let absent = BabyBear::new(101);
        let witness = acc.non_membership_witness(absent).unwrap();
        assert!(PolynomialAccumulator::verify_non_membership(
            &witness,
            absent,
            alpha,
            acc.accumulator_value(),
        ));

        // Prove non-membership of element 200.
        let absent2 = BabyBear::new(200);
        let witness2 = acc.non_membership_witness(absent2).unwrap();
        assert!(PolynomialAccumulator::verify_non_membership(
            &witness2,
            absent2,
            alpha,
            acc.accumulator_value(),
        ));
    }

    #[test]
    fn from_set_matches_incremental() {
        let alpha = test_alpha();
        let elems: Vec<BabyBear> = (1..=20).map(|i| BabyBear::new(i * 3)).collect();

        let acc_batch = PolynomialAccumulator::from_set(&elems, alpha);

        let mut acc_inc = PolynomialAccumulator::new(alpha);
        for &e in &elems {
            acc_inc.insert(e);
        }

        assert_eq!(acc_batch.accumulator_value(), acc_inc.accumulator_value());
    }

    #[test]
    fn derive_alpha_deterministic() {
        let domain = [BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)];
        let a1 = PolynomialAccumulator::derive_alpha(&domain);
        let a2 = PolynomialAccumulator::derive_alpha(&domain);
        assert_eq!(a1, a2);
    }

    #[test]
    fn derive_alpha_different_domains() {
        let d1 = [BabyBear::new(1)];
        let d2 = [BabyBear::new(2)];
        let a1 = PolynomialAccumulator::derive_alpha(&d1);
        let a2 = PolynomialAccumulator::derive_alpha(&d2);
        assert_ne!(a1, a2);
    }
}
