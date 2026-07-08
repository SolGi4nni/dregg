//! `R_q = ℤ_q[X]/(Xⁿ+1)` — the negacyclic polynomial quotient ring the Lean
//! spec's abstract `CommRing R` is instantiated at for this reference.
//!
//! Realistic-ward parameters (`N = 64`, `Q = 8380417`, the Dilithium prime
//! `2²³ − 2¹³ + 1`; `2N | Q − 1`, so the ring is NTT-friendly) but still
//! schoolbook negacyclic convolution: this is a REFERENCE, not a performant
//! or constant-time implementation. Production dimension is `n ≥ 256`; the
//! step to `N = 64` keeps the whole test suite (including the empirical
//! key-hiding TV measurements) fast under schoolbook `O(n²)` multiplication
//! while exercising real-modulus arithmetic.

/// Ring dimension `n` in `Xⁿ + 1`. Production target is `n ≥ 256`; this
/// reference runs at 64 (see the module doc).
pub const N: usize = 64;

/// The coefficient modulus `q` (prime; `8380417 = 2²³ − 2¹³ + 1`, the
/// Dilithium prime — `2¹³ | q − 1`, so negacyclic NTTs exist up to `n = 2¹²`).
pub const Q: u64 = 8380417;

/// An element of `R_q`: coefficients of `1, X, …, X^{N-1}`, each in `[0, Q)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Poly {
    /// Coefficient of `X^i` at position `i`, reduced mod [`Q`].
    pub coeffs: [u64; N],
}

impl Poly {
    /// The zero element.
    pub const ZERO: Poly = Poly { coeffs: [0; N] };

    /// The constant polynomial `v mod q` (the image of `ℤ_q ↪ R_q`).
    pub fn constant(v: u64) -> Self {
        let mut coeffs = [0u64; N];
        coeffs[0] = v % Q;
        Poly { coeffs }
    }

    /// Ring addition, coefficientwise mod `q`.
    pub fn add(&self, other: &Self) -> Self {
        let mut coeffs = [0u64; N];
        for (i, c) in coeffs.iter_mut().enumerate() {
            *c = (self.coeffs[i] + other.coeffs[i]) % Q;
        }
        Poly { coeffs }
    }

    /// Ring subtraction, coefficientwise mod `q`.
    pub fn sub(&self, other: &Self) -> Self {
        let mut coeffs = [0u64; N];
        for (i, c) in coeffs.iter_mut().enumerate() {
            *c = (self.coeffs[i] + Q - other.coeffs[i]) % Q;
        }
        Poly { coeffs }
    }

    /// Additive inverse.
    pub fn neg(&self) -> Self {
        Poly::ZERO.sub(self)
    }

    /// Ring multiplication: schoolbook NEGACYCLIC convolution — the index
    /// wraparound `X^N = -1` is the quotient by `Xⁿ + 1`.
    pub fn mul(&self, other: &Self) -> Self {
        // |acc| ≤ N · (Q-1)² = 64 · (8380416)² ≈ 4.5e15 — inside i64 (≈ 9.2e18).
        let mut acc = [0i64; N];
        for i in 0..N {
            for j in 0..N {
                let p = (self.coeffs[i] * other.coeffs[j]) as i64;
                let k = i + j;
                if k < N {
                    acc[k] += p;
                } else {
                    acc[k - N] -= p; // X^{k} = X^{k-N} · X^N = -X^{k-N}
                }
            }
        }
        let mut coeffs = [0u64; N];
        for i in 0..N {
            coeffs[i] = acc[i].rem_euclid(Q as i64) as u64;
        }
        Poly { coeffs }
    }

    /// Coefficient `i` in CENTERED representation: the unique integer in
    /// `(-q/2, q/2]` congruent to `coeffs[i]` mod `q`.
    pub fn centered_coeff(&self, i: usize) -> i64 {
        let c = self.coeffs[i];
        if c * 2 > Q {
            c as i64 - Q as i64
        } else {
            c as i64
        }
    }

    /// The L∞ norm in centered representation: `max_i |centered_coeff(i)|`.
    ///
    /// This is the norm carrier the Lean spec names but leaves abstract
    /// (`Lattice.ShortNorm` / the "shortness" of MSIS witnesses): every
    /// element of `ℤ_q` trivially has centered norm `≤ ⌊q/2⌋`, so a norm
    /// bound only has teeth when it is strictly below that ceiling.
    pub fn norm_inf(&self) -> u64 {
        (0..N)
            .map(|i| self.centered_coeff(i).unsigned_abs())
            .max()
            .unwrap_or(0)
    }

    /// Is this the image of a base-ring constant?
    pub fn is_constant(&self) -> bool {
        self.coeffs[1..].iter().all(|&c| c == 0)
    }

    /// Inverse of a CONSTANT unit polynomial (`c ∈ ℤ_q^*` embedded in `R_q`).
    ///
    /// The Lean `FieldModel` extractor divides by `c - c'`; in the deployed
    /// ring the challenge set is chosen so challenge differences are units.
    /// This reference exposes inversion only on the constant subring (where
    /// `q` prime makes every nonzero element a unit), enough to realize
    /// `extractPreimage` on constant-challenge forks. General `R_q` inversion
    /// is intentionally out of scope.
    pub fn inverse_constant(&self) -> Option<Self> {
        if !self.is_constant() {
            return None;
        }
        inv_mod_q(self.coeffs[0]).map(Poly::constant)
    }
}

/// `a⁻¹ mod q` by Fermat (q prime), or `None` for `a ≡ 0`.
pub fn inv_mod_q(a: u64) -> Option<u64> {
    let a = a % Q;
    if a == 0 {
        return None;
    }
    // a^(q-2) mod q by square-and-multiply.
    let mut base = a;
    let mut exp = Q - 2;
    let mut result = 1u64;
    while exp > 0 {
        if exp & 1 == 1 {
            result = result * base % Q;
        }
        base = base * base % Q;
        exp >>= 1;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x_to(k: usize) -> Poly {
        let mut coeffs = [0u64; N];
        coeffs[k] = 1;
        Poly { coeffs }
    }

    #[test]
    fn negacyclic_wraparound_x_n_is_minus_one() {
        // X^{N-1} · X = X^N ≡ -1 in ℤ_q[X]/(Xⁿ+1).
        let prod = x_to(N - 1).mul(&x_to(1));
        assert_eq!(prod, Poly::constant(Q - 1));
    }

    /// Deterministic pseudorandom ring element (LCG; test data only).
    fn test_poly(seed: u64) -> Poly {
        let mut coeffs = [0u64; N];
        let mut s = seed;
        for c in coeffs.iter_mut() {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *c = (s >> 17) % Q;
        }
        Poly { coeffs }
    }

    #[test]
    fn ring_laws_spot_checks() {
        let a = test_poly(0xA11CE);
        let b = test_poly(0xB0B);
        let c = test_poly(0xC0FFEE);
        // Commutativity and associativity of mul; distributivity over add.
        assert_eq!(a.mul(&b), b.mul(&a));
        assert_eq!(a.mul(&b).mul(&c), a.mul(&b.mul(&c)));
        assert_eq!(a.mul(&b.add(&c)), a.mul(&b).add(&a.mul(&c)));
        // Additive group.
        assert_eq!(a.add(&a.neg()), Poly::ZERO);
        assert_eq!(a.sub(&b), a.add(&b.neg()));
        // Multiplicative identity.
        assert_eq!(a.mul(&Poly::constant(1)), a);
    }

    #[test]
    fn constant_inversion() {
        for v in [1u64, 2, 13, 256, 3328, Q - 1] {
            let p = Poly::constant(v);
            let inv = p.inverse_constant().unwrap();
            assert_eq!(p.mul(&inv), Poly::constant(1));
        }
        assert!(Poly::constant(0).inverse_constant().is_none());
        assert!(x_to(1).inverse_constant().is_none());
    }
}
