//! `R_q = ℤ_q[X]/(Xⁿ+1)` — the negacyclic polynomial quotient ring the Lean
//! spec's abstract `CommRing R` is instantiated at for this reference.
//!
//! Production parameters (`N = 256`, `Q = 8380417`, the Dilithium prime
//! `2²³ − 2¹³ + 1`; `2N | Q − 1`, so the ring is NTT-friendly). Multiplication
//! ([`Poly::mul`]) is the **NTT** path — `O(n log n)`, the production-shaped
//! algorithm — with the schoolbook `O(n²)` convolution ([`Poly::mul_schoolbook`])
//! retained as the reference it is verified against. It is still a REFERENCE in
//! the other senses (trusted dealer, pre-audit) — but with NTT it now runs at
//! the REAL production dimension `N = 256`, not a toy one.

use std::sync::OnceLock;

/// Ring dimension `n` in `Xⁿ + 1`. Production target is `n ≥ 256`; this
/// this reference runs at the production dimension 256 (see the module doc).
pub const N: usize = 256;

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

    /// Ring multiplication (the default): the fast `O(n log n)` NTT path
    /// ([`Poly::mul_ntt`]), verified bit-for-bit against the schoolbook reference
    /// ([`Poly::mul_schoolbook`]) by `ntt_mul_agrees_with_schoolbook`.
    pub fn mul(&self, other: &Self) -> Self {
        self.mul_ntt(other)
    }

    /// Reference NEGACYCLIC convolution, `O(n²)` schoolbook — the index
    /// wraparound `X^N = -1` is the quotient by `Xⁿ + 1`. Kept as the obviously-
    /// correct reference the NTT path is checked against.
    pub fn mul_schoolbook(&self, other: &Self) -> Self {
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

// ============================================================================
// NTT-based negacyclic multiplication — O(n log n), the production-shaped mul
// ============================================================================
//
// `R_q = ℤ_q[X]/(Xⁿ+1)` is NTT-friendly (`2N | Q-1`), so multiplication is a
// weighted length-N number-theoretic transform: pre-scale each `aᵢ` by `ψⁱ` (ψ
// a primitive 2N-th root, `ψᴺ ≡ -1`), transform with `ω = ψ²` (a primitive
// N-th root), multiply pointwise, inverse-transform, and un-scale by `ψ⁻ⁱ`. This
// is `O(n log n)` vs the schoolbook `O(n²)` `mul`; `mul_ntt` is verified to agree
// with `mul` bit-for-bit (test `ntt_mul_agrees_with_schoolbook`).

/// `base^exp mod Q` by square-and-multiply.
fn pow_mod(mut base: u64, mut exp: u64) -> u64 {
    let mut r = 1u64;
    base %= Q;
    while exp > 0 {
        if exp & 1 == 1 {
            r = r * base % Q;
        }
        base = base * base % Q;
        exp >>= 1;
    }
    r
}

/// Precomputed negacyclic-NTT twiddle tables (built once via `OnceLock`).
struct NttTables {
    psi: [u64; N],       // ψⁱ (pre-scale weights)
    psi_inv: [u64; N],   // ψ⁻ⁱ (un-scale weights)
    omega: [u64; N],     // ωⁱ, ω = ψ² (forward twiddles)
    omega_inv: [u64; N], // ω⁻ⁱ (inverse twiddles)
    n_inv: u64,          // N⁻¹ mod Q (inverse-transform scale)
}

fn ntt_tables() -> &'static NttTables {
    static T: OnceLock<NttTables> = OnceLock::new();
    T.get_or_init(|| {
        // Primitive 2N-th root: ψᴺ ≡ -1 (mod Q) forces order exactly 2N (N a power of 2).
        let mut psi_root = 0u64;
        for c in 2..Q {
            if pow_mod(c, N as u64) == Q - 1 {
                psi_root = c;
                break;
            }
        }
        assert!(psi_root != 0, "no primitive 2N-th root of unity mod Q");
        let psi_inv_root = inv_mod_q(psi_root).unwrap();
        let omega_root = psi_root * psi_root % Q;
        let omega_inv_root = inv_mod_q(omega_root).unwrap();
        let mut psi = [0u64; N];
        let mut psi_inv = [0u64; N];
        let mut omega = [0u64; N];
        let mut omega_inv = [0u64; N];
        let (mut p, mut pi, mut w, mut wi) = (1u64, 1u64, 1u64, 1u64);
        for i in 0..N {
            psi[i] = p;
            psi_inv[i] = pi;
            omega[i] = w;
            omega_inv[i] = wi;
            p = p * psi_root % Q;
            pi = pi * psi_inv_root % Q;
            w = w * omega_root % Q;
            wi = wi * omega_inv_root % Q;
        }
        NttTables {
            psi,
            psi_inv,
            omega,
            omega_inv,
            n_inv: inv_mod_q(N as u64).unwrap(),
        }
    })
}

/// In-place iterative Cooley–Tukey NTT (decimation-in-time, bit-reversal first)
/// with the supplied `ωⁱ` power table.
fn ntt_inplace(a: &mut [u64; N], omega_pow: &[u64; N]) {
    // bit-reversal permutation
    let mut j = 0usize;
    for i in 1..N {
        let mut bit = N >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            a.swap(i, j);
        }
    }
    // butterflies
    let mut len = 2usize;
    while len <= N {
        let step = N / len;
        let half = len / 2;
        let mut start = 0usize;
        while start < N {
            let mut w_idx = 0usize;
            for k in 0..half {
                let u = a[start + k];
                let v = a[start + k + half] * omega_pow[w_idx] % Q;
                a[start + k] = (u + v) % Q;
                a[start + k + half] = (u + Q - v) % Q;
                w_idx += step;
            }
            start += len;
        }
        len <<= 1;
    }
}

impl Poly {
    /// NTT-based negacyclic multiplication — `O(n log n)`, the production-shaped
    /// counterpart of the schoolbook [`Poly::mul`]. Verified to agree with `mul`
    /// bit-for-bit. All intermediate products stay `< Q² < u64::MAX`.
    pub fn mul_ntt(&self, other: &Self) -> Self {
        let t = ntt_tables();
        let mut a = [0u64; N];
        let mut b = [0u64; N];
        for i in 0..N {
            a[i] = (self.coeffs[i] % Q) * t.psi[i] % Q;
            b[i] = (other.coeffs[i] % Q) * t.psi[i] % Q;
        }
        ntt_inplace(&mut a, &t.omega);
        ntt_inplace(&mut b, &t.omega);
        let mut c = [0u64; N];
        for i in 0..N {
            c[i] = a[i] * b[i] % Q;
        }
        ntt_inplace(&mut c, &t.omega_inv);
        let mut coeffs = [0u64; N];
        for i in 0..N {
            coeffs[i] = c[i] * t.n_inv % Q * t.psi_inv[i] % Q;
        }
        Poly { coeffs }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The O(n log n) NTT multiplication agrees with the O(n²) schoolbook `mul`
    /// bit-for-bit over random inputs — the NTT is verified against the reference.
    #[test]
    fn ntt_mul_agrees_with_schoolbook() {
        let mut s = 0x243F_6A88_85A3_08D3u64;
        let mut rnd = || {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (s >> 33) % Q
        };
        for _ in 0..200 {
            let mut a = Poly { coeffs: [0u64; N] };
            let mut b = Poly { coeffs: [0u64; N] };
            for i in 0..N {
                a.coeffs[i] = rnd();
                b.coeffs[i] = rnd();
            }
            assert_eq!(
                a.mul_schoolbook(&b).coeffs,
                a.mul_ntt(&b).coeffs,
                "NTT disagrees with schoolbook"
            );
        }
        // edge cases: one, X (the ring generator)
        let one = Poly::constant(1);
        let mut x = Poly { coeffs: [0u64; N] };
        x.coeffs[1] = 1;
        assert_eq!(x.mul_schoolbook(&one).coeffs, x.mul_ntt(&one).coeffs);
        assert_eq!(x.mul_schoolbook(&x).coeffs, x.mul_ntt(&x).coeffs);
    }

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
