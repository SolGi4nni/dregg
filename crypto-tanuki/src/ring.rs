//! `R_q = ℤ_q[X]/(Xⁿ+1)` — the negacyclic polynomial quotient ring Tanuki is
//! stated over (slide 6: "Power-of-2 cyclotomic ring `R = ℤ[X]/(X^φ+1)`,
//! `R_q = R/qR`").
//!
//! ## Reference parameters (DOCUMENTED, not NIST-audit-grade)
//!
//! * `N = 256` (the power-of-two ring degree; a real deployment dimension),
//! * `Q = 8380417 = 2²³ − 2¹³ + 1` (the Dilithium prime; `2·N | Q−1`, so the
//!   ring is NTT-friendly and negacyclic NTTs exist).
//!
//! Multiplication defaults to the `O(n log n)` NTT ([`Poly::mul_ntt`]),
//! bit-for-bit checked against the obviously-correct `O(n²)` schoolbook
//! ([`Poly::mul_schoolbook`]) by the `ntt_agrees_with_schoolbook` test.
//!
//! ## The rounding operator `⌊·⌉` (the Tanuki-defining primitive)
//!
//! Tanuki's KeyGen rounds the key (`t ← ⌊A·s + e⌉`) and the online round
//! rounds the aggregate (`w ← ⌊W·b⌉`); Raccoon-style verification reconciles
//! the two roundings with a hint `h`. This reference realizes `⌊·⌉` as
//! [`Poly::round_drop`]: round each centered coefficient to the nearest
//! multiple of `2^ν` (`DROP_BITS = ν`). This keeps the scale (so the algebra
//! is exact) while introducing a bounded rounding error `‖x − ⌊x⌉‖∞ ≤ 2^{ν−1}`
//! — exactly the "small" term the hint absorbs. The bandwidth-saving variant
//! (discard low bits, shrinking the modulus) is an explicitly-OPTIONAL Tanuki
//! instantiation (slide 11) and is out of scope for this correctness reference.

use std::sync::OnceLock;

/// Ring degree `n` in `Xⁿ + 1`.
pub const N: usize = 256;

/// Coefficient modulus `q` (the Dilithium prime; `2¹³ | q − 1`).
pub const Q: u64 = 8380417;

/// Number of low bits the rounding operator `⌊·⌉` zeroes (rounds to the nearest
/// multiple of `2^DROP_BITS`). The rounding error is bounded by `2^{DROP_BITS−1}`.
/// A modest reference value: large enough that the key/aggregate are genuinely
/// rounded (the hint mechanism is exercised, not a no-op), small enough that the
/// honest hint stays tiny relative to `q`.
pub const DROP_BITS: u32 = 4;

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
        coeffs[0] = v.rem_euclid(Q);
        Poly { coeffs }
    }

    /// The signed monomial `sign · X^deg` (`sign = ±1`), reduced negacyclically
    /// (`X^N = −1`). The aggregation vector `b` is a vector of these (the EKT24
    /// "signed monomial" instantiation of `b ← G(vk, ssid)`).
    pub fn signed_monomial(sign: i64, deg: usize) -> Self {
        let mut coeffs = [0u64; N];
        // Reduce X^deg negacyclically: X^deg = (−1)^{deg/N} · X^{deg mod N}.
        let mut effective_sign = sign;
        let mut d = deg;
        while d >= N {
            d -= N;
            effective_sign = -effective_sign;
        }
        coeffs[d] = if effective_sign >= 0 { 1 } else { Q - 1 };
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

    /// Ring multiplication (the default): the fast `O(n log n)` NTT path.
    pub fn mul(&self, other: &Self) -> Self {
        self.mul_ntt(other)
    }

    /// Reference NEGACYCLIC convolution, `O(n²)` schoolbook — the index
    /// wraparound `X^N = −1` is the quotient by `Xⁿ + 1`.
    pub fn mul_schoolbook(&self, other: &Self) -> Self {
        let mut acc = [0i64; N];
        for i in 0..N {
            for j in 0..N {
                let p = (self.coeffs[i] * other.coeffs[j]) as i64;
                let k = i + j;
                if k < N {
                    acc[k] += p;
                } else {
                    acc[k - N] -= p; // X^{k} = −X^{k−N}
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
    /// `(−q/2, q/2]` congruent to `coeffs[i]` mod `q`.
    pub fn centered_coeff(&self, i: usize) -> i64 {
        let c = self.coeffs[i];
        if c * 2 > Q {
            c as i64 - Q as i64
        } else {
            c as i64
        }
    }

    /// The L∞ norm in centered representation: `max_i |centered_coeff(i)|`.
    pub fn norm_inf(&self) -> u64 {
        (0..N)
            .map(|i| self.centered_coeff(i).unsigned_abs())
            .max()
            .unwrap_or(0)
    }

    /// Number of nonzero (centered) coefficients — the `ℓ₀` weight. Used to
    /// assert the fixed-weight challenge really has `ω` nonzeros.
    pub fn weight(&self) -> usize {
        (0..N).filter(|&i| self.centered_coeff(i) != 0).count()
    }

    /// The Tanuki rounding `⌊·⌉`: round each CENTERED coefficient to the nearest
    /// multiple of `2^DROP_BITS`, then re-reduce mod `q`. Returns the rounded
    /// element; `self.sub(&self.round_drop())` is the (small) rounding error,
    /// `‖·‖∞ ≤ 2^{DROP_BITS−1}`.
    pub fn round_drop(&self) -> Self {
        let step = 1i64 << DROP_BITS; // 2^ν
        let half = step / 2;
        let mut coeffs = [0u64; N];
        for i in 0..N {
            let x = self.centered_coeff(i);
            // Round to nearest multiple of `step` (ties toward +∞, harmless).
            let q_rounded = (x + half).div_euclid(step) * step;
            coeffs[i] = q_rounded.rem_euclid(Q as i64) as u64;
        }
        Poly { coeffs }
    }

    /// Is this the image of a base-ring constant (used by Shamir's unit check)?
    pub fn is_constant(&self) -> bool {
        self.coeffs[1..].iter().all(|&c| c == 0)
    }

    /// Inverse of a CONSTANT unit (`c ∈ ℤ_q^*` embedded in `R_q`). Every nonzero
    /// constant is a unit in `R_q` (`q` prime), which is exactly what Shamir
    /// reconstruction over `R_q` needs: distinct integer evaluation points give
    /// invertible constant differences `(i − j)`.
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
    Some(pow_mod(a, Q - 2))
}

// ============================================================================
// NTT-based negacyclic multiplication — O(n log n)
// ============================================================================

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

struct NttTables {
    psi: [u64; N],
    psi_inv: [u64; N],
    omega: [u64; N],
    omega_inv: [u64; N],
    n_inv: u64,
}

fn ntt_tables() -> &'static NttTables {
    static T: OnceLock<NttTables> = OnceLock::new();
    T.get_or_init(|| {
        // Primitive 2N-th root: ψᴺ ≡ −1 (mod Q) forces order exactly 2N.
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

/// In-place iterative Cooley–Tukey NTT with the supplied `ωⁱ` power table.
fn ntt_inplace(a: &mut [u64; N], omega_pow: &[u64; N]) {
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
    /// NTT-based negacyclic multiplication — `O(n log n)`, verified to agree with
    /// [`Poly::mul_schoolbook`] bit-for-bit. Intermediate products stay `< Q²`.
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
    fn ntt_agrees_with_schoolbook() {
        for k in 0..100 {
            let a = test_poly(0x1000 + k);
            let b = test_poly(0x2000 + k);
            assert_eq!(a.mul_schoolbook(&b).coeffs, a.mul_ntt(&b).coeffs);
        }
    }

    #[test]
    fn negacyclic_wraparound() {
        let mut x = Poly::ZERO;
        x.coeffs[N - 1] = 1;
        let mut x1 = Poly::ZERO;
        x1.coeffs[1] = 1;
        // X^{N-1}·X = X^N ≡ −1.
        assert_eq!(x.mul(&x1), Poly::constant(Q - 1));
    }

    #[test]
    fn signed_monomial_is_multiplication_by_that_monomial() {
        // b·p where b = ±X^d equals the (negacyclic) shift of p — check against mul.
        let p = test_poly(0xBEEF);
        for &(sign, d) in &[(1i64, 0usize), (1, 5), (-1, 7), (1, N - 1)] {
            let m = Poly::signed_monomial(sign, d);
            let mut explicit = Poly::ZERO;
            explicit.coeffs[d % N] = if sign > 0 { 1 } else { Q - 1 };
            assert_eq!(m.mul(&p), explicit.mul(&p));
        }
    }

    #[test]
    fn ring_laws() {
        let a = test_poly(0xA);
        let b = test_poly(0xB);
        let c = test_poly(0xC);
        assert_eq!(a.mul(&b), b.mul(&a));
        assert_eq!(a.mul(&b).mul(&c), a.mul(&b.mul(&c)));
        assert_eq!(a.mul(&b.add(&c)), a.mul(&b).add(&a.mul(&c)));
        assert_eq!(a.add(&a.neg()), Poly::ZERO);
        assert_eq!(a.mul(&Poly::constant(1)), a);
    }

    #[test]
    fn constant_inversion() {
        for v in [1u64, 2, 13, 1000, Q - 1] {
            let p = Poly::constant(v);
            assert_eq!(p.mul(&p.inverse_constant().unwrap()), Poly::constant(1));
        }
        assert!(Poly::constant(0).inverse_constant().is_none());
    }

    #[test]
    fn rounding_error_is_bounded() {
        let step = 1i64 << DROP_BITS;
        for k in 0..50 {
            let p = test_poly(0x5000 + k);
            let rounded = p.round_drop();
            let err = p.sub(&rounded);
            // ‖x − ⌊x⌉‖∞ ≤ 2^{ν−1}.
            assert!(
                err.norm_inf() <= (step / 2) as u64,
                "rounding error too big"
            );
            // The rounded value's centered coeffs are multiples of 2^ν.
            for i in 0..N {
                assert_eq!(rounded.centered_coeff(i) % step, 0);
            }
        }
    }
}
