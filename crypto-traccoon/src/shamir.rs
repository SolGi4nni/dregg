//! Shamir sharing of the secret `sk` over `R_q` (KeyGen: `(s_1,…,s_N) ←
//! ShamirShare(sk)`; NIST slide "Shamir secret sharing" — `a = Σ_{i∈S} λ_{i,S}
//! · a_i`, `λ_{i,S} = ∏_{j∈S\{i}} j/(i−j)`).
//!
//! `R_q = ℤ_q[X]/(Xⁿ+1)` is NOT a field, but Shamir only needs the differences
//! of the evaluation points to be UNITS. We use the CONSTANT evaluation points
//! `1, 2, …, N ∈ ℤ_q ↪ R_q`; every nonzero constant is a unit in `R_q`
//! (`q` prime), so `(i − j)` is invertible and Lagrange interpolation goes
//! through. The Lagrange coefficients `λ_{i,S}` are therefore CONSTANT
//! polynomials — but the shares `s_i = P(i)` are full, "large" `R_q` elements
//! (`P` is degree `T−1` over `R_q^d` with `P(0) = sk`). This is exactly the
//! regime TRaccoon's masking is designed for: the partial response term
//! `c·λ_{i,S}·s_i` is LARGE (large Lagrange coeff × large share), so the short
//! nonce `r_i` cannot hide it — the one-time additive mask must (NIST slide
//! "Insecure Threshold Raccoon": `r_i` is small whereas `c·λ_i·sk_i` is large).

use crate::linalg::PolyVec;
use crate::ring::{Poly, N};

/// A share: the party index (its evaluation point, `1..=N`) and `P(index)`,
/// a length-`d` vector over `R_q`.
#[derive(Clone, Debug)]
pub struct Share {
    pub index: usize,
    pub value: PolyVec,
}

/// Deterministic sampler for the random Shamir coefficients (full `R_q` — the
/// masking, not the shares, is what carries the hiding). A reference
/// splitmix-style stream keyed by `seed`; FLAG: not a CSPRNG (see the crate
/// boundary doc).
fn rand_polyvec(seed: u64, d: usize) -> PolyVec {
    let mut s = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    let mut next = || {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (s >> 17) % crate::ring::Q
    };
    PolyVec(
        (0..d)
            .map(|_| {
                let mut coeffs = [0u64; N];
                for c in coeffs.iter_mut() {
                    *c = next();
                }
                Poly { coeffs }
            })
            .collect(),
    )
}

/// `T`-of-`n` Shamir-share the length-`d` secret `sk` over `R_q`. The random
/// polynomial coefficients are derived from `coeff_seed` (reference sampler).
/// Returns the `n` shares at evaluation points `1..=n`.
pub fn share(sk: &PolyVec, t: usize, n: usize, coeff_seed: u64) -> Vec<Share> {
    assert!(t >= 1 && t <= n, "need 1 ≤ T ≤ n");
    let d = sk.len();
    // P(x) = sk + a_1 x + … + a_{T-1} x^{T-1}, each a_k ∈ R_q^d random.
    let mut poly_coeffs: Vec<PolyVec> = vec![sk.clone()];
    for k in 1..t {
        poly_coeffs.push(rand_polyvec(coeff_seed.wrapping_add(k as u64), d));
    }
    (1..=n)
        .map(|i| {
            // Horner over the CONSTANT point i (embedded in R_q).
            let x = Poly::constant(i as u64);
            let mut acc = PolyVec::zero(d);
            for a_k in poly_coeffs.iter().rev() {
                acc = acc.scale(&x).add(a_k);
            }
            Share {
                index: i,
                value: acc,
            }
        })
        .collect()
}

/// The Lagrange coefficient `λ_{i,S}` for reconstructing `P(0)` from the set
/// `S` of evaluation points: `λ_{i,S} = ∏_{j∈S, j≠i} (0 − j)/(i − j)`, a
/// CONSTANT polynomial in `R_q`.
pub fn lagrange_coeff(i: usize, set: &[usize]) -> Poly {
    let mut num = Poly::constant(1);
    let mut den = Poly::constant(1);
    for &j in set {
        if j == i {
            continue;
        }
        // (0 − j) and (i − j) as centered constants.
        num = num.mul(&Poly::constant(0).sub(&Poly::constant(j as u64)));
        let diff = if i >= j {
            Poly::constant((i - j) as u64)
        } else {
            Poly::constant(0).sub(&Poly::constant((j - i) as u64))
        };
        den = den.mul(&diff);
    }
    num.mul(
        &den.inverse_constant()
            .expect("distinct points → unit difference"),
    )
}

/// Reconstruct the secret `P(0)` from a subset of shares via
/// `Σ_{i∈S} λ_{i,S} · s_i`. Used in tests to witness `Σ λ_i s_i = sk`.
pub fn reconstruct(shares: &[Share]) -> PolyVec {
    let set: Vec<usize> = shares.iter().map(|s| s.index).collect();
    let d = shares[0].value.len();
    let mut acc = PolyVec::zero(d);
    for sh in shares {
        let lam = lagrange_coeff(sh.index, &set);
        acc = acc.add(&sh.value.scale(&lam));
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    fn secret(seed: u64, d: usize) -> PolyVec {
        rand_polyvec(seed, d)
    }

    #[test]
    fn any_threshold_subset_reconstructs() {
        let sk = secret(0x5EC, 3);
        let shares = share(&sk, 3, 5, 0xC0FFEE);
        // Every 3-subset reconstructs sk exactly.
        for a in 0..5 {
            for b in (a + 1)..5 {
                for c in (b + 1)..5 {
                    let subset = vec![shares[a].clone(), shares[b].clone(), shares[c].clone()];
                    assert_eq!(reconstruct(&subset), sk, "3-subset must reconstruct");
                }
            }
        }
    }

    #[test]
    fn sub_threshold_does_not_reconstruct() {
        let sk = secret(0xBEE, 2);
        let shares = share(&sk, 3, 5, 0xABCD);
        // A 2-subset (with the Lagrange set of just those 2 points) gives the
        // WRONG value — `T=3` genuinely needs 3 points.
        let subset = vec![shares[0].clone(), shares[1].clone()];
        assert_ne!(
            reconstruct(&subset),
            sk,
            "2 of 3-threshold must NOT reconstruct"
        );
    }

    #[test]
    fn lagrange_coeffs_are_constants() {
        let set = vec![2usize, 4, 5];
        for &i in &set {
            assert!(lagrange_coeff(i, &set).is_constant());
        }
    }
}
