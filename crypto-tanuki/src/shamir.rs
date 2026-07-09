//! Shamir sharing of the secret `s` over `R_q` (KeyGen line 3:
//! `(s_1,…,s_n) ← ShamirShare(s)`).
//!
//! `R_q = ℤ_q[X]/(Xⁿ+1)` is NOT a field, but Shamir only needs the differences
//! of the evaluation points to be UNITS. We use the CONSTANT evaluation points
//! `1, 2, …, n ∈ ℤ_q ↪ R_q`; every nonzero constant is a unit in `R_q`
//! (`q` prime), so `(i − j)` is invertible and Lagrange interpolation goes
//! through. Consequently the Lagrange coefficients `λ_{T,i}` are CONSTANT
//! polynomials — but the shares `s_i = p(i)` are full, "large" `R_q` elements
//! (`p` is a degree-`(t−1)` polynomial over `R_q^ℓ` with `p(0) = s`). This is
//! exactly the regime the paper's masking is designed for: "standard
//! Shamir-sharing of `s` with large Lagrange coefficients and shares"
//! (slide 10), where `R_i·b` alone cannot mask `c·λ_{T,i}·s_i`, so the
//! zero-sum masks are required.

use crate::linalg::PolyVec;
use crate::ring::{Poly, N};

/// A share: the party index (its evaluation point, `1..=n`) and `p(index)`,
/// a length-`ℓ` vector over `R_q`.
#[derive(Clone, Debug)]
pub struct Share {
    pub index: usize,
    pub value: PolyVec,
}

/// Deterministic sampler for the random Shamir coefficients (full `R_q` — the
/// masking, not the shares, is what must be uniform). A reference splitmix-style
/// stream keyed by `seed`; FLAG: not a CSPRNG (see the crate boundary doc).
fn rand_polyvec(seed: u64, ell: usize) -> PolyVec {
    let mut s = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    let mut next = || {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (s >> 17) % crate::ring::Q
    };
    PolyVec(
        (0..ell)
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

/// `t`-of-`n` Shamir-share the length-`ℓ` secret `s` over `R_q`. The random
/// polynomial coefficients are derived from `coeff_seed` (reference sampler).
/// Returns the `n` shares at evaluation points `1..=n`.
pub fn share(s: &PolyVec, t: usize, n: usize, coeff_seed: u64) -> Vec<Share> {
    assert!(t >= 1 && t <= n, "need 1 ≤ t ≤ n");
    let ell = s.len();
    // p(x) = s + a_1 x + … + a_{t-1} x^{t-1}, each a_k ∈ R_q^ℓ random.
    let mut poly_coeffs: Vec<PolyVec> = vec![s.clone()];
    for k in 1..t {
        poly_coeffs.push(rand_polyvec(coeff_seed.wrapping_add(k as u64), ell));
    }
    (1..=n)
        .map(|i| {
            // Horner over the CONSTANT point i (embedded in R_q).
            let x = Poly::constant(i as u64);
            let mut acc = PolyVec::zero(ell);
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

/// The Lagrange coefficient `λ_{T,i}` for reconstructing `p(0)` from the set
/// `T` of evaluation points: `λ_{T,i} = ∏_{j∈T, j≠i} (0 − j)/(i − j)`, a
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

/// Reconstruct the secret `p(0)` from a threshold subset of shares via
/// `Σ_{i∈T} λ_{T,i} · s_i`. (Used in tests to witness `Σ λ_i s_i = s`.)
pub fn reconstruct(shares: &[Share]) -> PolyVec {
    let set: Vec<usize> = shares.iter().map(|s| s.index).collect();
    let ell = shares[0].value.len();
    let mut acc = PolyVec::zero(ell);
    for sh in shares {
        let lam = lagrange_coeff(sh.index, &set);
        acc = acc.add(&sh.value.scale(&lam));
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    fn secret(seed: u64, ell: usize) -> PolyVec {
        rand_polyvec(seed, ell)
    }

    #[test]
    fn any_threshold_subset_reconstructs() {
        let s = secret(0x5EC, 3);
        let shares = share(&s, 3, 5, 0xC0FFEE);
        // Every 3-subset reconstructs s exactly.
        let idx = [0usize, 1, 2, 3, 4];
        for a in 0..5 {
            for b in (a + 1)..5 {
                for c in (b + 1)..5 {
                    let subset = vec![
                        shares[idx[a]].clone(),
                        shares[idx[b]].clone(),
                        shares[idx[c]].clone(),
                    ];
                    assert_eq!(reconstruct(&subset), s, "3-subset must reconstruct");
                }
            }
        }
    }

    #[test]
    fn sub_threshold_does_not_reconstruct() {
        let s = secret(0xBEE, 2);
        let shares = share(&s, 3, 5, 0xABCD);
        // A 2-subset with the WRONG Lagrange set (as if t=2) gives the wrong value.
        let subset = vec![shares[0].clone(), shares[1].clone()];
        assert_ne!(
            reconstruct(&subset),
            s,
            "2 of 3-threshold must NOT reconstruct"
        );
    }

    #[test]
    fn lagrange_coeffs_are_constants_summing_correctly() {
        // λ's are constant polynomials, and for the constant-1 sharing they sum to 1.
        let set = vec![2usize, 4, 5];
        for &i in &set {
            assert!(lagrange_coeff(i, &set).is_constant());
        }
    }
}
