//! The three random oracles Tanuki names, realized with blake3, plus the
//! reference small-element samplers:
//!
//! * [`agg_vector`]  — `b ← G(vk, ssid)` (slide 10 line 2). The EKT24
//!   "signed monomial" instantiation: `b ∈ R_q^{rep}`, each component `±X^d`.
//!   `ssid = (T, {W_j}_{j∈T}, m)` binds the session, so a swapped `W_j`
//!   changes `b`.
//! * [`challenge`]   — `c ← H(vk, m, w)` (slide 10 line 5). A FIXED-WEIGHT
//!   ternary challenge: exactly `ω` nonzero coefficients, each `±1`
//!   (`‖c‖∞ = 1`, `‖c‖₀ = ω`) — the sparse ternary challenge space `C ⊂ R`.
//! * [`mask_prf`] / [`mask_gen`] — `m_i ← MaskGen(sd_i, ssid)` (slide 10 line
//!   6). Pairwise PRF masks that sum to zero over the signer set `T`
//!   (`Σ_{j∈T} m_j = 0`), realized from the pairwise seeds `sd_{i,j}`.
//!
//! FLAG (reference sampler): the small-element sampler [`sample_small`] draws
//! coefficients in `[−η, η]` by reducing XOF bytes mod `2η+1` — slightly biased
//! and not constant-time. Production Tanuki uses discrete-Gaussian (or
//! sum-of-uniform) samplers whose exactness feeds the Hint-MLWE reduction
//! [KLSS23]; see the crate boundary doc.

use crate::linalg::PolyVec;
use crate::ring::{Poly, N, Q};

/// A blake3 XOF reader over a domain tag and a sequence of byte chunks.
fn xof(domain: &str, parts: &[&[u8]]) -> blake3::OutputReader {
    let mut h = blake3::Hasher::new();
    h.update(domain.as_bytes());
    for p in parts {
        // length-prefix each part so concatenation is injective (no ambiguity).
        h.update(&(p.len() as u64).to_le_bytes());
        h.update(p);
    }
    h.finalize_xof()
}

fn next_u64(r: &mut blake3::OutputReader) -> u64 {
    use std::io::Read;
    let mut b = [0u8; 8];
    r.read_exact(&mut b).unwrap();
    u64::from_le_bytes(b)
}

/// Sample a length-`len` vector of "small" `R_q` elements: each coefficient is
/// drawn from `[−eta, eta]`. Deterministic from `(domain, seed)`.
pub fn sample_small(domain: &str, seed: &[u8], len: usize, eta: u64) -> PolyVec {
    let mut r = xof(domain, &[seed]);
    let modulus = 2 * eta + 1;
    PolyVec(
        (0..len)
            .map(|_| {
                let mut coeffs = [0u64; N];
                for c in coeffs.iter_mut() {
                    let v = next_u64(&mut r) % modulus; // in [0, 2eta]
                    let centered = v as i64 - eta as i64; // in [-eta, eta]
                    *c = centered.rem_euclid(Q as i64) as u64;
                }
                Poly { coeffs }
            })
            .collect(),
    )
}

/// Sample a length-`rows*cols` set of small `R_q` elements as a flat vector, in
/// row-major order (used to fill `R_i ∈ R_q^{ℓ×rep}` and `E_i ∈ R_q^{k×rep}`).
pub fn sample_small_flat(domain: &str, seed: &[u8], count: usize, eta: u64) -> Vec<Poly> {
    sample_small(domain, seed, count, eta).0
}

/// A uniform `R_q^{len}` vector from `(domain, seed)` — used for the masks,
/// which must be uniform to statistically hide the large `c·λ_{T,i}·s_i` term.
pub fn sample_uniform(domain: &str, seed: &[u8], len: usize) -> PolyVec {
    let mut r = xof(domain, &[seed]);
    PolyVec(
        (0..len)
            .map(|_| {
                let mut coeffs = [0u64; N];
                for c in coeffs.iter_mut() {
                    *c = next_u64(&mut r) % Q;
                }
                Poly { coeffs }
            })
            .collect(),
    )
}

/// `b ← G(vk, ssid)`: the aggregation vector, `rep` signed monomials `±X^d`.
pub fn agg_vector(vk: &[u8], ssid: &[u8], rep: usize) -> PolyVec {
    let mut r = xof("tanuki/G/agg-vector", &[vk, ssid]);
    PolyVec(
        (0..rep)
            .map(|_| {
                let raw = next_u64(&mut r);
                let deg = (raw >> 1) as usize % N;
                let sign = if raw & 1 == 0 { 1 } else { -1 };
                Poly::signed_monomial(sign, deg)
            })
            .collect(),
    )
}

/// `c ← H(vk, m, w)`: a fixed-weight ternary challenge with exactly `omega`
/// nonzero coefficients, each `±1`. `‖c‖∞ = 1`, `‖c‖₀ = omega`.
pub fn challenge(vk: &[u8], msg: &[u8], w: &[u8], omega: usize) -> Poly {
    assert!(omega <= N, "challenge weight cannot exceed N");
    let mut r = xof("tanuki/H/challenge", &[vk, msg, w]);
    let mut coeffs = [0u64; N];
    let mut placed = 0;
    // Fisher–Yates-style: place omega ±1's into distinct positions.
    while placed < omega {
        let raw = next_u64(&mut r);
        let pos = (raw >> 1) as usize % N;
        if coeffs[pos] == 0 {
            coeffs[pos] = if raw & 1 == 0 { 1 } else { Q - 1 };
            placed += 1;
        }
    }
    Poly { coeffs }
}

/// The pairwise PRF: `PRF(sd_{i,j}, ssid) ∈ R_q^ℓ`, uniform. Symmetric in the
/// SEED (both parties `i,j` share `sd_{i,j}`), so both derive the same value.
pub fn mask_prf(pairwise_seed: &[u8], ssid: &[u8], ell: usize) -> PolyVec {
    let mut buf = Vec::with_capacity(pairwise_seed.len() + ssid.len());
    buf.extend_from_slice(pairwise_seed);
    buf.extend_from_slice(ssid);
    sample_uniform("tanuki/PRF/mask", &buf, ell)
}

/// `m_i ← MaskGen(sd_i, ssid)` for party `i` over the signer set `set`:
///
/// `m_i = Σ_{j∈set, j≠i} sign(i,j) · PRF(sd_{i,j}, ssid)`,  `sign(i,j)=+1 if i<j else −1`.
///
/// Because `sd_{i,j}=sd_{j,i}` and the signs are antisymmetric, the `{i,j}`
/// pair contributes `+PRF` to `m_i` and `−PRF` to `m_j`, so `Σ_{i∈set} m_i = 0`.
pub fn mask_gen(
    i: usize,
    set: &[usize],
    pairwise_seed: &dyn Fn(usize, usize) -> Vec<u8>,
    ssid: &[u8],
    ell: usize,
) -> PolyVec {
    let mut acc = PolyVec::zero(ell);
    for &j in set {
        if j == i {
            continue;
        }
        let seed = pairwise_seed(i, j);
        let contrib = mask_prf(&seed, ssid, ell);
        if i < j {
            acc = acc.add(&contrib);
        } else {
            acc = acc.sub(&contrib);
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge_is_fixed_weight_ternary() {
        let c = challenge(b"vk", b"msg", b"w", 30);
        assert_eq!(c.norm_inf(), 1, "challenge is ternary ‖c‖∞ = 1");
        assert_eq!(c.weight(), 30, "challenge has exactly ω nonzeros");
    }

    #[test]
    fn agg_vector_components_are_signed_monomials() {
        let b = agg_vector(b"vk", b"ssid", 4);
        assert_eq!(b.len(), 4);
        for comp in &b.0 {
            assert_eq!(comp.norm_inf(), 1);
            assert_eq!(comp.weight(), 1, "signed monomial has a single ±1 coeff");
        }
    }

    #[test]
    fn masks_sum_to_zero_over_the_set() {
        // Pairwise seed: deterministic function of the unordered pair.
        let pw = |i: usize, j: usize| {
            let (a, b) = if i < j { (i, j) } else { (j, i) };
            format!("seed-{a}-{b}").into_bytes()
        };
        let set = vec![2usize, 3, 5];
        let ell = 3;
        let mut total = PolyVec::zero(ell);
        for &i in &set {
            total = total.add(&mask_gen(i, &set, &pw, b"ssid-xyz", ell));
        }
        assert_eq!(total, PolyVec::zero(ell), "Σ_{{i∈T}} m_i must be 0");
    }

    #[test]
    fn ssid_changes_the_aggregation_vector() {
        let b1 = agg_vector(b"vk", b"ssid-A", 4);
        let b2 = agg_vector(b"vk", b"ssid-B", 4);
        assert_ne!(b1, b2, "different ssid → different b");
    }
}
