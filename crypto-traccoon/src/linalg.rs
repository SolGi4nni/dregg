//! Module elements over `R_q`: vectors ([`PolyVec`]) and matrices
//! ([`PolyMatrix`]). TRaccoon works with:
//!
//! * the augmented public matrix `Â = [A | I] ∈ R_q^{k×d}` (`d = ℓ+k`) — the
//!   MLWE matrix `A ∈ R_q^{k×ℓ}` with an identity block appended so the error
//!   lives inside the secret (`vk = Â·sk`),
//! * the secret `sk ∈ R_q^d` and its Shamir shares `s_i ∈ R_q^d`,
//! * per-signer nonces `r_i ∈ R_q^d`, commitments `w_i = Â·r_i ∈ R_q^k`,
//! * responses `z_i, z ∈ R_q^d` and additive masks `m_i, m*_i ∈ R_q^d`.

use crate::ring::Poly;

/// A vector over `R_q`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PolyVec(pub Vec<Poly>);

impl PolyVec {
    pub fn zero(len: usize) -> Self {
        PolyVec(vec![Poly::ZERO; len])
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len(), "PolyVec add length mismatch");
        PolyVec(self.0.iter().zip(&other.0).map(|(a, b)| a.add(b)).collect())
    }
    pub fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len(), "PolyVec sub length mismatch");
        PolyVec(self.0.iter().zip(&other.0).map(|(a, b)| a.sub(b)).collect())
    }
    /// Scalar action `c • v` (componentwise `R_q`-multiplication).
    pub fn scale(&self, c: &Poly) -> Self {
        PolyVec(self.0.iter().map(|a| c.mul(a)).collect())
    }
    /// L∞ norm over all components.
    pub fn norm_inf(&self) -> u64 {
        self.0.iter().map(Poly::norm_inf).max().unwrap_or(0)
    }
    /// Little-endian byte encoding, component by component (the stable
    /// serialization the random oracles hash a vector through — the aggregate
    /// `w` is bound into the challenge via this).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for p in &self.0 {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }
}

/// A `rows × cols` matrix over `R_q`, row-major.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PolyMatrix {
    pub rows: usize,
    pub cols: usize,
    entries: Vec<Poly>,
}

impl PolyMatrix {
    pub fn from_fn(rows: usize, cols: usize, mut f: impl FnMut(usize, usize) -> Poly) -> Self {
        let mut entries = Vec::with_capacity(rows * cols);
        for r in 0..rows {
            for c in 0..cols {
                entries.push(f(r, c));
            }
        }
        PolyMatrix {
            rows,
            cols,
            entries,
        }
    }
    pub fn entry(&self, r: usize, c: usize) -> &Poly {
        &self.entries[r * self.cols + c]
    }
    /// `Â·v` (matrix times column vector).
    pub fn mul_vec(&self, v: &PolyVec) -> PolyVec {
        assert_eq!(v.len(), self.cols, "matrix·vector dim mismatch");
        PolyVec(
            (0..self.rows)
                .map(|r| {
                    let mut acc = Poly::ZERO;
                    for c in 0..self.cols {
                        acc = acc.add(&self.entry(r, c).mul(&v.0[c]));
                    }
                    acc
                })
                .collect(),
        )
    }
    /// Byte encoding of every coefficient (row-major) — the serialization used
    /// to bind `Â` into `vk`'s hash.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for p in &self.entries {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(seed: u64) -> Poly {
        let mut coeffs = [0u64; crate::ring::N];
        let mut s = seed;
        for c in coeffs.iter_mut() {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *c = (s >> 20) % crate::ring::Q;
        }
        Poly { coeffs }
    }

    #[test]
    fn matrix_action_is_linear() {
        let a = PolyMatrix::from_fn(2, 3, |r, c| poly((r * 3 + c) as u64 + 1));
        let u = PolyVec(vec![poly(100), poly(101), poly(102)]);
        let v = PolyVec(vec![poly(200), poly(201), poly(202)]);
        let c = poly(300);
        assert_eq!(a.mul_vec(&u.add(&v)), a.mul_vec(&u).add(&a.mul_vec(&v)));
        assert_eq!(a.mul_vec(&u.scale(&c)), a.mul_vec(&u).scale(&c));
    }
}
