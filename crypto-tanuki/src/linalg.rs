//! Module elements over `R_q`: vectors ([`PolyVec`]) and matrices
//! ([`PolyMatrix`]). Tanuki works with several shapes:
//!
//! * the public matrix `A ∈ R_q^{k×ℓ}`,
//! * the WIDE commitment `W_i ∈ R_q^{k×rep}` (`rep` "replication" columns — the
//!   in-the-clear rep-column MLWE commitment, slide 10 `W_i ∈ R_q^{k×rep}`),
//! * the signer randomness `R_i ∈ R_q^{ℓ×rep}`, error `E_i ∈ R_q^{k×rep}`,
//! * the aggregation vector `b ∈ R_q^{rep}` (so `W·b ∈ R_q^k`, `R_i·b ∈ R_q^ℓ`).

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
    /// Coefficientwise rounding `⌊v⌉` — the vector lift of [`Poly::round_drop`].
    pub fn round_drop(&self) -> Self {
        PolyVec(self.0.iter().map(Poly::round_drop).collect())
    }
    /// L∞ norm over all components.
    pub fn norm_inf(&self) -> u64 {
        self.0.iter().map(Poly::norm_inf).max().unwrap_or(0)
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
    pub fn zero(rows: usize, cols: usize) -> Self {
        PolyMatrix::from_fn(rows, cols, |_, _| Poly::ZERO)
    }
    pub fn entry(&self, r: usize, c: usize) -> &Poly {
        &self.entries[r * self.cols + c]
    }
    pub fn set(&mut self, r: usize, c: usize, v: Poly) {
        self.entries[r * self.cols + c] = v;
    }
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(
            (self.rows, self.cols),
            (other.rows, other.cols),
            "matrix add shape mismatch"
        );
        PolyMatrix {
            rows: self.rows,
            cols: self.cols,
            entries: self
                .entries
                .iter()
                .zip(&other.entries)
                .map(|(a, b)| a.add(b))
                .collect(),
        }
    }
    /// `A·B` for a `rows×inner` times `inner×cols`.
    pub fn matmul(&self, other: &Self) -> Self {
        assert_eq!(self.cols, other.rows, "matmul inner-dim mismatch");
        PolyMatrix::from_fn(self.rows, other.cols, |r, c| {
            let mut acc = Poly::ZERO;
            for k in 0..self.cols {
                acc = acc.add(&self.entry(r, k).mul(other.entry(k, c)));
            }
            acc
        })
    }
    /// `A·v` (matrix times column vector).
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
    /// Coefficientwise rounding `⌊M⌉`.
    pub fn round_drop(&self) -> Self {
        PolyMatrix {
            rows: self.rows,
            cols: self.cols,
            entries: self.entries.iter().map(Poly::round_drop).collect(),
        }
    }
    /// Byte encoding of every coefficient (little-endian u64s), row-major — the
    /// stable serialization the random oracles hash a matrix through (ssid binds
    /// the `W_j`'s via this).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.entries.len() * crate::ring::N * 8);
        for p in &self.entries {
            for &c in &p.coeffs {
                out.extend_from_slice(&c.to_le_bytes());
            }
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

    #[test]
    fn matmul_then_vec_equals_vec_then_vec() {
        // A·(R·b) = (A·R)·b — associativity the signing algebra leans on.
        let a = PolyMatrix::from_fn(2, 3, |r, c| poly((r * 3 + c) as u64 + 1));
        let rr = PolyMatrix::from_fn(3, 2, |r, c| poly((r * 2 + c) as u64 + 50));
        let b = PolyVec(vec![poly(9), poly(10)]);
        assert_eq!(a.matmul(&rr).mul_vec(&b), a.mul_vec(&rr.mul_vec(&b)));
    }
}
