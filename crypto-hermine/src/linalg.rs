//! Module elements and the public matrix over `R_q`.
//!
//! The Lean spec is stated over abstract `R`-modules `M`, `N` and an
//! `R`-linear map `A : M →ₗ[R] N`. This reference instantiates
//! `M = R_q^cols`, `N = R_q^rows`, and `A` as a `rows × cols` matrix over
//! `R_q` acting by matrix–vector multiplication (which IS `R_q`-linear).

use crate::ring::Poly;

/// A module element: a vector over `R_q` (the Lean `M`/`N` carriers).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PolyVec(pub Vec<Poly>);

impl PolyVec {
    /// The zero vector of the given length.
    pub fn zero(len: usize) -> Self {
        PolyVec(vec![Poly::ZERO; len])
    }

    /// Vector length (module rank).
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the vector is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Componentwise addition. Panics on mismatched lengths (a caller bug).
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len(), "PolyVec length mismatch in add");
        PolyVec(
            self.0
                .iter()
                .zip(other.0.iter())
                .map(|(a, b)| a.add(b))
                .collect(),
        )
    }

    /// Componentwise subtraction. Panics on mismatched lengths.
    pub fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len(), "PolyVec length mismatch in sub");
        PolyVec(
            self.0
                .iter()
                .zip(other.0.iter())
                .map(|(a, b)| a.sub(b))
                .collect(),
        )
    }

    /// Scalar action of the ring on the module: `c • v`, componentwise
    /// `R_q`-multiplication — the Lean `•` (`SMul R M`).
    pub fn scale(&self, c: &Poly) -> Self {
        PolyVec(self.0.iter().map(|a| c.mul(a)).collect())
    }

    /// The L∞ norm of the vector in centered representation: the max of
    /// [`Poly::norm_inf`] over the components — the module-level shortness
    /// carrier (see `Poly::norm_inf` for why a bound needs to be `< ⌊q/2⌋`
    /// to say anything).
    pub fn norm_inf(&self) -> u64 {
        self.0.iter().map(Poly::norm_inf).max().unwrap_or(0)
    }
}

/// The public matrix `A`: `rows × cols` over `R_q`, row-major.
///
/// Its action [`Matrix::mul_vec`] is the Lean `A : M →ₗ[R] N`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Matrix {
    /// Number of rows (`k`; the rank of the codomain `N = R_q^k`).
    pub rows: usize,
    /// Number of columns (`ℓ`; the rank of the domain `M = R_q^ℓ`).
    pub cols: usize,
    entries: Vec<Poly>,
}

impl Matrix {
    /// Build a matrix from a row-major entry generator.
    pub fn from_fn(rows: usize, cols: usize, mut f: impl FnMut(usize, usize) -> Poly) -> Self {
        let mut entries = Vec::with_capacity(rows * cols);
        for r in 0..rows {
            for c in 0..cols {
                entries.push(f(r, c));
            }
        }
        Matrix {
            rows,
            cols,
            entries,
        }
    }

    /// Entry at `(row, col)`.
    pub fn entry(&self, row: usize, col: usize) -> &Poly {
        &self.entries[row * self.cols + col]
    }

    /// The linear map: `A·v` by matrix–vector multiplication over `R_q`.
    /// Panics if `v.len() != cols` (a caller bug, not an input to validate).
    pub fn mul_vec(&self, v: &PolyVec) -> PolyVec {
        assert_eq!(v.len(), self.cols, "Matrix·vector dimension mismatch");
        let mut out = Vec::with_capacity(self.rows);
        for r in 0..self.rows {
            let mut acc = Poly::ZERO;
            for c in 0..self.cols {
                acc = acc.add(&self.entry(r, c).mul(&v.0[c]));
            }
            out.push(acc);
        }
        PolyVec(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::{Poly, N, Q};

    fn poly(seed: u64) -> Poly {
        let mut coeffs = [0u64; N];
        let mut s = seed;
        for c in coeffs.iter_mut() {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *c = (s >> 20) % Q;
        }
        Poly { coeffs }
    }

    #[test]
    fn matrix_action_is_linear() {
        // The instantiation must actually BE the Lean hypothesis:
        // A(u + v) = A u + A v and A(c • v) = c • A v.
        let a = Matrix::from_fn(2, 3, |r, c| poly((r * 3 + c) as u64 + 1));
        let u = PolyVec(vec![poly(100), poly(101), poly(102)]);
        let v = PolyVec(vec![poly(200), poly(201), poly(202)]);
        let c = poly(300);
        assert_eq!(a.mul_vec(&u.add(&v)), a.mul_vec(&u).add(&a.mul_vec(&v)));
        assert_eq!(a.mul_vec(&u.scale(&c)), a.mul_vec(&u).scale(&c));
        assert_eq!(a.mul_vec(&PolyVec::zero(3)), PolyVec::zero(2));
    }
}
