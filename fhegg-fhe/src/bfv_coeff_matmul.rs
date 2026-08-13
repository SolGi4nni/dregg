//! ROTATION-FREE coefficient-encoded matrix-vector multiply — public matrix ×
//! encrypted vector, ZERO rotations, ZERO new key material.
//!
//! WHY THIS EXISTS: `notes/fhe-core-theory.md` ("THE INVERSION") measured the
//! slot/BSGS diagonal route at the deployed parameters and found it FAILS the
//! worst-case (provable) noise bound by ~2.9 bits at D=64 under every
//! key-switching variant — it survives only on the heuristic 2√n ring
//! expansion factor. The coefficient-encoding route (Cheetah, eprint 2022/207
//! §3.1 `HomFC`; the agenda note cites it as §4.1) closes with headroom for
//! two structural reasons:
//!   * NO key switch at all — a rotation costs 2^53.91 worst-case noise in
//!     RNS-BV; here there are no rotations, so that term is absent, not bounded.
//!   * the coefficient-encoded plaintext norm is the WEIGHT MAGNITUDE (2^7 for
//!     int8) rather than ~t/2 (2^19) — a flat ~12-bit gift per layer.
//!
//! ⚠ CORRECTION TO THAT SECOND REASON, MEASURED HERE (2026-08-13). The gift does
//! NOT materialize from coefficient encoding alone. `Plaintext` lifts `Z_t` to
//! `R_q` using the residues in `[0, t)`, so a weight of `−1` becomes the
//! coefficient `t − 1 ≈ 2^20` — every NEGATIVE weight is a full-size
//! coefficient, and int8 weights are half negative. Measured at the deployed
//! parameters by the SHIPPED test `measured_plaintext_norm_gift_vs_simd_encoding`
//! — same weights, same ciphertext, fresh noise 12 bits, signed int8:
//!
//! ```text
//!   SIMD-encoded weights                  : 37 bits  (+25)
//!   coefficient-encoded, Direct lift      : 37 bits  (+25)   ← gift ABSENT
//!   coefficient-encoded, SplitSign lift   : 24 bits  (+12)   ← gift recovered
//! ```
//!
//! So the coefficient encoding's raw advantage over SIMD at signed int8 weights
//! is **0 bits, not 12**. The recovery is [`WeightLift::SplitSign`] — evaluate
//! `W·v = W⁺·v − W⁻·v` with both parts NONNEGATIVE, which costs one extra ct×pt
//! multiply per block and no extra capacity: **13 bits** cheaper than SIMD, i.e.
//! the predicted gift, recovered without touching the vendored crate. It is the
//! DEFAULT here. (The alternative — lifting plaintexts with CENTERED
//! representatives in the ct×pt path — is strictly better still, saving the
//! extra multiply too, but lives in `vendor/fhe-dregg`; named, not taken.)
//!
//! The gift's mechanism was isolated in a one-off probe (NOT a shipped test, so
//! treat these as reported, not gated): nonnegative weights coefficient-encoded
//! cost 23 bits while the same magnitudes with signs cost 36, and a plaintext of
//! the single coefficient `−1` costs 32 bits where `+1` costs 0. The sign of the
//! ENCRYPTED vector was probed too and does NOT matter, so there is no
//! corresponding trick to do on the activation side.
//!
//! THE TECHNIQUE (Cheetah Proposition 1). In `A_{N,t} = Z_t[X]/(X^N + 1)`, put
//! the input vector in FORWARD order and the weight row in REVERSED order; the
//! coefficient where the two index ranges cross is exactly their inner product.
//! Packed for a whole block of rows:
//!
//! ```text
//!   v̂[j]                       = v[j]        for j ∈ [0, n_i)
//!   ŵ[i·n_i + (n_i − 1 − j)]   = W[i][j]     for i ∈ [0, n_o), j ∈ [0, n_i)
//!   (û = v̂ · ŵ)  ⇒  û[i·n_i + n_i − 1] = Σ_j v[j]·W[i][j] = (Wv)[i]
//! ```
//!
//! so ONE ciphertext-plaintext multiplication yields `n_o` inner products,
//! subject only to `n_i · n_o ≤ N`. That is the packing this module implements:
//! `n_o` results per polynomial multiply, NOT one. At the deployed N = 4096
//! with inner dim 504 (the 4-bit × 8-bit capacity ceiling, below) that is 8 rows
//! per multiply; with inner dim 31 (the 8-bit × 8-bit ceiling) it is 132.
//!
//! NEGACYCLIC SAFETY IS STRUCTURAL, NOT A HOPE. The wrap term of the product at
//! coefficient k is `−Σ_{a+b=k+N} v̂[a]ŵ[b]`. Here `a < n_i` and
//! `b < n_i·n_o ≤ N`, so `max(a+b) = n_i·n_o + n_i − 2 ≤ N + n_i − 2`, while
//! every extraction index satisfies `k + N ≥ N + n_i − 1`. Strict inequality:
//! **no negacyclic wrap can ever reach an extraction index.** The same
//! inequality shows the forward terms at index `i·n_i + n_i − 1` are exactly
//! row `i`'s window — no cross-row contamination either. (Test:
//! `no_negacyclic_contamination_at_extraction_indices`.)
//!
//! THE CAPACITY CONSTRAINT IS REAL AND IS ENFORCED. Coefficient arithmetic is
//! over `Z_t`, so an inner product whose true integer value leaves
//! `(−t/2, t/2)` wraps SILENTLY — a well-formed WRONG number, the class-(C)
//! hazard of `bfv_mul.rs` in its additive form. With `|W| ≤ 2^(w−1)` and
//! `|v| ≤ 2^(a−1)` the exact ceiling is
//!
//! ```text
//!   inner_dim · 2^(w−1) · 2^(a−1) ≤ (t − 1)/2
//! ```
//!
//! which at the deployed t = 1032193 gives inner dim ≤ **31** for 8-bit
//! weights × 8-bit activations, ≤ **504** for 4-bit × 8-bit, and ≤ **8064** for
//! 4-bit × 4-bit. [`MatmulPlan::new`] REFUSES outside it and names the numbers;
//! [`MatmulPlan::encode_vector`] / [`MatmulPlan::encode_matrix`] additionally
//! verify that the DECLARED bounds actually hold of the data, so the declared
//! bound cannot be a lie (unlike `bfv_mul`'s `BoundedCiphertext`, whose bound is
//! declared-not-checked — here both operands are available in the clear at
//! encode time, the matrix publicly and the vector on the client before
//! encryption).
//!
//! ⚠ 31 IS SMALL. At full int8 × int8 this packing carries an inner dimension
//! of 31, which is not a useful neural-network layer width. The honest reading
//! is that the deployed 20-bit `t` — not the technique — is what binds; see the
//! module tests and the lane report for the quantization ladder. Nothing here
//! quietly downgrades to 4-bit: the caller states the bit widths and the plan
//! refuses or does not.
//!
//! WHAT THIS MODULE DOES NOT DO (the honesty ledger):
//! * **No LWE `Extract`.** Cheetah's step 5 extracts an LWE ciphertext per
//!   output coefficient, which both compresses the reply and DESTROYS the
//!   non-extraction coefficients (they leak `v` against a public `W` in the 2PC
//!   setting). We return the whole RLWE ciphertext, so the decryptor sees the
//!   junk coefficients too. That is sound in the model this module is written
//!   for — the decryptor is the vector's owner, who could compute every
//!   coefficient from `v` and the public `W` anyway — and UNSOUND if the output
//!   is ever routed to a party that must not learn `v`. Extract is the named
//!   next stone.
//! * **No re-masking / no 2PC.** Cheetah's `r` share and the `b − ⌊p·r/q⌉`
//!   output-share step are absent; this is a one-sided homomorphic evaluation.
//! * **No LZ/Bae PC-MM (2024/1284) ct×ct or plaintext-GEMM batching.** This is
//!   the ct-vector × pt-matrix shape only.
//! * **No noise THEOREM.** The noise consumed is MEASURED here (see
//!   `tests/bfv_coeff_matmul_oracle.rs`), not proven. `metatheory/Bfv/Noise.lean`
//!   carries `matVecCt`/`RowBound`/`step_noise_le` — the right theorem shape for
//!   exactly this route — over a SCALAR model; the ring lift is that lane's work
//!   and is not claimed here.

use std::fmt;
use std::sync::Arc;

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext};
use fhe_traits::FheEncoder;

/// Errors — every refusal is loud and NAMES what was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoeffMatmulError {
    /// The declared operand magnitudes make a silent mod-t wrap POSSIBLE at the
    /// requested inner dimension. Refused before any encoding happens.
    CapacityExceeded {
        inner_dim: usize,
        weight_abs_bound: u64,
        activation_abs_bound: u64,
        /// `inner_dim · weight_abs_bound · activation_abs_bound`.
        worst_case_magnitude: u128,
        /// `(t − 1)/2`, the largest magnitude the centered representation holds.
        capacity: u128,
        plaintext_modulus: u64,
    },
    /// A weight exceeded the bound the plan was built against — the plan's
    /// capacity check was therefore computed on a false premise.
    WeightExceedsDeclaredBound {
        row: usize,
        col: usize,
        value: i64,
        declared_bound: u64,
    },
    /// An activation exceeded the bound the plan was built against.
    ActivationExceedsDeclaredBound {
        index: usize,
        value: i64,
        declared_bound: u64,
    },
    /// The chosen packing window does not fit one polynomial: `n_i · n_o > N`.
    WindowExceedsDegree {
        inner_window: usize,
        outer_window: usize,
        degree: usize,
    },
    /// A zero-sized window/shape was requested.
    ZeroDimension { what: &'static str },
    /// The matrix handed to `encode_matrix` does not have the plan's shape.
    MatrixShapeMismatch {
        expected_rows: usize,
        expected_cols: usize,
        found_rows: usize,
        found_cols: usize,
    },
    /// The vector handed to `encode_vector` does not have the plan's inner dim.
    VectorLengthMismatch { expected: usize, found: usize },
    /// The ciphertext count does not match the plan's input-block count.
    CiphertextCountMismatch { expected: usize, found: usize },
    /// A decrypted coefficient vector was shorter than the degree.
    ShortDecoding { expected: usize, found: usize },
    /// An underlying fhe.rs operation failed (its error text carried through).
    Fhe(String),
}

impl fmt::Display for CoeffMatmulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityExceeded {
                inner_dim,
                weight_abs_bound,
                activation_abs_bound,
                worst_case_magnitude,
                capacity,
                plaintext_modulus,
            } => write!(
                f,
                "coefficient-encoding capacity exceeded: inner_dim {inner_dim} × |w| \
                 {weight_abs_bound} × |v| {activation_abs_bound} = {worst_case_magnitude} > \
                 (t−1)/2 = {capacity} at t = {plaintext_modulus}; an inner product could wrap \
                 mod t silently"
            ),
            Self::WeightExceedsDeclaredBound {
                row,
                col,
                value,
                declared_bound,
            } => write!(
                f,
                "weight W[{row}][{col}] = {value} exceeds the declared bound {declared_bound} the \
                 capacity check was computed against"
            ),
            Self::ActivationExceedsDeclaredBound {
                index,
                value,
                declared_bound,
            } => write!(
                f,
                "activation v[{index}] = {value} exceeds the declared bound {declared_bound} the \
                 capacity check was computed against"
            ),
            Self::WindowExceedsDegree {
                inner_window,
                outer_window,
                degree,
            } => write!(
                f,
                "packing window {inner_window} × {outer_window} = {} exceeds the ring degree \
                 {degree}; one block must fit one polynomial",
                inner_window * outer_window
            ),
            Self::ZeroDimension { what } => write!(f, "zero {what} refused"),
            Self::MatrixShapeMismatch {
                expected_rows,
                expected_cols,
                found_rows,
                found_cols,
            } => write!(
                f,
                "matrix shape mismatch: plan is {expected_rows}×{expected_cols}, got \
                 {found_rows}×{found_cols}"
            ),
            Self::VectorLengthMismatch { expected, found } => write!(
                f,
                "vector length mismatch: plan inner dim is {expected}, got {found}"
            ),
            Self::CiphertextCountMismatch { expected, found } => write!(
                f,
                "ciphertext count mismatch: plan needs {expected} input blocks, got {found}"
            ),
            Self::ShortDecoding { expected, found } => write!(
                f,
                "decoded coefficient vector too short: expected {expected}, got {found}"
            ),
            Self::Fhe(e) => write!(f, "fhe.rs operation failed: {e}"),
        }
    }
}

impl std::error::Error for CoeffMatmulError {}

type Result<T> = std::result::Result<T, CoeffMatmulError>;

/// The largest inner dimension a coefficient-encoded inner product can carry at
/// plaintext modulus `t` given per-operand ABSOLUTE magnitude bounds — i.e. the
/// largest `c` with `c · weight_abs_bound · activation_abs_bound ≤ (t − 1)/2`.
///
/// Returns 0 when even a single term overflows the centered range.
pub fn max_inner_dim_bounded(t: u64, weight_abs_bound: u64, activation_abs_bound: u64) -> usize {
    let per_term = (weight_abs_bound as u128) * (activation_abs_bound as u128);
    if per_term == 0 {
        return usize::MAX;
    }
    let capacity = ((t as u128) - 1) / 2;
    (capacity / per_term).min(usize::MAX as u128) as usize
}

/// The bit-width flavour of [`max_inner_dim_bounded`]: signed `w`-bit weights
/// (`|W| ≤ 2^(w−1)`) against signed `a`-bit activations (`|v| ≤ 2^(a−1)`).
///
/// At the deployed t = 1032193 this is the quantization ladder the lane brief
/// derives: `(8, 8) → 31`, `(4, 8) → 504`, `(4, 4) → 8064`.
pub fn max_inner_dim(t: u64, weight_bits: u32, activation_bits: u32) -> usize {
    max_inner_dim_bounded(
        t,
        signed_abs_bound(weight_bits),
        signed_abs_bound(activation_bits),
    )
}

/// `|x| ≤ 2^(bits−1)` for a signed `bits`-wide quantized value. `bits = 0` maps
/// to 0 (the only representable value is zero).
pub fn signed_abs_bound(bits: u32) -> u64 {
    if bits == 0 {
        0
    } else {
        1u64 << (bits - 1)
    }
}

/// How the public weights are lifted from `Z_t` into `R_q` for the
/// ciphertext-plaintext multiply. This is a NOISE choice, not a correctness
/// one — both modes compute the same answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum WeightLift {
    /// One plaintext per block, weights handed to `Encoding::poly()` as-is.
    /// `fhe.rs` reduces them into `[0, t)`, so every NEGATIVE weight becomes a
    /// coefficient of size ~`t` and the small-plaintext-norm advantage of
    /// coefficient encoding is LOST (measured: 36 bits, versus 37 for SIMD).
    /// Kept so the comparison in `tests/bfv_coeff_matmul_oracle.rs` is real.
    Direct,
    /// `W = W⁺ − W⁻` with both parts NONNEGATIVE: two plaintexts per block and
    /// one homomorphic subtraction, so every plaintext coefficient really is a
    /// weight magnitude. MEASURED 13 bits cheaper than [`WeightLift::Direct`]
    /// and 14 cheaper than SIMD, for one extra ct×pt multiply per block and no
    /// extra plaintext capacity (`W⁺` and `W⁻` have disjoint support, so each
    /// partial inner product is bounded by the same `c·|w|·|v|`).
    #[default]
    SplitSign,
}

/// A checked Cheetah packing for one `rows × inner_dim` public matrix against
/// one encrypted `inner_dim`-vector at a fixed ring degree.
///
/// Blocking (Cheetah Figure 2 steps 1/3): the inner dimension is cut into
/// `input_blocks = ceil(inner_dim / inner_window)` windows and the rows into
/// `output_blocks = ceil(rows / outer_window)` windows, with
/// `inner_window · outer_window ≤ N`. Zero padding fills the ragged last
/// window in each direction. Evaluation costs `input_blocks × output_blocks`
/// ciphertext-plaintext multiplications and `input_blocks` ciphertexts of input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatmulPlan {
    degree: usize,
    rows: usize,
    inner_dim: usize,
    inner_window: usize,
    outer_window: usize,
    weight_abs_bound: u64,
    activation_abs_bound: u64,
    plaintext_modulus: u64,
    weight_lift: WeightLift,
}

impl MatmulPlan {
    /// Build a plan with the DEFAULT window choice: take the whole inner
    /// dimension in one window when it fits the degree (fewest ciphertexts,
    /// fewest multiplications), and fill the rest of the polynomial with rows.
    ///
    /// Refuses if the declared magnitudes admit a silent mod-t wrap.
    pub fn new(
        params: &Arc<BfvParameters>,
        rows: usize,
        inner_dim: usize,
        weight_abs_bound: u64,
        activation_abs_bound: u64,
    ) -> Result<Self> {
        let degree = params.degree();
        let (inner_window, outer_window) = default_windows(degree, rows, inner_dim)?;
        Self::with_windows(
            params,
            rows,
            inner_dim,
            inner_window,
            outer_window,
            weight_abs_bound,
            activation_abs_bound,
        )
    }

    /// Build a plan with explicit packing windows. Cheetah leaves `n_i^w` and
    /// `n_o^w` free public parameters subject to `n_i^w · n_o^w ≤ N`; this is
    /// that knob.
    pub fn with_windows(
        params: &Arc<BfvParameters>,
        rows: usize,
        inner_dim: usize,
        inner_window: usize,
        outer_window: usize,
        weight_abs_bound: u64,
        activation_abs_bound: u64,
    ) -> Result<Self> {
        let degree = params.degree();
        if rows == 0 {
            return Err(CoeffMatmulError::ZeroDimension { what: "row count" });
        }
        if inner_dim == 0 {
            return Err(CoeffMatmulError::ZeroDimension {
                what: "inner dimension",
            });
        }
        if inner_window == 0 || outer_window == 0 {
            return Err(CoeffMatmulError::ZeroDimension {
                what: "packing window",
            });
        }
        if inner_window
            .checked_mul(outer_window)
            .is_none_or(|p| p > degree)
        {
            return Err(CoeffMatmulError::WindowExceedsDegree {
                inner_window,
                outer_window,
                degree,
            });
        }
        let t = params.plaintext();

        // THE CAPACITY GATE. Note it is checked against `inner_dim`, the FULL
        // contracted dimension — not `inner_window`. Blocking splits the
        // polynomial multiplications but the results are summed homomorphically
        // across blocks, so the accumulated value is the full inner product and
        // it is the full inner product that must stay inside (−t/2, t/2).
        let worst_case_magnitude =
            (inner_dim as u128) * (weight_abs_bound as u128) * (activation_abs_bound as u128);
        let capacity = ((t as u128) - 1) / 2;
        if worst_case_magnitude > capacity {
            return Err(CoeffMatmulError::CapacityExceeded {
                inner_dim,
                weight_abs_bound,
                activation_abs_bound,
                worst_case_magnitude,
                capacity,
                plaintext_modulus: t,
            });
        }

        Ok(Self {
            degree,
            rows,
            inner_dim,
            inner_window,
            outer_window,
            weight_abs_bound,
            activation_abs_bound,
            plaintext_modulus: t,
            weight_lift: WeightLift::default(),
        })
    }

    /// Choose the weight lift. [`WeightLift::SplitSign`] is the default and is
    /// 13 measured bits cheaper; [`WeightLift::Direct`] exists for comparison.
    pub fn with_weight_lift(mut self, weight_lift: WeightLift) -> Self {
        self.weight_lift = weight_lift;
        self
    }

    /// The weight lift in force.
    pub fn weight_lift(&self) -> WeightLift {
        self.weight_lift
    }

    /// Rows of the public matrix (`n_o`).
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Contracted dimension (`n_i`).
    pub fn inner_dim(&self) -> usize {
        self.inner_dim
    }

    /// Ring degree `N`.
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// Cheetah's `n_i^w`.
    pub fn inner_window(&self) -> usize {
        self.inner_window
    }

    /// Cheetah's `n_o^w`.
    pub fn outer_window(&self) -> usize {
        self.outer_window
    }

    /// Cheetah's `n_i'` — how many ciphertexts the client must send.
    pub fn input_blocks(&self) -> usize {
        self.inner_dim.div_ceil(self.inner_window)
    }

    /// Cheetah's `n_o'` — how many ciphertexts come back.
    pub fn output_blocks(&self) -> usize {
        self.rows.div_ceil(self.outer_window)
    }

    /// Ciphertext-plaintext multiplications one `apply` performs. Doubled under
    /// [`WeightLift::SplitSign`], which multiplies by `W⁺` and `W⁻` separately.
    pub fn ct_pt_multiplications(&self) -> usize {
        let base = self.input_blocks() * self.output_blocks();
        match self.weight_lift {
            WeightLift::Direct => base,
            WeightLift::SplitSign => 2 * base,
        }
    }

    /// Plaintext polynomials the encoded matrix holds.
    pub fn weight_plaintexts(&self) -> usize {
        self.ct_pt_multiplications()
    }

    /// Inner products recovered per polynomial multiplication under this plan —
    /// the packing efficiency the whole exercise is about. A naive
    /// one-inner-product-per-multiply scheme has this equal to 1.
    pub fn results_per_multiplication(&self) -> usize {
        self.outer_window
    }

    /// Fraction of the `N` coefficient slots the weight packing occupies.
    pub fn slot_utilization(&self) -> f64 {
        (self.inner_window * self.outer_window) as f64 / self.degree as f64
    }

    /// Plaintext modulus the capacity gate was computed against.
    pub fn plaintext_modulus(&self) -> u64 {
        self.plaintext_modulus
    }

    /// Coefficient index carrying block-local row `i`'s inner product:
    /// `i · n_i^w + n_i^w − 1` (Cheetah's `ñ_i`).
    pub fn result_index(&self, block_row: usize) -> usize {
        block_row * self.inner_window + self.inner_window - 1
    }

    /// `π^i_fc`: cut `v` into `input_blocks` zero-padded windows and lay each
    /// out in FORWARD coefficient order. Returns one coefficient vector of
    /// length `N` per block, ready for `Encoding::poly()`.
    ///
    /// Verifies the declared activation bound actually holds.
    pub fn encode_vector_coefficients(&self, v: &[i64]) -> Result<Vec<Vec<i64>>> {
        if v.len() != self.inner_dim {
            return Err(CoeffMatmulError::VectorLengthMismatch {
                expected: self.inner_dim,
                found: v.len(),
            });
        }
        for (index, &value) in v.iter().enumerate() {
            if value.unsigned_abs() > self.activation_abs_bound {
                return Err(CoeffMatmulError::ActivationExceedsDeclaredBound {
                    index,
                    value,
                    declared_bound: self.activation_abs_bound,
                });
            }
        }
        let mut blocks = Vec::with_capacity(self.input_blocks());
        for alpha in 0..self.input_blocks() {
            let mut coeffs = vec![0i64; self.degree];
            let start = alpha * self.inner_window;
            let end = (start + self.inner_window).min(self.inner_dim);
            coeffs[..end - start].copy_from_slice(&v[start..end]);
            blocks.push(coeffs);
        }
        Ok(blocks)
    }

    /// [`Self::encode_vector_coefficients`] wrapped into `Encoding::poly()`
    /// plaintexts. Client-side: encrypt each of these.
    pub fn encode_vector(&self, v: &[i64], params: &Arc<BfvParameters>) -> Result<Vec<Plaintext>> {
        self.encode_vector_coefficients(v)?
            .into_iter()
            .map(|coeffs| {
                Plaintext::try_encode(&coeffs, Encoding::poly(), params)
                    .map_err(|e| CoeffMatmulError::Fhe(e.to_string()))
            })
            .collect()
    }

    /// `π^w_fc`: cut `W` into `output_blocks × input_blocks` zero-padded blocks
    /// and lay each out with the rows CONCATENATED and each row REVERSED —
    /// `ŵ[i·n_i^w + (n_i^w − 1 − j)] = W[i][j]`. Indexed `[beta][alpha]`.
    ///
    /// Verifies the declared weight bound actually holds.
    pub fn encode_matrix_coefficients(&self, w: &[Vec<i64>]) -> Result<Vec<Vec<Vec<i64>>>> {
        if w.len() != self.rows || w.iter().any(|r| r.len() != self.inner_dim) {
            let found_cols = w.first().map(|r| r.len()).unwrap_or(0);
            return Err(CoeffMatmulError::MatrixShapeMismatch {
                expected_rows: self.rows,
                expected_cols: self.inner_dim,
                found_rows: w.len(),
                found_cols,
            });
        }
        for (row, r) in w.iter().enumerate() {
            for (col, &value) in r.iter().enumerate() {
                if value.unsigned_abs() > self.weight_abs_bound {
                    return Err(CoeffMatmulError::WeightExceedsDeclaredBound {
                        row,
                        col,
                        value,
                        declared_bound: self.weight_abs_bound,
                    });
                }
            }
        }
        let mut out = Vec::with_capacity(self.output_blocks());
        for beta in 0..self.output_blocks() {
            let mut row_blocks = Vec::with_capacity(self.input_blocks());
            for alpha in 0..self.input_blocks() {
                let mut coeffs = vec![0i64; self.degree];
                for i in 0..self.outer_window {
                    let global_row = beta * self.outer_window + i;
                    if global_row >= self.rows {
                        break; // zero-padded bottom-most block
                    }
                    for j in 0..self.inner_window {
                        let global_col = alpha * self.inner_window + j;
                        if global_col >= self.inner_dim {
                            break; // zero-padded right-most block
                        }
                        coeffs[i * self.inner_window + (self.inner_window - 1 - j)] =
                            w[global_row][global_col];
                    }
                }
                row_blocks.push(coeffs);
            }
            out.push(row_blocks);
        }
        Ok(out)
    }

    /// Split the packed weight blocks into a NONNEGATIVE positive part and a
    /// NONNEGATIVE negative part with `W = W⁺ − W⁻` — the
    /// [`WeightLift::SplitSign`] representation, whose whole purpose is that
    /// every plaintext coefficient is a weight MAGNITUDE and therefore small.
    pub fn split_sign_coefficients(
        &self,
        w: &[Vec<i64>],
    ) -> Result<(Vec<Vec<Vec<i64>>>, Vec<Vec<Vec<i64>>>)> {
        let direct = self.encode_matrix_coefficients(w)?;
        let mut positive = Vec::with_capacity(direct.len());
        let mut negative = Vec::with_capacity(direct.len());
        for row_blocks in &direct {
            let mut pos_row = Vec::with_capacity(row_blocks.len());
            let mut neg_row = Vec::with_capacity(row_blocks.len());
            for coeffs in row_blocks {
                pos_row.push(coeffs.iter().map(|&c| c.max(0)).collect::<Vec<i64>>());
                neg_row.push(coeffs.iter().map(|&c| (-c).max(0)).collect::<Vec<i64>>());
            }
            positive.push(pos_row);
            negative.push(neg_row);
        }
        Ok((positive, negative))
    }

    /// [`Self::encode_matrix_coefficients`] wrapped into `Encoding::poly()`
    /// plaintexts, under the plan's [`WeightLift`]. Server-side and reusable
    /// across inputs: encode the public weights ONCE.
    pub fn encode_matrix(
        &self,
        w: &[Vec<i64>],
        params: &Arc<BfvParameters>,
    ) -> Result<EncodedMatrix> {
        let wrap = |grid: Vec<Vec<Vec<i64>>>| -> Result<Vec<Vec<Plaintext>>> {
            grid.into_iter()
                .map(|row_blocks| {
                    row_blocks
                        .into_iter()
                        .map(|coeffs| {
                            Plaintext::try_encode(&coeffs, Encoding::poly(), params)
                                .map_err(|e| CoeffMatmulError::Fhe(e.to_string()))
                        })
                        .collect::<Result<Vec<_>>>()
                })
                .collect::<Result<Vec<_>>>()
        };
        let (positive, negative) = match self.weight_lift {
            WeightLift::Direct => (wrap(self.encode_matrix_coefficients(w)?)?, None),
            WeightLift::SplitSign => {
                let (p, n) = self.split_sign_coefficients(w)?;
                (wrap(p)?, Some(wrap(n)?))
            }
        };
        Ok(EncodedMatrix {
            positive,
            negative,
            plan: self.clone(),
        })
    }

    /// Cheetah Figure 2 step 4, minus the 2PC share: `CT_β = Σ_α CT_α ⊠ ŵ_{β,α}`.
    ///
    /// ZERO rotations, ZERO key switches, ZERO relinearizations — the products
    /// are ciphertext × PLAINTEXT, which does not grow the ciphertext degree.
    /// Returns `output_blocks()` ciphertexts.
    pub fn apply(&self, matrix: &EncodedMatrix, cts: &[Ciphertext]) -> Result<Vec<Ciphertext>> {
        if matrix.plan != *self {
            return Err(CoeffMatmulError::MatrixShapeMismatch {
                expected_rows: self.rows,
                expected_cols: self.inner_dim,
                found_rows: matrix.plan.rows,
                found_cols: matrix.plan.inner_dim,
            });
        }
        if cts.len() != self.input_blocks() {
            return Err(CoeffMatmulError::CiphertextCountMismatch {
                expected: self.input_blocks(),
                found: cts.len(),
            });
        }
        let mut out = Vec::with_capacity(self.output_blocks());
        for beta in 0..self.output_blocks() {
            let mut acc: Option<Ciphertext> = None;
            for (alpha, ct) in cts.iter().enumerate() {
                let term = ct * &matrix.positive[beta][alpha];
                acc = Some(match acc {
                    None => term,
                    Some(sum) => &sum + &term,
                });
                // `W = W⁺ − W⁻`: subtract the negative part's contribution.
                if let Some(negative) = &matrix.negative {
                    let neg_term = ct * &negative[beta][alpha];
                    acc = Some(&acc.expect("set above") - &neg_term);
                }
            }
            out.push(acc.expect("input_blocks() >= 1 by construction"));
        }
        Ok(out)
    }

    /// Read the `rows` results out of the decrypted, poly-decoded coefficient
    /// vectors of the `output_blocks()` result ciphertexts — Cheetah's
    /// `Extract` positions, done in the clear because we ship the whole RLWE
    /// ciphertext (see the module ledger).
    pub fn decode_results(&self, decoded: &[Vec<i64>]) -> Result<Vec<i64>> {
        if decoded.len() != self.output_blocks() {
            return Err(CoeffMatmulError::CiphertextCountMismatch {
                expected: self.output_blocks(),
                found: decoded.len(),
            });
        }
        let mut out = vec![0i64; self.rows];
        for (beta, coeffs) in decoded.iter().enumerate() {
            if coeffs.len() < self.degree {
                return Err(CoeffMatmulError::ShortDecoding {
                    expected: self.degree,
                    found: coeffs.len(),
                });
            }
            for i in 0..self.outer_window {
                let global_row = beta * self.outer_window + i;
                if global_row >= self.rows {
                    break;
                }
                out[global_row] = coeffs[self.result_index(i)];
            }
        }
        Ok(out)
    }

    /// The PLAINTEXT REFERENCE this whole module is checked against: exact
    /// integer `W·v`, no modulus, no ring. Every oracle test compares against
    /// this.
    pub fn reference(&self, w: &[Vec<i64>], v: &[i64]) -> Result<Vec<i64>> {
        if w.len() != self.rows || w.iter().any(|r| r.len() != self.inner_dim) {
            let found_cols = w.first().map(|r| r.len()).unwrap_or(0);
            return Err(CoeffMatmulError::MatrixShapeMismatch {
                expected_rows: self.rows,
                expected_cols: self.inner_dim,
                found_rows: w.len(),
                found_cols,
            });
        }
        if v.len() != self.inner_dim {
            return Err(CoeffMatmulError::VectorLengthMismatch {
                expected: self.inner_dim,
                found: v.len(),
            });
        }
        Ok(w.iter()
            .map(|row| {
                row.iter()
                    .zip(v.iter())
                    .map(|(&a, &b)| (a as i128) * (b as i128))
                    .sum::<i128>() as i64
            })
            .collect())
    }
}

/// A public weight matrix already cut into Cheetah blocks and coefficient-
/// encoded. Encode once, reuse across every input vector.
#[derive(Debug, Clone)]
pub struct EncodedMatrix {
    /// `W` under [`WeightLift::Direct`]; `W⁺` under [`WeightLift::SplitSign`].
    positive: Vec<Vec<Plaintext>>,
    /// `W⁻` — present exactly under [`WeightLift::SplitSign`].
    negative: Option<Vec<Vec<Plaintext>>>,
    plan: MatmulPlan,
}

impl EncodedMatrix {
    /// The plan this matrix was encoded under.
    pub fn plan(&self) -> &MatmulPlan {
        &self.plan
    }

    /// `(output_blocks, input_blocks)`.
    pub fn block_count(&self) -> (usize, usize) {
        (
            self.positive.len(),
            self.positive.first().map(|r| r.len()).unwrap_or(0),
        )
    }

    /// Total plaintext polynomials held (double the block count under
    /// [`WeightLift::SplitSign`]).
    pub fn plaintext_count(&self) -> usize {
        let (b, a) = self.block_count();
        b * a * if self.negative.is_some() { 2 } else { 1 }
    }
}

/// Default window choice: give the whole contraction one window when it fits,
/// then spend the remaining coefficients on rows. When `inner_dim > N` the
/// contraction is split at `N` and each block carries a single row.
fn default_windows(degree: usize, rows: usize, inner_dim: usize) -> Result<(usize, usize)> {
    if degree == 0 {
        return Err(CoeffMatmulError::ZeroDimension { what: "degree" });
    }
    if rows == 0 {
        return Err(CoeffMatmulError::ZeroDimension { what: "row count" });
    }
    if inner_dim == 0 {
        return Err(CoeffMatmulError::ZeroDimension {
            what: "inner dimension",
        });
    }
    let inner_window = inner_dim.min(degree);
    let outer_window = (degree / inner_window).clamp(1, rows);
    Ok((inner_window, outer_window))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The deployed plaintext modulus (`FOLD_PLAINTEXT_MODULUS`).
    const T: u64 = 1_032_193;
    /// The deployed ring degree (`FOLD_DEGREE`).
    const N: usize = 4096;

    /// Pure-arithmetic stand-in for `fhe.rs`'s negacyclic ring multiply, so the
    /// packing can be checked without keys: `c = a · b mod (X^N + 1, t)`,
    /// returned centered.
    fn negacyclic_mul_centered(a: &[i64], b: &[i64], t: i128) -> Vec<i64> {
        let n = a.len();
        assert_eq!(b.len(), n);
        let mut out = vec![0i128; n];
        for (i, &ai) in a.iter().enumerate() {
            if ai == 0 {
                continue;
            }
            for (j, &bj) in b.iter().enumerate() {
                if bj == 0 {
                    continue;
                }
                let k = i + j;
                let term = (ai as i128) * (bj as i128);
                if k < n {
                    out[k] += term;
                } else {
                    out[k - n] -= term;
                }
            }
        }
        out.into_iter()
            .map(|x| {
                let r = x.rem_euclid(t);
                let c = if r > t / 2 { r - t } else { r };
                c as i64
            })
            .collect()
    }

    /// End-to-end packing check in the clear: encode, negacyclic-multiply,
    /// accumulate across input blocks, extract — must equal the exact reference.
    fn ring_roundtrip(plan: &MatmulPlan, w: &[Vec<i64>], v: &[i64]) -> Vec<i64> {
        let vhat = plan.encode_vector_coefficients(v).expect("encode v");
        let what = plan.encode_matrix_coefficients(w).expect("encode W");
        let mut decoded = Vec::with_capacity(plan.output_blocks());
        for beta in 0..plan.output_blocks() {
            let mut acc = vec![0i64; plan.degree()];
            for (alpha, vb) in vhat.iter().enumerate() {
                let prod = negacyclic_mul_centered(vb, &what[beta][alpha], T as i128);
                for (a, p) in acc.iter_mut().zip(prod.iter()) {
                    // Centered accumulation, then re-center at the end of the
                    // block loop; magnitudes stay inside i64 by the capacity gate.
                    *a += *p;
                }
            }
            let t = T as i64;
            for a in acc.iter_mut() {
                let r = (*a).rem_euclid(t);
                *a = if r > t / 2 { r - t } else { r };
            }
            decoded.push(acc);
        }
        plan.decode_results(&decoded).expect("decode")
    }

    fn params() -> Arc<BfvParameters> {
        fhegg_core::params::pick_params(20)
    }

    #[test]
    fn deployed_quantization_ladder_matches_the_derivation() {
        // The three numbers the lane brief derives from
        // `c · 2^(w−1) · 2^(a−1) < t/2` at t = 1032193.
        assert_eq!(max_inner_dim(T, 8, 8), 31, "8-bit × 8-bit ceiling");
        assert_eq!(max_inner_dim(T, 4, 8), 504, "4-bit × 8-bit ceiling");
        assert_eq!(max_inner_dim(T, 4, 4), 8064, "4-bit × 4-bit ceiling");
        // And the ceiling is TIGHT: one more term overflows the centered range.
        for (wb, ab) in [(8u32, 8u32), (4, 8), (4, 4)] {
            let c = max_inner_dim(T, wb, ab) as u128;
            let per = (signed_abs_bound(wb) as u128) * (signed_abs_bound(ab) as u128);
            let cap = ((T as u128) - 1) / 2;
            assert!(c * per <= cap, "ceiling {c} must fit");
            assert!((c + 1) * per > cap, "ceiling {c} must be maximal");
        }
    }

    #[test]
    fn capacity_gate_fires_one_past_the_ceiling() {
        let p = params();
        assert_eq!(p.plaintext(), T);
        let (w8, a8) = (signed_abs_bound(8), signed_abs_bound(8));
        // 31 is admitted...
        MatmulPlan::new(&p, 4, 31, w8, a8).expect("inner dim 31 at 8×8 must be admitted");
        // ...32 is REFUSED, and the refusal names the numbers.
        let err = MatmulPlan::new(&p, 4, 32, w8, a8).expect_err("inner dim 32 at 8×8 must refuse");
        match err {
            CoeffMatmulError::CapacityExceeded {
                inner_dim,
                worst_case_magnitude,
                capacity,
                plaintext_modulus,
                ..
            } => {
                assert_eq!(inner_dim, 32);
                assert_eq!(worst_case_magnitude, 32 * 128 * 128);
                assert_eq!(capacity, 516_096);
                assert_eq!(plaintext_modulus, T);
            }
            other => panic!("wrong refusal: {other}"),
        }
        // The 4-bit × 8-bit row of the ladder, both sides of the edge.
        let (w4, a8b) = (signed_abs_bound(4), signed_abs_bound(8));
        MatmulPlan::new(&p, 4, 504, w4, a8b).expect("504 at 4×8 must be admitted");
        MatmulPlan::new(&p, 4, 505, w4, a8b).expect_err("505 at 4×8 must refuse");
    }

    #[test]
    fn declared_bounds_are_verified_against_the_data() {
        let p = params();
        let plan = MatmulPlan::new(&p, 2, 8, 8, 128).expect("plan");
        // A weight one past the declared 4-bit bound is caught at encode.
        let w = vec![vec![9i64; 8], vec![0i64; 8]];
        match plan.encode_matrix_coefficients(&w) {
            Err(CoeffMatmulError::WeightExceedsDeclaredBound {
                row,
                col,
                value,
                declared_bound,
            }) => {
                assert_eq!((row, col, value, declared_bound), (0, 0, 9, 8));
            }
            other => panic!("expected a weight-bound refusal, got {other:?}"),
        }
        // Same for the activation side.
        let v: Vec<i64> = (0..8).map(|i| if i == 3 { 129 } else { 1 }).collect();
        match plan.encode_vector_coefficients(&v) {
            Err(CoeffMatmulError::ActivationExceedsDeclaredBound { index, value, .. }) => {
                assert_eq!((index, value), (3, 129));
            }
            other => panic!("expected an activation-bound refusal, got {other:?}"),
        }
    }

    #[test]
    fn cheetah_figure_3_toy_example() {
        // The paper's own worked example: N = 8, p = 2^5, W = [[1,2,3],[4,5,6]],
        // v = [7,8,9]; ŵ = 3 + 2X + X² + 6X³ + 5X⁴ + 4X⁵, results at
        // coefficients 2 and 5 (18 and 26 mod 32).
        let plan = MatmulPlan {
            degree: 8,
            rows: 2,
            inner_dim: 3,
            inner_window: 3,
            outer_window: 2,
            weight_abs_bound: 6,
            activation_abs_bound: 9,
            plaintext_modulus: 32,
            weight_lift: WeightLift::Direct,
        };
        let w = vec![vec![1i64, 2, 3], vec![4, 5, 6]];
        let v = vec![7i64, 8, 9];
        let what = plan.encode_matrix_coefficients(&w).expect("encode W");
        assert_eq!(what[0][0], vec![3, 2, 1, 6, 5, 4, 0, 0], "π^w_fc(W)");
        let vhat = plan.encode_vector_coefficients(&v).expect("encode v");
        assert_eq!(vhat[0], vec![7, 8, 9, 0, 0, 0, 0, 0], "π^i_fc(v)");
        assert_eq!((plan.result_index(0), plan.result_index(1)), (2, 5));
        let prod = negacyclic_mul_centered(&vhat[0], &what[0][0], 32);
        // 18 and 26 in the paper's [0, 32) convention; centered here.
        assert_eq!(prod[2], 18 - 32);
        assert_eq!(prod[5], 26 - 32);
    }

    #[test]
    fn packing_is_exact_at_the_8bit_ceiling() {
        let p = params();
        let plan = MatmulPlan::new(&p, 40, 31, 128, 128).expect("plan");
        // 4096 / 31 = 132 rows per polynomial: 40 rows fit in ONE multiply.
        assert_eq!(plan.outer_window(), 40);
        assert_eq!(plan.input_blocks(), 1);
        assert_eq!(plan.output_blocks(), 1);
        // 2, not 1: the default SplitSign lift multiplies by W⁺ and W⁻.
        assert_eq!(plan.ct_pt_multiplications(), 2);
        assert_eq!(
            plan.clone()
                .with_weight_lift(WeightLift::Direct)
                .ct_pt_multiplications(),
            1
        );
        let w: Vec<Vec<i64>> = (0..40)
            .map(|i| (0..31).map(|j| ((i * 31 + j) % 257) as i64 - 128).collect())
            .collect();
        let v: Vec<i64> = (0..31).map(|j| (j * 17 % 257) as i64 - 128).collect();
        assert_eq!(
            ring_roundtrip(&plan, &w, &v),
            plan.reference(&w, &v).unwrap()
        );
    }

    #[test]
    fn worst_case_magnitudes_do_not_wrap() {
        // Every weight and activation at the declared bound, alternating sign so
        // one row is +max and one is −max: the exact edge the capacity gate
        // protects. If the gate were off by one this is where it shows.
        let p = params();
        let plan = MatmulPlan::new(&p, 2, 31, 128, 128).expect("plan");
        let w = vec![vec![-128i64; 31], vec![128i64; 31]];
        let v = vec![-128i64; 31];
        let reference = plan.reference(&w, &v).unwrap();
        assert_eq!(reference, vec![31 * 128 * 128, -(31 * 128 * 128)]);
        assert_eq!(ring_roundtrip(&plan, &w, &v), reference);
    }

    #[test]
    fn no_negacyclic_contamination_at_extraction_indices() {
        // Structural claim from the module docblock, exercised where wrap is
        // most likely: the window exactly fills the polynomial (n_i·n_o = N) and
        // every coefficient is nonzero, so the negacyclic tail is maximally
        // populated. The extraction indices must still be clean.
        let p = params();
        let plan = MatmulPlan::with_windows(&p, 8, 512, 512, 8, 8, 126).expect("full-degree plan");
        assert_eq!(plan.inner_window() * plan.outer_window(), N);
        assert_eq!(plan.slot_utilization(), 1.0);
        let w: Vec<Vec<i64>> = (0..8)
            .map(|i| {
                (0..512)
                    .map(|j| (((i * 512 + j) % 17) as i64) - 8)
                    .collect()
            })
            .collect();
        let v: Vec<i64> = (0..512).map(|j| ((j % 253) as i64) - 126).collect();
        assert_eq!(
            ring_roundtrip(&plan, &w, &v),
            plan.reference(&w, &v).unwrap()
        );
    }

    #[test]
    fn ragged_dimensions_zero_pad_correctly() {
        let p = params();
        // Neither dimension divides its window: 7 rows into windows of 4 (the
        // bottom block is 3 padded to 4), 500 inner into windows of 300 (the
        // right block is 200 padded to 300).
        let plan = MatmulPlan::with_windows(&p, 7, 500, 300, 4, 8, 128).expect("ragged plan");
        assert_eq!(plan.input_blocks(), 2);
        assert_eq!(plan.output_blocks(), 2);
        assert_eq!(plan.ct_pt_multiplications(), 8);
        let w: Vec<Vec<i64>> = (0..7)
            .map(|i| {
                (0..500)
                    .map(|j| (((i * 500 + j) % 17) as i64) - 8)
                    .collect()
            })
            .collect();
        let v: Vec<i64> = (0..500).map(|j| (((j * 31) % 257) as i64) - 128).collect();
        assert_eq!(
            ring_roundtrip(&plan, &w, &v),
            plan.reference(&w, &v).unwrap()
        );
    }

    #[test]
    fn negative_weights_and_zero_rows_round_trip() {
        let p = params();
        let plan = MatmulPlan::new(&p, 5, 20, 128, 128).expect("plan");
        let mut w = vec![vec![0i64; 20]; 5];
        // row 0: all zero (the zero-row boundary case)
        // row 1: all negative
        w[1] = vec![-128i64; 20];
        // row 2: alternating sign
        w[2] = (0..20).map(|j| if j % 2 == 0 { -37 } else { 37 }).collect();
        // row 3: a single −1 against a POSITIVE entry of v (v[j] = j − 9, so
        // j = 15 gives +6) — the result must come back negative.
        w[3][15] = -1;
        // row 4: mixed
        w[4] = (0..20).map(|j| (j as i64) - 10).collect();
        let v: Vec<i64> = (0..20).map(|j| (j as i64) - 9).collect();
        let reference = plan.reference(&w, &v).unwrap();
        assert_eq!(reference[0], 0, "zero row must give zero");
        assert!(reference[3] < 0, "single negative weight must be negative");
        assert_eq!(ring_roundtrip(&plan, &w, &v), reference);
    }

    #[test]
    fn inner_dim_larger_than_degree_splits_across_ciphertexts() {
        // 4-bit × 4-bit admits inner dim up to 8064 > N = 4096, so the
        // contraction genuinely must split across input ciphertexts.
        let p = params();
        let plan = MatmulPlan::new(&p, 3, 6000, 8, 8).expect("plan");
        assert_eq!(plan.inner_window(), N);
        assert_eq!(plan.outer_window(), 1);
        assert_eq!(plan.input_blocks(), 2);
        assert_eq!(plan.output_blocks(), 3);
        assert_eq!(plan.ct_pt_multiplications(), 6 * 2);
        let w: Vec<Vec<i64>> = (0..3)
            .map(|i| {
                (0..6000)
                    .map(|j| (((i * 6000 + j) % 17) as i64) - 8)
                    .collect()
            })
            .collect();
        let v: Vec<i64> = (0..6000).map(|j| (((j * 5) % 17) as i64) - 8).collect();
        assert_eq!(
            ring_roundtrip(&plan, &w, &v),
            plan.reference(&w, &v).unwrap()
        );
    }

    #[test]
    fn split_sign_reconstructs_the_direct_encoding_exactly() {
        let p = params();
        let plan = MatmulPlan::new(&p, 9, 31, 128, 128).expect("plan");
        assert_eq!(
            plan.weight_lift(),
            WeightLift::SplitSign,
            "SplitSign is the default"
        );
        let w: Vec<Vec<i64>> = (0..9)
            .map(|i| {
                (0..31)
                    .map(|j| (((i * 31 + j) * 7 % 257) as i64) - 128)
                    .collect()
            })
            .collect();
        let direct = plan.encode_matrix_coefficients(&w).expect("direct");
        let (pos, neg) = plan.split_sign_coefficients(&w).expect("split");
        for (beta, row_blocks) in direct.iter().enumerate() {
            for (alpha, coeffs) in row_blocks.iter().enumerate() {
                // Both parts NONNEGATIVE — that is the entire point.
                assert!(pos[beta][alpha].iter().all(|&c| c >= 0));
                assert!(neg[beta][alpha].iter().all(|&c| c >= 0));
                // Disjoint support, so each partial inner product obeys the SAME
                // capacity bound the plan checked.
                assert!(pos[beta][alpha]
                    .iter()
                    .zip(neg[beta][alpha].iter())
                    .all(|(&a, &b)| a == 0 || b == 0));
                for (k, &c) in coeffs.iter().enumerate() {
                    assert_eq!(pos[beta][alpha][k] - neg[beta][alpha][k], c);
                }
            }
        }
        // And in the ring: W⁺·v − W⁻·v is the exact reference.
        let v: Vec<i64> = (0..31).map(|j| ((j * 19 % 257) as i64) - 128).collect();
        let vhat = plan.encode_vector_coefficients(&v).expect("encode v");
        let t = T as i64;
        let mut acc = vec![0i64; plan.degree()];
        for (alpha, vb) in vhat.iter().enumerate() {
            let p_term = negacyclic_mul_centered(vb, &pos[0][alpha], T as i128);
            let n_term = negacyclic_mul_centered(vb, &neg[0][alpha], T as i128);
            for k in 0..plan.degree() {
                acc[k] += p_term[k] - n_term[k];
            }
        }
        for a in acc.iter_mut() {
            let r = (*a).rem_euclid(t);
            *a = if r > t / 2 { r - t } else { r };
        }
        assert_eq!(
            plan.decode_results(&[acc]).unwrap(),
            plan.reference(&w, &v).unwrap()
        );
    }

    #[test]
    fn zero_and_oversized_shapes_are_refused() {
        let p = params();
        assert!(matches!(
            MatmulPlan::new(&p, 0, 8, 8, 8),
            Err(CoeffMatmulError::ZeroDimension { .. })
        ));
        assert!(matches!(
            MatmulPlan::new(&p, 8, 0, 8, 8),
            Err(CoeffMatmulError::ZeroDimension { .. })
        ));
        assert!(matches!(
            MatmulPlan::with_windows(&p, 8, 64, 64, 65, 8, 8),
            Err(CoeffMatmulError::WindowExceedsDegree { .. })
        ));
    }

    #[test]
    fn packing_efficiency_beats_one_result_per_multiply() {
        // The point of the blocking: a naive layout extracts ONE inner product
        // per polynomial multiplication. These are what Cheetah's layout gets at
        // the deployed degree, per quantization row.
        let p = params();
        for (bits, inner, expect_per_mul) in [
            ((8u32, 8u32), 31usize, 132usize), // 4096 / 31
            ((4, 8), 504, 8),                  // 4096 / 504
            ((4, 4), 4096, 1),                 // contraction fills the polynomial
        ] {
            let rows = expect_per_mul.max(1) * 2;
            let plan = MatmulPlan::new(
                &p,
                rows,
                inner,
                signed_abs_bound(bits.0),
                signed_abs_bound(bits.1),
            )
            .expect("plan");
            assert_eq!(
                plan.results_per_multiplication(),
                expect_per_mul,
                "packing efficiency at inner dim {inner}"
            );
            assert!(plan.results_per_multiplication() >= 1);
        }
    }
}
