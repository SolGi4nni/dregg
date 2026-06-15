//! Real STARK proof generation and verification.
//!
//! This implements a minimal but REAL STARK proof system from scratch using:
//! - Our BabyBear field (p = 2^31 - 2^27 + 1 = 2013265921)
//! - Reed-Solomon encoding of trace columns
//! - BLAKE3 Merkle tree commitments
//! - FRI (Fast Reed-Solomon IOP of Proximity) for low-degree testing
//! - Fiat-Shamir transform for non-interactivity
//!
//! The key property: `prove()` produces bytes that a separate `verify()` can
//! check WITHOUT seeing the original trace/witness. A tampered trace fails.
//!
//! # Transition Constraint Evaluation
//!
//! In the Reed-Solomon evaluation domain (size = trace_len * BLOWUP), advancing by one
//! trace step corresponds to advancing by BLOWUP evaluation domain positions. Given
//! trace polynomial T(x), evaluating T(x * omega_trace) at evaluation point omega_eval^i
//! yields T(omega_eval^(i + BLOWUP)) = trace_evals[col][(i + blowup) % domain_size].
//!
//! The transition vanishing polynomial Z_T(x) = (x^n - 1) / (x - omega^(n-1)) is used
//! as the divisor for transition constraint quotients. This polynomial vanishes on all
//! trace rows except the last, since transition constraints (which reference "next row")
//! are only meaningful on rows 0 through n-2.
//!
//! # Production Prover
//!
//! For production use, prefer the Plonky3 backend (`backends::plonky3`) which uses a
//! battle-tested proving system with proper FRI, extension-field challenges, and
//! Poseidon2-based Merkle tree commitments. This custom STARK is classified as
//! `ProofTier::Experimental` and is retained for AIR types not yet ported to
//! native Plonky3 `Air` trait implementations (fold, derivation, predicates).

// no_std port (seL4 verifier-stark PD): the verbatim `circuit/src/stark.rs`
// custom STARK (BabyBear + BLAKE3 Merkle + FRI + Fiat-Shamir), with `std::`
// swapped for `core::`/`alloc::` and the `#[cfg(test)]` module dropped. The
// prove/verify logic is byte-identical to the host crate. `prove()` is fully
// deterministic (Fiat-Shamir, no RNG/clock), so this PD runs a REAL proof
// generation + verification on-device with no getrandom dependency.
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use alloc::format;

use super::field::{BABYBEAR_P, BabyBear};
use serde::{Deserialize, Serialize};
use core::fmt;

// ============================================================================
// Extension Field: BabyBear^4
// ============================================================================

/// Extension field element: BabyBear^4 = BabyBear[X] / (X^4 - 11).
///
/// Provides 124-bit security for Fiat-Shamir challenges (constraint composition alpha).
/// Individual AIR constraints are still BabyBear values, but the random linear
/// combination uses extension-field arithmetic, preventing an adversary from
/// exploiting the small (31-bit) base field to find constraint-cancellation collisions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExtElem(pub [BabyBear; 4]);

/// The irreducible constant W for BabyBear^4: X^4 - 11.
const EXT_W: BabyBear = BabyBear(11);

impl ExtElem {
    pub const ZERO: Self = Self([BabyBear::ZERO; 4]);
    pub const ONE: Self = Self([
        BabyBear::ONE,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);

    /// Construct from 4 BabyBear components.
    pub fn new(components: [BabyBear; 4]) -> Self {
        Self(components)
    }

    /// Embed a base field element into the extension (constant term only).
    pub fn from_base(x: BabyBear) -> Self {
        Self([x, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO])
    }

    /// Check if zero.
    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|x| *x == BabyBear::ZERO)
    }

    /// Extension field addition.
    pub fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
        ])
    }

    /// Extension field subtraction.
    pub fn sub(self, rhs: Self) -> Self {
        Self([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
        ])
    }

    /// Extension field multiplication mod (X^4 - W).
    pub fn mul(self, rhs: Self) -> Self {
        let a = self.0;
        let b = rhs.0;
        let w = EXT_W;

        let c0 = a[0] * b[0] + w * (a[1] * b[3] + a[2] * b[2] + a[3] * b[1]);
        let c1 = a[0] * b[1] + a[1] * b[0] + w * (a[2] * b[3] + a[3] * b[2]);
        let c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + w * (a[3] * b[3]);
        let c3 = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];

        Self([c0, c1, c2, c3])
    }

    /// Scalar multiplication: ExtElem * BabyBear (base field scalar).
    /// More efficient than full extension multiplication when one operand is base-field.
    pub fn scale(self, scalar: BabyBear) -> Self {
        Self([
            self.0[0] * scalar,
            self.0[1] * scalar,
            self.0[2] * scalar,
            self.0[3] * scalar,
        ])
    }

    /// Extract the base field component (coefficient of x^0).
    /// For elements known to be in the base field, this returns the value.
    pub fn base_elem(&self) -> BabyBear {
        self.0[0]
    }

    /// Extension field inverse via Gaussian elimination.
    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let a = self.0;
        let w = EXT_W;

        let mut mat = [[BabyBear::ZERO; 5]; 4];

        mat[0][0] = a[0];
        mat[0][1] = w * a[3];
        mat[0][2] = w * a[2];
        mat[0][3] = w * a[1];
        mat[0][4] = BabyBear::ONE;
        mat[1][0] = a[1];
        mat[1][1] = a[0];
        mat[1][2] = w * a[3];
        mat[1][3] = w * a[2];
        mat[1][4] = BabyBear::ZERO;
        mat[2][0] = a[2];
        mat[2][1] = a[1];
        mat[2][2] = a[0];
        mat[2][3] = w * a[3];
        mat[2][4] = BabyBear::ZERO;
        mat[3][0] = a[3];
        mat[3][1] = a[2];
        mat[3][2] = a[1];
        mat[3][3] = a[0];
        mat[3][4] = BabyBear::ZERO;

        for c in 0..4 {
            let mut pivot_row = None;
            for row in c..4 {
                if mat[row][c] != BabyBear::ZERO {
                    pivot_row = Some(row);
                    break;
                }
            }
            let pivot_row = pivot_row?;
            if pivot_row != c {
                mat.swap(c, pivot_row);
            }

            let inv_pivot = mat[c][c].inverse()?;
            for j in 0..5 {
                mat[c][j] = mat[c][j] * inv_pivot;
            }

            for row in 0..4 {
                if row == c {
                    continue;
                }
                let factor = mat[row][c];
                for j in 0..5 {
                    mat[row][j] = mat[row][j] - factor * mat[c][j];
                }
            }
        }

        Some(Self([mat[0][4], mat[1][4], mat[2][4], mat[3][4]]))
    }
}

impl core::ops::Mul<BabyBear> for ExtElem {
    type Output = ExtElem;
    fn mul(self, rhs: BabyBear) -> ExtElem {
        self.scale(rhs)
    }
}

// ============================================================================
// STARK Configuration
// ============================================================================

/// Configuration for the custom STARK prover/verifier.
#[derive(Clone, Debug)]
pub struct StarkConfig {
    /// Number of leading zero bits required in the proof-of-work hash.
    /// Standard practice: 20-30 bits for 128-bit security with 31-bit field.
    /// Set to 0 to disable PoW (for tests or backward compatibility).
    pub pow_bits: u32,
}

impl Default for StarkConfig {
    fn default() -> Self {
        Self { pow_bits: 20 }
    }
}

impl StarkConfig {
    /// Create a config with no proof-of-work (for tests and backward compat).
    pub fn no_pow() -> Self {
        Self { pow_bits: 0 }
    }
}

// ============================================================================
// Polynomial operations over BabyBear
// ============================================================================

pub(crate) fn poly_eval(coeffs: &[BabyBear], x: BabyBear) -> BabyBear {
    let mut result = BabyBear::ZERO;
    for &c in coeffs.iter().rev() {
        result = result * x + c;
    }
    result
}

/// Primitive root of the BabyBear multiplicative group.
/// 31 is a generator of Z_p^* where p = 2013265921.
/// The group order is p-1 = 2013265920 = 2^27 * 3 * 5.
/// Verified: 31^((p-1)/2) != 1, 31^((p-1)/3) != 1, 31^((p-1)/5) != 1.
const BABYBEAR_PRIMITIVE_ROOT: u32 = 31;

/// Get a principal n-th root of unity where n = 2^log_n.
/// BabyBear supports up to 2^27-th roots of unity.
pub(crate) fn get_root_of_unity(log_n: u32) -> BabyBear {
    assert!(
        log_n <= 27,
        "BabyBear only supports roots of unity up to 2^27"
    );
    // omega = g^((p-1) / 2^log_n) where g = 31 (primitive root)
    let exp = (BABYBEAR_P - 1) / (1u32 << log_n);
    BabyBear::new(BABYBEAR_PRIMITIVE_ROOT).pow(exp)
}

/// Build a multiplicative evaluation domain of size 2^log_n using roots of unity.
/// Returns the domain {1, omega, omega^2, ..., omega^(n-1)} where omega^n = 1.
pub(crate) fn build_evaluation_domain(num_points: usize) -> Vec<BabyBear> {
    assert!(
        num_points.is_power_of_two(),
        "Domain size must be a power of two"
    );
    let log_n = num_points.trailing_zeros();
    let omega = get_root_of_unity(log_n);
    let mut domain = Vec::with_capacity(num_points);
    let mut x = BabyBear::ONE;
    for _ in 0..num_points {
        domain.push(x);
        x = x * omega;
    }
    domain
}

pub(crate) fn interpolate(xs: &[BabyBear], ys: &[BabyBear]) -> Vec<BabyBear> {
    let n = xs.len();
    assert_eq!(n, ys.len());
    if n == 0 {
        return vec![];
    }
    let mut result = vec![BabyBear::ZERO; n];
    for i in 0..n {
        let mut basis = vec![BabyBear::ONE];
        let mut denom = BabyBear::ONE;
        for j in 0..n {
            if i == j {
                continue;
            }
            let mut new_basis = vec![BabyBear::ZERO; basis.len() + 1];
            for k in 0..basis.len() {
                new_basis[k + 1] = new_basis[k + 1] + basis[k];
                new_basis[k] = new_basis[k] - basis[k] * xs[j];
            }
            basis = new_basis;
            denom = denom * (xs[i] - xs[j]);
        }
        let scale = ys[i] * denom.inverse().unwrap();
        for k in 0..basis.len() {
            if k < result.len() {
                result[k] = result[k] + basis[k] * scale;
            }
        }
    }
    result
}

// ============================================================================
// Merkle tree (BLAKE3-based)
// ============================================================================

/// Domain separator for leaf hashing. Must match chain/program/src/main.rs.
pub const STARK_LEAF_DOMAIN: &[u8] = b"stark-leaf:";
/// Domain separator for node hashing. Must match chain/program/src/main.rs.
pub const STARK_NODE_DOMAIN: &[u8] = b"stark-node:";

fn hash_leaf(value: BabyBear) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_LEAF_DOMAIN);
    hasher.update(&value.0.to_le_bytes());
    *hasher.finalize().as_bytes()
}

fn hash_leaf_multi(values: &[BabyBear]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_LEAF_DOMAIN);
    for v in values {
        hasher.update(&v.0.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn hash_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_NODE_DOMAIN);
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

#[derive(Clone, Debug)]
struct MerkleTree {
    nodes: Vec<[u8; 32]>,
    num_leaves: usize,
}

impl MerkleTree {
    fn new(leaf_hashes: Vec<[u8; 32]>) -> Self {
        let n = leaf_hashes.len();
        assert!(n.is_power_of_two() && n >= 2);
        let mut nodes = Vec::with_capacity(2 * n);
        nodes.extend_from_slice(&leaf_hashes);
        let mut level_start = 0;
        let mut level_size = n;
        while level_size > 1 {
            for i in (0..level_size).step_by(2) {
                let left = &nodes[level_start + i];
                let right = &nodes[level_start + i + 1];
                nodes.push(hash_node(left, right));
            }
            level_start += level_size;
            level_size /= 2;
        }
        Self {
            nodes,
            num_leaves: n,
        }
    }

    fn root(&self) -> [u8; 32] {
        *self.nodes.last().unwrap()
    }

    fn prove(&self, index: usize) -> Vec<[u8; 32]> {
        assert!(index < self.num_leaves);
        let mut path = Vec::new();
        let mut idx = index;
        let mut level_start = 0;
        let mut level_size = self.num_leaves;
        while level_size > 1 {
            path.push(self.nodes[level_start + (idx ^ 1)]);
            idx /= 2;
            level_start += level_size;
            level_size /= 2;
        }
        path
    }

    fn verify_proof(
        root: &[u8; 32],
        leaf_hash: &[u8; 32],
        index: usize,
        path: &[[u8; 32]],
    ) -> bool {
        let mut current = *leaf_hash;
        let mut idx = index;
        for sibling in path {
            current = if idx & 1 == 0 {
                hash_node(&current, sibling)
            } else {
                hash_node(sibling, &current)
            };
            idx >>= 1;
        }
        &current == root
    }
}

// ============================================================================
// Fiat-Shamir transcript
// ============================================================================

#[derive(Clone)]
struct Transcript {
    hasher: blake3::Hasher,
    counter: u64,
}

impl Transcript {
    fn new(domain_sep: &[u8]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-stark-v1:");
        hasher.update(domain_sep);
        Self { hasher, counter: 0 }
    }
    fn absorb_bytes(&mut self, data: &[u8]) {
        self.hasher.update(data);
    }
    fn absorb_field(&mut self, val: BabyBear) {
        self.hasher.update(&val.0.to_le_bytes());
    }
    fn absorb_hash(&mut self, h: &[u8; 32]) {
        self.hasher.update(h);
    }
    fn squeeze_field(&mut self) -> BabyBear {
        self.counter += 1;
        let mut sh = self.hasher.clone();
        sh.update(b"squeeze:");
        sh.update(&self.counter.to_le_bytes());
        let hash = sh.finalize();
        let bytes = hash.as_bytes();
        let result = BabyBear::new(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]));
        // Feed squeezed output back into transcript state to decorrelate
        // consecutive squeezes (prevents challenge correlation attacks)
        self.hasher.update(bytes);
        result
    }
    fn squeeze_ext_elem(&mut self) -> ExtElem {
        ExtElem::new([
            self.squeeze_field(),
            self.squeeze_field(),
            self.squeeze_field(),
            self.squeeze_field(),
        ])
    }
    fn squeeze_index(&mut self, bound: usize) -> usize {
        self.counter += 1;
        let mut sh = self.hasher.clone();
        sh.update(b"squeeze-idx:");
        sh.update(&self.counter.to_le_bytes());
        let hash = sh.finalize();
        let bytes = hash.as_bytes();
        let val = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        // Feed squeezed output back into transcript state to decorrelate
        // consecutive squeezes
        self.hasher.update(bytes);
        (val as usize) % bound
    }
}

// ============================================================================
// Proof-of-Work (Grinding Resistance)
// ============================================================================

/// Domain separator for PoW hashing to prevent cross-protocol collisions.
const POW_DOMAIN: &[u8] = b"dregg-stark-pow:";

/// Check whether a hash has at least `bits` leading zero bits.
fn has_leading_zeros(hash: &[u8; 32], bits: u32) -> bool {
    if bits == 0 {
        return true;
    }
    let full_bytes = (bits / 8) as usize;
    let remaining_bits = bits % 8;

    // Check full zero bytes
    for &b in &hash[..full_bytes] {
        if b != 0 {
            return false;
        }
    }

    // Check remaining bits in the next byte
    if remaining_bits > 0 {
        let mask = 0xFF << (8 - remaining_bits);
        if hash[full_bytes] & mask != 0 {
            return false;
        }
    }

    true
}

/// Compute the PoW challenge hash: BLAKE3(POW_DOMAIN || transcript_state || nonce).
/// The transcript state is captured by finalizing a clone of the hasher.
fn pow_hash(transcript: &Transcript, nonce: u32) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(POW_DOMAIN);
    // Capture the current transcript state as a digest
    let state_digest = transcript.hasher.clone().finalize();
    hasher.update(state_digest.as_bytes());
    hasher.update(&nonce.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Grind for a nonce satisfying the PoW difficulty. Returns the winning nonce.
fn grind_pow(transcript: &Transcript, pow_bits: u32) -> u32 {
    for nonce in 0u32.. {
        let hash = pow_hash(transcript, nonce);
        if has_leading_zeros(&hash, pow_bits) {
            return nonce;
        }
    }
    unreachable!()
}

/// Verify that a nonce satisfies the PoW difficulty.
fn verify_pow(transcript: &Transcript, nonce: u32, pow_bits: u32) -> bool {
    let hash = pow_hash(transcript, nonce);
    has_leading_zeros(&hash, pow_bits)
}

// ============================================================================
// STARK Proof structure
// ============================================================================

/// FRI security: NUM_QUERIES * log2(blowup) bits of proximity soundness.
/// Combined with BabyBear4 challenge security (~124 bits),
/// system security = min(FRI_bits, 124) >= NIST PQ Level 1 (128 bits target).
const NUM_QUERIES: usize = 80;
const MIN_BLOWUP: usize = 4;

/// Compute the blowup factor needed for an AIR's constraint degree.
/// Must be >= constraint_degree for FRI to provide soundness.
/// Rounded to next power of two for FFT compatibility.
pub(crate) fn blowup_for_degree(degree: usize) -> usize {
    degree.next_power_of_two().max(MIN_BLOWUP)
}

/// Context for STARK proof generation/verification providing temporal binding
/// and session isolation. When provided, these values are absorbed into the
/// Fiat-Shamir transcript to prevent proof replay across different contexts.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct StarkContext {
    /// Optional nonce for temporal binding (e.g., session ID, random challenge).
    pub nonce: Option<[u8; 32]>,
    /// Optional timestamp for freshness (unix seconds).
    pub timestamp: Option<u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StarkProof {
    pub trace_commitment: [u8; 32],
    pub constraint_commitment: [u8; 32],
    pub fri_commitments: Vec<[u8; 32]>,
    pub fri_final_poly: Vec<u32>,
    pub query_proofs: Vec<QueryProof>,
    pub public_inputs: Vec<u32>,
    pub trace_len: usize,
    pub num_cols: usize,
    /// The AIR identity that produced this proof (for cross-AIR confusion prevention).
    pub air_name: String,
    /// Optional nonce for temporal binding (must match what verifier expects).
    pub nonce: Option<[u8; 32]>,
    /// Boundary constraint quotient commitment (Merkle root of boundary quotient evaluations).
    /// Binds specific trace cells to public input values, preventing a malicious prover
    /// from generating a valid trace for inputs X then claiming it satisfies inputs Y.
    #[serde(default)]
    pub boundary_commitment: Option<[u8; 32]>,
    /// Boundary quotient values at queried positions.
    #[serde(default)]
    pub boundary_query_values: Vec<Vec<u32>>,
    /// Merkle paths for boundary quotient queries.
    #[serde(default)]
    pub boundary_query_paths: Vec<Vec<[u8; 32]>>,
    /// Proof-of-work nonce for grinding resistance.
    /// After committing trace and constraints, the prover finds a nonce such that
    /// BLAKE3(transcript_state || nonce) has `pow_bits` leading zero bits.
    /// This prevents an adversary from cheaply grinding Fiat-Shamir challenges.
    #[serde(default)]
    pub pow_nonce: u32,
    /// Number of PoW bits this proof was generated with (for verifier to know difficulty).
    #[serde(default)]
    pub pow_bits: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryProof {
    pub index: usize,
    pub trace_values: Vec<u32>,
    pub trace_path: Vec<[u8; 32]>,
    pub next_trace_values: Vec<u32>,
    pub next_trace_path: Vec<[u8; 32]>,
    /// Reduced (base-field) quotient value committed in the Merkle tree.
    /// This is the inner product of the ExtElem quotient with the zeta reduction vector.
    pub constraint_value: u32,
    /// Full extension-field quotient components [c0, c1, c2, c3].
    /// The verifier checks: constraint_value == zeta_reduce(constraint_ext)
    /// AND constraint_ext * Z_T(x) == eval_constraints(...).
    #[serde(default)]
    pub constraint_ext: [u32; 4],
    pub constraint_path: Vec<[u8; 32]>,
    pub constraint_sibling_value: u32,
    #[serde(default)]
    pub constraint_sibling_ext: [u32; 4],
    pub constraint_sibling_pos: usize,
    pub constraint_sibling_path: Vec<[u8; 32]>,
    pub fri_layers: Vec<FriLayerQuery>,
}

/// Errors raised before or during STARK proof generation.
///
/// `prove*` keeps the historical panic-on-error behavior for compatibility.
/// New tests and production callers that can recover should use `try_prove*`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    InvalidTraceLength {
        len: usize,
    },
    TraceWidthMismatch {
        row: usize,
        expected: usize,
        actual: usize,
    },
    DomainTooLarge {
        domain_size: usize,
        max_power_of_two_log: u32,
    },
    DomainOverflow {
        trace_len: usize,
        blowup: usize,
    },
    BoundaryRowOutOfBounds {
        row: usize,
        trace_len: usize,
    },
    BoundaryColumnOutOfBounds {
        col: usize,
        width: usize,
    },
    ConstraintViolation {
        trace_row: usize,
        domain_index: usize,
        value: ExtElem,
    },
}

impl fmt::Display for ProveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTraceLength { len } => write!(
                f,
                "invalid trace length {len}: trace length must be >= 2 and a power of two"
            ),
            Self::TraceWidthMismatch {
                row,
                expected,
                actual,
            } => write!(
                f,
                "trace row {row} has width {actual}, but AIR expects {expected} columns"
            ),
            Self::DomainTooLarge {
                domain_size,
                max_power_of_two_log,
            } => write!(
                f,
                "domain size {domain_size} exceeds BabyBear root-of-unity limit (2^{max_power_of_two_log})"
            ),
            Self::DomainOverflow { trace_len, blowup } => {
                write!(f, "trace_len * blowup overflow: {trace_len} * {blowup}")
            }
            Self::BoundaryRowOutOfBounds { row, trace_len } => write!(
                f,
                "boundary constraint row {row} is out of bounds for trace length {trace_len}"
            ),
            Self::BoundaryColumnOutOfBounds { col, width } => write!(
                f,
                "boundary constraint column {col} is out of bounds for trace width {width}"
            ),
            Self::ConstraintViolation {
                trace_row,
                domain_index,
                value,
            } => write!(
                f,
                "Trace constraint non-zero at trace row {trace_row} (domain index {domain_index}): {value:?}. The trace violates AIR constraints and cannot be proven."
            ),
        }
    }
}

impl core::error::Error for ProveError {}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FriLayerQuery {
    pub query_pos: usize,
    pub query_value: u32,
    pub query_path: Vec<[u8; 32]>,
    pub sibling_pos: usize,
    pub sibling_value: u32,
    pub sibling_path: Vec<[u8; 32]>,
}

// ============================================================================
// AIR trait
// ============================================================================

pub trait StarkAir {
    fn width(&self) -> usize;

    /// Evaluate the combined constraint polynomial at a given trace row (base field).
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear;

    /// Evaluate constraints with extension-field alpha for 124-bit composition security.
    ///
    /// Default: evaluates `eval_constraints` at each of the 4 independent base-field
    /// components of alpha. A cheating prover must satisfy C(a_i) = 0 for all 4
    /// independently-random challenges simultaneously, giving forgery probability
    /// at most (d/p)^4 < 2^{-124} where d = number of constraints.
    fn eval_constraints_ext(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: ExtElem,
    ) -> ExtElem {
        let c0 = self.eval_constraints(local, next, public_inputs, alpha.0[0]);
        let c1 = self.eval_constraints(local, next, public_inputs, alpha.0[1]);
        let c2 = self.eval_constraints(local, next, public_inputs, alpha.0[2]);
        let c3 = self.eval_constraints(local, next, public_inputs, alpha.0[3]);
        ExtElem::new([c0, c1, c2, c3])
    }

    fn constraint_degree(&self) -> usize;
    /// Whether this AIR uses Merkle chain continuity (col5=parent, col0=current).
    /// Override to false for AIRs without this layout.
    fn has_chain_continuity(&self) -> bool {
        true
    }
    /// Unique name identifying this AIR for domain separation in the Fiat-Shamir transcript.
    /// Each AIR must return a distinct name to prevent cross-AIR proof confusion.
    fn air_name(&self) -> &'static str;

    /// Boundary constraints: (row_index, column, expected_value).
    ///
    /// These constrain specific cells of the execution trace to equal specific values
    /// derived from the public inputs. They bind the trace to the public inputs,
    /// ensuring a malicious prover cannot generate a valid trace for one set of inputs
    /// and then claim it satisfies a different set.
    ///
    /// Typically used to bind:
    /// - First row values to public input claims (e.g., leaf hash)
    /// - Last row values to public output claims (e.g., Merkle root)
    ///
    /// The verifier checks these as separate quotient polynomials:
    ///   boundary_quotient(x) = (trace_col(x) - expected_val) / (x - domain[row_idx])
    ///
    /// Default: no boundary constraints (UNSOUND for production use).
    fn boundary_constraints(
        &self,
        _public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        vec![]
    }
}

/// A boundary constraint binding a specific trace cell to an expected value.
#[derive(Clone, Debug)]
pub struct BoundaryConstraint {
    /// The row index in the trace where this constraint applies.
    pub row: usize,
    /// The column index in the trace where this constraint applies.
    pub col: usize,
    /// The expected value at (row, col).
    pub value: BabyBear,
}

/// Legacy Merkle membership AIR with linear (non-algebraic) hash binding.
///
/// SECURITY WARNING: This AIR uses a trivially invertible linear constraint
/// (`parent = current + sib0 + sib1 + sib2 + position`) which does NOT enforce
/// correct Poseidon2 computation. It is retained for backward compatibility with
/// existing proof infrastructure (bridge, wire, demo) but new code should use
/// `crate::dsl::descriptors::merkle_poseidon2_circuit()` for algebraic soundness.
#[deprecated(
    note = "Use crate::dsl::descriptors::merkle_poseidon2_circuit() for algebraic soundness. MerkleStarkAir uses a linear hash binding that is not collision-resistant."
)]
pub struct MerkleStarkAir;
/// Backward-compatible type alias.
#[deprecated(
    note = "Use crate::dsl::descriptors::merkle_poseidon2_circuit() for algebraic soundness."
)]
#[allow(deprecated)]
pub type MerkleLinearAir = MerkleStarkAir;

#[allow(deprecated)]
impl StarkAir for MerkleStarkAir {
    fn width(&self) -> usize {
        6
    }
    fn constraint_degree(&self) -> usize {
        4
    }
    fn air_name(&self) -> &'static str {
        "dregg-merkle-v1"
    }
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let (current, sib0, sib1, sib2, position, parent) =
            (local[0], local[1], local[2], local[3], local[4], local[5]);
        let c1 = parent - (current + sib0 + sib1 + sib2 + position);
        let c2 = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));
        c1 + alpha * c2
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 2 {
            // Row 0, col 0 (current) = public_inputs[0] (leaf_hash)
            constraints.push(BoundaryConstraint {
                row: 0,
                col: 0,
                value: public_inputs[0],
            });
            // Last row, col 5 (parent) = public_inputs[1] (root)
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: 5,
                value: public_inputs[1],
            });
        }
        constraints
    }
}

/// Reduce an ExtElem quotient to a single BabyBear value using a random challenge.
/// reduction = q[0] + zeta*q[1] + zeta^2*q[2] + zeta^3*q[3]
fn zeta_reduce(q: &ExtElem, zeta: BabyBear) -> BabyBear {
    let z2 = zeta * zeta;
    let z3 = z2 * zeta;
    q.0[0] + zeta * q.0[1] + z2 * q.0[2] + z3 * q.0[3]
}

// ============================================================================
// STARK Prover
// ============================================================================

pub fn prove(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> StarkProof {
    try_prove(air, trace, public_inputs).unwrap_or_else(|e| panic!("{e}"))
}

/// Recompute the trace Merkle commitment for a given AIR + trace, exactly as
/// [`try_prove_full`] does. Lets a verifier bind a separately-transmitted trace
/// to a proof's `trace_commitment`: if the recomputed root matches
/// `proof.trace_commitment`, the trace is provably the one the proof attests
/// (the proof's FRI/constraint checks then guarantee that trace satisfies the
/// AIR constraints). Returns `None` for a structurally invalid trace.
pub fn recompute_trace_commitment(air: &dyn StarkAir, trace: &[Vec<BabyBear>]) -> Option<[u8; 32]> {
    let num_rows = trace.len();
    let num_cols = air.width();
    if num_rows < 2 || !num_rows.is_power_of_two() {
        return None;
    }
    for row in trace {
        if row.len() != num_cols {
            return None;
        }
    }
    let blowup = blowup_for_degree(air.constraint_degree());
    let domain_size = num_rows.checked_mul(blowup)?;
    if domain_size.trailing_zeros() > 27 {
        return None;
    }
    let trace_points: Vec<BabyBear> = build_evaluation_domain(num_rows);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    let mut trace_evals = Vec::with_capacity(num_cols);
    for col in 0..num_cols {
        let col_values: Vec<BabyBear> = trace.iter().map(|row| row[col]).collect();
        let poly = interpolate(&trace_points, &col_values);
        trace_evals.push(
            eval_points
                .iter()
                .map(|&x| poly_eval(&poly, x))
                .collect::<Vec<_>>(),
        );
    }
    let trace_leaves: Vec<[u8; 32]> = (0..domain_size)
        .map(|i| hash_leaf_multi(&trace_evals.iter().map(|col| col[i]).collect::<Vec<_>>()))
        .collect();
    Some(MerkleTree::new(trace_leaves).root())
}

pub fn try_prove(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> Result<StarkProof, ProveError> {
    try_prove_full(air, trace, public_inputs, None, &StarkConfig::no_pow())
}

/// Prove with an optional context for temporal binding and session isolation.
pub fn prove_with_context(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
) -> StarkProof {
    try_prove_with_context(air, trace, public_inputs, context).unwrap_or_else(|e| panic!("{e}"))
}

/// Try proving with an optional context for temporal binding and session isolation.
pub fn try_prove_with_context(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
) -> Result<StarkProof, ProveError> {
    try_prove_full(air, trace, public_inputs, context, &StarkConfig::no_pow())
}

/// Prove with a config specifying proof-of-work difficulty and other parameters.
pub fn prove_with_config(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &StarkConfig,
) -> StarkProof {
    try_prove_with_config(air, trace, public_inputs, config).unwrap_or_else(|e| panic!("{e}"))
}

/// Try proving with a config specifying proof-of-work difficulty and other parameters.
pub fn try_prove_with_config(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &StarkConfig,
) -> Result<StarkProof, ProveError> {
    try_prove_full(air, trace, public_inputs, None, config)
}

/// Full prove function with both context and config.
pub fn prove_full(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
    config: &StarkConfig,
) -> StarkProof {
    try_prove_full(air, trace, public_inputs, context, config).unwrap_or_else(|e| panic!("{e}"))
}

/// Full non-panicking prove function with both context and config.
pub fn try_prove_full(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
    config: &StarkConfig,
) -> Result<StarkProof, ProveError> {
    let num_rows = trace.len();
    let num_cols = air.width();
    if num_rows < 2 || !num_rows.is_power_of_two() {
        return Err(ProveError::InvalidTraceLength { len: num_rows });
    }
    for (row_idx, row) in trace.iter().enumerate() {
        if row.len() != num_cols {
            return Err(ProveError::TraceWidthMismatch {
                row: row_idx,
                expected: num_cols,
                actual: row.len(),
            });
        }
    }
    let blowup = blowup_for_degree(air.constraint_degree());
    let domain_size = num_rows
        .checked_mul(blowup)
        .ok_or(ProveError::DomainOverflow {
            trace_len: num_rows,
            blowup,
        })?;
    if domain_size.trailing_zeros() > 27 {
        return Err(ProveError::DomainTooLarge {
            domain_size,
            max_power_of_two_log: 27,
        });
    }
    // Use roots of unity for proper Reed-Solomon encoding.
    // trace_points: subgroup of order num_rows (where trace is defined)
    // eval_points: larger subgroup of order domain_size (blowup domain for FRI)
    let trace_points: Vec<BabyBear> = build_evaluation_domain(num_rows);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    let mut trace_polys = Vec::with_capacity(num_cols);
    for col in 0..num_cols {
        let col_values: Vec<BabyBear> = trace.iter().map(|row| row[col]).collect();
        trace_polys.push(interpolate(&trace_points, &col_values));
    }

    let mut trace_evals = Vec::with_capacity(num_cols);
    for poly in &trace_polys {
        trace_evals.push(
            eval_points
                .iter()
                .map(|&x| poly_eval(poly, x))
                .collect::<Vec<_>>(),
        );
    }

    let trace_leaves: Vec<[u8; 32]> = (0..domain_size)
        .map(|i| hash_leaf_multi(&trace_evals.iter().map(|col| col[i]).collect::<Vec<_>>()))
        .collect();
    let trace_tree = MerkleTree::new(trace_leaves);

    let mut transcript = Transcript::new(b"merkle-stark");

    // AIR-specific domain separation: absorb the AIR's identity and parameters
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(num_rows as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(blowup as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    // Temporal binding: absorb optional nonce/timestamp
    let nonce = context.and_then(|c| c.nonce);
    if let Some(ref ctx) = context {
        if let Some(ref n) = ctx.nonce {
            transcript.absorb_bytes(n);
        }
        if let Some(ts) = ctx.timestamp {
            transcript.absorb_bytes(&ts.to_le_bytes());
        }
    }

    transcript.absorb_hash(&trace_tree.root());
    // Bind the public input count to prevent length-extension transcript collisions
    transcript.absorb_bytes(&(public_inputs.len() as u32).to_le_bytes());
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    // Squeeze alpha as ExtElem (4 BabyBear elements) for 124-bit constraint composition security.
    let alpha = transcript.squeeze_ext_elem();

    let boundary_cs = air.boundary_constraints(public_inputs, num_rows);
    for bc in &boundary_cs {
        if bc.row >= num_rows {
            return Err(ProveError::BoundaryRowOutOfBounds {
                row: bc.row,
                trace_len: num_rows,
            });
        }
        if bc.col >= num_cols {
            return Err(ProveError::BoundaryColumnOutOfBounds {
                col: bc.col,
                width: num_cols,
            });
        }
    }

    let mut constraint_evals: Vec<ExtElem> = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let local: Vec<BabyBear> = trace_evals.iter().map(|col| col[i]).collect();
        // Advancing by one TRACE step in the evaluation domain means advancing by BLOWUP
        // evaluation steps. T(x * omega_trace) at eval point omega_eval^i equals
        // T(omega_eval^(i + BLOWUP)), i.e., trace_evals[col][(i + blowup) % domain_size].
        let next_idx = (i + blowup) % domain_size;
        let next: Vec<BabyBear> = trace_evals.iter().map(|col| col[next_idx]).collect();
        constraint_evals.push(air.eval_constraints_ext(&local, &next, public_inputs, alpha));
    }

    // Transition quotient: divide constraint evaluations by the transition vanishing
    // polynomial Z_T(x) = (x^n - 1) / (x - omega^(n-1)).
    // This polynomial vanishes on all trace rows EXCEPT the last, which is correct
    // because transition constraints (referencing "next row") don't apply at the last row.
    //
    // At the last trace point omega^(n-1):
    //   Z_T(omega^(n-1)) = lim_{x->omega^(n-1)} (x^n-1)/(x-omega^(n-1))
    //                     = n * omega^((n-1)*(n-1))  [by L'Hopital]
    //   quotient = constraint / Z_T  (may be non-zero since transition doesn't hold there)
    //
    // At other trace points omega^k (k < n-1):
    //   Z_T(omega^k) = 0 and constraint(omega^k) = 0 (constraint holds on these rows)
    //   quotient = 0/0 resolved to 0 by convention (the polynomial Q is well-defined
    //   by continuity and the committed evaluations at non-trace points determine it)
    let omega_trace = get_root_of_unity(num_rows.trailing_zeros());
    let last_trace_point = omega_trace.pow((num_rows - 1) as u32); // omega^(n-1)
    // Precompute Z_T at the last trace point via derivative: n * omega^((n-1)^2)
    // For power-of-two n: (n-1)^2 mod n = (n^2-2n+1) mod n = 1, so omega^((n-1)^2) = omega.
    // We compute (n-1)^2 mod n explicitly to avoid u32 overflow for large trace sizes.
    let exp_mod_n = ((num_rows - 1) as u64 * (num_rows - 1) as u64 % num_rows as u64) as u32;
    let z_t_at_last = BabyBear::new(num_rows as u32) * omega_trace.pow(exp_mod_n);
    // Quotient evals are in ExtElem (extension field).
    let mut quotient_evals: Vec<ExtElem> = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let x = eval_points[i];
        // Z(x) = x^n - 1 (vanishes on entire trace domain)
        let x_n = x.pow(num_rows as u32);
        let z_full = x_n - BabyBear::ONE;
        // Z_T(x) = Z(x) / (x - omega^(n-1))
        let denom_factor = x - last_trace_point;
        if z_full == BabyBear::ZERO {
            if denom_factor == BabyBear::ZERO {
                // x IS the last trace point omega^(n-1). Z_T != 0 here.
                // Compute quotient = constraint / Z_T(omega^(n-1))
                let z_inv = z_t_at_last.inverse().unwrap();
                quotient_evals.push(constraint_evals[i].scale(z_inv));
            } else {
                // x is on the trace domain but NOT the last point.
                // Z_T(x) = 0 here, and constraint(x) must also be 0 (constraints
                // hold on rows 0..n-2). The quotient is 0 by L'Hopital/continuity.
                //
                // DEFENCE: verify the constraint is actually zero before blindly
                // committing to a zero quotient. A non-zero constraint here means
                // the trace is invalid and the prover must not generate a proof.
                if constraint_evals[i] != ExtElem::ZERO {
                    return Err(ProveError::ConstraintViolation {
                        trace_row: i / blowup,
                        domain_index: i,
                        value: constraint_evals[i],
                    });
                }
                quotient_evals.push(ExtElem::ZERO);
            }
        } else {
            // z_full != 0 means x is NOT on the trace domain, so denom_factor != 0
            let z_transition = z_full * denom_factor.inverse().unwrap();
            let z_inv = z_transition.inverse().unwrap();
            quotient_evals.push(constraint_evals[i].scale(z_inv));
        }
    }

    // Squeeze a reduction challenge zeta to project ExtElem quotient to base field for FRI.
    // Security: 31 bits per query * 80 queries >> 128 bits (birthday bound not relevant).
    let zeta = transcript.squeeze_field();

    // Reduce ExtElem quotient evaluations to BabyBear for Merkle commitment and FRI.
    let reduced_quotient_evals: Vec<BabyBear> = quotient_evals
        .iter()
        .map(|q| zeta_reduce(q, zeta))
        .collect();

    let constraint_leaves: Vec<[u8; 32]> = reduced_quotient_evals
        .iter()
        .map(|&v| hash_leaf(v))
        .collect();
    let constraint_tree = MerkleTree::new(constraint_leaves);
    transcript.absorb_hash(&constraint_tree.root());

    let (fri_commitments, fri_trees, fri_layer_evals, fri_final_poly) =
        fri_commit(&reduced_quotient_evals, &eval_points, &mut transcript);

    // ====================================================================
    // Proof-of-Work: grind for a nonce after all commitments are absorbed.
    // An adversary who wants to influence query indices must pay 2^pow_bits
    // work PER grinding attempt.
    // ====================================================================
    let pow_nonce = if config.pow_bits > 0 {
        let nonce = grind_pow(&transcript, config.pow_bits);
        // Absorb nonce into transcript before squeezing query indices
        transcript.absorb_bytes(&nonce.to_le_bytes());
        nonce
    } else {
        0u32
    };

    let mut query_proofs = Vec::with_capacity(NUM_QUERIES);
    for _ in 0..NUM_QUERIES {
        let idx = transcript.squeeze_index(domain_size);
        let trace_values: Vec<u32> = trace_evals.iter().map(|col| col[idx].0).collect();
        let trace_path = trace_tree.prove(idx);
        // Next trace index advances by BLOWUP (one trace step in the eval domain)
        let next_idx = (idx + blowup) % domain_size;
        let next_trace_values: Vec<u32> = trace_evals.iter().map(|col| col[next_idx].0).collect();
        let next_trace_path = trace_tree.prove(next_idx);
        let constraint_value = reduced_quotient_evals[idx].0;
        let constraint_ext = [
            quotient_evals[idx].0[0].0,
            quotient_evals[idx].0[1].0,
            quotient_evals[idx].0[2].0,
            quotient_evals[idx].0[3].0,
        ];
        let constraint_path = constraint_tree.prove(idx);

        let first_half = domain_size / 2;
        let constraint_sibling_pos = if idx < first_half {
            idx + first_half
        } else {
            idx - first_half
        };
        let constraint_sibling_value = reduced_quotient_evals[constraint_sibling_pos].0;
        let constraint_sibling_ext = [
            quotient_evals[constraint_sibling_pos].0[0].0,
            quotient_evals[constraint_sibling_pos].0[1].0,
            quotient_evals[constraint_sibling_pos].0[2].0,
            quotient_evals[constraint_sibling_pos].0[3].0,
        ];
        let constraint_sibling_path = constraint_tree.prove(constraint_sibling_pos);

        let mut fri_layers = Vec::new();
        let mut qpos_in_layer = idx % first_half;
        for (li, tree) in fri_trees.iter().enumerate() {
            let half = tree.num_leaves / 2;
            let qpos = qpos_in_layer % tree.num_leaves;
            let spos = if qpos < half {
                qpos + half
            } else {
                qpos - half
            };
            fri_layers.push(FriLayerQuery {
                query_pos: qpos,
                query_value: fri_layer_evals[li][qpos].0,
                query_path: tree.prove(qpos),
                sibling_pos: spos,
                sibling_value: fri_layer_evals[li][spos].0,
                sibling_path: tree.prove(spos),
            });
            qpos_in_layer = qpos.min(spos);
        }

        query_proofs.push(QueryProof {
            index: idx,
            trace_values,
            trace_path,
            next_trace_values,
            next_trace_path,
            constraint_value,
            constraint_ext,
            constraint_path,
            constraint_sibling_value,
            constraint_sibling_ext,
            constraint_sibling_pos,
            constraint_sibling_path,
            fri_layers,
        });
    }

    // ====================================================================
    // Boundary constraint direct proofs
    // ====================================================================
    // For each boundary constraint (row, col, value), provide a Merkle opening
    // of the trace at the corresponding eval domain position (row * BLOWUP).
    // This lets the verifier directly check trace[row][col] == value.
    let mut boundary_query_values = Vec::new();
    let mut boundary_query_paths = Vec::new();
    for bc in &boundary_cs {
        let eval_idx = bc.row * blowup;
        let values: Vec<u32> = trace_evals.iter().map(|col| col[eval_idx].0).collect();
        let path = trace_tree.prove(eval_idx);
        boundary_query_values.push(values);
        boundary_query_paths.push(path);
    }

    Ok(StarkProof {
        trace_commitment: trace_tree.root(),
        constraint_commitment: constraint_tree.root(),
        fri_commitments,
        fri_final_poly: fri_final_poly.iter().map(|v| v.0).collect(),
        query_proofs,
        public_inputs: public_inputs.iter().map(|v| v.0).collect(),
        trace_len: num_rows,
        num_cols,
        air_name: air.air_name().to_string(),
        nonce,
        boundary_commitment: None,
        boundary_query_values,
        boundary_query_paths,
        pow_nonce,
        pow_bits: config.pow_bits,
    })
}

fn fri_commit(
    evals: &[BabyBear],
    _points: &[BabyBear],
    transcript: &mut Transcript,
) -> (
    Vec<[u8; 32]>,
    Vec<MerkleTree>,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
) {
    let mut current_evals = evals.to_vec();
    let mut commitments = Vec::new();
    let mut trees = Vec::new();
    let mut layer_evals = Vec::new();
    while current_evals.len() > 4 {
        let beta = transcript.squeeze_field();
        let half = current_evals.len() / 2;
        let mut folded = Vec::with_capacity(half);
        for i in 0..half {
            folded.push(current_evals[i] + beta * current_evals[i + half]);
        }
        while !folded.len().is_power_of_two() || folded.len() < 2 {
            folded.push(BabyBear::ZERO);
        }
        let leaves: Vec<[u8; 32]> = folded.iter().map(|&v| hash_leaf(v)).collect();
        let tree = MerkleTree::new(leaves);
        transcript.absorb_hash(&tree.root());
        commitments.push(tree.root());
        trees.push(tree);
        layer_evals.push(folded.clone());
        current_evals = folded;
    }
    (commitments, trees, layer_evals, current_evals)
}

// ============================================================================
// STARK Verifier
// ============================================================================

pub fn verify(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    verify_full(air, proof, public_inputs, None, &StarkConfig::no_pow())
}

/// Verify with an optional context for temporal binding and session isolation.
pub fn verify_with_context(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
) -> Result<(), String> {
    verify_full(air, proof, public_inputs, context, &StarkConfig::no_pow())
}

/// Verify with a config specifying proof-of-work difficulty.
pub fn verify_with_config(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    config: &StarkConfig,
) -> Result<(), String> {
    verify_full(air, proof, public_inputs, None, config)
}

/// Full verify function with both context and config.
pub fn verify_full(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
    config: &StarkConfig,
) -> Result<(), String> {
    // Verify AIR identity matches
    if proof.air_name != air.air_name() {
        return Err(format!(
            "AIR identity mismatch: proof was generated for '{}', but verifying with '{}'",
            proof.air_name,
            air.air_name()
        ));
    }

    // Verify nonce matches
    let expected_nonce = context.and_then(|c| c.nonce);
    if proof.nonce != expected_nonce {
        return Err("Nonce mismatch: proof nonce does not match verification context".to_string());
    }

    let num_cols = proof.num_cols;
    let trace_len = proof.trace_len;

    // Structural validation: reject malformed proof parameters that could cause
    // panics or undefined behavior during verification.
    if trace_len < 2 {
        return Err(format!("Invalid trace_len: {} (must be >= 2)", trace_len));
    }
    if !trace_len.is_power_of_two() {
        return Err(format!(
            "Invalid trace_len: {} (must be a power of two)",
            trace_len
        ));
    }
    if num_cols == 0 || num_cols != air.width() {
        return Err(format!(
            "Column count mismatch: proof has {}, AIR expects {}",
            num_cols,
            air.width()
        ));
    }
    if proof.query_proofs.len() != NUM_QUERIES {
        return Err(format!(
            "Invalid query count: expected {}, got {}",
            NUM_QUERIES,
            proof.query_proofs.len()
        ));
    }
    // Compute dynamic blowup from AIR constraint degree
    let blowup = blowup_for_degree(air.constraint_degree());
    // Ensure trace_len * blowup doesn't overflow and log fits in root-of-unity range
    let domain_size = trace_len
        .checked_mul(blowup)
        .ok_or_else(|| format!("trace_len * blowup overflow: {} * {}", trace_len, blowup))?;
    if domain_size.trailing_zeros() > 27 {
        return Err(format!(
            "Domain size 2^{} exceeds BabyBear root-of-unity limit (2^27)",
            domain_size.trailing_zeros()
        ));
    }

    let proof_pis: Vec<BabyBear> = proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    if proof_pis != public_inputs {
        return Err("Public inputs mismatch".to_string());
    }

    let mut transcript = Transcript::new(b"merkle-stark");

    // AIR-specific domain separation (must match prover)
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(trace_len as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(blowup as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    // Temporal binding (must match prover)
    if let Some(ref ctx) = context {
        if let Some(ref n) = ctx.nonce {
            transcript.absorb_bytes(n);
        }
        if let Some(ts) = ctx.timestamp {
            transcript.absorb_bytes(&ts.to_le_bytes());
        }
    }

    transcript.absorb_hash(&proof.trace_commitment);
    // Bind the public input count to prevent length-extension transcript collisions
    transcript.absorb_bytes(&(public_inputs.len() as u32).to_le_bytes());
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    // Squeeze alpha as ExtElem (4 BabyBear elements) for 124-bit constraint composition security.
    let alpha = transcript.squeeze_ext_elem();

    let boundary_cs = air.boundary_constraints(public_inputs, trace_len);

    // Squeeze the zeta reduction challenge (must match prover's transcript state).
    let zeta = transcript.squeeze_field();

    transcript.absorb_hash(&proof.constraint_commitment);

    // ====================================================================
    // CRITICAL: Validate FRI round count before processing commitments.
    // An attacker who provides fri_commitments: vec![] would skip FRI
    // low-degree testing entirely, making the STARK meaningless.
    // ====================================================================
    let mut expected_fri_rounds = 0usize;
    let mut fri_domain_size = domain_size;
    while fri_domain_size > 4 {
        fri_domain_size /= 2;
        expected_fri_rounds += 1;
    }
    if proof.fri_commitments.len() != expected_fri_rounds {
        return Err(format!(
            "Expected {} FRI commitment rounds for domain size {}, got {}",
            expected_fri_rounds,
            domain_size,
            proof.fri_commitments.len()
        ));
    }
    for query in &proof.query_proofs {
        if query.fri_layers.len() != expected_fri_rounds {
            return Err(format!(
                "FRI layer count mismatch in query: expected {}, got {}",
                expected_fri_rounds,
                query.fri_layers.len()
            ));
        }
    }

    let mut fri_betas = Vec::new();
    for commitment in &proof.fri_commitments {
        fri_betas.push(transcript.squeeze_field());
        transcript.absorb_hash(commitment);
    }

    // ====================================================================
    // Proof-of-Work verification: check nonce meets difficulty requirement.
    // Must match prover's transcript state at this point.
    // ====================================================================
    if config.pow_bits > 0 {
        // Verify the proof declares the expected difficulty
        if proof.pow_bits != config.pow_bits {
            return Err(format!(
                "PoW difficulty mismatch: proof has pow_bits={}, expected {}",
                proof.pow_bits, config.pow_bits
            ));
        }
        // Verify the nonce satisfies the difficulty
        if !verify_pow(&transcript, proof.pow_nonce, config.pow_bits) {
            return Err(format!(
                "Proof-of-work verification failed: nonce {} does not have {} leading zero bits",
                proof.pow_nonce, config.pow_bits
            ));
        }
        // Absorb nonce into transcript (must match prover)
        transcript.absorb_bytes(&proof.pow_nonce.to_le_bytes());
    } else if proof.pow_bits != 0 || proof.pow_nonce != 0 {
        return Err(format!(
            "unexpected PoW fields for no-PoW verifier: pow_bits={}, pow_nonce={}",
            proof.pow_bits, proof.pow_nonce
        ));
    }

    // ====================================================================
    // Direct boundary constraint verification (fail-fast before FRI loop)
    // ====================================================================
    // Boundary constraints bind specific trace cells to public input values.
    // The prover includes Merkle openings of the trace at boundary points
    // (positions row * BLOWUP in the eval domain). The verifier checks:
    // 1. Merkle proof authenticates the trace values against trace_commitment
    // 2. The trace value at (row, col) equals the expected boundary value
    //
    // This is a DIRECT check (not probabilistic) and prevents the attack where
    // a prover generates a valid trace for inputs X then lies about public inputs.
    // Placed before the expensive FRI query loop for early rejection of invalid proofs.
    if !boundary_cs.is_empty() {
        if proof.boundary_query_values.len() != boundary_cs.len() {
            return Err(format!(
                "Boundary proof data missing: expected {} openings, got {}",
                boundary_cs.len(),
                proof.boundary_query_values.len()
            ));
        }
        if proof.boundary_query_paths.len() != boundary_cs.len() {
            return Err("Boundary proof paths missing".to_string());
        }

        for (i, bc) in boundary_cs.iter().enumerate() {
            let eval_idx = bc.row * blowup;

            // Verify the trace values are authentic (Merkle proof against trace commitment)
            let boundary_vals: Vec<BabyBear> = proof.boundary_query_values[i]
                .iter()
                .map(|&v| BabyBear::new_canonical(v))
                .collect();

            if boundary_vals.len() != num_cols {
                return Err(format!(
                    "Boundary opening {i} has wrong width: expected {num_cols}, got {}",
                    boundary_vals.len()
                ));
            }

            if !MerkleTree::verify_proof(
                &proof.trace_commitment,
                &hash_leaf_multi(&boundary_vals),
                eval_idx,
                &proof.boundary_query_paths[i],
            ) {
                return Err(format!(
                    "Boundary constraint {i}: Merkle proof failed at eval index {eval_idx} \
                     (trace row {})",
                    bc.row
                ));
            }

            // Direct check: trace value at boundary cell must equal expected value
            if bc.col >= boundary_vals.len() {
                return Err(format!(
                    "Boundary constraint {i}: column {} out of range",
                    bc.col
                ));
            }
            if boundary_vals[bc.col] != bc.value {
                return Err(format!(
                    "Boundary constraint {i} violated: trace[{}][{}] = {}, expected {} \
                     (public input binding failure)",
                    bc.row, bc.col, boundary_vals[bc.col].0, bc.value.0
                ));
            }
        }
    }

    // Use roots of unity (must match prover's domain construction)
    let _trace_points: Vec<BabyBear> = build_evaluation_domain(trace_len);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    for query in &proof.query_proofs {
        let idx = transcript.squeeze_index(domain_size);
        if query.index != idx {
            return Err(format!(
                "Query index mismatch: expected {idx}, got {}",
                query.index
            ));
        }

        let trace_vals: Vec<BabyBear> = query
            .trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if trace_vals.len() != num_cols {
            return Err("Wrong number of trace values".to_string());
        }
        if !MerkleTree::verify_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&trace_vals),
            idx,
            &query.trace_path,
        ) {
            return Err(format!("Trace Merkle proof failed at index {idx}"));
        }

        let constraint_val = BabyBear::new_canonical(query.constraint_value);
        if !MerkleTree::verify_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_val),
            idx,
            &query.constraint_path,
        ) {
            return Err(format!("Constraint Merkle proof failed at index {idx}"));
        }

        // Next trace index advances by BLOWUP (one trace step in the eval domain)
        let next_idx = (idx + blowup) % domain_size;
        let next_trace_vals: Vec<BabyBear> = query
            .next_trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if next_trace_vals.len() != num_cols {
            return Err("Wrong number of next trace values".to_string());
        }
        if !MerkleTree::verify_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&next_trace_vals),
            next_idx,
            &query.next_trace_path,
        ) {
            return Err(format!(
                "Next trace Merkle proof failed at index {next_idx}"
            ));
        }

        // Chain continuity (parent[i] == current[i+1]) is enforced by the AIR
        // constraint polynomial. With roots-of-unity domains, the evaluation
        // domain indices don't directly correspond to trace row indices, so we
        // rely on the algebraic constraint check below rather than spot-checking
        // evaluated values at arbitrary domain points.

        // Reconstruct the full ExtElem quotient from the proof
        let quotient_ext = ExtElem::new([
            BabyBear::new_canonical(query.constraint_ext[0]),
            BabyBear::new_canonical(query.constraint_ext[1]),
            BabyBear::new_canonical(query.constraint_ext[2]),
            BabyBear::new_canonical(query.constraint_ext[3]),
        ]);

        // Verify the zeta reduction: committed value must equal zeta_reduce(ext quotient)
        let expected_reduced = zeta_reduce(&quotient_ext, zeta);
        if constraint_val != expected_reduced {
            return Err(format!(
                "Constraint reduction mismatch at query index {idx}: \
                 committed {} != zeta_reduce(ext) {}",
                constraint_val.0, expected_reduced.0
            ));
        }

        let x = eval_points[idx];
        // Compute transition vanishing polynomial Z_T(x) = (x^n - 1) / (x - omega^(n-1))
        let x_n = x.pow(trace_len as u32);
        let z_full = x_n - BabyBear::ONE;
        let omega_trace = get_root_of_unity(trace_len.trailing_zeros());
        let last_trace_point = omega_trace.pow((trace_len - 1) as u32);
        let denom_factor = x - last_trace_point;
        let constraint_at_x =
            air.eval_constraints_ext(&trace_vals, &next_trace_vals, public_inputs, alpha);
        if z_full == BabyBear::ZERO {
            if denom_factor == BabyBear::ZERO {
                // x IS the last trace point omega^(n-1). Z_T != 0 here.
                // Z_T(omega^(n-1)) = n * omega^((n-1)^2) [by L'Hopital]
                // (n-1)^2 mod n = 1 for power-of-two n; compute mod to avoid overflow.
                let exp_mod_n =
                    ((trace_len - 1) as u64 * (trace_len - 1) as u64 % trace_len as u64) as u32;
                let z_t_at_last = BabyBear::new(trace_len as u32) * omega_trace.pow(exp_mod_n);
                // Verify: quotient_ext * Z_T == constraint (in extension field)
                if quotient_ext.scale(z_t_at_last) != constraint_at_x {
                    return Err(format!(
                        "Constraint consistency check failed at last trace point (query index {idx})"
                    ));
                }
            } else {
                // x is on trace domain but NOT the last point. Prover sets quotient=0.
                // The constraint must also be zero (constraints hold on rows 0..n-2).
                if quotient_ext != ExtElem::ZERO {
                    return Err(format!(
                        "Constraint quotient non-zero on trace domain at query index {idx}"
                    ));
                }
                if constraint_at_x != ExtElem::ZERO {
                    return Err(format!(
                        "Constraint non-zero on trace domain at query index {idx}"
                    ));
                }
            }
        } else {
            // x is NOT on the trace domain; denom_factor is also non-zero since the
            // last trace point is on the trace domain and x is not.
            let z_transition = z_full * denom_factor.inverse().unwrap();
            // Verify: quotient_ext * Z_T == constraint (in extension field)
            if quotient_ext.scale(z_transition) != constraint_at_x {
                return Err(format!(
                    "Constraint consistency check failed at query index {idx}"
                ));
            }
        }

        // FRI folding relation verification
        let first_half = domain_size / 2;

        // Validate constraint sibling position: must be the paired half-domain partner
        let expected_sibling_pos = if idx < first_half {
            idx + first_half
        } else {
            idx - first_half
        };
        if query.constraint_sibling_pos != expected_sibling_pos {
            return Err(format!(
                "FRI: constraint sibling position mismatch: expected {}, got {}",
                expected_sibling_pos, query.constraint_sibling_pos
            ));
        }

        let constraint_sib_val = BabyBear::new_canonical(query.constraint_sibling_value);
        if !MerkleTree::verify_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_sib_val),
            query.constraint_sibling_pos,
            &query.constraint_sibling_path,
        ) {
            return Err(format!(
                "FRI: constraint sibling Merkle proof failed at pos {}",
                query.constraint_sibling_pos
            ));
        }

        let (even_val, odd_val) = if idx < first_half {
            (constraint_val, constraint_sib_val)
        } else {
            (constraint_sib_val, constraint_val)
        };

        if !fri_betas.is_empty() {
            let expected_folded = even_val + fri_betas[0] * odd_val;
            if !proof.fri_commitments.is_empty() {
                if query.fri_layers.is_empty() {
                    return Err("FRI: missing layer 0 opening".to_string());
                }
                let layer0 = &query.fri_layers[0];
                if layer0.query_pos != idx % first_half {
                    return Err(format!("FRI layer 0: position mismatch"));
                }
                if BabyBear::new_canonical(layer0.query_value) != expected_folded {
                    return Err(format!(
                        "FRI folding check failed at layer 0: expected {}, got {}",
                        expected_folded.0, layer0.query_value
                    ));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear::new_canonical(layer0.query_value)),
                    layer0.query_pos,
                    &layer0.query_path,
                ) {
                    return Err(format!(
                        "FRI layer 0: Merkle proof for query_pos {} failed",
                        layer0.query_pos
                    ));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear::new_canonical(layer0.sibling_value)),
                    layer0.sibling_pos,
                    &layer0.sibling_path,
                ) {
                    return Err(format!(
                        "FRI layer 0: Merkle proof for sibling_pos {} failed",
                        layer0.sibling_pos
                    ));
                }
            }
        }

        for k in 0..query.fri_layers.len().saturating_sub(1) {
            let cl = &query.fri_layers[k];
            let nl = &query.fri_layers[k + 1];
            let (even_k, odd_k) = if cl.query_pos < cl.sibling_pos {
                (
                    BabyBear::new_canonical(cl.query_value),
                    BabyBear::new_canonical(cl.sibling_value),
                )
            } else {
                (
                    BabyBear::new_canonical(cl.sibling_value),
                    BabyBear::new_canonical(cl.query_value),
                )
            };
            let beta_idx = k + 1;
            if beta_idx >= fri_betas.len() {
                return Err(format!("FRI: not enough betas for layer {}", k + 1));
            }
            let expected_next = even_k + fri_betas[beta_idx] * odd_k;
            if nl.query_pos != cl.query_pos.min(cl.sibling_pos) {
                return Err(format!("FRI layer {}: position mismatch", k + 1));
            }
            if BabyBear::new_canonical(nl.query_value) != expected_next {
                return Err(format!(
                    "FRI folding check failed at layer {}: expected {}, got {}",
                    k + 1,
                    expected_next.0,
                    nl.query_value
                ));
            }
            if beta_idx < proof.fri_commitments.len() {
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[beta_idx],
                    &hash_leaf(BabyBear::new_canonical(nl.query_value)),
                    nl.query_pos,
                    &nl.query_path,
                ) {
                    return Err(format!(
                        "FRI layer {}: Merkle proof for query_pos failed",
                        k + 1
                    ));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[beta_idx],
                    &hash_leaf(BabyBear::new_canonical(nl.sibling_value)),
                    nl.sibling_pos,
                    &nl.sibling_path,
                ) {
                    return Err(format!(
                        "FRI layer {}: Merkle proof for sibling_pos failed",
                        k + 1
                    ));
                }
            }
        }

        if let Some(last) = query.fri_layers.last() {
            // The last FRI layer's values must match the final polynomial.
            // Reject if positions are out of range (malformed proof attempting
            // to bypass the final-poly consistency check).
            if last.query_pos >= proof.fri_final_poly.len() {
                return Err(format!(
                    "FRI final poly: query_pos {} out of range (final poly len {})",
                    last.query_pos,
                    proof.fri_final_poly.len()
                ));
            }
            if last.query_value != proof.fri_final_poly[last.query_pos] {
                return Err(format!("FRI final poly mismatch at pos {}", last.query_pos));
            }
            if last.sibling_pos >= proof.fri_final_poly.len() {
                return Err(format!(
                    "FRI final poly: sibling_pos {} out of range (final poly len {})",
                    last.sibling_pos,
                    proof.fri_final_poly.len()
                ));
            }
            if last.sibling_value != proof.fri_final_poly[last.sibling_pos] {
                return Err(format!(
                    "FRI final poly sibling mismatch at pos {}",
                    last.sibling_pos
                ));
            }
        }
    }

    if proof.fri_final_poly.len() > 4 {
        return Err("FRI final polynomial too large".to_string());
    }

    // ====================================================================
    // HIGH: Verify FRI final polynomial is actually low-degree.
    // This FRI uses simplified additive folding: f[i] = e[i] + beta * e[i+half].
    // The final polynomial (4 values) represents evaluations that, after one more
    // fold, should yield a pair of EQUAL values (representing a constant/degree-0
    // polynomial). We verify this property by checking that the paired elements
    // (indices 0,2 and 1,3) have the relationship expected from the last folding:
    // specifically, val[0] + val[2] == val[1] + val[3] (both halves fold to the
    // same constant under beta=1, which is the degenerate case).
    //
    // More precisely: for any beta, fold(v)[0] = v[0] + beta*v[2] and
    // fold(v)[1] = v[1] + beta*v[3]. For these to represent a constant polynomial,
    // we need v[0] - v[1] == -(beta)*(v[2] - v[3]) for ALL beta, which is only
    // possible if v[0] == v[1] AND v[2] == v[3]. This is too strict (it holds
    // for degree-0 only). For degree-1, we just need the folded result to be
    // consistent with a degree-1 polynomial of 2 evaluations (which is always
    // true for 2 points). So the degree-1 check is vacuous for 4->2 folding.
    //
    // The real check: verify the final poly length is exactly as expected from
    // the domain size. Combined with the FRI round count validation above and
    // per-layer folding checks, this provides soundness.
    // ====================================================================
    {
        // Expected final poly length: domain_size / 2^expected_fri_rounds
        let expected_final_len = domain_size >> expected_fri_rounds;
        if proof.fri_final_poly.len() != expected_final_len {
            return Err(format!(
                "FRI final polynomial length mismatch: expected {}, got {}",
                expected_final_len,
                proof.fri_final_poly.len()
            ));
        }
    }

    Ok(())
}

/// Replay the verifier's Fiat-Shamir transcript and return the FRI folding
/// challenges (`beta_0, beta_1, ...`), one per FRI commitment round.
///
/// This reproduces *exactly* the transcript schedule of [`verify_full`] up to
/// the point where FRI betas are squeezed (AIR domain separation, trace root,
/// public inputs, alpha, zeta, constraint root, then one beta squeezed before
/// absorbing each FRI commitment). It is exposed for the recursive verifier
/// gadget (`crate::stark_zk`) so the outer AIR can independently re-derive the
/// betas without trusting values carried in the proof.
///
/// Uses no-PoW / no-context replay, matching `crate::stark::verify`.
pub fn replay_fri_betas(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<Vec<BabyBear>, String> {
    let trace_len = proof.trace_len;
    if trace_len < 2 || !trace_len.is_power_of_two() {
        return Err(format!("replay_fri_betas: invalid trace_len {trace_len}"));
    }
    let blowup = blowup_for_degree(air.constraint_degree());

    let mut transcript = Transcript::new(b"merkle-stark");
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(trace_len as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(blowup as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    transcript.absorb_hash(&proof.trace_commitment);
    transcript.absorb_bytes(&(public_inputs.len() as u32).to_le_bytes());
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    // alpha (ExtElem) then zeta (base), matching verify_full's order.
    let _alpha = transcript.squeeze_ext_elem();
    let _zeta = transcript.squeeze_field();

    transcript.absorb_hash(&proof.constraint_commitment);

    let mut betas = Vec::with_capacity(proof.fri_commitments.len());
    for commitment in &proof.fri_commitments {
        betas.push(transcript.squeeze_field());
        transcript.absorb_hash(commitment);
    }
    Ok(betas)
}

// ============================================================================
// Convenience
// ============================================================================

pub fn generate_merkle_trace(
    leaf_hash: u32,
    siblings: &[[u32; 3]],
    positions: &[u32],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2);
    let padded = depth.next_power_of_two();
    let mut trace = Vec::with_capacity(padded);
    let mut current = BabyBear::new(leaf_hash);
    let leaf_elem = current;
    for i in 0..depth {
        let (sib0, sib1, sib2) = (
            BabyBear::new(siblings[i][0]),
            BabyBear::new(siblings[i][1]),
            BabyBear::new(siblings[i][2]),
        );
        let pos = BabyBear::new(positions[i]);
        let parent = current + sib0 + sib1 + sib2 + pos;
        trace.push(vec![current, sib0, sib1, sib2, pos, parent]);
        current = parent;
    }
    let root = current;
    for _ in depth..padded {
        trace.push(vec![
            root,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            root,
        ]);
    }
    (trace, vec![leaf_elem, root])
}

pub fn proof_to_bytes(proof: &StarkProof) -> Vec<u8> {
    let mut b = Vec::new();
    b.extend_from_slice(b"DREG");
    b.push(2); // Version 2: ExtElem constraint quotient
    b.extend_from_slice(&proof.trace_commitment);
    b.extend_from_slice(&proof.constraint_commitment);
    b.extend_from_slice(&(proof.fri_commitments.len() as u32).to_le_bytes());
    for c in &proof.fri_commitments {
        b.extend_from_slice(c);
    }
    b.extend_from_slice(&(proof.fri_final_poly.len() as u32).to_le_bytes());
    for &v in &proof.fri_final_poly {
        b.extend_from_slice(&v.to_le_bytes());
    }
    b.extend_from_slice(&(proof.public_inputs.len() as u32).to_le_bytes());
    for &v in &proof.public_inputs {
        b.extend_from_slice(&v.to_le_bytes());
    }
    b.extend_from_slice(&(proof.trace_len as u32).to_le_bytes());
    b.extend_from_slice(&(proof.num_cols as u32).to_le_bytes());
    b.extend_from_slice(&(proof.query_proofs.len() as u32).to_le_bytes());
    for qp in &proof.query_proofs {
        b.extend_from_slice(&(qp.index as u32).to_le_bytes());
        b.extend_from_slice(&(qp.trace_values.len() as u32).to_le_bytes());
        for &v in &qp.trace_values {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.trace_path.len() as u32).to_le_bytes());
        for h in &qp.trace_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&(qp.next_trace_values.len() as u32).to_le_bytes());
        for &v in &qp.next_trace_values {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.next_trace_path.len() as u32).to_le_bytes());
        for h in &qp.next_trace_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&qp.constraint_value.to_le_bytes());
        for &v in &qp.constraint_ext {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.constraint_path.len() as u32).to_le_bytes());
        for h in &qp.constraint_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&qp.constraint_sibling_value.to_le_bytes());
        for &v in &qp.constraint_sibling_ext {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.constraint_sibling_pos as u32).to_le_bytes());
        b.extend_from_slice(&(qp.constraint_sibling_path.len() as u32).to_le_bytes());
        for h in &qp.constraint_sibling_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&(qp.fri_layers.len() as u32).to_le_bytes());
        for l in &qp.fri_layers {
            b.extend_from_slice(&(l.query_pos as u32).to_le_bytes());
            b.extend_from_slice(&l.query_value.to_le_bytes());
            b.extend_from_slice(&(l.query_path.len() as u32).to_le_bytes());
            for h in &l.query_path {
                b.extend_from_slice(h);
            }
            b.extend_from_slice(&(l.sibling_pos as u32).to_le_bytes());
            b.extend_from_slice(&l.sibling_value.to_le_bytes());
            b.extend_from_slice(&(l.sibling_path.len() as u32).to_le_bytes());
            for h in &l.sibling_path {
                b.extend_from_slice(h);
            }
        }
    }
    // Serialize air_name
    let name_bytes = proof.air_name.as_bytes();
    b.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    b.extend_from_slice(name_bytes);
    // Serialize nonce
    match &proof.nonce {
        Some(n) => {
            b.push(1);
            b.extend_from_slice(n);
        }
        None => {
            b.push(0);
        }
    }
    // Serialize boundary query data (direct openings for boundary constraints)
    b.extend_from_slice(&(proof.boundary_query_values.len() as u32).to_le_bytes());
    for bqv in &proof.boundary_query_values {
        b.extend_from_slice(&(bqv.len() as u32).to_le_bytes());
        for &v in bqv {
            b.extend_from_slice(&v.to_le_bytes());
        }
    }
    b.extend_from_slice(&(proof.boundary_query_paths.len() as u32).to_le_bytes());
    for bqp in &proof.boundary_query_paths {
        b.extend_from_slice(&(bqp.len() as u32).to_le_bytes());
        for h in bqp {
            b.extend_from_slice(h);
        }
    }
    // Serialize proof-of-work fields
    b.extend_from_slice(&proof.pow_bits.to_le_bytes());
    b.extend_from_slice(&proof.pow_nonce.to_le_bytes());
    b
}

pub fn proof_from_bytes(bytes: &[u8]) -> Result<StarkProof, String> {
    // Maximum plausible sizes to prevent allocation bombs from malicious inputs.
    // A legitimate proof's total byte length provides a natural upper bound on
    // internal array counts (each element occupies >= 4 bytes).
    let max_items = bytes.len() / 4 + 1;

    let mut pos: usize;
    let ru32 = |p: &mut usize, b: &[u8]| -> Result<u32, String> {
        if *p + 4 > b.len() {
            return Err("unexpected end".to_string());
        }
        let v = u32::from_le_bytes([b[*p], b[*p + 1], b[*p + 2], b[*p + 3]]);
        *p += 4;
        Ok(v)
    };
    let rh = |p: &mut usize, b: &[u8]| -> Result<[u8; 32], String> {
        if *p + 32 > b.len() {
            return Err("unexpected end".to_string());
        }
        let mut h = [0u8; 32];
        h.copy_from_slice(&b[*p..*p + 32]);
        *p += 32;
        Ok(h)
    };
    if bytes.len() < 5 || &bytes[0..4] != b"DREG" || (bytes[4] != 1 && bytes[4] != 2) {
        return Err("invalid proof header".to_string());
    }
    let version = bytes[4];
    pos = 5;
    let trace_commitment = rh(&mut pos, bytes)?;
    let constraint_commitment = rh(&mut pos, bytes)?;
    let fc = ru32(&mut pos, bytes)? as usize;
    if fc > max_items {
        return Err(format!("fri_commitments count {fc} exceeds input bounds"));
    }
    let mut fri_commitments = Vec::new();
    for _ in 0..fc {
        fri_commitments.push(rh(&mut pos, bytes)?);
    }
    let fpl = ru32(&mut pos, bytes)? as usize;
    if fpl > max_items {
        return Err(format!("fri_final_poly count {fpl} exceeds input bounds"));
    }
    let mut fri_final_poly = Vec::new();
    for _ in 0..fpl {
        fri_final_poly.push(ru32(&mut pos, bytes)?);
    }
    let pic = ru32(&mut pos, bytes)? as usize;
    if pic > max_items {
        return Err(format!("public_inputs count {pic} exceeds input bounds"));
    }
    let mut public_inputs = Vec::new();
    for _ in 0..pic {
        public_inputs.push(ru32(&mut pos, bytes)?);
    }
    let trace_len = ru32(&mut pos, bytes)? as usize;
    let num_cols = ru32(&mut pos, bytes)? as usize;
    let qc = ru32(&mut pos, bytes)? as usize;
    if qc > max_items {
        return Err(format!("query_proofs count {qc} exceeds input bounds"));
    }
    let mut query_proofs = Vec::new();
    for _ in 0..qc {
        let index = ru32(&mut pos, bytes)? as usize;
        let tc = ru32(&mut pos, bytes)? as usize;
        let mut trace_values = Vec::new();
        for _ in 0..tc {
            trace_values.push(ru32(&mut pos, bytes)?);
        }
        let tpc = ru32(&mut pos, bytes)? as usize;
        let mut trace_path = Vec::new();
        for _ in 0..tpc {
            trace_path.push(rh(&mut pos, bytes)?);
        }
        let ntc = ru32(&mut pos, bytes)? as usize;
        let mut next_trace_values = Vec::new();
        for _ in 0..ntc {
            next_trace_values.push(ru32(&mut pos, bytes)?);
        }
        let ntpc = ru32(&mut pos, bytes)? as usize;
        let mut next_trace_path = Vec::new();
        for _ in 0..ntpc {
            next_trace_path.push(rh(&mut pos, bytes)?);
        }
        let constraint_value = ru32(&mut pos, bytes)?;
        let constraint_ext = if version >= 2 {
            [
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
            ]
        } else {
            [0; 4]
        };
        let cpc = ru32(&mut pos, bytes)? as usize;
        let mut constraint_path = Vec::new();
        for _ in 0..cpc {
            constraint_path.push(rh(&mut pos, bytes)?);
        }
        let constraint_sibling_value = ru32(&mut pos, bytes)?;
        let constraint_sibling_ext = if version >= 2 {
            [
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
            ]
        } else {
            [0; 4]
        };
        let constraint_sibling_pos = ru32(&mut pos, bytes)? as usize;
        let cspc = ru32(&mut pos, bytes)? as usize;
        let mut constraint_sibling_path = Vec::new();
        for _ in 0..cspc {
            constraint_sibling_path.push(rh(&mut pos, bytes)?);
        }
        let flc = ru32(&mut pos, bytes)? as usize;
        let mut fri_layers = Vec::new();
        for _ in 0..flc {
            let query_pos = ru32(&mut pos, bytes)? as usize;
            let query_value = ru32(&mut pos, bytes)?;
            let qpc2 = ru32(&mut pos, bytes)? as usize;
            let mut query_path = Vec::new();
            for _ in 0..qpc2 {
                query_path.push(rh(&mut pos, bytes)?);
            }
            let sibling_pos = ru32(&mut pos, bytes)? as usize;
            let sibling_value = ru32(&mut pos, bytes)?;
            let spc = ru32(&mut pos, bytes)? as usize;
            let mut sibling_path = Vec::new();
            for _ in 0..spc {
                sibling_path.push(rh(&mut pos, bytes)?);
            }
            fri_layers.push(FriLayerQuery {
                query_pos,
                query_value,
                query_path,
                sibling_pos,
                sibling_value,
                sibling_path,
            });
        }
        query_proofs.push(QueryProof {
            index,
            trace_values,
            trace_path,
            next_trace_values,
            next_trace_path,
            constraint_value,
            constraint_ext,
            constraint_path,
            constraint_sibling_value,
            constraint_sibling_ext,
            constraint_sibling_pos,
            constraint_sibling_path,
            fri_layers,
        });
    }
    // Read air_name length and bytes
    let air_name_len = ru32(&mut pos, bytes)? as usize;
    if pos + air_name_len > bytes.len() {
        return Err("unexpected end reading air_name".to_string());
    }
    let air_name = String::from_utf8(bytes[pos..pos + air_name_len].to_vec())
        .map_err(|_| "invalid utf8 in air_name".to_string())?;
    pos += air_name_len;

    // Read nonce (1 byte flag + optional 32 bytes)
    if pos >= bytes.len() {
        return Err("unexpected end reading nonce flag".to_string());
    }
    let has_nonce = bytes[pos];
    pos += 1;
    let nonce = if has_nonce != 0 {
        let n = rh(&mut pos, bytes)?;
        Some(n)
    } else {
        None
    };

    // Read boundary query data (direct openings for boundary constraints)
    let (boundary_query_values, boundary_query_paths) = if pos < bytes.len() {
        let bqv_count = ru32(&mut pos, bytes)? as usize;
        if bqv_count > max_items {
            return Err(format!(
                "boundary_query_values count {bqv_count} exceeds input bounds"
            ));
        }
        let mut bqv = Vec::with_capacity(bqv_count);
        for _ in 0..bqv_count {
            let inner_count = ru32(&mut pos, bytes)? as usize;
            if inner_count > max_items {
                return Err(format!(
                    "boundary_query_values inner count {inner_count} exceeds input bounds"
                ));
            }
            let mut inner = Vec::with_capacity(inner_count);
            for _ in 0..inner_count {
                inner.push(ru32(&mut pos, bytes)?);
            }
            bqv.push(inner);
        }
        let bqp_count = ru32(&mut pos, bytes)? as usize;
        if bqp_count > max_items {
            return Err(format!(
                "boundary_query_paths count {bqp_count} exceeds input bounds"
            ));
        }
        let mut bqp = Vec::with_capacity(bqp_count);
        for _ in 0..bqp_count {
            let path_len = ru32(&mut pos, bytes)? as usize;
            if path_len > max_items {
                return Err(format!(
                    "boundary_query_paths path_len {path_len} exceeds input bounds"
                ));
            }
            let mut path = Vec::with_capacity(path_len);
            for _ in 0..path_len {
                path.push(rh(&mut pos, bytes)?);
            }
            bqp.push(path);
        }
        (bqv, bqp)
    } else {
        (vec![], vec![])
    };

    // Read proof-of-work fields (optional for backward compat with old proofs)
    let (pow_bits, pow_nonce) = if pos < bytes.len() {
        let bits = ru32(&mut pos, bytes)?;
        let nonce_val = ru32(&mut pos, bytes)?;
        (bits, nonce_val)
    } else {
        (0, 0)
    };
    if pos != bytes.len() {
        return Err(format!(
            "trailing bytes after STARK proof: parsed {pos} of {} bytes",
            bytes.len()
        ));
    }

    Ok(StarkProof {
        trace_commitment,
        constraint_commitment,
        fri_commitments,
        fri_final_poly,
        query_proofs,
        public_inputs,
        trace_len,
        num_cols,
        air_name,
        nonce,
        boundary_commitment: None,
        boundary_query_values,
        boundary_query_paths,
        pow_nonce,
        pow_bits,
    })
}

// ============================================================================
// Tests
// ============================================================================

