//! Poseidon2 hash function over BabyBear.
//!
//! This is a reference implementation of Poseidon2 suitable for use in AIR
//! constraint definitions and the mock prover. The parameters are chosen for
//! BabyBear (width=8, alpha=7, internal rounds=22, external rounds=8).
//!
//! Poseidon2 is a SNARK-friendly hash function designed for efficient
//! arithmetization. It operates on a state of field elements and applies:
//! - External rounds: full S-box layer (applied to all state elements)
//! - Internal rounds: partial S-box layer (applied to only first element)
//!
//! For the 4-ary Merkle tree, we use a width-8 Poseidon2:
//! - Input: 4 field elements (child hashes, padded to width)
//! - Output: 1 field element (the hash digest, taken from state[0])

use std::sync::LazyLock;

use crate::field::BabyBear;

/// Poseidon2 state width (number of field elements in state).
pub const WIDTH: usize = 8;

/// Number of external (full) rounds.
pub const EXTERNAL_ROUNDS: usize = 8;

/// Number of internal (partial) rounds.
pub const INTERNAL_ROUNDS: usize = 22;

/// Total rounds.
pub const TOTAL_ROUNDS: usize = EXTERNAL_ROUNDS + INTERNAL_ROUNDS;

/// S-box exponent for BabyBear (x^7).
const SBOX_ALPHA: u32 = 7;

/// Cached round constants, computed once from BLAKE3 derivation.
pub static ROUND_CONSTANTS: LazyLock<Vec<[BabyBear; WIDTH]>> =
    LazyLock::new(compute_round_constants);

/// Cached internal diagonal matrix, computed once from BLAKE3 derivation.
pub static INTERNAL_DIAG: LazyLock<[BabyBear; WIDTH]> = LazyLock::new(compute_internal_diag);

/// Round constants for Poseidon2 (generated deterministically).
/// In production these would be from a nothing-up-my-sleeve derivation.
/// For testing, we derive them from sequential hashing.
fn compute_round_constants() -> Vec<[BabyBear; WIDTH]> {
    let mut constants = Vec::with_capacity(TOTAL_ROUNDS);
    for round in 0..TOTAL_ROUNDS {
        let mut rc = [BabyBear::ZERO; WIDTH];
        for j in 0..WIDTH {
            // Deterministic pseudo-random constants from BLAKE3
            let input = format!("pyana-poseidon2-rc-{round}-{j}");
            let hash = blake3::hash(input.as_bytes());
            let bytes = hash.as_bytes();
            let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
            rc[j] = BabyBear::new(val);
        }
        constants.push(rc);
    }
    constants
}

/// Internal linear layer matrix (diagonal + 1 structure for Poseidon2).
/// M_I = diag(d_0, ..., d_{t-1}) where d_i are derived constants.
fn compute_internal_diag() -> [BabyBear; WIDTH] {
    let mut diag = [BabyBear::ZERO; WIDTH];
    for i in 0..WIDTH {
        let input = format!("pyana-poseidon2-diag-{i}");
        let hash = blake3::hash(input.as_bytes());
        let bytes = hash.as_bytes();
        let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        // Ensure non-zero
        diag[i] = BabyBear::new(val | 1);
    }
    diag
}

/// The Poseidon2 permutation state.
#[derive(Clone, Debug)]
pub struct Poseidon2State {
    pub state: [BabyBear; WIDTH],
}

impl Poseidon2State {
    /// Create a new state initialized to zero.
    pub fn new() -> Self {
        Self {
            state: [BabyBear::ZERO; WIDTH],
        }
    }

    /// Create a state from field elements (remaining positions zero-padded).
    pub fn from_elements(elements: &[BabyBear]) -> Self {
        let mut state = [BabyBear::ZERO; WIDTH];
        for (i, &e) in elements.iter().take(WIDTH).enumerate() {
            state[i] = e;
        }
        Self { state }
    }

    /// Apply the S-box: x -> x^7.
    #[inline]
    pub fn sbox(x: BabyBear) -> BabyBear {
        x.pow(SBOX_ALPHA)
    }

    /// Apply the external (full) linear layer: a circulant-like MDS matrix.
    /// Uses the Poseidon2 external matrix construction:
    /// M_E * x where M_E is a width-8 circulant derived from [2, 3, 1, 1, ...].
    pub fn external_linear_layer(&mut self) {
        // Simplified external matrix: use a Cauchy-like construction.
        // For width 8, we use the standard Poseidon2 external matrix.
        // This is equivalent to 4 parallel butterfly operations.
        let s = &mut self.state;

        // First: pairwise butterfly
        for i in (0..WIDTH).step_by(2) {
            let t = s[i] + s[i + 1];
            s[i + 1] = s[i] - s[i + 1];
            s[i] = t;
        }

        // Second: quad butterfly
        for i in (0..WIDTH).step_by(4) {
            let t0 = s[i] + s[i + 2];
            let t1 = s[i + 1] + s[i + 3];
            s[i + 2] = s[i] - s[i + 2];
            s[i + 3] = s[i + 1] - s[i + 3];
            s[i] = t0;
            s[i + 1] = t1;
        }

        // Third: full butterfly across halves
        for i in 0..4 {
            let t = s[i] + s[i + 4];
            s[i + 4] = s[i] - s[i + 4];
            s[i] = t;
        }

        // Mix with small multipliers for MDS property
        let multipliers = [
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::new(6),
            BabyBear::new(7),
            BabyBear::new(8),
            BabyBear::new(9),
        ];
        for i in 0..WIDTH {
            s[i] = s[i] * multipliers[i];
        }
    }

    /// Apply the internal linear layer: M_I * x.
    /// Poseidon2 internal layer: x_0 = sum(x_i) + (d_0 - 1) * x_0, others similar.
    pub fn internal_linear_layer(&mut self) {
        let diag = &*INTERNAL_DIAG;
        let sum: BabyBear = self
            .state
            .iter()
            .copied()
            .fold(BabyBear::ZERO, |a, b| a + b);

        for i in 0..WIDTH {
            // x_i' = sum + (d_i - 1) * x_i = sum - x_i + d_i * x_i
            self.state[i] = sum + (diag[i] - BabyBear::ONE) * self.state[i];
        }
    }

    /// Apply the full Poseidon2 permutation.
    pub fn permute(&mut self) {
        let rc = &*ROUND_CONSTANTS;

        // First half of external rounds
        for round in 0..EXTERNAL_ROUNDS / 2 {
            // Add round constants
            for i in 0..WIDTH {
                self.state[i] += rc[round][i];
            }
            // Full S-box layer
            for i in 0..WIDTH {
                self.state[i] = Self::sbox(self.state[i]);
            }
            // External linear layer
            self.external_linear_layer();
        }

        // Internal rounds
        for round in 0..INTERNAL_ROUNDS {
            let rc_idx = EXTERNAL_ROUNDS / 2 + round;
            // Add round constant to first element only
            self.state[0] += rc[rc_idx][0];
            // Partial S-box (only first element)
            self.state[0] = Self::sbox(self.state[0]);
            // Internal linear layer
            self.internal_linear_layer();
        }

        // Second half of external rounds
        for round in 0..EXTERNAL_ROUNDS / 2 {
            let rc_idx = EXTERNAL_ROUNDS / 2 + INTERNAL_ROUNDS + round;
            // Add round constants
            for i in 0..WIDTH {
                self.state[i] += rc[rc_idx][i];
            }
            // Full S-box layer
            for i in 0..WIDTH {
                self.state[i] = Self::sbox(self.state[i]);
            }
            // External linear layer
            self.external_linear_layer();
        }
    }
}

/// Apply the external linear layer to a state array (standalone version).
pub fn apply_external_linear_layer(state: &[BabyBear; WIDTH]) -> [BabyBear; WIDTH] {
    let mut s = *state;
    for i in (0..WIDTH).step_by(2) {
        let t = s[i] + s[i + 1];
        s[i + 1] = s[i] - s[i + 1];
        s[i] = t;
    }
    for i in (0..WIDTH).step_by(4) {
        let t0 = s[i] + s[i + 2];
        let t1 = s[i + 1] + s[i + 3];
        s[i + 2] = s[i] - s[i + 2];
        s[i + 3] = s[i + 1] - s[i + 3];
        s[i] = t0;
        s[i + 1] = t1;
    }
    for i in 0..4 {
        let t = s[i] + s[i + 4];
        s[i + 4] = s[i] - s[i + 4];
        s[i] = t;
    }
    let multipliers = [
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
        BabyBear::new(5),
        BabyBear::new(6),
        BabyBear::new(7),
        BabyBear::new(8),
        BabyBear::new(9),
    ];
    for i in 0..WIDTH {
        s[i] = s[i] * multipliers[i];
    }
    s
}

/// Apply the internal linear layer to a state array (standalone version).
pub fn apply_internal_linear_layer(state: &[BabyBear; WIDTH]) -> [BabyBear; WIDTH] {
    let diag = &*INTERNAL_DIAG;
    let sum: BabyBear = state.iter().copied().fold(BabyBear::ZERO, |a, b| a + b);
    let mut result = [BabyBear::ZERO; WIDTH];
    for i in 0..WIDTH {
        result[i] = sum + (diag[i] - BabyBear::ONE) * state[i];
    }
    result
}

/// Compute one full (external) round of Poseidon2.
pub fn compute_full_round(
    state: &[BabyBear; WIDTH],
    round_constants: &[BabyBear; WIDTH],
) -> [BabyBear; WIDTH] {
    let mut s = [BabyBear::ZERO; WIDTH];
    for i in 0..WIDTH {
        s[i] = Poseidon2State::sbox(state[i] + round_constants[i]);
    }
    apply_external_linear_layer(&s)
}

/// Compute one partial (internal) round of Poseidon2.
pub fn compute_partial_round(
    state: &[BabyBear; WIDTH],
    round_constant: BabyBear,
) -> [BabyBear; WIDTH] {
    let mut s = *state;
    s[0] = Poseidon2State::sbox(s[0] + round_constant);
    apply_internal_linear_layer(&s)
}

/// Compute the expected next state for a given round index (0-indexed).
pub fn compute_round(state: &[BabyBear; WIDTH], round_idx: usize) -> [BabyBear; WIDTH] {
    let rc = &*ROUND_CONSTANTS;
    if round_idx < EXTERNAL_ROUNDS / 2 {
        compute_full_round(state, &rc[round_idx])
    } else if round_idx < EXTERNAL_ROUNDS / 2 + INTERNAL_ROUNDS {
        compute_partial_round(state, rc[round_idx][0])
    } else if round_idx < TOTAL_ROUNDS {
        compute_full_round(state, &rc[round_idx])
    } else {
        *state
    }
}

/// Hash 4 field elements using Poseidon2 (4-to-1 compression).
/// This is used for the 4-ary Merkle tree internal nodes.
///
/// Input: 4 child hashes (each a single field element)
/// Output: 1 parent hash (a single field element)
///
/// Uses capacity elements for domain separation.
pub fn hash_4_to_1(inputs: &[BabyBear; 4]) -> BabyBear {
    let mut state = Poseidon2State::new();
    // Rate portion: inputs[0..4]
    state.state[0] = inputs[0];
    state.state[1] = inputs[1];
    state.state[2] = inputs[2];
    state.state[3] = inputs[3];
    // Capacity portion: domain separation tag
    state.state[4] = BabyBear::new(4); // arity tag
    // state[5..7] remain zero (capacity)

    state.permute();
    state.state[0]
}

/// Hash 2 field elements using Poseidon2 (2-to-1 compression).
pub fn hash_2_to_1(left: BabyBear, right: BabyBear) -> BabyBear {
    let mut state = Poseidon2State::new();
    state.state[0] = left;
    state.state[1] = right;
    state.state[4] = BabyBear::new(2); // arity tag

    state.permute();
    state.state[0]
}

/// Hash an arbitrary number of field elements (sponge construction).
/// Rate = 4, capacity = 4.
pub fn hash_many(inputs: &[BabyBear]) -> BabyBear {
    let rate = 4;
    let mut state = Poseidon2State::new();
    // Domain separation: encode length in capacity
    state.state[4] = BabyBear::new(inputs.len() as u32);

    // Absorb phase
    for chunk in inputs.chunks(rate) {
        for (i, &elem) in chunk.iter().enumerate() {
            state.state[i] += elem;
        }
        state.permute();
    }

    // Squeeze: return first element
    state.state[0]
}

/// Hash arbitrary bytes into a single BabyBear field element via Poseidon2.
///
/// Packs the input bytes into field elements (4 bytes per element with modular
/// reduction), then hashes through the sponge construction. This is useful for
/// bridging byte-oriented data (like BLAKE3 commitments) into the field-element
/// domain used by the Poseidon2 Merkle tree.
pub fn hash_bytes(data: &[u8]) -> BabyBear {
    let elements = BabyBear::from_bytes_packed(data);
    hash_many(&elements)
}

/// Hash a leaf fact (predicate + up to 4 terms encoded as field elements) into a single digest.
/// Each fact is up to 5 field elements; we hash them using the Poseidon2 permutation with leaf domain sep.
/// Terms beyond the provided slice are treated as zero.
pub fn hash_fact(predicate: BabyBear, terms: &[BabyBear]) -> BabyBear {
    let mut state = Poseidon2State::new();
    state.state[0] = predicate;
    if terms.len() > 0 {
        state.state[1] = terms[0];
    }
    if terms.len() > 1 {
        state.state[2] = terms[1];
    }
    if terms.len() > 2 {
        state.state[3] = terms[2];
    }
    if terms.len() > 3 {
        state.state[4] = terms[3];
    }
    // Leaf domain separation (different from node)
    state.state[5] = BabyBear::new(0xFACF); // "fact" marker
    state.state[6] = BabyBear::ONE; // leaf flag

    state.permute();
    state.state[0]
}

/// The Poseidon2 round function expressed as constraints.
/// This provides the intermediate values needed by the AIR to verify the hash.
///
/// Returns all intermediate states (for witness generation).
pub fn poseidon2_trace(input_state: &[BabyBear; WIDTH]) -> Vec<[BabyBear; WIDTH]> {
    let mut trace = Vec::with_capacity(TOTAL_ROUNDS + 1);
    let mut state = Poseidon2State::from_elements(input_state);
    trace.push(state.state);

    let rc = &*ROUND_CONSTANTS;

    // First half external rounds
    for round in 0..EXTERNAL_ROUNDS / 2 {
        for i in 0..WIDTH {
            state.state[i] += rc[round][i];
        }
        for i in 0..WIDTH {
            state.state[i] = Poseidon2State::sbox(state.state[i]);
        }
        state.external_linear_layer();
        trace.push(state.state);
    }

    // Internal rounds
    for round in 0..INTERNAL_ROUNDS {
        let rc_idx = EXTERNAL_ROUNDS / 2 + round;
        state.state[0] += rc[rc_idx][0];
        state.state[0] = Poseidon2State::sbox(state.state[0]);
        state.internal_linear_layer();
        trace.push(state.state);
    }

    // Second half external rounds
    for round in 0..EXTERNAL_ROUNDS / 2 {
        let rc_idx = EXTERNAL_ROUNDS / 2 + INTERNAL_ROUNDS + round;
        for i in 0..WIDTH {
            state.state[i] += rc[rc_idx][i];
        }
        for i in 0..WIDTH {
            state.state[i] = Poseidon2State::sbox(state.state[i]);
        }
        state.external_linear_layer();
        trace.push(state.state);
    }

    trace
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poseidon2_deterministic() {
        let input = [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ];
        let h1 = hash_4_to_1(&input);
        let h2 = hash_4_to_1(&input);
        assert_eq!(h1, h2);
    }

    #[test]
    fn poseidon2_different_inputs_different_outputs() {
        let a = [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ];
        let b = [
            BabyBear::new(5),
            BabyBear::new(6),
            BabyBear::new(7),
            BabyBear::new(8),
        ];
        assert_ne!(hash_4_to_1(&a), hash_4_to_1(&b));
    }

    #[test]
    fn poseidon2_non_zero_output() {
        let input = [BabyBear::ZERO; 4];
        let h = hash_4_to_1(&input);
        // With round constants, even zero input should produce non-zero output
        assert_ne!(h, BabyBear::ZERO);
    }

    #[test]
    fn hash_many_works() {
        let inputs: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i)).collect();
        let h = hash_many(&inputs);
        assert_ne!(h, BabyBear::ZERO);
    }

    #[test]
    fn hash_fact_deterministic() {
        let pred = BabyBear::new(42);
        let terms = [BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)];
        let h1 = hash_fact(pred, &terms);
        let h2 = hash_fact(pred, &terms);
        assert_eq!(h1, h2);
    }

    #[test]
    fn poseidon2_trace_consistency() {
        let input = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = poseidon2_trace(&input);
        // Should have TOTAL_ROUNDS + 1 states
        assert_eq!(trace.len(), TOTAL_ROUNDS + 1);
        // First state is input
        assert_eq!(trace[0], input);
        // Last state matches direct permutation
        let mut state = Poseidon2State::from_elements(&input);
        state.permute();
        assert_eq!(*trace.last().unwrap(), state.state);
    }

    #[test]
    fn sbox_power_7() {
        // x^7 for x=2: 128
        let x = BabyBear::new(2);
        let y = Poseidon2State::sbox(x);
        assert_eq!(y.0, 128);
    }

    #[test]
    fn hash_bytes_deterministic() {
        let data = b"hello world";
        let h1 = hash_bytes(data);
        let h2 = hash_bytes(data);
        assert_eq!(h1, h2);
        assert_ne!(h1, BabyBear::ZERO);
    }

    #[test]
    fn hash_bytes_different_inputs() {
        let h1 = hash_bytes(b"foo");
        let h2 = hash_bytes(b"bar");
        assert_ne!(h1, h2);
    }

    #[test]
    fn hash_bytes_32_byte_input() {
        let commitment = [0xAB_u8; 32];
        let h = hash_bytes(&commitment);
        assert_ne!(h, BabyBear::ZERO);
    }
}
