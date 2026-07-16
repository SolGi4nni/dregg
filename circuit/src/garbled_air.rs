//! STARK AIR for proving correct garbled circuit evaluation.
//!
//! The prover generates a STARK proof that they correctly evaluated a Poseidon2-garbled
//! circuit gate-by-gate. Each gate evaluation is one Poseidon2 call, which maps
//! naturally to STARK constraints.
//!
//! # Trace Layout
//!
//! One row per gate evaluation:
//!
//! | Columns   | Description                                              |
//! |-----------|----------------------------------------------------------|
//! | 0..7      | Left input label (8 BabyBear elements)                   |
//! | 8..15     | Right input label (8 BabyBear elements)                  |
//! | 16        | Gate index                                               |
//! | 17..24    | Hash output: Poseidon2(left || right || gate_index)       |
//! | 25..32    | Table entry (garbled ciphertext for this row)             |
//! | 33..40    | Decrypted output label                                   |
//! | 41        | Circuit commitment (constant across all rows)             |
//! | 42        | Output label hash (constant, last row only meaningful)    |
//!
//! # Constraints
//!
//! 1. **Hash correctness:** `hash_output == Poseidon2(left || right || gate_index)`
//! 2. **Decryption correctness:** `output_label == table_entry - hash_output`
//! 3. **Wire chaining:** For connected gates, the output label of one gate equals
//!    an input label of the next gate (enforced by the circuit topology).
//! 4. **Public input binding:** `circuit_commitment` matches public_inputs[0],
//!    `output_label_hash` matches public_inputs[1].
//!
//! # Public Inputs
//!
//! `[circuit_commitment, output_label_hash]`
//!
//! - `circuit_commitment`: Poseidon2 hash of all garbled tables (binds to specific circuit).
//! - `output_label_hash`: Poseidon2 hash of the output label (verifier checks against
//!   known true/false label hashes).

// ============================================================================
// Column layout
// ============================================================================

/// Trace width for the garbled evaluation AIR.
/// Widened: circuit_commitment and output_label_hash are now 4 elements each (WideHash).
pub const GARBLED_EVAL_AIR_WIDTH: usize = 49;

/// Column indices.
pub mod col {
    /// Left input label start (8 elements).
    pub const LEFT_LABEL_START: usize = 0;
    /// Right input label start (8 elements).
    pub const RIGHT_LABEL_START: usize = 8;
    /// Gate index.
    pub const GATE_INDEX: usize = 16;
    /// Hash output start (8 elements): Poseidon2(left || right || gate_index).
    pub const HASH_OUTPUT_START: usize = 17;
    /// Table entry start (8 elements): the garbled ciphertext.
    pub const TABLE_ENTRY_START: usize = 25;
    /// Decrypted output label start (8 elements).
    pub const OUTPUT_LABEL_START: usize = 33;
    /// Circuit commitment start (4 elements, WideHash for 124-bit binding).
    pub const CIRCUIT_COMMITMENT: usize = 41;
    /// Output label hash start (4 elements, WideHash for 124-bit binding).
    pub const OUTPUT_LABEL_HASH: usize = 45;

    /// Get column for left label element i.
    #[inline]
    pub const fn left(i: usize) -> usize {
        LEFT_LABEL_START + i
    }

    /// Get column for right label element i.
    #[inline]
    pub const fn right(i: usize) -> usize {
        RIGHT_LABEL_START + i
    }

    /// Get column for hash output element i.
    #[inline]
    pub const fn hash_out(i: usize) -> usize {
        HASH_OUTPUT_START + i
    }

    /// Get column for table entry element i.
    #[inline]
    pub const fn table_entry(i: usize) -> usize {
        TABLE_ENTRY_START + i
    }

    /// Get column for output label element i.
    #[inline]
    pub const fn output(i: usize) -> usize {
        OUTPUT_LABEL_START + i
    }
}

// ============================================================================
// AIR definition
// ============================================================================

/// The garbled evaluation AIR.
///
/// Proves that a garbled circuit was correctly evaluated gate-by-gate using
/// Poseidon2 as the garbling hash.
///
/// # Deprecation
///
/// Use `crate::dsl::garbled::garbled_dsl_circuit()` (constraints:
/// `garbled_extended_descriptor()`, trace: `generate_extended_garbled_trace()`).
/// The DSL version supports multi-gate chaining, gate type selectors, and
/// padding — a strict superset of this 49-column AIR's capabilities.
///
/// LAW #1 NOTE: unlike the DSL path, this type's `constraints()` is 16 sites of
/// Rust-authored algebra. `Dregg2.Circuit.Emit.GarbledEvalEmit` exists; this AIR
/// should be retired against it, not kept as a parallel hand-authored circuit.
#[deprecated(
    note = "Use crate::dsl::garbled::garbled_dsl_circuit(). This AIR is superseded by the 56-column DSL garbled evaluation circuit."
)]
// ============================================================================
// Tests
// ============================================================================
#[cfg(test)]
mod tests {
    // The former `GarbledEvaluationAir` tests (valid_evaluation / tampered_output_label_fails /
    // wrong_circuit_commitment_fails) exercised the hand-authored AIR retired under architectural law #1.
    // Their teeth live — strictly stronger — on the Lean-emitted path:
    // `circuit-prove/tests/garbled_eval_emit_gate.rs::{forged_commitment_pi_refuses,
    // forged_table_entry_refuses, forged_gate_index_delta_refuses}`, byte-pinned to
    // `metatheory/Dregg2/Circuit/Emit/GarbledEvalEmit.lean`. This module keeps only the live layout
    // constants (`GARBLED_EVAL_AIR_WIDTH`, `col`) that `dsl/garbled.rs` imports.
}
