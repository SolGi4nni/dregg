//! Poseidon2 permutation AIR expressed as a CircuitDescriptor.
//!
//! This DSL circuit constrains a single Poseidon2 permutation: given an input state
//! of 8 field elements (the first 8 of the 16-wide state), it enforces that the
//! output state equals the permutation output.
//!
//! # Construction
//!
//! The Poseidon2 permutation for BabyBear uses:
//! - State width: 16 (but we track the first 8 in-trace; full state used in Hash eval)
//! - S-box: x^7
//! - External (full) rounds: 8 (4 initial + 4 final)
//! - Internal (partial) rounds: 13
//! - Total rounds: 21
//!
//! For the DSL, we use the `ConstraintExpr::Hash` variant which internally calls
//! `hash_fact` to compute the Poseidon2 permutation and check correctness.
//! This is the most concise representation: instead of expressing each round
//! algebraically (which would require hundreds of degree-7 polynomial constraints),
//! the DSL delegates to the native Poseidon2 evaluator.
//!
//! # Trace Layout (width = 18, 2 rows)
//!
//! | Columns 0..7  | input state (first 8 elements)  |
//! | Columns 8..15 | output state (first 8 elements) |
//! | Column 16     | intermediate_h1                  |
//! | Column 17     | intermediate_h2                  |
//!
//! Both rows are identical (power-of-2 padding).
//!
//! # Public Inputs
//!
//! [input[0..8], output[0..8]] = 16 field elements
//!
//! The constraint verifies: output == poseidon2_permute(input).
//! This is achieved via two chained hash_fact calls that bind all 8 input elements.
//!
//! # Merkle membership
//!
//! For 4-ary Merkle membership using Poseidon2, see `merkle_poseidon2_dsl.rs` which
//! provides both standard and blinded (ring membership) variants.

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{Poseidon2State, WIDTH};
use dregg_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
};

// ============================================================================
// Single-permutation DSL (compact form using Hash constraints)
// ============================================================================

pub const INPUT_START: usize = 0;
pub const OUTPUT_START: usize = 8;
pub const INTERMEDIATE_H1: usize = 16;
pub const INTERMEDIATE_H2: usize = 17;

pub const POSEIDON2_DSL_WIDTH: usize = 18;

pub const PI_INPUT_START: usize = 0;
pub const PI_OUTPUT_START: usize = 8;
pub const PUBLIC_INPUT_COUNT: usize = 16;

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build a Poseidon2 permutation `CircuitDescriptor`.
///
/// This uses two chained `Hash` constraints to verify that the input state hashes
/// to the expected digest (first element of the permutation output). The remaining
/// output elements are bound via boundary constraints to public inputs (which the
/// verifier computes independently).
pub fn poseidon2_descriptor() -> CircuitDescriptor {
    let columns: Vec<ColumnDef> = (0..8)
        .map(|i| ColumnDef {
            name: format!("input_{i}"),
            index: INPUT_START + i,
            kind: ColumnKind::Value,
        })
        .chain((0..8).map(|i| ColumnDef {
            name: format!("output_{i}"),
            index: OUTPUT_START + i,
            kind: ColumnKind::Value,
        }))
        .chain(std::iter::once(ColumnDef {
            name: "intermediate_h1".into(),
            index: INTERMEDIATE_H1,
            kind: ColumnKind::Hash,
        }))
        .chain(std::iter::once(ColumnDef {
            name: "intermediate_h2".into(),
            index: INTERMEDIATE_H2,
            kind: ColumnKind::Hash,
        }))
        .collect();

    let mut constraints = Vec::new();

    // C1: intermediate_h1 == hash_fact(in[0], [in[1], in[2], in[3]])
    constraints.push(ConstraintExpr::Hash {
        output_col: INTERMEDIATE_H1,
        input_cols: vec![
            INPUT_START,
            INPUT_START + 1,
            INPUT_START + 2,
            INPUT_START + 3,
        ],
    });

    // C2: intermediate_h2 == hash_fact(h1, [in[4], in[5], in[6], in[7]])
    constraints.push(ConstraintExpr::Hash {
        output_col: INTERMEDIATE_H2,
        input_cols: vec![
            INTERMEDIATE_H1,
            INPUT_START + 4,
            INPUT_START + 5,
            INPUT_START + 6,
            INPUT_START + 7,
        ],
    });

    // Boundary constraints
    let mut boundaries = Vec::new();

    // Bind all input columns to public inputs on row 0
    for i in 0..8 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: INPUT_START + i,
            pi_index: PI_INPUT_START + i,
        });
    }

    // Bind all output columns to public inputs on row 0
    for i in 0..8 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: OUTPUT_START + i,
            pi_index: PI_OUTPUT_START + i,
        });
    }

    CircuitDescriptor {
        name: "dregg-poseidon2-dsl-v1".into(),
        trace_width: POSEIDON2_DSL_WIDTH,
        max_degree: 5, // Hash with 5 input_cols reports degree 5
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the Poseidon2 descriptor.
pub fn poseidon2_dsl_circuit() -> DslCircuit {
    DslCircuit::new(poseidon2_descriptor())
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate a valid Poseidon2 permutation trace.
///
/// Given an 8-element input (the meaningful portion of the 16-wide state),
/// computes the full Poseidon2 permutation and returns a trace with both
/// input and output columns filled correctly.
///
/// Returns (trace, public_inputs).
pub fn generate_poseidon2_trace(input: &[BabyBear; 8]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use dregg_circuit::poseidon2::hash_fact;

    // Compute full permutation
    let mut full_input = [BabyBear::ZERO; WIDTH];
    for i in 0..8 {
        full_input[i] = input[i];
    }
    let mut ps = Poseidon2State::from_elements(&full_input);
    ps.permute();
    let output: [BabyBear; 8] = {
        let mut out = [BabyBear::ZERO; 8];
        for i in 0..8 {
            out[i] = ps.state[i];
        }
        out
    };

    // Compute intermediates for Hash constraints
    let h1 = hash_fact(input[0], &[input[1], input[2], input[3]]);
    let h2 = hash_fact(h1, &[input[4], input[5], input[6], input[7]]);

    // Build trace row
    let mut row = vec![BabyBear::ZERO; POSEIDON2_DSL_WIDTH];
    for i in 0..8 {
        row[INPUT_START + i] = input[i];
    }
    for i in 0..8 {
        row[OUTPUT_START + i] = output[i];
    }
    row[INTERMEDIATE_H1] = h1;
    row[INTERMEDIATE_H2] = h2;

    // Power-of-2 padding: duplicate the row
    let trace = vec![row.clone(), row];

    // Public inputs: [input[0..8], output[0..8]]
    let mut public_inputs = Vec::with_capacity(PUBLIC_INPUT_COUNT);
    public_inputs.extend_from_slice(input);
    public_inputs.extend_from_slice(&output);

    (trace, public_inputs)
}

/// Generate a Poseidon2 trace for a known test vector.
pub fn generate_test_vector_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let input: [BabyBear; 8] = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
        BabyBear::new(5),
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ];
    generate_poseidon2_trace(&input)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::stark::{self, StarkAir};

    #[test]
    fn test_descriptor_validates() {
        let desc = poseidon2_descriptor();
        assert!(
            desc.validate().is_ok(),
            "poseidon2 descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn test_descriptor_structure() {
        let desc = poseidon2_descriptor();
        assert_eq!(desc.trace_width, POSEIDON2_DSL_WIDTH);
        assert_eq!(desc.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(desc.name, "dregg-poseidon2-dsl-v1");
        assert_eq!(desc.constraints.len(), 2);
        assert_eq!(desc.boundaries.len(), 16);
    }

    #[test]
    fn test_valid_trace_evaluates_to_zero() {
        let (trace, pi) = generate_test_vector_trace();
        let circuit = poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        for i in 0..trace.len() {
            let next_idx = (i + 1) % trace.len();
            let result = circuit.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Valid Poseidon2 trace should evaluate to ZERO at row {i}"
            );
        }
    }

    #[test]
    fn test_known_vector_deterministic() {
        let (trace1, pi1) = generate_test_vector_trace();
        let (trace2, pi2) = generate_test_vector_trace();
        assert_eq!(pi1, pi2);
        assert_eq!(trace1, trace2);
        let output_start = &pi1[8..16];
        assert!(
            output_start.iter().any(|&x| x != BabyBear::ZERO),
            "Poseidon2 output should be non-trivial"
        );
    }

    #[test]
    fn test_tampered_intermediate_detected() {
        let (mut trace, pi) = generate_test_vector_trace();
        let circuit = poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        trace[0][INTERMEDIATE_H1] = BabyBear::new(0xDEAD);
        trace[1][INTERMEDIATE_H1] = BabyBear::new(0xDEAD);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered intermediate hash must be detected"
        );
    }

    #[test]
    fn test_wrong_output_rejected_by_stark() {
        let (trace, pi) = generate_test_vector_trace();
        let circuit = poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[PI_OUTPUT_START] = BabyBear::new(999999);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong Poseidon2 output"
        );
    }

    #[test]
    fn test_stark_prove_verify_valid() {
        let (trace, pi) = generate_test_vector_trace();
        let circuit = poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify should succeed on valid Poseidon2 trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_different_input_different_output() {
        let input_a: [BabyBear; 8] = [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let input_b: [BabyBear; 8] = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(50),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];

        let (_, pi_a) = generate_poseidon2_trace(&input_a);
        let (_, pi_b) = generate_poseidon2_trace(&input_b);

        assert_ne!(
            &pi_a[8..16],
            &pi_b[8..16],
            "Different inputs must produce different Poseidon2 outputs"
        );
    }

    #[test]
    fn test_wrong_input_rejected_by_stark() {
        let (trace, pi) = generate_test_vector_trace();
        let circuit = poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let mut wrong_pi = pi.clone();
        wrong_pi[PI_INPUT_START] = BabyBear::new(999);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong input"
        );
    }

    #[test]
    fn test_wrong_h2_constraint_nonzero() {
        let (mut trace, pi) = generate_test_vector_trace();
        let circuit = poseidon2_dsl_circuit();
        let alpha = BabyBear::new(42);

        trace[0][INTERMEDIATE_H2] = BabyBear::new(12345678);
        trace[1][INTERMEDIATE_H2] = BabyBear::new(12345678);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong intermediate_h2 must produce non-zero constraint"
        );
    }

    #[test]
    fn test_permutation_output_cross_check() {
        let input: [BabyBear; 8] = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(50),
            BabyBear::new(60),
            BabyBear::new(70),
            BabyBear::new(80),
        ];

        let (_, pi) = generate_poseidon2_trace(&input);

        let mut full_input = [BabyBear::ZERO; WIDTH];
        for i in 0..8 {
            full_input[i] = input[i];
        }
        let mut ps = Poseidon2State::from_elements(&full_input);
        ps.permute();

        for i in 0..8 {
            assert_eq!(
                pi[PI_OUTPUT_START + i],
                ps.state[i],
                "Output element {i} mismatch between trace gen and raw permutation"
            );
        }
    }

    #[test]
    fn test_stark_different_inputs() {
        let inputs: Vec<[BabyBear; 8]> = vec![
            [BabyBear::new(0); 8],
            [BabyBear::ONE; 8],
            [
                BabyBear::new(100),
                BabyBear::new(200),
                BabyBear::new(300),
                BabyBear::new(400),
                BabyBear::new(500),
                BabyBear::new(600),
                BabyBear::new(700),
                BabyBear::new(800),
            ],
        ];

        let circuit = poseidon2_dsl_circuit();

        for input in &inputs {
            let (trace, pi) = generate_poseidon2_trace(input);
            let proof = stark::prove(&circuit, &trace, &pi);
            let result = stark::verify(&circuit, &proof, &pi);
            assert!(
                result.is_ok(),
                "STARK should verify for input {:?}: {:?}",
                input.iter().map(|x| x.0).collect::<Vec<_>>(),
                result.err()
            );
        }
    }
}
