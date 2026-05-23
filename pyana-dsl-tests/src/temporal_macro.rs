//! Temporal predicate defined using the `#[pyana_circuit]` macro.
//!
//! This is the macro-based equivalent of `temporal_dsl.rs` which manually
//! constructs a `CircuitDescriptor`. The macro generates a struct + `impl StarkAir`
//! that produces identical prove/verify results.

use pyana_circuit::field::BabyBear;
use pyana_dsl::pyana_circuit;

// Column layout constants (same as temporal_dsl.rs)
pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
pub const ACC_PLUS_ONE: usize = STEP_INDEX + 1; // 35
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 36
pub const TRACE_WIDTH: usize = STEP_PLUS_ONE + 1; // 37

/// Public input layout: [num_steps]
pub const PI_NUM_STEPS: usize = 0;
pub const PUBLIC_INPUT_COUNT: usize = 1;

#[pyana_circuit]
mod temporal_predicate {
    const WIDTH: usize = 37;
    const DEGREE: usize = 2;
    const PI_COUNT: usize = 1;

    mod col {
        pub const VALUE: usize = 0;
        pub const THRESHOLD: usize = 1;
        pub const DIFF: usize = 2;
        pub const DIFF_BITS_START: usize = 3;
        pub const NUM_DIFF_BITS: usize = 30;
        pub const ACCUMULATOR: usize = 33;
        pub const STEP_INDEX: usize = 34;
        pub const ACC_PLUS_ONE: usize = 35;
        pub const STEP_PLUS_ONE: usize = 36;
    }

    // Per-row constraints
    fn constraints(
        local: &[pyana_circuit::field::BabyBear],
        _next: &[pyana_circuit::field::BabyBear],
        pi: &[pyana_circuit::field::BabyBear],
    ) -> Vec<pyana_circuit::field::BabyBear> {
        use pyana_circuit::field::BabyBear;

        let mut cs = Vec::new();

        // C1: diff = value - threshold
        cs.push(local[col::DIFF] - (local[col::VALUE] - local[col::THRESHOLD]));

        // C2: Each diff_bit is binary
        for i in 0..col::NUM_DIFF_BITS {
            let bit = local[col::DIFF_BITS_START + i];
            cs.push(bit * (bit - BabyBear::ONE));
        }

        // C3: Bit reconstruction: sum(diff_bits[i] * 2^i) == diff
        {
            let mut reconstructed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            let two = BabyBear::new(2);
            for i in 0..col::NUM_DIFF_BITS {
                reconstructed = reconstructed + local[col::DIFF_BITS_START + i] * power_of_two;
                power_of_two = power_of_two * two;
            }
            cs.push(reconstructed - local[col::DIFF]);
        }

        // C4: High bit is zero (range proof: diff < 2^30 => non-negative)
        cs.push(local[col::DIFF_BITS_START + col::NUM_DIFF_BITS - 1]);

        // C5: acc_plus_one = accumulator + 1
        cs.push(
            local[col::ACC_PLUS_ONE] - local[col::ACCUMULATOR] - BabyBear::ONE,
        );

        // C6: step_plus_one = step_index + 1
        cs.push(
            local[col::STEP_PLUS_ONE] - local[col::STEP_INDEX] - BabyBear::ONE,
        );

        cs
    }

    // Transition constraints (row-to-row)
    fn transitions(
        local: &[pyana_circuit::field::BabyBear],
        next: &[pyana_circuit::field::BabyBear],
    ) -> Vec<pyana_circuit::field::BabyBear> {
        vec![
            // T1: next[accumulator] = local[acc_plus_one]
            next[col::ACCUMULATOR] - local[col::ACC_PLUS_ONE],
            // T2: next[step_index] = local[step_plus_one]
            next[col::STEP_INDEX] - local[col::STEP_PLUS_ONE],
        ]
    }

    // Boundary constraints
    fn boundaries(
        pi: &[pyana_circuit::field::BabyBear],
        trace_len: usize,
    ) -> Vec<(usize, usize, pyana_circuit::field::BabyBear)> {
        use pyana_circuit::field::BabyBear;
        vec![
            // First row: accumulator = 1
            (0, col::ACCUMULATOR, BabyBear::ONE),
            // First row: step_index = 0
            (0, col::STEP_INDEX, BabyBear::ZERO),
            // Last row: accumulator = num_steps (pi[0])
            (trace_len - 1, col::ACCUMULATOR, pi[0]),
        ]
    }
}

// ============================================================================
// Trace generation (same as temporal_dsl.rs)
// ============================================================================

/// Generate a valid temporal predicate trace.
pub fn generate_temporal_trace(
    values: &[u32],
    threshold: u32,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = values.len();
    assert!(num_steps >= 1, "need at least 1 step");

    let padded_len = num_steps.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(padded_len);

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

        let val = if step < num_steps {
            values[step]
        } else {
            values[num_steps - 1]
        };

        row[VALUE] = BabyBear::new(val);
        row[THRESHOLD] = BabyBear::new(threshold);

        let diff = val.wrapping_sub(threshold);
        row[DIFF] = BabyBear::new(diff);

        for i in 0..NUM_DIFF_BITS {
            row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
        }

        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);

        trace.push(row);
    }

    let public_inputs = vec![BabyBear::new(padded_len as u32)];

    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::stark::{self, StarkAir};

    #[test]
    fn test_macro_circuit_struct_exists() {
        // The macro generates `TemporalPredicate` struct.
        let circuit = TemporalPredicate;
        assert_eq!(circuit.width(), 37);
        assert_eq!(circuit.constraint_degree(), 2);
        assert_eq!(circuit.air_name(), "pyana-temporal_predicate-v1");
    }

    #[test]
    fn test_macro_circuit_valid_trace() {
        let circuit = TemporalPredicate;

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        assert_eq!(trace.len(), 4);

        // Verify per-row + transition constraints evaluate to zero.
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            let result =
                circuit.eval_constraints(&trace[i], &trace[i + 1], &public_inputs, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Constraint nonzero at row {i} (valid trace)"
            );
        }
    }

    #[test]
    fn test_macro_circuit_boundaries() {
        let circuit = TemporalPredicate;

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        let boundaries = circuit.boundary_constraints(&public_inputs, trace.len());

        // Should have 3 boundaries: first acc=1, first step=0, last acc=num_steps
        assert_eq!(boundaries.len(), 3);

        // Check first row accumulator = 1
        assert_eq!(boundaries[0].row, 0);
        assert_eq!(boundaries[0].col, ACCUMULATOR);
        assert_eq!(boundaries[0].value, BabyBear::ONE);

        // Check first row step = 0
        assert_eq!(boundaries[1].row, 0);
        assert_eq!(boundaries[1].col, STEP_INDEX);
        assert_eq!(boundaries[1].value, BabyBear::ZERO);

        // Check last row accumulator = padded trace len
        assert_eq!(boundaries[2].row, 3); // trace_len - 1 = 4 - 1 = 3
        assert_eq!(boundaries[2].col, ACCUMULATOR);
        assert_eq!(boundaries[2].value, BabyBear::new(4));
    }

    #[test]
    fn test_macro_circuit_invalid_value_below_threshold() {
        let circuit = TemporalPredicate;

        let values = vec![100u32, 30, 100]; // 30 < 50 threshold
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        let alpha = BabyBear::new(7);
        let row1_result =
            circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            row1_result,
            BabyBear::ZERO,
            "Constraint should be nonzero at row 1 where value < threshold"
        );
    }

    #[test]
    fn test_macro_circuit_transition_detects_gap() {
        let circuit = TemporalPredicate;

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (mut trace, public_inputs) = generate_temporal_trace(&values, threshold);

        // Corrupt row 2: accumulator gap
        trace[2][ACCUMULATOR] = BabyBear::new(4);
        trace[2][ACC_PLUS_ONE] = BabyBear::new(5);

        let alpha = BabyBear::new(7);
        let result =
            circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Transition constraint should be nonzero when accumulator has a gap"
        );

        // Row 0 -> Row 1 still fine
        let result_01 =
            circuit.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(result_01, BabyBear::ZERO);
    }

    #[test]
    fn test_macro_circuit_full_stark_prove_verify() {
        let circuit = TemporalPredicate;

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        let proof = stark::prove(&circuit, &trace, &public_inputs);
        let result = stark::verify(&circuit, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "STARK verify failed on valid trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_macro_circuit_rejects_wrong_public_inputs() {
        let circuit = TemporalPredicate;

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        let proof = stark::prove(&circuit, &trace, &public_inputs);

        // Verify with wrong num_steps
        let wrong_pi = vec![BabyBear::new(8)];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong num_steps");
    }

    #[test]
    fn test_macro_matches_descriptor_constraints() {
        // Verify that the macro-generated circuit produces the same constraint
        // evaluations as the manually-constructed CircuitDescriptor.
        use pyana_dsl_runtime::circuit::DslCircuit;

        let circuit = TemporalPredicate;
        let descriptor_circuit =
            DslCircuit::new(super::super::temporal_dsl::temporal_predicate_descriptor());

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        let alpha = BabyBear::new(13);

        for i in 0..trace.len() - 1 {
            let macro_result =
                circuit.eval_constraints(&trace[i], &trace[i + 1], &public_inputs, alpha);
            let desc_result = descriptor_circuit.eval_constraints(
                &trace[i],
                &trace[i + 1],
                &public_inputs,
                alpha,
            );
            assert_eq!(
                macro_result, desc_result,
                "Macro and descriptor disagree at row {i}"
            );
        }
    }
}
