//! Garbled circuit evaluation AIR expressed as a CircuitDescriptor.
//!
//! Proves that a garbled circuit was correctly evaluated gate-by-gate. This is
//! the DSL equivalent of `circuit/src/garbled_air.rs`.
//!
//! # Trace Layout
//!
//! One row per gate evaluation (same as the hand-written AIR):
//!
//! | Columns   | Description                                              |
//! |-----------|----------------------------------------------------------|
//! | 0..7      | Left input label (8 BabyBear elements)                   |
//! | 8..15     | Right input label (8 BabyBear elements)                  |
//! | 16        | Gate index                                               |
//! | 17..24    | Hash output: Poseidon2(left || right || gate_index)       |
//! | 25..32    | Table entry (garbled ciphertext for this row)             |
//! | 33..40    | Decrypted output label                                   |
//! | 41..44    | Circuit commitment (4-element WideHash, constant)         |
//! | 45..48    | Output label hash (4-element WideHash, constant)          |
//!
//! Total width: 49 columns.
//!
//! # Constraints
//!
//! 1. **Circuit commitment binding (4):** circuit_commitment[i] == pi[i]
//! 2. **Output label hash binding (4):** output_label_hash[i] == pi[4+i]
//! 3. **Decryption correctness (8):** output_label[i] == table_entry[i] - hash_output[i]
//!
//! # Public Inputs
//!
//! [circuit_commitment[0..4], output_label_hash[0..4]] (8 total)

use pyana_circuit::field::BabyBear;
use pyana_circuit::garbled_air::GARBLED_EVAL_AIR_WIDTH;
use pyana_circuit::garbled_air::col;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column layout constants (re-exported from garbled_air for clarity)
// ============================================================================

/// Trace width (matches garbled_air).
pub const GARBLED_DSL_WIDTH: usize = GARBLED_EVAL_AIR_WIDTH; // 49

/// Public input indices.
pub mod pi {
    /// Circuit commitment elements 0..3.
    pub const CIRCUIT_COMMITMENT_START: usize = 0;
    /// Output label hash elements 0..3.
    pub const OUTPUT_LABEL_HASH_START: usize = 4;
}

// ============================================================================
// Helpers
// ============================================================================

fn neg_one() -> BabyBear {
    BabyBear::new(pyana_circuit::field::BABYBEAR_P - 1)
}

fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the garbled circuit evaluation CircuitDescriptor.
///
/// Constraints:
/// - C1-C4: circuit_commitment[0..3] == pi[0..3] (PiBinding)
/// - C5-C8: output_label_hash[0..3] == pi[4..7] (PiBinding)
/// - C9-C16: Decryption correctness:
///     output_label[i] - table_entry[i] + hash_output[i] == 0 (Polynomial)
///
/// Boundary constraints bind the first row's commitment and hash columns to pi.
pub fn garbled_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C4: circuit_commitment matches public inputs
    for i in 0..4 {
        constraints.push(ConstraintExpr::PiBinding {
            col: col::CIRCUIT_COMMITMENT + i,
            pi_index: pi::CIRCUIT_COMMITMENT_START + i,
        });
    }

    // C5-C8: output_label_hash matches public inputs
    for i in 0..4 {
        constraints.push(ConstraintExpr::PiBinding {
            col: col::OUTPUT_LABEL_HASH + i,
            pi_index: pi::OUTPUT_LABEL_HASH_START + i,
        });
    }

    // C9-C16: Decryption correctness
    // output_label[i] == table_entry[i] - hash_output[i]
    // Rearranged: output_label[i] - table_entry[i] + hash_output[i] == 0
    for i in 0..8 {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::output(i)]),
                term(neg_one(), &[col::table_entry(i)]),
                term(BabyBear::ONE, &[col::hash_out(i)]),
            ],
        });
    }

    // Boundary constraints: bind first row's commitment/hash to pi values.
    let mut boundaries = Vec::new();
    for i in 0..4 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CIRCUIT_COMMITMENT + i,
            pi_index: pi::CIRCUIT_COMMITMENT_START + i,
        });
    }
    for i in 0..4 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::OUTPUT_LABEL_HASH + i,
            pi_index: pi::OUTPUT_LABEL_HASH_START + i,
        });
    }

    // Column definitions (representative subset for documentation)
    let mut columns = Vec::new();
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("left_label_{i}"),
            index: col::left(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("right_label_{i}"),
            index: col::right(i),
            kind: ColumnKind::Value,
        });
    }
    columns.push(ColumnDef {
        name: "gate_index".into(),
        index: col::GATE_INDEX,
        kind: ColumnKind::Value,
    });
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("hash_output_{i}"),
            index: col::hash_out(i),
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("table_entry_{i}"),
            index: col::table_entry(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("output_label_{i}"),
            index: col::output(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..4 {
        columns.push(ColumnDef {
            name: format!("circuit_commitment_{i}"),
            index: col::CIRCUIT_COMMITMENT + i,
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..4 {
        columns.push(ColumnDef {
            name: format!("output_label_hash_{i}"),
            index: col::OUTPUT_LABEL_HASH + i,
            kind: ColumnKind::Hash,
        });
    }

    CircuitDescriptor {
        name: "pyana-garbled-evaluation-dsl-v1".into(),
        trace_width: GARBLED_DSL_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: 8, // [circuit_commitment[0..4], output_label_hash[0..4]]
    }
}

/// Create a DslCircuit from the garbled evaluation descriptor.
pub fn garbled_dsl_circuit() -> DslCircuit {
    DslCircuit::new(garbled_circuit_descriptor())
}

// ============================================================================
// Trace generation from evaluation records
// ============================================================================

/// Generate a garbled evaluation trace from gate evaluation records and public commitments.
///
/// This mirrors the trace generation in `GarbledEvaluationAir::generate_trace()`.
pub fn generate_garbled_trace(
    gate_trace: &[pyana_circuit::garbled::GateEvalRecord],
    circuit_commitment: &pyana_circuit::binding::WideHash,
    output_label_hash: &pyana_circuit::binding::WideHash,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut trace = Vec::with_capacity(gate_trace.len().max(2));

    for record in gate_trace {
        let mut row = vec![BabyBear::ZERO; GARBLED_DSL_WIDTH];

        for i in 0..8 {
            row[col::left(i)] = record.left_label[i];
        }
        for i in 0..8 {
            row[col::right(i)] = record.right_label[i];
        }
        row[col::GATE_INDEX] = BabyBear::new(record.gate_index);
        for i in 0..8 {
            row[col::hash_out(i)] = record.hash_output[i];
        }
        for i in 0..8 {
            row[col::table_entry(i)] = record.table_entry[i];
        }
        for i in 0..8 {
            row[col::output(i)] = record.output_label[i];
        }
        for i in 0..4 {
            row[col::CIRCUIT_COMMITMENT + i] = circuit_commitment[i];
        }
        for i in 0..4 {
            row[col::OUTPUT_LABEL_HASH + i] = output_label_hash[i];
        }

        trace.push(row);
    }

    // Ensure at least 1 row.
    if trace.is_empty() {
        let mut row = vec![BabyBear::ZERO; GARBLED_DSL_WIDTH];
        for i in 0..4 {
            row[col::CIRCUIT_COMMITMENT + i] = circuit_commitment[i];
        }
        for i in 0..4 {
            row[col::OUTPUT_LABEL_HASH + i] = output_label_hash[i];
        }
        trace.push(row);
    }

    // Pad to power-of-two >= 2.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        // Duplicate the last row (all constraints are satisfied on it).
        trace.push(trace.last().unwrap().clone());
    }

    // Public inputs.
    let mut public_inputs = Vec::with_capacity(8);
    for &elem in circuit_commitment.as_slice() {
        public_inputs.push(elem);
    }
    for &elem in output_label_hash.as_slice() {
        public_inputs.push(elem);
    }

    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::garbled::{
        COMPARISON_BITS, evaluate_garbled_circuit, garble_comparison_circuit,
    };
    use pyana_circuit::stark::{self, StarkAir};

    // ========================================================================
    // Structure validation
    // ========================================================================

    #[test]
    fn descriptor_validates() {
        let desc = garbled_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "garbled circuit descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn descriptor_has_correct_structure() {
        let desc = garbled_circuit_descriptor();
        assert_eq!(desc.trace_width, GARBLED_DSL_WIDTH);
        assert_eq!(desc.trace_width, 49);
        assert_eq!(desc.public_input_count, 8);
        assert_eq!(desc.name, "pyana-garbled-evaluation-dsl-v1");

        // 4 PiBinding (commitment) + 4 PiBinding (output hash) + 8 Polynomial (decryption) = 16
        assert_eq!(desc.constraints.len(), 16);

        // 8 boundary constraints (4 commitment + 4 output hash)
        assert_eq!(desc.boundaries.len(), 8);
    }

    // ========================================================================
    // Valid gate evaluation
    // ========================================================================

    #[test]
    fn valid_gate_evaluation_constraints_pass() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(eval.output_bit, "150 >= 100 should be true");

        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Check all rows satisfy constraints.
        for i in 0..trace.len() {
            let next = if i + 1 < trace.len() {
                &trace[i + 1]
            } else {
                &trace[i]
            };
            let result = dsl_circuit.eval_constraints(&trace[i], next, &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Valid garbled trace row {i} should satisfy all constraints"
            );
        }
    }

    #[test]
    fn valid_gate_evaluation_value_less_than_threshold() {
        // Test case where prover_value < threshold (output_bit = false)
        let threshold = 200u32;
        let prover_value = 50u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(!eval.output_bit, "50 < 200 should be false");

        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();
        let alpha = BabyBear::new(13);

        // All rows should still satisfy constraints (the AIR proves correct EVALUATION,
        // not that the output is true).
        for i in 0..trace.len() {
            let next = if i + 1 < trace.len() {
                &trace[i + 1]
            } else {
                &trace[i]
            };
            let result = dsl_circuit.eval_constraints(&trace[i], next, &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Valid garbled trace (false output) row {i} should still pass"
            );
        }
    }

    // ========================================================================
    // Tampered output label caught
    // ========================================================================

    #[test]
    fn tampered_output_label_caught() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);

        // Tamper with the first gate's output label.
        let mut tampered_trace = eval.gate_trace.clone();
        tampered_trace[0].output_label[0] = tampered_trace[0].output_label[0] + BabyBear::ONE;

        let (trace, pi) =
            generate_garbled_trace(&tampered_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();
        let alpha = BabyBear::new(7);

        // The tampered row should fail the decryption correctness constraint.
        let next = if trace.len() > 1 {
            &trace[1]
        } else {
            &trace[0]
        };
        let result = dsl_circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered output label should violate decryption constraint"
        );
    }

    #[test]
    fn tampered_table_entry_caught() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);

        // Tamper with the first gate's table entry.
        let mut tampered_trace = eval.gate_trace.clone();
        tampered_trace[0].table_entry[3] = tampered_trace[0].table_entry[3] + BabyBear::new(42);

        let (trace, pi) =
            generate_garbled_trace(&tampered_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();
        let alpha = BabyBear::new(7);

        let next = if trace.len() > 1 {
            &trace[1]
        } else {
            &trace[0]
        };
        let result = dsl_circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered table entry should violate decryption constraint"
        );
    }

    // ========================================================================
    // Wrong circuit commitment caught
    // ========================================================================

    #[test]
    fn wrong_circuit_commitment_caught() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);

        // Use wrong circuit commitment in the trace.
        let wrong_commitment =
            pyana_circuit::binding::WideHash::from_poseidon2("wrong", &[BabyBear::new(99999)]);
        let (trace, _wrong_pi) =
            generate_garbled_trace(&eval.gate_trace, &wrong_commitment, &output_hash);

        // But verify against the CORRECT public inputs.
        let mut correct_pi = Vec::with_capacity(8);
        for &elem in circuit.circuit_commitment.as_slice() {
            correct_pi.push(elem);
        }
        for &elem in output_hash.as_slice() {
            correct_pi.push(elem);
        }

        let dsl_circuit = garbled_dsl_circuit();
        let alpha = BabyBear::new(7);

        // The PiBinding constraint will detect the mismatch.
        let next = if trace.len() > 1 {
            &trace[1]
        } else {
            &trace[0]
        };
        let result = dsl_circuit.eval_constraints(&trace[0], next, &correct_pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong circuit commitment should be caught by PiBinding constraint"
        );
    }

    #[test]
    fn wrong_output_label_hash_caught() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);

        // Build trace with correct values.
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        // Verify against wrong output hash pi.
        let mut wrong_pi = pi.clone();
        wrong_pi[pi::OUTPUT_LABEL_HASH_START] = BabyBear::new(11111);

        let dsl_circuit = garbled_dsl_circuit();
        let alpha = BabyBear::new(7);

        let next = if trace.len() > 1 {
            &trace[1]
        } else {
            &trace[0]
        };
        let result = dsl_circuit.eval_constraints(&trace[0], next, &wrong_pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong output label hash should be caught"
        );
    }

    // ========================================================================
    // STARK prove/verify round-trips
    // ========================================================================

    #[test]
    fn stark_prove_verify_valid_evaluation() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();

        let proof = stark::prove(&dsl_circuit, &trace, &pi);
        let result = stark::verify(&dsl_circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for valid garbled evaluation failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn stark_rejects_wrong_commitment_pi() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();

        let proof = stark::prove(&dsl_circuit, &trace, &pi);

        // Wrong public inputs (different commitment).
        let mut wrong_pi = pi.clone();
        wrong_pi[0] = BabyBear::new(77777);

        let result = stark::verify(&dsl_circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong circuit commitment pi"
        );
    }

    #[test]
    fn stark_rejects_wrong_output_hash_pi() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();

        let proof = stark::prove(&dsl_circuit, &trace, &pi);

        // Wrong output hash in pi.
        let mut wrong_pi = pi.clone();
        wrong_pi[pi::OUTPUT_LABEL_HASH_START + 2] = BabyBear::new(88888);

        let result = stark::verify(&dsl_circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong output label hash pi"
        );
    }

    #[test]
    fn stark_prove_verify_false_output() {
        // Prove correct evaluation that yields false (value < threshold).
        let threshold = 200u32;
        let prover_value = 50u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(!eval.output_bit);

        let output_hash = pyana_circuit::garbled::hash_label(&eval.output_label);
        let (trace, pi) =
            generate_garbled_trace(&eval.gate_trace, &circuit.circuit_commitment, &output_hash);

        let dsl_circuit = garbled_dsl_circuit();

        let proof = stark::prove(&dsl_circuit, &trace, &pi);
        let result = stark::verify(&dsl_circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for false-output garbled evaluation failed: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Boundary constraints
    // ========================================================================

    #[test]
    fn boundary_constraints_correct() {
        let dsl_circuit = garbled_dsl_circuit();
        let pi = vec![
            BabyBear::new(10), // commitment[0]
            BabyBear::new(20), // commitment[1]
            BabyBear::new(30), // commitment[2]
            BabyBear::new(40), // commitment[3]
            BabyBear::new(50), // output_hash[0]
            BabyBear::new(60), // output_hash[1]
            BabyBear::new(70), // output_hash[2]
            BabyBear::new(80), // output_hash[3]
        ];

        let boundaries = dsl_circuit.boundary_constraints(&pi, 4);
        assert_eq!(boundaries.len(), 8);

        // First 4: circuit commitment on row 0.
        for i in 0..4 {
            assert_eq!(boundaries[i].row, 0);
            assert_eq!(boundaries[i].col, col::CIRCUIT_COMMITMENT + i);
            assert_eq!(boundaries[i].value, pi[i]);
        }

        // Next 4: output label hash on row 0.
        for i in 0..4 {
            assert_eq!(boundaries[4 + i].row, 0);
            assert_eq!(boundaries[4 + i].col, col::OUTPUT_LABEL_HASH + i);
            assert_eq!(boundaries[4 + i].value, pi[4 + i]);
        }
    }
}
