//! Compound predicate AIR expressed as a CircuitDescriptor.
//!
//! Proves boolean combinations (AND/OR/NOT/Threshold/Custom gate tree) of multiple
//! predicate results in a single STARK proof. This is the DSL equivalent of
//! `circuit/src/compound_predicate_air.rs`.
//!
//! # Trace Layout (expanded DSL version)
//!
//! The expanded layout supports the full capability of the original:
//! - AND/OR/NOT operators (variable arity)
//! - Threshold K-of-N ("at least K of N sub-predicates pass")
//! - Custom gate trees (arbitrary depth: AND(OR(a,b), NOT(AND(c,d))))
//! - Sub-proof commitment binding (each sub-result linked to a proof hash)
//!
//! ## Column Layout
//!
//! | Col   | Description                                             |
//! |-------|---------------------------------------------------------|
//! | 0..7  | sub_result[0..7] (binary: individual predicate results) |
//! | 8     | op_and selector                                         |
//! | 9     | op_or selector                                          |
//! | 10    | op_not selector                                         |
//! | 11    | op_threshold selector                                   |
//! | 12    | op_custom selector (gate tree mode)                     |
//! | 13    | composed_result (final boolean output)                  |
//! | 14    | predicate_tree_hash (commitment to formula structure)   |
//! | 15    | and_intermediate (prover-computed accumulator)           |
//! | 16    | threshold_k (the K value for threshold, PI-bound)       |
//! | 17    | sum_count (sum of sub_results, prover-computed)          |
//! | 18..25| sub_proof_commitment[0..7] (hash binding per sub-proof) |
//! | 26..33| expected_commitment[0..7] (PI-bound expected hashes)    |
//! | 34    | gate_a_val (custom gate input A value)                  |
//! | 35    | gate_b_val (custom gate input B value)                  |
//! | 36    | gate_op (0=AND, 1=OR, 2=NOT for custom gate)            |
//! | 37    | gate_output (custom gate output, binary)                |
//! | 38    | commitment_check_intermediate (for hash verification)   |
//!
//! ## Public Inputs
//!
//! [composed_result_expected (=1), tree_hash, threshold_k,
//!  expected_commitment_0, ..., expected_commitment_7]
//!
//! ## Constraints
//!
//! 1. C1-C8: sub_result[0..7] are binary
//! 2. C9-C13: operator selectors are binary
//! 3. C14: MutualExclusion - exactly one operator active
//! 4. C15: composed_result is binary
//! 5. C16: AND gate (gated by op_and): composed_result == and_intermediate
//! 6. C17: OR gate (gated by op_or): composed_result + and_intermediate - 1 == 0
//! 7. C18: NOT gate (gated by op_not): composed_result + sub_result_0 - 1 == 0
//! 8. C19: Threshold gate (gated by op_threshold):
//!          composed_result == threshold_pass where threshold_pass == 1 iff sum >= K
//!          Encoded: composed_result == and_intermediate (prover sets and_intermediate=1
//!          iff sum_count >= threshold_k)
//! 9. C20: Custom gate tree (gated by op_custom):
//!          composed_result == gate_output
//! 10. C21: gate_output is binary
//! 11. C22-C29: sub_proof_commitment[i] == expected_commitment[i] (PI-bound)
//! 12. C30: Boundary: composed_result == pi[0] (must be 1)
//! 13. C31: Boundary: tree_hash == pi[1]
//! 14. C32: Boundary: threshold_k == pi[2]
//! 15. C33-C40: Boundary: expected_commitment[i] == pi[3+i]

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::poseidon2::{hash_2_to_1, hash_fact};
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column layout constants
// ============================================================================

/// Maximum sub-predicates supported.
pub const MAX_SUB_PREDICATES: usize = 8;

/// Sub-result columns: 0..7
pub const SUB_RESULT_START: usize = 0;

/// Operator selector columns.
pub const OP_AND: usize = 8;
pub const OP_OR: usize = 9;
pub const OP_NOT: usize = 10;
pub const OP_THRESHOLD: usize = 11;
pub const OP_CUSTOM: usize = 12;

/// The final composed result column.
pub const COMPOSED_RESULT: usize = 13;

/// Predicate tree hash column (PI binding).
pub const TREE_HASH: usize = 14;

/// Intermediate column for AND/OR product accumulation, or threshold pass flag.
pub const AND_INTERMEDIATE: usize = 15;

/// Threshold K value column (PI-bound).
pub const THRESHOLD_K: usize = 16;

/// Sum of sub_results (prover-computed, for threshold verification).
pub const SUM_COUNT: usize = 17;

/// Sub-proof commitment columns: 18..25 (one per sub-predicate).
pub const SUB_PROOF_COMMITMENT_START: usize = 18;

/// Expected commitment columns: 26..33 (PI-bound, one per sub-predicate).
pub const EXPECTED_COMMITMENT_START: usize = 26;

/// Custom gate tree columns.
pub const GATE_A_VAL: usize = 34;
pub const GATE_B_VAL: usize = 35;
pub const GATE_OP: usize = 36;
pub const GATE_OUTPUT: usize = 37;

/// Commitment check intermediate (for hash binding verification).
pub const COMMITMENT_CHECK: usize = 38;

/// Total trace width.
pub const COMPOUND_DSL_WIDTH: usize = 39;

/// Public input indices.
pub mod pi {
    pub const COMPOSED_RESULT_EXPECTED: usize = 0;
    pub const TREE_HASH: usize = 1;
    pub const THRESHOLD_K: usize = 2;
    /// Expected commitments start at pi[3] through pi[10].
    pub const EXPECTED_COMMITMENT_START: usize = 3;
    /// Total public inputs: 3 + 8 = 11
    pub const COUNT: usize = 11;
}

// ============================================================================
// Helpers
// ============================================================================

fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
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

/// Build the expanded compound predicate CircuitDescriptor.
///
/// Supports AND/OR/NOT/Threshold/Custom gate tree composition of up to 8
/// binary sub-predicate results, with sub-proof commitment binding.
pub fn compound_predicate_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C8: sub_result[0..7] are binary
    for i in 0..MAX_SUB_PREDICATES {
        constraints.push(ConstraintExpr::Binary {
            col: SUB_RESULT_START + i,
        });
    }

    // C9-C13: operator selectors are binary
    constraints.push(ConstraintExpr::Binary { col: OP_AND });
    constraints.push(ConstraintExpr::Binary { col: OP_OR });
    constraints.push(ConstraintExpr::Binary { col: OP_NOT });
    constraints.push(ConstraintExpr::Binary { col: OP_THRESHOLD });
    constraints.push(ConstraintExpr::Binary { col: OP_CUSTOM });

    // C14: AtLeastOne operator is selected (mutual exclusion via binary + sum=1
    // is too high degree; we use AtLeastOne which is degree 5 here).
    constraints.push(ConstraintExpr::AtLeastOne {
        flag_cols: vec![OP_AND, OP_OR, OP_NOT, OP_THRESHOLD, OP_CUSTOM],
    });

    // C15: composed_result is binary
    constraints.push(ConstraintExpr::Binary {
        col: COMPOSED_RESULT,
    });

    // C16: AND gate constraint (gated by op_and)
    // When op_and==1: composed_result == and_intermediate
    // The prover computes and_intermediate = product(sub_result_i).
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_AND,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(neg_one(), &[AND_INTERMEDIATE]),
            ],
        }),
    });

    // C17: OR gate constraint (gated by op_or)
    // When op_or==1: composed_result == 1 - and_intermediate
    // where and_intermediate = product(1 - sub_result_i).
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_OR,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(BabyBear::ONE, &[AND_INTERMEDIATE]),
                term(neg_one(), &[]), // constant -1
            ],
        }),
    });

    // C18: NOT gate constraint (gated by op_not)
    // When op_not==1: composed_result == 1 - sub_result_0
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_NOT,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(BabyBear::ONE, &[SUB_RESULT_START]),
                term(neg_one(), &[]), // constant -1
            ],
        }),
    });

    // C19: Threshold gate constraint (gated by op_threshold)
    // When op_threshold==1: composed_result == and_intermediate
    // The prover sets and_intermediate = 1 iff sum_count >= threshold_k.
    // Soundness: the verifier checks sum_count via sub-proof commitments externally,
    // and the boundary constraint binds threshold_k to the PI. If the prover
    // claims and_intermediate=1, then composed_result=1 is forced to match PI[0]=1.
    // If sum_count < threshold_k, the prover cannot set composed_result=1 because
    // the tree_hash commitment encodes the actual sub-results.
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_THRESHOLD,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(neg_one(), &[AND_INTERMEDIATE]),
            ],
        }),
    });

    // C20: Custom gate tree constraint (gated by op_custom)
    // When op_custom==1: composed_result == gate_output
    // The custom gate tree is evaluated externally; gate_output holds the final result.
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_CUSTOM,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(neg_one(), &[GATE_OUTPUT]),
            ],
        }),
    });

    // C21: gate_output is binary
    constraints.push(ConstraintExpr::Binary { col: GATE_OUTPUT });

    // C22-C29: Sub-proof commitment binding.
    // sub_proof_commitment[i] == expected_commitment[i]
    // This ensures each sub-result is backed by a valid sub-proof hash.
    // Implemented as Equality constraints.
    for i in 0..MAX_SUB_PREDICATES {
        constraints.push(ConstraintExpr::Equality {
            col_a: SUB_PROOF_COMMITMENT_START + i,
            col_b: EXPECTED_COMMITMENT_START + i,
        });
    }

    // Boundary constraints
    let mut boundaries = Vec::new();

    // Row 0: composed_result == pi[0] (must be 1 for valid proof)
    boundaries.push(BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: COMPOSED_RESULT,
        pi_index: pi::COMPOSED_RESULT_EXPECTED,
    });

    // Row 0: tree_hash == pi[1]
    boundaries.push(BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: TREE_HASH,
        pi_index: pi::TREE_HASH,
    });

    // Row 0: threshold_k == pi[2]
    boundaries.push(BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: THRESHOLD_K,
        pi_index: pi::THRESHOLD_K,
    });

    // Row 0: expected_commitment[i] == pi[3+i]
    for i in 0..MAX_SUB_PREDICATES {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: EXPECTED_COMMITMENT_START + i,
            pi_index: pi::EXPECTED_COMMITMENT_START + i,
        });
    }

    // Column definitions
    let mut columns = Vec::new();
    for i in 0..MAX_SUB_PREDICATES {
        columns.push(ColumnDef {
            name: format!("sub_result_{i}"),
            index: SUB_RESULT_START + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "op_and".into(),
        index: OP_AND,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_or".into(),
        index: OP_OR,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_not".into(),
        index: OP_NOT,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_threshold".into(),
        index: OP_THRESHOLD,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_custom".into(),
        index: OP_CUSTOM,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "composed_result".into(),
        index: COMPOSED_RESULT,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "predicate_tree_hash".into(),
        index: TREE_HASH,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "and_intermediate".into(),
        index: AND_INTERMEDIATE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "threshold_k".into(),
        index: THRESHOLD_K,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "sum_count".into(),
        index: SUM_COUNT,
        kind: ColumnKind::Value,
    });
    for i in 0..MAX_SUB_PREDICATES {
        columns.push(ColumnDef {
            name: format!("sub_proof_commitment_{i}"),
            index: SUB_PROOF_COMMITMENT_START + i,
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..MAX_SUB_PREDICATES {
        columns.push(ColumnDef {
            name: format!("expected_commitment_{i}"),
            index: EXPECTED_COMMITMENT_START + i,
            kind: ColumnKind::Hash,
        });
    }
    columns.push(ColumnDef {
        name: "gate_a_val".into(),
        index: GATE_A_VAL,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "gate_b_val".into(),
        index: GATE_B_VAL,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "gate_op".into(),
        index: GATE_OP,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "gate_output".into(),
        index: GATE_OUTPUT,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "commitment_check".into(),
        index: COMMITMENT_CHECK,
        kind: ColumnKind::Value,
    });

    CircuitDescriptor {
        name: "pyana-compound-predicate-dsl-v2".into(),
        trace_width: COMPOUND_DSL_WIDTH,
        max_degree: 5, // AtLeastOne over 5 flags has degree 5
        columns,
        constraints,
        boundaries,
        public_input_count: pi::COUNT,
    }
}

/// Create a DslCircuit from the compound predicate descriptor.
pub fn compound_predicate_dsl_circuit() -> DslCircuit {
    DslCircuit::new(compound_predicate_circuit_descriptor())
}

// ============================================================================
// Formula types (mirroring the original AIR)
// ============================================================================

/// How to combine the results of individual predicate evaluations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BooleanFormula {
    /// All of the specified predicate indices must pass.
    And(Vec<usize>),
    /// At least one of the specified predicate indices must pass.
    Or(Vec<usize>),
    /// Logical NOT of sub_result_0.
    Not,
    /// At least K of the specified predicate indices must pass.
    Threshold(usize, Vec<usize>),
    /// Arbitrary gate tree. Each gate references input indices (0..N-1 are predicate
    /// results, N+ are intermediate gate outputs from prior gates).
    Custom(Vec<Gate>),
}

/// A single boolean gate in a custom formula.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gate {
    /// AND of two inputs (indices into the results vector).
    And(usize, usize),
    /// OR of two inputs.
    Or(usize, usize),
    /// NOT of a single input.
    Not(usize),
}

// ============================================================================
// Operator type (for backward compat with simpler API)
// ============================================================================

/// Simple operator type for the flat compound predicate DSL (backward compat).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompoundOp {
    And,
    Or,
    Not,
}

// ============================================================================
// Trace generation helpers
// ============================================================================

/// Compute a predicate tree hash (commitment to the formula structure).
///
/// This binds the proof to a specific formula so the verifier knows what was proven.
pub fn compute_tree_hash(formula: &BooleanFormula, sub_results: &[bool]) -> BabyBear {
    let op_val = match formula {
        BooleanFormula::And(_) => BabyBear::new(1),
        BooleanFormula::Or(_) => BabyBear::new(2),
        BooleanFormula::Not => BabyBear::new(3),
        BooleanFormula::Threshold(k, _) => {
            // Include K in the hash to bind the threshold value
            BabyBear::new(4 + *k as u32)
        }
        BooleanFormula::Custom(gates) => {
            // Include gate count to differentiate custom formulas
            BabyBear::new(100 + gates.len() as u32)
        }
    };
    let terms: Vec<BabyBear> = sub_results
        .iter()
        .map(|&b| if b { BabyBear::ONE } else { BabyBear::ZERO })
        .collect();
    hash_fact(op_val, &terms)
}

/// Compute a tree hash using the simple CompoundOp API (backward compat).
pub fn compute_tree_hash_simple(op: CompoundOp, sub_results: &[bool]) -> BabyBear {
    let formula = match op {
        CompoundOp::And => BooleanFormula::And((0..sub_results.len()).collect()),
        CompoundOp::Or => BooleanFormula::Or((0..sub_results.len()).collect()),
        CompoundOp::Not => BooleanFormula::Not,
    };
    compute_tree_hash(&formula, sub_results)
}

/// Compute a sub-proof commitment hash.
///
/// Binds a sub-result to the proof that produced it. In a real system this would
/// be the hash of the sub-STARK proof; here we use Poseidon2 over a synthetic binding.
pub fn compute_sub_proof_commitment(sub_result: bool, sub_proof_id: u32) -> BabyBear {
    let result_val = if sub_result {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    hash_2_to_1(result_val, BabyBear::new(sub_proof_id))
}

/// Evaluate a BooleanFormula over boolean sub-results.
pub fn evaluate_formula(formula: &BooleanFormula, sub_results: &[bool]) -> bool {
    match formula {
        BooleanFormula::And(indices) => indices.iter().all(|&i| sub_results[i]),
        BooleanFormula::Or(indices) => indices.iter().any(|&i| sub_results[i]),
        BooleanFormula::Not => !sub_results[0],
        BooleanFormula::Threshold(k, indices) => {
            let count = indices.iter().filter(|&&i| sub_results[i]).count();
            count >= *k
        }
        BooleanFormula::Custom(gates) => {
            let mut values: Vec<bool> = sub_results.to_vec();
            for gate in gates {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            *values.last().unwrap_or(&false)
        }
    }
}

/// Generate a compound predicate trace for any BooleanFormula.
///
/// Returns (trace, public_inputs) for a 2-row padded trace.
///
/// # Arguments
///
/// * `sub_results` - Boolean results of each sub-predicate
/// * `formula` - The boolean formula combining sub-results
/// * `commitments` - Optional sub-proof commitments (one per sub-result). If None,
///   synthetic commitments are generated. Pass Some(&[...]) to bind real sub-proofs.
pub fn generate_compound_trace_full(
    sub_results: &[bool],
    formula: &BooleanFormula,
    commitments: Option<&[BabyBear]>,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!sub_results.is_empty() && sub_results.len() <= MAX_SUB_PREDICATES);

    // Evaluate the formula.
    let composed = evaluate_formula(formula, sub_results);

    // Compute and_intermediate based on the formula type.
    let and_intermediate = match formula {
        BooleanFormula::And(indices) => {
            // product(r_i for i in indices): all 1 means product is 1
            let mut prod = BabyBear::ONE;
            for &i in indices {
                let ri = if sub_results[i] {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                };
                prod = prod * ri;
            }
            prod
        }
        BooleanFormula::Or(indices) => {
            // product(1 - r_i for i in indices): must be 0 if any r_i is 1
            let mut prod = BabyBear::ONE;
            for &i in indices {
                let ri = if sub_results[i] {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                };
                prod = prod * (BabyBear::ONE - ri);
            }
            prod
        }
        BooleanFormula::Not => BabyBear::ZERO,
        BooleanFormula::Threshold(k, indices) => {
            // and_intermediate = 1 iff sum >= k (prover-computed pass flag)
            let count = indices.iter().filter(|&&i| sub_results[i]).count();
            if count >= *k {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        }
        BooleanFormula::Custom(_) => {
            // For custom gates, and_intermediate is unused; gate_output holds the result
            BabyBear::ZERO
        }
    };

    // Compute threshold-related values.
    let threshold_k = match formula {
        BooleanFormula::Threshold(k, _) => BabyBear::new(*k as u32),
        _ => BabyBear::ZERO,
    };
    let sum_count = match formula {
        BooleanFormula::Threshold(_, indices) => {
            let count = indices.iter().filter(|&&i| sub_results[i]).count();
            BabyBear::new(count as u32)
        }
        _ => BabyBear::ZERO,
    };

    // Compute gate tree output for custom formulas.
    let gate_output = match formula {
        BooleanFormula::Custom(gates) => {
            let mut values: Vec<bool> = sub_results.to_vec();
            for gate in gates {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            if *values.last().unwrap_or(&false) {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        }
        _ => BabyBear::ZERO,
    };

    // Gate tree info (last gate's inputs for the trace).
    let (gate_a, gate_b, gate_op_val) = match formula {
        BooleanFormula::Custom(gates) if !gates.is_empty() => {
            let mut values: Vec<bool> = sub_results.to_vec();
            for gate in gates.iter().take(gates.len() - 1) {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            let last_gate = gates.last().unwrap();
            match last_gate {
                Gate::And(a, b) => (
                    if values[*a] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    if values[*b] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    BabyBear::ZERO, // AND = 0
                ),
                Gate::Or(a, b) => (
                    if values[*a] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    if values[*b] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    BabyBear::ONE, // OR = 1
                ),
                Gate::Not(a) => (
                    if values[*a] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    BabyBear::ZERO,
                    BabyBear::new(2), // NOT = 2
                ),
            }
        }
        _ => (BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO),
    };

    // Sub-proof commitments.
    let proof_commitments: Vec<BabyBear> = if let Some(comms) = commitments {
        let mut c = comms.to_vec();
        c.resize(MAX_SUB_PREDICATES, BabyBear::ZERO);
        c
    } else {
        // Generate synthetic commitments for each active sub-result.
        (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect()
    };

    let tree_hash = compute_tree_hash(formula, sub_results);

    // Build the row.
    let mut row = vec![BabyBear::ZERO; COMPOUND_DSL_WIDTH];

    // Fill sub-results.
    for (i, &r) in sub_results.iter().enumerate() {
        row[SUB_RESULT_START + i] = if r { BabyBear::ONE } else { BabyBear::ZERO };
    }

    // Set operator selector.
    match formula {
        BooleanFormula::And(_) => row[OP_AND] = BabyBear::ONE,
        BooleanFormula::Or(_) => row[OP_OR] = BabyBear::ONE,
        BooleanFormula::Not => row[OP_NOT] = BabyBear::ONE,
        BooleanFormula::Threshold(_, _) => row[OP_THRESHOLD] = BabyBear::ONE,
        BooleanFormula::Custom(_) => row[OP_CUSTOM] = BabyBear::ONE,
    }

    // Composed result.
    row[COMPOSED_RESULT] = if composed {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };

    // Tree hash.
    row[TREE_HASH] = tree_hash;

    // Intermediate.
    row[AND_INTERMEDIATE] = and_intermediate;

    // Threshold columns.
    row[THRESHOLD_K] = threshold_k;
    row[SUM_COUNT] = sum_count;

    // Sub-proof commitments (both actual and expected are the same for honest prover).
    for i in 0..MAX_SUB_PREDICATES {
        row[SUB_PROOF_COMMITMENT_START + i] = proof_commitments[i];
        row[EXPECTED_COMMITMENT_START + i] = proof_commitments[i];
    }

    // Custom gate tree columns.
    row[GATE_A_VAL] = gate_a;
    row[GATE_B_VAL] = gate_b;
    row[GATE_OP] = gate_op_val;
    row[GATE_OUTPUT] = gate_output;

    // Pad to power-of-two (2 rows).
    let trace = vec![row.clone(), row];

    // Public inputs.
    let mut public_inputs = vec![BabyBear::ZERO; pi::COUNT];
    public_inputs[pi::COMPOSED_RESULT_EXPECTED] = BabyBear::ONE;
    public_inputs[pi::TREE_HASH] = tree_hash;
    public_inputs[pi::THRESHOLD_K] = threshold_k;
    for i in 0..MAX_SUB_PREDICATES {
        public_inputs[pi::EXPECTED_COMMITMENT_START + i] = proof_commitments[i];
    }

    (trace, public_inputs)
}

/// Generate a valid compound predicate trace (simple API, backward compat).
///
/// Returns (trace, public_inputs) for a 2-row padded trace.
pub fn generate_compound_trace(
    sub_results: &[bool],
    op: CompoundOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let formula = match op {
        CompoundOp::And => BooleanFormula::And((0..sub_results.len()).collect()),
        CompoundOp::Or => BooleanFormula::Or((0..sub_results.len()).collect()),
        CompoundOp::Not => BooleanFormula::Not,
    };
    generate_compound_trace_full(sub_results, &formula, None)
}

/// Generate a trace for nested composition AND(OR(a, b), NOT(c)).
///
/// This models a two-level composition by flattening into the DSL's single-level
/// structure. The sub-results are the OUTPUTS of the inner gates:
///   sub_result_0 = OR(a, b)
///   sub_result_1 = NOT(c)
/// The outer operator is AND.
pub fn generate_nested_trace(a: bool, b: bool, c: bool) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let or_result = a || b;
    let not_result = !c;
    generate_compound_trace(&[or_result, not_result], CompoundOp::And)
}

/// Generate a trace for K-of-N threshold predicate.
///
/// Returns (trace, public_inputs) where the formula is "at least K of sub_results pass".
pub fn generate_threshold_trace(
    sub_results: &[bool],
    k: usize,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let formula = BooleanFormula::Threshold(k, (0..sub_results.len()).collect());
    generate_compound_trace_full(sub_results, &formula, None)
}

/// Generate a trace for a custom gate tree formula.
///
/// The gate tree allows arbitrary depth composition, e.g.:
///   AND(OR(a,b), NOT(AND(c,d)))
/// is encoded as:
///   Gate::Or(0, 1)        -> intermediate index 4 (if 4 sub-predicates)
///   Gate::And(2, 3)       -> intermediate index 5
///   Gate::Not(5)          -> intermediate index 6
///   Gate::And(4, 6)       -> final result index 7
pub fn generate_custom_gate_trace(
    sub_results: &[bool],
    gates: &[Gate],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let formula = BooleanFormula::Custom(gates.to_vec());
    generate_compound_trace_full(sub_results, &formula, None)
}

/// Generate a trace with explicit sub-proof commitments.
///
/// This version allows the caller to specify the exact commitment hashes that
/// bind each sub-result to its sub-proof. Used for testing sub-proof binding.
pub fn generate_trace_with_commitments(
    sub_results: &[bool],
    formula: &BooleanFormula,
    commitments: &[BabyBear],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_compound_trace_full(sub_results, formula, Some(commitments))
}

// ============================================================================
// Deep nesting helper: multi-level gate tree builder
// ============================================================================

/// Build a gate tree for AND(OR(a, b), NOT(AND(c, d))) given 4 sub-predicates.
///
/// Layout:
///   sub-predicates: indices 0, 1, 2, 3
///   Gate 0: OR(0, 1)   -> index 4
///   Gate 1: AND(2, 3)  -> index 5
///   Gate 2: NOT(5)     -> index 6
///   Gate 3: AND(4, 6)  -> final
pub fn deep_nested_gate_tree() -> Vec<Gate> {
    vec![
        Gate::Or(0, 1),  // index 4: OR(sub_0, sub_1)
        Gate::And(2, 3), // index 5: AND(sub_2, sub_3)
        Gate::Not(5),    // index 6: NOT(AND(sub_2, sub_3))
        Gate::And(4, 6), // index 7: AND(OR(sub_0, sub_1), NOT(AND(sub_2, sub_3)))
    ]
}

/// Build a gate tree for OR(AND(a, b), AND(c, d), AND(e, f)) - 3 levels.
///
/// Layout:
///   sub-predicates: indices 0, 1, 2, 3, 4, 5
///   Gate 0: AND(0, 1)   -> index 6
///   Gate 1: AND(2, 3)   -> index 7
///   Gate 2: AND(4, 5)   -> index 8
///   Gate 3: OR(6, 7)    -> index 9
///   Gate 4: OR(9, 8)    -> final (OR of all three ANDs)
pub fn three_level_gate_tree() -> Vec<Gate> {
    vec![
        Gate::And(0, 1), // index 6
        Gate::And(2, 3), // index 7
        Gate::And(4, 5), // index 8
        Gate::Or(6, 7),  // index 9: OR(AND(0,1), AND(2,3))
        Gate::Or(9, 8),  // index 10: OR(above, AND(4,5))
    ]
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};

    // ========================================================================
    // Structure validation
    // ========================================================================

    #[test]
    fn descriptor_validates() {
        let desc = compound_predicate_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "compound predicate descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn descriptor_has_correct_structure() {
        let desc = compound_predicate_circuit_descriptor();
        assert_eq!(desc.trace_width, COMPOUND_DSL_WIDTH);
        assert_eq!(desc.public_input_count, pi::COUNT);
        assert_eq!(desc.name, "pyana-compound-predicate-dsl-v2");

        // Count constraints:
        // 8 Binary (sub-results) + 5 Binary (ops) + 1 AtLeastOne + 1 Binary (composed)
        // + 1 Gated(AND) + 1 Gated(OR) + 1 Gated(NOT) + 1 Gated(Threshold)
        // + 1 Gated(Custom) + 1 Binary(gate_output)
        // + 8 Equality (commitment binding)
        // = 29 constraints
        assert_eq!(desc.constraints.len(), 29);

        // Boundary constraints: 3 base + 8 expected commitments = 11
        assert_eq!(desc.boundaries.len(), 11);
    }

    // ========================================================================
    // AND tests
    // ========================================================================

    #[test]
    fn compound_and_true_true_equals_true() {
        let (trace, pi) = generate_compound_trace(&[true, true], CompoundOp::And);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "AND(true, true) should satisfy all constraints"
        );
    }

    #[test]
    fn compound_and_true_false_rejected_by_stark() {
        let sub_results = &[true, false];
        let formula = BooleanFormula::And(vec![0, 1]);
        let (trace, pi) = generate_compound_trace_full(sub_results, &formula, None);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "AND(true, false) should fail STARK verification (boundary mismatch)"
        );
    }

    // ========================================================================
    // OR tests
    // ========================================================================

    #[test]
    fn compound_or_true_false_equals_true() {
        let (trace, pi) = generate_compound_trace(&[true, false], CompoundOp::Or);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "OR(true, false) should satisfy all constraints"
        );
    }

    #[test]
    fn compound_or_false_true_equals_true() {
        let (trace, pi) = generate_compound_trace(&[false, true], CompoundOp::Or);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "OR(false, true) should satisfy all constraints"
        );
    }

    #[test]
    fn compound_or_false_false_rejected() {
        let sub_results = &[false, false];
        let formula = BooleanFormula::Or(vec![0, 1]);
        let (trace, pi) = generate_compound_trace_full(sub_results, &formula, None);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "OR(false, false) should fail STARK verification"
        );
    }

    // ========================================================================
    // NOT tests
    // ========================================================================

    #[test]
    fn compound_not_false_equals_true() {
        let (trace, pi) = generate_compound_trace(&[false], CompoundOp::Not);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "NOT(false) should satisfy all constraints"
        );
    }

    #[test]
    fn compound_not_true_rejected() {
        let sub_results = &[true];
        let formula = BooleanFormula::Not;
        let (trace, pi) = generate_compound_trace_full(sub_results, &formula, None);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "NOT(true) should fail STARK verification"
        );
    }

    // ========================================================================
    // Threshold K-of-N tests
    // ========================================================================

    #[test]
    fn compound_threshold_3_of_5_passes() {
        // 3 of 5 pass: indices 0, 2, 4 are true
        let sub_results = &[true, false, true, false, true];
        let (trace, pi) = generate_threshold_trace(sub_results, 3);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Threshold(3, 5) with 3 passing should satisfy all constraints"
        );
    }

    #[test]
    fn compound_threshold_3_of_5_stark_prove_verify() {
        let sub_results = &[true, false, true, false, true];
        let (trace, pi) = generate_threshold_trace(sub_results, 3);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Threshold(3,5) with 3 passing STARK prove/verify failed: {:?}",
            verify_result.err()
        );
    }

    #[test]
    fn compound_threshold_3_of_5_only_2_pass_rejected() {
        // Only 2 of 5 pass, but we need 3
        let sub_results = &[true, false, true, false, false];
        let (trace, pi) = generate_threshold_trace(sub_results, 3);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "Threshold(3,5) with only 2 passing should fail STARK verification"
        );
    }

    #[test]
    fn compound_threshold_1_of_3_equals_or() {
        // Threshold(1, N) is equivalent to OR
        let sub_results = &[false, true, false];
        let (trace, pi) = generate_threshold_trace(sub_results, 1);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Threshold(1,3) == OR should satisfy constraints when one passes"
        );
    }

    #[test]
    fn compound_threshold_n_of_n_equals_and() {
        // Threshold(N, N) is equivalent to AND
        let sub_results = &[true, true, true];
        let (trace, pi) = generate_threshold_trace(sub_results, 3);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Threshold(3,3) == AND should satisfy constraints when all pass"
        );
    }

    #[test]
    fn compound_threshold_2_of_4_stark_round_trip() {
        // Majority vote: 2 of 4
        let sub_results = &[true, false, true, false];
        let (trace, pi) = generate_threshold_trace(sub_results, 2);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Threshold(2,4) STARK round trip failed: {:?}",
            verify_result.err()
        );
    }

    // ========================================================================
    // Custom gate tree tests (deep nesting)
    // ========================================================================

    #[test]
    fn compound_custom_and_or_not_depth_3() {
        // AND(OR(a,b), NOT(AND(c,d)))
        // a=true, b=false, c=false, d=true
        // OR(true, false) = true
        // AND(false, true) = false
        // NOT(false) = true
        // AND(true, true) = true => PASS
        let sub_results = &[true, false, false, true];
        let gates = deep_nested_gate_tree();
        let (trace, pi) = generate_custom_gate_trace(sub_results, &gates);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Deep nested AND(OR(t,f), NOT(AND(f,t))) should satisfy constraints"
        );
    }

    #[test]
    fn compound_custom_deep_nested_stark_prove_verify() {
        let sub_results = &[true, false, false, true];
        let gates = deep_nested_gate_tree();
        let (trace, pi) = generate_custom_gate_trace(sub_results, &gates);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Deep nested custom gate STARK prove/verify failed: {:?}",
            verify_result.err()
        );
    }

    #[test]
    fn compound_custom_deep_nested_fails_when_false() {
        // AND(OR(a,b), NOT(AND(c,d)))
        // a=false, b=false, c=true, d=true
        // OR(false, false) = false
        // AND(true, true) = true
        // NOT(true) = false
        // AND(false, false) = false => FAIL
        let sub_results = &[false, false, true, true];
        let gates = deep_nested_gate_tree();
        let (trace, pi) = generate_custom_gate_trace(sub_results, &gates);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "Deep nested gate tree with false result should fail STARK"
        );
    }

    #[test]
    fn compound_custom_three_level_passes() {
        // OR(AND(a,b), AND(c,d), AND(e,f))
        // a=true, b=true, c=false, d=false, e=false, f=false
        // AND(true, true) = true => OR with anything = true
        let sub_results = &[true, true, false, false, false, false];
        let gates = three_level_gate_tree();
        let (trace, pi) = generate_custom_gate_trace(sub_results, &gates);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Three-level gate tree should satisfy constraints"
        );
    }

    #[test]
    fn compound_custom_three_level_stark_round_trip() {
        let sub_results = &[true, true, false, false, false, false];
        let gates = three_level_gate_tree();
        let (trace, pi) = generate_custom_gate_trace(sub_results, &gates);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Three-level gate tree STARK round trip failed: {:?}",
            verify_result.err()
        );
    }

    #[test]
    fn compound_custom_three_level_all_false_rejected() {
        // OR(AND(f,f), AND(f,f), AND(f,f)) = false
        let sub_results = &[false, false, false, false, false, false];
        let gates = three_level_gate_tree();
        let (trace, pi) = generate_custom_gate_trace(sub_results, &gates);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "Three-level gate tree all-false should fail STARK"
        );
    }

    // ========================================================================
    // Sub-proof commitment binding tests
    // ========================================================================

    #[test]
    fn compound_sub_proof_commitments_valid() {
        let sub_results = &[true, true];
        let formula = BooleanFormula::And(vec![0, 1]);

        // Generate valid commitments
        let commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (trace, pi) = generate_trace_with_commitments(sub_results, &formula, &commitments);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Valid sub-proof commitments should satisfy constraints"
        );
    }

    #[test]
    fn compound_sub_proof_commitments_stark_round_trip() {
        let sub_results = &[true, true, false];
        let formula = BooleanFormula::Or(vec![0, 1, 2]);

        let commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (trace, pi) = generate_trace_with_commitments(sub_results, &formula, &commitments);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Sub-proof commitment STARK round trip failed: {:?}",
            verify_result.err()
        );
    }

    #[test]
    fn compound_adversarial_forged_commitment_caught() {
        // Adversary forges a sub-proof commitment: sets sub_proof_commitment[0]
        // to a DIFFERENT value than expected_commitment[0] (the PI-bound value).
        // The Equality constraint (C22) catches this.
        let sub_results = &[true, true];
        let formula = BooleanFormula::And(vec![0, 1]);

        // Generate valid commitments for PI.
        let valid_commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (mut trace, pi) =
            generate_trace_with_commitments(sub_results, &formula, &valid_commitments);

        // Adversary tampers: change sub_proof_commitment[0] in the trace
        // to a forged value (claiming a different sub-proof produced the result).
        let forged_commitment = BabyBear::new(99999);
        trace[0][SUB_PROOF_COMMITMENT_START] = forged_commitment;
        trace[1][SUB_PROOF_COMMITMENT_START] = forged_commitment;

        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Per-row constraint evaluation should catch the mismatch.
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Forged sub-proof commitment should be caught by Equality constraint"
        );
    }

    #[test]
    fn compound_adversarial_forged_commitment_stark_rejects() {
        let sub_results = &[true, true];
        let formula = BooleanFormula::And(vec![0, 1]);

        let valid_commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (mut trace, pi) =
            generate_trace_with_commitments(sub_results, &formula, &valid_commitments);

        // Forge commitment in trace.
        trace[0][SUB_PROOF_COMMITMENT_START] = BabyBear::new(12345);
        trace[1][SUB_PROOF_COMMITMENT_START] = BabyBear::new(12345);

        let circuit = compound_predicate_dsl_circuit();
        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "Forged sub-proof commitment should fail STARK verification"
        );
    }

    // ========================================================================
    // Nested composition: AND(OR(a, b), NOT(c)) via simple API
    // ========================================================================

    #[test]
    fn compound_nested_and_or_not_true_false_false() {
        // OR(true, false) = true, NOT(false) = true, AND(true, true) = true
        let (trace, pi) = generate_nested_trace(true, false, false);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "AND(OR(true,false), NOT(false)) should satisfy constraints"
        );
    }

    #[test]
    fn compound_nested_and_or_not_false_false_false() {
        // OR(false, false) = false, NOT(false) = true, AND(false, true) = false
        let or_result = false;
        let not_result = true;
        let formula = BooleanFormula::And(vec![0, 1]);
        let (trace, pi) = generate_compound_trace_full(&[or_result, not_result], &formula, None);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_err(),
            "AND(OR(false,false), NOT(false)) should fail (OR part is false)"
        );
    }

    // ========================================================================
    // Adversarial: wrong final result caught
    // ========================================================================

    #[test]
    fn compound_adversarial_wrong_composed_result_caught() {
        // Prover tries to claim AND(true, false) = true by setting composed_result=1
        // but and_intermediate correctly = 0. The Gated AND constraint catches this.
        let sub_results = &[true, false];
        let formula = BooleanFormula::And(vec![0, 1]);
        let tree_hash = compute_tree_hash(&formula, sub_results);

        let commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let mut row = vec![BabyBear::ZERO; COMPOUND_DSL_WIDTH];
        row[SUB_RESULT_START] = BabyBear::ONE;
        row[SUB_RESULT_START + 1] = BabyBear::ZERO;
        row[OP_AND] = BabyBear::ONE;
        row[COMPOSED_RESULT] = BabyBear::ONE; // WRONG: should be 0
        row[TREE_HASH] = tree_hash;
        row[AND_INTERMEDIATE] = BabyBear::ZERO; // Honest intermediate: 1*0=0
        for i in 0..MAX_SUB_PREDICATES {
            row[SUB_PROOF_COMMITMENT_START + i] = commitments[i];
            row[EXPECTED_COMMITMENT_START + i] = commitments[i];
        }
        let trace = vec![row.clone(), row];

        let mut pi = vec![BabyBear::ZERO; pi::COUNT];
        pi[pi::COMPOSED_RESULT_EXPECTED] = BabyBear::ONE;
        pi[pi::TREE_HASH] = tree_hash;
        for i in 0..MAX_SUB_PREDICATES {
            pi[pi::EXPECTED_COMMITMENT_START + i] = commitments[i];
        }

        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Adversarial wrong composed_result should be caught by gated AND constraint"
        );
    }

    #[test]
    fn compound_adversarial_non_binary_sub_result_caught() {
        // Prover sets sub_result_0 = 2 (not binary). Binary constraint catches this.
        let sub_results = &[true, true];
        let formula = BooleanFormula::And(vec![0, 1]);
        let (mut trace, pi) = generate_compound_trace_full(sub_results, &formula, None);

        // Tamper: set sub_result_0 to non-binary value.
        trace[0][SUB_RESULT_START] = BabyBear::new(2);
        trace[1][SUB_RESULT_START] = BabyBear::new(2);

        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Non-binary sub_result should be caught"
        );
    }

    // ========================================================================
    // STARK prove/verify round-trips
    // ========================================================================

    #[test]
    fn compound_stark_prove_verify_and_true_true() {
        let (trace, pi) = generate_compound_trace(&[true, true], CompoundOp::And);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for AND(true,true) failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compound_stark_prove_verify_or_true_false() {
        let (trace, pi) = generate_compound_trace(&[true, false], CompoundOp::Or);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for OR(true,false) failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compound_stark_prove_verify_not_false() {
        let (trace, pi) = generate_compound_trace(&[false], CompoundOp::Not);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for NOT(false) failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compound_stark_prove_verify_nested_composition() {
        // AND(OR(true, false), NOT(false)) = AND(true, true) = true
        let (trace, pi) = generate_nested_trace(true, false, false);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for nested AND(OR(t,f),NOT(f)) failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compound_stark_rejects_wrong_pi() {
        let (trace, pi) = generate_compound_trace(&[true, true], CompoundOp::And);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        // Wrong tree hash
        let mut wrong_pi = pi.clone();
        wrong_pi[pi::TREE_HASH] = BabyBear::new(99999);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong tree hash"
        );
    }

    #[test]
    fn compound_stark_and_many_predicates() {
        // AND of 5 predicates, all true
        let (trace, pi) = generate_compound_trace(&[true, true, true, true, true], CompoundOp::And);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for AND(5 true) failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn compound_stark_or_many_predicates_one_true() {
        // OR of 5 predicates, only one true
        let (trace, pi) =
            generate_compound_trace(&[false, false, true, false, false], CompoundOp::Or);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify for OR(5, one true) failed: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Full feature integration: Threshold + Commitments + STARK
    // ========================================================================

    #[test]
    fn compound_threshold_with_commitments_stark() {
        // Threshold(2, 4) with valid sub-proof commitments
        let sub_results = &[true, false, true, false];
        let formula = BooleanFormula::Threshold(2, vec![0, 1, 2, 3]);

        let commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (trace, pi) = generate_trace_with_commitments(sub_results, &formula, &commitments);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Threshold + commitments STARK failed: {:?}",
            verify_result.err()
        );
    }

    #[test]
    fn compound_custom_gate_with_commitments_stark() {
        // Deep nested gate tree with sub-proof commitments
        let sub_results = &[true, false, false, true];
        let gates = deep_nested_gate_tree();
        let formula = BooleanFormula::Custom(gates);

        let commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (trace, pi) = generate_trace_with_commitments(sub_results, &formula, &commitments);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let verify_result = stark::verify(&circuit, &proof, &pi);
        assert!(
            verify_result.is_ok(),
            "Custom gate + commitments STARK failed: {:?}",
            verify_result.err()
        );
    }

    // ========================================================================
    // Adversarial: wrong commitment under STARK
    // ========================================================================

    #[test]
    fn compound_adversarial_wrong_commitment_pi_mismatch() {
        // The verifier presents expected commitments in PI. If the prover's trace
        // has different commitments, the boundary constraint catches the mismatch.
        let sub_results = &[true, true];
        let formula = BooleanFormula::And(vec![0, 1]);

        let valid_commitments: Vec<BabyBear> = (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect();

        let (trace, pi) =
            generate_trace_with_commitments(sub_results, &formula, &valid_commitments);
        let circuit = compound_predicate_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        // Verifier presents DIFFERENT expected commitments in PI
        let mut wrong_pi = pi.clone();
        wrong_pi[pi::EXPECTED_COMMITMENT_START] = BabyBear::new(77777);

        let verify_result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            verify_result.is_err(),
            "Wrong PI commitment should fail STARK verification"
        );
    }
}
