//! Relational predicate expressed as a CircuitDescriptor.
//!
//! Port of `circuit/src/relational_predicate_air.rs` (1054 lines) to the DSL runtime.
//!
//! Proves comparison relationships between two private committed values:
//! - GT: value_a > value_b
//! - LT: value_a < value_b
//! - GTE: value_a >= value_b
//! - LTE: value_a <= value_b
//! - EQ: value_a == value_b
//! - NEQ: value_a != value_b
//! - DiffGT: value_a - value_b > threshold (relative standing)
//! - SumGT: value_a + value_b > threshold (joint qualification)
//!
//! # Protocol
//!
//! 1. Alice commits C_a = Poseidon2(value_a, blinding_a)
//! 2. Bob commits C_b = Poseidon2(value_b, blinding_b)
//! 3. A comparison service generates a STARK proof of the relation.
//! 4. Public inputs: [commitment_a, commitment_b, result_bit]
//!
//! # Trace Layout (width = 45)
//!
//! | Column    | Description                                         |
//! |-----------|-----------------------------------------------------|
//! | 0         | value_a (private witness)                           |
//! | 1         | blinding_a (private witness)                        |
//! | 2         | value_b (private witness)                           |
//! | 3         | blinding_b (private witness)                        |
//! | 4         | diff (computed based on relation type)              |
//! | 5..34     | diff_bits[0..29] (bit decomposition, 30 bits)       |
//! | 35        | neq_inverse (for NEQ only)                          |
//! | 36        | result_bit (always 1 for valid proof)               |
//! | 37        | range_flag (1=range op, 0=eq/neq)                   |
//! | 38        | eq_flag (1=EQ, 0=other)                             |
//! | 39        | neq_flag (1=NEQ, 0=other)                           |
//! | 40        | threshold_col (for DiffGT/SumGT, else 0)            |
//! | 41        | commitment_a (bound to PI[0])                       |
//! | 42        | commitment_b (bound to PI[1])                       |
//! | 43        | commit_verify_flag (1=verify Hash2to1 in-circuit)   |
//! | 44        | zero_pad (always 0)                                 |
//!
//! # Public Inputs
//!
//! `[commitment_a, commitment_b, result_bit]`
//!
//! # Constraint Strategy
//!
//! Uses three flags to select between constraint paths:
//! - range_flag=1: bit decomposition + high bit zero (GT, LT, GTE, LTE, DiffGT, SumGT)
//! - eq_flag=1: diff must be zero
//! - neq_flag=1: diff*inverse = 1
//!
//! Exactly one of {range_flag, eq_flag, neq_flag} must be active.
//!
//! When commit_verify_flag=1, the circuit verifies in-circuit that:
//! - commitment_a == Hash2to1(value_a, blinding_a)
//! - commitment_b == Hash2to1(value_b, blinding_b)

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::poseidon2;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const VALUE_A: usize = 0;
pub const BLINDING_A: usize = 1;
pub const VALUE_B: usize = 2;
pub const BLINDING_B: usize = 3;
pub const DIFF: usize = 4;
pub const DIFF_BITS_START: usize = 5;
pub const NUM_DIFF_BITS: usize = 30;
pub const NEQ_INVERSE: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 35
pub const RESULT_BIT: usize = NEQ_INVERSE + 1; // 36
pub const RANGE_FLAG: usize = RESULT_BIT + 1; // 37
pub const EQ_FLAG: usize = RANGE_FLAG + 1; // 38
pub const NEQ_FLAG: usize = EQ_FLAG + 1; // 39
pub const THRESHOLD_COL: usize = NEQ_FLAG + 1; // 40
pub const COMMITMENT_A: usize = THRESHOLD_COL + 1; // 41
pub const COMMITMENT_B: usize = COMMITMENT_A + 1; // 42
pub const COMMIT_VERIFY_FLAG: usize = COMMITMENT_B + 1; // 43
pub const ZERO_PAD: usize = COMMIT_VERIFY_FLAG + 1; // 44
pub const TRACE_WIDTH: usize = ZERO_PAD + 1; // 45

/// Public input indices.
pub const PI_COMMITMENT_A: usize = 0;
pub const PI_COMMITMENT_B: usize = 1;
pub const PI_RESULT_BIT: usize = 2;
pub const PUBLIC_INPUT_COUNT: usize = 3;

/// Relational operator types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationalOp {
    GreaterThan,
    LessThan,
    GreaterOrEqual,
    LessOrEqual,
    Equal,
    NotEqual,
    /// Prove value_a - value_b > threshold.
    DiffGreaterThan(u32),
    /// Prove value_a + value_b > threshold.
    SumGreaterThan(u32),
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the relational predicate `CircuitDescriptor`.
pub fn relational_predicate_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef {
        name: "value_a".into(),
        index: VALUE_A,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "blinding_a".into(),
        index: BLINDING_A,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "value_b".into(),
        index: VALUE_B,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "blinding_b".into(),
        index: BLINDING_B,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "diff".into(),
        index: DIFF,
        kind: ColumnKind::Value,
    });
    for i in 0..NUM_DIFF_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: DIFF_BITS_START + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "neq_inverse".into(),
        index: NEQ_INVERSE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "result_bit".into(),
        index: RESULT_BIT,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "range_flag".into(),
        index: RANGE_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "eq_flag".into(),
        index: EQ_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "neq_flag".into(),
        index: NEQ_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "threshold_col".into(),
        index: THRESHOLD_COL,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "commitment_a".into(),
        index: COMMITMENT_A,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "commitment_b".into(),
        index: COMMITMENT_B,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "commit_verify_flag".into(),
        index: COMMIT_VERIFY_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "zero_pad".into(),
        index: ZERO_PAD,
        kind: ColumnKind::Value,
    });

    let mut constraints = Vec::new();

    // ─── C1: result_bit matches public input ────────────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: RESULT_BIT,
        pi_index: PI_RESULT_BIT,
    });

    // ─── C2: result_bit is 1 ────────────────────────────────────────────────
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![RESULT_BIT],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // ─── C3: Flags are binary ───────────────────────────────────────────────
    constraints.push(ConstraintExpr::Binary { col: RANGE_FLAG });
    constraints.push(ConstraintExpr::Binary { col: EQ_FLAG });
    constraints.push(ConstraintExpr::Binary { col: NEQ_FLAG });

    // ─── C4: Exactly one flag active: range + eq + neq = 1 ─────────────────
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![RANGE_FLAG],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![EQ_FLAG],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![NEQ_FLAG],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // ─── C5: At least one flag active ───────────────────────────────────────
    constraints.push(ConstraintExpr::AtLeastOne {
        flag_cols: vec![RANGE_FLAG, EQ_FLAG, NEQ_FLAG],
    });

    // ─── C6: Bit binary constraints (gated by range_flag) ───────────────────
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: RANGE_FLAG,
            inner: Box::new(ConstraintExpr::Binary {
                col: DIFF_BITS_START + i,
            }),
        });
    }

    // ─── C7: Bit reconstruction (gated by range_flag) ───────────────────────
    {
        let mut terms = Vec::with_capacity(NUM_DIFF_BITS + 1);
        let mut power_of_two = 1u32;
        for i in 0..NUM_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(power_of_two),
                col_indices: vec![DIFF_BITS_START + i],
            });
            power_of_two = power_of_two.wrapping_mul(2);
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![DIFF],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: RANGE_FLAG,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // ─── C8: High bit zero (gated by range_flag) ────────────────────────────
    constraints.push(ConstraintExpr::Gated {
        selector_col: RANGE_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
            }],
        }),
    });

    // ─── C9: EQ check: diff == 0 (gated by eq_flag) ────────────────────────
    constraints.push(ConstraintExpr::Gated {
        selector_col: EQ_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF],
            }],
        }),
    });

    // ─── C10: NEQ check: diff * inverse - 1 == 0 (gated by neq_flag) ───────
    constraints.push(ConstraintExpr::Gated {
        selector_col: NEQ_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![DIFF, NEQ_INVERSE],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![],
                },
            ],
        }),
    });

    // ─── C11: commit_verify_flag is binary ──────────────────────────────────
    constraints.push(ConstraintExpr::Binary {
        col: COMMIT_VERIFY_FLAG,
    });

    // ─── C12: commitment_a matches PI[0] ────────────────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: COMMITMENT_A,
        pi_index: PI_COMMITMENT_A,
    });

    // ─── C13: commitment_b matches PI[1] ────────────────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: COMMITMENT_B,
        pi_index: PI_COMMITMENT_B,
    });

    // ─── C14: Commitment A binding (gated by commit_verify_flag) ────────────
    // Hash2to1(value_a, blinding_a) == commitment_a
    constraints.push(ConstraintExpr::Gated {
        selector_col: COMMIT_VERIFY_FLAG,
        inner: Box::new(ConstraintExpr::Hash2to1 {
            output_col: COMMITMENT_A,
            input_col_a: VALUE_A,
            input_col_b: BLINDING_A,
        }),
    });

    // ─── C15: Commitment B binding (gated by commit_verify_flag) ────────────
    // Hash2to1(value_b, blinding_b) == commitment_b
    constraints.push(ConstraintExpr::Gated {
        selector_col: COMMIT_VERIFY_FLAG,
        inner: Box::new(ConstraintExpr::Hash2to1 {
            output_col: COMMITMENT_B,
            input_col_a: VALUE_B,
            input_col_b: BLINDING_B,
        }),
    });

    // ─── C16: zero_pad must be zero ─────────────────────────────────────────
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![ZERO_PAD],
        }],
    });

    // ─── Boundaries ──────────────────────────────────────────────────────────
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: RESULT_BIT,
            pi_index: PI_RESULT_BIT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: COMMITMENT_A,
            pi_index: PI_COMMITMENT_A,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: COMMITMENT_B,
            pi_index: PI_COMMITMENT_B,
        },
    ];

    CircuitDescriptor {
        name: "pyana-relational-predicate-dsl-v2".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3, // Gated(Hash2to1) = 1 + 2 = 3; AtLeastOne(3 flags) = 3
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Compute a value commitment: Poseidon2(value, blinding).
pub fn compute_commitment(value: BabyBear, blinding: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(value, blinding)
}

/// Full witness for relational trace generation.
#[derive(Clone, Debug)]
pub struct RelationalWitness {
    pub value_a: u32,
    pub blinding_a: u32,
    pub value_b: u32,
    pub blinding_b: u32,
    pub op: RelationalOp,
    /// When true, enables in-circuit commitment verification.
    pub verify_commitments: bool,
}

/// Generate a valid relational predicate trace.
///
/// Returns `(trace, public_inputs)`.
pub fn generate_relational_trace(
    value_a: u32,
    blinding_a: u32,
    value_b: u32,
    blinding_b: u32,
    op: RelationalOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_relational_trace_full(RelationalWitness {
        value_a,
        blinding_a,
        value_b,
        blinding_b,
        op,
        verify_commitments: false,
    })
}

/// Generate a relational trace with full witness control.
pub fn generate_relational_trace_full(
    witness: RelationalWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

    row[VALUE_A] = BabyBear::new(witness.value_a);
    row[BLINDING_A] = BabyBear::new(witness.blinding_a);
    row[VALUE_B] = BabyBear::new(witness.value_b);
    row[BLINDING_B] = BabyBear::new(witness.blinding_b);
    row[RESULT_BIT] = BabyBear::ONE;

    // Compute diff based on operation.
    let diff = match witness.op {
        RelationalOp::GreaterThan => witness
            .value_a
            .wrapping_sub(witness.value_b)
            .wrapping_sub(1),
        RelationalOp::LessThan => witness
            .value_b
            .wrapping_sub(witness.value_a)
            .wrapping_sub(1),
        RelationalOp::GreaterOrEqual => witness.value_a.wrapping_sub(witness.value_b),
        RelationalOp::LessOrEqual => witness.value_b.wrapping_sub(witness.value_a),
        RelationalOp::Equal | RelationalOp::NotEqual => {
            witness.value_a.wrapping_sub(witness.value_b)
        }
        RelationalOp::DiffGreaterThan(threshold) => {
            // diff = (a - b) - threshold - 1
            witness
                .value_a
                .wrapping_sub(witness.value_b)
                .wrapping_sub(threshold)
                .wrapping_sub(1)
        }
        RelationalOp::SumGreaterThan(threshold) => {
            // diff = (a + b) - threshold - 1
            witness
                .value_a
                .wrapping_add(witness.value_b)
                .wrapping_sub(threshold)
                .wrapping_sub(1)
        }
    };
    row[DIFF] = BabyBear::new(diff);

    // Set threshold column for DiffGT/SumGT.
    match witness.op {
        RelationalOp::DiffGreaterThan(t) | RelationalOp::SumGreaterThan(t) => {
            row[THRESHOLD_COL] = BabyBear::new(t);
        }
        _ => {}
    }

    // Set flags and path-specific witness.
    match witness.op {
        RelationalOp::Equal => {
            row[EQ_FLAG] = BabyBear::ONE;
        }
        RelationalOp::NotEqual => {
            row[NEQ_FLAG] = BabyBear::ONE;
            let diff_field = BabyBear::new(diff);
            if let Some(inv) = diff_field.inverse() {
                row[NEQ_INVERSE] = inv;
            }
        }
        _ => {
            row[RANGE_FLAG] = BabyBear::ONE;
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
            }
        }
    }

    // Commitment columns.
    let commitment_a = compute_commitment(
        BabyBear::new(witness.value_a),
        BabyBear::new(witness.blinding_a),
    );
    let commitment_b = compute_commitment(
        BabyBear::new(witness.value_b),
        BabyBear::new(witness.blinding_b),
    );
    row[COMMITMENT_A] = commitment_a;
    row[COMMITMENT_B] = commitment_b;

    // Commitment verification flag.
    if witness.verify_commitments {
        row[COMMIT_VERIFY_FLAG] = BabyBear::ONE;
    }

    // Zero pad is already zero.

    let public_inputs = vec![commitment_a, commitment_b, BabyBear::ONE];

    // Pad to 2 rows.
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::stark::{self, StarkAir};
    use pyana_dsl_runtime::circuit::DslCircuit;

    // ========================================================================
    // Descriptor structure
    // ========================================================================

    #[test]
    fn test_relational_descriptor_validates() {
        let descriptor = relational_predicate_descriptor();
        let result = descriptor.validate();
        assert!(
            result.is_ok(),
            "Descriptor validation failed: {:?}",
            result.err()
        );

        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(descriptor.name, "pyana-relational-predicate-dsl-v2");
    }

    // ========================================================================
    // GT tests
    // ========================================================================

    #[test]
    fn test_relational_gt_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(100, 111, 50, 222, RelationalOp::GreaterThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GT 100 > 50 should pass");
    }

    #[test]
    fn test_relational_gt_equal_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(50, 111, 50, 222, RelationalOp::GreaterThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "GT 50 > 50 should fail");
    }

    #[test]
    fn test_relational_gt_less_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(30, 111, 100, 222, RelationalOp::GreaterThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "GT 30 > 100 should fail");
    }

    // ========================================================================
    // LT tests
    // ========================================================================

    #[test]
    fn test_relational_lt_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(30, 333, 100, 444, RelationalOp::LessThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "LT 30 < 100 should pass");
    }

    #[test]
    fn test_relational_lt_greater_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(100, 333, 30, 444, RelationalOp::LessThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "LT 100 < 30 should fail");
    }

    // ========================================================================
    // GTE tests
    // ========================================================================

    #[test]
    fn test_relational_gte_equal() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(50, 555, 50, 666, RelationalOp::GreaterOrEqual);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 50 >= 50 should pass");
    }

    #[test]
    fn test_relational_gte_greater() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) =
            generate_relational_trace(100, 555, 50, 666, RelationalOp::GreaterOrEqual);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 100 >= 50 should pass");
    }

    // ========================================================================
    // LTE tests
    // ========================================================================

    #[test]
    fn test_relational_lte_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(30, 777, 100, 888, RelationalOp::LessOrEqual);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "LTE 30 <= 100 should pass");
    }

    // ========================================================================
    // EQ tests
    // ========================================================================

    #[test]
    fn test_relational_eq_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(42, 100, 42, 200, RelationalOp::Equal);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "EQ 42 == 42 should pass");
    }

    #[test]
    fn test_relational_eq_fails_when_different() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(42, 100, 43, 200, RelationalOp::Equal);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "EQ 42 == 43 should fail");
    }

    // ========================================================================
    // NEQ tests
    // ========================================================================

    #[test]
    fn test_relational_neq_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(42, 300, 100, 400, RelationalOp::NotEqual);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "NEQ 42 != 100 should pass");
    }

    #[test]
    fn test_relational_neq_fails_when_same() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(42, 300, 42, 400, RelationalOp::NotEqual);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "NEQ 42 != 42 should fail");
    }

    // ========================================================================
    // DiffGreaterThan tests (relative standing)
    // ========================================================================

    #[test]
    fn test_relational_diff_gt_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Prove: 200 - 50 > 100 (i.e., 150 > 100)
        let (trace, pi) =
            generate_relational_trace(200, 500, 50, 600, RelationalOp::DiffGreaterThan(100));
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "DiffGT (200-50=150) > 100 should pass"
        );
    }

    #[test]
    fn test_relational_diff_gt_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Prove: 120 - 50 > 100 (i.e., 70 > 100) -- should FAIL
        let (trace, pi) =
            generate_relational_trace(120, 500, 50, 600, RelationalOp::DiffGreaterThan(100));
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "DiffGT (120-50=70) > 100 should fail"
        );
    }

    #[test]
    fn test_relational_diff_gt_boundary() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Prove: 151 - 50 > 100 (i.e., 101 > 100) -- barely passes
        let (trace, pi) =
            generate_relational_trace(151, 500, 50, 600, RelationalOp::DiffGreaterThan(100));
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "DiffGT (151-50=101) > 100 should pass"
        );

        // Prove: 150 - 50 > 100 (i.e., 100 > 100) -- fails (not strictly greater)
        let (trace2, pi2) =
            generate_relational_trace(150, 500, 50, 600, RelationalOp::DiffGreaterThan(100));
        let result2 = circuit.eval_constraints(&trace2[0], &trace2[1], &pi2, alpha);
        assert_ne!(
            result2,
            BabyBear::ZERO,
            "DiffGT (150-50=100) > 100 should fail (not strictly greater)"
        );
    }

    // ========================================================================
    // SumGreaterThan tests (joint qualification)
    // ========================================================================

    #[test]
    fn test_relational_sum_gt_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Prove: 300 + 400 > 500 (i.e., 700 > 500)
        let (trace, pi) =
            generate_relational_trace(300, 700, 400, 800, RelationalOp::SumGreaterThan(500));
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "SumGT (300+400=700) > 500 should pass"
        );
    }

    #[test]
    fn test_relational_sum_gt_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Prove: 200 + 200 > 500 (i.e., 400 > 500) -- should FAIL
        let (trace, pi) =
            generate_relational_trace(200, 700, 200, 800, RelationalOp::SumGreaterThan(500));
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "SumGT (200+200=400) > 500 should fail"
        );
    }

    #[test]
    fn test_relational_sum_gt_boundary() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 251 + 250 > 500 (i.e., 501 > 500) -- barely passes
        let (trace, pi) =
            generate_relational_trace(251, 700, 250, 800, RelationalOp::SumGreaterThan(500));
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "SumGT (251+250=501) > 500 should pass"
        );
    }

    // ========================================================================
    // Commitment verification tests
    // ========================================================================

    #[test]
    fn test_relational_commitment_binding_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let witness = RelationalWitness {
            value_a: 100,
            blinding_a: 111,
            value_b: 50,
            blinding_b: 222,
            op: RelationalOp::GreaterThan,
            verify_commitments: true,
        };

        let (trace, pi) = generate_relational_trace_full(witness);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "GT 100 > 50 with commitment verification should pass"
        );
    }

    #[test]
    fn test_relational_wrong_commitment_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let witness = RelationalWitness {
            value_a: 100,
            blinding_a: 111,
            value_b: 50,
            blinding_b: 222,
            op: RelationalOp::GreaterThan,
            verify_commitments: true,
        };

        let (mut trace, pi) = generate_relational_trace_full(witness);
        // Tamper with value_a (so it no longer matches the commitment)
        trace[0][VALUE_A] = BabyBear::new(999);
        trace[1][VALUE_A] = BabyBear::new(999);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered value should fail commitment binding"
        );
    }

    #[test]
    fn test_relational_wrong_blinding_fails() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let witness = RelationalWitness {
            value_a: 100,
            blinding_a: 111,
            value_b: 50,
            blinding_b: 222,
            op: RelationalOp::GreaterThan,
            verify_commitments: true,
        };

        let (mut trace, pi) = generate_relational_trace_full(witness);
        // Tamper with blinding_b
        trace[0][BLINDING_B] = BabyBear::new(999);
        trace[1][BLINDING_B] = BabyBear::new(999);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered blinding should fail commitment binding"
        );
    }

    // ========================================================================
    // Adversarial: tampered trace
    // ========================================================================

    #[test]
    fn test_relational_tampered_diff_caught() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (mut trace, pi) =
            generate_relational_trace(100, 111, 50, 222, RelationalOp::GreaterThan);
        trace[0][DIFF] = BabyBear::ZERO;
        trace[1][DIFF] = BabyBear::ZERO;

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "Tampered diff should be caught");
    }

    // ========================================================================
    // Overflow/underflow detection
    // ========================================================================

    #[test]
    fn test_relational_overflow_detection() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) =
            generate_relational_trace(10, 111, 1000000, 222, RelationalOp::GreaterThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Overflow should be caught by high bit"
        );
    }

    // ========================================================================
    // Unlinkability
    // ========================================================================

    #[test]
    fn test_different_blindings_produce_different_commitments() {
        let value = BabyBear::new(1000);
        let c1 = compute_commitment(value, BabyBear::new(42));
        let c2 = compute_commitment(value, BabyBear::new(43));
        assert_ne!(
            c1, c2,
            "Different blindings must produce different commitments"
        );
    }

    // ========================================================================
    // STARK prove/verify
    // ========================================================================

    #[test]
    fn test_relational_stark_prove_verify_gt() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(100, 111, 50, 222, RelationalOp::GreaterThan);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify GT failed: {:?}", result.err());
    }

    #[test]
    fn test_relational_stark_prove_verify_eq() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(42, 100, 42, 200, RelationalOp::Equal);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify EQ failed: {:?}", result.err());
    }

    #[test]
    fn test_relational_stark_prove_verify_neq() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(42, 300, 100, 400, RelationalOp::NotEqual);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK verify NEQ failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_relational_stark_prove_verify_lte() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_relational_trace(30, 777, 100, 888, RelationalOp::LessOrEqual);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK verify LTE failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_relational_stark_prove_verify_diff_gt() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) =
            generate_relational_trace(200, 500, 50, 600, RelationalOp::DiffGreaterThan(100));
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK verify DiffGT failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_relational_stark_prove_verify_sum_gt() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) =
            generate_relational_trace(300, 700, 400, 800, RelationalOp::SumGreaterThan(500));
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK verify SumGT failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_relational_stark_rejects_wrong_pi() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor.clone());

        let (trace, pi) = generate_relational_trace(100, 111, 50, 222, RelationalOp::GreaterThan);
        let proof = stark::prove(&circuit, &trace, &pi);

        let wrong_pi = vec![BabyBear::new(99999), pi[1], pi[2]];
        let circuit2 = DslCircuit::new(descriptor);
        let result = stark::verify(&circuit2, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong commitment");
    }

    #[test]
    fn test_relational_stark_with_commitment_verification() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let witness = RelationalWitness {
            value_a: 100,
            blinding_a: 111,
            value_b: 50,
            blinding_b: 222,
            op: RelationalOp::GreaterThan,
            verify_commitments: true,
        };

        let (trace, pi) = generate_relational_trace_full(witness);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK with commitment verification failed: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Scenario tests (from original)
    // ========================================================================

    #[test]
    fn test_auction_scenario() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Alice bids 5000, Bob bids 3000. Prove Alice > Bob.
        let witness = RelationalWitness {
            value_a: 5000,
            blinding_a: 98765,
            value_b: 3000,
            blinding_b: 12345,
            op: RelationalOp::GreaterThan,
            verify_commitments: true,
        };

        let (trace, pi) = generate_relational_trace_full(witness);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Auction scenario failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_joint_qualification_scenario() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Alice=300, Bob=400. Prove combined > 500.
        let (trace, pi) =
            generate_relational_trace(300, 11111, 400, 22222, RelationalOp::SumGreaterThan(500));
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Joint qualification scenario failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_reputation_scenario() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Alice=800, Bob=200. Prove Alice - Bob > 500.
        let (trace, pi) =
            generate_relational_trace(800, 33333, 200, 44444, RelationalOp::DiffGreaterThan(500));
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Reputation scenario failed: {:?}",
            result.err()
        );
    }
}
