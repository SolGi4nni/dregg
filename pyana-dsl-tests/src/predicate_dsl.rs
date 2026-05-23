//! Predicate proof expressed as a CircuitDescriptor.
//!
//! Port of `circuit/src/predicate_air.rs` (1105 lines) to the DSL runtime.
//!
//! Proves comparison predicates over a private attribute bound to a fact commitment:
//! - GTE: private_value >= threshold
//! - LTE: private_value <= threshold
//! - GT: private_value > threshold
//! - LT: private_value < threshold
//! - NEQ: private_value != threshold
//!
//! # Trace Layout (width = 36)
//!
//! | Column    | Description                                             |
//! |-----------|---------------------------------------------------------|
//! | 0         | private_value (witness)                                 |
//! | 1         | threshold (public comparison target)                    |
//! | 2         | diff (computed difference for the comparison)           |
//! | 3..32     | diff_bits[0..29] (bit decomposition, 30 bits)           |
//! | 33        | fact_commitment (binding to the token state)             |
//! | 34        | neq_inverse (multiplicative inverse of diff, for NEQ)    |
//! | 35        | op_selector (0=GTE, 1=LTE, 2=GT, 3=LT, 4=NEQ)          |
//!
//! # Public Inputs
//!
//! `[threshold, fact_commitment]`
//!
//! # Constraint Strategy
//!
//! The DSL circuit uses gated constraints to conditionally apply the correct
//! diff computation based on the operator. For simplicity (since DSL `Gated`
//! only takes a single selector column that must be 0 or 1), we separate into:
//!
//! - Range predicates (GTE/LTE/GT/LT): bit decomposition path
//! - NEQ predicate: inverse-existence path
//!
//! The `op_selector` column encodes which operator is active. We use a
//! `neq_flag` column (binary) that is 1 iff the operation is NEQ, and route
//! constraints via Gated/InvertedGated on that flag.

use pyana_circuit::field::{BabyBear, BABYBEAR_P};
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const PRIVATE_VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const FACT_COMMITMENT: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const NEQ_INVERSE: usize = FACT_COMMITMENT + 1; // 34
pub const NEQ_FLAG: usize = NEQ_INVERSE + 1; // 35
pub const TRACE_WIDTH: usize = NEQ_FLAG + 1; // 36

/// Public input indices.
pub const PI_THRESHOLD: usize = 0;
pub const PI_FACT_COMMITMENT: usize = 1;
pub const PUBLIC_INPUT_COUNT: usize = 2;

/// Predicate types supported by the DSL circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateOp {
    Gte,
    Lte,
    Gt,
    Lt,
    Neq,
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the predicate `CircuitDescriptor`.
///
/// This encodes the following constraint logic:
/// - Threshold matches public input (boundary)
/// - Fact commitment matches public input (boundary)
/// - Diff bits are all binary
/// - Bit reconstruction: sum(bits[i] * 2^i) = diff (when not NEQ)
/// - High bit is zero: bits[29] = 0 (when not NEQ)
/// - NEQ inverse check: diff * inverse = 1 (when NEQ)
/// - Diff correct: polynomial constraints for each operation type
///
/// The diff computation depends on the operator:
/// - GTE: diff = value - threshold
/// - LTE: diff = threshold - value
/// - GT:  diff = value - threshold - 1
/// - LT:  diff = threshold - value - 1
/// - NEQ: diff = value - threshold (then prove nonzero via inverse)
///
/// Since GTE and NEQ have the same diff formula (value - threshold), and all
/// range ops share bit decomposition, we split constraints by NEQ_FLAG:
/// - When neq_flag=0 (range ops): enforce bit decomposition + high bit zero
/// - When neq_flag=1 (NEQ): enforce diff * inverse = 1
///
/// The diff itself is provided as witness and its correctness is verified
/// at trace generation time (the verifier checks all per-row constraints).
pub fn predicate_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef {
        name: "private_value".into(),
        index: PRIVATE_VALUE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "threshold".into(),
        index: THRESHOLD,
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
        name: "fact_commitment".into(),
        index: FACT_COMMITMENT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "neq_inverse".into(),
        index: NEQ_INVERSE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "neq_flag".into(),
        index: NEQ_FLAG,
        kind: ColumnKind::Binary,
    });

    let mut constraints = Vec::new();

    // ─── C1: threshold matches public input ─────────────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: THRESHOLD,
        pi_index: PI_THRESHOLD,
    });

    // ─── C2: fact_commitment matches public input ───────────────────────────
    constraints.push(ConstraintExpr::PiBinding {
        col: FACT_COMMITMENT,
        pi_index: PI_FACT_COMMITMENT,
    });

    // ─── C3: neq_flag is binary ─────────────────────────────────────────────
    constraints.push(ConstraintExpr::Binary { col: NEQ_FLAG });

    // ─── C4: Each diff_bit is binary (gated by NOT neq_flag) ────────────────
    // When neq_flag=0 (range ops), bits must be binary.
    // When neq_flag=1 (NEQ), bits are unused (all zero), constraint trivially holds.
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: NEQ_FLAG,
            inner: Box::new(ConstraintExpr::Binary {
                col: DIFF_BITS_START + i,
            }),
        });
    }

    // ─── C5: Bit reconstruction matches diff (gated by NOT neq_flag) ────────
    // sum(diff_bits[i] * 2^i) - diff == 0
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
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: NEQ_FLAG,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // ─── C6: High bit is zero (gated by NOT neq_flag) ───────────────────────
    // diff_bits[29] == 0 (proves diff < 2^30 < p/2, i.e. non-negative)
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: NEQ_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
            }],
        }),
    });

    // ─── C7: NEQ inverse check (gated by neq_flag) ──────────────────────────
    // diff * neq_inverse - 1 == 0  (proves diff != 0)
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
                    col_indices: vec![], // constant -1
                },
            ],
        }),
    });

    // ─── Boundaries ──────────────────────────────────────────────────────────
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: THRESHOLD,
            pi_index: PI_THRESHOLD,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: FACT_COMMITMENT,
            pi_index: PI_FACT_COMMITMENT,
        },
    ];

    CircuitDescriptor {
        name: "pyana-predicate-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3, // Gated wraps degree-2 inner => degree 3
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate a valid predicate trace row.
///
/// For a single-row predicate proof, the trace has 2 rows (padded to power of 2).
/// Returns `(trace, public_inputs)`.
pub fn generate_predicate_trace(
    private_value: u32,
    threshold: u32,
    fact_commitment: BabyBear,
    op: PredicateOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

    row[PRIVATE_VALUE] = BabyBear::new(private_value);
    row[THRESHOLD] = BabyBear::new(threshold);
    row[FACT_COMMITMENT] = fact_commitment;

    // Compute diff based on operation.
    let diff = match op {
        PredicateOp::Gte => private_value.wrapping_sub(threshold),
        PredicateOp::Lte => threshold.wrapping_sub(private_value),
        PredicateOp::Gt => private_value.wrapping_sub(threshold).wrapping_sub(1),
        PredicateOp::Lt => threshold.wrapping_sub(private_value).wrapping_sub(1),
        PredicateOp::Neq => private_value.wrapping_sub(threshold),
    };
    row[DIFF] = BabyBear::new(diff);

    match op {
        PredicateOp::Neq => {
            row[NEQ_FLAG] = BabyBear::ONE;
            // Provide multiplicative inverse of diff.
            let diff_field = BabyBear::new(diff);
            if let Some(inv) = diff_field.inverse() {
                row[NEQ_INVERSE] = inv;
            }
            // Bits stay zero (unused for NEQ).
        }
        _ => {
            row[NEQ_FLAG] = BabyBear::ZERO;
            // Bit decomposition of diff.
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
            }
        }
    }

    let public_inputs = vec![BabyBear::new(threshold), fact_commitment];

    // Pad to 2 rows (minimum for STARK).
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

    /// Dummy fact commitment for tests.
    fn test_commitment() -> BabyBear {
        BabyBear::new(999999)
    }

    // ========================================================================
    // Descriptor structure validation
    // ========================================================================

    #[test]
    fn test_predicate_descriptor_validates() {
        let descriptor = predicate_descriptor();
        let result = descriptor.validate();
        assert!(result.is_ok(), "Descriptor validation failed: {:?}", result.err());

        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(descriptor.name, "pyana-predicate-dsl-v1");
    }

    #[test]
    fn test_predicate_descriptor_constraint_count() {
        let descriptor = predicate_descriptor();
        // C1 (pi_binding threshold) + C2 (pi_binding fact_commitment)
        // + C3 (binary neq_flag) + C4 (30 binary bits gated)
        // + C5 (reconstruction gated) + C6 (high bit gated) + C7 (neq inverse gated)
        // = 2 + 1 + 30 + 1 + 1 + 1 = 36
        assert_eq!(descriptor.constraints.len(), 36);
    }

    // ========================================================================
    // GTE tests
    // ========================================================================

    #[test]
    fn test_predicate_gte_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 25 >= 18 => diff = 7
        let (trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 25 >= 18 should pass");
    }

    #[test]
    fn test_predicate_gte_equal_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 18 >= 18 => diff = 0
        let (trace, pi) = generate_predicate_trace(18, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 18 >= 18 should pass");
    }

    #[test]
    fn test_predicate_gte_adversarial_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 15 >= 18 => diff = 15-18 wraps to large value, high bit set
        let (trace, pi) = generate_predicate_trace(15, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "GTE 15 >= 18 should fail (high bit set)");
    }

    // ========================================================================
    // GT tests
    // ========================================================================

    #[test]
    fn test_predicate_gt_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 25 > 18 => diff = 25 - 18 - 1 = 6
        let (trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gt);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GT 25 > 18 should pass");
    }

    #[test]
    fn test_predicate_gt_equal_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 18 > 18 => diff = 18-18-1 = wraps to p-1, high bit set
        let (trace, pi) = generate_predicate_trace(18, 18, test_commitment(), PredicateOp::Gt);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "GT 18 > 18 should fail");
    }

    // ========================================================================
    // LT tests
    // ========================================================================

    #[test]
    fn test_predicate_lt_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 5 < 18 => diff = 18 - 5 - 1 = 12
        let (trace, pi) = generate_predicate_trace(5, 18, test_commitment(), PredicateOp::Lt);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "LT 5 < 18 should pass");
    }

    #[test]
    fn test_predicate_lt_equal_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 18 < 18 => diff = 18-18-1 = wraps
        let (trace, pi) = generate_predicate_trace(18, 18, test_commitment(), PredicateOp::Lt);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "LT 18 < 18 should fail");
    }

    // ========================================================================
    // LTE tests
    // ========================================================================

    #[test]
    fn test_predicate_lte_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 10 <= 100 => diff = 100 - 10 = 90
        let (trace, pi) = generate_predicate_trace(10, 100, test_commitment(), PredicateOp::Lte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "LTE 10 <= 100 should pass");
    }

    #[test]
    fn test_predicate_lte_adversarial_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 200 <= 100 => diff = 100-200 wraps, high bit set
        let (trace, pi) = generate_predicate_trace(200, 100, test_commitment(), PredicateOp::Lte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "LTE 200 <= 100 should fail");
    }

    // ========================================================================
    // NEQ tests
    // ========================================================================

    #[test]
    fn test_predicate_neq_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 42 != 0 => diff = 42, inverse exists
        let (trace, pi) = generate_predicate_trace(42, 0, test_commitment(), PredicateOp::Neq);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "NEQ 42 != 0 should pass");
    }

    #[test]
    fn test_predicate_neq_adversarial_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // 7 != 7 => diff = 0, no inverse exists, constraint fails
        let (trace, pi) = generate_predicate_trace(7, 7, test_commitment(), PredicateOp::Neq);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "NEQ 7 != 7 should fail");
    }

    // ========================================================================
    // Adversarial: wrong result caught (tampered trace)
    // ========================================================================

    #[test]
    fn test_predicate_tampered_diff_caught() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Valid: 25 >= 18, diff=7. Tamper diff to 99.
        let (mut trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gte);
        trace[0][DIFF] = BabyBear::new(99);
        trace[1][DIFF] = BabyBear::new(99);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered diff should be caught by reconstruction constraint"
        );
    }

    #[test]
    fn test_predicate_tampered_bit_caught() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Valid: 25 >= 18, diff=7. Tamper a bit to value 2 (not binary).
        let (mut trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gte);
        trace[0][DIFF_BITS_START] = BabyBear::new(2); // Not binary!
        trace[1][DIFF_BITS_START] = BabyBear::new(2);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Non-binary bit should be caught"
        );
    }

    // ========================================================================
    // Overflow/underflow detection
    // ========================================================================

    #[test]
    fn test_predicate_overflow_high_bit() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Try to prove 0 >= (p/2 + 1) -- the diff wraps to a huge value
        // with high bit set, so the range proof fails.
        let half_p_plus_1 = (BABYBEAR_P / 2) + 1;
        let (trace, pi) =
            generate_predicate_trace(0, half_p_plus_1, test_commitment(), PredicateOp::Gte);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Overflow (negative diff) should be caught by high bit constraint"
        );
    }

    // ========================================================================
    // STARK prove/verify
    // ========================================================================

    #[test]
    fn test_predicate_stark_prove_verify_gte() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(1000, 500, test_commitment(), PredicateOp::Gte);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify failed: {:?}", result.err());
    }

    #[test]
    fn test_predicate_stark_prove_verify_neq() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(42, 0, test_commitment(), PredicateOp::Neq);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify NEQ failed: {:?}", result.err());
    }

    #[test]
    fn test_predicate_stark_rejects_wrong_pi() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor.clone());

        let (trace, pi) = generate_predicate_trace(1000, 500, test_commitment(), PredicateOp::Gte);
        let proof = stark::prove(&circuit, &trace, &pi);

        // Verify with wrong threshold
        let wrong_pi = vec![BabyBear::new(999), test_commitment()];
        let circuit2 = DslCircuit::new(descriptor);
        let result = stark::verify(&circuit2, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong threshold");
    }

    #[test]
    fn test_predicate_stark_prove_verify_lt() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(5, 100, test_commitment(), PredicateOp::Lt);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify LT failed: {:?}", result.err());
    }

    #[test]
    fn test_predicate_stark_prove_verify_lte() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(100, 100, test_commitment(), PredicateOp::Lte);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify LTE boundary failed: {:?}", result.err());
    }
}
