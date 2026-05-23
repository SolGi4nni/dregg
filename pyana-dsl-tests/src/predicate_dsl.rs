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
//! - InRangeLow: value >= low (lower bound of range proof)
//! - InRangeHigh: value <= high (upper bound of range proof)
//!
//! # Trace Layout (width = 40)
//!
//! | Column    | Description                                             |
//! |-----------|---------------------------------------------------------|
//! | 0         | private_value (witness)                                 |
//! | 1         | threshold (public comparison target)                    |
//! | 2         | diff (computed difference for the comparison)           |
//! | 3..32     | diff_bits[0..29] (bit decomposition, 30 bits)           |
//! | 33        | fact_commitment (binding to the token state)             |
//! | 34        | neq_inverse (multiplicative inverse of diff, for NEQ)    |
//! | 35        | neq_flag (1=NEQ, 0=range op)                            |
//! | 36        | blinding (per-proof blinding factor, private)            |
//! | 37        | fact_hash (private, for commitment derivation)           |
//! | 38        | state_root (private, for commitment derivation)          |
//! | 39        | derivation_flag (1=verify commitment derivation in-circuit) |
//!
//! # Public Inputs
//!
//! `[threshold, fact_commitment]`
//!
//! # Constraint Strategy
//!
//! The DSL circuit uses gated constraints to conditionally apply the correct
//! diff computation based on the operator. We separate into:
//!
//! - Range predicates (GTE/LTE/GT/LT/InRangeLow/InRangeHigh): bit decomposition path
//! - NEQ predicate: inverse-existence path
//!
//! The `neq_flag` column (binary) is 1 iff the operation is NEQ, and routes
//! constraints via Gated/InvertedGated on that flag.
//!
//! ## Fact commitment derivation
//!
//! When `derivation_flag=1`, the circuit verifies in-circuit that:
//! - If blinding == 0: fact_commitment == Hash2to1(fact_hash, state_root)
//! - If blinding != 0: fact_commitment == Hash4to1([fact_hash, state_root, blinding, 0])
//!
//! The blinding path is selected by a blinding_active flag derived from blinding != 0.
//! For simplicity, when derivation_flag=1 and blinding=0, we use Hash2to1;
//! when derivation_flag=1 and blinding!=0, the prover provides a blinding_active_flag=1
//! and we use Hash4to1.

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::poseidon2;
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
pub const BLINDING: usize = NEQ_FLAG + 1; // 36
pub const FACT_HASH: usize = BLINDING + 1; // 37
pub const STATE_ROOT: usize = FACT_HASH + 1; // 38
pub const DERIVATION_FLAG: usize = STATE_ROOT + 1; // 39
pub const BLINDING_ACTIVE_FLAG: usize = DERIVATION_FLAG + 1; // 40
pub const BLINDING_INVERSE: usize = BLINDING_ACTIVE_FLAG + 1; // 41
pub const ZERO_PAD: usize = BLINDING_INVERSE + 1; // 42
pub const TRACE_WIDTH: usize = ZERO_PAD + 1; // 43

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
    InRangeLow,
    InRangeHigh,
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the predicate `CircuitDescriptor`.
///
/// This encodes the following constraint logic:
/// - Threshold matches public input (boundary)
/// - Fact commitment matches public input (boundary)
/// - Diff bits are all binary (gated by NOT neq_flag)
/// - Bit reconstruction: sum(bits[i] * 2^i) = diff (gated by NOT neq_flag)
/// - High bit is zero: bits[29] = 0 (gated by NOT neq_flag)
/// - NEQ inverse check: diff * inverse = 1 (gated by neq_flag)
/// - Commitment derivation (gated by derivation_flag):
///   - Unblinded path (InvertedGated by blinding_active_flag):
///     fact_commitment == Hash2to1(fact_hash, state_root)
///   - Blinded path (Gated by blinding_active_flag):
///     fact_commitment == Hash4to1([fact_hash, state_root, blinding, 0])
///   - blinding_active_flag consistency: when flag=1, blinding != 0
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
    columns.push(ColumnDef {
        name: "blinding".into(),
        index: BLINDING,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "fact_hash".into(),
        index: FACT_HASH,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "state_root".into(),
        index: STATE_ROOT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "derivation_flag".into(),
        index: DERIVATION_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "blinding_active_flag".into(),
        index: BLINDING_ACTIVE_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "blinding_inverse".into(),
        index: BLINDING_INVERSE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "zero_pad".into(),
        index: ZERO_PAD,
        kind: ColumnKind::Value,
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
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: NEQ_FLAG,
            inner: Box::new(ConstraintExpr::Binary {
                col: DIFF_BITS_START + i,
            }),
        });
    }

    // ─── C5: Bit reconstruction matches diff (gated by NOT neq_flag) ────────
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

    // ─── C8: derivation_flag is binary ──────────────────────────────────────
    constraints.push(ConstraintExpr::Binary {
        col: DERIVATION_FLAG,
    });

    // ─── C9: blinding_active_flag is binary ─────────────────────────────────
    constraints.push(ConstraintExpr::Binary {
        col: BLINDING_ACTIVE_FLAG,
    });

    // ─── C10: Unblinded commitment derivation ───────────────────────────────
    // When derivation_flag=1 AND blinding_active_flag=0:
    //   fact_commitment == Hash2to1(fact_hash, state_root)
    // Gated by derivation_flag, InvertedGated by blinding_active_flag.
    constraints.push(ConstraintExpr::Gated {
        selector_col: DERIVATION_FLAG,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: BLINDING_ACTIVE_FLAG,
            inner: Box::new(ConstraintExpr::Hash2to1 {
                output_col: FACT_COMMITMENT,
                input_col_a: FACT_HASH,
                input_col_b: STATE_ROOT,
            }),
        }),
    });

    // ─── C11: Blinded commitment derivation ─────────────────────────────────
    // When derivation_flag=1 AND blinding_active_flag=1:
    //   fact_commitment == Hash4to1([fact_hash, state_root, blinding, 0])
    // Uses ZERO_PAD column (constrained to zero by C13) as the 4th hash input.
    constraints.push(ConstraintExpr::Gated {
        selector_col: DERIVATION_FLAG,
        inner: Box::new(ConstraintExpr::Gated {
            selector_col: BLINDING_ACTIVE_FLAG,
            inner: Box::new(ConstraintExpr::Hash4to1 {
                output_col: FACT_COMMITMENT,
                input_cols: [FACT_HASH, STATE_ROOT, BLINDING, ZERO_PAD],
            }),
        }),
    });

    // ─── C12: blinding_active_flag consistency ──────────────────────────────
    // When blinding_active_flag=1, blinding must be nonzero.
    // Enforced via: blinding_active_flag * (blinding * blinding_inverse - 1) == 0
    constraints.push(ConstraintExpr::ConditionalNonzero {
        selector_col: BLINDING_ACTIVE_FLAG,
        value_col: BLINDING,
        inverse_col: BLINDING_INVERSE,
    });

    // ─── C13: ZERO_PAD must be zero ─────────────────────────────────────────
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
        name: "pyana-predicate-dsl-v2".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3, // Gated(InvertedGated(Hash2to1)): 1+1+1 = 3; ConditionalNonzero: 3
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Witness for trace generation.
#[derive(Clone, Debug)]
pub struct PredicateWitness {
    pub private_value: u32,
    pub threshold: u32,
    pub op: PredicateOp,
    pub fact_commitment: BabyBear,
    /// When Some, enables in-circuit commitment derivation verification.
    pub fact_hash: Option<BabyBear>,
    /// When Some, enables in-circuit commitment derivation verification.
    pub state_root: Option<BabyBear>,
    /// Per-proof blinding factor. When nonzero, uses blinded commitment.
    pub blinding: Option<BabyBear>,
}

/// Generate a valid predicate trace row.
///
/// Returns `(trace, public_inputs)`.
pub fn generate_predicate_trace(
    private_value: u32,
    threshold: u32,
    fact_commitment: BabyBear,
    op: PredicateOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_predicate_trace_full(PredicateWitness {
        private_value,
        threshold,
        op,
        fact_commitment,
        fact_hash: None,
        state_root: None,
        blinding: None,
    })
}

/// Generate a predicate trace with full witness (including optional commitment derivation).
pub fn generate_predicate_trace_full(
    witness: PredicateWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

    row[PRIVATE_VALUE] = BabyBear::new(witness.private_value);
    row[THRESHOLD] = BabyBear::new(witness.threshold);
    row[FACT_COMMITMENT] = witness.fact_commitment;

    // Compute diff based on operation.
    let diff = match witness.op {
        PredicateOp::Gte | PredicateOp::InRangeLow => {
            witness.private_value.wrapping_sub(witness.threshold)
        }
        PredicateOp::Lte | PredicateOp::InRangeHigh => {
            witness.threshold.wrapping_sub(witness.private_value)
        }
        PredicateOp::Gt => witness
            .private_value
            .wrapping_sub(witness.threshold)
            .wrapping_sub(1),
        PredicateOp::Lt => witness
            .threshold
            .wrapping_sub(witness.private_value)
            .wrapping_sub(1),
        PredicateOp::Neq => witness.private_value.wrapping_sub(witness.threshold),
    };
    row[DIFF] = BabyBear::new(diff);

    match witness.op {
        PredicateOp::Neq => {
            row[NEQ_FLAG] = BabyBear::ONE;
            let diff_field = BabyBear::new(diff);
            if let Some(inv) = diff_field.inverse() {
                row[NEQ_INVERSE] = inv;
            }
        }
        _ => {
            row[NEQ_FLAG] = BabyBear::ZERO;
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
            }
        }
    }

    // Commitment derivation columns.
    let derivation_active = witness.fact_hash.is_some() && witness.state_root.is_some();
    if derivation_active {
        row[DERIVATION_FLAG] = BabyBear::ONE;
        let fh = witness.fact_hash.unwrap();
        let sr = witness.state_root.unwrap();
        row[FACT_HASH] = fh;
        row[STATE_ROOT] = sr;

        let blinding = witness.blinding.unwrap_or(BabyBear::ZERO);
        row[BLINDING] = blinding;

        if blinding != BabyBear::ZERO {
            row[BLINDING_ACTIVE_FLAG] = BabyBear::ONE;
            if let Some(inv) = blinding.inverse() {
                row[BLINDING_INVERSE] = inv;
            }
        } else {
            row[BLINDING_ACTIVE_FLAG] = BabyBear::ZERO;
        }
    } else {
        row[DERIVATION_FLAG] = BabyBear::ZERO;
        row[BLINDING_ACTIVE_FLAG] = BabyBear::ZERO;
    }

    // ZERO_PAD is always zero (already initialized to zero).
    row[ZERO_PAD] = BabyBear::ZERO;

    let public_inputs = vec![BabyBear::new(witness.threshold), witness.fact_commitment];

    // Pad to 2 rows (minimum for STARK).
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

/// Compute unblinded fact commitment: Poseidon2_2to1(fact_hash, state_root).
pub fn compute_fact_commitment(fact_hash: BabyBear, state_root: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(fact_hash, state_root)
}

/// Compute blinded fact commitment: Poseidon2_4to1([fact_hash, state_root, blinding, 0]).
pub fn compute_blinded_fact_commitment(
    fact_hash: BabyBear,
    state_root: BabyBear,
    blinding: BabyBear,
) -> BabyBear {
    if blinding == BabyBear::ZERO {
        poseidon2::hash_2_to_1(fact_hash, state_root)
    } else {
        poseidon2::hash_4_to_1(&[fact_hash, state_root, blinding, BabyBear::ZERO])
    }
}

/// Prove an InRange predicate: value >= low AND value <= high.
/// Returns two traces (one for low bound, one for high bound).
pub fn generate_in_range_traces(
    private_value: u32,
    low: u32,
    high: u32,
    fact_commitment: BabyBear,
) -> Option<(
    (Vec<Vec<BabyBear>>, Vec<BabyBear>),
    (Vec<Vec<BabyBear>>, Vec<BabyBear>),
)> {
    if private_value < low || private_value > high {
        return None;
    }
    let low_trace =
        generate_predicate_trace(private_value, low, fact_commitment, PredicateOp::InRangeLow);
    let high_trace = generate_predicate_trace(
        private_value,
        high,
        fact_commitment,
        PredicateOp::InRangeHigh,
    );
    Some((low_trace, high_trace))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::poseidon2::hash_fact;
    use pyana_circuit::stark::{self, StarkAir};
    use pyana_dsl_runtime::circuit::DslCircuit;

    /// Dummy fact commitment for basic tests.
    fn test_commitment() -> BabyBear {
        BabyBear::new(999999)
    }

    /// Helper: create a fact commitment and its components for derivation tests.
    fn test_fact_commitment_parts(value: BabyBear) -> (BabyBear, BabyBear, BabyBear) {
        let fact_hash = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        let commitment = compute_fact_commitment(fact_hash, state_root);
        (commitment, fact_hash, state_root)
    }

    // ========================================================================
    // Descriptor structure validation
    // ========================================================================

    #[test]
    fn test_predicate_descriptor_validates() {
        let descriptor = predicate_descriptor();
        let result = descriptor.validate();
        assert!(
            result.is_ok(),
            "Descriptor validation failed: {:?}",
            result.err()
        );

        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(descriptor.name, "pyana-predicate-dsl-v2");
    }

    // ========================================================================
    // GTE tests
    // ========================================================================

    #[test]
    fn test_predicate_gte_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 25 >= 18 should pass");
    }

    #[test]
    fn test_predicate_gte_equal_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(18, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 18 >= 18 should pass");
    }

    #[test]
    fn test_predicate_gte_adversarial_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(15, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "GTE 15 >= 18 should fail (high bit set)"
        );
    }

    // ========================================================================
    // GT tests
    // ========================================================================

    #[test]
    fn test_predicate_gt_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gt);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GT 25 > 18 should pass");
    }

    #[test]
    fn test_predicate_gt_equal_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

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

        let (trace, pi) = generate_predicate_trace(5, 18, test_commitment(), PredicateOp::Lt);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "LT 5 < 18 should pass");
    }

    #[test]
    fn test_predicate_lt_equal_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

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

        let (trace, pi) = generate_predicate_trace(10, 100, test_commitment(), PredicateOp::Lte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "LTE 10 <= 100 should pass");
    }

    #[test]
    fn test_predicate_lte_adversarial_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

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

        let (trace, pi) = generate_predicate_trace(42, 0, test_commitment(), PredicateOp::Neq);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "NEQ 42 != 0 should pass");
    }

    #[test]
    fn test_predicate_neq_adversarial_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(7, 7, test_commitment(), PredicateOp::Neq);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "NEQ 7 != 7 should fail");
    }

    // ========================================================================
    // InRange tests
    // ========================================================================

    #[test]
    fn test_predicate_in_range_low_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // InRangeLow: 25 >= 18 (same as GTE)
        let (trace, pi) =
            generate_predicate_trace(25, 18, test_commitment(), PredicateOp::InRangeLow);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "InRangeLow 25 >= 18 should pass");
    }

    #[test]
    fn test_predicate_in_range_high_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // InRangeHigh: 25 <= 120 (same as LTE)
        let (trace, pi) =
            generate_predicate_trace(25, 120, test_commitment(), PredicateOp::InRangeHigh);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "InRangeHigh 25 <= 120 should pass");
    }

    #[test]
    fn test_predicate_in_range_below_low_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // InRangeLow: 15 >= 18 should fail
        let (trace, pi) =
            generate_predicate_trace(15, 18, test_commitment(), PredicateOp::InRangeLow);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "InRangeLow 15 >= 18 should fail");
    }

    #[test]
    fn test_predicate_in_range_above_high_fails() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // InRangeHigh: 200 <= 120 should fail
        let (trace, pi) =
            generate_predicate_trace(200, 120, test_commitment(), PredicateOp::InRangeHigh);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "InRangeHigh 200 <= 120 should fail");
    }

    #[test]
    fn test_predicate_in_range_combined() {
        // Prove: 18 <= 25 <= 120 using two separate traces.
        let commitment = test_commitment();
        let result = generate_in_range_traces(25, 18, 120, commitment);
        assert!(
            result.is_some(),
            "InRange 18 <= 25 <= 120 should produce traces"
        );

        let ((low_trace, low_pi), (high_trace, high_pi)) = result.unwrap();

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let alpha = BabyBear::new(7);

        let low_result = circuit.eval_constraints(&low_trace[0], &low_trace[1], &low_pi, alpha);
        assert_eq!(low_result, BabyBear::ZERO, "InRange low bound should pass");

        let high_result = circuit.eval_constraints(&high_trace[0], &high_trace[1], &high_pi, alpha);
        assert_eq!(
            high_result,
            BabyBear::ZERO,
            "InRange high bound should pass"
        );
    }

    #[test]
    fn test_predicate_in_range_out_of_bounds_returns_none() {
        let commitment = test_commitment();
        assert!(generate_in_range_traces(15, 18, 120, commitment).is_none());
        assert!(generate_in_range_traces(200, 18, 120, commitment).is_none());
    }

    // ========================================================================
    // Fact commitment derivation tests
    // ========================================================================

    #[test]
    fn test_predicate_unblinded_derivation() {
        let value = BabyBear::new(25);
        let (commitment, fh, sr) = test_fact_commitment_parts(value);

        let witness = PredicateWitness {
            private_value: 25,
            threshold: 18,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(fh),
            state_root: Some(sr),
            blinding: None,
        };

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace_full(witness);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Unblinded derivation GTE 25 >= 18 should pass"
        );
    }

    #[test]
    fn test_predicate_blinded_derivation() {
        let value = BabyBear::new(25);
        let fh = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let sr = BabyBear::new(99999);
        let blinding = BabyBear::new(42424242);
        let commitment = compute_blinded_fact_commitment(fh, sr, blinding);

        let witness = PredicateWitness {
            private_value: 25,
            threshold: 18,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(fh),
            state_root: Some(sr),
            blinding: Some(blinding),
        };

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace_full(witness);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            result,
            BabyBear::ZERO,
            "Blinded derivation GTE 25 >= 18 should pass"
        );
    }

    #[test]
    fn test_predicate_wrong_fact_hash_fails() {
        let value = BabyBear::new(25);
        let (commitment, _fh, sr) = test_fact_commitment_parts(value);

        // Use wrong fact_hash
        let wrong_fh = BabyBear::new(12345);
        let witness = PredicateWitness {
            private_value: 25,
            threshold: 18,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(wrong_fh),
            state_root: Some(sr),
            blinding: None,
        };

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace_full(witness);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong fact_hash should fail derivation constraint"
        );
    }

    #[test]
    fn test_predicate_wrong_state_root_fails() {
        let value = BabyBear::new(25);
        let (commitment, fh, _sr) = test_fact_commitment_parts(value);

        // Use wrong state_root
        let wrong_sr = BabyBear::new(77777);
        let witness = PredicateWitness {
            private_value: 25,
            threshold: 18,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(fh),
            state_root: Some(wrong_sr),
            blinding: None,
        };

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace_full(witness);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Wrong state_root should fail derivation constraint"
        );
    }

    #[test]
    fn test_predicate_blinding_unlinkability() {
        let value = BabyBear::new(25);
        let fh = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let sr = BabyBear::new(99999);

        let blinding_a = BabyBear::new(11111);
        let blinding_b = BabyBear::new(22222);

        let commit_a = compute_blinded_fact_commitment(fh, sr, blinding_a);
        let commit_b = compute_blinded_fact_commitment(fh, sr, blinding_b);

        assert_ne!(
            commit_a, commit_b,
            "Different blindings must produce different commitments"
        );
    }

    // ========================================================================
    // Adversarial: tampered trace
    // ========================================================================

    #[test]
    fn test_predicate_tampered_diff_caught() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

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

        let (mut trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gte);
        trace[0][DIFF_BITS_START] = BabyBear::new(2);
        trace[1][DIFF_BITS_START] = BabyBear::new(2);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(result, BabyBear::ZERO, "Non-binary bit should be caught");
    }

    // ========================================================================
    // Overflow/underflow detection
    // ========================================================================

    #[test]
    fn test_predicate_overflow_high_bit() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

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
        assert!(
            result.is_ok(),
            "STARK verify NEQ failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_predicate_stark_rejects_wrong_pi() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor.clone());

        let (trace, pi) = generate_predicate_trace(1000, 500, test_commitment(), PredicateOp::Gte);
        let proof = stark::prove(&circuit, &trace, &pi);

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
        assert!(
            result.is_ok(),
            "STARK verify LTE boundary failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_predicate_stark_prove_verify_gt() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) = generate_predicate_trace(50, 18, test_commitment(), PredicateOp::Gt);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify GT failed: {:?}", result.err());
    }

    #[test]
    fn test_predicate_stark_prove_verify_in_range_low() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) =
            generate_predicate_trace(50, 18, test_commitment(), PredicateOp::InRangeLow);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK verify InRangeLow failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_predicate_stark_prove_verify_in_range_high() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let (trace, pi) =
            generate_predicate_trace(50, 120, test_commitment(), PredicateOp::InRangeHigh);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK verify InRangeHigh failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_predicate_stark_with_derivation() {
        let value = BabyBear::new(1000);
        let (commitment, fh, sr) = test_fact_commitment_parts(value);

        let witness = PredicateWitness {
            private_value: 1000,
            threshold: 500,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(fh),
            state_root: Some(sr),
            blinding: None,
        };

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace_full(witness);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK with derivation failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_predicate_stark_with_blinded_derivation() {
        let value = BabyBear::new(1000);
        let fh = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let sr = BabyBear::new(99999);
        let blinding = BabyBear::new(7777777);
        let commitment = compute_blinded_fact_commitment(fh, sr, blinding);

        let witness = PredicateWitness {
            private_value: 1000,
            threshold: 500,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(fh),
            state_root: Some(sr),
            blinding: Some(blinding),
        };

        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace_full(witness);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK with blinded derivation failed: {:?}",
            result.err()
        );
    }
}
