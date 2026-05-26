//! Temporal predicate expressed as a CircuitDescriptor — complete replacement for
//! `circuit/src/temporal_predicate_air.rs`.
//!
//! Proves that a property held CONTINUOUSLY over a range of steps in the IVC chain.
//! The proof is bound to the chain state via state roots at each step and exposes
//! all relevant parameters as public inputs for verifier inspection.
//!
//! # Trace layout (per row)
//!
//! | Column | Name           | Description                                    |
//! |--------|----------------|------------------------------------------------|
//! | 0      | value          | The attribute value at this block               |
//! | 1      | threshold      | Constant threshold across all rows              |
//! | 2      | diff           | Computed difference (depends on predicate_type) |
//! | 3..32  | diff_bits[0..29] | Bit decomposition proving diff >= 0          |
//! | 33     | accumulator    | Running step counter (1, 2, ..., N)            |
//! | 34     | step_index     | Step index (0, 1, ..., N-1)                    |
//! | 35     | state_root     | The state root at this step (IVC chain binding)|
//! | 36     | acc_plus_one   | accumulator + 1 (auxiliary for transition)     |
//! | 37     | step_plus_one  | step_index + 1 (auxiliary for transition)      |
//! | 38     | diff_inv       | Inverse of diff (for Neq predicate only)       |
//! | 39     | neq_selector   | 1 when Neq predicate is active, 0 otherwise   |
//!
//! # Public Inputs
//!
//! `[threshold, num_steps, initial_state_root, final_state_root]`

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::predicate_air::PredicateType;
use dregg_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
pub const STATE_ROOT: usize = STEP_INDEX + 1; // 35
pub const ACC_PLUS_ONE: usize = STATE_ROOT + 1; // 36
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 37
pub const DIFF_INV: usize = STEP_PLUS_ONE + 1; // 38
pub const NEQ_SELECTOR: usize = DIFF_INV + 1; // 39
pub const TRACE_WIDTH: usize = NEQ_SELECTOR + 1; // 40

pub const PI_THRESHOLD: usize = 0;
pub const PI_NUM_STEPS: usize = 1;
pub const PI_INITIAL_STATE_ROOT: usize = 2;
pub const PI_FINAL_STATE_ROOT: usize = 3;
pub const PUBLIC_INPUT_COUNT: usize = 4;

// ============================================================================
// Predicate type encoding
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemporalPredicateKind {
    Gte,
    Lte,
    Gt,
    Lt,
    Neq,
    InRangeLow,
    InRangeHigh,
}

impl From<PredicateType> for TemporalPredicateKind {
    fn from(pt: PredicateType) -> Self {
        match pt {
            PredicateType::Gte => Self::Gte,
            PredicateType::Lte => Self::Lte,
            PredicateType::Gt => Self::Gt,
            PredicateType::Lt => Self::Lt,
            PredicateType::Neq => Self::Neq,
            PredicateType::InRangeLow => Self::InRangeLow,
            PredicateType::InRangeHigh => Self::InRangeHigh,
        }
    }
}

impl From<TemporalPredicateKind> for PredicateType {
    fn from(kind: TemporalPredicateKind) -> Self {
        match kind {
            TemporalPredicateKind::Gte => Self::Gte,
            TemporalPredicateKind::Lte => Self::Lte,
            TemporalPredicateKind::Gt => Self::Gt,
            TemporalPredicateKind::Lt => Self::Lt,
            TemporalPredicateKind::Neq => Self::Neq,
            TemporalPredicateKind::InRangeLow => Self::InRangeLow,
            TemporalPredicateKind::InRangeHigh => Self::InRangeHigh,
        }
    }
}

// ============================================================================
// Descriptor construction
// ============================================================================

pub fn temporal_predicate_descriptor(predicate_kind: TemporalPredicateKind) -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);
    let is_neq = predicate_kind == TemporalPredicateKind::Neq;

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef {
        name: "value".into(),
        index: VALUE,
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
        name: "accumulator".into(),
        index: ACCUMULATOR,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "step_index".into(),
        index: STEP_INDEX,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "state_root".into(),
        index: STATE_ROOT,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "acc_plus_one".into(),
        index: ACC_PLUS_ONE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "step_plus_one".into(),
        index: STEP_PLUS_ONE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "diff_inv".into(),
        index: DIFF_INV,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "neq_selector".into(),
        index: NEQ_SELECTOR,
        kind: ColumnKind::Selector,
    });

    let mut constraints = Vec::new();

    // C1: diff computation
    match predicate_kind {
        TemporalPredicateKind::Gte
        | TemporalPredicateKind::InRangeLow
        | TemporalPredicateKind::Neq => {
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![DIFF],
                    },
                    PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![VALUE],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![THRESHOLD],
                    },
                ],
            });
        }
        TemporalPredicateKind::Lte | TemporalPredicateKind::InRangeHigh => {
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![DIFF],
                    },
                    PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![THRESHOLD],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![VALUE],
                    },
                ],
            });
        }
        TemporalPredicateKind::Gt => {
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![DIFF],
                    },
                    PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![VALUE],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![THRESHOLD],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![],
                    },
                ],
            });
        }
        TemporalPredicateKind::Lt => {
            constraints.push(ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![DIFF],
                    },
                    PolyTerm {
                        coeff: neg_one,
                        col_indices: vec![THRESHOLD],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![VALUE],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![],
                    },
                ],
            });
        }
    }

    // C2: diff_bits binary
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: DIFF_BITS_START + i,
        });
    }

    // C3: bit reconstruction (gated off for Neq)
    {
        let mut terms = Vec::with_capacity(NUM_DIFF_BITS + 1);
        let mut pow2 = 1u32;
        for i in 0..NUM_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(pow2),
                col_indices: vec![DIFF_BITS_START + i],
            });
            pow2 = pow2.wrapping_mul(2);
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![DIFF],
        });
        if is_neq {
            constraints.push(ConstraintExpr::InvertedGated {
                selector_col: NEQ_SELECTOR,
                inner: Box::new(ConstraintExpr::Polynomial { terms }),
            });
        } else {
            constraints.push(ConstraintExpr::Polynomial { terms });
        }
    }

    // C4: high bit zero (gated off for Neq)
    if is_neq {
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: NEQ_SELECTOR,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
                }],
            }),
        });
    } else {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
            }],
        });
    }

    // C5: acc_plus_one = accumulator + 1
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![ACC_PLUS_ONE],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![ACCUMULATOR],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // C6: step_plus_one = step_index + 1
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![STEP_PLUS_ONE],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![STEP_INDEX],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // C7: threshold = pi[0]
    constraints.push(ConstraintExpr::PiBinding {
        col: THRESHOLD,
        pi_index: PI_THRESHOLD,
    });

    // C8: Neq nonzero proof
    if is_neq {
        constraints.push(ConstraintExpr::ConditionalNonzero {
            selector_col: NEQ_SELECTOR,
            value_col: DIFF,
            inverse_col: DIFF_INV,
        });
    }

    // C9: neq_selector binary
    constraints.push(ConstraintExpr::Binary { col: NEQ_SELECTOR });

    // C10/C11: transitions
    constraints.push(ConstraintExpr::Transition {
        next_col: ACCUMULATOR,
        local_col: ACC_PLUS_ONE,
    });
    constraints.push(ConstraintExpr::Transition {
        next_col: STEP_INDEX,
        local_col: STEP_PLUS_ONE,
    });

    let boundaries = vec![
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: ACCUMULATOR,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: STEP_INDEX,
            value: BabyBear::ZERO,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: STATE_ROOT,
            pi_index: PI_INITIAL_STATE_ROOT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: ACCUMULATOR,
            pi_index: PI_NUM_STEPS,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: STATE_ROOT,
            pi_index: PI_FINAL_STATE_ROOT,
        },
    ];

    let max_degree = if is_neq { 3 } else { 2 };

    CircuitDescriptor {
        name: "dregg-temporal-predicate-dsl-v2".into(),
        trace_width: TRACE_WIDTH,
        max_degree,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

// ============================================================================
// Trace generation
// ============================================================================

pub fn generate_temporal_trace(
    values: &[u32],
    state_roots: &[BabyBear],
    threshold: u32,
    predicate_kind: TemporalPredicateKind,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = values.len();
    assert!(num_steps >= 1, "need at least 1 step");
    assert_eq!(
        values.len(),
        state_roots.len(),
        "values and state_roots must have same length"
    );

    let is_neq = predicate_kind == TemporalPredicateKind::Neq;
    let padded_len = num_steps.next_power_of_two().max(2);
    let mut trace = Vec::with_capacity(padded_len);

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        let val = if step < num_steps {
            values[step]
        } else {
            values[num_steps - 1]
        };
        let sr = if step < num_steps {
            state_roots[step]
        } else {
            *state_roots.last().unwrap()
        };

        let val_field = BabyBear::new(val);
        let thresh_field = BabyBear::new(threshold);
        row[VALUE] = val_field;
        row[THRESHOLD] = thresh_field;
        row[STATE_ROOT] = sr;

        let diff_field = match predicate_kind {
            TemporalPredicateKind::Gte
            | TemporalPredicateKind::InRangeLow
            | TemporalPredicateKind::Neq => val_field - thresh_field,
            TemporalPredicateKind::Lte | TemporalPredicateKind::InRangeHigh => {
                thresh_field - val_field
            }
            TemporalPredicateKind::Gt => val_field - thresh_field - BabyBear::ONE,
            TemporalPredicateKind::Lt => thresh_field - val_field - BabyBear::ONE,
        };
        row[DIFF] = diff_field;

        if !is_neq {
            let dv = diff_field.as_u32();
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((dv >> i) & 1);
            }
        }

        if is_neq {
            row[NEQ_SELECTOR] = BabyBear::ONE;
            if let Some(inv) = diff_field.inverse() {
                row[DIFF_INV] = inv;
            }
        }

        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);
        trace.push(row);
    }

    let public_inputs = vec![
        BabyBear::new(threshold),
        BabyBear::new(padded_len as u32),
        state_roots[0],
        *state_roots.last().unwrap(),
    ];
    (trace, public_inputs)
}

// ============================================================================
// Intent integration
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemporalRequirement {
    pub attribute: String,
    pub predicate_kind: TemporalPredicateKind,
    pub threshold: u32,
    pub min_duration_steps: u32,
}

#[derive(Clone, Debug)]
pub struct TemporalProofClaim {
    pub predicate_kind: TemporalPredicateKind,
    pub threshold: u32,
    pub num_steps: u32,
    pub padded_len: u32,
    pub initial_state_root: BabyBear,
    pub final_state_root: BabyBear,
}

impl TemporalRequirement {
    pub fn is_satisfied_by(&self, claim: &TemporalProofClaim) -> bool {
        claim.predicate_kind == self.predicate_kind
            && claim.threshold >= self.threshold
            && claim.num_steps >= self.min_duration_steps
    }
}

// ============================================================================
// Prove / Verify
// ============================================================================

pub fn is_satisfiable(values: &[u32], threshold: u32, pk: TemporalPredicateKind) -> bool {
    if values.is_empty() {
        return false;
    }
    values.iter().all(|&v| match pk {
        TemporalPredicateKind::Gte | TemporalPredicateKind::InRangeLow => v >= threshold,
        TemporalPredicateKind::Lte | TemporalPredicateKind::InRangeHigh => v <= threshold,
        TemporalPredicateKind::Gt => v > threshold,
        TemporalPredicateKind::Lt => v < threshold,
        TemporalPredicateKind::Neq => v != threshold,
    })
}

pub fn prove_temporal(
    values: &[u32],
    state_roots: &[BabyBear],
    threshold: u32,
    pk: TemporalPredicateKind,
) -> Option<TemporalProofClaim> {
    use dregg_circuit::stark;
    use dregg_dsl_runtime::circuit::DslCircuit;
    if values.len() != state_roots.len() {
        return None;
    }
    if !is_satisfiable(values, threshold, pk) {
        return None;
    }
    let num_steps = values.len() as u32;
    let circuit = DslCircuit::new(temporal_predicate_descriptor(pk));
    let (trace, pi) = generate_temporal_trace(values, state_roots, threshold, pk);
    let padded_len = trace.len() as u32;
    let proof = stark::prove(&circuit, &trace, &pi);
    if stark::verify(&circuit, &proof, &pi).is_err() {
        return None;
    }
    Some(TemporalProofClaim {
        predicate_kind: pk,
        threshold,
        num_steps,
        padded_len,
        initial_state_root: state_roots[0],
        final_state_root: *state_roots.last().unwrap(),
    })
}

pub fn verify_temporal(
    claim: &TemporalProofClaim,
    threshold: u32,
    num_steps: u32,
    initial_root: BabyBear,
    final_root: BabyBear,
) -> bool {
    claim.threshold == threshold
        && claim.num_steps == num_steps
        && claim.initial_state_root == initial_root
        && claim.final_state_root == final_root
        && claim.padded_len >= claim.num_steps
        && claim.padded_len.is_power_of_two()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::stark::{self, StarkAir};
    use dregg_dsl_runtime::circuit::DslCircuit;

    fn test_state_roots(n: usize) -> Vec<BabyBear> {
        (0..n).map(|i| BabyBear::new(1000 + i as u32)).collect()
    }

    #[test]
    fn test_temporal_dsl_valid_trace_gte() {
        let pk = TemporalPredicateKind::Gte;
        let d = temporal_predicate_descriptor(pk);
        assert!(d.validate().is_ok());
        let c = DslCircuit::new(d);
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50, pk);
        assert_eq!(trace.len(), 4);
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            assert_eq!(
                c.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha),
                BabyBear::ZERO,
                "row {i}"
            );
        }
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_temporal_dsl_invalid_value_below_threshold() {
        let pk = TemporalPredicateKind::Gte;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 30, 100], &sr, 50, pk);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_temporal_dsl_invalid_accumulator_gap() {
        let pk = TemporalPredicateKind::Gte;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (mut trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50, pk);
        trace[2][ACCUMULATOR] = BabyBear::new(4);
        trace[2][ACC_PLUS_ONE] = BabyBear::new(5);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
        assert_eq!(
            c.eval_constraints(&trace[0], &trace[1], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_temporal_descriptor_validation() {
        let d = temporal_predicate_descriptor(TemporalPredicateKind::Gte);
        assert!(d.validate().is_ok());
        assert_eq!(d.trace_width, TRACE_WIDTH);
        assert_eq!(d.public_input_count, 4);
        assert_eq!(d.name, "dregg-temporal-predicate-dsl-v2");
    }

    #[test]
    fn test_temporal_has_transition_constraints() {
        let d = temporal_predicate_descriptor(TemporalPredicateKind::Gte);
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, ConstraintExpr::Transition { .. }))
                .count(),
            2
        );
    }

    #[test]
    fn test_temporal_dsl_invalid_step_index_gap() {
        let pk = TemporalPredicateKind::Gte;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (mut trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50, pk);
        trace[2][STEP_INDEX] = BabyBear::new(5);
        trace[2][STEP_PLUS_ONE] = BabyBear::new(6);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_temporal_dsl_stark_rejects_wrong_num_steps() {
        let pk = TemporalPredicateKind::Gte;
        let d = temporal_predicate_descriptor(pk);
        let c = DslCircuit::new(d.clone());
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50, pk);
        let proof = stark::prove(&c, &trace, &pi);
        let wrong = vec![BabyBear::new(50), BabyBear::new(8), sr[0], sr[2]];
        assert!(stark::verify(&DslCircuit::new(d), &proof, &wrong).is_err());
    }

    #[test]
    fn test_temporal_dsl_state_root_in_public_inputs() {
        let pk = TemporalPredicateKind::Gte;
        let d = temporal_predicate_descriptor(pk);
        let c = DslCircuit::new(d.clone());
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50, pk);
        assert_eq!(pi[PI_INITIAL_STATE_ROOT], sr[0]);
        assert_eq!(pi[PI_FINAL_STATE_ROOT], sr[2]);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(
            stark::verify(
                &DslCircuit::new(d.clone()),
                &proof,
                &vec![pi[0], pi[1], BabyBear::new(99999), pi[3]]
            )
            .is_err()
        );
        assert!(
            stark::verify(
                &DslCircuit::new(d),
                &proof,
                &vec![pi[0], pi[1], pi[2], BabyBear::new(99999)]
            )
            .is_err()
        );
    }

    #[test]
    fn test_temporal_dsl_threshold_in_public_inputs() {
        let pk = TemporalPredicateKind::Gte;
        let d = temporal_predicate_descriptor(pk);
        let c = DslCircuit::new(d.clone());
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50, pk);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(
            stark::verify(
                &DslCircuit::new(d),
                &proof,
                &vec![BabyBear::new(99), pi[1], pi[2], pi[3]]
            )
            .is_err()
        );
    }

    #[test]
    fn test_temporal_dsl_lte_valid() {
        let pk = TemporalPredicateKind::Lte;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(4);
        let (trace, pi) = generate_temporal_trace(&[50, 30, 100, 100], &sr, 100, pk);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_temporal_dsl_lte_violation_detected() {
        let pk = TemporalPredicateKind::Lte;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[50, 101, 80], &sr, 100, pk);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_temporal_dsl_gt_edge_case() {
        let pk = TemporalPredicateKind::Gt;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(2);
        let (trace, pi) = generate_temporal_trace(&[100, 100], &sr, 100, pk);
        assert_ne!(
            c.eval_constraints(&trace[0], &trace[1], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_temporal_dsl_gt_valid() {
        let pk = TemporalPredicateKind::Gt;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[101, 200, 150], &sr, 100, pk);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_temporal_dsl_lt_valid() {
        let pk = TemporalPredicateKind::Lt;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[50, 30, 99], &sr, 100, pk);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_temporal_dsl_lt_edge_case() {
        let pk = TemporalPredicateKind::Lt;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(2);
        let (trace, pi) = generate_temporal_trace(&[100, 50], &sr, 100, pk);
        assert_ne!(
            c.eval_constraints(&trace[0], &trace[1], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_temporal_dsl_neq_valid() {
        let pk = TemporalPredicateKind::Neq;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[99, 101, 200], &sr, 100, pk);
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            assert_eq!(
                c.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha),
                BabyBear::ZERO,
                "row {i}"
            );
        }
    }

    #[test]
    fn test_temporal_dsl_neq_violation() {
        let pk = TemporalPredicateKind::Neq;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[99, 100, 200], &sr, 100, pk);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_prove_verify_temporal_gte() {
        let sr = test_state_roots(4);
        let claim =
            prove_temporal(&[200, 150, 300, 100], &sr, 100, TemporalPredicateKind::Gte).unwrap();
        assert_eq!(claim.num_steps, 4);
        assert!(verify_temporal(&claim, 100, 4, sr[0], sr[3]));
    }

    #[test]
    fn test_prove_temporal_violation_returns_none() {
        let sr = test_state_roots(3);
        assert!(prove_temporal(&[200, 50, 300], &sr, 100, TemporalPredicateKind::Gte).is_none());
    }

    #[test]
    fn test_verify_temporal_wrong_threshold_rejected() {
        let sr = test_state_roots(3);
        let claim = prove_temporal(&[200, 150, 300], &sr, 100, TemporalPredicateKind::Gte).unwrap();
        assert!(!verify_temporal(&claim, 50, 3, sr[0], sr[2]));
    }

    #[test]
    fn test_verify_temporal_wrong_state_root_rejected() {
        let sr = test_state_roots(3);
        let claim = prove_temporal(&[200, 150, 300], &sr, 100, TemporalPredicateKind::Gte).unwrap();
        assert!(!verify_temporal(
            &claim,
            100,
            3,
            BabyBear::new(99999),
            sr[2]
        ));
        assert!(!verify_temporal(
            &claim,
            100,
            3,
            sr[0],
            BabyBear::new(99999)
        ));
    }

    #[test]
    fn test_temporal_requirement_satisfied() {
        let sr = test_state_roots(30);
        let claim = prove_temporal(&vec![200; 30], &sr, 100, TemporalPredicateKind::Gte).unwrap();
        let req = TemporalRequirement {
            attribute: "balance".into(),
            predicate_kind: TemporalPredicateKind::Gte,
            threshold: 100,
            min_duration_steps: 30,
        };
        assert!(req.is_satisfied_by(&claim));
    }

    #[test]
    fn test_temporal_requirement_insufficient_duration() {
        let sr = test_state_roots(10);
        let claim = prove_temporal(&vec![200; 10], &sr, 100, TemporalPredicateKind::Gte).unwrap();
        let req = TemporalRequirement {
            attribute: "balance".into(),
            predicate_kind: TemporalPredicateKind::Gte,
            threshold: 100,
            min_duration_steps: 30,
        };
        assert!(!req.is_satisfied_by(&claim));
    }

    #[test]
    fn test_temporal_requirement_wrong_predicate_type() {
        let sr = test_state_roots(10);
        let claim = prove_temporal(&vec![200; 10], &sr, 100, TemporalPredicateKind::Gte).unwrap();
        let req = TemporalRequirement {
            attribute: "balance".into(),
            predicate_kind: TemporalPredicateKind::Gt,
            threshold: 100,
            min_duration_steps: 5,
        };
        assert!(!req.is_satisfied_by(&claim));
    }

    #[test]
    fn test_temporal_dsl_fabricated_duration_rejected() {
        let pk = TemporalPredicateKind::Gte;
        let d = temporal_predicate_descriptor(pk);
        let c = DslCircuit::new(d.clone());
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[200, 150, 300], &sr, 100, pk);
        let proof = stark::prove(&c, &trace, &pi);
        let fake = vec![BabyBear::new(100), BabyBear::new(10), sr[0], sr[2]];
        assert!(stark::verify(&DslCircuit::new(d), &proof, &fake).is_err());
    }

    #[test]
    fn test_temporal_dsl_has_4_public_inputs() {
        assert_eq!(
            temporal_predicate_descriptor(TemporalPredicateKind::Gte).public_input_count,
            4
        );
    }

    #[test]
    fn test_temporal_dsl_boundary_count() {
        assert_eq!(
            temporal_predicate_descriptor(TemporalPredicateKind::Gte)
                .boundaries
                .len(),
            5
        );
    }

    #[test]
    fn test_temporal_all_predicate_kinds_validate() {
        for kind in [
            TemporalPredicateKind::Gte,
            TemporalPredicateKind::Lte,
            TemporalPredicateKind::Gt,
            TemporalPredicateKind::Lt,
            TemporalPredicateKind::Neq,
            TemporalPredicateKind::InRangeLow,
            TemporalPredicateKind::InRangeHigh,
        ] {
            assert!(
                temporal_predicate_descriptor(kind).validate().is_ok(),
                "{:?}",
                kind
            );
        }
    }

    #[test]
    fn test_temporal_dsl_in_range_low() {
        let pk = TemporalPredicateKind::InRangeLow;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 200, 150], &sr, 100, pk);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_temporal_dsl_in_range_high() {
        let pk = TemporalPredicateKind::InRangeHigh;
        let c = DslCircuit::new(temporal_predicate_descriptor(pk));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[50, 100, 80], &sr, 100, pk);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_temporal_mismatched_lengths() {
        assert!(
            prove_temporal(
                &[200, 150],
                &test_state_roots(3),
                100,
                TemporalPredicateKind::Gte
            )
            .is_none()
        );
    }

    #[test]
    fn test_temporal_empty_returns_none() {
        assert!(prove_temporal(&[], &[], 100, TemporalPredicateKind::Gte).is_none());
    }
}
