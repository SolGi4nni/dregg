//! DSL-native committed-threshold predicate proving and verification.
//!
//! This module provides a DSL `CircuitDescriptor` equivalent of the hand-written
//! `CommittedThresholdAir` from `circuit/src/committed_threshold.rs`.
//!
//! # Constraints
//!
//! 1. `threshold_commitment == pi[0]` (boundary)
//! 2. `fact_commitment == pi[1]` (boundary)
//! 3. `poseidon2_result == hash_2_to_1(threshold, blinding)` (Hash2to1 constraint)
//! 4. `poseidon2_result == threshold_commitment` (equality)
//! 5. `diff == private_value - threshold` (polynomial)
//! 6. Bit decomposition: `sum(diff_bit[i] * 2^i) == diff` (polynomial)
//! 7. Each diff_bit is binary (Binary constraint)
//! 8. High bit (bit 29) is zero (boundary: fixed value 0)
//!
//! # Public Inputs
//!
//! `[threshold_commitment, fact_commitment]`

use crate::committed_threshold::{
    COMMITTED_DIFF_BITS, COMMITTED_THRESHOLD_AIR_WIDTH, CommittedThresholdWitness, col,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2;

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Re-exports
// ============================================================================

pub use crate::committed_threshold::{
    COMMITTED_DIFF_BITS as DSL_COMMITTED_DIFF_BITS,
    COMMITTED_THRESHOLD_AIR_WIDTH as DSL_COMMITTED_THRESHOLD_WIDTH,
    CommittedThresholdWitness as CommittedThresholdWitnessType, compute_threshold_commitment,
    generate_blinding,
};

// ============================================================================
// Circuit descriptor
// ============================================================================

// ============================================================================
// Trace generation
// ============================================================================

/// Generate the DSL trace from a `CommittedThresholdWitness`.
///
/// Returns (trace, public_inputs) where trace is padded to power-of-2 length.
pub fn generate_committed_threshold_trace(
    witness: &CommittedThresholdWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; COMMITTED_THRESHOLD_AIR_WIDTH];

    // Fill witness columns
    row[col::PRIVATE_VALUE] = witness.private_value;
    row[col::THRESHOLD] = witness.threshold;
    row[col::BLINDING] = witness.blinding;

    // Compute diff
    let diff = witness.private_value - witness.threshold;
    row[col::DIFF] = diff;

    // Bit decomposition
    let diff_val = diff.as_u32();
    for i in 0..COMMITTED_DIFF_BITS {
        let bit = (diff_val >> i) & 1;
        row[col::diff_bit(i)] = BabyBear::new(bit);
    }

    // Poseidon2 commitment
    let poseidon2_result = poseidon2::hash_2_to_1(witness.threshold, witness.blinding);
    row[col::POSEIDON2_RESULT] = poseidon2_result;

    // Public-input-matching columns
    let threshold_commitment = witness.compute_threshold_commitment();
    row[col::THRESHOLD_COMMITMENT] = threshold_commitment;
    row[col::FACT_COMMITMENT] = witness.fact_commitment;

    let public_inputs = vec![threshold_commitment, witness.fact_commitment];

    // Pad to power of 2 (min 2 rows for STARK)
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

// ============================================================================
// Production prove/verify API
// ============================================================================

// ============================================================================
// WELDED committed-threshold: value ↔ fact bound IN-CIRCUIT.
//
// The plain `committed_threshold_circuit_descriptor()` above proves `value ≥
// threshold` and binds `threshold_commitment = Poseidon2(threshold, blinding)`,
// but `fact_commitment` is ONLY PI-pinned — `private_value` (the value the range
// gadget proves about) is a FREE witness, never tied to the committed fact. A
// prover can therefore prove "value ≥ threshold" about a value they do NOT hold,
// against a `fact_commitment` naming a different real fact.
//
// The credentialed fact model (see `bridge::present::prove_predicate_for_fact`,
// `sdk::cipherclerk`): a fact's felt view is
//   `fact_hash        = hash_fact(predicate_sym, [value, term1, term2])`   (value = term0)
//   `fact_commitment  = Poseidon2(fact_hash, state_root)`
// The welded descriptor closes the hole by opening BOTH hashes IN-CIRCUIT, feeding
// the SAME `private_value` column into the fact-hash preimage that feeds the range
// gadget. Now a satisfying assignment forces `hash_fact(pred, [private_value, …])`
// to equal the real fact's `fact_hash`, so `private_value` MUST be the committed
// fact's value (Poseidon2 collision resistance), else UNSAT.
// ============================================================================

/// Column layout for the welded committed-threshold circuit. Columns `0..37`
/// are byte-identical to the plain descriptor (`crate::committed_threshold::col`);
/// `37..42` are the fact-opening witnesses.
pub mod welded_col {
    use crate::committed_threshold::{COMMITTED_DIFF_BITS, col};

    pub use col::{
        BLINDING, DIFF, DIFF_BITS_START, FACT_COMMITMENT, POSEIDON2_RESULT, PRIVATE_VALUE,
        THRESHOLD, THRESHOLD_COMMITMENT, diff_bit,
    };

    /// The fact's predicate symbol (`hash_fact`'s first/predicate slot).
    pub const PREDICATE_SYM: usize = col::POSEIDON2_RESULT + 1; // 37
    /// The fact's second term (`hash_fact` term[1]).
    pub const TERM1: usize = PREDICATE_SYM + 1; // 38
    /// The fact's third term (`hash_fact` term[2]).
    pub const TERM2: usize = TERM1 + 1; // 39
    /// The token state root the fact commitment is taken over.
    pub const STATE_ROOT: usize = TERM2 + 1; // 40
    /// The computed `hash_fact(predicate_sym, [private_value, term1, term2])`.
    pub const FACT_HASH: usize = STATE_ROOT + 1; // 41
    /// Total welded trace width.
    pub const WELDED_WIDTH: usize = FACT_HASH + 1; // 42

    /// Number of range-check bits (re-exported for callers).
    pub const WELDED_DIFF_BITS: usize = COMMITTED_DIFF_BITS;
}

/// Witness for a welded committed-threshold proof: the threshold-commitment
/// witness PLUS the credentialed fact's felt fields, so the value proven-about is
/// tied in-circuit to `fact_commitment`.
#[derive(Clone, Debug)]
pub struct CommittedThresholdFactWitness {
    /// The prover's private attribute value (== the fact's term0).
    pub private_value: BabyBear,
    /// The verifier's threshold (secret; known to prover via secure channel).
    pub threshold: BabyBear,
    /// The verifier's threshold-commitment blinding.
    pub blinding: BabyBear,
    /// The fact's predicate symbol (`hash_fact` predicate slot).
    pub predicate_sym: BabyBear,
    /// The fact's term[1].
    pub term1: BabyBear,
    /// The fact's term[2].
    pub term2: BabyBear,
    /// The token state root the fact commitment covers.
    pub state_root: BabyBear,
}

impl CommittedThresholdFactWitness {
    /// The in-circuit fact hash: `hash_fact(predicate_sym, [value, term1, term2])`.
    pub fn compute_fact_hash(&self) -> BabyBear {
        poseidon2::hash_fact(
            self.predicate_sym,
            &[self.private_value, self.term1, self.term2],
        )
    }

    /// The fact commitment: `Poseidon2(fact_hash, state_root)`.
    pub fn compute_fact_commitment(&self) -> BabyBear {
        poseidon2::hash_2_to_1(self.compute_fact_hash(), self.state_root)
    }

    /// The threshold commitment: `Poseidon2(threshold, blinding)`.
    pub fn compute_threshold_commitment(&self) -> BabyBear {
        compute_threshold_commitment(self.threshold, self.blinding)
    }

    /// Whether the predicate is satisfiable (`value ≥ threshold`).
    pub fn is_satisfiable(&self) -> bool {
        self.private_value.as_u32() >= self.threshold.as_u32()
    }
}

/// Build the welded committed-threshold `CircuitDescriptor` (value ↔ fact bound).
pub fn committed_threshold_welded_descriptor() -> CircuitDescriptor {
    use welded_col as w;
    let neg_one = BabyBear::new(BABYBEAR_P - 1);
    let mut constraints = Vec::new();

    // C1: poseidon2_result == hash_2_to_1(threshold, blinding)
    constraints.push(ConstraintExpr::Hash2to1 {
        output_col: w::POSEIDON2_RESULT,
        input_col_a: w::THRESHOLD,
        input_col_b: w::BLINDING,
    });
    // C2: poseidon2_result == threshold_commitment
    constraints.push(ConstraintExpr::Equality {
        col_a: w::POSEIDON2_RESULT,
        col_b: w::THRESHOLD_COMMITMENT,
    });
    // C3: diff == private_value - threshold
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![w::DIFF],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![w::PRIVATE_VALUE],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![w::THRESHOLD],
            },
        ],
    });
    // C4: bit recomposition
    {
        let mut terms = Vec::with_capacity(COMMITTED_DIFF_BITS + 1);
        let mut power_of_two = BabyBear::ONE;
        for i in 0..COMMITTED_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![w::diff_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![w::DIFF],
        });
        constraints.push(ConstraintExpr::Polynomial { terms });
    }
    // C5: bits binary
    for i in 0..COMMITTED_DIFF_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: w::diff_bit(i),
        });
    }

    // === THE WELD ===
    // C6: fact_hash == hash_fact(predicate_sym, [private_value, term1, term2]).
    // The SAME `private_value` column feeds both this fact-hash and the range gadget
    // (C3/C4), so the value proven-about must be the value inside the committed fact.
    constraints.push(ConstraintExpr::Hash {
        output_col: w::FACT_HASH,
        input_cols: vec![w::PREDICATE_SYM, w::PRIVATE_VALUE, w::TERM1, w::TERM2],
    });
    // C7: fact_commitment == hash_2_to_1(fact_hash, state_root). This ties the
    // PI-pinned `fact_commitment` to the just-opened `fact_hash`.
    constraints.push(ConstraintExpr::Hash2to1 {
        output_col: w::FACT_COMMITMENT,
        input_col_a: w::FACT_HASH,
        input_col_b: w::STATE_ROOT,
    });

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: w::THRESHOLD_COMMITMENT,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: w::FACT_COMMITMENT,
            pi_index: 1,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: w::diff_bit(COMMITTED_DIFF_BITS - 1),
            value: BabyBear::ZERO,
        },
    ];

    let mut columns = vec![
        ColumnDef {
            name: "private_value".into(),
            index: w::PRIVATE_VALUE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "threshold".into(),
            index: w::THRESHOLD,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "blinding".into(),
            index: w::BLINDING,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff".into(),
            index: w::DIFF,
            kind: ColumnKind::Value,
        },
    ];
    for i in 0..COMMITTED_DIFF_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: w::diff_bit(i),
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "threshold_commitment".into(),
        index: w::THRESHOLD_COMMITMENT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "fact_commitment".into(),
        index: w::FACT_COMMITMENT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "poseidon2_result".into(),
        index: w::POSEIDON2_RESULT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "predicate_sym".into(),
        index: w::PREDICATE_SYM,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "term1".into(),
        index: w::TERM1,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "term2".into(),
        index: w::TERM2,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "state_root".into(),
        index: w::STATE_ROOT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "fact_hash".into(),
        index: w::FACT_HASH,
        kind: ColumnKind::Hash,
    });

    CircuitDescriptor {
        name: "dregg-committed-threshold-welded-dsl-v1".to_string(),
        trace_width: welded_col::WELDED_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

/// Build the welded DSL circuit.
pub fn committed_threshold_welded_circuit() -> DslCircuit {
    DslCircuit::new(committed_threshold_welded_descriptor())
}

/// Generate the welded trace from a `CommittedThresholdFactWitness`.
/// Returns `(trace, public_inputs)` with `public_inputs = [threshold_commitment,
/// fact_commitment]`.
pub fn generate_committed_threshold_welded_trace(
    witness: &CommittedThresholdFactWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use welded_col as w;
    let mut row = vec![BabyBear::ZERO; w::WELDED_WIDTH];

    row[w::PRIVATE_VALUE] = witness.private_value;
    row[w::THRESHOLD] = witness.threshold;
    row[w::BLINDING] = witness.blinding;

    let diff = witness.private_value - witness.threshold;
    row[w::DIFF] = diff;
    let diff_val = diff.as_u32();
    for i in 0..COMMITTED_DIFF_BITS {
        row[w::diff_bit(i)] = BabyBear::new((diff_val >> i) & 1);
    }

    let threshold_commitment = witness.compute_threshold_commitment();
    row[w::POSEIDON2_RESULT] = poseidon2::hash_2_to_1(witness.threshold, witness.blinding);
    row[w::THRESHOLD_COMMITMENT] = threshold_commitment;

    row[w::PREDICATE_SYM] = witness.predicate_sym;
    row[w::TERM1] = witness.term1;
    row[w::TERM2] = witness.term2;
    row[w::STATE_ROOT] = witness.state_root;
    let fact_hash = witness.compute_fact_hash();
    row[w::FACT_HASH] = fact_hash;
    let fact_commitment = poseidon2::hash_2_to_1(fact_hash, witness.state_root);
    row[w::FACT_COMMITMENT] = fact_commitment;

    let public_inputs = vec![threshold_commitment, fact_commitment];
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================
