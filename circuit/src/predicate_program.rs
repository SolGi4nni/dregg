//! Programmable predicate compilation pipeline.
//!
//! Turns a predicate specification into the appropriate AIR proof(s).
//! This implements Stage 1 of the programmable predicates compilation pipeline
//! from `docs/programmable-predicates.md`:
//!
//! ```text
//! PredicateProgram
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Program Analyzer   │  Determine which built-ins are needed
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  AIR Selector       │  Map each built-in to its specialized AIR
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Witness Generator  │  Fill traces from private state
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Proof Compositor   │  Compose sub-proofs into a single proof
//! └─────────────────────┘
//!     │
//!     ▼
//! PredicateProof (verifiable by anyone)
//! ```
//!
//! # Overview
//!
//! A `PredicateProgram` is a structured expression tree over leaf predicates
//! (range checks, membership, temporal continuity, relational comparisons,
//! committed thresholds) composed with boolean operators (AND, OR, NOT, Threshold).
//!
//! The compiler analyzes the program, maps each leaf to its specialized AIR,
//! and determines whether the program can be flattened into a single
//! `CompoundPredicateAir` or requires multi-AIR composition.
//!
//! # Compilation Strategy
//!
//! - **Single range leaf**: Dispatches directly to `PredicateAir`.
//! - **Multiple range leaves combined with AND/OR/Threshold**: Flattens into
//!   `CompoundPredicateAir` (up to 8 sub-predicates).
//! - **Temporal leaves**: Each becomes an independent `TemporalPredicateAir`.
//! - **Mixed AIR types or nested compositions**: Multi-AIR composition with
//!   a boolean formula over sub-proofs.

use std::collections::HashMap;

use crate::compound_predicate_air::{
    BooleanFormula, CompoundPredicateProof, Gate, prove_compound_predicate,
    verify_compound_predicate, MAX_COMPOUND_PREDICATES,
};
use crate::constraint_prover::ConstraintProof;
use crate::field::BabyBear;
use crate::poseidon2;
use crate::predicate_air::{
    PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
    verify_predicate,
};
use crate::relational_predicate_air::RelationType;
use crate::temporal_predicate_air::{
    TemporalPredicateProof, prove_temporal_predicate, verify_temporal_predicate,
};

// =============================================================================
// Program Representation
// =============================================================================

/// A predicate expression tree — the "program" that gets compiled to AIR proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateExpr {
    // ─── Leaf predicates (dispatch to specific AIRs) ───

    /// Range comparison: `attribute <op> threshold`.
    /// Dispatches to `PredicateAir`.
    Range {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },

    /// Set membership: `attribute IN committed_set`.
    /// Dispatches to `MerklePoseidon2StarkAir`.
    Membership {
        attribute: String,
        set_commitment: BabyBear,
    },

    /// Temporal continuity: `attribute <op> threshold for min_blocks consecutive steps`.
    /// Dispatches to `TemporalPredicateAir`.
    Temporal {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
        min_blocks: u64,
    },

    /// Relational comparison between two parties' committed values.
    /// Dispatches to `RelationalPredicateAir`.
    Relational {
        my_attribute: String,
        their_commitment: BabyBear,
        relation: RelationType,
    },

    /// Private threshold comparison where the threshold is committed.
    /// Dispatches to `CommittedThresholdAir`.
    CommittedThreshold {
        attribute: String,
        threshold_commitment: BabyBear,
    },

    // ─── Composition operators ───

    /// All sub-predicates must hold.
    And(Vec<PredicateExpr>),

    /// At least one sub-predicate must hold.
    Or(Vec<PredicateExpr>),

    /// The negation of a sub-predicate.
    Not(Box<PredicateExpr>),

    /// At least `k` of the given predicates must hold.
    Threshold { k: usize, predicates: Vec<PredicateExpr> },
}

/// A predicate program: an expression tree with resource limits.
#[derive(Clone, Debug)]
pub struct PredicateProgram {
    /// The predicate expression to evaluate and prove.
    pub expr: PredicateExpr,
    /// Maximum nesting depth (for resource limiting).
    pub max_depth: usize,
}

impl PredicateProgram {
    /// Create a new predicate program with the given expression and depth limit.
    pub fn new(expr: PredicateExpr, max_depth: usize) -> Self {
        Self { expr, max_depth }
    }

    /// Create a predicate program with the default depth limit (8).
    pub fn with_default_depth(expr: PredicateExpr) -> Self {
        Self { expr, max_depth: 8 }
    }
}

// =============================================================================
// Compilation Output
// =============================================================================

/// The type of AIR that a leaf predicate compiles to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AirType {
    /// `PredicateAir` — single range/comparison check.
    Range,
    /// `CompoundPredicateAir` — boolean combination of range checks.
    Compound,
    /// `TemporalPredicateAir` — predicate held over N steps.
    Temporal,
    /// `RelationalPredicateAir` — two-party value comparison.
    Relational,
    /// `CommittedThresholdAir` — value >= committed threshold.
    CommittedThreshold,
    /// `MerklePoseidon2StarkAir` — set membership proof.
    Membership,
}

/// Specification of what witness data is needed for a particular compiled sub-proof.
#[derive(Clone, Debug, PartialEq)]
pub enum WitnessSpec {
    /// Single range predicate: needs (attribute_name, predicate_type, threshold).
    Range {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },
    /// Temporal predicate: needs values at each step + state roots.
    Temporal {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
        min_blocks: u64,
    },
    /// Relational: needs my value + their commitment.
    Relational {
        my_attribute: String,
        their_commitment: BabyBear,
        relation: RelationType,
    },
    /// Committed threshold: needs my value + threshold + blinding.
    CommittedThreshold {
        attribute: String,
        threshold_commitment: BabyBear,
    },
    /// Membership: needs value + Merkle path.
    Membership {
        attribute: String,
        set_commitment: BabyBear,
    },
}

/// The compiled form of a predicate program — a plan for proof generation.
#[derive(Clone, Debug, PartialEq)]
pub enum CompiledPredicate {
    /// A single leaf that maps to one AIR instance.
    Single {
        air_type: AirType,
        witness_spec: WitnessSpec,
    },
    /// A compound predicate that uses `CompoundPredicateAir` to prove
    /// a boolean formula over multiple range sub-predicates in one proof.
    CompoundRange {
        /// The individual range sub-predicates (flattened from the expression tree).
        sub_predicates: Vec<WitnessSpec>,
        /// The boolean formula combining them.
        formula: BooleanFormula,
    },
    /// A multi-AIR composition: multiple independent sub-proofs combined
    /// by a boolean formula. This is used when the program mixes AIR types
    /// (e.g., range + temporal) that cannot be flattened into one AIR.
    Composite {
        sub_proofs: Vec<CompiledPredicate>,
        formula: CompositeFormula,
    },
}

/// Boolean formula for multi-AIR composition (over sub-proof results).
#[derive(Clone, Debug, PartialEq)]
pub enum CompositeFormula {
    /// All sub-proofs must verify.
    And,
    /// At least one sub-proof must verify.
    Or,
    /// At least `k` sub-proofs must verify.
    Threshold(usize),
    /// Negate the single sub-proof's result.
    Not,
}

// =============================================================================
// Compilation Errors
// =============================================================================

/// Errors that can occur during predicate compilation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The program exceeds the maximum allowed nesting depth.
    DepthExceeded { max: usize, actual: usize },
    /// The program has too many leaves for a compound AIR (> MAX_COMPOUND_PREDICATES).
    TooManyPredicates { max: usize, actual: usize },
    /// The program is empty (no predicates to prove).
    EmptyProgram,
    /// A NOT operator was applied to a non-single predicate (unsupported in current AIR).
    UnsupportedNot,
    /// Threshold `k` is zero or exceeds the number of predicates.
    InvalidThreshold { k: usize, n: usize },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DepthExceeded { max, actual } => {
                write!(f, "program depth {actual} exceeds maximum {max}")
            }
            Self::TooManyPredicates { max, actual } => {
                write!(f, "program has {actual} predicates, maximum is {max}")
            }
            Self::EmptyProgram => write!(f, "empty predicate program"),
            Self::UnsupportedNot => {
                write!(f, "NOT can only be applied to single-AIR predicates")
            }
            Self::InvalidThreshold { k, n } => {
                write!(f, "threshold k={k} is invalid for {n} predicates")
            }
        }
    }
}

// =============================================================================
// Compiler
// =============================================================================

/// Compile a predicate program into a proof plan.
///
/// The compiler:
/// 1. Validates depth/size limits.
/// 2. Flattens nested AND/OR into `CompoundPredicateAir` where possible
///    (when all leaves are range predicates and count <= MAX_COMPOUND_PREDICATES).
/// 3. Identifies which AIRs are needed.
/// 4. Returns a compilation plan (`CompiledPredicate`).
pub fn compile_predicate(program: &PredicateProgram) -> Result<CompiledPredicate, CompileError> {
    // Validate depth.
    let actual_depth = compute_depth(&program.expr);
    if actual_depth > program.max_depth {
        return Err(CompileError::DepthExceeded {
            max: program.max_depth,
            actual: actual_depth,
        });
    }

    compile_expr(&program.expr)
}

/// Compute the nesting depth of an expression.
fn compute_depth(expr: &PredicateExpr) -> usize {
    match expr {
        // Leaves have depth 1.
        PredicateExpr::Range { .. }
        | PredicateExpr::Membership { .. }
        | PredicateExpr::Temporal { .. }
        | PredicateExpr::Relational { .. }
        | PredicateExpr::CommittedThreshold { .. } => 1,

        // Composition operators have depth = 1 + max(children).
        PredicateExpr::And(children) | PredicateExpr::Or(children) => {
            1 + children.iter().map(compute_depth).max().unwrap_or(0)
        }
        PredicateExpr::Not(inner) => 1 + compute_depth(inner),
        PredicateExpr::Threshold { predicates, .. } => {
            1 + predicates.iter().map(compute_depth).max().unwrap_or(0)
        }
    }
}

/// Compile a single expression node.
fn compile_expr(expr: &PredicateExpr) -> Result<CompiledPredicate, CompileError> {
    match expr {
        // ─── Leaf nodes ───
        PredicateExpr::Range {
            attribute,
            predicate_type,
            threshold,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Range,
            witness_spec: WitnessSpec::Range {
                attribute: attribute.clone(),
                predicate_type: *predicate_type,
                threshold: *threshold,
            },
        }),

        PredicateExpr::Membership {
            attribute,
            set_commitment,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Membership,
            witness_spec: WitnessSpec::Membership {
                attribute: attribute.clone(),
                set_commitment: *set_commitment,
            },
        }),

        PredicateExpr::Temporal {
            attribute,
            predicate_type,
            threshold,
            min_blocks,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Temporal,
            witness_spec: WitnessSpec::Temporal {
                attribute: attribute.clone(),
                predicate_type: *predicate_type,
                threshold: *threshold,
                min_blocks: *min_blocks,
            },
        }),

        PredicateExpr::Relational {
            my_attribute,
            their_commitment,
            relation,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Relational,
            witness_spec: WitnessSpec::Relational {
                my_attribute: my_attribute.clone(),
                their_commitment: *their_commitment,
                relation: *relation,
            },
        }),

        PredicateExpr::CommittedThreshold {
            attribute,
            threshold_commitment,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::CommittedThreshold,
            witness_spec: WitnessSpec::CommittedThreshold {
                attribute: attribute.clone(),
                threshold_commitment: *threshold_commitment,
            },
        }),

        // ─── AND composition ───
        PredicateExpr::And(children) => {
            if children.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            compile_boolean_composition(children, CompositeFormulaKind::And)
        }

        // ─── OR composition ───
        PredicateExpr::Or(children) => {
            if children.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            compile_boolean_composition(children, CompositeFormulaKind::Or)
        }

        // ─── NOT ───
        PredicateExpr::Not(inner) => {
            // NOT is only supported over single-leaf predicates in the current AIR.
            // For range predicates we can flip the comparison (GTE -> LT, etc.).
            // For other types, we use a custom gate in a compound AIR.
            let compiled_inner = compile_expr(inner)?;
            match &compiled_inner {
                CompiledPredicate::Single { .. } => Ok(CompiledPredicate::Composite {
                    sub_proofs: vec![compiled_inner],
                    formula: CompositeFormula::Not,
                }),
                _ => Err(CompileError::UnsupportedNot),
            }
        }

        // ─── Threshold ───
        PredicateExpr::Threshold { k, predicates } => {
            if predicates.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            if *k == 0 || *k > predicates.len() {
                return Err(CompileError::InvalidThreshold {
                    k: *k,
                    n: predicates.len(),
                });
            }
            compile_boolean_composition(predicates, CompositeFormulaKind::Threshold(*k))
        }
    }
}

/// Internal enum for tracking which boolean composition to build.
#[derive(Clone, Debug)]
enum CompositeFormulaKind {
    And,
    Or,
    Threshold(usize),
}

/// Compile a boolean composition (AND, OR, Threshold) of child expressions.
///
/// If ALL children are range predicates and the total count fits in a single
/// `CompoundPredicateAir`, this flattens into a `CompoundRange` compilation.
/// Otherwise, it produces a `Composite` with independently compiled sub-proofs.
fn compile_boolean_composition(
    children: &[PredicateExpr],
    kind: CompositeFormulaKind,
) -> Result<CompiledPredicate, CompileError> {
    // Check if all children are range-type leaves (can flatten into CompoundPredicateAir).
    let all_range = children.iter().all(|c| matches!(c, PredicateExpr::Range { .. }));

    if all_range && children.len() <= MAX_COMPOUND_PREDICATES {
        // Flatten into a single CompoundPredicateAir.
        let sub_predicates: Vec<WitnessSpec> = children
            .iter()
            .map(|c| match c {
                PredicateExpr::Range {
                    attribute,
                    predicate_type,
                    threshold,
                } => WitnessSpec::Range {
                    attribute: attribute.clone(),
                    predicate_type: *predicate_type,
                    threshold: *threshold,
                },
                _ => unreachable!("checked all_range above"),
            })
            .collect();

        let indices: Vec<usize> = (0..sub_predicates.len()).collect();
        let formula = match kind {
            CompositeFormulaKind::And => BooleanFormula::And(indices),
            CompositeFormulaKind::Or => BooleanFormula::Or(indices),
            CompositeFormulaKind::Threshold(k) => BooleanFormula::Threshold(k, indices),
        };

        Ok(CompiledPredicate::CompoundRange {
            sub_predicates,
            formula,
        })
    } else {
        // Mixed AIR types or too many predicates: compile each child independently.
        let sub_proofs: Vec<CompiledPredicate> = children
            .iter()
            .map(compile_expr)
            .collect::<Result<Vec<_>, _>>()?;

        let formula = match kind {
            CompositeFormulaKind::And => CompositeFormula::And,
            CompositeFormulaKind::Or => CompositeFormula::Or,
            CompositeFormulaKind::Threshold(k) => CompositeFormula::Threshold(k),
        };

        Ok(CompiledPredicate::Composite {
            sub_proofs,
            formula,
        })
    }
}

// =============================================================================
// Proof Execution
// =============================================================================

/// Errors that can occur during proof generation.
#[derive(Clone, Debug)]
pub enum ProveError {
    /// A required attribute value is missing from the private state.
    MissingAttribute(String),
    /// The predicate is not satisfiable with the given private state.
    NotSatisfiable(String),
    /// Proof generation failed (AIR constraint violation or internal error).
    ProofGenerationFailed(String),
    /// Temporal proof requires historical values not provided.
    MissingTemporalData { attribute: String, needed: u64 },
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingAttribute(name) => write!(f, "missing attribute: {name}"),
            Self::NotSatisfiable(msg) => write!(f, "not satisfiable: {msg}"),
            Self::ProofGenerationFailed(msg) => write!(f, "proof generation failed: {msg}"),
            Self::MissingTemporalData { attribute, needed } => {
                write!(
                    f,
                    "temporal proof for '{attribute}' needs {needed} historical values"
                )
            }
        }
    }
}

/// The output of proving a predicate program: a collection of sub-proofs
/// with the boolean formula governing their composition.
#[derive(Clone, Debug)]
pub struct ProgramProof {
    /// The sub-proofs generated by the proving pipeline.
    pub sub_proofs: Vec<SubProof>,
    /// The composition structure matching the compiled predicate.
    pub structure: ProofStructure,
}

/// A single sub-proof within a program proof.
#[derive(Clone, Debug)]
pub enum SubProof {
    /// A single-predicate range proof.
    Range(PredicateProof),
    /// A compound range proof (multiple range checks in one AIR).
    Compound(CompoundPredicateProof),
    /// A temporal predicate proof.
    Temporal(TemporalPredicateProof),
    // Future: Relational, CommittedThreshold, Membership sub-proofs.
}

/// The structure of a program proof (mirrors the compiled predicate shape).
#[derive(Clone, Debug)]
pub enum ProofStructure {
    /// Single proof — just verify the sub-proof directly.
    Single,
    /// Compound range — one CompoundPredicateAir proof covers everything.
    CompoundRange,
    /// Composite — multiple sub-proofs composed with a formula.
    Composite(CompositeFormula),
}

/// Extended private state for proof generation.
///
/// Maps attribute names to their private values. For temporal predicates,
/// historical values and state roots are also provided.
#[derive(Clone, Debug, Default)]
pub struct PrivateState {
    /// Current attribute values: attribute_name -> value.
    pub values: HashMap<String, u64>,
    /// Historical values for temporal predicates: attribute_name -> (values, state_roots).
    pub temporal_history: HashMap<String, (Vec<u64>, Vec<BabyBear>)>,
    /// Fact hashes for each attribute (for computing fact commitments).
    pub fact_hashes: HashMap<String, BabyBear>,
}

/// Prove a compiled predicate program against private state.
///
/// # Arguments
///
/// * `compiled` - The compiled predicate (output of `compile_predicate`).
/// * `private_state` - The prover's private attribute values.
/// * `state_root` - The Poseidon2 root of the current token state.
///
/// # Returns
///
/// A `ProgramProof` that can be verified by anyone knowing the public inputs,
/// or a `ProveError` if the predicate cannot be proven.
pub fn prove_program(
    compiled: &CompiledPredicate,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    match compiled {
        CompiledPredicate::Single { witness_spec, .. } => {
            prove_single(witness_spec, private_state, state_root)
        }
        CompiledPredicate::CompoundRange {
            sub_predicates,
            formula,
        } => prove_compound_range(sub_predicates, formula, private_state, state_root),
        CompiledPredicate::Composite {
            sub_proofs,
            formula,
        } => prove_composite(sub_proofs, formula, private_state, state_root),
    }
}

/// Prove a single leaf predicate.
fn prove_single(
    witness_spec: &WitnessSpec,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    match witness_spec {
        WitnessSpec::Range {
            attribute,
            predicate_type,
            threshold,
        } => {
            let value = private_state
                .values
                .get(attribute)
                .ok_or_else(|| ProveError::MissingAttribute(attribute.clone()))?;

            let fact_hash = private_state
                .fact_hashes
                .get(attribute)
                .copied()
                .unwrap_or_else(|| compute_attribute_fact_hash(attribute, *value));

            let fact_commitment = compute_fact_commitment(fact_hash, state_root);

            let witness = PredicateWitness {
                private_value: BabyBear::new(*value as u32),
                threshold: BabyBear::new(*threshold as u32),
                predicate_type: *predicate_type,
                fact_commitment,
            };

            let proof = prove_predicate(witness).ok_or_else(|| {
                ProveError::NotSatisfiable(format!(
                    "{attribute}: value {value} does not satisfy {predicate_type:?} {threshold}"
                ))
            })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::Range(proof)],
                structure: ProofStructure::Single,
            })
        }

        WitnessSpec::Temporal {
            attribute,
            predicate_type,
            threshold,
            min_blocks,
        } => {
            let (values, roots) = private_state
                .temporal_history
                .get(attribute)
                .ok_or_else(|| ProveError::MissingTemporalData {
                    attribute: attribute.clone(),
                    needed: *min_blocks,
                })?;

            if (values.len() as u64) < *min_blocks {
                return Err(ProveError::MissingTemporalData {
                    attribute: attribute.clone(),
                    needed: *min_blocks,
                });
            }

            let values_bb: Vec<BabyBear> = values.iter().map(|v| BabyBear::new(*v as u32)).collect();
            let threshold_bb = BabyBear::new(*threshold as u32);

            let proof = prove_temporal_predicate(
                &values_bb,
                roots,
                *predicate_type,
                threshold_bb,
            )
            .ok_or_else(|| {
                ProveError::NotSatisfiable(format!(
                    "{attribute}: temporal predicate not satisfied across all steps"
                ))
            })?;

            Ok(ProgramProof {
                sub_proofs: vec![SubProof::Temporal(proof)],
                structure: ProofStructure::Single,
            })
        }

        // Membership, Relational, and CommittedThreshold are recognized but
        // their proof generation is deferred to Phase 2 (composition engine).
        WitnessSpec::Membership { attribute, .. }
        | WitnessSpec::Relational { my_attribute: attribute, .. }
        | WitnessSpec::CommittedThreshold { attribute, .. } => {
            Err(ProveError::ProofGenerationFailed(format!(
                "AIR type for '{}' not yet supported in program prover",
                attribute
            )))
        }
    }
}

/// Prove a compound range program (flattened into CompoundPredicateAir).
fn prove_compound_range(
    sub_predicates: &[WitnessSpec],
    formula: &BooleanFormula,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    // Build the predicate tuples for the compound AIR.
    let mut predicates: Vec<(BabyBear, PredicateType, BabyBear)> = Vec::with_capacity(sub_predicates.len());
    let mut commitments: Vec<BabyBear> = Vec::with_capacity(sub_predicates.len());

    for spec in sub_predicates {
        match spec {
            WitnessSpec::Range {
                attribute,
                predicate_type,
                threshold,
            } => {
                let value = private_state
                    .values
                    .get(attribute)
                    .ok_or_else(|| ProveError::MissingAttribute(attribute.clone()))?;

                let fact_hash = private_state
                    .fact_hashes
                    .get(attribute)
                    .copied()
                    .unwrap_or_else(|| compute_attribute_fact_hash(attribute, *value));

                let fact_commitment = compute_fact_commitment(fact_hash, state_root);

                predicates.push((
                    BabyBear::new(*value as u32),
                    *predicate_type,
                    BabyBear::new(*threshold as u32),
                ));
                commitments.push(fact_commitment);
            }
            _ => {
                return Err(ProveError::ProofGenerationFailed(
                    "compound range received non-range witness spec".to_string(),
                ));
            }
        }
    }

    let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments).ok_or_else(
        || {
            ProveError::NotSatisfiable(
                "compound predicate not satisfiable with given values".to_string(),
            )
        },
    )?;

    Ok(ProgramProof {
        sub_proofs: vec![SubProof::Compound(proof)],
        structure: ProofStructure::CompoundRange,
    })
}

/// Prove a composite program (multiple AIR types combined).
fn prove_composite(
    sub_compilations: &[CompiledPredicate],
    formula: &CompositeFormula,
    private_state: &PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProveError> {
    // For AND: all sub-proofs must succeed.
    // For OR: at least one must succeed.
    // For Threshold(k): at least k must succeed.
    // For NOT: the single sub-proof must FAIL (we invert the semantics).

    let mut all_sub_proofs: Vec<SubProof> = Vec::new();

    match formula {
        CompositeFormula::And => {
            // All must succeed.
            for sub in sub_compilations {
                let sub_result = prove_program(sub, private_state, state_root)?;
                all_sub_proofs.extend(sub_result.sub_proofs);
            }
        }
        CompositeFormula::Or => {
            // At least one must succeed. Try each; collect the first success.
            let mut found_success = false;
            for sub in sub_compilations {
                match prove_program(sub, private_state, state_root) {
                    Ok(sub_result) => {
                        all_sub_proofs.extend(sub_result.sub_proofs);
                        found_success = true;
                        break;
                    }
                    Err(_) => continue,
                }
            }
            if !found_success {
                return Err(ProveError::NotSatisfiable(
                    "no disjunct is satisfiable".to_string(),
                ));
            }
        }
        CompositeFormula::Threshold(k) => {
            // At least k must succeed.
            let mut successes = 0;
            for sub in sub_compilations {
                match prove_program(sub, private_state, state_root) {
                    Ok(sub_result) => {
                        all_sub_proofs.extend(sub_result.sub_proofs);
                        successes += 1;
                    }
                    Err(_) => continue,
                }
            }
            if successes < *k {
                return Err(ProveError::NotSatisfiable(format!(
                    "only {successes} of {k} required predicates satisfied"
                )));
            }
        }
        CompositeFormula::Not => {
            // The single sub-proof must be NOT satisfiable.
            // NOT in ZK is tricky: we prove that we CANNOT produce a valid proof.
            // For now, we check locally and produce a "vacuous" proof structure
            // indicating the inner predicate fails.
            if sub_compilations.len() != 1 {
                return Err(ProveError::ProofGenerationFailed(
                    "NOT requires exactly one sub-predicate".to_string(),
                ));
            }
            match prove_program(&sub_compilations[0], private_state, state_root) {
                Ok(_) => {
                    return Err(ProveError::NotSatisfiable(
                        "NOT: inner predicate is satisfied (should fail)".to_string(),
                    ));
                }
                Err(_) => {
                    // The inner predicate fails — NOT is satisfied.
                    // In the current system we cannot produce a ZK proof of non-satisfaction,
                    // so we record this as a composite with no sub-proofs.
                    // Full support requires Phase 2 (MPC-in-the-head or NonRevocationAir).
                }
            }
        }
    }

    Ok(ProgramProof {
        sub_proofs: all_sub_proofs,
        structure: ProofStructure::Composite(formula.clone()),
    })
}

// =============================================================================
// Verification
// =============================================================================

/// Verify a program proof against expected public commitments.
///
/// The verifier provides:
/// - The compiled predicate (they know the program structure).
/// - The program proof to verify.
/// - Expected fact commitments for each attribute.
///
/// Returns `true` if the proof is valid for the given commitments.
pub fn verify_program(
    proof: &ProgramProof,
    compiled: &CompiledPredicate,
    expected_commitments: &HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    match (&proof.structure, compiled) {
        (ProofStructure::Single, CompiledPredicate::Single { witness_spec, .. }) => {
            verify_single_proof(&proof.sub_proofs, witness_spec, expected_commitments, state_root)
        }
        (
            ProofStructure::CompoundRange,
            CompiledPredicate::CompoundRange {
                sub_predicates,
                formula,
            },
        ) => verify_compound_range_proof(
            &proof.sub_proofs,
            sub_predicates,
            formula,
            expected_commitments,
            state_root,
        ),
        (
            ProofStructure::Composite(_),
            CompiledPredicate::Composite { sub_proofs: compiled_subs, formula },
        ) => verify_composite_proof(
            &proof.sub_proofs,
            compiled_subs,
            formula,
            expected_commitments,
            state_root,
        ),
        _ => false, // Structure mismatch.
    }
}

/// Verify a single range or temporal sub-proof.
fn verify_single_proof(
    sub_proofs: &[SubProof],
    witness_spec: &WitnessSpec,
    expected_commitments: &HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    if sub_proofs.len() != 1 {
        return false;
    }

    match (&sub_proofs[0], witness_spec) {
        (
            SubProof::Range(proof),
            WitnessSpec::Range {
                attribute,
                threshold,
                ..
            },
        ) => {
            let expected_commitment = expected_commitments
                .get(attribute)
                .copied()
                .unwrap_or_else(|| {
                    // If no explicit commitment provided, we cannot verify.
                    BabyBear::ZERO
                });
            verify_predicate(proof, BabyBear::new(*threshold as u32), expected_commitment)
        }

        (
            SubProof::Temporal(proof),
            WitnessSpec::Temporal {
                threshold,
                min_blocks,
                ..
            },
        ) => {
            // For temporal, the verifier checks threshold, num_steps, and state roots.
            proof.num_steps as u64 >= *min_blocks
                && proof.threshold == BabyBear::new(*threshold as u32)
                // The proof internally verifies via its constraint proof.
                && proof.proof.verify(&[
                    BabyBear::new(*threshold as u32),
                    BabyBear::new(proof.num_steps),
                    proof.initial_state_root,
                    proof.final_state_root,
                ])
        }

        _ => false,
    }
}

/// Verify a compound range proof.
fn verify_compound_range_proof(
    sub_proofs: &[SubProof],
    sub_predicates: &[WitnessSpec],
    formula: &BooleanFormula,
    expected_commitments: &HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    if sub_proofs.len() != 1 {
        return false;
    }

    let compound_proof = match &sub_proofs[0] {
        SubProof::Compound(p) => p,
        _ => return false,
    };

    // Reconstruct expected commitments for the compound proof.
    let mut expected: Vec<BabyBear> = Vec::with_capacity(sub_predicates.len());
    for spec in sub_predicates {
        match spec {
            WitnessSpec::Range { attribute, threshold, .. } => {
                let commitment = expected_commitments
                    .get(attribute)
                    .copied()
                    .unwrap_or(BabyBear::ZERO);
                expected.push(commitment);
            }
            _ => return false,
        }
    }

    verify_compound_predicate(compound_proof, &expected, formula)
}

/// Verify a composite proof.
fn verify_composite_proof(
    sub_proofs: &[SubProof],
    compiled_subs: &[CompiledPredicate],
    formula: &CompositeFormula,
    expected_commitments: &HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    match formula {
        CompositeFormula::And => {
            // For AND composite: all sub-proofs must be present and verify.
            // We verify each sub-proof against its corresponding compiled predicate.
            let mut proof_idx = 0;
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if proof_idx + sub_proof_count > sub_proofs.len() {
                    return false;
                }
                let sub_slice = &sub_proofs[proof_idx..proof_idx + sub_proof_count];
                let sub_program_proof = ProgramProof {
                    sub_proofs: sub_slice.to_vec(),
                    structure: infer_structure(compiled_sub),
                };
                if !verify_program(&sub_program_proof, compiled_sub, expected_commitments, state_root) {
                    return false;
                }
                proof_idx += sub_proof_count;
            }
            true
        }
        CompositeFormula::Or => {
            // For OR: at least one sub-proof must verify.
            if sub_proofs.is_empty() {
                return false;
            }
            // We try verifying the provided sub-proofs against each compiled sub.
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if sub_proof_count <= sub_proofs.len() {
                    let sub_slice = &sub_proofs[..sub_proof_count];
                    let sub_program_proof = ProgramProof {
                        sub_proofs: sub_slice.to_vec(),
                        structure: infer_structure(compiled_sub),
                    };
                    if verify_program(&sub_program_proof, compiled_sub, expected_commitments, state_root) {
                        return true;
                    }
                }
            }
            false
        }
        CompositeFormula::Threshold(k) => {
            // For Threshold(k): at least k sub-proofs must verify.
            // The prover provides exactly the proofs for the k satisfied branches.
            // We count how many compiled subs can be verified with the provided proofs.
            let mut verified = 0;
            let mut proof_idx = 0;
            for compiled_sub in compiled_subs {
                let sub_proof_count = count_expected_sub_proofs(compiled_sub);
                if proof_idx + sub_proof_count > sub_proofs.len() {
                    break;
                }
                let sub_slice = &sub_proofs[proof_idx..proof_idx + sub_proof_count];
                let sub_program_proof = ProgramProof {
                    sub_proofs: sub_slice.to_vec(),
                    structure: infer_structure(compiled_sub),
                };
                if verify_program(&sub_program_proof, compiled_sub, expected_commitments, state_root) {
                    verified += 1;
                    proof_idx += sub_proof_count;
                }
            }
            verified >= *k
        }
        CompositeFormula::Not => {
            // NOT verification: the proof must be empty (inner was not satisfiable).
            sub_proofs.is_empty()
        }
    }
}

/// Count how many sub-proof items a compiled predicate generates.
fn count_expected_sub_proofs(compiled: &CompiledPredicate) -> usize {
    match compiled {
        CompiledPredicate::Single { .. } => 1,
        CompiledPredicate::CompoundRange { .. } => 1,
        CompiledPredicate::Composite { sub_proofs, .. } => {
            sub_proofs.iter().map(count_expected_sub_proofs).sum()
        }
    }
}

/// Infer the proof structure from a compiled predicate.
fn infer_structure(compiled: &CompiledPredicate) -> ProofStructure {
    match compiled {
        CompiledPredicate::Single { .. } => ProofStructure::Single,
        CompiledPredicate::CompoundRange { .. } => ProofStructure::CompoundRange,
        CompiledPredicate::Composite { formula, .. } => {
            ProofStructure::Composite(formula.clone())
        }
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute a default fact hash for an attribute/value pair.
///
/// This is a convenience for testing and simple cases. In production, the fact hash
/// would come from the committed token state's Merkle tree.
fn compute_attribute_fact_hash(attribute: &str, value: u64) -> BabyBear {
    let attr_bytes = blake3::hash(attribute.as_bytes());
    let attr_bb = poseidon2::hash_many(&BabyBear::encode_hash(attr_bytes.as_bytes()));
    let value_bb = BabyBear::new(value as u32);
    poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO])
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a default private state with given attribute values.
    fn make_state(attrs: &[(&str, u64)]) -> PrivateState {
        let mut state = PrivateState::default();
        for &(name, value) in attrs {
            state.values.insert(name.to_string(), value);
        }
        state
    }

    /// Helper: create expected commitments matching the private state.
    fn make_commitments(attrs: &[(&str, u64)], state_root: BabyBear) -> HashMap<String, BabyBear> {
        let mut map = HashMap::new();
        for &(name, value) in attrs {
            let fact_hash = compute_attribute_fact_hash(name, value);
            let commitment = compute_fact_commitment(fact_hash, state_root);
            map.insert(name.to_string(), commitment);
        }
        map
    }

    // =========================================================================
    // Compilation tests
    // =========================================================================

    #[test]
    fn test_compile_single_range() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        });

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Single {
                air_type,
                witness_spec,
            } => {
                assert_eq!(*air_type, AirType::Range);
                match witness_spec {
                    WitnessSpec::Range {
                        attribute,
                        predicate_type,
                        threshold,
                    } => {
                        assert_eq!(attribute, "balance");
                        assert_eq!(*predicate_type, PredicateType::Gte);
                        assert_eq!(*threshold, 1000);
                    }
                    _ => panic!("expected Range witness spec"),
                }
            }
            _ => panic!("expected Single compiled predicate"),
        }
    }

    #[test]
    fn test_compile_and_two_ranges_flattens_to_compound() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::CompoundRange {
                sub_predicates,
                formula,
            } => {
                assert_eq!(sub_predicates.len(), 2);
                assert_eq!(*formula, BooleanFormula::And(vec![0, 1]));
            }
            _ => panic!("expected CompoundRange, got {:?}", compiled),
        }
    }

    #[test]
    fn test_compile_or_ranges_flattens_to_compound() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::Range {
                attribute: "tier".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 3,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::CompoundRange { formula, .. } => {
                assert_eq!(*formula, BooleanFormula::Or(vec![0, 1]));
            }
            _ => panic!("expected CompoundRange"),
        }
    }

    #[test]
    fn test_compile_mixed_types_produces_composite() {
        // AND(range, temporal) cannot flatten because temporal uses a different AIR.
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
            },
            PredicateExpr::Temporal {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
                min_blocks: 30,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Composite { sub_proofs, formula } => {
                assert_eq!(sub_proofs.len(), 2);
                assert!(matches!(formula, CompositeFormula::And));
            }
            _ => panic!("expected Composite"),
        }
    }

    #[test]
    fn test_compile_nested_or_and_produces_composite() {
        // OR(AND(range, range), temporal) -> Composite because of mixed types.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::And(vec![
                PredicateExpr::Range {
                    attribute: "age".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 18,
                },
                PredicateExpr::Range {
                    attribute: "balance".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 500,
                },
            ]),
            PredicateExpr::Temporal {
                attribute: "reputation".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 50,
                min_blocks: 10,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        match &compiled {
            CompiledPredicate::Composite { sub_proofs, formula } => {
                assert_eq!(sub_proofs.len(), 2);
                assert!(matches!(formula, CompositeFormula::Or));
                // First sub-proof should be CompoundRange (AND of two ranges).
                assert!(matches!(&sub_proofs[0], CompiledPredicate::CompoundRange { .. }));
                // Second should be Single(Temporal).
                assert!(matches!(
                    &sub_proofs[1],
                    CompiledPredicate::Single { air_type: AirType::Temporal, .. }
                ));
            }
            _ => panic!("expected Composite"),
        }
    }

    #[test]
    fn test_compile_depth_exceeded() {
        // Create a deeply nested program.
        let mut expr = PredicateExpr::Range {
            attribute: "x".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1,
        };
        for _ in 0..5 {
            expr = PredicateExpr::And(vec![expr]);
        }
        // Depth is 6 (5 levels of And + 1 leaf).
        let program = PredicateProgram::new(expr, 3); // max_depth = 3
        let result = compile_predicate(&program);
        assert!(matches!(result, Err(CompileError::DepthExceeded { max: 3, .. })));
    }

    #[test]
    fn test_compile_empty_and_fails() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![]));
        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::EmptyProgram));
    }

    #[test]
    fn test_compile_threshold_invalid_k() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Threshold {
            k: 0,
            predicates: vec![PredicateExpr::Range {
                attribute: "x".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1,
            }],
        });
        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::InvalidThreshold { k: 0, n: 1 }));
    }

    #[test]
    fn test_compile_threshold_k_exceeds_n() {
        let program = PredicateProgram::with_default_depth(PredicateExpr::Threshold {
            k: 3,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 1,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 1,
                },
            ],
        });
        let result = compile_predicate(&program);
        assert_eq!(result, Err(CompileError::InvalidThreshold { k: 3, n: 2 }));
    }

    // =========================================================================
    // Prove + verify roundtrip tests
    // =========================================================================

    #[test]
    fn test_prove_verify_single_range() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("balance", 5000)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_single_range_unsatisfiable() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 10000,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 500)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_prove_verify_compound_and() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("age", 25), ("balance", 5000)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_compound_and_one_fails() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::And(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 18,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 500)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::NotSatisfiable(_))));
    }

    #[test]
    fn test_prove_verify_compound_or() {
        let state_root = BabyBear::new(99999);
        // OR(age >= 21, balance >= 10000) -- only age passes.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::Range {
                attribute: "age".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 21,
            },
            PredicateExpr::Range {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 10000,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 500)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("age", 25), ("balance", 500)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_threshold() {
        let state_root = BabyBear::new(99999);
        // At least 2 of (a >= 10, b >= 20, c >= 30): a=15 pass, b=25 pass, c=5 fail.
        let program = PredicateProgram::with_default_depth(PredicateExpr::Threshold {
            k: 2,
            predicates: vec![
                PredicateExpr::Range {
                    attribute: "a".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 10,
                },
                PredicateExpr::Range {
                    attribute: "b".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 20,
                },
                PredicateExpr::Range {
                    attribute: "c".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 30,
                },
            ],
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("a", 15), ("b", 25), ("c", 5)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        let commitments = make_commitments(&[("a", 15), ("b", 25), ("c", 5)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_composite_or_with_temporal() {
        let state_root = BabyBear::new(99999);
        // OR(AND(age >= 18, balance >= 500), temporal(balance >= 1000 for 5 blocks))
        // We satisfy the first branch (AND).
        let program = PredicateProgram::with_default_depth(PredicateExpr::Or(vec![
            PredicateExpr::And(vec![
                PredicateExpr::Range {
                    attribute: "age".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 18,
                },
                PredicateExpr::Range {
                    attribute: "balance".to_string(),
                    predicate_type: PredicateType::Gte,
                    threshold: 500,
                },
            ]),
            PredicateExpr::Temporal {
                attribute: "balance".to_string(),
                predicate_type: PredicateType::Gte,
                threshold: 1000,
                min_blocks: 5,
            },
        ]));

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("age", 25), ("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        // For OR composite, verification should pass with the first branch's proofs.
        let commitments = make_commitments(&[("age", 25), ("balance", 5000)], state_root);
        assert!(verify_program(&proof, &compiled, &commitments, state_root));
    }

    #[test]
    fn test_prove_verify_temporal() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Temporal {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_blocks: 5,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Provide temporal history.
        let mut private_state = PrivateState::default();
        private_state.values.insert("balance".to_string(), 200);
        let values: Vec<u64> = vec![200, 150, 300, 100, 500];
        let roots: Vec<BabyBear> = (0..5).map(|i| BabyBear::new(1000 + i)).collect();
        private_state
            .temporal_history
            .insert("balance".to_string(), (values, roots));

        let proof = prove_program(&compiled, &private_state, state_root).unwrap();
        assert!(matches!(proof.structure, ProofStructure::Single));
        assert_eq!(proof.sub_proofs.len(), 1);
        assert!(matches!(&proof.sub_proofs[0], SubProof::Temporal(_)));
    }

    #[test]
    fn test_prove_temporal_insufficient_history() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Temporal {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_blocks: 10,
        });

        let compiled = compile_predicate(&program).unwrap();

        // Only provide 5 steps when 10 are needed.
        let mut private_state = PrivateState::default();
        let values: Vec<u64> = vec![200, 150, 300, 100, 500];
        let roots: Vec<BabyBear> = (0..5).map(|i| BabyBear::new(1000 + i)).collect();
        private_state
            .temporal_history
            .insert("balance".to_string(), (values, roots));

        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::MissingTemporalData { .. })));
    }

    #[test]
    fn test_prove_missing_attribute() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "nonexistent".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 5000)]);
        let result = prove_program(&compiled, &private_state, state_root);
        assert!(matches!(result, Err(ProveError::MissingAttribute(_))));
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment() {
        let state_root = BabyBear::new(99999);
        let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        });

        let compiled = compile_predicate(&program).unwrap();
        let private_state = make_state(&[("balance", 5000)]);
        let proof = prove_program(&compiled, &private_state, state_root).unwrap();

        // Use wrong commitments.
        let mut wrong_commitments = HashMap::new();
        wrong_commitments.insert("balance".to_string(), BabyBear::new(12345));
        assert!(!verify_program(
            &proof,
            &compiled,
            &wrong_commitments,
            state_root
        ));
    }
}
