//! Standard DSL circuit descriptors for dregg proof generation and verification.
//!
//! This module provides factory functions for all production DSL circuits:
//! - [`merkle_poseidon2_descriptor`] / [`merkle_poseidon2_circuit`]
//! - [`blinded_merkle_poseidon2_descriptor`] / [`blinded_merkle_poseidon2_circuit`]
//! - [`derivation_descriptor`] / [`derivation_circuit`]
//!
//! These replace the old hand-written AIRs (`MerklePoseidon2StarkAir`,
//! `BlindedMerklePoseidon2StarkAir`, `NonRevocationAir`, `DerivationAir`) which
//! are now DEPRECATED.

use crate::field::{BABYBEAR_P, BabyBear};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// AIR name constants (canonical, versioned)
// ============================================================================

/// AIR name for Effect VM proofs (sovereign transitions).
pub const EFFECT_VM_AIR_NAME: &str = "dregg-effect-vm-v1";

/// AIR name for standard Merkle Poseidon2 membership proofs.
pub const MERKLE_POSEIDON2_AIR_NAME: &str = "dregg-merkle-poseidon2-v1";

/// AIR name for blinded (ring) Merkle membership proofs.
pub const BLINDED_MERKLE_AIR_NAME: &str = "dregg-blinded-merkle-v1";

/// AIR name for derivation proofs.
pub const DERIVATION_AIR_NAME: &str = "dregg-derivation-v1";

// ============================================================================
// Merkle Poseidon2
// ============================================================================

/// Column layout for Merkle Poseidon2.
pub mod merkle_col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
    // Blinded variant only:
    pub const BLINDING: usize = 6;
    pub const BLINDED: usize = 7;
}

pub const MERKLE_P2_WIDTH: usize = 6;
pub const BLINDED_MERKLE_P2_WIDTH: usize = 8;
pub const MERKLE_PUBLIC_INPUT_COUNT: usize = 2;

/// Build a 4-ary Merkle membership `CircuitDescriptor` using Poseidon2 (hash_fact).
///
/// Proves: "I know a leaf and a path such that hashing up the tree yields the claimed root."
///
/// Public inputs: [leaf_hash, root]
pub fn merkle_poseidon2_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let constraints = vec![
        // C1: Position validity -- pos*(pos-1)*(pos-2)*(pos-3) == 0
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                    ],
                },
                PolyTerm {
                    coeff: neg_6,
                    col_indices: vec![
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                    ],
                },
                PolyTerm {
                    coeff: pos_11,
                    col_indices: vec![merkle_col::POSITION, merkle_col::POSITION],
                },
                PolyTerm {
                    coeff: neg_6,
                    col_indices: vec![merkle_col::POSITION],
                },
            ],
        },
        // C2: Parent hash binding (position-independent 4-to-1 hash)
        ConstraintExpr::MerkleHash {
            output_col: merkle_col::PARENT,
            current_col: merkle_col::CURRENT,
            sib_cols: [merkle_col::SIB0, merkle_col::SIB1, merkle_col::SIB2],
            position_col: merkle_col::POSITION,
        },
        // C3: Chain continuity
        ConstraintExpr::Transition {
            next_col: merkle_col::CURRENT,
            local_col: merkle_col::PARENT,
        },
    ];

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: merkle_col::CURRENT,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: merkle_col::PARENT,
            pi_index: 1,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: merkle_col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: merkle_col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: merkle_col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: merkle_col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: merkle_col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: merkle_col::PARENT,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: MERKLE_POSEIDON2_AIR_NAME.into(),
        trace_width: MERKLE_P2_WIDTH,
        max_degree: 5,
        columns,
        constraints,
        boundaries,
        public_input_count: MERKLE_PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` for standard Merkle Poseidon2 membership.
pub fn merkle_poseidon2_circuit() -> DslCircuit {
    DslCircuit::new(merkle_poseidon2_descriptor())
}

/// Build a blinded 4-ary Merkle membership `CircuitDescriptor` using Poseidon2.
///
/// Proves: "I know a leaf in this tree" WITHOUT revealing which leaf.
/// Public inputs: [blinded_leaf, root]
pub fn blinded_merkle_poseidon2_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let constraints = vec![
        // C1: Position validity
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                    ],
                },
                PolyTerm {
                    coeff: neg_6,
                    col_indices: vec![
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                        merkle_col::POSITION,
                    ],
                },
                PolyTerm {
                    coeff: pos_11,
                    col_indices: vec![merkle_col::POSITION, merkle_col::POSITION],
                },
                PolyTerm {
                    coeff: neg_6,
                    col_indices: vec![merkle_col::POSITION],
                },
            ],
        },
        // C2: Parent hash binding (position-independent 4-to-1 hash)
        ConstraintExpr::MerkleHash {
            output_col: merkle_col::PARENT,
            current_col: merkle_col::CURRENT,
            sib_cols: [merkle_col::SIB0, merkle_col::SIB1, merkle_col::SIB2],
            position_col: merkle_col::POSITION,
        },
        // C3: Chain continuity
        ConstraintExpr::Transition {
            next_col: merkle_col::CURRENT,
            local_col: merkle_col::PARENT,
        },
        // C4: Blinding hash binding
        ConstraintExpr::Hash {
            output_col: merkle_col::BLINDED,
            input_cols: vec![merkle_col::CURRENT, merkle_col::BLINDING],
        },
    ];

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: merkle_col::BLINDED,
            pi_index: 0,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: merkle_col::PARENT,
            pi_index: 1,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: merkle_col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: merkle_col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: merkle_col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: merkle_col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: merkle_col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: merkle_col::PARENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "blinding".into(),
            index: merkle_col::BLINDING,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "blinded".into(),
            index: merkle_col::BLINDED,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: BLINDED_MERKLE_AIR_NAME.into(),
        trace_width: BLINDED_MERKLE_P2_WIDTH,
        max_degree: 5,
        columns,
        constraints,
        boundaries,
        public_input_count: MERKLE_PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` for blinded Merkle Poseidon2 membership (ring membership).
pub fn blinded_merkle_poseidon2_circuit() -> DslCircuit {
    DslCircuit::new(blinded_merkle_poseidon2_descriptor())
}

// ============================================================================
// Derivation
// ============================================================================

/// Auxiliary column indices for C2 (ConditionalNonzero) inverse columns.
pub use crate::dsl::derivation::BODY_HASH_INV_START as DERIVATION_BODY_HASH_INV_START;

/// Extended trace width including auxiliary inverse columns for C2.
pub use crate::dsl::derivation::EXTENDED_TRACE_WIDTH as DERIVATION_EXTENDED_TRACE_WIDTH;

/// Build the derivation AIR as a `CircuitDescriptor`.
///
/// Encodes constraints C1-C28 with 379 columns (371 standard + 8 inverse auxiliary).
/// This delegates to [`crate::dsl::derivation::derivation_circuit_descriptor()`] which
/// contains the correct, fully-specified 28-constraint implementation.
///
/// Public inputs: [state_root, derived_hash, not_after, org_id, budget]
pub fn derivation_descriptor() -> CircuitDescriptor {
    crate::dsl::derivation::derivation_circuit_descriptor()
}

/// Create a `DslCircuit` for derivation proofs.
pub fn derivation_circuit() -> DslCircuit {
    crate::dsl::derivation::derivation_dsl_circuit()
}

/// AIR name for DSL base predicate proofs.
pub const PREDICATE_DSL_AIR_NAME: &str = "dregg-predicate-dsl-v2";

/// AIR name for DSL relational predicate proofs.
pub const RELATIONAL_PREDICATE_DSL_AIR_NAME: &str = "dregg-relational-predicate-dsl-v2";

/// AIR name for the quarantined experimental compound-predicate descriptor.
///
/// The current descriptor does not bind its selected sub-results/custom gates to
/// the claimed composed result, so this name is intentionally absent from the
/// public dispatch functions below.  Direct construction remains available for
/// regression tests while it is replaced by the exact `Dregg2.Logic.PredBoolGraph`
/// compiler.
pub const COMPOUND_PREDICATE_DSL_AIR_NAME: &str = "dregg-compound-predicate-dsl-v2";

/// Returns `true` if the given AIR name matches any of the standard DSL circuits.
///
/// Used by verifiers to determine if a proof can be verified through the unified
/// DSL verification path.
pub fn is_known_dsl_air(air_name: &str) -> bool {
    matches!(
        air_name,
        EFFECT_VM_AIR_NAME
            | MERKLE_POSEIDON2_AIR_NAME
            | BLINDED_MERKLE_AIR_NAME
            | DERIVATION_AIR_NAME
            | PREDICATE_DSL_AIR_NAME
            | RELATIONAL_PREDICATE_DSL_AIR_NAME
    )
}

/// Get the appropriate `DslCircuit` for a given AIR name, or `None` if unrecognized.
///
/// This is the single dispatch point for verifying standard proofs. All standard
/// proof types (membership, blinded membership, non-revocation, derivation, predicates)
/// are handled here. Effect VM uses its own `EffectVmAir` directly.
pub fn circuit_for_air_name(air_name: &str) -> Option<DslCircuit> {
    match air_name {
        MERKLE_POSEIDON2_AIR_NAME => Some(merkle_poseidon2_circuit()),
        BLINDED_MERKLE_AIR_NAME => Some(blinded_merkle_poseidon2_circuit()),
        DERIVATION_AIR_NAME => Some(derivation_circuit()),
        PREDICATE_DSL_AIR_NAME => Some(DslCircuit::new(
            crate::dsl::predicates::predicate_descriptor(),
        )),
        RELATIONAL_PREDICATE_DSL_AIR_NAME => Some(DslCircuit::new(
            crate::dsl::predicates::relational_predicate_descriptor(),
        )),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Fail closed until the exact BoolGraph lowering replaces the incomplete
    /// compound relation.  Keeping the name constant makes accidental
    /// re-registration a visible compatibility decision rather than silently
    /// accepting old proofs again.
    #[test]
    fn incomplete_compound_predicate_is_not_publicly_dispatched() {
        assert!(!is_known_dsl_air(COMPOUND_PREDICATE_DSL_AIR_NAME));
        assert!(circuit_for_air_name(COMPOUND_PREDICATE_DSL_AIR_NAME).is_none());
    }
}
