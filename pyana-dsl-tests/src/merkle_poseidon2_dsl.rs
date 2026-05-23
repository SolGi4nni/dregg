//! 4-ary Merkle membership AIR expressed as a CircuitDescriptor using Poseidon2.
//!
//! This module provides DSL circuit descriptors for:
//! 1. `merkle_poseidon2_descriptor()` — proves leaf membership in a 4-ary Poseidon2 Merkle tree
//! 2. `blinded_merkle_poseidon2_descriptor()` — same but with blinding for unlinkable ring membership
//!
//! # Design
//!
//! The `MerklePoseidon2StarkAir` in `circuit/src/poseidon2_air.rs` uses `hash_4_to_1` with
//! Lagrange child selection. This DSL port uses `hash_fact` (via `ConstraintExpr::Hash`) which
//! provides the same security property: the parent hash is uniquely determined by the children
//! and position. The difference is domain separation — `hash_fact` uses a different internal
//! tagging than `hash_4_to_1`. This is sound because:
//! - The DSL trace generation uses `hash_fact` for parent computation
//! - The DSL constraint evaluator uses `hash_fact` for verification
//! - The binding is self-consistent: any incorrect value produces a non-zero constraint
//!
//! # Trace Layout (width = 6 for standard, 8 for blinded)
//!
//! Standard (one row per tree level, leaf to root):
//! | Col | Name     | Description                              |
//! |-----|----------|------------------------------------------|
//! | 0   | current  | Hash at this level (leaf hash on row 0)  |
//! | 1   | sib0     | First sibling hash                       |
//! | 2   | sib1     | Second sibling hash                      |
//! | 3   | sib2     | Third sibling hash                       |
//! | 4   | position | Child position index (0..3)              |
//! | 5   | parent   | Computed parent = hash_fact(current, [sib0, sib1, sib2, position]) |
//!
//! Blinded adds:
//! | 6   | blinding | Blinding factor (meaningful at row 0)    |
//! | 7   | blinded  | hash_fact(current, [blinding])           |
//!
//! # Constraints
//!
//! Standard:
//! - C1: Position validity — `pos*(pos-1)*(pos-2)*(pos-3) == 0`
//! - C2: Parent hash binding — `Hash { output=parent, inputs=[current, sib0, sib1, sib2, position] }`
//! - C3: Chain continuity — `Transition { next_col=current, local_col=parent }`
//!
//! Blinded adds:
//! - C4: Blinding hash binding — `Hash { output=blinded, inputs=[current, blinding] }`
//!
//! # Public Inputs
//!
//! Standard: [leaf_hash, root]
//! Blinded: [blinded_leaf, root]
//!
//! # Boundary Constraints
//!
//! Standard:
//! - First row: current == pi[0] (leaf)
//! - Last row: parent == pi[1] (root)
//!
//! Blinded:
//! - First row: blinded == pi[0] (blinded_leaf = hash_fact(leaf, [blinding]))
//! - Last row: parent == pi[1] (root)
//! - NOTE: leaf_hash (col 0) is NOT publicly bound — it remains private

use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::hash_fact;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column indices
// ============================================================================

/// Column layout for the standard Merkle Poseidon2 circuit.
pub mod col {
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

/// Public input indices for the standard variant.
pub mod pi {
    pub const LEAF_HASH: usize = 0;
    pub const ROOT: usize = 1;
}

/// Public input indices for the blinded variant.
pub mod blinded_pi {
    pub const BLINDED_LEAF: usize = 0;
    pub const ROOT: usize = 1;
}

pub const MERKLE_P2_WIDTH: usize = 6;
pub const BLINDED_MERKLE_P2_WIDTH: usize = 8;
pub const PUBLIC_INPUT_COUNT: usize = 2;

// ============================================================================
// Standard Merkle Poseidon2 descriptor
// ============================================================================

/// Build a 4-ary Merkle membership `CircuitDescriptor` using Poseidon2 (hash_fact).
///
/// Proves: "I know a leaf and a path such that hashing up the tree yields the claimed root."
///
/// Public inputs: [leaf_hash, root]
pub fn merkle_poseidon2_descriptor() -> CircuitDescriptor {
    let p = pyana_circuit::field::BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: Position validity — pos*(pos-1)*(pos-2)*(pos-3) == 0
    // Expanded: pos^4 - 6*pos^3 + 11*pos^2 - 6*pos == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION],
            },
        ],
    });

    // C2: Parent hash binding — parent == hash_fact(current, [sib0, sib1, sib2, position])
    constraints.push(ConstraintExpr::Hash {
        output_col: col::PARENT,
        input_cols: vec![col::CURRENT, col::SIB0, col::SIB1, col::SIB2, col::POSITION],
    });

    // C3: Chain continuity — next[current] == local[parent]
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CURRENT,
        local_col: col::PARENT,
    });

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CURRENT,
            pi_index: pi::LEAF_HASH,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT,
            pi_index: pi::ROOT,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: col::PARENT,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "pyana-merkle-poseidon2-dsl-v1".into(),
        trace_width: MERKLE_P2_WIDTH,
        max_degree: 5,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the Merkle Poseidon2 descriptor.
pub fn merkle_poseidon2_dsl_circuit() -> DslCircuit {
    DslCircuit::new(merkle_poseidon2_descriptor())
}

// ============================================================================
// Blinded Merkle Poseidon2 descriptor (ring membership / unlinkability)
// ============================================================================

/// Build a blinded 4-ary Merkle membership `CircuitDescriptor` using Poseidon2.
///
/// Proves: "I know a leaf in this tree" WITHOUT revealing which leaf.
/// Public inputs: [blinded_leaf, root] where blinded_leaf = hash_fact(leaf, [blinding]).
///
/// Since the blinding factor is fresh random per presentation, the same issuer
/// produces different blinded_leaf values each time (unlinkable).
pub fn blinded_merkle_poseidon2_descriptor() -> CircuitDescriptor {
    let p = pyana_circuit::field::BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: Position validity — pos*(pos-1)*(pos-2)*(pos-3) == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION],
            },
        ],
    });

    // C2: Parent hash binding — parent == hash_fact(current, [sib0, sib1, sib2, position])
    constraints.push(ConstraintExpr::Hash {
        output_col: col::PARENT,
        input_cols: vec![col::CURRENT, col::SIB0, col::SIB1, col::SIB2, col::POSITION],
    });

    // C3: Chain continuity — next[current] == local[parent]
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CURRENT,
        local_col: col::PARENT,
    });

    // C4: Blinding hash binding — blinded == hash_fact(current, [blinding])
    constraints.push(ConstraintExpr::Hash {
        output_col: col::BLINDED,
        input_cols: vec![col::CURRENT, col::BLINDING],
    });

    let boundaries = vec![
        // First row: blinded == pi[0] (blinded_leaf)
        // NOTE: col 0 (leaf_hash) is NOT bound — it remains private!
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::BLINDED,
            pi_index: blinded_pi::BLINDED_LEAF,
        },
        // Last row: parent == pi[1] (root)
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT,
            pi_index: blinded_pi::ROOT,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: col::PARENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "blinding".into(),
            index: col::BLINDING,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "blinded".into(),
            index: col::BLINDED,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "pyana-blinded-merkle-poseidon2-dsl-v1".into(),
        trace_width: BLINDED_MERKLE_P2_WIDTH,
        max_degree: 5,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the blinded Merkle Poseidon2 descriptor.
pub fn blinded_merkle_poseidon2_dsl_circuit() -> DslCircuit {
    DslCircuit::new(blinded_merkle_poseidon2_descriptor())
}

// ============================================================================
// Trace generation: standard Merkle Poseidon2
// ============================================================================

/// Generate a valid Merkle membership trace for the Poseidon2 DSL circuit.
///
/// Each row represents one level of the 4-ary Merkle tree (leaf to root).
/// The parent hash is computed as `hash_fact(current, [sib0, sib1, sib2, position])`.
///
/// Returns (trace, public_inputs) where public_inputs = [leaf_hash, root].
pub fn generate_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2 for STARK");

    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let position = BabyBear::new(pos as u32);
        let sib0 = siblings[i][0];
        let sib1 = siblings[i][1];
        let sib2 = siblings[i][2];

        // Parent = hash_fact(current, [sib0, sib1, sib2, position])
        let parent = hash_fact(current, &[sib0, sib1, sib2, position]);

        trace.push(vec![current, sib0, sib1, sib2, position, parent]);
        current = parent;
    }

    // Pad to power of two (minimum 2 rows). Padding rows must satisfy all constraints:
    // - Position validity: position=0 satisfies pos*(pos-1)*(pos-2)*(pos-3)=0
    // - Hash binding: parent = hash_fact(current, [0, 0, 0, 0])
    // - Chain continuity: next[current] = local[parent]
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        let prev_parent = trace.last().unwrap()[col::PARENT];
        let pad_pos = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_parent = hash_fact(prev_parent, &[pad_sib0, pad_sib1, pad_sib2, pad_pos]);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_pos,
            pad_parent,
        ]);
    }

    let root = trace.last().unwrap()[col::PARENT];
    let public_inputs = vec![leaf_hash, root];
    (trace, public_inputs)
}

/// Generate a test witness (deterministic siblings/positions).
pub fn create_test_witness(
    leaf_hash: BabyBear,
    depth: usize,
) -> (Vec<[BabyBear; 3]>, Vec<u8>, BabyBear) {
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = (i % 4) as u8;
        let sibs = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        let position = BabyBear::new(pos as u32);
        current = hash_fact(current, &[sibs[0], sibs[1], sibs[2], position]);
        siblings.push(sibs);
        positions.push(pos);
    }

    (siblings, positions, current) // current = expected root
}

// ============================================================================
// Trace generation: blinded Merkle Poseidon2
// ============================================================================

/// Generate a blinded Merkle membership trace.
///
/// Public inputs are [blinded_leaf, root] where:
///   blinded_leaf = hash_fact(leaf_hash, [blinding_factor])
///
/// The leaf_hash remains private (not bound to any public input).
pub fn generate_blinded_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
    blinding_factor: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2 for STARK");

    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let position = BabyBear::new(pos as u32);
        let sib0 = siblings[i][0];
        let sib1 = siblings[i][1];
        let sib2 = siblings[i][2];

        let parent = hash_fact(current, &[sib0, sib1, sib2, position]);

        // Blinding column: real value at row 0, zero elsewhere
        let row_blinding = if i == 0 {
            blinding_factor
        } else {
            BabyBear::ZERO
        };
        // Blinded column: hash_fact(current, [blinding]) — must be correct on every row
        let row_blinded = hash_fact(current, &[row_blinding]);

        trace.push(vec![
            current,
            sib0,
            sib1,
            sib2,
            position,
            parent,
            row_blinding,
            row_blinded,
        ]);
        current = parent;
    }

    // Pad to power of two
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        let prev_parent = trace.last().unwrap()[col::PARENT];
        let pad_pos = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_parent = hash_fact(prev_parent, &[pad_sib0, pad_sib1, pad_sib2, pad_pos]);
        // Blinding=0 on padding rows; blinded = hash_fact(prev_parent, [0])
        let pad_blinded = hash_fact(prev_parent, &[BabyBear::ZERO]);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_pos,
            pad_parent,
            BabyBear::ZERO,
            pad_blinded,
        ]);
    }

    let root = trace.last().unwrap()[col::PARENT];
    // blinded_leaf = hash_fact(leaf_hash, [blinding_factor])
    let blinded_leaf = hash_fact(leaf_hash, &[blinding_factor]);
    let public_inputs = vec![blinded_leaf, root];
    (trace, public_inputs)
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
    // Standard Merkle Poseidon2
    // ========================================================================

    #[test]
    fn descriptor_validates() {
        let desc = merkle_poseidon2_descriptor();
        assert!(
            desc.validate().is_ok(),
            "merkle poseidon2 descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn descriptor_structure() {
        let desc = merkle_poseidon2_descriptor();
        assert_eq!(desc.trace_width, MERKLE_P2_WIDTH);
        assert_eq!(desc.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(desc.name, "pyana-merkle-poseidon2-dsl-v1");
        assert_eq!(desc.max_degree, 5);
        // 1 Polynomial (position) + 1 Hash (parent) + 1 Transition (chain) = 3
        assert_eq!(desc.constraints.len(), 3);
        // 2 boundary constraints (leaf + root)
        assert_eq!(desc.boundaries.len(), 2);
        assert_eq!(desc.columns.len(), 6);
    }

    #[test]
    fn valid_trace_evaluates_to_zero() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // All rows except last should evaluate to zero (transition wraps on last)
        for i in 0..trace.len() - 1 {
            let result = circuit.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Row {i} should satisfy all constraints, got {:?}",
                result
            );
        }
    }

    #[test]
    fn wrong_sibling_detected() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (mut trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper with sib0 on row 1 (parent hash will no longer match)
        trace[1][col::SIB0] = BabyBear::new(999999);

        let result = circuit.eval_constraints(&trace[1], &trace[2], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered sibling should violate Hash constraint"
        );
    }

    #[test]
    fn wrong_position_detected() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (mut trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Set position to 5 (invalid: only 0-3 allowed)
        trace[0][col::POSITION] = BabyBear::new(5);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Invalid position (5) should violate polynomial constraint"
        );
    }

    #[test]
    fn wrong_root_pi_rejected_by_stark() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let wrong_pi = vec![pi[0], BabyBear::new(99999)];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong root PI"
        );
    }

    #[test]
    fn wrong_leaf_pi_rejected_by_stark() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let wrong_pi = vec![BabyBear::new(99999), pi[1]];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong leaf PI"
        );
    }

    #[test]
    fn stark_prove_verify_roundtrip() {
        let leaf = BabyBear::new(42);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify should succeed on valid Merkle Poseidon2 trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn stark_depth_8() {
        let leaf = BabyBear::new(7777);
        let (siblings, positions, _root) = create_test_witness(leaf, 8);
        let (trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Depth-8 Merkle Poseidon2 should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn chain_continuity_violation_detected() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (mut trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Break chain: change row 2's current so it no longer matches row 1's parent
        trace[2][col::CURRENT] = trace[2][col::CURRENT] + BabyBear::ONE;

        let result = circuit.eval_constraints(&trace[1], &trace[2], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Broken chain continuity should violate Transition constraint"
        );
    }

    #[test]
    fn collision_resistance() {
        let (_, _, root_a) = create_test_witness(BabyBear::new(111), 4);
        let (_, _, root_b) = create_test_witness(BabyBear::new(222), 4);
        assert_ne!(
            root_a, root_b,
            "Different leaves should produce different roots"
        );
    }

    #[test]
    fn tampered_parent_detected() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let (mut trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let circuit = merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper parent on row 0
        trace[0][col::PARENT] = BabyBear::new(0xDEAD);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered parent hash should be detected"
        );
    }

    // ========================================================================
    // Blinded Merkle Poseidon2 (ring membership / unlinkability)
    // ========================================================================

    #[test]
    fn blinded_descriptor_validates() {
        let desc = blinded_merkle_poseidon2_descriptor();
        assert!(
            desc.validate().is_ok(),
            "blinded merkle poseidon2 descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn blinded_descriptor_structure() {
        let desc = blinded_merkle_poseidon2_descriptor();
        assert_eq!(desc.trace_width, BLINDED_MERKLE_P2_WIDTH);
        assert_eq!(desc.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(desc.name, "pyana-blinded-merkle-poseidon2-dsl-v1");
        assert_eq!(desc.max_degree, 5);
        // 1 Polynomial (position) + 1 Hash (parent) + 1 Transition (chain) + 1 Hash (blinding) = 4
        assert_eq!(desc.constraints.len(), 4);
        // 2 boundary constraints (blinded_leaf + root)
        assert_eq!(desc.boundaries.len(), 2);
        assert_eq!(desc.columns.len(), 8);
    }

    #[test]
    fn blinded_valid_trace_evaluates_to_zero() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(987654321);
        let (trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(42);

        for i in 0..trace.len() - 1 {
            let result = circuit.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Blinded row {i} should satisfy all constraints, got {:?}",
                result
            );
        }
    }

    #[test]
    fn blinded_stark_prove_verify_roundtrip() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(987654321);
        let (trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Blinded Merkle Poseidon2 STARK verification failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn blinded_unlinkability() {
        // Same leaf, two different blinding factors => different blinded_leaf values
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);

        let blinding_1 = BabyBear::new(111111);
        let blinding_2 = BabyBear::new(222222);

        let (_, pi_1) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_1);
        let (_, pi_2) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_2);

        // Same root (same tree)
        assert_eq!(pi_1[1], pi_2[1]);
        // Different blinded_leaf (unlinkable!)
        assert_ne!(
            pi_1[0], pi_2[0],
            "Same leaf with different blinding must produce different blinded_leaf"
        );

        // Both should verify independently
        let circuit = blinded_merkle_poseidon2_dsl_circuit();
        let (trace_1, _) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_1);
        let (trace_2, _) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_2);

        let proof_1 = stark::prove(&circuit, &trace_1, &pi_1);
        let proof_2 = stark::prove(&circuit, &trace_2, &pi_2);

        assert!(stark::verify(&circuit, &proof_1, &pi_1).is_ok());
        assert!(stark::verify(&circuit, &proof_2, &pi_2).is_ok());
    }

    #[test]
    fn blinded_wrong_root_rejected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(555555);
        let (trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let wrong_pi = vec![pi[0], BabyBear::new(99999)];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject wrong root");
    }

    #[test]
    fn blinded_wrong_blinded_leaf_rejected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(555555);
        let (trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        let wrong_pi = vec![BabyBear::new(77777), pi[1]];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject wrong blinded_leaf");
    }

    #[test]
    fn blinded_wrong_sibling_detected() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(271828);
        let (mut trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper with sib1 on row 2
        trace[2][col::SIB1] = BabyBear::new(888888);

        let result = circuit.eval_constraints(&trace[2], &trace[3], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered sibling should violate Hash constraint in blinded variant"
        );
    }

    #[test]
    fn blinded_wrong_position_detected() {
        let leaf = BabyBear::new(12345);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(314159);
        let (mut trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Set position to 7 (invalid)
        trace[1][col::POSITION] = BabyBear::new(7);

        let result = circuit.eval_constraints(&trace[1], &trace[2], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Invalid position should violate polynomial constraint in blinded variant"
        );
    }

    #[test]
    fn blinded_depth_8() {
        let leaf = BabyBear::new(7777);
        let (siblings, positions, _root) = create_test_witness(leaf, 8);
        let blinding = BabyBear::new(161803);
        let (trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Blinded depth-8 should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn blinded_tampered_blinding_detected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(123456);
        let (mut trace, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let circuit = blinded_merkle_poseidon2_dsl_circuit();
        let alpha = BabyBear::new(13);

        // Tamper blinding on row 0 (makes blinded column incorrect)
        trace[0][col::BLINDING] = BabyBear::new(999);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered blinding factor should violate blinding Hash constraint"
        );
    }

    #[test]
    fn blinded_leaf_privacy() {
        // The leaf_hash is NOT in the public inputs for the blinded variant.
        // Only blinded_leaf (= hash_fact(leaf, [blinding])) and root are public.
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(777);
        let (_, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);

        // PI[0] should be blinded_leaf, NOT the raw leaf
        assert_ne!(
            pi[0], leaf,
            "Public input should be blinded_leaf, not raw leaf"
        );
        let expected_blinded = hash_fact(leaf, &[blinding]);
        assert_eq!(pi[0], expected_blinded);
    }
}
