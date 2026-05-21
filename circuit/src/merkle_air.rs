//! Merkle membership proof AIR.
//!
//! Proves: "this fact exists in the committed 4-ary Merkle tree at this root."
//!
//! Trace layout (one row per tree level, from leaf to root):
//!
//! | Column       | Description                                           |
//! |-------------|-------------------------------------------------------|
//! | 0: current  | Hash at this level (starts as leaf hash)              |
//! | 1: sib0     | First sibling hash                                    |
//! | 2: sib1     | Second sibling hash                                   |
//! | 3: sib2     | Third sibling hash                                    |
//! | 4: position | Position index at this level (0..3)                   |
//! | 5: parent   | Computed parent hash (hash_node of children in order) |
//!
//! Constraints:
//! 1. Position is valid: position * (position - 1) * (position - 2) * (position - 3) = 0
//! 2. Parent is correctly computed from children ordered by position
//! 3. Chain continuity: parent[row] = current[row + 1]
//! 4. Last row's parent = expected root (public input)
//! 5. First row's current = leaf hash (public input)

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;

/// The tree depth (number of levels from leaf to root).
pub const TREE_DEPTH: usize = 16;

/// Trace width for the Merkle AIR.
pub const MERKLE_AIR_WIDTH: usize = 6;

/// Column indices.
pub mod col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
}

/// Witness for a single Merkle membership proof.
#[derive(Clone, Debug)]
pub struct MerkleWitness {
    /// The leaf hash (as a field element).
    pub leaf_hash: BabyBear,
    /// At each level: the position index (0..3) and three sibling hashes.
    pub levels: Vec<MerkleLevelWitness>,
    /// The expected root.
    pub expected_root: BabyBear,
}

/// Witness data for one level of the Merkle tree.
#[derive(Clone, Debug)]
pub struct MerkleLevelWitness {
    /// Position of the current node among its siblings (0..3).
    pub position: u8,
    /// The three sibling hashes at this level.
    pub siblings: [BabyBear; 3],
}

/// The Merkle membership AIR.
pub struct MerkleAir {
    /// The witness for the proof.
    pub witness: MerkleWitness,
}

impl MerkleAir {
    /// Create a new Merkle AIR from a witness.
    pub fn new(witness: MerkleWitness) -> Self {
        Self { witness }
    }

    /// Compute what the parent hash should be given the current hash, position, and siblings.
    /// If position is out of range (>3), returns ZERO (constraint will catch this).
    pub fn compute_parent(current: BabyBear, position: u8, siblings: &[BabyBear; 3]) -> BabyBear {
        if position > 3 {
            return BabyBear::ZERO;
        }
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for i in 0..4u8 {
            if i == position {
                children[i as usize] = current;
            } else {
                children[i as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        hash_4_to_1(&children)
    }
}

impl Air for MerkleAir {
    fn trace_width(&self) -> usize {
        MERKLE_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        2 // leaf_hash, expected_root
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // Constraint 1: Position validity.
            // position * (position - 1) * (position - 2) * (position - 3) = 0
            Constraint {
                name: "position_valid".to_string(),
                eval: Box::new(|row, _, _| {
                    let pos = row[col::POSITION];
                    pos * (pos - BabyBear::ONE)
                        * (pos - BabyBear::new(2))
                        * (pos - BabyBear::new(3))
                }),
            },
            // Constraint 2: Parent hash is correctly computed.
            // We verify this by checking that `parent` equals the hash of children
            // arranged according to `position`.
            //
            // In a real STARK AIR, we'd expand this into Poseidon2 round constraints.
            // For the mock prover, we directly check the hash.
            Constraint {
                name: "parent_hash_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let current = row[col::CURRENT];
                    let siblings = [row[col::SIB0], row[col::SIB1], row[col::SIB2]];
                    let position = row[col::POSITION].as_u32() as u8;

                    // Skip if position is out of range (caught by position_valid)
                    if position > 3 {
                        return BabyBear::ZERO;
                    }

                    let expected_parent = MerkleAir::compute_parent(current, position, &siblings);
                    let claimed_parent = row[col::PARENT];

                    expected_parent - claimed_parent
                }),
            },
            // Constraint 3: Chain continuity — parent[row] = current[row+1].
            // Only applies to non-last rows.
            Constraint {
                name: "chain_continuity".to_string(),
                eval: Box::new(|row, next_row, _| {
                    if let Some(next) = next_row {
                        row[col::PARENT] - next[col::CURRENT]
                    } else {
                        BabyBear::ZERO // No constraint on last row
                    }
                }),
            },
        ]
    }

    fn first_row_constraints(&self) -> Vec<Constraint> {
        vec![
            // First row's current must equal the leaf hash (public input 0).
            Constraint {
                name: "leaf_hash_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[col::CURRENT] - public_inputs[0]),
            },
        ]
    }

    fn last_row_constraints(&self) -> Vec<Constraint> {
        vec![
            // Last row's parent must equal the expected root (public input 1).
            Constraint {
                name: "root_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[col::PARENT] - public_inputs[1]),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let mut trace = Vec::with_capacity(self.witness.levels.len());
        let mut current = self.witness.leaf_hash;

        for level in &self.witness.levels {
            let parent = MerkleAir::compute_parent(current, level.position, &level.siblings);

            let row = vec![
                current,
                level.siblings[0],
                level.siblings[1],
                level.siblings[2],
                BabyBear::new(level.position as u32),
                parent,
            ];
            trace.push(row);
            current = parent;
        }

        let public_inputs = vec![self.witness.leaf_hash, self.witness.expected_root];
        (trace, public_inputs)
    }
}

/// Helper: Create a Merkle witness for testing with a given depth.
pub fn create_test_witness(leaf_hash: BabyBear, depth: usize) -> MerkleWitness {
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        let parent = MerkleAir::compute_parent(current, position, &siblings);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;

    #[test]
    fn merkle_air_valid_proof() {
        let leaf = BabyBear::new(12345);
        let witness = create_test_witness(leaf, TREE_DEPTH);
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Merkle AIR should verify: {:?}",
            result.violations()
        );
    }

    #[test]
    fn merkle_air_wrong_root_fails() {
        let leaf = BabyBear::new(12345);
        let mut witness = create_test_witness(leaf, TREE_DEPTH);
        // Tamper with expected root
        witness.expected_root = BabyBear::new(99999);
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid());
    }

    #[test]
    fn merkle_air_wrong_leaf_fails() {
        let leaf = BabyBear::new(12345);
        let mut witness = create_test_witness(leaf, TREE_DEPTH);
        // Tamper with leaf hash (but keep levels the same)
        witness.leaf_hash = BabyBear::new(99999);
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid());
    }

    #[test]
    fn merkle_air_tampered_sibling_fails() {
        let leaf = BabyBear::new(12345);
        let mut witness = create_test_witness(leaf, TREE_DEPTH);
        // Tamper with a sibling at level 5
        witness.levels[5].siblings[0] = BabyBear::new(999999);
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        // This should fail because the parent hashes won't chain correctly
        assert!(!result.is_valid());
    }

    #[test]
    fn merkle_air_invalid_position_fails() {
        let leaf = BabyBear::new(42);
        let mut witness = create_test_witness(leaf, 4);
        // Set an invalid position
        witness.levels[2].position = 5; // only 0-3 are valid
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        // Should fail: position_valid constraint catches out-of-range position,
        // and chain_continuity fails because compute_parent returns ZERO for invalid pos.
        assert!(!result.is_valid());
        let has_position_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name.contains("position_valid"));
        assert!(has_position_violation);
    }

    #[test]
    fn merkle_air_short_depth() {
        // Test with a small tree (depth 4)
        let leaf = BabyBear::new(7777);
        let witness = create_test_witness(leaf, 4);
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(result.is_valid());
    }
}
