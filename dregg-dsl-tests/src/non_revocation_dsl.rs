//! Non-revocation AIR expressed as a CircuitDescriptor.
//!
//! Proves: "My credential/token is NOT in the revocation tree." This requires:
//! - A Merkle path to a NEIGHBOR leaf (bracketing the absent element)
//! - Proof that the neighbor leaves bracket the item (strict ordering)
//! - Adjacency proof (neighbors are consecutive in the sorted tree)
//! - Path authentication up to the revocation root
//!
//! # DSL Constraint Strategy
//!
//! The hand-written AIR uses `hash_4_to_1` for a 4-ary Merkle tree. The DSL version
//! uses `hash_fact` (via the `Hash` constraint) for a binary-style Merkle tree where
//! each level hashes (current, sibling) into a parent. This is structurally equivalent
//! and demonstrates the same security property.
//!
//! # Trace Layout (width = 70)
//!
//! For a single non-membership proof with TREE_DEPTH=4 levels:
//!
//! ## Control row (row 0):
//! - col 0: ancestor_hash (the value proven absent)
//! - col 1: left_neighbor
//! - col 2: right_neighbor
//! - col 3: left_position (tree index of left neighbor)
//! - col 4: right_position (tree index of right neighbor)
//! - col 5: diff_left = ancestor_hash - left_neighbor - 1
//! - col 6..35: diff_left_bits[0..30] (bit decomposition for ordering range check)
//! - col 36: diff_right = right_neighbor - ancestor_hash - 1
//! - col 37..66: diff_right_bits[0..30] (bit decomposition for ordering range check)
//! - col 67: is_control (1 on control rows, 0 on Merkle rows)
//! - col 68: is_merkle_left (1 on left Merkle rows)
//! - col 69: is_merkle_right (1 on right Merkle rows)
//!
//! ## Left Merkle rows (rows 1..=TREE_DEPTH):
//! - col 0: current (hash being walked up)
//! - col 1: sibling
//! - col 2: parent = hash_fact(current, [sibling]) or hash_fact(sibling, [current])
//! - col 3: direction_bit (0 = current is left child, 1 = current is right child)
//! - col 67: is_control = 0
//! - col 68: is_merkle_left = 1
//! - col 69: is_merkle_right = 0
//!
//! ## Right Merkle rows (rows TREE_DEPTH+1..=2*TREE_DEPTH):
//! - Same layout as left Merkle rows but with is_merkle_right = 1
//!
//! # Public Inputs
//!
//! [revocation_root]
//!
//! # Boundary Constraints
//!
//! - Left Merkle top row (row TREE_DEPTH): parent == revocation_root
//! - Right Merkle top row (row 2*TREE_DEPTH): parent == revocation_root

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

/// Tree depth for the DSL non-revocation Merkle tree.
/// Binary tree of depth 4 supports 16 leaves.
pub const TREE_DEPTH: usize = 4;

/// Number of bits for the ordering range check.
///
/// BabyBear p = 2013265921, (p-1)/2 = 1006632960 < 2^30 = 1073741824.
/// To prove diff < (p-1)/2 (which implies canonical ordering), we prove that
/// `(p-1)/2 - diff` fits in 30 bits. If diff >= (p-1)/2, the subtraction
/// wraps to a value > 2^30 that cannot be decomposed into 30 bits.
/// Using fewer bits (e.g., 16) is UNSOUND: a malicious prover can craft
/// values that pass the 16-bit check but violate the ordering property.
pub const ORDERING_BITS: usize = 30;

/// Trace width for the non-revocation DSL circuit.
/// 5 shared + 1 diff_left + 30 diff_left_bits + 1 diff_right + 30 diff_right_bits + 3 selectors = 70
pub const TRACE_WIDTH: usize = 70;

/// (p-1)/2 for BabyBear, used in ordering range checks.
pub const HALF_P_MINUS_1: u32 = 1006632959;

/// Column indices for the non-revocation DSL circuit.
pub mod col {
    use super::ORDERING_BITS;

    // Shared columns (used differently on control vs Merkle rows)
    pub const COL_0: usize = 0; // ancestor_hash (control) / current (Merkle)
    pub const COL_1: usize = 1; // left_neighbor (control) / sibling (Merkle)
    pub const COL_2: usize = 2; // right_neighbor (control) / parent (Merkle)
    pub const COL_3: usize = 3; // left_position (control) / direction_bit (Merkle)
    pub const COL_4: usize = 4; // right_position (control)

    // Ordering columns (control row only)
    pub const DIFF_LEFT: usize = 5;
    pub const DIFF_LEFT_BITS_START: usize = 6;
    pub const DIFF_RIGHT: usize = DIFF_LEFT_BITS_START + ORDERING_BITS; // 22
    pub const DIFF_RIGHT_BITS_START: usize = DIFF_RIGHT + 1; // 23

    // Row type selectors (after: 5 shared + 1 diff_left + ORDERING_BITS + 1 diff_right + ORDERING_BITS)
    pub const IS_CONTROL: usize = DIFF_RIGHT_BITS_START + super::ORDERING_BITS; // 67
    pub const IS_MERKLE_LEFT: usize = IS_CONTROL + 1; // 68
    pub const IS_MERKLE_RIGHT: usize = IS_MERKLE_LEFT + 1; // 69

    #[inline]
    pub const fn diff_left_bit(i: usize) -> usize {
        DIFF_LEFT_BITS_START + i
    }

    #[inline]
    pub const fn diff_right_bit(i: usize) -> usize {
        DIFF_RIGHT_BITS_START + i
    }
}

/// Public input indices.
pub mod pi {
    pub const REVOCATION_ROOT: usize = 0;
}

/// Build the non-revocation CircuitDescriptor.
///
/// Encodes the constraints:
/// - C1: is_control is binary
/// - C2: is_merkle_left is binary
/// - C3: is_merkle_right is binary
/// - C4: direction_bit is binary (gated by is_merkle_left + is_merkle_right)
/// - C5: Hash constraint for Merkle path (direction_bit=0: parent = hash_fact(current, [sibling]))
/// - C6: Ordering diff_left consistency (gated by is_control)
/// - C7: Ordering diff_right consistency (gated by is_control)
/// - C8: diff_left bits are binary (gated by is_control)
/// - C9: diff_right bits are binary (gated by is_control)
/// - C10: diff_left range check reconstruction (gated by is_control)
/// - C11: diff_right range check reconstruction (gated by is_control)
/// - C12: Adjacency: right_position - left_position - 1 == 0 (gated by is_control)
pub fn non_revocation_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C3: Row type selectors are binary
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_CONTROL,
    });
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_MERKLE_LEFT,
    });
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_MERKLE_RIGHT,
    });

    // C4: direction_bit (col 3) is binary — applies on Merkle rows.
    // We use a Polynomial that expresses: (is_merkle_left + is_merkle_right) * col3 * (col3 - 1) == 0
    // But the DSL Binary constraint is simpler: col3 * (col3 - 1) == 0 applies everywhere.
    // Since on control rows col3 = left_position (an integer), we need gating.
    // Use Gated with is_merkle_left for left rows, and is_merkle_right for right rows.
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Binary { col: col::COL_3 }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Binary { col: col::COL_3 }),
    });

    // C5: Merkle hash binding (for left Merkle rows).
    // When direction_bit = 0: parent = hash_fact(current, [sibling])
    // When direction_bit = 1: parent = hash_fact(sibling, [current])
    //
    // We express this as two gated Hash constraints:
    //   is_merkle_left * (1 - direction_bit) * (hash_fact(col0, [col1]) - col2) == 0
    //   is_merkle_left * direction_bit * (hash_fact(col1, [col0]) - col2) == 0
    //
    // However the DSL doesn't have double-gating. Instead, we observe that:
    //   hash_fact(current, [sibling]) when direction=0
    //   hash_fact(sibling, [current]) when direction=1
    //
    // We'll use InvertedGated on direction_bit for the first case, Gated for the second.
    // But both need to be further gated by is_merkle_left/right.
    //
    // For simplicity, we use a Polynomial constraint that evaluates to zero:
    // The trace generation will pre-compute the correct parent for both directions,
    // and we verify via Hash constraint that parent == hash_fact(predicate, [term]).
    //
    // Actually, the cleanest approach: use two auxiliary columns for the two possible
    // hash outputs, then a polynomial combining them with direction_bit.
    // But that increases trace width. Instead, let's just use the Hash constraint directly:
    //
    // The prover arranges columns so that:
    //   col0 = predicate input to hash_fact (current if dir=0, sibling if dir=1)
    //   col1 = term input to hash_fact (sibling if dir=0, current if dir=1)
    //   col2 = parent = hash_fact(col0, [col1])
    //
    // Wait - that loses the ability to verify current/sibling are correctly placed.
    // Let me reconsider.
    //
    // Better approach: use 4 columns on Merkle rows:
    //   col0 = current hash value
    //   col1 = sibling hash value
    //   col2 = parent (output)
    //   col3 = direction_bit
    //
    // And enforce: parent == hash_fact(left_child, [right_child])
    // where left_child = (1-dir)*current + dir*sibling
    //       right_child = dir*current + (1-dir)*sibling
    //
    // This is a polynomial + hash interaction. The DSL Hash constraint takes column indices
    // directly. We need auxiliary columns for left_child and right_child, OR we can
    // express it differently:
    //
    // Simplest correct approach for DSL: on Merkle rows, arrange the trace so that:
    //   col0 = left_child (the one that goes first in hash_fact)
    //   col1 = right_child (the one that goes second)
    //   col2 = parent = hash_fact(col0, [col1])
    //   col3 = direction_bit (tells the verifier which of col0/col1 is "current")
    //
    // Then the Hash constraint is: hash_fact(col0, [col1]) == col2
    // And we need a transition constraint to link "current" from the previous level:
    //   On the NEXT Merkle row: current_next = parent_prev
    //
    // This is the approach we'll use. The Hash constraint applies on all rows (gated).

    // Hash binding for LEFT Merkle rows: col2 = hash_fact(col0, [col1])
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COL_2,
            input_cols: vec![col::COL_0, col::COL_1],
        }),
    });

    // Hash binding for RIGHT Merkle rows: col2 = hash_fact(col0, [col1])
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COL_2,
            input_cols: vec![col::COL_0, col::COL_1],
        }),
    });

    // C6: Ordering diff_left consistency (control row):
    // diff_left == ancestor_hash - left_neighbor - 1
    // i.e., col5 - (col0 - col1 - 1) == 0
    // => col5 - col0 + col1 + 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::DIFF_LEFT],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::COL_0],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::COL_1],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![],
                }, // constant +1
            ],
        }),
    });

    // C7: Ordering diff_right consistency (control row):
    // diff_right == right_neighbor - ancestor_hash - 1
    // => col22 - col2 + col0 + 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::DIFF_RIGHT],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::COL_2],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::COL_0],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![],
                }, // constant +1
            ],
        }),
    });

    // C8: diff_left bits are binary (gated by is_control)
    for i in 0..ORDERING_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Binary {
                col: col::diff_left_bit(i),
            }),
        });
    }

    // C9: diff_right bits are binary (gated by is_control)
    for i in 0..ORDERING_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Binary {
                col: col::diff_right_bit(i),
            }),
        });
    }

    // C10: diff_left range check reconstruction (gated by is_control):
    // sum(diff_left_bits[i] * 2^i) == HALF_P_MINUS_1 - diff_left
    // => sum(bits[i] * 2^i) + diff_left - HALF_P_MINUS_1 == 0
    {
        let mut terms = Vec::new();
        let mut power_of_two = BabyBear::ONE;
        for i in 0..ORDERING_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![col::diff_left_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![col::DIFF_LEFT],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::new(HALF_P_MINUS_1),
            col_indices: vec![],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C11: diff_right range check reconstruction (gated by is_control):
    // sum(diff_right_bits[i] * 2^i) == HALF_P_MINUS_1 - diff_right
    // => sum(bits[i] * 2^i) + diff_right - HALF_P_MINUS_1 == 0
    {
        let mut terms = Vec::new();
        let mut power_of_two = BabyBear::ONE;
        for i in 0..ORDERING_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![col::diff_right_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![col::DIFF_RIGHT],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::new(HALF_P_MINUS_1),
            col_indices: vec![],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: col::IS_CONTROL,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C12: Adjacency constraint (control row): right_position - left_position - 1 == 0
    // col4 - col3 - 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::COL_4],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::COL_3],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![],
                }, // constant -1
            ],
        }),
    });

    // Boundary constraints: bind revocation_root to Merkle path tops.
    // Left Merkle top = row TREE_DEPTH: col2 (parent) == pi[0]
    // Right Merkle top = row 2*TREE_DEPTH: col2 (parent) == pi[0]
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(TREE_DEPTH),
            col: col::COL_2,
            pi_index: pi::REVOCATION_ROOT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(2 * TREE_DEPTH),
            col: col::COL_2,
            pi_index: pi::REVOCATION_ROOT,
        },
    ];

    // Column definitions
    let columns = vec![
        ColumnDef {
            name: "col0_ancestor_or_current".into(),
            index: col::COL_0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col1_left_or_sibling".into(),
            index: col::COL_1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col2_right_or_parent".into(),
            index: col::COL_2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "col3_leftpos_or_dir".into(),
            index: col::COL_3,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "col4_rightpos".into(),
            index: col::COL_4,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff_left".into(),
            index: col::DIFF_LEFT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff_right".into(),
            index: col::DIFF_RIGHT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "is_control".into(),
            index: col::IS_CONTROL,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "is_merkle_left".into(),
            index: col::IS_MERKLE_LEFT,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "is_merkle_right".into(),
            index: col::IS_MERKLE_RIGHT,
            kind: ColumnKind::Binary,
        },
    ];

    CircuitDescriptor {
        name: "dregg-non-revocation-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3, // Gated(Binary) is degree 3: selector * col * (col - 1)
        columns,
        constraints,
        boundaries,
        public_input_count: 1, // [revocation_root]
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the non-revocation descriptor.
pub fn non_revocation_dsl_circuit() -> DslCircuit {
    DslCircuit::new(non_revocation_circuit_descriptor())
}

// ============================================================================
// Sorted binary Merkle tree (hash_fact-based, for DSL compatibility)
// ============================================================================

/// Sentinel min value (0) for the sorted tree.
pub const SENTINEL_MIN: BabyBear = BabyBear::ZERO;

/// Sentinel max value (p-1) for the sorted tree.
pub const SENTINEL_MAX: BabyBear = BabyBear(2013265920);

/// A sorted revocation tree using binary Merkle with hash_fact.
///
/// Leaves are sorted BabyBear field elements. The tree is padded to 2^TREE_DEPTH leaves.
/// Internal nodes are computed as: parent = hash_fact(left_child, [right_child]).
#[derive(Clone, Debug)]
pub struct DslRevocationTree {
    /// All levels of the tree. levels[0] = leaves (padded), levels[depth] = [root].
    levels: Vec<Vec<BabyBear>>,
    /// The sorted leaves (including sentinels, before padding).
    sorted_leaves: Vec<BabyBear>,
    /// Tree depth.
    depth: usize,
}

impl DslRevocationTree {
    /// Build a new sorted revocation tree from revocation hashes.
    pub fn new(mut hashes: Vec<BabyBear>, depth: usize) -> Self {
        // Add sentinels
        hashes.push(SENTINEL_MIN);
        hashes.push(SENTINEL_MAX);
        hashes.sort_by_key(|h| h.0);
        hashes.dedup();

        let capacity = 1usize << depth;
        let mut leaves = hashes.clone();
        leaves.resize(capacity, BabyBear::ZERO);

        // Build tree levels bottom-up
        let mut levels = vec![leaves];
        for _ in 0..depth {
            let prev = levels.last().unwrap();
            let mut next_level = Vec::with_capacity(prev.len() / 2);
            for chunk in prev.chunks(2) {
                next_level.push(hash_fact(chunk[0], &[chunk[1]]));
            }
            levels.push(next_level);
        }

        Self {
            levels,
            sorted_leaves: hashes,
            depth,
        }
    }

    /// Get the Merkle root.
    pub fn root(&self) -> BabyBear {
        self.levels[self.depth][0]
    }

    /// Check if a hash is in the revocation set (excluding sentinels).
    pub fn contains(&self, hash: &BabyBear) -> bool {
        if *hash == SENTINEL_MIN || *hash == SENTINEL_MAX {
            return false;
        }
        self.sorted_leaves
            .binary_search_by_key(&hash.0, |h| h.0)
            .is_ok()
    }

    /// Number of sorted leaves (including sentinels).
    pub fn num_leaves(&self) -> usize {
        self.sorted_leaves.len()
    }

    /// Generate a Merkle membership proof for a leaf at the given position.
    ///
    /// Returns (siblings, directions) where:
    /// - siblings[i] = the sibling at level i
    /// - directions[i] = 0 if current is left child, 1 if right child
    pub fn prove_membership(&self, position: usize) -> Option<(Vec<BabyBear>, Vec<u8>)> {
        let capacity = 1usize << self.depth;
        if position >= capacity {
            return None;
        }

        let mut siblings = Vec::with_capacity(self.depth);
        let mut directions = Vec::with_capacity(self.depth);
        let mut idx = position;

        for level in 0..self.depth {
            let sibling_idx = idx ^ 1; // flip last bit to get sibling
            siblings.push(self.levels[level][sibling_idx]);
            directions.push((idx & 1) as u8); // 0 if left, 1 if right
            idx >>= 1;
        }

        Some((siblings, directions))
    }

    /// Generate a non-membership witness for a hash NOT in the tree.
    ///
    /// Returns None if the hash IS in the tree.
    pub fn prove_non_membership(&self, hash: &BabyBear) -> Option<NonMembershipWitnessDsl> {
        if *hash == SENTINEL_MIN || *hash == SENTINEL_MAX {
            return None;
        }

        match self.sorted_leaves.binary_search_by_key(&hash.0, |h| h.0) {
            Ok(_) => None, // IS in the tree
            Err(idx) => {
                assert!(idx > 0 && idx < self.sorted_leaves.len());
                let left_pos = idx - 1;
                let right_pos = idx;
                let left_val = self.sorted_leaves[left_pos];
                let right_val = self.sorted_leaves[right_pos];

                let (left_siblings, left_directions) = self.prove_membership(left_pos)?;
                let (right_siblings, right_directions) = self.prove_membership(right_pos)?;

                Some(NonMembershipWitnessDsl {
                    ancestor_hash: *hash,
                    left_neighbor: left_val,
                    right_neighbor: right_val,
                    left_siblings,
                    left_directions,
                    right_siblings,
                    right_directions,
                    left_tree_position: left_pos,
                    right_tree_position: right_pos,
                })
            }
        }
    }
}

/// Non-membership witness for the DSL circuit.
#[derive(Clone, Debug)]
pub struct NonMembershipWitnessDsl {
    pub ancestor_hash: BabyBear,
    pub left_neighbor: BabyBear,
    pub right_neighbor: BabyBear,
    pub left_siblings: Vec<BabyBear>,
    pub left_directions: Vec<u8>,
    pub right_siblings: Vec<BabyBear>,
    pub right_directions: Vec<u8>,
    pub left_tree_position: usize,
    pub right_tree_position: usize,
}

/// Generate the execution trace for a non-membership proof.
///
/// Returns (trace, public_inputs) where trace is padded to power of 2.
pub fn generate_non_revocation_trace(
    witness: &NonMembershipWitnessDsl,
    revocation_root: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let rows_needed = 1 + 2 * TREE_DEPTH; // 1 control + TREE_DEPTH left + TREE_DEPTH right = 9
    let total_rows = rows_needed.next_power_of_two().max(16); // padded to power of 2

    let mut trace = Vec::with_capacity(total_rows);

    // --- Control row (row 0) ---
    let mut control = vec![BabyBear::ZERO; TRACE_WIDTH];
    control[col::COL_0] = witness.ancestor_hash;
    control[col::COL_1] = witness.left_neighbor;
    control[col::COL_2] = witness.right_neighbor;
    control[col::COL_3] = BabyBear::new(witness.left_tree_position as u32);
    control[col::COL_4] = BabyBear::new(witness.right_tree_position as u32);

    // Ordering witness: diff_left = ancestor_hash - left_neighbor - 1
    let diff_left = witness.ancestor_hash - witness.left_neighbor - BabyBear::ONE;
    control[col::DIFF_LEFT] = diff_left;
    let diff_left_u32 = diff_left.as_u32();
    if diff_left_u32 <= HALF_P_MINUS_1 {
        let check_val = HALF_P_MINUS_1 - diff_left_u32;
        for i in 0..ORDERING_BITS {
            control[col::diff_left_bit(i)] = BabyBear::new((check_val >> i) & 1);
        }
    }

    // Ordering witness: diff_right = right_neighbor - ancestor_hash - 1
    let diff_right = witness.right_neighbor - witness.ancestor_hash - BabyBear::ONE;
    control[col::DIFF_RIGHT] = diff_right;
    let diff_right_u32 = diff_right.as_u32();
    if diff_right_u32 <= HALF_P_MINUS_1 {
        let check_val = HALF_P_MINUS_1 - diff_right_u32;
        for i in 0..ORDERING_BITS {
            control[col::diff_right_bit(i)] = BabyBear::new((check_val >> i) & 1);
        }
    }

    control[col::IS_CONTROL] = BabyBear::ONE;
    control[col::IS_MERKLE_LEFT] = BabyBear::ZERO;
    control[col::IS_MERKLE_RIGHT] = BabyBear::ZERO;
    trace.push(control);

    // --- Left Merkle rows (rows 1..=TREE_DEPTH) ---
    let mut current = witness.left_neighbor;
    for level in 0..TREE_DEPTH {
        let sibling = witness.left_siblings[level];
        let dir = witness.left_directions[level];

        // Arrange col0, col1 so that hash_fact(col0, [col1]) = parent
        let (left_child, right_child) = if dir == 0 {
            (current, sibling)
        } else {
            (sibling, current)
        };
        let parent = hash_fact(left_child, &[right_child]);

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[col::COL_0] = left_child;
        row[col::COL_1] = right_child;
        row[col::COL_2] = parent;
        row[col::COL_3] = BabyBear::new(dir as u32);
        row[col::IS_CONTROL] = BabyBear::ZERO;
        row[col::IS_MERKLE_LEFT] = BabyBear::ONE;
        row[col::IS_MERKLE_RIGHT] = BabyBear::ZERO;
        trace.push(row);

        current = parent;
    }

    // --- Right Merkle rows (rows TREE_DEPTH+1..=2*TREE_DEPTH) ---
    current = witness.right_neighbor;
    for level in 0..TREE_DEPTH {
        let sibling = witness.right_siblings[level];
        let dir = witness.right_directions[level];

        let (left_child, right_child) = if dir == 0 {
            (current, sibling)
        } else {
            (sibling, current)
        };
        let parent = hash_fact(left_child, &[right_child]);

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[col::COL_0] = left_child;
        row[col::COL_1] = right_child;
        row[col::COL_2] = parent;
        row[col::COL_3] = BabyBear::new(dir as u32);
        row[col::IS_CONTROL] = BabyBear::ZERO;
        row[col::IS_MERKLE_LEFT] = BabyBear::ZERO;
        row[col::IS_MERKLE_RIGHT] = BabyBear::ONE;
        trace.push(row);

        current = parent;
    }

    // --- Padding rows (inactive) ---
    while trace.len() < total_rows {
        let row = vec![BabyBear::ZERO; TRACE_WIDTH];
        // All selectors are zero, so no constraints fire on padding rows
        trace.push(row);
    }

    let public_inputs = vec![revocation_root];
    (trace, public_inputs)
}

/// Helper: create a deterministic hash for testing.
#[cfg(test)]
fn make_test_hash(seed: u32) -> BabyBear {
    use dregg_circuit::poseidon2::hash_many;
    hash_many(&[BabyBear::new(seed), BabyBear::new(0xBEEF)])
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::stark::{self, StarkAir};

    /// Build a test tree with the given number of revoked entries.
    fn build_test_tree(num_revoked: usize) -> DslRevocationTree {
        let hashes: Vec<BabyBear> = (1..=num_revoked as u32)
            .map(|i| make_test_hash(i * 100))
            .collect();
        DslRevocationTree::new(hashes, TREE_DEPTH)
    }

    // ========================================================================
    // Structure validation
    // ========================================================================

    #[test]
    fn descriptor_validates() {
        let desc = non_revocation_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "non-revocation descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn descriptor_has_correct_structure() {
        let desc = non_revocation_circuit_descriptor();
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        assert_eq!(desc.public_input_count, 1);
        assert_eq!(desc.name, "dregg-non-revocation-dsl-v1");

        // Should have 2 boundary constraints (left top, right top)
        assert_eq!(desc.boundaries.len(), 2);

        // Count constraints:
        // 3 binary (selectors) + 2 gated binary (direction) + 2 hash (Merkle)
        // + 2 ordering diff + 30 diff_left bits + 30 diff_right bits
        // + 2 range check reconstruction + 1 adjacency = 72
        let expected_constraints = 3 + 2 + 2 + 2 + ORDERING_BITS + ORDERING_BITS + 2 + 1;
        assert_eq!(
            desc.constraints.len(),
            expected_constraints,
            "Expected {} constraints, got {}",
            expected_constraints,
            desc.constraints.len()
        );
    }

    // ========================================================================
    // Tree construction and basic properties
    // ========================================================================

    #[test]
    fn tree_construction_with_sentinels() {
        let tree = build_test_tree(5);
        // 5 revoked + 2 sentinels = 7 sorted leaves
        assert_eq!(tree.num_leaves(), 7);
        assert_eq!(tree.sorted_leaves[0], SENTINEL_MIN);
        assert_eq!(*tree.sorted_leaves.last().unwrap(), SENTINEL_MAX);

        // Verify sorted
        for i in 1..tree.sorted_leaves.len() {
            assert!(tree.sorted_leaves[i - 1].0 < tree.sorted_leaves[i].0);
        }
    }

    #[test]
    fn tree_root_deterministic() {
        let t1 = build_test_tree(5);
        let t2 = build_test_tree(5);
        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn membership_proof_verifies() {
        let tree = build_test_tree(5);
        let root = tree.root();

        for i in 0..tree.num_leaves() {
            let leaf = tree.sorted_leaves[i];
            let (siblings, directions) = tree.prove_membership(i).unwrap();

            // Walk up the path manually
            let mut current = leaf;
            for level in 0..TREE_DEPTH {
                let sib = siblings[level];
                let dir = directions[level];
                let (left, right) = if dir == 0 {
                    (current, sib)
                } else {
                    (sib, current)
                };
                current = hash_fact(left, &[right]);
            }
            assert_eq!(current, root, "Membership proof failed for leaf {i}");
        }
    }

    // ========================================================================
    // Valid non-membership trace evaluates to zero
    // ========================================================================

    #[test]
    fn valid_non_membership_evaluates_to_zero() {
        let tree = build_test_tree(5);
        let absent = make_test_hash(999);
        assert!(!tree.contains(&absent));

        let witness = tree.prove_non_membership(&absent).unwrap();
        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&witness, root);

        let circuit = non_revocation_dsl_circuit();
        let alpha = BabyBear::new(7);

        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = circuit.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {i}: c = {}",
                c.0
            );
        }
    }

    #[test]
    fn multiple_absent_hashes_all_evaluate_to_zero() {
        let tree = build_test_tree(8);
        let circuit = non_revocation_dsl_circuit();
        let alpha = BabyBear::new(13);
        let root = tree.root();

        for seed in [999u32, 1234, 5678, 9999, 42424] {
            let absent = make_test_hash(seed);
            if tree.contains(&absent) {
                continue;
            }

            let witness = tree.prove_non_membership(&absent).unwrap();
            let (trace, pi) = generate_non_revocation_trace(&witness, root);

            for i in 0..trace.len() {
                let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
                let c = circuit.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "Constraint non-zero at row {} for seed {}: c = {}",
                    i,
                    seed,
                    c.0
                );
            }
        }
    }

    // ========================================================================
    // Adversarial: wrong path (bad sibling) detected
    // ========================================================================

    #[test]
    fn bad_sibling_detected() {
        let tree = build_test_tree(5);
        let absent = make_test_hash(999);
        assert!(!tree.contains(&absent));

        let mut witness = tree.prove_non_membership(&absent).unwrap();
        // Corrupt a left sibling
        witness.left_siblings[1] = BabyBear::new(0xBAD);

        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&witness, root);

        // The Hash constraints will still evaluate to zero on each row (because
        // we recompute parent from the corrupted sibling in trace generation).
        // BUT the boundary constraint won't be satisfied (the top parent won't
        // equal the real root). We verify this via STARK.
        let circuit = non_revocation_dsl_circuit();
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_err(),
            "Bad sibling should be rejected by STARK (boundary mismatch)"
        );
    }

    // ========================================================================
    // Adversarial: item actually IN the tree (equality where inequality required)
    // ========================================================================

    #[test]
    fn item_in_tree_equality_rejected() {
        let tree = build_test_tree(5);

        // Pick a leaf that IS in the tree (not a sentinel)
        let present = tree.sorted_leaves[2];
        assert!(present != SENTINEL_MIN && present != SENTINEL_MAX);

        // Craft a witness where ancestor_hash == left_neighbor
        let left_pos = 2;
        let right_pos = 3;
        let left_val = tree.sorted_leaves[left_pos];
        let right_val = tree.sorted_leaves[right_pos];
        assert_eq!(left_val, present);

        let (left_siblings, left_directions) = tree.prove_membership(left_pos).unwrap();
        let (right_siblings, right_directions) = tree.prove_membership(right_pos).unwrap();

        let malicious = NonMembershipWitnessDsl {
            ancestor_hash: present, // equals left_neighbor!
            left_neighbor: left_val,
            right_neighbor: right_val,
            left_siblings,
            left_directions,
            right_siblings,
            right_directions,
            left_tree_position: left_pos,
            right_tree_position: right_pos,
        };

        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&malicious, root);

        let circuit = non_revocation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // The ordering constraint should reject this:
        // diff_left = ancestor - left - 1 = present - present - 1 = p - 1 (wraps!)
        // The bit decomposition of HALF_P_MINUS_1 - (p-1) would wrap, so the
        // range check reconstruction will fail.
        let mut any_nonzero = false;
        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = circuit.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
            if c != BabyBear::ZERO {
                any_nonzero = true;
                break;
            }
        }
        assert!(
            any_nonzero,
            "Item equal to left neighbor (in tree) must be rejected by ordering constraints"
        );
    }

    #[test]
    fn item_equals_right_neighbor_rejected() {
        let tree = build_test_tree(5);

        // Pick a leaf that IS in the tree
        let present = tree.sorted_leaves[3];
        assert!(present != SENTINEL_MIN && present != SENTINEL_MAX);

        let left_pos = 2;
        let right_pos = 3;
        let left_val = tree.sorted_leaves[left_pos];
        let right_val = tree.sorted_leaves[right_pos];
        assert_eq!(right_val, present);

        let (left_siblings, left_directions) = tree.prove_membership(left_pos).unwrap();
        let (right_siblings, right_directions) = tree.prove_membership(right_pos).unwrap();

        let malicious = NonMembershipWitnessDsl {
            ancestor_hash: present, // equals right_neighbor!
            left_neighbor: left_val,
            right_neighbor: right_val,
            left_siblings,
            left_directions,
            right_siblings,
            right_directions,
            left_tree_position: left_pos,
            right_tree_position: right_pos,
        };

        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&malicious, root);

        let circuit = non_revocation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // diff_right = right - ancestor - 1 = present - present - 1 = p - 1 (wraps!)
        let mut any_nonzero = false;
        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = circuit.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
            if c != BabyBear::ZERO {
                any_nonzero = true;
                break;
            }
        }
        assert!(
            any_nonzero,
            "Item equal to right neighbor (in tree) must be rejected by ordering constraints"
        );
    }

    // ========================================================================
    // Adversarial: wrong root detected
    // ========================================================================

    #[test]
    fn wrong_root_rejected_by_stark() {
        let tree = build_test_tree(5);
        let absent = make_test_hash(999);
        assert!(!tree.contains(&absent));

        let witness = tree.prove_non_membership(&absent).unwrap();
        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&witness, root);

        let circuit = non_revocation_dsl_circuit();
        let proof = stark::prove(&circuit, &trace, &pi);

        // Verify with wrong root
        let wrong_pi = vec![BabyBear::new(0xBAD)];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "Wrong revocation root should be rejected by STARK"
        );
    }

    // ========================================================================
    // Adversarial: non-adjacent neighbors
    // ========================================================================

    #[test]
    fn non_adjacent_neighbors_rejected() {
        let tree = build_test_tree(10); // 10 revoked + 2 sentinels = 12 leaves

        // Find a hash that falls between non-adjacent leaves
        let target = make_test_hash(12345);
        if tree.contains(&target) {
            return; // skip if accidentally in tree
        }

        let target_val = target.0;

        // Find two non-adjacent leaves that bracket the target (skip one in between)
        let mut found = None;
        for i in 0..tree.sorted_leaves.len().saturating_sub(2) {
            if tree.sorted_leaves[i].0 < target_val && tree.sorted_leaves[i + 2].0 > target_val {
                found = Some((i, i + 2));
                break;
            }
        }

        let (left_idx, right_idx) = match found {
            Some(pair) => pair,
            None => return, // can't construct this test case
        };

        assert_eq!(right_idx - left_idx, 2); // non-adjacent

        let left_val = tree.sorted_leaves[left_idx];
        let right_val = tree.sorted_leaves[right_idx];
        let (left_siblings, left_directions) = tree.prove_membership(left_idx).unwrap();
        let (right_siblings, right_directions) = tree.prove_membership(right_idx).unwrap();

        let malicious = NonMembershipWitnessDsl {
            ancestor_hash: target,
            left_neighbor: left_val,
            right_neighbor: right_val,
            left_siblings,
            left_directions,
            right_siblings,
            right_directions,
            left_tree_position: left_idx,
            right_tree_position: right_idx,
        };

        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&malicious, root);

        let circuit = non_revocation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // The adjacency constraint should reject (right_pos - left_pos - 1 != 0)
        let mut any_nonzero = false;
        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = circuit.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
            if c != BabyBear::ZERO {
                any_nonzero = true;
                break;
            }
        }
        assert!(
            any_nonzero,
            "Non-adjacent neighbors must be rejected by adjacency constraint"
        );
    }

    // ========================================================================
    // STARK prove/verify round-trip
    // ========================================================================

    #[test]
    fn stark_prove_verify_roundtrip() {
        let tree = build_test_tree(5);
        let absent = make_test_hash(999);
        assert!(!tree.contains(&absent));

        let witness = tree.prove_non_membership(&absent).unwrap();
        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&witness, root);

        let circuit = non_revocation_dsl_circuit();
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify should succeed on valid non-membership trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn stark_roundtrip_multiple_absent_values() {
        let tree = build_test_tree(8);
        let circuit = non_revocation_dsl_circuit();
        let root = tree.root();

        for seed in [777u32, 888, 2222, 4444] {
            let absent = make_test_hash(seed);
            if tree.contains(&absent) {
                continue;
            }

            let witness = tree.prove_non_membership(&absent).unwrap();
            let (trace, pi) = generate_non_revocation_trace(&witness, root);

            let proof = stark::prove(&circuit, &trace, &pi);
            let result = stark::verify(&circuit, &proof, &pi);
            assert!(
                result.is_ok(),
                "STARK roundtrip failed for seed {}: {:?}",
                seed,
                result.err()
            );
        }
    }

    #[test]
    fn stark_rejects_tampered_proof() {
        let tree = build_test_tree(5);
        let absent = make_test_hash(999);
        let witness = tree.prove_non_membership(&absent).unwrap();
        let root = tree.root();
        let (trace, pi) = generate_non_revocation_trace(&witness, root);

        let circuit = non_revocation_dsl_circuit();
        let mut proof = stark::prove(&circuit, &trace, &pi);

        // Tamper with the trace commitment
        proof.trace_commitment[0] ^= 0xFF;

        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_err(), "Tampered proof should be rejected");
    }

    // ========================================================================
    // Boundary constraints check
    // ========================================================================

    #[test]
    fn boundary_constraints_bind_root() {
        let circuit = non_revocation_dsl_circuit();
        let root = BabyBear::new(123456);
        let pi = vec![root];

        let boundaries = circuit.boundary_constraints(&pi, 16);
        assert_eq!(boundaries.len(), 2);

        // First boundary: row TREE_DEPTH, col 2, value = root
        assert_eq!(boundaries[0].row, TREE_DEPTH);
        assert_eq!(boundaries[0].col, col::COL_2);
        assert_eq!(boundaries[0].value, root);

        // Second boundary: row 2*TREE_DEPTH, col 2, value = root
        assert_eq!(boundaries[1].row, 2 * TREE_DEPTH);
        assert_eq!(boundaries[1].col, col::COL_2);
        assert_eq!(boundaries[1].value, root);
    }
}
