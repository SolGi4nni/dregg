//! Production non-revocation proving via DSL circuit.
//!
//! This module provides the canonical implementation for non-revocation proofs:
//! - [`DslRevocationTree`] — sorted binary Merkle tree (hash_fact-based)
//! - [`prove_non_revocation_dsl`] — generate a STARK proof of non-membership
//! - [`verify_non_revocation_dsl`] — verify a STARK non-membership proof
//! - [`revocation_hash_to_field`] — convert 32-byte revocation hash to BabyBear
//!
//! Supersedes the old `dregg_circuit::non_revocation_air` (4-ary, hand-written AIR)
//! and the test-only `dregg_dsl_tests::non_revocation_dsl`.

use crate::field::BabyBear;
use crate::poseidon2::{hash_fact, hash_many};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Constants
// ============================================================================

/// Tree depth for the DSL non-revocation Merkle tree.
/// Binary tree of depth 4 supports 16 leaves.
pub const TREE_DEPTH: usize = 4;

/// Alias for external consumers that used `REVOCATION_TREE_DEPTH`.
pub const REVOCATION_TREE_DEPTH: usize = TREE_DEPTH;

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
/// 5 shared + 1 diff_left + 30 diff_left_bits + 1 diff_right + 30 diff_right_bits + 3 selectors
/// + 1 sentinel selector = 71
pub const TRACE_WIDTH: usize = 71;

/// (p-1)/2 for BabyBear, used in ordering range checks.
pub const HALF_P_MINUS_1: u32 = 1006632959;

/// Sentinel min value (0) for the sorted tree.
pub const SENTINEL_MIN: BabyBear = BabyBear::ZERO;

/// Sentinel max value (p-1) for the sorted tree.
pub const SENTINEL_MAX: BabyBear = BabyBear(2013265920);

// ============================================================================
// Column layout
// ============================================================================

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
    pub const DIFF_RIGHT: usize = DIFF_LEFT_BITS_START + ORDERING_BITS; // 36
    pub const DIFF_RIGHT_BITS_START: usize = DIFF_RIGHT + 1; // 37

    // Row type selectors
    pub const IS_CONTROL: usize = DIFF_RIGHT_BITS_START + ORDERING_BITS; // 67
    pub const IS_MERKLE_LEFT: usize = IS_CONTROL + 1; // 68
    pub const IS_MERKLE_RIGHT: usize = IS_MERKLE_LEFT + 1; // 69
    pub const RIGHT_IS_SENTINEL: usize = IS_MERKLE_RIGHT + 1; // 70

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

    /// The queried item (`ancestor_hash`), exposed as a PUBLIC input so a
    /// composing verifier can bind the proven-fresh item to a turn's nullifier
    /// (no-double-spend binding "b"). This is a REAL binding, not a free wire:
    /// the same value occupies control-row `COL_0`, which the ordering
    /// constraints C6/C7/C10/C11 pin strictly between two adjacent sorted
    /// leaves, and a row-0 `PiBinding` (see `boundaries`) ties that cell to
    /// `pi[1]` in-circuit. A prover who publishes a `QUERIED_ITEM` other than
    /// the bracketed item violates the row-0 boundary and the proof is UNSAT.
    pub const QUERIED_ITEM: usize = 1;
}

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the non-revocation CircuitDescriptor.
///
/// Encodes constraints C1-C12 for sorted-tree non-membership with 30-bit
/// ordering range checks and binary Merkle path authentication.
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
    constraints.push(ConstraintExpr::Binary {
        col: col::RIGHT_IS_SENTINEL,
    });

    // C4: direction_bit (col 3) is binary on Merkle rows
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Binary { col: col::COL_3 }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Binary { col: col::COL_3 }),
    });

    // C5: Hash binding for Merkle rows: col2 = hash_fact(col0, [col1])
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_LEFT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COL_2,
            input_cols: vec![col::COL_0, col::COL_1],
        }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE_RIGHT,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COL_2,
            input_cols: vec![col::COL_0, col::COL_1],
        }),
    });

    // C6: Ordering diff_left consistency (control row):
    // diff_left == ancestor_hash - left_neighbor - 1
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

    // C7: Ordering diff_right consistency (control row, unless the upper
    // neighbor is the max sentinel):
    // diff_right == right_neighbor - ancestor_hash - 1
    // => col_DIFF_RIGHT - col2 + col0 + 1 == 0
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: col::RIGHT_IS_SENTINEL,
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
        }),
    });

    // C7b: A disabled right-gap check is allowed only for the canonical max sentinel.
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_CONTROL,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::RIGHT_IS_SENTINEL, col::COL_2],
                },
                PolyTerm {
                    coeff: -SENTINEL_MAX,
                    col_indices: vec![col::RIGHT_IS_SENTINEL],
                },
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
            inner: Box::new(ConstraintExpr::InvertedGated {
                selector_col: col::RIGHT_IS_SENTINEL,
                inner: Box::new(ConstraintExpr::Polynomial { terms }),
            }),
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

    // Boundary constraints: bind revocation_root to Merkle path tops, and bind
    // the queried item (control-row COL_0) to the second public input.
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
        // QUERIED-ITEM binding (no-double-spend tooth "b"): the control row is
        // row 0, where COL_0 holds `ancestor_hash` — the item being proven
        // fresh. The ordering constraints C6/C7/C10/C11 already pin COL_0
        // strictly between two adjacent sorted leaves, so exposing it as
        // `pi[QUERIED_ITEM]` via this row-0 boundary is a REAL binding, not a
        // free wire: a proof whose published `pi[1]` differs from the bracketed
        // item violates this boundary and is UNSAT.
        BoundaryDef::PiBinding {
            row: BoundaryRow::Index(0),
            col: col::COL_0,
            pi_index: pi::QUERIED_ITEM,
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
        ColumnDef {
            name: "right_is_sentinel".into(),
            index: col::RIGHT_IS_SENTINEL,
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
        public_input_count: 2, // [revocation_root, queried_item]
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the non-revocation descriptor.
pub fn non_revocation_dsl_circuit() -> DslCircuit {
    DslCircuit::new(non_revocation_circuit_descriptor())
}

// ============================================================================
// Sorted binary Merkle tree (hash_fact-based)
// ============================================================================

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

    /// Number of actual revoked entries (excluding sentinels).
    pub fn num_revoked(&self) -> usize {
        self.sorted_leaves
            .iter()
            .filter(|h| **h != SENTINEL_MIN && **h != SENTINEL_MAX)
            .count()
    }

    /// Whether the tree has no revoked entries.
    pub fn is_empty(&self) -> bool {
        self.num_revoked() == 0
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

// ============================================================================
// Trace generation
// ============================================================================

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

    // Ordering witness: diff_right = right_neighbor - ancestor_hash - 1.
    // The max sentinel is the one legal upper-tail case where the canonical
    // integer gap may exceed the half-field range bound; the sentinel selector
    // disables only the right-gap reconstruction/range check for that row.
    if witness.right_neighbor == SENTINEL_MAX {
        control[col::RIGHT_IS_SENTINEL] = BabyBear::ONE;
    } else {
        let diff_right = witness.right_neighbor - witness.ancestor_hash - BabyBear::ONE;
        control[col::DIFF_RIGHT] = diff_right;
        let diff_right_u32 = diff_right.as_u32();
        if diff_right_u32 <= HALF_P_MINUS_1 {
            let check_val = HALF_P_MINUS_1 - diff_right_u32;
            for i in 0..ORDERING_BITS {
                control[col::diff_right_bit(i)] = BabyBear::new((check_val >> i) & 1);
            }
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

    // PI layout: [revocation_root, queried_item]. The queried item is
    // `ancestor_hash` — the control-row COL_0 value the row-0 QUERIED_ITEM
    // boundary binds and the ordering constraints bracket.
    let public_inputs = vec![revocation_root, witness.ancestor_hash];
    (trace, public_inputs)
}

// ============================================================================
// Production prove / verify API
// ============================================================================

/// Generate a STARK proof that `item_hash` is NOT in the given revocation tree.
///
/// Returns `Err` if the item IS in the tree (cannot prove non-membership).
pub fn prove_non_revocation_dsl(
    tree: &DslRevocationTree,
    item_hash: BabyBear,
) -> Result<StarkProof, String> {
    let witness = tree
        .prove_non_membership(&item_hash)
        .ok_or_else(|| "item is in the revocation tree (revoked)".to_string())?;

    let root = tree.root();
    let (trace, public_inputs) = generate_non_revocation_trace(&witness, root);
    let circuit = non_revocation_dsl_circuit();
    Ok(stark::prove(&circuit, &trace, &public_inputs))
}

/// Verify a STARK non-revocation proof against the given root and item hash.
///
/// The verifier supplies the revocation `root` (committed by the federation)
/// AND the `item_hash` whose freshness it expects this proof to attest. Both
/// are public inputs (`[revocation_root, queried_item]`): the proof is bound
/// in-circuit to BOTH, so a proof of freshness for a DIFFERENT item is
/// rejected (the row-0 QUERIED_ITEM boundary fails). In privacy-preserving
/// composition the caller may pass the item it independently expects (e.g. a
/// turn's nullifier); the item is no longer hidden from a verifier that
/// chooses to bind it.
pub fn verify_non_revocation_dsl(
    proof: &StarkProof,
    root: BabyBear,
    item_hash: BabyBear,
) -> Result<(), String> {
    let circuit = non_revocation_dsl_circuit();
    let public_inputs = vec![root, item_hash];
    stark::verify(&circuit, proof, &public_inputs)
}

// ============================================================================
// AUDITED p3 non-revocation proving / verification (`p3-batch-stark`)
// ============================================================================
//
// These route the SAME non-revocation (sorted-tree non-membership) statement
// through the audited Plonky3 verifier (`dsl_p3_air::prove_dsl_p3` /
// `verify_dsl_p3` → `p3-batch-stark`) instead of the bespoke `crate::stark`.
// The non-revocation circuit is algebraic except its two `ConstraintExpr::Hash`
// (`hash_fact` sponge) node-hash constraints, which `dsl_p3_air` arithmetizes
// via the real in-circuit Poseidon2 gadget. The proof carries a REAL terminal
// low-degree test (FRI). Public inputs: `[revocation_root]`.

/// Prove `item_hash` is NOT revoked through the AUDITED Plonky3 prover
/// (`p3-batch-stark`). Returns `Err` if the item IS in the tree (cannot prove
/// non-membership) or the audited prover/verifier rejects.
#[cfg(feature = "recursion")]
pub fn prove_non_revocation_p3(
    tree: &DslRevocationTree,
    item_hash: BabyBear,
) -> Result<crate::dsl::dsl_p3_air::DslP3Proof, String> {
    let witness = tree
        .prove_non_membership(&item_hash)
        .ok_or_else(|| "item is in the revocation tree (revoked)".to_string())?;
    let root = tree.root();
    let (trace, public_inputs) = generate_non_revocation_trace(&witness, root);
    let circuit = non_revocation_dsl_circuit();
    crate::dsl::dsl_p3_air::prove_dsl_p3(&circuit, &trace, &public_inputs)
        .map_err(|e| format!("non-revocation p3 proof failed: {e}"))
}

/// Verify a non-revocation proof on the AUDITED Plonky3 verifier
/// (`p3-batch-stark`). The verifier supplies the revocation `root` AND the
/// `item_hash` whose freshness it expects this proof to attest; both are public
/// inputs (`[revocation_root, queried_item]`) bound in-circuit. A proof of
/// freshness for a DIFFERENT item publishes a different `pi[1]` and is rejected
/// by the row-0 QUERIED_ITEM boundary.
#[cfg(feature = "recursion")]
pub fn verify_non_revocation_p3(
    proof: &crate::dsl::dsl_p3_air::DslP3Proof,
    root: BabyBear,
    item_hash: BabyBear,
) -> Result<(), String> {
    let circuit = non_revocation_dsl_circuit();
    let public_inputs = vec![root, item_hash];
    crate::dsl::dsl_p3_air::verify_dsl_p3(&circuit, proof, &public_inputs)
        .map_err(|e| format!("non-revocation p3 verification failed: {e}"))
}

// ============================================================================
// Utility functions
// ============================================================================

/// Convert a 32-byte revocation hash (from `DerivationTree::revocation_hash`) to a BabyBear
/// field element suitable for the sorted revocation tree.
///
/// Uses Poseidon2 to compress the 32 bytes into a single field element,
/// matching the approach used in `commit::poseidon2_tree::commitment_to_field`.
pub fn revocation_hash_to_field(hash: &[u8; 32]) -> BabyBear {
    let elements = BabyBear::encode_hash(hash);
    hash_many(&elements)
}

#[cfg(all(test, feature = "recursion"))]
mod p3_tests {
    use super::*;

    fn build_tree(num_revoked: u32) -> DslRevocationTree {
        let hashes: Vec<BabyBear> = (1..=num_revoked)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect();
        DslRevocationTree::new(hashes, TREE_DEPTH)
    }

    /// AUDITED p3 path: an honest non-revocation proof (item NOT in the tree)
    /// proves+verifies through the real Plonky3 verifier (`p3-batch-stark`),
    /// including the in-circuit Poseidon2 arithmetization of the node-hash
    /// `hash_fact` sponge constraints.
    #[test]
    fn p3_non_revocation_roundtrip() {
        let tree = build_tree(20);
        let root = tree.root();
        // An item NOT in the tree.
        let fresh = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);

        let proof =
            prove_non_revocation_p3(&tree, fresh).expect("honest non-revocation must prove+verify");
        verify_non_revocation_p3(&proof, root, fresh)
            .expect("audited p3 verify accepts honest freshness");
    }

    /// ANTI-FORGERY (no-double-spend binding "b"): a non-revocation proof that
    /// genuinely proves freshness for item X MUST be rejected when the verifier
    /// expects a DIFFERENT item Y. The queried item is now a public input
    /// (`pi[QUERIED_ITEM]`) bound in-circuit to control-row COL_0 (the value the
    /// ordering constraints bracket), so verifying with the wrong item supplies
    /// a `pi[1]` the row-0 boundary cannot satisfy.
    #[test]
    fn p3_non_revocation_rejects_wrong_queried_item() {
        let tree = build_tree(20);
        let root = tree.root();
        let fresh = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);
        let proof = prove_non_revocation_p3(&tree, fresh).expect("honest proof");

        // Verify with a DIFFERENT item than the one actually proven fresh.
        let other_item = hash_many(&[BabyBear::new(0xF00D), BabyBear::new(0xCAFE)]);
        assert_ne!(other_item, fresh);
        let res = verify_non_revocation_p3(&proof, root, other_item);
        assert!(
            res.is_err(),
            "SOUNDNESS (binding b): a freshness proof for one item MUST NOT verify against a \
             different expected item — the QUERIED_ITEM public-input binding is unenforced!"
        );
    }

    /// ANTI-GHOST: a forged revocation `root` public input MUST be rejected by
    /// the audited p3 verifier (the proof binds the genuine sorted-tree root).
    #[test]
    fn p3_non_revocation_rejects_forged_root() {
        let tree = build_tree(20);
        let root = tree.root();
        let fresh = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);
        let proof = prove_non_revocation_p3(&tree, fresh).expect("honest proof");

        let forged_root = root + BabyBear::new(1);
        let res = verify_non_revocation_p3(&proof, forged_root, fresh);
        assert!(
            res.is_err(),
            "SOUNDNESS: a forged revocation root MUST be rejected by the audited p3 verifier"
        );
    }

    /// ANTI-GHOST: a REVOKED item (present in the tree) cannot produce a
    /// non-revocation proof — `prove_non_membership` returns `None`, so the
    /// prover errors. A revoked capability cannot forge freshness.
    #[test]
    fn p3_revoked_item_cannot_prove_freshness() {
        let revoked = hash_many(&[BabyBear::new(100), BabyBear::new(0xDEAD)]); // i=1 ⇒ in tree
        let tree = build_tree(20);
        let res = prove_non_revocation_p3(&tree, revoked);
        assert!(
            res.is_err(),
            "SOUNDNESS: a REVOKED item must NOT be able to prove non-revocation"
        );
    }
}
