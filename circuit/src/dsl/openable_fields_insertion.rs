//! The openable-`fields_root` IN-CIRCUIT INSERTION gate (the REFUSAL
//! ledgerless-authority close, #103): a STARK that
//!
//! ```text
//! post_root = insert(pre_root, key → value)
//! ```
//!
//! is FORCED in-circuit — the post-root is DERIVED from the pre-root + the
//! public `(key, value)`, NOT anchored off-circuit from a trusted post-cell.
//!
//! ## Why this exists (the gap it closes)
//!
//! `refusal`'s authority change writes an audit record into the
//! protocol-reserved `fields_root` key (`REFUSAL_AUDIT_EXT_KEY`). The deployed
//! `fields_root` is a sponge over the WHOLE map, so the post-root depends on
//! every entry — today the verifier recomputes it OFF-CIRCUIT from the trusted
//! post-cell (`Anchor::RecordDigest`). With the openable
//! [`crate::openable_fields_root::OpenableFieldsTree`] representation, the
//! post-root is the single-leaf insertion of `(key, value)` into the pre-root,
//! and THIS circuit proves that insertion: a ledgerless client supplies the
//! pre-root and the PUBLIC `(key, value)` (for refusal, the public audit felt),
//! and the proof alone binds the post-root.
//!
//! ## The statement (depth = [`FIELDS_TREE_DEPTH`], binary `cap_node` nodes)
//!
//! The trace is exactly `FIELDS_TREE_DEPTH` rows (16), one per tree level,
//! bottom-up. Each row carries TWO Merkle folds that ride the SAME witnessed
//! sibling and the SAME direction bit — the OLD fold (recomputing `pre_root`
//! from the old leaf digest) and the NEW fold (recomputing `post_root` from the
//! new leaf digest `hash[key, value]`):
//!
//! ```text
//! row r:  cur_old_r ∈ {left_old_r, right_old_r}   (selected by dir_r)
//!         cur_new_r ∈ {left_new_r, right_new_r}   (SAME dir_r)
//!         sibling_r is the SHARED sibling at level r (occupies the OTHER slot
//!                   in BOTH the old and the new node hash)
//!         parent_old_r = cap_node(left_old_r, right_old_r)   (in-circuit P2)
//!         parent_new_r = cap_node(left_new_r, right_new_r)   (in-circuit P2)
//!         cur_old_{r+1} = parent_old_r        (chain continuity, old)
//!         cur_new_{r+1} = parent_new_r        (chain continuity, new)
//! row 0:  cur_old_0 = pi[OLD_LEAF]            (old leaf digest)
//!         cur_new_0 = pi[NEW_LEAF]            (new leaf digest = hash[key,value])
//! last:   parent_old = pi[PRE_ROOT]
//!         parent_new = pi[POST_ROOT]
//! ```
//!
//! ## Why the post-root is DERIVED, not a free column (the soundness core)
//!
//! The post-root is NOT a witnessed wire the prover sets freely. It is the
//! last-row `parent_new` boundary, and `parent_new` at each level is the
//! in-circuit `cap_node` of the new child and the SHARED sibling — the SAME
//! sibling that, in the OLD fold, hashes up to `pi[PRE_ROOT]`. So:
//!
//!   * the OLD fold pins the witnessed sibling path against `pre_root`
//!     (a tampered sibling tops a different `pre_root`, rejected by the
//!     `PRE_ROOT` boundary);
//!   * the NEW fold reuses those SAME sibling columns and the SAME direction
//!     bits (forced equal across the two folds — there is ONE `sibling` and ONE
//!     `dir` column per row), so `post_root` is uniquely the insertion of the
//!     new leaf at the position the old leaf occupied.
//!
//! A prover who publishes a `post_root` that is NOT the genuine insertion has
//! no satisfying assignment: the only freedom is the sibling path, and that is
//! pinned by the `pre_root` boundary. This is the [`crate::cap_membership`]
//! pattern (membership-open against a pinned root) run TWICE over ONE path.
//! All constraints are forms the audited `prove_dsl_p3` / `verify_dsl_p3` path
//! arithmetizes for real (the node hashes via `Hash3Cap`); the proof carries a
//! REAL terminal FRI low-degree test.

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::BabyBear;
use crate::openable_fields_root::FIELDS_TREE_DEPTH;

/// Trace width: `[cur_old, cur_new, sibling, dir, left_old, right_old,
/// parent_old, left_new, right_new, parent_new]`.
pub const TRACE_WIDTH: usize = 10;

/// Column indices.
pub mod col {
    /// The OLD child node authenticated at this level (row 0: the old leaf digest).
    pub const CUR_OLD: usize = 0;
    /// The NEW child node authenticated at this level (row 0: the new leaf digest).
    pub const CUR_NEW: usize = 1;
    /// The SHARED sibling at this level (occupies the OTHER slot in BOTH hashes).
    pub const SIBLING: usize = 2;
    /// Direction bit: 0 ⇒ `cur` is the LEFT child (sibling right), 1 ⇒ RIGHT.
    /// SHARED by both folds (one column).
    pub const DIR: usize = 3;
    /// OLD node's left child (= cur_old or sibling per dir).
    pub const LEFT_OLD: usize = 4;
    /// OLD node's right child.
    pub const RIGHT_OLD: usize = 5;
    /// `cap_node(left_old, right_old)` — the OLD parent node.
    pub const PARENT_OLD: usize = 6;
    /// NEW node's left child.
    pub const LEFT_NEW: usize = 7;
    /// NEW node's right child.
    pub const RIGHT_NEW: usize = 8;
    /// `cap_node(left_new, right_new)` — the NEW parent node.
    pub const PARENT_NEW: usize = 9;
}

/// Public input indices.
pub mod pi {
    /// The OLD leaf digest at the insertion position (row-0 `cur_old`). The
    /// composing verifier recomputes it from the pre-state map (ZERO for a
    /// fresh key, `hash[key, old_value]` for an overwrite).
    pub const OLD_LEAF: usize = 0;
    /// The NEW leaf digest `hash[key, value]` (row-0 `cur_new`). The composing
    /// verifier recomputes it from the PUBLIC `(key, value)` — for refusal,
    /// from the public audit felt — so the leaf FIELDS are bound.
    pub const NEW_LEAF: usize = 1;
    /// The pre-`fields_root` (last-row `parent_old`). Pinned to the holder's
    /// canonical pre-state `fields_root` (in its openable representation).
    pub const PRE_ROOT: usize = 2;
    /// The post-`fields_root` (last-row `parent_new`). DERIVED in-circuit —
    /// the verifier reads it from this PI, it needs no trusted post-cell.
    pub const POST_ROOT: usize = 3;
}

/// Build the openable-fields insertion CircuitDescriptor.
pub fn openable_fields_insertion_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1: the direction bit is binary.
    constraints.push(ConstraintExpr::Binary { col: col::DIR });

    // C2 (OLD placement): `cur_old` occupies the child slot `dir` selects, and
    // the SHARED sibling occupies the other slot.
    //   left_old  = (1 - dir)·cur_old + dir·sibling
    //   right_old = (1 - dir)·sibling + dir·cur_old
    // Encoded as two algebraic identities (left_old - … == 0, right_old - … == 0).
    constraints.push(placement(col::LEFT_OLD, col::CUR_OLD, col::SIBLING));
    constraints.push(placement(col::RIGHT_OLD, col::SIBLING, col::CUR_OLD));

    // C3 (NEW placement): the NEW fold reuses the SAME `dir` and the SAME
    // `sibling` column — this is what forces the two folds onto ONE path.
    constraints.push(placement(col::LEFT_NEW, col::CUR_NEW, col::SIBLING));
    constraints.push(placement(col::RIGHT_NEW, col::SIBLING, col::CUR_NEW));

    // C4: parent_old = cap_node(left_old, right_old) — REAL in-circuit Poseidon2.
    constraints.push(ConstraintExpr::Hash3Cap {
        output_col: col::PARENT_OLD,
        left_col: col::LEFT_OLD,
        right_col: col::RIGHT_OLD,
    });
    // C5: parent_new = cap_node(left_new, right_new) — REAL in-circuit Poseidon2.
    constraints.push(ConstraintExpr::Hash3Cap {
        output_col: col::PARENT_NEW,
        left_col: col::LEFT_NEW,
        right_col: col::RIGHT_NEW,
    });

    // C6: chain continuity — the next level authenticates THIS level's parent,
    // for BOTH folds (when_transition-gated on the p3 path, so the last row has
    // no wrap-around obligation).
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CUR_OLD,
        local_col: col::PARENT_OLD,
    });
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CUR_NEW,
        local_col: col::PARENT_NEW,
    });

    // Boundaries: the two leaves enter at the bottom; the two roots exit at the top.
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CUR_OLD,
            pi_index: pi::OLD_LEAF,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CUR_NEW,
            pi_index: pi::NEW_LEAF,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT_OLD,
            pi_index: pi::PRE_ROOT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT_NEW,
            pi_index: pi::POST_ROOT,
        },
    ];

    let columns = vec![
        valcol("cur_old", col::CUR_OLD),
        valcol("cur_new", col::CUR_NEW),
        valcol("sibling", col::SIBLING),
        ColumnDef {
            name: "dir".into(),
            index: col::DIR,
            kind: ColumnKind::Binary,
        },
        valcol("left_old", col::LEFT_OLD),
        valcol("right_old", col::RIGHT_OLD),
        ColumnDef {
            name: "parent_old".into(),
            index: col::PARENT_OLD,
            kind: ColumnKind::Hash,
        },
        valcol("left_new", col::LEFT_NEW),
        valcol("right_new", col::RIGHT_NEW),
        ColumnDef {
            name: "parent_new".into(),
            index: col::PARENT_NEW,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "dregg-openable-fields-insertion-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 7, // Poseidon2 S-box
        columns,
        constraints,
        boundaries,
        public_input_count: 4, // [old_leaf, new_leaf, pre_root, post_root]
        lookup_tables: vec![],
    }
}

/// `slot = (1 - dir)·a + dir·b`, i.e. `slot - a + dir·a - dir·b == 0`
/// (dir = 0 ⇒ slot == a; dir = 1 ⇒ slot == b). Used to place `cur`/`sibling`
/// into the left/right child slots per the direction bit.
fn placement(slot: usize, a: usize, b: usize) -> ConstraintExpr {
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![slot],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![a],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::DIR, a],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![col::DIR, b],
            },
        ],
    }
}

fn valcol(name: &str, index: usize) -> ColumnDef {
    ColumnDef {
        name: name.into(),
        index,
        kind: ColumnKind::Value,
    }
}

/// Create a DslCircuit from the insertion descriptor.
pub fn openable_fields_insertion_dsl_circuit() -> DslCircuit {
    DslCircuit::new(openable_fields_insertion_circuit_descriptor())
}

/// Generate the insertion trace from the old/new leaf digests + the SHARED
/// sorted-Merkle path (the [`crate::openable_fields_root::FieldsInsertionWitness`]
/// shape: bottom-up shared siblings + shared direction bits). Returns
/// `(trace, public_inputs)` with `public_inputs = [old_leaf, new_leaf,
/// pre_root, post_root]`, where `pre_root` / `post_root` are the two recomputed
/// path tops. Errs on a malformed witness.
pub fn generate_insertion_trace(
    old_leaf: BabyBear,
    new_leaf: BabyBear,
    siblings: &[BabyBear],
    directions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    use crate::cap_root::cap_node;
    if siblings.len() != FIELDS_TREE_DEPTH || directions.len() != FIELDS_TREE_DEPTH {
        return Err(format!(
            "insertion witness must have exactly {FIELDS_TREE_DEPTH} levels \
             (got {} siblings / {} directions)",
            siblings.len(),
            directions.len()
        ));
    }
    let mut trace = Vec::with_capacity(FIELDS_TREE_DEPTH);
    let mut cur_old = old_leaf;
    let mut cur_new = new_leaf;
    for level in 0..FIELDS_TREE_DEPTH {
        let sib = siblings[level];
        let dir = directions[level];
        let (left_old, right_old, left_new, right_new) = match dir {
            0 => (cur_old, sib, cur_new, sib),
            1 => (sib, cur_old, sib, cur_new),
            d => return Err(format!("direction bit {d} at level {level} is not binary")),
        };
        let parent_old = cap_node(left_old, right_old);
        let parent_new = cap_node(left_new, right_new);
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        row[col::CUR_OLD] = cur_old;
        row[col::CUR_NEW] = cur_new;
        row[col::SIBLING] = sib;
        row[col::DIR] = BabyBear::new(dir as u32);
        row[col::LEFT_OLD] = left_old;
        row[col::RIGHT_OLD] = right_old;
        row[col::PARENT_OLD] = parent_old;
        row[col::LEFT_NEW] = left_new;
        row[col::RIGHT_NEW] = right_new;
        row[col::PARENT_NEW] = parent_new;
        trace.push(row);
        cur_old = parent_old;
        cur_new = parent_new;
    }
    Ok((trace, vec![old_leaf, new_leaf, cur_old, cur_new]))
}

/// Prove an openable-fields insertion through the AUDITED Plonky3 prover
/// (`p3-batch-stark`). Returns the proof + its public inputs `[old_leaf,
/// new_leaf, pre_root, post_root]`. The COMPOSING verifier pins `pre_root` to
/// the canonical pre-state `fields_root` and recomputes `new_leaf` from the
/// PUBLIC `(key, value)` — then reads `post_root` from the proof.
pub fn prove_insertion_p3(
    old_leaf: BabyBear,
    new_leaf: BabyBear,
    siblings: &[BabyBear],
    directions: &[u8],
) -> Result<(crate::dsl::dsl_p3_air::DslP3Proof, Vec<BabyBear>), String> {
    let (trace, public_inputs) =
        generate_insertion_trace(old_leaf, new_leaf, siblings, directions)?;
    let circuit = openable_fields_insertion_dsl_circuit();
    let proof = crate::dsl::dsl_p3_air::prove_dsl_p3(&circuit, &trace, &public_inputs)
        .map_err(|e| format!("openable-fields insertion p3 proof failed: {e}"))?;
    Ok((proof, public_inputs))
}

/// Verify an openable-fields insertion proof on the AUDITED Plonky3 verifier.
/// The caller supplies the four public inputs it expects; all are bound
/// in-circuit (row-0 / last-row boundaries), so a proof for a different leaf,
/// against a different pre-root, or claiming a different post-root is rejected.
pub fn verify_insertion_p3(
    proof: &crate::dsl::dsl_p3_air::DslP3Proof,
    old_leaf: BabyBear,
    new_leaf: BabyBear,
    pre_root: BabyBear,
    post_root: BabyBear,
) -> Result<(), String> {
    let circuit = openable_fields_insertion_dsl_circuit();
    let public_inputs = vec![old_leaf, new_leaf, pre_root, post_root];
    crate::dsl::dsl_p3_air::verify_dsl_p3(&circuit, proof, &public_inputs)
        .map_err(|e| format!("openable-fields insertion p3 verification failed: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::openable_fields_root::{
        FieldsInsertionWitness, FieldsLeaf, OpenableFieldsTree, REFUSAL_AUDIT_EXT_KEY,
        field_key_hash, refusal_audit_value, refusal_insertion_witness, refusal_pre_tree,
    };

    fn leaf(key: u64, val: u32) -> FieldsLeaf {
        FieldsLeaf {
            key_hash: field_key_hash(key),
            value: BabyBear::new(val),
        }
    }

    /// Build a real pre-tree (with the audit slot RESERVED, position-stable) +
    /// the genuine refusal insertion witness.
    fn refusal_witness(audit: &[u8; 32]) -> (OpenableFieldsTree, FieldsInsertionWitness) {
        let pre = refusal_pre_tree(vec![leaf(20, 7), leaf(33, 9), leaf(99, 3)]);
        let w = refusal_insertion_witness(&pre, audit).expect("refusal witness");
        (pre, w)
    }

    /// CONTROL — an HONEST refusal proves + verifies through the audited p3
    /// verifier: the published `post_root` IS the in-circuit insertion of the
    /// PUBLIC audit at the refusal-audit key into the pre-`fields_root`. NO
    /// executor, NO trusted post-cell — the proof alone binds the post-root.
    #[test]
    fn honest_refusal_insertion_round_trips_through_p3() {
        let audit = [0x33u8; 32];
        let (pre, w) = refusal_witness(&audit);
        let (proof, pis) = prove_insertion_p3(
            w.old_leaf_digest,
            w.new_leaf_digest(),
            &w.siblings,
            &w.directions,
        )
        .expect("honest refusal insertion must prove+verify through audited p3");

        // The published PIs: old=ZERO (fresh audit key), new=hash[key,audit],
        // pre=canonical pre-root, post=in-circuit-derived insertion root.
        assert_eq!(pis[pi::OLD_LEAF], w.old_leaf_digest);
        assert_eq!(pis[pi::NEW_LEAF], w.new_leaf_digest());
        assert_eq!(pis[pi::PRE_ROOT], pre.root(), "PRE_ROOT is the canonical pre-state fields_root");
        assert_eq!(pis[pi::POST_ROOT], w.post_root, "POST_ROOT is DERIVED in-circuit");
        // A ledgerless client recomputes the audit value from the PUBLIC bytes
        // and confirms the new leaf binds it — no trusted post-cell.
        assert_eq!(
            w.new_leaf.value,
            refusal_audit_value(&audit),
            "the new leaf carries the public audit felt"
        );

        verify_insertion_p3(
            &proof,
            w.old_leaf_digest,
            w.new_leaf_digest(),
            pre.root(),
            w.post_root,
        )
        .expect("audited p3 verify accepts the honest refusal insertion");
    }

    /// THE TOOTH (forged-refusal UNSAT, NO executor) — a forged refusal whose
    /// `post_fields_root` is NOT the genuine `insert(pre_root, AUDIT_KEY → audit)`
    /// CANNOT verify: the post-root is DERIVED from the SAME witnessed sibling
    /// path that the `PRE_ROOT` boundary pins, so claiming a different post-root
    /// is UNSAT through the proof ALONE. No executor, no trusted post-cell.
    #[test]
    fn forged_post_root_is_rejected() {
        let audit = [0x44u8; 32];
        let (pre, w) = refusal_witness(&audit);
        let (proof, _) = prove_insertion_p3(
            w.old_leaf_digest,
            w.new_leaf_digest(),
            &w.siblings,
            &w.directions,
        )
        .expect("honest proof");

        // Forge: claim a post_root that is NOT the genuine insertion.
        let forged_post = w.post_root + BabyBear::new(1);
        assert!(
            verify_insertion_p3(
                &proof,
                w.old_leaf_digest,
                w.new_leaf_digest(),
                pre.root(),
                forged_post,
            )
            .is_err(),
            "SOUNDNESS: a forged post_fields_root MUST be rejected — the insertion is in-circuit-forced"
        );
    }

    /// THE TOOTH (forged audit VALUE) — a refusal that inserts a DIFFERENT
    /// value than the public audit at the audit key is rejected: the verifier
    /// recomputes `new_leaf` from the PUBLIC audit, so a tampered inserted value
    /// publishes a `new_leaf` the row-0 boundary cannot satisfy.
    #[test]
    fn forged_audit_value_is_rejected() {
        let audit = [0x55u8; 32];
        let (pre, w) = refusal_witness(&audit);
        let (proof, _) = prove_insertion_p3(
            w.old_leaf_digest,
            w.new_leaf_digest(),
            &w.siblings,
            &w.directions,
        )
        .expect("honest proof");

        // The verifier expects the audit value the PUBLIC bytes fold to. A
        // refusal that inserted some OTHER value carries a different new leaf.
        let tampered_leaf = FieldsLeaf {
            key_hash: field_key_hash(REFUSAL_AUDIT_EXT_KEY),
            value: w.new_leaf.value + BabyBear::new(1),
        };
        assert_ne!(tampered_leaf.digest(), w.new_leaf_digest());
        assert!(
            verify_insertion_p3(
                &proof,
                w.old_leaf_digest,
                tampered_leaf.digest(),
                pre.root(),
                w.post_root,
            )
            .is_err(),
            "SOUNDNESS: a refusal inserting a non-public-audit value MUST be rejected"
        );
    }

    /// THE TOOTH (forged PRE_ROOT) — an honest insertion proof verified against
    /// a DIFFERENT pre-`fields_root` is rejected: the last-row `parent_old`
    /// boundary pins the genuine path top. A prover cannot graft the insertion
    /// onto a tree it did not open.
    #[test]
    fn forged_pre_root_is_rejected() {
        let audit = [0x66u8; 32];
        let (pre, w) = refusal_witness(&audit);
        let (proof, _) = prove_insertion_p3(
            w.old_leaf_digest,
            w.new_leaf_digest(),
            &w.siblings,
            &w.directions,
        )
        .expect("honest proof");
        let forged_pre = pre.root() + BabyBear::new(1);
        assert!(
            verify_insertion_p3(
                &proof,
                w.old_leaf_digest,
                w.new_leaf_digest(),
                forged_pre,
                w.post_root,
            )
            .is_err(),
            "SOUNDNESS: a forged pre_fields_root MUST be rejected"
        );
    }

    /// A tampered sibling tops a DIFFERENT pre/post root pair, so the proof
    /// cannot verify against the canonical pre-root: the witnessed path is
    /// genuinely load-bearing (not a free column).
    #[test]
    fn tampered_path_does_not_reach_canonical_root() {
        let audit = [0x77u8; 32];
        let (pre, w) = refusal_witness(&audit);
        let mut siblings = w.siblings.clone();
        siblings[5] = siblings[5] + BabyBear::new(1);
        let (proof, pis) =
            prove_insertion_p3(w.old_leaf_digest, w.new_leaf_digest(), &siblings, &w.directions)
                .expect("the tampered path still proves SOME insertion");
        assert_ne!(pis[pi::PRE_ROOT], pre.root(), "tampered path tops a different pre-root");
        assert!(
            verify_insertion_p3(
                &proof,
                w.old_leaf_digest,
                w.new_leaf_digest(),
                pre.root(),
                w.post_root,
            )
            .is_err(),
            "SOUNDNESS: a path that does not reach the canonical pre-root MUST be rejected"
        );
    }

    /// A malformed witness (wrong path length / non-binary direction) is refused
    /// at trace generation.
    #[test]
    fn malformed_witness_is_refused() {
        let audit = [0x88u8; 32];
        let (_, w) = refusal_witness(&audit);
        assert!(
            generate_insertion_trace(
                w.old_leaf_digest,
                w.new_leaf_digest(),
                &w.siblings[..4],
                &w.directions[..4]
            )
            .is_err()
        );
        let mut dirs = w.directions.clone();
        dirs[0] = 2;
        assert!(
            generate_insertion_trace(w.old_leaf_digest, w.new_leaf_digest(), &w.siblings, &dirs)
                .is_err()
        );
    }
}
