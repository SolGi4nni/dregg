//! Capability-membership DSL circuit (cap Phase D): a STARK that a leaf digest
//! is a member of the canonical **openable** capability tree
//! ([`crate::cap_root::CanonicalCapTree`] — the sorted binary Poseidon2 Merkle
//! tree whose root is the cell's `capability_root` since cap Phase A).
//!
//! ## Why this exists (the AUTHORITY payoff leg)
//!
//! Phase B proves capability membership IN-ROW for the Attenuate/Grant
//! EffectVm selectors (the non-amplification gates). Every OTHER verb's
//! capability-gated turn needs a STANDALONE membership leg the composed
//! full-turn proof can carry: "the consumed capability's 7-field leaf is a
//! member of the holder's pre-state `capability_root`". The Phase-C executor
//! witness ([`dregg_turn::TurnReceipt::consumed_capabilities`]) supplies the
//! leaf preimage + sorted-Merkle path; this circuit proves the path, and
//! `dregg_sdk::verify_full_turn_bound` pins its two public inputs:
//!
//!   * `pi[LEAF_DIGEST]` — the Poseidon2 digest of the consumed cap's 7-field
//!     leaf preimage (the verifier recomputes it from the receipt's witnessed
//!     fields, so a leaf-field tamper mismatches);
//!   * `pi[CAP_ROOT]` — the Merkle root the path reaches (the verifier pins it
//!     to the holder's CANONICAL pre-state `capability_root`, so a path into a
//!     prover-chosen tree mismatches).
//!
//! ## The statement (depth = [`CAP_TREE_DEPTH`], binary `cap_node` nodes)
//!
//! The trace is exactly `CAP_TREE_DEPTH` rows (16 — a power of two, no
//! padding), one per tree level, bottom-up:
//!
//! ```text
//! row r:  cur_r  ∈ {left_r, right_r}   (selected by dir_r ∈ {0,1})
//!         parent_r = cap_node(left_r, right_r)        (in-circuit Poseidon2)
//!         cur_{r+1} = parent_r                        (chain continuity)
//! row 0:  cur_0 = pi[LEAF_DIGEST]
//! last:   parent  = pi[CAP_ROOT]
//! ```
//!
//! `cap_node(left, right)` (= `cap_chip_absorb([FACT_MARK, left, right])`, the
//! SINGLE in-circuit cap hash since decision #1) is byte-identical to the node
//! hash [`CanonicalCapTree`] builds with (the in-circuit gadget
//! `dsl_p3_air::hash_input_state` mirrors it via the `Hash3Cap` form), so the
//! proven root IS the canonical capability root. All five constraints are forms
//! the audited `prove_dsl_p3`/`verify_dsl_p3` path arithmetizes for real (no
//! bespoke `stark`).

use crate::cap_root::{CAP_TREE_DEPTH, cap_node};
use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::BabyBear;

/// Trace width: `[cur, left, right, parent, dir]`.
pub const TRACE_WIDTH: usize = 5;

/// Column indices.
pub mod col {
    /// The child node being authenticated at this level (= previous parent;
    /// row 0 carries the leaf digest).
    pub const CUR: usize = 0;
    /// Left child of this level's node hash.
    pub const LEFT: usize = 1;
    /// Right child of this level's node hash.
    pub const RIGHT: usize = 2;
    /// `cap_node(left, right)` — the parent node.
    pub const PARENT: usize = 3;
    /// Direction bit: 0 ⇒ `cur` is the LEFT child (sibling right), 1 ⇒ RIGHT.
    pub const DIR: usize = 4;
}

/// Public input indices.
pub mod pi {
    /// The leaf digest being proven a member (row-0 `cur` boundary). The
    /// composing verifier recomputes this from the consumed-cap witness's
    /// 7-field leaf preimage, so the leaf FIELDS are bound, not just a digest.
    pub const LEAF_DIGEST: usize = 0;
    /// The Merkle root the path reaches (last-row `parent` boundary). The
    /// composing verifier pins this to the holder's canonical pre-state
    /// `capability_root`.
    pub const CAP_ROOT: usize = 1;
}

/// Build the capability-membership CircuitDescriptor.
pub fn cap_membership_circuit_descriptor() -> CircuitDescriptor {
    let constraints = vec![
        // C1: the direction bit is binary.
        ConstraintExpr::Binary { col: col::DIR },
        // C2: `cur` occupies the child slot `dir` selects:
        //     (1 - dir)·(left - cur) + dir·(right - cur) == 0
        //   ⇔ left - cur - dir·left + dir·right == 0
        // (dir = 0 ⇒ left == cur; dir = 1 ⇒ right == cur). The OTHER slot is the
        // prover-supplied sibling — unconstrained by design (any sibling defines
        // SOME path; only a path whose top equals the pinned canonical root
        // verifies).
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::LEFT],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::CUR],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::DIR, col::LEFT],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::DIR, col::RIGHT],
                },
            ],
        },
        // C3: parent = cap_node(left, right) — REAL in-circuit Poseidon2 (one permutation
        // aux block per row on the p3 path), the EXACT node hash `CanonicalCapTree` builds
        // with since decision #1 (`cap_chip_absorb([FACT_MARK, left, right])`, the single
        // in-circuit cap hash — NOT the capacity-tagged `hash_fact`).
        ConstraintExpr::Hash3Cap {
            output_col: col::PARENT,
            left_col: col::LEFT,
            right_col: col::RIGHT,
        },
        // C4: chain continuity — the next level authenticates THIS level's parent.
        // (Transition constraints are when_transition-gated on the p3 path, so the
        // last row has no wrap-around obligation.)
        ConstraintExpr::Transition {
            next_col: col::CUR,
            local_col: col::PARENT,
        },
    ];

    // Boundaries: leaf digest enters at the bottom, the root exits at the top.
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CUR,
            pi_index: pi::LEAF_DIGEST,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT,
            pi_index: pi::CAP_ROOT,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "cur".into(),
            index: col::CUR,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "left".into(),
            index: col::LEFT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "right".into(),
            index: col::RIGHT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: col::PARENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "dir".into(),
            index: col::DIR,
            kind: ColumnKind::Binary,
        },
    ];

    CircuitDescriptor {
        name: "dregg-cap-membership-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 7, // Poseidon2 S-box
        columns,
        constraints,
        boundaries,
        public_input_count: 2, // [leaf_digest, cap_root]
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the cap-membership descriptor.
pub fn cap_membership_dsl_circuit() -> DslCircuit {
    DslCircuit::new(cap_membership_circuit_descriptor())
}

/// Generate the cap-membership trace from a leaf digest + sorted-Merkle path
/// (the [`crate::cap_root::CanonicalCapTree::prove_membership`] /
/// `ConsumedCapWitness` shape: bottom-up siblings + direction bits, 0 = current
/// node is the LEFT child).
///
/// Returns `(trace, public_inputs)` where `public_inputs = [leaf_digest, root]`
/// and `root` is the path's recomputed top. Errs on a malformed witness (wrong
/// path length or a non-binary direction bit).
pub fn generate_cap_membership_trace(
    leaf_digest: BabyBear,
    siblings: &[BabyBear],
    directions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if siblings.len() != CAP_TREE_DEPTH || directions.len() != CAP_TREE_DEPTH {
        return Err(format!(
            "cap-membership witness must have exactly {CAP_TREE_DEPTH} levels \
             (got {} siblings / {} directions)",
            siblings.len(),
            directions.len()
        ));
    }
    let mut trace = Vec::with_capacity(CAP_TREE_DEPTH);
    let mut cur = leaf_digest;
    for level in 0..CAP_TREE_DEPTH {
        let sib = siblings[level];
        let (left, right) = match directions[level] {
            0 => (cur, sib),
            1 => (sib, cur),
            d => return Err(format!("direction bit {d} at level {level} is not binary")),
        };
        let parent = cap_node(left, right);
        trace.push(vec![
            cur,
            left,
            right,
            parent,
            BabyBear::new(directions[level] as u32),
        ]);
        cur = parent;
    }
    Ok((trace, vec![leaf_digest, cur]))
}

/// Prove capability membership through the AUDITED Plonky3 prover
/// (`p3-batch-stark`). Public inputs of the returned proof: `[leaf_digest,
/// root]` where `root` is the path's recomputed top — the COMPOSING verifier is
/// responsible for pinning that root to the canonical pre-state
/// `capability_root` (the non-vacuity tooth).
pub fn prove_cap_membership_p3(
    leaf_digest: BabyBear,
    siblings: &[BabyBear],
    directions: &[u8],
) -> Result<(crate::dsl::dsl_p3_air::DslP3Proof, Vec<BabyBear>), String> {
    let (trace, public_inputs) = generate_cap_membership_trace(leaf_digest, siblings, directions)?;
    let circuit = cap_membership_dsl_circuit();
    let proof = crate::dsl::dsl_p3_air::prove_dsl_p3(&circuit, &trace, &public_inputs)
        .map_err(|e| format!("cap-membership p3 proof failed: {e}"))?;
    Ok((proof, public_inputs))
}

/// Verify a cap-membership proof on the AUDITED Plonky3 verifier. The caller
/// supplies the `leaf_digest` AND `root` it expects this proof to attest; both
/// are bound in-circuit (row-0 / last-row boundaries), so a proof for a
/// different leaf or against a different tree is rejected.
pub fn verify_cap_membership_p3(
    proof: &crate::dsl::dsl_p3_air::DslP3Proof,
    leaf_digest: BabyBear,
    root: BabyBear,
) -> Result<(), String> {
    let circuit = cap_membership_dsl_circuit();
    let public_inputs = vec![leaf_digest, root];
    crate::dsl::dsl_p3_air::verify_dsl_p3(&circuit, proof, &public_inputs)
        .map_err(|e| format!("cap-membership p3 verification failed: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap_root::{
        CapLeaf, cap_node, encode_breadstuff, encode_expiry, fold_bytes32, slot_hash,
        split_effect_mask,
    };

    fn leaf(slot: u32, target_byte: u8, tier: u32, mask: u32) -> CapLeaf {
        let mut tgt = [0u8; 32];
        tgt[0] = target_byte;
        let (mask_lo, mask_hi) = split_effect_mask(mask);
        CapLeaf {
            slot_hash: slot_hash(slot),
            target: fold_bytes32(&tgt),
            auth_tag: BabyBear::new(tier),
            mask_lo,
            mask_hi,
            expiry: encode_expiry(None),
            breadstuff: encode_breadstuff(None),
        }
    }

    /// Build an honest 1-felt membership witness self-consistent with the DSL AIR's
    /// own `cap_node` fold (the standalone 1-felt demonstration scheme — distinct
    /// from the deployed faithful 8-felt `cap_node8` cap tree). The leaf digest is
    /// the lane-0 projection of a genuine `CapLeaf`'s 8-felt digest; the siblings are
    /// deterministic felts; the returned root is the `cap_node`-folded path top.
    fn real_tree_witness() -> (BabyBear, CapLeaf, Vec<BabyBear>, Vec<u8>) {
        let target = leaf(1, 9, 1, 0x0000_00FF);
        let leaf_digest = target.digest()[0];
        let mut siblings = Vec::with_capacity(CAP_TREE_DEPTH);
        let mut directions = Vec::with_capacity(CAP_TREE_DEPTH);
        let mut cur = leaf_digest;
        for level in 0..CAP_TREE_DEPTH {
            let sib = BabyBear::new(0x1357 + level as u32);
            let dir = (level % 2) as u8;
            cur = if dir == 0 {
                cap_node(cur, sib)
            } else {
                cap_node(sib, cur)
            };
            siblings.push(sib);
            directions.push(dir);
        }
        (cur, target, siblings, directions)
    }

    /// CONTROL: an honest membership witness proves + verifies through the audited
    /// p3 verifier, and the published root equals the `cap_node`-folded path top.
    #[test]
    fn honest_cap_membership_round_trips_through_p3() {
        let (root, target, siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest()[0];
        let (proof, pis) = prove_cap_membership_p3(leaf_digest, &siblings, &directions)
            .expect("honest cap membership must prove+verify through audited p3");
        assert_eq!(pis[pi::LEAF_DIGEST], leaf_digest);
        assert_eq!(pis[pi::CAP_ROOT], root, "published root IS the folded root");
        verify_cap_membership_p3(&proof, leaf_digest, root)
            .expect("audited p3 verify accepts the honest membership");
    }

    /// ANTI-FORGERY (root): an honest proof verified against a DIFFERENT root
    /// is REJECTED — the last-row boundary pins the genuine path top.
    #[test]
    fn forged_root_is_rejected() {
        let (root, target, siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest()[0];
        let (proof, _) =
            prove_cap_membership_p3(leaf_digest, &siblings, &directions).expect("honest");
        let forged_root = root + BabyBear::new(1);
        assert!(
            verify_cap_membership_p3(&proof, leaf_digest, forged_root).is_err(),
            "SOUNDNESS: a forged cap_root MUST be rejected by the audited p3 verifier"
        );
    }

    /// ANTI-FORGERY (leaf): an honest proof verified for a DIFFERENT leaf
    /// digest is REJECTED — the row-0 boundary pins the genuine leaf.
    #[test]
    fn forged_leaf_is_rejected() {
        let (root, target, siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest()[0];
        let (proof, _) =
            prove_cap_membership_p3(leaf_digest, &siblings, &directions).expect("honest");
        // An "inflated mask" tamper: same leaf but EFFECT_ALL rights.
        let mut inflated = target;
        let (lo, hi) = split_effect_mask(0xFFFF_FFFF);
        inflated.mask_lo = lo;
        inflated.mask_hi = hi;
        assert_ne!(inflated.digest()[0], leaf_digest);
        assert!(
            verify_cap_membership_p3(&proof, inflated.digest()[0], root).is_err(),
            "SOUNDNESS: an inflated-mask leaf digest MUST be rejected"
        );
    }

    /// ANTI-FORGERY (witness): a tampered sibling produces a path whose top is
    /// NOT the canonical root, so the proof cannot verify against it.
    #[test]
    fn tampered_path_does_not_reach_canonical_root() {
        let (root, target, mut siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest()[0];
        siblings[3] = siblings[3] + BabyBear::new(1);
        let (proof, pis) = prove_cap_membership_p3(leaf_digest, &siblings, &directions)
            .expect("the tampered path still proves membership in SOME tree");
        assert_ne!(
            pis[pi::CAP_ROOT],
            root,
            "tampered path tops a different root"
        );
        assert!(
            verify_cap_membership_p3(&proof, leaf_digest, root).is_err(),
            "SOUNDNESS: a path that does not reach the canonical root MUST be rejected"
        );
    }

    /// A leaf NOT in the tree (no fabricated position) has no honest witness;
    /// the trace generator rejects malformed paths outright.
    #[test]
    fn malformed_witness_is_refused() {
        let (_, target, siblings, mut directions) = real_tree_witness();
        let leaf_digest = target.digest()[0];
        // Wrong length.
        assert!(
            generate_cap_membership_trace(leaf_digest, &siblings[..4], &directions[..4]).is_err()
        );
        // Non-binary direction bit.
        directions[0] = 2;
        assert!(generate_cap_membership_trace(leaf_digest, &siblings, &directions).is_err());
    }
}
