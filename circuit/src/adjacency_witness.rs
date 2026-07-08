//! Rust witness builder for the emitted **neighbor-adjacency** descriptor
//! (`dregg-membership-adjacency::poseidon2-v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/AdjacencyMembershipEmit.lean`).
//!
//! The adjacency descriptor is the sorted-set NON-membership lift: it proves two leaves
//! `leaf_lower` (at reconstructed `idx_lower`) and `leaf_upper` (at `idx_upper`) are CONSECUTIVE
//! (`idx_upper == idx_lower + 1`) leaves of a shared binary-Poseidon2 root — the in-circuit tooth
//! that turns `lower < candidate < upper` into a sound non-membership witness (no set member can
//! sit strictly between two adjacent leaves). Until now the only Rust producer for it lived inside
//! `circuit-prove/tests/adjacency_membership_emit_gate.rs`; there was NO production witness builder
//! (the analog of [`crate::membership_descriptor_general::membership_witness`]) that consumers of
//! [`crate::descriptor_by_name::descriptor_by_name`] could call. This module is that builder.
//!
//! [`adjacency_witness`] emits the 32-column trace (one binary-tree level per row: two parallel
//! authentication paths lower ‖ upper + the shared power-of-two index accumulator) and the 5-element
//! public-input vector `[root, leaf_lower, leaf_upper, idx_lower, idx_upper]` the descriptor pins. It
//! is purely mechanical — it does NOT enforce consecutiveness or equal roots; the DESCRIPTOR's
//! Last-row boundaries (the internalized `u_idx_out - l_idx_out - 1 == 0` catch tooth and the
//! root pins) are the judge, so a non-adjacent or wrong-root pair yields a well-formed but
//! UNSATISFYING trace that `verify_vm_descriptor2` rejects.

use crate::field::BabyBear;
use crate::poseidon2::hash_2_to_1;

// --- Trace column layout (must match `AdjacencyMembershipEmit.lean` §1). ---
const L_CUR: usize = 0;
const L_SIB: usize = 1;
const L_DIR: usize = 2;
const L_LEFT: usize = 3;
const L_RIGHT: usize = 4;
const L_PAR: usize = 5;
const L_IDX_IN: usize = 6;
const L_IDX_OUT: usize = 7;
const U_CUR: usize = 8;
const U_SIB: usize = 9;
const U_DIR: usize = 10;
const U_LEFT: usize = 11;
const U_RIGHT: usize = 12;
const U_PAR: usize = 13;
const U_IDX_IN: usize = 14;
const U_IDX_OUT: usize = 15;
const POW: usize = 16;
const POW2: usize = 17;
/// Total main-trace width (18 semantic + two 7-lane chip blocks).
pub const ADJ_WIDTH: usize = 32;

// --- PI indices (`adj_pi`). ---
/// PI slot: the shared committed root.
pub const PI_ROOT: usize = 0;
/// PI slot: the lower neighbor leaf.
pub const PI_LEAF_LOWER: usize = 1;
/// PI slot: the upper neighbor leaf.
pub const PI_LEAF_UPPER: usize = 2;
/// PI slot: the reconstructed lower index.
pub const PI_IDX_LOWER: usize = 3;
/// PI slot: the reconstructed upper index.
pub const PI_IDX_UPPER: usize = 4;
/// Public-input count.
pub const ADJ_PI_COUNT: usize = 5;

/// One Merkle authentication step for an adjacency path (mirrors
/// `membership_adjacency_air::AdjStep`): the co-path `sibling` at this level and whether the running
/// hash is the RIGHT child (`dir`; `dir` at level ℓ is bit ℓ of the leaf index).
#[derive(Clone, Copy, Debug)]
pub struct AdjWitnessStep {
    /// The co-path sibling at this level.
    pub sibling: BabyBear,
    /// `true` ⇒ the running hash is the RIGHT child at this level.
    pub dir: bool,
}

fn bit(b: bool) -> BabyBear {
    if b { BabyBear::ONE } else { BabyBear::ZERO }
}

/// Walk a leaf→root path, returning `(root, reconstructed_index)` (the index is the little-endian
/// concatenation of the per-level direction bits).
pub fn adjacency_walk(leaf: BabyBear, path: &[AdjWitnessStep]) -> (BabyBear, u64) {
    let mut cur = leaf;
    let mut idx: u64 = 0;
    for (level, step) in path.iter().enumerate() {
        let (l, r) = if step.dir {
            (step.sibling, cur)
        } else {
            (cur, step.sibling)
        };
        cur = hash_2_to_1(l, r);
        if step.dir {
            idx |= 1u64 << level;
        }
    }
    (cur, idx)
}

/// Build the 32-column adjacency trace + the 5-element public-input vector
/// `[root, leaf_lower, leaf_upper, idx_lower, idx_upper]` for the emitted
/// `dregg-membership-adjacency::poseidon2-v1` descriptor.
///
/// `lower_path` / `upper_path` are the leaf→root authentication paths of the two neighbor leaves in
/// a shared binary-Poseidon2 tree (`hash_2_to_1` nodes). Both paths must have the same power-of-two
/// depth ≥ 2. The 14 chip-lane columns are left zero (`prove_vm_descriptor2`'s `trace_with_chip_lanes`
/// fills them). The published root (`pis[PI_ROOT]`) is the LOWER path's authenticated root; if the two
/// paths do not reach the same root the descriptor's Last-row `U_PAR == PI_ROOT` pin rejects, and if
/// the indices are not consecutive the internalized catch tooth rejects — this builder does not
/// pre-judge either.
pub fn adjacency_witness(
    leaf_lower: BabyBear,
    lower_path: &[AdjWitnessStep],
    leaf_upper: BabyBear,
    upper_path: &[AdjWitnessStep],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = lower_path.len();
    if depth != upper_path.len() {
        return Err(format!(
            "adjacency lower/upper path length mismatch ({depth} vs {})",
            upper_path.len()
        ));
    }
    if depth < 2 || !depth.is_power_of_two() {
        return Err(format!(
            "adjacency depth {depth} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut l_cur = leaf_lower;
    let mut u_cur = leaf_upper;
    let mut pow = BabyBear::ONE;
    let mut l_idx_in = BabyBear::ZERO;
    let mut u_idx_in = BabyBear::ZERO;

    for level in 0..depth {
        let ls = lower_path[level];
        let us = upper_path[level];

        let l_dir = bit(ls.dir);
        let (l_left, l_right) = if ls.dir {
            (ls.sibling, l_cur)
        } else {
            (l_cur, ls.sibling)
        };
        let l_par = hash_2_to_1(l_left, l_right);
        let l_idx_out = l_idx_in + l_dir * pow;

        let u_dir = bit(us.dir);
        let (u_left, u_right) = if us.dir {
            (us.sibling, u_cur)
        } else {
            (u_cur, us.sibling)
        };
        let u_par = hash_2_to_1(u_left, u_right);
        let u_idx_out = u_idx_in + u_dir * pow;

        let pow2 = pow + pow;

        let mut row = vec![BabyBear::ZERO; ADJ_WIDTH];
        row[L_CUR] = l_cur;
        row[L_SIB] = ls.sibling;
        row[L_DIR] = l_dir;
        row[L_LEFT] = l_left;
        row[L_RIGHT] = l_right;
        row[L_PAR] = l_par;
        row[L_IDX_IN] = l_idx_in;
        row[L_IDX_OUT] = l_idx_out;
        row[U_CUR] = u_cur;
        row[U_SIB] = us.sibling;
        row[U_DIR] = u_dir;
        row[U_LEFT] = u_left;
        row[U_RIGHT] = u_right;
        row[U_PAR] = u_par;
        row[U_IDX_IN] = u_idx_in;
        row[U_IDX_OUT] = u_idx_out;
        row[POW] = pow;
        row[POW2] = pow2;
        trace.push(row);

        l_cur = l_par;
        u_cur = u_par;
        l_idx_in = l_idx_out;
        u_idx_in = u_idx_out;
        pow = pow2;
    }

    let (root_l, idx_l) = adjacency_walk(leaf_lower, lower_path);
    let (_root_u, idx_u) = adjacency_walk(leaf_upper, upper_path);
    let pis = vec![
        root_l,
        leaf_lower,
        leaf_upper,
        BabyBear::from_u64(idx_l),
        BabyBear::from_u64(idx_u),
    ];
    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use std::panic::AssertUnwindSafe;

    const ADJ_NAME: &str = "dregg-membership-adjacency::poseidon2-v1";

    /// Build a full binary tree over `leaves` (length a power of two) under `hash_2_to_1`; return
    /// every level (level 0 = leaves, last = `[root]`).
    fn build_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
        assert!(leaves.len().is_power_of_two());
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let mut next = Vec::with_capacity(cur.len() / 2);
            for pair in cur.chunks(2) {
                next.push(hash_2_to_1(pair[0], pair[1]));
            }
            levels.push(next);
        }
        levels
    }

    fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<AdjWitnessStep> {
        let depth = levels.len() - 1;
        let mut path = Vec::with_capacity(depth);
        for level in &levels[..depth] {
            let is_right = index & 1 == 1;
            let sibling = if is_right {
                level[index - 1]
            } else {
                level[index + 1]
            };
            path.push(AdjWitnessStep {
                sibling,
                dir: is_right,
            });
            index >>= 1;
        }
        path
    }

    fn sample_leaves(n: usize) -> Vec<BabyBear> {
        (0..n).map(|i| BabyBear::new((i as u32 + 1) * 10)).collect()
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails
    /// to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        match r {
            Err(_) => true,
            Ok(Err(_)) => true,
            Ok(Ok(())) => false,
        }
    }

    /// THE POSITIVE POLE: an honest consecutive pair (leaves 5 & 6 of a depth-4 tree, both genuinely
    /// authenticating to the shared root) proves through the DISPATCHED emitted descriptor and
    /// re-verifies. The witness comes from the production [`adjacency_witness`] builder.
    #[test]
    fn honest_adjacency_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(ADJ_NAME).expect("adjacency descriptor dispatches");
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 6);

        let (trace, pis) =
            adjacency_witness(leaves[5], &lp, leaves[6], &up).expect("witness builds");
        assert_eq!(pis[PI_ROOT], root, "the shared authenticated root");
        assert_eq!(pis[PI_IDX_LOWER], BabyBear::from_u64(5));
        assert_eq!(pis[PI_IDX_UPPER], BabyBear::from_u64(6));

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest consecutive witness must prove");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
    }

    /// THE CATCH TOOTH: a genuinely dual-authenticated but NON-CONSECUTIVE pair (leaves 5 & 7 — both
    /// authenticate to the shared root, indices reconstruct to 5 and 7) is REJECTED by the
    /// internalized consecutiveness Last-row boundary (`7 - 5 - 1 = 1 ≠ 0`). Non-vacuous: the
    /// adjacent (5,6) pair is asserted to ACCEPT above.
    #[test]
    fn nonadjacent_pair_refuses_via_dispatch() {
        let desc = descriptor_by_name(ADJ_NAME).expect("dispatch");
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];

        // non-vacuity: the adjacent (5,6) pair accepts.
        let lp6 = auth_path(&levels, 5);
        let up6 = auth_path(&levels, 6);
        let (t_ok, pi_ok) = adjacency_witness(leaves[5], &lp6, leaves[6], &up6).expect("witness");
        assert!(
            !rejects(&desc, &t_ok, &pi_ok),
            "the adjacent (5,6) pair must be accepted — else the canary is vacuous"
        );

        // the wide bracket (5,7): both real Merkle members, but NOT adjacent.
        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 7);
        let (trace, pis) = adjacency_witness(leaves[5], &lp, leaves[7], &up).expect("witness");
        assert_eq!(pis[PI_ROOT], root);
        assert_eq!(pis[PI_IDX_LOWER], BabyBear::from_u64(5));
        assert_eq!(pis[PI_IDX_UPPER], BabyBear::from_u64(7));
        assert!(
            rejects(&desc, &trace, &pis),
            "a non-consecutive wide-bracket pair must be REJECTED (the in-circuit consecutiveness tooth)"
        );
    }

    /// Malformed witnesses (mismatched depth, non-power-of-two) are refused at build time.
    #[test]
    fn malformed_witness_refuses() {
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let lp = auth_path(&levels, 5); // depth 4
        let mut short = lp.clone();
        short.pop(); // depth 3 (not a power of two)
        assert!(adjacency_witness(leaves[5], &short, leaves[6], &short).is_err());
        let up_short: Vec<AdjWitnessStep> = lp[..2].to_vec();
        assert!(adjacency_witness(leaves[5], &lp, leaves[6], &up_short).is_err());
    }
}
