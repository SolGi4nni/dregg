//! Production witness builder for the Lean-emitted composed non-revocation descriptor.
//!
//! `dregg-non-revocation-adjacency::poseidon2-fact-v1` proves two private neighbours are
//! consecutive members of the public depth-general binary revocation tree and the public queried
//! item lies strictly between them. This builder emits **one row per Merkle level**. It never clones
//! one active row as trace padding: a depth-4 witness therefore has four distinct co-path folds and
//! continues to authenticate a 16-leaf tree.
//!
//! Constraint authorship lives exclusively in
//! `metatheory/Dregg2/Circuit/Emit/NonRevocationAdjacencyEmit.lean`. This module only computes the
//! witness columns. It deliberately does not reject a forged bracket, non-adjacent path pair, bad
//! sibling, or wrong root; the Lean-authored descriptor is the judge.

use crate::dsl::revocation::{HALF_P_MINUS_1, NonMembershipWitnessDsl};
use crate::field::BabyBear;
use crate::poseidon2::hash_fact;

/// Dispatch name of the Lean-emitted composed descriptor.
pub const NON_REVOCATION_ADJACENCY_NAME: &str = "dregg-non-revocation-adjacency::poseidon2-fact-v1";

// Adjacency path layout, byte-identical to `AdjacencyMembershipEmit.lean` cols 0..31.
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

/// Ordering columns appended by `NonRevocationAdjacencyEmit.lean`.
pub const X: usize = 32;
pub const DIFF_L: usize = 33;
pub const DIFF_R: usize = 34;
pub const RL: usize = 35;
pub const RR: usize = 36;
pub const NONREV_ADJ_WIDTH: usize = 37;

/// Public inputs stay wire-compatible with the deployed proof: `[root, queried_item]`.
pub const PI_ROOT: usize = 0;
pub const PI_QUERIED_ITEM: usize = 1;
pub const NONREV_ADJ_PI_COUNT: usize = 2;

fn direction(value: u8, side: &str, level: usize) -> Result<(bool, BabyBear), String> {
    match value {
        0 => Ok((false, BabyBear::ZERO)),
        1 => Ok((true, BabyBear::ONE)),
        other => Err(format!(
            "non-revocation {side} direction at level {level} is {other}, expected 0 or 1"
        )),
    }
}

/// Build the 37-column composed non-revocation trace and two public inputs
/// `[expected_root, queried_item]`.
///
/// The two authentication paths are folded in parallel with the deployed revocation-tree node
/// function `hash_fact(left, [right])`. `expected_root` is supplied by the committed tree, not
/// recomputed into the public inputs; a forged leaf/sibling/path reaches a different last-row parent
/// and is refused by the descriptor's two root bindings.
pub fn non_revocation_adjacency_witness(
    witness: &NonMembershipWitnessDsl,
    expected_root: BabyBear,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = witness.left_siblings.len();
    let lengths = [
        ("left directions", witness.left_directions.len()),
        ("right siblings", witness.right_siblings.len()),
        ("right directions", witness.right_directions.len()),
    ];
    for (name, len) in lengths {
        if len != depth {
            return Err(format!(
                "non-revocation path length mismatch: left siblings {depth}, {name} {len}"
            ));
        }
    }
    if depth < 2 || !depth.is_power_of_two() {
        return Err(format!(
            "non-revocation path depth {depth} must be a power of two >= 2 (trace height)"
        ));
    }

    let x = witness.ancestor_hash;
    let diff_l = x - witness.left_neighbor - BabyBear::ONE;
    let diff_r = witness.right_neighbor - x - BabyBear::ONE;
    let half = BabyBear::new(HALF_P_MINUS_1);

    let mut trace = Vec::with_capacity(depth);
    let mut l_cur = witness.left_neighbor;
    let mut u_cur = witness.right_neighbor;
    let mut l_idx_in = BabyBear::ZERO;
    let mut u_idx_in = BabyBear::ZERO;
    let mut pow = BabyBear::ONE;

    for level in 0..depth {
        let (l_is_right, l_dir) = direction(witness.left_directions[level], "left", level)?;
        let l_sib = witness.left_siblings[level];
        let (l_left, l_right) = if l_is_right {
            (l_sib, l_cur)
        } else {
            (l_cur, l_sib)
        };
        let l_par = hash_fact(l_left, &[l_right]);
        let l_idx_out = l_idx_in + l_dir * pow;

        let (u_is_right, u_dir) = direction(witness.right_directions[level], "right", level)?;
        let u_sib = witness.right_siblings[level];
        let (u_left, u_right) = if u_is_right {
            (u_sib, u_cur)
        } else {
            (u_cur, u_sib)
        };
        let u_par = hash_fact(u_left, &[u_right]);
        let u_idx_out = u_idx_in + u_dir * pow;
        let pow2 = pow + pow;

        let mut row = vec![BabyBear::ZERO; NONREV_ADJ_WIDTH];
        row[L_CUR] = l_cur;
        row[L_SIB] = l_sib;
        row[L_DIR] = l_dir;
        row[L_LEFT] = l_left;
        row[L_RIGHT] = l_right;
        row[L_PAR] = l_par;
        row[L_IDX_IN] = l_idx_in;
        row[L_IDX_OUT] = l_idx_out;
        row[U_CUR] = u_cur;
        row[U_SIB] = u_sib;
        row[U_DIR] = u_dir;
        row[U_LEFT] = u_left;
        row[U_RIGHT] = u_right;
        row[U_PAR] = u_par;
        row[U_IDX_IN] = u_idx_in;
        row[U_IDX_OUT] = u_idx_out;
        row[POW] = pow;
        row[POW2] = pow2;

        // Range lookups fire on every row. The ordering equations are First-row boundaries against
        // the actual leaves; repeating these scalar witnesses simply supplies every lookup row.
        row[X] = x;
        row[DIFF_L] = diff_l;
        row[DIFF_R] = diff_r;
        row[RL] = half - diff_l;
        row[RR] = half - diff_r;
        trace.push(row);

        l_cur = l_par;
        u_cur = u_par;
        l_idx_in = l_idx_out;
        u_idx_in = u_idx_out;
        pow = pow2;
    }

    Ok((trace, vec![expected_root, x]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dsl::revocation::{DslRevocationTree, TREE_DEPTH};

    #[test]
    fn deployed_depth_four_emits_four_distinct_path_rows() {
        assert_eq!(
            TREE_DEPTH, 4,
            "the deployed revocation tree must remain depth 4"
        );
        let tree = DslRevocationTree::new(
            [100u32, 300, 500, 700]
                .into_iter()
                .map(BabyBear::new)
                .collect(),
            TREE_DEPTH,
        );
        let witness = tree
            .prove_non_membership(&BabyBear::new(400))
            .expect("400 is strictly between two deployed-tree leaves");
        let (trace, pis) = non_revocation_adjacency_witness(&witness, tree.root())
            .expect("depth-4 witness builds");
        assert_eq!(trace.len(), TREE_DEPTH, "one trace row per Merkle level");
        assert_eq!(trace[0][L_CUR], witness.left_neighbor);
        for level in 1..TREE_DEPTH {
            assert_eq!(
                trace[level][L_CUR],
                trace[level - 1][L_PAR],
                "row {level} must fold the prior row's parent, never clone an active row"
            );
        }
        assert_eq!(trace.last().unwrap()[L_PAR], tree.root());
        assert_eq!(trace.last().unwrap()[U_PAR], tree.root());
        assert_eq!(pis, vec![tree.root(), BabyBear::new(400)]);
    }
}
