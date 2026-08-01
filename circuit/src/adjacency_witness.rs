//! Rust witness builder for the emitted **WIDE neighbor-adjacency** descriptor
//! (`dregg-membership-adjacency-wide::node8-v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/AdjacencyMembershipWideEmit.lean`).
//!
//! The adjacency descriptor is the sorted-set NON-membership lift: it proves two leaves
//! `leaf_lower` (at reconstructed `idx_lower`) and `leaf_upper` (at `idx_upper`) are CONSECUTIVE
//! (`idx_upper == idx_lower + 1`) leaves of a shared binary-Poseidon2 root — the in-circuit tooth
//! that turns `lower < candidate < upper` into a sound non-membership witness (no set member can
//! sit strictly between two adjacent leaves).
//!
//! # ⚑ FLAG DAY: every value in this tree used to be ONE BabyBear felt
//!
//! The retired construction chained `poseidon2::hash_2_to_1` — a genuine 16-wide permutation whose
//! `state.state[0]` was kept and whose other fifteen lanes were discarded — level to level, and the
//! descriptor's per-level lookup was `chipLookupTupleNarrow [left, right] par`, the arity-2 NARROW
//! bus, which binds `out0` alone. Leaves and root were one felt each.
//!
//! So every node lived in a codomain of size `p = 15·2^27 + 1`, `log2 p = 30.9069`:
//!
//! | | retired (1 felt) | deployed (`node8`, 8 felts) |
//! |---|---|---|
//! | codomain | 30.907 bits | 247.255 bits |
//! | **COLLISION (binding)** | **2^15.45** | **2^123.63** |
//! | second-preimage | 2^30.91 | 2^247.26 |
//!
//! ⚑ The COLLISION figure is the binding one, because the attacker chooses BOTH sides: they mint a
//! leaf pair whose parent collides with a genuine adjacent leaf pair of the committed tree, present
//! it at the same index — genuinely consecutive, so the catch tooth is SATISFIED — and choose it to
//! bracket a key that IS in the set. `circuit/tests/adjacency_forge_tooth.rs` exhibits exactly that,
//! at the deployed parameter, and shows `node8` refusing the same forgery.
//!
//! The node is now `adjacency_node8(l, r) = A16(l ‖ r)` — one arity-16 `node8` absorb, since two
//! 8-felt children are exactly `CHIP_RATE = 16` felts; it is the same `absorb16` the heap/cap/fields
//! and 4-ary membership trees already ride. All eight output lanes are bound at every level, the
//! level chain is eight windows (was one), and both leaf PIs widen with the root (a 1-felt bracket
//! key would re-narrow the gate at its boundary no matter how wide the interior is).
//!
//! [`adjacency_witness`] emits the 88-column trace (one binary-tree level per row: two parallel
//! authentication paths lower ‖ upper + the shared power-of-two index accumulator) and the
//! 26-element public-input vector
//! `[root0..7, leaf_lower0..7, leaf_upper0..7, idx_lower, idx_upper]` the descriptor pins. It is
//! purely mechanical — it does NOT enforce consecutiveness or equal roots; the DESCRIPTOR's
//! Last-row boundaries (the internalized `u_idx_out - l_idx_out - 1 == 0` catch tooth and the
//! root pins) are the judge, so a non-adjacent or wrong-root pair yields a well-formed but
//! UNSATISFYING trace that `verify_vm_descriptor2` rejects.

use crate::descriptor_ir2::EffectVmDescriptor2;
use crate::descriptor_ir2::parse_vm_descriptor2;
use crate::field::BabyBear;
use crate::membership_descriptor_4ary::{DIGEST_W, Digest8, absorb16};

// --- Trace column layout (must match `AdjacencyMembershipWideEmit.lean` §1). Every Merkle value
//     is an 8-lane GROUP; the direction bit and the index accumulators stay scalars (a position is
//     one integer at any digest width). ---
/// Lower path: the 8-felt running hash (row 0 = `leaf_lower`).
pub const L_CUR: usize = 0;
/// Lower path: the 8-felt co-path sibling at this level.
pub const L_SIB: usize = 8;
/// Lower path: the direction bit (`1` ⇒ the running hash is the RIGHT child).
pub const L_DIR: usize = 16;
/// Lower path: the ordered 8-felt left child.
pub const L_LEFT: usize = 17;
/// Lower path: the ordered 8-felt right child.
pub const L_RIGHT: usize = 25;
/// Lower path: the 8-felt parent `A16(left ‖ right)`.
pub const L_PAR: usize = 33;
/// Lower path: the index accumulated before this level.
pub const L_IDX_IN: usize = 41;
/// Lower path: the index accumulated including this level.
pub const L_IDX_OUT: usize = 42;
/// Upper path: the mirror of the lower block, `+43`.
pub const U_CUR: usize = 43;
pub const U_SIB: usize = 51;
pub const U_DIR: usize = 59;
pub const U_LEFT: usize = 60;
pub const U_RIGHT: usize = 68;
pub const U_PAR: usize = 76;
pub const U_IDX_IN: usize = 84;
pub const U_IDX_OUT: usize = 85;
/// `2^level` for this row (row 0 = 1).
pub const POW: usize = 86;
/// `2·pow` (the helper feeding the next row's `pow`).
pub const POW2: usize = 87;
/// Total main-trace width: ten 8-lane groups + two direction bits + four index scalars + pow/pow2.
///
/// ⚑ FLAG DAY: was **18** (every Merkle value one felt).
pub const ADJ_WIDTH: usize = 88;

// --- PI indices. ---
/// PI slots 0..8: the shared committed **8-felt** root.
pub const PI_ROOT: usize = 0;
/// PI slots 8..16: the **8-felt** lower neighbor leaf.
pub const PI_LEAF_LOWER: usize = 8;
/// PI slots 16..24: the **8-felt** upper neighbor leaf.
pub const PI_LEAF_UPPER: usize = 16;
/// PI slot: the reconstructed lower index.
pub const PI_IDX_LOWER: usize = 24;
/// PI slot: the reconstructed upper index.
pub const PI_IDX_UPPER: usize = 25;
/// Public-input count.
///
/// ⚑ FLAG DAY: was **5** (one felt each for root and the two leaves).
pub const ADJ_PI_COUNT: usize = 26;

/// **THE WIRE DISPATCH IDENTITY** and the emitted descriptor's own `name`, for the wide family.
///
/// ⚑ FLAG DAY: this string CHANGED at the `node8` cutover (it was
/// `dregg-membership-adjacency::poseidon2-v1`). The old identity no longer resolves, so a producer
/// or a stored proof from the one-felt epoch is answered `None` by
/// [`crate::descriptor_by_name::descriptor_by_name`] and REFUSED rather than reinterpreted under a
/// descriptor with different semantics.
pub const ADJACENCY_WIDE_NAME: &str = "dregg-membership-adjacency-wide::node8-v1";

/// Exact bytes emitted and byte-pinned by
/// `Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit.ADJACENCY_WIDE_GOLDEN`.
pub const ADJACENCY_WIDE_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/by-name/adjacency-membership-wide.json");

/// Parse the Lean-authored, depth-uniform WIDE adjacency descriptor. The depth is represented by
/// the trace height, so Rust never rewrites the emitted artifact.
pub fn adjacency_wide_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ADJACENCY_WIDE_DESCRIPTOR_JSON)
        .expect("Lean-emitted wide adjacency descriptor must parse")
}

/// **The binary `node8` fold** — one arity-16 `node8` chip absorb over the two ordered 8-felt
/// children, returning ALL EIGHT output lanes. Lean twin: `wideNode2`.
///
/// Two 8-felt children are exactly `CHIP_RATE = 16` felts, so a binary level is ONE absorb — no
/// balanced two-stage fold is needed (unlike the 4-ary membership family, whose four children are
/// 32 felts). It is byte-identical to the absorb the descriptor's `chipLookupTupleN` lookup
/// enforces, so a forged lane has no serving chip row → UNSAT.
pub fn adjacency_node8(left: &Digest8, right: &Digest8) -> Digest8 {
    absorb16(left, right)
}

/// One Merkle authentication step for an adjacency path: the co-path `sibling` (an 8-felt digest)
/// at this level and whether the running hash is the RIGHT child (`dir`; `dir` at level ℓ is bit ℓ
/// of the leaf index).
#[derive(Clone, Copy, Debug)]
pub struct AdjWitnessStep {
    /// The co-path sibling at this level — a FULL 8-felt digest.
    pub sibling: Digest8,
    /// `true` ⇒ the running hash is the RIGHT child at this level.
    pub dir: bool,
}

fn bit(b: bool) -> BabyBear {
    if b { BabyBear::ONE } else { BabyBear::ZERO }
}

/// Walk a leaf→root path, returning `(root8, reconstructed_index)` (the index is the little-endian
/// concatenation of the per-level direction bits).
pub fn adjacency_walk(leaf: Digest8, path: &[AdjWitnessStep]) -> (Digest8, u64) {
    let mut cur = leaf;
    let mut idx: u64 = 0;
    for (level, step) in path.iter().enumerate() {
        cur = if step.dir {
            adjacency_node8(&step.sibling, &cur)
        } else {
            adjacency_node8(&cur, &step.sibling)
        };
        if step.dir {
            idx |= 1u64 << level;
        }
    }
    (cur, idx)
}

/// Build the 88-column adjacency trace + the 26-element public-input vector
/// `[root0..7, leaf_lower0..7, leaf_upper0..7, idx_lower, idx_upper]` for the emitted
/// `dregg-membership-adjacency-wide::node8-v1` descriptor.
///
/// `lower_path` / `upper_path` are the leaf→root authentication paths of the two neighbor leaves in
/// a shared binary-Poseidon2 tree ([`adjacency_node8`] nodes). Both paths must have the same
/// power-of-two depth ≥ 2. The published root (`pis[PI_ROOT..PI_ROOT + 8]`) is the LOWER path's
/// authenticated root; if the two paths do not reach the same root the descriptor's Last-row
/// `U_PAR[k] == PI_ROOT + k` pins reject (all eight lanes), and if the indices are not consecutive
/// the internalized catch tooth rejects — this builder does not pre-judge either.
pub fn adjacency_witness(
    leaf_lower: Digest8,
    lower_path: &[AdjWitnessStep],
    leaf_upper: Digest8,
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
        let l_par = adjacency_node8(&l_left, &l_right);
        let l_idx_out = l_idx_in + l_dir * pow;

        let u_dir = bit(us.dir);
        let (u_left, u_right) = if us.dir {
            (us.sibling, u_cur)
        } else {
            (u_cur, us.sibling)
        };
        let u_par = adjacency_node8(&u_left, &u_right);
        let u_idx_out = u_idx_in + u_dir * pow;

        let pow2 = pow + pow;

        let mut row = vec![BabyBear::ZERO; ADJ_WIDTH];
        row[L_CUR..L_CUR + DIGEST_W].copy_from_slice(&l_cur);
        row[L_SIB..L_SIB + DIGEST_W].copy_from_slice(&ls.sibling);
        row[L_DIR] = l_dir;
        row[L_LEFT..L_LEFT + DIGEST_W].copy_from_slice(&l_left);
        row[L_RIGHT..L_RIGHT + DIGEST_W].copy_from_slice(&l_right);
        row[L_PAR..L_PAR + DIGEST_W].copy_from_slice(&l_par);
        row[L_IDX_IN] = l_idx_in;
        row[L_IDX_OUT] = l_idx_out;
        row[U_CUR..U_CUR + DIGEST_W].copy_from_slice(&u_cur);
        row[U_SIB..U_SIB + DIGEST_W].copy_from_slice(&us.sibling);
        row[U_DIR] = u_dir;
        row[U_LEFT..U_LEFT + DIGEST_W].copy_from_slice(&u_left);
        row[U_RIGHT..U_RIGHT + DIGEST_W].copy_from_slice(&u_right);
        row[U_PAR..U_PAR + DIGEST_W].copy_from_slice(&u_par);
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
    let mut pis = Vec::with_capacity(ADJ_PI_COUNT);
    pis.extend_from_slice(&root_l);
    pis.extend_from_slice(&leaf_lower);
    pis.extend_from_slice(&leaf_upper);
    pis.push(BabyBear::from_u64(idx_l));
    pis.push(BabyBear::from_u64(idx_u));
    debug_assert_eq!(pis.len(), ADJ_PI_COUNT);
    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2};
    use crate::refusal::{Outcome, classify};

    /// Build a full binary tree over `leaves` (length a power of two) under [`adjacency_node8`];
    /// return every level (level 0 = leaves, last = `[root]`).
    pub(crate) fn build_tree(leaves: &[Digest8]) -> Vec<Vec<Digest8>> {
        assert!(leaves.len().is_power_of_two());
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let mut next = Vec::with_capacity(cur.len() / 2);
            for pair in cur.chunks(2) {
                next.push(adjacency_node8(&pair[0], &pair[1]));
            }
            levels.push(next);
        }
        levels
    }

    pub(crate) fn auth_path(levels: &[Vec<Digest8>], mut index: usize) -> Vec<AdjWitnessStep> {
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

    fn sample_leaves(n: usize) -> Vec<Digest8> {
        (0..n)
            .map(|i| core::array::from_fn(|k| BabyBear::new((i as u32 + 1) * 10 + k as u32)))
            .collect()
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails
    /// to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// The emitted artifact carries the widened shape, and the retired identity is GONE from
    /// dispatch (a pre-cutover proof identity is refused, not reinterpreted).
    #[test]
    fn wide_descriptor_shape_and_retired_name_refused() {
        let desc = descriptor_by_name(ADJACENCY_WIDE_NAME).expect("wide adjacency dispatches");
        assert_eq!(desc.trace_width, ADJ_WIDTH);
        assert_eq!(desc.public_input_count, ADJ_PI_COUNT);
        assert_eq!(desc.name, ADJACENCY_WIDE_NAME);
        assert!(
            descriptor_by_name("dregg-membership-adjacency::poseidon2-v1").is_none(),
            "the RETIRED one-felt adjacency identity must no longer resolve"
        );
    }

    /// THE POSITIVE POLE: an honest consecutive pair (leaves 5 & 6 of a depth-4 tree, both genuinely
    /// authenticating to the shared root) proves through the DISPATCHED emitted descriptor and
    /// re-verifies. The witness comes from the production [`adjacency_witness`] builder.
    #[test]
    fn honest_adjacency_proves_and_verifies_via_dispatch() {
        let desc =
            descriptor_by_name(ADJACENCY_WIDE_NAME).expect("adjacency descriptor dispatches");
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 6);

        let (trace, pis) =
            adjacency_witness(leaves[5], &lp, leaves[6], &up).expect("witness builds");
        assert_eq!(
            &pis[PI_ROOT..PI_ROOT + DIGEST_W],
            &root[..],
            "the shared authenticated 8-felt root"
        );
        assert_eq!(
            &pis[PI_LEAF_LOWER..PI_LEAF_LOWER + DIGEST_W],
            &leaves[5][..]
        );
        assert_eq!(
            &pis[PI_LEAF_UPPER..PI_LEAF_UPPER + DIGEST_W],
            &leaves[6][..]
        );
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
        let desc = descriptor_by_name(ADJACENCY_WIDE_NAME).expect("dispatch");
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
        assert_eq!(&pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);
        assert_eq!(pis[PI_IDX_LOWER], BabyBear::from_u64(5));
        assert_eq!(pis[PI_IDX_UPPER], BabyBear::from_u64(7));
        assert!(
            rejects(&desc, &trace, &pis),
            "a non-consecutive wide-bracket pair must be REJECTED (the in-circuit consecutiveness tooth)"
        );
    }

    /// EVERY LANE OF THE ROOT IS PINNED: a proof whose published root agrees with the honest one on
    /// lane 0 but differs at lane 7 is REFUSED. Under the retired descriptor lane 7 did not exist,
    /// so this assignment class was admitted wholesale.
    #[test]
    fn root_lane_seven_is_bound_not_just_lane_zero() {
        let desc = descriptor_by_name(ADJACENCY_WIDE_NAME).expect("dispatch");
        let leaves = sample_leaves(16);
        let levels = build_tree(&leaves);
        let lp = auth_path(&levels, 5);
        let up = auth_path(&levels, 6);
        let (trace, pis) = adjacency_witness(leaves[5], &lp, leaves[6], &up).expect("witness");
        assert!(!rejects(&desc, &trace, &pis), "non-vacuity: honest accepts");

        let mut tampered = pis.clone();
        tampered[PI_ROOT + 7] = tampered[PI_ROOT + 7] + BabyBear::ONE;
        assert_eq!(
            tampered[PI_ROOT], pis[PI_ROOT],
            "the tamper must be invisible at lane 0 — that is the whole point"
        );
        assert!(
            rejects(&desc, &trace, &tampered),
            "a root differing ONLY at lane 7 must be REFUSED — all eight lanes are pinned"
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
