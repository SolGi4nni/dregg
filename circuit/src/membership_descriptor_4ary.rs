//! Depth-GENERAL **4-ary, 8-felt (`node8`)** Poseidon2 Merkle-membership descriptor (IR-v2) —
//! THE production membership tree.
//!
//! ## What this closes (felt-width finding #9)
//!
//! Until the WIDE cutover this family's per-level node was **one BabyBear felt**:
//! `hash_4_to_1(children)` returned `state.state[0]`, `chip4(&children)[0]` discarded seven of the
//! chip's eight output lanes, and the continuity window chained ONE column. Every interior node and
//! the committed root were therefore ~31-bit commitments. That is not a hash-image question — the
//! bottleneck was the **output width**: a perfect random oracle with a 31-bit codomain is
//! second-preimaged in 2^31 queries and *collided in 2^15.5*, which is milliseconds. An attacker who
//! contributes to (or mints) a subtree birthday-collides an interior node and presents a second,
//! distinct authentication path reaching the SAME authorized root for a key that was never in the
//! set. `membership_forge_tooth.rs` exhibits exactly that collision.
//!
//! **Every node of this tree is now a full 8-felt Poseidon2 digest.** The one-felt path is DELETED,
//! not deprecated: `hash_4_to_1`-chained roots, the 11-wide trace, and the 2-PI `[leaf, root]`
//! binding no longer exist anywhere in the membership family.
//!
//! ## The widened scheme (authored in Lean — LAW #1)
//!
//! The algebra is `Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit`; Rust parses the emitted IR2
//! bytes and supplies witnesses, and constructs no constraints. Four 8-felt children are 32 felts —
//! double the chip rate (`CHIP_RATE = 16`) — so the node fold is a balanced pair of arity-16
//! absorbs, all three bound at full output width by `chipLookupTupleN`:
//!
//! ```text
//! node8_4ary(c0,c1,c2,c3) = A16( A16(c0 ‖ c1) ‖ A16(c2 ‖ c3) )
//! ```
//!
//! where `A16` is [`chip_absorb_all_lanes`] at [`CHIP_NODE8_ARITY`] — the SAME arity-16 `node8`
//! absorb the deployed heap/cap/fields trees already ride. The Lean keystones are
//! `wideNodeFold_sound` (a row's three lookups force the genuine `wideFold4`),
//! `wGroups_arranged` (the four 8-felt children ARE the positional arrangement, every lane), and
//! `wCont_all_zero_iff` (the chain rides all 8 lanes, where the deployed family chained lane 0).
//!
//! ## The layout (one 4-ary Merkle level per row; 9 8-lane groups + 2 bits = 90 columns)
//!
//! | cols    | name        | meaning                                                          |
//! |---------|-------------|------------------------------------------------------------------|
//! | 0..8    | cur8        | running 8-felt node (row 0 = the leaf; bound to PIs 0..8)         |
//! | 8..32   | sib0..sib2  | the three co-path 8-felt siblings at this level                   |
//! | 32,33   | b0,b1       | the two position bits (`position = b0 + 2·b1 ∈ {0,1,2,3}`)        |
//! | 34..66  | c0..c3      | the ordered 8-felt children (`children[position] = cur8`)         |
//! | 66..74  | h01         | stage-1 left  `A16(c0 ‖ c1)` — all 8 lanes bound                   |
//! | 74..82  | h23         | stage-1 right `A16(c2 ‖ c3)` — all 8 lanes bound                   |
//! | 82..90  | par8        | `A16(h01 ‖ h23)` — the 8-felt parent (last row bound to PIs 8..16)|
//!
//! Position rides TWO binary bits so the child-selection gates have integer coefficients. The
//! per-row bit-binary and child-selection gates are TRANSITION constraints (vacuous on the last
//! row), so they are re-lowered as `Last`-row boundaries — without that the top level's children
//! are unconstrained.

use crate::descriptor_ir2::{
    CHIP_NODE8_ARITY, CHIP_OUT_LANES, EffectVmDescriptor2, chip_absorb_all_lanes,
    parse_vm_descriptor2,
};
use crate::field::BabyBear;

/// The membership digest width: every node of the tree is this many felts.
pub const DIGEST_W: usize = CHIP_OUT_LANES; // 8

/// An 8-felt membership node (leaf, sibling, interior node, or root).
pub type Digest8 = [BabyBear; DIGEST_W];

// ---- Column layout (one 4-ary Merkle level per row); mirrors the Lean `w*` column defs. ----
/// Running 8-felt node, lanes `CUR..CUR+8` (row 0 = the leaf).
pub const CUR: usize = 0;
/// First co-path 8-felt sibling, lanes `SIB0..SIB0+8`.
pub const SIB0: usize = 8;
/// Second co-path 8-felt sibling.
pub const SIB1: usize = 16;
/// Third co-path 8-felt sibling.
pub const SIB2: usize = 24;
/// Low position bit.
pub const B0: usize = 32;
/// High position bit (`position = b0 + 2·b1`).
pub const B1: usize = 33;
/// Ordered 8-felt child 0.
pub const C0: usize = 34;
/// Ordered 8-felt child 1.
pub const C1: usize = 42;
/// Ordered 8-felt child 2.
pub const C2: usize = 50;
/// Ordered 8-felt child 3.
pub const C3: usize = 58;
/// Stage-1 left digest `A16(c0 ‖ c1)`.
pub const H01: usize = 66;
/// Stage-1 right digest `A16(c2 ‖ c3)`.
pub const H23: usize = 74;
/// The 8-felt parent `A16(h01 ‖ h23)`.
pub const PAR: usize = 82;
/// Total main-trace width (9 8-lane groups + 2 position bits).
pub const MEMBERSHIP_4ARY_WIDTH: usize = 90;

/// PI slots `0..8`: the 8-felt membership leaf (row-0 `cur8`).
pub const PI_LEAF: usize = 0;
/// PI slots `8..16`: the committed 8-felt root (last-row `par8`).
pub const PI_ROOT: usize = 8;
/// Public-input count: `[leaf0..leaf7, root0..root7]`.
pub const MEMBERSHIP_4ARY_PI_COUNT: usize = 16;

/// THE WIRE DISPATCH PREFIX. Every supported depth resolves to the same Lean-emitted,
/// depth-uniform WIDE descriptor (the depth rides the trace height).
///
/// ⚑ FLAG DAY: this string CHANGED at the `node8` cutover (it was
/// `merkle-membership::poseidon2-4ary-general-depth`). The old identity no longer resolves, so a
/// producer or a stored proof from the one-felt epoch is answered `UnknownAir` and REFUSED rather
/// than reinterpreted under a descriptor with different semantics.
///
/// ⚠ THIS IS *NOT* THE EMITTED DESCRIPTOR'S OWN `name`. Use [`membership_4ary_dispatch_name`] to
/// build a wire identity — never `membership_descriptor_of_depth_4ary(d).name`. See that function
/// for the production wound the distinction cost.
pub const MEMBERSHIP_4ARY_NAME_PREFIX: &str =
    "merkle-membership::poseidon2-4ary-wide-general-depth";

/// **THE WIRE DISPATCH IDENTITY** a producer must put in a proof wire's
/// `predicate`/`descriptor_name`, and the string
/// [`crate::descriptor_by_name::descriptor_by_name`] resolves.
///
/// ⚑ IT IS DELIBERATELY DIFFERENT FROM THE EMITTED DESCRIPTOR'S `name`, and the two were conflated
/// in production. Before `9ba02881b` the 4-ary membership descriptor was *built in Rust* and its
/// `name` WAS this string, so producers wrote `predicate: desc.name` and it routed. That commit
/// replaced it with the Lean-emitted artifact (LAW #1 — the AIR is authored in Lean), whose own
/// name is `dregg-merkle-membership-4ary-wide-general::v1`. `descriptor_by_name` still routes ONLY
/// the prefix above, so every `desc.name` producer silently began emitting an identity NO CONSUMER
/// CAN RESOLVE: `dregg_bridge::present::verify_ir2_issuer_wire` answers `UnknownAir` and
/// `verify_with_predicate` refuses an HONEST proof. It compiled, it proved, and it failed only at
/// the far end of the wire.
///
/// The kernel's own verifier (`turn/src/executor/membership_verifier.rs`) always built the name
/// this way; this function exists so every other producer reads the identity from the SAME place
/// instead of re-deriving it or reaching for `.name`.
pub fn membership_4ary_dispatch_name(depth: usize) -> String {
    format!("{MEMBERSHIP_4ARY_NAME_PREFIX}{depth}")
}

/// Exact bytes emitted and byte-pinned by
/// `Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit.MEMBERSHIP_4ARY_WIDE_GOLDEN`.
pub const MEMBERSHIP_4ARY_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/by-name/merkle-membership-4ary-wide-general.json");

/// Parse the Lean-authored, depth-uniform WIDE membership descriptor. The depth is represented by
/// the trace height, so Rust never rewrites the emitted artifact.
pub fn membership_descriptor_of_depth_4ary(depth: usize) -> EffectVmDescriptor2 {
    assert!(
        depth >= 2 && depth.is_power_of_two(),
        "membership depth must be a power of two ≥ 2"
    );
    parse_vm_descriptor2(MEMBERSHIP_4ARY_DESCRIPTOR_JSON)
        .expect("Lean-emitted wide 4-ary membership descriptor must parse")
}

/// **`A16`** — one arity-16 `node8` chip absorb over two 8-felt groups, returning ALL EIGHT output
/// lanes. This is the single deployed compression the wide fold chains on, and it is byte-identical
/// to the absorb the descriptor's `chipLookupTupleN` lookups enforce (`chip_absorb_all_lanes` is
/// the same function the chip table's witness generator runs), so a forged lane has no serving chip
/// row → UNSAT.
pub fn absorb16(left: &Digest8, right: &Digest8) -> Digest8 {
    let mut ins = [BabyBear::ZERO; CHIP_NODE8_ARITY];
    ins[..DIGEST_W].copy_from_slice(left);
    ins[DIGEST_W..].copy_from_slice(right);
    chip_absorb_all_lanes(CHIP_NODE8_ARITY, &ins)
}

/// **THE 4-ary `node8` fold** — the widened node function, the Rust twin of Lean's `wideFold4`:
///
/// ```text
/// node8_4ary(c0,c1,c2,c3) = A16( A16(c0 ‖ c1) ‖ A16(c2 ‖ c3) )
/// ```
///
/// All 32 child felts enter the preimage and all 8 output lanes are the node. There is NO lane-0
/// projection: the per-node collision floor is the full 8-felt width, not 31 bits.
pub fn node8_4ary(children: &[Digest8; 4]) -> Digest8 {
    let h01 = absorb16(&children[0], &children[1]);
    let h23 = absorb16(&children[2], &children[3]);
    absorb16(&h01, &h23)
}

/// Arrange the four ordered 8-felt children at a level: `children[position] = cur8`, the three
/// siblings fill the remaining slots in order. `position` must be `< 4`. Lean twin: `wArrange8`.
fn arrange_children(cur: &Digest8, siblings: &[Digest8; 3], position: u8) -> [Digest8; 4] {
    debug_assert!(position < 4);
    let mut children = [[BabyBear::ZERO; DIGEST_W]; 4];
    children[position as usize] = *cur;
    let mut sib_idx = 0;
    for (j, slot) in children.iter_mut().enumerate() {
        if j != position as usize {
            *slot = siblings[sib_idx];
            sib_idx += 1;
        }
    }
    children
}

/// The depth-`d` **8-felt** root implied by an 8-felt leaf + authentication path, under the
/// descriptor's `node8_4ary` fold.
pub fn membership_root_4ary(leaf: Digest8, siblings: &[[Digest8; 3]], positions: &[u8]) -> Digest8 {
    let mut cur = leaf;
    for (sibs, &pos) in siblings.iter().zip(positions.iter()) {
        let children = arrange_children(&cur, sibs, pos);
        cur = node8_4ary(&children);
    }
    cur
}

/// Build the depth-`d` **4-ary `node8`** membership base trace + public inputs
/// `[leaf0..leaf7, root0..root7]`.
///
/// One row per level; every row carries the two position bits, the four genuine ordered 8-felt
/// children, both stage-1 digests, and the 8-felt parent. `siblings.len()` must equal
/// `positions.len()`, each position must be `< 4`, and the depth must be a power of two ≥ 2 (the
/// trace-height requirement).
pub fn membership_witness_4ary(
    leaf: Digest8,
    siblings: &[[Digest8; 3]],
    positions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = siblings.len();
    if depth != positions.len() {
        return Err(format!(
            "siblings/positions length mismatch ({depth} vs {})",
            positions.len()
        ));
    }
    if depth < 2 || !depth.is_power_of_two() {
        return Err(format!(
            "membership depth {depth} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut cur = leaf;
    for (sibs, &pos) in siblings.iter().zip(positions.iter()) {
        if pos >= 4 {
            return Err(format!("position {pos} must be < 4"));
        }
        let children = arrange_children(&cur, sibs, pos);
        let h01 = absorb16(&children[0], &children[1]);
        let h23 = absorb16(&children[2], &children[3]);
        let par = absorb16(&h01, &h23);

        let mut row = vec![BabyBear::ZERO; MEMBERSHIP_4ARY_WIDTH];
        row[CUR..CUR + DIGEST_W].copy_from_slice(&cur);
        row[SIB0..SIB0 + DIGEST_W].copy_from_slice(&sibs[0]);
        row[SIB1..SIB1 + DIGEST_W].copy_from_slice(&sibs[1]);
        row[SIB2..SIB2 + DIGEST_W].copy_from_slice(&sibs[2]);
        row[B0] = BabyBear::new((pos & 1) as u32);
        row[B1] = BabyBear::new(((pos >> 1) & 1) as u32);
        row[C0..C0 + DIGEST_W].copy_from_slice(&children[0]);
        row[C1..C1 + DIGEST_W].copy_from_slice(&children[1]);
        row[C2..C2 + DIGEST_W].copy_from_slice(&children[2]);
        row[C3..C3 + DIGEST_W].copy_from_slice(&children[3]);
        row[H01..H01 + DIGEST_W].copy_from_slice(&h01);
        row[H23..H23 + DIGEST_W].copy_from_slice(&h23);
        row[PAR..PAR + DIGEST_W].copy_from_slice(&par);
        trace.push(row);
        cur = par;
    }
    debug_assert!(trace.len().is_power_of_two());
    let mut pis = Vec::with_capacity(MEMBERSHIP_4ARY_PI_COUNT);
    pis.extend_from_slice(&leaf);
    pis.extend_from_slice(&cur);
    Ok((trace, pis))
}

/// Build a deterministic honest depth-`depth` witness: 8-felt siblings, mixed positions
/// (`pos = i % 4`), and the `node8_4ary`-folded root.
///
/// Returns `(siblings, positions, root)`.
pub fn create_test_witness(leaf: Digest8, depth: usize) -> (Vec<[Digest8; 3]>, Vec<u8>, Digest8) {
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    let mut cur = leaf;
    for i in 0..depth {
        let pos = (i % 4) as u8;
        let sibs: [Digest8; 3] = core::array::from_fn(|s| {
            core::array::from_fn(|k| BabyBear::new((i * 24 + s * 8 + k + 1) as u32))
        });
        let children = arrange_children(&cur, &sibs, pos);
        cur = node8_4ary(&children);
        siblings.push(sibs);
        positions.push(pos);
    }
    (siblings, positions, cur)
}

/// Widen a 32-byte value into the 8-felt membership leaf domain — the SAME composition
/// `dregg_commit::typed::compress_member` folds (`A16(canonical_32_to_felts_8(v) ‖ 0⁸)`, all eight
/// lanes). Re-exported here so leaf-domain producers inside `dregg-circuit` (which cannot depend on
/// `dregg-commit`) compute the identical leaf.
pub fn compress_member_felts(limbs8: &Digest8) -> Digest8 {
    absorb16(limbs8, &[BabyBear::ZERO; DIGEST_W])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::{
        CHIP_RATE, LookupSpec, MemBoundaryWitness, TID_P2, TID_P2_NARROW, VmConstraint2,
        prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::lean_descriptor_air::LeanExpr;
    use crate::refusal::{Outcome, classify};

    fn d8(base: u32) -> Digest8 {
        core::array::from_fn(|k| BabyBear::new(base + k as u32))
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof
    /// fails to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// STEP 1 — THE `node8` CHIP KAT: the fold's three stages ARE arity-16 chip absorbs, all eight
    /// lanes distinct and every one of the 32 child felts load-bearing. This is the hash-level
    /// width the tree-level width builds on: perturbing ANY lane of ANY child moves ALL 8 lanes of
    /// the parent, so there is no lane-0 waist anywhere in the node.
    #[test]
    fn node8_fold_binds_all_thirty_two_child_felts_across_all_eight_lanes() {
        let children = [d8(1_000), d8(2_000), d8(3_000), d8(4_000)];
        let par = node8_4ary(&children);

        // Eight genuinely distinct output lanes — catches a replicated / `[x]*8` widening.
        for i in 0..DIGEST_W {
            for j in (i + 1)..DIGEST_W {
                assert_ne!(par[i], par[j], "parent lanes {i},{j} collide — not 8 felts");
            }
        }
        // Every child felt is bound, in every output lane.
        for c in 0..4 {
            for k in 0..DIGEST_W {
                let mut alt = children;
                alt[c][k] += BabyBear::ONE;
                let alt_par = node8_4ary(&alt);
                for i in 0..DIGEST_W {
                    assert_ne!(
                        par[i], alt_par[i],
                        "parent lane {i} unchanged after perturbing child {c} lane {k} \
                         — that input felt is dead"
                    );
                }
            }
        }
        // The fold IS the two-stage arity-16 chip composition (the Lean `wideFold4`).
        let h01 = absorb16(&children[0], &children[1]);
        let h23 = absorb16(&children[2], &children[3]);
        assert_eq!(par, absorb16(&h01, &h23));
    }

    /// STEP 2 — THE POSITIVE POLE + ROUND-TRIP (anti-vacuity): an honest depth-`d` witness proves
    /// and verifies at the deployed prover, AND its committed root ROUND-TRIPS — the 16 published
    /// PIs are exactly the leaf and the independently recomputed `membership_root_4ary` fold, and
    /// the trace's last-row parent group IS that root.
    #[test]
    fn honest_wide_witness_proves_verifies_and_round_trips_depths_2_4_8() {
        for depth in [2usize, 4, 8] {
            let leaf = d8(0xA11CE + depth as u32);
            let (siblings, positions, root) = create_test_witness(leaf, depth);
            assert_eq!(siblings.len(), depth);

            let desc = membership_descriptor_of_depth_4ary(depth);
            let (trace, pis) =
                membership_witness_4ary(leaf, &siblings, &positions).expect("witness builds");
            assert_eq!(trace.len(), depth, "one trace row per 4-ary Merkle level");
            assert_eq!(trace[0].len(), MEMBERSHIP_4ARY_WIDTH);
            assert_eq!(pis.len(), MEMBERSHIP_4ARY_PI_COUNT);

            // ROUND-TRIP, not "two digests differ": the leaf and the recomputed root ARE the PIs.
            assert_eq!(&pis[PI_LEAF..PI_LEAF + DIGEST_W], &leaf[..]);
            assert_eq!(
                &pis[PI_ROOT..PI_ROOT + DIGEST_W],
                &membership_root_4ary(leaf, &siblings, &positions)[..],
                "published root must BE the independently folded node8 root"
            );
            assert_eq!(&pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);
            // and the trace's last-row parent group is that same root, lane for lane.
            let last = trace.last().unwrap();
            assert_eq!(&last[PAR..PAR + DIGEST_W], &root[..]);

            let proof =
                prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| {
                        panic!("honest depth-{depth} wide membership must prove: {e}")
                    });
            verify_vm_descriptor2(&desc, &proof, &pis)
                .unwrap_or_else(|e| panic!("honest depth-{depth} wide proof must verify: {e}"));
        }
    }

    /// STEP 3 — DEPTH-GENUINENESS: in a depth-8 tree, perturbing the sibling at EACH level
    /// (including interior levels a depth-2 pad would drop) changes the root, so claiming the
    /// honest root becomes UNSAT — the depth-8 proof genuinely consumes all 8 `node8` levels.
    #[test]
    fn depth8_every_level_is_load_bearing() {
        let depth = 8usize;
        let leaf = d8(0xBEEF);
        let (siblings, positions, root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);

        let (honest_trace, honest_pis) =
            membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
        assert_eq!(&honest_pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);
        assert!(
            !rejects(&desc, &honest_trace, &honest_pis),
            "honest depth-8 wide witness must be accepted — else the canary is vacuous"
        );

        for lvl in 0..depth {
            let mut bad_siblings = siblings.clone();
            bad_siblings[lvl][0][0] += BabyBear::ONE;
            let bad_root = membership_root_4ary(leaf, &bad_siblings, &positions);
            assert_ne!(
                bad_root, root,
                "perturbing level {lvl}'s sibling must change the root — that level is dead"
            );
            let (bad_trace, _bad_pis) =
                membership_witness_4ary(leaf, &bad_siblings, &positions).expect("witness");
            assert!(
                rejects(&desc, &bad_trace, &honest_pis),
                "a forged co-path at level {lvl} (claiming the real root) must be REJECTED"
            );
        }
    }

    /// STEP 3b — **THE LANE TOOTH**: perturbing a HIGH lane (lane 7) of a sibling — a change the
    /// one-felt family could not see at all, because it absorbed only lane 0 — moves the root and
    /// is REJECTED. This is the deleted wound, stated as a live gate.
    #[test]
    fn a_high_lane_sibling_change_is_seen_and_refused() {
        let depth = 4usize;
        let leaf = d8(0xC0FFEE);
        let (siblings, positions, root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (_ht, honest_pis) =
            membership_witness_4ary(leaf, &siblings, &positions).expect("witness");

        for lane in 1..DIGEST_W {
            let mut bad = siblings.clone();
            bad[1][2][lane] += BabyBear::ONE; // level 1, sibling 2, a NON-zero lane
            assert_ne!(
                membership_root_4ary(leaf, &bad, &positions),
                root,
                "a lane-{lane} sibling change must move the root (the one-felt fold was blind to it)"
            );
            let (bad_trace, _) = membership_witness_4ary(leaf, &bad, &positions).expect("witness");
            assert!(
                rejects(&desc, &bad_trace, &honest_pis),
                "a lane-{lane}-only forged co-path claiming the real root must be REJECTED"
            );
        }
    }

    /// STEP 3c — **THE LEAF LANE TOOTH**: the leaf is pinned across ALL EIGHT PIs, so a forged leaf
    /// that agrees on lane 0 (the entire binding the one-felt family had) is REFUSED.
    #[test]
    fn a_lane0_equal_but_distinct_leaf_is_refused() {
        let depth = 4usize;
        let leaf = d8(0xDEC0DE);
        let (siblings, positions, _root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (trace, pis) = membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
        assert!(!rejects(&desc, &trace, &pis), "honest witness accepted");

        let mut forged_leaf = leaf;
        forged_leaf[3] += BabyBear::ONE;
        assert_eq!(forged_leaf[0], leaf[0], "shares the lane-0 projection");
        assert_ne!(forged_leaf, leaf, "distinct as an 8-felt digest");

        let mut forged_pis = pis.clone();
        forged_pis[PI_LEAF..PI_LEAF + DIGEST_W].copy_from_slice(&forged_leaf);
        assert!(
            rejects(&desc, &trace, &forged_pis),
            "a lane-0-equal but full-width-distinct leaf MUST be rejected by the 8 leaf pins"
        );
    }

    /// STEP 4 — a forged CLAIMED root (leaf does not fold to it) is refused by the 8 root pins, in
    /// EVERY lane (not just lane 0 — which is all the one-felt family pinned).
    #[test]
    fn forged_root_refuses_in_every_lane() {
        let depth = 4usize;
        let leaf = d8(0xF00D);
        let (siblings, positions, _root) = create_test_witness(leaf, depth);
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (trace, pis) = membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest witness accepted (non-vacuity)"
        );
        for lane in 0..DIGEST_W {
            let mut forged = pis.clone();
            forged[PI_ROOT + lane] += BabyBear::ONE;
            assert!(
                rejects(&desc, &trace, &forged),
                "a claimed root differing in lane {lane} must be REJECTED"
            );
        }
    }

    /// STEP 5 — a non-power-of-two depth, a length mismatch, and an out-of-range position are all
    /// refused at witness time (the trace-height / arrangement requirements).
    #[test]
    fn malformed_witness_refuses() {
        let leaf = d8(7);
        let zero3 = [[BabyBear::ZERO; DIGEST_W]; 3];
        // depth 3 (not a power of two).
        assert!(membership_witness_4ary(leaf, &vec![zero3; 3], &[0, 0, 0]).is_err());
        // length mismatch.
        assert!(membership_witness_4ary(leaf, &vec![zero3; 2], &[0]).is_err());
        // out-of-range position (4 ∉ {0,1,2,3}).
        assert!(membership_witness_4ary(leaf, &vec![zero3; 2], &[0, 4]).is_err());
    }

    /// Shape pins — the WIDE shape, pinned against the Lean `#guard`s (90 columns, 16 PIs, 95
    /// constraints, THREE arity-16 wide-bus chip lookups and NO narrow-bus lookup).
    #[test]
    fn descriptor_shape() {
        let d = membership_descriptor_of_depth_4ary(8);
        assert_eq!(d.trace_width, MEMBERSHIP_4ARY_WIDTH);
        assert_eq!(d.trace_width, 90);
        assert_eq!(d.public_input_count, MEMBERSHIP_4ARY_PI_COUNT);
        assert_eq!(d.public_input_count, 16);
        assert_eq!(d.constraints.len(), 95);
        assert!(d.tables.is_empty());
        assert_eq!(d.name, "dregg-merkle-membership-4ary-wide-general::v1");

        // THREE arity-16 node8 chip lookups per row: the two stage-1 folds and the parent.
        let chips: Vec<&LookupSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chips.len(), 3, "two stage-1 folds + the parent fold");
        for l in &chips {
            assert_eq!(
                l.tuple[0],
                LeanExpr::Const(CHIP_NODE8_ARITY as i64),
                "every fold stage is an arity-16 node8 absorb"
            );
            assert_eq!(
                l.tuple.len(),
                1 + CHIP_RATE + CHIP_OUT_LANES,
                "the WIDE tuple shape (arity ‖ 16 ins ‖ 8 out lanes)"
            );
        }
        // BUS IDENTITY — the widening is a CUTOVER: NO narrow (single-output) chip lookup survives.
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2_NARROW))
                .count(),
            0,
            "no NARROW-bus chip lookup may survive the node8 widening — a single-output \
             lookup is exactly the one-felt waist this cutover deleted"
        );
        // EIGHT continuity windows (the deployed family had ONE).
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
                .count(),
            DIGEST_W,
            "the chain must ride every lane"
        );
    }

    /// ⚑ THE ROUTING GATE — the tooth for the wound documented on
    /// [`membership_4ary_dispatch_name`]: a proof wire's identity must RESOLVE, and the emitted
    /// descriptor's own `name` is NOT that identity. Plus the FLAG-DAY half: the retired one-felt
    /// identity must NOT resolve, so a stored pre-cutover proof is refused, never reinterpreted.
    #[test]
    fn the_wire_dispatch_name_resolves_and_is_not_the_emitted_descriptor_name() {
        use crate::descriptor_by_name::descriptor_by_name;
        for depth in [2usize, 4, 8, 16] {
            let dispatch = membership_4ary_dispatch_name(depth);
            let routed = descriptor_by_name(&dispatch).unwrap_or_else(|| {
                panic!("the wire identity {dispatch:?} MUST resolve — a producer emitting it would be refused by every consumer")
            });
            let direct = membership_descriptor_of_depth_4ary(depth);
            assert_eq!(
                routed, direct,
                "the routed descriptor must BE the one a producer proves under"
            );
            assert_ne!(
                direct.name, dispatch,
                "the emitted descriptor's own name is NOT the wire identity — if these \
                 ever coincide again, delete this assert and the two-name distinction \
                 together, deliberately"
            );
            assert!(
                descriptor_by_name(&direct.name).is_none(),
                "the emitted name {:?} does NOT route: a producer that puts it on the wire \
                 emits an UnknownAir. This is the failure mode the dispatch helper exists \
                 to prevent.",
                direct.name
            );
            // ⚑ FLAG DAY: the retired one-felt wire identity must be UNROUTABLE.
            let retired = format!("merkle-membership::poseidon2-4ary-general-depth{depth}");
            assert!(
                descriptor_by_name(&retired).is_none(),
                "the retired one-felt identity {retired:?} still routes — a pre-cutover proof \
                 would be REINTERPRETED under the wide descriptor instead of refused"
            );
        }
    }
}
