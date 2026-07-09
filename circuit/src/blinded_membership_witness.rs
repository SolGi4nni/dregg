//! Rust witness builder for the emitted **blinded ring-membership** descriptor
//! (`dregg-blinded-membership::v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/BlindedMembershipEmit.lean` as `blindedMembershipDesc`).
//!
//! ## What this closes (Golden Lift, stage 3d-2)
//!
//! The deployed anonymous-credential show proves `issuer ∈ federation` with a HAND-written blinded
//! STARK (`air_name = BLINDED_MERKLE`, `poseidon2_air.rs:647 generate_blinded_merkle_poseidon2_trace`).
//! Its published `pi[0] = blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)` (`poseidon2_air.rs:720`)
//! hides both the real member `leaf_hash` and the fresh `blinding_factor`; a 4-ary Poseidon2 Merkle
//! path proves `leaf_hash ∈ tree(root)` (`pi[1]`). That STARK was an OFF-descriptor named leaf: a
//! light client / the recursion fold saw only the two published felts, with nothing in the
//! light-client-visible descriptor forcing `blinded_leaf` to actually BE `hash_2_to_1` of a
//! `leaf_hash` that sits under `root`. Stage 3d-1 (`blindedMembershipDesc`) internalized both teeth;
//! until now there was NO production witness builder that could produce a descriptor-matching trace.
//! This module is that builder — the blinded-membership twin of
//! [`crate::bound_presentation_witness`] — so consumers of
//! [`crate::descriptor_by_name::descriptor_by_name`] can prove+verify a blinded membership through
//! the real p3 prover, and the fold adapter can wrap it as a recursion leaf.
//!
//! ## The trace layout (a single logical row, repeated to a power-of-two height)
//!
//! | col     | name                | meaning                                                       |
//! |---------|---------------------|--------------------------------------------------------------|
//! | 0       | `LEAF`              | the hidden member `leaf_hash` (Merkle input 0 AND blind in0) |
//! | 1..3    | `SIB0A/B/C`         | level-0 siblings (HIDDEN)                                     |
//! | 4       | `PARENT0`           | `hash_4_to_1(leaf, sib0…)` = level-0 chip out0 (HIDDEN)       |
//! | 5       | `CUR1`              | level-1 path input; the continuity gate pins `CUR1=PARENT0`  |
//! | 6..8    | `SIB1A/B/C`         | level-1 siblings (HIDDEN)                                     |
//! | 9       | `PARENT1`           | `hash_4_to_1(cur1, sib1…)` = the ROOT (chip out0); PI-pinned  |
//! | 10      | `BLINDING`          | the fresh `blinding_factor` (HIDDEN — this gives unlinkability)|
//! | 11      | `BLINDED_LEAF`      | `hash_2_to_1(leaf, blinding)` = blind chip out0; PI-pinned    |
//! | 12..18  | `LEVEL0_LANES`      | the 7 witnessed level-0 permutation lanes 1..7               |
//! | 19..25  | `LEVEL1_LANES`      | the 7 witnessed level-1 permutation lanes 1..7               |
//! | 26..32  | `BLIND_LANES`       | the 7 witnessed blind (arity-2) permutation lanes 1..7       |
//!
//! Every chip lane is GENUINE Poseidon2 permutation output ([`chip_absorb_all_lanes`]): out0 (the
//! digest columns `PARENT0`/`PARENT1`/`BLINDED_LEAF`) plus its seven exposed lanes, so each of the
//! three `TID_P2` chip lookups is SERVED — a forged digest, lane, blinding factor, or member has no
//! serving chip row → UNSAT. The two PIs are `[blinded_leaf, root]`; the member `leaf_hash` and the
//! `blinding_factor` are DELIBERATELY hidden (unlinkability): the same member blinded with two
//! factors publishes two DIFFERENT `blinded_leaf`, each a genuine Poseidon2 image of the SAME member
//! proven under the SAME public `root`.
//!
//! ## The leftmost-child convention (a real property of the emitted descriptor)
//!
//! `blindedMembershipDesc` hashes `[LEAF, SIB0A, SIB0B, SIB0C]` at level 0 and `[CUR1, SIB1A, SIB1B,
//! SIB1C]` at level 1 — the member/child is ALWAYS the leftmost (slot-0) input, exactly the
//! convention `MerkleMembershipEmit.merkleMembershipDesc` uses. The deployed
//! `generate_blinded_merkle_poseidon2_trace` places the child at an arbitrary slot `positions[i]`;
//! this builder therefore accepts `positions` (to mirror that signature) but requires each entry to
//! be `0`. Position-general trees need a position-generalized emitted descriptor (a descriptor-lane
//! follow-up), not a change here.

use crate::descriptor_ir2::{CHIP_OUT_LANES, chip_absorb_all_lanes};
use crate::field::BabyBear;

// ---- Column layout (mirror `BlindedMembershipEmit.lean` §1). ----
/// Level-0 path element = the member `leaf_hash` (HIDDEN; also the blinding tooth's input 0).
pub const LEAF: usize = 0;
/// Level-0 siblings (the three other children of the leaf's parent; HIDDEN).
pub const SIB0A: usize = 1;
pub const SIB0B: usize = 2;
pub const SIB0C: usize = 3;
/// Level-0 parent digest = `hash_4_to_1(leaf, sib0a, sib0b, sib0c)` (chip out0; HIDDEN).
pub const PARENT0: usize = 4;
/// Level-1 path element (the chained input; the continuity gate forces `CUR1 = PARENT0`; HIDDEN).
pub const CUR1: usize = 5;
/// Level-1 siblings (HIDDEN).
pub const SIB1A: usize = 6;
pub const SIB1B: usize = 7;
pub const SIB1C: usize = 8;
/// Level-1 parent digest = the ROOT = `hash_4_to_1(cur1, sib1…)`; pinned to `ROOT_PI`.
pub const PARENT1: usize = 9;
/// The blinding factor — fresh per presentation; HIDDEN (this hiddenness gives unlinkability).
pub const BLINDING: usize = 10;
/// The published blinded leaf = `hash_2_to_1(leaf_hash, blinding)`; pinned to `BLINDED_LEAF_PI`.
pub const BLINDED_LEAF: usize = 11;

/// First of the 7 witnessed level-0 Poseidon2 chip output lanes 1..7.
pub const LEVEL0_LANE_BASE: usize = 12;
/// First of the 7 witnessed level-1 Poseidon2 chip output lanes 1..7.
pub const LEVEL1_LANE_BASE: usize = 19;
/// First of the 7 witnessed blinding (arity-2) Poseidon2 chip output lanes 1..7.
pub const BLIND_LANE_BASE: usize = 26;

/// Total main-trace width: 12 base columns + 7·3 chip lane blocks.
pub const BLINDED_WIDTH: usize = 33;

/// PI slot 0: the published `blinded_leaf` (the unlinkable commitment).
pub const BLINDED_LEAF_PI: usize = 0;
/// PI slot 1: the public federation Merkle `root`.
pub const ROOT_PI: usize = 1;
/// Number of public inputs: `[blinded_leaf, root]`.
pub const BLINDED_MEMBERSHIP_PI_COUNT: usize = 2;

/// The Merkle depth the emitted `blindedMembershipDesc` fixes (two `child → parent` levels).
pub const BLINDED_MEMBERSHIP_DEPTH: usize = 2;

/// The canonical power-of-two base-trace height (the height the merkle-membership goldens use).
pub const BLINDED_MEMBERSHIP_HEIGHT: usize = 4;

/// The emitted descriptor's dispatch key (`descriptor_by_name`).
pub const BLINDED_MEMBERSHIP_NAME: &str = "dregg-blinded-membership::v1";

/// The byte-pinned emitted golden (the identical string `descriptor_by_name` serves and the Lean
/// `emitVmJson2 blindedMembershipDesc` `#guard` pins).
pub const BLINDED_MEMBERSHIP_JSON: &str =
    include_str!("../descriptors/by-name/blinded-membership.json");

/// The unlinkable published `blinded_leaf` the descriptor binds `BLINDED_LEAF` to: the arity-2 chip
/// absorb out0 of `[leaf_hash, blinding_factor]` (= `hash_2_to_1(leaf_hash, blinding_factor)`). The
/// in-circuit hash a light client / the fold re-verifies.
pub fn blinded_leaf(leaf_hash: BabyBear, blinding_factor: BabyBear) -> BabyBear {
    chip_absorb_all_lanes(2, &[leaf_hash, blinding_factor])[0]
}

/// Build the **blinded ring-membership** base trace + public inputs `[blinded_leaf, root]` for the
/// emitted `dregg-blinded-membership::v1` descriptor.
///
/// `siblings` is the per-level sibling triple (depth [`BLINDED_MEMBERSHIP_DEPTH`] = 2); `positions`
/// mirrors [`crate::poseidon2_air::generate_blinded_merkle_poseidon2_trace`]'s signature but — since
/// the emitted descriptor pins the member to the leftmost child slot — each entry must be `0`.
///
/// The two Merkle parents (`PARENT0`, `PARENT1` = root) are the genuine `hash_4_to_1` chip out0 of
/// their child+siblings, and `BLINDED_LEAF` is the genuine arity-2 `hash_2_to_1` chip out0 of
/// `[leaf_hash, blinding]`; each digest's 7 permutation lanes are witnessed alongside it, so all
/// three `TID_P2` chip lookups are SERVED. The trace is [`BLINDED_MEMBERSHIP_HEIGHT`] identical rows
/// (row-uniform: per-row lookups/pins + the `CUR1 = PARENT0` continuity gate hold identically).
///
/// The two public inputs are `[blinded_leaf, root]` — the member `leaf_hash` and the `blinding`
/// preimage are DELIBERATELY absent (unlinkability).
pub fn blinded_membership_witness(
    leaf_hash: BabyBear,
    blinding_factor: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if siblings.len() != BLINDED_MEMBERSHIP_DEPTH {
        return Err(format!(
            "blinded-membership expects {BLINDED_MEMBERSHIP_DEPTH} sibling levels (the emitted \
             depth-2 descriptor), got {}",
            siblings.len()
        ));
    }
    if positions.len() != BLINDED_MEMBERSHIP_DEPTH {
        return Err(format!(
            "blinded-membership expects {BLINDED_MEMBERSHIP_DEPTH} positions, got {}",
            positions.len()
        ));
    }
    if let Some((lvl, &p)) = positions.iter().enumerate().find(|&(_, &p)| p != 0) {
        return Err(format!(
            "blinded-membership position[{lvl}] = {p}: the emitted `blindedMembershipDesc` pins the \
             member to the leftmost child slot (slot 0), like `merkleMembershipDesc` — a \
             non-leftmost position needs a position-generalized emitted descriptor (a descriptor-lane \
             follow-up), not this builder"
        ));
    }

    // Level-0 child → parent (genuine arity-4 chip absorb): out0 = parent0, lanes 1..7 witnessed.
    let level0 = chip_absorb_all_lanes(
        4,
        &[leaf_hash, siblings[0][0], siblings[0][1], siblings[0][2]],
    );
    let parent0 = level0[0];
    // Level-1 child → parent: CUR1 = PARENT0 (the continuity chain), out0 = the root.
    let level1 = chip_absorb_all_lanes(
        4,
        &[parent0, siblings[1][0], siblings[1][1], siblings[1][2]],
    );
    let root = level1[0];
    // The blinding tooth (genuine arity-2 chip absorb): out0 = blinded_leaf, lanes 1..7 witnessed.
    let blind = chip_absorb_all_lanes(2, &[leaf_hash, blinding_factor]);
    let published_blinded_leaf = blind[0];

    let mut row = vec![BabyBear::ZERO; BLINDED_WIDTH];
    row[LEAF] = leaf_hash;
    row[SIB0A] = siblings[0][0];
    row[SIB0B] = siblings[0][1];
    row[SIB0C] = siblings[0][2];
    row[PARENT0] = parent0;
    row[CUR1] = parent0; // the continuity gate: CUR1 == PARENT0
    row[SIB1A] = siblings[1][0];
    row[SIB1B] = siblings[1][1];
    row[SIB1C] = siblings[1][2];
    row[PARENT1] = root;
    row[BLINDING] = blinding_factor;
    row[BLINDED_LEAF] = published_blinded_leaf;
    for j in 0..(CHIP_OUT_LANES - 1) {
        row[LEVEL0_LANE_BASE + j] = level0[j + 1];
        row[LEVEL1_LANE_BASE + j] = level1[j + 1];
        row[BLIND_LANE_BASE + j] = blind[j + 1];
    }

    let trace: Vec<Vec<BabyBear>> = (0..BLINDED_MEMBERSHIP_HEIGHT)
        .map(|_| row.clone())
        .collect();

    let mut pis = vec![BabyBear::ZERO; BLINDED_MEMBERSHIP_PI_COUNT];
    pis[BLINDED_LEAF_PI] = published_blinded_leaf;
    pis[ROOT_PI] = root;

    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, LookupSpec, MemBoundaryWitness, TID_P2, VmConstraint2,
        parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::lean_descriptor_air::LeanExpr;
    use std::panic::AssertUnwindSafe;

    const GOLDEN_JSON: &str = include_str!("../descriptors/by-name/blinded-membership.json");

    fn sample_siblings() -> ([[BabyBear; 3]; 2], [u8; 2]) {
        (
            [
                [
                    BabyBear::new(2002),
                    BabyBear::new(3003),
                    BabyBear::new(4004),
                ],
                [
                    BabyBear::new(5005),
                    BabyBear::new(6006),
                    BabyBear::new(7007),
                ],
            ],
            [0, 0],
        )
    }

    fn honest() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let (sibs, pos) = sample_siblings();
        blinded_membership_witness(BabyBear::new(1001), BabyBear::new(0xB11D), &sibs, &pos)
            .expect("witness builds")
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails verify).
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        matches!(r, Err(_) | Ok(Err(_)))
    }

    /// STEP 0 — the dispatched descriptor is exactly the byte-pinned golden (the migration wiring).
    #[test]
    fn dispatch_serves_the_byte_pinned_golden() {
        let via = descriptor_by_name(BLINDED_MEMBERSHIP_NAME)
            .expect("blinded-membership descriptor dispatches");
        assert_eq!(via.name, BLINDED_MEMBERSHIP_NAME);
        assert_eq!(via.trace_width, BLINDED_WIDTH);
        assert_eq!(via.public_input_count, BLINDED_MEMBERSHIP_PI_COUNT);
        let golden = parse_vm_descriptor2(GOLDEN_JSON).expect("golden decodes");
        assert_eq!(
            via, golden,
            "descriptor_by_name must serve the byte-pinned emitted golden verbatim"
        );
        // three chip lookups: two arity-4 Merkle levels + one arity-2 blinding tooth.
        let chip: Vec<&LookupSpec> = via
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chip.len(), 3, "two Merkle levels + the blinding tooth");
        assert_eq!(chip[0].tuple[0], LeanExpr::Const(4), "level-0 arity-4");
        assert_eq!(chip[1].tuple[0], LeanExpr::Const(4), "level-1 arity-4");
        assert_eq!(chip[2].tuple[0], LeanExpr::Const(2), "blinding arity-2");
    }

    /// STEP 1 — THE POSITIVE POLE: an honest blinded membership proves through the DISPATCHED
    /// descriptor and re-verifies; the two PIs are the genuine `[blinded_leaf, root]` images.
    #[test]
    fn honest_blinded_membership_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(BLINDED_MEMBERSHIP_NAME).expect("dispatch");
        let (sibs, pos) = sample_siblings();
        let leaf = BabyBear::new(1001);
        let blinding = BabyBear::new(0xB11D);
        let (trace, pis) =
            blinded_membership_witness(leaf, blinding, &sibs, &pos).expect("witness");

        assert_eq!(pis.len(), BLINDED_MEMBERSHIP_PI_COUNT);
        assert_eq!(
            pis[BLINDED_LEAF_PI],
            blinded_leaf(leaf, blinding),
            "PI[0] is the genuine hash_2_to_1(leaf, blinding) image"
        );
        assert_eq!(
            pis[ROOT_PI], trace[0][PARENT1],
            "PI[1] is the genuine Merkle root (last parent)"
        );
        // the member leaf_hash and blinding factor are HIDDEN — not PIs.
        assert!(
            !pis.contains(&leaf),
            "leaf_hash is a hidden witness, not a PI"
        );
        assert!(
            !pis.contains(&blinding),
            "blinding_factor is a hidden witness, not a PI"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest blinded-membership witness must prove through the descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
    }

    /// STEP 2 — NON-MEMBER: a forged claimed `root` PI (not the genuine last parent) makes the
    /// root pin UNSAT. Non-vacuous: the honest witness is accepted first.
    #[test]
    fn non_member_root_refuses() {
        let desc = descriptor_by_name(BLINDED_MEMBERSHIP_NAME).expect("dispatch");
        let (trace, pis) = honest();
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );

        let mut bad_pis = pis.clone();
        bad_pis[ROOT_PI] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &bad_pis),
            "a non-member (forged root PI) must be REJECTED (root pin)"
        );
    }

    /// STEP 3 — WRONG BLINDED_LEAF: an attacker publishes a `blinded_leaf` PI that is NOT the
    /// arity-2 Poseidon2 image of `[leaf, blinding]`. Overwrite the column AND its PI copy → the
    /// blinding chip lookup has no serving row → UNSAT. Non-vacuous.
    #[test]
    fn wrong_blinded_leaf_refuses() {
        let desc = descriptor_by_name(BLINDED_MEMBERSHIP_NAME).expect("dispatch");
        let (trace, pis) = honest();
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );

        let mut bad_trace = trace.clone();
        let mut bad_pis = pis.clone();
        let bogus = trace[0][BLINDED_LEAF] + BabyBear::ONE;
        for r in bad_trace.iter_mut() {
            r[BLINDED_LEAF] = bogus;
        }
        bad_pis[BLINDED_LEAF_PI] = bogus; // keep the PI pin satisfiable
        assert!(
            rejects(&desc, &bad_trace, &bad_pis),
            "a blinded_leaf that is not hash_2_to_1(leaf, blinding) must be REJECTED (chip lookup)"
        );
    }

    /// STEP 4 — UNLINKABILITY: the SAME member `leaf_hash` blinded with two DIFFERENT factors
    /// yields two DIFFERENT `blinded_leaf` PIs, both of which verify under the SAME `root`.
    #[test]
    fn unlinkability_two_factors_two_blinded_leaves_both_verify() {
        let desc = descriptor_by_name(BLINDED_MEMBERSHIP_NAME).expect("dispatch");
        let (sibs, pos) = sample_siblings();
        let leaf = BabyBear::new(1001);
        let b1 = BabyBear::new(0xB11D);
        let b2 = BabyBear::new(0xDEAD);

        let (t1, p1) = blinded_membership_witness(leaf, b1, &sibs, &pos).expect("show 1");
        let (t2, p2) = blinded_membership_witness(leaf, b2, &sibs, &pos).expect("show 2");

        // Two shows of ONE credential publish two DIFFERENT blinded leaves...
        assert_ne!(
            p1[BLINDED_LEAF_PI], p2[BLINDED_LEAF_PI],
            "distinct blinding factors must give distinct blinded_leaf (unlinkability)"
        );
        // ...yet the SAME public root (same member, same tree).
        assert_eq!(
            p1[ROOT_PI], p2[ROOT_PI],
            "both shows commit to the same member under the same root"
        );

        // Both verify.
        let pf1 = prove_vm_descriptor2(&desc, &t1, &p1, &MemBoundaryWitness::default(), &[])
            .expect("show 1 proves");
        verify_vm_descriptor2(&desc, &pf1, &p1).expect("show 1 verifies");
        let pf2 = prove_vm_descriptor2(&desc, &t2, &p2, &MemBoundaryWitness::default(), &[])
            .expect("show 2 proves");
        verify_vm_descriptor2(&desc, &pf2, &p2).expect("show 2 verifies");
    }

    /// STEP 5 — malformed inputs (wrong depth / non-leftmost position) are refused at build time.
    #[test]
    fn malformed_witness_refuses() {
        let leaf = BabyBear::new(1001);
        let blinding = BabyBear::new(0xB11D);
        let (sibs, _) = sample_siblings();
        // wrong depth
        assert!(
            blinded_membership_witness(leaf, blinding, &sibs[..1], &[0]).is_err(),
            "a wrong sibling depth must be refused"
        );
        // non-leftmost position (the descriptor pins slot 0)
        assert!(
            blinded_membership_witness(leaf, blinding, &sibs, &[1, 0]).is_err(),
            "a non-leftmost position must be refused (the descriptor pins slot 0)"
        );
    }
}
