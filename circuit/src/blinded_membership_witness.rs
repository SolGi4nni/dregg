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
//!
//! E7 narrowed all three lookups onto the NARROW chip bus (`chipLookupTupleNarrow`,
//! `BlindedMembershipEmit.lean`), deleting the three trailing 7-lane blocks `[12, 33)`. Each
//! digest column (`PARENT0`/`PARENT1`/`BLINDED_LEAF`) is still GENUINE Poseidon2 out0
//! ([`chip_absorb_all_lanes`]), and each `TID_P2_NARROW` lookup is SERVED by the 18-prefix of the
//! SAME chip rows (`ChipNarrowLookup.lean`) — a forged digest, blinding factor, or member has no
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

use crate::descriptor_ir2::{EffectVmDescriptor2, chip_absorb_all_lanes, parse_vm_descriptor2};
use crate::field::BabyBear;
use crate::membership_descriptor_4ary::{
    CUR, DIGEST_W, Digest8, MEMBERSHIP_4ARY_WIDTH, PI_ROOT, membership_witness_4ary,
};

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

/// Total main-trace width: the 12 base columns. E7's narrow-bus cutover deleted the three
/// trailing 7-lane chip blocks `[12, 33)` — a pure tail truncation, so no base index moved.
pub const BLINDED_WIDTH: usize = BLINDED_LEAF + 1; // 12

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
/// mirrors the signature of the now-DELETED `generate_blinded_merkle_poseidon2_trace` but — since
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

    let trace: Vec<Vec<BabyBear>> = (0..BLINDED_MEMBERSHIP_HEIGHT)
        .map(|_| row.clone())
        .collect();

    let mut pis = vec![BabyBear::ZERO; BLINDED_MEMBERSHIP_PI_COUNT];
    pis[BLINDED_LEAF_PI] = published_blinded_leaf;
    pis[ROOT_PI] = root;

    Ok((trace, pis))
}

// ============================================================================================
// Depth-GENERAL, 4-ARY, GENERAL-POSITION, **8-FELT (`node8`)** blinded ring-membership.
//
// ## What this closes (felt-width finding #2 — federation)
//
// Until the WIDE cutover this family's node was **one BabyBear felt**: each level absorbed the four
// children as four SINGLE felts (arity 4, out0 only), the continuity window chained ONE column, and
// the blinding tooth absorbed the member digest as ONE felt (arity 2). So every interior node, the
// committed root, AND the published blinded leaf were ~31-bit commitments — collidable at 2^15.5.
// An attacker who contributes to a subtree birthday-collides an interior node and presents a
// second, distinct authentication path reaching the SAME authorized federation root; and two member
// digests agreeing on lane 0 publish the SAME blinded leaf under the same blinding factor, for free.
//
// **Every node of this tree is now a full 8-felt Poseidon2 digest, and the published blinded leaf is
// 8 felts of a 9-felt preimage.** The one-felt path is DELETED, not deprecated.
//
// ## The widened scheme (authored in Lean — LAW #1)
//
// The algebra is `Dregg2.Circuit.Emit.BlindedMembershipWideEmit` (`blindedMembershipWideDesc`);
// Rust parses the emitted IR2 bytes and supplies witnesses, and constructs no constraints. The path
// block (columns 0..90) is laid out IDENTICALLY to `MerkleMembership4aryWideEmit` — the same
// balanced two-stage arity-16 `node8` fold
//
//     node8_4ary(c0,c1,c2,c3) = A16( A16(c0 ‖ c1) ‖ A16(c2 ‖ c3) )
//
// — so [`membership_witness_4ary`] builds it verbatim and this builder only appends the blinding
// tooth. The Lean keystones are `wideNodeFold_sound` (a row's three fold lookups force the genuine
// `wideFold4`), `wideBlind_sound` (the blind lookup forces the 8 published columns to
// `A11(cur8 ‖ blinding ‖ 0 ‖ 0)` — the commitment binds the WHOLE member digest, not its lane 0),
// `wCont_all_zero_iff` (the chain rides all 8 lanes), and the two anti-masquerade teeth
// `interior_forge_narrow_admits_wide_refuses` / `blinded_leaf_forge_narrow_admits_wide_refuses`.
//
// **THE BLINDING IS PRESERVED.** The fresh blinding factor still rides the leaf, and leaf +
// blinding stay HIDDEN — that hiddenness IS the unlinkability. What widened is the PREIMAGE and the
// published image, not the PI *surface* of a secret.
//
// ## Column layout (width 99) — cols 0..90 are byte-for-byte
// [`crate::membership_descriptor_4ary`]'s wide path row; the blinding tooth appends two blocks.
//
// | cols    | name                     | meaning                                                    |
// |---------|--------------------------|------------------------------------------------------------|
// | 0..8    | `CUR`                    | running 8-felt node (row 0 = the HIDDEN member leaf digest) |
// | 8..32   | `SIB0..SIB2`             | the three co-path 8-felt siblings at this level (HIDDEN)    |
// | 32,33   | `B0,B1`                  | position bits (`position = b0 + 2·b1 ∈ {0,1,2,3}`)          |
// | 34..66  | `C0..C3`                 | the ordered 8-felt children (`children[position] = cur8`)   |
// | 66..74  | `H01`                    | stage-1 left  `A16(c0 ‖ c1)` — all 8 lanes bound            |
// | 74..82  | `H23`                    | stage-1 right `A16(c2 ‖ c3)` — all 8 lanes bound            |
// | 82..90  | `PAR`                    | `A16(h01 ‖ h23)`; last row pinned to PIs 8..16 = the root   |
// | 90      | `BLINDING_4ARY`          | the fresh blinding factor (HIDDEN — the unlinkability)      |
// | 91..99  | `BLINDED_LEAF_COL_4ARY`  | `A11(cur8 ‖ blinding ‖ 0 ‖ 0)`; row 0 pinned to PIs 0..8             |
//
// UNLIKE the plain wide membership, the row-0 running node is NOT PI-pinned: it stays hidden, and
// only its 8-felt blinded image is published.

/// The blinding tooth's chip arity: all 8 lanes of the member digest, the blinding felt, and TWO
/// ZERO PADS, in ONE absorb (Lean `wBlindIns`, `#guard wBlindIns.length == 11`). The eleven inputs
/// carry the whole preimage — the retired family's arity-2 `[cur0, blinding]` is exactly the lane-0
/// waist this deletes.
///
/// ⚠ **ELEVEN, NOT NINE, AND THE DEPLOYED CHIP FORCES IT.** The Lean asked for arity 9 until
/// 2026-08-01 and the descriptor was UNPROVABLE: the chip AIR admits `arity ∈ {0,2,3,4,7,11,16}`
/// (`descriptor_ir2.rs` asserts `arity·(a−2)(a−3)(a−4)(a−7)(a−11)(a−16) = 0`, degree 7 = the whole
/// S-box budget, so no eighth factor can be added) and at `a = 9` that product is `52920 ≠ 0`.
/// Independently, [`chip_absorb_all_lanes`] seeds lanes 4/5/6 from the inputs only when
/// `arity ∈ {7, 11, 16}`; at 9 it writes the arity TAG into lane 4 and zeros 5 and 6, so three of
/// the eight member lanes never entered the preimage and the tooth bound five, not eight. Arity 11
/// is the deployed wide arity (`CHIP_WIDE_ARITY`), the pads are binding-preserving
/// (`packBlind_inj`), and every leaf lane now enters the permutation.
pub const BLIND_ARITY_4ARY: usize = crate::descriptor_ir2::CHIP_WIDE_ARITY; // 11

// DRIFT GUARD — the padded preimage must still carry the whole member digest plus the blinding.
const _: () = assert!(BLIND_ARITY_4ARY >= DIGEST_W + 1);

/// The fresh blinding factor column (HIDDEN). Lean `wBLINDING`.
pub const BLINDING_4ARY: usize = 90;
/// First column of the published 8-felt blinded leaf group `[91, 99)` (row 0 pinned to PIs 0..8).
/// Lean `wBLINDED`.
pub const BLINDED_LEAF_COL_4ARY: usize = 91;
/// Total main-trace width: the 90-column wide path row + the blinding felt + the 8-felt image.
pub const BLINDED_4ARY_WIDTH: usize = 99;

// DRIFT GUARD — two INDEPENDENT sources must agree, not a constant against its own definition.
// The literals above are read off the Lean `w*` column defs; `MEMBERSHIP_4ARY_WIDTH` is the plain
// wide membership family's own width. The Lean lays this family's path block out identically to
// `MerkleMembership4aryWideEmit`, so the blinding tooth MUST start exactly where that row ends. If
// either side moves, this fails at compile time instead of silently renumbering the trace.
const _: () = assert!(BLINDING_4ARY == MEMBERSHIP_4ARY_WIDTH);
const _: () = assert!(BLINDED_LEAF_COL_4ARY == BLINDING_4ARY + 1);
const _: () = assert!(BLINDED_4ARY_WIDTH == BLINDED_LEAF_COL_4ARY + DIGEST_W);

/// PI slots `0..8`: the published 8-felt `blinded_leaf` (the unlinkable commitment). Lean
/// `wPI_BLINDED`.
pub const PI_BLINDED_LEAF_4ARY: usize = 0;
/// PI slots `8..16`: the public 8-felt federation Merkle `root`. Lean `wPI_ROOT`.
pub const PI_ROOT_4ARY: usize = 8;
/// Public-input count: `[blinded0..blinded7, root0..root7]`.
pub const BLINDED_4ARY_PI_COUNT: usize = 16;

/// THE WIRE DISPATCH PREFIX for the depth-GENERAL 4-ary blinded ring-membership family
/// ([`blinded_membership_descriptor_of_depth_4ary`] writes `depth{N}` after it, and — unlike the
/// plain membership family — stamps that label into the served descriptor's own `name`, so a
/// producer that puts `desc.name` on the wire still routes).
///
/// ⚑ FLAG DAY: this string CHANGED at the `node8` cutover (it was
/// `dregg-blinded-membership-4ary-general-depth`). The old identity no longer resolves, so a
/// producer or a stored proof from the one-felt epoch is answered `UnknownAir` and REFUSED rather
/// than reinterpreted under a descriptor with different semantics and a different PI count.
pub const BLINDED_4ARY_NAME_PREFIX: &str = "dregg-blinded-membership-4ary-wide-general-depth";

/// The emitted descriptor's OWN name, as the Lean `blindedMembershipWideDesc` fixes it. The served
/// descriptor's `name` is overwritten with the depth label (above); this constant exists so the
/// byte-pin test can check the golden it started from.
pub const BLINDED_4ARY_WIDE_EMITTED_NAME: &str = "dregg-blinded-membership-4ary-wide-general::v1";

/// Exact bytes emitted and byte-pinned by
/// `Dregg2.Circuit.Emit.BlindedMembershipWideEmit.BLINDED_MEMBERSHIP_WIDE_GOLDEN`.
pub const BLINDED_MEMBERSHIP_4ARY_WIDE_JSON: &str =
    include_str!("../descriptors/by-name/blinded-membership-4ary-wide.json");

/// **The WIDE published blinded leaf** — the 8-felt image `A11(leaf8 ‖ blinding ‖ 0 ‖ 0)` the descriptor
/// binds the `BLINDED_LEAF_COL_4ARY` group to, and the in-circuit hash a light client / the fold
/// re-verifies. All 8 lanes of the member digest and the blinding felt enter ONE absorb, and all 8
/// output lanes are the commitment: there is no lane-0 projection on either side.
pub fn blinded_leaf_8(leaf: &Digest8, blinding_factor: BabyBear) -> Digest8 {
    let mut ins = [BabyBear::ZERO; BLIND_ARITY_4ARY];
    ins[..DIGEST_W].copy_from_slice(leaf);
    ins[DIGEST_W] = blinding_factor;
    chip_absorb_all_lanes(BLIND_ARITY_4ARY, &ins)
}

/// **`blinded_membership_descriptor_of_depth_4ary`** — the depth-GENERAL, 4-ary, general-position,
/// 8-felt blinded ring-membership descriptor. The constraint block is depth-uniform (the depth
/// lives in the trace HEIGHT), so Rust parses ONE Lean-emitted artifact for every supported depth
/// and never rewrites a constraint.
///
/// It DOES stamp the depth label into `name`. That is deliberate and load-bearing: this family's
/// producers (`bridge/present.rs`'s `build_descriptor_wire`) put the served descriptor's `name` on
/// the wire as the `predicate`, and `descriptor_by_name` routes only the
/// [`BLINDED_4ARY_NAME_PREFIX`]`{depth}` form — so name and wire identity must coincide here.
/// (Contrast [`crate::membership_descriptor_4ary::membership_4ary_dispatch_name`], where they are
/// deliberately distinct and the conflation cost a production `UnknownAir`.)
pub fn blinded_membership_descriptor_of_depth_4ary(depth: usize) -> EffectVmDescriptor2 {
    assert!(
        depth >= 2 && depth.is_power_of_two(),
        "blinded-membership depth must be a power of two ≥ 2"
    );
    let mut desc = parse_vm_descriptor2(BLINDED_MEMBERSHIP_4ARY_WIDE_JSON)
        .expect("Lean-emitted WIDE blinded-membership descriptor must parse");
    desc.name = format!("{BLINDED_4ARY_NAME_PREFIX}{depth}");
    desc
}

/// Build the depth-GENERAL, 4-ary, general-position **8-felt blinded** ring-membership base trace +
/// public inputs `[blinded0..blinded7, root0..root7]`.
///
/// The authentication path is built by [`membership_witness_4ary`] — the SAME 90-column wide row,
/// so the committed root is byte-equal to the plain wide membership family's `node8_4ary` fold —
/// and each row is then extended with the wide blinding tooth: the 8 columns at
/// [`BLINDED_LEAF_COL_4ARY`] carry `A9(cur8 ‖ blinding_factor)` for THAT row's running node. The
/// row-0 running node is the hidden member leaf digest, so `pis[0..8] = blinded_leaf_8(leaf_hash,
/// blinding_factor)`. The blinding factor is reused on interior rows only to serve the (unpinned)
/// per-row blinding lookup; only the row-0 image is public.
///
/// `siblings.len()` must equal `positions.len()`, each position `< 4`, and the depth a power of two
/// ≥ 2 (the trace-height requirement, enforced by [`membership_witness_4ary`]). The member digest
/// and the blinding factor are DELIBERATELY absent from the PIs (unlinkability).
pub fn blinded_membership_witness_4ary(
    leaf_hash: Digest8,
    blinding_factor: BabyBear,
    siblings: &[[Digest8; 3]],
    positions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (path_trace, path_pis) = membership_witness_4ary(leaf_hash, siblings, positions)?;
    // path_pis = [leaf0..leaf7, root0..root7]; the root is the wide `node8_4ary` fold.
    let root: Digest8 = core::array::from_fn(|k| path_pis[PI_ROOT + k]);

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(path_trace.len());
    let mut published_blinded_leaf = [BabyBear::ZERO; DIGEST_W];
    for (j, prow) in path_trace.iter().enumerate() {
        debug_assert_eq!(prow.len(), MEMBERSHIP_4ARY_WIDTH);
        let cur: Digest8 = core::array::from_fn(|k| prow[CUR + k]);
        // The genuine arity-11 chip absorb: all 8 output lanes ARE the blinded image, and all 8
        // lanes of `cur` plus the blinding felt are in the preimage. A forged image lane, a forged
        // member lane, or a forged blinding factor has no serving chip row → UNSAT.
        let blind = blinded_leaf_8(&cur, blinding_factor);
        let mut row = vec![BabyBear::ZERO; BLINDED_4ARY_WIDTH];
        row[..MEMBERSHIP_4ARY_WIDTH].copy_from_slice(prow);
        row[BLINDING_4ARY] = blinding_factor;
        row[BLINDED_LEAF_COL_4ARY..BLINDED_LEAF_COL_4ARY + DIGEST_W].copy_from_slice(&blind);
        if j == 0 {
            published_blinded_leaf = blind; // = blinded_leaf_8(leaf_hash, blinding_factor)
        }
        trace.push(row);
    }

    let mut pis = Vec::with_capacity(BLINDED_4ARY_PI_COUNT);
    pis.extend_from_slice(&published_blinded_leaf);
    pis.extend_from_slice(&root);
    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, LookupSpec, MemBoundaryWitness, TID_P2, TID_P2_NARROW, VmConstraint2,
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
        // Three chip lookups: two arity-4 Merkle levels + one arity-2 blinding tooth — counted on
        // the bus the descriptor NOW uses. E7 moved all three onto the NARROW bus
        // (`TID_P2_NARROW`, the 18-wide `[arity, ins, out0]` tuple), served by the SAME chip rows.
        let chip: Vec<&LookupSpec> = via
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2_NARROW => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chip.len(), 3, "two Merkle levels + the blinding tooth");
        assert_eq!(chip[0].tuple[0], LeanExpr::Const(4), "level-0 arity-4");
        assert_eq!(chip[1].tuple[0], LeanExpr::Const(4), "level-1 arity-4");
        assert_eq!(chip[2].tuple[0], LeanExpr::Const(2), "blinding arity-2");
        // BUS IDENTITY — the narrowing is a CUTOVER, not an addition. Without this leg the count
        // above would pass on a re-widened descriptor that merely added narrow lookups beside the
        // wide ones, and the 21 deleted lane columns would silently come back.
        assert_eq!(
            via.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count(),
            0,
            "no WIDE-bus chip lookup may survive the E7 narrowing"
        );
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

#[cfg(test)]
mod tests_4ary {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        CHIP_NODE8_ARITY, CHIP_OUT_LANES, CHIP_RATE, EffectVmDescriptor2, LookupSpec,
        MemBoundaryWitness, TID_P2, TID_P2_NARROW, VmConstraint2, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::dsl::membership::create_test_witness;
    use crate::lean_descriptor_air::LeanExpr;
    use crate::membership_descriptor_4ary::membership_root_4ary;
    use crate::refusal::{Outcome, classify};

    fn d8(base: u32) -> Digest8 {
        core::array::from_fn(|k| BabyBear::new(base + k as u32))
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails
    /// to verify). Prove-THEN-verify is the faithful consumer posture; `classify` REDS on any panic
    /// that is not the p3 debug prover's documented unsat verdict, so a crash cannot masquerade as
    /// a refusal.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// The production-shaped witness: a depth-`d`, general-position (`position = i % 4`) path
    /// (exactly `create_test_witness` / `bridge/present.rs`), blinded with `blinding`.
    fn general_position_witness(
        leaf: Digest8,
        blinding: BabyBear,
        depth: usize,
    ) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Digest8) {
        let (siblings, positions, prod_root) = create_test_witness(leaf, depth);
        let (trace, pis) = blinded_membership_witness_4ary(leaf, blinding, &siblings, &positions)
            .expect("4-ary wide blinded witness builds");
        (trace, pis, prod_root)
    }

    /// SHAPE PIN — the WIDE shape, pinned against the Lean `#guard`s in
    /// `BlindedMembershipWideEmit.lean` (99 columns, 16 PIs, 96 constraints, FOUR wide-bus chip
    /// lookups — three arity-16 fold stages plus the arity-11 blinding tooth — EIGHT continuity
    /// windows, and ZERO narrow-bus lookups).
    #[test]
    fn descriptor_shape_is_the_wide_lean_guarded_one() {
        let d = blinded_membership_descriptor_of_depth_4ary(8);
        assert_eq!(d.trace_width, BLINDED_4ARY_WIDTH);
        assert_eq!(d.trace_width, 99);
        assert_eq!(d.public_input_count, BLINDED_4ARY_PI_COUNT);
        assert_eq!(d.public_input_count, 16);
        assert_eq!(d.constraints.len(), 96);
        assert!(d.tables.is_empty());

        // FOUR wide chip lookups: the two stage-1 folds, the parent fold, and the blinding tooth.
        let chips: Vec<&LookupSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(
            chips.len(),
            4,
            "two stage-1 folds + the parent fold + the wide blinding tooth"
        );
        let arities: Vec<LeanExpr> = chips.iter().map(|l| l.tuple[0].clone()).collect();
        assert_eq!(
            arities,
            vec![
                LeanExpr::Const(CHIP_NODE8_ARITY as i64),
                LeanExpr::Const(CHIP_NODE8_ARITY as i64),
                LeanExpr::Const(CHIP_NODE8_ARITY as i64),
                LeanExpr::Const(BLIND_ARITY_4ARY as i64),
            ],
            "three arity-16 node8 fold stages, then the arity-11 blinding absorb \
             (the deployed family's arity-2 `[cur0, blinding]` tooth is DELETED)"
        );
        for l in &chips {
            assert_eq!(
                l.tuple.len(),
                1 + CHIP_RATE + CHIP_OUT_LANES,
                "the WIDE tuple shape (arity ‖ 16 ins ‖ 8 out lanes)"
            );
        }
        // BUS IDENTITY — the widening is a CUTOVER, not an addition. A single-output (narrow)
        // lookup is exactly the one-felt waist this deleted; none may survive.
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2_NARROW))
                .count(),
            0,
            "no NARROW-bus chip lookup may survive the node8 widening"
        );
        // EIGHT continuity windows (the deployed family had ONE).
        assert_eq!(
            d.constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
                .count(),
            DIGEST_W,
            "the level chain must ride every lane"
        );
    }

    /// BYTE-PIN — the served descriptor IS the byte-pinned Lean golden
    /// (`BLINDED_MEMBERSHIP_WIDE_GOLDEN`), modulo the ONE deliberate mutation: the depth label
    /// stamped into `name` so the wire identity and the descriptor name coincide for this family.
    #[test]
    fn builder_is_the_lean_golden_modulo_the_depth_label() {
        use crate::descriptor_ir2::parse_vm_descriptor2;
        let golden = parse_vm_descriptor2(BLINDED_MEMBERSHIP_4ARY_WIDE_JSON)
            .expect("the WIDE Lean golden decodes");
        assert_eq!(
            golden.name, BLINDED_4ARY_WIDE_EMITTED_NAME,
            "the golden's own name is the Lean `blindedMembershipWideDesc.name`"
        );
        for depth in [2usize, 4, 8, 16] {
            let mut expect = golden.clone();
            expect.name = format!("{BLINDED_4ARY_NAME_PREFIX}{depth}");
            assert_eq!(
                expect,
                blinded_membership_descriptor_of_depth_4ary(depth),
                "the builder must be the Lean golden verbatim except for the depth label"
            );
        }
    }

    /// ⚑ FLAG DAY — the retired ONE-FELT wire identity must be UNROUTABLE, so a stored pre-cutover
    /// proof is REFUSED (`UnknownAir`) rather than reinterpreted under a descriptor with a
    /// different PI count and different semantics. The new identity must route, and route to
    /// exactly what a producer proves under.
    #[test]
    fn dispatch_routes_the_new_identity_and_refuses_the_retired_one() {
        for depth in [2usize, 4, 8] {
            let name = format!("{BLINDED_4ARY_NAME_PREFIX}{depth}");
            let via = descriptor_by_name(&name).expect("the wide blinded identity must route");
            assert_eq!(via.name, name, "the served name IS the wire identity here");
            assert_eq!(via.trace_width, BLINDED_4ARY_WIDTH);
            assert_eq!(via.public_input_count, BLINDED_4ARY_PI_COUNT);
            assert_eq!(via, blinded_membership_descriptor_of_depth_4ary(depth));

            let retired = format!("dregg-blinded-membership-4ary-general-depth{depth}");
            assert!(
                descriptor_by_name(&retired).is_none(),
                "the retired one-felt identity {retired:?} still routes — a pre-cutover proof \
                 would be REINTERPRETED under the wide descriptor instead of refused"
            );
        }
    }

    /// ⚑ THE BLINDING TOOTH, AT WIDTH — the published commitment binds EVERY lane of the member
    /// digest and the blinding felt. Perturbing any one of the nine preimage felts moves the image
    /// in EVERY output lane; and the deployed narrow tooth's blind spot is stated as the contrast:
    /// two members agreeing at lane 0 published the SAME one-felt blinded leaf for free.
    #[test]
    fn the_wide_blinding_tooth_binds_all_nine_preimage_felts() {
        let leaf = d8(0xA11CE);
        let blinding = BabyBear::new(0xB11D);
        let img = blinded_leaf_8(&leaf, blinding);

        // Eight genuinely distinct output lanes — catches a replicated / `[x]*8` widening.
        for i in 0..DIGEST_W {
            for j in (i + 1)..DIGEST_W {
                assert_ne!(img[i], img[j], "image lanes {i},{j} collide — not 8 felts");
            }
        }
        // Every member lane is load-bearing, in every output lane.
        for k in 0..DIGEST_W {
            let mut alt = leaf;
            alt[k] += BabyBear::ONE;
            let alt_img = blinded_leaf_8(&alt, blinding);
            for i in 0..DIGEST_W {
                assert_ne!(
                    img[i], alt_img[i],
                    "image lane {i} unchanged after perturbing member lane {k} \
                     — that member felt is NOT in the preimage"
                );
            }
        }
        // The blinding felt is load-bearing too (this is the unlinkability input).
        let other = blinded_leaf_8(&leaf, blinding + BabyBear::ONE);
        for i in 0..DIGEST_W {
            assert_ne!(
                img[i], other[i],
                "image lane {i} ignores the blinding factor"
            );
        }
        // THE DELETED WOUND, stated: a lane-0-equal but distinct member published the SAME
        // one-felt blinded leaf under the deployed arity-2 tooth. The wide tooth separates them.
        let mut sibling_member = leaf;
        sibling_member[4] += BabyBear::ONE;
        assert_eq!(sibling_member[0], leaf[0], "shares the lane-0 projection");
        assert_eq!(
            blinded_leaf(leaf[0], blinding),
            blinded_leaf(sibling_member[0], blinding),
            "the deployed one-felt tooth CANNOT tell these two members apart — the wound"
        );
        assert_ne!(
            blinded_leaf_8(&leaf, blinding),
            blinded_leaf_8(&sibling_member, blinding),
            "the WIDE tooth must separate two members that agree only on lane 0"
        );
    }

    /// STEP 1 — THE PRODUCTION POLE + ROUND-TRIP: an honest DEPTH-8, general-position blinded
    /// membership proves through the dispatched descriptor and re-verifies, and its 16 PIs
    /// ROUND-TRIP: the published blinded-leaf group IS `blinded_leaf_8(leaf, blinding)` and the
    /// published root group IS the independently recomputed `membership_root_4ary` fold, lane for
    /// lane. The member digest and the blinding factor are HIDDEN.
    #[test]
    fn honest_depth8_general_position_proves_verifies_and_round_trips() {
        let depth = 8usize;
        let name = format!("{BLINDED_4ARY_NAME_PREFIX}{depth}");
        let desc = descriptor_by_name(&name).expect("dispatch");
        let leaf = d8(0xA11CE);
        let blinding = BabyBear::new(0xB11D);
        let (siblings, positions, prod_root) = create_test_witness(leaf, depth);
        let (trace, pis) = blinded_membership_witness_4ary(leaf, blinding, &siblings, &positions)
            .expect("witness builds");

        assert_eq!(trace.len(), depth, "one trace row per 4-ary Merkle level");
        assert_eq!(trace[0].len(), BLINDED_4ARY_WIDTH);
        assert_eq!(pis.len(), BLINDED_4ARY_PI_COUNT);

        // ROUND-TRIP, not "two digests differ".
        assert_eq!(
            &pis[PI_BLINDED_LEAF_4ARY..PI_BLINDED_LEAF_4ARY + DIGEST_W],
            &blinded_leaf_8(&leaf, blinding)[..],
            "PIs 0..8 must BE the genuine A9(leaf8 ‖ blinding) image"
        );
        assert_eq!(
            &pis[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W],
            &membership_root_4ary(leaf, &siblings, &positions)[..],
            "PIs 8..16 must BE the independently folded node8 root"
        );
        assert_eq!(&pis[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W], &prod_root[..]);
        // and the trace agrees with the PIs at both ends.
        assert_eq!(
            &trace[0][BLINDED_LEAF_COL_4ARY..BLINDED_LEAF_COL_4ARY + DIGEST_W],
            &pis[PI_BLINDED_LEAF_4ARY..PI_BLINDED_LEAF_4ARY + DIGEST_W]
        );
        assert_eq!(
            &trace[depth - 1][crate::membership_descriptor_4ary::PAR
                ..crate::membership_descriptor_4ary::PAR + DIGEST_W],
            &prod_root[..]
        );

        // The member digest and the blinding factor are HIDDEN — no lane of either is published.
        for k in 0..DIGEST_W {
            assert!(
                !pis.contains(&leaf[k]),
                "member lane {k} leaked into the PIs — it is a hidden witness"
            );
        }
        assert!(
            !pis.contains(&blinding),
            "the blinding factor is hidden, not a PI"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest depth-8 general-position wide blinded membership must prove");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
    }

    /// Round-trips + proves at every production depth (2, 4, 8), all general-position.
    #[test]
    fn round_trips_depths_2_4_8() {
        for depth in [2usize, 4, 8] {
            let name = format!("{BLINDED_4ARY_NAME_PREFIX}{depth}");
            let desc = descriptor_by_name(&name).expect("dispatch");
            let leaf = d8(0xF00D + depth as u32);
            let blinding = BabyBear::new(0xBEEF + depth as u32);
            let (trace, pis, root) = general_position_witness(leaf, blinding, depth);
            assert_eq!(&pis[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W], &root[..]);
            assert_eq!(
                &pis[PI_BLINDED_LEAF_4ARY..PI_BLINDED_LEAF_4ARY + DIGEST_W],
                &blinded_leaf_8(&leaf, blinding)[..]
            );
            let proof =
                prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| panic!("depth-{depth} must prove: {e}"));
            verify_vm_descriptor2(&desc, &proof, &pis)
                .unwrap_or_else(|e| panic!("depth-{depth} must verify: {e}"));
        }
    }

    /// STEP 2 — NON-MEMBER: a forged claimed `root` PI makes the root pin UNSAT — in EVERY lane,
    /// not just lane 0 (which is all the one-felt family pinned). Non-vacuous: honest first.
    #[test]
    fn forged_root_refuses_in_every_lane() {
        let depth = 4usize;
        let desc =
            descriptor_by_name(&format!("{BLINDED_4ARY_NAME_PREFIX}{depth}")).expect("dispatch");
        let (trace, pis, _) = general_position_witness(d8(1001), BabyBear::new(7), depth);
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: the honest witness is accepted"
        );
        for lane in 0..DIGEST_W {
            let mut bad = pis.clone();
            bad[PI_ROOT_4ARY + lane] += BabyBear::ONE;
            assert!(
                rejects(&desc, &trace, &bad),
                "a claimed root differing in lane {lane} must be REJECTED"
            );
        }
    }

    /// STEP 2b — a forged CO-PATH at an interior level (claiming the real root) is rejected, and a
    /// HIGH-LANE-only sibling change — a change the one-felt fold was structurally blind to — is
    /// seen and refused. The depth-8 proof genuinely consumes all 8 `node8` levels, at full width.
    #[test]
    fn forged_interior_copath_refuses_including_high_lane_only() {
        let depth = 8usize;
        let desc =
            descriptor_by_name(&format!("{BLINDED_4ARY_NAME_PREFIX}{depth}")).expect("dispatch");
        let leaf = d8(0xBEEF);
        let blinding = BabyBear::new(0x51D);
        let (siblings, positions, root) = create_test_witness(leaf, depth);
        let (honest_trace, honest_pis) =
            blinded_membership_witness_4ary(leaf, blinding, &siblings, &positions)
                .expect("witness");
        assert!(
            !rejects(&desc, &honest_trace, &honest_pis),
            "non-vacuity: the honest witness is accepted"
        );

        // lane 0 at three levels, plus a HIGH lane (7) — the one-felt blind spot.
        for (lvl, lane) in [(0usize, 0usize), (3, 0), (7, 0), (3, 7), (7, 5)] {
            let mut bad = siblings.clone();
            bad[lvl][0][lane] += BabyBear::ONE;
            assert_ne!(
                membership_root_4ary(leaf, &bad, &positions),
                root,
                "a level-{lvl} lane-{lane} sibling change must move the root"
            );
            let (bad_trace, _) =
                blinded_membership_witness_4ary(leaf, blinding, &bad, &positions).expect("witness");
            assert!(
                rejects(&desc, &bad_trace, &honest_pis),
                "a forged co-path at level {lvl} lane {lane} (claiming the real root) must be \
                 REJECTED"
            );
        }
    }

    /// STEP 3 — ⚑ THE LANE-0-EQUAL FORGERY: an attacker publishes a `blinded_leaf` that agrees
    /// with the honest one on LANE 0 — the entire binding the deployed one-felt family had — but
    /// differs at a higher lane. Overwriting the row-0 column group AND its PI copy (so the pin
    /// stays satisfiable) leaves the arity-11 blinding lookup with no serving chip row → UNSAT.
    /// Non-vacuous: the honest witness is accepted first.
    #[test]
    fn a_lane0_equal_but_distinct_blinded_leaf_is_refused() {
        let depth = 4usize;
        let desc =
            descriptor_by_name(&format!("{BLINDED_4ARY_NAME_PREFIX}{depth}")).expect("dispatch");
        let (trace, pis, _) = general_position_witness(d8(0xDEC0DE), BabyBear::new(0x51D), depth);
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: the honest witness is accepted"
        );

        for lane in 1..DIGEST_W {
            let mut bad_trace = trace.clone();
            let mut bad_pis = pis.clone();
            let bogus = trace[0][BLINDED_LEAF_COL_4ARY + lane] + BabyBear::ONE;
            bad_trace[0][BLINDED_LEAF_COL_4ARY + lane] = bogus;
            bad_pis[PI_BLINDED_LEAF_4ARY + lane] = bogus; // keep the PI pin satisfiable
            assert_eq!(
                bad_pis[PI_BLINDED_LEAF_4ARY], pis[PI_BLINDED_LEAF_4ARY],
                "the forgery agrees on lane 0 — the deployed family's whole binding"
            );
            assert!(
                rejects(&desc, &bad_trace, &bad_pis),
                "a published blinded leaf differing only at lane {lane} must be REJECTED \
                 (the arity-11 blinding lookup has no serving chip row)"
            );
        }
        // And the lane-0 forgery too, so the gate is not lane-selective.
        let mut bad_trace = trace.clone();
        let mut bad_pis = pis.clone();
        let bogus = trace[0][BLINDED_LEAF_COL_4ARY] + BabyBear::ONE;
        bad_trace[0][BLINDED_LEAF_COL_4ARY] = bogus;
        bad_pis[PI_BLINDED_LEAF_4ARY] = bogus;
        assert!(
            rejects(&desc, &bad_trace, &bad_pis),
            "lane-0 forgery refused"
        );
    }

    /// STEP 4 — UNLINKABILITY, AT WIDTH: the SAME member blinded with two DIFFERENT factors yields
    /// blinded-leaf PIs that differ in ALL EIGHT lanes (not merely "the digests differ"), while
    /// committing to the SAME 8-felt root. Both shows prove and verify.
    #[test]
    fn unlinkability_two_factors_differ_in_every_lane_and_both_verify() {
        let depth = 4usize;
        let desc =
            descriptor_by_name(&format!("{BLINDED_4ARY_NAME_PREFIX}{depth}")).expect("dispatch");
        let leaf = d8(1001);
        let (siblings, positions, _root) = create_test_witness(leaf, depth);
        let (t1, p1) =
            blinded_membership_witness_4ary(leaf, BabyBear::new(0xB11D), &siblings, &positions)
                .expect("show 1");
        let (t2, p2) =
            blinded_membership_witness_4ary(leaf, BabyBear::new(0xDEAD), &siblings, &positions)
                .expect("show 2");

        for lane in 0..DIGEST_W {
            assert_ne!(
                p1[PI_BLINDED_LEAF_4ARY + lane],
                p2[PI_BLINDED_LEAF_4ARY + lane],
                "two shows of ONE credential must differ in blinded-leaf lane {lane} — a lane \
                 that agreed across shows would be a linkability handle"
            );
        }
        assert_eq!(
            &p1[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W],
            &p2[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W],
            "both shows commit to the same member under the same 8-felt root"
        );

        let pf1 = prove_vm_descriptor2(&desc, &t1, &p1, &MemBoundaryWitness::default(), &[])
            .expect("show 1 proves");
        verify_vm_descriptor2(&desc, &pf1, &p1).expect("show 1 verifies");
        let pf2 = prove_vm_descriptor2(&desc, &t2, &p2, &MemBoundaryWitness::default(), &[])
            .expect("show 2 proves");
        verify_vm_descriptor2(&desc, &pf2, &p2).expect("show 2 verifies");
    }

    /// STEP 5 — malformed inputs (non-power-of-two depth, length mismatch, out-of-range position)
    /// are refused at witness-build time by the shared path builder.
    #[test]
    fn malformed_witness_refuses() {
        let leaf = d8(7);
        let blinding = BabyBear::new(3);
        let zero3 = [[BabyBear::ZERO; DIGEST_W]; 3];
        assert!(
            blinded_membership_witness_4ary(leaf, blinding, &vec![zero3; 3], &[0, 0, 0]).is_err(),
            "depth 3 is not a power of two"
        );
        assert!(
            blinded_membership_witness_4ary(leaf, blinding, &vec![zero3; 2], &[0]).is_err(),
            "siblings/positions length mismatch"
        );
        assert!(
            blinded_membership_witness_4ary(leaf, blinding, &vec![zero3; 2], &[0, 4]).is_err(),
            "position 4 is out of range"
        );
    }
}
