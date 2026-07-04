//! **THE CAP-ROOT GENTIAN-WELD TOOTH — the 31-bit cap-root forge is CLOSED at 8-felt.**
//!
//! The cap hole (the soundness downgrade the faithful 8-felt cap root closes): the deployed cap
//! tree's root is a native-`node8` `Digest8` (8 lanes, ~124 bits), but a verifier that pinned only
//! LANE 0 (the historical scalar `cap_root` limb 25, a ~2^31 projection) could be fooled — two
//! GENUINELY-DIFFERENT capability trees (a cap scoped to cell A vs cell B) can COLLIDE on lane 0
//! while topping DIFFERENT 8-felt roots. A ledgerless light client holding only the lane-0 projection
//! could not tell which target the consumed cap was scoped to.
//!
//! This tooth reconstructs a CONCRETE such collision (found by a birthday search over the cap's
//! `target` field; the two salts are pinned so the tooth is deterministic) and shows:
//!
//!   * the two cap trees are GENUINELY different (different leaves → different 8-felt roots);
//!   * their LANE-0 roots COLLIDE — the 31-bit hole a 1-felt `cap_root` commit leaves open;
//!   * the FAITHFUL 8-felt root (limb 25 ‖ completion limbs 51..57, the value
//!     `compute_canonical_capability_root_8` / `compute_rotated_pre_limbs` commits) SEPARATES them.
//!
//! So the 31-bit forge that survived a lane-0 commit cannot survive the 8-felt welded commit: the
//! deployed write descriptor's trace-forced `afterCapRootCols` weld (Lean
//! `effCapOpenWriteV3 … _forces_write8`, the native `recomposeUp8` / `writesTo8` relation) pins all
//! eight lanes, so a forged colliding tree is UNSAT — ledgerless, with no post-cell to consult.

use dregg_circuit::cap_root::{
    CapLeaf, compute_capability_root, encode_breadstuff, encode_expiry, fold_bytes32, slot_hash,
    split_effect_mask,
};
use dregg_circuit::field::BabyBear;

/// A single-capability c-list whose lone cap is scoped to `target_salt` (the forge axis: the cell the
/// capability authorizes). Everything else is fixed, so two salts produce two GENUINELY-different
/// authority states (a cap over cell A vs a cap over cell B).
fn cap_tree_root_8(target_salt: u32) -> [BabyBear; 8] {
    compute_capability_root(vec![one_cap(target_salt)]).limbs()
}

fn one_cap(target_salt: u32) -> CapLeaf {
    let mut tgt = [0u8; 32];
    tgt[0..4].copy_from_slice(&target_salt.to_le_bytes());
    let (mask_lo, mask_hi) = split_effect_mask(0x0000_00FF);
    CapLeaf {
        slot_hash: slot_hash(1),
        target: fold_bytes32(&tgt),
        auth_tag: BabyBear::new(1),
        mask_lo,
        mask_hi,
        expiry: encode_expiry(None),
        breadstuff: encode_breadstuff(None),
    }
}

// ── The pinned colliding pair (found by `search_cap_lane0_collision` below). ──────────────────────
// Two genuinely-different cap targets whose 8-felt cap roots share LANE 0 (the ~31-bit projection) but
// differ in the completion lanes. Regenerate with:
//   cargo test -p dregg-circuit --test cap_root_gentian_weld -- --ignored --nocapture
// Two distinct cap targets whose 8-felt cap roots share LANE 0 == 426068865 (the ~31-bit projection)
// but differ in the completion lanes — found by `search_cap_lane0_collision`.
const COLLIDE_SALT_A: u32 = 50249;
const COLLIDE_SALT_B: u32 = 57896;

#[test]
fn cap_root_gentian_31bit_collision_separated_at_8_felt() {
    let root_a = cap_tree_root_8(COLLIDE_SALT_A);
    let root_b = cap_tree_root_8(COLLIDE_SALT_B);

    // The two cap trees are GENUINELY different authority states (the cap is scoped to a different
    // target cell) — the forge's whole point.
    assert_ne!(
        one_cap(COLLIDE_SALT_A).target,
        one_cap(COLLIDE_SALT_B).target,
        "the two caps must be scoped to genuinely-different targets"
    );

    // LANE 0 (the historical scalar `cap_root` limb 25, ~2^31 projection): the two trees COLLIDE — a
    // ledgerless verifier pinning only lane 0 cannot tell them apart. THIS IS THE HOLE.
    assert_eq!(
        root_a[0], root_b[0],
        "the lane-0 cap-root projection COLLIDES the two distinct cap trees — the 31-bit hole"
    );

    // THE FAITHFUL 8-felt root (all 8 lanes, the value the rotated commit absorbs at limb 25 ‖ 51..57
    // and the write descriptor's `afterCapRootCols` weld forces): the two are SEPARATED. The forge
    // that survived a lane-0 commit cannot survive the 8-felt welded commit — UNSAT, ledgerless.
    assert_ne!(
        root_a, root_b,
        "the FAITHFUL 8-felt cap root must SEPARATE the lane-0-colliding distinct cap trees \
         — the GENTIAN close (the native node8 commit no longer opens as either tree)"
    );

    // The separation lives in the completion lanes 1..7 (limbs 51..57), exactly the felts the v10 weld
    // added — lane 0 alone is blind here.
    assert_ne!(
        root_a[1..8],
        root_b[1..8],
        "the completion lanes 1..7 (committed at limbs 51..57) carry the separation lane 0 misses"
    );
}

/// One-shot birthday search for a lane-0 cap-root collision across two distinct targets. `#[ignore]`d
/// (it is the GENERATOR for the pinned `COLLIDE_SALT_*` constants, not a CI assertion). Run with
/// `--ignored --nocapture` and paste the printed pair into the constants above.
#[test]
#[ignore]
fn search_cap_lane0_collision() {
    use std::collections::HashMap;
    let mut seen: HashMap<u32, u32> = HashMap::new();
    for salt in 0u32..40_000_000 {
        let lane0 = cap_tree_root_8(salt)[0].as_u32();
        if let Some(&prev) = seen.get(&lane0) {
            if cap_tree_root_8(prev) != cap_tree_root_8(salt) {
                println!(
                    "CAP_COLLISION_SALT_A = {prev}; CAP_COLLISION_SALT_B = {salt}; lane0 = {lane0}"
                );
                return;
            }
        } else {
            seen.insert(lane0, salt);
        }
    }
    panic!("no lane-0 cap-root collision found in the searched range");
}
