//! **THE FIELDS-ROOT GENTIAN-WELD TOOTH — the 31-bit fields-root forge is CLOSED at 8-felt.**
//!
//! The fields hole (the soundness downgrade the faithful 8-felt fields root closes): the deployed
//! user-field-MAP tree's root is a native-`node8` 8-felt digest (8 lanes, ~124 bits), but a verifier
//! that pinned only LANE 0 (the historical scalar `fields_root` limb 36, a ~2^31 projection) could be
//! fooled — two GENUINELY-DIFFERENT field maps (a cell whose overflow map binds key A vs key B) can
//! COLLIDE on lane 0 while topping DIFFERENT 8-felt roots. A ledgerless light client holding only the
//! lane-0 projection could not tell which state the cell committed to.
//!
//! This tooth reconstructs a CONCRETE such collision (found by a birthday search over the overflow
//! entry's key; the two keys are pinned so the tooth is deterministic) and shows:
//!
//!   * the two field maps are GENUINELY different (different keys → different 8-felt roots);
//!   * their LANE-0 roots COLLIDE — the 31-bit hole a 1-felt `fields_root` commit leaves open;
//!   * the FAITHFUL 8-felt root (limb 36 ‖ completion limbs 65,66,19..23, the value
//!     `compute_canonical_fields_root_8` / `compute_rotated_pre_limbs` commits) SEPARATES them.
//!
//! So the 31-bit forge that survived a lane-0 commit cannot survive the 8-felt welded commit: the
//! deployed fields-write descriptor's trace-forced weld (the native `node8` MapOps recompose on
//! `BUS_P2`, all eight lanes pinned) rejects a forged colliding field map — ledgerless, with no
//! post-cell to consult. Modeled byte-for-byte on `heap_root_gentian_weld.rs`.

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{HeapLeaf, compute_canonical_heap_root_8};
use dregg_circuit::openable_fields_root::{REFUSAL_AUDIT_EXT_KEY, field_key_hash};

/// The OPENABLE leaf set of a single-overflow-entry field map keyed by `key` (the forge axis: the
/// overflow key the cell's state binds). Mirrors `dregg_cell::state::fields_root_leaves` inline (the
/// reserved value-ZERO refusal-audit slot included) so the tooth exercises the deployed tree over the
/// SAME leaf discipline `compute_canonical_fields_root_8` folds.
fn fields_leaves(key: u64) -> Vec<HeapLeaf> {
    let mut leaves = vec![HeapLeaf {
        addr: field_key_hash(key),
        value: BabyBear::new(42),
    }];
    let audit_addr = field_key_hash(REFUSAL_AUDIT_EXT_KEY);
    if !leaves.iter().any(|l| l.addr == audit_addr) {
        leaves.push(HeapLeaf {
            addr: audit_addr,
            value: BabyBear::ZERO,
        });
    }
    leaves
}

/// A single-entry field map whose lone overflow entry is keyed by `key`. Everything else is fixed, so
/// two keys produce two GENUINELY-different field-map states (a value bound at key A vs key B).
fn fields_root_8(key: u64) -> [BabyBear; 8] {
    compute_canonical_heap_root_8(fields_leaves(key)).limbs()
}

// ── The pinned colliding pair (found by `search_fields_lane0_collision` below). ───────────────────
// Two genuinely-different overflow keys whose 8-felt fields roots share LANE 0 (the ~31-bit
// projection) but differ in the completion lanes. Regenerate with:
//   cargo test -p dregg-circuit --test fields_root_gentian_weld -- --ignored --nocapture
const COLLIDE_KEY_A: u64 = 25545;
const COLLIDE_KEY_B: u64 = 66188;
const COLLIDE_LANE0: u32 = 641231100;

#[test]
fn fields_root_gentian_31bit_collision_separated_at_8_felt() {
    // Guard: the search must have been run and the pinned pair filled in.
    assert_ne!(
        COLLIDE_KEY_A, COLLIDE_KEY_B,
        "pinned colliding pair not set — run the ignored `search_fields_lane0_collision` generator"
    );

    let root_a = fields_root_8(COLLIDE_KEY_A);
    let root_b = fields_root_8(COLLIDE_KEY_B);

    // Sanity: the pinned lane-0 matches the recorded constant.
    assert_eq!(root_a[0].as_u32(), COLLIDE_LANE0, "pinned lane-0 drifted");

    // The two field maps are GENUINELY different states (the value is bound at a different key) — the
    // forge's whole point.
    assert_ne!(
        field_key_hash(COLLIDE_KEY_A),
        field_key_hash(COLLIDE_KEY_B),
        "the two field maps must bind genuinely-different keys"
    );

    // LANE 0 (the historical scalar `fields_root` limb 36, ~2^31 projection): the two maps COLLIDE — a
    // ledgerless verifier pinning only lane 0 cannot tell them apart. THIS IS THE HOLE.
    assert_eq!(
        root_a[0], root_b[0],
        "the lane-0 fields-root projection COLLIDES the two distinct field maps — the 31-bit hole"
    );

    // THE FAITHFUL 8-felt root (all 8 lanes, the value the rotated commit absorbs at limb 36 ‖
    // 65,66,19..23 and the write descriptor's node8 weld forces): the two are SEPARATED. The forge
    // that survived a lane-0 commit cannot survive the 8-felt welded commit — UNSAT, ledgerless.
    assert_ne!(
        root_a, root_b,
        "the FAITHFUL 8-felt fields root must SEPARATE the lane-0-colliding distinct field maps \
         — the GENTIAN close (the native node8 commit no longer opens as either map)"
    );

    // The separation lives in the completion lanes 1..7 (limbs 65,66,19..23), exactly the felts the
    // weld added — lane 0 alone is blind here.
    assert_ne!(
        root_a[1..8],
        root_b[1..8],
        "the completion lanes 1..7 (committed at limbs 65,66,19..23) carry the separation lane 0 misses"
    );
}

/// One-shot birthday search for a lane-0 fields-root collision across two distinct keys. `#[ignore]`d
/// (it is the GENERATOR for the pinned `COLLIDE_KEY_*` constants, not a CI assertion). Run with
/// `--ignored --nocapture` and paste the printed pair into the constants above.
#[test]
#[ignore]
fn search_fields_lane0_collision() {
    use std::collections::HashMap;
    let mut seen: HashMap<u32, u64> = HashMap::new();
    for key in 0u64..200_000_000 {
        let lane0 = fields_root_8(key)[0].as_u32();
        if let Some(&prev) = seen.get(&lane0) {
            if fields_root_8(prev) != fields_root_8(key) {
                println!(
                    "FIELDS_COLLISION_KEY_A = {prev}; FIELDS_COLLISION_KEY_B = {key}; lane0 = {lane0}"
                );
                return;
            }
        } else {
            seen.insert(lane0, key);
        }
    }
    panic!("no lane-0 fields-root collision found in the searched range");
}
