//! **THE HEAP-ROOT GENTIAN-WELD TOOTH — the 31-bit heap-root forge is CLOSED at 8-felt.**
//!
//! The heap hole (the soundness downgrade the faithful 8-felt heap root closes): the deployed heap
//! tree's root is a native-`heap_node8` 8-felt digest (8 lanes, ~124 bits), but a verifier that
//! pinned only LANE 0 (the historical scalar `heap_root` limb 28, a ~2^31 projection) could be
//! fooled — two GENUINELY-DIFFERENT heaps (a cell whose state maps address A vs address B) can
//! COLLIDE on lane 0 while topping DIFFERENT 8-felt roots. A ledgerless light client holding only
//! the lane-0 projection could not tell which state the cell committed to.
//!
//! This tooth reconstructs a CONCRETE such collision (found by a birthday search over the heap
//! entry's key; the two keys are pinned so the tooth is deterministic) and shows:
//!
//!   * the two heaps are GENUINELY different (different entries → different 8-felt roots);
//!   * their LANE-0 roots COLLIDE — the 31-bit hole a 1-felt `heap_root` commit leaves open;
//!   * the FAITHFUL 8-felt root (limb 28 ‖ completion limbs 58..64, the value
//!     `compute_canonical_heap_root_8` / `compute_rotated_pre_limbs` commits) SEPARATES them.
//!
//! So the 31-bit forge that survived a lane-0 commit cannot survive the 8-felt welded commit: the
//! deployed heap-write descriptor's trace-forced weld (the native `node8` MapOps recompose on
//! `BUS_P2`, all eight lanes pinned) rejects a forged colliding heap — ledgerless, with no post-cell
//! to consult. Modeled byte-for-byte on `cap_root_gentian_weld.rs`.

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{HeapLeaf, compute_canonical_heap_root_8, heap_addr};

/// A single-entry heap whose lone entry is keyed by `key_salt` (the forge axis: the address the
/// cell's state maps). Everything else is fixed, so two salts produce two GENUINELY-different heap
/// states (a value stored at address A vs address B).
fn heap_root_8(key_salt: u32) -> [BabyBear; 8] {
    compute_canonical_heap_root_8(vec![one_entry(key_salt)])
}

fn one_entry(key_salt: u32) -> HeapLeaf {
    HeapLeaf {
        addr: heap_addr(BabyBear::new(1), BabyBear::new(key_salt)),
        value: BabyBear::new(42),
    }
}

// ── The pinned colliding pair (found by `search_heap_lane0_collision` below). ─────────────────────
// Two genuinely-different heap keys whose 8-felt heap roots share LANE 0 (the ~31-bit projection) but
// differ in the completion lanes. Regenerate with:
//   cargo test -p dregg-circuit --test heap_root_gentian_weld -- --ignored --nocapture
// Two distinct heap keys whose 8-felt heap roots share LANE 0 == 424579150 (the ~31-bit projection)
// but differ in the completion lanes — found by `search_heap_lane0_collision`.
const COLLIDE_SALT_A: u32 = 99374;
const COLLIDE_SALT_B: u32 = 144075;

#[test]
fn heap_root_gentian_31bit_collision_separated_at_8_felt() {
    // Guard: the search must have been run and the pinned pair filled in.
    assert_ne!(
        COLLIDE_SALT_A, COLLIDE_SALT_B,
        "pinned colliding pair not set — run the ignored `search_heap_lane0_collision` generator"
    );

    let root_a = heap_root_8(COLLIDE_SALT_A);
    let root_b = heap_root_8(COLLIDE_SALT_B);

    // The two heaps are GENUINELY different states (the entry is mapped at a different address) — the
    // forge's whole point.
    assert_ne!(
        one_entry(COLLIDE_SALT_A).addr,
        one_entry(COLLIDE_SALT_B).addr,
        "the two heaps must map genuinely-different addresses"
    );

    // LANE 0 (the historical scalar `heap_root` limb 28, ~2^31 projection): the two heaps COLLIDE — a
    // ledgerless verifier pinning only lane 0 cannot tell them apart. THIS IS THE HOLE.
    assert_eq!(
        root_a[0], root_b[0],
        "the lane-0 heap-root projection COLLIDES the two distinct heaps — the 31-bit hole"
    );

    // THE FAITHFUL 8-felt root (all 8 lanes, the value the rotated commit absorbs at limb 28 ‖ 58..64
    // and the write descriptor's node8 weld forces): the two are SEPARATED. The forge that survived a
    // lane-0 commit cannot survive the 8-felt welded commit — UNSAT, ledgerless.
    assert_ne!(
        root_a, root_b,
        "the FAITHFUL 8-felt heap root must SEPARATE the lane-0-colliding distinct heaps \
         — the GENTIAN close (the native node8 commit no longer opens as either heap)"
    );

    // The separation lives in the completion lanes 1..7 (limbs 58..64), exactly the felts the weld
    // added — lane 0 alone is blind here.
    assert_ne!(
        root_a[1..8],
        root_b[1..8],
        "the completion lanes 1..7 (committed at limbs 58..64) carry the separation lane 0 misses"
    );
}

/// Lane-0 of the 8-felt leaf digest equals the lossy 1-felt `HeapLeaf::digest` (`hash_many`): the
/// 8-felt weld EXTENDS the deployed 1-felt commitment (does not fork it). The completion lanes 1..7
/// are the faithful extras the 1-felt chain dropped.
#[test]
fn heap_leaf_digest8_lane0_matches_1felt() {
    let leaf = one_entry(12345);
    assert_eq!(
        leaf.digest8()[0],
        leaf.digest(),
        "8-felt leaf digest lane 0 must equal the deployed 1-felt hash_many leaf digest"
    );
}

/// One-shot birthday search for a lane-0 heap-root collision across two distinct keys. `#[ignore]`d
/// (it is the GENERATOR for the pinned `COLLIDE_SALT_*` constants, not a CI assertion). Run with
/// `--ignored --nocapture` and paste the printed pair into the constants above.
#[test]
#[ignore]
fn search_heap_lane0_collision() {
    use std::collections::HashMap;
    let mut seen: HashMap<u32, u32> = HashMap::new();
    for salt in 0u32..80_000_000 {
        let lane0 = heap_root_8(salt)[0].as_u32();
        if let Some(&prev) = seen.get(&lane0) {
            if heap_root_8(prev) != heap_root_8(salt) {
                println!(
                    "HEAP_COLLISION_SALT_A = {prev}; HEAP_COLLISION_SALT_B = {salt}; lane0 = {lane0}"
                );
                return;
            }
        } else {
            seen.insert(lane0, salt);
        }
    }
    panic!("no lane-0 heap-root collision found in the searched range");
}
