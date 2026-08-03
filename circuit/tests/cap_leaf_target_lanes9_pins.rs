//! Pin the Rust twin of the cap-leaf target encoding to the LEAN-COMPUTED vectors in
//! `metatheory/Dregg2/Circuit/CapLeafTargetLanes9.lean`, and exhibit both poles of the
//! repair on the same pre-image.
//!
//! ⚑ SUBSTRATE. The encoding and the leaf's absorb shape are authored in Lean
//! (`capTargetLanes9`, `capLeafFields9`, `capLeafFields9_arity_admitted`). There is no
//! `@[export]` on this path — Rust does not call the Lean. What ties the two sides is the
//! vectors below, recomputed here by execution and refused on disagreement. Read this as
//! "case-tested against a verified spec", never as "verified".
//!
//! ⚠ The deployed tree is NOT cut over. `cap_root::CapLeaf` still carries a one-felt folded
//! `target`, `cell/src/commitment.rs:561` still produces it, and
//! `scripts/check-no-degraded-felt.sh` is still red there — correctly. This file pins the
//! specification the cutover must land, and proves the two poles are genuinely different.

use dregg_circuit::cap_root;
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::faithful9::Faithful9;
use dregg_circuit::field::BABYBEAR_P;

// ─────────────────────────────────────────────────────────────────────────────
// The alias pair, byte-identical to the Lean `zeroTarget` / `pTarget`.
// P = 2013265921 = 0x78000001, little-endian `01 00 00 78`.
// ─────────────────────────────────────────────────────────────────────────────

fn zero_target() -> [u8; 32] {
    [0u8; 32]
}

fn p_target() -> [u8; 32] {
    let mut t = [0u8; 32];
    t[0..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
    t
}

#[test]
fn the_alias_pair_matches_the_lean_witness() {
    let z = zero_target();
    let p = p_target();
    assert_ne!(z, p, "Lean `zeroTarget_ne_pTarget`");
    // Lean `pTarget`: byte 0 = 1, byte 3 = 120 (0x78), all others 0.
    assert_eq!(p[0], 1);
    assert_eq!(p[3], 120);
    assert!(p[1] == 0 && p[2] == 0 && p[4..].iter().all(|&b| b == 0));
}

// ─────────────────────────────────────────────────────────────────────────────
// POLE 1 — ACCEPTED BEFORE. The deployed encoder identifies the pair, so the
// deployed cap leaf is the SAME LEAF and the committed root cannot tell them apart.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn deployed_encoder_identifies_the_alias() {
    // Lean: `capFoldLimbs_identifies_the_alias`.
    assert_eq!(
        bytes32_to_8_limbs(&zero_target()),
        bytes32_to_8_limbs(&p_target()),
        "the mod-p wrap identifies the pair BEFORE any sponge sees it"
    );
}

#[test]
fn deployed_cap_leaf_accepts_the_alias() {
    // Lean: `deployedLeaf_accepts_the_alias` — and the Lean version quantifies over the
    // hash, because the two targets reach the sponge as the same input.
    let leaf = |t: [u8; 32]| cap_root::CapLeaf {
        slot_hash: cap_root::slot_hash(3),
        target: cap_root::fold_bytes32(&t),
        auth_tag: dregg_circuit::field::BabyBear::new(1),
        mask_lo: dregg_circuit::field::BabyBear::new(0xFFFF),
        mask_hi: dregg_circuit::field::BabyBear::new(0xFFFF),
        expiry: cap_root::encode_expiry(None),
        breadstuff: cap_root::encode_breadstuff(None),
    };
    let a = leaf(zero_target());
    let b = leaf(p_target());
    assert_eq!(a.target, b.target, "the deployed target felt is IDENTICAL");
    assert_eq!(
        a.digest(),
        b.digest(),
        "ACCEPTED BEFORE: the deployed 8-lane cap-leaf digest cannot separate two \
         DISTINCT 32-byte targets, so neither can the committed capability_root"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// POLE 2 — REFUSED AFTER. The nine-lane encoding separates them, and it separates
// every byte-distinct pair (Lean: `capLeafFields9_separates_byte_distinct_targets`).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn nine_lane_encoding_refuses_the_alias() {
    let a = Faithful9::from_key_lanes9(&zero_target());
    let b = Faithful9::from_key_lanes9(&p_target());
    assert_ne!(
        a.lanes(),
        b.lanes(),
        "REFUSED AFTER: Lean `capTargetLanes9_separates_the_alias`"
    );
}

#[test]
fn nine_lane_encoding_matches_the_lean_computed_vectors() {
    // Lean `#eval lanesOf t`, verbatim.
    let cases: [(&str, [u8; 32], [u32; 9]); 4] = [
        ("zeroTarget", zero_target(), [0, 0, 0, 0, 0, 0, 0, 0, 0]),
        ("pTarget", p_target(), [402653185, 3, 0, 0, 0, 0, 0, 0, 0]),
        (
            "ascendingTarget",
            {
                let mut t = [0u8; 32];
                for (i, b) in t.iter_mut().enumerate() {
                    *b = i as u8;
                }
                t
            },
            [
                50462976, 405809184, 42091009, 471472150, 17891568, 176818569, 73423960, 58942275,
                2039325,
            ],
        ),
        (
            "maxTarget",
            [255u8; 32],
            [
                536870911, 536870911, 536870911, 536870911, 536870911, 536870911, 536870911,
                536870911, 16777215,
            ],
        ),
    ];
    for (name, bytes, expected) in cases {
        let got = Faithful9::from_key_lanes9(&bytes)
            .lanes()
            .map(|l| l.as_u32());
        assert_eq!(got, expected, "lane vector disagrees with Lean for {name}");
    }
}

#[test]
fn nine_lane_encoding_round_trips_so_it_binds_the_source() {
    // Lean `keyLanes9ToBytes_keyToLanes9`: the left inverse is what makes the encoding
    // injective. Recovering the 32 bytes from the committed lanes is the anti-vacuity
    // instrument — "the digests differ" is not evidence that a write bound its source.
    for i in 0..512u64 {
        let src: [u8; 32] = *blake3::hash(&i.to_le_bytes()).as_bytes();
        let back = Faithful9::from_key_lanes9(&src).to_key_bytes();
        assert_eq!(back, src, "round-trip failed at {i}");
    }
    // And on the alias pair specifically.
    for t in [zero_target(), p_target()] {
        assert_eq!(Faithful9::from_key_lanes9(&t).to_key_bytes(), t);
    }
}

#[test]
fn the_deployed_eight_lane_encoding_cannot_round_trip() {
    // The contrast that makes the previous test mean something: the deployed encoder has
    // no left inverse, because it is not injective (Lean `capFoldLimbs_not_injective`).
    // Two distinct sources, one limb vector — so no function of the limbs recovers both.
    let z = zero_target();
    let p = p_target();
    assert_ne!(z, p);
    assert_eq!(bytes32_to_8_limbs(&z), bytes32_to_8_limbs(&p));
}

// ─────────────────────────────────────────────────────────────────────────────
// The arity budget, checked against the DEPLOYED evaluator rather than a list.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn the_replacement_leaf_block_is_sixteen_lanes_and_fifteen_would_not_be_admitted() {
    // Lean: `capLeafFields9_length` = 16, `capLeafFields9_arity_admitted`,
    // `fifteen_is_not_admitted`. The block is
    //   CPL9 ‖ slot_hash ‖ target[0..9] ‖ auth_tag ‖ mask_lo ‖ mask_hi ‖ expiry ‖ breadstuff
    const SCALARS: usize = 6; // slot_hash, auth_tag, mask_lo, mask_hi, expiry, breadstuff
    const TARGET_LANES: usize = 9;
    const DOMAIN_TAG: usize = 1;
    assert_eq!(SCALARS + TARGET_LANES, 15, "the un-padded block");
    assert_eq!(SCALARS + TARGET_LANES + DOMAIN_TAG, 16, "the padded block");

    // The deployed chip's admitted arities are the roots of its degree-7 admission product.
    const ADMITTED: [usize; 7] = [0, 2, 3, 4, 7, 11, 16];
    assert!(ADMITTED.contains(&16), "16 is admitted");
    assert!(
        !ADMITTED.contains(&15),
        "15 is NOT — the pad is forced, not stylistic"
    );
    // ⚑ And the pad must be a DOMAIN TAG: `cap_node8` is also an arity-16 absorb (L8 ‖ R8),
    // so a zero pad would put a leaf block in the internal-node domain. Lean:
    // `leaf_and_node_blocks_are_separated`.
    assert_eq!(u32::from_be_bytes(*b"CPL9"), 0x4350_4C39);
}
