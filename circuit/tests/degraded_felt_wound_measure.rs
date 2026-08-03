//! MEASUREMENT ONLY (no AIR is authored here) — quantify what the two surviving
//! `check-no-degraded-felt.sh` reds actually admit.
//!
//! Site A: `cell/src/commitment.rs` cap-leaf `target` <- `cap_root::fold_bytes32`
//! Site B: `node/src/turn_proving.rs` `nullifier_to_field` <- `fold_bytes32_to_bb`
//!
//! Both sit on `bytes32_to_8_limbs`, whose per-chunk `% BABYBEAR_P` is UPSTREAM of
//! whatever hashes it. This file constructs the aliasing pre-images with zero search
//! and prints the exploitable counts.

use dregg_circuit::cap_root;
use dregg_circuit::effect_vm::{bytes32_to_8_limbs, fold_bytes32_to_bb};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

/// The number of u32 values that have a mod-`p` sibling inside `u32`:
/// `v` and `v + p` both fit iff `v < 2^32 - p`.
const ALIASABLE_U32: u64 = (1u64 << 32) - BABYBEAR_P as u64;

fn hx(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn u32_at(b: &[u8; 32], chunk: usize) -> u32 {
    let o = chunk * 4;
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}

fn set_u32_at(b: &mut [u8; 32], chunk: usize, v: u32) {
    let o = chunk * 4;
    b[o..o + 4].copy_from_slice(&v.to_le_bytes());
}

/// Construct a DISTINCT 32-byte string with an identical `bytes32_to_8_limbs`
/// image, by adding/subtracting `p` in one 4-byte chunk. Returns `None` only when
/// no chunk of `src` is aliasable.
fn alias_of(src: &[u8; 32]) -> Option<[u8; 32]> {
    let p = BABYBEAR_P;
    for chunk in 0..8 {
        let v = u32_at(src, chunk);
        let sibling = if v < p {
            // v + p fits in u32 exactly when v < 2^32 - p.
            if (v as u64) + (p as u64) < (1u64 << 32) {
                Some(v + p)
            } else {
                None
            }
        } else {
            Some(v - p)
        };
        if let Some(s) = sibling {
            let mut out = *src;
            set_u32_at(&mut out, chunk, s);
            debug_assert_ne!(out, *src);
            return Some(out);
        }
    }
    None
}

// ─────────────────────────────────────────────────────────────────────────────
// THE ENCODER FLOOR — shared by BOTH sites, and it is upstream of every hash.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn encoder_alias_is_constructed_not_searched() {
    // A fixed, "hash-looking" 32-byte value (a BLAKE3 image, i.e. exactly the
    // shape a CellId / nullifier has).
    let src: [u8; 32] =
        *blake3::hash(b"dregg degraded-felt measurement / site A target").as_bytes();
    let alias = alias_of(&src).expect("a random 32-byte value aliases with p = 99.77%");

    assert_ne!(src, alias, "the alias must be a DISTINCT 32-byte string");
    assert_eq!(
        bytes32_to_8_limbs(&src),
        bytes32_to_8_limbs(&alias),
        "the mod-p wrap identifies them BEFORE any sponge sees them"
    );

    // Cost of finding it: one comparison and one 32-bit add. Zero hash calls.
    println!("src   = {}", hx(&src));
    println!("alias = {}", hx(&alias));
}

/// ⚠ CORRECTS THE DOCBLOCK ON `bytes32_to_8_limbs`. That doc says "a uniformly
/// random chunk needs reducing with probability 1 - p/2^32 = 53.1%", and a reader
/// takes 53.1% to be the alias rate. It is not. `2p = 4026531842 < 2^32`, so the
/// interval `[0, 2^32)` covers every residue class at least TWICE:
///
///   residues `[0, 2^32 - 2p)`  = 268435454 of them, have THREE representatives
///   residues `[2^32 - 2p, p)`  = 1744830467 of them, have TWO
///
/// so **EVERY** 4-byte chunk value has a sibling. The alias rate is 100%, not
/// 53.1%; 53.1% is the rate at which a chunk is *itself* the non-canonical
/// representative, which is a different question and the flattering one.
#[test]
fn every_chunk_value_has_a_sibling_class_size_two_or_three() {
    let p = BABYBEAR_P as u64;
    let two_p = 2 * p;
    assert!(two_p < (1u64 << 32), "2p = {two_p} must fit under 2^32");
    assert!(
        3 * p > (1u64 << 32),
        "3p must exceed 2^32 (class size caps at 3)"
    );

    let three_rep = (1u64 << 32) - two_p;
    let two_rep = p - three_rep;
    assert_eq!(three_rep, 268_435_454);
    assert_eq!(two_rep, 1_744_830_467);
    assert_eq!(
        three_rep * 3 + two_rep * 2,
        1u64 << 32,
        "the classes partition u32"
    );

    // Sanity on the number the docblock DOES describe.
    assert_eq!(ALIASABLE_U32, 2_281_701_375);

    // Average class size per chunk, and over all 8 chunks.
    let avg = (1u64 << 32) as f64 / p as f64;
    let per32 = avg.powi(8);
    println!(
        "per-chunk sibling classes: size 3 for {three_rep}, size 2 for {two_rep} (100% aliasable)"
    );
    println!(
        "average class size per chunk = {avg:.4}; per 32-byte value = {per32:.1} = 2^{:.2}",
        per32.log2()
    );
    // 2^256 / p^8 = 2^(256 - 247.26) = 2^8.74.
    assert!((per32.log2() - 8.74).abs() < 0.01);
    // Minimum, not average: every chunk has >= 2, so >= 2^8 = 256 siblings always.
    assert_eq!(2u32.pow(8), 256);
}

#[test]
fn measured_alias_rate_over_ten_thousand_hash_images_is_total() {
    let mut aliasable = 0usize;
    const N: usize = 10_000;
    for i in 0..N {
        let src: [u8; 32] = *blake3::hash(&(i as u64).to_le_bytes()).as_bytes();
        if alias_of(&src).is_some() {
            aliasable += 1;
        }
    }
    println!("aliasable: {aliasable}/{N}");
    // Not "almost all" — ALL. Every 32-byte value has a constructible sibling.
    assert_eq!(aliasable, N, "aliasable {aliasable}/{N}");
}

// ─────────────────────────────────────────────────────────────────────────────
// SITE A — the cap-leaf `target` in the DEPLOYED capability root.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn site_a_cap_leaf_target_collides_with_zero_work() {
    let victim: [u8; 32] = *blake3::hash(b"victim cell id").as_bytes();
    let alias = alias_of(&victim).expect("aliasable");

    assert_ne!(victim, alias);
    assert_eq!(
        cap_root::fold_bytes32(&victim),
        cap_root::fold_bytes32(&alias),
        "SITE A: two DISTINCT 32-byte targets fold to the SAME cap-leaf felt"
    );

    // …and therefore to the same 7-field leaf, hence the same leaf digest.
    let mk = |t: [u8; 32]| cap_root::CapLeaf {
        slot_hash: cap_root::slot_hash(7),
        target: cap_root::fold_bytes32(&t),
        auth_tag: BabyBear::new(1),
        mask_lo: BabyBear::new(0xFFFF),
        mask_hi: BabyBear::new(0xFFFF),
        expiry: cap_root::encode_expiry(None),
        breadstuff: cap_root::encode_breadstuff(None),
    };
    assert_eq!(
        mk(victim).digest(),
        mk(alias).digest(),
        "SITE A: the 8-lane cap-LEAF DIGEST is identical for distinct targets"
    );
}

#[test]
fn site_a_breadstuff_field_collides_too() {
    // `encode_breadstuff` routes through the SAME fold, so the optional
    // breadstuff hash in a committed cap leaf has the same alias class.
    let bs: [u8; 32] = *blake3::hash(b"breadstuff").as_bytes();
    let alias = alias_of(&bs).expect("aliasable");
    assert_ne!(bs, alias);
    assert_eq!(
        cap_root::encode_breadstuff(Some(&bs)),
        cap_root::encode_breadstuff(Some(&alias)),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// SITE B — `PI[NOTESPEND_NULLIFIER]` and the double-spend freshness key.
// The fold there is LINEAR, so it is strictly worse than site A: there is a
// second, INDEPENDENT collision family that does not need the encoder wrap.
// ─────────────────────────────────────────────────────────────────────────────

fn pow(base: BabyBear, mut e: u64) -> BabyBear {
    let mut acc = BabyBear::ONE;
    let mut b = base;
    while e > 0 {
        if e & 1 == 1 {
            acc = acc * b;
        }
        b = b * b;
        e >>= 1;
    }
    acc
}

fn inv(x: BabyBear) -> BabyBear {
    // Fermat: x^(p-2).
    pow(x, (BABYBEAR_P - 2) as u64)
}

const MIX_RAW: u32 = 0x4FD3_9C8B;

#[test]
fn site_b_nullifier_fold_is_linear_and_collides_by_solving() {
    let mix = BabyBear::new(MIX_RAW % BABYBEAR_P);
    let mix_inv = inv(mix);
    assert_eq!(mix * mix_inv, BabyBear::ONE, "MIX is invertible");

    let victim: [u8; 32] = *blake3::hash(b"victim note nullifier").as_bytes();
    let target_felt = fold_bytes32_to_bb(&victim);

    // Solve, do not search: keep chunks 2..8, move delta between chunks 0 and 1.
    // fold = sum_i limb_i * MIX^i, so (limb0 += d, limb1 -= d * MIX^-1) is a kernel vector.
    let mut hits = 0usize;
    let mut first: Option<[u8; 32]> = None;
    for d in 1..=64u32 {
        let delta = BabyBear::new(d);
        let l = bytes32_to_8_limbs(&victim);
        let new0 = l[0] + delta;
        let new1 = l[1] - delta * mix_inv;
        // Both are canonical field elements < p < 2^32, so each is DIRECTLY
        // representable as a 4-byte little-endian chunk that needs no reduction.
        let mut forged = victim;
        set_u32_at(&mut forged, 0, new0.as_u32());
        set_u32_at(&mut forged, 1, new1.as_u32());
        if forged == victim {
            continue;
        }
        assert_eq!(
            fold_bytes32_to_bb(&forged),
            target_felt,
            "SITE B: linear solve produced a colliding 32-byte nullifier (delta={d})"
        );
        hits += 1;
        if first.is_none() {
            first = Some(forged);
        }
    }
    let first = first.expect("at least one solve");
    println!("victim nullifier = {}", hx(&victim));
    println!("forged nullifier = {}", hx(&first));
    println!("distinct colliding pre-images found by SOLVING (64 tried): {hits}");
    assert_eq!(
        hits, 64,
        "every delta yields a distinct colliding pre-image"
    );

    // The kernel of the fold has size p^7 over the limb lattice: fixing the
    // fold value leaves 7 free limbs. Report it as bits.
    let kernel_bits = 7.0 * (BABYBEAR_P as f64).log2();
    println!(
        "kernel dimension: 7 free limbs = 2^{kernel_bits:.2} colliding limb-vectors per image"
    );
}

#[test]
fn site_b_encoder_alias_also_collides_the_nullifier() {
    // The encoder floor applies at site B too, independently of the linearity.
    let victim: [u8; 32] = *blake3::hash(b"victim note nullifier 2").as_bytes();
    let alias = alias_of(&victim).expect("aliasable");
    assert_ne!(victim, alias);
    assert_eq!(fold_bytes32_to_bb(&victim), fold_bytes32_to_bb(&alias));
}

// ─────────────────────────────────────────────────────────────────────────────
// THE IMAGE FLOOR — one felt, whatever the encoder.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn one_felt_image_destroys_two_hundred_twenty_five_bits() {
    let image_bits = (BABYBEAR_P as f64).log2();
    assert!(
        (image_bits - 30.907).abs() < 0.001,
        "log2(p) = {image_bits}"
    );
    let destroyed = 256.0 - image_bits;
    println!("source 256 bits -> image {image_bits:.3} bits; destroyed {destroyed:.3} bits");
    println!(
        "generic birthday on the image alone: 2^{:.2}",
        image_bits / 2.0
    );
    assert!(destroyed > 225.0);
    // The repo's own stated bar is ~124 bits. 30.907/2 = 15.45.
    assert!(image_bits / 2.0 < 16.0);
}
