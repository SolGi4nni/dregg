//! `split_u64`'s stated contract was FALSE — this pins the two places it breaks.
//!
//! The doc-comment on `circuit/src/effect_vm/helpers.rs::split_u64` claimed "both
//! values fit in BabyBear (< 2^31)" and "(fits in u32 since val < 2^64)". Neither
//! holds: `val >> 30` reaches `2^34`, so the `as u32` truncates, and `BabyBear::new`
//! then reduces mod `p`. Both aliases are constructed below, so a future reader
//! cannot re-acquire the false contract from the name.
//!
//! This is the encoder underneath HORIZONLOG A8: the committed note-accumulator leaf
//! (`cell::commitment_set::CommitmentSet::accumulator_leaf`,
//! `cell::nullifier_set::NullifierSet::accumulator_leaf`) carries `split_u64(value).0`
//! ALONE, so its faithful domain is `[0, 2^30)` — and `param::NOTE_VALUE_HI`, the
//! companion limb the trace generator writes on both note rows, is read by nothing.

use dregg_circuit::effect_vm::split_u64;
use dregg_circuit::field::BABYBEAR_P;

/// The LOW limb — the only limb any committed accumulator leaf carries — is
/// `2^30`-periodic. Two ordinary values a single period apart are indistinguishable
/// to every consumer that reads `split_u64(v).0`.
#[test]
fn low_limb_is_2_30_periodic() {
    for base in [0u64, 1, 17, 4_242, 1_000_000_000] {
        let shifted = base + (1u64 << 30);
        assert_eq!(
            split_u64(base).0,
            split_u64(shifted).0,
            "low limb must be 2^30-periodic at base {base}"
        );
        assert_ne!(
            split_u64(base).1,
            split_u64(shifted).1,
            "the HIGH limb does distinguish them — it is written and read by nothing"
        );
    }
}

/// **The `as u32` truncation.** `val >> 30` is a 34-bit quantity; casting it to `u32`
/// discards bits 62..64 of the input BEFORE any field reduction. So the FULL limb
/// PAIR collides — the value is not recoverable even from both published limbs.
#[test]
fn both_limbs_collide_at_2_62_because_the_shift_is_cast_to_u32() {
    assert_eq!(
        split_u64(0),
        split_u64(1u64 << 62),
        "`(val >> 30) as u32` truncates at 2^62, so both limbs collide with zero"
    );
    assert_eq!(
        split_u64(9),
        split_u64(9 + (1u64 << 63)),
        "and again at 2^63"
    );
}

/// **The mod-`p` reduction.** Independently of the cast, the high limb is reduced
/// modulo `p`, so the pair aliases with a value period of `p · 2^30`.
#[test]
fn high_limb_aliases_at_the_field_modulus() {
    let period = (BABYBEAR_P as u64) << 30;
    assert!(
        period < (1u64 << 62),
        "the mod-p alias lands below the cast alias"
    );
    assert_eq!(
        split_u64(0),
        split_u64(period),
        "the high limb is reduced mod p, so `p * 2^30` is a second alias period"
    );
}

/// The positive pole: on `[0, 2^61)` — below both alias periods — the limb pair IS
/// faithful, so this is a bounded domain statement, not a claim that the encoder is
/// broken everywhere.
#[test]
fn the_limb_pair_is_faithful_below_the_first_alias_period() {
    let samples = [
        0u64,
        1,
        (1 << 30) - 1,
        1 << 30,
        (1 << 30) + 1,
        1_000_000_000_000,
        1 << 40,
        (1 << 60) + 12345,
    ];
    for (i, a) in samples.iter().enumerate() {
        for b in samples.iter().skip(i + 1) {
            assert_ne!(
                split_u64(*a),
                split_u64(*b),
                "values {a} and {b} are both below 2^61 and must not share a limb pair"
            );
        }
    }
}
