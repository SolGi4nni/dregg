//! **Byte→felt codec pins.** The falsifiers for the Stage-0/1 collapse in
//! `docs/DESIGN-canonical-byte-felt-codec.md`.
//!
//! Three things are pinned here, and each exists because the collapse would otherwise rest on a
//! reading rather than on a test:
//!
//! 1. `effect_vm::bytes32_to_8_limbs` — now the SINGLE family-F1 body, after twelve byte-identical
//!    copies were deleted and rewired into it — computes exactly the map those copies computed.
//!    Pinned against an INDEPENDENTLY WRITTEN reference, not against itself.
//! 2. `field_limbs8` is NOT that map, and the vectors the pre-existing tests use CANNOT tell them
//!    apart. That is a live trap for whoever writes the next differential, so it is made explicit.
//! 3. `dregg_codec` — the designation — agrees with the deployed exact-fields codec it was promoted
//!    from, and its prime matches the field's.

use dregg_circuit::effect_vm::{bytes32_to_8_limbs, field_limbs8};
use dregg_circuit::exact_nullifier_aafi::{raw_to_u16_le, u16_le_to_raw};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_codec::{BABYBEAR_P as CODEC_P, Bytes32};

/// An INDEPENDENT transcription of family F1, written from the specification
/// ("eight little-endian 4-byte chunks, each reduced mod p, ascending") rather than by copying the
/// implementation. If this and `bytes32_to_8_limbs` ever disagree, one of them moved.
fn f1_reference(b: &[u8; 32]) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    for (i, slot) in out.iter_mut().enumerate() {
        let chunk = u32::from_le_bytes([b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]]);
        *slot = BabyBear::new(chunk % BABYBEAR_P);
    }
    out
}

/// Vectors chosen to be NON-UNIFORM and NON-ROTATION-INVARIANT, so a lane permutation or a
/// per-lane endianness flip cannot survive them. `[0x42; 32]` is deliberately absent — see
/// `the_uniform_vector_cannot_distinguish_f1_from_field_limbs8`.
fn adversarial_vectors() -> Vec<[u8; 32]> {
    let mut v: Vec<[u8; 32]> = Vec::new();
    // ascending bytes: every 4-byte chunk distinct, every chunk non-palindromic
    let mut asc = [0u8; 32];
    for (i, b) in asc.iter_mut().enumerate() {
        *b = i as u8;
    }
    v.push(asc);
    // descending
    let mut desc = [0u8; 32];
    for (i, b) in desc.iter_mut().enumerate() {
        *b = (255 - i) as u8;
    }
    v.push(desc);
    // one chunk above p, the rest zero (exercises the reduction on a single lane)
    for lane in 0..8usize {
        let mut b = [0u8; 32];
        b[4 * lane + 3] = 0x80;
        b[4 * lane] = 0x01;
        v.push(b);
    }
    // high bytes only in the tail (the lanes `field_limbs8` reads BIG-endian)
    let mut tail = [0u8; 32];
    tail[24..].copy_from_slice(&[1, 2, 3, 4, 5, 6, 7, 8]);
    v.push(tail);
    v
}

#[test]
fn the_single_f1_body_matches_an_independent_reference() {
    for raw in adversarial_vectors() {
        assert_eq!(
            bytes32_to_8_limbs(&raw),
            f1_reference(&raw),
            "the collapsed F1 body diverged from its specification on {raw:02x?}"
        );
    }
}

/// **The trap, made explicit.** `field_limbs8` is a DIFFERENT map — lanes 0/1 are big-endian over
/// bytes `28..32` and `24..28`, lanes 2..7 little-endian over `0..24` — so it is F1's lanes 0..5
/// rotated up by two plus a byte swap on two lanes. It is kept (its lane-0-first order is deployed
/// ABI) and it must never be substituted for F1.
#[test]
fn field_limbs8_is_a_different_map_and_must_not_be_substituted() {
    let mut asc = [0u8; 32];
    for (i, b) in asc.iter_mut().enumerate() {
        *b = i as u8;
    }
    assert_ne!(
        field_limbs8(&asc),
        bytes32_to_8_limbs(&asc),
        "field_limbs8 and bytes32_to_8_limbs are distinct maps"
    );
    // The exact relationship, so a change to either is caught rather than merely noticed.
    let f1 = bytes32_to_8_limbs(&asc);
    let fl = field_limbs8(&asc);
    for k in 2..8usize {
        assert_eq!(
            fl[k],
            f1[k - 2],
            "field_limbs8 lane {k} is F1 lane {}",
            k - 2
        );
    }
    let swap = |x: BabyBear| BabyBear::new(x.as_u32().swap_bytes() % BABYBEAR_P);
    assert_eq!(
        fl[0],
        swap(f1[7]),
        "field_limbs8 lane 0 is byteswap(F1 lane 7)"
    );
    assert_eq!(
        fl[1],
        swap(f1[6]),
        "field_limbs8 lane 1 is byteswap(F1 lane 6)"
    );
}

/// ⚠ **Why the pre-existing distinctness tests could not have caught a swap.** They use
/// `[0x42; 32]`, on which the two maps AGREE: every 4-byte chunk is byte-palindromic and the chunk
/// sequence is rotation-invariant. Any future differential must use a non-uniform vector.
#[test]
fn the_uniform_vector_cannot_distinguish_f1_from_field_limbs8() {
    for uniform in [[0x42u8; 32], [0u8; 32]] {
        assert_eq!(
            field_limbs8(&uniform),
            bytes32_to_8_limbs(&uniform),
            "on a uniform vector the two maps coincide — this is the trap, not a bug"
        );
    }
}

/// The designation agrees with the map it was promoted from: `dregg_codec::Bytes32::limbs()` IS
/// `exact_nullifier_aafi::raw_to_u16_le`, the codec backing the live exact fields root. If these
/// ever diverge, the crate stopped being the designation and became an eighteenth encoder.
#[test]
fn the_codec_designation_equals_the_deployed_exact_fields_codec() {
    assert_eq!(CODEC_P, BABYBEAR_P, "dregg-codec carries the field's prime");
    for raw in adversarial_vectors() {
        assert_eq!(
            *Bytes32::new(raw).limbs().as_u16s(),
            raw_to_u16_le(raw),
            "the codec diverged from the deployed exact-fields map on {raw:02x?}"
        );
        // ...and the inverse agrees too, in both directions.
        assert_eq!(Bytes32::new(raw).limbs().to_bytes32().into_bytes(), raw);
        assert_eq!(u16_le_to_raw(raw_to_u16_le(raw)), raw);
    }
}

/// **The wound, exhibited.** The alias pair that F1 collapses is an `O(1)` collision — no grind —
/// and the canonical codec does not collapse it. This is the falsifier for "the new codec actually
/// fixes the old failure", run against the DEPLOYED encoder rather than a description of it.
#[test]
fn f1_collides_in_o1_on_the_alias_pair_and_the_canonical_codec_does_not() {
    let mut lo = [0u8; 32];
    lo[3] = 0x08; // chunk 0 = 0x0800_0000
    let mut hi = [0u8; 32];
    hi[0] = 0x01;
    hi[3] = 0x80; // chunk 0 = 0x8000_0001 = 0x0800_0000 + p
    assert_ne!(lo, hi, "two distinct 32-byte values");

    // F1: the deployed encoder maps them to the SAME limb vector. Constructed, not searched.
    assert_eq!(
        bytes32_to_8_limbs(&lo),
        bytes32_to_8_limbs(&hi),
        "family F1 is O(1)-aliasable — if this ever fails, the encoder was fixed and this test \
         should become the regression pin for that fix"
    );

    // The canonical codec keeps them distinct, and keeps both recoverable.
    let (a, b) = (Bytes32::new(lo), Bytes32::new(hi));
    assert_ne!(a.limbs(), b.limbs());
    assert_eq!(a.limbs().to_bytes32(), a);
    assert_eq!(b.limbs().to_bytes32(), b);
}
