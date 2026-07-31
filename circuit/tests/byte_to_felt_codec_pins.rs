//! **Byte→felt codec pins.** The falsifiers for the Stage-0/1 collapse in
//! `docs/DESIGN-canonical-byte-felt-codec.md`.
//!
//! Three things are pinned here, and each exists because the collapse would otherwise rest on a
//! reading rather than on a test:
//!
//! 1. `effect_vm::bytes32_to_8_limbs` — now the SINGLE family-F1 body, after twelve byte-identical
//!    copies were deleted and rewired into it — computes exactly the map those copies computed.
//!    Pinned against an INDEPENDENTLY WRITTEN reference, not against itself.
//! 2. `field_limbs9` — the NINE-lane fields nonet that replaced the deleted `field_limbs8` — is NOT
//!    that map. Its lanes 0/1 are a byte-swapped F1 tail (deployed ABI, unchanged); its lanes 2..8
//!    are the seven base-`2^28` digits of `W = ofDigits 256 (b[0..24] ++ [q₀ + 4·q₁])`. ⚑ The two
//!    maps OVERLAP more than the previous (hashed) octet did — on the ZERO vector they agree
//!    completely, and free lane 2 coincides with F1 lane 0 whenever `b[3] < 16` — so the trap for
//!    whoever writes the next differential is WIDER, not narrower. It is made explicit below.
//! 3. `dregg_codec` — the designation — agrees with the deployed exact-fields codec it was promoted
//!    from, and its prime matches the field's.

use dregg_circuit::effect_vm::{bytes32_to_8_limbs, field_limbs9};
use dregg_circuit::exact_nullifier_aafi::{raw_to_u16_le, u16_le_to_raw};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_codec::{BABYBEAR_P as CODEC_P, Bytes32};

/// An INDEPENDENT transcription of `field_limbs9`'s FREE-LANE half, written from the specification
/// (`W = ofDigits 256 (b[0..24] ++ [q₀ + 4·q₁])`, read off as seven base-`2^28` digits, low first)
/// rather than by calling the encoder.
///
/// ⚑ It is deliberately a DIFFERENT ALGORITHM. The deployed body streams the 25 source bytes through
/// a 64-bit accumulator; this one assembles `W` as a 256-bit little-endian `[u64; 4]` and shifts the
/// whole number right by 28 for each digit. A transcription that reproduced the deployed loop would
/// reproduce its bugs, which is the failure mode this file exists to prevent — the previous version
/// of this reference shared the sponge primitive with its subject and could only say so in prose.
fn free_lanes_reference(b: &[u8; 32]) -> [u32; 7] {
    let lo = u32::from_be_bytes([b[28], b[29], b[30], b[31]]);
    let hi = u32::from_be_bytes([b[24], b[25], b[26], b[27]]);
    let carry = (lo / BABYBEAR_P) + 4 * (hi / BABYBEAR_P);
    assert!(carry < 16, "the carry digit is q0 + 4*q1 with each q <= 2");

    // W as a 256-bit little-endian integer: the 24 unbound bytes, then the carry as byte 24.
    let mut w = [0u64; 4];
    for (i, &byte) in b[..24].iter().enumerate() {
        w[i / 8] |= u64::from(byte) << (8 * (i % 8));
    }
    w[3] |= u64::from(carry); // source byte 24 = limb 3, bit offset 0

    let mut out = [0u32; 7];
    for digit in out.iter_mut() {
        *digit = (w[0] & ((1u64 << 28) - 1)) as u32;
        for k in 0..3 {
            w[k] = (w[k] >> 28) | (w[k + 1] << 36);
        }
        w[3] >>= 28;
    }
    assert_eq!(
        w, [0u64; 4],
        "W is 196 bits: seven 28-bit digits exhaust it"
    );
    out
}

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
/// per-lane endianness flip cannot survive them. `[0x42; 32]` and `[0; 32]` are deliberately absent
/// — see `the_uniform_vector_cannot_distinguish_f1_from_the_fields_nonet`.
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
    // high bytes only in the tail (the lanes `field_limbs9` reads BIG-endian)
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

/// **The trap, made explicit.** `field_limbs9` is a DIFFERENT map — lanes 0/1 are big-endian over
/// bytes `28..32` and `24..28`; lanes 2..8 are the seven base-`2^28` digits of
/// `W = ofDigits 256 (b[0..24] ++ [q₀ + 4·q₁])`. It must never be substituted for F1.
///
/// ⚑ **THE FREE-LANE HALF OF THIS PIN HAS BEEN REWRITTEN TWICE AND THE SECOND TIME IT GOT WEAKER,
/// WHICH IS WORTH SAYING OUT LOUD.** Lanes 2..7 were once exactly F1 lanes 0..5 (six `u32 % p`
/// chunks over bytes `0..24`), and this test asserted that equality lane-for-lane — an equality that
/// WAS the `O(1)` alias. It became a Poseidon2 image and the pin became "lane k is never F1 lane
/// k−2", which held for every input because a hash agrees with a chunk on nothing.
///
/// Under the nine-lane encoder that blanket negation is **FALSE**: free lane 2 is the low 28 bits of
/// `b[0..24]` read little-endian, so it EQUALS F1 lane 0 whenever `b[3] < 16` (ascending bytes is
/// such a vector — lane 2 and F1 lane 0 are both `0x03020100`). That is not an alias; the nonet is
/// injective as a whole. It is a per-lane coincidence, and a pin that forbade it would be a pin
/// against the correct encoder. So the discriminator is now (i) the free lanes against the
/// independent reference above, and (ii) the maps differing AS MAPS.
#[test]
fn the_fields_nonet_is_a_different_map_and_must_not_be_substituted() {
    let mut asc = [0u8; 32];
    for (i, b) in asc.iter_mut().enumerate() {
        *b = i as u8;
    }
    let f1 = bytes32_to_8_limbs(&asc);
    let fl = field_limbs9(&asc);
    assert_ne!(
        &fl[..8],
        &f1[..],
        "field_limbs9 and bytes32_to_8_limbs are distinct maps"
    );

    // (a) the DEPLOYED-ABI half — unchanged, and it must stay unchanged: lane 0 is the welded v1
    //     face column `stateBase + FIELD_BASE + i` that `field_to_u64` and every capacity weld
    //     read, lane 1 is the staged capacity descriptors' hi-pin slot.
    let swap = |x: BabyBear| BabyBear::new(x.as_u32().swap_bytes() % BABYBEAR_P);
    assert_eq!(fl[0], swap(f1[7]), "nonet lane 0 is byteswap(F1 lane 7)");
    assert_eq!(fl[1], swap(f1[6]), "nonet lane 1 is byteswap(F1 lane 6)");

    // (b) the FREE-LANE half — pinned against the independent 256-bit reference, on every
    //     adversarial vector, and never against the function itself.
    for raw in adversarial_vectors() {
        let lanes = field_limbs9(&raw);
        let reference = free_lanes_reference(&raw);
        for (i, &expected) in reference.iter().enumerate() {
            assert_eq!(
                lanes[2 + i].as_u32(),
                expected,
                "free lane {} diverged from its specification on {raw:02x?}",
                2 + i
            );
        }
        // And every free lane is below 2^28 — the property that makes them NOT the `u32 % p` shape
        // that aliased. A free lane at or above 2^28 would be a reducing lane and the wound back.
        for i in 0..7 {
            assert!(
                lanes[2 + i].as_u32() < (1 << 28),
                "free lane {} must be a 28-bit digit on {raw:02x?}",
                2 + i
            );
        }
        // The maps differ AS MAPS on every non-degenerate vector.
        assert_ne!(&lanes[..8], &bytes32_to_8_limbs(&raw)[..]);
    }

    // (c) THE COINCIDENCE, ASSERTED RATHER THAN FORBIDDEN. A pin that said "no free lane may ever
    //     equal an F1 lane" would go red against the correct encoder, so it is stated as the fact
    //     it is: the low free lane and the low F1 lane read the same bytes in the same order.
    assert_eq!(
        fl[2].as_u32(),
        f1[0].as_u32(),
        "free lane 2 IS F1 lane 0 when b[3] < 16 — a per-lane overlap, not an alias; the nonet is \
         injective as a whole (`fieldToLanes9_injective`)"
    );
    // The lanes above it cannot coincide: they are 28-bit windows, F1's are 32-bit ones.
    let mut differing = 0usize;
    for k in 3..8usize {
        if fl[k] != f1[k - 2] {
            differing += 1;
        }
    }
    assert_eq!(
        differing, 5,
        "free lanes 3..7 are 28-bit windows and F1's are 32-bit chunks — they must all differ"
    );
}

/// ⚠ **Why the pre-existing distinctness tests could not have caught a swap — and where that trap
/// GREW.** They use `[0x42; 32]`, on which F1 and the fields encoder agreed outright: every 4-byte
/// chunk is byte-palindromic and the chunk sequence is rotation-invariant.
///
/// ⚑ **AND THE ZERO VECTOR IS NOW A COMPLETE COINCIDENCE.** Under the hashed octet, `[0; 32]` still
/// separated the maps, because a hash of zero is not zero. The nine-lane encoder is a positional
/// encoding, so it necessarily sends zero to zero — exactly as F1 does — and the two maps AGREE ON
/// EVERY LANE there. The previous version of this test asserted `fl != f1` on `[0; 32]` and it would
/// now be red; it was measuring an accident of the hash, not a property of the encoding.
///
/// So the trap is wider than it was: any differential written on `[0; 32]` distinguishes NOTHING,
/// and one written on a uniform vector distinguishes nothing in lanes 0/1. Use `adversarial_vectors`.
#[test]
fn the_uniform_vector_cannot_distinguish_f1_from_the_fields_nonet() {
    // The zero vector: TOTAL coincidence across the whole octet.
    let zero_fl = field_limbs9(&[0u8; 32]);
    let zero_f1 = bytes32_to_8_limbs(&[0u8; 32]);
    assert_eq!(
        &zero_fl[..8],
        &zero_f1[..],
        "on the zero vector the two maps coincide on EVERY lane — this is the trap, not a bug: a \
         positional encoding sends zero to zero"
    );
    assert!(
        zero_fl.iter().all(|l| *l == BabyBear::ZERO),
        "and the ninth lane is zero too"
    );

    // The uniform 0x42 vector: coincidence on the deployed-ABI lanes 0/1 only.
    let fl = field_limbs9(&[0x42u8; 32]);
    let f1 = bytes32_to_8_limbs(&[0x42u8; 32]);
    assert_eq!(
        &fl[..2],
        &f1[..2],
        "on a uniform vector the two maps coincide on lanes 0/1 — the deployed ABI is byte-swap \
         invariant there"
    );
    assert_ne!(
        &fl[..8],
        &f1[..],
        "the free lanes must separate the maps on a NONZERO uniform vector"
    );
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
