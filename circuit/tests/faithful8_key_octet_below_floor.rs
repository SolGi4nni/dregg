//! **The KEY_COMMIT encoder was below the faithful-commitment law's own floor. It was REPLACED
//! on 2026-08-01, and this file is now the record of both halves of that: what closed, and the
//! one that did not.**
//!
//! ## What this file used to say
//!
//! `Faithful8::from_canonical_key` was listed beside the tree roots as a *faithful* constructor,
//! with a doc reading "8+8+8+6 = 30 bits per limb, 240 bits total, faithful". The arithmetic here
//! demoted it: `& 0x3F` discarded bits 6-7 of bytes 3, 7, …, 31, so the IMAGE was `2^240`, the
//! birthday COLLISION `2^120`, and the law's floor `2^123.63` — below floor on the generous
//! reading. The ungenerous reading is the one that mattered: an Ed25519 public key carries its
//! x-sign in bit 7 of byte 31, one of the unread bits, so a key and its negation packed to ONE
//! octet and the ACTUAL collision cost among valid keys was **`0`**.
//!
//! ## What is deployed now
//!
//! The base-`2^29` **nonet** — `dregg_commit::typed::canonical_32_to_lanes_9`, with byte-twins in
//! `dregg_cell::commitment`, `dregg_storage::commitment` and inlined in
//! `circuit/src/effect_vm/trace.rs`. `8 * 29 + 24 = 256` exactly, every lane below `2^29 < p` so
//! nothing reduces, image EXACTLY `2^256`. Its Lean authority is
//! `Dregg2.Circuit.KeyLanes9.keyToLanes9` with `keyToLanes9_injective` proved from a total decoder
//! plus a machine-checked left inverse — **not a hash bound and not a birthday bound; there is no
//! encoding collision left to quantify.**
//!
//! * `an_ed25519_key_and_its_negation_no_longer_pack_to_one_lane_vector` is the flag day as a
//!   test. It was `..._pack_to_one_octet` and it asserted the collision; it now asserts the
//!   SEPARATION, exhibits the retired octet still merging the pair, and pins that the separation
//!   happens in lane 8 and nowhere else.
//! * `the_deployed_pack_reads_every_source_bit_and_the_retired_one_read_240` is the inverted
//!   read-set walk: 256/0 for the nonet, 240/16 for the retired octet, measured side by side.
//! * `the_deployed_nonet_matches_an_independent_reference_and_round_trips` pins the deployed
//!   encoder against a differently-written reference and round-trips it. A differential, not a
//!   proof — there is no formal semantics of Rust and this encoder is not extracted from the Lean.
//! * `the_forged_nonet_passes_a_uniform_range_check_and_decodes_to_the_zero_key` keeps the
//!   envelope's SECOND range leg honest: `[0, …, 0, 2^24]` clears a uniform 29-bit check and
//!   decodes to the all-zero key, so widening 24 to 29 "for uniformity" re-opens the encoding.
//!
//! ## ⚠ AND THE HALF THAT DID NOT CLOSE — read this before quoting anything above
//!
//! **The encoder is injective. The ANCHOR WRITE is not.** `B_PUBKEY_OCTET` is eight columns wide
//! in the deployed 184-limb geometry, so `compute_rotated_pre_limbs` and its producer twin commit
//! lanes 0..=7 and DROP lane 8. Bit 7 of byte 31 is source bit 255, which lives in lane 8. So the
//! signed consensus anchor still does not distinguish the cell owned by `A` from the cell owned by
//! `-A`, and `key_octet_collision_is_below_the_law_floor` measures that residual at **232 bits of
//! image, `2^116` birthday — four bits WORSE than the retired octet's `2^120`.** Both are `0`
//! against the structured attack, and the low-eight write is the emitted shape minus one column,
//! which is why it is still the right write; the four-bit regression is asserted rather than
//! glossed, in that test.
//!
//! The column that closes it is in-block limb 186 of the 187-limb layout, PROVED and committed in
//! Lean (`RotatedLayout.rotated187`, `94532b3a4`) and **NOT EMITTED** — the emitter
//! `metatheory/EmitLayoutManifest.lean` transitively imports
//! `Dregg2/Circuit/Emit/EffectVmEmitRotationWide.lean`, which is red on three `sorryAx`
//! axiom-hygiene failures under another lane's edit. `key_nonet_ninth_lane_reaches_the_anchor.rs`
//! is the gate that flips, keyed on `NUM_PRE_LIMBS`.
//!
//! * `the_burn_down_list_names_every_hatch_admission` turns the law's "adding a `_DANGER` site
//!   without listing it here is a review-time violation" into something that can go red. ⚑ It is
//!   keyed on the `(file, reason-constant)` ADMISSION, not on the file path — see the section
//!   header below for the wound that keying cost. The residual it now names is
//!   `KEY_NONET_NINTH_LANE_UNBOUND`, not the retired `KEY_COMMIT_30BIT_RESIDUAL`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;
use dregg_cell::commitment::canonical_to_babybear_nonet;
use dregg_circuit::Faithful8;
use dregg_circuit::faithful8::KEY_NONET_NINTH_LANE_UNBOUND;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

/// The sixteen source bits the `8+8+8+6` pack throws away: bits 6 and 7 of every fourth byte.
/// Written from the SHAPE (`hi & 0x3F` on `canonical[4i+3]`), and then CHECKED against the
/// deployed packer in both directions below — this array is the hypothesis, not the measurement.
const CLAIMED_UNREAD: [(usize, u8); 16] = [
    (3, 6),
    (3, 7),
    (7, 6),
    (7, 7),
    (11, 6),
    (11, 7),
    (15, 6),
    (15, 7),
    (19, 6),
    (19, 7),
    (23, 6),
    (23, 7),
    (27, 6),
    (27, 7),
    (31, 6),
    (31, 7),
];

/// The DEPLOYED encoder: nine lanes, base `2^29`, little-endian.
fn nonet(b: &[u8; 32]) -> [u32; 9] {
    canonical_to_babybear_nonet(b)
}

/// What the rotated pre-limb write actually commits at `B_PUBKEY_OCTET`: the low eight lanes.
/// The gap between this and [`nonet`] is the whole of what is left open.
fn faithful_low8(b: &[u8; 32]) -> Faithful8 {
    Faithful8::from_key_nonet_low8(nonet(b).map(BabyBear::new))
}

/// A base vector with every bit of every byte exercised across the 32 positions, so a flip test
/// is never masked by a byte that happened to already be 0 or 0xFF.
fn base_vector() -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, byte) in b.iter_mut().enumerate() {
        *byte = (i as u8).wrapping_mul(37).wrapping_add(0x5a);
    }
    b
}

/// ⚑ **INVERTED 2026-08-01.** This was `the_deployed_pack_never_reads_sixteen_source_bits` and it
/// MEASURED the defect. The deployed pack is now the nonet and it reads all 256, so the same walk
/// is run against the same base vector and the expected counts are the other way round. The
/// retired octet is walked beside it, so the 16/240 split stays on the record as the thing that
/// changed rather than vanishing from the file.
#[test]
fn the_deployed_pack_reads_every_source_bit_and_the_retired_one_read_240() {
    let base = base_vector();

    let walk = |f: &dyn Fn(&[u8; 32]) -> Vec<u32>| {
        let reference = f(&base);
        let mut unread = Vec::new();
        let mut read = Vec::new();
        for byte in 0..32usize {
            for bit in 0..8u8 {
                let mut flipped = base;
                flipped[byte] ^= 1 << bit;
                if f(&flipped) == reference {
                    unread.push((byte, bit));
                } else {
                    read.push((byte, bit));
                }
            }
        }
        (read, unread)
    };

    // THE DEPLOYED ENCODER. Every one of the 256 source bits moves the lane vector.
    let (read, unread) = walk(&|b| nonet(b).to_vec());
    assert_eq!(
        unread.len(),
        0,
        "the deployed nonet must read every source bit; these are unread: {unread:?}"
    );
    assert_eq!(read.len(), 256, "expected 256 read source bits");

    // THE RETIRED ENCODER, walked identically. If this ever stops splitting 240/16 the refutation
    // elsewhere in this file has gone vacuous.
    let (old_read, old_unread) = walk(&|b| retired_octet_pack(b).to_vec());
    assert_eq!(old_read.len(), 240, "the retired octet read 240 bits");
    assert_eq!(
        old_unread.as_slice(),
        CLAIMED_UNREAD.as_slice(),
        "the retired octet's unread set is not the sign/high-bit pair of every fourth byte"
    );

    // ⚠ AND THE WALL, WHICH IS THE HALF THAT DID NOT CLOSE. `Faithful8::from_key_nonet_low8`
    // commits lanes 0..=7, so it is blind to source bits 232..255 — bytes 29, 30 and 31, the
    // Ed25519 sign bit among them. MEASURED here, not inferred, so the residual named by
    // `KEY_NONET_NINTH_LANE_UNBOUND` has a number attached to it in the test suite.
    let (wall_read, wall_unread) = walk(&|b| faithful_low8(b).limbs().map(|f| f.as_u32()).to_vec());
    assert_eq!(
        wall_read.len(),
        232,
        "the low-eight anchor write should bind 232 source bits"
    );
    assert_eq!(wall_unread.len(), 24);
    assert!(
        wall_unread.iter().all(|(byte, _)| *byte >= 29),
        "the unbound bits must be exactly the top three bytes, got {wall_unread:?}"
    );
    assert!(
        wall_unread.contains(&(31usize, 7u8)),
        "the Ed25519 sign bit must be among them — that is why the anchor still merges A and -A"
    );
}

#[test]
fn key_octet_collision_is_below_the_law_floor() {
    // Source A: the field's own prime, defined structurally in `circuit/src/field.rs` as
    // (1<<31) - (1<<27) + 1 — not a literal transcribed here.
    let log2_p = f64::from(BABYBEAR_P).log2();

    // THE FLOOR the law quotes as "~124-bit" is a BIRTHDAY COLLISION bound over a full 8-lane
    // image: 8 lanes x log2 p bits of image, halved.
    let floor_image_bits = 8.0 * log2_p;
    let floor_collision_bits = floor_image_bits / 2.0;
    assert!(
        (floor_image_bits - 247.255).abs() < 1e-2,
        "8-lane image is 247.26 bits, got {floor_image_bits}"
    );
    assert!(
        (floor_collision_bits - 123.6276).abs() < 1e-3,
        "the law's ~124-bit floor is 123.63 bits of COLLISION, got {floor_collision_bits}"
    );

    // Source B: what the ANCHOR now binds, derived from the MEASURED read-set of the low-eight
    // write rather than from any doc. ⚠ THIS IS THE NUMBER TO QUOTE FOR THE RESIDUAL, and it is
    // the unflattering one of the pair.
    let base = base_vector();
    let reference = faithful_low8(&base).limbs();
    let mut unread = 0u32;
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if faithful_low8(&flipped).limbs() == reference {
                unread += 1;
            }
        }
    }
    let anchor_image_bits = f64::from(256 - unread);
    let anchor_collision_bits = anchor_image_bits / 2.0;
    assert_eq!(anchor_image_bits, 232.0, "measured anchor image bits");
    assert_eq!(anchor_collision_bits, 116.0);

    // ⚑ SAY IT PLAINLY, INCLUDING THE PART THAT GOT WORSE. The retired octet bound 240 bits at
    // this site (birthday 2^120); the low-eight nonet write binds 232 (birthday 2^116). On the
    // birthday number the anchor moved DOWN by four bits, and quoting only "the encoder is now
    // injective" would hide that.
    //
    // Why it is still the right write, stated as an argument and not as a reassurance:
    //   * against the attack that actually exists both are ZERO, not 2^120 and 2^116 — each drops
    //     bit 7 of byte 31, so each merges an Ed25519 key with its negation, which the attacker
    //     constructs for free. A birthday bound over an image is not the cost of a STRUCTURED
    //     collision, and this file's own header is where that distinction is made.
    //   * lanes 0..=7 at `B_PUBKEY_OCTET` is EXACTLY the emitted shape minus one column
    //     (`KeyCanonicity9Emit.deployedKeyCols w B_PUBKEY_NINTH_LANE` is those eight plus limb
    //     186), so this write is the final one; the octet would have had to be rewritten again.
    //   * keeping the octet here and the nonet everywhere else would put two encoders for one
    //     object in the tree, which is how the twins drifted in the first place.
    assert!(
        anchor_collision_bits < floor_collision_bits,
        "if this ever passes, the ninth lane landed and this whole test should be re-derived"
    );
    let retired_anchor_collision_bits = 120.0_f64;
    assert!(
        anchor_collision_bits < retired_anchor_collision_bits,
        "the four-bit birthday regression at the anchor is real and is asserted, not glossed"
    );

    // ⚠ SAY WHICH BOUND FOR THE FIX TOO. Nine BabyBear lanes have a CAPACITY of 9 x log2 p =
    // 278.16 bits with a 139.08-bit birthday bound. This file, `faithful8.rs` and the law doc all
    // used to quote that pair as the ninth key lane's IMAGE and COLLISION. It is neither: it is the
    // size of the CODOMAIN. The tell is one comparison —
    let nine_lane_capacity_image = 9.0 * log2_p;
    let nine_lane_capacity_collision = nine_lane_capacity_image / 2.0;
    assert!((nine_lane_capacity_image - 278.163).abs() < 1e-2);
    assert!((nine_lane_capacity_collision - 139.081).abs() < 1e-2);
    assert!(
        nine_lane_capacity_image > 256.0,
        "THE TELL: 2^{nine_lane_capacity_image} exceeds the 2^256 source, so it cannot be the image \
         of any encoding of 32 bytes — it is what nine lanes can HOLD"
    );
    assert!(nine_lane_capacity_collision > floor_collision_bits);

    // THE ENCODING ACTUALLY RECOMMENDED is the base-2^29 nonet (`Dregg2.Circuit.KeyLanes9`'s
    // `keyToLanes9`, injective in Lean by a total decoder and a machine-checked left inverse). Its
    // arithmetic, recomputed from BABYBEAR_P rather than quoted: the radix sits below p so no lane
    // reduces, and eight lanes of 29 bits leave a top lane of 24 — 2^256 on the nose.
    const NONET_RADIX_BITS: u32 = 29;
    assert!(
        f64::from(1u32 << NONET_RADIX_BITS) < f64::from(BABYBEAR_P),
        "the nonet radix must sit below p, else a lane reduces and injectivity dies"
    );
    let top_lane_bits = 256 - 8 * NONET_RADIX_BITS;
    assert_eq!(top_lane_bits, 24, "the top lane's width");
    assert!(
        top_lane_bits > 0 && top_lane_bits <= NONET_RADIX_BITS,
        "nine lanes at this radix must cover 256 bits with the top lane no wider than the radix"
    );
    // And eight cannot, whatever the lanes carry — the same pigeonhole as `floor_image_bits`.
    assert!(
        floor_image_bits < 256.0,
        "if eight lanes ever held 2^256 the ninth would be unnecessary"
    );

    // ⚑ THE HONEST SENTENCE: image EXACTLY 2^256, INJECTIVE, so the encoding step loses nothing and
    // the binding reduces to the sponge. NOT "2^139.08 of collision" — no encoding collision
    // exists at all. `the_nonet_separates_the_pair_the_octet_merges` is the exhibit.
    let nonet_image_bits = f64::from(8 * NONET_RADIX_BITS + top_lane_bits);
    assert_eq!(nonet_image_bits, 256.0);
}

/// **THE DEPLOYED ENCODER, AGAINST AN INDEPENDENTLY-WRITTEN ONE.** A pin of a constant against
/// its own definition is decoration; two independent derivations are a gate. The nested `lane` /
/// `unnonet` below are written bit-at-a-time from the SPEC in
/// `Dregg2.Circuit.KeyLanes9` — "the `i`-th base-`2^29` digit of the little-endian 256-bit
/// number" — and never call the deployed encoder, which builds each lane from a five-byte window
/// and a shift. Two different pieces of arithmetic; equality is the evidence.
///
/// ⚠ **SUBSTRATE, said out loud.** `keyToLanes9_injective` and `keyLanes9ToBytes_keyToLanes9` are
/// **Lean** theorems. There is no formal semantics of Rust and `canonical_to_babybear_nonet` is
/// not extracted from that Lean, so what this test establishes is that a Rust encoder agrees with
/// an independently-written Rust reference and round-trips on the vectors walked. That is a
/// differential, not a proof of injectivity — say it at that resolution.
#[test]
fn the_deployed_nonet_matches_an_independent_reference_and_round_trips() {
    /// Bits `[29i, 29i+29)` of the 32 bytes read as a little-endian 256-bit integer.
    fn lane(b: &[u8; 32], i: usize) -> u32 {
        let mut v = 0u32;
        for k in 0..29usize {
            let bit = 29 * i + k;
            if bit >= 256 {
                break;
            }
            if (b[bit / 8] >> (bit % 8)) & 1 == 1 {
                v |= 1 << k;
            }
        }
        v
    }
    fn reference_nonet(b: &[u8; 32]) -> [u32; 9] {
        std::array::from_fn(|i| lane(b, i))
    }
    fn unnonet(lanes: [u32; 9]) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, l) in lanes.iter().enumerate() {
            for k in 0..29usize {
                let bit = 29 * i + k;
                if bit >= 256 {
                    break;
                }
                if (l >> k) & 1 == 1 {
                    out[bit / 8] |= 1 << (bit % 8);
                }
            }
        }
        out
    }

    // A corpus with structure before bulk: the extremes, every single source bit alone (the only
    // way a lane-boundary error is guaranteed to be seen), and the Ed25519 pair.
    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let mut corpus: Vec<[u8; 32]> = vec![
        [0x00; 32],
        [0xFF; 32],
        base_vector(),
        a.compress().to_bytes(),
        (-a).compress().to_bytes(),
    ];
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut x = [0u8; 32];
            x[byte] = 1u8 << bit;
            corpus.push(x);
        }
    }

    for x in &corpus {
        let deployed = nonet(x);
        assert_eq!(
            deployed,
            reference_nonet(x),
            "the deployed nonet disagrees with the independent reference on {x:02x?}"
        );

        // Every lane is a legal BabyBear value with no reduction, and the top lane is narrower.
        for (i, l) in deployed.iter().enumerate() {
            assert!(*l < 1 << 29, "lane {i} = {l} must be below the radix");
            assert!(
                u64::from(*l) < u64::from(BABYBEAR_P),
                "lane {i} = {l} must not reduce — a reducing lane is not an injection"
            );
        }
        assert!(
            deployed[8] < 1 << 24,
            "the top lane must carry 24 bits, got {}",
            deployed[8]
        );

        // The LEFT INVERSE, which is what makes it injective rather than merely wide.
        assert_eq!(unnonet(deployed), *x, "round-trip failed on {x:02x?}");
    }

    // Injective ON THE CORPUS, stated as a count so a collapsed corpus cannot pass it silently.
    let distinct: std::collections::HashSet<[u32; 9]> = corpus.iter().map(nonet).collect();
    let distinct_inputs: std::collections::HashSet<[u8; 32]> = corpus.iter().copied().collect();
    assert_eq!(
        distinct.len(),
        distinct_inputs.len(),
        "two distinct inputs shared a lane vector"
    );
    assert!(
        distinct.len() > 250,
        "corpus collapsed to {}",
        distinct.len()
    );
}

/// ⚑ **THE EXHIBIT THAT KEEPS THE SECOND RANGE LEG HONEST.** `Dregg2.Circuit.KeyLanes9`'s
/// canonicity envelope is two legs — lanes 0..=7 below `2^29`, and lane 8 below `2^24` — and the
/// second is NOT a consequence of the first. `forgedKeyNonet = [0, …, 0, 2^24]` passes a *uniform*
/// nine-lane `< 2^29` check, has value exactly `2^256`, and the total decoder reads it modulo
/// `2^256` as the ALL-ZERO key. So it is a lane vector outside the encoder's image that decodes to
/// an honest key's decode.
///
/// This is the Rust twin of `keyCanon9_rejects_the_forged_nonet` (an UNSAT over `Satisfied2`) and
/// exists so that anyone tempted to "simplify" `CUSTOM_RANGE_WIDTHS` by dropping 24 and
/// range-checking all nine lanes at 29 finds out here.
#[test]
fn the_forged_nonet_passes_a_uniform_range_check_and_decodes_to_the_zero_key() {
    let forged: [u32; 9] = {
        let mut l = [0u32; 9];
        l[8] = 1 << 24;
        l
    };

    // It passes leg 1 — the naive reading of "range-check the lanes".
    for (i, l) in forged.iter().enumerate() {
        assert!(*l < 1 << 29, "lane {i} escapes a uniform 29-bit lookup");
    }
    // And it fails leg 2, which is the whole reason leg 2 is a separate width.
    assert!(
        forged[8] >= 1 << 24,
        "the exhibit must violate the narrow top-lane leg"
    );

    // It is not in the image: no 32-byte key encodes to it.
    let zero_key = [0u8; 32];
    assert_ne!(
        nonet(&zero_key),
        forged,
        "the forged vector must not be the honest encoding of anything"
    );
    assert_eq!(nonet(&zero_key), [0u32; 9]);

    // ⚑ And it collides with the zero key THROUGH THE DECODER: 2^256 mod 2^256 = 0. That is the
    // sense in which a uniform check would admit a second preimage.
    let decoded = {
        let mut out = [0u8; 32];
        for (i, l) in forged.iter().enumerate() {
            for k in 0..29usize {
                let bit = i * 29 + k;
                if bit < 256 && (l >> k) & 1 == 1 {
                    out[bit / 8] |= 1 << (bit % 8);
                }
            }
        }
        out
    };
    assert_eq!(
        decoded, zero_key,
        "the forged nonet must decode byte-for-byte to the all-zero key"
    );
    assert_eq!(
        8 * 29 + 24,
        256,
        "and the reason is exactly that the top lane starts at source bit 232"
    );
}

/// **THE FLAG DAY, EXPRESSED AS A TEST.** This file's namesake used to be
/// `an_ed25519_key_and_its_negation_pack_to_one_octet` and it asserted the *collision*. The
/// deployed encoder is now the base-`2^29` nonet, so the pair it merged is SEPARATED, and the old
/// assertion is exhibited here as **false** rather than deleted — a reader six weeks out needs the
/// flag day findable, not absent.
///
/// ⚠ Read the second half. Separation at the ENCODER is not separation at the ANCHOR: the
/// rotated pre-limb write still takes only the low eight lanes, and on this specific pair that is
/// exactly the half that does not separate. This test asserts both, so neither can be quoted
/// without the other.
#[test]
fn an_ed25519_key_and_its_negation_no_longer_pack_to_one_lane_vector() {
    // A real curve point, and its negation. RFC 8032 5.1.2: the encoding is y little-endian with
    // the x-sign in the most significant bit of the final octet. Negation flips exactly that bit.
    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let minus_a = -a;

    let key_a: [u8; 32] = a.compress().to_bytes();
    let key_minus_a: [u8; 32] = minus_a.compress().to_bytes();

    // They are DIFFERENT public keys — and different in exactly one bit, the sign bit the old
    // 8+8+8+6 pack discarded. The attacker holds the private half of the negation (`-a mod L`),
    // so this pair cost zero to construct then and costs zero to construct now.
    assert_ne!(key_a, key_minus_a);
    let mut diff_bits = Vec::new();
    for byte in 0..32usize {
        let x = key_a[byte] ^ key_minus_a[byte];
        for bit in 0..8u8 {
            if x & (1 << bit) != 0 {
                diff_bits.push((byte, bit));
            }
        }
    }
    assert_eq!(
        diff_bits,
        vec![(31usize, 7u8)],
        "the two encodings must differ in exactly the x-sign bit"
    );
    assert!(
        CLAIMED_UNREAD.contains(&(31, 7)),
        "and that bit is the one the RETIRED octet never read"
    );

    // Both are valid, decompressible Edwards points of the same order — not malformed strings.
    assert!(
        curve25519_dalek::edwards::CompressedEdwardsY(key_a)
            .decompress()
            .is_some()
    );
    assert!(
        curve25519_dalek::edwards::CompressedEdwardsY(key_minus_a)
            .decompress()
            .is_some()
    );

    // ⚑ THE ASSERTION THAT FLIPPED. This was `assert_eq!` and it PASSED. The deployed encoder
    // now SEPARATES the pair, in the lane the old scheme had no room for.
    let na = nonet(&key_a);
    let nma = nonet(&key_minus_a);
    assert_ne!(
        na, nma,
        "THE FLAG DAY REGRESSED: the deployed encoder merged an Ed25519 key with its negation \
         again. Whatever re-introduced an 8-lane pack, revert it — p^8 < 2^256, so no member of \
         that family can separate this pair."
    );

    // And it separates in EXACTLY ONE PLACE, and that place is the ninth lane. Bit 7 of byte 31
    // is source bit 255, which is bit 23 of lane 8 (255 - 8*29 = 23) — the only lane the old
    // eight-lane geometry did not have.
    let differing: Vec<usize> = (0..9).filter(|i| na[*i] != nma[*i]).collect();
    assert_eq!(
        differing,
        vec![8],
        "the pair must separate in lane 8 and nowhere else"
    );
    assert_eq!(
        na[8] ^ nma[8],
        1 << 23,
        "and the separating bit must be bit 23 of the top lane, i.e. source bit 255"
    );

    // The old claim, exhibited as FALSE. `retired_octet_pack` is the deleted encoder, kept in
    // this file ONLY as the thing being refuted — it has no call site in the tree.
    assert_eq!(
        retired_octet_pack(&key_a),
        retired_octet_pack(&key_minus_a),
        "the RETIRED octet must still merge them — this is the claim being refuted, and if it \
         ever stops holding, the refutation has become vacuous and this test proves nothing"
    );

    // ⚠ THE HALF THAT IS NOT CLOSED, asserted so it cannot be quietly forgotten. The rotated
    // pre-limb write takes lanes 0..=7, and lane 8 is where this pair separates. So the ANCHOR
    // still does not distinguish the cell owned by A from the cell owned by -A. That is the
    // geometry residual named by `KEY_NONET_NINTH_LANE_UNBOUND`, and
    // `key_nonet_ninth_lane_reaches_the_anchor.rs` is the gate that flips when it closes.
    assert_eq!(
        Faithful8::from_key_nonet_low8(na.map(BabyBear::new)).limbs(),
        Faithful8::from_key_nonet_low8(nma.map(BabyBear::new)).limbs(),
        "if the low-eight write started separating this pair, the ninth lane landed — retire \
         KEY_NONET_NINTH_LANE_UNBOUND and delete this assertion rather than relaxing it"
    );
}

/// The **deleted** `8+8+8+6 = 30` bits/limb pack, retained in this test file and nowhere else, as
/// the object the assertions above refute. It has no production call site; the burn-down gate
/// below walks every `*.rs` in the tree and would see one.
fn retired_octet_pack(canonical: &[u8; 32]) -> [u32; 8] {
    std::array::from_fn(|i| {
        let lo = canonical[i * 4] as u32;
        let mid1 = canonical[i * 4 + 1] as u32;
        let mid2 = canonical[i * 4 + 2] as u32;
        let hi = canonical[i * 4 + 3] as u32;
        lo | (mid1 << 8) | (mid2 << 16) | ((hi & 0x3F) << 24)
    })
}

// ---------------------------------------------------------------------------------------------
// THE BURN-DOWN LIST, AS A GATE — KEYED ON THE ADMISSION, NOT ON THE FILE
// ---------------------------------------------------------------------------------------------
//
// ⚑ **The wound this rewrite closes, measured 2026-08-01.** The first version of this gate pushed
// a FILE PATH once per file (`hit = true; break;` on the first match). It caught a new file with a
// hatch call — and it was BLIND exactly where the next degraded octet gets added, because the three
// listed files are the two deployed producers and the wall itself. A second, DISTINCT residual
// declared inside `circuit/src/faithful8.rs` and admitted through a new router passed 5/5. A gate
// whose stated purpose is "a documented wound is not a detected one" could not see the wound it
// guards.
//
// The key is now the pair `(file, reason-constant)`. `(file, line)` would have been the obvious
// alternative and it is worse: it goes red on every reflow, so it would be relaxed within a week.
// The reason constant survives a reformat and names the thing being admitted.

/// The needles are assembled with `concat!` so this file does not itself contain the literals it
/// searches for — the walk below covers every `*.rs` in the workspace, including this one, and a
/// path exclusion would be a place to hide a call site.
const HATCH: &str = concat!("from_lossy_", "31bit_DANGER");

/// The hatch's own source file. Two things are read out of it and NEITHER is transcribed here: the
/// set of ROUTERS (constructors whose body calls the hatch, so that calling one is an admission
/// even though the call site never names the hatch), and the `&str` REASON CONSTANTS with their
/// values. `from_canonical_key` is a router because its body is
/// `Self::from_lossy_31bit_DANGER(KEY_COMMIT_30BIT_RESIDUAL, limbs)` — measured, so a second
/// constructor that does the same becomes a router the moment it is written.
const HATCH_SRC: &str = "circuit/src/faithful8.rs";

const LIST_BEGIN: &str = "<!-- BURN-DOWN-LIST-BEGIN -->";
const LIST_END: &str = "<!-- BURN-DOWN-LIST-END -->";

/// One admission: the file that makes it, and the reason constant it is made under.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Admission {
    file: String,
    reason: String,
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit/ has a parent")
        .to_path_buf()
}

fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
    let skip = ["target", ".git", "node_modules", ".lake", "lake-packages"];
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if !skip.contains(&name.as_ref()) {
                collect_rs(&path, out);
            }
        } else if name.ends_with(".rs") {
            out.push(path);
        }
    }
}

fn hatch_source() -> String {
    std::fs::read_to_string(repo_root().join(HATCH_SRC))
        .expect("the hatch's own source is readable")
}

/// The first argument of the call whose `(` sits at byte `open`, as written. Depth- and
/// string-aware, and it spans lines, so a rustfmt-wrapped call still yields its reason.
fn first_arg(text: &str, open: usize) -> String {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut escaped = false;
    let mut out = String::new();
    for c in text[open + 1..].chars() {
        if in_str {
            out.push(c);
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        match c {
            '"' => {
                in_str = true;
                out.push(c);
            }
            '(' | '[' | '{' => {
                depth += 1;
                out.push(c);
            }
            ')' | ']' | '}' => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                out.push(c);
            }
            ',' if depth == 0 => break,
            _ => out.push(c),
        }
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The declared name of the `fn` a line opens, if it opens one (`fn f(`, `pub fn f(`,
/// `pub(crate) const fn f(` all qualify).
fn declared_fn(line: &str) -> Option<String> {
    let at = line.find("fn ")?;
    let rest = &line[at + 3..];
    let end = rest.find('(')?;
    let name = rest[..end].trim();
    if name.is_empty() || !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return None;
    }
    Some(name.to_string())
}

/// Is the needle occurrence at `at` a DEFINITION rather than a call? Precise where the old
/// `contains("fn from_")` filter was a heuristic: the text immediately before the name is `fn`.
fn is_definition(line: &str, at: usize) -> bool {
    line[..at].trim_end().ends_with("fn")
}

/// Occurrences of `name(` on a non-comment line, as `(byte-offset-of-the-paren)`.
fn call_parens(text: &str, line: &str, line_start: usize, name: &str) -> Vec<usize> {
    let needle = format!("{name}(");
    let mut out = Vec::new();
    let mut from = 0usize;
    while let Some(rel) = line[from..].find(&needle) {
        let at = from + rel;
        from = at + needle.len();
        if !is_definition(line, at) {
            out.push(line_start + at + name.len());
        }
    }
    let _ = text;
    out
}

/// The ROUTERS: constructors in the hatch's own file whose body calls the hatch, mapped to the
/// reason they pass. DERIVED, not transcribed — `from_canonical_key` is here because its body
/// reads `Self::from_lossy_31bit_DANGER(KEY_COMMIT_30BIT_RESIDUAL, limbs)`, and a second such
/// constructor becomes a router the moment somebody writes one.
fn routers(src: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    let mut offset = 0usize;
    for line in src.split_inclusive('\n') {
        let start = offset;
        offset += line.len();
        let t = line.trim_start();
        if t.starts_with("//") {
            continue;
        }
        if let Some(name) = declared_fn(line) {
            current = Some(name);
        }
        for paren in call_parens(src, line, start, HATCH) {
            let Some(owner) = current.clone() else {
                continue;
            };
            if owner == HATCH {
                continue;
            }
            out.insert(owner, first_arg(src, paren));
        }
    }
    out
}

/// A minimal Rust `&str` literal reader — `\\`, `\"`, `\n`, `\t`, `\r`, and the LINE CONTINUATION
/// (`\` before a newline swallows the newline and the next line's indent), which is how
/// `KEY_COMMIT_30BIT_RESIDUAL` is written. `None` on anything it does not understand, and an
/// unresolvable reason FAILS the gate rather than being quietly skipped.
fn read_str_literal(text: &str) -> Option<String> {
    let mut chars = text.chars();
    if chars.next()? != '"' {
        return None;
    }
    let mut out = String::new();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                '\\' => out.push('\\'),
                '"' => out.push('"'),
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                '\n' => {
                    let mut peek = chars.clone();
                    while let Some(w) = peek.next() {
                        if w.is_whitespace() {
                            chars = peek.clone();
                        } else {
                            break;
                        }
                    }
                }
                _ => return None,
            },
            _ => out.push(c),
        }
    }
    None
}

/// The `&str` reason constants declared beside the hatch, by name, with their values — PARSED from
/// the source rather than linked, so a residual whose constant is not `pub` (or that this test
/// never imported) is still resolvable and still gated.
fn reason_constants(src: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut rest = src;
    while let Some(at) = rest.find("const ") {
        let after = &rest[at + "const ".len()..];
        rest = after;
        let Some(colon) = after.find(':') else {
            continue;
        };
        let name = after[..colon].trim();
        if name.is_empty()
            || !name
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        {
            continue;
        }
        let Some(tail) = after[colon + 1..].trim_start().strip_prefix("&str") else {
            continue;
        };
        let Some(tail) = tail.trim_start().strip_prefix('=') else {
            continue;
        };
        let Some(value) = read_str_literal(tail.trim_start()) else {
            continue;
        };
        out.insert(name.to_string(), value);
    }
    out
}

/// Every admission in the tree, as `(file, reason)` pairs. A call to the hatch contributes the
/// reason it passes; a call to a ROUTER contributes the reason that router's body passes.
///
/// ⚠ **`tests/` directories are scoped out, and the law is what scopes them.** "Non-commitment
/// uses of the fold are out of scope and sound: … and tests." A test that CALLS the residual is
/// exercising it, not admitting it into a commitment. The exclusion is by directory rather than
/// by heuristic so it cannot be argued with — and it is safe in the one direction that matters,
/// because production code does not live in a `tests/` directory, while a `#[cfg(test)] mod` in a
/// `src/` file IS still scanned. First run of this gate went red on a sibling lane's
/// `commit/tests/key_octet_f2_twins_and_the_hole.rs`, which is how the scope question surfaced.
fn burn_down_admissions(routers: &BTreeMap<String, String>) -> BTreeSet<Admission> {
    let root = repo_root();
    let mut files = Vec::new();
    collect_rs(&root, &mut files);
    files.sort();

    let mut out = BTreeSet::new();
    for file in files {
        if file.components().any(|c| c.as_os_str() == "tests") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&file) else {
            continue;
        };
        let rel = file
            .strip_prefix(&root)
            .expect("under the repo root")
            .to_string_lossy()
            .replace('\\', "/");

        let mut offset = 0usize;
        for line in text.split_inclusive('\n') {
            let start = offset;
            offset += line.len();
            if line.trim_start().starts_with("//") {
                continue;
            }
            for paren in call_parens(&text, line, start, HATCH) {
                out.insert(Admission {
                    file: rel.clone(),
                    reason: first_arg(&text, paren),
                });
            }
            for (router, reason) in routers {
                if call_parens(&text, line, start, router).is_empty() {
                    continue;
                }
                out.insert(Admission {
                    file: rel.clone(),
                    reason: reason.clone(),
                });
            }
        }
    }
    out
}

fn law_doc() -> String {
    std::fs::read_to_string(repo_root().join("docs/FAITHFUL-COMMITMENT-LAW.md"))
        .expect("the law doc is readable")
}

fn burn_down_section(doc: &str) -> String {
    let begin = doc.find(LIST_BEGIN).expect(
        "the law doc must carry a machine-readable burn-down section — the marker is missing",
    );
    let end = doc
        .find(LIST_END)
        .expect("the burn-down section must be closed");
    assert!(begin < end, "burn-down markers are out of order");
    doc[begin..end].to_string()
}

/// The listed admissions: an entry reads ``- `<path>` — `<REASON_CONST>` — prose``, and the first
/// two code spans on the line are the key. Continuation lines carry no `- ` and are ignored.
fn listed_admissions(section: &str) -> BTreeSet<Admission> {
    let mut out = BTreeSet::new();
    for line in section.lines() {
        let t = line.trim_start();
        if !t.starts_with("- `") {
            continue;
        }
        let spans: Vec<&str> = t.split('`').skip(1).step_by(2).collect();
        assert!(
            spans.len() >= 2,
            "a burn-down entry must read: - `<path>` — `<REASON_CONST>` — why. Got: {t}"
        );
        assert!(
            spans[1]
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_'),
            "the SECOND code span of a burn-down entry is the reason constant, not prose. Got \
             `{}` on: {t}",
            spans[1]
        );
        out.insert(Admission {
            file: spans[0].to_string(),
            reason: spans[1].to_string(),
        });
    }
    out
}

#[test]
fn the_burn_down_list_names_every_hatch_admission() {
    let src = hatch_source();
    let routers = routers(&src);

    // ANTI-VACUITY on the DERIVATION, before anything is compared. If the router scan came back
    // empty, both deployed producers would silently vanish from the measured set — a green gate
    // over an unwatched tree, which is the failure this whole file exists to make impossible.
    assert!(
        !routers.is_empty(),
        "no hatch router derived from {HATCH_SRC} — the scan is broken, not the tree"
    );
    // ⚑ RENAMED 2026-08-01 with the encoder. Was `from_canonical_key`, whose body packed the
    // 30-bit octet; it is now `from_key_nonet_low8`, which PROJECTS the injective nonet and whose
    // residual is the missing ninth COLUMN rather than a lossy encoding. The two deployed
    // producers still reach the hatch through it, so losing it still blinds the walk.
    let key_router = concat!("from_key_nonet", "_low8");
    assert!(
        routers.contains_key(key_router),
        "the deployed key-lane router is not among the derived routers {:?} — the two producers \
         reach the hatch THROUGH it, so losing it blinds the walk",
        routers.keys().collect::<Vec<_>>()
    );

    let measured = burn_down_admissions(&routers);

    // The list is NOT empty. It was recorded as "EMPTY (v13 DONE)" while the key octet rode in
    // through the front door; an empty list is a claim, and this is the instrument for it.
    assert!(
        !measured.is_empty(),
        "no burn-down admissions found at all — the walk is broken, not the tree"
    );

    let doc = law_doc();
    let section = burn_down_section(&doc);
    let listed = listed_admissions(&section);

    let unlisted: Vec<_> = measured.difference(&listed).collect();
    assert!(
        unlisted.is_empty(),
        "burn-down admissions missing from docs/FAITHFUL-COMMITMENT-LAW.md: {unlisted:#?}\n\
         The key is (file, reason), so a SECOND residual inside a file already on the list is a \
         new entry and must be written down. Adding a degraded-octet admission without listing it \
         is a review-time violation, and this is the test that makes it a red one."
    );

    let stale: Vec<_> = listed.difference(&measured).collect();
    assert!(
        stale.is_empty(),
        "the law doc lists burn-down admissions that no longer exist: {stale:#?}\n\
         A closed residual must leave the list, or the list stops meaning anything."
    );

    // ⚑ AND THE REASON ITSELF MUST BE IN THE DOC, VERBATIM. Keying on the constant NAME is only
    // half of it: the name is a label, and the doc has to carry what it labels. This is generic
    // over the residuals, which is what the previous version was not — it asserted three
    // hand-picked needles, so a second residual's reason went unchecked entirely.
    let consts = reason_constants(&src);
    for admission in &measured {
        let value = consts.get(&admission.reason).unwrap_or_else(|| {
            panic!(
                "the reason `{}` admitted in {} is not a `&str` constant declared beside the hatch \
                 in {HATCH_SRC}. Declare it there: the burn-down grep and the law doc need one \
                 source, and an inline literal gives them two.",
                admission.reason, admission.file
            )
        });
        assert!(
            value.trim().len() > 20,
            "the reason `{}` is too thin to be a residual's justification: {value:?}",
            admission.reason
        );
        assert!(
            section.contains(value.as_str()),
            "the burn-down section of docs/FAITHFUL-COMMITMENT-LAW.md does not quote the reason \
             `{}` VERBATIM. The doc and the constant must not drift.\n  wanted: {value}",
            admission.reason
        );
    }
}

#[test]
fn the_law_doc_quotes_the_bound_it_means() {
    let doc = law_doc();

    // The house error this document names is quoting an IMAGE size where a COLLISION bound is
    // meant. All three of the key octet's numbers must appear, so a reader cannot pick up the
    // flattering one by accident. ⚑ The needles are DERIVED from `BABYBEAR_P` and from this file's
    // own measurement of the deployed packer, not transcribed — a pin against a transcription is
    // decoration.
    // ⚑ The measured quantity is now the ANCHOR RESIDUAL, not the retired encoder: the low-eight
    // write's read-set. That is the number a reader of this doc must be able to find, because it
    // is the one that is still true.
    let log2_p = f64::from(BABYBEAR_P).log2();
    let base = base_vector();
    let reference = faithful_low8(&base).limbs();
    let mut unread = 0u32;
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if faithful_low8(&flipped).limbs() == reference {
                unread += 1;
            }
        }
    }
    let image_bits = 256 - unread;
    assert_eq!(image_bits, 232, "the anchor residual's measured image");
    for needle in [
        format!("2^{}", 8 * 30), // the RETIRED octet's IMAGE, 2^240 — kept on record
        format!("{:.2}", 8.0 * log2_p / 2.0), // the FLOOR, 123.63
        "2^256".to_string(),     // the NONET's image — the thing that changed
    ] {
        assert!(
            doc.contains(&needle),
            "the law doc must state {needle} for the key octet"
        );
    }

    // ⚠ AND IT MUST NOT QUOTE THE FLATTERING NUMBER OF THE FIX. `2^278.16` / `2^139.08` are the
    // CAPACITY of nine BabyBear lanes; they were written into this document, into `faithful8.rs`
    // and into this file's own header as the ninth key lane's IMAGE and COLLISION — inside the
    // section that forbids exactly that substitution.
    //
    // ⚑ A NEGATIVE textual check is the wrong instrument here and the first draft of this test
    // used one: `!doc.contains("2^278.16 image")` passed only because markdown puts a backtick
    // between the two words, so it could not have gone red for the regression it named — and it
    // would also fight the corrective prose, which has to QUOTE the wrong sentence to record it.
    // The gate is instead POSITIVE and ANCHORED: the paragraph that prices the ninth key lane must
    // carry what the encoding actually is.
    assert!(
        9.0 * log2_p > 256.0,
        "the tell, restated from BABYBEAR_P: nine lanes hold more than the 2^256 source, so \
         2^{:.2} is a CAPACITY and cannot be any encoding's image",
        9.0 * log2_p
    );

    const ANCHOR: &str = "What closes it: a NINTH key lane";
    let at = doc
        .find(ANCHOR)
        .expect("the law doc must price the ninth key lane under a findable heading");
    let window: String = doc[at..].chars().take(1000).collect();
    for needle in [
        "2^256",                 // the nonet's image, exactly
        "INJECTIVE",             // what it is, and the reason there is no collision term
        "keyToLanes9_injective", // the Lean theorem, nameable
        "CAPACITY",              // and the 2^278.16 pair labelled for what it is
    ] {
        assert!(
            window.contains(needle),
            "the law doc's ninth-key-lane paragraph must say {needle}. The honest sentence is: \
             image exactly 2^256, INJECTIVE, so the encoding step loses nothing and the binding \
             reduces to the sponge — NOT a 2^{:.2} image with a 2^{:.2} birthday bound, which is \
             the nine-lane CAPACITY.\n--- paragraph as found ---\n{window}",
            9.0 * log2_p,
            9.0 * log2_p / 2.0
        );
    }

    // The same correction, at the constructor that carries the residual — the site a reader hits
    // first is the doc comment, not this document.
    let src = hatch_source();
    for needle in ["keyToLanes9_injective", "image exactly `2^256`", "CAPACITY"] {
        assert!(
            src.contains(needle),
            "{HATCH_SRC} must say {needle} where it prices the ninth key lane"
        );
    }

    // And the residual's reason string must name what is actually left and how it closes, so the
    // grep is readable without opening the doc. ⚑ It must ALSO not still be selling the old
    // wound: an encoder that is now injective, described by a constant that says it drops sixteen
    // bits, is a stale label on a live gate.
    assert!(
        KEY_NONET_NINTH_LANE_UNBOUND.contains("NUM_PRE_LIMBS = 187"),
        "the residual must name the geometry that closes it"
    );
    assert!(
        KEY_NONET_NINTH_LANE_UNBOUND.contains(&format!("{image_bits} of 256")),
        "the residual must state its MEASURED width, {image_bits}, not a remembered one"
    );
    assert!(
        KEY_NONET_NINTH_LANE_UNBOUND.contains("the encoder is injective"),
        "the residual must say which half closed, or a reader re-fixes the encoder"
    );
    assert!(
        !KEY_NONET_NINTH_LANE_UNBOUND.contains("16 source bits unread"),
        "the residual is still describing the RETIRED encoder's wound"
    );
}
