//! **The KEY_COMMIT encoder was below the faithful-commitment law's own floor. It was REPLACED
//! on 2026-08-01 and its ninth lane reached the signed anchor on 2026-08-02; this file is the
//! record of both halves, and of the two retired shapes it refutes.**
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
//!   read-set walk: 256/0 for the nonet AND for the anchor write, 240/16 for the retired octet,
//!   232/24 for the retired low-eight write, all measured side by side by one walk.
//! * `the_deployed_nonet_matches_an_independent_reference_and_round_trips` pins the deployed
//!   encoder against a differently-written reference and round-trips it. A differential, not a
//!   proof — there is no formal semantics of Rust and this encoder is not extracted from the Lean.
//! * `the_forged_nonet_passes_a_uniform_range_check_and_decodes_to_the_zero_key` keeps the
//!   envelope's SECOND range leg honest: `[0, …, 0, 2^24]` clears a uniform 29-bit check and
//!   decodes to the all-zero key, so widening 24 to 29 "for uniformity" re-opens the encoding.
//!
//! ## ⚑ THE HALF THAT DID NOT CLOSE UNTIL 2026-08-02 — and what closing it did NOT buy
//!
//! This section read: *"The encoder is injective. The ANCHOR WRITE is not."* `B_PUBKEY_OCTET` is
//! eight columns wide, so both producers committed lanes 0..=7 and DROPPED lane 8 — and bit 7 of
//! byte 31 is source bit 255, which lives in lane 8. The signed consensus anchor therefore did not
//! distinguish the cell owned by `A` from the cell owned by `-A`: **232 of 256 bits, a `2^116`
//! birthday, four bits WORSE than the retired octet's `2^120`, and `0` against the structured
//! attack in both cases.**
//!
//! It is closed. The emitted geometry is `NUM_PRE_LIMBS = 187` with `B_PUBKEY_NINTH_LANE = 186` —
//! an ABSORBED pre-limb, so `wireCommitR` folds `[0, 187)` over it — and both producers write all
//! nine lanes through `Faithful9::from_key_lanes9` over `PUBKEY_NONET_LANE_COL`. The measurement
//! is `the_anchor_write_binds_the_whole_key_and_the_retired_packs_did_not`, which walks the real
//! COLUMN MAP rather than the encoder, and `an_ed25519_key_and_its_negation_no_longer_pack_to_one_lane_vector`
//! now exhibits the pair merging under BOTH retired shapes and separating at the committed
//! columns, then round-trips the 32 bytes back out of the nine lanes.
//!
//! ## ⚠ WHAT THIS DOES NOT BUY — three of them, and none is bookkeeping
//!
//! 1. **The canonicity ENVELOPE is still not emitted.** `Emit.KeyCanonicity9Emit.keyCanonical9At`
//!    — eight range lookups at 29 bits plus one at 24 — is authored, proved
//!    (`keyCanon9_determines_the_owner_key_deployed`, `keyCanon9_rejects_the_forged_nonet`) and
//!    **applied by nothing**. So the anchor now BINDS all 256 key bits, and no emitted constraint
//!    REFUSES a lane vector outside the encoder's image. `the_forged_nonet_...` below is the Rust
//!    twin of what that envelope would reject, and it is a TEST, not a constraint.
//! 2. **The `KEY_COMMIT` teeth are a separate surface.** `trace_rotated.rs`'s
//!    `pubkey_to_witness_key_commit` folds the eight octet limbs at `B_PUBKEY_OCTET` and does not
//!    read limb 186. This flag day moved `state_commit`; it did not move those teeth.
//!    ⚠ Do not read "the anchor binds 256 bits" as "every pubkey-derived value does".
//!    ⚑ What DOES cover the ninth lane at the constraint level is `OwnerFreezeWire`, which is
//!    emitted and welds limb 186 BEFORE↔AFTER (the E10 free-felt hole on that lane).
//! 3. **`child_vk` and `contract_hash` still ride `Faithful8::from_bytes32`.** The 187-limb grow
//!    bought THREE ninth lanes (184, 185, 186) and this lane used one. `B_CHILD_VK_NINTH_LANE` and
//!    `B_CONTRACT_HASH_NINTH_LANE` are emitted columns that no producer writes, and `from_bytes32`
//!    is `O(1)`-aliasable for a chosen 32-byte input — which a factory child VK is.
//!
//! * `the_burn_down_list_names_every_hatch_admission` turns the law's "adding a `_DANGER` site
//!   without listing it here is a review-time violation" into something that can go red. ⚑ It is
//!   keyed on the `(file, reason-constant)` ADMISSION, not on the file path — see the section
//!   header below for the wound that keying cost. It names NO residual today: the owner-key octet
//!   was the last one, so the gate's anti-vacuity moved onto a SYNTHETIC probe rather than relying
//!   on the tree still being wounded.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;
use dregg_cell::commitment::canonical_to_babybear_nonet;
use dregg_circuit::Faithful9;
use dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL;
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

/// **WHAT THE ROTATED PRE-LIMB WRITE ACTUALLY COMMITS**, reconstructed the way the two producers
/// do it: `Faithful9::from_key_lanes9` scattered over `PUBKEY_NONET_LANE_COL`, then read back out
/// of the limb vector by column. This is deliberately not `nonet(b)` — it goes through the COLUMN
/// MAP, so a lane written to the wrong column, or dropped, shows up here as a zero.
///
/// ⚑ Until 2026-08-02 this function was `faithful_low8` and returned a `Faithful8` of lanes 0..=7,
/// because `B_PUBKEY_OCTET` was eight columns wide and lane 8 had nowhere to go. "The gap between
/// this and `nonet` is the whole of what is left open" was its doc, and the gap was 24 bits
/// including the Ed25519 sign bit. The gap is now zero and this function is how that is measured.
fn anchor_lanes(b: &[u8; 32]) -> [u32; 9] {
    let mut pre = vec![BabyBear::ZERO; dregg_circuit::effect_vm::layout_generated::NUM_PRE_LIMBS];
    Faithful9::from_key_lanes9(b).write_lanes(&mut pre, PUBKEY_NONET_LANE_COL);
    std::array::from_fn(|i| pre[PUBKEY_NONET_LANE_COL[i]].as_u32())
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

    // ⚑ AND THE WALL, WHICH IS THE HALF THAT CLOSED ON 2026-08-02. This block used to assert
    // 232/24 — the low-eight write was blind to source bits 232..255 (bytes 29, 30, 31, the
    // Ed25519 sign bit among them) — and it was the measurement behind the retired reason constant
    // `KEY_NONET_NINTH_LANE_UNBOUND`. The walk is IDENTICAL; only the expected counts moved, which
    // is what makes this a flipped gate rather than a rewritten one.
    //
    // ⚠ It walks `anchor_lanes`, i.e. through `PUBKEY_NONET_LANE_COL`, NOT through the encoder.
    // That distinction is the whole point: the encoder was already injective on 2026-08-01 and the
    // anchor still bound 232 bits, because the ninth lane was written nowhere.
    let (wall_read, wall_unread) = walk(&|b| anchor_lanes(b).to_vec());
    assert_eq!(
        wall_read.len(),
        256,
        "the anchor write must bind every source bit — if this is 232 again, a producer or the \
         column map lost lane 8; do not relax it"
    );
    assert!(
        wall_unread.is_empty(),
        "the anchor write must read every source bit, got unread {wall_unread:?}"
    );

    // ⚑ ANTI-VACUITY ON THE COLUMN MAP ITSELF. A read-set walk cannot tell "lane 8 landed on its
    // column" from "lane 8 landed on some other column that this walk also reads", so pin the
    // ninth column against the emitted layout — a second, independent source.
    assert_eq!(
        PUBKEY_NONET_LANE_COL[8],
        dregg_circuit::effect_vm::layout_generated::B_PUBKEY_NINTH_LANE,
        "lane 8 must land on the layout's own ninth-lane column"
    );
    assert!(
        PUBKEY_NONET_LANE_COL[8] < dregg_circuit::effect_vm::layout_generated::NUM_PRE_LIMBS,
        "…and that column must be an ABSORBED pre-limb, or wireCommitR never folds it"
    );
}

/// ⚑ **INVERTED AND RENAMED 2026-08-02.** This was `key_octet_collision_is_below_the_law_floor`
/// and it MEASURED the residual: the anchor bound 232 bits, a `2^116` birthday, 7.63 bits below
/// the law's `2^123.63` floor and four bits WORSE than the retired octet's `2^120`. The ninth lane
/// now lands on in-block limb 186 and the anchor binds all 256, so the comparison it made no
/// longer has a subject. The floor derivation is kept verbatim — it is still the law's number and
/// the other octets are still measured against it — and the anchor leg is re-derived.
///
/// ⚠ **AND THE FLOOR IS THE WRONG INSTRUMENT FOR THIS OBJECT, which is why the conclusion below
/// does not read "clears the floor".** `2^123.63` is a BIRTHDAY COLLISION bound over an 8-lane
/// image; a KEY needs INJECTIVITY, and an injective encoding has no collision bound to compare —
/// it has none. Quoting "the anchor now clears the ~124-bit floor" would be this tree's oldest
/// mistake (the flattering number of a pair) wearing a green test.
#[test]
fn the_anchor_write_binds_the_whole_key_and_the_retired_packs_did_not() {
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

    // Source B: what the ANCHOR binds, derived from the MEASURED read-set of the real column
    // write rather than from any doc.
    let base = base_vector();
    let reference = anchor_lanes(&base);
    let mut unread = 0u32;
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if anchor_lanes(&flipped) == reference {
                unread += 1;
            }
        }
    }
    assert_eq!(unread, 0, "the anchor write must read every source bit");
    let anchor_bits = f64::from(256 - unread);
    assert_eq!(anchor_bits, 256.0, "measured anchor read-set");

    // And the two RETIRED packs, measured by the SAME walk, so the thing that changed stays on
    // the record as a number rather than as an adjective.
    let mut retired_unread = 0u32;
    let retired_ref = retired_octet_pack(&base);
    let mut low8_unread = 0u32;
    let low8_ref: [u32; 8] = std::array::from_fn(|i| nonet(&base)[i]);
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if retired_octet_pack(&flipped) == retired_ref {
                retired_unread += 1;
            }
            let l: [u32; 8] = std::array::from_fn(|i| nonet(&flipped)[i]);
            if l == low8_ref {
                low8_unread += 1;
            }
        }
    }
    assert_eq!(
        retired_unread, 16,
        "the 30-bit octet bound 240 of 256 (birthday 2^120)"
    );
    assert_eq!(
        low8_unread, 24,
        "the low-eight nonet write bound 232 of 256 (birthday 2^116)"
    );

    // ⚑ SAY IT PLAINLY, AND SAY WHICH BOUND. Both retired packs had a birthday figure ABOVE the
    // one that mattered — 2^120 and 2^116 — and against the attack that actually existed both were
    // ZERO: each dropped bit 7 of byte 31, so each merged an Ed25519 key with its negation, which
    // the attacker constructs for free. That is why "240 bits" and "232 bits" were never the
    // interesting numbers, and why the fix was not a wider fold.
    //
    // The claim for the CURRENT write is a different KIND of claim, and the assertion says so:
    // the read-set is the whole source (256/256), and the nine lanes are an INJECTION with a total
    // decoder, so there is no collision bound to compare against `floor_collision_bits` at all.
    // The floor stays derived above because the OTHER octets in this tree are still measured
    // against it.
    assert!(
        anchor_bits > floor_image_bits,
        "the anchor read-set ({anchor_bits}) must exceed what any 8-lane image can carry \
         ({floor_image_bits}) — that inequality IS the pigeonhole argument, measured"
    );
    assert!(
        f64::from(256 - retired_unread) / 2.0 < floor_collision_bits
            && f64::from(256 - low8_unread) / 2.0 < floor_collision_bits,
        "both RETIRED packs must still measure below the law floor — this is the refutation, and \
         if it stops holding the flag day has become unfalsifiable"
    );
    // ⚑ AND THE FOUR-BIT REGRESSION THAT USED TO BE ASSERTED HERE, kept as an ORDERING between
    // the two retired shapes rather than deleted: the low-eight nonet write bound FEWER bits at
    // the anchor (232, birthday 2^116) than the 30-bit octet it replaced (240, birthday 2^120).
    // Quoting only "the encoder became injective" hid that for a day, which is why the comparison
    // stays in the suite even though neither shape is deployed.
    assert!(
        f64::from(256 - low8_unread) < f64::from(256 - retired_unread),
        "the retired low-eight write bound FEWER source bits at the anchor than the octet it \
         replaced — that regression is part of the record, not a rounding error"
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
/// ⚑ **AND THE SECOND HALF CLOSED 2026-08-02.** This doc used to warn that separation at the
/// ENCODER is not separation at the ANCHOR — the rotated pre-limb write took only the low eight
/// lanes, and on this specific pair that was exactly the half that did not separate. The ninth
/// lane now has in-block limb 186 and both producers write it, so the test asserts the pair
/// separating at BOTH, and exhibits both retired shapes still merging it.
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

    // ⚑ **OLD ADMITS.** Both retired shapes merge the pair, exhibited side by side so the flag
    // day has a subject. Neither cost a search: `-A` is the negation of a point whose private half
    // the attacker holds.
    //
    //   * the 30-bit octet (`canonical_32_to_felts_8`, retired 2026-08-01) — 16 unread source bits;
    //   * the LOW-EIGHT NONET WRITE (retired 2026-08-02) — the encoder was injective and the
    //     WRITE threw lane 8 away, so the merge survived the encoder flag day untouched. That is
    //     the one this file's header used to call "the half that did not close".
    let low8 = |l: [u32; 9]| -> [u32; 8] { std::array::from_fn(|i| l[i]) };
    assert_eq!(
        retired_octet_pack(&key_a),
        retired_octet_pack(&key_minus_a),
        "the RETIRED octet must still merge them — this is the claim being refuted, and if it \
         ever stops holding, the refutation has become vacuous and this test proves nothing"
    );
    assert_eq!(
        low8(na),
        low8(nma),
        "the RETIRED low-eight write must still merge them — same reason. Lane 8 is the ONLY lane \
         that separates this pair, so dropping it is exactly as bad as never having read bit 255"
    );

    // ⚑ **NEW REJECTS, AT THE COLUMNS.** `anchor_lanes` goes through `PUBKEY_NONET_LANE_COL`, so
    // this is the producers' actual write and not the encoder a second time.
    assert_ne!(
        anchor_lanes(&key_a),
        anchor_lanes(&key_minus_a),
        "THE FLAG DAY REGRESSED AT THE ANCHOR: the committed limb vectors of a key and its \
         negation are identical again. The encoder separating is NOT enough — check that both \
         producers write PUBKEY_NONET_LANE_COL[8] and that it is < NUM_PRE_LIMBS"
    );
    let anchor_diff: Vec<usize> = (0..9)
        .filter(|i| anchor_lanes(&key_a)[*i] != anchor_lanes(&key_minus_a)[*i])
        .collect();
    assert_eq!(
        anchor_diff,
        vec![8],
        "and the separation must be in the ninth committed lane, nowhere else"
    );

    // ⚑ **ANTI-VACUITY: ROUND-TRIP, not \"the digests differ\".** Two lane vectors differing proves
    // nothing about whether either BINDS its key. Decode both committed vectors back to 32 bytes
    // and require the original keys — that is the property the whole flag day is for.
    let back_a = Faithful9::from_key_lanes9(&key_a).to_key_bytes();
    let back_minus_a = Faithful9::from_key_lanes9(&key_minus_a).to_key_bytes();
    assert_eq!(back_a, key_a, "the committed nonet must decode back to A");
    assert_eq!(
        back_minus_a, key_minus_a,
        "…and to -A, which is what makes the separation a BINDING and not just a difference"
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

    // ⚑ **ANTI-VACUITY, AND IT HAD TO CHANGE SHAPE ON 2026-08-02.** Until then this asserted
    // `!routers.is_empty()` and `!measured.is_empty()`, using the tree's own residuals as proof
    // that the scanner worked. The owner-key octet was the LAST residual, so both sets are now
    // legitimately empty and those two assertions would have had to be deleted — leaving a gate
    // that passes green over a tree it never actually read.
    //
    // A floor must be SATISFIABLE and REFUTABLE but not PROVABLE. So the scanner is exercised
    // against a SYNTHETIC source that does contain a router and a reason constant: if the parser
    // rots, this goes red whether or not the tree has residuals.
    {
        let synthetic = concat!(
            "pub const SYNTHETIC_RESIDUAL_FOR_THE_SELF_TEST: &str = \"a reason long enough to \
             pass the thinness check\";\n",
            "impl Faithful8 {\n",
            "    pub fn from_synthetic_probe(x: [BabyBear; 8]) -> Self {\n",
            "        Self::from_lossy_",
            "31bit_DANGER(SYNTHETIC_RESIDUAL_FOR_THE_SELF_TEST, x)\n",
            "    }\n}\n"
        );
        let probe_routers = self::routers(synthetic);
        assert_eq!(
            probe_routers
                .get("from_synthetic_probe")
                .map(String::as_str),
            Some("SYNTHETIC_RESIDUAL_FOR_THE_SELF_TEST"),
            "the ROUTER scan cannot see a router in a source that plainly has one — the parser is \
             broken, and a broken parser must not read as a clean tree. Derived: {probe_routers:?}"
        );
        let probe_consts = self::reason_constants(synthetic);
        let v = probe_consts
            .get("SYNTHETIC_RESIDUAL_FOR_THE_SELF_TEST")
            .expect("the REASON-CONSTANT scan cannot see a `&str` const that is plainly declared");
        assert!(
            v.contains("a reason long enough"),
            "the literal reader mangled it: {v:?}"
        );
        // …and the DOC parser must see an entry when there is one.
        let probe_listed = listed_admissions(
            "- `some/file.rs` — `SYNTHETIC_RESIDUAL_FOR_THE_SELF_TEST` — why it is admitted",
        );
        assert_eq!(
            probe_listed.len(),
            1,
            "the burn-down doc parser sees no entry in a line that is one"
        );
    }
    let measured = burn_down_admissions(&routers);

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

    // ⚑ The state as of 2026-08-02, asserted rather than assumed: the list is EMPTY, because the
    // owner-key octet was the last entry and its ninth lane now reaches the anchor. This is a
    // narrow claim — nothing routes through the `_DANGER` hatch — and NOT "every constructor here
    // is faithful": `from_bytes32` still admits an O(1)-aliasable octet through the front door,
    // which is exactly how the list read "EMPTY (v13 DONE)" while the key octet sat in the tree.
    assert!(
        measured.is_empty(),
        "a residual re-entered the burn-down list: {measured:#?}. That is not a failure by \
         itself — write the doc rows and this passes — but it IS a claim the tree did not carry \
         a moment ago, so it must be a deliberate one."
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
    // ⚑ The measured quantity is the ANCHOR's read-set, and as of 2026-08-02 it is the WHOLE
    // source. It was 232 while the low-eight write was deployed, and this assertion moving from
    // 232 to 256 is the flag day landing in the one place a reader of the law doc can check.
    let log2_p = f64::from(BABYBEAR_P).log2();
    let base = base_vector();
    let reference = anchor_lanes(&base);
    let mut unread = 0u32;
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if anchor_lanes(&flipped) == reference {
                unread += 1;
            }
        }
    }
    let image_bits = 256 - unread;
    assert_eq!(image_bits, 256, "the anchor now reads every source bit");
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

    // ⚑ THE SUCCESSOR CARRIES THE CORRECTION NOW. Until 2026-08-02 this block asserted four
    // properties of `KEY_NONET_NINTH_LANE_UNBOUND` — the residual's reason string — so that the
    // grep was readable without opening the doc. That constant is DELETED with its residual, and
    // the four assertions could not simply be dropped: the sentences they policed are exactly the
    // ones a reader hits first, and they moved rather than expired.
    //
    // They now sit on `Faithful9`'s key constructor, which is where a reader arrives today. Read
    // from the SOURCE rather than linked, so a rewrite that quietly drops the correction is red.
    let f9 = std::fs::read_to_string(repo_root().join("circuit/src/faithful9.rs"))
        .expect("circuit/src/faithful9.rs must exist — it is the successor to the key octet");
    for needle in [
        "image is exactly `2^256`",   // the number to quote
        "INJECTIVITY, NOT COLLISION", // the distinction this tree keeps losing
        "x-sign",                     // WHY it mattered: the Ed25519 bit that made the merge free
        "p^8 < 2^256",                // why no 8-lane repair was available
    ] {
        assert!(
            f9.contains(needle),
            "circuit/src/faithful9.rs must say {needle:?} where it documents the key nonet — the \
             corrections that lived on the retired residual's reason constant moved HERE when it \
             was deleted, and dropping them would leave the next reader to re-derive the wound"
        );
    }
    // …and the deleted things must stay deleted, with the note that says so. A constructor that
    // reappears is the 232-bit anchor reappearing.
    let hatch = hatch_source();
    assert!(
        !hatch.contains(&format!("pub fn {}(", concat!("from_key_nonet", "_low8"))),
        "the low-eight key projection is back in {HATCH_SRC} — it commits {image_bits} bits minus \
         the ninth lane, which is the wound this file measures"
    );
    // The measured anchor width is stated by the doc that governs it, so the two cannot drift.
    assert!(
        doc.contains("232 of 256") || doc.contains("232 of the owner key's 256"),
        "the law doc must keep the number the retired write bound ({image_bits} is today's), or \
         the flag day stops being findable six weeks out"
    );
}
