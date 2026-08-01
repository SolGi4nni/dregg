//! # The KEY-OCTET 30-bit packer (family **F2**): its FOUR twins, its HOLE, and the floor.
//!
//! ## What this file is, at current resolution
//!
//! Three gates, and only the FIRST of them is a security property:
//!
//! 1. **`f2_*_twins_*`** — a real cross-check. Four byte-identical re-implementations of the
//!    `8+8+8+6 = 30` bits/limb packing of a 32-byte canonical value into eight BabyBear lanes
//!    exist in this tree, in four different crates, and until this file their byte-identity was
//!    asserted **in prose only**, with no test between any pair. These tests pin them equal on an
//!    adversarial corpus. Mutating any one of them by a single bit turns these red.
//! 2. **`hole_f2_*`** — ⚠ **these DOCUMENT A HOLE; they do not guard one.** They are constructive:
//!    given any 32-byte value they *build* a different 32-byte value with an identical octet, and
//!    then carry that collision downstream through the membership-leaf compress and the four-felt
//!    id fold. A reader who sees them green should read "the hole is still exactly where we said",
//!    not "the packer is safe". They go red only if someone FIXES the encoder — at which point
//!    they should be deleted, not repaired.
//! 3. **`floor_f2_*`** — the arithmetic, pinned, with the IMAGE and the COLLISION bound kept in
//!    separate named constants because conflating them is this house's documented error
//!    (`docs/FAITHFUL-COMMITMENT-LAW.md` line 128: *"Quoting the image size where the birthday
//!    bound is meant is the house error"*).
//!
//! ## Its sibling, and what is NOT duplicated
//!
//! `circuit/tests/faithful8_key_octet_below_floor.rs` landed the same day from the wall lane and
//! is the file that **demoted** `Faithful8::from_canonical_key` onto the `_DANGER` hatch. It owns
//! the burn-down-list gate, the law-doc bound-quoting gate, and the Ed25519 exhibit (a key and its
//! negation differ only in bit 7 of byte 31 — one of the sixteen unread bits — so the collision
//! cost among *valid* public keys is `0`, not `2^120`). **Read it first; it is the finding.** The
//! numbers here were checked against it and agree to the digit (247.2551 / 123.6276 / 240 / 120 /
//! 3.6276). Do not edit `docs/FAITHFUL-COMMITMENT-LAW.md` casually — that file's gate parses it.
//!
//! What is here and not there, because `dregg-circuit` cannot see `dregg-commit` or
//! `dregg-storage` from its own test target:
//!
//! * the **twin cross-check** itself — the wall lane measures ONE packer, this measures FOUR
//!   against each other;
//! * the collision carried **downstream** through `compress_member` and both four-felt folds;
//! * the pigeonhole as **exact integer arithmetic** (`p^8 < 2^256 <= p^9`, the Rust twin of
//!   `FieldLanes9.nine_lanes_is_the_minimum`) rather than as a float comparison;
//! * the image established as a **bit permutation** (GF(2) linearity + an injective, surjective
//!   source-bit-to-lane-slot map) rather than by counting bits that fail to move the octet. Two
//!   independent derivations of `240` is the point, not an accident.
//!
//! ## The four twins
//!
//! | # | site | returns |
//! |---|------|---------|
//! | 1 | `cell/src/commitment.rs::canonical_to_babybear_pi` | `[u32; 8]` |
//! | 2 | `commit/src/typed.rs::canonical_32_to_felts_8` | `[BabyBear; 8]` |
//! | 3 | `storage/src/commitment.rs::canonical_32_to_felts_8` | `[BabyBear; 8]` |
//! | 4 | `circuit/src/effect_vm/trace.rs::canonical_id_to_felts_4` | inlines the packing, folds to 4 |
//!
//! `circuit/src/faithful8.rs::Faithful8::from_canonical_key` is a fifth *mention* but not a fifth
//! implementation — it takes twin #2's output and names the lane. It is pinned here as a
//! pass-through so that a future re-encoding inside the wall would also show up.
//!
//! ## Where the octet lands (why the hole is not academic)
//!
//! `turn/src/rotation_witness.rs:560-561` computes `canonical_32_to_felts_8(cell.public_key())`
//! and writes it through `Faithful8::from_canonical_key` into `B_PUBKEY_OCTET` (in-block offset
//! 105..112, both BEFORE and AFTER blocks). That is a pre-iroot limb, so it rides the
//! `wireCommitR` absorption chain into `state_commit` and the signed consensus anchor.
//! `commit/src/typed.rs:615::compress_member` runs the same packing into the membership leaf.
//!
//! ## Why this file lives in `dregg-commit`
//!
//! `dregg_commit::typed` is where the packing is owned (`circuit/src/faithful8.rs:188` names it as
//! the owner). `dregg-cell` and `dregg-storage` are `[dev-dependencies]` here purely so all four
//! twins are visible from one test target; nothing in `dregg-commit`'s library depends on them.
//!
//! ## What this file deliberately does NOT claim
//!
//! Agreement among four copies of one map says **nothing** about whether the map is injective. It
//! is not (gate 2 exhibits that constructively). These twins agreeing is the *floor* of what a
//! reader should expect, not evidence of soundness.

use dregg_circuit::Faithful8;
use dregg_circuit::effect_vm::canonical_id_to_felts_4;
use dregg_circuit::field::BABYBEAR_P;
use dregg_commit::typed::{canonical_32_to_felts_4, canonical_32_to_felts_8, compress_member};

// ---------------------------------------------------------------------------
// The corpus.
// ---------------------------------------------------------------------------

/// The byte indices whose TOP TWO BITS the `hi & 0x3F` mask discards: every fourth byte.
const MASKED_BYTES: [usize; 8] = [3, 7, 11, 15, 19, 23, 27, 31];

/// Deterministic, dependency-free PRNG (splitmix64). A test corpus must be reproducible from
/// the source alone — a seeded `rand` would make a red un-rerunnable.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn next_bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_exact_mut(8) {
            chunk.copy_from_slice(&self.next_u64().to_le_bytes());
        }
        out
    }
}

/// Write a u32 into 32-byte position `i` as a little-endian 4-byte chunk — the exact chunking
/// the packer reads, so a "straddling p" case can be aimed at a specific lane.
fn with_chunk(base: &[u8; 32], lane: usize, chunk: u32) -> [u8; 32] {
    let mut out = *base;
    out[lane * 4..lane * 4 + 4].copy_from_slice(&chunk.to_le_bytes());
    out
}

/// The adversarial corpus: structure first, then bulk.
fn corpus() -> Vec<[u8; 32]> {
    let mut v: Vec<[u8; 32]> = Vec::new();

    // Extremes.
    v.push([0x00; 32]);
    v.push([0xFF; 32]);
    v.push([0x3F; 32]);
    v.push([0xC0; 32]);
    v.push([0x80; 32]);
    v.push([0x01; 32]);

    // Every single source bit, alone. 256 vectors — this is also what gate 3's structural
    // analysis walks, and it is the only way a mask change is guaranteed to be seen.
    for byte in 0..32usize {
        for bit in 0..8u32 {
            let mut x = [0u8; 32];
            x[byte] = 1u8 << bit;
            v.push(x);
        }
    }

    // Every byte position saturated alone.
    for byte in 0..32usize {
        let mut x = [0u8; 32];
        x[byte] = 0xFF;
        v.push(x);
    }

    // ⚑ Values STRADDLING p, aimed one lane at a time. F2's lanes are `< 2^30 < p` so they never
    // reduce — but these are exactly the chunks that separate F2 from family F1
    // (`bytes32_to_8_limbs`, a 4-byte LE `% p`), and a twin that silently drifted toward F1 dies
    // here and nowhere else.
    let straddle: [u32; 10] = [
        BABYBEAR_P - 1,
        BABYBEAR_P,
        BABYBEAR_P + 1,
        2 * BABYBEAR_P - 1,
        2 * BABYBEAR_P,
        u32::MAX,
        1u32 << 30,
        (1u32 << 30) - 1,
        1u32 << 31,
        0x3FFF_FFFF,
    ];
    for lane in 0..8usize {
        for chunk in straddle {
            v.push(with_chunk(&[0x00; 32], lane, chunk));
            v.push(with_chunk(&[0xFF; 32], lane, chunk));
        }
    }

    // The discarded-bit positions specifically: all 2^16 masks is gate 2's job; here take a
    // structured slice so the twin gate also exercises them.
    let base = [0xA5u8; 32];
    for mask in [0x0000u16, 0x0001, 0x8000, 0x5555, 0xAAAA, 0xFFFF] {
        v.push(flip_discarded_bits(&base, mask));
    }

    // Bulk.
    let mut rng = SplitMix64(0x4472_6567_674B_6579); // "DreggKey"
    for _ in 0..4096 {
        v.push(rng.next_bytes32());
    }

    v
}

// ---------------------------------------------------------------------------
// The four twins, called uniformly.
// ---------------------------------------------------------------------------

fn twin1_cell(x: &[u8; 32]) -> [u32; 8] {
    dregg_cell::commitment::canonical_to_babybear_pi(x)
}

fn twin2_commit(x: &[u8; 32]) -> [u32; 8] {
    canonical_32_to_felts_8(x).map(|f| f.as_u32())
}

fn twin3_storage(x: &[u8; 32]) -> [u32; 8] {
    dregg_storage::commitment::canonical_32_to_felts_8(x).map(|f| f.as_u32())
}

// ---------------------------------------------------------------------------
// GATE 1 — the twin cross-check.
// ---------------------------------------------------------------------------

#[test]
fn f2_packer_twins_agree_across_cell_commit_and_storage() {
    let corpus = corpus();
    assert!(
        corpus.len() > 4000,
        "corpus collapsed to {} entries — a gate over an empty corpus is not a gate",
        corpus.len()
    );

    for (idx, x) in corpus.iter().enumerate() {
        let a = twin1_cell(x);
        let b = twin2_commit(x);
        let c = twin3_storage(x);

        assert_eq!(
            a,
            b,
            "TWIN DRIFT at corpus[{idx}] ({}): \
             cell::commitment::canonical_to_babybear_pi != commit::typed::canonical_32_to_felts_8\n\
             cell    = {a:?}\ncommit  = {b:?}",
            hex(x)
        );
        assert_eq!(
            b,
            c,
            "TWIN DRIFT at corpus[{idx}] ({}): \
             commit::typed::canonical_32_to_felts_8 != storage::commitment::canonical_32_to_felts_8\n\
             commit  = {b:?}\nstorage = {c:?}",
            hex(x)
        );
    }
}

#[test]
fn f2_packer_twins_agree_on_the_four_felt_fold_in_circuit_trace() {
    // `circuit/src/effect_vm/trace.rs::canonical_id_to_felts_4` INLINES the packing (so the
    // dregg-circuit crate stays free of a dregg-commit edge) and then applies the same four
    // `hash_4_to_1` compressions as `commit::typed::canonical_32_to_felts_4`. Its own doc-comment
    // claims the `federation_owner_binding_round_trip` test would catch drift; that test does not
    // compare the two functions. This one does.
    for (idx, x) in corpus().iter().enumerate() {
        let via_commit = canonical_32_to_felts_4(x);
        let via_circuit = canonical_id_to_felts_4(x);
        assert_eq!(
            via_commit.map(|f| f.as_u32()),
            via_circuit.map(|f| f.as_u32()),
            "TWIN DRIFT at corpus[{idx}] ({}): \
             commit::typed::canonical_32_to_felts_4 != circuit::effect_vm::canonical_id_to_felts_4",
            hex(x)
        );
    }
}

#[test]
fn f2_faithful8_wall_is_a_pass_through_not_a_fifth_encoding() {
    // `Faithful8::from_canonical_key` NAMES the lane; it must not transform it. If a future
    // change makes the wall re-encode, the deployed `B_PUBKEY_OCTET` fill
    // (`turn/src/rotation_witness.rs:561`) would silently stop matching every off-AIR
    // reconstruction that calls the packer directly.
    //
    // ⚠ HONESTY, so nobody overweights this one: it is the WEAKEST test in the file, and it is
    // close to a pin against its own definition — the constructor's body is a move today, so the
    // assertion is nearly true by construction. It survived both encoder mutations that killed
    // seven of the ten tests here, which is correct behaviour and also a warning about how much
    // it can detect. Its one real job is the day someone puts arithmetic inside the wall: the
    // 2026-08-01 demotion already re-routed this body through the `_DANGER` hatch, and this is
    // what would have caught that re-routing if it had not been transparent.
    for x in corpus() {
        let limbs = canonical_32_to_felts_8(&x);
        assert_eq!(
            Faithful8::from_canonical_key(limbs)
                .limbs()
                .map(|f| f.as_u32()),
            limbs.map(|f| f.as_u32()),
            "Faithful8::from_canonical_key transformed its input"
        );
    }
}

#[test]
fn f2_every_lane_is_a_thirty_bit_value_so_none_of_the_twins_ever_reduces() {
    // The packing's own justification (`cell/src/commitment.rs` doc: "30-bit limbs guarantee a
    // unique encoding without modular reduction collisions"). The claim about REDUCTION is true
    // and this pins it. The claim of a "unique encoding" is FALSE and gate 2 exhibits why.
    for x in corpus() {
        for (lane, value) in twin2_commit(&x).iter().enumerate() {
            assert!(
                *value < (1u32 << 30),
                "lane {lane} = {value} is not a 30-bit value for {}",
                hex(&x)
            );
            assert!(*value < BABYBEAR_P, "lane {lane} = {value} exceeds p");
        }
    }
}

// ---------------------------------------------------------------------------
// GATE 2 — ⚠ THE HOLE, CONSTRUCTED. These tests DOCUMENT; they do not GUARD.
// ---------------------------------------------------------------------------

/// Flip the discarded bits selected by `mask`: bit `2k` of the mask flips bit 6 of
/// `MASKED_BYTES[k]`, bit `2k+1` flips bit 7. Every one of the 2^16 masks names a distinct
/// 32-byte string, and every one of them has the SAME eight-lane image.
fn flip_discarded_bits(x: &[u8; 32], mask: u16) -> [u8; 32] {
    let mut out = *x;
    for (k, byte) in MASKED_BYTES.iter().enumerate() {
        if mask & (1u16 << (2 * k)) != 0 {
            out[*byte] ^= 1u8 << 6;
        }
        if mask & (1u16 << (2 * k + 1)) != 0 {
            out[*byte] ^= 1u8 << 7;
        }
    }
    out
}

#[test]
fn hole_f2_pack_collides_by_construction_on_every_input() {
    // ⚠ GREEN HERE MEANS THE HOLE IS OPEN. This test is a MEASUREMENT of a defect.
    //
    // No search, no birthday, no grind: given ANY 32-byte value, one XOR produces a different
    // 32-byte value with a bit-identical octet.
    for (idx, x) in corpus().iter().enumerate() {
        let sibling = flip_discarded_bits(x, 0x0001); // flip bit 6 of byte 3 — one bit.
        assert_ne!(
            *x, sibling,
            "corpus[{idx}]: the sibling construction did not change the input"
        );
        assert_eq!(
            twin2_commit(x),
            twin2_commit(&sibling),
            "corpus[{idx}] ({}): the one-bit sibling did NOT collide — the encoder was FIXED. \
             Delete this test rather than repairing it, and retire the KEY_COMMIT burn-down rows \
             in docs/FAITHFUL-COMMITMENT-LAW.md.",
            hex(x)
        );
    }
}

#[test]
fn hole_f2_second_preimage_class_has_exactly_65536_members() {
    // ⚠ GREEN HERE MEANS THE HOLE IS OPEN.
    //
    // The image is not merely non-injective: the fibre through any point is EXACTLY 2^16 distinct
    // 32-byte strings and all of them are enumerable in constant time. This is the precise sense
    // in which second preimage on the raw string costs O(1) and is not a "bound" at all.
    let bases: [[u8; 32]; 3] = [
        [0x00; 32],
        [0xFF; 32],
        SplitMix64(0xF2F2_F2F2).next_bytes32(),
    ];

    for base in bases {
        let target = twin2_commit(&base);
        let mut seen: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
        for mask in 0u32..=0xFFFF {
            let sibling = flip_discarded_bits(&base, mask as u16);
            assert_eq!(
                twin2_commit(&sibling),
                target,
                "mask {mask:#06x} left the octet — the fibre is smaller than claimed"
            );
            assert!(
                seen.insert(sibling),
                "mask {mask:#06x} produced a duplicate string; the 16 flipped bits are not free"
            );
        }
        assert_eq!(seen.len(), 1 << 16, "fibre size is not 2^16");
    }
}

#[test]
fn hole_f2_collision_survives_the_membership_compress_and_the_four_felt_fold() {
    // ⚠ GREEN HERE MEANS THE HOLE IS OPEN.
    //
    // The collision is not contained by the Poseidon2 layer above it — a hash of equal inputs is
    // equal. Two distinct 32-byte keys therefore share:
    //   * `compress_member`               — the membership-domain Merkle leaf
    //                                       (`commit/src/typed.rs:615`, called from
    //                                       `turn/src/executor/membership_verifier.rs:96`);
    //   * `canonical_32_to_felts_4` /
    //     `canonical_id_to_felts_4`       — the federation-id / owner-cell-id PI binding
    //                                       (`circuit/src/effect_vm/trace.rs:1146-1147`);
    //   * `Faithful8::from_canonical_key` — the fill written to `B_PUBKEY_OCTET`
    //                                       (`turn/src/rotation_witness.rs:560-561`), a pre-iroot
    //                                       limb absorbed into `state_commit`.
    let a = SplitMix64(0xDEAD_BEEF_0000_0001).next_bytes32();
    let b = flip_discarded_bits(&a, 0xFFFF); // all 16 discarded bits flipped at once.
    assert_ne!(a, b);
    assert_eq!(
        a.iter().zip(b.iter()).filter(|(p, q)| p != q).count(),
        8,
        "the two strings should differ in all eight masked bytes"
    );

    // ⚑ `compress_member` was widened from ONE felt to EIGHT on 2026-08-01 (felt-width finding
    // #9 — a 31-bit leaf domain is collided in 2^15.5). That fix is real and orthogonal: it
    // repairs the OUTPUT width, while F2 is a defect in the INPUT. The full-width leaf still
    // fails to separate this pair, because a hash of equal inputs is equal however wide it is.
    assert_eq!(
        compress_member(&a).map(|f| f.as_u32()),
        compress_member(&b).map(|f| f.as_u32()),
        "membership leaf separated the pair — compress_member no longer rides F2"
    );
    assert_eq!(
        canonical_32_to_felts_4(&a).map(|f| f.as_u32()),
        canonical_32_to_felts_4(&b).map(|f| f.as_u32()),
        "the four-felt fold separated the pair"
    );
    assert_eq!(
        canonical_id_to_felts_4(&a).map(|f| f.as_u32()),
        canonical_id_to_felts_4(&b).map(|f| f.as_u32()),
        "the circuit-side four-felt id fold separated the pair"
    );
    assert_eq!(
        Faithful8::from_canonical_key(canonical_32_to_felts_8(&a))
            .limbs()
            .map(|f| f.as_u32()),
        Faithful8::from_canonical_key(canonical_32_to_felts_8(&b))
            .limbs()
            .map(|f| f.as_u32()),
        "the pubkey-octet fill separated the pair"
    );
}

// ---------------------------------------------------------------------------
// GATE 3 — the floor arithmetic. IMAGE and COLLISION BOUND are kept apart on purpose.
// ---------------------------------------------------------------------------

/// The number of source bits F2 retains, established structurally by
/// [`floor_f2_retains_exactly_240_source_bits_as_a_bit_permutation`] rather than asserted.
/// **This is an IMAGE size in bits. It is NOT a security bound.**
const F2_IMAGE_BITS: f64 = 240.0;

/// The birthday bound over an image of `2^F2_IMAGE_BITS`. **This is the COLLISION bound.**
const F2_COLLISION_BOUND_BITS: f64 = F2_IMAGE_BITS / 2.0;

#[test]
fn floor_f2_retains_exactly_240_source_bits_as_a_bit_permutation() {
    // The packing is `lo | mid1<<8 | mid2<<16 | (hi & 0x3F)<<24` — an OR of DISJOINT bit ranges,
    // so it is GF(2)-linear and fully determined by its action on the 256 unit vectors. Walking
    // them establishes the image size EXACTLY, with integers, rather than by an entropy argument.

    // (a) linearity, so the unit-vector walk is complete rather than a sample.
    let mut rng = SplitMix64(0x1111_2222_3333_4444);
    for _ in 0..2048 {
        let x = rng.next_bytes32();
        let y = rng.next_bytes32();
        let mut xor = [0u8; 32];
        for (slot, (p, q)) in xor.iter_mut().zip(x.iter().zip(y.iter())) {
            *slot = p ^ q;
        }
        let lx = twin2_commit(&x);
        let ly = twin2_commit(&y);
        let lxor = twin2_commit(&xor);
        for lane in 0..8 {
            assert_eq!(
                lxor[lane],
                lx[lane] ^ ly[lane],
                "the packing is not GF(2)-linear on lane {lane}"
            );
        }
    }

    // (b) the unit-vector walk.
    let mut retained: Vec<(usize, u32)> = Vec::new(); // source bit -> (lane, lane bit)
    let mut discarded: Vec<usize> = Vec::new();
    for b in 0..256usize {
        let mut x = [0u8; 32];
        x[b / 8] = 1u8 << (b % 8);
        let lanes = twin2_commit(&x);
        let set: Vec<(usize, u32)> = lanes
            .iter()
            .enumerate()
            .filter(|(_, v)| **v != 0)
            .map(|(l, v)| {
                assert_eq!(
                    v.count_ones(),
                    1,
                    "source bit {b} lit {} bits in lane {l}; the packing is not a bit map",
                    v.count_ones()
                );
                (l, v.trailing_zeros())
            })
            .collect();
        match set.len() {
            0 => discarded.push(b),
            1 => retained.push((b, set[0].0 as u32 * 30 + set[0].1)),
            n => panic!("source bit {b} reached {n} lanes"),
        }
    }

    // (c) exactly 16 bits are lost, and they are exactly the ones the `& 0x3F` mask names.
    let expected_discarded: Vec<usize> = MASKED_BYTES
        .iter()
        .flat_map(|byte| [byte * 8 + 6, byte * 8 + 7])
        .collect();
    let mut sorted = discarded.clone();
    sorted.sort_unstable();
    let mut expected_sorted = expected_discarded.clone();
    expected_sorted.sort_unstable();
    assert_eq!(
        sorted, expected_sorted,
        "the DISCARDED source bits are not the 16 the `hi & 0x3F` mask names"
    );
    assert_eq!(discarded.len(), 16);

    // (d) the retained bits land injectively and surjectively on the 8 x 30 = 240 lane slots.
    assert_eq!(retained.len(), 240, "retained source bit count");
    let mut slots: Vec<u32> = retained.iter().map(|(_, s)| *s).collect();
    slots.sort_unstable();
    slots.dedup();
    assert_eq!(
        slots.len(),
        240,
        "two source bits share a lane slot — the map is not a permutation"
    );
    assert_eq!(*slots.first().unwrap(), 0);
    assert_eq!(*slots.last().unwrap(), 239);

    // (e) hence the IMAGE is exactly 2^240, established, not assumed.
    assert_eq!(F2_IMAGE_BITS, retained.len() as f64);
}

#[test]
fn floor_eight_babybear_lanes_cannot_injectively_carry_thirty_two_bytes() {
    // The Rust twin of `metatheory/Dregg2/Circuit/FieldLanes9.lean::nine_lanes_is_the_minimum`
    // (`P^8 < 2^256 <= P^9`), computed here with exact integer arithmetic rather than floats so
    // the pigeonhole is a COUNT and not a rounding.
    //
    // ⚑ This is a statement about EVERY 8-lane encoding of 32 bytes — not about F2's masking.
    // Even a perfect 8-lane packing would be non-injective; F2 is worse than that floor, not
    // equal to it (see the image/collision constants above).
    assert_eq!(BABYBEAR_P, 2_013_265_921, "BabyBear modulus moved");
    assert_eq!(
        BABYBEAR_P,
        (1u32 << 31) - (1u32 << 27) + 1,
        "p is not 2^31 - 2^27 + 1"
    );

    let p8 = big_pow(BABYBEAR_P, 8);
    let p9 = big_pow(BABYBEAR_P, 9);
    let two_256 = big_pow(2, 256);

    assert_eq!(
        big_cmp(&p8, &two_256),
        std::cmp::Ordering::Less,
        "p^8 >= 2^256 — the pigeonhole does not hold and this whole campaign is wrong"
    );
    assert_ne!(
        big_cmp(&p9, &two_256),
        std::cmp::Ordering::Less,
        "p^9 < 2^256 — nine lanes would not suffice either"
    );

    // The exact bit lengths, pinned, so a silent change in `big_pow` cannot make the two
    // comparisons above pass vacuously.
    assert_eq!(big_bit_len(&p8), 248, "bit length of p^8");
    assert_eq!(big_bit_len(&p9), 279, "bit length of p^9");
    assert_eq!(big_bit_len(&two_256), 257, "bit length of 2^256");
}

#[test]
fn floor_f2_collision_bound_is_below_the_law_s_own_octet_collision_bound() {
    // `docs/FAITHFUL-COMMITMENT-LAW.md` line 4 states the bar as "~124-bit, the 8-felt encoding".
    // That figure IS a collision bound: an 8-felt image carries 8 * log2(p) = 247.2551 bits, and
    // the birthday bound over it is half that, 123.6276 — which rounds to the doc's "~124".
    //
    // ⚠ The law itself names the trap (line 128): "Quoting the image size where the birthday
    // bound is meant is the house error". So both quantities are named separately below and the
    // comparison is collision-against-collision.
    let log2_p = f64::from(BABYBEAR_P).log2();
    assert!(
        (log2_p - 30.906_890_596_325_1).abs() < 1e-9,
        "log2(p) = {log2_p}"
    );

    let law_octet_image_bits = 8.0 * log2_p;
    let law_octet_collision_bound_bits = law_octet_image_bits / 2.0;

    assert!(
        (law_octet_image_bits - 247.255_124_770_600_8).abs() < 1e-6,
        "8 lanes of IMAGE = {law_octet_image_bits}"
    );
    assert!(
        (law_octet_collision_bound_bits - 123.627_562_385_300_4).abs() < 1e-6,
        "the law's octet COLLISION bound = {law_octet_collision_bound_bits}"
    );

    // The pigeonhole, restated in the same units as the doc.
    assert!(
        law_octet_image_bits < 256.0,
        "8 lanes carry {law_octet_image_bits} bits of IMAGE against 256 bits of source"
    );

    // F2 does not even reach that ceiling: it throws away 7.2551 bits of the available image
    // before any encoding question is asked.
    assert!(
        F2_IMAGE_BITS < law_octet_image_bits,
        "F2 IMAGE {F2_IMAGE_BITS} vs available {law_octet_image_bits}"
    );

    // ⚑ THE FINDING, in one comparison, both sides COLLISION bounds.
    assert!(
        F2_COLLISION_BOUND_BITS < law_octet_collision_bound_bits,
        "F2 COLLISION bound 2^{F2_COLLISION_BOUND_BITS} is not below the law's \
         2^{law_octet_collision_bound_bits}"
    );
    let deficit = law_octet_collision_bound_bits - F2_COLLISION_BOUND_BITS;
    assert!(
        (3.6..3.7).contains(&deficit),
        "the F2 shortfall against the law's bar moved: {deficit} bits"
    );

    // And the number that actually matters for the deployed pubkey octet is neither of the two
    // above: for a raw 32-byte STRING second preimage is O(1) (gate 2), and the 2^120 figure is
    // the cost only when the colliding value must ALSO be a well-formed key. Stated here so a
    // reader who quotes one number from this file quotes it with its qualifier.
    assert_eq!(F2_COLLISION_BOUND_BITS, 120.0);
}

// ---------------------------------------------------------------------------
// Helpers.
// ---------------------------------------------------------------------------

fn hex(x: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in x {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Little-endian u32-limb bignum, only what the pigeonhole needs.
fn big_mul_small(v: &mut Vec<u32>, m: u32) {
    let mut carry: u64 = 0;
    for limb in v.iter_mut() {
        let prod = u64::from(*limb) * u64::from(m) + carry;
        *limb = (prod & 0xFFFF_FFFF) as u32;
        carry = prod >> 32;
    }
    while carry > 0 {
        v.push((carry & 0xFFFF_FFFF) as u32);
        carry >>= 32;
    }
}

fn big_pow(base: u32, exp: u32) -> Vec<u32> {
    let mut v = vec![1u32];
    for _ in 0..exp {
        big_mul_small(&mut v, base);
    }
    v
}

fn big_bit_len(v: &[u32]) -> u32 {
    for (i, limb) in v.iter().enumerate().rev() {
        if *limb != 0 {
            return i as u32 * 32 + (32 - limb.leading_zeros());
        }
    }
    0
}

fn big_cmp(a: &[u32], b: &[u32]) -> std::cmp::Ordering {
    let la = big_bit_len(a);
    let lb = big_bit_len(b);
    if la != lb {
        return la.cmp(&lb);
    }
    let n = a.len().max(b.len());
    for i in (0..n).rev() {
        let x = a.get(i).copied().unwrap_or(0);
        let y = b.get(i).copied().unwrap_or(0);
        if x != y {
            return x.cmp(&y);
        }
    }
    std::cmp::Ordering::Equal
}
