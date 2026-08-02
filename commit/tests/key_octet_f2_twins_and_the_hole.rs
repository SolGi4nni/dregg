//! # The KEY-LANE encoder (family **F2**): its FOUR twins, pinned equal — and the HOLE, CLOSED.
//!
//! ## What this file is, at current resolution
//!
//! 1. **`f2_*_twins_*`** — a real cross-check, and the load-bearing gate of this file. Four
//!    byte-identical re-implementations of the 32-byte → BabyBear-lane packing exist in this tree,
//!    in four different crates, and until this file their byte-identity was asserted **in prose
//!    only**, with no test between any pair. These tests pin them equal on an adversarial corpus.
//!    Mutating any one of them by a single bit turns these red — which is exactly what happened,
//!    deliberately, when the 2026-08-01 flag day moved all four at once.
//! 2. **`nonet_*`** — the encoder is now INJECTIVE and these are the properties that say so:
//!    a total decoder that is a left inverse, no lane reducing, and the ex-collision pair
//!    separated. ⚑ They replace the `hole_f2_*` tests, which were CONSTRUCTIVE exhibits of the
//!    defect and whose own instruction was *"they go red only if someone FIXES the encoder — at
//!    which point they should be deleted, not repaired."* Someone fixed the encoder.
//! 3. **`floor_f2_*`** — the arithmetic, pinned, with the IMAGE and the COLLISION bound kept in
//!    separate named constants because conflating them is this house's documented error
//!    (`docs/FAITHFUL-COMMITMENT-LAW.md` line 128: *"Quoting the image size where the birthday
//!    bound is meant is the house error"*).
//!
//! ## ⚑ WHAT CHANGED, 2026-08-01 — and what did NOT
//!
//! The packing was `lo | mid1<<8 | mid2<<16 | ((hi & 0x3F) << 24)`, `8+8+8+6 = 30` bits over
//! **eight** lanes. Bits 6-7 of bytes 3, 7, …, 31 were discarded: sixteen source bits, so every
//! input had `2^16 - 1` siblings with an identical lane vector, reachable by one XOR. Among
//! Ed25519 public keys the cost was `0`, the sign bit being one of them.
//!
//! It is now the base-`2^29` **NONET**: nine lanes, little-endian digits of the key read as one
//! 256-bit number, `8 * 29 + 24 = 256` exactly, image exactly `2^256`, no lane reducing. Lean
//! authority `Dregg2.Circuit.KeyLanes9.keyToLanes9` / `keyToLanes9_injective`.
//!
//! ⚠ **What did NOT change is where the ninth lane LANDS.** `B_PUBKEY_OCTET` is eight columns in
//! the deployed 184-limb geometry, so the rotated pre-limb write still commits lanes 0..=7 and the
//! signed anchor still binds 232 of 256 key bits. That residual is named
//! `KEY_NONET_NINTH_LANE_UNBOUND` and measured in
//! `circuit/tests/faithful8_key_octet_below_floor.rs`. **This file is about the ENCODER; do not
//! read a green run here as "the owner key is bound".**
//!
//! ## Its sibling
//!
//! `circuit/tests/faithful8_key_octet_below_floor.rs` owns the burn-down-list gate, the law-doc
//! bound-quoting gate, and the Ed25519 exhibit. **Read it first; it is the finding, and it is
//! where the un-closed half is measured.**
//!
//! What is here and not there, because `dregg-circuit` cannot see `dregg-commit` or
//! `dregg-storage` from its own test target:
//!
//! * the **twin cross-check** itself — the wall lane measures ONE packer, this measures FOUR
//!   against each other;
//! * the encoder's injectivity carried **downstream** through `compress_member` and both
//!   four-felt folds — i.e. that the fix reaches the membership leaf and the PI id bindings, not
//!   just the raw lanes;
//! * the pigeonhole as **exact integer arithmetic** (`p^8 < 2^256 <= p^9`, the Rust twin of
//!   `FieldLanes9.nine_lanes_is_the_minimum`) rather than as a float comparison. This is the
//!   statement that made eight lanes unrepairable and nine the minimum, and it is unchanged.
//!
//! ## The four twins
//!
//! | # | site | returns |
//! |---|------|---------|
//! | 1 | `cell/src/commitment.rs::canonical_to_babybear_nonet` | `[u32; 9]` |
//! | 2 | `commit/src/typed.rs::canonical_32_to_lanes_9` | `[BabyBear; 9]` |
//! | 3 | `storage/src/commitment.rs::canonical_32_to_lanes_9` | `[BabyBear; 9]` |
//! | 4 | `circuit/src/effect_vm/helpers.rs::key_limbs9` | `[BabyBear; 9]` |
//!
//! ⚑ **Twin #4 was INVISIBLE to this file until 2026-08-02.** It was an inline loop inside
//! `circuit/src/effect_vm/trace.rs::canonical_id_to_felts_4`, so the corpus below cross-checked
//! THREE transcriptions and the fourth was pinned only through a four-felt FOLD of itself. It is
//! now the named `key_limbs9` (hoisted, zero felts moved) and it is a full leg of the cross-check
//! — which matters more than the tidiness, because `key_limbs9` is the body BOTH deployed rotated
//! producers write into the committed owner-key carrier.
//!
//! ## Why this file lives in `dregg-commit`
//!
//! `dregg_commit::typed` is where the packing is owned. `dregg-cell` and `dregg-storage` are
//! `[dev-dependencies]` here purely so all four twins are visible from one test target; nothing in
//! `dregg-commit`'s library depends on them.
//!
//! ## What this file deliberately does NOT claim
//!
//! Agreement among four copies of one map says **nothing** about whether the map is injective —
//! that is why gate 2 exists as a separate set of properties rather than as a corollary. And
//! injectivity of the map says nothing about whether the anchor absorbs all nine of its lanes; see
//! the ⚠ above.

use dregg_circuit::Faithful9;
use dregg_circuit::effect_vm::canonical_id_to_felts_4;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_commit::typed::{
    KEY_LANE_BITS, KEY_TOP_LANE_BITS, canonical_32_to_felts_4, canonical_32_to_lanes_9,
    compress_member, lanes_9_to_canonical_32,
};

// ---------------------------------------------------------------------------
// The corpus.
// ---------------------------------------------------------------------------

/// The byte indices whose TOP TWO BITS the `hi & 0x3F` mask discards: every fourth byte.
const MASKED_BYTES: [usize; 8] = [3, 7, 11, 15, 19, 23, 27, 31];

/// Flip the bits the RETIRED octet discarded, selected by `mask`: bit `2k` flips bit 6 of
/// `MASKED_BYTES[k]`, bit `2k+1` flips bit 7.
///
/// ⚑ Each of the `2^16` masks used to name a distinct 32-byte string with the SAME eight-lane
/// image — that was the fibre, and this function was the constructor that exhibited it. Under the
/// nonet every one of those strings has its OWN lane vector, so the same function is now the
/// generator of the hardest adversarial slice available: the pairs the previous encoder could not
/// tell apart. It is kept for exactly that reason, and
/// `nonet_separates_every_pair_the_retired_octet_merged` is where it earns its keep.
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

fn twin1_cell(x: &[u8; 32]) -> [u32; 9] {
    dregg_cell::commitment::canonical_to_babybear_nonet(x)
}

fn twin2_commit(x: &[u8; 32]) -> [u32; 9] {
    canonical_32_to_lanes_9(x).map(|f| f.as_u32())
}

fn twin3_storage(x: &[u8; 32]) -> [u32; 9] {
    dregg_storage::commitment::canonical_32_to_lanes_9(x).map(|f| f.as_u32())
}

/// ⚑ **TWIN #4, VISIBLE FOR THE FIRST TIME (2026-08-02).** This body used to be INLINED inside
/// `circuit/src/effect_vm/trace.rs::canonical_id_to_felts_4`, which is exactly why the corpus below
/// pinned three transcriptions and not four: an unnamed inline copy is the copy a twin test cannot
/// reach. It is now `dregg_circuit::effect_vm::key_limbs9`, hoisted rather than re-typed (zero felts
/// moved), and it is also the body BOTH deployed rotated producers write through — so drift here is
/// drift at the signed anchor.
fn twin4_circuit(x: &[u8; 32]) -> [u32; 9] {
    dregg_circuit::effect_vm::key_limbs9(x).map(|f| f.as_u32())
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
        let d = twin4_circuit(x);

        assert_eq!(
            a,
            b,
            "TWIN DRIFT at corpus[{idx}] ({}): \
             cell::commitment::canonical_to_babybear_nonet != commit::typed::canonical_32_to_lanes_9\n\
             cell    = {a:?}\ncommit  = {b:?}",
            hex(x)
        );
        assert_eq!(
            b,
            c,
            "TWIN DRIFT at corpus[{idx}] ({}): \
             commit::typed::canonical_32_to_lanes_9 != storage::commitment::canonical_32_to_lanes_9\n\
             commit  = {b:?}\nstorage = {c:?}",
            hex(x)
        );
        assert_eq!(
            c,
            d,
            "TWIN DRIFT at corpus[{idx}] ({}): \
             storage::commitment::canonical_32_to_lanes_9 != circuit::effect_vm::key_limbs9\n\
             storage = {c:?}\ncircuit = {d:?}\n\
             ⚑ circuit::key_limbs9 is what BOTH rotated producers write into the committed key \
             carrier, so this leg is the one that reaches the signed anchor.",
            hex(x)
        );

        // ⚑ AND THE ROUND TRIP, on the same corpus. Four encoders agreeing could all be wrong
        // together; a total decoder recovering the 32 bytes cannot be satisfied by a consensus.
        assert_eq!(
            dregg_circuit::effect_vm::key_from_lanes9(&dregg_circuit::effect_vm::key_limbs9(x)),
            *x,
            "ROUND-TRIP FAILED at corpus[{idx}] ({}) — the nonet is not injective on this input",
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

/// ⚑ **REPOINTED 2026-08-02.** This was `f2_faithful8_wall_is_the_low_eight_lanes_and_nothing_else`
/// and it pinned `Faithful8::from_key_nonet_low8` — the projection — against its own input, which
/// its own comment called "the WEAKEST test in the file, close to a pin against its own
/// definition". It also carried the sentence that made the residual visible here: *"the wall takes
/// nine lanes and keeps eight."*
///
/// The wall now takes nine lanes and keeps NINE, so the interesting property is no longer "it did
/// not transform them" — it is that the wall is **invertible**, which no `Faithful8` constructor
/// could ever claim. That is a real assertion rather than a near-tautology: a wall that scrambled,
/// truncated or reordered would fail it, and so would one that lost lane 8 again.
#[test]
fn f2_faithful9_wall_keeps_all_nine_lanes_and_inverts() {
    for x in corpus() {
        let lanes = canonical_32_to_lanes_9(&x);
        let walled = Faithful9::from_key_lanes9(&x).lanes();
        assert_eq!(
            walled.map(|f| f.as_u32()),
            lanes.map(|f| f.as_u32()),
            "Faithful9::from_key_lanes9 disagrees with the authoring twin \
             commit::typed::canonical_32_to_lanes_9"
        );
        assert_eq!(
            walled.len(),
            9,
            "the wall is NINE lanes wide — that is the flag day"
        );
        // ⚑ ANTI-VACUITY: the 32 bytes come back. "The lanes match" is a differential between two
        // encoders and says nothing about whether either binds its source; this does.
        assert_eq!(
            Faithful9::from_key_lanes9(&x).to_key_bytes(),
            x,
            "the committed nonet must decode back to the key it encodes"
        );
    }
}

#[test]
fn f2_every_lane_is_below_the_radix_so_none_of_the_twins_ever_reduces() {
    // The encoding's own justification: `2^29 < p`, so no lane is a `mod p` reduction and the
    // nine lanes are genuine base-`2^29` digits. Unlike its predecessor's "unique encoding"
    // claim, this one is true AND sufficient — see `nonet_round_trips_through_a_total_decoder`.
    for x in corpus() {
        let lanes = twin2_commit(&x);
        for (lane, value) in lanes.iter().enumerate() {
            assert!(
                *value < (1u32 << KEY_LANE_BITS),
                "lane {lane} = {value} is not a {KEY_LANE_BITS}-bit value for {}",
                hex(&x)
            );
            assert!(*value < BABYBEAR_P, "lane {lane} = {value} exceeds p");
        }
        assert!(
            lanes[8] < (1u32 << KEY_TOP_LANE_BITS),
            "the top lane {} exceeds its {KEY_TOP_LANE_BITS}-bit width for {}",
            lanes[8],
            hex(&x)
        );
    }
}

// ---------------------------------------------------------------------------
// GATE 2 — THE ENCODER IS INJECTIVE. (These REPLACE the `hole_f2_*` exhibits.)
// ---------------------------------------------------------------------------
//
// ⚑ The `hole_f2_*` tests that stood here were CONSTRUCTIVE measurements of the defect: given any
// 32-byte value they built a different one with an identical octet, and carried that collision
// downstream through `compress_member` and both four-felt folds. Their own instruction read:
//
//     "They go red only if someone FIXES the encoder — at which point they should be deleted,
//      not repaired."
//
// The encoder was fixed on 2026-08-01 and they are deleted, not repaired. `flip_discarded_bits`
// and `MASKED_BYTES` survive here because the corpus still walks the byte positions the old mask
// named — they are now just an adversarial slice with a historical name, and the structural walk
// in gate 3 re-derives the read-set from scratch rather than trusting them.

#[test]
fn nonet_round_trips_through_a_total_decoder() {
    // What "injective" MEANS here, and the only form of it a Rust test can establish: a total
    // decoder that is a left inverse on the whole corpus. `Dregg2.Circuit.KeyLanes9` proves
    // `keyLanes9ToBytes_keyToLanes9` for ALL 32-byte values; this checks the Rust twin agrees
    // wherever it is asked. A differential over a corpus, not a proof over a domain.
    for (idx, x) in corpus().iter().enumerate() {
        assert_eq!(
            lanes_9_to_canonical_32(canonical_32_to_lanes_9(x)),
            *x,
            "corpus[{idx}] ({}) did not round-trip",
            hex(x)
        );
    }
}

#[test]
fn nonet_separates_every_pair_the_retired_octet_merged() {
    // The exact construction the deleted `hole_f2_pack_collides_by_construction_on_every_input`
    // used, run against the encoder that replaced it. Every sibling it built is now SEPARATED.
    // This is the refutation of the old test, kept as a test rather than as a claim.
    for (idx, x) in corpus().iter().enumerate() {
        let sibling = flip_discarded_bits(x, 0x0001); // flip bit 6 of byte 3 — one bit.
        assert_ne!(*x, sibling);
        assert_ne!(
            twin2_commit(x),
            twin2_commit(&sibling),
            "corpus[{idx}] ({}): a one-bit sibling still collides — an 8-lane pack came back",
            hex(x)
        );
    }

    // And the whole 2^16 fibre the old encoder had: every one of those strings is now distinct.
    // 65536 encodings, all different, is the fibre collapsing to a point.
    let base = [0xA5u8; 32];
    let mut seen = std::collections::HashSet::new();
    for mask in 0u32..=0xFFFF {
        assert!(
            seen.insert(twin2_commit(&flip_discarded_bits(&base, mask as u16))),
            "mask {mask:#06x} collided — the old 2^16 fibre has not fully collapsed"
        );
    }
    assert_eq!(seen.len(), 1 << 16);
}

#[test]
fn nonet_injectivity_reaches_the_membership_leaf_and_both_four_felt_folds() {
    // ⚑ THIS IS THE TEST THAT SAYS THE FIX REACHED THE CONSUMERS, and it is the direct inversion
    // of `hole_f2_collision_survives_the_membership_compress_and_the_four_felt_fold`. The old
    // collision was not contained by the Poseidon2 layer above it — a hash of equal inputs is
    // equal — so it flowed into:
    //   * `compress_member`             — the membership-domain Merkle leaf;
    //   * `canonical_32_to_felts_4` /
    //     `canonical_id_to_felts_4`     — the turn-hash / federation-id / owner-cell-id PI binding.
    // All three now absorb NINE lanes, so all three separate the pair.
    let a = SplitMix64(0xDEAD_BEEF_0000_0001).next_bytes32();
    let b = flip_discarded_bits(&a, 0xFFFF); // all 16 formerly-discarded bits flipped at once.
    assert_ne!(a, b);
    assert_eq!(
        a.iter().zip(b.iter()).filter(|(p, q)| p != q).count(),
        8,
        "the two strings should differ in all eight formerly-masked bytes"
    );

    assert_ne!(
        compress_member(&a).map(|f| f.as_u32()),
        compress_member(&b).map(|f| f.as_u32()),
        "the membership leaf still merges the pair — compress_member is not on the nonet"
    );
    assert_ne!(
        canonical_32_to_felts_4(&a).map(|f| f.as_u32()),
        canonical_32_to_felts_4(&b).map(|f| f.as_u32()),
        "the four-felt fold still merges the pair"
    );
    assert_ne!(
        canonical_id_to_felts_4(&a).map(|f| f.as_u32()),
        canonical_id_to_felts_4(&b).map(|f| f.as_u32()),
        "the circuit-side four-felt id fold still merges the pair"
    );

    // ⚑ **AND THE ONE THAT USED TO MERGE — now the sharpest leg of the file.** Until 2026-08-02
    // this block asserted `assert_eq!` on the low-eight anchor write and its message read "if this
    // started separating, the ninth lane landed — retire KEY_NONET_NINTH_LANE_UNBOUND and delete
    // this assertion". It landed; the assertion is inverted rather than deleted, because a pair
    // differing ONLY in bit 255 is the tightest possible probe of the ninth lane and it would be a
    // waste to lose it.
    //
    // Bit 7 of byte 31 is source bit 255, which is bit 23 of lane 8 (`255 - 8*29 = 23`) — the ONLY
    // lane that can see it. So this pair separates iff lane 8 is committed, and nothing else about
    // the write can make it pass.
    let mut c = a;
    c[31] ^= 1 << 7;
    assert_ne!(a, c);
    let lanes_a = canonical_32_to_lanes_9(&a);
    let lanes_c = canonical_32_to_lanes_9(&c);
    let low8 = |l: [BabyBear; 9]| -> [u32; 8] { std::array::from_fn(|i| l[i].as_u32()) };
    assert_eq!(
        low8(lanes_a),
        low8(lanes_c),
        "OLD ADMITS: the retired low-eight write must still merge this pair — it is the claim \
         being refuted, and if it stops holding the refutation is vacuous"
    );
    assert_ne!(
        Faithful9::from_key_lanes9(&a).lanes().map(|f| f.as_u32()),
        Faithful9::from_key_lanes9(&c).lanes().map(|f| f.as_u32()),
        "NEW REJECTS: the nine-lane wall must separate a pair differing only in source bit 255 — \
         if it does not, lane 8 is being dropped somewhere"
    );
    assert_eq!(
        (lanes_a[8].as_u32()) ^ (lanes_c[8].as_u32()),
        1 << 23,
        "…and the separation must be exactly bit 23 of lane 8"
    );
}

// ---------------------------------------------------------------------------
// GATE 3 — the floor arithmetic. IMAGE and COLLISION BOUND are kept apart on purpose.
// ---------------------------------------------------------------------------

/// The number of source bits the DEPLOYED nonet retains, established structurally by
/// [`floor_nonet_retains_all_256_source_bits_as_a_bit_permutation`] rather than asserted.
/// **This is an IMAGE size in bits. It is NOT a security bound** — but at 256 it is the whole
/// source, so for this encoder there is no encoding collision to bound at all.
const NONET_IMAGE_BITS: f64 = 256.0;

/// What the RETIRED octet retained. Kept as a named constant so the comparison below is
/// collision-against-collision and the two numbers cannot be confused for one another.
const RETIRED_OCTET_IMAGE_BITS: f64 = 240.0;

#[test]
fn floor_nonet_retains_all_256_source_bits_as_a_bit_permutation() {
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
            1 => retained.push((b, set[0].0 as u32 * KEY_LANE_BITS as u32 + set[0].1)),
            n => panic!("source bit {b} reached {n} lanes"),
        }
    }

    // (c) NOTHING is lost. This is the assertion that inverted on 2026-08-01: the retired octet
    // discarded the 16 bits `MASKED_BYTES` names, and the nonet discards none.
    assert!(
        discarded.is_empty(),
        "the deployed encoder discards source bits {discarded:?} — an 8-lane pack came back"
    );
    let retired_would_have_discarded: Vec<usize> = MASKED_BYTES
        .iter()
        .flat_map(|byte| [byte * 8 + 6, byte * 8 + 7])
        .collect();
    assert_eq!(
        retired_would_have_discarded.len(),
        16,
        "the retired octet's discarded set, kept for the record"
    );

    // (d) the retained bits land injectively and surjectively on the 8 x 29 + 24 = 256 lane
    // slots. Surjectivity is what says no slot is wasted; injectivity is what says no two source
    // bits share one, which is exactly the property the mask destroyed.
    assert_eq!(retained.len(), 256, "retained source bit count");
    let mut slots: Vec<u32> = retained.iter().map(|(_, s)| *s).collect();
    slots.sort_unstable();
    slots.dedup();
    assert_eq!(
        slots.len(),
        256,
        "two source bits share a lane slot — the map is not a permutation"
    );
    assert_eq!(*slots.first().unwrap(), 0);
    assert_eq!(*slots.last().unwrap(), 255);

    // (e) hence the IMAGE is exactly 2^256, established, not assumed — the source is 32 bytes, so
    // the encoding step loses NOTHING and there is no encoding collision to quantify.
    assert_eq!(NONET_IMAGE_BITS, retained.len() as f64);
    assert!(NONET_IMAGE_BITS > RETIRED_OCTET_IMAGE_BITS);
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

    // ⚑ THE FINDING AS IT STOOD, kept because deleting it would delete the reason nine lanes
    // exist. The retired octet did not even reach that ceiling: it threw away 7.2551 bits of the
    // available image before any encoding question was asked, and its birthday COLLISION bound
    // was 3.63 bits below the law's bar.
    assert!(
        RETIRED_OCTET_IMAGE_BITS < law_octet_image_bits,
        "retired IMAGE {RETIRED_OCTET_IMAGE_BITS} vs available {law_octet_image_bits}"
    );
    let retired_collision_bits = RETIRED_OCTET_IMAGE_BITS / 2.0;
    assert_eq!(retired_collision_bits, 120.0);
    let deficit = law_octet_collision_bound_bits - retired_collision_bits;
    assert!(
        (3.6..3.7).contains(&deficit),
        "the retired octet's shortfall against the law's bar moved: {deficit} bits"
    );

    // ⚑ AND WHY THE REPLACEMENT IS NOT JUST "A BIGGER NUMBER". `law_octet_image_bits` is the
    // most eight lanes could EVER carry, and it is 247.26 against a 256-bit source — so the whole
    // eight-lane family is non-injective before masking is discussed, and "range-check the octet"
    // could never have been the fix. The nonet's image is the source itself.
    assert!(
        law_octet_image_bits < NONET_IMAGE_BITS,
        "if eight lanes ever carried 2^256 the ninth would be unnecessary"
    );
    assert_eq!(NONET_IMAGE_BITS, 256.0);

    // ⚠ SAY WHICH BOUND, FOR THE FIX AS WELL AS FOR THE WOUND. Nine lanes have a CAPACITY of
    // 9 * log2(p) = 278.16 bits. That is the CODOMAIN, not this encoding's image, and quoting it
    // as a security level is the same error in the other direction — the tell is that it exceeds
    // 256, which no map out of 32 bytes can. The honest sentence is: image exactly 2^256,
    // INJECTIVE, so the encoding step contributes NO collision and the binding reduces to the
    // sponge that absorbs the lanes.
    let nine_lane_capacity = 9.0 * log2_p;
    assert!((nine_lane_capacity - 278.162_015_366_926_0).abs() < 1e-9);
    assert!(
        nine_lane_capacity > 256.0,
        "THE TELL: 2^{nine_lane_capacity} exceeds the source, so it is capacity, not image"
    );

    // ⚠ AND THE RESIDUAL, IN THE SAME UNITS, because this file must not be quotable as "closed".
    // The rotated pre-limb write commits lanes 0..=7: 8 * 29 = 232 bits of image, birthday
    // 2^116 — which is BELOW both the law's bar and the retired octet's own 2^120. The encoder is
    // fixed; the anchor is not, and it is not until `NUM_PRE_LIMBS` reaches 187.
    let anchor_image_bits = 8.0 * KEY_LANE_BITS as f64;
    assert_eq!(anchor_image_bits, 232.0);
    let anchor_collision_bits = anchor_image_bits / 2.0;
    assert_eq!(anchor_collision_bits, 116.0);
    assert!(
        anchor_collision_bits < law_octet_collision_bound_bits,
        "the anchor residual is below the law's bar and that is stated, not hidden"
    );
    assert!(
        anchor_collision_bits < retired_collision_bits,
        "and it is four bits below what the RETIRED octet bound at the same site"
    );
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
