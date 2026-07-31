//! **A `fields[0..7]` mod-`p` alias reaches the signed consensus anchor.**
//!
//! ═══ THE WOUND ═══════════════════════════════════════════════════════════════════
//! `cell/src/commitment.rs` welds `fields[0..7]` into the v9 rotated limbs through
//! `Faithful8::from_field_limbs8` — eight lanes, each `u32 % BABYBEAR_P`. And:
//!
//!   * `p = 2013265921`, so `log₂ p = 30.907`: eight lanes carry **247.26 bits** against a 32-byte
//!     field's **256**. No 8-lane encoding of 32 bytes is injective under ANY chunking — pigeonhole.
//!   * `2p = 4026531842 < 2^32`, so EVERY residue has at least two `u32` preimages (`c`, `c + p`).
//!     A colliding sibling is **CONSTRUCTED**, not ground for: add `p` to any 4-byte chunk.
//!
//! ⚑ AND `fields[0..7]` HAVE NO BYTE-EXACT COMPANION. `commitment.rs`'s authority residue walks
//! `st.fields[8..STATE_SLOTS]` and deliberately EXCLUDES `fields[0..8]` ("bound by their own limbs").
//! So these lanes are the only binding, and they reach `TurnReceipt::{pre,post}_state_hash` — the
//! executor's Ed25519 signature, the federation receipt QC, and the `AttestedRoot` quorum.
//!
//! The inversion this exhibits: `fields[8..15]` have **no proof lane at all** (the deployed AIR
//! carries eight, established in `6978fc5ae`) and are bound at BLAKE3 strength; `fields[0..7]` carry
//! every proof obligation and are bound by lanes that collide in O(1). **The attested tier has the
//! breakable commitment.**
//!
//! ═══ WHY THIS TEST EXISTS ════════════════════════════════════════════════════════
//! The repo has a coherent family of non-injectivity exhibits — `split_u64_is_not_injective.rs`,
//! `note_value_aliases_at_2_30.rs`, `effects_hash_fold_and_burn_target_width.rs`,
//! `byte_to_felt_codec_pins.rs`, `dregg-codec/src/limbs.rs` — and `field_limbs8` had **no member**.
//! A documented wound is not a detected one: three separate docstrings claimed this commitment was
//! "faithful" and nothing could contradict them.
//!
//! Built on `note_value_aliases_at_2_30.rs`'s template deliberately, so the two read alike.
//!
//! ═══ ⚑ THIS TOOTH'S MEANING HAS BEEN FLIPPED TWICE, AND SAYING SO IS THE POINT ═══
//!
//! **Flip 1 — "documents the wound" → "pins the hash repair".** It shipped RED, and its docstring
//! said so: *"THIS TEST IS EXPECTED TO FAIL TODAY. It asserts the property we want, not the
//! behaviour we have. It goes green when the field octet migrates onto an injective preimage."*
//! 3 of its 5 assertions failed. Then `field_limbs8` lanes 2..7 moved onto the leading six felts of
//! a Poseidon2 image over an injective 16 × u16-LE preimage, the constructed `c` / `c + p` pair
//! stopped reaching one anchor, and every assertion became a regression pin for THAT repair.
//!
//! **Flip 2 — "pins the hash repair" → "asserts the repair, and the alias pair is now IMPOSSIBLE
//! TO BUILD" (2026-07-30).** The counting argument the header opens with is now discharged rather
//! than merely stated: `metatheory/Dregg2/Circuit/FieldLanes9.lean` carries the NINE-lane encoder
//! with `lanes9ToField_fieldToLanes9` (a total decoder that is a left inverse) and
//! `fieldToLanes9_injective` (its corollary), both `#assert_axioms`-clean, plus
//! `nine_lanes_is_the_minimum` (`P^8 < 2^256 ≤ P^9`). Its Rust twin is
//! `dregg_circuit::effect_vm::field_limbs9`, pinned to the Lean by KAT + round-trip in
//! `circuit/tests/field_lanes9_injective.rs`. **Under that encoder no alias pair EXISTS** — not "is
//! expensive to find", does not exist — so the `c` / `c + p` construction this file is built around
//! cannot be built at all. `the_constructed_alias_pair_cannot_be_built_under_the_nine_lane_encoder`
//! below asserts exactly that, by exhibiting the decoder that recovers both members.
//!
//! ⚠ ═══ AND THE HALF THAT IS NOT DONE, MEASURED RATHER THAN NARRATED ══════════════
//! **The anchor does not run the nine-lane encoder yet.** `cell/src/commitment.rs` and
//! `turn/src/rotation_witness.rs` still call `Faithful8::from_field_limbs8(..).write_lanes(..)` with
//! an `[usize; 8]` index array — the rotated pre-limb layout gives each field EIGHT slots
//! (`4 + i` ‖ `113 + 7·i .. +6`) and there is no ninth column. Allocating one is a
//! `layout_generated.rs` re-emit from the Lean layout manifest plus a VK rotation, which is the AIR
//! lane's work, not an encoder edit.
//!
//! So the split, stated at its real resolution:
//!
//!   * **the ENCODER** is injective, and `field_limbs9` is the deployed name for it;
//!   * **the ANCHOR** still separates this alias family at HASH strength (~2^92.7 collision, the
//!     six Poseidon2 lanes), because the ninth lane — the one that carries the quotient lane 0
//!     discards — is not committed.
//!
//! `the_anchors_separation_of_this_family_is_still_hash_strength_not_injective` MEASURES that
//! instead of asserting it in prose: it shows the deployed octet's pinned pair COLLIDING on the
//! alias, so the reader can see that every bit of the anchor's separation is carried by the hash
//! lanes and none by the pinned pair.
//!
//! Anti-vacuity throughout: the field values are asserted to ROUND-TRIP out of the cell, so an
//! encoder that scrambled everything — and separated the pair by accident — would not pass.

use dregg_cell::commitment_set::CommitmentSet;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::state_commit::{consensus_ctx, consensus_state_commitment};

/// BabyBear's modulus — the reduction the PINNED lanes (0 and 1) perform in both the deployed
/// eight-lane octet and the nine-lane encoder, and therefore the alias generator this file is built
/// around. (`field_limbs9`'s seven FREE lanes are `< 2^28 < p` and never reduce — which is the
/// whole reason the alias stops at them.)
const P: u32 = 2013265921;

fn cell_with(seed: u8) -> Cell {
    Cell::with_balance([seed; 32], [0u8; 32], 1_000)
}

/// The signed anchor over a one-cell ledger whose `fields[slot]` holds `value`.
///
/// Empty accumulators throughout: the note/nullifier axes are exercised by
/// `note_value_aliases_at_2_30.rs`, and holding them fixed isolates the FIELD octet.
fn anchor_with_field(seed: u8, slot: usize, value: [u8; 32]) -> [u8; 32] {
    let mut cell = cell_with(seed);
    cell.state.set_field(slot, value);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let ctx = consensus_ctx(
        &ledger,
        NullifierSet::new().root8(),
        CommitmentSet::new().root8(),
        dregg_turn::rotation_witness::empty_revoked_root_8(),
    );
    consensus_state_commitment(&ledger, &agent, &ctx)
}

/// A 32-byte field value whose LE `u32` chunk at `chunk` holds `v`, zero elsewhere.
///
/// Chunk index `k` is byte range `4k..4k+4`. Chunks 0..6 sit below byte 24, i.e. OUTSIDE the kernel
/// u64 lane that `field_limbs8` lanes 0/1 read — so the only way such a value reaches the
/// commitment at all is through the completion lanes. Under the old encoding chunk `k` rode lane
/// `k + 2` alone, which is exactly what made `c` / `c + p` a one-lane collision; the lanes are a
/// hash of all 32 bytes now.
fn field_with_le_chunk(chunk: usize, v: u32) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[chunk * 4..chunk * 4 + 4].copy_from_slice(&v.to_le_bytes());
    b
}

/// ⚑ **THE ANTI-VACUITY POLE.** "Two values give two anchors" is satisfied by an encoder that
/// destroys information, so every separation asserted below is paired with this: the field value
/// still ROUND-TRIPS out of the cell it was written into, byte for byte.
fn assert_round_trips(slot: usize, value: [u8; 32]) {
    let mut cell = cell_with(0x5A);
    assert!(
        cell.state.set_field(slot, value),
        "set_field({slot}) must take"
    );
    assert_eq!(
        cell.state.fields[slot], value,
        "the field value must survive the round trip — the encoder is a projection of the state, \
         not a rewrite of it"
    );
}

#[test]
fn the_alias_pair_is_genuinely_two_different_field_values() {
    // ANTI-VACUITY, first: if these were the same bytes, every assertion below would be trivial.
    let a = field_with_le_chunk(0, 1);
    let b = field_with_le_chunk(0, 1 + P);
    assert_ne!(a, b, "the alias pair must be two DISTINCT 32-byte values");

    // And they are distinct in the way the encoder is blind to: same residue, different preimage.
    assert_eq!(
        1u32 % P,
        (1u32 + P) % P,
        "the pair must share a lane — that is what makes it an alias"
    );
    // The construction needs no grind: `c` and `c + p` for any `c < 2^32 - p`.
    assert!(
        (1u64 + P as u64) < u32::MAX as u64,
        "c + p must still fit a u32, or this pair does not exist"
    );
}

#[test]
fn a_constructed_field_alias_must_not_reach_the_same_signed_anchor() {
    let honest = field_with_le_chunk(0, 1);
    let alias = field_with_le_chunk(0, 1 + P);

    // ANTI-VACUITY: both values survive the store, so the separation below is the COMMITMENT
    // distinguishing them and not the state having been mangled.
    assert_round_trips(0, honest);
    assert_round_trips(0, alias);

    let anchor_honest = anchor_with_field(0xA1, 0, honest);
    let anchor_alias = anchor_with_field(0xA1, 0, alias);

    assert_ne!(
        anchor_honest, anchor_alias,
        "\n⚑ A CONSTRUCTED `fields[0]` ALIAS PRODUCED A BYTE-IDENTICAL CONSENSUS ANCHOR.\n\n\
         Two DIFFERENT 32-byte field values — chunk 0 holding 1 and 1+p — commit to the same\n\
         `consensus_state_commitment`, which is what the executor signs and the federation QC\n\
         certifies. A receipt-only client cannot tell these two cell states apart.\n\n\
         The pair costs one addition to construct. `fields[0..7]` have no byte-exact companion in\n\
         the commitment (the authority residue starts at `fields[8]`), so these lanes are the only\n\
         binding.\n\n\
         THIS ASSERTION IS A REGRESSION PIN, NOT A WOUND REPORT: it went green when `field_limbs8`\n\
         lanes 2..7 moved onto a Poseidon2 image over an injective 16 x u16-LE preimage. A red here\n\
         means the `u32 % p` chunk encoding came back.\n"
    );
}

#[test]
fn the_alias_reaches_the_anchor_from_every_le_chunk_not_just_the_first() {
    // The aliasing is per-lane, so it is not a quirk of one byte range. Chunks 0..6 are the LE
    // lanes 2..8; walking them shows the attack surface is the whole low 24 bytes.
    for chunk in 0..6usize {
        let honest = field_with_le_chunk(chunk, 7);
        let alias = field_with_le_chunk(chunk, 7 + P);
        assert_ne!(
            honest, alias,
            "chunk {chunk}: the pair must differ in bytes"
        );
        assert_round_trips(1, honest);
        assert_round_trips(1, alias);
        assert_ne!(
            anchor_with_field(0xB2, 1, honest),
            anchor_with_field(0xB2, 1, alias),
            "chunk {chunk}: a constructed alias reached the same signed anchor"
        );
    }
}

#[test]
fn an_honest_field_change_does_move_the_anchor() {
    // THE CONTROL. Without this, the assertions above could pass on a commitment that ignores
    // `fields` entirely — "different values give different anchors" is worthless if NO value
    // change moves it. Two values that do not alias must be distinguished.
    let one = field_with_le_chunk(0, 1);
    let two = field_with_le_chunk(0, 2);
    assert_ne!(
        anchor_with_field(0xC3, 0, one),
        anchor_with_field(0xC3, 0, two),
        "a sub-modulus field change MUST move the anchor, or this test proves nothing"
    );
}

/// ⚑ **THE PRODUCER TWIN, ASSERTED RATHER THAN READ.** `dregg_turn::rotation_witness::produce` and
/// `dregg_cell::commitment::compute_rotated_pre_limbs` both fill the fields octet, and both are
/// documented as byte-identical — but the carrier-octet three-way test
/// (`circuit/tests/effect_vm_rotation_flip.rs`) covers `child_vk8`/`contract_hash8`, not this one.
/// A doc comment is a name, not a proof, and this octet is the one whose encoding just moved.
///
/// The structural reason it holds is that there is ONE encoder and two call sites of it
/// (`Faithful8::from_field_limbs8` at `turn/src/rotation_witness.rs` and `cell/src/commitment.rs`,
/// with the same `[4 + i, 113 + 7·i .. +6]` index array); this asserts the consequence, so a future
/// hand-inlined second body is caught instead of trusted.
#[test]
fn both_producers_fill_the_fields_octet_byte_identically() {
    use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
    use dregg_turn::rotation_witness as rw;

    // A cell whose eight flat fields are all DIFFERENT and none of them small — so a twin that
    // agreed only on zeros, or only on the u64 lane, would not pass.
    let mut cell = cell_with(0xE7);
    for slot in 0..8usize {
        let mut v = [0u8; 32];
        v[0] = 0xF0 ^ slot as u8;
        v[7] = slot as u8;
        v[24..32].copy_from_slice(&(((slot as u64) << 33) | 0x0BAD_F00D).to_be_bytes());
        assert!(cell.state.set_field(slot, v));
    }
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell.clone()).unwrap();

    let z8 = dregg_circuit::heap_root::empty_heap_root_8();
    let revoked = dregg_turn::rotation_witness::empty_revoked_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let w = rw::produce(
        &cell,
        &ledger,
        &z8,
        &z8,
        &revoked,
        &receipt_log,
        &Default::default(),
    );
    let twin = compute_rotated_pre_limbs(
        &cell,
        &V9RotationContext {
            cells_root: rw::cells_root(&ledger),
            nullifier_root: z8,
            commitments_root: z8,
            revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
            iroot: w.iroot,
            material: Default::default(),
        },
    );

    let zero = dregg_circuit::field::BabyBear::ZERO;
    for slot in 0..8usize {
        // lane 0 rides the welded limb `4 + slot`; lanes 1..7 ride `113 + 7·slot .. +6`.
        let positions: Vec<usize> = std::iter::once(4 + slot)
            .chain((0..7).map(|k| 113 + 7 * slot + k))
            .collect();
        // NON-VACUITY: an all-zero octet would let a twin that writes nothing pass.
        assert!(
            positions.iter().any(|&p| w.pre_limbs[p] != zero),
            "slot {slot}: the octet must be non-zero, or this comparison proves nothing"
        );
        for (lane, &pos) in positions.iter().enumerate() {
            assert_eq!(
                w.pre_limbs[pos], twin[pos],
                "producer twins must write fields[{slot}] lane {lane} (limb {pos}) \
                 byte-identically"
            );
        }
    }
}

/// ⚑ **THE PAIR THIS WHOLE FILE IS BUILT AROUND CANNOT BE BUILT ANY MORE.**
///
/// Every other test here asks "do these two values reach the same anchor?" — a question that only
/// makes sense while an alias pair can exist. Under the nine-lane encoder it cannot: Lean's
/// `fieldToLanes9_injective` says no two distinct 32-byte values share a lane vector, so the search
/// space for this attack is EMPTY, not merely expensive.
///
/// Asserted here in the only form a Rust test can honestly take — the LEFT INVERSE, which is what
/// the injectivity is a corollary of. If both members of a would-be alias pair are recovered from
/// their lane vectors, the vectors were never equal.
///
/// The alias family walked below is the full construction this file exhibits: `c` / `c + p` in the
/// pinned u64 window (lanes 0/1) AND in each of the six low LE chunks (the lanes that used to be
/// `u32 % p` chunks). Neither survives.
#[test]
fn the_constructed_alias_pair_cannot_be_built_under_the_nine_lane_encoder() {
    use dregg_circuit::effect_vm::{field_from_lanes9, field_limbs9};

    let mut family: Vec<([u8; 32], [u8; 32])> = Vec::new();
    // (a) the LOW-HALF construction: chunk `k` of bytes 0..24, `c` vs `c + p`.
    for chunk in 0..6usize {
        family.push((
            field_with_le_chunk(chunk, 1),
            field_with_le_chunk(chunk, 1 + P),
        ));
        family.push((
            field_with_le_chunk(chunk, 7),
            field_with_le_chunk(chunk, 7 + P),
        ));
    }
    // (b) the U64-WINDOW construction: `c` and `c + p` big-endian in bytes 28..32. This is the one
    //     lane 0 CANNOT distinguish — it is `BE(b[28..32]) % p` and always will be, because that
    //     lane is welded to the v1 face column and read by `field_to_u64`. The ninth lane is what
    //     separates it.
    for c in [0u32, 1, 7, 0x0800_0000] {
        let (mut lo, mut hi) = ([0u8; 32], [0u8; 32]);
        lo[28..32].copy_from_slice(&c.to_be_bytes());
        hi[28..32].copy_from_slice(&(c + P).to_be_bytes());
        family.push((lo, hi));
    }

    assert!(
        family.len() >= 16,
        "the family must be non-trivial or this test proves nothing"
    );
    for (a, b) in family {
        assert_ne!(a, b, "each pair must be two DISTINCT 32-byte values");
        let (la, lb) = (field_limbs9(&a), field_limbs9(&b));
        // THE ANTI-VACUITY AND THE PROPERTY IN ONE: both members come back out of their lane
        // vectors. A separating-but-scrambling encoder fails this; an aliasing one cannot pass it.
        assert_eq!(field_from_lanes9(&la), a, "{a:02x?} must decode back");
        assert_eq!(field_from_lanes9(&lb), b, "{b:02x?} must decode back");
        assert_ne!(
            la, lb,
            "\n⚑ AN ALIAS PAIR EXISTS UNDER THE NINE-LANE ENCODER.\n\n\
             {a:02x?}\nand\n{b:02x?}\nshare a lane vector. Lean's `fieldToLanes9_injective` says \
             this is impossible, so a red here is a DIVERGENCE BETWEEN THE RUST TWIN AND ITS \
             VERIFIED SPEC — not a newly discovered wound in the encoding.\n"
        );
    }
}

/// ⚠ **THE RESIDUAL, MEASURED.** The anchor is not on the nine-lane encoder: `cell/src/commitment.rs`
/// and `turn/src/rotation_witness.rs` write `Faithful8::from_field_limbs8(..).write_lanes(..)` into
/// EIGHT rotated slots per field (`4 + i` ‖ `113 + 7·i .. +6`), and the layout has no ninth column.
///
/// This test does not restate that in prose — it shows the consequence. The deployed octet's PINNED
/// PAIR (lanes 0 and 1, the kernel u64 window, byte-identical across both encoders) COLLIDES on the
/// u64-window alias. So the anchor's separation of this family, which
/// `a_constructed_field_alias_must_not_reach_the_same_signed_anchor` confirms holds, is carried
/// ENTIRELY by the six Poseidon2 completion lanes: hash strength (~2^92.7 collision), not the
/// injection.
///
/// A green here is not good news; it is the honest size of what is left. It turns red — correctly,
/// and loudly — the day the fields octet is re-laid onto nine committed lanes, at which point this
/// test is deleted and the anchor inherits the injection.
#[test]
fn the_anchors_separation_of_this_family_is_still_hash_strength_not_injective() {
    use dregg_circuit::effect_vm::{field_limbs8, field_limbs9};

    let (mut honest, mut sibling) = ([0u8; 32], [0u8; 32]);
    honest[28..32].copy_from_slice(&7u32.to_be_bytes());
    sibling[28..32].copy_from_slice(&(7u32 + P).to_be_bytes());
    assert_ne!(honest, sibling);

    let (o8, s8) = (field_limbs8(&honest), field_limbs8(&sibling));
    let (o9, s9) = (field_limbs9(&honest), field_limbs9(&sibling));

    // The pinned pair is the SAME two lanes in both encoders — that is the deployed ABI, and it is
    // exactly why the ninth lane had to exist rather than lane 0 being re-chunked.
    assert_eq!(o8[0], o9[0], "lane 0 is byte-identical across the encoders");
    assert_eq!(o8[1], o9[1], "lane 1 is byte-identical across the encoders");

    // ⚑ THE MEASUREMENT: on the alias, the committed pinned pair carries NO separation at all.
    assert_eq!(
        (o8[0], o8[1]),
        (s8[0], s8[1]),
        "the u64-window alias collides in the deployed pinned pair — every bit of the anchor's \
         separation is the hash lanes'"
    );

    // And what the ninth lane would have added, if it were committed: the quotient, in lane 8.
    assert_ne!(
        o9[8], s9[8],
        "the UNCOMMITTED ninth lane is what distinguishes the pair by construction rather than by \
         hash strength"
    );
    assert_ne!(o9, s9, "the nine-lane vectors separate");

    // The anchor does separate them today — via the hash lanes. Stated so the residual is not
    // mistaken for an open forgery.
    assert_ne!(
        anchor_with_field(0xE5, 0, honest),
        anchor_with_field(0xE5, 0, sibling),
        "the anchor must still separate the pair at hash strength"
    );
}

#[test]
fn fields_8_and_above_are_already_byte_exact_which_is_the_inversion() {
    // The contrast that makes the finding legible: the slots with NO proof lane are bound at
    // BLAKE3 strength through the authority residue, so an alias pair there is already
    // distinguished today. If this ever fails, the residue stopped covering `fields[8..]` and that
    // is a separate, larger regression.
    let honest = field_with_le_chunk(0, 1);
    let alias = field_with_le_chunk(0, 1 + P);
    assert_ne!(
        anchor_with_field(0xD4, 8, honest),
        anchor_with_field(0xD4, 8, alias),
        "fields[8] is bound by RAW BYTES into the authority residue and must already distinguish \
         an alias pair — the attested tier (fields[0..7]) is the one with the weaker commitment"
    );
}
