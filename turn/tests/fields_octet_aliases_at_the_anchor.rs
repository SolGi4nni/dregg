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
//! ═══ ⚑ THIS TOOTH'S MEANING WAS FLIPPED, AND SAYING SO IS THE POINT ══════════════
//! It shipped RED, and its docstring said so: *"THIS TEST IS EXPECTED TO FAIL TODAY. It asserts the
//! property we want, not the behaviour we have. It goes green when the field octet migrates onto an
//! injective preimage."* 3 of its 5 assertions failed.
//!
//! The octet migrated. `field_limbs8` lanes 2..7 now carry the leading six felts of a Poseidon2
//! image over an injective 16 × u16-LE preimage of the whole 32-byte value, so the constructed
//! `c` / `c + p` pair no longer reaches one anchor. **Every assertion below is now a REGRESSION PIN
//! for that repair, not a statement of a wound.** A red here means the chunk encoding came back.
//!
//! ⚠ **AND THE WOUND IT NAMED IS NOT FULLY CLOSED.** Eight lanes carry 247.26 bits against 256, so
//! the octet is still NOT injective — the repair converted a CONSTRUCTED alias into a hash-strength
//! one and did not deliver injectivity. Injectivity needs a ninth lane (a descriptor re-emit, a VK
//! rotation and a re-genesis). Nothing here may be described as "faithful".
//!
//! Anti-vacuity throughout: the field values are asserted to ROUND-TRIP out of the cell, so an
//! encoder that scrambled everything — and separated the pair by accident — would not pass.

use dregg_cell::commitment_set::CommitmentSet;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::state_commit::{consensus_ctx, consensus_state_commitment};

/// BabyBear's modulus — the reduction every lane of `field_limbs8` performs.
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
