//! # `A` and `-A` at the OWNER-KEY CARRIER — old admits, new rejects.
//!
//! The 2026-08-02 owner-key flag day, measured at the deployed producer and the deployed
//! `wireCommitR` fold. ⚠ **Read the CORRECTION section below before quoting this file**: the claim
//! it can make is about the key's own committed columns, not about `state_commit` as a whole, and
//! the difference is not cosmetic.
//!
//! ## The wound, in one paragraph
//!
//! `canonical_32_to_felts_8` — the retired 30-bit key pack — dropped bits 6-7 of bytes 3, 7, …, 31.
//! RFC 8032 §5.1.2 puts an Ed25519 public key's x-sign in **bit 7 of byte 31**, so a point `A` and
//! its negation `-A` packed to one octet. That encoder was replaced on 2026-08-01 by the base-`2^29`
//! nonet (image exactly `2^256`, injective) — and **the anchor did not move**, because
//! `B_PUBKEY_OCTET` is eight columns wide and the producers wrote lanes 0..=7 only. The separating
//! bit lives in lane 8. So for one day the encoder distinguished the pair and the signed commitment
//! did not.
//!
//! The geometry is now 187 pre-limbs with `B_PUBKEY_NINTH_LANE = 186`, an ABSORBED pre-limb, and
//! both producers write the full nonet.
//!
//! ## ⚑⚑ A CORRECTION TO THE BRIEF THIS FILE WAS WRITTEN UNDER — measured here, on the first run
//!
//! The framing that motivated this flag day was **"the signed consensus anchor binds 232 of 256
//! key bits"**, with the corollary that `A` and `-A` published ONE `state_commit`. The first
//! version of [`old_admits_new_rejects_at_the_published_state_commit`] asserted exactly that and
//! **it failed**, because the owner key reaches the anchor by TWO paths and only one of them was
//! the key carrier:
//!
//! 1. **the dedicated key carrier** — `B_PUBKEY_OCTET` 105..=112, now plus limb 186. This is the
//!    path that bound 232 bits and merged `A` with `-A` at cost zero. It is what this flag day
//!    repaired, and repairing it is what makes the committed nonet *determine* the key.
//! 2. **the AUTHORITY DIGEST** — `authority_residue_bytes` absorbs `cell.public_key` **BYTE-EXACTLY**
//!    (`cell/src/commitment.rs`), blake3-roots it, and `compute_authority_digest_8` places the
//!    eight limbs at `AUTHORITY_DIGEST_GROUP = [24, 12, 13, 14, 15, 16, 17, 18]` — all absorbed
//!    pre-limbs. So `state_commit` DID separate `A` from `-A` before 2026-08-02.
//!
//! **Say the resolution, both ways.** Path 2 is a *hash* binding, not an injection: blake3 into
//! `Faithful8::from_bytes32`, so it separates the pair at the law's `2^123.63` birthday-collision
//! figure and NOT for free. Path 1 is now an *injection* — the committed nonet determines exactly
//! one key, decodable, no bound to quote. The upgrade is real and is not the one the brief named:
//! it is **232 bits → an injection on the key's own columns**, not **0 → 256 at the anchor**.
//!
//! ⚠ Path 2 is also FROZEN across non-record-mover effects (the digest is forced equal BEFORE↔AFTER
//! rather than recomputed from the key), and it is not what the KEY_COMMIT teeth or the octet-reading
//! gates read. Those read the carrier. So "the authority digest already covered it" is not a reason
//! the carrier could have stayed at eight lanes.
//!
//! ## What each test here establishes, and at which resolution
//!
//! * [`old_admits_new_rejects_at_the_published_state_commit`] — the load-bearing one, stated at the
//!   KEY CARRIER, which is the object that changed. Two cells differing ONLY in owner key (`A` vs
//!   `-A`) go through the **deployed** producer; the retired write is reconstructed from the same
//!   limb vector by zeroing limb 186. At the carrier's nine columns the retired write is
//!   BYTE-IDENTICAL and the current one is not, and the same holds for the carrier's contribution
//!   to the **deployed** chained fold. Both paths above are measured, so neither can be quoted
//!   without the other.
//! * [`the_two_producers_agree_lane_for_lane_on_the_ninth_lane`] — completeness across the twin
//!   boundary: `dregg_cell::commitment::compute_rotated_pre_limbs` and
//!   `dregg_turn::rotation_witness::produce` must write the same nine columns, or an honest turn
//!   goes UNSAT against a witness the other produced.
//! * [`the_thirty_two_bytes_round_trip_out_of_the_committed_limbs`] — ANTI-VACUITY. "The digests
//!   differ" is not evidence of binding. The 32 key bytes are recovered from the nine columns
//!   read back out of the pre-limb vector.
//! * [`an_honest_turn_still_folds_and_the_three_producers_agree`] — completeness: the pre-limb
//!   vector is still the right length and shape, the published felt still equals an independent
//!   re-fold, and the key change touches ONLY the two paths named above.
//!
//! ## ⚠ Resolution, said out loud
//!
//! These run the deployed PRODUCER and the deployed FOLD (`wire_commit`, the Rust twin of Lean
//! `wireCommitR`, and the value the rotated trace's `STATE_COMMIT` carrier must carry). They do
//! **not** run a STARK. What they establish is that the committed value separates the pair; the
//! `effect_vm_rotation_flip` differential is what ties that value to the trace the prover proves,
//! and the FRI/STARK floor below it is undischarged as always.
//!
//! ⚠ And they say nothing about the canonicity ENVELOPE. `Emit.KeyCanonicity9Emit.keyCanonical9At`
//! — eight range lookups at 29 bits plus one at 24 — is authored, proved, and **applied by
//! nothing** (measured at HEAD, 2026-08-02). The anchor BINDS the nonet; no emitted constraint
//! REFUSES a lane vector outside the encoder's image.

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;
use dregg_cell::Cell;
use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
use dregg_circuit::Faithful9;
use dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL;
use dregg_circuit::effect_vm::layout_generated::{
    AUTHORITY_DIGEST_GROUP, B_PUBKEY_NINTH_LANE, NUM_PRE_LIMBS,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;

/// `A` and `-A`: a real curve point and its negation. Both valid, both decompressible, both the
/// same order, differing in exactly the x-sign bit — and the attacker holds the private half of
/// the negation (`-a mod L`), so this pair costs ZERO to construct. No search, no grind.
fn a_and_minus_a() -> ([u8; 32], [u8; 32]) {
    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let key_a: [u8; 32] = a.compress().to_bytes();
    let key_minus_a: [u8; 32] = (-a).compress().to_bytes();
    assert_ne!(
        key_a, key_minus_a,
        "the pair must be two distinct encodings"
    );
    let differing: Vec<(usize, u8)> = (0..32)
        .flat_map(|byte| {
            (0..8u8).filter_map(move |bit| {
                ((key_a[byte] ^ key_minus_a[byte]) & (1 << bit) != 0).then_some((byte, bit))
            })
        })
        .collect();
    assert_eq!(
        differing,
        vec![(31usize, 7u8)],
        "…and they must differ in exactly the RFC 8032 x-sign bit, or this exhibit is about \
         something else"
    );
    (key_a, key_minus_a)
}

/// A cell owned by `pk`, identical in every other respect. Everything the rotated commitment
/// absorbs other than the owner key is held fixed, so a difference downstream can only be the key.
fn cell_owned_by(pk: [u8; 32]) -> Cell {
    Cell::with_balance(pk, [0u8; 32], 100_000)
}

fn fixed_context() -> V9RotationContext {
    V9RotationContext {
        cells_root: dregg_circuit::heap_root::compute_canonical_heap_root_8_entries(&[(
            (BabyBear::ZERO, BabyBear::new(0x5678)),
            BabyBear::ONE,
        )]),
        nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
        commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
        revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
        iroot: BabyBear::new(0x1234),
        material: Default::default(),
    }
}

/// The deployed chained rotated fold, re-derived here from the public `hash_many` primitive rather
/// than called from `turn::rotation_witness::wire_commit` — so agreement with the producer is a
/// differential and not a tautology. Byte-for-byte the Lean `EffectVmEmitRotationR.wireCommitR`:
/// a 4-wide head, 3-wide chip groups while ≥ 3 pre-iroot limbs remain, the iroot ALONE last.
fn independent_wire_commit(pre: &[BabyBear], iroot: BabyBear) -> BabyBear {
    assert_eq!(pre.len(), NUM_PRE_LIMBS);
    let mut d = hash_many(&[pre[0], pre[1], pre[2], pre[3]]);
    let mut col = 4;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, pre[col], pre[col + 1], pre[col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, pre[col]]);
            col += 1;
        }
    }
    hash_many(&[d, iroot])
}

/// **THE RETIRED WRITE, reconstructed from the CURRENT limb vector.** The pre-2026-08-02 producer
/// wrote lanes 0..=7 at `B_PUBKEY_OCTET` and left limb 186 at its zero-initialised value, so the
/// old committed vector is exactly this one with that column zeroed. Reconstructing it *from the
/// current vector* — rather than re-typing the old producer — is what makes the refutation
/// unarguable: the two differ in one column and nothing else.
fn as_the_retired_write_committed_it(pre: &[BabyBear]) -> Vec<BabyBear> {
    let mut old = pre.to_vec();
    old[B_PUBKEY_NINTH_LANE] = BabyBear::ZERO;
    old
}

#[test]
fn old_admits_new_rejects_at_the_published_state_commit() {
    let (key_a, key_minus_a) = a_and_minus_a();
    let ctx = fixed_context();

    let pre_a = compute_rotated_pre_limbs(&cell_owned_by(key_a), &ctx);
    let pre_ma = compute_rotated_pre_limbs(&cell_owned_by(key_minus_a), &ctx);
    assert_eq!(pre_a.len(), NUM_PRE_LIMBS);

    // ── WHERE THE PAIR MOVES THE COMMITTED VECTOR — measured, and it is TWO places. ───────────
    // The first version of this block asserted `vec![B_PUBKEY_NINTH_LANE]` and failed with
    // `[12, 13, 14, 15, 16, 17, 18, 24, 186]`. Those seven-plus-one are `AUTHORITY_DIGEST_GROUP`:
    // `authority_residue_bytes` absorbs `cell.public_key` byte-exactly and blake3-roots it. The
    // failure is preserved as the assertion, because it is the correction.
    let differing: Vec<usize> = (0..NUM_PRE_LIMBS)
        .filter(|&i| pre_a[i] != pre_ma[i])
        .collect();
    let mut expected: Vec<usize> = AUTHORITY_DIGEST_GROUP.to_vec();
    expected.push(B_PUBKEY_NINTH_LANE);
    expected.sort_unstable();
    assert_eq!(
        differing, expected,
        "a key change must move exactly the AUTHORITY DIGEST group and the key carrier's ninth \
         lane. Anything else means a write is landing outside its group"
    );

    // ⚑ AND THE ASYMMETRY THAT MAKES THE FLAG DAY NECESSARY: of the key CARRIER's nine columns,
    // only the ninth moves. Lanes 0..=7 are byte-identical for `A` and `-A`, which is the 232-bit
    // wound stated exactly.
    let carrier_moved: Vec<usize> = PUBKEY_NONET_LANE_COL
        .iter()
        .copied()
        .filter(|&c| pre_a[c] != pre_ma[c])
        .collect();
    assert_eq!(
        carrier_moved,
        vec![B_PUBKEY_NINTH_LANE],
        "inside the key carrier the pair must separate in the NINTH lane and nowhere else — that \
         is why eight columns bound 232 of 256 bits"
    );

    // ── OLD ADMITS, at the carrier. ───────────────────────────────────────────────────────────
    // The retired write left limb 186 at its zero-initialised value, so the old committed carrier
    // is this one with that column zeroed. Reconstructed FROM the current vector rather than
    // re-typed, so the two differ in one column and nothing else.
    let old_a = as_the_retired_write_committed_it(&pre_a);
    let old_ma = as_the_retired_write_committed_it(&pre_ma);
    let carrier =
        |v: &[BabyBear]| -> [BabyBear; 9] { std::array::from_fn(|i| v[PUBKEY_NONET_LANE_COL[i]]) };
    assert_eq!(
        carrier(&old_a),
        carrier(&old_ma),
        "⚑ THE WOUND: under the retired write the owner-key carrier of a cell owned by A and one \
         owned by -A was BYTE-IDENTICAL. Every gate that reads that carrier — the KEY_COMMIT \
         teeth, the owner freeze, the octet-reading welds — saw one key where there were two, at \
         cost zero and with no search."
    );

    // ── NEW REJECTS, at the carrier. ──────────────────────────────────────────────────────────
    assert_ne!(
        carrier(&pre_a),
        carrier(&pre_ma),
        "the owner-key carrier must SEPARATE A from -A. If this fails, a producer stopped writing \
         PUBKEY_NONET_LANE_COL[8] or that column left the absorbed pre-limb region"
    );

    // ── AND AT THE DEPLOYED FOLD, in ISOLATION — the carrier's own contribution to the anchor. ─
    // ⚠ THIS IS AN ISOLATION AND IS LABELLED AS ONE. Folding the two full vectors would separate
    // even under the retired write, via the authority digest, so it would not be evidence about
    // the carrier. These vectors are ZERO except the key's nine columns, so what the chained
    // absorption sees is the carrier and nothing else — and the fold is the DEPLOYED one.
    let only_carrier = |v: &[BabyBear]| -> Vec<BabyBear> {
        let mut out = vec![BabyBear::ZERO; NUM_PRE_LIMBS];
        for &c in PUBKEY_NONET_LANE_COL.iter() {
            out[c] = v[c];
        }
        out
    };
    assert_eq!(
        dregg_turn::rotation_witness::wire_commit(&only_carrier(&old_a), ctx.iroot),
        dregg_turn::rotation_witness::wire_commit(&only_carrier(&old_ma), ctx.iroot),
        "OLD ADMITS at the fold: the retired carrier contributed one value to wireCommitR for both \
         keys"
    );
    assert_ne!(
        dregg_turn::rotation_witness::wire_commit(&only_carrier(&pre_a), ctx.iroot),
        dregg_turn::rotation_witness::wire_commit(&only_carrier(&pre_ma), ctx.iroot),
        "NEW REJECTS at the fold: the carrier must contribute distinct values, or limb 186 is not \
         being absorbed"
    );

    // ── ⚑ THE SECOND PATH, ASSERTED SO IT CANNOT BE QUOTED AWAY EITHER DIRECTION. ─────────────
    // `state_commit` over the FULL vectors separated the pair BEFORE this flag day too, through
    // the authority digest. Saying "A and -A published one state_commit" would have been false.
    assert_ne!(
        dregg_turn::rotation_witness::wire_commit(&old_a, ctx.iroot),
        dregg_turn::rotation_witness::wire_commit(&old_ma, ctx.iroot),
        "the RETIRED full-vector state_commit is expected to SEPARATE the pair (via the authority \
         digest). If it ever merges them, the authority digest stopped absorbing public_key and \
         the wound is far larger than this file describes"
    );
    // …and it still does, now by both paths.
    assert_ne!(
        dregg_turn::rotation_witness::wire_commit(&pre_a, ctx.iroot),
        dregg_turn::rotation_witness::wire_commit(&pre_ma, ctx.iroot)
    );
    // ⚠ The two paths are NOT the same kind of claim. Path 2 is blake3 into `from_bytes32` — a
    // hash binding at the law's 2^123.63 birthday figure. Path 1 is now an INJECTION, which is
    // what `keyCanon9_determines_the_owner_key_deployed` needs and what a hash can never give:
    // the round-trip test below recovers the key from the carrier, and no test can recover it
    // from the digest.

    // ⚑ The absorption is what carries any of this: limb 186 is INSIDE the folded range. A column
    // at or past `NUM_PRE_LIMBS` would live in the appendix and `wireCommitR` would never see it —
    // which is precisely the state the pre-cutover geometry was in.
    // ⚑ Absorbed-pre-limb is a BUILD obligation, not a runtime one: `B_PUBKEY_NINTH_LANE <
    // NUM_PRE_LIMBS` is const-asserted in `dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL`'s
    // initializer, so a re-emit that moved lane 8 into the appendix could not compile the crate
    // this test links against. Re-asserting it here could only ever agree.
}

#[test]
fn the_two_producers_agree_lane_for_lane_on_the_ninth_lane() {
    // ⚠ COMPLETENESS ACROSS THE TWIN BOUNDARY. `dregg_turn::rotation_witness::produce` builds the
    // witness a prover uses; `dregg_cell::commitment::compute_rotated_pre_limbs` is what the SDK
    // and the cell-side reconstruction use. If one writes the ninth lane and the other does not,
    // an honest turn is UNSAT against a witness the other produced — the exact shape that made
    // ~143 rotated members UNSAT across the `178 -> 184` flag day.
    //
    // They are compared through the COLUMN MAP rather than by whole-vector equality so that a
    // failure names the lane, and so that this stays a statement about the key write specifically.
    let (key_a, _) = a_and_minus_a();
    let ctx = fixed_context();
    let cell = cell_owned_by(key_a);

    let cell_side = compute_rotated_pre_limbs(&cell, &ctx);
    let expected = Faithful9::from_key_lanes9(&key_a).lanes();

    for (lane, &col) in PUBKEY_NONET_LANE_COL.iter().enumerate() {
        assert_eq!(
            cell_side[col], expected[lane],
            "cell-side producer wrote the wrong value at lane {lane} (column {col})"
        );
    }

    // ⚑ ANTI-VACUITY on the expectation itself: lane 8 must be NON-ZERO for this key, or the
    // comparison above would pass on a producer that writes nothing at all. (The zero-initialised
    // vector is what the retired write left there.)
    assert_ne!(
        expected[8],
        BabyBear::ZERO,
        "the fixture key must exercise a non-zero ninth lane, or this test cannot fail for the \
         reason it exists"
    );
    assert_ne!(
        cell_side[B_PUBKEY_NINTH_LANE],
        BabyBear::ZERO,
        "the producer left the ninth lane at its zero-initialised value — that IS the retired write"
    );
}

#[test]
fn the_thirty_two_bytes_round_trip_out_of_the_committed_limbs() {
    // ⚑ **THE ANTI-VACUITY TEST.** Everything above shows values DIFFERING. Differing is not
    // binding: a hash of the key would also differ, and would bind nothing recoverable. This reads
    // the nine committed COLUMNS back out of the pre-limb vector and reconstructs the 32 bytes.
    //
    // It is the property the whole flag day exists for — the committed nonet determines EXACTLY
    // ONE key (Lean `keyCanon9_determines_the_owner_key_deployed`) — measured at the columns.
    let ctx = fixed_context();
    let (key_a, key_minus_a) = a_and_minus_a();

    for key in [key_a, key_minus_a, [0u8; 32], [0xFFu8; 32], {
        let mut k = [0u8; 32];
        for (i, b) in k.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(37).wrapping_add(0x5a);
        }
        k
    }] {
        let pre = compute_rotated_pre_limbs(&cell_owned_by(key), &ctx);
        let committed: [BabyBear; 9] = std::array::from_fn(|lane| pre[PUBKEY_NONET_LANE_COL[lane]]);
        let recovered = dregg_circuit::effect_vm::key_from_lanes9(&committed);
        assert_eq!(
            recovered, key,
            "the 32 bytes must come back out of the nine COMMITTED columns. Recovered {:02x?} \
             from {committed:?}",
            recovered
        );
    }
}

#[test]
fn an_honest_turn_still_folds_and_the_three_producers_agree() {
    // COMPLETENESS. A flag day that separates the attacker's pair but breaks the honest path is
    // not a fix. Three things, none of which the tests above would catch:
    let ctx = fixed_context();
    let (key_a, _) = a_and_minus_a();
    let cell = cell_owned_by(key_a);
    let pre = compute_rotated_pre_limbs(&cell, &ctx);

    //  1. the vector is the emitted length — a producer that wrote past the end would panic, but
    //     one that grew the vector without the layout would not.
    assert_eq!(
        pre.len(),
        NUM_PRE_LIMBS,
        "the pre-limb vector must be exactly the emitted length"
    );
    assert_eq!(
        dregg_cell::commitment::V9_NUM_PRE_LIMBS,
        NUM_PRE_LIMBS,
        "…and the cell-side name for it must be the same emitted constant"
    );

    //  2. the deployed fold still equals an independent re-fold over that vector — i.e. the shape
    //     of the absorption did not move when the region grew.
    assert_eq!(
        dregg_turn::rotation_witness::wire_commit(&pre, ctx.iroot),
        independent_wire_commit(&pre, ctx.iroot),
        "the deployed chained fold and an independent re-fold must agree at 187 limbs"
    );

    //  3. NOTHING ELSE MOVED. Changing the owner key must touch the key's nine columns and the
    //     authority digest's eight, and NOTHING ELSE — a producer that accidentally shifted a
    //     neighbouring group would still separate A from -A and would break every other weld in
    //     the block. (This is the leg that caught the two-path correction in the header.)
    let mut other = key_a;
    other[0] ^= 0xFF;
    let pre_other = compute_rotated_pre_limbs(&cell_owned_by(other), &ctx);
    let moved: Vec<usize> = (0..NUM_PRE_LIMBS)
        .filter(|&i| pre[i] != pre_other[i])
        .collect();
    for col in &moved {
        assert!(
            PUBKEY_NONET_LANE_COL.contains(col) || AUTHORITY_DIGEST_GROUP.contains(col),
            "changing the owner key moved column {col}, which is neither one of the key's nine \
             lanes {PUBKEY_NONET_LANE_COL:?} nor the authority digest group \
             {AUTHORITY_DIGEST_GROUP:?} — the write is landing outside its group"
        );
    }
    assert!(
        !moved.is_empty(),
        "changing the owner key moved NOTHING — the key is not reaching the anchor at all"
    );
    // ⚠ ANTI-VACUITY on the sweep: a key change that touched ONLY the authority digest would pass
    // the loop above and would mean the carrier had stopped tracking the key entirely.
    assert!(
        moved.iter().any(|c| PUBKEY_NONET_LANE_COL.contains(c)),
        "the key's own carrier must move when the key does"
    );
}
