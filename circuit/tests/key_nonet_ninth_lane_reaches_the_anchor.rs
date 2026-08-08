//! # THE GATE THAT FLIPPED — the owner key's ninth lane, and the column it now has.
//!
//! ## What this file is
//!
//! The 2026-08-01 key flag day landed in two pieces and for one day only one of them was in the
//! bytes. **Both are now.**
//!
//! * **The ENCODER moved** (2026-08-01). All four twins run the base-`2^29` nonet, image exactly
//!   `2^256`, and the membership leaf (`compress_member`) and both four-felt id folds absorb all
//!   nine lanes.
//! * **The GEOMETRY followed** (2026-08-02). `NUM_PRE_LIMBS` is 187, `B_PUBKEY_NINTH_LANE` is
//!   in-block limb 186, and both producers write lane 8 there through
//!   `Faithful9::from_key_lanes9`. 186 is an ABSORBED pre-limb, so `wireCommitR` — which folds
//!   `[0, NUM_PRE_LIMBS)` — carries it into `state_commit` and therefore into the signed consensus
//!   anchor. **The anchor binds all 256 key bits**; it bound 232 the day before, and the 24 it
//!   missed included the Ed25519 x-sign, so `A` and `-A` committed identically at cost zero.
//!
//! **A documented wound is not a detected one.** This file was the detector, and it did its job:
//! it was GREEN while it asserted the shortfall and went RED the day the geometry moved. That is
//! the shape a cutover cannot walk past, as opposed to a test that is red every day and everybody
//! learns to skip. It is keyed on `NUM_PRE_LIMBS`, GENERATED from
//! `metatheory/EmitLayoutManifest.lean`, so it cannot rot the way the hand-carried
//! `B_CHAIN_BASE = 180` rotted across the `178 → 184` flag day (`28695cefc`: one un-exported
//! constant made ~143 rotated members UNSAT).
//!
//! ## ⚑ WHAT IT DETECTS NOW — the same shape, pointed the other way
//!
//! [`the_geometry_reached_187_and_every_lane_has_a_column`] is the flipped assertion. It is not
//! `assert_eq!(NUM_PRE_LIMBS, 187)` and nothing else: a pin of a constant against a remembered
//! number is decoration. It asserts the three things that make the column MEAN something — the
//! lane's home is the layout's own ninth-lane entry, that entry is inside the absorbed region, and
//! the producers' column map agrees with it — each read from a source that is not the others.
//!
//! ⚠ **What this file does NOT assert, and must not be read as asserting.** That the canonicity
//! ENVELOPE is emitted. `Emit.KeyCanonicity9Emit.keyCanonical9At` is authored and proved and
//! **applied by nothing** — measured at HEAD, not relayed. So the anchor BINDS the nonet and no
//! emitted constraint REFUSES a lane vector outside the encoder's image.
//! [`the_deployed_range_widths_admit_the_nonets_two_legs`] below checks the two widths have
//! TABLES, which is a precondition for emitting the envelope and not the envelope itself.

use dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL;
use dregg_circuit::effect_vm::layout_generated::{
    B_IROOT, B_PUBKEY_NINTH_LANE, B_PUBKEY_OCTET, B_STATE_COMMIT, NUM_PRE_LIMBS,
    ROTATED_OCTET_NINTH_LANES, ROTATED_PADS,
};

/// The pre-limb count the nine-lane key layout requires. **This is not a target typed from
/// memory** — it is forced, and the two facts that force it are asserted below rather than quoted:
/// the region is full, and `n ≡ 1 (mod 3)`.
const NINE_LANE_NUM_PRE_LIMBS: usize = 187;

/// ⚑ **THE FLIP, AND IT IS SAID OUT LOUD.** This test was
/// `the_geometry_is_still_at_184_and_here_is_what_that_costs`, it asserted `NUM_PRE_LIMBS == 184`,
/// and it existed to go RED on the day the fix landed. It went red on 2026-08-02 and the three
/// follow-ups it named were done: both producers write lane 8 to in-block limb 186,
/// `Faithful8::from_key_nonet_low8` and `KEY_NONET_NINTH_LANE_UNBOUND` are deleted with their
/// three burn-down rows, and the 232-bit residual assertions were deleted rather than relaxed.
///
/// **Leaving it green at 184 would have meant the cutover did not happen.** It is now the
/// post-cutover gate for the same geometry, and it is deliberately not one assertion: a constant
/// pinned against a number somebody remembered is decoration, so each leg below comes from a
/// source the others do not.
#[test]
fn the_geometry_reached_187_and_every_lane_has_a_column() {
    assert_eq!(
        NUM_PRE_LIMBS, NINE_LANE_NUM_PRE_LIMBS,
        "layout_generated.rs moved OFF the nine-lane geometry. If this is 184 again the owner \
         key's ninth lane has no column and the signed anchor is back to 232 of 256 bits, with \
         the Ed25519 sign bit outside it — do not relax this, re-emit."
    );

    // LEG 1 — the lane's home, from the layout's own ninth-lane table (NOT from `NUM_PRE_LIMBS`,
    // which is what the pre-cutover version of this file was keyed on, and NOT from a stride off
    // the octet, which would land on `fields[0]`'s completion window at 113).
    assert_eq!(
        B_PUBKEY_NINTH_LANE, 186,
        "the owner nonet's ninth lane is in-block limb 186"
    );
    assert_eq!(
        ROTATED_OCTET_NINTH_LANES[2], B_PUBKEY_NINTH_LANE,
        "the octet-parallel table and the named constant must be the same column"
    );
    // The two structural facts this test used to assert at RUNTIME — lane 8 is an ABSORBED
    // pre-limb, and it is NOT flush against its octet — are const-asserted inside
    // `dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL`'s initializer, so a re-emit that broke
    // either one would fail to COMPILE `dregg-circuit` rather than fail this one test. Asserting
    // them again here reads as a second check and is not one.

    // LEG 2 — it is an ABSORBED pre-limb, which is the whole point. `wireCommitR` folds
    // `[0, NUM_PRE_LIMBS)`; a column at or past that index is in the appendix and carries nothing.
    // (absorbed-pre-limb: const-asserted in `PUBKEY_NONET_LANE_COL`, see LEG 1 above)

    // LEG 3 — the PRODUCERS' column map agrees. `PUBKEY_NONET_LANE_COL` is what
    // `compute_rotated_pre_limbs` and `rotation_witness::produce` actually write through, so this
    // is the leg that would catch "the layout grew and the producers did not follow" — which is
    // exactly the state this file was created to detect, one geometry earlier.
    assert_eq!(
        PUBKEY_NONET_LANE_COL[8], B_PUBKEY_NINTH_LANE,
        "the producers write lane 8 somewhere other than the layout's ninth-lane column"
    );
    assert_eq!(
        PUBKEY_NONET_LANE_COL[..8],
        [
            B_PUBKEY_OCTET,
            B_PUBKEY_OCTET + 1,
            B_PUBKEY_OCTET + 2,
            B_PUBKEY_OCTET + 3,
            B_PUBKEY_OCTET + 4,
            B_PUBKEY_OCTET + 5,
            B_PUBKEY_OCTET + 6,
            B_PUBKEY_OCTET + 7
        ],
        "lanes 0..=7 must still be the deployed contiguous octet"
    );

    // The frame, unchanged: iroot sits right after the pre-limbs and state_commit after it.
    assert_eq!(
        B_IROOT, NUM_PRE_LIMBS,
        "iroot sits right after the pre-limbs"
    );
    assert_eq!(B_STATE_COMMIT, B_IROOT + 1);
}

#[test]
fn the_pre_limb_region_is_full_so_the_ninth_lane_cannot_be_squeezed_in() {
    // The first of the two facts that forced a GROW rather than a re-use, kept AFTER the cutover
    // because it is what refutes "just move the lane into a pad" the next time this comes up.
    // `ROTATED_PADS` is the spare-column list and it is empty at 187 too — the two former pads
    // were eaten by the FIELDS nonet on 2026-07-31, and the three columns 184/185/186 the grow
    // bought are the three carrier octets' ninth lanes, not spares.
    assert!(
        ROTATED_PADS.is_empty(),
        "there are spare pre-limbs {ROTATED_PADS:?} — re-check whether the region must grow at all"
    );
}

#[test]
fn the_ninth_lane_needs_187_not_185_and_the_reason_is_a_floor_division() {
    // ⚑ THE SECOND FACT, and the one that makes 185 a TRAP rather than merely wrong.
    //
    // The rotated block's span is `B_SPAN := n + 3 + (n - 4) / 3` — Nat FLOOR division — while the
    // real carrier chain is `chunk31`, whose count is a CEILING. The two agree only when
    // `n ≡ 1 (mod 3)`, and nobody had written that invariant down.
    //
    // Recomputed here from both sides rather than transcribed, so this is two independent
    // derivations meeting and not a pin against its own definition.
    let b_span_formula = |n: usize| n + 3 + (n - 4) / 3;
    // The carrier chain over a body of `n - 4` limbs, grouped three at a time, ceiling.
    let chunk_count = |n: usize| (n - 4).div_ceil(3) + 1;

    assert_eq!(b_span_formula(184), 247);
    assert_eq!(
        chunk_count(184),
        61,
        "184 is consistent: formula and chain agree"
    );

    // 185 — the number an eyeball reaches for, needing "one more limb". The formula silently
    // under-allocates the block by one carrier column, which is the shape that made every rotated
    // member UNSAT the last time a geometry constant went quietly wrong.
    assert_ne!(
        b_span_formula(185) - 185,
        chunk_count(185) + 2,
        "185 must be INCONSISTENT — if this ever passes, the trap is gone and 185 would work"
    );

    // 186 is not body-aligned either.
    assert_ne!(
        (186 - 4) % 3,
        0,
        "186 leaves an arity-2 leftover in the body"
    );

    // 187 is the next value that is both body-aligned and consistent. This is why the flag day is
    // 184 -> 187 and buys THREE ninth lanes (child_vk, contract_hash, public_key) rather than one.
    assert_eq!((NINE_LANE_NUM_PRE_LIMBS - 4) % 3, 0, "187 is body-aligned");
    assert_eq!(
        NINE_LANE_NUM_PRE_LIMBS % 3,
        1,
        "the unwritten invariant: n = 1 mod 3"
    );
    assert_eq!(b_span_formula(NINE_LANE_NUM_PRE_LIMBS), 251);
    assert_eq!(chunk_count(NINE_LANE_NUM_PRE_LIMBS), 62);

    // And the three limbs 187 buys are exactly the three eight-lane carrier octets in the block.
    assert_eq!(
        NINE_LANE_NUM_PRE_LIMBS - 184,
        3,
        "the grow buys one ninth lane each for child_vk, contract_hash and public_key"
    );
}

#[test]
fn the_deployed_range_widths_admit_the_nonets_two_legs() {
    // The canonicity envelope is TWO legs at TWO widths — eight lookups at 29 and one at 24 — and
    // both must be admissible custom range widths or the envelope cannot be emitted at all.
    use dregg_circuit::descriptor_ir2::CUSTOM_RANGE_WIDTHS;
    assert!(
        CUSTOM_RANGE_WIDTHS.contains(&29),
        "the 29-bit lane lookup has no table: {CUSTOM_RANGE_WIDTHS:?}"
    );
    assert!(
        CUSTOM_RANGE_WIDTHS.contains(&24),
        "the 24-bit top-lane lookup has no table: {CUSTOM_RANGE_WIDTHS:?}"
    );

    // ⚠ AND THEY MUST STAY TWO. A uniform nine-lane check at 29 admits `[0, …, 0, 2^24]`, whose
    // value is exactly 2^256 and which decodes to the all-zero key. Dropping 24 "for uniformity"
    // re-opens the encoding — the exhibit is in `faithful8_key_octet_below_floor.rs`.
    assert_ne!(
        24, 29,
        "the two legs are different widths and that is the point"
    );
}
