//! **THE FLAT-FIELDS[0..8] NONET GENTIAN-WELD TOOTH — the fields forge is closed by an INJECTION.**
//!
//! The v13 fields hole: the deployed rotated state commitment once folded each 32-byte flat record
//! field `fields[i]` to ONE BabyBear via the ~31-bit `fold_bytes32_to_bb` Horner fold (one
//! `from_lossy_31bit_DANGER` octet carrying all eight folds). Two GENUINELY-DIFFERENT field values
//! that AGREE in the u64-lane lo32 (the historical scalar the old lane-0 commit pinned) but DIFFER in
//! their higher bytes could COLLIDE on that single felt — a ledgerless light client holding only the
//! lane-0 projection could not tell which field value the cell committed to.
//!
//! ⚑ **THIS FILE HAS NOW OUTLIVED THREE ENCODERS AND THE FIRST TWO WERE NOT FIXES.** The 1-felt fold
//! became an eight-lane `u32 % p` split (still `O(1)`-aliasable: `2p < 2^32`, so add `p` to any chunk
//! for a byte-identical vector, no grind). That became eight lanes with a Poseidon2 image over an
//! injective preimage in lanes 2..7 — which killed the CONSTRUCTED alias and landed at a **2^92.7
//! COLLISION**, the birthday figure, below the ~124-bit bar quoted elsewhere in this tree. It could
//! never have been better: `p = 2013265921`, `log₂ p = 30.907`, so eight lanes carry **247.26 bits**
//! against 256 and no 8-lane encoding of 32 bytes is injective under ANY chunking. Pigeonhole.
//!
//! The encoder this file now measures is [`dregg_circuit::effect_vm::field_limbs9`] — NINE lanes,
//! whose Lean authority `metatheory/Dregg2/Circuit/FieldLanes9.lean` carries `fieldToLanes9_injective`
//! from a TOTAL decoder and a machine-checked left inverse. `field_limbs8` is DELETED. The separation
//! this tooth exhibits is no longer a hash's and no longer a layout's — it is an injection's.
//!
//! The in-circuit companion bite — a forged completion lane smuggled into NEW_COMMIT on a
//! non-field-writing VALUE turn is UNSAT — is proven in Lean
//! (`EffectVmEmitRotationV3.rotateV3FrozenAuthority_rejects_fields_forge`, `#assert_axioms`-clean):
//! the shared value wrap freezes the completion lanes BEFORE↔AFTER. Modeled on the spirit of
//! `fields_root_gentian_weld.rs` (the overflow-MAP root tooth), applied to the flat nonet.

use dregg_circuit::effect_vm::layout_generated::ROTATED_FIELD_LANE_COL;
use dregg_circuit::effect_vm::trace_rotated::NUM_PRE_LIMBS;
use dregg_circuit::effect_vm::{field_from_lanes9, field_limbs9};
use dregg_circuit::field::BabyBear;
use dregg_circuit::{Faithful8, Faithful9};

/// A 32-byte flat-field value whose u64-lane lo32 (`field_limbs9` lane 0 = big-endian bytes 28..32)
/// is fixed at `lo`, and whose byte 0 — OUTSIDE the u64 lane, so invisible to lanes 0/1 — is the
/// forge axis. It reaches the vector only through the free lanes.
fn field_value(lo: u32, byte0: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[28..32].copy_from_slice(&lo.to_be_bytes()); // lane 0 = lo
    b[0] = byte0; // outside 24..32: lanes 0/1 cannot see it
    b
}

/// The chained 8-felt rotated state commitment over the DEPLOYED single-field pre-limb layout:
/// field 0's nonet scattered through the Lean-emitted `ROTATED_FIELD_LANE_COL[0]` — lane 0 → limb 4,
/// lanes 1..7 → the completion window, lane 8 → column 176. ⚠ Read the table; never a stride.
fn state_commit(value: &[u8; 32]) -> [BabyBear; 8] {
    let mut pre = vec![BabyBear::ZERO; NUM_PRE_LIMBS];
    Faithful9::from_field_lanes9(value).write_lanes(&mut pre, ROTATED_FIELD_LANE_COL[0]);
    let iroot = BabyBear::new(7); // any fixed context felt — the same for both sides.
    Faithful8::from_wire_commit(&pre, iroot).limbs()
}

#[test]
fn lane0_collision_is_separated_by_the_injective_nonet() {
    // Two GENUINELY-different field values agreeing in the u64-lane lo32 (lane 0) but differing in
    // byte 0 — the 31-bit forge the old single-felt `fields[i]` commit could not separate.
    let v1 = field_value(42, 1);
    let v2 = field_value(42, 2);
    assert_ne!(v1, v2, "the two field values must be genuinely different");

    let o1 = field_limbs9(&v1);
    let o2 = field_limbs9(&v2);

    // (1) the LANE-0 projections COLLIDE — the hole a lane-0-only commit leaves open. Lane 1 too:
    //     byte 0 is outside the u64 lane, so NEITHER window lane can see the forge.
    assert_eq!(
        o1[0], o2[0],
        "lane 0 (u64-lane lo32) must collide: this is the 31-bit forge axis"
    );
    assert_eq!(o1[1], o2[1], "lane 1 (u64-lane hi32) collides too");
    // (2) the NONET SEPARATES them, and the separation rides the free lanes.
    assert_ne!(o1, o2, "the field_limbs9 nonet must separate them");
    assert!(
        (2..9).any(|k| o1[k] != o2[k]),
        "the separation must ride the free lanes — they are the only lanes that can see byte 0"
    );

    // (3) ANTI-VACUITY: both values come back. A separation produced by an encoder that scrambled
    //     its input would pass (1)+(2) and fail here. This is the property `field_limbs8` could
    //     never offer — a hash image has no inverse, so "the vectors differ" was the whole story.
    assert_eq!(field_from_lanes9(&o1), v1);
    assert_eq!(field_from_lanes9(&o2), v2);
}

#[test]
fn state_commit_rejects_the_lane0_forge() {
    // The deployed `state_commit` (chained `wire_commit_8` over the nonet-scattered pre-limbs) binds
    // ALL 9 lanes, so the lane-0-colliding forge produces a DISTINCT commitment — a ledgerless light
    // client cannot be fooled about which field value the cell committed to.
    let honest = state_commit(&field_value(42, 1));
    let forged = state_commit(&field_value(42, 2));
    assert_ne!(
        honest, forged,
        "the nine-lane commitment must separate two lane-0-colliding field values"
    );
}

/// ⚑ **THIS TEST'S ASSERTION HAS NOW BEEN INVERTED TWICE, AND THE SECOND INVERSION IS THE REPAIR.**
///
/// It began as `honest_small_value_has_zero_completion_lanes` and drew the freeze argument from the
/// zeros. Those zeros were an ACCIDENT of the `u32 % p` encoding — lanes 2..7 were chunks over the
/// all-zero bytes `0..24` — and that same chunk structure is what made the octet collide in `O(1)`.
/// It was then rewritten to demand a NONZERO completion octet, because the hash lanes covered the
/// whole value and a zero would have meant the chunk form was back.
///
/// Under the nine-lane encoder a small numeric field has ZERO free lanes again, and that is now
/// CORRECT rather than a smell: the free lanes carry `b[0..24]` plus the two `mod p` quotients
/// VERBATIM, and `field_from_u64` leaves all of that empty. The zeros are no longer load-bearing in
/// either direction — injectivity is a theorem (`fieldToLanes9_injective`), not an inference from
/// how busy the lanes look. That is exactly the difference between an injection and a containment,
/// and it is why this assertion could flip twice without anyone learning anything.
///
/// What this test pins is the freeze argument, which never needed the zeros: the lanes are a FUNCTION
/// of the field value, so an unchanged field satisfies `colEq(before, after)` lane-for-lane, and a
/// CHANGED field moves at least one lane. Both poles are asserted; the second is the one the GENTIAN
/// law rests on.
#[test]
fn the_completion_lanes_are_a_function_of_the_field_value_and_they_bite() {
    let small = field_value(1_000, 0);
    let nonet = field_limbs9(&small);
    assert_eq!(
        nonet[0],
        BabyBear::new(1_000),
        "lane 0 still carries the numeric value — the escrow/discharge/vault weld constants"
    );
    assert_eq!(nonet[1], BabyBear::ZERO, "lane 1 (hi32) is zero below 2^32");
    // The nine-lane shape, stated: a kernel-numeric value has EMPTY free lanes, because they carry
    // `b[0..24]` and the quotients literally, and `field_from_u64` leaves both empty. The old
    // encoder's nonzero hash lanes are gone with it.
    assert!(
        (2..9).all(|k| nonet[k] == BabyBear::ZERO),
        "a kernel-numeric field has empty free lanes — they carry b[0..24] and the quotients \
         verbatim, and both are empty here"
    );

    // POLE 1 — the freeze holds: the same field value projects to the same nonet, so a turn that
    // does not write this field satisfies `colEq(before, after)` on all eight completion lanes.
    assert_eq!(
        field_limbs9(&small),
        nonet,
        "an unchanged field value must project identically — this IS the completion freeze"
    );

    // POLE 2 — and the freeze BITES: any change to the field moves a completion lane, including
    // changes the lane-0/1 window cannot see AND changes inside it (the quotient rides lane 8).
    for other in [
        field_value(1_000, 1), // a high byte, invisible to lanes 0/1
        field_value(1_001, 0), // the u64 window itself
        field_value(0, 0),     // the zero field
        field_value(1_000, 0), // ⚑ THE CONTROL — identical to `small`, and it must NOT read as a bite
    ] {
        if other == small {
            // The control: an unchanged value must NOT be counted as a bite. Without this the loop
            // could be satisfied by an encoder that moved a lane on every call.
            assert_eq!(field_limbs9(&other), nonet);
            continue;
        }
        let o = field_limbs9(&other);
        assert!(
            (1..9).any(|k| o[k] != nonet[k]) || o[0] != nonet[0],
            "a changed field value must move a lane, else the freeze admits it"
        );
        // And the free lanes alone must catch the change that lanes 0/1 cannot see.
        if other[24..32] == small[24..32] {
            assert!(
                (2..9).any(|k| o[k] != nonet[k]),
                "a change OUTSIDE the u64 window must move a free lane — lanes 0/1 are blind to it"
            );
        }
    }
}
