//! **THE FLAT-FIELDS[0..7] OCTET GENTIAN-WELD TOOTH — the 31-bit ONE-FELT fields[0..7] forge is
//! closed at 8 lanes.** (It is not "the last degraded-felt residual" and this file claimed it was;
//! see the correction below and `docs/FAITHFUL-COMMITMENT-LAW.md`.)
//!
//! The v13 fields hole: the deployed rotated state
//! commitment once folded each 32-byte flat record field `fields[i]` to ONE BabyBear via the ~31-bit
//! `fold_bytes32_to_bb` Horner fold (one `from_lossy_31bit_DANGER` octet carrying all eight folds).
//! Two GENUINELY-DIFFERENT field values that AGREE in the u64-lane lo32 (the historical scalar the old
//! lane-0 commit pinned) but DIFFER in their higher bytes could COLLIDE on that single felt — a
//! ledgerless light client holding only the lane-0 projection could not tell which field value the
//! cell committed to.
//!
//! The v13 fields-octet grow replaces that with the `field_limbs8` 8-lane split (lane 0 = u64-lane
//! lo32 riding the welded limb `4 + i`, lanes 1..7 riding the completion lanes `113 + 7·i .. +6`).
//! This tooth constructs a concrete lane-0 collision and shows:
//!
//!   * the two field values are GENUINELY different (they differ in byte 0);
//!   * their LANE-0 projections COLLIDE — the 31-bit hole a 1-felt `fields[i]` commit left open;
//!   * the 8-lane octet SEPARATES them — the completion lanes differ, so the chained
//!     `wire_commit_8` (the deployed `state_commit`) is DISTINCT.
//!
//! ⚠ **"FAITHFUL" IS THE WRONG WORD AND USED TO APPEAR HERE FOUR TIMES.** Eight BabyBear lanes carry
//! 247.26 bits against a 32-byte field's 256, so no 8-lane octet is injective under any chunking.
//! Lanes 1..7 also no longer carry "the higher bytes": lanes 2..7 are the leading six felts of a
//! Poseidon2 image over an injective 16 × u16-LE preimage of the WHOLE value, because the old
//! `u32 % p` chunk form collided in `O(1)` — see `circuit/src/effect_vm/helpers.rs::field_limbs8`.
//! The separation this tooth exhibits is now a hash's, not a layout's.
//!
//! The in-circuit companion bite — a forged completion lane smuggled into NEW_COMMIT on a
//! non-field-writing VALUE turn is UNSAT — is proven in Lean
//! (`EffectVmEmitRotationV3.rotateV3FrozenAuthority_rejects_fields_forge`, `#assert_axioms`-clean):
//! the shared value wrap freezes all 56 completion lanes BEFORE↔AFTER. Modeled on the spirit of
//! `fields_root_gentian_weld.rs` (the overflow-MAP root tooth), applied to the flat octet.

use dregg_circuit::Faithful8;
use dregg_circuit::effect_vm::field_limbs8;
use dregg_circuit::effect_vm::trace_rotated::NUM_PRE_LIMBS;
use dregg_circuit::field::BabyBear;

/// A 32-byte flat-field value whose u64-lane lo32 (`field_limbs8` lane 0 = big-endian bytes 28..32)
/// is fixed at `lo`, and whose byte 0 — OUTSIDE the u64 lane, so invisible to lanes 0/1 — is the
/// forge axis. It reaches the octet only through the completion lanes.
fn field_value(lo: u32, byte0: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[28..32].copy_from_slice(&lo.to_be_bytes()); // lane 0 = lo
    b[0] = byte0; // outside 24..32: lanes 0/1 cannot see it
    b
}

/// The chained 8-felt rotated state commitment over a single-field pre-limb layout: field 0's octet
/// scattered lane 0 → limb 4, lanes 1..7 → the completion lanes 112..118 (the deployed v13 shape).
fn state_commit(value: &[u8; 32]) -> [BabyBear; 8] {
    let mut pre = vec![BabyBear::ZERO; NUM_PRE_LIMBS];
    Faithful8::from_field_limbs8(value)
        .write_lanes(&mut pre, [4, 112, 113, 114, 115, 116, 117, 118]);
    let iroot = BabyBear::new(7); // any fixed context felt — the same for both sides.
    Faithful8::from_wire_commit(&pre, iroot).limbs()
}

#[test]
fn lane0_collision_is_separated_by_the_faithful_octet() {
    // Two GENUINELY-different field values agreeing in the u64-lane lo32 (lane 0) but differing in
    // byte 0 — the 31-bit forge the old single-felt `fields[i]` commit could not separate.
    let v1 = field_value(42, 1);
    let v2 = field_value(42, 2);
    assert_ne!(v1, v2, "the two field values must be genuinely different");

    let o1 = field_limbs8(&v1);
    let o2 = field_limbs8(&v2);

    // (1) the LANE-0 projections COLLIDE — the hole a lane-0-only commit leaves open. Lane 1 too:
    //     byte 0 is outside the u64 lane, so NEITHER window lane can see the forge.
    assert_eq!(
        o1[0], o2[0],
        "lane 0 (u64-lane lo32) must collide: this is the 31-bit forge axis"
    );
    assert_eq!(o1[1], o2[1], "lane 1 (u64-lane hi32) collides too");
    // (2) the 8-lane octet SEPARATES them, and the separation rides the COMPLETION lanes.
    assert_ne!(o1, o2, "the field_limbs8 octet must separate them");
    assert!(
        (2..8).any(|k| o1[k] != o2[k]),
        "the separation must ride the completion lanes — they are the only lanes that can see \
         byte 0"
    );
}

#[test]
fn faithful_state_commit_rejects_the_lane0_forge() {
    // The deployed `state_commit` (chained `wire_commit_8` over the octet-scattered pre-limbs) binds
    // ALL 8 lanes, so the lane-0-colliding forge produces a DISTINCT commitment — a ledgerless light
    // client cannot be fooled about which field value the cell committed to.
    let honest = state_commit(&field_value(42, 1));
    let forged = state_commit(&field_value(42, 2));
    assert_ne!(
        honest, forged,
        "the 8-lane commitment must separate two lane-0-colliding field values"
    );
}

/// ⚑ **THIS TEST WAS `honest_small_value_has_zero_completion_lanes` AND ITS ASSERTION IS INVERTED.**
///
/// It asserted that a small numeric field has ZERO completion lanes, and drew the freeze argument
/// from that: `before == after == 0` for the seven non-written fields on a value turn. The zero was
/// an ACCIDENT of the old encoding — lanes 2..7 were `u32 % p` over the (all-zero) bytes `0..24` —
/// and that same chunk structure is what made the octet collide in `O(1)`. Lanes 2..7 now hash the
/// whole value, so a small value has a NONZERO, value-determined completion octet.
///
/// The freeze argument survives intact and is what this test now pins, because it never needed the
/// zeros: the completion lanes are a FUNCTION of the field value, so an unchanged field satisfies
/// `colEq(before, after)` lane-for-lane, and a CHANGED field moves at least one lane. Both poles are
/// asserted, and the second is the one the GENTIAN law actually rests on.
#[test]
fn honest_small_value_has_a_value_determined_completion_octet() {
    let small = field_value(1_000, 0);
    let octet = field_limbs8(&small);
    assert_eq!(
        octet[0],
        BabyBear::new(1_000),
        "lane 0 still carries the numeric value — the escrow/discharge/vault weld constants"
    );
    assert_eq!(octet[1], BabyBear::ZERO, "lane 1 (hi32) is zero below 2^32");
    // The change, stated: the completion octet is no longer zero.
    assert!(
        (2..8).any(|k| octet[k] != BabyBear::ZERO),
        "the completion octet must be NONZERO for a small value — if every lane is zero the \
         `u32 % p` chunk encoding is back and the O(1) alias with it"
    );

    // POLE 1 — the freeze holds: the same field value projects to the same octet, so a turn that
    // does not write this field satisfies `colEq(before, after)` on all seven completion lanes.
    assert_eq!(
        field_limbs8(&small),
        octet,
        "an unchanged field value must project identically — this IS the completion freeze"
    );

    // POLE 2 — and the freeze BITES: any change to the field moves the completion octet, including
    // changes the lane-0/1 window cannot see AND changes inside it (the hash covers all 32 bytes).
    for other in [
        field_value(1_000, 1), // a high byte, invisible to lanes 0/1
        field_value(1_001, 0), // the u64 window itself
        field_value(0, 0),     // the zero field
    ] {
        assert_ne!(other, small);
        let o = field_limbs8(&other);
        assert!(
            (2..8).any(|k| o[k] != octet[k]),
            "a changed field value must move a completion lane, else the freeze admits it"
        );
    }
}
