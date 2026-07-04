//! **THE FLAT-FIELDS[0..7] OCTET GENTIAN-WELD TOOTH — the 31-bit fields[0..7] forge is CLOSED at 8-felt.**
//!
//! The v13 fields hole (the LAST degraded-felt residual, now closed): the deployed rotated state
//! commitment once folded each 32-byte flat record field `fields[i]` to ONE BabyBear via the ~31-bit
//! `fold_bytes32_to_bb` Horner fold (one `from_lossy_31bit_DANGER` octet carrying all eight folds).
//! Two GENUINELY-DIFFERENT field values that AGREE in the u64-lane lo32 (the historical scalar the old
//! lane-0 commit pinned) but DIFFER in their higher bytes could COLLIDE on that single felt — a
//! ledgerless light client holding only the lane-0 projection could not tell which field value the
//! cell committed to.
//!
//! The v13 fields-octet grow replaces that with a FAITHFUL `field_limbs8` 8-lane split (lane 0 =
//! u64-lane lo32 riding the welded limb `4 + i`, lanes 1..7 = the higher bytes riding the completion
//! lanes `112 + 7·i .. +6`). This tooth constructs a concrete lane-0 collision and shows:
//!
//!   * the two field values are GENUINELY different (differ in byte 0 → completion lane 2);
//!   * their LANE-0 projections COLLIDE — the 31-bit hole a 1-felt `fields[i]` commit left open;
//!   * the FAITHFUL 8-lane octet SEPARATES them — a completion lane differs, so the chained
//!     `wire_commit_8` (the deployed `state_commit`) is DISTINCT.
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
/// is fixed at `lo`, and whose byte 0 (little-endian into `field_limbs8` lane 2) is the forge axis.
fn field_value(lo: u32, byte0: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[28..32].copy_from_slice(&lo.to_be_bytes()); // lane 0 = lo
    b[0] = byte0; // lane 2 = u32::from_le_bytes([byte0, 0, 0, 0]) = byte0
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
    // byte 0 (lane 2) — the 31-bit forge the old single-felt `fields[i]` commit could not separate.
    let v1 = field_value(42, 1);
    let v2 = field_value(42, 2);
    assert_ne!(v1, v2, "the two field values must be genuinely different");

    let o1 = field_limbs8(&v1);
    let o2 = field_limbs8(&v2);

    // (1) the LANE-0 projections COLLIDE — the hole a lane-0-only commit leaves open.
    assert_eq!(
        o1[0], o2[0],
        "lane 0 (u64-lane lo32) must collide: this is the 31-bit forge axis"
    );
    // (2) the FAITHFUL 8-lane octets DIFFER — in completion lane 2 (the byte-0 axis).
    assert_ne!(o1, o2, "the faithful field_limbs8 octet must separate them");
    assert_ne!(
        o1[2], o2[2],
        "the separation rides completion lane 2 (limb 113)"
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
        "the faithful 8-lane commitment must separate two lane-0-colliding field values"
    );
}

#[test]
fn honest_small_value_has_zero_completion_lanes() {
    // A small numeric field (the honest DUE_BITS / vault-operand domain) stored big-endian in the
    // last bytes has ZERO completion lanes — so the fields COMPLETION freeze (`before == after == 0`)
    // holds for the seven non-written fields on a value turn, and only a forged higher byte trips it.
    let small = field_value(1_000, 0);
    let octet = field_limbs8(&small);
    assert_eq!(
        octet[0],
        BabyBear::new(1_000),
        "lane 0 carries the numeric value"
    );
    for (lane, felt) in octet.iter().enumerate().skip(1) {
        assert_eq!(
            *felt,
            BabyBear::ZERO,
            "completion lane {lane} must be zero for a small value"
        );
    }
}
