//! **THE TOOTH — slot-caveat operand lane parity** (sibling of the SetField
//! narrow-4-byte projector, `docs/DESIGN-canonical-byte-felt-codec.md` §"Narrow-4-byte
//! projectors").
//!
//! `project_slot_caveat_manifest` (`turn/src/executor/mod.rs`) lowers a cell program's
//! value-bearing `StateConstraint`s — `FieldEquals` / `FieldGte` / `FieldLte` /
//! `FieldDelta` / `AllowedTransitions` — into PI manifest operands that
//! `dregg_circuit::effect_vm::verify_slot_caveat_manifest` compares DIRECTLY against
//! the AIR's `STATE_BEFORE_BASE` / `STATE_AFTER_BASE` field columns.
//!
//! Those columns carry `field_limbs9(f)[0]` = `u32::from_be_bytes(f[28..32])` — the lo32
//! of the kernel u64 lane that `dregg_cell::field_from_u64` writes. The operand projector
//! used to take `u32::from_le_bytes(f[0..4])` instead: a DIFFERENT lane, and identically
//! ZERO for every canonically-encoded operand. That skew is not a narrow binding, it is a
//! DEAD GATE — `FieldGte` re-evaluated as `new >= 0` (vacuous, can never go red) and
//! `FieldEquals` / `FieldLte` / `FieldDelta` re-evaluated against `0` (fail-closed on
//! honest turns).
//!
//! Reachability, stated honestly: no production caller populates
//! `EffectVmContext::slot_caveat_count` today (it is `0` outside tests), so this was a
//! LATENT skew, not a live hole — and correcting it moves no deployed PI byte. These
//! tests exist so it cannot come back, and so the gate is demonstrably REFUTABLE before
//! anyone wires the manifest to a live producer.

use dregg_cell::field_from_u64;
use dregg_cell::program::StateConstraint;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, field_limbs9, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;
use dregg_turn::executor::project_slot_caveat_manifest;

const SLOT: u8 = 3;

fn pi_with_manifest(count: u32, entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count);
    for (i, entry) in entries.iter().enumerate().take(count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

/// The AIR's field-column view of a cell slot — the exact map
/// `verify_slot_caveat_manifest` is documented to be compared against.
fn air_field_view(slot_value: u64) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[SLOT as usize] = field_limbs9(&field_from_u64(slot_value))[0];
    f
}

/// A canonically-encoded operand must reach the manifest INTACT, in the AIR's lane.
#[test]
fn value_operands_project_into_the_air_field_lane() {
    for v in [1u64, 5, 42, 9_999, u32::MAX as u64] {
        let (count, entries) = project_slot_caveat_manifest(&[StateConstraint::FieldGte {
            index: SLOT,
            value: field_from_u64(v),
        }]);
        assert_eq!(count, 1);
        assert_eq!(entries[0].type_tag, pi::SLOT_CAVEAT_TAG_FIELD_GTE);
        assert_eq!(
            entries[0].params[0],
            field_limbs9(&field_from_u64(v))[0],
            "the FieldGte operand must land in the AIR's field-column lane for {v}"
        );
        assert_ne!(
            entries[0].params[0],
            BabyBear::ZERO,
            "a nonzero canonical operand MUST NOT project to the zero felt ({v})"
        );
    }
}

/// **The falsifier: the gate must be able to go RED.** Under the old lane the operand
/// was `0`, so `new >= 0` held for every possible state and `FieldGte` could never
/// refuse anything.
#[test]
fn field_gte_refuses_a_below_threshold_write() {
    let (count, entries) = project_slot_caveat_manifest(&[StateConstraint::FieldGte {
        index: SLOT,
        value: field_from_u64(100),
    }]);
    let public_inputs = pi_with_manifest(count, &entries);
    let before = air_field_view(0);

    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &air_field_view(100), 0).is_ok(),
        "an at-threshold write must be ACCEPTED"
    );
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &air_field_view(4_000), 0).is_ok(),
        "an above-threshold write must be ACCEPTED"
    );
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &air_field_view(99), 0).is_err(),
        "a BELOW-threshold write must be REFUSED — this is the assertion the old \
         low-4-bytes operand lane could never make (it compared against 0)"
    );
}

/// The mirror direction: `FieldEquals` must ACCEPT the honest write it names. Under the
/// old lane the operand was `0` while the column carried the real value, so every honest
/// canonical write was refused — availability, the other face of the same skew.
#[test]
fn field_equals_accepts_the_honest_write_and_refuses_the_others() {
    let (count, entries) = project_slot_caveat_manifest(&[StateConstraint::FieldEquals {
        index: SLOT,
        value: field_from_u64(7),
    }]);
    let public_inputs = pi_with_manifest(count, &entries);
    let before = air_field_view(0);

    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &air_field_view(7), 0).is_ok(),
        "the honest write of the declared value must be ACCEPTED"
    );
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &air_field_view(8), 0).is_err(),
        "any other value must be REFUSED"
    );
}

/// `AllowedTransitions` carries TWO operands (`params[1]`, `params[2]`); both ride the
/// same lane, and a canonical pair must not collapse into `(0, 0)`.
#[test]
fn allowed_transitions_operands_are_distinguished() {
    let (count, entries) = project_slot_caveat_manifest(&[StateConstraint::AllowedTransitions {
        slot_index: SLOT,
        allowed: vec![(field_from_u64(1), field_from_u64(2))],
    }]);
    assert_eq!(count, 1);
    let e = entries[0];
    assert_eq!(e.type_tag, pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS);
    assert_eq!(e.params[1], field_limbs9(&field_from_u64(1))[0]);
    assert_eq!(e.params[2], field_limbs9(&field_from_u64(2))[0]);
    assert_ne!(
        e.params[1], e.params[2],
        "the old/new operands of a transition must not collapse to the same felt"
    );
}

/// The residual, pinned so the fix is not over-read: this is still a ONE-felt operand.
/// Bytes 0..28 of a 32-byte operand ride `field_limbs9` lanes 1..8 and are NOT carried
/// by the manifest entry — a 32-byte digest is not a caveat operand, exactly as
/// `docs/FINDING-state-field-truncation.md` concludes ("a `fields[]` slot is
/// definitionally a u64 lane").
#[test]
fn the_one_felt_operand_ceiling_is_real() {
    let mut a = field_from_u64(5);
    let mut b = field_from_u64(5);
    a[0] = 0xAA;
    b[0] = 0xBB;
    let (_, ea) = project_slot_caveat_manifest(&[StateConstraint::FieldEquals {
        index: SLOT,
        value: a,
    }]);
    let (_, eb) = project_slot_caveat_manifest(&[StateConstraint::FieldEquals {
        index: SLOT,
        value: b,
    }]);
    assert_eq!(
        ea[0].params[0], eb[0].params[0],
        "byte 0 rides lane 2 — the one-felt operand cannot separate it"
    );
}
