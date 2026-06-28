//! Executor projection round-trip for the SettleEscrow weld (tag 17 —
//! `docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`).
//!
//! `project_slot_caveat_manifest` lowers a cell program's declared
//! `StateConstraint::SettleEscrow { leg_a_index, leg_b_index }` into the tag-17
//! Effect-VM slot-caveat manifest entry that a light client re-evaluates via
//! `dregg_circuit::effect_vm::verify_slot_caveat_manifest`. This test pins the
//! projection encoding (slot_index = leg A, params[0] = leg B) and then closes
//! the loop end-to-end: the projected manifest, written into a PI vector, ACCEPTS
//! an honest both-legs settle and REFUSES a forged partial settle — the same
//! atomic gate the Lean `SettleGate` proves (`SealedEscrow.lean` §6).
//!
//! STAGED: the projection is additive and gated by a cell DECLARING the caveat,
//! so it is dead-by-default until a cell opts in (no VK change — the gate rides
//! the public inputs + off-AIR re-evaluation, exactly the temporal tags 13–16).

use dregg_cell::program::StateConstraint;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;
use dregg_turn::executor::project_slot_caveat_manifest;

const LEG_A: u8 = 3;
const LEG_B: u8 = 4;
const DEPOSITED: u32 = pi::SETTLE_ESCROW_STATUS_DEPOSITED;
const CONSUMED: u32 = pi::SETTLE_ESCROW_STATUS_CONSUMED;

fn pi_with_manifest(count: u32, entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count);
    for (i, entry) in entries.iter().enumerate().take(count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

fn legs(status_a: u32, status_b: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[LEG_A as usize] = BabyBear::new(status_a);
    f[LEG_B as usize] = BabyBear::new(status_b);
    f
}

#[test]
fn settle_escrow_projects_tag_17_with_both_leg_slots() {
    let constraints = vec![StateConstraint::SettleEscrow {
        leg_a_index: LEG_A,
        leg_b_index: LEG_B,
    }];
    let (count, entries) = project_slot_caveat_manifest(&constraints);
    assert_eq!(count, 1, "exactly one entry projected");
    let e = entries[0];
    assert_eq!(e.type_tag, pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW);
    assert_eq!(e.slot_index, LEG_A, "slot_index carries leg A");
    assert_eq!(
        e.params[0],
        BabyBear::new(LEG_B as u32),
        "params[0] carries leg B"
    );
}

#[test]
fn projected_manifest_accepts_honest_and_rejects_partial() {
    let constraints = vec![StateConstraint::SettleEscrow {
        leg_a_index: LEG_A,
        leg_b_index: LEG_B,
    }];
    let (count, entries) = project_slot_caveat_manifest(&constraints);
    let public_inputs = pi_with_manifest(count, &entries);

    // Honest: both legs Deposited -> both Consumed.
    let before = legs(DEPOSITED, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after, 0).is_ok(),
        "the projected manifest must ACCEPT an honest both-legs settle"
    );

    // Forged partial: leg B left Deposited.
    let after_partial = legs(CONSUMED, DEPOSITED);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after_partial, 0).is_err(),
        "the projected manifest must REFUSE a half-open settle"
    );
}
