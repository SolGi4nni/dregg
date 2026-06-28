//! Executor projection round-trip for the DischargeObligation weld (tag 18 —
//! `docs/deos/DISCHARGE-OBLIGATION-WELD-DESIGN.md`).
//!
//! `project_slot_caveat_manifest` lowers a cell program's declared
//! `StateConstraint::DischargeObligation { cursor_slot, due_slot, amount_slot,
//! period, amount }` into the tag-18 Effect-VM slot-caveat manifest entry that a
//! light client re-evaluates via `dregg_circuit::effect_vm::verify_slot_caveat_manifest`.
//! This test pins the projection encoding (slot_index = cursor slot, params =
//! [due_slot, total_slot, period, amount]) and then closes the loop end-to-end: the
//! projected manifest, written into a PI vector, ACCEPTS an honest due ∧ exact ∧
//! advanced discharge and REFUSES an early one — the same per-period gate the Lean
//! `DischargeGate` proves (`StandingObligation.lean` §6b).
//!
//! STAGED: the projection is additive and gated by a cell DECLARING the caveat, so it
//! is dead-by-default until a cell opts in (no VK change — the gate rides the public
//! inputs + off-AIR re-evaluation, exactly the temporal tags 13–16 and the
//! sealed-escrow tag 17).

use dregg_cell::program::StateConstraint;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;
use dregg_turn::executor::project_slot_caveat_manifest;

const CURSOR: u8 = 1;
const DUE: u8 = 2;
const TOTAL: u8 = 3;
const PERIOD: u32 = 100;
const AMOUNT: u32 = 50;
const DUE_BLOCK: u32 = 1000;

fn pi_with_manifest(count: u32, entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count);
    for (i, entry) in entries.iter().enumerate().take(count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

fn obl(cursor: u32, due: u32, total: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[CURSOR as usize] = BabyBear::new(cursor);
    f[DUE as usize] = BabyBear::new(due);
    f[TOTAL as usize] = BabyBear::new(total);
    f
}

#[test]
fn discharge_obligation_projects_tag_18_with_schedule_slots() {
    let constraints = vec![StateConstraint::DischargeObligation {
        cursor_slot: CURSOR,
        due_slot: DUE,
        amount_slot: TOTAL,
        period: PERIOD,
        amount: AMOUNT,
    }];
    let (count, entries) = project_slot_caveat_manifest(&constraints);
    assert_eq!(count, 1, "exactly one entry projected");
    let e = entries[0];
    assert_eq!(e.type_tag, pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION);
    assert_eq!(e.slot_index, CURSOR, "slot_index carries the cursor slot");
    assert_eq!(
        e.params[0],
        BabyBear::new(DUE as u32),
        "params[0] carries the due slot"
    );
    assert_eq!(
        e.params[1],
        BabyBear::new(TOTAL as u32),
        "params[1] carries the total slot"
    );
    assert_eq!(
        e.params[2],
        BabyBear::new(PERIOD),
        "params[2] carries the period"
    );
    assert_eq!(
        e.params[3],
        BabyBear::new(AMOUNT),
        "params[3] carries the amount"
    );
}

#[test]
fn projected_manifest_accepts_honest_and_rejects_early() {
    let constraints = vec![StateConstraint::DischargeObligation {
        cursor_slot: CURSOR,
        due_slot: DUE,
        amount_slot: TOTAL,
        period: PERIOD,
        amount: AMOUNT,
    }];
    let (count, entries) = project_slot_caveat_manifest(&constraints);
    let public_inputs = pi_with_manifest(count, &entries);

    // Honest: cursor advances one period, total advances by the exact amount, at the
    // due block.
    let before = obl(DUE_BLOCK, DUE_BLOCK, 0);
    let after = obl(DUE_BLOCK + PERIOD, DUE_BLOCK, AMOUNT);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64).is_ok(),
        "the projected manifest must ACCEPT an honest due discharge"
    );

    // Early: clock one short of the due block.
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64 - 1).is_err(),
        "the projected manifest must REFUSE an early discharge"
    );

    // Non-advanced cursor: a replay that does not move the one-shot cursor.
    let after_replay = obl(DUE_BLOCK, DUE_BLOCK, AMOUNT);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after_replay, DUE_BLOCK as u64)
            .is_err(),
        "the projected manifest must REFUSE a non-advanced (replay) discharge"
    );
}
