//! Standing-obligation per-period discharge AIR-teeth tests (the DischargeObligation
//! weld, tag 18 — `docs/deos/DISCHARGE-OBLIGATION-WELD-DESIGN.md`).
//!
//! These are the circuit-side shadow of the Lean `DischargeGate` teeth
//! (`metatheory/Dregg2/Deos/StandingObligation.lean` §6b): a SINGLE manifest entry
//! reads the committed `next_due` cursor and discharged-total slots and re-evaluates
//! the per-period discharge transition off-AIR against the public-input-bound
//! `state_before`/`state_after` slot views, using the block height as the schedule
//! clock. Both polarities are exercised, mirroring the Lean `#guard`s:
//!
//!   * an HONEST due ∧ exact ∧ advanced discharge PASSES — non-vacuity / accept
//!     polarity (`discharge_passes_gate`);
//!   * an EARLY discharge (block height below the committed due block) is REFUSED
//!     (`discharge_gate_early_rejected`);
//!   * a WRONG-AMOUNT discharge (the total does not advance by exactly the schedule
//!     amount) is REFUSED (`wrong_amount_rejected`);
//!   * a NON-ADVANCED cursor (a replay that leaves the one-shot cursor where it was)
//!     is REFUSED (`cursor_not_advanced_rejected`).
//!
//! The weld is STAGED: the AIR constraint polynomials (the VK bytes) are UNCHANGED —
//! the gate is carried in public inputs and enforced by the off-AIR manifest
//! re-evaluation, exactly as the temporal tags 13–16 and the sealed-escrow tag 17. An
//! old verifier rejects tag 18 as `unknown type_tag` (the lockstep standing-obligation
//! verifier epoch), NOT a proving-key rotation.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;

/// The `next_due` cursor slot (mirrors `obligation_standing.rs::KEY_NEXT_DUE`).
const CURSOR: u8 = 1;
/// The current period's due-block slot.
const DUE: u8 = 2;
/// The cumulative discharged-total slot (mirrors `KEY_DISCHARGED_TOTAL`).
const TOTAL: u8 = 3;

// The sample schedule (the Lean `t0` / the Rust `sample_terms`): owe 50 every 100
// blocks from block 1000.
const PERIOD: u32 = 100;
const AMOUNT: u32 = 50;
const DUE_BLOCK: u32 = 1000;
const CURSOR_BEFORE: u32 = 1000; // next_due at period 0
const CURSOR_AFTER: u32 = 1100; // advanced one period

fn pi_with_manifest(entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    let count = entries.len().min(pi::MAX_SLOT_CAVEATS);
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count as u32);
    for (i, entry) in entries.iter().take(count).enumerate() {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

/// The tag-18 DischargeObligation entry: `slot_index` = the cursor slot, `params` =
/// [due_slot, total_slot, period, amount].
fn discharge_entry() -> SlotCaveatEntry {
    SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
        slot_index: CURSOR,
        params: [
            BabyBear::new(DUE as u32),
            BabyBear::new(TOTAL as u32),
            BabyBear::new(PERIOD),
            BabyBear::new(AMOUNT),
        ],
    }
}

/// Build an 8-slot field view from explicit cursor/due/total values.
fn obl(cursor: u32, due: u32, total: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[CURSOR as usize] = BabyBear::new(cursor);
    f[DUE as usize] = BabyBear::new(due);
    f[TOTAL as usize] = BabyBear::new(total);
    f
}

// ─────────────────────────────────────────────────────────────────────
// Accept polarity — the honest due ∧ exact ∧ advanced discharge.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn honest_due_discharge_passes() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    let after = obl(CURSOR_AFTER, DUE_BLOCK, AMOUNT);
    // Block height (the schedule clock) has reached the due block.
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_ok(),
        "honest due discharge (cursor advanced one period, total advanced by the exact amount, \
         at/after the due block) must pass: {result:?}"
    );
}

#[test]
fn honest_discharge_strictly_after_due_passes() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    let after = obl(CURSOR_AFTER, DUE_BLOCK, AMOUNT);
    // A clock strictly past the due block is still due.
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64 + 5);
    assert!(
        result.is_ok(),
        "a discharge past the due block must pass: {result:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the EARLY discharge (Lean `discharge_gate_early_rejected`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn early_discharge_rejected() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    let after = obl(CURSOR_AFTER, DUE_BLOCK, AMOUNT);
    // Block height one short of the due block — not yet due.
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64 - 1);
    assert!(
        result.is_err(),
        "an early discharge (clock below the due block) must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the WRONG-AMOUNT discharge (Lean `wrong_amount_rejected`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn over_discharge_rejected() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    // Total advanced by 9999 instead of the schedule amount 50.
    let after = obl(CURSOR_AFTER, DUE_BLOCK, 9999);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_err(),
        "an over-discharge (total advanced by the wrong amount) must be REFUSED"
    );
}

#[test]
fn under_discharge_rejected() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    // Total advanced by only 1 instead of 50.
    let after = obl(CURSOR_AFTER, DUE_BLOCK, 1);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_err(),
        "an under-discharge (total advanced by the wrong amount) must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the NON-ADVANCED cursor / replay
// (Lean `cursor_not_advanced_rejected`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn cursor_not_advanced_rejected() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    // Cursor left at 1000 (the one-shot cursor did not move) but total still bumped.
    let after = obl(CURSOR_BEFORE, DUE_BLOCK, AMOUNT);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_err(),
        "a discharge that does not advance the one-shot cursor must be REFUSED"
    );
}

#[test]
fn cursor_over_advanced_rejected() {
    let public_inputs = pi_with_manifest(&[discharge_entry()]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    // Cursor jumped two periods (1200) — a skip, not a single-period advance.
    let after = obl(CURSOR_BEFORE + 2 * PERIOD, DUE_BLOCK, AMOUNT);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_err(),
        "a discharge that advances the cursor by more than one period must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Malformed entry — due/total slot index out of range fails closed.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn due_slot_out_of_range_rejected() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
        slot_index: CURSOR,
        params: [
            BabyBear::new(8), // due slot 8 is out of the 0..8 range
            BabyBear::new(TOTAL as u32),
            BabyBear::new(PERIOD),
            BabyBear::new(AMOUNT),
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    let after = obl(CURSOR_AFTER, DUE_BLOCK, AMOUNT);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_err(),
        "an out-of-range due slot index must be REFUSED"
    );
}

#[test]
fn total_slot_out_of_range_rejected() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
        slot_index: CURSOR,
        params: [
            BabyBear::new(DUE as u32),
            BabyBear::new(8), // total slot 8 is out of the 0..8 range
            BabyBear::new(PERIOD),
            BabyBear::new(AMOUNT),
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let before = obl(CURSOR_BEFORE, DUE_BLOCK, 0);
    let after = obl(CURSOR_AFTER, DUE_BLOCK, AMOUNT);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, DUE_BLOCK as u64);
    assert!(
        result.is_err(),
        "an out-of-range total slot index must be REFUSED"
    );
}
