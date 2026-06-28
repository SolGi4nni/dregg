//! Sealed-escrow atomic-swap AIR-teeth tests (the SettleEscrow weld, tag 17 —
//! `docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`).
//!
//! These are the circuit-side shadow of the Lean `SettleGate` teeth
//! (`metatheory/Dregg2/Deos/SealedEscrow.lean` §6): a SINGLE manifest entry reads
//! BOTH leg-status slots and re-evaluates the atomic both-or-none settlement
//! transition off-AIR against the public-input-bound `state_before`/`state_after`
//! slot views. Both polarities are exercised, mirroring the Lean `#guard`s:
//!
//!   * an HONEST both-legs settle (both `Deposited` before, both `Consumed`
//!     after) PASSES — non-vacuity / accept polarity (`settle_passes_gate`);
//!   * a forged PARTIAL settle (one leg `Consumed`, the other left `Deposited` —
//!     the half-open trade) is REFUSED (`partial_settle_rejected`);
//!   * a PHANTOM settle (a before-leg never `Deposited` — `Empty` or an
//!     already-`Consumed` replay) is REFUSED (`phantom_settle_rejected`).
//!
//! The weld is STAGED: the AIR constraint polynomials (the VK bytes) are
//! UNCHANGED — the gate is carried in public inputs and enforced by the off-AIR
//! manifest re-evaluation, exactly as the temporal tags 13–16. An old verifier
//! rejects tag 17 as `unknown type_tag` (the lockstep sealed-escrow verifier
//! epoch), NOT a proving-key rotation.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;

/// Leg A's status slot (mirrors `cell/src/escrow_sealed.rs::KEY_LEG_A_STATUS`).
const LEG_A: u8 = 3;
/// Leg B's status slot (mirrors `KEY_LEG_B_STATUS`).
const LEG_B: u8 = 4;

const EMPTY: u32 = 0;
const DEPOSITED: u32 = pi::SETTLE_ESCROW_STATUS_DEPOSITED; // 1
const CONSUMED: u32 = pi::SETTLE_ESCROW_STATUS_CONSUMED; // 2

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

/// The tag-17 SettleEscrow entry naming the two leg-status slots: `slot_index`
/// = leg A, `params[0]` = leg B.
fn settle_entry() -> SlotCaveatEntry {
    SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        slot_index: LEG_A,
        params: [
            BabyBear::new(LEG_B as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    }
}

/// Build an 8-slot field view with the two leg-status slots set.
fn legs(status_a: u32, status_b: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[LEG_A as usize] = BabyBear::new(status_a);
    f[LEG_B as usize] = BabyBear::new(status_b);
    f
}

// ─────────────────────────────────────────────────────────────────────
// Accept polarity — the honest both-legs settle (Lean `settle_passes_gate`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn honest_both_legs_settle_passes() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    let before = legs(DEPOSITED, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_ok(),
        "honest both-legs settle (both Deposited -> both Consumed) must pass: {result:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the forged PARTIAL settle (Lean `partial_settle_rejected`).
// One leg flips to Consumed, the other is left Deposited: the half-open trade.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn partial_settle_leg_b_unflipped_rejected() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    let before = legs(DEPOSITED, DEPOSITED);
    // Leg A consumed, leg B still Deposited — B walks away un-swapped.
    let after = legs(CONSUMED, DEPOSITED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "a half-open settle (leg B left Deposited) must be REFUSED"
    );
}

#[test]
fn partial_settle_leg_a_unflipped_rejected() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    let before = legs(DEPOSITED, DEPOSITED);
    // Symmetric: leg B consumed, leg A still Deposited.
    let after = legs(DEPOSITED, CONSUMED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "a half-open settle (leg A left Deposited) must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the PHANTOM settle (Lean `phantom_settle_rejected`).
// A before-leg that never genuinely locked (Empty, or an already-Consumed
// replay) cannot be consumed: a consumption conjured from an unlocked leg.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn phantom_settle_leg_a_never_deposited_rejected() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    // Leg A was never Deposited (Empty before) yet "settles".
    let before = legs(EMPTY, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "a phantom settle (leg A never Deposited) must be REFUSED"
    );
}

#[test]
fn replayed_consumed_leg_settle_rejected() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    // Leg A already Consumed (a spent nullifier) — a replay attempt.
    let before = legs(CONSUMED, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "a replay of an already-Consumed leg must be REFUSED"
    );
}

#[test]
fn neither_leg_deposited_rejected() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    let before = legs(EMPTY, EMPTY);
    let after = legs(CONSUMED, CONSUMED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "settling two never-deposited legs must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Malformed entry — leg-B slot index out of range fails closed.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn leg_b_slot_out_of_range_rejected() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        slot_index: LEG_A,
        params: [
            BabyBear::new(8), // leg B slot 8 is out of the 0..8 range
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let before = legs(DEPOSITED, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "an out-of-range leg-B slot index must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// An old verifier rejects tag 17 as unknown — the lockstep verifier epoch.
// (Documented here as an executable note: a verifier that does NOT know tag 17
// would hit the `other =>` unknown-tag arm. We can't run an old verifier, but
// we assert the new one's accept is GATED on the exact atomic shape, which is
// the property the epoch rolls out.)
// ─────────────────────────────────────────────────────────────────────

#[test]
fn accept_is_gated_on_exact_atomic_shape() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    // Every non-(Deposited,Deposited -> Consumed,Consumed) combination of the
    // two legs over {Empty, Deposited, Consumed} must reject; only the honest
    // one accepts.
    let codes = [EMPTY, DEPOSITED, CONSUMED];
    let mut accepted = 0usize;
    for &ba in &codes {
        for &bb in &codes {
            for &aa in &codes {
                for &ab in &codes {
                    let before = legs(ba, bb);
                    let after = legs(aa, ab);
                    let ok =
                        verify_slot_caveat_manifest(&public_inputs, &before, &after, 0).is_ok();
                    if ok {
                        accepted += 1;
                        assert_eq!(
                            (ba, bb, aa, ab),
                            (DEPOSITED, DEPOSITED, CONSUMED, CONSUMED),
                            "the ONLY accepting shape is both-Deposited -> both-Consumed"
                        );
                    }
                }
            }
        }
    }
    assert_eq!(accepted, 1, "exactly one atomic shape accepts");
}
