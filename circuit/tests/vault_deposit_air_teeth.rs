//! Share-vault no-dilution deposit AIR-teeth tests (the VaultDeposit weld, tag 19 —
//! `docs/deos/VAULT-DEPOSIT-WELD-DESIGN.md`).
//!
//! These are the circuit-side shadow of the Lean `VaultDepositGate` teeth
//! (`metatheory/Dregg2/Deos/Vault.lean` §6b): a SINGLE manifest entry reads the
//! committed `total_assets` and `total_shares` counter slots and re-evaluates the
//! no-dilution share-price transition off-AIR against the public-input-bound
//! `state_before`/`state_after` slot views. Both polarities are exercised, mirroring
//! the Lean `#guard`s:
//!
//!   * an HONEST deposit (assets advance by `d>0`, shares by the fair `m>0`, no
//!     existing holder diluted) PASSES — non-vacuity / accept polarity
//!     (`vault_passes_gate`);
//!   * a ZERO-MINT deposit (positive deposit, zero shares minted — the ERC-4626
//!     first-depositor INFLATION ATTACK) is REFUSED (`inflation_attack_rejected`);
//!   * an over-minting DILUTING deposit (`before_assets·m > before_shares·d`) is
//!     REFUSED (`dilution_rejected`);
//!   * a NON-CONSERVING deposit (total_assets not advancing by a positive deposit) is
//!     REFUSED (`assets_not_conserved_rejected`).
//!
//! The weld is STAGED: the AIR constraint polynomials (the VK bytes) are UNCHANGED —
//! the gate is carried in public inputs and enforced by the off-AIR manifest
//! re-evaluation, exactly as the temporal tags 13–16, the sealed-escrow tag 17, and the
//! standing-obligation tag 18. An old verifier rejects tag 19 as `unknown type_tag`
//! (the lockstep share-vault verifier epoch), NOT a proving-key rotation.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;

/// The committed `total_assets` counter slot (mirrors `vault.rs::KEY_TOTAL_ASSETS`).
const ASSETS: u8 = 0;
/// The committed `total_shares` counter slot (mirrors `vault.rs::KEY_TOTAL_SHARES`).
const SHARES: u8 = 1;

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

/// The tag-19 VaultDeposit entry: `slot_index` = the total_assets slot, `params[0]` =
/// the total_shares slot.
fn vault_entry() -> SlotCaveatEntry {
    SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
        slot_index: ASSETS,
        params: [
            BabyBear::new(SHARES as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    }
}

/// Build an 8-slot field view from explicit (total_assets, total_shares) counters.
fn vault(assets: u32, shares: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[ASSETS as usize] = BabyBear::new(assets);
    f[SHARES as usize] = BabyBear::new(shares);
    f
}

// ─────────────────────────────────────────────────────────────────────
// Accept polarity — the honest no-dilution deposit.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn honest_deposit_passes() {
    let public_inputs = pi_with_manifest(&[vault_entry()]);
    // Established vault (T=2, S=4); a deposit of d=10 mints the fair m=20 (the Lean
    // `sharesOut 2 4 10 = 20`): assets 2→12, shares 4→24, no-dilution 2·20 ≤ 4·10.
    let before = vault(2, 4);
    let after = vault(12, 24);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_ok(),
        "an honest no-dilution deposit must pass: {result:?}"
    );
}

#[test]
fn bootstrap_deposit_passes() {
    let public_inputs = pi_with_manifest(&[vault_entry()]);
    // The empty vault (T=0, S=0) bootstraps 1:1: a deposit of 100 mints 100; the
    // no-dilution floor 0·100 ≤ 0·100 holds and the mint is positive.
    let before = vault(0, 0);
    let after = vault(100, 100);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_ok(),
        "the bootstrap 1:1 deposit must pass: {result:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the ZERO-MINT / INFLATION ATTACK (Lean `inflation_attack_rejected`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn inflation_attack_zero_mint_rejected() {
    let public_inputs = pi_with_manifest(&[vault_entry()]);
    // A skewed vault (T=10001, S=1, as ERC-4626's balanceOf would read after a
    // donation): a victim's deposit of 100 rounds to floor(100·1/10001) = 0 shares.
    // The deposit advances assets 10001→10101 but mints ZERO shares (1→1) — the
    // gate REFUSES it, so the victim is never robbed.
    let before = vault(10001, 1);
    let after = vault(10101, 1);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "the ERC-4626 zero-mint inflation attack must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the over-minting DILUTING deposit (Lean `dilution_rejected`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn over_mint_dilution_rejected() {
    let public_inputs = pi_with_manifest(&[vault_entry()]);
    // Established vault (T=2, S=4); a deposit of d=10 forging m=21 shares (the fair
    // ratio yields 20). 2·21 = 42 > 4·10 = 40 — the existing holders are diluted, so
    // the no-dilution floor REFUSES it.
    let before = vault(2, 4);
    let after = vault(12, 25);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "an over-minting (diluting) deposit must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Reject polarity — the NON-CONSERVING deposit (Lean `assets_not_conserved_rejected`).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn non_positive_deposit_rejected() {
    let public_inputs = pi_with_manifest(&[vault_entry()]);
    // The committed total_assets did NOT advance (a phantom mint with no real
    // deposit): assets 2→2, shares 4→24. No genuine deposit — REFUSED.
    let before = vault(2, 4);
    let after = vault(2, 24);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "a deposit that does not advance total_assets must be REFUSED"
    );
}

#[test]
fn assets_decrease_rejected() {
    let public_inputs = pi_with_manifest(&[vault_entry()]);
    // total_assets DECREASED across the transition (not a deposit at all) — REFUSED.
    let before = vault(50, 50);
    let after = vault(40, 60);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "a transition that decreases total_assets must be REFUSED"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Malformed entry — shares slot index out of range fails closed.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn shares_slot_out_of_range_rejected() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
        slot_index: ASSETS,
        params: [
            BabyBear::new(8), // shares slot 8 is out of the 0..8 range
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let before = vault(2, 4);
    let after = vault(12, 24);
    let result = verify_slot_caveat_manifest(&public_inputs, &before, &after, 0);
    assert!(
        result.is_err(),
        "an out-of-range shares slot index must be REFUSED"
    );
}
