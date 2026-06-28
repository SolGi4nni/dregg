//! Executor projection round-trip for the VaultDeposit weld (tag 19 —
//! `docs/deos/VAULT-DEPOSIT-WELD-DESIGN.md`).
//!
//! `project_slot_caveat_manifest` lowers a cell program's declared
//! `StateConstraint::VaultDeposit { assets_slot, shares_slot }` into the tag-19
//! Effect-VM slot-caveat manifest entry that a light client re-evaluates via
//! `dregg_circuit::effect_vm::verify_slot_caveat_manifest`. This test pins the
//! projection encoding (slot_index = total_assets slot, params[0] = total_shares slot)
//! and then closes the loop end-to-end: the projected manifest, written into a PI
//! vector, ACCEPTS an honest no-dilution deposit and REFUSES the ERC-4626 zero-mint
//! inflation attack — the same no-dilution gate the Lean `VaultDepositGate` proves
//! (`Vault.lean` §6b).
//!
//! STAGED: the projection is additive and gated by a cell DECLARING the caveat, so it
//! is dead-by-default until a cell opts in (no VK change — the gate rides the public
//! inputs + off-AIR re-evaluation, exactly the temporal tags 13–16, the sealed-escrow
//! tag 17, and the standing-obligation tag 18).

use dregg_cell::program::StateConstraint;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;
use dregg_turn::executor::project_slot_caveat_manifest;

const ASSETS: u8 = 0;
const SHARES: u8 = 1;

fn pi_with_manifest(count: u32, entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count);
    for (i, entry) in entries.iter().enumerate().take(count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

fn vault(assets: u32, shares: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[ASSETS as usize] = BabyBear::new(assets);
    f[SHARES as usize] = BabyBear::new(shares);
    f
}

#[test]
fn vault_deposit_projects_tag_19_with_counter_slots() {
    let constraints = vec![StateConstraint::VaultDeposit {
        assets_slot: ASSETS,
        shares_slot: SHARES,
    }];
    let (count, entries) = project_slot_caveat_manifest(&constraints);
    assert_eq!(count, 1, "exactly one entry projected");
    let e = entries[0];
    assert_eq!(e.type_tag, pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT);
    assert_eq!(
        e.slot_index, ASSETS,
        "slot_index carries the total_assets slot"
    );
    assert_eq!(
        e.params[0],
        BabyBear::new(SHARES as u32),
        "params[0] carries the total_shares slot"
    );
    assert_eq!(e.params[1], BabyBear::ZERO);
    assert_eq!(e.params[2], BabyBear::ZERO);
    assert_eq!(e.params[3], BabyBear::ZERO);
}

#[test]
fn projected_manifest_accepts_honest_and_rejects_inflation() {
    let constraints = vec![StateConstraint::VaultDeposit {
        assets_slot: ASSETS,
        shares_slot: SHARES,
    }];
    let (count, entries) = project_slot_caveat_manifest(&constraints);
    let public_inputs = pi_with_manifest(count, &entries);

    // Honest: an established vault (T=2, S=4) takes a deposit of 10 minting the fair 20
    // (assets 2→12, shares 4→24, no-dilution 2·20 ≤ 4·10).
    let before = vault(2, 4);
    let after = vault(12, 24);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after, 0).is_ok(),
        "the projected manifest must ACCEPT an honest no-dilution deposit"
    );

    // The ERC-4626 inflation attack: a skewed vault (T=10001, S=1) where a victim's
    // deposit of 100 rounds to ZERO shares (assets 10001→10101, shares 1→1).
    let infl_before = vault(10001, 1);
    let infl_after = vault(10101, 1);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &infl_before, &infl_after, 0).is_err(),
        "the projected manifest must REFUSE the ERC-4626 zero-mint inflation attack"
    );

    // An over-minting diluting deposit (m=21 when the fair ratio yields 20).
    let dilute_after = vault(12, 25);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &dilute_after, 0).is_err(),
        "the projected manifest must REFUSE an over-minting (diluting) deposit"
    );
}
