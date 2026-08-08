/-
# Salvage Crate — the hostility-lab EVALUATION, out of the crypto archive's build

`SalvageCrate.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its hostility lab ran eighteen `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace
(the compilation-unit coupling the stale-fixture outage measured). The lab's STATEMENTS
remain in `SalvageCrate.lean` as evaluation-free `check_* : Bool` definitions, beside the
private core they must see; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite open refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Two construction proofs did NOT move (`fixture_config_valid`, `rerolled_config_valid`) —
`Config` carries its validity proof as data, so they must elaborate where the fixture configs
are built. They are the named residue; the lab header in `SalvageCrate.lean` records it.
-/
import Dregg2.Games.PathOfAngels.SalvageCrate

namespace Dregg2.Games.PathOfAngels.SalvageCrate

set_option autoImplicit false

theorem fixture_daily_open_succeeds :
    check_fixture_daily_open_succeeds = true := by native_decide

theorem two_crew_members_may_open_the_same_period :
    check_two_crew_members_may_open_the_same_period = true := by native_decide

theorem genesis_snapshot_is_the_installed_state :
    check_genesis_snapshot_is_the_installed_state = true := by native_decide

theorem public_open_from_genesis_succeeds :
    check_public_open_from_genesis_succeeds = true := by native_decide

theorem public_double_open_in_one_period_refuses :
    check_public_double_open_in_one_period_refuses = true := by native_decide

theorem public_tomorrow_open_refuses :
    check_public_tomorrow_open_refuses = true := by native_decide

theorem public_finality_advance_succeeds :
    check_public_finality_advance_succeeds = true := by native_decide

theorem lab_witnesses_share_a_period_and_differ_only_in_crew :
    check_lab_witnesses_share_a_period_and_differ_only_in_crew = true := by native_decide

theorem identical_daily_open_reroll_refuses :
    check_identical_daily_open_reroll_refuses = true := by native_decide

theorem tomorrow_and_old_epoch_claims_refuse :
    check_tomorrow_and_old_epoch_claims_refuse = true := by native_decide

theorem fresh_state_reopen_against_global_snapshot_refuses :
    check_fresh_state_reopen_against_global_snapshot_refuses = true := by native_decide

theorem operator_beacon_reroll_breaks_authorized_identity :
    check_operator_beacon_reroll_breaks_authorized_identity = true := by native_decide

theorem forged_transferable_table_refuses :
    check_forged_transferable_table_refuses = true := by native_decide

theorem empty_loot_table_refuses :
    check_empty_loot_table_refuses = true := by native_decide

theorem modulo_bias_tail_refuses_instead_of_favoring_zero :
    check_modulo_bias_tail_refuses_instead_of_favoring_zero = true := by native_decide

theorem counter_exhaustion_refuses_otherwise_eligible_open :
    check_counter_exhaustion_refuses_otherwise_eligible_open = true := by native_decide

theorem skipped_periods_do_not_change_the_daily_prize :
    check_skipped_periods_do_not_change_the_daily_prize = true := by native_decide

/-- The two public lab witnesses are REAL accepted openings, not the fallback: the receipts
downstream welds (`ShipInstrumentPanel.ofSalvageOpen`) consume are the accepted results'
own, byte-for-byte. This is the pin that makes the fail-closed `match` arms in
`fixtureOpenReceipt`/`fixtureOpenReceiptSecondCrew` unreachable. -/
theorem lab_witness_receipts_are_the_accepted_openings :
    fixtureOpenReceipt.period = (⟨12⟩ : EpochId)
      ∧ fixtureOpenReceiptSecondCrew.period = (⟨12⟩ : EpochId)
      ∧ fixtureOpenReceipt.player ≠ fixtureOpenReceiptSecondCrew.player := by
  native_decide

#assert_compiled fixture_daily_open_succeeds
#assert_compiled two_crew_members_may_open_the_same_period
#assert_compiled genesis_snapshot_is_the_installed_state
#assert_compiled public_open_from_genesis_succeeds
#assert_compiled public_double_open_in_one_period_refuses
#assert_compiled public_tomorrow_open_refuses
#assert_compiled public_finality_advance_succeeds
#assert_compiled lab_witnesses_share_a_period_and_differ_only_in_crew
#assert_compiled identical_daily_open_reroll_refuses
#assert_compiled tomorrow_and_old_epoch_claims_refuse
#assert_compiled fresh_state_reopen_against_global_snapshot_refuses
#assert_compiled operator_beacon_reroll_breaks_authorized_identity
#assert_compiled forged_transferable_table_refuses
#assert_compiled empty_loot_table_refuses
#assert_compiled modulo_bias_tail_refuses_instead_of_favoring_zero
#assert_compiled counter_exhaustion_refuses_otherwise_eligible_open
#assert_compiled skipped_periods_do_not_change_the_daily_prize
#assert_compiled lab_witness_receipts_are_the_accepted_openings

end Dregg2.Games.PathOfAngels.SalvageCrate
