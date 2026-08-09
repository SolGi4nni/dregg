/-
# Shipworks — the strategy/hostile-fixture EVALUATION, out of the crypto archive's build

`Shipworks.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its strategy and hostile examples ran twenty-two `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving
target in the workspace (the compilation-unit coupling the stale-fixture outage measured).
The STATEMENTS remain in `Shipworks.lean` as evaluation-free `check_* : Bool` definitions;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  `Shipworks` keeps no `native_decide` residue of its
own — every fixture value is constructed with kernel-checked (`decide`/`norm_num`) proofs.
-/
import Dregg2.Games.PathOfAngels.Shipworks

namespace Dregg2.Games.PathOfAngels.Shipworks

set_option autoImplicit false

theorem careful_power_completes :
    check_careful_power_completes = true := by native_decide

theorem reserve_power_completes :
    check_reserve_power_completes = true := by native_decide

theorem careful_power_preserves_more_quality :
    check_careful_power_preserves_more_quality = true := by native_decide

theorem reserve_power_trades_quality_for_cohesion :
    check_reserve_power_trades_quality_for_cohesion = true := by native_decide

theorem power_strategies_have_distinct_exact_contributions :
    check_power_strategies_have_distinct_exact_contributions = true := by native_decide

theorem authored_epoch_variant_changes_pressure_exactly :
    check_authored_epoch_variant_changes_pressure_exactly = true := by native_decide

theorem atmosphere_scrub_completes :
    check_atmosphere_scrub_completes = true := by native_decide

theorem coolant_repair_completes :
    check_coolant_repair_completes = true := by native_decide

theorem ration_synthesis_completes :
    check_ration_synthesis_completes = true := by native_decide

theorem three_other_jobs_have_distinct_exact_contributions :
    check_three_other_jobs_have_distinct_exact_contributions = true := by native_decide

theorem duplicate_tools_refuse :
    check_duplicate_tools_refuse = true := by native_decide

theorem early_certification_refuses :
    check_early_certification_refuses = true := by native_decide

theorem duplicate_scan_refuses :
    check_duplicate_scan_refuses = true := by native_decide

theorem duplicate_tool_use_refuses :
    check_duplicate_tool_use_refuses = true := by native_decide

theorem reserve_exhaustion_refuses :
    check_reserve_exhaustion_refuses = true := by native_decide

theorem second_spare_cartridge_use_refuses :
    check_second_spare_cartridge_use_refuses = true := by native_decide

theorem near_full_spare_state_is_valid :
    check_near_full_spare_state_is_valid = true := by native_decide

theorem over_capacity_spare_cartridge_refuses :
    check_over_capacity_spare_cartridge_refuses = true := by native_decide

theorem first_power_claim_succeeds :
    check_first_power_claim_succeeds = true := by native_decide

theorem power_claim_ignores_browser_calendar :
    check_power_claim_ignores_browser_calendar = true := by native_decide

theorem same_epoch_second_claim_refuses :
    check_same_epoch_second_claim_refuses = true := by native_decide

theorem missed_epochs_do_not_change_reward :
    check_missed_epochs_do_not_change_reward = true := by native_decide

#assert_compiled careful_power_completes
#assert_compiled reserve_power_completes
#assert_compiled careful_power_preserves_more_quality
#assert_compiled reserve_power_trades_quality_for_cohesion
#assert_compiled power_strategies_have_distinct_exact_contributions
#assert_compiled authored_epoch_variant_changes_pressure_exactly
#assert_compiled atmosphere_scrub_completes
#assert_compiled coolant_repair_completes
#assert_compiled ration_synthesis_completes
#assert_compiled three_other_jobs_have_distinct_exact_contributions
#assert_compiled duplicate_tools_refuse
#assert_compiled early_certification_refuses
#assert_compiled duplicate_scan_refuses
#assert_compiled duplicate_tool_use_refuses
#assert_compiled reserve_exhaustion_refuses
#assert_compiled second_spare_cartridge_use_refuses
#assert_compiled near_full_spare_state_is_valid
#assert_compiled over_capacity_spare_cartridge_refuses
#assert_compiled first_power_claim_succeeds
#assert_compiled power_claim_ignores_browser_calendar
#assert_compiled same_epoch_second_claim_refuses
#assert_compiled missed_epochs_do_not_change_reward

end Dregg2.Games.PathOfAngels.Shipworks
