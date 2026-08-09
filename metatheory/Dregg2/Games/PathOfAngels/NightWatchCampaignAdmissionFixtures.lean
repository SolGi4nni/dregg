/-
# NightWatch campaign admission — the teeth's EVALUATION, out of the crypto archive's build

`NightWatchCampaignAdmission.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its teeth ran eleven `native_decide` pins at elaboration — each one
a Poseidon2 slot commitment and a real SHA-256 over manifest bytes — so any fixture regression
was a hard failure of every Rust proving target in the workspace (the compilation-unit coupling
the stale-fixture outage measured). The teeth's STATEMENTS remain in
`NightWatchCampaignAdmission.lean` as evaluation-free `check_* : Bool` definitions, beside the
fixture world/manifest/member they bite on; THIS module is where they are RUN. It is rooted in
the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ Budget: these pins run Poseidon2 sponges and SHA-256 over the manifest bytes — minutes, not
seconds.

⚠ Named residue: NONE. Every fixture value in the parent is a plain `def`, so no proof is
demanded as data at construction and all eleven pins moved.
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

set_option autoImplicit false

theorem fixture_config_round_trips_through_the_wire :
    check_fixture_config_round_trips_through_the_wire = true := by native_decide

theorem fixture_manifest_decodes_canonically :
    check_fixture_manifest_decodes_canonically = true := by native_decide

theorem the_activated_world_admits_its_own_campaign_config :
    check_the_activated_world_admits_its_own_campaign_config = true := by native_decide

theorem a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it :
    check_a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it = true := by
  native_decide

theorem a_component_under_another_name_is_not_this_organs_config :
    check_a_component_under_another_name_is_not_this_organs_config = true := by native_decide

theorem a_config_cannot_be_carried_into_another_content_session :
    check_a_config_cannot_be_carried_into_another_content_session = true := by native_decide

theorem an_invalid_config_in_an_exactly_matching_world_still_yields_no_member :
    check_an_invalid_config_in_an_exactly_matching_world_still_yields_no_member = true := by
  native_decide

theorem oversized_rule_list_refuses :
    check_oversized_rule_list_refuses = true := by native_decide

theorem a_risk_threshold_above_the_face_count_refuses :
    check_a_risk_threshold_above_the_face_count_refuses = true := by native_decide

theorem initial_resource_above_the_bound_refuses :
    check_initial_resource_above_the_bound_refuses = true := by native_decide

theorem a_config_carrying_the_retired_hazard_cycle_refuses :
    check_a_config_carrying_the_retired_hazard_cycle_refuses = true := by native_decide

#assert_compiled fixture_config_round_trips_through_the_wire
#assert_compiled fixture_manifest_decodes_canonically
#assert_compiled the_activated_world_admits_its_own_campaign_config
#assert_compiled a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it
#assert_compiled a_component_under_another_name_is_not_this_organs_config
#assert_compiled a_config_cannot_be_carried_into_another_content_session
#assert_compiled an_invalid_config_in_an_exactly_matching_world_still_yields_no_member
#assert_compiled oversized_rule_list_refuses
#assert_compiled a_risk_threshold_above_the_face_count_refuses
#assert_compiled initial_resource_above_the_bound_refuses
#assert_compiled a_config_carrying_the_retired_hazard_cycle_refuses

end Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
