/-
# Records runtime — the fixture-pin EVALUATION, out of the crypto archive's build

`RecordsRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its seventeen fixture pins ran `native_decide` at elaboration — each
accepted fixture row costing two native judge invocations — so any Records-fixture
regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The fixtures' STATEMENTS
remain in `RecordsRuntime.lean` as evaluation-free `check_* : Bool` definitions, beside
the private fixture rows and views they must see; THIS module is where they are RUN. It
is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING,
so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
projected view refuses answers `false`, so a broken projection reds THIS module.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.RecordsRuntime

namespace Dregg2.Games.PathOfAngels.RecordsRuntime

set_option autoImplicit false

theorem fixture_request_round_trips :
    check_fixture_request_round_trips = true := by native_decide

theorem fixture_genesis_only_view_is_a_real_world :
    check_fixture_genesis_only_view_is_a_real_world = true := by native_decide

theorem fixture_one_finalized_run_lands_in_every_projection :
    check_fixture_one_finalized_run_lands_in_every_projection = true := by native_decide

theorem fixture_live_seed_is_a_real_needle :
    check_fixture_live_seed_is_a_real_needle = true := by native_decide

theorem fixture_transcript_is_plaintext_of_the_submitted_code :
    check_fixture_transcript_is_plaintext_of_the_submitted_code = true := by native_decide

theorem view_never_publishes_the_live_run_seed :
    check_view_never_publishes_the_live_run_seed = true := by native_decide

theorem view_never_publishes_the_transcript :
    check_view_never_publishes_the_transcript = true := by native_decide

theorem hostile_live_run_seed_config_refused :
    check_hostile_live_run_seed_config_refused = true := by native_decide

theorem hostile_live_config_is_a_real_substitution :
    check_hostile_live_config_is_a_real_substitution = true := by native_decide

theorem hostile_substituted_signer_refused :
    check_hostile_substituted_signer_refused = true := by native_decide

theorem hostile_substituted_actor_root_refused :
    check_hostile_substituted_actor_root_refused = true := by native_decide

theorem hostile_row_against_a_foreign_genesis_refused :
    check_hostile_row_against_a_foreign_genesis_refused = true := by native_decide

theorem hostile_replayed_row_refused :
    check_hostile_replayed_row_refused = true := by native_decide

theorem hostile_out_of_order_rows_refused :
    check_hostile_out_of_order_rows_refused = true := by native_decide

theorem hostile_foreign_authority_refused :
    check_hostile_foreign_authority_refused = true := by native_decide

theorem hostile_mission_from_another_world_refused :
    check_hostile_mission_from_another_world_refused = true := by native_decide

theorem fixture_export_refuses_malformed :
    check_fixture_export_refuses_malformed = true := by native_decide

#assert_compiled fixture_request_round_trips
#assert_compiled fixture_genesis_only_view_is_a_real_world
#assert_compiled fixture_one_finalized_run_lands_in_every_projection
#assert_compiled fixture_live_seed_is_a_real_needle
#assert_compiled fixture_transcript_is_plaintext_of_the_submitted_code
#assert_compiled view_never_publishes_the_live_run_seed
#assert_compiled view_never_publishes_the_transcript
#assert_compiled hostile_live_run_seed_config_refused
#assert_compiled hostile_live_config_is_a_real_substitution
#assert_compiled hostile_substituted_signer_refused
#assert_compiled hostile_substituted_actor_root_refused
#assert_compiled hostile_row_against_a_foreign_genesis_refused
#assert_compiled hostile_replayed_row_refused
#assert_compiled hostile_out_of_order_rows_refused
#assert_compiled hostile_foreign_authority_refused
#assert_compiled hostile_mission_from_another_world_refused
#assert_compiled fixture_export_refuses_malformed

end Dregg2.Games.PathOfAngels.RecordsRuntime
