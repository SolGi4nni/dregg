/-
# Signal network judge — the fixture-pin EVALUATION, out of the crypto archive's build

`NetworkJudge.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its seventeen fixture pins ran `native_decide` at elaboration — so any
Signal-judge fixture regression was a hard failure of every Rust proving target in the
workspace (the compilation-unit coupling the stale-fixture outage measured). The fixtures'
STATEMENTS remain in `NetworkJudge.lean` as evaluation-free `check_* : Bool` definitions,
beside the hostile inputs they exercise; THIS module is where they are RUN. It is rooted in
the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.NetworkJudge

namespace Dregg2.Games.PathOfAngels.NetworkJudge

set_option autoImplicit false

theorem fixture_processSignalWire_success :
    check_fixture_processSignalWire_success = true := by native_decide

theorem fixture_signalJudgeFFI_success :
    check_fixture_signalJudgeFFI_success = true := by native_decide

theorem fixture_signalJudgeFFI_malformed_refused :
    check_fixture_signalJudgeFFI_malformed_refused = true := by native_decide

theorem fixture_verifySignalTransition_success :
    check_fixture_verifySignalTransition_success = true := by native_decide

theorem fixture_incomplete_canon_output_refused :
    check_fixture_incomplete_canon_output_refused = true := by native_decide

theorem fixture_wrong_player_refused :
    check_fixture_wrong_player_refused = true := by native_decide

theorem fixture_wrong_config_refused :
    check_fixture_wrong_config_refused = true := by native_decide

theorem fixture_wrong_current_counter_refused :
    check_fixture_wrong_current_counter_refused = true := by native_decide

theorem fixture_stale_counter_refused :
    check_fixture_stale_counter_refused = true := by native_decide

theorem fixture_wrong_action_refused :
    check_fixture_wrong_action_refused = true := by native_decide

theorem fixture_multiple_actions_refused :
    check_fixture_multiple_actions_refused = true := by native_decide

theorem fixture_stale_revision_refused :
    check_fixture_stale_revision_refused = true := by native_decide

theorem fixture_replay_against_successor_refused :
    check_fixture_replay_against_successor_refused = true := by native_decide

theorem fixture_swapped_slot_secret_refused :
    check_fixture_swapped_slot_secret_refused = true := by native_decide

theorem fixture_wrong_slot_commitment_refused :
    check_fixture_wrong_slot_commitment_refused = true := by native_decide

theorem fixture_wrong_claimed_slot_refused :
    check_fixture_wrong_claimed_slot_refused = true := by native_decide

theorem fixture_unbound_run_seed_refused :
    check_fixture_unbound_run_seed_refused = true := by native_decide

/-! ## ⚑ THE SECOND GAME — measured 2026-08-09, all nine `true`

These run a real Vent Crawl transcript through `processSignalWire`, the body of
`@[export dregg_poa_signal_judge]`.  They are the evidence that this boundary settles
more than one game; every one of them was EVALUATED before it was written down.

⚠ They are `native_decide` for the same reason the Signal pins are: `admissionChecks`
re-derives the run seed with `HiddenInstance.runSeedFor`, a Poseidon2 sponge the kernel
cannot reduce (47.6 GB / 68 min, measured).  `#assert_compiled` records that as a
confession, not a certificate. -/

theorem vent_fixture_settles : check_vent_fixture_settles = true := by native_decide

theorem vent_output_is_canonical : check_vent_output_is_canonical = true := by native_decide

theorem vent_and_signal_are_different_runs :
    check_vent_and_signal_are_different_runs = true := by native_decide

theorem vent_forged_continuation_refused :
    check_vent_forged_continuation_refused = true := by native_decide

theorem vent_wrong_instance_refused :
    check_vent_wrong_instance_refused = true := by native_decide

theorem vent_replayed_counter_refused :
    check_vent_replayed_counter_refused = true := by native_decide

theorem vent_wrong_mission_refused :
    check_vent_wrong_mission_refused = true := by native_decide

theorem vent_retagged_as_signal_refused :
    check_vent_retagged_as_signal_refused = true := by native_decide

theorem signal_retagged_as_vent_refused :
    check_signal_retagged_as_vent_refused = true := by native_decide

#assert_compiled fixture_processSignalWire_success
#assert_compiled fixture_signalJudgeFFI_success
#assert_compiled fixture_signalJudgeFFI_malformed_refused
#assert_compiled fixture_verifySignalTransition_success
#assert_compiled fixture_incomplete_canon_output_refused
#assert_compiled fixture_wrong_player_refused
#assert_compiled fixture_wrong_config_refused
#assert_compiled fixture_wrong_current_counter_refused
#assert_compiled fixture_stale_counter_refused
#assert_compiled fixture_wrong_action_refused
#assert_compiled fixture_multiple_actions_refused
#assert_compiled fixture_stale_revision_refused
#assert_compiled fixture_replay_against_successor_refused
#assert_compiled fixture_swapped_slot_secret_refused
#assert_compiled fixture_wrong_slot_commitment_refused
#assert_compiled fixture_wrong_claimed_slot_refused
#assert_compiled fixture_unbound_run_seed_refused
#assert_compiled vent_fixture_settles
#assert_compiled vent_output_is_canonical
#assert_compiled vent_and_signal_are_different_runs
#assert_compiled vent_forged_continuation_refused
#assert_compiled vent_wrong_instance_refused
#assert_compiled vent_replayed_counter_refused
#assert_compiled vent_wrong_mission_refused
#assert_compiled vent_retagged_as_signal_refused
#assert_compiled signal_retagged_as_vent_refused

end Dregg2.Games.PathOfAngels.NetworkJudge
