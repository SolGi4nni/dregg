/-
# Crew field mission runtime — the activation-lab EVALUATION, out of the crypto archive's build

`CrewFieldMissionRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its executable activation laboratory ran twenty-seven
`native_decide` pins at elaboration — so a stale runtime fixture was a hard failure of every
Rust proving target in the workspace (the compilation-unit coupling the stale-fixture outage
measured). The STATEMENTS remain in `CrewFieldMissionRuntime.lean`, beside the private
activation world (`fixtureActivation`, `fixtureGenesis`, `fixtureSafeCommand`, the rekeyed
crew) they must see; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. Pins whose statement was ALREADY a named public `Bool`
definition are pinned under that definition; the rest go through the
`check_<theorem_name> : Bool` definition the parent now carries.

⚠ Two construction proofs did NOT move — `fixture_activation_valid` and
`rekeyed_crew_activation_is_valid`. `Activation` carries `activationValidB raw = true` as a
field, so they must elaborate where `fixtureActivation` and `rekeyedActivation` are BUILT.
They are the named residue; the lab header in `CrewFieldMissionRuntime.lean` records it.
`hostile_rekeyed_roster_shares_the_authored_activation_id` also stays there — `rfl`, with an
`#assert_compiled` census line reflecting the residue its statement reaches through.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

namespace Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

set_option autoImplicit false

/-! ## The authored activation and its wire transcripts -/

theorem fixture_runtime_content_valid :
    check_fixture_runtime_content_valid = true := by native_decide

theorem fixture_wire_transcripts_decode_back_to_the_kernel_traces :
    check_fixture_wire_transcripts_decode_back_to_the_kernel_traces = true := by native_decide

/-! ## Honest complete runs -/

theorem honest_complete_run_emits_one_ordinary_salvage_authorization :
    honestOrdinarySalvageB = true := by native_decide

theorem deep_run_separates_exchangeable_parts_from_nonmarket_relic_custody :
    deepTaxonomyB = true := by native_decide

/-! ## The hostile settlement cases -/

theorem hostile_same_admission_and_run_cannot_replay :
    replayRefusedB = true := by native_decide

theorem hostile_cross_activation_command_refused :
    check_hostile_cross_activation_command_refused = true := by native_decide

theorem hostile_forged_route_refused :
    check_hostile_forged_route_refused = true := by native_decide

theorem hostile_forged_outcome_refused :
    check_hostile_forged_outcome_refused = true := by native_decide

theorem hostile_actor_who_is_not_the_selected_officer_refused :
    check_hostile_actor_who_is_not_the_selected_officer_refused = true := by native_decide

theorem hostile_truncated_crew_transcript_refused :
    check_hostile_truncated_crew_transcript_refused = true := by native_decide

theorem hostile_forged_handoff_signature_refused_by_the_kernel :
    forgedHandoffSignatureRefusedB = true := by native_decide

theorem hostile_seal_for_another_session_cannot_activate :
    check_hostile_seal_for_another_session_cannot_activate = true := by native_decide

theorem hostile_canon_relic_market_activation_refused :
    check_hostile_canon_relic_market_activation_refused = true := by native_decide

theorem hostile_canon_relic_direct_trade_activation_refused :
    check_hostile_canon_relic_direct_trade_activation_refused = true := by native_decide

/-! ## The strict codec -/

theorem hostile_caller_authored_salvage_field_refused_by_strict_codec :
    check_hostile_caller_authored_salvage_field_refused_by_strict_codec = true := by
  native_decide

theorem strict_command_roundtrip :
    check_strict_command_roundtrip = true := by native_decide

theorem strict_state_roundtrip :
    check_strict_state_roundtrip = true := by native_decide

/-! ## The step ABI -/

theorem the_step_abi_reports_the_cursor_the_signed_transcript_used :
    stepAbiAnswersEveryPrefixB = true := by native_decide

theorem the_step_abi_refuses_a_wrong_crew_a_wrong_seat_and_an_overlong_prefix :
    stepAbiRefusalsB = true := by native_decide

/-! ## The two-crews-one-key collision, and the binding that closes it -/

theorem rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone :
    rekeySubstitutionRealB = true := by native_decide

theorem rekeyed_roster_changes_the_computed_crew_binding :
    check_rekeyed_roster_changes_the_computed_crew_binding = true := by native_decide

theorem hostile_authored_seal_cannot_activate_the_substituted_crew :
    check_hostile_authored_seal_cannot_activate_the_substituted_crew = true := by native_decide

theorem cross_crew_state_refused_only_by_the_roster_binding :
    crossCrewStateRefusedOnRosterB = true := by native_decide

theorem hostile_substituted_crew_cannot_consume_the_authored_crews_admission :
    crossCrewRunRefusedB = true := by native_decide

theorem callable_entrypoint_emits_the_exact_successful_receipt :
    check_callable_entrypoint_emits_the_exact_successful_receipt = true := by native_decide

#assert_compiled fixture_runtime_content_valid
#assert_compiled fixture_wire_transcripts_decode_back_to_the_kernel_traces
#assert_compiled honest_complete_run_emits_one_ordinary_salvage_authorization
#assert_compiled deep_run_separates_exchangeable_parts_from_nonmarket_relic_custody
#assert_compiled hostile_same_admission_and_run_cannot_replay
#assert_compiled hostile_cross_activation_command_refused
#assert_compiled hostile_forged_route_refused
#assert_compiled hostile_forged_outcome_refused
#assert_compiled hostile_actor_who_is_not_the_selected_officer_refused
#assert_compiled hostile_truncated_crew_transcript_refused
#assert_compiled hostile_forged_handoff_signature_refused_by_the_kernel
#assert_compiled hostile_seal_for_another_session_cannot_activate
#assert_compiled hostile_canon_relic_market_activation_refused
#assert_compiled hostile_canon_relic_direct_trade_activation_refused
#assert_compiled hostile_caller_authored_salvage_field_refused_by_strict_codec
#assert_compiled strict_command_roundtrip
#assert_compiled strict_state_roundtrip
#assert_compiled the_step_abi_reports_the_cursor_the_signed_transcript_used
#assert_compiled the_step_abi_refuses_a_wrong_crew_a_wrong_seat_and_an_overlong_prefix
#assert_compiled rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone
#assert_compiled rekeyed_roster_changes_the_computed_crew_binding
#assert_compiled hostile_authored_seal_cannot_activate_the_substituted_crew
#assert_compiled cross_crew_state_refused_only_by_the_roster_binding
#assert_compiled hostile_substituted_crew_cannot_consume_the_authored_crews_admission
#assert_compiled callable_entrypoint_emits_the_exact_successful_receipt

end Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
