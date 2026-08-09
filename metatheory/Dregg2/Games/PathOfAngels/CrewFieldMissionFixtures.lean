/-
# Crew field mission — the hostility-lab EVALUATION, out of the crypto archive's build

`CrewFieldMission.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its laboratory ran sixty-three `native_decide` pins at elaboration — the
largest single population in the game cone — so any game-fixture regression was a hard failure
of every Rust proving target in the workspace (the compilation-unit coupling the stale-fixture
outage measured). The lab's STATEMENTS remain in `CrewFieldMission.lean`, beside the private
fixture world (`fixtureConfig`, `drive`, `completionFor?`, `katConfig`, the KAT envelopes) they
must see; THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library
and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. Two statement shapes arrive here, both evaluation-free in
the parent: pins whose statement was ALREADY a named public `Bool` definition are pinned under
that definition; the rest are pinned through the `check_<theorem_name> : Bool` definition the
parent now carries.

⚠ Five construction proofs did NOT move — `fixturePolicy.catalogue_bounded`,
`wrongArtifactPolicy.catalogue_bounded`, `fixture_config_valid`, `fixture_rekeyed_config_valid`
and `kat_config_valid`. `ActivityOutcome.Policy` carries its bound as a field and `Config`
carries `rawConfigValidB … = true` as a field, so those proofs must elaborate where the
fixture, rekeyed and KAT worlds are BUILT. They are the named residue; the lab header in
`CrewFieldMission.lean` records it. `fixture_run_seal_carries_the_fixture_session` also stays
there — it is `rfl`, and its `#assert_compiled` census line reflects the residue its statement
reaches through.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMission

namespace Dregg2.Games.PathOfAngels.CrewFieldMission

set_option autoImplicit false

/-! ## Activation: the authored deployment, and what activation refuses -/

theorem fixture_ordered_briefing_deck_is_commitment_bound :
    check_fixture_ordered_briefing_deck_is_commitment_bound = true := by native_decide

theorem hostile_unwinnable_terminal_costs_are_individually_within_budget :
    check_hostile_unwinnable_terminal_costs_are_individually_within_budget = true := by
  native_decide

theorem hostile_unwinnable_config_has_no_affordable_safe_terminal :
    check_hostile_unwinnable_config_has_no_affordable_safe_terminal = true := by native_decide

theorem hostile_globally_unwinnable_config_refused_at_activation :
    check_hostile_globally_unwinnable_config_refused_at_activation = true := by native_decide

theorem raw_identity_fields_must_exactly_match_policy_mission :
    missionIdentityMutationsRefusedB = true := by native_decide

theorem wrong_mission_artifact_is_otherwise_declared_and_outcome_valid :
    check_wrong_mission_artifact_is_otherwise_declared_and_outcome_valid = true := by
  native_decide

theorem artifact_mission_must_exactly_match_activated_mission :
    check_artifact_mission_must_exactly_match_activated_mission = true := by native_decide

theorem hostile_same_role_briefing_substitution_breaks_activation_commitment :
    check_hostile_same_role_briefing_substitution_breaks_activation_commitment = true := by
  native_decide

/-! ## The second sealed world — the rekeyed crew -/

theorem fixture_rekeyed_roster_substitutes_only_the_player_keys :
    check_fixture_rekeyed_roster_substitutes_only_the_player_keys = true := by native_decide

theorem the_fixture_briefing_commitment_does_not_separate_the_two_crews :
    check_the_fixture_briefing_commitment_does_not_separate_the_two_crews = true := by
  native_decide

theorem the_two_fixture_seals_carry_different_sessions :
    check_the_two_fixture_seals_carry_different_sessions = true := by native_decide

theorem exported_fixture_transcripts_are_four_signed_handoffs_each :
    check_exported_fixture_transcripts_are_four_signed_handoffs_each = true := by native_decide

/-! ## The step surface over a real signed transcript -/

theorem the_step_surface_answers_at_every_prefix_replay_refuses :
    stepAnswersEveryPrefixWhileReplayIsSilentB = true := by native_decide

theorem a_crew_plays_a_whole_run_one_signed_handoff_at_a_time :
    stepSurfaceDrivesAWholeSignedRunB = true := by native_decide

theorem the_step_surface_opens_a_briefing_only_to_its_own_seat :
    stepSurfaceRefusesAnotherSeatsAdmissionB = true := by native_decide

/-! ## The seal — satisfiable AND refutable -/

theorem run_seal_admits_the_record_the_kernel_produced :
    sealAdmitsKernelProducedRecordB = true := by native_decide

theorem run_seal_refuses_a_terminal_state_the_kernel_did_not_reach :
    sealRefusesAssertedTerminalRootB = true := by native_decide

theorem run_seal_refuses_a_forged_handoff_signature :
    sealRefusesForgedHandoffSignatureB = true := by native_decide

/-! ## Cooperative play, and what the authored table costs -/

theorem safe_extraction_accepts_two_matching_signed_recommendations :
    check_safe_extraction_accepts_two_matching_signed_recommendations = true := by native_decide

theorem alternative_safe_route_is_reachable :
    check_alternative_safe_route_is_reachable = true := by native_decide

theorem deep_recovery_requires_and_accepts_full_crew_consensus :
    check_deep_recovery_requires_and_accepts_full_crew_consensus = true := by native_decide

theorem route_and_extraction_choices_produce_materially_distinct_records :
    completedPlansDifferB = true := by native_decide

theorem specialist_steps_and_final_route_are_both_charged_exactly :
    completedBudgetAccountingB = true := by native_decide

theorem route_changes_cost_reward_and_artifact_at_fixed_extraction :
    fixedExtractionRouteVariationB = true := by native_decide

theorem all_six_authored_route_extraction_outcomes_are_bounded_and_declared :
    allAuthoredOutcomesWellFormedB = true := by native_decide

theorem combined_field_record_replays_every_signed_handoff_exactly :
    exactReplayB deepPlan = true := by native_decide

theorem unchecked_record_projection_readmits_after_exact_replay :
    readmitB deepPlan = true := by native_decide

/-! ## The hostile transitions -/

theorem recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary :
    check_recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary = true := by
  native_decide

theorem hostile_mixed_crew_strategy_refused :
    check_hostile_mixed_crew_strategy_refused = true := by native_decide

theorem hostile_deep_recovery_without_unanimity_refused :
    check_hostile_deep_recovery_without_unanimity_refused = true := by native_decide

theorem hostile_private_observation_substitution_refused :
    check_hostile_private_observation_substitution_refused = true := by native_decide

theorem hostile_stale_predecessor_root_refused :
    check_hostile_stale_predecessor_root_refused = true := by native_decide

theorem hostile_handoff_signature_substitution_refused :
    check_hostile_handoff_signature_substitution_refused = true := by native_decide

theorem hostile_full_field_decision_substitution_refused_by_signature :
    check_hostile_full_field_decision_substitution_refused_by_signature = true := by
  native_decide

theorem hostile_signature_issued_for_other_seat_refused :
    check_hostile_signature_issued_for_other_seat_refused = true := by native_decide

theorem hostile_signing_suite_substitution_refused :
    check_hostile_signing_suite_substitution_refused = true := by native_decide

theorem hostile_public_message_digest_submitted_as_signature_refused :
    check_hostile_public_message_digest_submitted_as_signature_refused = true := by
  native_decide

theorem hostile_combined_record_route_substitution_refused :
    tamperedRecordReadmitsB = false := by native_decide

theorem hostile_expanded_record_mutation_matrix_refused :
    expandedRecordMutationsRefusedB = true := by native_decide

#assert_compiled fixture_ordered_briefing_deck_is_commitment_bound
#assert_compiled hostile_unwinnable_terminal_costs_are_individually_within_budget
#assert_compiled hostile_unwinnable_config_has_no_affordable_safe_terminal
#assert_compiled hostile_globally_unwinnable_config_refused_at_activation
#assert_compiled raw_identity_fields_must_exactly_match_policy_mission
#assert_compiled wrong_mission_artifact_is_otherwise_declared_and_outcome_valid
#assert_compiled artifact_mission_must_exactly_match_activated_mission
#assert_compiled hostile_same_role_briefing_substitution_breaks_activation_commitment
#assert_compiled fixture_rekeyed_roster_substitutes_only_the_player_keys
#assert_compiled the_fixture_briefing_commitment_does_not_separate_the_two_crews
#assert_compiled the_two_fixture_seals_carry_different_sessions
#assert_compiled exported_fixture_transcripts_are_four_signed_handoffs_each
#assert_compiled the_step_surface_answers_at_every_prefix_replay_refuses
#assert_compiled a_crew_plays_a_whole_run_one_signed_handoff_at_a_time
#assert_compiled the_step_surface_opens_a_briefing_only_to_its_own_seat
#assert_compiled run_seal_admits_the_record_the_kernel_produced
#assert_compiled run_seal_refuses_a_terminal_state_the_kernel_did_not_reach
#assert_compiled run_seal_refuses_a_forged_handoff_signature
#assert_compiled safe_extraction_accepts_two_matching_signed_recommendations
#assert_compiled alternative_safe_route_is_reachable
#assert_compiled deep_recovery_requires_and_accepts_full_crew_consensus
#assert_compiled route_and_extraction_choices_produce_materially_distinct_records
#assert_compiled specialist_steps_and_final_route_are_both_charged_exactly
#assert_compiled route_changes_cost_reward_and_artifact_at_fixed_extraction
#assert_compiled all_six_authored_route_extraction_outcomes_are_bounded_and_declared
#assert_compiled combined_field_record_replays_every_signed_handoff_exactly
#assert_compiled unchecked_record_projection_readmits_after_exact_replay
#assert_compiled recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary
#assert_compiled hostile_mixed_crew_strategy_refused
#assert_compiled hostile_deep_recovery_without_unanimity_refused
#assert_compiled hostile_private_observation_substitution_refused
#assert_compiled hostile_stale_predecessor_root_refused
#assert_compiled hostile_handoff_signature_substitution_refused
#assert_compiled hostile_full_field_decision_substitution_refused_by_signature
#assert_compiled hostile_signature_issued_for_other_seat_refused
#assert_compiled hostile_signing_suite_substitution_refused
#assert_compiled hostile_public_message_digest_submitted_as_signature_refused
#assert_compiled hostile_combined_record_route_substitution_refused
#assert_compiled hostile_expanded_record_mutation_matrix_refused

/-! ## The production ML-DSA-65 signing suite, and the cross-language KAT

These are the pins that run the REAL executable FIPS 204 verify over signatures the Rust
`fips204` crate produced.  They are the expensive half of this module and the reason the
coupling mattered: a stale KAT vector reddened the archive's own build. -/

namespace ProductionSigning

theorem observation_codes_are_injective :
    check_observation_codes_are_injective = true := by native_decide

theorem decision_codes_are_injective :
    check_decision_codes_are_injective = true := by native_decide

theorem shake_digest_lengths_hold_on_instances :
    check_shake_digest_lengths_hold_on_instances = true := by native_decide

theorem production_suite_ids_are_distinct_and_not_the_fixture_ids :
    check_production_suite_ids_are_distinct_and_not_the_fixture_ids = true := by native_decide

theorem kat_player_key_is_the_seat0_public_key_digest :
    check_kat_player_key_is_the_seat0_public_key_digest = true := by native_decide

theorem kat_wrong_public_key_digest_is_not_the_seat_key :
    check_kat_wrong_public_key_digest_is_not_the_seat_key = true := by native_decide

theorem production_activation_seals_the_kat_mission :
    check_production_activation_seals_the_kat_mission = true := by native_decide

theorem production_activation_refuses_the_fixture_suite_config :
    check_production_activation_refuses_the_fixture_suite_config = true := by native_decide

theorem kat_envelopes_are_exact :
    check_kat_envelopes_are_exact = true := by native_decide

theorem kat_messages_are_the_pinned_bytes :
    check_kat_messages_are_the_pinned_bytes = true := by native_decide

theorem kat_seat_admission_signature_verifies_cross_language :
    check_kat_seat_admission_signature_verifies_cross_language = true := by native_decide

theorem kat_handoff_signature_verifies_cross_language :
    check_kat_handoff_signature_verifies_cross_language = true := by native_decide

theorem kat_one_seats_signed_handoff_is_executed_by_the_kernel :
    katFirstHandoffExecutesB = true := by native_decide

theorem kat_tampered_signature_byte_is_refused :
    check_kat_tampered_signature_byte_is_refused = true := by native_decide

theorem kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin :
    check_kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin = true := by
  native_decide

theorem kat_signature_does_not_transfer_to_a_different_body :
    check_kat_signature_does_not_transfer_to_a_different_body = true := by native_decide

theorem kat_seat_admission_envelope_is_refused_as_a_handoff :
    check_kat_seat_admission_envelope_is_refused_as_a_handoff = true := by native_decide

theorem kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed :
    katStepSurfaceHandsBackTheSignedBytesB = true := by native_decide

theorem kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key :
    katStepSurfaceRefusesAWrongKeyEnvelopeB = true := by native_decide

#assert_compiled observation_codes_are_injective
#assert_compiled decision_codes_are_injective
#assert_compiled shake_digest_lengths_hold_on_instances
#assert_compiled production_suite_ids_are_distinct_and_not_the_fixture_ids
#assert_compiled kat_player_key_is_the_seat0_public_key_digest
#assert_compiled kat_wrong_public_key_digest_is_not_the_seat_key
#assert_compiled production_activation_seals_the_kat_mission
#assert_compiled production_activation_refuses_the_fixture_suite_config
#assert_compiled kat_envelopes_are_exact
#assert_compiled kat_messages_are_the_pinned_bytes
#assert_compiled kat_seat_admission_signature_verifies_cross_language
#assert_compiled kat_handoff_signature_verifies_cross_language
#assert_compiled kat_one_seats_signed_handoff_is_executed_by_the_kernel
#assert_compiled kat_tampered_signature_byte_is_refused
#assert_compiled kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin
#assert_compiled kat_signature_does_not_transfer_to_a_different_body
#assert_compiled kat_seat_admission_envelope_is_refused_as_a_handoff
#assert_compiled kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed
#assert_compiled kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key

end ProductionSigning

end Dregg2.Games.PathOfAngels.CrewFieldMission
