/-
# CrewRelayExpeditionBoundary — constructor-privacy regression teeth

This separate module proves that importing the relay exposes observers and the
checked producers, but not the constructors that would forge deck activation,
seat authority, completion, settlement, or judge output.
-/
import Dregg2.Games.PathOfAngels.CrewRelayExpedition
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewRelayExpeditionBoundary

open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

theorem deck_binding_constructor_is_private : True := by
  fail_if_success (have _ := DeckBinding.mk)
  trivial

theorem config_and_verifier_selection_constructor_is_private : True := by
  fail_if_success (have _ := Config.mk)
  trivial

theorem canonical_run_admission_constructor_is_private : True := by
  fail_if_success (have _ := CanonicalRunAdmission.mk)
  trivial

theorem raw_initial_state_producer_is_private : True := by
  fail_if_success (have _ := initialState)
  trivial

theorem fixture_run_admission_minter_is_private : True := by
  fail_if_success (have _ := testRunAdmission)
  trivial

/-- Regression teeth for the fixture-only authority path.  These helpers mint
test admission/signature capabilities internally and therefore must never be an
importable API over an arbitrary caller-supplied `Config`. -/
theorem fixture_capability_producer_is_private : True := by
  fail_if_success (have _ := testCapability?)
  trivial

theorem fixture_turn_producer_is_private : True := by
  fail_if_success (have _ := testTurn?)
  trivial

theorem fixture_driver_is_private : True := by
  fail_if_success (have _ := driveTest)
  trivial

theorem fixture_completion_producer_is_private : True := by
  fail_if_success (have _ := completionFor?)
  trivial

/-- Even a fully signed raw transcript has no raw-only authority decoder.  Both
wire producers require an opaque canonical run admission as their first
explicit argument. -/
theorem never_admitted_wire_record_has_no_record_authority_producer
    (config : Config) : config = config := by
  fail_if_success
    (have _ : RawCombinedExtractionRecord →
        Option (CombinedExtractionRecord config) :=
      @admitCombinedExtractionRecord? config)
  rfl

theorem never_admitted_wire_record_has_no_completion_authority_producer
    (config : Config) : config = config := by
  fail_if_success
    (have _ : RawCombinedExtractionRecord →
        Option (CompletedRelayCapability config) :=
      @admitCompletedRelay? config)
  rfl

theorem seat_capability_constructor_is_private : True := by
  fail_if_success (have _ := SeatCapability.mk)
  trivial

theorem relay_state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem extraction_record_constructor_is_private : True := by
  fail_if_success (have _ := CombinedExtractionRecord.mk)
  trivial

theorem completed_capability_constructor_is_private : True := by
  fail_if_success (have _ := CompletedRelayCapability.mk)
  trivial

theorem step_result_constructor_is_private : True := by
  fail_if_success (have _ := StepResult.mk)
  trivial

theorem settlement_state_constructor_is_private : True := by
  fail_if_success (have _ := SettlementState.mk)
  trivial

theorem canonical_settlement_genesis_constructor_is_private : True := by
  fail_if_success (have _ := CanonicalSettlementGenesis.mk)
  trivial

theorem settlement_registry_constructor_is_private : True := by
  fail_if_success (have _ := SettlementRegistry.mk)
  trivial

theorem settlement_transition_constructor_is_private : True := by
  fail_if_success (have _ := SettlementTransition.mk)
  trivial

#assert_axioms deck_binding_constructor_is_private
#assert_axioms config_and_verifier_selection_constructor_is_private
#assert_axioms canonical_run_admission_constructor_is_private
#assert_axioms raw_initial_state_producer_is_private
#assert_axioms fixture_run_admission_minter_is_private
#assert_axioms fixture_capability_producer_is_private
#assert_axioms fixture_turn_producer_is_private
#assert_axioms fixture_driver_is_private
#assert_axioms fixture_completion_producer_is_private
#assert_axioms never_admitted_wire_record_has_no_record_authority_producer
#assert_axioms never_admitted_wire_record_has_no_completion_authority_producer
#assert_axioms seat_capability_constructor_is_private
#assert_axioms relay_state_constructor_is_private
#assert_axioms extraction_record_constructor_is_private
#assert_axioms completed_capability_constructor_is_private
#assert_axioms step_result_constructor_is_private
#assert_axioms settlement_state_constructor_is_private
#assert_axioms canonical_settlement_genesis_constructor_is_private
#assert_axioms settlement_registry_constructor_is_private
#assert_axioms settlement_transition_constructor_is_private

end Dregg2.Games.PathOfAngels.CrewRelayExpeditionBoundary
