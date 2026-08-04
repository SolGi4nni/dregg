/-
# HolderMechanicsBoundary — admitted-grant and fixture privacy teeth
-/
import Dregg2.Games.PathOfAngels.HolderMechanics
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.HolderMechanicsBoundary

open Dregg2.Games.PathOfAngels.HolderMechanics

set_option autoImplicit false

theorem admitted_grant_constructor_is_private : True := by
  fail_if_success (have _ := AdmittedHoldingGrant.mk)
  trivial

theorem settled_loss_evidence_constructor_is_private : True := by
  fail_if_success (have _ := SettledLossEvidence.mk)
  trivial

theorem holder_state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem executable_grant_fixture_is_private : True := by
  fail_if_success (have _ := fixtureGrantForPolicy)
  fail_if_success (have _ := grantA1)
  trivial

theorem executable_loss_fixture_is_private : True := by
  fail_if_success (have _ := fixtureLossEvidenceForPolicy)
  fail_if_success (have _ := insuranceEvidence)
  trivial

theorem executable_policy_and_event_fixtures_are_private : True := by
  fail_if_success (have _ := fixturePolicy)
  fail_if_success (have _ := sideEvent)
  fail_if_success (have _ := sourcedSideEvent)
  trivial

theorem executable_derived_states_are_private : True := by
  fail_if_success (have _ := afterSide)
  fail_if_success (have _ := afterChoir)
  fail_if_success (have _ := afterSponsor)
  fail_if_success (have _ := afterInsurance)
  fail_if_success (have _ := afterPublic)
  trivial

#assert_axioms admitted_grant_constructor_is_private
#assert_axioms settled_loss_evidence_constructor_is_private
#assert_axioms holder_state_constructor_is_private
#assert_axioms executable_grant_fixture_is_private
#assert_axioms executable_loss_fixture_is_private
#assert_axioms executable_policy_and_event_fixtures_are_private
#assert_axioms executable_derived_states_are_private

end Dregg2.Games.PathOfAngels.HolderMechanicsBoundary
