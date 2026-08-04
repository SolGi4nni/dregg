/-
# GalleyMaintenanceDailyBoundary — authority and fixture privacy teeth
-/
import Dregg2.Games.PathOfAngels.GalleyMaintenanceDaily
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyBoundary

open Dregg2.Games.PathOfAngels.GalleyMaintenanceDaily

set_option autoImplicit false

theorem daily_state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem exact_output_constructor_is_private : True := by
  fail_if_success (have _ := ExactFinalizedOutput.mk)
  trivial

theorem post_ballot_fixture_is_private : True := by
  fail_if_success (have _ := fixtureMaintenanceReady)
  fail_if_success (have _ := fixtureCompleted)
  fail_if_success (have _ := fixtureRecorded)
  trivial

theorem authored_and_finalized_fixtures_are_private : True := by
  fail_if_success (have _ := fixtureSpec)
  fail_if_success (have _ := fixtureFinalizedPayload)
  fail_if_success (have _ := fixtureReplay)
  trivial

#assert_axioms daily_state_constructor_is_private
#assert_axioms exact_output_constructor_is_private
#assert_axioms post_ballot_fixture_is_private
#assert_axioms authored_and_finalized_fixtures_are_private

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyBoundary
