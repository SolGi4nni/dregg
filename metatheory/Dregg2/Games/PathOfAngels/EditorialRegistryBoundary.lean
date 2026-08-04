/-
# EditorialRegistryBoundary — fixture and authority privacy regression teeth

The editorial registry's executable fixtures mint opaque origin, genesis,
curator, root-resolution, and canonical-store authority internally.  This
separate importing module pins that none of those fixture producers, envelopes,
or derived canonical-looking states are part of the external API.
-/
import Dregg2.Games.PathOfAngels.EditorialRegistry
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EditorialRegistryBoundary

open Dregg2.Games.PathOfAngels.EditorialRegistry

set_option autoImplicit false

theorem fixture_provisional_producers_are_private : True := by
  fail_if_success (have _ := fixtureProvisionalA?)
  fail_if_success (have _ := fixtureProvisionalB?)
  trivial

theorem fixture_policy_producer_is_private : True := by
  fail_if_success (have _ := fixtureIdentity)
  fail_if_success (have _ := fixturePolicy)
  trivial

theorem fixture_genesis_state_producers_are_private : True := by
  fail_if_success (have _ := fixtureOpened?)
  fail_if_success (have _ := fixtureInitial)
  trivial

theorem fixture_envelopes_are_private : True := by
  fail_if_success (have _ := promoteA)
  fail_if_success (have _ := competingPromoteB)
  fail_if_success (have _ := supersedeAWithB)
  fail_if_success (have _ := retractB)
  trivial

theorem fixture_derived_state_producers_are_private : True := by
  fail_if_success (have _ := afterPromoteA?)
  fail_if_success (have _ := afterSupersede?)
  fail_if_success (have _ := afterRetraction?)
  trivial

theorem opaque_authority_constructors_are_private : True := by
  fail_if_success (have _ := ProvisionalOriginCapability.mk)
  fail_if_success (have _ := ActorRootImplementation.mk)
  fail_if_success (have _ := GenesisCapability.mk)
  fail_if_success (have _ := CuratorCapability.mk)
  fail_if_success (have _ := CanonicalCasCommit.mk)
  trivial

#assert_axioms fixture_provisional_producers_are_private
#assert_axioms fixture_policy_producer_is_private
#assert_axioms fixture_genesis_state_producers_are_private
#assert_axioms fixture_envelopes_are_private
#assert_axioms fixture_derived_state_producers_are_private
#assert_axioms opaque_authority_constructors_are_private

end Dregg2.Games.PathOfAngels.EditorialRegistryBoundary
