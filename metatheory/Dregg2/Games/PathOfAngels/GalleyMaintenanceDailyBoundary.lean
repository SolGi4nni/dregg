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

theorem commons_fixtures_are_private : True := by
  fail_if_success (have _ := fixtureCommonsRaw)
  fail_if_success (have _ := fixtureCommons)
  fail_if_success (have _ := brothChoice)
  fail_if_success (have _ := afterFirstCommonsVisit)
  trivial

theorem unchecked_daily_steps_are_private : True := by
  fail_if_success (have _ := participantStep)
  fail_if_success (have _ := openMaintenanceStep)
  fail_if_success (have _ := performStep)
  fail_if_success (have _ := visitCommonsStep)
  fail_if_success (have _ := recordOutputStep)
  trivial

theorem raw_replay_surface_is_private : True := by
  fail_if_success (have _ := initialState)
  fail_if_success (have _ := reduce)
  fail_if_success (have _ := nextEnvelope)
  fail_if_success (have _ := applySourcedEvent)
  fail_if_success (have _ := proposeDaily)
  trivial

theorem activation_authority_is_opaque : True := by
  fail_if_success (have _ := DailyActivationProvenance.mk)
  fail_if_success (have _ := DailyActivationCapability.mk)
  fail_if_success (have _ := ActivatedDaily.mk)
  trivial

theorem command_and_output_authority_are_opaque : True := by
  fail_if_success (have _ := OutputCommitProvenance.mk)
  fail_if_success (have _ := DailyOutputCommitCapability.mk)
  fail_if_success (have _ := AdmittedDurableOutput.mk)
  fail_if_success (have _ := DailyCommandCapability.mk)
  fail_if_success (have _ := AdmittedDailyCommand.mk)
  trivial

theorem durable_continuation_is_opaque : True := by
  fail_if_success (have _ := DailyDeploymentSnapshot.mk)
  fail_if_success (have _ := DailyPersistenceCapability.mk)
  fail_if_success (have _ := DailyRootGenesisCapability.mk)
  fail_if_success (have _ := DailyRootCertificate.mk)
  fail_if_success (have _ := DurableDailyLoad.mk)
  fail_if_success (have _ := PersistedDailyRuntime.mk)
  fail_if_success (have _ := PersistedDailyTransition.mk)
  fail_if_success (have _ := DailyTransitionCandidate.mk)
  trivial

theorem global_output_registry_authority_is_opaque : True := by
  fail_if_success (have _ := OutputRegistryState.mk)
  fail_if_success (have _ := OutputRegistryCandidate.mk)
  fail_if_success (have _ := ConsumedDurableOutput.mk)
  fail_if_success (have _ := OutputRegistryPersistenceCapability.mk)
  fail_if_success (have _ := OutputRegistryGenesisCapability.mk)
  fail_if_success (have _ := OutputRegistryGenesisCertificate.mk)
  fail_if_success (have _ := DurableOutputRegistryLoad.mk)
  fail_if_success (have _ := PersistedOutputRegistry.mk)
  fail_if_success (have _ := PersistedOutputRegistryTransition.mk)
  fail_if_success (have _ := CommittedOutputConsumption.mk)
  trivial

theorem cross_deployment_cas_receipts_cannot_be_relabelled : True := by
  fail_if_success (have _ := PersistedDailyTransition.mk)
  fail_if_success (have _ := PersistedOutputRegistryTransition.mk)
  trivial

theorem shared_host_provisioning_portal_is_opaque : True := by
  fail_if_success (have _ := HostInitializer.mk)
  fail_if_success (have _ := ProvisionedCapabilityBundle.mk)
  fail_if_success (have _ := ProvisionedDeployment.mk)
  trivial

#check admitDailyActivation
#check admitDurableOutput
#check admitDailyCommand
#check admitPersistedDailyRuntime
#check dailyGenesisSnapshot
#check bootstrapDailyRoot
#check startPersistedDaily
#check admitDurableDailyLoad
#check admitDailyCASReceipt
#check proposePersistedDaily
#check continuePersistedDaily
#check PersistedDailyTransition.deployment_scoped
#check admitPersistedDailyRuntime_wrong_cursor_version
#check admitDurableOutputRegistryLoad
#check outputRegistryGenesisState
#check bootstrapOutputRegistry
#check startOutputRegistry
#check admitPersistedOutputRegistry
#check proposePersistedOutputConsumption
#check admitOutputRegistryCASReceipt
#check continueOutputConsumption
#check PersistedOutputRegistryTransition.deployment_scoped
#check ActivatedDaily.cap_pins_deployment_and_key
#check provisionCapabilities
#check initializeDeployment

#assert_axioms daily_state_constructor_is_private
#assert_axioms exact_output_constructor_is_private
#assert_axioms post_ballot_fixture_is_private
#assert_axioms authored_and_finalized_fixtures_are_private
#assert_axioms commons_fixtures_are_private
#assert_axioms unchecked_daily_steps_are_private
#assert_axioms raw_replay_surface_is_private
#assert_axioms activation_authority_is_opaque
#assert_axioms command_and_output_authority_are_opaque
#assert_axioms durable_continuation_is_opaque
#assert_axioms global_output_registry_authority_is_opaque
#assert_axioms cross_deployment_cas_receipts_cannot_be_relabelled
#assert_axioms shared_host_provisioning_portal_is_opaque

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyBoundary
