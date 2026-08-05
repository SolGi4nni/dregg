/-
# Galley Commons external admission boundary

This module imports the implementation as an ordinary consumer.  Its negative
elaboration proofs ensure production callers can use the checked admission API,
but cannot reach authority constructors, the deployment capability constructor,
or test-only fixture minters.
-/
import Dregg2.Games.PathOfAngels.GalleyCommons
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyCommonsBoundary

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.GalleyCommons

set_option autoImplicit false

theorem genesis_constructor_private : True := by
  fail_if_success
    (have _constructor := GenesisAuthority.mk)
  trivial

theorem finality_constructor_private : True := by
  fail_if_success
    (have _constructor := FinalizedEpochCertificate.mk)
  trivial

theorem command_constructor_private : True := by
  fail_if_success
    (have _constructor := AuthenticatedCommand.mk)
  trivial

theorem admission_capability_constructor_private : True := by
  fail_if_success
    (have _constructor := AdmissionCapability.mk)
  trivial

theorem finality_capability_constructor_private : True := by
  fail_if_success
    (have _constructor := ConsensusFinalityCapability.mk)
  trivial

theorem admission_provenance_constructor_private : True := by
  fail_if_success
    (have _constructor := AdmissionProvenance.mk)
  trivial

theorem persistence_receipt_constructor_private : True := by
  fail_if_success
    (have _constructor := PersistedTransition.mk)
  trivial

theorem cross_deployment_cas_receipt_cannot_be_relabelled : True := by
  -- Deployment is a type index; importers cannot reconstruct the private
  -- receipt at a different index from an unscoped host fact.
  fail_if_success
    (have _constructor := PersistedTransition.mk)
  trivial

theorem persistence_capability_constructor_private : True := by
  fail_if_success
    (have _constructor := PersistenceCapability.mk)
  trivial

theorem durable_load_constructor_private : True := by
  fail_if_success
    (have _constructor := DurableStoreLoad.mk)
  trivial

theorem deployment_root_authority_is_opaque : True := by
  fail_if_success
    (have _constructor := DeploymentRootGenesisCapability.mk)
  fail_if_success
    (have _constructor := DeploymentRootCertificate.mk)
  trivial

theorem host_provisioning_bundle_is_opaque : True := by
  fail_if_success
    (have _constructor := HostInitializer.mk)
  fail_if_success
    (have _constructor := ProvisionedDeployment.mk)
  trivial

theorem persisted_runtime_constructor_private : True := by
  fail_if_success
    (have _constructor := PersistedPoolRuntime.mk)
  trivial

theorem transition_candidate_constructor_private : True := by
  fail_if_success
    (have _constructor := TransitionCandidate.mk)
  trivial

theorem raw_candidate_executor_private : True := by
  fail_if_success
    (have _executor := execute)
  trivial

theorem settled_credit_constructor_private : True := by
  fail_if_success
    (have _constructor := GalleyCredit.mk)
  trivial

theorem fixture_genesis_minter_private : True := by
  fail_if_success
    (have _fixture := fixtureGenesisAuthority)
  trivial

theorem fixture_finality_minter_private : True := by
  fail_if_success
    (have _fixture := fixtureFinality)
  trivial

theorem fixture_command_minter_private : True := by
  fail_if_success
    (have _fixture := fixtureAuthority)
  trivial

theorem raw_settled_projection_private : True := by
  fail_if_success
    (have _projection := creditFromSettled)
  trivial

-- Public surface smoke checks: importers can call these only with the opaque,
-- oracle-indexed deployment capability supplied by the trusted host bridge.
#check admitGenesis
#check deploymentGenesisStore
#check bootstrapDeploymentRoot
#check provisionDeployment
#check admitConsensusFinality
#check admitCommand
#check admitSettledInclusion
#check admitCASReceipt
#check admitDurableStoreLoad
#check admitPersistedRuntime
#check proposePersisted
#check continueFromCommit
#check PersistedTransition.deployment_scoped

#assert_axioms genesis_constructor_private
#assert_axioms finality_constructor_private
#assert_axioms command_constructor_private
#assert_axioms admission_capability_constructor_private
#assert_axioms finality_capability_constructor_private
#assert_axioms admission_provenance_constructor_private
#assert_axioms persistence_receipt_constructor_private
#assert_axioms cross_deployment_cas_receipt_cannot_be_relabelled
#assert_axioms persistence_capability_constructor_private
#assert_axioms durable_load_constructor_private
#assert_axioms deployment_root_authority_is_opaque
#assert_axioms host_provisioning_bundle_is_opaque
#assert_axioms persisted_runtime_constructor_private
#assert_axioms transition_candidate_constructor_private
#assert_axioms raw_candidate_executor_private
#assert_axioms settled_credit_constructor_private
#assert_axioms fixture_genesis_minter_private
#assert_axioms fixture_finality_minter_private
#assert_axioms fixture_command_minter_private
#assert_axioms raw_settled_projection_private

end Dregg2.Games.PathOfAngels.GalleyCommonsBoundary
