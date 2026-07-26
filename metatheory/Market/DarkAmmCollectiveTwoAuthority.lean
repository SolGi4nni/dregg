/-
# Market.DarkAmmCollectiveTwoAuthority — atomic commit under two replay authorities.

The collective Dark AMM service has two independent authorization/replay
domains.  A same-opening authority binds hidden inputs to the exact staged
candidate; an `FHDAR001` authority authorizes the resulting equality decision.
Verifying or staging one must not consume the replay authority of the other.

This module refines the public-host lifecycle with that split.  Staging records
exact pending work while preserving committed material, sequence, and both
replay images.  Only the final accepting commit consumes both fresh replay ids,
installs the exact candidate after-state, advances sequence, and clears pending
work in one state value.  Abandonment after staging reconstructs the exact
pre-stage state.

Same-opening verification and `FHDAR001` verification remain injected
capabilities.  No theorem interprets signatures, BFV, MPC, codecs, storage, or
rollback resistance.
-/

import Market.DarkAmmPublicHostLifecycle
import Dregg2.Tactics

namespace Market.DarkAmmCollectiveTwoAuthority

set_option autoImplicit false

open Market.DarkAmmPublicHost
open Market.DarkAmmPublicHostLifecycle

/-- A separate type keeps a same-opening replay slot from being confused with
an `FHDAR001` replay id even when both are represented by integers on wire. -/
structure SameOpeningReplayId where
  value : Nat
  deriving DecidableEq, Repr

/-- Complete collective service image.  `committed.usedReplayIds` is the
`FHDAR001` replay authority; `usedSameOpeningReplayIds` is independently owned
by the same-opening authority. -/
structure CollectiveState (CiphertextState : Type) where
  committed : HostState CiphertextState
  nextSequence : Nat
  usedSameOpeningReplayIds : List SameOpeningReplayId
  pending : Option (PendingCandidate CiphertextState)

/-- Projection to the already-proved public-host lifecycle. -/
def lifecycleView {CiphertextState : Type}
    (state : CollectiveState CiphertextState) : LifecycleState CiphertextState :=
  { committed := state.committed, pending := state.pending }

/-- Reuse the lifecycle's exact candidate-binding and empty-pending staging
capability. -/
abbrev CollectiveStageCapability {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (before : CollectiveState CiphertextState)
    (candidate : Candidate CiphertextState) :=
  StageCapability identify nonceOf (lifecycleView before) candidate

/-- Stage only disposable evaluated work.  Neither replay authority, the
committed image, nor the sequence is advanced here. -/
def stage {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    (before : CollectiveState CiphertextState)
    (candidate : Candidate CiphertextState)
    (capability : CollectiveStageCapability identify nonceOf before candidate) :
    CollectiveState CiphertextState :=
  { committed := before.committed
    nextSequence := before.nextSequence
    usedSameOpeningReplayIds := before.usedSameOpeningReplayIds
    pending := some { pendingId := capability.pendingId, candidate } }

/-- Staging records the exact candidate and consumes neither replay domain. -/
theorem stage_records_exact_pending_and_preserves_precommit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    (before : CollectiveState CiphertextState)
    (candidate : Candidate CiphertextState)
    (capability : CollectiveStageCapability identify nonceOf before candidate) :
    (stage before candidate capability).committed = before.committed ∧
    (stage before candidate capability).nextSequence = before.nextSequence ∧
    (stage before candidate capability).usedSameOpeningReplayIds =
      before.usedSameOpeningReplayIds ∧
    (stage before candidate capability).committed.usedReplayIds =
      before.committed.usedReplayIds ∧
    (stage before candidate capability).pending =
      some { pendingId := capability.pendingId, candidate } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Abandon only removes disposable pending work. -/
def abandon {CiphertextState : Type}
    (before : CollectiveState CiphertextState) : CollectiveState CiphertextState :=
  { committed := before.committed
    nextSequence := before.nextSequence
    usedSameOpeningReplayIds := before.usedSameOpeningReplayIds
    pending := none }

/-- Because staging requires the prior pending slot to be empty and changes no
other field, abandoning that exact stage restores the complete prior image. -/
theorem abandon_after_stage_restores_exact_before
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    (before : CollectiveState CiphertextState)
    (candidate : Candidate CiphertextState)
    (capability : CollectiveStageCapability identify nonceOf before candidate) :
    abandon (stage before candidate capability) = before := by
  have hempty : before.pending = none := capability.empty
  cases before
  simp_all [stage, abandon, lifecycleView]

/-- Public meaning of the same-opening authority result.  It names the exact
pending handle, sequence, before/after identities, and candidate nonce. -/
structure SameOpeningAttestation where
  replayId : SameOpeningReplayId
  pendingId : PendingId
  sequence : Nat
  beforeStateId : StateId
  afterStateId : StateId
  candidateNonce : DecisionNonce
  deriving DecidableEq, Repr

/-- Fresh, externally verified same-opening authority for one exact pending
candidate.  The verifier predicate is injected; no signature bit is promoted
to this capability inside Lean. -/
structure FreshSameOpeningCapability {CiphertextState : Type}
    (SameOpeningVerified : SameOpeningAttestation → Prop)
    (before : CollectiveState CiphertextState)
    (pending : PendingCandidate CiphertextState) where
  attestation : SameOpeningAttestation
  verified : SameOpeningVerified attestation
  pendingBinding : attestation.pendingId = pending.pendingId
  sequenceBinding : attestation.sequence = before.nextSequence
  beforeBinding : attestation.beforeStateId = pending.candidate.beforeStateId
  afterBinding : attestation.afterStateId = pending.candidate.afterStateId
  nonceBinding : attestation.candidateNonce = pending.candidate.decisionNonce
  fresh : attestation.replayId ∉ before.usedSameOpeningReplayIds

/-- One commit submission carries both independently issued public envelopes. -/
structure CommitRequest where
  pendingId : PendingId
  sameOpening : SameOpeningAttestation
  decisionReceipt : AttestedReceipt
  deriving DecidableEq, Repr

/-- Complete authorization for the exact pending value found in the state.
The two capability values are independently verified and independently fresh;
equalities prevent a capability for another submitted envelope from being
reused here. -/
structure CommitAuthorization {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (SameOpeningVerified : SameOpeningAttestation → Prop)
    (ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop)
    (policy : ReceiptPolicy)
    (before : CollectiveState CiphertextState)
    (pending : PendingCandidate CiphertextState)
    (request : CommitRequest) where
  requestPending : request.pendingId = pending.pendingId
  candidateBinding : CandidateBinds identify nonceOf before.committed pending.candidate
  sameOpening : FreshSameOpeningCapability SameOpeningVerified before pending
  exactSameOpening : sameOpening.attestation = request.sameOpening
  decision : TrueFreshReceiptCapability ReceiptVerified policy before.committed pending.candidate
  exactDecisionReceipt : decision.receipt = request.decisionReceipt

/-- One atomic accepting image.  The existing `acceptedState` performs the
exact public material install and `FHDAR001` replay consumption; this wrapper
adds same-opening replay consumption, sequence advance, and pending clear. -/
def committedState {CiphertextState : Type}
    (before : CollectiveState CiphertextState)
    (pending : PendingCandidate CiphertextState)
    (request : CommitRequest) : CollectiveState CiphertextState :=
  { committed := acceptedState before.committed pending.candidate request.decisionReceipt
    nextSequence := before.nextSequence + 1
    usedSameOpeningReplayIds :=
      request.sameOpening.replayId :: before.usedSameOpeningReplayIds
    pending := none }

def CommitAccepts {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (SameOpeningVerified : SameOpeningAttestation → Prop)
    (ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop)
    (policy : ReceiptPolicy)
    (before : CollectiveState CiphertextState)
    (request : CommitRequest)
    (after : CollectiveState CiphertextState) : Prop :=
  ∃ pending,
    before.pending = some pending ∧
    ∃ _authorization : CommitAuthorization identify nonceOf SameOpeningVerified
        ReceiptVerified policy before pending request,
      after = committedState before pending request

inductive CommitDecision where
  | accepted
  | refused
  deriving DecidableEq, Repr

/-- Refusal from either authority, any binding check, or any replay check holds
the entire pre-state. -/
def CommitStep {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (SameOpeningVerified : SameOpeningAttestation → Prop)
    (ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop)
    (policy : ReceiptPolicy)
    (before : CollectiveState CiphertextState)
    (request : CommitRequest)
    (decision : CommitDecision)
    (after : CollectiveState CiphertextState) : Prop :=
  match decision with
  | .accepted => CommitAccepts identify nonceOf SameOpeningVerified ReceiptVerified
      policy before request after
  | .refused => after = before

/-- The accepted branch necessarily selected the exact pending value and both
submitted envelopes have independently fresh, bound capabilities. -/
theorem acceptance_requires_exact_pending_and_two_capabilities
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hstep : CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .accepted after) :
    ∃ pending,
      before.pending = some pending ∧
      ∃ authorization : CommitAuthorization identify nonceOf SameOpeningVerified
          ReceiptVerified policy before pending request,
        request.pendingId = pending.pendingId ∧
        authorization.sameOpening.attestation = request.sameOpening ∧
        authorization.decision.receipt = request.decisionReceipt := by
  rcases hstep with ⟨pending, hpending, authorization, hafter⟩
  exact ⟨pending, hpending, authorization, authorization.requestPending,
    authorization.exactSameOpening, authorization.exactDecisionReceipt⟩

/-- Successful commit performs the entire transition together: exact
candidate install, both exact replay-id consumptions, sequence advance, and
pending clear.  Both consumed ids were absent from their own authority before
the transition. -/
theorem successful_commit_installs_after_and_consumes_both_exact_replays
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hstep : CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .accepted after) :
    ∃ pending,
      before.pending = some pending ∧
      after.committed.material.evaluation = before.committed.material.evaluation ∧
      after.committed.material.ciphertextState = pending.candidate.afterState ∧
      identify after.committed.material = pending.candidate.afterStateId ∧
      after.nextSequence = before.nextSequence + 1 ∧
      after.usedSameOpeningReplayIds =
        request.sameOpening.replayId :: before.usedSameOpeningReplayIds ∧
      after.committed.usedReplayIds =
        request.decisionReceipt.replayId :: before.committed.usedReplayIds ∧
      request.sameOpening.replayId ∉ before.usedSameOpeningReplayIds ∧
      request.decisionReceipt.replayId ∉ before.committed.usedReplayIds ∧
      after.pending = none := by
  rcases hstep with ⟨pending, hpending, authorization, rfl⟩
  have hsameFresh :
      request.sameOpening.replayId ∉ before.usedSameOpeningReplayIds := by
    rw [← authorization.exactSameOpening]
    exact authorization.sameOpening.fresh
  have hdecisionFresh :
      request.decisionReceipt.replayId ∉ before.committed.usedReplayIds := by
    rw [← authorization.exactDecisionReceipt]
    exact authorization.decision.fresh
  refine ⟨pending, hpending, rfl, rfl, ?_, rfl, rfl, rfl,
    hsameFresh, hdecisionFresh, rfl⟩
  exact authorization.candidateBinding.afterState.symm

theorem no_pending_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hempty : before.pending = none) :
    ¬ CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, authorization, hafter⟩
  rw [hempty] at hpending
  contradiction

theorem wrong_pending_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hwrong : ∀ pending, before.pending = some pending →
      request.pendingId ≠ pending.pendingId) :
    ¬ CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, authorization, hafter⟩
  exact (hwrong pending hpending) authorization.requestPending

theorem replayed_same_opening_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hreplayed : request.sameOpening.replayId ∈ before.usedSameOpeningReplayIds) :
    ¬ CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, authorization, hafter⟩
  have hfresh : request.sameOpening.replayId ∉ before.usedSameOpeningReplayIds := by
    rw [← authorization.exactSameOpening]
    exact authorization.sameOpening.fresh
  exact hfresh hreplayed

theorem replayed_decision_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hreplayed : request.decisionReceipt.replayId ∈ before.committed.usedReplayIds) :
    ¬ CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, authorization, hafter⟩
  have hfresh : request.decisionReceipt.replayId ∉ before.committed.usedReplayIds := by
    rw [← authorization.exactDecisionReceipt]
    exact authorization.decision.fresh
  exact hfresh hreplayed

/-- Any failure is a full-state hold: neither replay domain, committed
material, sequence, nor pending work can be partially changed. -/
theorem refusal_holds_complete_state
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest}
    (hstep : CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request .refused after) :
    after = before :=
  hstep

/-- There is no phase-local outcome between full acceptance and a complete
state hold. -/
theorem commit_accepts_or_holds
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {SameOpeningVerified : SameOpeningAttestation → Prop}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy}
    {before after : CollectiveState CiphertextState}
    {request : CommitRequest} {decision : CommitDecision}
    (hstep : CommitStep identify nonceOf SameOpeningVerified ReceiptVerified policy
      before request decision after) :
    (decision = .accepted ∧
      CommitAccepts identify nonceOf SameOpeningVerified ReceiptVerified
        policy before request after) ∨
    (decision = .refused ∧ after = before) := by
  cases decision with
  | accepted => exact Or.inl ⟨rfl, hstep⟩
  | refused => exact Or.inr ⟨rfl, hstep⟩

#assert_axioms stage_records_exact_pending_and_preserves_precommit
#assert_axioms abandon_after_stage_restores_exact_before
#assert_axioms acceptance_requires_exact_pending_and_two_capabilities
#assert_axioms successful_commit_installs_after_and_consumes_both_exact_replays
#assert_axioms no_pending_cannot_commit
#assert_axioms wrong_pending_cannot_commit
#assert_axioms replayed_same_opening_cannot_commit
#assert_axioms replayed_decision_cannot_commit
#assert_axioms refusal_holds_complete_state
#assert_axioms commit_accepts_or_holds

/- Staging and abandonment cannot accidentally acquire either authorization or
commit semantics. -/
-- POSITIVE CONTROL for the rejectors below: reached only through the commit proof's term.
#assert_depends_on Market.DarkAmmCollectiveTwoAuthority.successful_commit_installs_after_and_consumes_both_exact_replays
  [Market.DarkAmmCollectiveTwoAuthority.committedState]

#assert_not_depends_on Market.DarkAmmCollectiveTwoAuthority.stage [
  Market.DarkAmmCollectiveTwoAuthority.FreshSameOpeningCapability,
  Market.DarkAmmPublicHost.TrueFreshReceiptCapability,
  Market.DarkAmmCollectiveTwoAuthority.CommitAuthorization,
  Market.DarkAmmCollectiveTwoAuthority.CommitStep]

#assert_not_depends_on Market.DarkAmmCollectiveTwoAuthority.abandon [
  Market.DarkAmmCollectiveTwoAuthority.FreshSameOpeningCapability,
  Market.DarkAmmPublicHost.TrueFreshReceiptCapability,
  Market.DarkAmmCollectiveTwoAuthority.CommitAuthorization,
  Market.DarkAmmCollectiveTwoAuthority.CommitStep]

/- Same-opening authorization has no dependency on the independently defined
`FHDAR001` receipt capability. -/
#assert_not_depends_on Market.DarkAmmCollectiveTwoAuthority.FreshSameOpeningCapability [
  Market.DarkAmmPublicHost.AttestedReceipt,
  Market.DarkAmmPublicHost.TrueFreshReceiptCapability]

#assert_all_clean [
  Market.DarkAmmCollectiveTwoAuthority.stage_records_exact_pending_and_preserves_precommit,
  Market.DarkAmmCollectiveTwoAuthority.abandon_after_stage_restores_exact_before,
  Market.DarkAmmCollectiveTwoAuthority.acceptance_requires_exact_pending_and_two_capabilities,
  Market.DarkAmmCollectiveTwoAuthority.successful_commit_installs_after_and_consumes_both_exact_replays,
  Market.DarkAmmCollectiveTwoAuthority.no_pending_cannot_commit,
  Market.DarkAmmCollectiveTwoAuthority.wrong_pending_cannot_commit,
  Market.DarkAmmCollectiveTwoAuthority.replayed_same_opening_cannot_commit,
  Market.DarkAmmCollectiveTwoAuthority.replayed_decision_cannot_commit,
  Market.DarkAmmCollectiveTwoAuthority.refusal_holds_complete_state,
  Market.DarkAmmCollectiveTwoAuthority.commit_accepts_or_holds]

end Market.DarkAmmCollectiveTwoAuthority
