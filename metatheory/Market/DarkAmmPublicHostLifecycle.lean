/-
# Market.DarkAmmPublicHostLifecycle — two-phase secretless host lifecycle.

The public-only Dark AMM host first evaluates and stages an exact encrypted
candidate, then later receives an independently verified equality receipt and
commits that candidate. This file separates those phases and proves their
atomic state-machine laws.

As in `DarkAmmPublicHost`, ciphertext state, public state identity, nonce
construction, receipt verification, and wire encoding are parameters. The
theorems do not claim BFV, fhe.rs, signature, MPC, or storage soundness.
-/

import Market.DarkAmmPublicHost
import Dregg2.Tactics

namespace Market.DarkAmmPublicHostLifecycle

set_option autoImplicit false

open Market.DarkAmmPublicHost

abbrev PendingId := Nat

/-- Exact work retained between public evaluation and collective decision. -/
structure PendingCandidate (CiphertextState : Type) where
  pendingId : PendingId
  candidate : Candidate CiphertextState

/-- Complete two-phase process image. `committed` is authoritative; `pending`
is disposable work which has not changed it. -/
structure LifecycleState (CiphertextState : Type) where
  committed : HostState CiphertextState
  pending : Option (PendingCandidate CiphertextState)

/-- Staging authority produced by the evaluator. It records that the candidate
was bound to the exact committed public state and that no other work was
already pending. -/
structure StageCapability {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (before : LifecycleState CiphertextState)
    (candidate : Candidate CiphertextState) where
  pendingId : PendingId
  empty : before.pending = none
  candidateBinding : CandidateBinds identify nonceOf before.committed candidate

/-- Stage exact evaluated work. The capability is consumed by the call; only
its public pending id and exact candidate remain. -/
def stage {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    (before : LifecycleState CiphertextState)
    (candidate : Candidate CiphertextState)
    (capability : StageCapability identify nonceOf before candidate) :
    LifecycleState CiphertextState :=
  { committed := before.committed
    pending := some { pendingId := capability.pendingId, candidate } }

theorem staging_preserves_committed_state
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    (before : LifecycleState CiphertextState)
    (candidate : Candidate CiphertextState)
    (capability : StageCapability identify nonceOf before candidate) :
    (stage before candidate capability).committed = before.committed :=
  rfl

theorem staging_records_exact_candidate
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    (before : LifecycleState CiphertextState)
    (candidate : Candidate CiphertextState)
    (capability : StageCapability identify nonceOf before candidate) :
    (stage before candidate capability).pending =
      some { pendingId := capability.pendingId, candidate } :=
  rfl

/-- Public commit submission. Candidate identities are repeated so an adapter
cannot accidentally select pending work by only one underspecified handle. -/
structure CommitRequest where
  pendingId : PendingId
  beforeStateId : StateId
  afterStateId : StateId
  receipt : AttestedReceipt
  deriving DecidableEq, Repr

/-- Every check which must hold before mutation. `verifyReceipt` is the
external configured verifier result; all structural and replay facts remain
separate fields. -/
structure CommitAuthorization {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool)
    (policy : ReceiptPolicy)
    (before : LifecycleState CiphertextState)
    (pending : PendingCandidate CiphertextState)
    (request : CommitRequest) : Prop where
  pendingId : request.pendingId = pending.pendingId
  submittedBeforeId : request.beforeStateId = pending.candidate.beforeStateId
  submittedAfterId : request.afterStateId = pending.candidate.afterStateId
  candidateBinding : CandidateBinds identify nonceOf before.committed pending.candidate
  policyBinding : ReceiptBindsPolicy policy request.receipt
  poolDomain : policy.plaintextModulus =
    before.committed.material.evaluation.plaintextModulus
  verified : verifyReceipt policy request.receipt = true
  receiptNonce : request.receipt.candidateNonce = pending.candidate.decisionNonce
  trueBit : request.receipt.equal = true
  fresh : request.receipt.replayId ∉ before.committed.usedReplayIds

def committedLifecycleState {CiphertextState : Type}
    (before : LifecycleState CiphertextState)
    (pending : PendingCandidate CiphertextState)
    (request : CommitRequest) : LifecycleState CiphertextState :=
  { committed := acceptedState before.committed pending.candidate request.receipt
    pending := none }

def CommitAccepts {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool)
    (policy : ReceiptPolicy)
    (before : LifecycleState CiphertextState)
    (request : CommitRequest)
    (after : LifecycleState CiphertextState) : Prop :=
  ∃ pending,
    before.pending = some pending ∧
    CommitAuthorization identify nonceOf verifyReceipt policy before pending request ∧
    after = committedLifecycleState before pending request

inductive CommitDecision where
  | accepted
  | refused
  deriving DecidableEq, Repr

/-- Refusal at any phase holds both committed and pending state. -/
def CommitStep {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool)
    (policy : ReceiptPolicy)
    (before : LifecycleState CiphertextState)
    (request : CommitRequest)
    (decision : CommitDecision)
    (after : LifecycleState CiphertextState) : Prop :=
  match decision with
  | .accepted => CommitAccepts identify nonceOf verifyReceipt policy before request after
  | .refused => after = before

/-- No staged work means there is nothing an otherwise valid receipt can
commit. -/
theorem no_pending_candidate_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hempty : before.pending = none) :
    ¬ CommitStep identify nonceOf verifyReceipt policy before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, hauthorization, hafter⟩
  rw [hempty] at hpending
  contradiction

/-- A wrong pending handle or repeated before/after identity cannot select the
actual staged candidate. The premise talks only about whichever exact pending
value the host contains. -/
theorem wrong_pending_or_identity_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hwrong : ∀ pending, before.pending = some pending →
      request.pendingId ≠ pending.pendingId ∨
      request.beforeStateId ≠ pending.candidate.beforeStateId ∨
      request.afterStateId ≠ pending.candidate.afterStateId) :
    ¬ CommitStep identify nonceOf verifyReceipt policy before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, hauthorization, hafter⟩
  rcases hwrong pending hpending with hpendingId | hbeforeId | hafterId
  · exact hpendingId hauthorization.pendingId
  · exact hbeforeId hauthorization.submittedBeforeId
  · exact hafterId hauthorization.submittedAfterId

/-- Pending work becomes stale if committed state advances by another path;
fresh receipt material cannot repair its before-state mismatch. -/
theorem stale_pending_candidate_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hstale : ∀ pending, before.pending = some pending →
      pending.candidate.beforeStateId ≠ identify before.committed.material) :
    ¬ CommitStep identify nonceOf verifyReceipt policy before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, hauthorization, hafter⟩
  exact (hstale pending hpending) hauthorization.candidateBinding.beforeState

theorem false_receipt_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hfalse : request.receipt.equal = false) :
    ¬ CommitStep identify nonceOf verifyReceipt policy before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, hauthorization, hafter⟩
  have htrue := hauthorization.trueBit
  simp [hfalse] at htrue

theorem unverified_receipt_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hunverified : verifyReceipt policy request.receipt = false) :
    ¬ CommitStep identify nonceOf verifyReceipt policy before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, hauthorization, hafter⟩
  have hverified := hauthorization.verified
  simp [hunverified] at hverified

theorem replayed_receipt_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hreplayed : request.receipt.replayId ∈ before.committed.usedReplayIds) :
    ¬ CommitStep identify nonceOf verifyReceipt policy before request .accepted after := by
  intro hstep
  rcases hstep with ⟨pending, hpending, hauthorization, hafter⟩
  exact hauthorization.fresh hreplayed

/-- The positive branch installs exactly the staged after-state, preserves the
evaluation identity, consumes exactly the submitted fresh replay id, and clears
pending work in the same state value. -/
theorem successful_commit_installs_exact_after
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hstep : CommitStep identify nonceOf verifyReceipt policy before request .accepted after) :
    ∃ pending,
      before.pending = some pending ∧
      after.committed.material.evaluation = before.committed.material.evaluation ∧
      after.committed.material.ciphertextState = pending.candidate.afterState ∧
      identify after.committed.material = pending.candidate.afterStateId ∧
      after.committed.usedReplayIds =
        request.receipt.replayId :: before.committed.usedReplayIds ∧
      request.receipt.replayId ∉ before.committed.usedReplayIds ∧
      after.pending = none := by
  rcases hstep with ⟨pending, hpending, hauthorization, rfl⟩
  refine ⟨pending, hpending, rfl, rfl, ?_, rfl, hauthorization.fresh, rfl⟩
  exact hauthorization.candidateBinding.afterState.symm

/-- Any refused commit holds committed material, replay, and the pending value;
there is no phase-local partial mutation. -/
theorem commit_refusal_holds_complete_lifecycle
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest}
    (hstep : CommitStep identify nonceOf verifyReceipt policy before request .refused after) :
    after = before :=
  hstep

theorem commit_accepts_or_holds
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest} {decision : CommitDecision}
    (hstep : CommitStep identify nonceOf verifyReceipt policy before request decision after) :
    (decision = .accepted ∧
      CommitAccepts identify nonceOf verifyReceipt policy before request after) ∨
    (decision = .refused ∧ after = before) := by
  cases decision with
  | accepted => exact Or.inl ⟨rfl, hstep⟩
  | refused => exact Or.inr ⟨rfl, hstep⟩

/-- Abandoning staged work clears only the pending field. -/
def abandon {CiphertextState : Type}
    (before : LifecycleState CiphertextState) : LifecycleState CiphertextState :=
  { committed := before.committed, pending := none }

theorem abandoned_pending_preserves_committed_state
    {CiphertextState : Type} (before : LifecycleState CiphertextState) :
    (abandon before).committed = before.committed ∧
    (abandon before).pending = none :=
  ⟨rfl, rfl⟩

/-- After abandonment there is no pending value from which any receipt could
partially settle. A new explicit staging phase is required. -/
theorem abandoned_pending_cannot_commit
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {verifyReceipt : ReceiptPolicy → AttestedReceipt → Bool}
    {policy : ReceiptPolicy} {before after : LifecycleState CiphertextState}
    {request : CommitRequest} :
    ¬ CommitStep identify nonceOf verifyReceipt policy (abandon before) request
        .accepted after := by
  exact no_pending_candidate_cannot_commit rfl

/-- Pure full-lifecycle restart theorem. The caller supplies the exact codec
round-trip premise for both committed and pending state. -/
def restart {CiphertextState : Type}
    (state : LifecycleState CiphertextState) : LifecycleState CiphertextState :=
  state

theorem decode_encode_restart_preserves_committed_and_pending
    {CiphertextState Wire : Type}
    (encode : LifecycleState CiphertextState → Wire)
    (decode : Wire → Option (LifecycleState CiphertextState))
    (state : LifecycleState CiphertextState)
    (hroundtrip : decode (encode state) = some state) :
    Option.map restart (decode (encode state)) = some state := by
  simp [hroundtrip, restart]

#assert_axioms staging_preserves_committed_state
#assert_axioms staging_records_exact_candidate
#assert_axioms no_pending_candidate_cannot_commit
#assert_axioms wrong_pending_or_identity_cannot_commit
#assert_axioms stale_pending_candidate_cannot_commit
#assert_axioms false_receipt_cannot_commit
#assert_axioms unverified_receipt_cannot_commit
#assert_axioms replayed_receipt_cannot_commit
#assert_axioms successful_commit_installs_exact_after
#assert_axioms commit_refusal_holds_complete_lifecycle
#assert_axioms commit_accepts_or_holds
#assert_axioms abandoned_pending_preserves_committed_state
#assert_axioms abandoned_pending_cannot_commit
#assert_axioms decode_encode_restart_preserves_committed_and_pending

/- Staging and abandonment remain independent of receipt verification and
commit semantics. -/
-- POSITIVE CONTROL for the rejectors below: reached only through the commit proof's term.
#assert_depends_on Market.DarkAmmPublicHostLifecycle.successful_commit_installs_exact_after
  [Market.DarkAmmPublicHostLifecycle.committedLifecycleState]

#assert_not_depends_on Market.DarkAmmPublicHostLifecycle.stage [
  Market.DarkAmmPublicHostLifecycle.CommitAuthorization,
  Market.DarkAmmPublicHostLifecycle.CommitAccepts,
  Market.DarkAmmPublicHostLifecycle.CommitStep]

#assert_not_depends_on Market.DarkAmmPublicHostLifecycle.abandon [
  Market.DarkAmmPublicHostLifecycle.CommitAuthorization,
  Market.DarkAmmPublicHostLifecycle.CommitAccepts,
  Market.DarkAmmPublicHostLifecycle.CommitStep]

#assert_all_clean [
  Market.DarkAmmPublicHostLifecycle.staging_preserves_committed_state,
  Market.DarkAmmPublicHostLifecycle.staging_records_exact_candidate,
  Market.DarkAmmPublicHostLifecycle.no_pending_candidate_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.wrong_pending_or_identity_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.stale_pending_candidate_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.false_receipt_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.unverified_receipt_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.replayed_receipt_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.successful_commit_installs_exact_after,
  Market.DarkAmmPublicHostLifecycle.commit_refusal_holds_complete_lifecycle,
  Market.DarkAmmPublicHostLifecycle.commit_accepts_or_holds,
  Market.DarkAmmPublicHostLifecycle.abandoned_pending_preserves_committed_state,
  Market.DarkAmmPublicHostLifecycle.abandoned_pending_cannot_commit,
  Market.DarkAmmPublicHostLifecycle.decode_encode_restart_preserves_committed_and_pending]

end Market.DarkAmmPublicHostLifecycle
