/-
# Market.DarkAmmContextBoundDecision — the contextual collective-decision task law.

The Rust collective worker does not sign the context-free Dark AMM candidate
nonce.  It signs an `FHDAR001` claim whose session nonce is the digest of a
strict canonical public task.  That task binds the hosted table, sequence,
committed pre-root and material, same-opening claim, BFV/DKG/collective-key
identity, decision shape, and the exact encrypted candidate carrier.

This file authors the executable semantic law at that boundary. `TaskDigest`
is the decoded canonical preimage represented structurally, not an assertion
that BLAKE3 is injective.  The Rust codec/hash refinement must establish that a
verified wire digest denotes this exact value; after that portal, all
substitution, replay, and state-transition laws below are theorem-proved.

The candidate carrier is deliberately data, never an authoritative state
constructor.  `acceptedState` installs only the exact post-material named by a
task which also matches the host's independently pinned committed state and
pending carrier. This is the Lean image of the Rust rule that the host
reconstructs its candidate from the proved request and merely *matches* the
worker carrier.
-/

import Market.DarkAmmCollectiveTwoAuthority
import Market.DarkAmmDecisionReceipt
import Dregg2.Tactics

namespace Market.DarkAmmContextBoundDecision

set_option autoImplicit false

open Market.DarkAmmPublicHost

abbrev HostedSession := Nat
abbrev RootDigest := Nat
abbrev SameOpeningClaimDigest := Nat
abbrev MaterialDigest := Nat
abbrev ParameterDigest := Nat
abbrev KeygenDigest := Nat
abbrev CollectiveKeyDigest := Nat
abbrev CiphertextDigest := Nat

/-- Every independently pinned public field outside the encrypted candidate. -/
structure TaskContext where
  hostedSession : HostedSession
  sequence : Nat
  preRoot : RootDigest
  sameOpeningClaimDigest : SameOpeningClaimDigest
  committedMaterialDigest : MaterialDigest
  parameterDigest : ParameterDigest
  keygenDigest : KeygenDigest
  collectiveKeyDigest : CollectiveKeyDigest
  valueBits : Nat
  deriving DecidableEq, Repr

/-- Exact public encrypted carrier.  It contains identities and ciphertext
digests/bounds, not reserves, amounts, openings, a BFV secret, or a constructor
for authoritative host state. -/
structure CandidateCarrier where
  preMaterialDigest : MaterialDigest
  postMaterialDigest : MaterialDigest
  preStateDigest : CiphertextDigest
  invariantCiphertextDigest : CiphertextDigest
  postStateDigest : CiphertextDigest
  postRoot : RootDigest
  publicK : Nat
  invariantBound : Nat
  candidateNonce : DecisionNonce
  deriving DecidableEq, Repr

/-- Complete decoded meaning of `DBDTv001`. -/
structure DecisionTask where
  context : TaskContext
  candidate : CandidateCarrier
  deriving DecidableEq, Repr

/-- Semantic image of the canonical task digest.  Keeping a distinct type
prevents candidate nonces, material digests, and task digests from crossing. -/
structure TaskDigest where
  context : TaskContext
  candidate : CandidateCarrier
  deriving DecidableEq, Repr

def taskDigest (task : DecisionTask) : TaskDigest :=
  { context := task.context, candidate := task.candidate }

/-- The decoded canonical task identity loses no semantic field.  This is a
structural theorem, not a cryptographic collision-resistance theorem. -/
theorem taskDigest_injective : Function.Injective taskDigest := by
  intro a b h
  cases a
  cases b
  simp_all [taskDigest]

theorem different_context_changes_task_digest {a b : DecisionTask}
    (hcontext : a.context ≠ b.context) : taskDigest a ≠ taskDigest b := by
  intro hdigest
  exact hcontext (congrArg DecisionTask.context (taskDigest_injective hdigest))

theorem different_candidate_changes_task_digest {a b : DecisionTask}
    (hcandidate : a.candidate ≠ b.candidate) : taskDigest a ≠ taskDigest b := by
  intro hdigest
  exact hcandidate (congrArg DecisionTask.candidate (taskDigest_injective hdigest))

/-- Authoritative host image relevant to one pending collective decision. -/
structure MachineState where
  committedMaterialDigest : MaterialDigest
  currentRoot : RootDigest
  nextSequence : Nat
  pending : Option CandidateCarrier
  usedDecisionReplayIds : List ReplayId
  deriving DecidableEq, Repr

/-- The receipt repeats the semantic task digest and candidate nonce.  The real
wire carries their 32-byte encodings; transcript and equality remain public. -/
structure ContextualReceipt where
  replayId : ReplayId
  taskDigest : TaskDigest
  candidateNonce : DecisionNonce
  transcriptDigest : PublicId
  equal : Bool
  deriving DecidableEq, Repr

def TaskBindsState (before : MachineState) (task : DecisionTask) : Prop :=
  task.context.committedMaterialDigest = before.committedMaterialDigest ∧
  task.context.preRoot = before.currentRoot ∧
  task.context.sequence = before.nextSequence ∧
  task.candidate.preMaterialDigest = before.committedMaterialDigest ∧
  before.pending = some task.candidate

def taskBindsStateCheck (before : MachineState) (task : DecisionTask) : Bool :=
  task.context.committedMaterialDigest == before.committedMaterialDigest &&
  task.context.preRoot == before.currentRoot &&
  task.context.sequence == before.nextSequence &&
  task.candidate.preMaterialDigest == before.committedMaterialDigest &&
  before.pending == some task.candidate

theorem taskBindsStateCheck_iff (before : MachineState) (task : DecisionTask) :
    taskBindsStateCheck before task = true ↔ TaskBindsState before task := by
  simp [taskBindsStateCheck, TaskBindsState, and_assoc]

def ReceiptBindsTask (task : DecisionTask) (receipt : ContextualReceipt) : Prop :=
  receipt.taskDigest = taskDigest task ∧
  receipt.candidateNonce = task.candidate.candidateNonce

def receiptBindsTaskCheck (task : DecisionTask) (receipt : ContextualReceipt) : Bool :=
  receipt.taskDigest == taskDigest task &&
  receipt.candidateNonce == task.candidate.candidateNonce

theorem receiptBindsTaskCheck_iff (task : DecisionTask) (receipt : ContextualReceipt) :
    receiptBindsTaskCheck task receipt = true ↔ ReceiptBindsTask task receipt := by
  simp [receiptBindsTaskCheck, ReceiptBindsTask]

/-- The only state produced by a successful contextual decision. -/
def acceptedState (before : MachineState) (task : DecisionTask)
    (receipt : ContextualReceipt) : MachineState :=
  { committedMaterialDigest := task.candidate.postMaterialDigest
    currentRoot := task.candidate.postRoot
    nextSequence := before.nextSequence + 1
    pending := none
    usedDecisionReplayIds := receipt.replayId :: before.usedDecisionReplayIds }

/-- Executable fail-closed transition. `signatureValid` is the injected
configured-roster verifier; all semantic binding and replay checks stay
visible and executable here. -/
def applyDecision
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState)
    (task : DecisionTask)
    (receipt : ContextualReceipt) : Option MachineState :=
  if !taskBindsStateCheck before task then none
  else if !receiptBindsTaskCheck task receipt then none
  else if !signatureValid receipt then none
  else if receipt.replayId ∈ before.usedDecisionReplayIds then none
  else if !receipt.equal then none
  else some (acceptedState before task receipt)

theorem wrong_state_context_refused
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (task : DecisionTask) (receipt : ContextualReceipt)
    (hwrong : taskBindsStateCheck before task = false) :
    applyDecision signatureValid before task receipt = none := by
  simp [applyDecision, hwrong]

/-- A receipt for task A cannot authorize task B, independently of which task
field was substituted and even if the signature predicate accepts it. -/
theorem task_substitution_refused
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (task : DecisionTask) (receipt : ContextualReceipt)
    (hwrong : receipt.taskDigest ≠ taskDigest task) :
    applyDecision signatureValid before task receipt = none := by
  simp [applyDecision, receiptBindsTaskCheck, hwrong]

theorem cross_context_receipt_refused
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (taskA taskB : DecisionTask)
    (receipt : ContextualReceipt)
    (hreceipt : receipt.taskDigest = taskDigest taskA)
    (hcontext : taskA.context ≠ taskB.context) :
    applyDecision signatureValid before taskB receipt = none := by
  apply task_substitution_refused
  rw [hreceipt]
  exact different_context_changes_task_digest hcontext

theorem candidate_substitution_receipt_refused
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (taskA taskB : DecisionTask)
    (receipt : ContextualReceipt)
    (hreceipt : receipt.taskDigest = taskDigest taskA)
    (hcandidate : taskA.candidate ≠ taskB.candidate) :
    applyDecision signatureValid before taskB receipt = none := by
  apply task_substitution_refused
  rw [hreceipt]
  exact different_candidate_changes_task_digest hcandidate

theorem replayed_receipt_refused
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (task : DecisionTask) (receipt : ContextualReceipt)
    (hreplay : receipt.replayId ∈ before.usedDecisionReplayIds) :
    applyDecision signatureValid before task receipt = none := by
  simp [applyDecision, hreplay]

theorem false_receipt_refused
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (task : DecisionTask) (receipt : ContextualReceipt)
    (hfalse : receipt.equal = false) :
    applyDecision signatureValid before task receipt = none := by
  simp [applyDecision, hfalse]

/-- Positive capstone: exact context, exact task receipt, valid signature,
fresh replay id, and true bit perform precisely one atomic transition. -/
theorem exact_fresh_true_receipt_installs_only_named_post
    (signatureValid : ContextualReceipt → Bool)
    (before : MachineState) (task : DecisionTask) (receipt : ContextualReceipt)
    (hstate : taskBindsStateCheck before task = true)
    (hreceipt : receiptBindsTaskCheck task receipt = true)
    (hsig : signatureValid receipt = true)
    (hfresh : receipt.replayId ∉ before.usedDecisionReplayIds)
    (htrue : receipt.equal = true) :
    applyDecision signatureValid before task receipt = some (acceptedState before task receipt) := by
  simp [applyDecision, hstate, hreceipt, hsig, hfresh, htrue]

theorem successful_transition_is_atomic
    (signatureValid : ContextualReceipt → Bool)
    (before after : MachineState) (task : DecisionTask) (receipt : ContextualReceipt)
    (hstate : taskBindsStateCheck before task = true)
    (hreceipt : receiptBindsTaskCheck task receipt = true)
    (hsig : signatureValid receipt = true)
    (hfresh : receipt.replayId ∉ before.usedDecisionReplayIds)
    (htrue : receipt.equal = true)
    (happly : applyDecision signatureValid before task receipt = some after) :
    after.committedMaterialDigest = task.candidate.postMaterialDigest ∧
    after.currentRoot = task.candidate.postRoot ∧
    after.nextSequence = before.nextSequence + 1 ∧
    after.pending = none ∧
    after.usedDecisionReplayIds = receipt.replayId :: before.usedDecisionReplayIds := by
  rw [exact_fresh_true_receipt_installs_only_named_post signatureValid before task receipt
    hstate hreceipt hsig hfresh htrue] at happly
  injection happly with heq
  subst after
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Executable teeth -/

def fixtureContext : TaskContext :=
  { hostedSession := 101
    sequence := 7
    preRoot := 202
    sameOpeningClaimDigest := 303
    committedMaterialDigest := 404
    parameterDigest := 505
    keygenDigest := 606
    collectiveKeyDigest := 707
    valueBits := 19 }

def fixtureCandidate : CandidateCarrier :=
  { preMaterialDigest := 404
    postMaterialDigest := 405
    preStateDigest := 808
    invariantCiphertextDigest := 909
    postStateDigest := 1001
    postRoot := 203
    publicK := 90000
    invariantBound := 400000
    candidateNonce := 1102 }

def fixtureTask : DecisionTask :=
  { context := fixtureContext, candidate := fixtureCandidate }

def fixtureReceipt : ContextualReceipt :=
  { replayId := 77
    taskDigest := taskDigest fixtureTask
    candidateNonce := fixtureCandidate.candidateNonce
    transcriptDigest := 1203
    equal := true }

def fixtureState : MachineState :=
  { committedMaterialDigest := 404
    currentRoot := 202
    nextSequence := 7
    pending := some fixtureCandidate
    usedDecisionReplayIds := [] }

#guard taskBindsStateCheck fixtureState fixtureTask
#guard receiptBindsTaskCheck fixtureTask fixtureReceipt
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with hostedSession := 102 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with sequence := 8 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with preRoot := 999 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with sameOpeningClaimDigest := 304 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with committedMaterialDigest := 406 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with keygenDigest := 607 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with context := { fixtureContext with collectiveKeyDigest := 708 } }
#guard taskDigest fixtureTask != taskDigest {
  fixtureTask with candidate := { fixtureCandidate with invariantCiphertextDigest := 910 } }

#guard applyDecision (fun _ => true) fixtureState fixtureTask fixtureReceipt ==
  some (acceptedState fixtureState fixtureTask fixtureReceipt)
#guard applyDecision (fun _ => true) fixtureState
  { fixtureTask with context := { fixtureContext with hostedSession := 102 } }
  fixtureReceipt == none
#guard applyDecision (fun _ => true)
  { fixtureState with usedDecisionReplayIds := [77] } fixtureTask fixtureReceipt == none
#guard applyDecision (fun _ => true) fixtureState fixtureTask
  { fixtureReceipt with equal := false } == none

#assert_axioms taskDigest_injective
#assert_axioms different_context_changes_task_digest
#assert_axioms different_candidate_changes_task_digest
#assert_axioms taskBindsStateCheck_iff
#assert_axioms receiptBindsTaskCheck_iff
#assert_axioms wrong_state_context_refused
#assert_axioms task_substitution_refused
#assert_axioms cross_context_receipt_refused
#assert_axioms candidate_substitution_receipt_refused
#assert_axioms replayed_receipt_refused
#assert_axioms false_receipt_refused
#assert_axioms exact_fresh_true_receipt_installs_only_named_post
#assert_axioms successful_transition_is_atomic

#assert_all_clean [
  Market.DarkAmmContextBoundDecision.taskDigest_injective,
  Market.DarkAmmContextBoundDecision.different_context_changes_task_digest,
  Market.DarkAmmContextBoundDecision.different_candidate_changes_task_digest,
  Market.DarkAmmContextBoundDecision.taskBindsStateCheck_iff,
  Market.DarkAmmContextBoundDecision.receiptBindsTaskCheck_iff,
  Market.DarkAmmContextBoundDecision.wrong_state_context_refused,
  Market.DarkAmmContextBoundDecision.task_substitution_refused,
  Market.DarkAmmContextBoundDecision.cross_context_receipt_refused,
  Market.DarkAmmContextBoundDecision.candidate_substitution_receipt_refused,
  Market.DarkAmmContextBoundDecision.replayed_receipt_refused,
  Market.DarkAmmContextBoundDecision.false_receipt_refused,
  Market.DarkAmmContextBoundDecision.exact_fresh_true_receipt_installs_only_named_post,
  Market.DarkAmmContextBoundDecision.successful_transition_is_atomic]

end Market.DarkAmmContextBoundDecision
