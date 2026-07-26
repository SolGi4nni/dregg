/-
# Market.DarkAmmPublicHost — structural FHDAP001/FHDAR001 host law.

This file models the public-only Dark AMM host introduced by the strict
`FHDAP001` carrier and the independently verified `FHDAR001` equality receipt.
It proves the state-machine facts only: exact before/after identity binding,
fresh replay consumption, atomic install/refusal, and restart preservation.

`CiphertextState`, its public identity function, the nonce construction, the
wire codec, and `ReceiptVerified` are parameters.  No theorem here says that
fhe.rs bytes decode correctly, that a public/relinearization key shares a
secret-key domain with a ciphertext, that the initial hidden reserves multiply
to `k`, or that Ed25519/BFV/MPC is sound.
-/

import Dregg2.Tactics

namespace Market.DarkAmmPublicHost

set_option autoImplicit false

abbrev PublicId := Nat
abbrev StateId := Nat
abbrev DecisionNonce := Nat
abbrev ReplayId := Nat

/-- Public, immutable evaluation identity retained by a secretless host.  The
identifiers stand for canonical parameter/key objects; this model does not
interpret their bytes. -/
structure PublicEvaluationIdentity where
  parameterDigest : PublicId
  publicKeyId : PublicId
  relinearizationKeyId : PublicId
  plaintextModulus : Nat
  invariantK : Nat
  deriving DecidableEq, Repr

/-- Semantic shape of an `FHDAP001` carrier. `CiphertextState` is supplied by
an external refinement and is intended to include both encrypted reserves and
their public caps. -/
structure PublicHostMaterial (CiphertextState : Type) where
  evaluation : PublicEvaluationIdentity
  ciphertextState : CiphertextState

/-- Complete mutable state of the public-only host. -/
structure HostState (CiphertextState : Type) where
  material : PublicHostMaterial CiphertextState
  usedReplayIds : List ReplayId

/-- Restore is intentionally boring: validated public material plus durable
replay state is the complete semantic host image. -/
def restore {CiphertextState : Type}
    (material : PublicHostMaterial CiphertextState)
    (usedReplayIds : List ReplayId) : HostState CiphertextState :=
  { material, usedReplayIds }

/-- Encrypted candidate whose private fields in Rust are constructible only by
the evaluating host. Its public nonce binds exact before and after identities. -/
structure Candidate (CiphertextState : Type) where
  beforeStateId : StateId
  afterState : CiphertextState
  afterStateId : StateId
  decisionNonce : DecisionNonce

def candidateAfterMaterial {CiphertextState : Type}
    (before : HostState CiphertextState)
    (candidate : Candidate CiphertextState) : PublicHostMaterial CiphertextState :=
  { evaluation := before.material.evaluation
    ciphertextState := candidate.afterState }

/-- Pure public candidate binding. `identify` and `nonceOf` are external
functions so this definition makes no hash-collision or codec claim. -/
structure CandidateBinds {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (before : HostState CiphertextState)
    (candidate : Candidate CiphertextState) : Prop where
  beforeState : candidate.beforeStateId = identify before.material
  afterState : candidate.afterStateId = identify (candidateAfterMaterial before candidate)
  nonce : candidate.decisionNonce =
    nonceOf candidate.beforeStateId candidate.afterStateId

/-- Independently configured relying-party equality policy. None of these
fields is learned from the submitted receipt. -/
structure ReceiptPolicy where
  rosterDigest : PublicId
  nParties : Nat
  valueBits : Nat
  plaintextModulus : Nat
  deriving DecidableEq, Repr

/-- Public abstraction of the strict `FHDAR001` equality envelope. It contains
no operand, invariant residue, BFV share, Beaver triple, or reserve opening. -/
structure AttestedReceipt where
  replayId : ReplayId
  candidateNonce : DecisionNonce
  rosterDigest : PublicId
  nParties : Nat
  valueBits : Nat
  plaintextModulus : Nat
  transcriptDigest : PublicId
  equal : Bool
  deriving DecidableEq, Repr

def ReceiptBindsPolicy (policy : ReceiptPolicy) (receipt : AttestedReceipt) : Prop :=
  receipt.rosterDigest = policy.rosterDigest ∧
  receipt.nParties = policy.nParties ∧
  receipt.valueBits = policy.valueBits ∧
  receipt.plaintextModulus = policy.plaintextModulus

/-- The only accepting authorization. `ReceiptVerified` is an injected
external verifier premise. Structural policy, pool-domain, nonce, true-bit,
and freshness facts remain visible projections rather than being hidden in it. -/
structure TrueFreshReceiptCapability {CiphertextState : Type}
    (ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop)
    (policy : ReceiptPolicy)
    (before : HostState CiphertextState)
    (candidate : Candidate CiphertextState) where
  receipt : AttestedReceipt
  policyBinding : ReceiptBindsPolicy policy receipt
  poolDomain : policy.plaintextModulus = before.material.evaluation.plaintextModulus
  verified : ReceiptVerified policy receipt
  candidateBinding : receipt.candidateNonce = candidate.decisionNonce
  trueBit : receipt.equal = true
  fresh : receipt.replayId ∉ before.usedReplayIds

def acceptedState {CiphertextState : Type}
    (before : HostState CiphertextState)
    (candidate : Candidate CiphertextState)
    (receipt : AttestedReceipt) : HostState CiphertextState :=
  { material := candidateAfterMaterial before candidate
    usedReplayIds := receipt.replayId :: before.usedReplayIds }

/-- Accepting branch for one submitted receipt. Equality with the capability's
receipt prevents a verifier result for another envelope from authorizing this
transition. -/
def HostAccepts {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop)
    (policy : ReceiptPolicy)
    (before : HostState CiphertextState)
    (candidate : Candidate CiphertextState)
    (submitted : AttestedReceipt)
    (after : HostState CiphertextState) : Prop :=
  CandidateBinds identify nonceOf before candidate ∧
  ∃ capability : TrueFreshReceiptCapability ReceiptVerified policy before candidate,
    capability.receipt = submitted ∧
    after = acceptedState before candidate submitted

inductive HostDecision where
  | accepted
  | refused
  deriving DecidableEq, Repr

/-- One atomic host step. Refusal has no special case for failure phase: every
failed preflight, false bit, verifier refusal, or replay hit holds the complete
material and replay image. -/
def HostStep {CiphertextState : Type}
    (identify : PublicHostMaterial CiphertextState → StateId)
    (nonceOf : StateId → StateId → DecisionNonce)
    (ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop)
    (policy : ReceiptPolicy)
    (before : HostState CiphertextState)
    (candidate : Candidate CiphertextState)
    (submitted : AttestedReceipt)
    (decision : HostDecision)
    (after : HostState CiphertextState) : Prop :=
  match decision with
  | .accepted =>
      HostAccepts identify nonceOf ReceiptVerified policy before candidate submitted after
  | .refused => after = before

/-- A candidate evaluated from another public material identity cannot enter
the accepting branch from the current host state. -/
theorem stale_candidate_cannot_accept
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    (hstale : candidate.beforeStateId ≠ identify before.material) :
    ¬ HostStep identify nonceOf ReceiptVerified policy before candidate submitted
        .accepted after := by
  intro hstep
  exact hstale hstep.1.beforeState

/-- Acceptance installs exactly `candidate.afterState`, preserves the public
evaluation identity, realizes the candidate's declared after id, and prepends
exactly one previously fresh replay id. -/
theorem acceptance_installs_after_and_consumes_exact_replay
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    (hstep : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      .accepted after) :
    after.material.evaluation = before.material.evaluation ∧
    after.material.ciphertextState = candidate.afterState ∧
    identify after.material = candidate.afterStateId ∧
    after.usedReplayIds = submitted.replayId :: before.usedReplayIds ∧
    submitted.replayId ∉ before.usedReplayIds := by
  rcases hstep.2 with ⟨capability, hreceipt, hafter⟩
  have hfresh : submitted.replayId ∉ before.usedReplayIds := by
    rw [← hreceipt]
    exact capability.fresh
  rw [hafter]
  refine ⟨rfl, rfl, ?_, rfl, hfresh⟩
  exact hstep.1.afterState.symm

/-- Sequential barrier 1 (state identity, not replay): if an accepted
candidate names a genuinely different after-state id, then that exact
candidate is stale immediately after installation. It cannot accept again even
under a different verifier policy and a hypothetical fresh receipt. -/
theorem accepted_candidate_cannot_repeat_by_state_staleness
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {ReceiptVerifiedAgain : ReceiptPolicy → AttestedReceipt → Prop}
    {policy policyAgain : ReceiptPolicy}
    {before after afterAgain : HostState CiphertextState}
    {candidate : Candidate CiphertextState}
    {submitted submittedAgain : AttestedReceipt}
    (hfirst : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      .accepted after)
    (hchanged : candidate.afterStateId ≠ candidate.beforeStateId) :
    ¬ HostStep identify nonceOf ReceiptVerifiedAgain policyAgain after candidate submittedAgain
        .accepted afterAgain := by
  have hinstalled := acceptance_installs_after_and_consumes_exact_replay hfirst
  have hafterId : identify after.material = candidate.afterStateId := hinstalled.2.2.1
  have hstale : candidate.beforeStateId ≠ identify after.material := by
    intro heq
    apply hchanged
    calc
      candidate.afterStateId = identify after.material := hafterId.symm
      _ = candidate.beforeStateId := heq.symm
  exact stale_candidate_cannot_accept hstale

/-- Sequential barrier 2 (replay, not state identity): the exact accepted
receipt cannot authorize any next candidate because its replay id is now used.
No non-stuttering or state-id assumption is needed, and even a different
verifier policy cannot manufacture freshness. -/
theorem accepted_receipt_cannot_repeat_by_replay
    {CiphertextState : Type}
    {identify identifyAgain : PublicHostMaterial CiphertextState → StateId}
    {nonceOf nonceOfAgain : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {ReceiptVerifiedAgain : ReceiptPolicy → AttestedReceipt → Prop}
    {policy policyAgain : ReceiptPolicy}
    {before after afterAgain : HostState CiphertextState}
    {candidate candidateAgain : Candidate CiphertextState}
    {submitted : AttestedReceipt}
    (hfirst : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      .accepted after) :
    ¬ HostStep identifyAgain nonceOfAgain ReceiptVerifiedAgain policyAgain after candidateAgain
        submitted .accepted afterAgain := by
  intro hsecond
  have hinstalled := acceptance_installs_after_and_consumes_exact_replay hfirst
  have hused : submitted.replayId ∈ after.usedReplayIds := by
    rw [hinstalled.2.2.2.1]
    simp
  rcases hsecond.2 with ⟨capability, hreceipt, hafter⟩
  have hfresh : submitted.replayId ∉ after.usedReplayIds := by
    rw [← hreceipt]
    exact capability.fresh
  exact hfresh hused

/-- The verified envelope is bound to the candidate's independently derived
nonce and therefore to both state identities. -/
theorem acceptance_pins_receipt_nonce
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    (hstep : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      .accepted after) :
    submitted.candidateNonce = candidate.decisionNonce ∧
    candidate.decisionNonce = nonceOf candidate.beforeStateId candidate.afterStateId := by
  rcases hstep.2 with ⟨capability, hreceipt, hafter⟩
  refine ⟨?_, hstep.1.nonce⟩
  rw [← hreceipt]
  exact capability.candidateBinding

/-- A submitted false bit cannot inhabit the accepting capability, regardless
of what an untrusted caller claims about its signature or transcript. -/
theorem false_receipt_cannot_accept
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    (hfalse : submitted.equal = false) :
    ¬ HostStep identify nonceOf ReceiptVerified policy before candidate submitted
        .accepted after := by
  intro hstep
  rcases hstep.2 with ⟨capability, hreceipt, hafter⟩
  have htrue : submitted.equal = true := by
    rw [← hreceipt]
    exact capability.trueBit
  simp [hfalse] at htrue

/-- Every refusal, including a false receipt, holds the complete encrypted
material and replay image. -/
theorem refusal_holds_complete_state
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    (hstep : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      .refused after) :
    after = before :=
  hstep

/-- Any well-formed step submitted with a false public bit holds the complete
host image: acceptance is impossible, and the only remaining branch is the
atomic refusal branch. -/
theorem false_receipt_step_holds_complete_state
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    {decision : HostDecision}
    (hfalse : submitted.equal = false)
    (hstep : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      decision after) :
    after = before := by
  cases decision with
  | accepted => exact (false_receipt_cannot_accept hfalse hstep).elim
  | refused => exact hstep

/-- The transition relation has no partially installed third outcome. -/
theorem step_accepts_or_holds
    {CiphertextState : Type}
    {identify : PublicHostMaterial CiphertextState → StateId}
    {nonceOf : StateId → StateId → DecisionNonce}
    {ReceiptVerified : ReceiptPolicy → AttestedReceipt → Prop}
    {policy : ReceiptPolicy} {before after : HostState CiphertextState}
    {candidate : Candidate CiphertextState} {submitted : AttestedReceipt}
    {decision : HostDecision}
    (hstep : HostStep identify nonceOf ReceiptVerified policy before candidate submitted
      decision after) :
    (decision = .accepted ∧
      HostAccepts identify nonceOf ReceiptVerified policy before candidate submitted after) ∨
    (decision = .refused ∧ after = before) := by
  cases decision with
  | accepted => exact Or.inl ⟨rfl, hstep⟩
  | refused => exact Or.inr ⟨rfl, hstep⟩

/-- Pure restart theorem. The codec round-trip is an explicit premise; Lean
does not assert that `FHDAP001` bytes or fhe.rs implement it. -/
theorem decode_encode_restart_preserves
    {CiphertextState Wire : Type}
    (encode : PublicHostMaterial CiphertextState → Wire)
    (decode : Wire → Option (PublicHostMaterial CiphertextState))
    (material : PublicHostMaterial CiphertextState)
    (usedReplayIds : List ReplayId)
    (hroundtrip : decode (encode material) = some material) :
    Option.map (fun decoded => restore decoded usedReplayIds)
        (decode (encode material)) =
      some (restore material usedReplayIds) := by
  simp [hroundtrip]

#assert_axioms stale_candidate_cannot_accept
#assert_axioms acceptance_installs_after_and_consumes_exact_replay
#assert_axioms accepted_candidate_cannot_repeat_by_state_staleness
#assert_axioms accepted_receipt_cannot_repeat_by_replay
#assert_axioms acceptance_pins_receipt_nonce
#assert_axioms false_receipt_cannot_accept
#assert_axioms refusal_holds_complete_state
#assert_axioms false_receipt_step_holds_complete_state
#assert_axioms step_accepts_or_holds
#assert_axioms decode_encode_restart_preserves

/- Candidate/state binding must remain independent of external receipt
verification and acceptance semantics. -/
-- POSITIVE CONTROL for the rejectors below: reached only through the acceptance proof's term.
#assert_depends_on Market.DarkAmmPublicHost.acceptance_installs_after_and_consumes_exact_replay
  [Market.DarkAmmPublicHost.acceptedState, Market.DarkAmmPublicHost.candidateAfterMaterial]

#assert_not_depends_on Market.DarkAmmPublicHost.CandidateBinds [
  Market.DarkAmmPublicHost.TrueFreshReceiptCapability,
  Market.DarkAmmPublicHost.HostAccepts,
  Market.DarkAmmPublicHost.HostStep]

/- Restart semantics must not silently acquire a receipt or state-transition
premise. -/
#assert_not_depends_on Market.DarkAmmPublicHost.restore [
  Market.DarkAmmPublicHost.ReceiptBindsPolicy,
  Market.DarkAmmPublicHost.TrueFreshReceiptCapability,
  Market.DarkAmmPublicHost.HostAccepts]

#assert_all_clean [
  Market.DarkAmmPublicHost.stale_candidate_cannot_accept,
  Market.DarkAmmPublicHost.acceptance_installs_after_and_consumes_exact_replay,
  Market.DarkAmmPublicHost.accepted_candidate_cannot_repeat_by_state_staleness,
  Market.DarkAmmPublicHost.accepted_receipt_cannot_repeat_by_replay,
  Market.DarkAmmPublicHost.acceptance_pins_receipt_nonce,
  Market.DarkAmmPublicHost.false_receipt_cannot_accept,
  Market.DarkAmmPublicHost.refusal_holds_complete_state,
  Market.DarkAmmPublicHost.false_receipt_step_holds_complete_state,
  Market.DarkAmmPublicHost.step_accepts_or_holds,
  Market.DarkAmmPublicHost.decode_encode_restart_preserves]

end Market.DarkAmmPublicHost
