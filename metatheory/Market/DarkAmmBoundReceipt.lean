/-
# Market.DarkAmmBoundReceipt — exact-opening-required hosted AMM transition.

This file is the Lean semantic model for the versioned v3 host boundary.  A
HidingFri proof-only v2 request is not enough: acceptance additionally consumes
an explicit exact-opening capability whose public claim pins the hosted
session/sequence, the complete private-receipt statement, both ciphertext
identities, both public wrap-safety bounds, the configured authority
roster/verifier/tier/threshold, and the exact fresh replay slot.

The capability is deliberately a premise, not a theorem that BFV,
HidingFri, or Ed25519 is sound.  `CipherOpensTo` is an uninterpreted relation,
and `verifiedMeaning` explicitly carries the semantic refinement which an
external same-opening authority must establish.  The independent encrypted
candidate gate is likewise represented by `DarkAmmDecisionReceipt.TrustedMeaning`;
no signature bit is promoted into that meaning inside Lean.
-/

import Market.DarkAmmPrivateReceipt
import Market.DarkAmmDecisionReceipt
import Dregg2.Tactics

namespace Market.DarkAmmBoundReceipt

set_option autoImplicit false

abbrev CiphertextId := Nat
abbrev AuthorityId := Nat

/-- Only v3 carries the exact-opening authorization required by this host
transition. A v2 request can still contain a valid hiding proof, but cannot
inhabit the accepting version equation. -/
inductive RequestVersion where
  | proofOnlyV2
  | exactOpeningV3
  deriving DecidableEq, Repr

structure ReplaySlot where
  hostedSession : Nat
  sequence : Nat
  deriving DecidableEq, Repr

/-- Public policy fixed by the host, independently of any submitted request. -/
structure HostPolicy where
  hostedSession : Nat
  receiptSession : Int
  rule : Int
  authorityRosterDigest : AuthorityId
  authorityVerifierId : AuthorityId
  authorityTier : Nat
  authorityThreshold : Nat
  deriving DecidableEq, Repr

/-- Atomic host state. Hidden reserves are semantic state; only `k`, the root,
sequence, and replay occupancy belong in the public protocol view. -/
structure HostState where
  reserves : Market.DarkAmmPrivateSwap.Reserves
  currentRoot : List Int
  nextSequence : Nat
  usedReplaySlots : List ReplaySlot
  deriving DecidableEq, Repr

/-- Versioned public request. Ciphertexts are represented only by their exact
canonical identities; this model never decodes them. -/
structure Request where
  version : RequestVersion
  hostedSession : Nat
  sequence : Nat
  statement : Market.DarkAmmPrivateReceipt.PublicStatement
  dxCiphertext : CiphertextId
  dyCiphertext : CiphertextId
  /-- Public inclusive bounds used by the BFV multiplication wrap guard. -/
  dxBound : Nat
  dyBound : Nat
  deriving DecidableEq, Repr

/-- Canonical public claim carried by an exact-opening authority result. -/
structure SameOpeningClaim where
  hostedSession : Nat
  sequence : Nat
  statement : Market.DarkAmmPrivateReceipt.PublicStatement
  dxCiphertext : CiphertextId
  dyCiphertext : CiphertextId
  dxBound : Nat
  dyBound : Nat
  authorityRosterDigest : AuthorityId
  authorityVerifierId : AuthorityId
  authorityTier : Nat
  authorityThreshold : Nat
  replaySlot : ReplaySlot
  deriving DecidableEq, Repr

def witnessReserves (statement : Market.DarkAmmPrivateReceipt.PublicStatement)
    (witness : Market.DarkAmmPrivateReceipt.PrivateWitness) :
    Market.DarkAmmPrivateSwap.Reserves :=
  { x := witness.x.val, y := witness.y.val, k := statement.k }

def witnessAmounts (witness : Market.DarkAmmPrivateReceipt.PrivateWitness) :
    Market.DarkAmmPrivateSwap.Amounts :=
  { dx := witness.dx.val, dy := witness.dy.val }

/-- The exact semantic obligation discharged outside Lean by a same-opening
authority. `CipherOpensTo` remains abstract: there is no axiom asserting that
BFV bytes or signatures imply it. -/
def CapabilityWitness
    (hash8 : List Int → List Int)
    (CipherOpensTo : CiphertextId → Nat → Prop)
    (before : HostState) (claim : SameOpeningClaim)
    (witness : Market.DarkAmmPrivateReceipt.PrivateWitness) : Prop :=
  Market.DarkAmmPrivateReceipt.Accepts hash8 claim.statement witness ∧
  before.reserves = witnessReserves claim.statement witness ∧
  CipherOpensTo claim.dxCiphertext witness.dx.val ∧
  CipherOpensTo claim.dyCiphertext witness.dy.val ∧
  witness.dx.val ≤ claim.dxBound ∧
  witness.dy.val ≤ claim.dyBound

/-- Opaque verified authorization, indexed by the exact pre-state. Besides its
public claim it carries two proof obligations: this replay slot is fresh for
that state, and some hidden witness satisfies both the private receipt and the
abstract ciphertext-opening relation. -/
structure ExactOpeningCapability
    (hash8 : List Int → List Int)
    (CipherOpensTo : CiphertextId → Nat → Prop)
    (before : HostState) where
  claim : SameOpeningClaim
  fresh : claim.replaySlot ∉ before.usedReplaySlots
  verifiedMeaning : ∃ witness,
    CapabilityWitness hash8 CipherOpensTo before claim witness

/-- Every equality checked before v3 acceptance. Keeping this as a structure
makes omission of a binding visible in theorem statements and projections. -/
structure Binds (policy : HostPolicy) (before : HostState)
    (request : Request) (claim : SameOpeningClaim) : Prop where
  requestVersion : request.version = .exactOpeningV3
  requestHostedSession : request.hostedSession = policy.hostedSession
  capabilityHostedSession : claim.hostedSession = request.hostedSession
  requestSequence : request.sequence = before.nextSequence
  capabilitySequence : claim.sequence = request.sequence
  statement : claim.statement = request.statement
  receiptSession : claim.statement.session = policy.receiptSession
  policyRule : policy.rule = Market.DarkAmmPrivateReceipt.RULE_ID
  statementRule : claim.statement.rule = policy.rule
  invariant : claim.statement.k = before.reserves.k
  oldRoot : claim.statement.oldRoot = before.currentRoot
  dxCiphertext : claim.dxCiphertext = request.dxCiphertext
  dyCiphertext : claim.dyCiphertext = request.dyCiphertext
  dxBound : claim.dxBound = request.dxBound
  dyBound : claim.dyBound = request.dyBound
  authorityRoster : claim.authorityRosterDigest = policy.authorityRosterDigest
  authorityVerifier : claim.authorityVerifierId = policy.authorityVerifierId
  authorityTier : claim.authorityTier = policy.authorityTier
  authorityThreshold : claim.authorityThreshold = policy.authorityThreshold
  replaySlot : claim.replaySlot =
    { hostedSession := policy.hostedSession, sequence := before.nextSequence }

/-- Exact semantic meaning of the independent encrypted-candidate decision.
The external authenticated receipt verifier must supply `TrustedMeaning`; this
definition does not derive it from a signature. -/
def CandidateGateMeaning (before : HostState)
    (amounts : Market.DarkAmmPrivateSwap.Amounts)
    (receipt : Market.DarkAmmDecisionReceipt.Receipt) : Prop :=
  Market.DarkAmmDecisionReceipt.TrustedMeaning true
      { reserves := before.reserves, usedReceiptIds := [] }
      amounts receipt ∧
    receipt.equal = true

def acceptedState (before : HostState) (claim : SameOpeningClaim)
    (witness : Market.DarkAmmPrivateReceipt.PrivateWitness) : HostState :=
  { reserves := Market.DarkAmmPrivateSwap.post before.reserves (witnessAmounts witness)
    currentRoot := claim.statement.newRoot
    nextSequence := before.nextSequence + 1
    usedReplaySlots := claim.replaySlot :: before.usedReplaySlots }

/-- Relational accepting branch. The witness stays existential: the host state
transition is specified by its meaning without exposing it in the public
receipt. -/
def HostAccepts
    (hash8 : List Int → List Int)
    (CipherOpensTo : CiphertextId → Nat → Prop)
    (policy : HostPolicy) (before : HostState) (request : Request)
    (capability : ExactOpeningCapability hash8 CipherOpensTo before)
    (after : HostState) : Prop :=
  Binds policy before request capability.claim ∧
  ∃ witness decisionReceipt,
    CapabilityWitness hash8 CipherOpensTo before capability.claim witness ∧
    CandidateGateMeaning before (witnessAmounts witness) decisionReceipt ∧
    after = acceptedState before capability.claim witness

inductive HostDecision where
  | accepted
  | refused
  deriving DecidableEq, Repr

/-- A refused request holds the complete state. An accepted request must
inhabit `HostAccepts`; there is no third partially-mutated outcome. -/
def HostStep
    (hash8 : List Int → List Int)
    (CipherOpensTo : CiphertextId → Nat → Prop)
    (policy : HostPolicy) (before : HostState) (request : Request)
    (capability : ExactOpeningCapability hash8 CipherOpensTo before)
    (decision : HostDecision) (after : HostState) : Prop :=
  match decision with
  | .accepted => HostAccepts hash8 CipherOpensTo policy before request capability after
  | .refused => after = before

/-- A proof-only v2 request cannot enter the v3 accepting constructor, even if
all of its statement fields happen to equal a valid v3 statement. -/
theorem proofOnly_v2_cannot_accept
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hversion : request.version = .proofOnlyV2) :
    ¬ HostStep hash8 CipherOpensTo policy before request capability .accepted after := by
  intro hstep
  have hv3 := hstep.1.requestVersion
  simp [hversion] at hv3

/-- Acceptance preserves the complete binding record, including both exact
ciphertext identities and every configured authority identity. -/
theorem accepted_pins_every_binding
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability .accepted after) :
    Binds policy before request capability.claim :=
  hstep.1

/-- The bounds handed to the runtime's wrap guard really bound the hidden
amounts in the exact ciphertext-opening witness. This is why the bounds belong
inside the authority claim rather than only in the unsigned request body. -/
theorem accepted_bounds_are_sound
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability .accepted after) :
    ∃ witness,
      CapabilityWitness hash8 CipherOpensTo before capability.claim witness ∧
      witness.dx.val ≤ request.dxBound ∧ witness.dy.val ≤ request.dyBound := by
  rcases hstep.2 with ⟨witness, decisionReceipt, hcap, hdecision, hafter⟩
  refine ⟨witness, hcap, ?_, ?_⟩
  · rw [← hstep.1.dxBound]
    exact hcap.2.2.2.2.1
  · rw [← hstep.1.dyBound]
    exact hcap.2.2.2.2.2

/-- The consumed replay key is exactly the configured hosted session and old
sequence; it was absent before and is present after. -/
theorem accepted_consumes_exact_replay_slot
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability .accepted after) :
    capability.claim.replaySlot =
        { hostedSession := policy.hostedSession, sequence := before.nextSequence } ∧
      capability.claim.replaySlot ∉ before.usedReplaySlots ∧
      capability.claim.replaySlot ∈ after.usedReplaySlots := by
  refine ⟨hstep.1.replaySlot, capability.fresh, ?_⟩
  rcases hstep.2 with ⟨witness, decisionReceipt, hcap, hdecision, rfl⟩
  simp [acceptedState]

/-- Acceptance advances reserves, root, sequence, and replay occupancy through
one exact state value, under both the private receipt relation and the explicit
decision-gate meaning. -/
theorem accepted_advances_atomically_under_private_receipt
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability .accepted after) :
    ∃ witness decisionReceipt,
      Market.DarkAmmPrivateReceipt.Accepts hash8 capability.claim.statement witness ∧
      CandidateGateMeaning before (witnessAmounts witness) decisionReceipt ∧
      after.reserves = Market.DarkAmmPrivateSwap.post before.reserves (witnessAmounts witness) ∧
      after.currentRoot = capability.claim.statement.newRoot ∧
      after.nextSequence = before.nextSequence + 1 ∧
      after.usedReplaySlots = capability.claim.replaySlot :: before.usedReplaySlots := by
  rcases hstep.2 with ⟨witness, decisionReceipt, hcap, hdecision, rfl⟩
  exact ⟨witness, decisionReceipt, hcap.1, hdecision, rfl, rfl, rfl, rfl⟩

/-- The accepted reserve transition is the existing semantic `commit`, not a
freely chosen next reserve. Admissibility comes from the explicit decision
meaning; no BFV or signature theorem is smuggled into this proof. -/
theorem accepted_reserves_refine_private_commit
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability .accepted after) :
    ∃ witness,
      Market.DarkAmmPrivateSwap.Admissible before.reserves (witnessAmounts witness) ∧
      after.reserves = Market.DarkAmmPrivateSwap.commit before.reserves
        (witnessAmounts witness) := by
  rcases hstep.2 with ⟨witness, decisionReceipt, hcap, hdecision, hafter⟩
  have hadmit : Market.DarkAmmPrivateSwap.Admissible before.reserves
      (witnessAmounts witness) :=
    Market.DarkAmmDecisionReceipt.true_receipt_implies_admissible
      hdecision.1 hdecision.2 rfl
  refine ⟨witness, hadmit, ?_⟩
  rw [hafter]
  exact (Market.DarkAmmPrivateSwap.admitted_commits_post hadmit).symm

/-- Refusal is fully atomic, including hidden reserves, root, sequence, and
replay set. -/
theorem refusal_holds_complete_state
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability .refused after) :
    after = before :=
  hstep

/-- There is no partially applied semantic outcome. -/
theorem step_accepts_or_holds
    {hash8 : List Int → List Int}
    {CipherOpensTo : CiphertextId → Nat → Prop}
    {policy : HostPolicy} {before after : HostState} {request : Request}
    {capability : ExactOpeningCapability hash8 CipherOpensTo before}
    {decision : HostDecision}
    (hstep : HostStep hash8 CipherOpensTo policy before request capability decision after) :
    (decision = .accepted ∧
      HostAccepts hash8 CipherOpensTo policy before request capability after) ∨
    (decision = .refused ∧ after = before) := by
  cases decision with
  | accepted => exact Or.inl ⟨rfl, hstep⟩
  | refused => exact Or.inr ⟨rfl, hstep⟩

#assert_axioms proofOnly_v2_cannot_accept
#assert_axioms accepted_pins_every_binding
#assert_axioms accepted_bounds_are_sound
#assert_axioms accepted_consumes_exact_replay_slot
#assert_axioms accepted_advances_atomically_under_private_receipt
#assert_axioms accepted_reserves_refine_private_commit
#assert_axioms refusal_holds_complete_state
#assert_axioms step_accepts_or_holds

/- The public equality layer must remain purely structural. In particular,
adding a cryptographic or semantic verifier to `Binds` is a build error rather
than a silent strengthening of what “all fields match” means. -/
-- POSITIVE CONTROL for the rejector below: these are reached only through the acceptance proof's
-- term, never its statement, so a closure walk gone blind reds here instead of passing silently.
#assert_depends_on Market.DarkAmmBoundReceipt.accepted_consumes_exact_replay_slot
  [Market.DarkAmmBoundReceipt.acceptedState, Market.DarkAmmBoundReceipt.witnessAmounts]

#assert_not_depends_on Market.DarkAmmBoundReceipt.Binds [
  Market.DarkAmmPrivateReceipt.Accepts,
  Market.DarkAmmPrivateReceipt.check,
  Market.DarkAmmDecisionReceipt.TrustedMeaning,
  Market.DarkAmmDecisionReceipt.applyReceipt]

#assert_all_clean [
  Market.DarkAmmBoundReceipt.proofOnly_v2_cannot_accept,
  Market.DarkAmmBoundReceipt.accepted_pins_every_binding,
  Market.DarkAmmBoundReceipt.accepted_bounds_are_sound,
  Market.DarkAmmBoundReceipt.accepted_consumes_exact_replay_slot,
  Market.DarkAmmBoundReceipt.accepted_advances_atomically_under_private_receipt,
  Market.DarkAmmBoundReceipt.accepted_reserves_refine_private_commit,
  Market.DarkAmmBoundReceipt.refusal_holds_complete_state,
  Market.DarkAmmBoundReceipt.step_accepts_or_holds]

end Market.DarkAmmBoundReceipt
