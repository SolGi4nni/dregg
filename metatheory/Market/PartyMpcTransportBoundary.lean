/-
# Market.PartyMpcTransportBoundary — the honest process-transport boundary

This file models the exact claim made by the process-separated PartyMPC
equality transport used by the Dark Bazaar:

* the router's public carrier contains routes, peer ciphertexts, masked Beaver
  openings, and the final equality bit;
* party operands, Boolean ingress plaintexts, signing seeds, and Beaver rows
  remain in party custody and have no constructor in that public projection;
* an accepted peer frame is session-, route-, sequence-, signature-, and
  AEAD-bound, and accepting it advances the sequence so the same frame cannot
  be accepted again;
* a party signs a decision claim only after the authenticated public gate and
  decision frames reconstruct the exact reveal transcript.

The projection theorem below is deliberately structural: it holds when the
public ciphertext carrier is held fixed. It is NOT a cryptographic
indistinguishability theorem. XChaCha20-Poly1305 confidentiality, Ed25519
unforgeability, static Curve25519 identity conversion, OS nonce freshness, and
HKDF security live outside Lean here. Likewise, transport acceptance does not
prove honest input formation, honest Beaver preprocessing, or honest gate
evaluation; the executable counterexample at the end makes that residual
impossible to erase by prose.
-/

import Dregg2.Tactics

namespace Market.PartyMpcTransportBoundary

set_option autoImplicit false

inductive WireKind where
  | peerIngress
  | gateShare
  | gateOpened
  | decisionShare
  deriving DecidableEq, Repr

/-- Metadata deliberately visible to the forwarding supervisor. -/
structure Route where
  sender : Nat
  recipient : Nat
  sequence : Nat
  kind : WireKind
  deriving DecidableEq, Repr

/-- Secret process custody. None of these fields occurs in `PublicRelease`. -/
structure PrivateCustody where
  leftOperandShare : Nat
  rightOperandShare : Nat
  ingressPlaintext : List Bool
  signingSeed : Nat
  beaverRow : List (Bool × Bool × Bool)
  deriving DecidableEq, Repr

/-- Exact public carrier, before relying on any hiding theorem.

Peer ciphertext bytes and masked openings are observable. Only their claimed
hiding is cryptographic/algebraic; this structure does not pretend otherwise. -/
structure PublicRelease where
  routes : List Route
  peerCiphertexts : List (List Nat)
  maskedOpenings : List (Bool × Bool)
  decision : Option Bool
  deriving DecidableEq, Repr

structure ProcessRun where
  privateCustody : PrivateCustody
  publicRelease : PublicRelease
  deriving DecidableEq, Repr

def release (run : ProcessRun) : PublicRelease := run.publicRelease

/-- Structural custody noninterference: replacing only private custody cannot
change the public projection. Ciphertexts are held fixed, so this says nothing
about cryptographic indistinguishability of encryptions of different inputs. -/
theorem release_independent_of_private_custody
    (run : ProcessRun) (replacement : PrivateCustody) :
    release { run with privateCustody := replacement } = release run := by
  rfl

/-- Checks performed before a peer-ingress plaintext may be parsed. -/
structure PeerIngressCheck where
  sessionMatches : Bool
  routeMatches : Bool
  signatureValid : Bool
  aeadValid : Bool
  sequence : Nat
  expectedSequence : Nat
  deriving DecidableEq, Repr

def AcceptsPeerIngress (check : PeerIngressCheck) : Prop :=
  check.sessionMatches = true ∧
  check.routeMatches = true ∧
  check.signatureValid = true ∧
  check.aeadValid = true ∧
  check.sequence = check.expectedSequence

def advance (check : PeerIngressCheck) : PeerIngressCheck :=
  { check with expectedSequence := check.expectedSequence + 1 }

theorem accepted_peer_ingress_names_every_check
    {check : PeerIngressCheck} (h : AcceptsPeerIngress check) :
    check.sessionMatches = true ∧
    check.routeMatches = true ∧
    check.signatureValid = true ∧
    check.aeadValid = true ∧
    check.sequence = check.expectedSequence :=
  h

/-- Strict per-sender sequencing makes the byte-identical accepted frame a
replay immediately after its first acceptance. -/
theorem accepted_peer_ingress_replay_refused
    {check : PeerIngressCheck} (h : AcceptsPeerIngress check) :
    ¬ AcceptsPeerIngress (advance check) := by
  intro replay
  have acceptedSequence : check.sequence = check.expectedSequence := h.2.2.2.2
  have replaySequence : check.sequence = check.expectedSequence + 1 := replay.2.2.2.2
  omega

/-- Public transcript claimed by a receipt signer. -/
structure PublicTranscript where
  maskedOpenings : List (Bool × Bool)
  decision : Bool
  deriving DecidableEq, Repr

/-- Result of strict signature/session/route/sequence verification and XOR
reconstruction over the complete party-to-coordinator frame set. -/
structure AuthenticatedReconstruction where
  transcript : PublicTranscript
  completeRoster : Bool
  exactSequence : Bool
  allSignaturesValid : Bool
  deriving DecidableEq, Repr

def MaySignClaim
    (reconstruction : AuthenticatedReconstruction)
    (claimed : PublicTranscript) : Prop :=
  reconstruction.completeRoster = true ∧
  reconstruction.exactSequence = true ∧
  reconstruction.allSignaturesValid = true ∧
  claimed = reconstruction.transcript

theorem signed_claim_is_exact_authenticated_transcript
    {reconstruction : AuthenticatedReconstruction}
    {claimed : PublicTranscript}
    (h : MaySignClaim reconstruction claimed) :
    claimed = reconstruction.transcript :=
  h.2.2.2

theorem substituted_transcript_cannot_be_signed
    {reconstruction : AuthenticatedReconstruction}
    {claimed : PublicTranscript}
    (different : claimed ≠ reconstruction.transcript) :
    ¬ MaySignClaim reconstruction claimed := by
  intro h
  exact different h.2.2.2

/-! ## The named honest residual -/

structure ArithmeticFormation where
  honestInputShares : Bool
  honestBeaverRows : Bool
  honestGateMessages : Bool
  deriving DecidableEq, Repr

structure AcceptedExecution where
  ingress : PeerIngressCheck
  formation : ArithmeticFormation
  deriving DecidableEq, Repr

def TransportAccepted (execution : AcceptedExecution) : Prop :=
  AcceptsPeerIngress execution.ingress

def ArithmeticHonest (execution : AcceptedExecution) : Prop :=
  execution.formation.honestInputShares = true ∧
  execution.formation.honestBeaverRows = true ∧
  execution.formation.honestGateMessages = true

def acceptedDishonestFixture : AcceptedExecution :=
  { ingress :=
      { sessionMatches := true
        routeMatches := true
        signatureValid := true
        aeadValid := true
        sequence := 7
        expectedSequence := 7 }
    formation :=
      { honestInputShares := false
        honestBeaverRows := false
        honestGateMessages := false } }

/-- RED theorem: transport authenticity/confidentiality does not imply
malicious-security of the arithmetic. A legitimately authenticated party can
still form dishonest shares, triples, or gate messages. -/
theorem transport_acceptance_does_not_imply_arithmetic_honesty :
    ∃ execution,
      TransportAccepted execution ∧
      ¬ ArithmeticHonest execution := by
  refine ⟨acceptedDishonestFixture, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [ArithmeticHonest, acceptedDishonestFixture]

/-! Executable boundary teeth. -/

#guard acceptedDishonestFixture.ingress.signatureValid
#guard acceptedDishonestFixture.ingress.aeadValid
#guard !acceptedDishonestFixture.formation.honestInputShares
#guard !acceptedDishonestFixture.formation.honestBeaverRows
#guard !acceptedDishonestFixture.formation.honestGateMessages

#assert_all_clean [
  Market.PartyMpcTransportBoundary.release_independent_of_private_custody,
  Market.PartyMpcTransportBoundary.accepted_peer_ingress_names_every_check,
  Market.PartyMpcTransportBoundary.accepted_peer_ingress_replay_refused,
  Market.PartyMpcTransportBoundary.signed_claim_is_exact_authenticated_transcript,
  Market.PartyMpcTransportBoundary.substituted_transcript_cannot_be_signed,
  Market.PartyMpcTransportBoundary.transport_acceptance_does_not_imply_arithmetic_honesty]

end Market.PartyMpcTransportBoundary
