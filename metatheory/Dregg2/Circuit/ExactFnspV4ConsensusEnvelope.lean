/-
# Exact FNSP-v4 consensus cores and local validator envelopes

FNSP-v3 activation records include the executing node's local public key in the
activation-hash preimage.  Two honest validators with different local keys therefore do not even
hash the same bytes.  That is a consensus-determinism defect, independently of signature or hash
security.

This module states the corrective v4 boundary as Lean types:

* `ActivationCore` and `FrameCore` contain only common finalized-input coordinates;
* `LocalEvidence` contains the validator identity, local receipt bytes, and signature;
* `LocalEnvelope.message` is derived from an already-fixed `FrameId`;
* replacing any local evidence cannot change the consensus message;
* an envelope verified for one frame core cannot verify for a core with a different frame ID.

Hashing and signature verification remain explicit parameters.  The final theorem bottoms out at
frame-ID equality: excluding collisions is a cryptographic floor, not a structural Lean axiom.
This module models one local validator envelope only.  It deliberately does not claim a threshold
or committee-signature construction.
-/

import Dregg2.Circuit.ExactFnspV3ReceiptFrame

namespace Dregg2.Circuit.ExactFnspV4ConsensusEnvelope

open Dregg2.Circuit.ExactFnspV3ReceiptFrame

/-! ## 1. Distinct consensus identities -/

/-- Hash of a signer-independent exact-v4 activation core. -/
structure ActivationId where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- Hash of a signer-independent exact-v4 frame core. -/
structure FrameId where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- The activation predecessor and frame predecessor remain different runtime constructors even
when their raw digest bytes happen to agree. -/
inductive FramePredecessor where
  | activation (id : ActivationId)
  | frame (id : FrameId)
deriving DecidableEq, Repr

inductive ConsensusLink where
  | activation (id : ActivationId)
  | frame (id : FrameId)
deriving DecidableEq, Repr

theorem activationLink_ne_frameLink (activation : ActivationId) (frame : FrameId) :
    ConsensusLink.activation activation ≠ ConsensusLink.frame frame := by
  intro h
  cases h

/-! ## 2. Signer-independent common cores -/

/-- Deterministic flag-day coordinates.  In particular there is no executor/validator public key,
signature, wall clock, or locally encoded signed receipt in this structure. -/
structure ActivationCore where
  protocolEpoch : Nat
  federation : List UInt8
  committeeEpoch : Nat
  receiptCutoverCursor : Nat
  receiptCutoverTip : Option ReceiptHash
  exactInitial : ExactStatePoint
  verifierProgramId : List UInt8
  transitionProgramId : List UInt8

/-- Structural activation validity.  Authorization by finalized federation policy is a separate
store/finality relation; it is not caller-authored data inside the core. -/
structure ActivationCore.Valid (core : ActivationCore) : Prop where
  nonzeroProtocolEpoch : core.protocolEpoch ≠ 0
  cutoverShape : (core.receiptCutoverCursor = 0) ↔ core.receiptCutoverTip = none

/-- Deterministic exact-frame coordinates reconstructed from the finalized block and pre-state.
Every field belongs to the consensus transition.  Local validator identity and signature material
are absent by construction. -/
structure FrameCore where
  activation : ActivationId
  sequence : Nat
  predecessor : FramePredecessor
  receiptIndex : Nat
  receiptHash : ReceiptHash
  fullPredecessorIndex : Option Nat
  fullPredecessorHash : Option ReceiptHash
  blockId : List UInt8
  commitOrdinal : Nat
  turnHash : List UInt8
  forestHash : List UInt8
  actor : List UInt8
  federation : List UInt8
  fullPreState : FullStateCommit
  fullPostState : FullStateCommit
  exactBefore : ExactStatePoint
  exactAfter : ExactStatePoint
  acceptedStatementDigest : List UInt8
  acceptedProofDigest : List UInt8
  consequenceCommitment : List UInt8
  outputNotesCommitment : List UInt8

/-- The frame's structural step law.  Durable receipt lookup, finalized-block membership, proof
acceptance, and consequence persistence are independent authority relations layered around it. -/
structure FrameCore.Valid (core : FrameCore) : Prop where
  positiveSequence : core.sequence ≠ 0
  receiptPredecessorShape :
    core.fullPredecessorIndex.isSome = core.fullPredecessorHash.isSome
  receiptPredecessorOrder :
    ∀ index, core.fullPredecessorIndex = some index → index < core.receiptIndex
  exactCountStep : core.exactAfter.1.count = core.exactBefore.1.count + 1

abbrev ActivationHasher := ActivationCore → ActivationId
abbrev FrameHasher := FrameCore → FrameId

/-- The common frame is scoped to the common activation.  This prevents a perfectly well-shaped
frame for another federation or activation from borrowing the current envelope policy. -/
structure CommonCoresLinked (activationHash : ActivationHasher)
    (activation : ActivationCore) (frame : FrameCore) : Prop where
  activationId : frame.activation = activationHash activation
  federation : frame.federation = activation.federation

/-- Local signer material is intentionally a separate type.  `receiptEvidence` may retain the
node-local signed executor receipt for recovery, but it is not a frame-ID input. -/
structure LocalEvidence (Validator Signature : Type) where
  validator : Validator
  receiptEvidence : List UInt8
  signature : Signature

/-- A deliberately defective v3-shaped activation preimage.  This is retained only to state the
counterexample: the node-local key occurs inside the would-be common hash preimage. -/
structure LegacyV3ActivationPreimage where
  common : ActivationCore
  localExecutorPublicKey : List UInt8

/-- Different local executor keys produce different v3 structural preimages for the same common
finalized input.  The result is about bytes-before-hashing and therefore needs no hash assumption. -/
theorem legacyV3_preimage_depends_on_local_signer
    (common : ActivationCore) {leftKey rightKey : List UInt8} (hne : leftKey ≠ rightKey) :
    LegacyV3ActivationPreimage.mk common leftKey ≠
      LegacyV3ActivationPreimage.mk common rightKey := by
  intro h
  exact hne (congrArg LegacyV3ActivationPreimage.localExecutorPublicKey h)

/-- What a validator deterministically derives from common cores.  The local evidence argument is
present to state the noninterference boundary, but cannot flow into either identifier. -/
def deriveConsensusAtValidator {Validator Signature : Type}
    (activationHash : ActivationHasher) (frameHash : FrameHasher)
    (activation : ActivationCore) (frame : FrameCore)
    (_local : LocalEvidence Validator Signature) : ActivationId × FrameId :=
  (activationHash activation, frameHash frame)

/-- **Signer erasure.** Distinct local identities, receipt bytes, or signatures cannot change the
activation/frame IDs derived from one common finalized input. -/
theorem consensusIds_independent_of_local_signer
    {Validator Signature : Type}
    (activationHash : ActivationHasher) (frameHash : FrameHasher)
    (activation : ActivationCore) (frame : FrameCore)
    (left right : LocalEvidence Validator Signature) :
    deriveConsensusAtValidator activationHash frameHash activation frame left =
      deriveConsensusAtValidator activationHash frameHash activation frame right := by
  rfl

/-- Local signer material also cannot alter either committed successor state.  This is the state
half of deterministic re-execution, separated from the ID theorem above. -/
def deriveSuccessorAtValidator {Validator Signature : Type}
    (frame : FrameCore) (_local : LocalEvidence Validator Signature) :
    FullStateCommit × ExactStatePoint :=
  (frame.fullPostState, frame.exactAfter)

theorem successorState_independent_of_local_signer
    {Validator Signature : Type} (frame : FrameCore)
    (left right : LocalEvidence Validator Signature) :
    deriveSuccessorAtValidator frame left = deriveSuccessorAtValidator frame right := by
  rfl

/-! ## 3. A local envelope authenticates one fixed common core -/

/-- Exact message authenticated by one local validator.  The block ordinal prevents moving an
otherwise valid observation to another durable commit position. -/
structure EnvelopeMessage where
  federation : List UInt8
  committeeEpoch : Nat
  blockId : List UInt8
  commitOrdinal : Nat
  frame : FrameId
deriving DecidableEq, Repr

/-- Construct the only local-signature message for a frame core. -/
def envelopeMessage (activation : ActivationCore) (frameHash : FrameHasher)
    (frame : FrameCore) : EnvelopeMessage :=
  { federation := activation.federation
    committeeEpoch := activation.committeeEpoch
    blockId := frame.blockId
    commitOrdinal := frame.commitOrdinal
    frame := frameHash frame }

/-- Local evidence around an already-fixed consensus message.  Honest validators may store
different values of `evidence`; the `message` must be identical. -/
structure LocalEnvelope (Validator Signature : Type) where
  message : EnvelopeMessage
  evidence : LocalEvidence Validator Signature

/-- Mint a local envelope without giving local signer material any route into the message. -/
def makeLocalEnvelope {Validator Signature : Type}
    (activation : ActivationCore) (frameHash : FrameHasher) (frame : FrameCore)
    (evidence : LocalEvidence Validator Signature) : LocalEnvelope Validator Signature :=
  { message := envelopeMessage activation frameHash frame
    evidence := evidence }

/-- Replacing all local receipt/signature evidence preserves the consensus message definitionally. -/
def LocalEnvelope.replaceLocal {Validator Signature : Type}
    (envelope : LocalEnvelope Validator Signature)
    (evidence : LocalEvidence Validator Signature) : LocalEnvelope Validator Signature :=
  { envelope with evidence := evidence }

theorem replaceLocal_preserves_consensus_message
    {Validator Signature : Type} (envelope : LocalEnvelope Validator Signature)
    (evidence : LocalEvidence Validator Signature) :
    (envelope.replaceLocal evidence).message = envelope.message := by
  rfl

/-- Two validators enveloping the same core obtain byte-identical consensus messages, regardless of
their validator identity, local receipt encoding, or signature bytes. -/
theorem local_envelopes_share_consensus_message
    {Validator Signature : Type}
    (activation : ActivationCore) (frameHash : FrameHasher) (frame : FrameCore)
    (left right : LocalEvidence Validator Signature) :
    (makeLocalEnvelope activation frameHash frame left).message =
      (makeLocalEnvelope activation frameHash frame right).message := by
  rfl

/-- Signature verification is an explicit predicate.  No cryptographic correctness, unforgeability,
hybrid composition, threshold, or committee-quorum claim is hidden in this structural module. -/
abbrev SignatureVerifier (Validator Signature : Type) :=
  Validator → EnvelopeMessage → Signature → Prop

/-- Verification first pins the envelope to the recomputed common-core message, then checks the
local signature over that exact message. -/
structure EnvelopeVerified {Validator Signature : Type}
    (verify : SignatureVerifier Validator Signature)
    (activationHash : ActivationHasher) (activation : ActivationCore)
    (frameHash : FrameHasher) (frame : FrameCore)
    (envelope : LocalEnvelope Validator Signature) : Prop where
  common : CommonCoresLinked activationHash activation frame
  fixedCore : envelope.message = envelopeMessage activation frameHash frame
  signature :
    verify envelope.evidence.validator envelope.message envelope.evidence.signature

/-- A verified envelope authenticates exactly the recomputed frame ID—not a signer-selected ID. -/
theorem verifiedEnvelope_frame_fixed
    {Validator Signature : Type} {verify : SignatureVerifier Validator Signature}
    {activationHash : ActivationHasher} {activation : ActivationCore}
    {frameHash : FrameHasher} {frame : FrameCore}
    {envelope : LocalEnvelope Validator Signature}
    (h : EnvelopeVerified verify activationHash activation frameHash frame envelope) :
    envelope.message.frame = frameHash frame := by
  rw [h.fixedCore]
  rfl

/-- The signature verifier receives the fixed, recomputed core message. -/
theorem verifiedEnvelope_signature_checks_recomputed_message
    {Validator Signature : Type} {verify : SignatureVerifier Validator Signature}
    {activationHash : ActivationHasher} {activation : ActivationCore}
    {frameHash : FrameHasher} {frame : FrameCore}
    {envelope : LocalEnvelope Validator Signature}
    (h : EnvelopeVerified verify activationHash activation frameHash frame envelope) :
    verify envelope.evidence.validator (envelopeMessage activation frameHash frame)
      envelope.evidence.signature := by
  rw [← h.fixedCore]
  exact h.signature

/-- **Fixed-core envelope soundness.** An envelope accepted for one core cannot also be accepted for
a core whose recomputed frame ID differs.  Turning frame-ID equality into core equality is exactly
the collision-resistance/refinement obligation left outside this structural theorem. -/
theorem verifiedEnvelope_refuses_different_frameId
    {Validator Signature : Type} {verify : SignatureVerifier Validator Signature}
    {activationHash : ActivationHasher} {activation : ActivationCore}
    {frameHash : FrameHasher} {frame other : FrameCore}
    {envelope : LocalEnvelope Validator Signature}
    (accepted : EnvelopeVerified verify activationHash activation frameHash frame envelope)
    (different : frameHash frame ≠ frameHash other) :
    ¬ EnvelopeVerified verify activationHash activation frameHash other envelope := by
  intro otherAccepted
  apply different
  rw [← verifiedEnvelope_frame_fixed accepted]
  exact verifiedEnvelope_frame_fixed otherAccepted

/-! ## 4. Activation and the first accepted frame commit atomically -/

/-- Minimal durable exact-v4 consensus head.  Local envelopes live in a separate evidence table;
neither local signatures nor their availability decide this common head. -/
structure DurableConsensusHead where
  activation : Option ActivationId
  frame : Option FrameId
  exact : ExactStatePoint

/-- The only inactive-to-active transition installs an authorized activation and an already
accepted first frame in one state-machine step.  `accepted` and `authorized` are store/finality
relations supplied by the caller; they are not booleans inside the payload. -/
inductive ActivateAndAppend
    (activationHash : ActivationHasher) (frameHash : FrameHasher)
    (accepted : FrameCore → Prop) (authorized : ActivationCore → FrameCore → Prop) :
    DurableConsensusHead → ActivationCore → FrameCore → DurableConsensusHead → Prop where
  | first {before : DurableConsensusHead} {activation : ActivationCore} {frame : FrameCore}
      (inactiveActivation : before.activation = none)
      (inactiveFrame : before.frame = none)
      (activationValid : activation.Valid)
      (frameValid : frame.Valid)
      (linked : CommonCoresLinked activationHash activation frame)
      (firstSequence : frame.sequence = 1)
      (firstPredecessor : frame.predecessor = .activation (activationHash activation))
      (exactBefore : frame.exactBefore = before.exact)
      (hAccepted : accepted frame)
      (hAuthorized : authorized activation frame) :
      ActivateAndAppend activationHash frameHash accepted authorized before activation frame
        { activation := some (activationHash activation)
          frame := some (frameHash frame)
          exact := frame.exactAfter }

/-- A successful activation always carries the accepted first frame that caused it.  There is no
activation-only constructor for a rejected or merely parsed payload. -/
theorem activateAndAppend_requires_accepted
    {activationHash : ActivationHasher} {frameHash : FrameHasher}
    {accepted : FrameCore → Prop} {authorized : ActivationCore → FrameCore → Prop}
    {before after : DurableConsensusHead} {activation : ActivationCore} {frame : FrameCore}
    (h : ActivateAndAppend activationHash frameHash accepted authorized before activation frame
      after) : accepted frame := by
  cases h
  assumption

/-- A rejected first frame cannot select or persist an activation cutover. -/
theorem rejectedFrame_cannot_activate
    {activationHash : ActivationHasher} {frameHash : FrameHasher}
    {accepted : FrameCore → Prop} {authorized : ActivationCore → FrameCore → Prop}
    {before after : DurableConsensusHead} {activation : ActivationCore} {frame : FrameCore}
    (rejected : ¬ accepted frame) :
    ¬ ActivateAndAppend activationHash frameHash accepted authorized before activation frame
      after := by
  intro h
  exact rejected (activateAndAppend_requires_accepted h)

/-- The atomic step's entire durable successor is fixed by the common cores. -/
theorem activateAndAppend_result
    {activationHash : ActivationHasher} {frameHash : FrameHasher}
    {accepted : FrameCore → Prop} {authorized : ActivationCore → FrameCore → Prop}
    {before after : DurableConsensusHead} {activation : ActivationCore} {frame : FrameCore}
    (h : ActivateAndAppend activationHash frameHash accepted authorized before activation frame
      after) :
    after =
      { activation := some (activationHash activation)
        frame := some (frameHash frame)
        exact := frame.exactAfter } := by
  cases h
  rfl

/-- In every successful step the activation and first-frame heads become present together. -/
theorem activateAndAppend_no_activation_only_result
    {activationHash : ActivationHasher} {frameHash : FrameHasher}
    {accepted : FrameCore → Prop} {authorized : ActivationCore → FrameCore → Prop}
    {before after : DurableConsensusHead} {activation : ActivationCore} {frame : FrameCore}
    (h : ActivateAndAppend activationHash frameHash accepted authorized before activation frame
      after) :
    after.activation.isSome = true ∧ after.frame.isSome = true := by
  rw [activateAndAppend_result h]
  simp

/-- The atomic inactive-to-active transition is deterministic for fixed common inputs. -/
theorem activateAndAppend_deterministic
    {activationHash : ActivationHasher} {frameHash : FrameHasher}
    {accepted : FrameCore → Prop} {authorized : ActivationCore → FrameCore → Prop}
    {before left right : DurableConsensusHead} {activation : ActivationCore} {frame : FrameCore}
    (hleft : ActivateAndAppend activationHash frameHash accepted authorized before activation frame
      left)
    (hright : ActivateAndAppend activationHash frameHash accepted authorized before activation frame
      right) : left = right := by
  rw [activateAndAppend_result hleft, activateAndAppend_result hright]

/-! ## 5. Axiom hygiene -/

#assert_axioms activationLink_ne_frameLink
#assert_axioms legacyV3_preimage_depends_on_local_signer
#assert_axioms consensusIds_independent_of_local_signer
#assert_axioms successorState_independent_of_local_signer
#assert_axioms replaceLocal_preserves_consensus_message
#assert_axioms local_envelopes_share_consensus_message
#assert_axioms verifiedEnvelope_frame_fixed
#assert_axioms verifiedEnvelope_signature_checks_recomputed_message
#assert_axioms verifiedEnvelope_refuses_different_frameId
#assert_axioms activateAndAppend_requires_accepted
#assert_axioms rejectedFrame_cannot_activate
#assert_axioms activateAndAppend_result
#assert_axioms activateAndAppend_no_activation_only_result
#assert_axioms activateAndAppend_deterministic

end Dregg2.Circuit.ExactFnspV4ConsensusEnvelope
