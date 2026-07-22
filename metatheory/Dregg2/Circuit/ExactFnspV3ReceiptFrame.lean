/-
# Exact FNSP-v3 receipt frames — two linked chains, one typed frame

The exact note-spend descriptor opens a proof-local rotated state whose changing component is
`FNS3(root8,count)`.  A real turn receipt commits the complete actor transition: nonce, fees, and
every effect.  These are deliberately different state machines.  In particular, a genuine turn
can advance the full actor state while the exact descriptor keeps every non-FNS3 lane stable.

This module makes the architectural boundary a Lean type/law rather than a byte-array convention:

* `FullStateCommit` and `ProofOuterCommit` are different types;
* `ReceiptHash`, `ActivationHash`, and `FrameHash` are different link types;
* an exact frame contains an ordinary full-turn receipt and an exact proof-local subreceipt;
* `WellFormedStep` requires full-state continuity, exact-state continuity, and the outer frame link
  independently — it never compares the full receipt's post-state with the proof-local successor;
* the exact points are canonical heads from `ExactFnspV3DurableAuthority`, so their FNS3 values are
  recomputed from their own root and count;
* the durable consequence transition consumes `(epoch activation, frame hash)` once.  A second
  finalization of the same frame is impossible even if a caller replays the accepted proof token.

The receipt/frame digest functions remain parameters.  Collision resistance is a cryptographic
floor, not a Lean axiom.  The laws here prove the typed protocol composition and exactly-once state
machine that must surround those hashes.
-/

import Dregg2.Circuit.ExactFnspV3DurableAuthority

namespace Dregg2.Circuit.ExactFnspV3ReceiptFrame

/-! ## 1. Distinct commitment and link domains -/

/-- Complete actor-state commitment carried by the ordinary turn receipt. -/
structure FullStateCommit where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- Rotated state commitment opened only inside the exact FNSP-v3 proof relation. -/
structure ProofOuterCommit where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- Exact `FNS3(root8,count)` checkpoint.  It is extracted from a canonical exact head. -/
structure Fns3Commit where
  lanes : Dregg2.Circuit.ExactNullifierAafiPlan.Root8

/-- Hash of an ordinary full-turn receipt. -/
structure ReceiptHash where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- Hash of the explicit legacy-to-exact activation record. -/
structure ActivationHash where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- Hash of the versioned exact frame that joins the two receipt domains. -/
structure FrameHash where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- Runtime commitment tags.  Even equal byte payloads remain different protocol objects. -/
inductive CommitmentEnvelope where
  | fullState (commitment : FullStateCommit)
  | proofOuter (commitment : ProofOuterCommit)
  | fns3 (commitment : Fns3Commit)

/-- Runtime link tags.  An activation/frame hash cannot be supplied where the full-turn chain asks
for a receipt hash. -/
inductive LinkEnvelope where
  | receipt (hash : ReceiptHash)
  | activation (hash : ActivationHash)
  | frame (hash : FrameHash)
deriving DecidableEq, Repr

/-- Full actor-state and proof-local outer commitments remain distinct even when their raw bytes
are identical. -/
theorem fullState_ne_proofOuter (full : FullStateCommit) (proof : ProofOuterCommit) :
    CommitmentEnvelope.fullState full ≠ CommitmentEnvelope.proofOuter proof := by
  intro h
  cases h

/-- A full actor-state commitment cannot be reinterpreted as an FNS3 checkpoint. -/
theorem fullState_ne_fns3 (full : FullStateCommit) (exact : Fns3Commit) :
    CommitmentEnvelope.fullState full ≠ CommitmentEnvelope.fns3 exact := by
  intro h
  cases h

/-- The legacy full-turn receipt link is not the exact-epoch activation link. -/
theorem receiptLink_ne_activationLink (receipt : ReceiptHash) (activation : ActivationHash) :
    LinkEnvelope.receipt receipt ≠ LinkEnvelope.activation activation := by
  intro h
  cases h

/-- The full-turn receipt link is not the exact frame link. -/
theorem receiptLink_ne_frameLink (receipt : ReceiptHash) (frame : FrameHash) :
    LinkEnvelope.receipt receipt ≠ LinkEnvelope.frame frame := by
  intro h
  cases h

/-- The activation link and later exact-frame link are distinct constructors. -/
theorem activationLink_ne_frameLink (activation : ActivationHash) (frame : FrameHash) :
    LinkEnvelope.activation activation ≠ LinkEnvelope.frame frame := by
  intro h
  cases h

/-! ## 2. The parallel receipt objects -/

/-- A canonical exact accumulator point.  The proof component makes the FNS3 field derived from
the point's own root/count pair and preserves the permanent-BOT count law. -/
abbrev ExactStatePoint :=
  { head : Dregg2.Circuit.ExactFnspV3DurableAuthority.Head // head.Canonical }

/-- Extract the exact state checkpoint from a canonical point. -/
def exactStateCommit (point : ExactStatePoint) : Fns3Commit :=
  ⟨point.1.fns3⟩

/-- Canonical exact points carry the real FNS3 recomputation equation. -/
theorem exactStateCommit_recomputed (point : ExactStatePoint) :
    (exactStateCommit point).lanes =
      Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan.accumulatorStateCommitReal
        point.1.root (Dregg2.Circuit.ExactFnspV3DurableAuthority.count4 point.1.count) :=
  point.2.2.2

/-- The ordinary executor receipt.  Its hash is supplied by the deployed receipt encoder/hash
function; it is not a caller-selected field of this semantic record. -/
structure FullTurnReceipt where
  previous : ReceiptHash
  preState : FullStateCommit
  postState : FullStateCommit
  effectsCommit : List UInt8
  nonceBefore : Nat
  nonceAfter : Nat
deriving DecidableEq, Repr

/-- Proof-local exact subreceipt.  The accepted-statement and proof-carrier digests keep the exact
transition joined to the proof that authorized it. -/
structure ExactSubreceipt where
  before : ExactStatePoint
  after : ExactStatePoint
  outerBefore : ProofOuterCommit
  outerAfter : ProofOuterCommit
  acceptedStatementDigest : List UInt8
  signedProofDigest : List UInt8

/-- Exact subreceipt validity: one append and no caller-selected FNS3.  The latter is already
enforced by `ExactStatePoint`'s canonical subtype. -/
def ExactSubreceipt.Valid (receipt : ExactSubreceipt) : Prop :=
  receipt.after.1.count = receipt.before.1.count + 1

/-- The exact frame's predecessor is either the explicit activation or a prior exact frame. -/
inductive ExactPredecessor where
  | activation (hash : ActivationHash)
  | frame (hash : FrameHash)
deriving DecidableEq, Repr

/-- Flag-day record.  Both state families are intentionally adjacent but not equated. -/
structure Activation where
  epoch : Nat
  legacyTip : ReceiptHash
  legacyTipPostState : FullStateCommit
  exactInitial : ExactStatePoint

/-- One versioned frame binds a genuine full-turn receipt to its exact proof-local subreceipt. -/
structure ExactFrame where
  epoch : Nat
  activation : ActivationHash
  predecessor : ExactPredecessor
  full : FullTurnReceipt
  exact : ExactSubreceipt

/-- Hash functions are explicit inputs.  No injectivity/collision-resistance axiom is hidden in
the structural receipt laws. -/
abbrev ReceiptHasher := FullTurnReceipt → ReceiptHash
abbrev ActivationHasher := Activation → ActivationHash
abbrev FrameHasher := ExactFrame → FrameHash

/-! ## 3. Independent linkage relations -/

/-- Ordinary full-turn continuity.  This is the only relation that compares complete actor-state
commitments. -/
structure FullReceiptLinked (receiptHash : ReceiptHasher)
    (previous next : FullTurnReceipt) : Prop where
  predecessor : next.previous = receiptHash previous
  state : next.preState = previous.postState
  nonce : next.nonceAfter = next.nonceBefore + 1

/-- Exact proof-local continuity.  This relation sees neither full receipt commitment. -/
structure ExactStateLinked (previous next : ExactSubreceipt) : Prop where
  state : next.before = previous.after
  valid : next.Valid

/-- Outer-frame continuity.  The frame hash joins both embedded receipt objects without making
their state commitments equal. -/
def FrameLinked (frameHash : FrameHasher) (previous next : ExactFrame) : Prop :=
  next.predecessor = .frame (frameHash previous) ∧
  next.activation = previous.activation ∧
  next.epoch = previous.epoch

/-- The first exact frame links the ordinary receipt chain to the terminal legacy receipt and the
exact state chain to the independently reconstructed exact activation point. -/
structure WellFormedFirst (activationHash : ActivationHasher)
    (activation : Activation) (frame : ExactFrame) : Prop where
  nonzeroEpoch : activation.epoch ≠ 0
  epoch : frame.epoch = activation.epoch
  activationMatches : frame.activation = activationHash activation
  framePredecessor : frame.predecessor = .activation (activationHash activation)
  fullPredecessor : frame.full.previous = activation.legacyTip
  fullPreState : frame.full.preState = activation.legacyTipPostState
  fullNonce : frame.full.nonceAfter = frame.full.nonceBefore + 1
  exactPreState : frame.exact.before = activation.exactInitial
  exactValid : frame.exact.Valid

/-- A later frame advances all three links independently.  Notice there is no field of the shape
`next.full.postState = next.exact.outerAfter`; the comparison is absent by construction. -/
structure WellFormedStep (receiptHash : ReceiptHasher) (frameHash : FrameHasher)
    (previous next : ExactFrame) : Prop where
  full : FullReceiptLinked receiptHash previous.full next.full
  exact : ExactStateLinked previous.exact next.exact
  frame : FrameLinked frameHash previous next

/-- The first frame begins at the activated exact accumulator point. -/
theorem first_exact_begins_at_activation
    {activationHash : ActivationHasher} {activation : Activation} {frame : ExactFrame}
    (h : WellFormedFirst activationHash activation frame) :
    frame.exact.before = activation.exactInitial :=
  h.exactPreState

/-- The first exact frame advances the physical count exactly once. -/
theorem first_exact_count_increments
    {activationHash : ActivationHasher} {activation : Activation} {frame : ExactFrame}
    (h : WellFormedFirst activationHash activation frame) :
    frame.exact.after.1.count = activation.exactInitial.1.count + 1 := by
  rw [h.exactValid, h.exactPreState]

/-- A well-formed continuation extends the genuine full-turn receipt hash chain. -/
theorem step_full_receipt_link
    {receiptHash : ReceiptHasher} {frameHash : FrameHasher} {previous next : ExactFrame}
    (h : WellFormedStep receiptHash frameHash previous next) :
    next.full.previous = receiptHash previous.full :=
  h.full.predecessor

/-- A well-formed continuation extends the genuine full actor-state chain. -/
theorem step_full_state_link
    {receiptHash : ReceiptHasher} {frameHash : FrameHasher} {previous next : ExactFrame}
    (h : WellFormedStep receiptHash frameHash previous next) :
    next.full.preState = previous.full.postState :=
  h.full.state

/-- A well-formed continuation separately extends the exact root/count/FNS3 chain. -/
theorem step_exact_state_link
    {receiptHash : ReceiptHasher} {frameHash : FrameHasher} {previous next : ExactFrame}
    (h : WellFormedStep receiptHash frameHash previous next) :
    next.exact.before = previous.exact.after :=
  h.exact.state

/-- A well-formed continuation advances the exact physical count exactly once. -/
theorem step_exact_count_increments
    {receiptHash : ReceiptHasher} {frameHash : FrameHasher} {previous next : ExactFrame}
    (h : WellFormedStep receiptHash frameHash previous next) :
    next.exact.after.1.count = previous.exact.after.1.count + 1 := by
  rw [h.exact.valid, h.exact.state]

/-- A well-formed continuation advances the ordinary executor nonce exactly once as well.  The
two increments coexist, but their commitment objects remain unrelated. -/
theorem step_full_nonce_increments
    {receiptHash : ReceiptHasher} {frameHash : FrameHasher} {previous next : ExactFrame}
    (h : WellFormedStep receiptHash frameHash previous next) :
    next.full.nonceAfter = next.full.nonceBefore + 1 :=
  h.full.nonce

/-- The outer exact-frame chain links to the prior frame hash, never the full receipt hash. -/
theorem step_frame_link
    {receiptHash : ReceiptHasher} {frameHash : FrameHasher} {previous next : ExactFrame}
    (h : WellFormedStep receiptHash frameHash previous next) :
    next.predecessor = .frame (frameHash previous) :=
  h.frame.1

/-- Exact-state continuity is invariant under replacing either complete full-turn receipt.  This
is the formal non-comparison law: proof-local successor validity does not inspect full post-state.
The outer frame hash still joins the chosen full receipt at the enclosing `WellFormedStep` layer. -/
theorem exactStateLinked_ignores_full_receipts
    (previous next : ExactFrame) (previousFull nextFull : FullTurnReceipt) :
    ExactStateLinked
        ({ previous with full := previousFull }).exact
        ({ next with full := nextFull }).exact ↔
      ExactStateLinked previous.exact next.exact := by
  rfl

/-- Even byte-identical raw payloads remain separated at the commitment boundary.  This is the
executable shape of “do not compare `TurnReceipt.post_state_hash` with proof-local AFTER.” -/
theorem byteIdentical_full_and_proof_still_distinct (bytes : List UInt8) :
    CommitmentEnvelope.fullState ⟨bytes⟩ ≠ CommitmentEnvelope.proofOuter ⟨bytes⟩ :=
  fullState_ne_proofOuter _ _

/-! ## 4. Durable exactly-once consequence consumption -/

/-- Global durable consequence identity.  It includes the activated epoch and exact frame hash;
a per-object boolean is not sufficient for cross-instance replay protection. -/
structure ConsequenceKey where
  activation : ActivationHash
  frame : FrameHash
deriving DecidableEq, Repr

/-- Derive the only key under which a frame's externally visible consequence may commit. -/
def consequenceKey (frameHash : FrameHasher) (frame : ExactFrame) : ConsequenceKey :=
  { activation := frame.activation, frame := frameHash frame }

/-- Durable global set, represented extensionally as a newest-first list. -/
abbrev Consumed := List ConsequenceKey

/-- Exactly one fresh global consumption.  This is the semantic CAS transition; persistence and
crash-atomic realization remain the store implementation's refinement obligation. -/
inductive ConsumeStep : Consumed → ConsequenceKey → Consumed → Prop where
  | fresh {seen : Consumed} {key : ConsequenceKey} (notSeen : key ∉ seen) :
      ConsumeStep seen key (key :: seen)

/-- Successful consumption inserts exactly the requested global key. -/
theorem consumeStep_result {seen next : Consumed} {key : ConsequenceKey}
    (h : ConsumeStep seen key next) : next = key :: seen := by
  cases h
  rfl

/-- A key at the durable head cannot be consumed again. -/
theorem consumed_head_refuses_replay (seen : Consumed) (key : ConsequenceKey) :
    ¬ ConsumeStep (key :: seen) key (key :: key :: seen) := by
  intro h
  cases h with
  | fresh notSeen => exact notSeen (by simp)

/-- **Exactly once.** After one successful consumption, no second transition for the same key can
start from the resulting durable state. -/
theorem successful_consume_cannot_repeat
    {seen once twice : Consumed} {key : ConsequenceKey}
    (first : ConsumeStep seen key once) : ¬ ConsumeStep once key twice := by
  cases first with
  | fresh notSeen =>
      intro second
      cases second with
      | fresh notSeenAgain => exact notSeenAgain (by simp)

/-- A successful consumption transition is deterministic. -/
theorem consumeStep_deterministic
    {seen left right : Consumed} {key : ConsequenceKey}
    (hleft : ConsumeStep seen key left) (hright : ConsumeStep seen key right) : left = right := by
  rw [consumeStep_result hleft, consumeStep_result hright]

/-- Finalizing the same exact frame twice is impossible, even if the proof carrier is replayed. -/
theorem exactFrame_finalizes_at_most_once
    {frameHash : FrameHasher} {seen once twice : Consumed} {frame : ExactFrame}
    (first : ConsumeStep seen (consequenceKey frameHash frame) once) :
    ¬ ConsumeStep once (consequenceKey frameHash frame) twice :=
  successful_consume_cannot_repeat first

/-! ## 5. Axiom hygiene -/

#assert_axioms fullState_ne_proofOuter
#assert_axioms fullState_ne_fns3
#assert_axioms receiptLink_ne_activationLink
#assert_axioms receiptLink_ne_frameLink
#assert_axioms activationLink_ne_frameLink
#assert_axioms exactStateCommit_recomputed
#assert_axioms first_exact_begins_at_activation
#assert_axioms first_exact_count_increments
#assert_axioms step_full_receipt_link
#assert_axioms step_full_state_link
#assert_axioms step_exact_state_link
#assert_axioms step_exact_count_increments
#assert_axioms step_full_nonce_increments
#assert_axioms step_frame_link
#assert_axioms exactStateLinked_ignores_full_receipts
#assert_axioms byteIdentical_full_and_proof_still_distinct
#assert_axioms consumeStep_result
#assert_axioms consumed_head_refuses_replay
#assert_axioms successful_consume_cannot_repeat
#assert_axioms consumeStep_deterministic
#assert_axioms exactFrame_finalizes_at_most_once

end Dregg2.Circuit.ExactFnspV3ReceiptFrame
