/-
# Shielded v4 finalization — apex, consensus core, time, and terminal ACK in one step

This module composes three already-separated layers:

* `ShieldedExactApexV4.Relation`: one shared hidden opening determines the full nullifier,
  wide value/asset binding, conserved consequence, FNS4 append, and exact output-note root;
* `ExactFnspV4ConsensusEnvelope`: signer-independent activation/frame identities with local
  validator evidence outside the common core; and
* `ConsensusTimeAck`: finalized execution reads authenticated causal time and only a committed
  installation produces this transition's installation ACK.

`AtomicCommit.first` is deliberately the only state-changing constructor.  It installs activation,
first frame, FNS4 successor, exact output-note root, and deterministic receipt core as one
value.  There is no activation-only, frame-only, note-only, or receipt-only state.  A proof/frame
rejection therefore cannot construct the transition; retry/fatal outcomes preserve the predecessor.

The local envelope may be retained as evidence, but it is absent from `DeterministicReceiptCore`.
Likewise a validator wall clock is not an input to the transition.  Hash/signature/proof-system
soundness remains exactly where the imported modules put it: in explicit hasher, verifier, and
`PinnedVerifierContract.knowledgeSound` fields.  No new cryptographic axiom is introduced here.
-/

import Dregg2.Circuit.ShieldedExactApexV4
import Dregg2.Circuit.ExactFnspV4ConsensusEnvelope
import Dregg2.Distributed.ConsensusTimeAck

namespace Dregg2.Circuit.ShieldedV4Finalization

set_option autoImplicit false

/-! ## 1. The fixed deployed system and one finalized input -/

/-- Code-owned functions and the pinned verifier contract for one shielded-v4 deployment.
`projectExact` is the explicit representation bridge from the envelope's canonical durable point to
the FNS4 semantic point.  The two root encoders are likewise named byte-boundary obligations, not
hidden coercions. -/
structure System (BlockId Validator Signature : Type) where
  apex : ShieldedExactApexV4.Environment
  expectedRelationId : List UInt8
  expectedVerifierKey : List UInt8
  contract : ShieldedExactApexV4.PinnedVerifierContract apex expectedRelationId expectedVerifierKey
  activationHash : ExactFnspV4ConsensusEnvelope.ActivationHasher
  frameHash : ExactFnspV4ConsensusEnvelope.FrameHasher
  verify : ExactFnspV4ConsensusEnvelope.SignatureVerifier Validator Signature
  authorized : ExactFnspV4ConsensusEnvelope.ActivationCore → ExactFnspV4ConsensusEnvelope.FrameCore → Prop
  projectExact :
    Dregg2.Circuit.ExactFnspV3ReceiptFrame.ExactStatePoint → ShieldedExactApexV4.ExactState
  encodeBlockId : BlockId → List UInt8
  encodeRoot : ShieldedExactApexV4.Root8 → List UInt8

/-- One finalized candidate.  Consensus time lives only in the authenticated context.  Local
validator evidence lives only in `envelope`. -/
structure FinalizedInput (BlockId Validator Signature : Type) where
  activation : ExactFnspV4ConsensusEnvelope.ActivationCore
  frame : ExactFnspV4ConsensusEnvelope.FrameCore
  statement : ShieldedExactApexV4.PublicStatement
  context : Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionContext BlockId
  predecessorTimes : List Int
  envelope : ExactFnspV4ConsensusEnvelope.LocalEnvelope Validator Signature

/-- Replace every local evidence byte while preserving the common finalized input. -/
def FinalizedInput.replaceEnvelope
    {BlockId Validator Signature : Type}
    (input : FinalizedInput BlockId Validator Signature)
    (envelope : ExactFnspV4ConsensusEnvelope.LocalEnvelope Validator Signature) :
    FinalizedInput BlockId Validator Signature :=
  { input with envelope }

/-- The frame acceptance predicate supplied to the imported atomic activation step.  It pins the
fixed frame, the sound verifier's acceptance, both exact-state representations, finalized block
context, and the two shielded public roots. -/
def FrameAccepts
    {BlockId Validator Signature : Type}
    (system : System BlockId Validator Signature)
    (input : FinalizedInput BlockId Validator Signature)
    (candidate : ExactFnspV4ConsensusEnvelope.FrameCore) : Prop :=
  candidate = input.frame ∧
  system.contract.accepts input.statement ∧
  system.projectExact candidate.exactBefore = input.statement.exactBefore ∧
  system.projectExact candidate.exactAfter = input.statement.exactAfter ∧
  candidate.blockId = system.encodeBlockId input.context.blockId ∧
  candidate.commitOrdinal = input.context.ordinal ∧
  candidate.outputNotesCommitment = system.encodeRoot input.statement.outputNotesRoot ∧
  candidate.consequenceCommitment = system.encodeRoot input.statement.consequence ∧
  input.activation.transitionProgramId = system.contract.relationId ∧
  input.activation.verifierProgramId = system.contract.verifierKey

/-! ## 2. Deterministic receipt core and the single atomic durable state -/

/-- Signer-independent receipt identity material installed by a successful transition.  It binds
the authenticated time context and the semantic FNS4/output consequence, but contains no local
validator, receipt envelope, signature, wall clock, or serialization choice. -/
structure DeterministicReceiptCore (BlockId : Type) where
  activation : ExactFnspV4ConsensusEnvelope.ActivationId
  frame : ExactFnspV4ConsensusEnvelope.FrameId
  blockId : BlockId
  commitOrdinal : Nat
  consensusTime : Int
  exactAfter : ShieldedExactApexV4.ExactState
  outputNotesRoot : ShieldedExactApexV4.Root8
  consequence : ShieldedExactApexV4.Root8

/-- Derive the deterministic receipt core from common input only. -/
def receiptCore
    {BlockId Validator Signature : Type}
    (system : System BlockId Validator Signature)
    (input : FinalizedInput BlockId Validator Signature) :
    DeterministicReceiptCore BlockId :=
  { activation := system.activationHash input.activation
    frame := system.frameHash input.frame
    blockId := input.context.blockId
    commitOrdinal := input.context.ordinal
    consensusTime := input.context.consensusTime
    exactAfter := input.statement.exactAfter
    outputNotesRoot := input.statement.outputNotesRoot
    consequence := input.statement.consequence }

/-- The one durable shielded-v4 image.  `consensus.frame` and `receiptCore` are redundant on purpose:
the theorem below proves they are installed together and name the same fixed frame. -/
structure DurableState (BlockId : Type) where
  consensus : ExactFnspV4ConsensusEnvelope.DurableConsensusHead
  fns4 : ShieldedExactApexV4.ExactState
  createdOutputNotesRoot : Option ShieldedExactApexV4.Root8
  receiptCore : Option (DeterministicReceiptCore BlockId)

/-- One successful state transition.  Every persistent component occurs in the constructor's one
successor value, so an implementation refining this relation must use one atomic durability event. -/
inductive AtomicCommit
    {BlockId Validator Signature : Type}
    (system : System BlockId Validator Signature)
    (timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy) :
    DurableState BlockId → FinalizedInput BlockId Validator Signature →
      DurableState BlockId → DeterministicReceiptCore BlockId → Prop where
  | first
      {before : DurableState BlockId}
      {input : FinalizedInput BlockId Validator Signature}
      {afterConsensus : ExactFnspV4ConsensusEnvelope.DurableConsensusHead}
      (timeValid : Dregg2.Distributed.ConsensusTimeAck.validClaim timePolicy input.predecessorTimes
        { unixSeconds := input.context.consensusTime })
      (envelopeValid : ExactFnspV4ConsensusEnvelope.EnvelopeVerified system.verify system.activationHash
        input.activation system.frameHash input.frame input.envelope)
      (fns4Before : before.fns4 = input.statement.exactBefore)
      (activate : ExactFnspV4ConsensusEnvelope.ActivateAndAppend system.activationHash system.frameHash
        (FrameAccepts system input) system.authorized before.consensus input.activation input.frame
        afterConsensus) :
      AtomicCommit system timePolicy before input
        { consensus := afterConsensus
          fns4 := input.statement.exactAfter
          createdOutputNotesRoot := some input.statement.outputNotesRoot
          receiptCore := some (receiptCore system input) }
        (receiptCore system input)

/-! ## 3. The composition theorems -/

/-- The atomic transition has one definitionally fixed successor and deterministic receipt core. -/
theorem AtomicCommit.result
    {BlockId Validator Signature : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before after : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {receipt : DeterministicReceiptCore BlockId}
    (committed : AtomicCommit system timePolicy before input after receipt) :
    after.fns4 = input.statement.exactAfter ∧
      after.createdOutputNotesRoot = some input.statement.outputNotesRoot ∧
      after.receiptCore = some (receiptCore system input) ∧
      receipt = receiptCore system input := by
  cases committed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Acceptance of the installed frame extracts one shared-witness apex relation from the pinned
verifier contract.  This is the proof-system-to-semantics join. -/
theorem AtomicCommit.has_shared_witness
    {BlockId Validator Signature : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before after : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {receipt : DeterministicReceiptCore BlockId}
    (committed : AtomicCommit system timePolicy before input after receipt) :
    ∃ witness, ShieldedExactApexV4.Relation system.apex witness input.statement := by
  cases committed with
  | first _ _ _ activate =>
      have accepted := ExactFnspV4ConsensusEnvelope.activateAndAppend_requires_accepted activate
      exact system.contract.knowledgeSound input.statement accepted.2.1

/-- A successful transition advances FNS4 by exactly one and installs the exact root of the hidden
output-note list extracted from the same apex witness. -/
theorem AtomicCommit.advances_fns4_and_exact_outputs
    {BlockId Validator Signature : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before after : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {receipt : DeterministicReceiptCore BlockId}
    (committed : AtomicCommit system timePolicy before input after receipt) :
    after.fns4 = input.statement.exactAfter ∧
    input.statement.exactAfter.count = input.statement.exactBefore.count + 1 ∧
    ∃ witness, ShieldedExactApexV4.Relation system.apex witness input.statement ∧
      0 < witness.outputs.length ∧
      input.statement.outputNotesRoot =
        system.apex.outputRoot.hash
          (witness.outputs.map system.apex.noteCommitment.commit) := by
  obtain ⟨witness, relation⟩ := committed.has_shared_witness
  refine ⟨committed.result.1, relation.exact_count_advances, witness, relation, ?_, ?_⟩
  · exact relation.output_exists
  · exact relation.output_root_refines_exact_creation

/-- Activation, first-frame identity, FNS4 successor, created-note root, and receipt core are one
successor.  In particular no activation-only or note-only durable result exists. -/
theorem AtomicCommit.first_frame_notes_receipt_atomic
    {BlockId Validator Signature : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before after : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {receipt : DeterministicReceiptCore BlockId}
    (committed : AtomicCommit system timePolicy before input after receipt) :
    after.consensus.activation = some (system.activationHash input.activation) ∧
    after.consensus.frame = some (system.frameHash input.frame) ∧
    after.fns4 = input.statement.exactAfter ∧
    after.createdOutputNotesRoot = some input.statement.outputNotesRoot ∧
    after.receiptCore = some receipt := by
  cases committed with
  | first _ _ _ activate =>
      have result := ExactFnspV4ConsensusEnvelope.activateAndAppend_result activate
      rw [result]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Installation outcome, ACK, and failure non-mutation -/

/-- Use the common finalized-outcome type; only `committed` carries an installed state/core pair. -/
abbrev Outcome (State Receipt Rejection Error : Type) :=
  Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome (State × Receipt) Rejection Error

/-- Project the state installed by an outcome.  Every non-commit preserves the predecessor. -/
def installedState {State Receipt Rejection Error : Type}
    (before : State) : Outcome State Receipt Rejection Error → State
  | .committed installed => installed.1
  | .deterministicallyRejected _ => before
  | .retryableOperational _ => before
  | .fatalIntegrity _ => before

/-- An installation ACK is narrower than the cursor's durable-terminal ACK: it certifies that this
shielded state/core pair was installed.  A durable deterministic rejection may advance a generic
block cursor, but it never manufactures an installation ACK. -/
def installationAck? {State Receipt Rejection Error : Type} :
    Outcome State Receipt Rejection Error → Option Receipt
  | .committed installed => some installed.2
  | .deterministicallyRejected _ => none
  | .retryableOperational _ => none
  | .fatalIntegrity _ => none

/-- The atomic transition yields both its shielded installation ACK and the generic durable
committed terminal recognized by `ConsensusTimeAck`. -/
theorem AtomicCommit.yields_terminal_ack
    {BlockId Validator Signature Rejection Error : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before after : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {receipt : DeterministicReceiptCore BlockId}
    (committed : AtomicCommit system timePolicy before input after receipt) :
    installationAck?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.committed (after, receipt) :
          Outcome (DurableState BlockId) (DeterministicReceiptCore BlockId) Rejection Error) =
        some receipt ∧
      Dregg2.Distributed.ConsensusTimeAck.durableTerminal?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.committed (after, receipt) :
          Outcome (DurableState BlockId) (DeterministicReceiptCore BlockId) Rejection Error) =
        some (.committed (after, receipt)) := by
  cases committed
  exact ⟨rfl, rfl⟩

@[simp] theorem rejected_preserves_state_and_has_no_installation_ack
    {State Receipt Rejection Error : Type}
    (before : State) (rejection : Rejection) :
    installedState before
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.deterministicallyRejected rejection :
          Outcome State Receipt Rejection Error) = before ∧
      installationAck?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.deterministicallyRejected rejection :
          Outcome State Receipt Rejection Error) = none :=
  ⟨rfl, rfl⟩

@[simp] theorem retry_preserves_state_and_has_no_ack
    {State Receipt Rejection Error : Type}
    (before : State) (error : Error) :
    installedState before
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.retryableOperational error :
          Outcome State Receipt Rejection Error) = before ∧
      installationAck?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.retryableOperational error :
          Outcome State Receipt Rejection Error) = none ∧
      Dregg2.Distributed.ConsensusTimeAck.durableTerminal?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.retryableOperational error :
          Outcome State Receipt Rejection Error) = none :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem fatal_preserves_state_and_has_no_ack
    {State Receipt Rejection Error : Type}
    (before : State) (error : Error) :
    installedState before
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.fatalIntegrity error :
          Outcome State Receipt Rejection Error) = before ∧
      installationAck?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.fatalIntegrity error :
          Outcome State Receipt Rejection Error) = none ∧
      Dregg2.Distributed.ConsensusTimeAck.durableTerminal?
        (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.fatalIntegrity error :
          Outcome State Receipt Rejection Error) = none :=
  ⟨rfl, rfl, rfl⟩

/-- A proof/frame rejection cannot construct any state installation in the first place. -/
theorem rejected_apex_cannot_commit
    {BlockId Validator Signature : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before after : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {receipt : DeterministicReceiptCore BlockId}
    (rejected : ¬ system.contract.accepts input.statement) :
    ¬ AtomicCommit system timePolicy before input after receipt := by
  intro committed
  cases committed with
  | first _ _ _ activate =>
      exact rejected
        (ExactFnspV4ConsensusEnvelope.activateAndAppend_requires_accepted activate).2.1

/-! ## 5. Validator-local noninterference -/

/-- Replacing the local envelope cannot change the signer-independent receipt core. -/
theorem receipt_core_independent_of_local_envelope
    {BlockId Validator Signature : Type}
    (system : System BlockId Validator Signature)
    (input : FinalizedInput BlockId Validator Signature)
    (replacement : ExactFnspV4ConsensusEnvelope.LocalEnvelope Validator Signature) :
    receiptCore system (input.replaceEnvelope replacement) = receiptCore system input := by
  rfl

/-- Two accepted local envelopes around the same common input install identical state and receipt
core.  Signature material is an admission witness, never consensus state. -/
theorem local_envelope_noninterference
    {BlockId Validator Signature : Type}
    {system : System BlockId Validator Signature} {timePolicy : Dregg2.Distributed.ConsensusTimeAck.TimePolicy}
    {before leftAfter rightAfter : DurableState BlockId}
    {input : FinalizedInput BlockId Validator Signature}
    {leftReceipt rightReceipt : DeterministicReceiptCore BlockId}
    (replacement : ExactFnspV4ConsensusEnvelope.LocalEnvelope Validator Signature)
    (left : AtomicCommit system timePolicy before input leftAfter leftReceipt)
    (right : AtomicCommit system timePolicy before (input.replaceEnvelope replacement)
      rightAfter rightReceipt) :
    leftAfter = rightAfter ∧ leftReceipt = rightReceipt := by
  cases left with
  | first _ _ _ leftActivate =>
      cases right with
      | first _ _ _ rightActivate =>
          change ExactFnspV4ConsensusEnvelope.ActivateAndAppend system.activationHash
            system.frameHash (FrameAccepts system input) system.authorized before.consensus
            input.activation input.frame _ at rightActivate
          have consensusEq := ExactFnspV4ConsensusEnvelope.activateAndAppend_deterministic
            leftActivate rightActivate
          cases consensusEq
          exact ⟨rfl, rfl⟩

/-- Wall clocks are absent from the receipt derivation.  Only the authenticated context time can
flow into the installed core. -/
def receiptCoreAtValidator
    {BlockId Validator Signature : Type}
    (system : System BlockId Validator Signature)
    (input : FinalizedInput BlockId Validator Signature)
    (_localClock : Int) : DeterministicReceiptCore BlockId :=
  receiptCore system input

theorem validator_clock_noninterference
    {BlockId Validator Signature : Type}
    (system : System BlockId Validator Signature)
    (input : FinalizedInput BlockId Validator Signature)
    (leftClock rightClock : Int) :
    receiptCoreAtValidator system input leftClock =
      receiptCoreAtValidator system input rightClock := by
  rfl

/-! ## 6. Executable outcome teeth -/

#guard installationAck?
    (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.committed (7, 11) : Outcome Nat Nat Nat Nat) == some 11
#guard installedState 3
    (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.committed (7, 11) : Outcome Nat Nat Nat Nat) == 7
#guard installationAck?
    (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.deterministicallyRejected 5 : Outcome Nat Nat Nat Nat) == none
#guard installedState 3
    (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.retryableOperational 9 : Outcome Nat Nat Nat Nat) == 3
#guard installationAck?
    (Dregg2.Distributed.ConsensusTimeAck.FinalizedExecutionOutcome.fatalIntegrity 9 : Outcome Nat Nat Nat Nat) == none

/-! ## 7. Axiom hygiene -/

#assert_axioms AtomicCommit.has_shared_witness
#assert_axioms AtomicCommit.advances_fns4_and_exact_outputs
#assert_axioms AtomicCommit.first_frame_notes_receipt_atomic
#assert_axioms AtomicCommit.yields_terminal_ack
#assert_axioms rejected_preserves_state_and_has_no_installation_ack
#assert_axioms retry_preserves_state_and_has_no_ack
#assert_axioms fatal_preserves_state_and_has_no_ack
#assert_axioms rejected_apex_cannot_commit
#assert_axioms receipt_core_independent_of_local_envelope
#assert_axioms local_envelope_noninterference
#assert_axioms validator_clock_noninterference

end Dregg2.Circuit.ShieldedV4Finalization
