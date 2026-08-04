/-
# FinalizedRunEventAggregate — the second durable PoA aggregate

Signal finality already demonstrates the first special-purpose durable aggregate:
one finalized Dregg turn is judged by native Lean and its exact input/output and
Canon successor are welded into the generic commit transaction.  This module
extracts the smallest reusable *second aggregate* semantics from that path.

The canonical source is a dense event stream of exact judge input/output
bytes plus finalized-turn coordinates.  Every projection is rebuilt from the
same re-judged `JudgedRun`:

* Canon owns the world successor and replay key;
* Field Archive receives `ArchiveEntry.ofJudged`;
* the personal locker receives the same origin, scoped to the receipt player;
* Attendant receives a non-spendable `ReceiptIdentity` notice (never a forged
  `Credit`; its separate canonical-settlement capability is still required);
* Editorial receives an inbox notice only (never a curator capability or an
  automatic alpha promotion).

`FinalizedTurnCoordinate.turnHash` and `.receiptHash` are storage coordinates.
Lean checks the federation/signer/actor root it can reconstruct from the native
judge input.  The generic durable-store weld must compare the remaining fields
to the actual finalized `CommitRecord`, exactly as `poa_signal_state.rs` does
today.  `DigestBoundary` and atomic CAS remain named deployment
boundaries; this module does not relabel either as a proof.
-/
import Dregg2.Games.PathOfAngels.NetworkJudge
import Dregg2.Games.PathOfAngels.FieldArchive
import Dregg2.Games.PathOfAngels.AttendantKernel
import Dregg2.Games.PathOfAngels.EditorialRegistry
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire

set_option autoImplicit false

/-! ## Minimal dense append kernel

This isolated module carries the smallest executable stream kernel needed for
the second aggregate.  The shared generic `EventSourcing` module is being
developed concurrently; keeping this kernel local lets the end-to-end PoA seam
compile without taking ownership of that work.  The eventual cutover is a
type-for-type replacement, not a semantic redesign. -/

structure AggregateId where
  namespaceId : Digest32
  kind : Nat
  key : Digest32
deriving DecidableEq

structure SchemaVersion where
  value : Nat
deriving DecidableEq, Repr

structure StreamSpec where
  aggregate : AggregateId
  version : SchemaVersion
  genesisHead : Digest32
deriving DecidableEq

structure EventStatement where
  aggregate : AggregateId
  version : SchemaVersion
  sequence : Nat
  predecessor : Digest32
  payloadDigest : Digest32
deriving DecidableEq

structure EventEnvelope (Payload : Type) where
  statement : EventStatement
  payload : Payload
  eventDigest : Digest32

/-- Named deployment trust boundary.  Lean proves the sequencing rules
parametrically; the durable adapter must supply faithful codecs and hashes. -/
structure DigestBoundary (Payload : Type) where
  payloadDigest : Payload → Digest32
  eventDigest : EventStatement → Digest32

structure Cursor where
  aggregate : AggregateId
  version : SchemaVersion
  sequence : Nat
  head : Digest32
deriving DecidableEq

def StreamSpec.genesisCursor (spec : StreamSpec) : Cursor where
  aggregate := spec.aggregate
  version := spec.version
  sequence := 0
  head := spec.genesisHead

inductive StreamError where
  | cursorAggregate
  | cursorVersion
  | wrongAggregate
  | wrongVersion
  | wrongSequence (expected actual : Nat)
  | wrongPredecessor
  | wrongPayloadDigest
  | wrongEventDigest
  | reducerRejected
deriving DecidableEq, Repr

structure ReplayState (State : Type) where
  cursor : Cursor
  projection : State
deriving DecidableEq

abbrev Reducer (State Payload : Type) := State → Payload → Option State

/-- Validate and reduce one exact dense successor.  The returned cursor is only
a CAS candidate; atomic persistence beside the finalized turn is an adapter
obligation. -/
def applyEvent {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (before : ReplayState State) (event : EventEnvelope Payload) :
    Except StreamError (ReplayState State) := do
  if before.cursor.aggregate != spec.aggregate then throw .cursorAggregate
  if before.cursor.version != spec.version then throw .cursorVersion
  if event.statement.aggregate != spec.aggregate then throw .wrongAggregate
  if event.statement.version != spec.version then throw .wrongVersion
  let expected := before.cursor.sequence + 1
  if event.statement.sequence != expected then
    throw (.wrongSequence expected event.statement.sequence)
  if event.statement.predecessor != before.cursor.head then throw .wrongPredecessor
  if event.statement.payloadDigest != digests.payloadDigest event.payload then
    throw .wrongPayloadDigest
  if event.eventDigest != digests.eventDigest event.statement then throw .wrongEventDigest
  let projection ← match reduce before.projection event.payload with
    | none => throw .reducerRejected
    | some projection => pure projection
  pure {
    cursor := {
      aggregate := spec.aggregate
      version := spec.version
      sequence := event.statement.sequence
      head := event.eventDigest
    }
    projection
  }

def replay {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload) :
    ReplayState State → List (EventEnvelope Payload) → Except StreamError (ReplayState State)
  | state, [] => .ok state
  | state, event :: rest => do
      let applied ← applyEvent spec digests reduce state event
      replay spec digests reduce applied rest

def rebuild {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (initial : State) (events : List (EventEnvelope Payload)) :
    Except StreamError (ReplayState State) :=
  replay spec digests reduce { cursor := spec.genesisCursor, projection := initial } events

def rebuildProjection {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (initial : State) (events : List (EventEnvelope Payload)) : Except StreamError State :=
  (rebuild spec digests reduce initial events).map ReplayState.projection

theorem replay_deterministic {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (start : ReplayState State) (events : List (EventEnvelope Payload))
    (left right : ReplayState State)
    (hl : replay spec digests reduce start events = .ok left)
    (hr : replay spec digests reduce start events = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

/-! ## Exact finalized carrier and durable payload -/

/-- Coordinates supplied by the finalized-turn adapter and welded to the
generic commit row.  `eventIndex = 0` is the current exact Signal carrier shape:
one reserved event and no piggyback effects. -/
structure FinalizedTurnCoordinate where
  federationId : Digest32
  commitOrdinal : Nat
  turnHash : Digest32
  receiptHash : Digest32
  eventIndex : Nat
  actorRoot : Digest32
  signer : Digest32
deriving DecidableEq

/-- Durable, codec-ready event payload.  No semantic state or projection is
trusted from storage: reopening runs the native Lean judge over these exact
bytes again. -/
structure Payload where
  finalized : FinalizedTurnCoordinate
  judgeInput : String
  judgeOutput : String
deriving DecidableEq

/-- Checked in-memory view.  Its private constructor prevents a projection from
substituting a different settlement after `checkPayload?` has accepted the exact
native judge output. -/
structure CheckedPayload where
  private mk ::
  raw : Payload
  input : SemanticInput
  settlement : NetworkJudge.Settlement
  output : SignalOutputWire
  outputExact : output.toJson = raw.judgeOutput
  federationExact : raw.finalized.federationId = settlement.carrier.federationId
  actorRootExact : raw.finalized.actorRoot = settlement.carrier.actorRoot
  signerExact : raw.finalized.signer = settlement.carrier.playerKey
  eventIndexExact : raw.finalized.eventIndex = 0

/-- Decode and re-run the actual Signal judge.  Exact byte equality—not merely a
semantic output decode—binds the durable event to Lean's canonical result. -/
def checkPayload? (raw : Payload) : Option CheckedPayload := do
  let wire ← decodeSignalInput raw.judgeInput
  let input ← wire.toSemantic?
  let settlement ← NetworkJudge.settle input
  let output ← settlement.toWire?
  if houtput : output.toJson = raw.judgeOutput then
    if hfederation : raw.finalized.federationId = settlement.carrier.federationId then
      if hroot : raw.finalized.actorRoot = settlement.carrier.actorRoot then
        if hsigner : raw.finalized.signer = settlement.carrier.playerKey then
          if hindex : raw.finalized.eventIndex = 0 then
            some ⟨raw, input, settlement, output, houtput, hfederation,
              hroot, hsigner, hindex⟩
          else none
        else none
      else none
    else none
  else none

/-! ## Receipt-derived read models -/

/-- Personal display placement is a projection, not custody.  The exact Archive
origin and receipt player are retained; moving this card in a UI cannot transfer
or mint the underlying artifact. -/
structure LockerEntry where
  owner : Digest32
  origin : FieldArchive.ArchiveEntry
deriving DecidableEq

def LockerEntry.ofJudged (run : JudgedRun) : LockerEntry where
  owner := run.receipt.playerKey
  origin := FieldArchive.ArchiveEntry.ofJudged run

structure LockerState where
  entries : Finset LockerEntry
deriving DecidableEq

def LockerState.empty : LockerState := ⟨∅⟩

def LockerState.acquire (run : JudgedRun) (state : LockerState) : LockerState where
  entries := insert (LockerEntry.ofJudged run) state.entries

/-- This is deliberately weaker than `AttendantKernel.Credit`: it is a durable
notification that an exact settled receipt exists, but supplies neither the
Attendant canonical-settlement capability nor owner-command authority. -/
structure AttendantCreditNotice where
  owner : Digest32
  receipt : Attendant.ReceiptIdentity
deriving DecidableEq

def AttendantCreditNotice.ofJudged (run : JudgedRun) : AttendantCreditNotice where
  owner := run.receipt.playerKey
  receipt := Attendant.receiptIdentity run.receipt

/-- Likewise, an inbox item is not an `EditorialRegistry.CuratorCapability` and
does not call `prepareStep`.  It only makes the exact beta origin available for
later human editorial selection. -/
structure EditorialInboxEntry where
  origin : FieldArchive.ArchiveEntry
deriving DecidableEq

def EditorialInboxEntry.ofJudged (run : JudgedRun) : EditorialInboxEntry :=
  ⟨FieldArchive.ArchiveEntry.ofJudged run⟩

/-- All read models rebuilt from the event stream.  Canon remains in its exact
bounded wire representation so stream admission has decidable byte-level state
identity; proof fields inside semantic `CanonState` are deliberately not treated
as persistence identity.  World is not stored twice. -/
structure Projection where
  canon : CanonStateWire
  archive : FieldArchive.ArchiveState
  locker : LockerState
  attendantNotices : Finset AttendantCreditNotice
  editorialInbox : Finset EditorialInboxEntry
  lastFinalized : Option FinalizedTurnCoordinate
deriving DecidableEq

def Projection.initial (canon : CanonState) : Projection where
  canon := CanonStateWire.ofSemantic canon
  archive := FieldArchive.ArchiveState.empty
  locker := LockerState.empty
  attendantNotices := ∅
  editorialInbox := ∅
  lastFinalized := none

def Projection.world? (projection : Projection) : Option WorldState :=
  projection.canon.world.toSemantic?

/-- One reducer, one judged run, all projections.  The event's pre-Canon must be
the current projection and recomputing `applyGameEffect` must yield the exact
successor retained by the native Signal settlement. -/
def reduce : Reducer Projection Payload := fun before raw =>
  match checkPayload? raw with
  | none => none
  | some checked =>
      if _hbefore : CanonStateWire.ofSemantic checked.settlement.beforeCanon = before.canon then
        let run := checked.settlement.judgedRun
        some {
          canon := checked.output.successorCanon
          archive := FieldArchive.acquire run before.archive
          locker := before.locker.acquire run
          attendantNotices := insert (AttendantCreditNotice.ofJudged run) before.attendantNotices
          editorialInbox := insert (EditorialInboxEntry.ofJudged run) before.editorialInbox
          lastFinalized := some raw.finalized
        }
      else none

theorem reduce_projects_one_exact_judged_run {before after : Projection} {raw : Payload}
    (h : reduce before raw = some after) :
    ∃ checked : CheckedPayload,
      checkPayload? raw = some checked ∧
      CanonStateWire.ofSemantic checked.settlement.beforeCanon = before.canon ∧
      after.canon = checked.output.successorCanon ∧
      FieldArchive.ArchiveEntry.ofJudged checked.settlement.judgedRun ∈
        after.archive.entries ∧
      LockerEntry.ofJudged checked.settlement.judgedRun ∈ after.locker.entries ∧
      AttendantCreditNotice.ofJudged checked.settlement.judgedRun ∈
        after.attendantNotices ∧
      EditorialInboxEntry.ofJudged checked.settlement.judgedRun ∈
        after.editorialInbox := by
  unfold reduce at h
  cases hc : checkPayload? raw with
  | none => simp [hc] at h
  | some checked =>
      simp only [hc] at h
      split at h
      · rename_i hbefore
        injection h with heq
        subst after
        exact ⟨checked, rfl, hbefore, rfl,
          by simp [FieldArchive.acquire], by simp [LockerState.acquire],
          by simp, by simp⟩
      · simp at h

theorem reduce_world_is_native_judge_successor {before after : Projection} {raw : Payload}
    (h : reduce before raw = some after) :
    ∃ checked : CheckedPayload,
      checkPayload? raw = some checked ∧
      after.world? = checked.output.successorCanon.world.toSemantic? := by
  obtain ⟨checked, checkedRaw, _, canonExact, _⟩ := reduce_projects_one_exact_judged_run h
  exact ⟨checked, checkedRaw, by simp [Projection.world?, canonExact]⟩

/-! ## Stream construction -/

/-- The aggregate identity is deployment/session scoped.  Kind `2` is the
candidate second durable PoA aggregate; it is not a display name. -/
def aggregateId (canon : CanonState) : AggregateId where
  namespaceId := canon.federationId
  kind := 2
  key := canon.contentSession

def streamSpec (canon : CanonState) (genesisHead : Digest32) : StreamSpec where
  aggregate := aggregateId canon
  version := ⟨1⟩
  genesisHead

/-- Deterministically construct the next semantic event envelope.  This is not
a durable append or finality claim; `applyEvent` rechecks it, and
the store must CAS the exact predecessor head atomically with the commit row. -/
def nextEnvelope (spec : StreamSpec)
    (digests : DigestBoundary Payload)
    (cursor : Cursor) (payload : Payload) :
    EventEnvelope Payload :=
  let statement : EventStatement := {
    aggregate := spec.aggregate
    version := spec.version
    sequence := cursor.sequence + 1
    predecessor := cursor.head
    payloadDigest := digests.payloadDigest payload
  }
  { statement, payload, eventDigest := digests.eventDigest statement }

/-! ## Executable fixture and hostile paths -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureCoordinate : FinalizedTurnCoordinate where
  federationId := fixtureCarrier.federationId
  commitOrdinal := 7
  turnHash := digestByte 201
  receiptHash := digestByte 202
  eventIndex := 0
  actorRoot := fixtureCarrier.actorRoot
  signer := fixtureCarrier.playerKey

private def fixturePayload : Payload where
  finalized := fixtureCoordinate
  judgeInput := fixtureInputBytes
  judgeOutput := fixtureOutputBytes

private def fixtureDigests : DigestBoundary Payload where
  payloadDigest payload := digestByte
    (20 + payload.finalized.commitOrdinal + payload.judgeInput.length + payload.judgeOutput.length)
  eventDigest statement := digestByte
    (40 + statement.sequence + statement.version.value + statement.aggregate.kind)

private def fixtureSpec : StreamSpec :=
  streamSpec fixtureCanon (digestByte 10)

private def fixtureEventOne : EventEnvelope Payload :=
  nextEnvelope fixtureSpec fixtureDigests fixtureSpec.genesisCursor fixturePayload

private def fixtureProjection? : Option Projection :=
  match rebuildProjection fixtureSpec fixtureDigests reduce
      (Projection.initial fixtureCanon) [fixtureEventOne] with
  | .ok projection => some projection
  | .error _ => none

theorem fixture_native_judge_event_populates_every_projection :
    (do
      let checked ← checkPayload? fixturePayload
      let projection ← fixtureProjection?
      let run := checked.settlement.judgedRun
      some (
        decide (projection.world? = some checked.settlement.successorWorld) &&
        decide (FieldArchive.ArchiveEntry.ofJudged run ∈ projection.archive.entries) &&
        decide (LockerEntry.ofJudged run ∈ projection.locker.entries) &&
        decide (AttendantCreditNotice.ofJudged run ∈ projection.attendantNotices) &&
        decide (EditorialInboxEntry.ofJudged run ∈ projection.editorialInbox) &&
        decide (ArtifactRefWire.ofSemantic run.receipt.mission.artifact ∈
          projection.canon.known) &&
        decide (projection.lastFinalized = some fixtureCoordinate))) = some true := by
  native_decide

def wrongOutputPayload : Payload := { fixturePayload with judgeOutput := "{}" }

theorem hostile_non_lean_output_refused : checkPayload? wrongOutputPayload = none := by
  native_decide

def wrongSignerPayload : Payload := {
  fixturePayload with finalized := { fixtureCoordinate with signer := digestByte 250 } }

theorem hostile_finalized_signer_substitution_refused :
    checkPayload? wrongSignerPayload = none := by native_decide

def wrongEventIndexPayload : Payload := {
  fixturePayload with finalized := { fixtureCoordinate with eventIndex := 1 } }

/-- The initial carrier contract is one reserved game command per finalized
turn.  A future multi-event carrier must version this rule rather than silently
reusing the v1 aggregate. -/
theorem hostile_unversioned_second_carrier_event_refused :
    checkPayload? wrongEventIndexPayload = none := by native_decide

theorem hostile_wrong_stream_predecessor_refused :
    let badStatement := {
      fixtureEventOne.statement with predecessor := digestByte 99 }
    let bad : EventEnvelope Payload := {
      fixtureEventOne with
      statement := badStatement
      eventDigest := fixtureDigests.eventDigest badStatement
    }
    rebuild fixtureSpec fixtureDigests reduce (Projection.initial fixtureCanon) [bad] =
      .error .wrongPredecessor := by
  native_decide

theorem hostile_wrong_payload_digest_refused :
    let badStatement := {
      fixtureEventOne.statement with payloadDigest := digestByte 77 }
    let bad : EventEnvelope Payload := {
      fixtureEventOne with
      statement := badStatement
      eventDigest := fixtureDigests.eventDigest badStatement
    }
    rebuild fixtureSpec fixtureDigests reduce (Projection.initial fixtureCanon) [bad] =
      .error .wrongPayloadDigest := by
  native_decide

private def fixtureReplayEvent : EventEnvelope Payload :=
  nextEnvelope fixtureSpec fixtureDigests {
    aggregate := fixtureSpec.aggregate
    version := fixtureSpec.version
    sequence := 1
    head := fixtureEventOne.eventDigest
  } fixturePayload

/-- A fresh stream sequence cannot launder an already consumed judged receipt:
the projection reducer re-runs Canon's receipt-key/counter admission. -/
theorem hostile_same_finalized_run_at_fresh_sequence_refused :
    rebuild fixtureSpec fixtureDigests reduce
      (Projection.initial fixtureCanon) [fixtureEventOne, fixtureReplayEvent] =
        .error .reducerRejected := by
  native_decide

#assert_axioms reduce_projects_one_exact_judged_run
#assert_axioms reduce_world_is_native_judge_successor
#assert_compiled fixture_native_judge_event_populates_every_projection
#assert_compiled hostile_non_lean_output_refused
#assert_compiled hostile_finalized_signer_substitution_refused
#assert_compiled hostile_unversioned_second_carrier_event_refused
#assert_compiled hostile_wrong_stream_predecessor_refused
#assert_compiled hostile_wrong_payload_digest_refused
#assert_compiled hostile_same_finalized_run_at_fresh_sequence_refused

end Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
