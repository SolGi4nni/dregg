/-
# EventBatch — one finalized turn, many replayable PoA aggregates

`EventSourcing` gives every aggregate an exact local history.  A local history
is not, by itself, an atomic world transaction: one finalized game turn may
advance Canon, a daily, an attendant, custody, and a market projection together.

This module supplies the missing Lean-authored transaction statement.  One
batch binds an exact PoA deployment, finalized Dregg carrier, actor, ordered
event indices, every per-stream predecessor/successor, and one batch digest.
The fold below is the semantic planning phase for a durable all-or-none append.
Rust may persist the returned plan, but it may not select another ordering or
invent another stream successor.

The digest functions remain named deployment boundaries.  This file proves
structural replay properties; it does not claim collision resistance, durable
atomicity, or that a host supplied the real finalized `CommitRecord`.
-/
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EventBatch

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

/-! ## One deployment and one finalized carrier -/

/-- Identity of the PoA world whose aggregates may participate in a batch.
This is the common intersection already carried by `CanonState`, game receipts,
attendants, and Galley provisioning. -/
structure WorldIdentity where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
deriving DecidableEq

/-- Exact finalized carrier shared by every event in one batch.  `blockId`,
`turnHash`, `receiptHash`, and `commitOrdinal` must be welded to the generic
`CommitRecord`; `actorRoot` and `signer` must be welded to the native judge. -/
structure FinalizedTurnCoordinate where
  world : WorldIdentity
  commitOrdinal : Nat
  blockId : Digest32
  turnHash : Digest32
  receiptHash : Digest32
  actorRoot : Digest32
  signer : Digest32
deriving DecidableEq

/-- A stream is an aggregate together with the schema version under which its
event bytes are interpreted.  Schema version is part of stream identity. -/
structure StreamId where
  aggregate : AggregateId
  version : SchemaVersion
deriving DecidableEq

def streamOfStatement (statement : EventStatement) : StreamId where
  aggregate := statement.aggregate
  version := statement.version

/-- Authoritative pre/post cursor material for one stream.  `head` is the
semantic event digest, not a host's storage-frame digest. -/
structure StreamHead where
  stream : StreamId
  sequence : Nat
  head : Digest32
deriving DecidableEq

def streamIds (heads : List StreamHead) : List StreamId :=
  heads.map StreamHead.stream

def headFor? : List StreamHead → StreamId → Option StreamHead
  | [], _ => none
  | head :: heads, stream =>
      if head.stream = stream then some head else headFor? heads stream

def replaceHead (heads : List StreamHead) (successor : StreamHead) : List StreamHead :=
  heads.map fun head => if head.stream = successor.stream then successor else head

/-! ## Ordered batch statement -/

/-- One payload-erased, fully ordered event.  Payload bytes are committed by
`statement.payloadDigest`; `eventDigest` is the exact successor head. -/
structure IndexedEvent where
  eventIndex : Nat
  statement : EventStatement
  eventDigest : Digest32
deriving DecidableEq

/-- The digest preimage for the complete cross-aggregate transaction. -/
structure Statement where
  coordinate : FinalizedTurnCoordinate
  events : List IndexedEvent
deriving DecidableEq

structure Envelope where
  statement : Statement
  batchDigest : Digest32
deriving DecidableEq

/-- Cryptographic and canonical-codec boundary selected at deployment. -/
structure DigestBoundary where
  eventDigest : EventStatement → Digest32
  batchDigest : Statement → Digest32

abbrev MAX_BATCH_EVENTS : Nat := 4096
abbrev WIRE_U32_MODULUS : Nat := 2 ^ 32
abbrev WIRE_U64_MODULUS : Nat := 2 ^ 64

inductive Error where
  | emptyBatch
  | batchTooLarge
  | duplicateInitialStream
  | commitOrdinalOutOfRange
  | eventIndexOutOfRange
  | sequenceOutOfRange
  | wrongBatchDigest
  | wrongEventIndex
  | wrongFederationNamespace
  | unknownStream
  | wrongSequence
  | wrongPredecessor
  | wrongEventDigest
deriving DecidableEq, Repr

/-- The only successor state exposed by successful batch admission. -/
structure AppliedBatch where
  coordinate : FinalizedTurnCoordinate
  batchDigest : Digest32
  events : List IndexedEvent
  successorHeads : List StreamHead
deriving DecidableEq

private def applyOne (boundary : DigestBoundary)
    (coordinate : FinalizedTurnCoordinate) (expectedIndex : Nat)
    (heads : List StreamHead) (event : IndexedEvent) : Except Error (List StreamHead) := do
  if event.eventIndex != expectedIndex then throw .wrongEventIndex
  if WIRE_U32_MODULUS ≤ event.eventIndex then throw .eventIndexOutOfRange
  if WIRE_U64_MODULUS ≤ event.statement.sequence then throw .sequenceOutOfRange
  if event.statement.aggregate.namespaceId != coordinate.world.federationId then
    throw .wrongFederationNamespace
  let stream := streamOfStatement event.statement
  let before ← match headFor? heads stream with
    | none => throw .unknownStream
    | some before => pure before
  if event.statement.sequence != before.sequence + 1 then throw .wrongSequence
  if event.statement.predecessor != before.head then throw .wrongPredecessor
  if event.eventDigest != boundary.eventDigest event.statement then throw .wrongEventDigest
  pure (replaceHead heads {
    stream
    sequence := event.statement.sequence
    head := event.eventDigest
  })

/-- Ordered planning fold.  Repeating a stream is permitted only by explicitly
placing another indexed event whose sequence and predecessor continue the
successor produced by its earlier event. -/
def applyEvents (boundary : DigestBoundary) (coordinate : FinalizedTurnCoordinate) :
    Nat → List StreamHead → List IndexedEvent → Except Error (List StreamHead)
  | _, heads, [] => .ok heads
  | expectedIndex, heads, event :: events => do
      let next ← applyOne boundary coordinate expectedIndex heads event
      applyEvents boundary coordinate (expectedIndex + 1) next events

/-- Admit one all-or-none semantic batch against exact initial stream heads. -/
def applyBatch (boundary : DigestBoundary) (initialHeads : List StreamHead)
    (envelope : Envelope) : Except Error AppliedBatch := do
  if envelope.statement.events.isEmpty then throw .emptyBatch
  if MAX_BATCH_EVENTS < envelope.statement.events.length then throw .batchTooLarge
  if !(streamIds initialHeads).Nodup then throw .duplicateInitialStream
  if WIRE_U64_MODULUS ≤ envelope.statement.coordinate.commitOrdinal then
    throw .commitOrdinalOutOfRange
  if envelope.batchDigest != boundary.batchDigest envelope.statement then
    throw .wrongBatchDigest
  let successorHeads ← applyEvents boundary envelope.statement.coordinate 0
    initialHeads envelope.statement.events
  pure {
    coordinate := envelope.statement.coordinate
    batchDigest := envelope.batchDigest
    events := envelope.statement.events
    successorHeads
  }

/-- Planning is a function, not an alternate-choice relation. -/
theorem applyBatch_deterministic (boundary : DigestBoundary)
    (initialHeads : List StreamHead) (envelope : Envelope) (left right : AppliedBatch)
    (hl : applyBatch boundary initialHeads envelope = .ok left)
    (hr : applyBatch boundary initialHeads envelope = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

/-! ## Executable cross-aggregate and hostile fixtures -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureWorld : WorldIdentity where
  federationId := digestByte 1
  contentRoot := digestByte 2
  activationDigest := digestByte 3
  contentSession := digestByte 4
  contentEpoch := ⟨5⟩

private def fixtureCoordinate : FinalizedTurnCoordinate where
  world := fixtureWorld
  commitOrdinal := 7
  blockId := digestByte 8
  turnHash := digestByte 9
  receiptHash := digestByte 10
  actorRoot := digestByte 11
  signer := digestByte 12

private def stream (kind : Nat) (key : Nat) : StreamId where
  aggregate := { namespaceId := fixtureWorld.federationId, kind, key := digestByte key }
  version := ⟨1⟩

private def initialHead (kind key genesis : Nat) : StreamHead where
  stream := stream kind key
  sequence := 0
  head := digestByte genesis

private def fixtureBoundary : DigestBoundary where
  eventDigest statement := digestByte
    (100 + statement.aggregate.kind + statement.sequence)
  batchDigest statement := digestByte
    (200 + statement.coordinate.commitOrdinal + statement.events.length)

private def event (eventIndex : Nat) (stream : StreamId) (sequence predecessor payload : Nat) :
    IndexedEvent :=
  let statement : EventStatement := {
    aggregate := stream.aggregate
    version := stream.version
    sequence
    predecessor := digestByte predecessor
    payloadDigest := digestByte payload
  }
  { eventIndex, statement, eventDigest := fixtureBoundary.eventDigest statement }

private def canonHead := initialHead 2 20 30
private def attendantHead := initialHead 10 21 31
private def firstCanon := event 0 canonHead.stream 1 30 40
private def attendant := event 1 attendantHead.stream 1 31 41
private def secondCanon := event 2 canonHead.stream 2 103 42

private def fixtureStatement : Statement where
  coordinate := fixtureCoordinate
  events := [firstCanon, attendant, secondCanon]

private def fixtureEnvelope : Envelope where
  statement := fixtureStatement
  batchDigest := fixtureBoundary.batchDigest fixtureStatement

theorem fixture_cross_aggregate_batch_accepts :
    (applyBatch fixtureBoundary [canonHead, attendantHead] fixtureEnvelope).isOk = true := by
  native_decide

theorem fixture_repeated_stream_is_explicitly_chained :
    (applyBatch fixtureBoundary [canonHead, attendantHead] fixtureEnvelope).map
      (fun applied =>
        (headFor? applied.successorHeads canonHead.stream).map StreamHead.sequence) =
      .ok (some 2) := by
  native_decide

private def fixtureSuccessorHeads : List StreamHead :=
  [ { stream := canonHead.stream, sequence := 2, head := secondCanon.eventDigest }
  , { stream := attendantHead.stream, sequence := 1, head := attendant.eventDigest } ]

theorem fixture_cross_aggregate_successors_are_exact :
    applyBatch fixtureBoundary [canonHead, attendantHead] fixtureEnvelope =
      .ok {
        coordinate := fixtureCoordinate
        batchDigest := fixtureEnvelope.batchDigest
        events := fixtureStatement.events
        successorHeads := fixtureSuccessorHeads
      } := by
  native_decide

theorem hostile_semantic_reapplication_refused :
    applyBatch fixtureBoundary fixtureSuccessorHeads fixtureEnvelope =
      .error .wrongSequence := by
  native_decide

theorem hostile_event_gap_refused :
    let bad := { secondCanon with statement := { secondCanon.statement with sequence := 3 } }
    let statement := { fixtureStatement with events := [firstCanon, attendant, bad] }
    applyBatch fixtureBoundary [canonHead, attendantHead]
      { statement, batchDigest := fixtureBoundary.batchDigest statement } =
        .error .wrongSequence := by
  native_decide

theorem hostile_cross_stream_predecessor_refused :
    let bad := { attendant with statement :=
      { attendant.statement with predecessor := firstCanon.eventDigest } }
    let statement := { fixtureStatement with events := [firstCanon, bad] }
    applyBatch fixtureBoundary [canonHead, attendantHead]
      { statement, batchDigest := fixtureBoundary.batchDigest statement } =
        .error .wrongPredecessor := by
  native_decide

theorem hostile_index_reorder_refused :
    let statement := { fixtureStatement with events := [attendant, firstCanon] }
    applyBatch fixtureBoundary [canonHead, attendantHead]
      { statement, batchDigest := fixtureBoundary.batchDigest statement } =
        .error .wrongEventIndex := by
  native_decide

theorem hostile_batch_digest_refused :
    applyBatch fixtureBoundary [canonHead, attendantHead]
      { fixtureEnvelope with batchDigest := digestByte 255 } = .error .wrongBatchDigest := by
  native_decide

theorem hostile_duplicate_initial_stream_refused :
    applyBatch fixtureBoundary [canonHead, canonHead, attendantHead] fixtureEnvelope =
      .error .duplicateInitialStream := by
  native_decide

theorem hostile_foreign_federation_refused :
    let foreignAggregate := { firstCanon.statement.aggregate with namespaceId := digestByte 99 }
    let badStatement := { firstCanon.statement with aggregate := foreignAggregate }
    let bad : IndexedEvent :=
      ⟨firstCanon.eventIndex, badStatement, fixtureBoundary.eventDigest badStatement⟩
    let statement := { fixtureStatement with events := [bad] }
    applyBatch fixtureBoundary [canonHead, attendantHead]
      { statement, batchDigest := fixtureBoundary.batchDigest statement } =
        .error .wrongFederationNamespace := by
  native_decide

#assert_axioms applyBatch_deterministic
#assert_compiled fixture_cross_aggregate_batch_accepts
#assert_compiled fixture_repeated_stream_is_explicitly_chained
#assert_compiled fixture_cross_aggregate_successors_are_exact
#assert_compiled hostile_semantic_reapplication_refused
#assert_compiled hostile_event_gap_refused
#assert_compiled hostile_cross_stream_predecessor_refused
#assert_compiled hostile_index_reorder_refused
#assert_compiled hostile_batch_digest_refused
#assert_compiled hostile_duplicate_initial_stream_refused
#assert_compiled hostile_foreign_federation_refused

end Dregg2.Games.PathOfAngels.EventBatch
