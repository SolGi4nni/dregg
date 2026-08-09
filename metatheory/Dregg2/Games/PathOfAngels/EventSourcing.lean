/-
# EventSourcing — generic, replay-first PoA aggregate semantics

The canonical object is an ordered event stream.  Projections and snapshots are
derived caches.  The payload is generic: Signal runs, expeditions, archives,
attendants, and editorial aggregates may share this sequencing kernel without
sharing their event vocabulary.

This module proves structural replay laws.  It does not claim cryptographic
security for the supplied digest boundary, durable storage, or atomic database
CAS.  A deployment must instantiate `DigestBoundary` faithfully and atomically
compare/persist the returned cursor.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EventSourcing

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

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

/-- The digestable, payload-erased event statement.  Payload bytes are represented
by their exact boundary digest; sequence and predecessor remain structural. -/
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

/-- Named trust boundary.  Kernel laws are parametric in this implementation;
collision resistance and faithful serialization are deployment obligations. -/
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

inductive Error where
  | cursorAggregate
  | cursorVersion
  | wrongAggregate
  | wrongVersion
  | wrongSequence (expected actual : Nat)
  | wrongPredecessor
  | wrongPayloadDigest
  | wrongEventDigest
  | reducerRejected
  | snapshotAggregate
  | snapshotVersion
deriving DecidableEq, Repr

structure ReplayState (State : Type) where
  cursor : Cursor
  projection : State
deriving DecidableEq

abbrev Reducer (State Payload : Type) := State → Payload → Option State

structure AppliedEvent (spec : StreamSpec) (State : Type) where
  state : ReplayState State
  aggregate_exact : state.cursor.aggregate = spec.aggregate
  version_exact : state.cursor.version = spec.version

/-- Validate and reduce exactly one successor.  This is a pure CAS candidate;
atomic persistence of the returned cursor is outside the Lean value model. -/
def applyEvent {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (before : ReplayState State) (event : EventEnvelope Payload) :
    Except Error (AppliedEvent spec State) := do
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
    state := {
      cursor := {
        aggregate := spec.aggregate
        version := spec.version
        sequence := event.statement.sequence
        head := event.eventDigest
      }
      projection
    }
    aggregate_exact := rfl
    version_exact := rfl
  }

theorem applyEvent_success_cursor {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (before : ReplayState State) (after : AppliedEvent spec State)
    (event : EventEnvelope Payload)
    (_h : applyEvent spec digests reduce before event = .ok after) :
    after.state.cursor.aggregate = spec.aggregate ∧
      after.state.cursor.version = spec.version :=
  ⟨after.aggregate_exact, after.version_exact⟩

/-- ⚑ THE REDUCER IS THE SEMANTICS.  An accepted event's successor projection is
EXACTLY the supplied reducer's answer on the predecessor projection.

Without this law every theorem proved about a `Reducer` is a theorem about a
function the emitted bytes need not have called: `applyEvent` could publish any
projection at all and every `reduce_*` lemma downstream would stay green.  A wire
codec that exports a judge needs this to carry its reducer facts to its output —
see `GalleyMaintenanceDailyRuntime.judge_command_projection_is_reduce`.

Refutation to watch: give `applyEvent` a successor it did not get from `reduce`
(e.g. `projection := bonus projection`) and this goes red immediately. -/
theorem applyEvent_projection_is_reduce {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (before : ReplayState State) (event : EventEnvelope Payload)
    (after : AppliedEvent spec State)
    (accepted : applyEvent spec digests reduce before event = .ok after) :
    reduce before.projection event.payload = some after.state.projection := by
  cases hreduce : reduce before.projection event.payload with
  | none =>
      exfalso
      simp only [applyEvent, hreduce, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at accepted
      repeat' split at accepted
      all_goals simp at accepted
  | some projection =>
      simp only [applyEvent, hreduce, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at accepted
      repeat' split at accepted
      all_goals first
        | (simp at accepted
           done)
        | (simp only [Except.ok.injEq] at accepted
           subst accepted
           rfl)

def replay {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload) :
    ReplayState State → List (EventEnvelope Payload) → Except Error (ReplayState State)
  | state, [] => .ok state
  | state, event :: rest => do
      let applied ← applyEvent spec digests reduce state event
      replay spec digests reduce applied.state rest

theorem replay_success_cursor {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (start after : ReplayState State) (events : List (EventEnvelope Payload))
    (aggregate : start.cursor.aggregate = spec.aggregate)
    (version : start.cursor.version = spec.version)
    (h : replay spec digests reduce start events = .ok after) :
    after.cursor.aggregate = spec.aggregate ∧ after.cursor.version = spec.version := by
  induction events generalizing start after with
  | nil =>
      simp only [replay] at h
      rw [← Except.ok.inj h]
      exact ⟨aggregate, version⟩
  | cons event rest ih =>
      simp only [replay] at h
      cases hs : applyEvent spec digests reduce start event with
      | error error =>
          rw [hs] at h
          contradiction
      | ok applied =>
          rw [hs] at h
          exact ih applied.state after applied.aggregate_exact applied.version_exact h

/-- Rebuild is deliberately just replay from genesis, not a second semantics. -/
def rebuild {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (initial : State) (events : List (EventEnvelope Payload)) :
    Except Error (ReplayState State) :=
  replay spec digests reduce { cursor := spec.genesisCursor, projection := initial } events

def rebuildProjection {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (initial : State) (events : List (EventEnvelope Payload)) : Except Error State :=
  (rebuild spec digests reduce initial events).map ReplayState.projection

/-- A snapshot has no authority beyond its provenance.  It is safe only when
produced by replay of a named prefix; the equivalence theorem below says exactly
that and nothing stronger. -/
structure Snapshot (State : Type) where
  cursor : Cursor
  projection : State
deriving DecidableEq

def snapshotPrefix {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (initial : State) (leading : List (EventEnvelope Payload)) : Except Error (Snapshot State) := do
  let rebuilt ← rebuild spec digests reduce initial leading
  pure { cursor := rebuilt.cursor, projection := rebuilt.projection }

def resumeSnapshot {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (snapshot : Snapshot State) (suffix : List (EventEnvelope Payload)) :
    Except Error (ReplayState State) := do
  if snapshot.cursor.aggregate != spec.aggregate then throw .snapshotAggregate
  if snapshot.cursor.version != spec.version then throw .snapshotVersion
  replay spec digests reduce
    { cursor := snapshot.cursor, projection := snapshot.projection } suffix

theorem replay_append {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (start : ReplayState State) (left right : List (EventEnvelope Payload)) :
    replay spec digests reduce start (left ++ right) =
      (replay spec digests reduce start left >>= fun middle =>
        replay spec digests reduce middle right) := by
  induction left generalizing start with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.cons_append, replay]
      cases applyEvent spec digests reduce start event <;> simp [ih]

theorem replay_deterministic {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (start : ReplayState State) (events : List (EventEnvelope Payload))
    (left right : ReplayState State)
    (hl : replay spec digests reduce start events = .ok left)
    (hr : replay spec digests reduce start events = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

theorem snapshot_cache_equivalence {State Payload : Type} (spec : StreamSpec)
    (digests : DigestBoundary Payload) (reduce : Reducer State Payload)
    (initial : State) (leading suffix : List (EventEnvelope Payload)) :
    (do
      let snapshot ← snapshotPrefix spec digests reduce initial leading
      resumeSnapshot spec digests reduce snapshot suffix) =
      rebuild spec digests reduce initial (leading ++ suffix) := by
  unfold snapshotPrefix rebuild
  rw [replay_append]
  cases h : replay spec digests reduce
      { cursor := spec.genesisCursor, projection := initial } leading with
  | error error =>
      rfl
  | ok middle =>
      have valid := replay_success_cursor spec digests reduce
        { cursor := spec.genesisCursor, projection := initial } middle leading rfl rfl h
      change resumeSnapshot spec digests reduce
        { cursor := middle.cursor, projection := middle.projection } suffix =
        replay spec digests reduce middle suffix
      unfold resumeSnapshot
      simp [valid.1, valid.2]

/-! ## Executable adversarial teeth

⚑ **THE TEETH NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target. The teeth's STATEMENTS
stay here, each as an evaluation-free `check_* : Bool` definition (a `def` body elaborates
without running); the EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `EventSourcingFixtures.lean`, rooted in the
`PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale fixture
reds the guard library instead of the archive.

The hostile checks pin the EXACT refusal error, which is strictly stronger than the old
`fail_if_success`-guarded "not accepted" harness — an equality with `.error e` refutes
acceptance by construction. Named residue: none; every evaluation moved. -/

private def digestByte (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureAggregate : AggregateId :=
  { namespaceId := digestByte 1, kind := 4, key := digestByte 2 }

private def wrongAggregate : AggregateId :=
  { namespaceId := digestByte 1, kind := 5, key := digestByte 2 }

private def fixtureSpec : StreamSpec :=
  { aggregate := fixtureAggregate, version := ⟨3⟩, genesisHead := digestByte 10 }

private def fixtureDigests : DigestBoundary Nat where
  payloadDigest payload := digestByte (20 + payload)
  eventDigest statement := digestByte
    (40 + statement.sequence + statement.version.value + statement.aggregate.kind)

private def fixtureReducer : Reducer Nat Nat := fun state payload => some (state + payload)

private def fixtureEvent (sequence : Nat) (predecessor : Digest32) (payload : Nat) :
    EventEnvelope Nat :=
  let statement : EventStatement := {
    aggregate := fixtureAggregate
    version := fixtureSpec.version
    sequence
    predecessor
    payloadDigest := fixtureDigests.payloadDigest payload
  }
  { statement, payload, eventDigest := fixtureDigests.eventDigest statement }

private def eventOne : EventEnvelope Nat := fixtureEvent 1 fixtureSpec.genesisHead 7
private def eventTwo : EventEnvelope Nat := fixtureEvent 2 eventOne.eventDigest 11

/-- The dense two-event stream rebuilds to exactly 0 + 7 + 11.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_fixture_dense_rebuild : Bool :=
  decide (rebuildProjection fixtureSpec fixtureDigests fixtureReducer 0 [eventOne, eventTwo] =
    .ok 18)

/-- A stream that skips sequence 1 is refused with the exact gap error — the
exact-error equality refutes acceptance by construction.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_gap_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventTwo] =
    .error (.wrongSequence 1 2))

/-- Reordered events are refused at the first out-of-sequence statement.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_reorder_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventTwo, eventOne] =
    .error (.wrongSequence 1 2))

private def wrongAggregateEvent : EventEnvelope Nat :=
  { eventOne with statement := { eventOne.statement with aggregate := wrongAggregate } }

/-- An event carrying a foreign aggregate id is refused.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_aggregate_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [wrongAggregateEvent] =
    .error .wrongAggregate)

private def wrongVersionEvent : EventEnvelope Nat :=
  { eventOne with statement := { eventOne.statement with version := ⟨4⟩ } }

/-- An event carrying a foreign schema version is refused.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_version_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [wrongVersionEvent] =
    .error .wrongVersion)

private def wrongPredecessorEvent : EventEnvelope Nat :=
  { eventTwo with statement := { eventTwo.statement with predecessor := digestByte 99 } }

/-- A successor naming the wrong predecessor head is refused.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_predecessor_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventOne, wrongPredecessorEvent] =
    .error .wrongPredecessor)

private def forgedAggregateSnapshot : Snapshot Nat where
  cursor := { fixtureSpec.genesisCursor with aggregate := wrongAggregate }
  projection := 777

/-- A snapshot forged for a foreign aggregate is refused even with an empty suffix.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_aggregate_snapshot_empty_suffix_refused : Bool :=
  decide (resumeSnapshot fixtureSpec fixtureDigests fixtureReducer forgedAggregateSnapshot [] =
    .error .snapshotAggregate)

private def forgedVersionSnapshot : Snapshot Nat where
  cursor := { fixtureSpec.genesisCursor with version := ⟨4⟩ }
  projection := 777

/-- A snapshot forged for a foreign schema version is refused even with an empty suffix.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_version_snapshot_empty_suffix_refused : Bool :=
  decide (resumeSnapshot fixtureSpec fixtureDigests fixtureReducer forgedVersionSnapshot [] =
    .error .snapshotVersion)

theorem fixture_snapshot_is_cache_equivalent :
    (do
      let snapshot ← snapshotPrefix fixtureSpec fixtureDigests fixtureReducer 0 [eventOne]
      resumeSnapshot fixtureSpec fixtureDigests fixtureReducer snapshot [eventTwo]) =
      rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventOne, eventTwo] := by
  exact snapshot_cache_equivalence fixtureSpec fixtureDigests fixtureReducer 0 [eventOne] [eventTwo]

#assert_axioms replay_append
#assert_axioms replay_deterministic
#assert_axioms applyEvent_success_cursor
#assert_axioms applyEvent_projection_is_reduce
#assert_axioms replay_success_cursor
#assert_axioms snapshot_cache_equivalence
#assert_axioms fixture_snapshot_is_cache_equivalent

-- The eight adversarial pins (`#assert_compiled` + `native_decide`) live in
-- `EventSourcingFixtures.lean`, rooted in `PathOfAngelsGuards` — see the teeth header above.

end Dregg2.Games.PathOfAngels.EventSourcing
