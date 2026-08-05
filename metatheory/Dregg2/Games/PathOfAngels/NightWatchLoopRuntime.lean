/-
# NightWatchLoopRuntime — compile accepted watch events into an EventBatch plan

`NightWatchLoop.execute` is the sole source of effect-bearing semantic events.
This module projects those accepted events onto five deployment-scoped streams and
constructs the exact `EventBatch.Envelope` against supplied predecessor heads.
Authored extraction, or an explicitly activated mechanical draft, expands in order
to the watch receipt, world contribution, and zero or more fixed-order custody intents;
an unactivated draft remains local semantic history.  The generic EventBatch planner rechecks every
index, stream sequence, predecessor, event digest, and batch digest.

The boundary below does not claim a particular codec or hash.  A native adapter
must instantiate `payloadDigest` faithfully and use the deployment's authenticated
EventBatch boundary.  This file creates no finalized-turn coordinate and grants no
storage authority.
-/
import Dregg2.Games.PathOfAngels.NightWatchLoop
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchLoopRuntime

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchLoop

set_option autoImplicit false

inductive StreamKind where | commons | watch | officer | world | custody
deriving Repr, DecidableEq

structure RawStreams where
  commons : EventBatch.StreamId
  watch : EventBatch.StreamId
  officer : EventBatch.StreamId
  world : EventBatch.StreamId
  custody : EventBatch.StreamId
deriving DecidableEq

def RawStreams.list (streams : RawStreams) : List EventBatch.StreamId :=
  [streams.commons, streams.watch, streams.officer, streams.world, streams.custody]

def streamsValidB (world : EventBatch.WorldIdentity) (streams : RawStreams) : Bool :=
  streams.list.all (fun stream => stream.world = world && stream.validB) &&
  decide streams.list.Nodup

structure Streams where
  private mk ::
  policy : NightWatchLoop.Policy
  raw : RawStreams
  valid : streamsValidB policy.raw.world raw = true
deriving DecidableEq

def activateStreams? (policy : NightWatchLoop.Policy) (raw : RawStreams) : Option Streams :=
  if h : streamsValidB policy.raw.world raw = true then
    some ⟨policy, raw, h⟩ else none

def Streams.forKind (streams : Streams) : StreamKind → EventBatch.StreamId
  | .commons => streams.raw.commons
  | .watch => streams.raw.watch
  | .officer => streams.raw.officer
  | .world => streams.raw.world
  | .custody => streams.raw.custody

inductive CustodyDestination where | quarantine | archive
deriving Repr, DecidableEq

inductive WorldContributionIntent where
  | maintenance (contribution : Contribution)
  | expedition (terminal : TerminalId) (contribution : Contribution)
      (featuredArtifact : ArtifactId) (debrief : DebriefId) (operationalCost : Nat)
deriving DecidableEq

structure CustodyIntent where
  private mk ::
  terminal : TerminalId
  relic : RelicId
  destination : CustodyDestination
  marketEligible : Bool
  directTradeAllowed : Bool
  market_refused : marketEligible = false
  direct_trade_refused : directTradeAllowed = false
deriving DecidableEq

inductive IntentPayload where
  | semantic (event : NightWatchLoop.EventEnvelope)
  | worldContribution (intent : WorldContributionIntent)
  | custody (intent : CustodyIntent)
deriving DecidableEq

def semanticStream : NightWatchLoop.Event → StreamKind
  | .servingAllocated _ => .commons
  | .maintenancePerformed .. | .routeCommitted _ | .choiceResolved _
  | .extractionResolved _ => .watch
  | .briefingDelivered _ | .handoffRecorded _ _ | .injuryRecorded _
  | .recoveryServingRecorded _ | .recoveryCalibrationCompleted _
  | .nextWatchEnrolled _ | .draftSettlementActivated .. | .debriefIssued _ => .officer

def IntentPayload.streamKind : IntentPayload → StreamKind
  | .semantic event => semanticStream event.payload
  | .worldContribution _ => .world
  | .custody _ => .custody

/-- Fixed semantic custody destinations.  No caller chooses this projection. -/
def custodyIntentFor? (terminal : TerminalId) : RelicId → Option CustodyIntent
  | relic =>
      if relic = relicSilentBearing then
        some ⟨terminal, relic, .quarantine, false, false, rfl, rfl⟩
      else if relic = relicIndexFilm then
        some ⟨terminal, relic, .archive, false, false, rfl, rfl⟩
      else if relic = relicThresholdWedge then
        some ⟨terminal, relic, .quarantine, false, false, rfl, rfl⟩
      else none

/-- This order is semantic, unlike a host traversal of a set. -/
def custodyIntents (receipt : OutcomeReceipt) : List CustodyIntent :=
  [relicSilentBearing, relicIndexFilm, relicThresholdWedge].filterMap fun relic =>
    if relic ∈ receipt.carriedRelics then custodyIntentFor? receipt.terminal relic else none

def settlementIntents (event : NightWatchLoop.EventEnvelope)
    (receipt : OutcomeReceipt) : List IntentPayload :=
  .semantic event ::
  .worldContribution (.expedition receipt.terminal receipt.contribution
    receipt.featuredArtifact receipt.debrief receipt.terminalOperationalCost) ::
  (custodyIntents receipt).map IntentPayload.custody

def intentsForEvent (event : NightWatchLoop.EventEnvelope) : List IntentPayload :=
  match event.payload with
  | .maintenancePerformed _ index action =>
      let semantic := IntentPayload.semantic event
      if index + 1 = maintenanceProcedure.length && action = .verifyFirstCycle then
        [semantic, .worldContribution (.maintenance maintenanceContribution)]
      else [semantic]
  | .extractionResolved receipt =>
      match receipt.terminal with
      | .authored _ => settlementIntents event receipt
      | .mechanicalDraft _ => [.semantic event]
  | .draftSettlementActivated receipt _ _ => settlementIntents event receipt
  | _ => [.semantic event]

def intentsForEvents (events : List NightWatchLoop.EventEnvelope) : List IntentPayload :=
  events.flatMap intentsForEvent

structure DigestBoundary where
  payloadDigest : IntentPayload → Digest32
  batch : EventBatch.DigestBoundary

structure BuildState where
  nextIndex : Nat
  heads : List EventBatch.StreamHead
  payloads : List IntentPayload
  indexed : List EventBatch.IndexedEvent
  count_exact : payloads.length = indexed.length
deriving DecidableEq

inductive Error where
  | policyScope
  | coordinateWorld
  | missingInitialHead
  | invalidBatch (error : EventBatch.Error)
deriving Repr, DecidableEq

private def appendIntent (streams : Streams) (boundary : DigestBoundary)
    (build : BuildState) (payload : IntentPayload) : Except Error BuildState := do
  let stream := streams.forKind payload.streamKind
  let head ← match EventBatch.headFor? build.heads stream with
    | none => throw .missingInitialHead
    | some head => pure head
  let statement : EventSourcing.EventStatement := {
    aggregate := stream.aggregate
    version := stream.version
    sequence := head.sequence + 1
    predecessor := head.head
    payloadDigest := boundary.payloadDigest payload
  }
  let eventDigest := boundary.batch.eventDigest statement
  let indexed : EventBatch.IndexedEvent := ⟨build.nextIndex, statement, eventDigest⟩
  let successor : EventBatch.StreamHead :=
    ⟨stream, statement.sequence, eventDigest⟩
  pure {
    nextIndex := build.nextIndex + 1
    heads := EventBatch.replaceHead build.heads successor
    payloads := build.payloads ++ [payload]
    indexed := build.indexed ++ [indexed]
    count_exact := by simp [build.count_exact]
  }

private def appendIntents (streams : Streams) (boundary : DigestBoundary) :
    BuildState → List IntentPayload → Except Error BuildState
  | build, [] => .ok build
  | build, payload :: payloads => do
      let next ← appendIntent streams boundary build payload
      appendIntents streams boundary next payloads

structure PreparedBatch (before : NightWatchLoop.State) (command : NightWatchLoop.Command) where
  private mk ::
  transition : NightWatchLoop.AcceptedTransition before command
  payloads : List IntentPayload
  envelope : EventBatch.Envelope
  applied : EventBatch.AppliedBatch
  payload_count_exact : payloads.length = envelope.statement.events.length
  private activatedPolicy : NightWatchLoop.Policy
  policy_exact : before.policy = activatedPolicy
  coordinate_world_exact : envelope.statement.coordinate.world = before.policy.raw.world
  private appliedBoundary : EventBatch.DigestBoundary
  private appliedInitialHeads : List EventBatch.StreamHead
  applied_exact : EventBatch.applyBatch appliedBoundary appliedInitialHeads envelope = .ok applied

/-- Compile one already accepted semantic command into a cross-aggregate batch.
The finalized coordinate remains an input from the lower authority bridge; this
  function neither manufactures nor authenticates it. -/
def prepareBatch {before : NightWatchLoop.State} {command : NightWatchLoop.Command}
    (streams : Streams) (boundary : DigestBoundary)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (initialHeads : List EventBatch.StreamHead)
    (transition : NightWatchLoop.AcceptedTransition before command) :
    Except Error (PreparedBatch before command) :=
  if hpolicy : before.policy = streams.policy then
    if hworld : coordinate.world = streams.policy.raw.world then do
      let payloads := intentsForEvents transition.events
      let built ← appendIntents streams boundary
        ⟨0, initialHeads, [], [], rfl⟩ payloads
      let statement : EventBatch.Statement := ⟨coordinate, built.indexed⟩
      let envelope : EventBatch.Envelope :=
        ⟨statement, boundary.batch.batchDigest statement⟩
      match hbatch : EventBatch.applyBatch boundary.batch initialHeads envelope with
      | .error error => throw (.invalidBatch error)
      | .ok applied =>
          have hcount : built.payloads.length = envelope.statement.events.length := by
            simp only [envelope, statement]
            exact built.count_exact
          have hcoordinate : envelope.statement.coordinate.world = before.policy.raw.world := by
            simp only [envelope, statement]
            rw [hworld, ← hpolicy]
          pure ⟨transition, built.payloads, envelope, applied, hcount,
            streams.policy, hpolicy, hcoordinate, boundary.batch, initialHeads, hbatch⟩
    else .error .coordinateWorld
  else .error .policyScope

theorem prepared_batch_was_rechecked {before : NightWatchLoop.State}
    {command : NightWatchLoop.Command} (prepared : PreparedBatch before command) :
    EventBatch.applyBatch prepared.appliedBoundary prepared.appliedInitialHeads
      prepared.envelope = .ok prepared.applied :=
  prepared.applied_exact

theorem custody_intent_is_never_market (intent : CustodyIntent) :
    intent.marketEligible = false ∧ intent.directTradeAllowed = false := by
  exact ⟨intent.market_refused, intent.direct_trade_refused⟩

theorem prepared_batch_scope_is_exact {before : NightWatchLoop.State}
    {command : NightWatchLoop.Command} (prepared : PreparedBatch before command) :
    before.policy = prepared.activatedPolicy ∧
      prepared.envelope.statement.coordinate.world = before.policy.raw.world :=
  ⟨prepared.policy_exact, prepared.coordinate_world_exact⟩

theorem maintenance_completion_emits_exactly_one_world_intent
    (sequence : Nat) (actor : Digest32) :
    intentsForEvent ⟨sequence, .maintenancePerformed actor
      (maintenanceProcedure.length - 1) .verifyFirstCycle⟩ =
      [ .semantic ⟨sequence, .maintenancePerformed actor
          (maintenanceProcedure.length - 1) .verifyFirstCycle⟩
      , .worldContribution (.maintenance maintenanceContribution) ] := by
  simp [intentsForEvent, maintenanceProcedure]

theorem prepareBatch_refuses_world_or_pack_scope_substitution
    {before : NightWatchLoop.State} {command : NightWatchLoop.Command}
    (streams : Streams) (boundary : DigestBoundary)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (initialHeads : List EventBatch.StreamHead)
    (transition : NightWatchLoop.AcceptedTransition before command)
    (hscope : before.policy ≠ streams.policy) :
    prepareBatch streams boundary coordinate initialHeads transition = .error .policyScope := by
  simp [prepareBatch, hscope]

theorem prepareBatch_refuses_different_pack_digest
    {before : NightWatchLoop.State} {command : NightWatchLoop.Command}
    (streams : Streams) (boundary : DigestBoundary)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (initialHeads : List EventBatch.StreamHead)
    (transition : NightWatchLoop.AcceptedTransition before command)
    (hpack : before.policy.raw.content.packDigest ≠
      streams.policy.raw.content.packDigest) :
    prepareBatch streams boundary coordinate initialHeads transition = .error .policyScope := by
  apply prepareBatch_refuses_world_or_pack_scope_substitution
  exact different_pack_digest_forces_policy_inequality _ _ hpack

theorem unactivated_mechanical_draft_extraction_is_local_only
    (sequence : Nat) (receipt : OutcomeReceipt) (draft : MechanicalDraftOutcomeId)
    (hterminal : receipt.terminal = .mechanicalDraft draft) :
    intentsForEvent ⟨sequence, .extractionResolved receipt⟩ =
      [.semantic ⟨sequence, .extractionResolved receipt⟩] := by
  simp [intentsForEvent, hterminal]

theorem activated_mechanical_draft_is_the_only_draft_settlement_projection
    (sequence : Nat) (receipt : OutcomeReceipt)
    (carrier : SignedDraftActivationCarrier) (admission : DraftActivationAdmission) :
    intentsForEvent ⟨sequence, .draftSettlementActivated receipt carrier admission⟩ =
      settlementIntents
        ⟨sequence, .draftSettlementActivated receipt carrier admission⟩ receipt := by
  rfl

#assert_axioms prepared_batch_was_rechecked
#assert_axioms custody_intent_is_never_market
#assert_axioms prepared_batch_scope_is_exact
#assert_axioms maintenance_completion_emits_exactly_one_world_intent
#assert_axioms prepareBatch_refuses_world_or_pack_scope_substitution
#assert_axioms prepareBatch_refuses_different_pack_digest
#assert_axioms unactivated_mechanical_draft_extraction_is_local_only
#assert_axioms activated_mechanical_draft_is_the_only_draft_settlement_projection

end Dregg2.Games.PathOfAngels.NightWatchLoopRuntime
