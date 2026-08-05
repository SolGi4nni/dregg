/-
# ShipExpeditionSeason — derived expedition receipts, never a second authority

The canonical expedition semantics and salvage taxonomy live in
`CrewFieldMissionRuntime`.  This module is a replayable season index over receipts
which have already passed that runtime and an atomic `EventBatch`.  It does not
advance a world state, mint salvage, own custody, mutate crew wounds, or settle a
barter.  Those successors belong to their specialist streams.

The season retains the useful game-facing surface: authored shift plans, completed
run summaries, career counts, ordinary-part notices, non-market relic custody
notices, beta-candidate notices, recovery displays, and market activity.  Every one
of those values is a derived projection which may be discarded and rebuilt.

`CrewFieldMissionRuntime.PartId` is the only exchangeable salvage identifier here.
`ContentContract.RelicId` can appear only in a non-market custody notice.  There is
no function from a relic notice to a Bazaar receipt.
-/
import Dregg2.Games.PathOfAngels.BazaarGame
import Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ShipExpeditionSeason

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

abbrev MAX_SHIFTS : Nat := CrewFieldMissionRuntime.MAX_RUNS
abbrev MAX_SEASON_EVENTS : Nat := 16384
abbrev MAX_FANOUT_EVENTS : Nat := 16
abbrev EXPEDITION_SEASON_STREAM_KIND : Nat := 12
abbrev RUNTIME_RECEIPT_DIGEST_DOMAIN : Nat := 0x504f415a

structure SeasonId where value : Nat
deriving Repr, DecidableEq

structure ShiftId where value : Nat
deriving Repr, DecidableEq

structure SeasonIdentity where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  season : SeasonId
  activationDigest : Digest32
deriving DecidableEq

structure ShiftPlan where
  shift : ShiftId
  officer : Seat
  selectedCrew : List Seat
deriving DecidableEq

structure RawConfig where
  schemaVersion : Nat
  identity : SeasonIdentity
  runtimeStream : EventBatch.StreamId
deriving DecidableEq

structure Config where
  private mk ::
  raw : RawConfig

def activate (raw : RawConfig) : Option Config :=
  if raw.schemaVersion = 0 then none
  else if !raw.runtimeStream.validB then none
  else if raw.runtimeStream.world.federationId != raw.identity.federationId then none
  else if raw.runtimeStream.world.activationDigest != raw.identity.activationDigest then none
  else if raw.runtimeStream.world.contentSession != raw.identity.contentSession then none
  else if raw.runtimeStream.world.contentEpoch != raw.identity.contentEpoch then none
  else some ⟨raw⟩

/-! ## Actual runtime + EventBatch inclusion -/

def runtimeReceiptPayloadDigest (receipt : CrewFieldMissionRuntime.ReceiptWire) : Digest32 :=
  CrewFieldMissionRuntime.digestString RUNTIME_RECEIPT_DIGEST_DOMAIN receipt.toJson

/-- Opaque evidence that one exact runtime output was included by the ordered
batch planner.  The constructor is private.  Production can obtain it only from
`sealRuntimeReceipt`, which requires both the real `judge` equation and the real
`EventBatch.applyBatch` equation. -/
structure RuntimeEventBatchReceipt where
  private mk ::
  activationId : Digest32
  runtimeStream : EventBatch.StreamId
  plan : ShiftPlan
  output : CrewFieldMissionRuntime.OutputWire
  batch : EventBatch.AppliedBatch
  includedEvent : EventBatch.IndexedEvent
  included : includedEvent ∈ batch.events
  streamExact : EventBatch.streamOfStatement batch.coordinate.world includedEvent.statement =
    runtimeStream
  payloadExact : includedEvent.statement.payloadDigest =
    runtimeReceiptPayloadDigest output.receipt
  actorExact : plan.officer.playerKey = output.receipt.actor
  shiftExact : plan.shift.value = output.receipt.admission
  runtimeRoster : List Seat
  rosterExact : plan.selectedCrew = runtimeRoster

/-- The only public constructor.  The proofs are deliberately not retained as
runtime data, but crossing this function requires an actual accepted runtime
successor and an actual accepted EventBatch containing its payload. -/
def sealRuntimeReceipt (activation : CrewFieldMissionRuntime.Activation)
    (before : CrewFieldMissionRuntime.StateWire)
    (command : CrewFieldMissionRuntime.CommandWire)
    (output : CrewFieldMissionRuntime.OutputWire)
    (judged : CrewFieldMissionRuntime.judge activation before command = .ok output)
    (boundary : EventBatch.DigestBoundary) (initialHeads : List EventBatch.StreamHead)
    (envelope : EventBatch.Envelope) (batch : EventBatch.AppliedBatch)
    (batchAccepted : EventBatch.applyBatch boundary initialHeads envelope = .ok batch)
    (runtimeStream : EventBatch.StreamId) (plan : ShiftPlan)
    (includedEvent : EventBatch.IndexedEvent)
    (included : includedEvent ∈ batch.events)
    (streamExact : EventBatch.streamOfStatement batch.coordinate.world includedEvent.statement =
      runtimeStream)
    (payloadExact : includedEvent.statement.payloadDigest =
      runtimeReceiptPayloadDigest output.receipt)
    (actorExact : plan.officer.playerKey = output.receipt.actor)
    (shiftExact : plan.shift.value = output.receipt.admission)
    (rosterExact : plan.selectedCrew = activation.raw.fieldSession.roster) :
    RuntimeEventBatchReceipt :=
  let _ := judged
  let _ := batchAccepted
  ⟨activation.raw.activationId, runtimeStream, plan, output, batch, includedEvent,
    included, streamExact, payloadExact, actorExact, shiftExact,
    activation.raw.fieldSession.roster, rosterExact⟩

def RuntimeEventBatchReceipt.receiptId (receipt : RuntimeEventBatchReceipt) : Digest32 :=
  receipt.output.receipt.runDigest

def RuntimeEventBatchReceipt.owner (receipt : RuntimeEventBatchReceipt) : Digest32 :=
  receipt.output.receipt.actor

def RuntimeEventBatchReceipt.sourceBatchDigest
    (receipt : RuntimeEventBatchReceipt) : Digest32 :=
  receipt.batch.batchDigest

/-! ## Explicitly sealed specialist seams -/

structure DerivedCrewHealthView where
  wounds : Nat
  strain : Nat
  inRecovery : Bool
  training : Nat
deriving Repr, DecidableEq

def DerivedCrewHealthView.empty : DerivedCrewHealthView := ⟨0, 0, false, 0⟩

/-- No health reducer lives here.  A future canonical crew-health stream must
emit this receipt after EventBatch inclusion. -/
structure CanonicalHealthReceiptInterface where
  private mk ::
  receiptId : Digest32
  sourceBatchDigest : Digest32
  owner : Digest32
  before : DerivedCrewHealthView
  after : DerivedCrewHealthView
  recovery : Bool
  recoveryProgress : recovery = true →
    (after.wounds < before.wounds ∨ after.strain < before.strain)

structure OrdinaryPartTransfer where
  part : CrewFieldMissionRuntime.PartId
  serial : Nat
  beforeOwner : Digest32
  afterOwner : Digest32
deriving DecidableEq

/-- Current BazaarGame does not expose ordinary `PartId` custody.  This adapter
therefore stays sealed.  It contains no relic, mint, price, or contribution. -/
structure BazaarPartReceiptInterface where
  private mk ::
  receiptId : Digest32
  sourceBatchDigest : Digest32
  seller : Digest32
  buyer : Digest32
  offered : OrdinaryPartTransfer
  requested : OrdinaryPartTransfer
  offeredExact : offered.beforeOwner = seller ∧ offered.afterOwner = buyer
  requestedExact : requested.beforeOwner = buyer ∧ requested.afterOwner = seller

def relicMarketIngress (_ : ContentContract.RelicId) : Option BazaarPartReceiptInterface := none

theorem content_contract_relic_is_non_market (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

/-! ## Derived gameplay projections -/

structure OrdinaryPartNotice where
  sourceRun : Digest32
  part : CrewFieldMissionRuntime.PartId
  quantity : Nat
  recipient : Digest32
deriving DecidableEq

structure NonMarketRelicNotice where
  sourceRun : Digest32
  relic : ContentContract.RelicId
  destination : ContentContract.CustodyLocation
deriving DecidableEq

structure BetaCandidateNotice where
  sourceRun : Digest32
  artifact : Nat
deriving DecidableEq

structure ShiftSummary where
  plan : ShiftPlan
  runDigest : Digest32
  route : String
  extraction : String
  contribution : CrewFieldMissionRuntime.ContributionWire
  featuredArtifact : Nat
  ordinaryPartCount : Nat
  nonMarketRelicCount : Nat
deriving DecidableEq

def summaryOf (receipt : RuntimeEventBatchReceipt) : ShiftSummary where
  plan := receipt.plan
  runDigest := receipt.receiptId
  route := receipt.output.receipt.route
  extraction := receipt.output.receipt.extraction
  contribution := receipt.output.receipt.contribution
  featuredArtifact := receipt.output.receipt.featuredArtifact
  ordinaryPartCount := receipt.output.receipt.ordinaryMints.length
  nonMarketRelicCount := receipt.output.receipt.relicCustody.length

def ordinaryNoticesOf (receipt : RuntimeEventBatchReceipt) : List OrdinaryPartNotice :=
  receipt.output.receipt.ordinaryMints.map fun mint =>
    ⟨receipt.receiptId, mint.part, mint.quantity, mint.recipient⟩

def relicNoticesOf (receipt : RuntimeEventBatchReceipt) : List NonMarketRelicNotice :=
  receipt.output.receipt.relicCustody.map fun custody =>
    ⟨receipt.receiptId, custody.relic, custody.destination⟩

def betaCandidateOf (receipt : RuntimeEventBatchReceipt) : BetaCandidateNotice :=
  ⟨receipt.receiptId, receipt.output.receipt.featuredArtifact⟩

structure DerivedCareerView where
  expeditions : Nat
  returnNow : Nat
  descendFurther : Nat
  runtimeScore : Nat
  recoveriesObserved : Nat
  marketExchangesObserved : Nat
deriving Repr, DecidableEq

def DerivedCareerView.empty : DerivedCareerView := ⟨0, 0, 0, 0, 0, 0⟩

def advanceCareer (before : DerivedCareerView) (summary : ShiftSummary) :
    DerivedCareerView :=
  { before with
    expeditions := before.expeditions + 1
    returnNow := before.returnNow + if summary.extraction = "return-now" then 1 else 0
    descendFurther := before.descendFurther +
      if summary.extraction = "descend-further" then 1 else 0
    runtimeScore := before.runtimeScore + summary.contribution.score }

structure PartMarketObservation where
  receiptId : Digest32
  offered : CrewFieldMissionRuntime.PartId
  requested : CrewFieldMissionRuntime.PartId
deriving DecidableEq

inductive FanoutEvent where
  | runtimeRunObserved (run : Digest32) (shift : ShiftId)
  | careerProjectionChanged (before after : DerivedCareerView)
  | ordinaryPartAuthorizationObserved (notice : OrdinaryPartNotice)
  | nonMarketRelicCustodyObserved (notice : NonMarketRelicNotice)
  | betaCandidateObserved (notice : BetaCandidateNotice)
  | healthProjectionObserved (receipt : Digest32)
  | partMarketObserved (receipt : Digest32)
deriving DecidableEq

structure FanoutBatch where
  sourceEvent : Nat
  sourceBatchDigest : Digest32
  ordered : List FanoutEvent
deriving DecidableEq

/-- No authoritative world, crew, inventory, custody, offer, or balance field. -/
structure State where
  private mk ::
  identity : SeasonIdentity
  eventCount : Nat
  career : DerivedCareerView
  health : DerivedCrewHealthView
  consumedRuntimeRuns : Finset Digest32
  consumedHealthReceipts : Finset Digest32
  consumedMarketReceipts : Finset Digest32
  completed : List ShiftSummary
  ordinaryParts : List OrdinaryPartNotice
  nonMarketRelics : List NonMarketRelicNotice
  betaCandidates : List BetaCandidateNotice
  marketActivity : List PartMarketObservation
  fanoutBatches : List FanoutBatch
deriving DecidableEq

def initialState (config : Config) : State where
  identity := config.raw.identity
  eventCount := 0
  career := .empty
  health := .empty
  consumedRuntimeRuns := ∅
  consumedHealthReceipts := ∅
  consumedMarketReceipts := ∅
  completed := []
  ordinaryParts := []
  nonMarketRelics := []
  betaCandidates := []
  marketActivity := []
  fanoutBatches := []

inductive ObservedReceipt where
  | runtime (receipt : RuntimeEventBatchReceipt)
  | health (receipt : CanonicalHealthReceiptInterface)
  | partMarket (receipt : BazaarPartReceiptInterface)

def ObservedReceipt.sourceBatchDigest : ObservedReceipt → Digest32
  | .runtime receipt => receipt.sourceBatchDigest
  | .health receipt => receipt.sourceBatchDigest
  | .partMarket receipt => receipt.sourceBatchDigest

private def appendFanout (before : State) (sourceBatchDigest : Digest32)
    (ordered : List FanoutEvent) : State :=
  { before with
    eventCount := before.eventCount + 1
    fanoutBatches := before.fanoutBatches ++
      [⟨before.eventCount + 1, sourceBatchDigest, ordered⟩] }

def runtimeTaxonomyValidB (receipt : RuntimeEventBatchReceipt) : Bool :=
  receipt.output.receipt.ordinaryMints.all fun mint =>
      decide (0 < mint.quantity ∧ mint.quantity ≤ CrewFieldMissionRuntime.MAX_PART_QUANTITY) &&
      decide (mint.marketEligible = true) &&
      decide (mint.recipient = receipt.owner) &&
  receipt.output.receipt.relicCustody.all fun custody =>
      decide (custody.marketEligible = false) &&
      decide (custody.directTradeAllowed = false) &&
      decide (custody.destination ≠ .market)

private def acceptRuntime (config : Config) (before : State)
    (receipt : RuntimeEventBatchReceipt) : Option State := do
  if receipt.activationId != config.raw.identity.activationDigest then none
  else if receipt.runtimeStream != config.raw.runtimeStream then none
  else if receipt.batch.coordinate.world.federationId != before.identity.federationId then none
  else if receipt.batch.coordinate.world.contentSession != before.identity.contentSession then none
  else if receipt.batch.coordinate.world.contentEpoch != before.identity.contentEpoch then none
  else if receipt.receiptId ∈ before.consumedRuntimeRuns then none
  else if before.completed.length >= MAX_SHIFTS then none
  else if !runtimeTaxonomyValidB receipt then none
  else
    let summary := summaryOf receipt
    let career := advanceCareer before.career summary
    let parts := ordinaryNoticesOf receipt
    let relics := relicNoticesOf receipt
    let candidate := betaCandidateOf receipt
    let events :=
      [.runtimeRunObserved receipt.receiptId receipt.plan.shift,
       .careerProjectionChanged before.career career] ++
      parts.map FanoutEvent.ordinaryPartAuthorizationObserved ++
      relics.map FanoutEvent.nonMarketRelicCustodyObserved ++
      [.betaCandidateObserved candidate]
    let next := { before with
      career
      consumedRuntimeRuns := insert receipt.receiptId before.consumedRuntimeRuns
      completed := before.completed ++ [summary]
      ordinaryParts := before.ordinaryParts ++ parts
      nonMarketRelics := before.nonMarketRelics ++ relics
      betaCandidates := before.betaCandidates ++ [candidate] }
    some (appendFanout next receipt.sourceBatchDigest events)

private def acceptHealth (before : State)
    (receipt : CanonicalHealthReceiptInterface) : Option State := do
  if receipt.receiptId ∈ before.consumedHealthReceipts then none
  else if receipt.before != before.health then none
  else
    let career := { before.career with
      recoveriesObserved := before.career.recoveriesObserved +
        if receipt.recovery then 1 else 0 }
    let next := { before with
      career
      health := receipt.after
      consumedHealthReceipts := insert receipt.receiptId before.consumedHealthReceipts }
    some (appendFanout next receipt.sourceBatchDigest
      [.healthProjectionObserved receipt.receiptId])

private def acceptPartMarket (before : State)
    (receipt : BazaarPartReceiptInterface) : Option State := do
  if receipt.receiptId ∈ before.consumedMarketReceipts then none
  else
    let observation : PartMarketObservation :=
      ⟨receipt.receiptId, receipt.offered.part, receipt.requested.part⟩
    let career := { before.career with
      marketExchangesObserved := before.career.marketExchangesObserved + 1 }
    let next := { before with
      career
      consumedMarketReceipts := insert receipt.receiptId before.consumedMarketReceipts
      marketActivity := before.marketActivity ++ [observation] }
    some (appendFanout next receipt.sourceBatchDigest
      [.partMarketObserved receipt.receiptId])

def reduce (config : Config) (before : State) : ObservedReceipt → Option State
  | .runtime receipt => acceptRuntime config before receipt
  | .health receipt => acceptHealth before receipt
  | .partMarket receipt => acceptPartMarket before receipt

theorem reduce_deterministic (config : Config) (before : State)
    (receipt : ObservedReceipt) {left right : State}
    (hl : reduce config before receipt = some left)
    (hr : reduce config before receipt = some right) : left = right := by
  rw [hl] at hr
  exact Option.some.inj hr

theorem runtime_receipt_only_projects (config : Config) (before after : State)
    (receipt : RuntimeEventBatchReceipt)
    (h : reduce config before (.runtime receipt) = some after) :
    after.health = before.health ∧
      after.consumedHealthReceipts = before.consumedHealthReceipts ∧
      after.consumedMarketReceipts = before.consumedMarketReceipts ∧
      after.marketActivity = before.marketActivity := by
  simp only [reduce, acceptRuntime] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem market_receipt_cannot_change_health_or_runtime_history
    (config : Config) (before after : State) (receipt : BazaarPartReceiptInterface)
    (h : reduce config before (.partMarket receipt) = some after) :
    after.health = before.health ∧
      after.consumedRuntimeRuns = before.consumedRuntimeRuns ∧
      after.ordinaryParts = before.ordinaryParts ∧
      after.nonMarketRelics = before.nonMarketRelics := by
  simp only [reduce, acceptPartMarket] at h
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Exact replay and ordered derived fan-out -/

structure Boundary where
  aggregateKey : SeasonIdentity → Digest32
  genesisHead : State → Digest32
  payloadDigest : ObservedReceipt → Digest32
  eventDigest : EventStatement → Digest32

def streamSpec (boundary : Boundary) (config : Config) : StreamSpec where
  aggregate := {
    namespaceId := config.raw.identity.federationId
    kind := EXPEDITION_SEASON_STREAM_KIND
    key := boundary.aggregateKey config.raw.identity }
  version := ⟨config.raw.schemaVersion⟩
  genesisHead := boundary.genesisHead (initialState config)

def digestBoundary (boundary : Boundary) :
    EventSourcing.DigestBoundary ObservedReceipt where
  payloadDigest := boundary.payloadDigest
  eventDigest := boundary.eventDigest

abbrev Envelope := EventSourcing.EventEnvelope ObservedReceipt

def rebuild (boundary : Boundary) (config : Config) (events : List Envelope) :
    Except EventSourcing.Error (EventSourcing.ReplayState State) :=
  EventSourcing.rebuild (streamSpec boundary config) (digestBoundary boundary)
    (reduce config) (initialState config) events

structure IntendedBatchStatement where
  aggregate : AggregateId
  identity : SeasonIdentity
  sourceEvent : Nat
  sourceBatchDigest : Digest32
  ordered : List FanoutEvent
deriving DecidableEq

def intendedBatch? (boundary : Boundary) (config : Config) (state : State)
    (sourceEvent : Nat) : Option IntendedBatchStatement := do
  let batch ← state.fanoutBatches.find? fun item => item.sourceEvent = sourceEvent
  some ⟨(streamSpec boundary config).aggregate, state.identity, batch.sourceEvent,
    batch.sourceBatchDigest, batch.ordered⟩

structure FanoutBatchBoundary where
  stream : FanoutEvent → EventBatch.StreamId
  payloadDigest : FanoutEvent → Digest32
  digests : EventBatch.DigestBoundary

private def planIndexedEvents (boundary : FanoutBatchBoundary) :
    Nat → List EventBatch.StreamHead → List FanoutEvent →
      Option (List EventBatch.IndexedEvent × List EventBatch.StreamHead)
  | _, heads, [] => some ([], heads)
  | index, heads, event :: events => do
      let stream := boundary.stream event
      let head ← EventBatch.headFor? heads stream
      let statement : EventStatement := {
        aggregate := stream.aggregate
        version := stream.version
        sequence := head.sequence + 1
        predecessor := head.head
        payloadDigest := boundary.payloadDigest event }
      let indexed : EventBatch.IndexedEvent :=
        ⟨index, statement, boundary.digests.eventDigest statement⟩
      let successor : EventBatch.StreamHead :=
        ⟨stream, statement.sequence, indexed.eventDigest⟩
      let (rest, finalHeads) ← planIndexedEvents boundary (index + 1)
        (EventBatch.replaceHead heads successor) events
      some (indexed :: rest, finalHeads)

def eventBatchEnvelope? (boundary : FanoutBatchBoundary)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (initialHeads : List EventBatch.StreamHead) (batch : IntendedBatchStatement) :
    Option EventBatch.Envelope := do
  if batch.identity.federationId != coordinate.world.federationId then none
  else if batch.ordered.isEmpty then none
  else if MAX_FANOUT_EVENTS < batch.ordered.length then none
  else
    let (events, _) ← planIndexedEvents boundary 0 initialHeads batch.ordered
    let statement : EventBatch.Statement := ⟨coordinate, events⟩
    some ⟨statement, boundary.digests.batchDigest statement⟩

/-! ## Executable projection and taxonomy fixtures -/

private def digestFilled (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureOwner : Digest32 := digestFilled 7
private def fixtureBuyer : Digest32 := digestFilled 8

private def fixtureRuntimeStream : EventBatch.StreamId where
  world := {
    federationId := digestFilled 1
    contentRoot := digestFilled 5
    activationDigest := digestFilled 4
    contentSession := digestFilled 3
    contentEpoch := ⟨1⟩ }
  aggregate := ⟨digestFilled 1, 80, digestFilled 2⟩
  version := ⟨1⟩

private def fixtureIdentity : SeasonIdentity :=
  ⟨digestFilled 1, digestFilled 3, ⟨1⟩, ⟨1⟩, digestFilled 4⟩

private def fixtureConfig : Config :=
  ⟨⟨1, fixtureIdentity, fixtureRuntimeStream⟩⟩

private def fixturePlan : ShiftPlan where
  shift := ⟨1⟩
  officer := CrewRelayExpedition.fixtureSeat0
  selectedCrew := [CrewRelayExpedition.fixtureSeat0,
    CrewRelayExpedition.fixtureSeat1, CrewRelayExpedition.fixtureSeat2,
    CrewRelayExpedition.fixtureSeat3]

private def fixtureRuntimeState : CrewFieldMissionRuntime.StateWire where
  activationId := fixtureIdentity.activationDigest
  sequence := 1
  head := digestFilled 20
  nextAdmission := 2
  consumedRuns := [digestFilled 21]

private def fixtureRuntimeReceiptWire : CrewFieldMissionRuntime.ReceiptWire where
  activationId := fixtureIdentity.activationDigest
  replayVerifierId := digestFilled 22
  admission := 1
  actor := fixturePlan.officer.playerKey
  route := "sealed-nave"
  extraction := "descend-further"
  runDigest := digestFilled 21
  predecessor := digestFilled 19
  successor := digestFilled 20
  contribution := ⟨3, 4, 5, 0, 120, [447]⟩
  featuredArtifact := 12
  ordinaryMints := [⟨⟨901⟩, 1, fixturePlan.officer.playerKey, true⟩]
  relicCustody := [⟨⟨447⟩, .quarantine, false, false⟩]

private def fixtureRuntimeOutput : CrewFieldMissionRuntime.OutputWire :=
  ⟨fixtureRuntimeState, fixtureRuntimeReceiptWire⟩

private def fixtureCoordinate : EventBatch.FinalizedTurnCoordinate where
  world := fixtureRuntimeStream.world
  commitOrdinal := 1
  blockId := digestFilled 30
  turnHash := digestFilled 31
  receiptHash := digestFilled 32
  actorRoot := fixturePlan.officer.playerKey
  signer := fixturePlan.officer.playerKey

private def fixtureRuntimeStatement : EventStatement where
  aggregate := fixtureRuntimeStream.aggregate
  version := fixtureRuntimeStream.version
  sequence := 1
  predecessor := digestFilled 33
  payloadDigest := runtimeReceiptPayloadDigest fixtureRuntimeReceiptWire

private def fixtureRuntimeEvent : EventBatch.IndexedEvent :=
  ⟨0, fixtureRuntimeStatement, digestFilled 34⟩

private def fixtureAppliedBatch : EventBatch.AppliedBatch :=
  ⟨fixtureCoordinate, digestFilled 35, [fixtureRuntimeEvent],
    [⟨fixtureRuntimeStream, 1, digestFilled 34⟩]⟩

/-- Private fixture bypasses the public sealer only to exercise the projection;
the boundary module proves no importer can do this. -/
private def fixtureRuntimeReceipt : RuntimeEventBatchReceipt where
  activationId := fixtureIdentity.activationDigest
  runtimeStream := fixtureRuntimeStream
  plan := fixturePlan
  output := fixtureRuntimeOutput
  batch := fixtureAppliedBatch
  includedEvent := fixtureRuntimeEvent
  included := by simp [fixtureAppliedBatch]
  streamExact := rfl
  payloadExact := rfl
  actorExact := rfl
  shiftExact := rfl
  runtimeRoster := fixturePlan.selectedCrew
  rosterExact := rfl

private def fixtureAfterRuntime : State :=
  (reduce fixtureConfig (initialState fixtureConfig) (.runtime fixtureRuntimeReceipt)).get
    (by native_decide)

private def fixtureHealthReceipt : CanonicalHealthReceiptInterface where
  receiptId := digestFilled 40
  sourceBatchDigest := digestFilled 41
  owner := fixtureOwner
  before := .empty
  after := ⟨1, 2, true, 3⟩
  recovery := false
  recoveryProgress := by simp

private def fixtureMarketReceipt : BazaarPartReceiptInterface where
  receiptId := digestFilled 42
  sourceBatchDigest := digestFilled 43
  seller := fixtureOwner
  buyer := fixtureBuyer
  offered := ⟨⟨901⟩, 1, fixtureOwner, fixtureBuyer⟩
  requested := ⟨⟨902⟩, 2, fixtureBuyer, fixtureOwner⟩
  offeredExact := ⟨rfl, rfl⟩
  requestedExact := ⟨rfl, rfl⟩

theorem runtime_receipt_projects_parts_relics_and_candidate_without_owning_them :
    fixtureAfterRuntime.completed.length = 1 ∧
      fixtureAfterRuntime.career.expeditions = 1 ∧
      fixtureAfterRuntime.ordinaryParts = [⟨digestFilled 21, ⟨901⟩, 1,
        fixturePlan.officer.playerKey⟩] ∧
      fixtureAfterRuntime.nonMarketRelics =
        [⟨digestFilled 21, ⟨447⟩, .quarantine⟩] ∧
      fixtureAfterRuntime.betaCandidates = [⟨digestFilled 21, 12⟩] := by
  native_decide

theorem hostile_same_runtime_run_cannot_project_twice :
    reduce fixtureConfig fixtureAfterRuntime (.runtime fixtureRuntimeReceipt) = none := by
  native_decide

theorem sealed_health_receipt_only_updates_derived_health :
    (reduce fixtureConfig (initialState fixtureConfig) (.health fixtureHealthReceipt)).map
      (fun state => (state.health, state.consumedRuntimeRuns,
        state.ordinaryParts, state.nonMarketRelics)) =
      some (fixtureHealthReceipt.after, ∅, [], []) := by
  native_decide

theorem sealed_part_market_receipt_never_moves_relic_or_runtime_projection :
    (reduce fixtureConfig fixtureAfterRuntime (.partMarket fixtureMarketReceipt)).map
      (fun state => (state.health, state.consumedRuntimeRuns,
        state.ordinaryParts, state.nonMarketRelics)) =
      some (fixtureAfterRuntime.health, fixtureAfterRuntime.consumedRuntimeRuns,
        fixtureAfterRuntime.ordinaryParts, fixtureAfterRuntime.nonMarketRelics) := by
  native_decide

#assert_axioms reduce_deterministic
#assert_axioms runtime_receipt_only_projects
#assert_axioms market_receipt_cannot_change_health_or_runtime_history
#assert_axioms content_contract_relic_is_non_market
#assert_compiled runtime_receipt_projects_parts_relics_and_candidate_without_owning_them
#assert_compiled hostile_same_runtime_run_cannot_project_twice
#assert_compiled sealed_health_receipt_only_updates_derived_health
#assert_compiled sealed_part_market_receipt_never_moves_relic_or_runtime_projection

end Dregg2.Games.PathOfAngels.ShipExpeditionSeason
