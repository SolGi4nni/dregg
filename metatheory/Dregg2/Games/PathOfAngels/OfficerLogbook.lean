/-
# OfficerLogbook — a rebuildable career record over finalized PoA batches

An officer logbook is not another game authority.  It is a bounded projection
of exact receipts which have already been placed in an `EventBatch`.  The
projection owns no browser session, balance, inventory, custody, health, canon,
or world-meter successor.  Deleting it and replaying the same accepted batches
reconstructs the same value.

The three source families deliberately retain their existing semantic types:

* Galley entries retain `GalleyMaintenanceDailyRuntime.ReceiptWire`;
* Shipworks entries retain the privately constructed `Shipworks.Settlement`;
* field entries retain `CrewFieldMissionRuntime.ReceiptWire`, its existing
  `CrewRelayExpedition.Seat` roster, ordinary-part authorizations, and
  non-market relic-custody authorizations.

Field recovery is the exact beta-only `ContentContract.RecoveryConsequence`.
It is recorded as an observation, never applied as health or a world debit.
Likewise, contribution history records the source receipt verbatim and never
sums it into personal wealth or gameplay power.  A featured artifact is a beta
discovery reference only; this module imports no canon-promotion operation.

`DigestBoundary.receiptDigest` is the canonical-codec/hash boundary for the
complete `ReceiptPayload`, including its subject.  `applyBatch` rechecks the
full ordered `EventBatch` before any projection changes.  Collision resistance,
durable CAS, and the host's claim that `FinalizedTurnCoordinate` came from the
real generic `CommitRecord` remain named deployment obligations.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime
import Dregg2.Games.PathOfAngels.Shipworks
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.OfficerLogbook

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

abbrev MAX_BATCHES : Nat := 4096
abbrev MAX_MISSIONS : Nat := 16384
abbrev MAX_AUXILIARY_RECORDS : Nat := 65536
abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1

/-! ## Exact source receipts -/

/-- The crew runtime does not carry the authored recovery row in its public
receipt.  This small extension is part of the finalized payload, not a browser
claim.  Validation below admits only the existing four-seat role schema and the
existing beta-only, zero-debit recovery semantics. -/
structure CrewReceipt where
  receipt : CrewFieldMissionRuntime.ReceiptWire
  roster : List Seat
  recovery : ContentContract.RecoveryConsequence
deriving DecidableEq

inductive SourceReceipt where
  | galley (receipt : GalleyMaintenanceDailyRuntime.ReceiptWire)
  | shipworks (settlement : Shipworks.Settlement)
  | crew (receipt : CrewReceipt)
deriving DecidableEq

/-- `subject` is committed with the receipt.  It is the logbook being updated,
not necessarily the actor who finalized a four-person crew mission. -/
structure ReceiptPayload where
  subject : Digest32
  source : SourceReceipt
deriving DecidableEq

structure DigestBoundary where
  batch : EventBatch.DigestBoundary
  receiptDigest : ReceiptPayload -> Digest32

/-- One proposed projection step.  The event envelope and its initial heads
are retained so Lean, rather than the storage host, decides whether the batch
is structurally admissible. -/
structure FinalizedBatch where
  initialHeads : List EventBatch.StreamHead
  envelope : EventBatch.Envelope
  receipts : List ReceiptPayload
deriving DecidableEq

/-! ## Disposable logbook views -/

inductive SourceKind where
  | galley
  | shipworks
  | crew
deriving Repr, DecidableEq

inductive Participation where
  | principal
  | assist
deriving Repr, DecidableEq

structure EventRef where
  coordinate : EventBatch.FinalizedTurnCoordinate
  batchDigest : Digest32
  eventIndex : Nat
  stream : EventBatch.StreamId
  eventDigest : Digest32
deriving DecidableEq

structure MissionRecord where
  event : EventRef
  source : SourceKind
  participation : Participation
  role : Option CrewRole
deriving DecidableEq

structure RoleRecord where
  event : EventRef
  role : CrewRole
deriving DecidableEq

structure AssistRecord where
  event : EventRef
  principal : Digest32
  role : CrewRole
deriving DecidableEq

/-- This is a beta recovery observation.  It is not an injury mutation. -/
structure RecoveryRecord where
  event : EventRef
  consequence : ContentContract.RecoveryConsequence
deriving DecidableEq

structure RouteRecord where
  event : EventRef
  /-- Exact canonical spelling emitted by the crew runtime. -/
  route : String
deriving DecidableEq

/-- A beta discovery reference.  No alpha fact or canon authority is present. -/
structure DiscoveryRecord where
  event : EventRef
  artifact : ContentContract.ArtifactId
deriving DecidableEq

/-- Authorization observed in a receipt, not an inventory row or mint. -/
structure OrdinarySalvageRecord where
  event : EventRef
  authorization : CrewFieldMissionRuntime.OrdinaryMintAuthorization
deriving DecidableEq

/-- Custody observed in a receipt, not custody owned by this projection. -/
structure CustodyRecord where
  event : EventRef
  authorization : CrewFieldMissionRuntime.RelicCustodyAuthorization
deriving DecidableEq

inductive ContributionValue where
  | galleyLocalService (amount : Nat)
  | shipworks (contribution : Contribution)
  | crewMission (contribution : CrewFieldMissionRuntime.ContributionWire)
deriving DecidableEq

/-- Mission-level history.  Nothing in this type denotes a personal balance. -/
structure ContributionRecord where
  event : EventRef
  value : ContributionValue
deriving DecidableEq

structure Identity where
  world : EventBatch.WorldIdentity
  officer : Digest32
deriving DecidableEq

/-- All lists preserve finalized order.  They are histories, not alternate
successor authorities. -/
structure Projection where
  identity : Identity
  lastCoordinate : Option EventBatch.FinalizedTurnCoordinate
  batchDigests : List Digest32
  missions : List MissionRecord
  roles : List RoleRecord
  assists : List AssistRecord
  recoveries : List RecoveryRecord
  routes : List RouteRecord
  discoveries : List DiscoveryRecord
  ordinarySalvage : List OrdinarySalvageRecord
  custody : List CustodyRecord
  contributions : List ContributionRecord
deriving DecidableEq

def Projection.empty (identity : Identity) : Projection where
  identity
  lastCoordinate := none
  batchDigests := []
  missions := []
  roles := []
  assists := []
  recoveries := []
  routes := []
  discoveries := []
  ordinarySalvage := []
  custody := []
  contributions := []

private def recordWorldExactB (world : EventBatch.WorldIdentity)
    (event : EventRef) : Bool :=
  event.coordinate.world = world

def Projection.validB (state : Projection) : Bool :=
  decide (state.batchDigests.length <= MAX_BATCHES) &&
  decide state.batchDigests.Nodup &&
  decide (state.missions.length <= MAX_MISSIONS) &&
  decide (state.roles.length <= MAX_MISSIONS) &&
  decide (state.assists.length <= MAX_MISSIONS) &&
  decide (state.recoveries.length <= MAX_MISSIONS) &&
  decide (state.routes.length <= MAX_MISSIONS) &&
  decide (state.discoveries.length <= MAX_MISSIONS) &&
  decide (state.ordinarySalvage.length <= MAX_AUXILIARY_RECORDS) &&
  decide (state.custody.length <= MAX_AUXILIARY_RECORDS) &&
  decide (state.contributions.length <= MAX_MISSIONS) &&
  state.missions.all (recordWorldExactB state.identity.world ∘ MissionRecord.event) &&
  state.roles.all (recordWorldExactB state.identity.world ∘ RoleRecord.event) &&
  state.assists.all (recordWorldExactB state.identity.world ∘ AssistRecord.event) &&
  state.recoveries.all (recordWorldExactB state.identity.world ∘ RecoveryRecord.event) &&
  state.routes.all (recordWorldExactB state.identity.world ∘ RouteRecord.event) &&
  state.discoveries.all (recordWorldExactB state.identity.world ∘ DiscoveryRecord.event) &&
  state.ordinarySalvage.all
    (recordWorldExactB state.identity.world ∘ OrdinarySalvageRecord.event) &&
  state.custody.all (recordWorldExactB state.identity.world ∘ CustodyRecord.event) &&
  state.contributions.all
    (recordWorldExactB state.identity.world ∘ ContributionRecord.event) &&
  match state.lastCoordinate with
  | none => state.batchDigests.isEmpty && state.missions.isEmpty
  | some coordinate =>
      decide (coordinate.world = state.identity.world) &&
      !state.batchDigests.isEmpty && !state.missions.isEmpty

/-! ## Source validation and exact deltas -/

private def seatForPlayer? : List Seat -> Digest32 -> Option Seat
  | [], _ => none
  | seat :: seats, player =>
      if seat.playerKey = player then some seat else seatForPlayer? seats player

private def rosterValidB (roster : List Seat) : Bool :=
  decide (roster.length = CrewFieldMission.CREW_SIZE) &&
  decide (roster.map Seat.id = [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]) &&
  decide (roster.map Seat.role = CrewFieldMission.expectedRoles) &&
  decide (roster.map Seat.playerKey).Nodup &&
  decide (roster.map Seat.credential).Nodup

private def crewContributionValidB
    (contribution : CrewFieldMissionRuntime.ContributionWire) : Bool :=
  decide (contribution.intel <= METRIC_LIMIT) &&
  decide (contribution.supplies <= METRIC_LIMIT) &&
  decide (contribution.cohesion <= METRIC_LIMIT) &&
  decide (contribution.influence <= METRIC_LIMIT) &&
  decide (contribution.score <= METRIC_LIMIT) &&
  decide (contribution.relics.length <= RELIC_LIMIT) &&
  decide contribution.relics.Nodup &&
  contribution.relics.all fun relic => decide (relic <= WIRE_U64_MAX)

private def ordinarySalvageValidB (actor : Digest32)
    (authorizations : List CrewFieldMissionRuntime.OrdinaryMintAuthorization) : Bool :=
  decide (authorizations.length <= CrewFieldMissionRuntime.MAX_PART_RULES) &&
  decide (authorizations.map (fun authorization => authorization.part)).Nodup &&
  authorizations.all fun authorization =>
    decide (0 < authorization.quantity) &&
    decide (authorization.quantity <= CrewFieldMissionRuntime.MAX_PART_QUANTITY) &&
    decide (authorization.part.value <= WIRE_U64_MAX) &&
    decide (authorization.recipient = actor) &&
    authorization.marketEligible

private def custodyValidB
    (authorizations : List CrewFieldMissionRuntime.RelicCustodyAuthorization) : Bool :=
  decide (authorizations.length <= RELIC_LIMIT) &&
  decide (authorizations.map (fun authorization => authorization.relic)).Nodup &&
  authorizations.all fun authorization =>
    decide (authorization.relic.value <= WIRE_U64_MAX) &&
    !authorization.marketEligible && !authorization.directTradeAllowed &&
    decide (authorization.destination != .market)

private def knownCrewRouteB (route : String) : Bool :=
  route = "maintenance-spine" || route = "signal-gallery" || route = "sealed-nave"

private def knownExtractionB (extraction : String) : Bool :=
  extraction = "return-now" || extraction = "descend-further"

private def galleyValidB (coordinate : EventBatch.FinalizedTurnCoordinate)
    (event : EventBatch.IndexedEvent) (subject : Digest32)
    (receipt : GalleyMaintenanceDailyRuntime.ReceiptWire) : Bool :=
  decide (subject = coordinate.signer) &&
  decide (receipt.actor = coordinate.signer) &&
  decide (receipt.sequence = event.statement.sequence) &&
  (receipt.kind = "public-play" || receipt.kind = "holder-sponsor") &&
  decide (0 < receipt.localService) &&
  decide (receipt.localService <= GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE) &&
  decide (receipt.powerDelta = 0) && decide (receipt.lootDelta = 0) &&
  decide (receipt.canonRevisionDelta = 0)

private def shipworksValidB (coordinate : EventBatch.FinalizedTurnCoordinate)
    (subject : Digest32) (settlement : Shipworks.Settlement) : Bool :=
  decide (subject = coordinate.signer) &&
  decide (settlement.finalState.status = .complete) &&
  decide (settlement.finalState.dispatch.epoch = settlement.missionEpoch) &&
  decide (settlement.finalState.dispatch.job = settlement.job) &&
  decide (settlement.claimCounter = settlement.nextRecord.lastCounter) &&
  decide (settlement.nextRecord.lastClaimedEpoch = some settlement.missionEpoch) &&
  decide (Shipworks.contributionFor settlement.finalState = some settlement.contribution)

private def crewValidB (coordinate : EventBatch.FinalizedTurnCoordinate)
    (subject : Digest32) (source : CrewReceipt) : Bool :=
  decide (source.receipt.activationId = coordinate.world.activationDigest) &&
  decide (source.receipt.actor = coordinate.signer) &&
  decide (0 < source.receipt.admission) &&
  rosterValidB source.roster &&
  decide ((seatForPlayer? source.roster source.receipt.actor).isSome) &&
  decide ((seatForPlayer? source.roster subject).isSome) &&
  knownCrewRouteB source.receipt.route && knownExtractionB source.receipt.extraction &&
  decide (source.receipt.featuredArtifact <= WIRE_U64_MAX) &&
  crewContributionValidB source.receipt.contribution &&
  ordinarySalvageValidB source.receipt.actor source.receipt.ordinaryMints &&
  custodyValidB source.receipt.relicCustody &&
  ContentContract.recoveryConsequenceValidB source.recovery

private def sourceValidB (coordinate : EventBatch.FinalizedTurnCoordinate)
    (event : EventBatch.IndexedEvent) (payload : ReceiptPayload) : Bool :=
  match payload.source with
  | .galley receipt => galleyValidB coordinate event payload.subject receipt
  | .shipworks settlement => shipworksValidB coordinate payload.subject settlement
  | .crew receipt => crewValidB coordinate payload.subject receipt

private def eventRef (coordinate : EventBatch.FinalizedTurnCoordinate)
    (batchDigest : Digest32) (event : EventBatch.IndexedEvent) : EventRef where
  coordinate
  batchDigest
  eventIndex := event.eventIndex
  stream := EventBatch.streamOfStatement coordinate.world event.statement
  eventDigest := event.eventDigest

private structure Delta where
  missions : List MissionRecord := []
  roles : List RoleRecord := []
  assists : List AssistRecord := []
  recoveries : List RecoveryRecord := []
  routes : List RouteRecord := []
  discoveries : List DiscoveryRecord := []
  ordinarySalvage : List OrdinarySalvageRecord := []
  custody : List CustodyRecord := []
  contributions : List ContributionRecord := []

private def deltaFor? (coordinate : EventBatch.FinalizedTurnCoordinate)
    (batchDigest : Digest32) (event : EventBatch.IndexedEvent)
    (payload : ReceiptPayload) : Option Delta := do
  if !sourceValidB coordinate event payload then none
  let reference := eventRef coordinate batchDigest event
  match payload.source with
  | .galley receipt =>
      some {
        missions := [⟨reference, .galley, .principal, none⟩]
        contributions := [⟨reference, .galleyLocalService receipt.localService⟩]
      }
  | .shipworks settlement =>
      some {
        missions := [⟨reference, .shipworks, .principal, none⟩]
        contributions := [⟨reference, .shipworks settlement.contribution⟩]
      }
  | .crew source =>
      let seat <- seatForPlayer? source.roster payload.subject
      let participation :=
        if payload.subject = source.receipt.actor then .principal else .assist
      let assists := if participation = .assist then
        [AssistRecord.mk reference source.receipt.actor seat.role] else []
      let ordinary := source.receipt.ordinaryMints.filterMap fun authorization =>
        if authorization.recipient = payload.subject then
          some (OrdinarySalvageRecord.mk reference authorization)
        else none
      some {
        missions := [⟨reference, .crew, participation, some seat.role⟩]
        roles := [⟨reference, seat.role⟩]
        assists
        recoveries := [⟨reference, source.recovery⟩]
        routes := [⟨reference, source.receipt.route⟩]
        discoveries := [⟨reference, ⟨source.receipt.featuredArtifact⟩⟩]
        ordinarySalvage := ordinary
        custody := source.receipt.relicCustody.map (CustodyRecord.mk reference)
        contributions := [⟨reference, .crewMission source.receipt.contribution⟩]
      }

private def appendDeltas (left right : Delta) : Delta where
  missions := left.missions ++ right.missions
  roles := left.roles ++ right.roles
  assists := left.assists ++ right.assists
  recoveries := left.recoveries ++ right.recoveries
  routes := left.routes ++ right.routes
  discoveries := left.discoveries ++ right.discoveries
  ordinarySalvage := left.ordinarySalvage ++ right.ordinarySalvage
  custody := left.custody ++ right.custody
  contributions := left.contributions ++ right.contributions

private def deltasFor? (boundary : DigestBoundary)
    (coordinate : EventBatch.FinalizedTurnCoordinate) (batchDigest : Digest32) :
    List EventBatch.IndexedEvent -> List ReceiptPayload -> Option Delta
  | [], [] => some {}
  | event :: events, payload :: payloads => do
      if event.statement.payloadDigest != boundary.receiptDigest payload then none
      let first <- deltaFor? coordinate batchDigest event payload
      let rest <- deltasFor? boundary coordinate batchDigest events payloads
      some (appendDeltas first rest)
  | _, _ => none

private def withinBoundsB (state : Projection) (delta : Delta) : Bool :=
  decide (state.missions.length + delta.missions.length <= MAX_MISSIONS) &&
  decide (state.roles.length + delta.roles.length <= MAX_MISSIONS) &&
  decide (state.assists.length + delta.assists.length <= MAX_MISSIONS) &&
  decide (state.recoveries.length + delta.recoveries.length <= MAX_MISSIONS) &&
  decide (state.routes.length + delta.routes.length <= MAX_MISSIONS) &&
  decide (state.discoveries.length + delta.discoveries.length <= MAX_MISSIONS) &&
  decide (state.ordinarySalvage.length + delta.ordinarySalvage.length <=
    MAX_AUXILIARY_RECORDS) &&
  decide (state.custody.length + delta.custody.length <= MAX_AUXILIARY_RECORDS) &&
  decide (state.contributions.length + delta.contributions.length <= MAX_MISSIONS)

private def appendDelta (state : Projection) (delta : Delta) : Projection :=
  { state with
    missions := state.missions ++ delta.missions
    roles := state.roles ++ delta.roles
    assists := state.assists ++ delta.assists
    recoveries := state.recoveries ++ delta.recoveries
    routes := state.routes ++ delta.routes
    discoveries := state.discoveries ++ delta.discoveries
    ordinarySalvage := state.ordinarySalvage ++ delta.ordinarySalvage
    custody := state.custody ++ delta.custody
    contributions := state.contributions ++ delta.contributions }

inductive Error where
  | invalidProjection
  | wrongWorld
  | staleCoordinate
  | repeatedBatch
  | tooManyBatches
  | eventBatch (error : EventBatch.Error)
  | receiptBinding
  | recordLimit
  | invalidSuccessor
deriving Repr, DecidableEq

/-- The only projection transition.  Every source event must have one exact
payload in event order; partial or extra payload lists refuse. -/
def applyFinalizedBatch (boundary : DigestBoundary) (before : Projection)
    (input : FinalizedBatch) : Except Error Projection := do
  if !before.validB then throw .invalidProjection
  let coordinate := input.envelope.statement.coordinate
  if coordinate.world != before.identity.world then throw .wrongWorld
  match before.lastCoordinate with
  | none => pure ()
  | some prior =>
      if coordinate.commitOrdinal <= prior.commitOrdinal then throw .staleCoordinate
  if input.envelope.batchDigest ∈ before.batchDigests then throw .repeatedBatch
  if before.batchDigests.length >= MAX_BATCHES then throw .tooManyBatches
  match EventBatch.applyBatch boundary.batch input.initialHeads input.envelope with
  | .error error => throw (.eventBatch error)
  | .ok _ => pure ()
  let delta <- match deltasFor? boundary coordinate input.envelope.batchDigest
      input.envelope.statement.events input.receipts with
    | none => throw .receiptBinding
    | some delta => pure delta
  if !withinBoundsB before delta then throw .recordLimit
  let after := appendDelta before delta
  let after := { after with
    lastCoordinate := some coordinate
    batchDigests := before.batchDigests ++ [input.envelope.batchDigest] }
  if !after.validB then throw .invalidSuccessor
  pure after

def replay (boundary : DigestBoundary) : Projection -> List FinalizedBatch -> Except Error Projection
  | state, [] => .ok state
  | state, input :: inputs => do
      let next <- applyFinalizedBatch boundary state input
      replay boundary next inputs

theorem applyFinalizedBatch_deterministic (boundary : DigestBoundary)
    (before : Projection) (input : FinalizedBatch) (left right : Projection)
    (hl : applyFinalizedBatch boundary before input = .ok left)
    (hr : applyFinalizedBatch boundary before input = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

theorem replay_append (boundary : DigestBoundary) (before : Projection)
    (left right : List FinalizedBatch) :
    replay boundary before (left ++ right) =
      (replay boundary before left >>= fun middle => replay boundary middle right) := by
  induction left generalizing before with
  | nil => rfl
  | cons input inputs ih =>
      simp only [List.cons_append, replay]
      cases applyFinalizedBatch boundary before input <;> simp [ih]

theorem replay_deterministic (boundary : DigestBoundary) (before : Projection)
    (inputs : List FinalizedBatch) (left right : Projection)
    (hl : replay boundary before inputs = .ok left)
    (hr : replay boundary before inputs = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

/-! ## Executable exact and hostile fixtures -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureOfficer : Digest32 := digestByte 21
private def fixtureAssistant : Digest32 := digestByte 22

private def fixtureWorld : EventBatch.WorldIdentity where
  federationId := digestByte 1
  contentRoot := digestByte 2
  activationDigest := digestByte 3
  contentSession := digestByte 4
  contentEpoch := ⟨5⟩

private def fixtureCoordinate (ordinal : Nat) (signer : Digest32) :
    EventBatch.FinalizedTurnCoordinate where
  world := fixtureWorld
  commitOrdinal := ordinal
  blockId := digestByte (30 + ordinal)
  turnHash := digestByte (40 + ordinal)
  receiptHash := digestByte (50 + ordinal)
  actorRoot := digestByte (60 + ordinal)
  signer := signer

private def fixtureStream (kind key : Nat) : EventBatch.StreamId where
  world := fixtureWorld
  aggregate := { namespaceId := fixtureWorld.federationId, kind, key := digestByte key }
  version := ⟨1⟩

private def fixtureHead (kind key genesis : Nat) : EventBatch.StreamHead where
  stream := fixtureStream kind key
  sequence := 0
  head := digestByte genesis

private def fixtureReceiptCode : SourceReceipt -> Nat
  | .galley _ => 71
  | .shipworks _ => 72
  | .crew _ => 73

private def fixtureBoundary : DigestBoundary where
  receiptDigest payload := digestByte (fixtureReceiptCode payload.source +
    if payload.subject = fixtureOfficer then 0 else 10)
  batch := {
    eventDigest := fun statement =>
      digestByte (100 + statement.aggregate.kind + statement.sequence)
    batchDigest := fun statement =>
      digestByte (200 + statement.coordinate.commitOrdinal + statement.events.length) }

private def fixtureEvent (index : Nat) (stream : EventBatch.StreamId)
    (head : Digest32) (payload : ReceiptPayload) : EventBatch.IndexedEvent :=
  let statement : EventSourcing.EventStatement := {
    aggregate := stream.aggregate
    version := stream.version
    sequence := 1
    predecessor := head
    payloadDigest := fixtureBoundary.receiptDigest payload }
  ⟨index, statement, fixtureBoundary.batch.eventDigest statement⟩

private def fixtureGalleyReceipt : GalleyMaintenanceDailyRuntime.ReceiptWire where
  kind := "public-play"
  actor := fixtureOfficer
  beneficiary := fixtureOfficer
  sequence := 1
  localService := 3
  consumedGrantNullifier := digestByte 0
  authorityCommitment := digestByte 0
  powerDelta := 0
  lootDelta := 0
  canonRevisionDelta := 0

private def fixtureSettlement : Shipworks.Settlement :=
  (Shipworks.settle Shipworks.CareRecord.empty
    (Shipworks.powerSubmission 20000)).get (by native_decide)

private def fixtureRoster : List Seat :=
  [ ⟨⟨0⟩, fixtureOfficer, ⟨10⟩, .pathfinder, 0⟩
  , ⟨⟨1⟩, fixtureAssistant, ⟨11⟩, .engineer, 0⟩
  , ⟨⟨2⟩, digestByte 23, ⟨12⟩, .containment, 0⟩
  , ⟨⟨3⟩, digestByte 24, ⟨13⟩, .quartermaster, 0⟩ ]

private def fixtureCrewReceipt : CrewReceipt where
  receipt := {
    activationId := fixtureWorld.activationDigest
    replayVerifierId := digestByte 80
    admission := 1
    actor := fixtureOfficer
    route := "signal-gallery"
    extraction := "return-now"
    runDigest := digestByte 81
    predecessor := digestByte 82
    successor := digestByte 83
    contribution := ⟨6, 2, 3, 0, 25, []⟩
    featuredArtifact := 20
    ordinaryMints := [⟨⟨7⟩, 2, fixtureOfficer, true⟩]
    relicCustody := [⟨⟨8⟩, .quarantine, false, false⟩]
  }
  roster := fixtureRoster
  recovery := ⟨⟨40⟩, .marked, .oneStudyCycle, .betaRecordOnly, 0⟩

private def galleyPayload : ReceiptPayload :=
  ⟨fixtureOfficer, .galley fixtureGalleyReceipt⟩

private def shipworksPayload : ReceiptPayload :=
  ⟨fixtureOfficer, .shipworks fixtureSettlement⟩

private def crewPayload (subject : Digest32) : ReceiptPayload :=
  ⟨subject, .crew fixtureCrewReceipt⟩

private def galleyHead := fixtureHead 9 91 101
private def shipworksHead := fixtureHead 10 92 102
private def crewHead := fixtureHead 11 93 103

private def fixtureEvents : List EventBatch.IndexedEvent :=
  [ fixtureEvent 0 galleyHead.stream galleyHead.head galleyPayload
  , fixtureEvent 1 shipworksHead.stream shipworksHead.head shipworksPayload
  , fixtureEvent 2 crewHead.stream crewHead.head (crewPayload fixtureOfficer) ]

private def fixtureBatch : FinalizedBatch :=
  let statement : EventBatch.Statement :=
    ⟨fixtureCoordinate 1 fixtureOfficer, fixtureEvents⟩
  {
    initialHeads := [galleyHead, shipworksHead, crewHead]
    envelope := ⟨statement, fixtureBoundary.batch.batchDigest statement⟩
    receipts := [galleyPayload, shipworksPayload, crewPayload fixtureOfficer]
  }

private def fixtureInitial : Projection :=
  Projection.empty ⟨fixtureWorld, fixtureOfficer⟩

private def fixtureAfter : Projection :=
  (applyFinalizedBatch fixtureBoundary fixtureInitial fixtureBatch).toOption.get
    (by native_decide)

theorem fixture_three_source_batch_is_exactly_projected :
    fixtureAfter.missions.length = 3 &&
    fixtureAfter.roles.length = 1 &&
    fixtureAfter.assists.length = 0 &&
    fixtureAfter.recoveries.length = 1 &&
    fixtureAfter.routes.map RouteRecord.route = ["signal-gallery"] &&
    fixtureAfter.discoveries.map (fun record => record.artifact.value) = [20] &&
    fixtureAfter.ordinarySalvage.length = 1 &&
    fixtureAfter.custody.length = 1 &&
    fixtureAfter.contributions.length = 3 := by
  native_decide

theorem fixture_projection_remains_non_authoritative :
    fixtureAfter.ordinarySalvage.map
      (fun record => record.authorization.recipient) = [fixtureOfficer] &&
    fixtureAfter.custody.map
      (fun record => record.authorization.marketEligible) = [false] &&
    fixtureAfter.custody.map
      (fun record => record.authorization.directTradeAllowed) = [false] &&
    fixtureAfter.recoveries.map
      (fun record => record.consequence.implementation) = [.betaRecordOnly] &&
    fixtureAfter.recoveries.map
      (fun record => record.consequence.globalMeterDebit) = [0] := by
  native_decide

private def assistEvent : EventBatch.IndexedEvent :=
  fixtureEvent 0 crewHead.stream crewHead.head (crewPayload fixtureAssistant)

private def assistBatch : FinalizedBatch :=
  let statement : EventBatch.Statement :=
    ⟨fixtureCoordinate 2 fixtureOfficer, [assistEvent]⟩
  {
    initialHeads := [crewHead]
    envelope := ⟨statement, fixtureBoundary.batch.batchDigest statement⟩
    receipts := [crewPayload fixtureAssistant]
  }

private def assistantInitial : Projection :=
  Projection.empty ⟨fixtureWorld, fixtureAssistant⟩

theorem finalized_crew_member_gets_role_and_assist_not_personal_salvage :
    (applyFinalizedBatch fixtureBoundary assistantInitial assistBatch).map (fun state =>
      (state.missions.map MissionRecord.participation,
        state.roles.map RoleRecord.role,
        state.assists.map AssistRecord.principal,
        state.ordinarySalvage.length)) =
      .ok ([.assist], [.engineer], [fixtureOfficer], 0) := by
  native_decide

theorem hostile_exact_batch_replay_refused :
    applyFinalizedBatch fixtureBoundary fixtureAfter fixtureBatch =
      .error .staleCoordinate := by
  native_decide

theorem hostile_receipt_reorder_refused :
    applyFinalizedBatch fixtureBoundary fixtureInitial
      { fixtureBatch with receipts :=
        [shipworksPayload, galleyPayload, crewPayload fixtureOfficer] } =
      .error .receiptBinding := by
  native_decide

theorem hostile_nonparticipant_cannot_receive_crew_log :
    let stranger := digestByte 99
    let payload := crewPayload stranger
    let event := fixtureEvent 0 crewHead.stream crewHead.head payload
    let statement : EventBatch.Statement :=
      ⟨fixtureCoordinate 3 fixtureOfficer, [event]⟩
    let input : FinalizedBatch := {
      initialHeads := [crewHead]
      envelope := ⟨statement, fixtureBoundary.batch.batchDigest statement⟩
      receipts := [payload] }
    applyFinalizedBatch fixtureBoundary (Projection.empty ⟨fixtureWorld, stranger⟩) input =
      .error .receiptBinding := by
  native_decide

theorem hostile_automatic_recovery_mutation_refused :
    let source := { fixtureCrewReceipt with recovery :=
      { fixtureCrewReceipt.recovery with
        implementation := .automaticWorldMutation, globalMeterDebit := 1 } }
    let payload : ReceiptPayload := ⟨fixtureOfficer, .crew source⟩
    let event := fixtureEvent 0 crewHead.stream crewHead.head payload
    let statement : EventBatch.Statement :=
      ⟨fixtureCoordinate 4 fixtureOfficer, [event]⟩
    let input : FinalizedBatch := {
      initialHeads := [crewHead]
      envelope := ⟨statement, fixtureBoundary.batch.batchDigest statement⟩
      receipts := [payload] }
    applyFinalizedBatch fixtureBoundary fixtureInitial input = .error .receiptBinding := by
  native_decide

theorem hostile_market_relic_custody_refused :
    let badAuthorization : CrewFieldMissionRuntime.RelicCustodyAuthorization :=
      ⟨⟨8⟩, .market, true, true⟩
    let source := { fixtureCrewReceipt with receipt :=
      { fixtureCrewReceipt.receipt with relicCustody := [badAuthorization] } }
    let payload : ReceiptPayload := ⟨fixtureOfficer, .crew source⟩
    let event := fixtureEvent 0 crewHead.stream crewHead.head payload
    let statement : EventBatch.Statement :=
      ⟨fixtureCoordinate 5 fixtureOfficer, [event]⟩
    let input : FinalizedBatch := {
      initialHeads := [crewHead]
      envelope := ⟨statement, fixtureBoundary.batch.batchDigest statement⟩
      receipts := [payload] }
    applyFinalizedBatch fixtureBoundary fixtureInitial input = .error .receiptBinding := by
  native_decide

theorem hostile_contribution_overflow_refused :
    let source := { fixtureCrewReceipt with receipt :=
      { fixtureCrewReceipt.receipt with contribution :=
        { fixtureCrewReceipt.receipt.contribution with intel := METRIC_LIMIT + 1 } } }
    let payload : ReceiptPayload := ⟨fixtureOfficer, .crew source⟩
    let event := fixtureEvent 0 crewHead.stream crewHead.head payload
    let statement : EventBatch.Statement :=
      ⟨fixtureCoordinate 6 fixtureOfficer, [event]⟩
    let input : FinalizedBatch := {
      initialHeads := [crewHead]
      envelope := ⟨statement, fixtureBoundary.batch.batchDigest statement⟩
      receipts := [payload] }
    applyFinalizedBatch fixtureBoundary fixtureInitial input = .error .receiptBinding := by
  native_decide

theorem hostile_foreign_world_refused :
    let foreignWorld := { fixtureWorld with contentEpoch := ⟨99⟩ }
    applyFinalizedBatch fixtureBoundary
      (Projection.empty ⟨foreignWorld, fixtureOfficer⟩) fixtureBatch =
      .error .wrongWorld := by
  native_decide

#assert_compiled fixture_three_source_batch_is_exactly_projected
#assert_compiled fixture_projection_remains_non_authoritative
#assert_compiled finalized_crew_member_gets_role_and_assist_not_personal_salvage
#assert_compiled hostile_exact_batch_replay_refused
#assert_compiled hostile_receipt_reorder_refused
#assert_compiled hostile_nonparticipant_cannot_receive_crew_log
#assert_compiled hostile_automatic_recovery_mutation_refused
#assert_compiled hostile_market_relic_custody_refused
#assert_compiled hostile_contribution_overflow_refused
#assert_compiled hostile_foreign_world_refused

end Dregg2.Games.PathOfAngels.OfficerLogbook
