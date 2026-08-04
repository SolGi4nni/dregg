/-
# Cartography — asynchronous community mapping from expedition receipts

Cartography is not a second expedition combat loop.  Players contribute exact
observations projected from completed `DeckExpedition.ExtractionReceipt`s, join
independent observations into connections, expose contradictory hazard reports,
and publish beta map revisions.  Commands contain identifiers, never scores,
room definitions, provenance fields, or canon authority.

The authority chain has no public representation-level shortcut.  Upstream, only
the expedition judge can construct an `ExtractionReceipt`.  Here,
`Observation.ofReceipt?` is the only observation producer and accepts a fact only
when its room, hotspot, or hazard is in the activated pack and was visited by that
exact receipt.  The cartography judge alone constructs a `MapRevision` by replaying
the counter-bound notebook, and only revisions can enter a privately normalized
`CommunityMap`.  Source catalogues also come only from validated expedition
configs.  Publication produces an `ActivityOutcome.Checked` beta candidate and
imports no canon-promotion surface.

Individual notebooks are strictly sequenced and counter-bound.  Published
revisions enter a set-union community map whose merge is commutative, associative,
and idempotent, so revision arrival order does not choose the board.  This does
not claim arbitrary command permutation: notebook commands still respect their
submit-before-connect/dispute dependencies.
-/
import Dregg2.Games.PathOfAngels.DeckExpedition
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.Cartography

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DeckGraph
open Dregg2.Games.PathOfAngels.DeckExpedition

set_option autoImplicit false

/-- ADT boundary tooth: Cartography may project receipt accessors, but it must
not be able to construct an expedition receipt.  If the upstream constructor is
made public again, the inner declaration succeeds and this example goes red. -/
theorem extraction_receipt_constructor_is_private : True := by
  fail_if_success
    (have _constructor := DeckExpedition.ExtractionReceipt.mk)
  trivial

abbrev MAX_OBSERVATIONS : Nat := 64
abbrev MAX_OPERATIONS : Nat := 32
abbrev MAX_CONNECTIONS : Nat := 32
abbrev MAX_DISPUTES : Nat := 32

structure ObservationId where
  value : Nat
deriving Repr, DecidableEq

inductive HazardStatus where
  | present
  | cleared
deriving Repr, DecidableEq

inductive Fact where
  | roomSeen (room : RoomId)
  | connectionSeen (hotspot : HotspotId)
  | hazardStatus (hazard : HazardId) (status : HazardStatus)
deriving Repr, DecidableEq

def Fact.targetRoom? (config : DeckExpedition.Config) : Fact → Option RoomId
  | .roomSeen room => some room
  | .connectionSeen hotspot =>
      (DeckGraph.hotspotById? config.raw.graph.pack.hotspots hotspot).map Hotspot.destination
  | .hazardStatus hazard _ =>
      (DeckExpedition.hazardById? config.raw.hazards hazard).map HazardSpec.room

/-- A receipt can report only pack objects it actually reached.  Hazard status is
provisional testimony, but the hazard identity and its room are never invented. -/
def factWitnessedB (config : DeckExpedition.Config)
    (receipt : DeckExpedition.ExtractionReceipt config) : Fact → Bool
  | .roomSeen room => decide (room ∈ receipt.visited)
  | .connectionSeen hotspotId =>
      match DeckGraph.hotspotById? config.raw.graph.pack.hotspots hotspotId with
      | none => false
      | some hotspot =>
          decide (hotspot.source ∈ receipt.visited) &&
          decide (hotspot.destination ∈ receipt.visited)
  | .hazardStatus hazardId _ =>
      match DeckExpedition.hazardById? config.raw.hazards hazardId with
      | none => false
      | some hazard => decide (hazard.room ∈ receipt.visited)

/-! ## Receipt-derived observations and activated source catalogue -/

structure SourceCatalogue where
  private mk ::
  mission : MissionSpec
  pack : PackKey
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  rooms : Finset RoomId
  hotspots : Finset HotspotId
  hazards : Finset HazardId
deriving DecidableEq

def SourceCatalogue.ofExpedition (config : DeckExpedition.Config) : SourceCatalogue where
  mission := config.raw.policy.mission
  pack := config.packKey
  federationId := config.raw.policy.mission.federationId
  contentRoot := config.raw.policy.mission.contentRoot
  activationDigest := config.raw.policy.mission.activationDigest
  contentSession := config.raw.policy.mission.contentSession
  contentEpoch := config.raw.policy.mission.epoch
  rooms := (DeckGraph.roomIds config.raw.graph.pack).toFinset
  hotspots := (DeckGraph.hotspotIds config.raw.graph.pack).toFinset
  hazards := (DeckExpedition.hazardIds config.raw).toFinset

structure Observation where
  private mk ::
  id : ObservationId
  fact : Fact
  sourceMission : MissionSpec
  sourcePack : PackKey
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  originKey : ExpeditionKey
  finalPosition : Position
  receiptTurnsUsed : Nat
  receiptSuppliesSpent : Nat
  receiptRecovered : Finset SalvageId
deriving DecidableEq

/-- The sole public producer of observations. -/
def Observation.ofReceipt? (config : DeckExpedition.Config)
    (receipt : DeckExpedition.ExtractionReceipt config)
    (id : ObservationId) (fact : Fact) : Option Observation :=
  if factWitnessedB config receipt fact then
    some {
      id
      fact
      sourceMission := config.raw.policy.mission
      sourcePack := config.packKey
      federationId := config.raw.policy.mission.federationId
      contentRoot := config.raw.policy.mission.contentRoot
      activationDigest := config.raw.policy.mission.activationDigest
      contentSession := config.raw.policy.mission.contentSession
      contentEpoch := config.raw.policy.mission.epoch
      originKey := receipt.key
      finalPosition := receipt.finalPosition
      receiptTurnsUsed := receipt.turnsUsed
      receiptSuppliesSpent := receipt.suppliesSpent
      receiptRecovered := receipt.recovered
    }
  else none

theorem Observation.ofReceipt_exact_provenance
    (config : DeckExpedition.Config)
    (receipt : DeckExpedition.ExtractionReceipt config)
    (id : ObservationId) (fact : Fact) (observation : Observation)
    (accepted : Observation.ofReceipt? config receipt id fact = some observation) :
    observation.id = id ∧
    observation.fact = fact ∧
    observation.sourceMission = config.raw.policy.mission ∧
    observation.sourcePack = config.packKey ∧
    observation.federationId = config.raw.policy.mission.federationId ∧
    observation.contentRoot = config.raw.policy.mission.contentRoot ∧
    observation.activationDigest = config.raw.policy.mission.activationDigest ∧
    observation.contentSession = config.raw.policy.mission.contentSession ∧
    observation.contentEpoch = config.raw.policy.mission.epoch ∧
    observation.originKey = receipt.key ∧
    observation.finalPosition = receipt.finalPosition ∧
    observation.receiptTurnsUsed = receipt.turnsUsed ∧
    observation.receiptSuppliesSpent = receipt.suppliesSpent ∧
    observation.receiptRecovered = receipt.recovered ∧
    factWitnessedB config receipt fact = true := by
  simp only [Observation.ofReceipt?] at accepted
  split at accepted <;> try contradiction
  injection accepted with heq
  rw [← heq]
  simp_all

def factInSourceB (source : SourceCatalogue) : Fact → Bool
  | .roomSeen room => decide (room ∈ source.rooms)
  | .connectionSeen hotspot => decide (hotspot ∈ source.hotspots)
  | .hazardStatus hazard _ => decide (hazard ∈ source.hazards)

structure OriginFactKey where
  origin : ExpeditionKey
  fact : Fact
deriving DecidableEq

def Observation.originFactKey (observation : Observation) : OriginFactKey :=
  ⟨observation.originKey, observation.fact⟩

/-! ## Activated mapping catalogue -/

/-- Authored authority bridge from one exact expedition source mission to one
exact mapping mission.  Different mission ids are permitted, but neither side
may silently cross federation, content, activation, session, or epoch domains. -/
structure SourceMapBridge where
  sourceMissionId : MissionId
  mapMissionId : MissionId
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
deriving DecidableEq

structure RawConfig where
  mapPolicy : ActivityOutcome.Policy
  revisionArtifact : ArtifactRef
  source : SourceCatalogue
  bridge : SourceMapBridge
  observations : List Observation
  operationBudget : Nat
deriving DecidableEq

def bridgeValidB (raw : RawConfig) : Bool :=
  decide (raw.bridge.sourceMissionId = raw.source.mission.missionId) &&
  decide (raw.bridge.mapMissionId = raw.mapPolicy.mission.missionId) &&
  decide (raw.bridge.federationId = raw.source.federationId) &&
  decide (raw.bridge.federationId = raw.mapPolicy.mission.federationId) &&
  decide (raw.bridge.contentRoot = raw.source.contentRoot) &&
  decide (raw.bridge.contentRoot = raw.mapPolicy.mission.contentRoot) &&
  decide (raw.bridge.activationDigest = raw.source.activationDigest) &&
  decide (raw.bridge.activationDigest = raw.mapPolicy.mission.activationDigest) &&
  decide (raw.bridge.contentSession = raw.source.contentSession) &&
  decide (raw.bridge.contentSession = raw.mapPolicy.mission.contentSession) &&
  decide (raw.bridge.contentEpoch = raw.source.contentEpoch) &&
  decide (raw.bridge.contentEpoch = raw.mapPolicy.mission.epoch)

def observationValidB (raw : RawConfig) (observation : Observation) : Bool :=
  decide (observation.sourceMission = raw.source.mission) &&
  decide (observation.sourcePack = raw.source.pack) &&
  decide (observation.federationId = raw.source.federationId) &&
  decide (observation.contentRoot = raw.source.contentRoot) &&
  decide (observation.activationDigest = raw.source.activationDigest) &&
  decide (observation.contentSession = raw.source.contentSession) &&
  decide (observation.contentEpoch = raw.source.contentEpoch) &&
  decide (observation.originKey.pack = raw.source.pack) &&
  decide (observation.originKey.day = raw.source.contentEpoch) &&
  decide (0 < observation.originKey.counter) &&
  factInSourceB raw.source observation.fact

def configValidB (raw : RawConfig) : Bool :=
  bridgeValidB raw &&
  decide (raw.revisionArtifact ∈ raw.mapPolicy.allowedBeta) &&
  decide (raw.revisionArtifact.missionId = raw.mapPolicy.mission.missionId) &&
  decide (0 < raw.mapPolicy.resultLimit.val) &&
  raw.mapPolicy.mission.acceptsContribution Contribution.zero &&
  decide (raw.observations.length ≤ MAX_OBSERVATIONS) &&
  decide ((raw.observations.map Observation.id).Nodup) &&
  decide ((raw.observations.map Observation.originFactKey).Nodup) &&
  raw.observations.all (observationValidB raw) &&
  decide (0 < raw.operationBudget) &&
  decide (raw.operationBudget ≤ MAX_OPERATIONS)

structure Config where
  raw : RawConfig
  valid : configValidB raw = true

def validateConfig? (raw : RawConfig) : Option Config :=
  if h : configValidB raw = true then some { raw, valid := h } else none

def observationById? (config : Config) (id : ObservationId) : Option Observation :=
  config.raw.observations.find? (fun observation => observation.id = id)

theorem Config.observation_has_exact_source (config : Config)
    (observation : Observation) (member : observation ∈ config.raw.observations) :
    observation.sourceMission = config.raw.source.mission ∧
    observation.sourcePack = config.raw.source.pack ∧
    observation.federationId = config.raw.source.federationId ∧
    observation.contentRoot = config.raw.source.contentRoot ∧
    observation.activationDigest = config.raw.source.activationDigest ∧
    observation.contentSession = config.raw.source.contentSession ∧
    observation.contentEpoch = config.raw.source.contentEpoch ∧
    observation.originKey.pack = config.raw.source.pack ∧
    observation.originKey.day = config.raw.source.contentEpoch ∧
    0 < observation.originKey.counter ∧
    factInSourceB config.raw.source observation.fact = true := by
  have valid := config.valid
  simp only [configValidB, Bool.and_eq_true] at valid
  have hall : config.raw.observations.all (observationValidB config.raw) = true := by
    tauto
  have row := (List.all_eq_true.mp hall) observation member
  simp only [observationValidB, Bool.and_eq_true, decide_eq_true_eq] at row
  tauto

theorem Config.bridge_binds_source_and_map (config : Config) :
    config.raw.bridge.sourceMissionId = config.raw.source.mission.missionId ∧
    config.raw.bridge.mapMissionId = config.raw.mapPolicy.mission.missionId ∧
    config.raw.bridge.federationId = config.raw.source.federationId ∧
    config.raw.bridge.federationId = config.raw.mapPolicy.mission.federationId ∧
    config.raw.bridge.contentRoot = config.raw.source.contentRoot ∧
    config.raw.bridge.contentRoot = config.raw.mapPolicy.mission.contentRoot ∧
    config.raw.bridge.activationDigest = config.raw.source.activationDigest ∧
    config.raw.bridge.activationDigest = config.raw.mapPolicy.mission.activationDigest ∧
    config.raw.bridge.contentSession = config.raw.source.contentSession ∧
    config.raw.bridge.contentSession = config.raw.mapPolicy.mission.contentSession ∧
    config.raw.bridge.contentEpoch = config.raw.source.contentEpoch ∧
    config.raw.bridge.contentEpoch = config.raw.mapPolicy.mission.epoch := by
  have valid := config.valid
  simp only [configValidB, bridgeValidB, Bool.and_eq_true, decide_eq_true_eq] at valid
  tauto

/-! ## Sequenced notebook play -/

/-- Full-width canonical semantic digest of the mapping catalogue.  This is not
a 32-byte arithmetic fold: equality retains the complete source catalogue,
authority bridge, map policy/domain, revision artifact, ordered observation
catalogue, and operation budget.  A compact wire hash may commit to this object,
but it cannot replace this faithful equality boundary. -/
structure CatalogueDigest where
  source : SourceCatalogue
  bridge : SourceMapBridge
  mapPolicy : ActivityOutcome.Policy
  revisionArtifact : ArtifactRef
  observations : List Observation
  operationBudget : Nat
deriving DecidableEq

def RawConfig.catalogueDigest (raw : RawConfig) : CatalogueDigest where
  source := raw.source
  bridge := raw.bridge
  mapPolicy := raw.mapPolicy
  revisionArtifact := raw.revisionArtifact
  observations := raw.observations
  operationBudget := raw.operationBudget

structure SessionKey where
  actorRoot : Digest32
  catalogueDigest : CatalogueDigest
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  missionId : MissionId
  playerKey : Digest32
  playerCounter : Nat
deriving DecidableEq

structure JudgeContext where
  /-- Finalized prestate identity.  The runtime must authenticate this root and
  the freshness of `previousPlayerCounter`; this Lean machine binds both exact
  values into every action session and refuses an out-of-domain next counter. -/
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

/-- The next notebook receipt counter must fit the canonical unsigned 64-bit
PoA player-counter domain. -/
def JudgeContext.nextCounterAdmissibleB (context : JudgeContext) : Bool :=
  decide (context.previousPlayerCounter + 1 < PLAYER_COUNTER_MODULUS)

def sessionKey (config : Config) (context : JudgeContext) : SessionKey where
  actorRoot := context.actorRoot
  catalogueDigest := config.raw.catalogueDigest
  federationId := config.raw.mapPolicy.mission.federationId
  contentSession := config.raw.mapPolicy.mission.contentSession
  contentEpoch := config.raw.mapPolicy.mission.epoch
  missionId := config.raw.mapPolicy.mission.missionId
  playerKey := context.playerKey
  playerCounter := context.previousPlayerCounter + 1

theorem session_key_binds_prestate_and_catalogue
    (config : Config) (context : JudgeContext) :
    (sessionKey config context).actorRoot = context.actorRoot ∧
      (sessionKey config context).catalogueDigest = config.raw.catalogueDigest ∧
      (sessionKey config context).playerCounter = context.previousPlayerCounter + 1 := by
  exact ⟨rfl, rfl, rfl⟩

structure PairKey where
  low : ObservationId
  high : ObservationId
deriving Repr, DecidableEq

def PairKey.canonical (left right : ObservationId) : PairKey :=
  if left.value ≤ right.value then ⟨left, right⟩ else ⟨right, left⟩

inductive Command where
  | submit (observation : ObservationId)
  | connect (left right : ObservationId)
  | dispute (left right : ObservationId)
  | publish
deriving Repr, DecidableEq

structure Action where
  session : SessionKey
  sequence : Nat
  command : Command
deriving DecidableEq

structure State where
  session : SessionKey
  nextSequence : Nat
  operationsSpent : Nat
  submitted : Finset ObservationId
  connections : Finset PairKey
  disputes : Finset PairKey
  published : Bool
deriving DecidableEq

def initialState (config : Config) (context : JudgeContext) : State where
  session := sessionKey config context
  nextSequence := 0
  operationsSpent := 0
  submitted := ∅
  connections := ∅
  disputes := ∅
  published := false

def charged (state : State) : State :=
  { state with
    nextSequence := state.nextSequence + 1
    operationsSpent := state.operationsSpent + 1 }

def sameIndependentConnectionB (config : Config) (state : State)
    (leftId rightId : ObservationId) : Bool :=
  match observationById? config leftId, observationById? config rightId with
  | some left, some right =>
      decide (leftId ≠ rightId) &&
      decide (leftId ∈ state.submitted) &&
      decide (rightId ∈ state.submitted) &&
      (match left.fact, right.fact with
       | .connectionSeen leftHotspot, .connectionSeen rightHotspot =>
           decide (leftHotspot = rightHotspot)
       | _, _ => false) &&
      decide (left.originKey ≠ right.originKey) &&
      decide (left.originKey.playerKey ≠ right.originKey.playerKey) &&
      decide (PairKey.canonical leftId rightId ∉ state.connections)
  | _, _ => false

def contradictoryHazardB (config : Config) (state : State)
    (leftId rightId : ObservationId) : Bool :=
  match observationById? config leftId, observationById? config rightId with
  | some left, some right =>
      decide (leftId ≠ rightId) &&
      decide (leftId ∈ state.submitted) &&
      decide (rightId ∈ state.submitted) &&
      (match left.fact, right.fact with
       | .hazardStatus leftHazard leftStatus, .hazardStatus rightHazard rightStatus =>
           decide (leftHazard = rightHazard) && decide (leftStatus ≠ rightStatus)
       | _, _ => false) &&
      decide (left.originKey ≠ right.originKey) &&
      decide (left.originKey.playerKey ≠ right.originKey.playerKey) &&
      decide (PairKey.canonical leftId rightId ∉ state.disputes)
  | _, _ => false

def publishableB (state : State) : Bool :=
  decide (0 < state.submitted.card) &&
  decide (0 < state.connections.card) &&
  decide (state.connections.card ≤ MAX_CONNECTIONS) &&
  decide (state.disputes.card ≤ MAX_DISPUTES)

def commandStep (config : Config) (state : State) : Command → Option State
  | .submit id =>
      match observationById? config id with
      | none => none
      | some _ =>
          if id ∈ state.submitted then none
          else some { state with submitted := insert id state.submitted }
  | .connect left right =>
      if sameIndependentConnectionB config state left right then
        some { state with connections := insert (PairKey.canonical left right) state.connections }
      else none
  | .dispute left right =>
      if contradictoryHazardB config state left right then
        some { state with disputes := insert (PairKey.canonical left right) state.disputes }
      else none
  | .publish =>
      if publishableB state then some { state with published := true } else none

/-- Wrong domain/counter, replayed sequence, closed publication, exhausted budget,
duplicate submissions, weak triangulations, and fake disputes all refuse. -/
def step (config : Config) (state : State) (action : Action) : Option State :=
  if action.session ≠ state.session then none
  else if action.sequence ≠ state.nextSequence then none
  else if state.published then none
  else if config.raw.operationBudget ≤ state.operationsSpent then none
  else (commandStep config state action.command).map charged

def replay (config : Config) : State → List Action → Option State
  | state, [] => some state
  | state, action :: actions => do
      let next ← step config state action
      replay config next actions

/-! ## Exact beta revision and order-independent community merge -/

/-- Compact publication provenance.  It preserves the stable receipt key and
the receipt projections used by the map, but deliberately does not duplicate
the complete visited set or invent a cryptographic receipt commitment.  A
standalone network verifier must retrieve the constructor-private expedition
receipt by `originKey` (or trust the cartography judge's serialization boundary)
before independently replaying `factWitnessedB`. -/
structure ObservationProvenance where
  observationId : ObservationId
  fact : Fact
  sourceMission : MissionId
  sourcePack : PackKey
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  originKey : ExpeditionKey
  finalPosition : Position
  receiptTurnsUsed : Nat
  receiptSuppliesSpent : Nat
  receiptRecovered : Finset SalvageId
deriving DecidableEq

def Observation.provenance (observation : Observation) : ObservationProvenance where
  observationId := observation.id
  fact := observation.fact
  sourceMission := observation.sourceMission.missionId
  sourcePack := observation.sourcePack
  federationId := observation.federationId
  contentRoot := observation.contentRoot
  activationDigest := observation.activationDigest
  contentSession := observation.contentSession
  contentEpoch := observation.contentEpoch
  originKey := observation.originKey
  finalPosition := observation.finalPosition
  receiptTurnsUsed := observation.receiptTurnsUsed
  receiptSuppliesSpent := observation.receiptSuppliesSpent
  receiptRecovered := observation.receiptRecovered

def submittedObservations (config : Config) (state : State) : List Observation :=
  config.raw.observations.filter (fun observation => decide (observation.id ∈ state.submitted))

def submittedProvenance (config : Config) (state : State) : List ObservationProvenance :=
  (submittedObservations config state).map Observation.provenance

def authoredPairs (config : Config) : List PairKey :=
  config.raw.observations.flatMap fun left =>
    (config.raw.observations.filter fun right => decide (left.id.value < right.id.value)).map
      fun right => PairKey.canonical left.id right.id

def connectionHotspots (config : Config) (state : State) : Finset HotspotId :=
  (authoredPairs config).filterMap (fun pair =>
    if pair ∈ state.connections then do
      let observation ← observationById? config pair.low
      match observation.fact with
      | .connectionSeen hotspot => some hotspot
      | _ => none
    else none) |>.toFinset

structure HazardClaim where
  hazard : HazardId
  status : HazardStatus
deriving DecidableEq

def hazardClaims (config : Config) (state : State) : Finset HazardClaim :=
  (submittedObservations config state).filterMap (fun observation =>
    match observation.fact with
    | .hazardStatus hazard status => some ⟨hazard, status⟩
    | _ => none) |>.toFinset

def disputedHazards (config : Config) (state : State) : Finset HazardId :=
  (authoredPairs config).filterMap (fun pair =>
    if pair ∈ state.disputes then do
      let observation ← observationById? config pair.low
      match observation.fact with
      | .hazardStatus hazard _ => some hazard
      | _ => none
    else none) |>.toFinset

def rawBetaOutcome (config : Config) : ActivityOutcome.Raw where
  contribution := {
    intel := 0, supplies := 0, cohesion := 0, influence := 0, score := 0, relics := [] }
  betaCandidates := [config.raw.revisionArtifact]

theorem raw_beta_outcome_has_no_score (config : Config) :
    (rawBetaOutcome config).contribution.score = 0 := rfl

structure MapRevision (config : Config) where
  private mk ::
  artifact : ArtifactRef
  session : SessionKey
  provenance : List ObservationProvenance
  connections : Finset HotspotId
  hazardClaims : Finset HazardClaim
  disputedHazards : Finset HazardId
  beta : ActivityOutcome.Checked config.raw.mapPolicy

private def terminalRevision? (config : Config) (state : State) : Option (MapRevision config) := do
  if state.published then
    let beta ← ActivityOutcome.validate config.raw.mapPolicy (rawBetaOutcome config)
    some {
      artifact := config.raw.revisionArtifact
      session := state.session
      provenance := submittedProvenance config state
      connections := connectionHotspots config state
      hazardClaims := hazardClaims config state
      disputedHazards := disputedHazards config state
      beta
    }
  else none

/-- The publication boundary always starts from the exact counter-bound initial
state and replays the whole notebook.  A representation-level `State` cannot be
submitted as a revision. -/
def judge (config : Config) (context : JudgeContext)
    (actions : List Action) : Option (MapRevision config) := do
  if context.nextCounterAdmissibleB then
    let final ← replay config (initialState config context) actions
    terminalRevision? config final
  else none

theorem terminal_revision_has_exact_beta_artifact
    (config : Config) (state : State) (revision : MapRevision config)
    (accepted : terminalRevision? config state = some revision) :
    revision.artifact = config.raw.revisionArtifact ∧
      revision.beta.betaCandidates = {config.raw.revisionArtifact} := by
  unfold terminalRevision? at accepted
  split at accepted <;> try contradiction
  cases hbeta : ActivityOutcome.validate config.raw.mapPolicy (rawBetaOutcome config) with
  | none => simp [hbeta] at accepted
  | some beta =>
      rw [hbeta] at accepted
      simp at accepted
      subst revision
      refine ⟨rfl, ?_⟩
      have exact := ActivityOutcome.validate_some_candidates_exact
        config.raw.mapPolicy (rawBetaOutcome config) beta hbeta
      simpa [rawBetaOutcome] using exact

theorem judge_deterministic (config : Config) (context : JudgeContext)
    (actions : List Action) {first second : MapRevision config}
    (hfirst : judge config context actions = some first)
    (hsecond : judge config context actions = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem judge_refuses_exhausted_player_counter
    (config : Config) (context : JudgeContext) (actions : List Action)
    (exhausted : PLAYER_COUNTER_MODULUS ≤ context.previousPlayerCounter + 1) :
    judge config context actions = none := by
  simp [judge, JudgeContext.nextCounterAdmissibleB, Nat.not_lt.mpr exhausted]

theorem judged_revision_has_exact_beta_artifact
    (config : Config) (context : JudgeContext) (actions : List Action)
    (revision : MapRevision config)
    (accepted : judge config context actions = some revision) :
    revision.artifact = config.raw.revisionArtifact ∧
      revision.beta.betaCandidates = {config.raw.revisionArtifact} := by
  unfold judge at accepted
  split at accepted <;> try contradiction
  cases hreplay : replay config (initialState config context) actions with
  | none => simp [hreplay] at accepted
  | some final =>
      rw [hreplay] at accepted
      exact terminal_revision_has_exact_beta_artifact config final revision accepted

theorem submitted_provenance_has_exact_catalogue_origin
    (config : Config) (state : State) (used : ObservationProvenance)
    (member : used ∈ submittedProvenance config state) :
    ∃ observation ∈ config.raw.observations,
      observation.id ∈ state.submitted ∧
      used = observation.provenance ∧
      observation.originKey.pack = config.raw.source.pack ∧
      observation.originKey.day = config.raw.source.contentEpoch ∧
      0 < observation.originKey.counter ∧
      factInSourceB config.raw.source observation.fact = true := by
  simp only [submittedProvenance, List.mem_map] at member
  obtain ⟨observation, filtered, heq⟩ := member
  have authored := (List.mem_filter.mp filtered).1
  have submitted := of_decide_eq_true (List.mem_filter.mp filtered).2
  have exact := config.observation_has_exact_source observation authored
  exact ⟨observation, authored, submitted, heq.symm,
    exact.2.2.2.2.2.2.2.1, exact.2.2.2.2.2.2.2.2.1,
    exact.2.2.2.2.2.2.2.2.2.1, exact.2.2.2.2.2.2.2.2.2.2⟩

def HazardStatus.opposite : HazardStatus → HazardStatus
  | .present => .cleared
  | .cleared => .present

/-- Contradiction is normalized from the complete claim set.  This catches the
asynchronous case where opposite reports arrive in separate revisions. -/
def conflictedHazards (claims : Finset HazardClaim) : Finset HazardId :=
  (claims.filter fun claim =>
    decide (({ hazard := claim.hazard, status := claim.status.opposite } : HazardClaim) ∈ claims))
  |>.image HazardClaim.hazard

/-- Monotone cross-revision accumulator.  Each admitted revision is bounded by
its notebook/config, but this aggregate is intentionally unbounded across an
epoch; deployments must epoch/shard or snapshot it rather than implying a global
fixed cap.  Its private constructor and normalization proof prevent an aggregate
whose dispute set disagrees with its accumulated claims. -/
structure CommunityMap (config : Config) where
  private mk ::
  observations : Finset ObservationProvenance
  connections : Finset HotspotId
  hazardClaims : Finset HazardClaim
  disputedHazards : Finset HazardId
  betaArtifacts : Finset ArtifactRef
  disputes_normalized : disputedHazards = conflictedHazards hazardClaims
deriving DecidableEq

def CommunityMap.empty (config : Config) : CommunityMap config :=
  ⟨∅, ∅, ∅, ∅, ∅, by native_decide⟩

def CommunityMap.ofRevision {config : Config}
    (revision : MapRevision config) : CommunityMap config :=
  ⟨revision.provenance.toFinset, revision.connections, revision.hazardClaims,
    conflictedHazards revision.hazardClaims, {revision.artifact}, rfl⟩

def CommunityMap.merge {config : Config}
    (left right : CommunityMap config) : CommunityMap config :=
  let claims := left.hazardClaims ∪ right.hazardClaims
  ⟨left.observations ∪ right.observations,
   left.connections ∪ right.connections,
   claims,
   conflictedHazards claims,
   left.betaArtifacts ∪ right.betaArtifacts,
   rfl⟩

theorem CommunityMap.disputes_are_exactly_normalized {config : Config}
    (board : CommunityMap config) :
    board.disputedHazards = conflictedHazards board.hazardClaims :=
  board.disputes_normalized

theorem CommunityMap.merge_comm {config : Config}
    (left right : CommunityMap config) : left.merge right = right.merge left := by
  cases left
  cases right
  simp [CommunityMap.merge, Finset.union_comm]

theorem CommunityMap.merge_assoc {config : Config}
    (first second third : CommunityMap config) :
    (first.merge second).merge third = first.merge (second.merge third) := by
  cases first
  cases second
  cases third
  simp [CommunityMap.merge, Finset.union_assoc]

theorem CommunityMap.merge_idempotent {config : Config}
    (board : CommunityMap config) : board.merge board = board := by
  cases board
  rename_i observations connections claims disputes artifacts normalized
  cases normalized
  simp [CommunityMap.merge]

/-! ## General transition laws -/

theorem step_deterministic (config : Config) (state : State) (action : Action)
    {first second : State} (hfirst : step config state action = some first)
    (hsecond : step config state action = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem wrong_session_refuses (config : Config) (state : State) (action : Action)
    (wrong : action.session ≠ state.session) : step config state action = none := by
  simp [step, wrong]

theorem wrong_sequence_refuses (config : Config) (state : State) (action : Action)
    (wrong : action.sequence ≠ state.nextSequence) : step config state action = none := by
  by_cases hs : action.session = state.session <;> simp [step, hs, wrong]

theorem duplicate_submission_refuses (config : Config) (state : State)
    (id : ObservationId) (present : id ∈ state.submitted) :
    commandStep config state (.submit id) = none := by
  simp only [commandStep]
  cases observationById? config id <;> simp [present]

theorem exhausted_budget_refuses (config : Config) (state : State)
    (action : Action)
    (spent : config.raw.operationBudget ≤ state.operationsSpent) :
    step config state action = none := by
  by_cases hs : action.session = state.session
  · by_cases hq : action.sequence = state.nextSequence
    · by_cases hp : state.published
      · simp [step, hs, hq, hp]
      · simp [step, hs, hq, hp, spent]
    · simp [step, hs, hq]
  · simp [step, hs]

theorem commandStep_preserves_counters (config : Config) (state : State)
    (command : Command) {next : State}
    (accepted : commandStep config state command = some next) :
    next.nextSequence = state.nextSequence ∧
      next.operationsSpent = state.operationsSpent := by
  cases command with
  | submit id =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      injection accepted with heq
      rw [← heq]
      exact ⟨rfl, rfl⟩
  | connect left right =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      injection accepted with heq
      rw [← heq]
      exact ⟨rfl, rfl⟩
  | dispute left right =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      injection accepted with heq
      rw [← heq]
      exact ⟨rfl, rfl⟩
  | publish =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      injection accepted with heq
      rw [← heq]
      exact ⟨rfl, rfl⟩

theorem accepted_step_advances_sequence_and_cost
    (config : Config) (state : State) (action : Action) {next : State}
    (accepted : step config state action = some next) :
    next.nextSequence = state.nextSequence + 1 ∧
    next.operationsSpent = state.operationsSpent + 1 := by
  unfold step at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases hcommand : commandStep config state action.command with
  | none => simp [hcommand] at accepted
  | some provisional =>
      simp only [hcommand, Option.map_some, Option.some.injEq] at accepted
      rw [← accepted]
      have preserved := commandStep_preserves_counters config state action.command hcommand
      simp [charged, preserved.1, preserved.2]

theorem accepted_step_respects_operation_budget
    (config : Config) (state : State) (action : Action) {next : State}
    (accepted : step config state action = some next) :
    next.operationsSpent ≤ config.raw.operationBudget := by
  have advance := (accepted_step_advances_sequence_and_cost
    config state action accepted).2
  have before : state.operationsSpent < config.raw.operationBudget := by
    by_contra notBefore
    have spent : config.raw.operationBudget ≤ state.operationsSpent :=
      Nat.le_of_not_gt notBefore
    have refused := exhausted_budget_refuses config state action spent
    rw [refused] at accepted
    contradiction
  omega

/-! ## Cooperative and adversarial executable fixture -/

def digestFilled (value : Fin 256) : Digest32 where
  bytes := List.replicate 32 value
  length_eq := by simp

def playerA : Digest32 := digestFilled 1
def playerB : Digest32 := digestFilled 2
def cartographer : Digest32 := digestFilled 3

def expeditionKeyFor (player : Digest32) : ExpeditionKey where
  pack := DeckExpedition.fixtureConfig.packKey
  playerKey := player
  day := DeckExpedition.fixtureConfig.raw.day
  counter := 1

def expeditionActionsFor (player : Digest32) : List DeckExpedition.Action :=
  [ .begin (expeditionKeyFor player) DeckExpedition.fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront DeckExpedition.fixtureHazard.id DeckExpedition.fixtureContainment.id
  , .traverse DeckGraph.fixtureWrap.id
  , .recover DeckExpedition.fixtureSalvage.id DeckExpedition.fixtureEngineer.id
  , .traverse DeckGraph.fixtureMirror.id
  , .survey DeckExpedition.fixtureArtifact DeckExpedition.fixturePathfinder.id
  , .traverse DeckGraph.fixturePhase.id
  , .extract ]

def expeditionReceipt? (player : Digest32) :
    Option (DeckExpedition.ExtractionReceipt DeckExpedition.fixtureConfig) :=
  match DeckExpedition.replay DeckExpedition.fixtureConfig
      (expeditionActionsFor player).length
      (DeckExpedition.initialState DeckExpedition.fixtureConfig player)
      (expeditionActionsFor player) with
  | some (_, [receipt]) => some receipt
  | _ => none

theorem playerA_receipt_exists : (expeditionReceipt? playerA).isSome = true := by native_decide
theorem playerB_receipt_exists : (expeditionReceipt? playerB).isSome = true := by native_decide

def receiptA : DeckExpedition.ExtractionReceipt DeckExpedition.fixtureConfig :=
  (expeditionReceipt? playerA).get playerA_receipt_exists

def receiptB : DeckExpedition.ExtractionReceipt DeckExpedition.fixtureConfig :=
  (expeditionReceipt? playerB).get playerB_receipt_exists

def observation? (receipt : DeckExpedition.ExtractionReceipt DeckExpedition.fixtureConfig)
    (id : Nat) (fact : Fact) : Option Observation :=
  Observation.ofReceipt? DeckExpedition.fixtureConfig receipt ⟨id⟩ fact

def roomObservation? := observation? receiptA 0 (.roomSeen DeckGraph.fixtureRoomA.id)
def connectionA? := observation? receiptA 1 (.connectionSeen DeckGraph.fixtureOneWay.id)
def connectionB? := observation? receiptB 2 (.connectionSeen DeckGraph.fixtureOneWay.id)
def hazardPresent? := observation? receiptA 3
  (.hazardStatus DeckExpedition.fixtureHazard.id .present)
def hazardCleared? := observation? receiptB 4
  (.hazardStatus DeckExpedition.fixtureHazard.id .cleared)
def extractionObservation? := observation? receiptB 5
  (.roomSeen DeckGraph.fixtureExtraction.id)

def allObservationsExistB : Bool :=
  roomObservation?.isSome && connectionA?.isSome && connectionB?.isSome &&
  hazardPresent?.isSome && hazardCleared?.isSome && extractionObservation?.isSome

theorem fixture_receipted_observations_exist : allObservationsExistB = true := by native_decide

def fixtureObservations : List Observation :=
  [ roomObservation?.get (by native_decide)
  , connectionA?.get (by native_decide)
  , connectionB?.get (by native_decide)
  , hazardPresent?.get (by native_decide)
  , hazardCleared?.get (by native_decide)
  , extractionObservation?.get (by native_decide) ]

def fixtureBridge : SourceMapBridge where
  sourceMissionId := DeckExpedition.fixtureMission.missionId
  mapMissionId := DeckExpedition.fixturePolicy.mission.missionId
  federationId := DeckExpedition.fixtureMission.federationId
  contentRoot := DeckExpedition.fixtureMission.contentRoot
  activationDigest := DeckExpedition.fixtureMission.activationDigest
  contentSession := DeckExpedition.fixtureMission.contentSession
  contentEpoch := DeckExpedition.fixtureMission.epoch

def fixtureRawConfig : RawConfig where
  mapPolicy := DeckExpedition.fixturePolicy
  revisionArtifact := DeckExpedition.fixtureArtifact
  source := SourceCatalogue.ofExpedition DeckExpedition.fixtureConfig
  bridge := fixtureBridge
  observations := fixtureObservations
  operationBudget := 12

theorem fixture_config_valid : configValidB fixtureRawConfig = true := by native_decide
def fixtureConfig : Config := ⟨fixtureRawConfig, fixture_config_valid⟩

def fixtureContext : JudgeContext :=
  { actorRoot := digestFilled 8, playerKey := cartographer, previousPlayerCounter := 40 }

def exhaustedCounterContext : JudgeContext :=
  { actorRoot := digestFilled 8
    playerKey := cartographer
    previousPlayerCounter := PLAYER_COUNTER_MODULUS - 1 }

def action (sequence : Nat) (command : Command) : Action :=
  { session := sessionKey fixtureConfig fixtureContext, sequence, command }

def cooperativeActions : List Action :=
  [ action 0 (.submit ⟨0⟩)
  , action 1 (.submit ⟨1⟩)
  , action 2 (.submit ⟨2⟩)
  , action 3 (.connect ⟨1⟩ ⟨2⟩)
  , action 4 (.submit ⟨3⟩)
  , action 5 (.submit ⟨4⟩)
  , action 6 (.dispute ⟨3⟩ ⟨4⟩)
  , action 7 (.submit ⟨5⟩)
  , action 8 .publish ]

def reorderedActions : List Action :=
  [ action 0 (.submit ⟨2⟩)
  , action 1 (.submit ⟨1⟩)
  , action 2 (.connect ⟨2⟩ ⟨1⟩)
  , action 3 (.submit ⟨4⟩)
  , action 4 (.submit ⟨3⟩)
  , action 5 (.dispute ⟨4⟩ ⟨3⟩)
  , action 6 (.submit ⟨5⟩)
  , action 7 (.submit ⟨0⟩)
  , action 8 .publish ]

/-- Two independently publishable revisions carry opposite hazard claims.  The
contradiction exists only after their asynchronous community merge. -/
def presentOnlyActions : List Action :=
  [ action 0 (.submit ⟨1⟩)
  , action 1 (.submit ⟨2⟩)
  , action 2 (.connect ⟨1⟩ ⟨2⟩)
  , action 3 (.submit ⟨3⟩)
  , action 4 .publish ]

def clearedOnlyActions : List Action :=
  [ action 0 (.submit ⟨1⟩)
  , action 1 (.submit ⟨2⟩)
  , action 2 (.connect ⟨1⟩ ⟨2⟩)
  , action 3 (.submit ⟨4⟩)
  , action 4 .publish ]

def revisionFor? (actions : List Action) : Option (MapRevision fixtureConfig) := do
  judge fixtureConfig fixtureContext actions

theorem fixture_cooperative_revision_publishes :
    (revisionFor? cooperativeActions).isSome = true := by native_decide

theorem fixture_max_player_counter_refuses_publication :
    judge fixtureConfig exhaustedCounterContext cooperativeActions = none := by
  native_decide

def communityFor? (actions : List Action) : Option (CommunityMap fixtureConfig) :=
  (revisionFor? actions).map CommunityMap.ofRevision

/-- Semantic map output is independent of the two legal browser orderings. -/
theorem fixture_reordered_play_has_same_community_map :
    communityFor? cooperativeActions = communityFor? reorderedActions := by
  native_decide

def splitRevisionConflictB : Bool :=
  match communityFor? presentOnlyActions, communityFor? clearedOnlyActions with
  | some presentBoard, some clearedBoard =>
      decide (DeckExpedition.fixtureHazard.id ∉ presentBoard.disputedHazards) &&
      decide (DeckExpedition.fixtureHazard.id ∉ clearedBoard.disputedHazards) &&
      decide (DeckExpedition.fixtureHazard.id ∈
        (presentBoard.merge clearedBoard).disputedHazards) &&
      decide (presentBoard.merge clearedBoard = clearedBoard.merge presentBoard)
  | _, _ => false

theorem fixture_separate_revisions_normalize_cross_claim_dispute :
    splitRevisionConflictB = true := by native_decide

def reorderedCatalogueRaw : RawConfig :=
  { fixtureRawConfig with observations := fixtureRawConfig.observations.reverse }

theorem reordered_catalogue_config_valid : configValidB reorderedCatalogueRaw = true := by
  native_decide

def reorderedCatalogueConfig : Config :=
  ⟨reorderedCatalogueRaw, reordered_catalogue_config_valid⟩

theorem fixture_catalogue_digest_moves_with_observation_order :
    fixtureConfig.raw.catalogueDigest ≠ reorderedCatalogueConfig.raw.catalogueDigest := by
  native_decide

/-- An ID-only action signed for one catalogue cannot be replayed against a
different catalogue in the same federation/content/player/counter domain. -/
theorem fixture_cross_catalogue_session_replay_refuses :
    step reorderedCatalogueConfig
      (initialState reorderedCatalogueConfig fixtureContext)
      (action 0 (.submit ⟨0⟩)) = none := by
  native_decide

def phantomRoomRefusedB : Bool :=
  (observation? receiptA 99 (.roomSeen ⟨999_999⟩)).isNone

def phantomHotspotRefusedB : Bool :=
  (observation? receiptA 99 (.connectionSeen ⟨999_999⟩)).isNone

def phantomHazardRefusedB : Bool :=
  (observation? receiptA 99 (.hazardStatus ⟨999_999⟩ .present)).isNone

def hostilePlayRefusalsB : Bool :=
  let initial := initialState fixtureConfig fixtureContext
  let first := action 0 (.submit ⟨1⟩)
  match step fixtureConfig initial first with
  | none => false
  | some afterFirst =>
      decide (step fixtureConfig afterFirst first = none) &&
      decide (step fixtureConfig afterFirst (action 1 (.submit ⟨1⟩)) = none) &&
      decide (step fixtureConfig afterFirst (action 1 (.connect ⟨1⟩ ⟨1⟩)) = none) &&
      decide (step fixtureConfig afterFirst (action 1 (.dispute ⟨3⟩ ⟨4⟩)) = none) &&
      decide (step fixtureConfig afterFirst (action 1 .publish) = none)

theorem fixture_phantom_objects_refuse :
    phantomRoomRefusedB && phantomHotspotRefusedB && phantomHazardRefusedB = true := by
  native_decide

theorem fixture_replays_weak_links_and_early_publish_refuse :
    hostilePlayRefusalsB = true := by native_decide

def duplicateOriginFactRaw : RawConfig :=
  { fixtureRawConfig with
    observations := fixtureObservations ++
      [{ connectionA?.get (by native_decide) with id := ⟨60⟩ }] }

theorem fixture_duplicate_origin_fact_refuses :
    configValidB duplicateOriginFactRaw = false := by native_decide

def wrongFederationSource : SourceCatalogue :=
  { fixtureRawConfig.source with federationId := digestFilled 200 }

def wrongFederationRaw : RawConfig :=
  { fixtureRawConfig with source := wrongFederationSource }

theorem fixture_wrong_federation_provenance_refuses :
    configValidB wrongFederationRaw = false := by native_decide

#assert_axioms extraction_receipt_constructor_is_private
#assert_axioms Observation.ofReceipt_exact_provenance
#assert_axioms Config.observation_has_exact_source
#assert_axioms Config.bridge_binds_source_and_map
#assert_axioms session_key_binds_prestate_and_catalogue
#assert_axioms submitted_provenance_has_exact_catalogue_origin
#assert_axioms raw_beta_outcome_has_no_score
#assert_axioms terminal_revision_has_exact_beta_artifact
#assert_axioms judge_deterministic
#assert_axioms judge_refuses_exhausted_player_counter
#assert_axioms judged_revision_has_exact_beta_artifact
#assert_axioms CommunityMap.merge_comm
#assert_axioms CommunityMap.merge_assoc
#assert_axioms CommunityMap.merge_idempotent
#assert_axioms CommunityMap.disputes_are_exactly_normalized
#assert_axioms step_deterministic
#assert_axioms wrong_session_refuses
#assert_axioms wrong_sequence_refuses
#assert_axioms duplicate_submission_refuses
#assert_axioms exhausted_budget_refuses
#assert_axioms commandStep_preserves_counters
#assert_axioms accepted_step_advances_sequence_and_cost
#assert_axioms accepted_step_respects_operation_budget

#assert_compiled playerA_receipt_exists
#assert_compiled playerB_receipt_exists
#assert_compiled fixture_receipted_observations_exist
#assert_compiled fixture_config_valid
#assert_compiled fixture_cooperative_revision_publishes
#assert_compiled fixture_max_player_counter_refuses_publication
#assert_compiled fixture_reordered_play_has_same_community_map
#assert_compiled fixture_separate_revisions_normalize_cross_claim_dispute
#assert_compiled reordered_catalogue_config_valid
#assert_compiled fixture_catalogue_digest_moves_with_observation_order
#assert_compiled fixture_cross_catalogue_session_replay_refuses
#assert_compiled fixture_phantom_objects_refuse
#assert_compiled fixture_replays_weak_links_and_early_publish_refuse
#assert_compiled fixture_duplicate_origin_fact_refuses
#assert_compiled fixture_wrong_federation_provenance_refuses

end Dregg2.Games.PathOfAngels.Cartography
