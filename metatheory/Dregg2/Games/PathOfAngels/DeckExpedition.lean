/-
# DeckExpedition — persistent micro-scale exploration of the Khovokhi

The deck pack owns topology.  This module owns an expedition over that topology:
an officer party, a strict daily counter, bounded turns and operational supplies,
authored hazards, persistent injuries, per-object salvage custody, and bounded
beta-canon discovery candidates.

Discovery, custody, settlement, and canon are deliberately distinct.  A successful
extraction produces an `ActivityOutcome.Checked` and a custody receipt.  It cannot
promote canon and it cannot mint a Bazaar asset.
-/
import Dregg2.Games.PathOfAngels.ActivityOutcome
import Dregg2.Games.PathOfAngels.DeckGraph
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.DeckExpedition

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DeckGraph

set_option autoImplicit false

abbrev MAX_PARTY : Nat := 4
abbrev MAX_HAZARDS : Nat := 64
abbrev MAX_SALVAGE : Nat := 64
abbrev MAX_DISCOVERIES : Nat := 64
abbrev MAX_DAILY_RUNS : Nat := 16
abbrev MAX_TURNS : Nat := DeckGraph.MAX_NAVIGATION_FUEL
abbrev MAX_OPERATIONAL_SUPPLIES : Nat := 256
abbrev TREATMENT_SUPPLY_COST : Nat := 1

structure OfficerId where
  value : Nat
deriving Repr, DecidableEq

structure HazardId where
  value : Nat
deriving Repr, DecidableEq

structure SalvageId where
  value : Nat
deriving Repr, DecidableEq

inductive OfficerRole where
  | pathfinder
  | engineer
  | containment
  | medic
deriving Repr, DecidableEq

structure OfficerProfile where
  id : OfficerId
  role : OfficerRole
deriving Repr, DecidableEq

/-- Injury 3 means unavailable for non-medical actions.  Hazards saturate at this
declared terminal severity; treatment is the only transition that lowers it. -/
abbrev Injury := Fin 4

structure OfficerState where
  id : OfficerId
  injury : Injury
deriving Repr, DecidableEq

structure HazardSpec where
  id : HazardId
  room : RoomId
  damage : Fin 4
  supplyCost : Nat
deriving Repr, DecidableEq

structure SalvageSpec where
  id : SalvageId
  room : RoomId
  relic : RelicId
deriving Repr, DecidableEq

structure DiscoverySpec where
  room : RoomId
  artifact : ArtifactRef
deriving DecidableEq

/-- One row per authored salvage object.  Custody is a sum, not an ordered code:
an object exists in exactly the location named by its one record. -/
inductive Custody where
  | onDeck (room : RoomId)
  | carried (officer : OfficerId)
  | secured
deriving Repr, DecidableEq

structure SalvageRecord where
  id : SalvageId
  custody : Custody
deriving Repr, DecidableEq

/-- A complete pack identity.  Bare room and pack ids are intentionally not replay
domains because authored ids may recur in later content epochs. -/
structure PackKey where
  packId : PackId
  activation : ActivationIdentity
deriving DecidableEq

structure ExpeditionKey where
  pack : PackKey
  playerKey : Digest32
  day : EpochId
  counter : Nat
deriving DecidableEq

structure RawConfig where
  graph : ValidatedPack
  policy : ActivityOutcome.Policy
  day : EpochId
  officers : List OfficerProfile
  hazards : List HazardSpec
  salvage : List SalvageSpec
  discoveries : List DiscoverySpec
  dailyRunBudget : Nat
  turnBudget : Nat
  operationalSupplyBudget : Nat
  baseContribution : Contribution

def packKeyRaw (raw : RawConfig) : PackKey where
  packId := raw.graph.pack.packId
  activation := raw.graph.pack.activation

def officerIds (raw : RawConfig) : List OfficerId :=
  raw.officers.map OfficerProfile.id

def officerRoles (raw : RawConfig) : List OfficerRole :=
  raw.officers.map OfficerProfile.role

def hazardIds (raw : RawConfig) : List HazardId :=
  raw.hazards.map HazardSpec.id

def salvageIds (raw : RawConfig) : List SalvageId :=
  raw.salvage.map SalvageSpec.id

def salvageRelics (raw : RawConfig) : List RelicId :=
  raw.salvage.map SalvageSpec.relic

def discoveryArtifacts (raw : RawConfig) : List ArtifactRef :=
  raw.discoveries.map DiscoverySpec.artifact

/-- Executable check for everything whose identity or limit must be committed
before play. -/
def configValidB (raw : RawConfig) : Bool :=
  decide (raw.day = raw.policy.mission.epoch) &&
  decide (raw.policy.mission.federationId = raw.graph.pack.activation.federationId) &&
  decide (raw.policy.mission.contentRoot = raw.graph.pack.activation.contentRoot) &&
  decide (raw.policy.mission.activationDigest = raw.graph.pack.activation.activationDigest) &&
  decide (raw.policy.mission.contentSession = raw.graph.pack.activation.contentSession) &&
  decide (raw.policy.mission.epoch = raw.graph.pack.activation.contentEpoch) &&
  !raw.officers.isEmpty &&
  decide (raw.officers.length ≤ MAX_PARTY) &&
  decide (officerIds raw).Nodup &&
  decide (officerRoles raw).Nodup &&
  decide (raw.hazards.length ≤ MAX_HAZARDS) &&
  decide (hazardIds raw).Nodup &&
  raw.hazards.all (fun hazard =>
    DeckGraph.hasRoom raw.graph.pack hazard.room &&
    decide (0 < hazard.damage.val) &&
    decide (hazard.supplyCost ≤ raw.operationalSupplyBudget)) &&
  decide (raw.salvage.length ≤ MAX_SALVAGE) &&
  decide (salvageIds raw).Nodup &&
  decide (salvageRelics raw).Nodup &&
  raw.salvage.all (fun item =>
    DeckGraph.hasRoom raw.graph.pack item.room &&
    decide (item.relic ∈ raw.policy.mission.allowedRelics)) &&
  decide (raw.salvage.length ≤ raw.policy.mission.budget.relics.val) &&
  decide (raw.discoveries.length ≤ MAX_DISCOVERIES) &&
  decide (discoveryArtifacts raw).Nodup &&
  raw.discoveries.all (fun discovery =>
    DeckGraph.hasRoom raw.graph.pack discovery.room &&
    decide (discovery.artifact ∈ raw.policy.allowedBeta)) &&
  decide (raw.discoveries.length ≤ raw.policy.resultLimit.val) &&
  decide (0 < raw.dailyRunBudget) &&
  decide (raw.dailyRunBudget ≤ MAX_DAILY_RUNS) &&
  decide (0 < raw.turnBudget) &&
  decide (raw.turnBudget ≤ MAX_TURNS) &&
  decide (raw.operationalSupplyBudget ≤ MAX_OPERATIONAL_SUPPLIES) &&
  decide (raw.baseContribution.relics = ∅) &&
  raw.policy.mission.acceptsContribution raw.baseContribution

structure Config where
  raw : RawConfig
  valid : configValidB raw = true

def validateConfig? (raw : RawConfig) : Option Config :=
  if h : configValidB raw = true then some { raw, valid := h } else none

def Config.packKey (cfg : Config) : PackKey := packKeyRaw cfg.raw

structure RunState where
  key : ExpeditionKey
  position : Position
  party : List OfficerId
  turnsUsed : Nat
  suppliesSpent : Nat
  visited : Finset RoomId
  resolvedHazards : Finset HazardId
  discoveries : Finset ArtifactRef
deriving DecidableEq

structure State where
  playerKey : Digest32
  day : EpochId
  runsUsed : Nat
  nextCounter : Nat
  consumed : Finset ExpeditionKey
  officers : List OfficerState
  visited : Finset RoomId
  salvage : List SalvageRecord
  active : Option RunState
deriving DecidableEq

def profileById? : List OfficerProfile → OfficerId → Option OfficerProfile
  | [], _ => none
  | profile :: profiles, id =>
      if profile.id = id then some profile else profileById? profiles id

def officerById? : List OfficerState → OfficerId → Option OfficerState
  | [], _ => none
  | officer :: officers, id =>
      if officer.id = id then some officer else officerById? officers id

def hazardById? : List HazardSpec → HazardId → Option HazardSpec
  | [], _ => none
  | hazard :: hazards, id =>
      if hazard.id = id then some hazard else hazardById? hazards id

def salvageSpecById? : List SalvageSpec → SalvageId → Option SalvageSpec
  | [], _ => none
  | item :: items, id =>
      if item.id = id then some item else salvageSpecById? items id

def discoveryByArtifact? : List DiscoverySpec → ArtifactRef → Option DiscoverySpec
  | [], _ => none
  | discovery :: discoveries, artifact =>
      if discovery.artifact = artifact then some discovery
      else discoveryByArtifact? discoveries artifact

def salvageRecordById? : List SalvageRecord → SalvageId → Option SalvageRecord
  | [], _ => none
  | item :: items, id =>
      if item.id = id then some item else salvageRecordById? items id

def initialOfficers (raw : RawConfig) : List OfficerState :=
  raw.officers.map fun profile => { id := profile.id, injury := 0 }

def initialSalvage (raw : RawConfig) : List SalvageRecord :=
  raw.salvage.map fun item => { id := item.id, custody := .onDeck item.room }

def initialState (cfg : Config) (playerKey : Digest32) : State where
  playerKey
  day := cfg.raw.day
  runsUsed := 0
  nextCounter := 1
  consumed := ∅
  officers := initialOfficers cfg.raw
  visited := ∅
  salvage := initialSalvage cfg.raw
  active := none

def partyValidB (cfg : Config) (state : State) (party : List OfficerId) : Bool :=
  !party.isEmpty && decide (party.length ≤ MAX_PARTY) && decide party.Nodup &&
  party.all fun id =>
    match officerById? state.officers id, profileById? cfg.raw.officers id with
    | some officer, some profile =>
        officer.id == id && profile.id == id && decide (officer.injury.val < 3)
    | _, _ => false

def custodyHomeValidB (cfg : Config) (state : State) : Bool :=
  state.salvage.all fun item =>
    match item.custody with
    | .onDeck room =>
        match salvageSpecById? cfg.raw.salvage item.id with
        | some spec => spec.room == room
        | none => false
    | .carried officer => decide (officer ∈ state.officers.map OfficerState.id)
    | .secured => true

def inactiveCustodyValidB (state : State) : Bool :=
  state.salvage.all fun item =>
    match item.custody with
    | .carried _ => false
    | _ => true

def carriedCustodyValidB (run : RunState) (state : State) : Bool :=
  state.salvage.all fun item =>
    match item.custody with
    | .carried officer => decide (officer ∈ run.party)
    | _ => true

def activeValidB (cfg : Config) (state : State) (run : RunState) : Bool :=
  decide (run.key ∈ state.consumed) &&
  decide (run.key.pack = cfg.packKey) &&
  decide (run.key.playerKey = state.playerKey) &&
  decide (run.key.day = state.day) &&
  DeckGraph.hasRoom cfg.raw.graph.pack run.position.room &&
  partyValidB cfg state run.party &&
  decide (run.turnsUsed ≤ cfg.raw.turnBudget) &&
  decide (run.suppliesSpent ≤ cfg.raw.operationalSupplyBudget) &&
  decide (run.position.room ∈ run.visited) &&
  decide (run.visited ⊆ state.visited) &&
  decide (run.resolvedHazards ⊆ (hazardIds cfg.raw).toFinset) &&
  decide (run.discoveries ⊆ (discoveryArtifacts cfg.raw).toFinset) &&
  carriedCustodyValidB run state

def validStateB (cfg : Config) (state : State) : Bool :=
  decide (state.day = cfg.raw.day) &&
  decide (state.runsUsed ≤ cfg.raw.dailyRunBudget) &&
  decide (state.nextCounter = state.runsUsed + 1) &&
  decide (state.consumed.card = state.runsUsed) &&
  decide (∀ key ∈ state.consumed,
    key.pack = cfg.packKey ∧ key.playerKey = state.playerKey ∧ key.day = state.day) &&
  decide (state.officers.map OfficerState.id = officerIds cfg.raw) &&
  decide (state.salvage.map SalvageRecord.id = salvageIds cfg.raw) &&
  decide (state.salvage.map SalvageRecord.id).Nodup &&
  decide (∀ room ∈ state.visited, room ∈ DeckGraph.roomIds cfg.raw.graph.pack) &&
  custodyHomeValidB cfg state &&
  match state.active with
  | none => inactiveCustodyValidB state
  | some run => activeValidB cfg state run

def officerHasRoleB (cfg : Config) (id : OfficerId) (role : OfficerRole) : Bool :=
  match profileById? cfg.raw.officers id with
  | some profile => profile.role == role
  | none => false

def officerCanActB (state : State) (id : OfficerId) : Bool :=
  match officerById? state.officers id with
  | some officer => decide (officer.injury.val < 3)
  | none => false

def officerReadyForB (cfg : Config) (state : State) (run : RunState)
    (id : OfficerId) (role : OfficerRole) : Bool :=
  decide (id ∈ run.party) && officerHasRoleB cfg id role && officerCanActB state id

def unresolvedHazardAtB (cfg : Config) (run : RunState) : Bool :=
  cfg.raw.hazards.any fun hazard =>
    hazard.room == run.position.room && decide (hazard.id ∉ run.resolvedHazards)

def withinTurnB (cfg : Config) (run : RunState) : Bool :=
  decide (run.turnsUsed < cfg.raw.turnBudget)

def injuryAfter (injury damage : Injury) : Injury :=
  ⟨min 3 (injury.val + damage.val), by omega⟩

def injuryAfterTreatment (injury : Injury) : Injury :=
  ⟨injury.val - 1, by omega⟩

def updateOfficerInjury (officers : List OfficerState) (id : OfficerId)
    (injury : Injury) : List OfficerState :=
  officers.map fun officer =>
    if officer.id = id then { officer with injury } else officer

def setCustody (items : List SalvageRecord) (id : SalvageId)
    (custody : Custody) : List SalvageRecord :=
  items.map fun item => if item.id = id then { item with custody } else item

def secureCarried (items : List SalvageRecord) : List SalvageRecord :=
  items.map fun item =>
    match item.custody with
    | .carried _ => { item with custody := .secured }
    | _ => item

def restoreCarried (cfg : Config) (items : List SalvageRecord) : List SalvageRecord :=
  items.map fun item =>
    match item.custody with
    | .carried _ =>
        match salvageSpecById? cfg.raw.salvage item.id with
        | some spec => { item with custody := .onDeck spec.room }
        | none => item
    | _ => item

def carriedRecords (state : State) : List SalvageRecord :=
  state.salvage.filter fun item =>
    match item.custody with
    | .carried _ => true
    | _ => false

def carriedRelics (cfg : Config) (state : State) : List RelicId :=
  (carriedRecords state).filterMap fun item =>
    (salvageSpecById? cfg.raw.salvage item.id).map SalvageSpec.relic

def carriedIds (state : State) : Finset SalvageId :=
  ((carriedRecords state).map SalvageRecord.id).toFinset

def rawOutcome (cfg : Config) (state : State) (run : RunState) : ActivityOutcome.Raw where
  contribution := {
    intel := cfg.raw.baseContribution.intel.val
    supplies := cfg.raw.baseContribution.supplies.val
    cohesion := cfg.raw.baseContribution.cohesion.val
    influence := cfg.raw.baseContribution.influence.val
    score := cfg.raw.baseContribution.score.val
    relics := carriedRelics cfg state
  }
  betaCandidates :=
    (cfg.raw.discoveries.filter fun discovery =>
      decide (discovery.artifact ∈ run.discoveries)).map DiscoverySpec.artifact

structure ExtractionReceipt (cfg : Config) where
  key : ExpeditionKey
  finalPosition : Position
  turnsUsed : Nat
  suppliesSpent : Nat
  visited : Finset RoomId
  recovered : Finset SalvageId
  outcome : ActivityOutcome.Checked cfg.raw.policy
  at_authored_extraction : finalPosition.room = cfg.raw.graph.pack.extraction
  turns_bounded : turnsUsed ≤ cfg.raw.turnBudget
deriving DecidableEq

inductive Action where
  | begin (key : ExpeditionKey) (party : List OfficerId)
  | traverse (hotspot : HotspotId)
  | confront (hazard : HazardId) (officer : OfficerId)
  | survey (artifact : ArtifactRef) (officer : OfficerId)
  | recover (salvage : SalvageId) (officer : OfficerId)
  | treat (medic target : OfficerId)
  | extract
  | withdraw
deriving DecidableEq

structure StepResult (cfg : Config) where
  state : State
  receipt : Option (ExtractionReceipt cfg)
deriving DecidableEq

private def beginTransition (cfg : Config) (state : State)
    (key : ExpeditionKey) (party : List OfficerId) : Option (StepResult cfg) :=
  if state.active.isSome then none
  else if key.pack != cfg.packKey then none
  else if key.playerKey != state.playerKey then none
  else if key.day != state.day then none
  else if key.counter != state.nextCounter then none
  else if key ∈ state.consumed then none
  else if state.runsUsed ≥ cfg.raw.dailyRunBudget then none
  else if partyValidB cfg state party then
    let run : RunState := {
      key
      position := DeckGraph.initialPosition cfg.raw.graph.pack
      party
      turnsUsed := 0
      suppliesSpent := 0
      visited := {cfg.raw.graph.pack.entry}
      resolvedHazards := ∅
      discoveries := ∅
    }
    some {
      state := {
        state with
        runsUsed := state.runsUsed + 1
        nextCounter := state.nextCounter + 1
        consumed := insert key state.consumed
        visited := insert cfg.raw.graph.pack.entry state.visited
        active := some run
      }
      receipt := none
    }
  else none

private def traverseTransition (cfg : Config) (state : State)
    (hotspot : HotspotId) : Option (StepResult cfg) := do
  let run ← state.active
  if !withinTurnB cfg run then none
  else if unresolvedHazardAtB cfg run then none
  else
    let position ← DeckGraph.navigateStep cfg.raw.graph.pack run.position hotspot
    let run' := {
      run with
      position
      turnsUsed := run.turnsUsed + 1
      visited := insert position.room run.visited
    }
    some {
      state := {
        state with
        visited := insert position.room state.visited
        active := some run'
      }
      receipt := none
    }

private def confrontTransition (cfg : Config) (state : State)
    (hazardId : HazardId) (officerId : OfficerId) : Option (StepResult cfg) := do
  let run ← state.active
  let hazard ← hazardById? cfg.raw.hazards hazardId
  let officer ← officerById? state.officers officerId
  if !withinTurnB cfg run then none
  else if !officerReadyForB cfg state run officerId .containment then none
  else if hazard.room != run.position.room then none
  else if hazard.id ∈ run.resolvedHazards then none
  else if cfg.raw.operationalSupplyBudget < run.suppliesSpent + hazard.supplyCost then none
  else
    let injury := injuryAfter officer.injury hazard.damage
    let run' := {
      run with
      turnsUsed := run.turnsUsed + 1
      suppliesSpent := run.suppliesSpent + hazard.supplyCost
      resolvedHazards := insert hazard.id run.resolvedHazards
    }
    some {
      state := {
        state with
        officers := updateOfficerInjury state.officers officerId injury
        active := some run'
      }
      receipt := none
    }

private def surveyTransition (cfg : Config) (state : State)
    (artifact : ArtifactRef) (officerId : OfficerId) : Option (StepResult cfg) := do
  let run ← state.active
  let discovery ← discoveryByArtifact? cfg.raw.discoveries artifact
  if !withinTurnB cfg run then none
  else if !officerReadyForB cfg state run officerId .pathfinder then none
  else if discovery.room != run.position.room then none
  else if artifact ∈ run.discoveries then none
  else
    let run' := {
      run with
      turnsUsed := run.turnsUsed + 1
      discoveries := insert artifact run.discoveries
    }
    some { state := { state with active := some run' }, receipt := none }

private def recoverTransition (cfg : Config) (state : State)
    (salvageId : SalvageId) (officerId : OfficerId) : Option (StepResult cfg) := do
  let run ← state.active
  let spec ← salvageSpecById? cfg.raw.salvage salvageId
  let record ← salvageRecordById? state.salvage salvageId
  if !withinTurnB cfg run then none
  else if !officerReadyForB cfg state run officerId .engineer then none
  else if spec.room != run.position.room then none
  else if record.custody != .onDeck spec.room then none
  else
    let run' := { run with turnsUsed := run.turnsUsed + 1 }
    some {
      state := {
        state with
        salvage := setCustody state.salvage salvageId (.carried officerId)
        active := some run'
      }
      receipt := none
    }

private def treatTransition (cfg : Config) (state : State)
    (medicId targetId : OfficerId) : Option (StepResult cfg) := do
  let run ← state.active
  let target ← officerById? state.officers targetId
  if !withinTurnB cfg run then none
  else if !officerReadyForB cfg state run medicId .medic then none
  else if targetId ∉ run.party then none
  else if target.injury.val = 0 then none
  else if cfg.raw.operationalSupplyBudget < run.suppliesSpent + TREATMENT_SUPPLY_COST then none
  else
    let run' := {
      run with
      turnsUsed := run.turnsUsed + 1
      suppliesSpent := run.suppliesSpent + TREATMENT_SUPPLY_COST
    }
    some {
      state := {
        state with
        officers := updateOfficerInjury state.officers targetId (injuryAfterTreatment target.injury)
        active := some run'
      }
      receipt := none
    }

private def extractTransition (cfg : Config) (state : State) : Option (StepResult cfg) := do
  let run ← state.active
  if hturn : run.turnsUsed < cfg.raw.turnBudget then
    if hroom : run.position.room = cfg.raw.graph.pack.extraction then
      if unresolvedHazardAtB cfg run then none
      else
        let outcome ← ActivityOutcome.validate cfg.raw.policy (rawOutcome cfg state run)
        let receipt : ExtractionReceipt cfg := {
          key := run.key
          finalPosition := run.position
          turnsUsed := run.turnsUsed + 1
          suppliesSpent := run.suppliesSpent
          visited := run.visited
          recovered := carriedIds state
          outcome
          at_authored_extraction := hroom
          turns_bounded := hturn
        }
        some {
          state := { state with salvage := secureCarried state.salvage, active := none }
          receipt := some receipt
        }
    else none
  else none

private def withdrawTransition (cfg : Config) (state : State) : Option (StepResult cfg) := do
  let _run ← state.active
  some {
    state := { state with salvage := restoreCarried cfg state.salvage, active := none }
    receipt := none
  }

private def transition (cfg : Config) (state : State) : Action → Option (StepResult cfg)
  | .begin key party => beginTransition cfg state key party
  | .traverse hotspot => traverseTransition cfg state hotspot
  | .confront hazard officer => confrontTransition cfg state hazard officer
  | .survey artifact officer => surveyTransition cfg state artifact officer
  | .recover salvage officer => recoverTransition cfg state salvage officer
  | .treat medic target => treatTransition cfg state medic target
  | .extract => extractTransition cfg state
  | .withdraw => withdrawTransition cfg state

/-- Public semantic transition.  Both caller state and emitted state must satisfy
the complete invariant; a bug in an individual action therefore fails closed. -/
def step (cfg : Config) (state : State) (action : Action) : Option (StepResult cfg) :=
  if validStateB cfg state then
    match transition cfg state action with
    | some result => if validStateB cfg result.state then some result else none
    | none => none
  else none

/-- Replay fails at the first refused action.  Fuel bounds transcript work even
across begin/withdraw cycles, independently of a run's stricter turn budget. -/
def replay (cfg : Config) : Nat → State → List Action →
    Option (State × List (ExtractionReceipt cfg))
  | _, state, [] => some (state, [])
  | 0, _, _ :: _ => none
  | fuel + 1, state, action :: actions => do
      let result ← step cfg state action
      let (finalState, receipts) ← replay cfg fuel result.state actions
      let receipts := match result.receipt with
        | none => receipts
        | some receipt => receipt :: receipts
      some (finalState, receipts)

/-! ## General laws -/

theorem step_deterministic (cfg : Config) (state : State) (action : Action)
    {first second : StepResult cfg}
    (hfirst : step cfg state action = some first)
    (hsecond : step cfg state action = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem replay_deterministic (cfg : Config) (fuel : Nat) (state : State)
    (actions : List Action) {first second : State × List (ExtractionReceipt cfg)}
    (hfirst : replay cfg fuel state actions = some first)
    (hsecond : replay cfg fuel state actions = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/-- Exact replay identity: the same activated config, initial state, fuel, and
action transcript determine both the final persistent state and every extraction
receipt, component-for-component. -/
theorem exact_replay_identity (cfg : Config) (fuel : Nat) (state : State)
    (actions : List Action) {first second : State × List (ExtractionReceipt cfg)}
    (hfirst : replay cfg fuel state actions = some first)
    (hsecond : replay cfg fuel state actions = some second) :
    first.1 = second.1 ∧ first.2 = second.2 := by
  have h := replay_deterministic cfg fuel state actions hfirst hsecond
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem Config.dailyRunBudget_bounded (cfg : Config) :
    cfg.raw.dailyRunBudget ≤ MAX_DAILY_RUNS := by
  have h := cfg.valid
  simp only [configValidB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

theorem Config.turnBudget_bounded (cfg : Config) :
    cfg.raw.turnBudget ≤ MAX_TURNS := by
  have h := cfg.valid
  simp only [configValidB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

theorem step_some_input_valid (cfg : Config) (state : State) (action : Action)
    (result : StepResult cfg) (h : step cfg state action = some result) :
    validStateB cfg state = true := by
  simp only [step] at h
  split at h <;> simp_all

theorem step_some_output_valid (cfg : Config) (state : State) (action : Action)
    (result : StepResult cfg) (h : step cfg state action = some result) :
    validStateB cfg result.state = true := by
  simp only [step] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all

theorem validState_runs_bounded (cfg : Config) (state : State)
    (h : validStateB cfg state = true) :
    state.runsUsed ≤ cfg.raw.dailyRunBudget := by
  simp only [validStateB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

theorem validState_salvage_ids_exact (cfg : Config) (state : State)
    (h : validStateB cfg state = true) :
    state.salvage.map SalvageRecord.id = salvageIds cfg.raw := by
  simp only [validStateB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

theorem validState_salvage_ids_unique (cfg : Config) (state : State)
    (h : validStateB cfg state = true) :
    (state.salvage.map SalvageRecord.id).Nodup := by
  simp only [validStateB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

theorem validState_active_budgets (cfg : Config) (state : State) (run : RunState)
    (hvalid : validStateB cfg state = true) (hactive : state.active = some run) :
    run.turnsUsed ≤ cfg.raw.turnBudget ∧
      run.suppliesSpent ≤ cfg.raw.operationalSupplyBudget := by
  simp only [validStateB, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  simp only [hactive, activeValidB, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  aesop

/-- Every custody mutation changes the tag in an existing object row; it never
adds, removes, or substitutes an object identity. -/
theorem setCustody_preserves_ids (items : List SalvageRecord) (id : SalvageId)
    (custody : Custody) :
    (setCustody items id custody).map SalvageRecord.id =
      items.map SalvageRecord.id := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      change
        (if item.id = id then { item with custody } else item).id ::
            (setCustody items id custody).map SalvageRecord.id =
          item.id :: items.map SalvageRecord.id
      rw [ih]
      by_cases heq : item.id = id <;> simp [heq]

theorem secureCarried_preserves_ids (items : List SalvageRecord) :
    (secureCarried items).map SalvageRecord.id = items.map SalvageRecord.id := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      change
        (match item.custody with
          | .carried _ => { item with custody := .secured }
          | _ => item).id ::
            (secureCarried items).map SalvageRecord.id =
          item.id :: items.map SalvageRecord.id
      rw [ih]
      cases item.custody <;> rfl

theorem restoreCarried_preserves_ids (cfg : Config) (items : List SalvageRecord) :
    (restoreCarried cfg items).map SalvageRecord.id = items.map SalvageRecord.id := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      change
        (match item.custody with
          | .carried _ =>
              match salvageSpecById? cfg.raw.salvage item.id with
              | some spec => { item with custody := .onDeck spec.room }
              | none => item
          | _ => item).id ::
            (restoreCarried cfg items).map SalvageRecord.id =
          item.id :: items.map SalvageRecord.id
      rw [ih]
      cases hcustody : item.custody with
      | onDeck room => rfl
      | secured => rfl
      | carried officer =>
          cases salvageSpecById? cfg.raw.salvage item.id <;> rfl

/-- Custody conservation for the public transition: accepted actions preserve the
exact authored object-id sequence, not merely its length. -/
theorem step_custody_conservation (cfg : Config) (state : State) (action : Action)
    (result : StepResult cfg) (h : step cfg state action = some result) :
    result.state.salvage.map SalvageRecord.id =
      state.salvage.map SalvageRecord.id := by
  rw [validState_salvage_ids_exact cfg result.state (step_some_output_valid cfg state action result h)]
  rw [validState_salvage_ids_exact cfg state (step_some_input_valid cfg state action result h)]

theorem step_custody_count_conservation (cfg : Config) (state : State)
    (action : Action) (result : StepResult cfg)
    (h : step cfg state action = some result) :
    result.state.salvage.length = state.salvage.length := by
  have hids := step_custody_conservation cfg state action result h
  simpa using congrArg List.length hids

theorem step_output_has_unique_salvage (cfg : Config) (state : State)
    (action : Action) (result : StepResult cfg)
    (h : step cfg state action = some result) :
    (result.state.salvage.map SalvageRecord.id).Nodup :=
  validState_salvage_ids_unique cfg result.state
    (step_some_output_valid cfg state action result h)

theorem step_output_daily_bound (cfg : Config) (state : State) (action : Action)
    (result : StepResult cfg) (h : step cfg state action = some result) :
    result.state.runsUsed ≤ cfg.raw.dailyRunBudget :=
  validState_runs_bounded cfg result.state
    (step_some_output_valid cfg state action result h)

theorem receipt_contribution_accepted (cfg : Config)
    (receipt : ExtractionReceipt cfg) :
    cfg.raw.policy.mission.acceptsContribution receipt.outcome.contribution = true :=
  receipt.outcome.contribution_accepted

theorem receipt_at_authored_extraction (cfg : Config)
    (receipt : ExtractionReceipt cfg) :
    receipt.finalPosition.room = cfg.raw.graph.pack.extraction :=
  receipt.at_authored_extraction

theorem receipt_turns_bounded (cfg : Config) (receipt : ExtractionReceipt cfg) :
    receipt.turnsUsed ≤ cfg.raw.turnBudget := receipt.turns_bounded

theorem receipt_beta_candidates_declared (cfg : Config)
    (receipt : ExtractionReceipt cfg) :
    receipt.outcome.betaCandidates ⊆ cfg.raw.policy.allowedBeta :=
  receipt.outcome.beta_candidates_declared

theorem receipt_beta_candidates_bounded (cfg : Config)
    (receipt : ExtractionReceipt cfg) :
    receipt.outcome.betaCandidates.card ≤ ActivityOutcome.BETA_CANDIDATE_LIMIT :=
  le_trans receipt.outcome.beta_candidates_bounded
    (Nat.lt_succ_iff.mp cfg.raw.policy.resultLimit.isLt)

theorem injuryAfter_never_decreases (injury damage : Injury) :
    injury.val ≤ (injuryAfter injury damage).val := by
  simp only [injuryAfter, Fin.val_mk]
  omega

theorem injuryAfter_bounded (injury damage : Injury) :
    (injuryAfter injury damage).val ≤ 3 := by
  exact Nat.lt_succ_iff.mp (injuryAfter injury damage).isLt

theorem treatment_decreases_exactly_one (injury : Injury) (h : 0 < injury.val) :
    (injuryAfterTreatment injury).val + 1 = injury.val := by
  simp only [injuryAfterTreatment, Fin.val_mk]
  omega

theorem replay_overfuel_refused (cfg : Config) (fuel : Nat) (state : State)
    (actions : List Action) (h : fuel < actions.length) :
    replay cfg fuel state actions = none := by
  induction fuel generalizing state actions with
  | zero =>
      cases actions with
      | nil => simp at h
      | cons action actions => rfl
  | succ fuel ih =>
      cases actions with
      | nil => simp at h
      | cons action actions =>
          cases hstep : step cfg state action with
          | none => simp [replay, hstep]
          | some result =>
              have htail : fuel < actions.length := by simpa using h
              simp [replay, hstep, ih result.state actions htail]

theorem refused_head_refuses_replay (cfg : Config) (fuel : Nat) (state : State)
    (action : Action) (actions : List Action)
    (h : step cfg state action = none) :
    replay cfg (fuel + 1) state (action :: actions) = none := by
  simp [replay, h]

theorem consumed_key_refused (cfg : Config) (state : State)
    (key : ExpeditionKey) (party : List OfficerId) (hkey : key ∈ state.consumed) :
    step cfg state (.begin key party) = none := by
  simp only [step]
  split <;> try rfl
  simp [transition, beginTransition, hkey]

theorem exhausted_daily_budget_refuses_begin (cfg : Config) (state : State)
    (key : ExpeditionKey) (party : List OfficerId)
    (hexhausted : cfg.raw.dailyRunBudget ≤ state.runsUsed) :
    step cfg state (.begin key party) = none := by
  simp only [step]
  split <;> try rfl
  simp [transition, beginTransition, hexhausted]

theorem inactive_traverse_refused (cfg : Config) (state : State)
    (hotspot : HotspotId) (hinactive : state.active = none) :
    step cfg state (.traverse hotspot) = none := by
  simp [step, transition, traverseTransition, hinactive]

/-! ## Executable accepted and hostile fixtures -/

def fixtureValidatedPack : ValidatedPack where
  pack := DeckGraph.fixturePack
  validation := DeckGraph.fixture_pack_validates

def fixtureMissionId : MissionId := ⟨7001⟩
def fixtureRelic : RelicId := ⟨447⟩

def fixtureArtifact : ArtifactRef where
  missionId := fixtureMissionId
  artifactId := ⟨812⟩
  sourceDigest := DeckGraph.zeroDigest
  contentDigest := DeckGraph.zeroDigest

def fixtureBudget : ContributionBudget where
  intel := ⟨20, by decide⟩
  supplies := ⟨20, by decide⟩
  cohesion := ⟨20, by decide⟩
  influence := ⟨20, by decide⟩
  score := ⟨100, by decide⟩
  relics := ⟨4, by decide⟩

def fixtureMission : MissionSpec where
  missionId := fixtureMissionId
  artifact := fixtureArtifact
  epoch := DeckGraph.fixtureActivation.contentEpoch
  federationId := DeckGraph.fixtureActivation.federationId
  contentRoot := DeckGraph.fixtureActivation.contentRoot
  activationDigest := DeckGraph.fixtureActivation.activationDigest
  contentSession := DeckGraph.fixtureActivation.contentSession
  runSeed := DeckGraph.zeroDigest
  budget := fixtureBudget
  allowedRelics := {fixtureRelic}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

def fixtureBaseContribution : Contribution where
  intel := ⟨2, by decide⟩
  supplies := ⟨1, by decide⟩
  cohesion := ⟨1, by decide⟩
  influence := ⟨0, by decide⟩
  score := ⟨10, by decide⟩
  relics := ∅
  relics_bounded := by simp

def fixturePolicy : ActivityOutcome.Policy where
  mission := fixtureMission
  allowedBeta := {fixtureArtifact}
  resultLimit := ⟨1, by decide⟩
  catalogue_bounded := by simp

def fixturePathfinder : OfficerProfile := { id := ⟨1⟩, role := .pathfinder }
def fixtureEngineer : OfficerProfile := { id := ⟨2⟩, role := .engineer }
def fixtureContainment : OfficerProfile := { id := ⟨3⟩, role := .containment }
def fixtureMedic : OfficerProfile := { id := ⟨4⟩, role := .medic }

def fixtureHazard : HazardSpec where
  id := ⟨1⟩
  room := DeckGraph.fixtureRoomB.id
  damage := ⟨1, by decide⟩
  supplyCost := 1

def fixtureSalvage : SalvageSpec where
  id := ⟨1⟩
  room := DeckGraph.fixtureRoomC.id
  relic := fixtureRelic

def fixtureDiscovery : DiscoverySpec where
  room := DeckGraph.fixtureRoomD.id
  artifact := fixtureArtifact

def fixtureRawConfig : RawConfig where
  graph := fixtureValidatedPack
  policy := fixturePolicy
  day := DeckGraph.fixtureActivation.contentEpoch
  officers := [fixturePathfinder, fixtureEngineer, fixtureContainment, fixtureMedic]
  hazards := [fixtureHazard]
  salvage := [fixtureSalvage]
  discoveries := [fixtureDiscovery]
  dailyRunBudget := 2
  turnBudget := 12
  operationalSupplyBudget := 4
  baseContribution := fixtureBaseContribution

theorem fixture_raw_config_valid : configValidB fixtureRawConfig = true := by
  native_decide

def fixtureConfig : Config where
  raw := fixtureRawConfig
  valid := fixture_raw_config_valid

def fixturePlayer : Digest32 := DeckGraph.zeroDigest

def fixtureKey : ExpeditionKey where
  pack := fixtureConfig.packKey
  playerKey := fixturePlayer
  day := fixtureConfig.raw.day
  counter := 1

def fixtureKeyTwo : ExpeditionKey := { fixtureKey with counter := 2 }
def fixtureKeyThree : ExpeditionKey := { fixtureKey with counter := 3 }

def fixtureParty : List OfficerId :=
  [fixturePathfinder.id, fixtureEngineer.id, fixtureContainment.id, fixtureMedic.id]

def fixtureInitial : State := initialState fixtureConfig fixturePlayer

theorem fixture_initial_state_valid : validStateB fixtureConfig fixtureInitial = true := by
  native_decide

def fixtureActions : List Action :=
  [ .begin fixtureKey fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront fixtureHazard.id fixtureContainment.id
  , .traverse DeckGraph.fixtureWrap.id
  , .recover fixtureSalvage.id fixtureEngineer.id
  , .traverse DeckGraph.fixtureMirror.id
  , .survey fixtureArtifact fixturePathfinder.id
  , .traverse DeckGraph.fixturePhase.id
  , .extract
  ]

def fixtureAcceptedB : Bool :=
  match replay fixtureConfig fixtureActions.length fixtureInitial fixtureActions with
  | some (state, [receipt]) =>
      decide (state.active = none) &&
      decide (receipt.key = fixtureKey) &&
      decide (receipt.finalPosition = DeckGraph.fixtureFinalPosition) &&
      decide (fixtureSalvage.id ∈ receipt.recovered) &&
      decide (fixtureRelic ∈ receipt.outcome.contribution.relics) &&
      decide (fixtureArtifact ∈ receipt.outcome.betaCandidates) &&
      decide (salvageRecordById? state.salvage fixtureSalvage.id =
        some { id := fixtureSalvage.id, custody := .secured }) &&
      validStateB fixtureConfig state
  | _ => false

theorem fixture_full_expedition_accepts : fixtureAcceptedB = true := by
  native_decide

/-- An unfinished run can withdraw, but carried salvage returns to its exact
authored deck room and produces no extraction receipt.  Charted rooms persist. -/
def fixtureWithdrawActions : List Action :=
  [ .begin fixtureKey fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront fixtureHazard.id fixtureContainment.id
  , .traverse DeckGraph.fixtureWrap.id
  , .recover fixtureSalvage.id fixtureEngineer.id
  , .withdraw
  ]

def fixtureWithdrawalRestoresB : Bool :=
  match replay fixtureConfig fixtureWithdrawActions.length fixtureInitial fixtureWithdrawActions with
  | some (state, []) =>
      decide (salvageRecordById? state.salvage fixtureSalvage.id =
        some { id := fixtureSalvage.id, custody := .onDeck fixtureSalvage.room }) &&
      decide (DeckGraph.fixtureRoomC.id ∈ state.visited) &&
      validStateB fixtureConfig state
  | _ => false

theorem fixture_withdrawal_restores_custody : fixtureWithdrawalRestoresB = true := by
  native_decide

def fixtureSameKeyReplayRefusedB : Bool :=
  match replay fixtureConfig 2 fixtureInitial
      [.begin fixtureKey fixtureParty, .withdraw] with
  | some (state, []) => decide (step fixtureConfig state (.begin fixtureKey fixtureParty) = none)
  | _ => false

theorem fixture_same_key_replay_refused : fixtureSameKeyReplayRefusedB = true := by
  native_decide

def fixtureDailyExhaustionB : Bool :=
  match replay fixtureConfig 4 fixtureInitial
      [ .begin fixtureKey fixtureParty, .withdraw
      , .begin fixtureKeyTwo fixtureParty, .withdraw ] with
  | some (state, []) =>
      decide (step fixtureConfig state (.begin fixtureKeyThree fixtureParty) = none)
  | _ => false

theorem fixture_daily_budget_is_hard : fixtureDailyExhaustionB = true := by
  native_decide

def fixtureUnknownArtifact : ArtifactRef :=
  { fixtureArtifact with artifactId := ⟨999999⟩ }

def fixtureUndeclaredDiscoveryRefusedB : Bool :=
  match step fixtureConfig fixtureInitial (.begin fixtureKey fixtureParty) with
  | some begun =>
      decide (step fixtureConfig begun.state
        (.survey fixtureUnknownArtifact fixturePathfinder.id) = none)
  | none => false

theorem fixture_undeclared_discovery_refused :
    fixtureUndeclaredDiscoveryRefusedB = true := by
  native_decide

def fixtureEarlyExtractionRefusedB : Bool :=
  match step fixtureConfig fixtureInitial (.begin fixtureKey fixtureParty) with
  | some begun => decide (step fixtureConfig begun.state .extract = none)
  | none => false

theorem fixture_early_extraction_refused : fixtureEarlyExtractionRefusedB = true := by
  native_decide

def fixtureTightRawConfig : RawConfig := { fixtureRawConfig with turnBudget := 1 }

theorem fixture_tight_raw_config_valid : configValidB fixtureTightRawConfig = true := by
  native_decide

def fixtureTightConfig : Config :=
  { raw := fixtureTightRawConfig, valid := fixture_tight_raw_config_valid }

def fixtureTightInitial : State := initialState fixtureTightConfig fixturePlayer
def fixtureTightKey : ExpeditionKey :=
  { fixtureKey with pack := fixtureTightConfig.packKey }

theorem fixture_turn_budget_refuses_second_run_action :
    replay fixtureTightConfig 3 fixtureTightInitial
      [ .begin fixtureTightKey fixtureParty
      , .traverse DeckGraph.fixtureOneWay.id
      , .confront fixtureHazard.id fixtureContainment.id ] = none := by
  native_decide

def fixtureTreatmentActions : List Action :=
  [ .begin fixtureKey fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront fixtureHazard.id fixtureContainment.id
  , .treat fixtureMedic.id fixtureContainment.id
  ]

def fixtureTreatmentB : Bool :=
  match replay fixtureConfig fixtureTreatmentActions.length fixtureInitial fixtureTreatmentActions with
  | some (state, []) =>
      match officerById? state.officers fixtureContainment.id with
      | some officer => decide (officer.injury.val = 0)
      | none => false
  | _ => false

theorem fixture_declared_treatment_repairs_injury : fixtureTreatmentB = true := by
  native_decide

/-! Kernel/compiled axiom accounting. -/

#assert_axioms step_deterministic
#assert_axioms replay_deterministic
#assert_axioms exact_replay_identity
#assert_axioms Config.dailyRunBudget_bounded
#assert_axioms Config.turnBudget_bounded
#assert_axioms step_some_input_valid
#assert_axioms step_some_output_valid
#assert_axioms validState_runs_bounded
#assert_axioms validState_salvage_ids_exact
#assert_axioms validState_salvage_ids_unique
#assert_axioms validState_active_budgets
#assert_axioms setCustody_preserves_ids
#assert_axioms secureCarried_preserves_ids
#assert_axioms restoreCarried_preserves_ids
#assert_axioms step_custody_conservation
#assert_axioms step_custody_count_conservation
#assert_axioms step_output_has_unique_salvage
#assert_axioms step_output_daily_bound
#assert_axioms receipt_contribution_accepted
#assert_axioms receipt_at_authored_extraction
#assert_axioms receipt_turns_bounded
#assert_axioms receipt_beta_candidates_declared
#assert_axioms receipt_beta_candidates_bounded
#assert_axioms injuryAfter_never_decreases
#assert_axioms injuryAfter_bounded
#assert_axioms treatment_decreases_exactly_one
#assert_axioms replay_overfuel_refused
#assert_axioms refused_head_refuses_replay
#assert_axioms consumed_key_refused
#assert_axioms exhausted_daily_budget_refuses_begin
#assert_axioms inactive_traverse_refused

#assert_compiled fixture_raw_config_valid
#assert_compiled fixture_initial_state_valid
#assert_compiled fixture_full_expedition_accepts
#assert_compiled fixture_withdrawal_restores_custody
#assert_compiled fixture_same_key_replay_refused
#assert_compiled fixture_daily_budget_is_hard
#assert_compiled fixture_undeclared_discovery_refused
#assert_compiled fixture_early_extraction_refused
#assert_compiled fixture_tight_raw_config_valid
#assert_compiled fixture_turn_budget_refuses_second_run_action
#assert_compiled fixture_declared_treatment_repairs_injury

end Dregg2.Games.PathOfAngels.DeckExpedition
