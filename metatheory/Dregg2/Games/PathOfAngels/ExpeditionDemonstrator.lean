/-
# ExpeditionDemonstrator — a fiction-neutral branching deck-design instrument

This is deliberately not story content.  It is a nine-room pressure-test pack for
`DeckExpedition`: a longer safe route competes with a shorter hazardous route.
Turns, operational supplies, injury, provisional observations, and salvage custody
remain separate axes, allowing the bounded analyzer at the end of the file to find
and compare materially different strategies.

Nothing here imports Canon, creates an asset, or claims that a provisional find is
true in the show.  This module is also not an umbrella import; it is an isolated
executable design fixture.
-/
import Dregg2.Games.PathOfAngels.DeckExpedition
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ExpeditionDemonstrator

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DeckGraph
open Dregg2.Games.PathOfAngels.DeckExpedition

set_option autoImplicit false

/-! ## Nine-room forked pack -/

def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

def demoActivation : ActivationIdentity where
  federationId := zeroDigest
  contentRoot := zeroDigest
  activationDigest := zeroDigest
  contentSession := zeroDigest
  contentEpoch := ⟨42⟩
  signerKeyId := zeroDigest
  activationCounter := 7

def entryRoom : Room := { id := ⟨100⟩ }
def junctionRoom : Room := { id := ⟨101⟩ }
def safeRoomA : Room := { id := ⟨102⟩ }
def safeRoomB : Room := { id := ⟨103⟩ }
def safeRoomC : Room := { id := ⟨104⟩ }
def hazardRoom : Room := { id := ⟨105⟩ }
def cacheRoom : Room := { id := ⟨106⟩ }
def mergeRoom : Room := { id := ⟨107⟩ }
def extractionRoom : Room := { id := ⟨108⟩ }

def entryToJunction : Hotspot :=
  { id := ⟨1000⟩, source := entryRoom.id, destination := junctionRoom.id,
    modifier := .oneWay }

def junctionToSafeA : Hotspot :=
  { id := ⟨1001⟩, source := junctionRoom.id, destination := safeRoomA.id,
    modifier := .oneWay }

def safeAToSafeB : Hotspot :=
  { id := ⟨1002⟩, source := safeRoomA.id, destination := safeRoomB.id,
    modifier := .oneWay }

def safeBToSafeC : Hotspot :=
  { id := ⟨1003⟩, source := safeRoomB.id, destination := safeRoomC.id,
    modifier := .oneWay }

def safeCToMerge : Hotspot :=
  { id := ⟨1004⟩, source := safeRoomC.id, destination := mergeRoom.id,
    modifier := .oneWay }

def junctionToHazard : Hotspot :=
  { id := ⟨1005⟩, source := junctionRoom.id, destination := hazardRoom.id,
    modifier := .oneWay }

def hazardToCache : Hotspot :=
  { id := ⟨1006⟩, source := hazardRoom.id, destination := cacheRoom.id,
    modifier := .oneWay }

def cacheToMerge : Hotspot :=
  { id := ⟨1007⟩, source := cacheRoom.id, destination := mergeRoom.id,
    modifier := .oneWay }

def mergeToExtraction : Hotspot :=
  { id := ⟨1008⟩, source := mergeRoom.id, destination := extractionRoom.id,
    modifier := .phase 0 1 }

def demoPack : Pack where
  schemaVersion := CURRENT_SCHEMA_VERSION
  packId := ⟨404⟩
  activation := demoActivation
  rooms :=
    [entryRoom, junctionRoom, safeRoomA, safeRoomB, safeRoomC,
      hazardRoom, cacheRoom, mergeRoom, extractionRoom]
  hotspots :=
    [entryToJunction, junctionToSafeA, safeAToSafeB, safeBToSafeC,
      safeCToMerge, junctionToHazard, hazardToCache, cacheToMerge,
      mergeToExtraction]
  entry := entryRoom.id
  extraction := extractionRoom.id
  initialPhase := 0
  navigationFuel := 8
  validationFuel := 32

theorem demo_pack_validates : validateB demoPack = true := by
  native_decide

theorem demo_pack_has_nine_rooms_and_nine_hotspots :
    demoPack.rooms.length = 9 ∧ demoPack.hotspots.length = 9 := by
  decide

def demoValidatedPack : ValidatedPack where
  pack := demoPack
  validation := demo_pack_validates

/-! ## Authored roles, pressure, finds, and reward policy -/

def demoMissionId : MissionId := ⟨4040⟩
def demoRelic : RelicId := ⟨9001⟩

def safeObservation : ArtifactRef where
  missionId := demoMissionId
  artifactId := ⟨1⟩
  sourceDigest := zeroDigest
  contentDigest := zeroDigest

def cacheObservation : ArtifactRef where
  missionId := demoMissionId
  artifactId := ⟨2⟩
  sourceDigest := zeroDigest
  contentDigest := zeroDigest

def demoBudget : ContributionBudget where
  intel := ⟨20, by decide⟩
  supplies := ⟨20, by decide⟩
  cohesion := ⟨20, by decide⟩
  influence := ⟨20, by decide⟩
  score := ⟨100, by decide⟩
  relics := ⟨2, by decide⟩

def demoMission : MissionSpec where
  missionId := demoMissionId
  artifact := safeObservation
  epoch := demoActivation.contentEpoch
  federationId := demoActivation.federationId
  contentRoot := demoActivation.contentRoot
  activationDigest := demoActivation.activationDigest
  contentSession := demoActivation.contentSession
  runSeed := zeroDigest
  budget := demoBudget
  allowedRelics := {demoRelic}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

def demoBaseContribution : Contribution where
  intel := ⟨3, by decide⟩
  supplies := ⟨1, by decide⟩
  cohesion := ⟨1, by decide⟩
  influence := ⟨0, by decide⟩
  score := ⟨12, by decide⟩
  relics := ∅
  relics_bounded := by simp

def demoPolicy : ActivityOutcome.Policy where
  mission := demoMission
  allowedBeta := {safeObservation, cacheObservation}
  resultLimit := ⟨2, by decide⟩
  catalogue_bounded := by
    calc
      ({safeObservation, cacheObservation} : Finset ArtifactRef).card ≤
          ({cacheObservation} : Finset ArtifactRef).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by simp
      _ ≤ ActivityOutcome.BETA_CATALOGUE_LIMIT := by decide

def pathfinder : OfficerProfile := { id := ⟨11⟩, role := .pathfinder }
def engineer : OfficerProfile := { id := ⟨12⟩, role := .engineer }
def containment : OfficerProfile := { id := ⟨13⟩, role := .containment }
def medic : OfficerProfile := { id := ⟨14⟩, role := .medic }

def pressureHazard : HazardSpec where
  id := ⟨21⟩
  room := hazardRoom.id
  damage := ⟨1, by decide⟩
  supplyCost := 2

def salvageFind : SalvageSpec where
  id := ⟨31⟩
  room := cacheRoom.id
  relic := demoRelic

def safeFind : DiscoverySpec := { room := safeRoomB.id, artifact := safeObservation }
def optionalCacheFind : DiscoverySpec :=
  { room := cacheRoom.id, artifact := cacheObservation }

def demoRawConfig : RawConfig where
  graph := demoValidatedPack
  policy := demoPolicy
  day := demoActivation.contentEpoch
  officers := [pathfinder, engineer, containment, medic]
  hazards := [pressureHazard]
  salvage := [salvageFind]
  discoveries := [safeFind, optionalCacheFind]
  dailyRunBudget := 1
  turnBudget := 8
  operationalSupplyBudget := 3
  baseContribution := demoBaseContribution

theorem demo_config_valid : configValidB demoRawConfig = true := by
  native_decide

def demoConfig : Config := { raw := demoRawConfig, valid := demo_config_valid }
def demoPlayer : Digest32 := zeroDigest

def demoKey : ExpeditionKey where
  pack := demoConfig.packKey
  playerKey := demoPlayer
  day := demoConfig.raw.day
  counter := 1

def demoParty : List OfficerId :=
  [pathfinder.id, engineer.id, containment.id, medic.id]

def demoInitial : State := initialState demoConfig demoPlayer

def beginAction : Action := .begin demoKey demoParty

def begunState : State :=
  match step demoConfig demoInitial beginAction with
  | some result => result.state
  | none => demoInitial

theorem demo_begin_accepts :
    (step demoConfig demoInitial beginAction).isSome = true := by
  native_decide

theorem demo_begun_state_valid : validStateB demoConfig begunState = true := by
  native_decide

/-! ## Three successful policies and one greedy failure -/

/-- More navigation, no operational supplies or injury, one provisional find. -/
def safeSurveyPlan : List Action :=
  [ .traverse entryToJunction.id
  , .traverse junctionToSafeA.id
  , .traverse safeAToSafeB.id
  , .survey safeObservation pathfinder.id
  , .traverse safeBToSafeC.id
  , .traverse safeCToMerge.id
  , .traverse mergeToExtraction.id
  , .extract
  ]

/-- Fewer turns, but it spends supplies and accepts an injury. -/
def rapidPushPlan : List Action :=
  [ .traverse entryToJunction.id
  , .traverse junctionToHazard.id
  , .confront pressureHazard.id containment.id
  , .traverse hazardToCache.id
  , .traverse cacheToMerge.id
  , .traverse mergeToExtraction.id
  , .extract
  ]

/-- The hazardous route can spend its one-turn margin recovering exact salvage. -/
def salvagePushPlan : List Action :=
  [ .traverse entryToJunction.id
  , .traverse junctionToHazard.id
  , .confront pressureHazard.id containment.id
  , .traverse hazardToCache.id
  , .recover salvageFind.id engineer.id
  , .traverse cacheToMerge.id
  , .traverse mergeToExtraction.id
  , .extract
  ]

/-- Trying to take both optional cache rewards consumes the extraction turn. -/
def greedyPushPlan : List Action :=
  [ .traverse entryToJunction.id
  , .traverse junctionToHazard.id
  , .confront pressureHazard.id containment.id
  , .traverse hazardToCache.id
  , .recover salvageFind.id engineer.id
  , .survey cacheObservation pathfinder.id
  , .traverse cacheToMerge.id
  , .traverse mergeToExtraction.id
  , .extract
  ]

def safeSuccessB : Bool :=
  match replay demoConfig safeSurveyPlan.length begunState safeSurveyPlan with
  | some (state, [receipt]) =>
      decide (receipt.turnsUsed = 8) &&
      decide (receipt.suppliesSpent = 0) &&
      decide (safeObservation ∈ receipt.outcome.betaCandidates) &&
      decide (receipt.recovered = ∅) &&
      decide (state.active = none)
  | _ => false

theorem safe_strategy_succeeds : safeSuccessB = true := by
  native_decide

def rapidPushSuccessB : Bool :=
  match replay demoConfig rapidPushPlan.length begunState rapidPushPlan with
  | some (state, [receipt]) =>
      decide (receipt.turnsUsed = 7) &&
      decide (receipt.suppliesSpent = 2) &&
      decide (receipt.outcome.betaCandidates = ∅) &&
      decide (receipt.recovered = ∅) &&
      match officerById? state.officers containment.id with
      | some officer => decide (officer.injury.val = 1)
      | none => false
  | _ => false

theorem rapid_push_strategy_succeeds : rapidPushSuccessB = true := by
  native_decide

/-- The two successful policies are genuinely incomparable: safe survey spends
one more turn but no supplies or injury; rapid push spends two supplies and one
injury to retain that turn. -/
theorem successful_strategies_trade_incomparable_resources :
    safeSurveyPlan.length = 8 ∧ rapidPushPlan.length = 7 ∧
      pressureHazard.supplyCost = 2 ∧ pressureHazard.damage.val = 1 := by
  decide

def salvagePushSuccessB : Bool :=
  match replay demoConfig salvagePushPlan.length begunState salvagePushPlan with
  | some (state, [receipt]) =>
      decide (receipt.recovered = {salvageFind.id}) &&
      decide (receipt.outcome.contribution.relics = {demoRelic}) &&
      decide (salvageRecordById? state.salvage salvageFind.id =
        some { id := salvageFind.id, custody := .secured }) &&
      decide (receipt.finalPosition.room = demoPack.extraction)
  | _ => false

theorem salvage_extraction_preserves_identity_and_secures_custody :
    salvagePushSuccessB = true := by
  native_decide

theorem greedy_push_loses_its_extraction_window :
    replay demoConfig greedyPushPlan.length begunState greedyPushPlan = none := by
  native_decide

def greedyBeforeExtractPlan : List Action := greedyPushPlan.dropLast

def greedyArrivesWithoutExtractionTurnB : Bool :=
  match replay demoConfig greedyBeforeExtractPlan.length begunState greedyBeforeExtractPlan with
  | some (state, []) =>
      match state.active with
      | some run =>
          decide (run.position.room = demoPack.extraction) &&
          decide (run.turnsUsed = demoConfig.raw.turnBudget) &&
          decide (cacheObservation ∈ run.discoveries) &&
          decide (salvageRecordById? state.salvage salvageFind.id =
            some { id := salvageFind.id, custody := .carried engineer.id }) &&
          decide (step demoConfig state .extract = none)
      | none => false
  | _ => false

theorem greedy_push_reaches_exit_with_find_but_no_extraction_turn :
    greedyArrivesWithoutExtractionTurnB = true := by
  native_decide

/-! ## Illegal-shortcut refusal -/

def junctionState : State :=
  match replay demoConfig 1 begunState [.traverse entryToJunction.id] with
  | some (state, []) => state
  | _ => begunState

def hazardState : State :=
  match replay demoConfig 2 begunState
      [.traverse entryToJunction.id, .traverse junctionToHazard.id] with
  | some (state, []) => state
  | _ => begunState

theorem merge_exit_cannot_be_used_from_the_junction :
    step demoConfig junctionState (.traverse mergeToExtraction.id) = none := by
  native_decide

theorem unresolved_hazard_blocks_the_cache_shortcut :
    step demoConfig hazardState (.traverse hazardToCache.id) = none := by
  native_decide

/-! ## Bounded strategic-fork analyzer -/

/-- The complete role-correct action alphabet for this one authored run.  Hostile
wrong-role calls are omitted because they cannot add a reachable state. -/
def authoredActions : List Action :=
  (demoPack.hotspots.map fun hotspot => .traverse hotspot.id) ++
  [ .confront pressureHazard.id containment.id
  , .survey safeObservation pathfinder.id
  , .survey cacheObservation pathfinder.id
  , .recover salvageFind.id engineer.id
  , .treat medic.id containment.id
  , .extract
  , .withdraw
  ]

theorem authored_action_alphabet_has_sixteen_entries : authoredActions.length = 16 := by
  decide

structure StrategyNode where
  state : State
  transcript : List Action
  receipt : Option (ExtractionReceipt demoConfig)
deriving DecidableEq

def initialNode : StrategyNode := { state := begunState, transcript := [], receipt := none }

def expandNode (node : StrategyNode) : List StrategyNode :=
  authoredActions.filterMap fun action =>
    match step demoConfig node.state action with
    | none => none
    | some result => some {
        state := result.state
        transcript := node.transcript ++ [action]
        receipt := match result.receipt with
          | some receipt => some receipt
          | none => node.receipt
      }

/-- All distinct successful nodes reachable in at most `fuel` authored actions.
The transcript is retained intentionally: two routes reaching similar physical
state are still different design strategies. -/
def exploreAtMost : Nat → List StrategyNode
  | 0 => [initialNode]
  | fuel + 1 =>
      let prior := exploreAtMost fuel
      (prior ++ prior.flatMap expandNode).eraseDups

structure StrategySummary where
  transcript : List Action
  turns : Nat
  supplies : Nat
  injury : Nat
  recovered : Nat
  betaCandidates : Nat
deriving DecidableEq

def injuryBurden (state : State) : Nat :=
  state.officers.foldl (fun total officer => total + officer.injury.val) 0

def summarize? (node : StrategyNode) : Option StrategySummary := do
  let receipt ← node.receipt
  some {
    transcript := node.transcript
    turns := receipt.turnsUsed
    supplies := receipt.suppliesSpent
    injury := injuryBurden node.state
    recovered := receipt.recovered.card
    betaCandidates := receipt.outcome.betaCandidates.card
  }

def strategySummaries (fuel : Nat) : List StrategySummary :=
  (exploreAtMost fuel).filterMap summarize?

/-- Multi-objective dominance: no more pressure on any resource, no less output
on either independent reward axis, and at least one strict improvement. -/
def dominates (a b : StrategySummary) : Bool :=
  decide (a.turns ≤ b.turns) &&
  decide (a.supplies ≤ b.supplies) &&
  decide (a.injury ≤ b.injury) &&
  decide (b.recovered ≤ a.recovered) &&
  decide (b.betaCandidates ≤ a.betaCandidates) &&
  decide (a.turns < b.turns ∨ a.supplies < b.supplies ∨ a.injury < b.injury ∨
    b.recovered < a.recovered ∨ b.betaCandidates < a.betaCandidates)

def paretoFrontier (fuel : Nat) : List StrategySummary :=
  let summaries := strategySummaries fuel
  summaries.filter fun candidate =>
    !(summaries.any fun other => dominates other candidate)

def safeSummary : StrategySummary where
  transcript := safeSurveyPlan
  turns := 8
  supplies := 0
  injury := 0
  recovered := 0
  betaCandidates := 1

def rapidPushSummary : StrategySummary where
  transcript := rapidPushPlan
  turns := 7
  supplies := 2
  injury := 1
  recovered := 0
  betaCandidates := 0

def salvagePushSummary : StrategySummary where
  transcript := salvagePushPlan
  turns := 8
  supplies := 2
  injury := 1
  recovered := 1
  betaCandidates := 0

def analyzerBoundedB : Bool :=
  (exploreAtMost 8).all fun node => decide (node.transcript.length ≤ 8)

theorem bounded_analyzer_respects_fuel : analyzerBoundedB = true := by
  native_decide

theorem analyzer_finds_safe_strategy : safeSummary ∈ strategySummaries 8 := by
  native_decide

theorem analyzer_finds_rapid_push_strategy : rapidPushSummary ∈ strategySummaries 8 := by
  native_decide

theorem analyzer_finds_salvage_push_strategy : salvagePushSummary ∈ strategySummaries 8 := by
  native_decide

theorem safe_and_rapid_push_are_incomparable :
    dominates safeSummary rapidPushSummary = false ∧
      dominates rapidPushSummary safeSummary = false := by
  decide

theorem analyzer_has_nine_successful_strategy_summaries :
    (strategySummaries 8).length = 9 := by
  native_decide

theorem analyzer_has_three_pareto_profiles : (paretoFrontier 8).length = 3 := by
  native_decide

/-- The analyzer exposes an important balance fact rather than rubber-stamping the
authored examples: a no-reward rapid push is dominated by a safe sprint. -/
theorem analyzer_rejects_dominated_rapid_push :
    rapidPushSummary ∉ paretoFrontier 8 := by
  native_decide

/-- The two reward-bearing strategies remain on the frontier because provisional
knowledge and secured salvage are intentionally independent output axes. -/
theorem analyzer_keeps_distinct_reward_strategies :
    safeSummary ∈ paretoFrontier 8 ∧ salvagePushSummary ∈ paretoFrontier 8 := by
  native_decide

/-! ## Axiom accounting -/

#assert_compiled demo_pack_validates
#assert_axioms demo_pack_has_nine_rooms_and_nine_hotspots
#assert_compiled demo_config_valid
#assert_compiled demo_begin_accepts
#assert_compiled demo_begun_state_valid
#assert_compiled safe_strategy_succeeds
#assert_compiled rapid_push_strategy_succeeds
#assert_axioms successful_strategies_trade_incomparable_resources
#assert_compiled salvage_extraction_preserves_identity_and_secures_custody
#assert_compiled greedy_push_loses_its_extraction_window
#assert_compiled greedy_push_reaches_exit_with_find_but_no_extraction_turn
#assert_compiled merge_exit_cannot_be_used_from_the_junction
#assert_compiled unresolved_hazard_blocks_the_cache_shortcut
#assert_axioms authored_action_alphabet_has_sixteen_entries
#assert_compiled bounded_analyzer_respects_fuel
#assert_compiled analyzer_finds_safe_strategy
#assert_compiled analyzer_finds_rapid_push_strategy
#assert_compiled analyzer_finds_salvage_push_strategy
#assert_axioms safe_and_rapid_push_are_incomparable
#assert_compiled analyzer_has_nine_successful_strategy_summaries
#assert_compiled analyzer_has_three_pareto_profiles
#assert_compiled analyzer_rejects_dominated_rapid_push
#assert_compiled analyzer_keeps_distinct_reward_strategies

end Dregg2.Games.PathOfAngels.ExpeditionDemonstrator
