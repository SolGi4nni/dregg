/-
# ArchiveLabDemonstratorEmit — finite browser authority for evidence deduction

The committed `ArchiveLab.step` remains the rules oracle for every charged
screen, test, triangulation, and publication.  This module adds only a finite
specimen cursor: at each exact archive entry the player either passes it unopened
or begins the real two-operation screen/test protocol.  Once screening begins,
testing must finish before the cursor advances.  That removes permutation-only
state explosion while preserving the demonstrator's exhaustive unique-plan claim.

The emitted surface is fiction-neutral beta research.  It cannot promote canon,
mint an asset, settle a reward, or supply a caller-authored deduction.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.ArchiveLabDemonstrator
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ArchiveLabDemonstratorEmit

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.FieldArchive
open Dregg2.Games.PathOfAngels.ArchiveLab
open Dregg2.Games.PathOfAngels.ArchiveLabDemonstrator

set_option autoImplicit false

abbrev FORMAT : String := "POA-ARCHIVE-LAB-TABLE"
abbrev SCHEMA_VERSION : Nat := 1
abbrev EXPLORATION_HORIZON : Nat := 18

private def jsonString (s : String) : String := String.quote s

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def jsonPrettyArray (xs : List String) : String :=
  match xs with
  | [] => "[]"
  | _ => "[\n" ++ String.intercalate ",\n" xs ++ "\n  ]"

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def byteHex (value : Fin 256) : String :=
  String.ofList [lowerHexDigit (value.val / 16), lowerHexDigit (value.val % 16)]

def bytes32Hex (digest : Digest32) : String :=
  String.join (digest.bytes.map byteHex)

/-! ## Cursor instrument, delegating charged moves to `ArchiveLab.step` -/

inductive LabPhase where
  | choose
  | screened
deriving DecidableEq, Repr

structure LabState where
  core : State
  cursor : Nat
  phase : LabPhase
deriving DecidableEq

inductive LabMove where
  | screenCurrent
  | passCurrent
  | testCurrent
  | triangulateSupport
  | publish (hypothesis : HypothesisId)
deriving DecidableEq, Repr

def labMoves : List LabMove :=
  [ .screenCurrent
  , .passCurrent
  , .testCurrent
  , .triangulateSupport
  , .publish resonance
  , .publish maintenanceBeacon
  , .publish externalCarrier
  , .publish sensorArtifact
  ]

def initialLabState : LabState where
  core := initialState demoConfig demoContext
  cursor := 0
  phase := .choose

def currentObservation? (state : LabState) : Option Observation :=
  demoObservations[state.cursor]?

def atAnalysisB (state : LabState) : Bool :=
  decide (state.cursor = demoObservations.length) && decide (state.phase = .choose)

def coreAction (state : LabState) (command : ArchiveLab.Command) : Action :=
  act state.core.nextSequence command

def labStep (state : LabState) : LabMove → Option LabState
  | .screenCurrent =>
      if state.core.published.isSome then none
      else if state.phase ≠ .choose then none
      else match currentObservation? state with
        | none => none
        | some observation => do
            let core ← ArchiveLab.step demoConfig state.core
              (coreAction state (.screen observation.id))
            some { state with core, phase := .screened }
  | .passCurrent =>
      if state.core.published.isSome then none
      else if state.phase ≠ .choose then none
      else match currentObservation? state with
        | none => none
        | some _ => some { state with cursor := state.cursor + 1 }
  | .testCurrent =>
      if state.core.published.isSome then none
      else if state.phase ≠ .screened then none
      else match currentObservation? state with
        | none => none
        | some observation => do
            let core ← ArchiveLab.step demoConfig state.core
              (coreAction state (.test observation.id))
            some { core, cursor := state.cursor + 1, phase := .choose }
  | .triangulateSupport =>
      if state.core.published.isSome then none
      else if !atAnalysisB state then none
      else do
        let core ← ArchiveLab.step demoConfig state.core
          (coreAction state (.triangulate thermalRise carrierBeat))
        some { state with core }
  | .publish hypothesis =>
      if state.core.published.isSome then none
      else if !atAnalysisB state then none
      else do
        let core ← ArchiveLab.step demoConfig state.core
          (coreAction state (.publish hypothesis))
        some { state with core }

def replayLab : LabState → List LabMove → Option LabState
  | state, [] => some state
  | state, move :: moves => do
      let next ← labStep state move
      replayLab next moves

def winningLabMoves : List LabMove :=
  [ .screenCurrent, .testCurrent
  , .screenCurrent, .testCurrent
  , .passCurrent
  , .screenCurrent, .testCurrent
  , .screenCurrent, .testCurrent
  , .screenCurrent, .testCurrent
  , .passCurrent
  , .screenCurrent, .testCurrent
  , .triangulateSupport
  , .publish resonance
  ]

def winningLabB : Bool :=
  match replayLab initialLabState winningLabMoves with
  | none => false
  | some state =>
      decide (state.core.published = some resonance) &&
      decide (state.core.operationsSpent = 14) &&
      decide (supportScore demoConfig state.core resonance = 5) &&
      decide (refuteScore demoConfig state.core resonance = 0) &&
      decide (informationGain demoConfig state.core = 20) &&
      witnessedContradictionB demoConfig state.core resonance

theorem winning_lab_route_is_exact_archive_lab_play : winningLabB = true := by
  native_decide

/-! ## Complete reachable table -/

def expandState (state : LabState) : List LabState :=
  labMoves.filterMap (labStep state)

def exploreAtMost : Nat → List LabState
  | 0 => [initialLabState]
  | fuel + 1 =>
      let prior := exploreAtMost fuel
      (prior ++ prior.flatMap expandState).eraseDups

def states : List LabState := exploreAtMost EXPLORATION_HORIZON

inductive RefusalReason where
  | terminal
  | wrongPhase
  | noCurrentSpecimen
  | analysisNotReached
  | budgetExhausted
  | notTriangulatable
  | notPublishable
  | coreRejected
deriving DecidableEq

def RefusalReason.id : RefusalReason → String
  | .terminal => "terminal"
  | .wrongPhase => "wrong-phase"
  | .noCurrentSpecimen => "no-current-specimen"
  | .analysisNotReached => "analysis-not-reached"
  | .budgetExhausted => "budget-exhausted"
  | .notTriangulatable => "not-triangulatable"
  | .notPublishable => "not-publishable"
  | .coreRejected => "core-rejected"

def classifyRefusal (state : LabState) : LabMove → RefusalReason
  | .screenCurrent =>
      if state.core.published.isSome then .terminal
      else if state.phase ≠ .choose then .wrongPhase
      else if (currentObservation? state).isNone then .noCurrentSpecimen
      else if demoRawConfig.operationBudget ≤ state.core.operationsSpent then .budgetExhausted
      else .coreRejected
  | .passCurrent =>
      if state.core.published.isSome then .terminal
      else if state.phase ≠ .choose then .wrongPhase
      else .noCurrentSpecimen
  | .testCurrent =>
      if state.core.published.isSome then .terminal
      else if state.phase ≠ .screened then .wrongPhase
      else if (currentObservation? state).isNone then .noCurrentSpecimen
      else if demoRawConfig.operationBudget ≤ state.core.operationsSpent then .budgetExhausted
      else .coreRejected
  | .triangulateSupport =>
      if state.core.published.isSome then .terminal
      else if !atAnalysisB state then .analysisNotReached
      else if demoRawConfig.operationBudget ≤ state.core.operationsSpent then .budgetExhausted
      else .notTriangulatable
  | .publish _ =>
      if state.core.published.isSome then .terminal
      else if !atAnalysisB state then .analysisNotReached
      else if demoRawConfig.operationBudget ≤ state.core.operationsSpent then .budgetExhausted
      else .notPublishable

structure TransitionRow where
  state : LabState
  move : LabMove
  result : Option LabState
  reason : Option RefusalReason
deriving DecidableEq

def transitionRow (state : LabState) (move : LabMove) : TransitionRow :=
  let result := labStep state move
  { state, move, result
    reason := if result.isSome then none else some (classifyRefusal state move) }

def transitions : List TransitionRow :=
  states.flatMap fun state => labMoves.map (transitionRow state)

def tableClosedB : Bool :=
  transitions.all fun row =>
    match row.result with
    | none => true
    | some next => decide (next ∈ states)

def refusalReasonsCompleteB : Bool :=
  transitions.all fun row =>
    match row.result, row.reason with
    | some _, none => true
    | none, some _ => true
    | _, _ => false

/-! ## Stable identities and display projections -/

def observationIdsIn (selected : Finset ObservationId) : List ObservationId :=
  (demoObservations.filter fun observation => decide (observation.id ∈ selected)).map (·.id)

def pairId (pair : PairKey) : String :=
  toString pair.low.value ++ ":" ++ toString pair.high.value

def knownPairIds (state : LabState) : List String :=
  let pair := PairKey.canonical thermalRise carrierBeat
  if pair ∈ state.core.triangulations then [pairId pair] else []

def phaseId : LabPhase → String
  | .choose => "choose"
  | .screened => "screened"

def stateId (state : LabState) : String :=
  let screened := String.intercalate ";"
    ((observationIdsIn state.core.screened).map fun id => toString id.value)
  let tested := String.intercalate ";"
    ((observationIdsIn state.core.tested).map fun id => toString id.value)
  let pairs := String.intercalate ";" (knownPairIds state)
  let published := match state.core.published with
    | none => "none"
    | some hypothesis => toString hypothesis.value
  "a:c=" ++ toString state.cursor ++ ":p=" ++ phaseId state.phase ++
    ":n=" ++ toString state.core.nextSequence ++
    ":o=" ++ toString state.core.operationsSpent ++
    ":s=" ++ screened ++ ":t=" ++ tested ++ ":g=" ++ pairs ++ ":u=" ++ published

def moveId : LabMove → String
  | .screenCurrent => "screen-current"
  | .passCurrent => "pass-current"
  | .testCurrent => "test-current"
  | .triangulateSupport => "triangulate:0:1"
  | .publish hypothesis => "publish:" ++ toString hypothesis.value

def moveTag : LabMove → String
  | .screenCurrent => "screen"
  | .passCurrent => "pass"
  | .testCurrent => "test"
  | .triangulateSupport => "triangulate"
  | .publish _ => "publish"

def hypothesisLabel (hypothesis : HypothesisId) : String :=
  match hypothesis.value with
  | 0 => "Resonance"
  | 1 => "Maintenance beacon"
  | 2 => "External carrier"
  | 3 => "Sensor artifact"
  | value => "Hypothesis " ++ toString value

def moveLabel : LabMove → String
  | .screenCurrent => "Screen current specimen"
  | .passCurrent => "Pass unopened specimen"
  | .testCurrent => "Complete specimen test"
  | .triangulateSupport => "Triangulate independent support"
  | .publish hypothesis => "Publish: " ++ hypothesisLabel hypothesis

def observationLabel (observation : Observation) : String :=
  match observation.id.value with
  | 0 => "Thermal rise"
  | 1 => "Carrier beat"
  | 2 => "Regular ping"
  | 3 => "Timing drift"
  | 4 => "Hull scrape"
  | 5 => "Pressure silence"
  | 6 => "Sensor dropout"
  | 7 => "Gyro continuity"
  | value => "Observation " ++ toString value

def bearingKind : Bearing → String
  | .supports _ => "supports"
  | .refutes _ => "refutes"

def verdictId : EvidenceVerdict → String
  | .sound => "sound"
  | .contaminated => "contaminated"

def observationStatus (state : LabState) (observation : Observation) : String :=
  if observation.id ∈ state.core.tested then "tested"
  else if observation.id ∈ state.core.screened then "screened"
  else if observation.id.value < state.cursor then "passed"
  else "pending"

def bearingJson (bearing : Bearing) : String :=
  "{\"kind\":" ++ jsonString (bearingKind bearing) ++
    ",\"hypothesis\":" ++ toString bearing.hypothesis.value ++ "}"

def observationJson (state : LabState) (observation : Observation) : String :=
  let screened := decide (observation.id ∈ state.core.screened)
  let tested := decide (observation.id ∈ state.core.tested)
  "{\"id\":" ++ toString observation.id.value ++
    ",\"label\":" ++ jsonString (observationLabel observation) ++
    ",\"status\":" ++ jsonString (observationStatus state observation) ++
    ",\"artifact_id\":" ++ toString observation.entry.artifact.artifactId.value ++
    ",\"source_mission\":" ++ toString observation.sourceMission.value ++
    ",\"custodian\":" ++ jsonString (bytes32Hex observation.custody.holder) ++
    ",\"transfer_sequence\":" ++ toString observation.custody.transferSequence ++
    ",\"bearing\":" ++ (if screened then bearingJson observation.bearing else "null") ++
    ",\"weight\":" ++ (if tested then toString observation.weight.val else "null") ++
    ",\"information\":" ++
      (if tested then toString observation.information.val else "null") ++
    ",\"verdict\":" ++
      (if tested then jsonString (verdictId observation.verdict) else "null") ++ "}"

def hypothesisJson (state : LabState) (hypothesis : HypothesisId) : String :=
  let support := supportScore demoConfig state.core hypothesis
  let refutation := refuteScore demoConfig state.core hypothesis
  let contradiction := decide (0 < support ∧ support < refutation)
  "{\"id\":" ++ toString hypothesis.value ++
    ",\"label\":" ++ jsonString (hypothesisLabel hypothesis) ++
    ",\"support\":" ++ toString support ++
    ",\"refutation\":" ++ toString refutation ++
    ",\"contradiction\":" ++ jsonBool contradiction ++
    ",\"publishable\":" ++ jsonBool (publishableB demoConfig state.core hypothesis) ++ "}"

def currentObservationId (state : LabState) : String :=
  match currentObservation? state with
  | none => "null"
  | some observation => toString observation.id.value

def publishedId (state : LabState) : String :=
  match state.core.published with
  | none => "null"
  | some hypothesis => toString hypothesis.value

def contradictionIds (state : LabState) : List HypothesisId :=
  demoRawConfig.hypotheses.filter fun hypothesis =>
    let support := supportScore demoConfig state.core hypothesis
    let refutation := refuteScore demoConfig state.core hypothesis
    decide (0 < support ∧ support < refutation)

def stateJson (state : LabState) : String :=
  let remaining := demoRawConfig.operationBudget - state.core.operationsSpent
  "    {\"id\":" ++ jsonString (stateId state) ++
    ",\"terminal\":" ++ jsonBool state.core.published.isSome ++
    ",\"view\":{\"cursor\":" ++ toString state.cursor ++
    ",\"phase\":" ++ jsonString (phaseId state.phase) ++
    ",\"current_observation\":" ++ currentObservationId state ++
    ",\"operations_spent\":" ++ toString state.core.operationsSpent ++
    ",\"operation_budget\":" ++ toString demoRawConfig.operationBudget ++
    ",\"operations_remaining\":" ++ toString remaining ++
    ",\"screened\":" ++ jsonArray
      ((observationIdsIn state.core.screened).map fun id => toString id.value) ++
    ",\"tested\":" ++ jsonArray
      ((observationIdsIn state.core.tested).map fun id => toString id.value) ++
    ",\"triangulations\":" ++ jsonArray ((knownPairIds state).map jsonString) ++
    ",\"published\":" ++ publishedId state ++
    ",\"information\":" ++ toString (informationGain demoConfig state.core) ++
    ",\"contradictions\":" ++ jsonArray
      ((contradictionIds state).map fun id => toString id.value) ++
    ",\"observations\":" ++ jsonArray (demoObservations.map (observationJson state)) ++
    ",\"hypotheses\":" ++ jsonArray
      (demoRawConfig.hypotheses.map (hypothesisJson state)) ++ "}}"

def actionJson (move : LabMove) : String :=
  let hypothesis := match move with
    | .publish hypothesis => toString hypothesis.value
    | _ => "null"
  "    {\"id\":" ++ jsonString (moveId move) ++
    ",\"tag\":" ++ jsonString (moveTag move) ++
    ",\"label\":" ++ jsonString (moveLabel move) ++
    ",\"hypothesis\":" ++ hypothesis ++ "}"

def transitionEffect : LabMove → String
  | .screenCurrent => "screened"
  | .passCurrent => "passed"
  | .testCurrent => "tested"
  | .triangulateSupport => "triangulated"
  | .publish _ => "published"

def recordJson (state : LabState) : String :=
  match state.core.published with
  | none => "null"
  | some hypothesis =>
      "{\"fiction_status\":\"beta-only\",\"hypothesis\":" ++
        toString hypothesis.value ++
        ",\"artifact\":\"" ++ toString researchArtifact.missionId.value ++ ":" ++
          toString researchArtifact.artifactId.value ++ "\"" ++
        ",\"evidence\":" ++ jsonArray
          ((observationIdsIn state.core.tested).map fun id => toString id.value) ++
        ",\"triangulations\":" ++ jsonArray ((knownPairIds state).map jsonString) ++
        ",\"support\":" ++ toString (supportScore demoConfig state.core hypothesis) ++
        ",\"refutation\":" ++ toString (refuteScore demoConfig state.core hypothesis) ++
        ",\"information\":" ++ toString (informationGain demoConfig state.core) ++
        ",\"operations_spent\":" ++ toString state.core.operationsSpent ++
        ",\"canon_claim\":false,\"reward_claim\":false}"

def transitionJson (row : TransitionRow) : String :=
  "    {\"state\":" ++ jsonString (stateId row.state) ++
    ",\"action\":" ++ jsonString (moveId row.move) ++
    ",\"verdict\":" ++ jsonString (if row.result.isSome then "accept" else "refuse") ++
    ",\"next\":" ++ (match row.result with
      | none => "null"
      | some next => jsonString (stateId next)) ++
    ",\"reason\":" ++ (match row.reason with
      | none => "null"
      | some reason => jsonString reason.id) ++
    ",\"effect\":" ++ (match row.result with
      | none => "null"
      | some _ => jsonString (transitionEffect row.move)) ++
    ",\"record\":" ++ (match row.result with
      | none => "null"
      | some next => if next.core.published.isSome then recordJson next else "null") ++ "}"

def routeJson : String :=
  "    {\"id\":\"unique-research-plan\",\"initial_state\":" ++
    jsonString (stateId initialLabState) ++
    ",\"actions\":" ++ jsonArray (winningLabMoves.map fun move => jsonString (moveId move)) ++ "}"

def descriptorJson : String :=
  "{\n" ++
  "  \"format\":\"" ++ FORMAT ++ "\",\n" ++
  "  \"schema_version\":" ++ toString SCHEMA_VERSION ++ ",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.ArchiveLab\",\n" ++
  "  \"fixture_module\":\"Dregg2.Games.PathOfAngels.ArchiveLabDemonstrator\",\n" ++
  "  \"fiction_status\":\"beta-only-demonstrator\",\n" ++
  "  \"authority\":{\"transition\":\"lean-table\",\"deduction\":\"lean-projection\"," ++
    "\"canon_promotion\":false,\"asset_minting\":false,\"reward_settlement\":false},\n" ++
  "  \"research\":{\"mission_id\":" ++ toString researchMissionId.value ++
    ",\"artifact_id\":" ++ toString researchArtifact.artifactId.value ++
    ",\"source_mission_id\":" ++ toString sourceMissionId.value ++
    ",\"content_epoch\":" ++ toString epoch.value ++
    ",\"observation_count\":" ++ toString demoObservations.length ++
    ",\"hypothesis_count\":" ++ toString demoRawConfig.hypotheses.length ++
    ",\"operation_budget\":" ++ toString demoRawConfig.operationBudget ++
    ",\"winning_plan_count\":1},\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (stateId initialLabState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map stateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (labMoves.map actionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (transitions.map transitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"reference_routes\":" ++ jsonPrettyArray [routeJson] ++ "\n" ++
  "}\n"

def stateIdsUniqueB : Bool := (states.map stateId).Nodup
def moveIdsUniqueB : Bool := (labMoves.map moveId).Nodup
def transitionKeysUniqueB : Bool :=
  (transitions.map fun row => (stateId row.state, moveId row.move)).Nodup

def terminalStates : List LabState :=
  states.filter fun state => state.core.published.isSome

def descriptorParsesB : Bool :=
  match Json.parse descriptorJson with
  | .ok _ => true
  | .error _ => false

theorem emitted_winning_route_accepts : winningLabB = true := by native_decide
theorem emitted_has_exactly_822_reachable_states : states.length = 822 := by native_decide
theorem emitted_has_exactly_8_actions : labMoves.length = 8 := by native_decide
theorem emitted_has_exactly_6576_transition_rows : transitions.length = 6576 := by native_decide
theorem emitted_state_ids_unique : stateIdsUniqueB = true := by native_decide
theorem emitted_move_ids_unique : moveIdsUniqueB = true := by native_decide
theorem emitted_transition_keys_unique : transitionKeysUniqueB = true := by native_decide
theorem emitted_table_closed : tableClosedB = true := by native_decide
theorem emitted_refusals_are_explicit : refusalReasonsCompleteB = true := by native_decide
theorem emitted_has_exactly_one_terminal_research_plan : terminalStates.length = 1 := by
  native_decide
theorem emitted_descriptor_is_json : descriptorParsesB = true := by native_decide

#assert_compiled winning_lab_route_is_exact_archive_lab_play
#assert_compiled emitted_winning_route_accepts
#assert_compiled emitted_has_exactly_822_reachable_states
#assert_compiled emitted_has_exactly_8_actions
#assert_compiled emitted_has_exactly_6576_transition_rows
#assert_compiled emitted_state_ids_unique
#assert_compiled emitted_move_ids_unique
#assert_compiled emitted_transition_keys_unique
#assert_compiled emitted_table_closed
#assert_compiled emitted_refusals_are_explicit
#assert_compiled emitted_has_exactly_one_terminal_research_plan
#assert_compiled emitted_descriptor_is_json

end Dregg2.Games.PathOfAngels.ArchiveLabDemonstratorEmit

/-- Print the canonical standalone Archive Lab browser artifact to stdout. -/
def main : IO Unit :=
  IO.print Dregg2.Games.PathOfAngels.ArchiveLabDemonstratorEmit.descriptorJson
