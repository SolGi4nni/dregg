/-
# ExpeditionDemonstratorEmit — browser-consumable finite Lean authority

This isolated emitter closes the fiction-neutral demonstrator over its complete
role-correct action alphabet through the authored eight-action horizon.  Browsers
receive display projections and a finite state/action table; they do not implement
a second expedition transition function.

The emitted beta observations remain provisional candidates.  No Canon, market,
asset, live bundle, or web module is imported here.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.ExpeditionDemonstrator
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ExpeditionDemonstratorEmit

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DeckGraph
open Dregg2.Games.PathOfAngels.DeckExpedition
open Dregg2.Games.PathOfAngels.ExpeditionDemonstrator

set_option autoImplicit false

abbrev FORMAT : String := "POA-EXPEDITION-TABLE"
abbrev SCHEMA_VERSION : Nat := 1
abbrev AUTHORED_HORIZON : Nat := 8

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

private def byteHex (byte : Fin 256) : String :=
  String.ofList [lowerHexDigit (byte.val / 16), lowerHexDigit (byte.val % 16)]

def bytes32Hex (digest : Digest32) : String :=
  String.join (digest.bytes.map byteHex)

/-! ## Canonical state and action identities -/

def roleId : OfficerRole → String
  | .pathfinder => "pathfinder"
  | .engineer => "engineer"
  | .containment => "containment"
  | .medic => "medic"

def artifactId (artifact : ArtifactRef) : String :=
  toString artifact.missionId.value ++ ":" ++ toString artifact.artifactId.value

def custodyId : Custody → String
  | .onDeck room => "deck:" ++ toString room.value
  | .carried officer => "carried:" ++ toString officer.value
  | .secured => "secured"

def visitedRoomIds (state : State) : List RoomId :=
  (demoPack.rooms.filter fun room => decide (room.id ∈ state.visited)).map Room.id

def discoveredArtifactIds (run : RunState) : List ArtifactRef :=
  (demoConfig.raw.discoveries.filter fun discovery =>
    decide (discovery.artifact ∈ run.discoveries)).map DiscoverySpec.artifact

def resolvedHazardIds (run : RunState) : List HazardId :=
  (demoConfig.raw.hazards.filter fun hazard =>
    decide (hazard.id ∈ run.resolvedHazards)).map HazardSpec.id

def officerStateId (officer : OfficerState) : String :=
  toString officer.id.value ++ "=" ++ toString officer.injury.val

def salvageStateId (record : SalvageRecord) : String :=
  toString record.id.value ++ "=" ++ custodyId record.custody

/-- Collision-free over this emitted fixture state set, as checked by the compiled
gate below.  The demonstrator fixes the pack/config/player/party/run-key
relationships; this projection is not claimed to be injective for arbitrary
`DeckExpedition.State` values. -/
def stateId (state : State) : String :=
  let officers := String.intercalate ";" (state.officers.map officerStateId)
  let visited := String.intercalate ";" ((visitedRoomIds state).map fun id => toString id.value)
  let salvage := String.intercalate ";" (state.salvage.map salvageStateId)
  let active := match state.active with
    | none => "closed"
    | some run =>
        "active:" ++ toString run.position.room.value ++ ":" ++
        toString run.position.phase.val ++ ":" ++ toString run.turnsUsed ++ ":" ++
        toString run.suppliesSpent ++ ":h=" ++
        String.intercalate ";" ((resolvedHazardIds run).map fun id => toString id.value) ++
        ":d=" ++ String.intercalate ";" ((discoveredArtifactIds run).map artifactId)
  "s:p=" ++ bytes32Hex state.playerKey ++ ":" ++ toString state.day.value ++ ":" ++
    toString state.runsUsed ++ ":" ++
    toString state.nextCounter ++ ":c=" ++ toString state.consumed.card ++
    ":o=" ++ officers ++ ":v=" ++ visited ++ ":x=" ++ salvage ++ ":" ++ active

def actionId : Action → String
  | .begin key _ => "begin:" ++ toString key.counter
  | .traverse hotspot => "traverse:" ++ toString hotspot.value
  | .confront hazard officer =>
      "confront:" ++ toString hazard.value ++ ":" ++ toString officer.value
  | .survey artifact officer =>
      "survey:" ++ artifactId artifact ++ ":" ++ toString officer.value
  | .recover salvage officer =>
      "recover:" ++ toString salvage.value ++ ":" ++ toString officer.value
  | .treat medicOfficer target =>
      "treat:" ++ toString medicOfficer.value ++ ":" ++ toString target.value
  | .extract => "extract"
  | .withdraw => "withdraw"

def actionLabel : Action → String
  | .begin _ _ => "Begin expedition"
  | .traverse hotspot => "Traverse passage " ++ toString hotspot.value
  | .confront hazard _ => "Contain hazard " ++ toString hazard.value
  | .survey artifact _ => "Survey candidate " ++ artifactId artifact
  | .recover salvage _ => "Recover salvage " ++ toString salvage.value
  | .treat _ target => "Treat officer " ++ toString target.value
  | .extract => "Extract"
  | .withdraw => "Withdraw"

/-! ## Complete bounded table -/

def horizonStates : List State :=
  ((exploreAtMost AUTHORED_HORIZON).map StrategyNode.state).eraseDups

/-- One-step closure adds only terminal withdrawal projections from active states
at the turn cap.  This keeps every accepted `next` addressable without pretending
that a ninth turn-consuming action belongs to the authored horizon. -/
def closureStates : List State :=
  horizonStates.flatMap fun state =>
    authoredActions.filterMap fun action =>
      (step demoConfig state action).map StepResult.state

def states : List State := (horizonStates ++ closureStates).eraseDups

inductive RefusalReason where
  | invalidState
  | terminal
  | turnLimit
  | unresolvedHazard
  | unknownHotspot
  | wrongOriginOrPhase
  | unknownHazard
  | officerNotReady
  | wrongRoom
  | alreadyResolved
  | supplyLimit
  | unknownDiscovery
  | alreadySurveyed
  | unknownSalvage
  | custodyMismatch
  | targetNotInParty
  | targetUninjured
  | notAtExtraction
  | outcomeRejected
  | beginExcluded
  | postStateInvariant
deriving DecidableEq

def RefusalReason.id : RefusalReason → String
  | .invalidState => "invalid-state"
  | .terminal => "terminal"
  | .turnLimit => "turn-limit"
  | .unresolvedHazard => "unresolved-hazard"
  | .unknownHotspot => "unknown-hotspot"
  | .wrongOriginOrPhase => "wrong-origin-or-phase"
  | .unknownHazard => "unknown-hazard"
  | .officerNotReady => "officer-not-ready"
  | .wrongRoom => "wrong-room"
  | .alreadyResolved => "already-resolved"
  | .supplyLimit => "supply-limit"
  | .unknownDiscovery => "unknown-discovery"
  | .alreadySurveyed => "already-surveyed"
  | .unknownSalvage => "unknown-salvage"
  | .custodyMismatch => "custody-mismatch"
  | .targetNotInParty => "target-not-in-party"
  | .targetUninjured => "target-uninjured"
  | .notAtExtraction => "not-at-extraction"
  | .outcomeRejected => "outcome-rejected"
  | .beginExcluded => "begin-excluded"
  | .postStateInvariant => "post-state-invariant"

private def classifyActiveRefusal (state : State) (run : RunState) : Action → RefusalReason
  | .begin _ _ => .beginExcluded
  | .traverse hotspotId =>
      if run.turnsUsed ≥ demoConfig.raw.turnBudget then .turnLimit
      else if unresolvedHazardAtB demoConfig run then .unresolvedHazard
      else match hotspotById? demoPack.hotspots hotspotId with
        | none => .unknownHotspot
        | some hotspot =>
            match traverseHotspot run.position hotspot with
            | none => .wrongOriginOrPhase
            | some _ => .postStateInvariant
  | .confront hazardId officerId =>
      if run.turnsUsed ≥ demoConfig.raw.turnBudget then .turnLimit
      else match hazardById? demoConfig.raw.hazards hazardId with
        | none => .unknownHazard
        | some hazard =>
            if !officerReadyForB demoConfig state run officerId .containment then .officerNotReady
            else if hazard.room != run.position.room then .wrongRoom
            else if hazard.id ∈ run.resolvedHazards then .alreadyResolved
            else if demoConfig.raw.operationalSupplyBudget <
                run.suppliesSpent + hazard.supplyCost then .supplyLimit
            else .postStateInvariant
  | .survey artifact officerId =>
      if run.turnsUsed ≥ demoConfig.raw.turnBudget then .turnLimit
      else match discoveryByArtifact? demoConfig.raw.discoveries artifact with
        | none => .unknownDiscovery
        | some discovery =>
            if !officerReadyForB demoConfig state run officerId .pathfinder then .officerNotReady
            else if discovery.room != run.position.room then .wrongRoom
            else if artifact ∈ run.discoveries then .alreadySurveyed
            else .postStateInvariant
  | .recover salvageId officerId =>
      if run.turnsUsed ≥ demoConfig.raw.turnBudget then .turnLimit
      else match salvageSpecById? demoConfig.raw.salvage salvageId,
          salvageRecordById? state.salvage salvageId with
        | none, _ => .unknownSalvage
        | _, none => .unknownSalvage
        | some spec, some record =>
            if !officerReadyForB demoConfig state run officerId .engineer then .officerNotReady
            else if spec.room != run.position.room then .wrongRoom
            else if record.custody != .onDeck spec.room then .custodyMismatch
            else .postStateInvariant
  | .treat medicId targetId =>
      if run.turnsUsed ≥ demoConfig.raw.turnBudget then .turnLimit
      else match officerById? state.officers targetId with
        | none => .officerNotReady
        | some target =>
            if !officerReadyForB demoConfig state run medicId .medic then .officerNotReady
            else if targetId ∉ run.party then .targetNotInParty
            else if target.injury.val = 0 then .targetUninjured
            else if demoConfig.raw.operationalSupplyBudget <
                run.suppliesSpent + TREATMENT_SUPPLY_COST then .supplyLimit
            else .postStateInvariant
  | .extract =>
      if run.turnsUsed ≥ demoConfig.raw.turnBudget then .turnLimit
      else if run.position.room != demoPack.extraction then .notAtExtraction
      else if unresolvedHazardAtB demoConfig run then .unresolvedHazard
      else if (ActivityOutcome.validate demoConfig.raw.policy
          (rawOutcome demoConfig state run)).isNone then .outcomeRejected
      else .postStateInvariant
  | .withdraw => .postStateInvariant

def classifyRefusal (state : State) (action : Action) : RefusalReason :=
  if validStateB demoConfig state != true then .invalidState
  else match state.active with
    | none => .terminal
    | some run => classifyActiveRefusal state run action

def refusalReason? (state : State) (action : Action) : Option RefusalReason :=
  if (step demoConfig state action).isSome then none
  else some (classifyRefusal state action)

structure TransitionRow where
  state : State
  action : Action
  result : Option (StepResult demoConfig)
  reason : Option RefusalReason
deriving DecidableEq

def transitionRow (state : State) (action : Action) : TransitionRow where
  state
  action
  result := step demoConfig state action
  reason := refusalReason? state action

def transitions : List TransitionRow :=
  states.flatMap fun state => authoredActions.map (transitionRow state)

theorem transitions_length :
    transitions.length = states.length * authoredActions.length := by
  simp [transitions]

/-- Every accepting row is definitionally the result of the authoritative Lean
step, including its exact receipt; no emitter-local transition exists. -/
theorem transition_row_exact_step (row : TransitionRow) (h : row ∈ transitions) :
    row.result = step demoConfig row.state row.action := by
  simp only [transitions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨state, _hstate, action, _haction, rfl⟩ := h
  rfl

def refusalReasonsCompleteB : Bool :=
  transitions.all fun row =>
    match row.result, row.reason with
    | some _, none => true
    | none, some _ => true
    | _, _ => false

def noInvariantFallbackB : Bool :=
  transitions.all fun row => row.reason != some .postStateInvariant

def tableClosedB : Bool :=
  transitions.all fun row =>
    match row.result with
    | none => true
    | some result => decide (result.state ∈ states)

def terminalRowsRefuseB : Bool :=
  transitions.all fun row =>
    match row.state.active with
    | none => row.result.isNone
    | some _ => true

theorem transition_refusal_is_explicit (row : TransitionRow) (hrow : row ∈ transitions)
    (hrefused : row.result = none) : ∃ reason, row.reason = some reason := by
  simp only [transitions, List.mem_flatMap, List.mem_map] at hrow
  obtain ⟨state, _hstate, action, _haction, rfl⟩ := hrow
  simp only [transitionRow] at hrefused ⊢
  simp [refusalReason?, hrefused]

def rowFor? : List TransitionRow → State → Action → Option TransitionRow
  | [], _, _ => none
  | row :: rows, state, action =>
      if row.state = state ∧ row.action = action then some row
      else rowFor? rows state action

def tableStep (state : State) (action : Action) : Option (StepResult demoConfig) := do
  let row ← rowFor? transitions state action
  row.result

def tableLookupExactB : Bool :=
  states.all fun state =>
    authoredActions.all fun action =>
      decide (tableStep state action = step demoConfig state action)

def replayRows : Nat → State → List Action →
    Option (State × List (ExtractionReceipt demoConfig))
  | _, state, [] => some (state, [])
  | 0, _, _ :: _ => none
  | fuel + 1, state, action :: actions => do
      let result ← tableStep state action
      let (finalState, receipts) ← replayRows fuel result.state actions
      let receipts := match result.receipt with
        | none => receipts
        | some receipt => receipt :: receipts
      some (finalState, receipts)

def safeRouteReplaysFromRowsB : Bool :=
  decide (replayRows safeSurveyPlan.length begunState safeSurveyPlan =
    replay demoConfig safeSurveyPlan.length begunState safeSurveyPlan)

def salvageRouteReplaysFromRowsB : Bool :=
  decide (replayRows salvagePushPlan.length begunState salvagePushPlan =
    replay demoConfig salvagePushPlan.length begunState salvagePushPlan)

def emittedSafeBetaB : Bool :=
  match replayRows safeSurveyPlan.length begunState safeSurveyPlan with
  | some (_, [receipt]) =>
      decide (safeObservation ∈ receipt.outcome.betaCandidates) &&
      decide (receipt.recovered = ∅)
  | _ => false

def emittedSalvageRelicB : Bool :=
  match replayRows salvagePushPlan.length begunState salvagePushPlan with
  | some (state, [receipt]) =>
      decide (receipt.recovered = {salvageFind.id}) &&
      decide (receipt.outcome.contribution.relics = {demoRelic}) &&
      decide (salvageRecordById? state.salvage salvageFind.id =
        some { id := salvageFind.id, custody := .secured })
  | _ => false

/-! ## Display projections and canonical JSON -/

def actionTag : Action → String
  | .begin _ _ => "begin"
  | .traverse _ => "traverse"
  | .confront _ _ => "confront"
  | .survey _ _ => "survey"
  | .recover _ _ => "recover"
  | .treat _ _ => "treat"
  | .extract => "extract"
  | .withdraw => "withdraw"

def actionRole? : Action → Option OfficerRole
  | .confront _ _ => some .containment
  | .survey _ _ => some .pathfinder
  | .recover _ _ => some .engineer
  | .treat _ _ => some .medic
  | _ => none

private def officerJson (officer : OfficerState) : String :=
  let role := (profileById? demoConfig.raw.officers officer.id).map OfficerProfile.role
  "{\"id\":" ++ toString officer.id.value ++
    ",\"role\":" ++ (match role with | none => "null" | some value => jsonString (roleId value)) ++
    ",\"injury\":" ++ toString officer.injury.val ++
    ",\"available\":" ++ jsonBool (officer.injury.val < 3) ++ "}"

private def salvageJson (record : SalvageRecord) : String :=
  "{\"id\":" ++ toString record.id.value ++
    ",\"custody\":" ++ jsonString (custodyId record.custody) ++ "}"

private def activeField (state : State) (f : RunState → String) : String :=
  match state.active with
  | none => "null"
  | some run => f run

private def stateStatus (state : State) : String :=
  match state.active with
  | some _ => "active"
  | none =>
      if state.salvage.any fun record => record.custody == .secured
      then "inactive-with-secured-salvage" else "inactive"

/-- State projection never invents the edge event that produced an inactive
state.  Extraction and withdrawal are emitted only as transition effects. -/
theorem inactive_state_status_is_honest (state : State) (h : state.active = none) :
    stateStatus state = "inactive" ∨
      stateStatus state = "inactive-with-secured-salvage" := by
  simp only [stateStatus, h]
  split <;> simp_all

def stateJson (state : State) : String :=
  let visited := (visitedRoomIds state).map fun id => toString id.value
  let resolved := activeField state fun run =>
    jsonArray ((resolvedHazardIds run).map fun id => toString id.value)
  let discoveries := activeField state fun run =>
    jsonArray ((discoveredArtifactIds run).map fun artifact => jsonString (artifactId artifact))
  "    {\"id\":" ++ jsonString (stateId state) ++
    ",\"terminal\":" ++ jsonBool state.active.isNone ++
    ",\"view\":{\"status\":" ++ jsonString (stateStatus state) ++
    ",\"room\":" ++ activeField state (fun run => toString run.position.room.value) ++
    ",\"phase\":" ++ activeField state (fun run => toString run.position.phase.val) ++
    ",\"turns\":" ++ activeField state (fun run => toString run.turnsUsed) ++
    ",\"turn_limit\":" ++ toString demoConfig.raw.turnBudget ++
    ",\"supplies_spent\":" ++ activeField state (fun run => toString run.suppliesSpent) ++
    ",\"supply_limit\":" ++ toString demoConfig.raw.operationalSupplyBudget ++
    ",\"officers\":" ++ jsonArray (state.officers.map officerJson) ++
    ",\"visited_rooms\":" ++ jsonArray visited ++
    ",\"resolved_hazards\":" ++ resolved ++
    ",\"provisional_candidates\":" ++ discoveries ++
    ",\"salvage\":" ++ jsonArray (state.salvage.map salvageJson) ++ "}}"

def actionJson (action : Action) : String :=
  "    {\"id\":" ++ jsonString (actionId action) ++
    ",\"tag\":" ++ jsonString (actionTag action) ++
    ",\"label\":" ++ jsonString (actionLabel action) ++
    ",\"role\":" ++ (match actionRole? action with
      | none => "null"
      | some role => jsonString (roleId role)) ++ "}"

def recoveredSalvage (receipt : ExtractionReceipt demoConfig) : List SalvageId :=
  (demoConfig.raw.salvage.filter fun item =>
    decide (item.id ∈ receipt.recovered)).map SalvageSpec.id

def receiptBeta (receipt : ExtractionReceipt demoConfig) : List ArtifactRef :=
  (demoConfig.raw.discoveries.filter fun discovery =>
    decide (discovery.artifact ∈ receipt.outcome.betaCandidates)).map DiscoverySpec.artifact

def receiptRelics (receipt : ExtractionReceipt demoConfig) : List RelicId :=
  (demoConfig.raw.salvage.filter fun item =>
    decide (item.relic ∈ receipt.outcome.contribution.relics)).map SalvageSpec.relic

def receiptJson (receipt : ExtractionReceipt demoConfig) : String :=
  "{\"turns\":" ++ toString receipt.turnsUsed ++
    ",\"supplies_spent\":" ++ toString receipt.suppliesSpent ++
    ",\"final_room\":" ++ toString receipt.finalPosition.room.value ++
    ",\"recovered_salvage\":" ++
      jsonArray ((recoveredSalvage receipt).map fun id => toString id.value) ++
    ",\"provisional_candidates\":" ++
      jsonArray ((receiptBeta receipt).map fun artifact => jsonString (artifactId artifact)) ++
    ",\"relic_discoveries\":" ++
      jsonArray ((receiptRelics receipt).map fun id => toString id.value) ++ "}"

def transitionJson (row : TransitionRow) : String :=
  let next := row.result.map fun result => stateId result.state
  let receipt := row.result.bind StepResult.receipt
  let effect := match row.result with
    | none => none
    | some result =>
        if result.receipt.isSome then some "extracted"
        else match row.action with
          | .withdraw => some "withdrawn"
          | _ => some "advanced"
  "    {\"state\":" ++ jsonString (stateId row.state) ++
    ",\"action\":" ++ jsonString (actionId row.action) ++
    ",\"verdict\":" ++ jsonString (if next.isSome then "accept" else "refuse") ++
    ",\"next\":" ++ (match next with | none => "null" | some id => jsonString id) ++
    ",\"reason\":" ++ (match row.reason with
      | none => "null"
      | some reason => jsonString reason.id) ++
    ",\"effect\":" ++ (match effect with
      | none => "null"
      | some value => jsonString value) ++
    ",\"receipt\":" ++ (match receipt with
      | none => "null"
      | some value => receiptJson value) ++ "}"

def routeJson (id : String) (actions : List Action) : String :=
  "    {\"id\":" ++ jsonString id ++
    ",\"initial_state\":" ++ jsonString (stateId begunState) ++
    ",\"actions\":" ++ jsonArray (actions.map fun action => jsonString (actionId action)) ++ "}"

def descriptorJson : String :=
  "{\n" ++
  "  \"format\":\"" ++ FORMAT ++ "\",\n" ++
  "  \"schema_version\":" ++ toString SCHEMA_VERSION ++ ",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.DeckExpedition\",\n" ++
  "  \"fixture_module\":\"Dregg2.Games.PathOfAngels.ExpeditionDemonstrator\",\n" ++
  "  \"fiction_status\":\"non-canon-demonstrator\",\n" ++
  "  \"authority\":{\"transition\":\"lean-table\",\"beta_candidates\":\"provisional-only\"," ++
    "\"canon_promotion\":false,\"asset_minting\":false},\n" ++
  "  \"pack\":{\"id\":" ++ toString demoPack.packId.value ++
    ",\"activation_counter\":" ++ toString demoPack.activation.activationCounter ++
    ",\"content_epoch\":" ++ toString demoPack.activation.contentEpoch.value ++
    ",\"rooms\":" ++ toString demoPack.rooms.length ++
    ",\"hotspots\":" ++ toString demoPack.hotspots.length ++ "},\n" ++
  "  \"player_key\":" ++ jsonString (bytes32Hex demoPlayer) ++ ",\n" ++
  "  \"limits\":{\"authored_horizon\":" ++ toString AUTHORED_HORIZON ++
    ",\"turns\":" ++ toString demoConfig.raw.turnBudget ++
    ",\"operational_supplies\":" ++ toString demoConfig.raw.operationalSupplyBudget ++ "},\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (stateId begunState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map stateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (authoredActions.map actionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (transitions.map transitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"reference_routes\":" ++ jsonPrettyArray
    [routeJson "safe-beta" safeSurveyPlan, routeJson "salvage-relic" salvagePushPlan] ++ "\n" ++
  "}\n"

def descriptorParsesB : Bool :=
  match Json.parse descriptorJson with
  | .ok _ => true
  | .error _ => false

def stateIdsUniqueB : Bool := (states.map stateId).Nodup
def actionIdsUniqueB : Bool := (authoredActions.map actionId).Nodup

def transitionKeysUniqueB : Bool :=
  (transitions.map fun row => (stateId row.state, actionId row.action)).Nodup

def acceptingRows : List TransitionRow :=
  transitions.filter fun row => row.result.isSome

def refusingRows : List TransitionRow :=
  transitions.filter fun row => row.result.isNone

/-! ## Executable gates -/

theorem emitted_states_count : states.length = 53 := by native_decide
theorem emitted_actions_count : authoredActions.length = 16 := by native_decide
theorem emitted_transitions_count : transitions.length = 848 := by native_decide
theorem emitted_accepting_rows_count : acceptingRows.length = 92 := by native_decide
theorem emitted_refusing_rows_count : refusingRows.length = 756 := by native_decide
theorem emitted_horizon_is_one_step_closed : states = horizonStates := by native_decide
theorem emitted_state_ids_unique : stateIdsUniqueB = true := by native_decide
theorem emitted_action_ids_unique : actionIdsUniqueB = true := by native_decide
theorem emitted_transition_keys_unique : transitionKeysUniqueB = true := by native_decide
theorem emitted_table_closed : tableClosedB = true := by native_decide
theorem emitted_rows_have_explicit_refusals : refusalReasonsCompleteB = true := by native_decide
theorem emitted_rows_need_no_invariant_fallback : noInvariantFallbackB = true := by native_decide
theorem emitted_terminal_rows_refuse_extension : terminalRowsRefuseB = true := by native_decide
theorem emitted_lookup_is_exact_step : tableLookupExactB = true := by native_decide
theorem emitted_safe_route_replays_exactly : safeRouteReplaysFromRowsB = true := by native_decide
theorem emitted_salvage_route_replays_exactly : salvageRouteReplaysFromRowsB = true := by native_decide
theorem emitted_safe_route_returns_beta : emittedSafeBetaB = true := by native_decide
theorem emitted_salvage_route_returns_relic : emittedSalvageRelicB = true := by native_decide
theorem emitted_descriptor_is_json : descriptorParsesB = true := by native_decide

#assert_compiled transitions_length
#assert_compiled transition_row_exact_step
#assert_compiled transition_refusal_is_explicit
#assert_axioms inactive_state_status_is_honest
#assert_compiled emitted_states_count
#assert_compiled emitted_actions_count
#assert_compiled emitted_transitions_count
#assert_compiled emitted_accepting_rows_count
#assert_compiled emitted_refusing_rows_count
#assert_compiled emitted_horizon_is_one_step_closed
#assert_compiled emitted_state_ids_unique
#assert_compiled emitted_action_ids_unique
#assert_compiled emitted_transition_keys_unique
#assert_compiled emitted_table_closed
#assert_compiled emitted_rows_have_explicit_refusals
#assert_compiled emitted_rows_need_no_invariant_fallback
#assert_compiled emitted_terminal_rows_refuse_extension
#assert_compiled emitted_lookup_is_exact_step
#assert_compiled emitted_safe_route_replays_exactly
#assert_compiled emitted_salvage_route_replays_exactly
#assert_compiled emitted_safe_route_returns_beta
#assert_compiled emitted_salvage_route_returns_relic
#assert_compiled emitted_descriptor_is_json

end Dregg2.Games.PathOfAngels.ExpeditionDemonstratorEmit

/-- `lake env lean --run ExpeditionDemonstratorEmit.lean` writes the canonical
browser artifact to stdout.  It never mutates the live POAG1 bundle. -/
def main : IO Unit :=
  IO.print Dregg2.Games.PathOfAngels.ExpeditionDemonstratorEmit.descriptorJson
