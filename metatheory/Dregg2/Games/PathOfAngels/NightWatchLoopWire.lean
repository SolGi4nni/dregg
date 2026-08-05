/-
# NightWatchLoopWire — canonical public wire and planning boundary

This module is intentionally asymmetric.  Canonical JSON may construct public
player commands and proof-erased views, but it cannot construct a `Policy`,
`State`, `Streams`, handoff admission, draft-activation admission, or next-watch
admission.  Planning therefore takes the opaque Lean values as pre-existing
arguments, executes the public command through `NightWatchLoop.execute`, and
passes only its accepted transition to `NightWatchLoopRuntime.prepareBatch`.

The three authority-bearing command families are absent from `PublicCommandWire`.
Their textual tags fail closed at the parser.  Decoded state, policy, event, and
batch values are inert views; none is a restoration or authority decoder.
-/
import Lean.Data.Json
import Mathlib.Data.List.Sort
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Games.PathOfAngels.NightWatchLoopRuntime
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchLoopWire

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchLoop
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

abbrev COMMAND_FORMAT : String := "POA-NIGHT-WATCH-COMMAND-1"
abbrev POLICY_FORMAT : String := "POA-NIGHT-WATCH-POLICY-VIEW-1"
abbrev STATE_FORMAT : String := "POA-NIGHT-WATCH-STATE-VIEW-1"
abbrev EVENT_FORMAT : String := "POA-NIGHT-WATCH-EVENT-VIEW-1"
abbrev PLAN_INPUT_FORMAT : String := "POA-NIGHT-WATCH-PLAN-IN-1"
abbrev PLAN_OUTPUT_FORMAT : String := "POA-NIGHT-WATCH-PLAN-OUT-1"
abbrev WIRE_BYTE_LIMIT : Nat := 1024 * 1024
abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1
abbrev MAX_EVENT_VIEW_ITEMS : Nat := 16
abbrev MAX_HEADS : Nat := 5
abbrev MAX_ACCEPTED_EVENTS : Nat := 4

private def jsonString (value : String) : String := String.quote value
private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"
private def optionJson {T : Type} (encode : T → String) : Option T → String
  | none => "null"
  | some value => encode value
private def boolJson (value : Bool) : String := if value then "true" else "false"

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def boundedNat (limit value : Nat) : Except String Nat :=
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def objectNat (j : Json) (key : String) (limit : Nat := WIRE_U64_MAX) :
    Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

private def parseNat (j : Json) (limit : Nat := WIRE_U64_MAX) : Except String Nat := do
  boundedNat limit (← fromJson? j)

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def parseDigest (j : Json) : Except String Digest32 := do
  let spelling ← j.getStr?
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def parseBool (j : Json) : Except String Bool :=
  match j with
  | .bool value => pure value
  | _ => throw "expected boolean"

private def parseBoundedList {T : Type} (j : Json) (limit : Nat)
    (parse : Json → Except String T) : Except String (List T) := do
  let values := (← j.getArr?).toList
  if values.length > limit then throw "array exceeds wire bound"
  values.mapM parse

private def parseOption {T : Type} (j : Json)
    (parse : Json → Except String T) : Except String (Option T) :=
  match j with
  | .null => pure none
  | value => some <$> parse value

private def canonicalDecode {T : Type} (parse : Json → Except String T)
    (encode : T → String) (byteLimit : Nat) (bytes : String) : Option T :=
  if bytes.utf8ByteSize > byteLimit then none
  else match Json.parse bytes with
    | .error _ => none
    | .ok json => match parse json with
      | .error _ => none
      | .ok value => if _h : encode value = bytes then some value else none

private theorem canonicalDecode_reencodes {T : Type} (parse : Json → Except String T)
    (encode : T → String) (byteLimit : Nat) (bytes : String) (value : T)
    (accepted : canonicalDecode parse encode byteLimit bytes = some value) :
    encode value = bytes := by
  unfold canonicalDecode at accepted
  split at accepted <;> try contradiction
  next _ =>
    split at accepted <;> try contradiction
    next json _ =>
      split at accepted <;> try contradiction
      next decoded _ =>
        split at accepted
        next agreed =>
          have same : decoded = value := Option.some.inj accepted
          simpa [same] using agreed
        next _ => contradiction

/-! ## Stable finite codecs -/

def roleCode : CrewRole → Nat
  | .pathfinder => 0 | .engineer => 1 | .containment => 2 | .quartermaster => 3

def roleOfCode? : Nat → Option CrewRole
  | 0 => some .pathfinder | 1 => some .engineer
  | 2 => some .containment | 3 => some .quartermaster | _ => none

def routeOfCode? : Nat → Option Route
  | 0 => some .maintenanceSpine | 1 => some .signalGallery
  | 2 => some .sealedNave | _ => none

def maintenanceOfCode? : Nat → Option MaintenanceActionId
  | 0 => some .readTwinGauges | 1 => some .isolateFeederThree
  | 2 => some .routeReturnBypass | 3 => some .ventMemoryPocket
  | 4 => some .calibrateReturnFloat | 5 => some .reseedCultureCup
  | 6 => some .verifyFirstCycle | _ => none

def servingOfCode? : Nat → Option ServingChoiceId
  | 0 => some .steadyBowl | 1 => some .watchCup | 2 => some .softReturn | 3 => some .liftPacket
  | 4 => some .quietBroth | 5 => some .saltFold | 6 => some .sharedHeel | 7 => some .sealedFlask
  | 8 => some .amberMash | 9 => some .lampTea | 10 => some .watchCrust | 11 => some .returnSling
  | 12 => some .filterCake | 13 => some .brightPickle | 14 => some .drySleeve | 15 => some .sealedCrumb
  | 16 => some .witnessStew | 17 => some .intervalCoffee | 18 => some .recoveryPair | 19 => some .chalkPacket
  | 20 => some .coolGrain | 21 => some .trenchSalt | 22 => some .wrappedFruit | 23 => some .heatShieldTin
  | 24 => some .homePot | 25 => some .awakeSlice | 26 => some .blueTray | 27 => some .secondWindowKit
  | 28 => some .ordinaryBowl | 29 => some .scratchTonic | 30 => some .offWatchPudding
  | 31 => some .plainReturnKit | _ => none

def choiceOfCode? : Nat → Option ChoiceId
  | 100 => some .markMovingClearance | 101 => some .observeSecondMovement
  | 102 => some .ignoreMovingClearance | 110 => some .braceObservedRhythm
  | 111 => some .overdriveTruss | 112 => some .withdrawAtTruss
  | 120 => some .replaySharedIntervals | 121 => some .commitPrivateIntervals
  | 122 => some .misventRelief | 130 => some .triangulateFullSequence
  | 131 => some .preserveRawTrace | 132 => some .moveBeforeRepeat
  | 140 => some .screenCorridor | 141 => some .waitMovementCycle
  | 142 => some .abandonShoal | 150 => some .performTwoRoleHandoff
  | 151 => some .recordClosedThreshold | 152 => some .withdrawFromThreshold
  | 160 => some .exchangeCalibrationBlock | 161 => some .photographCradle
  | 162 => some .leaveCavityUntouched | _ => none

def terminalOfCode? : Nat → Option TerminalId
  | 0 => some (.authored .maintenanceReturn) | 1 => some (.authored .maintenanceDeep)
  | 2 => some (.authored .signalReturn) | 3 => some (.authored .signalDeep)
  | 4 => some (.authored .sealedReturn) | 5 => some (.authored .sealedDeep)
  | 100 => some (.mechanicalDraft .maintenanceReturnInjured)
  | 101 => some (.mechanicalDraft .maintenanceWithdrawn)
  | 102 => some (.mechanicalDraft .signalReturnPartial)
  | 103 => some (.mechanicalDraft .signalCorridorLost)
  | 104 => some (.mechanicalDraft .sealedReturnClosed)
  | _ => none

def phaseCode : Phase → Nat
  | .galley => 0 | .maintenance => 1 | .briefings => 2 | .routeSelection => 3
  | .encounters => 4 | .extraction => 5 | .returned => 6 | .debriefed => 7

def phaseOfCode? : Nat → Option Phase
  | 0 => some .galley | 1 => some .maintenance | 2 => some .briefings
  | 3 => some .routeSelection | 4 => some .encounters | 5 => some .extraction
  | 6 => some .returned | 7 => some .debriefed | _ => none

def gradeCode : RecoveryGrade → Nat
  | .clean => 0 | .injured => 1 | .marked => 2 | .lostOpportunity => 3
  | .containmentDebt => 4 | .failedReturn => 5

theorem roleOfCode_roleCode (role : CrewRole) : roleOfCode? (roleCode role) = some role := by
  cases role <;> rfl

theorem routeOfCode_code (route : Route) : routeOfCode? route.code = some route := by
  cases route <;> rfl

theorem maintenanceOfCode_code (action : MaintenanceActionId) :
    maintenanceOfCode? action.code = some action := by
  cases action <;> rfl

theorem servingOfCode_code (choice : ServingChoiceId) :
    servingOfCode? choice.code = some choice := by
  cases choice <;> rfl

theorem choiceOfCode_code (choice : ChoiceId) : choiceOfCode? choice.code = some choice := by
  cases choice <;> rfl

theorem terminalOfCode_code (terminal : TerminalId) :
    terminalOfCode? terminal.code = some terminal := by
  cases terminal with
  | authored outcome => cases outcome <;> rfl
  | mechanicalDraft outcome => cases outcome <;> rfl

theorem phaseOfCode_phaseCode (phase : Phase) : phaseOfCode? (phaseCode phase) = some phase := by
  cases phase <;> rfl

/-! ## Exact identity views -/

structure WorldWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
deriving DecidableEq

structure ContentWire where
  component : Digest32
  packDigest : Digest32
deriving DecidableEq

structure DayWire where
  contentEpoch : Nat
  dayIndex : Nat
deriving DecidableEq

structure OfficerWire where
  role : Nat
  recipient : Digest32
deriving DecidableEq

structure PolicyViewWire where
  world : WorldWire
  content : ContentWire
  missionId : Nat
  sessionId : Digest32
  missionDay : DayWire
  watchOfficer : Digest32
  roster : List OfficerWire
deriving DecidableEq

def WorldWire.ofSemantic (world : EventBatch.WorldIdentity) : WorldWire :=
  ⟨world.federationId, world.contentRoot, world.activationDigest,
   world.contentSession, world.contentEpoch.value⟩

def WorldWire.toSemantic (world : WorldWire) : EventBatch.WorldIdentity where
  federationId := world.federationId
  contentRoot := world.contentRoot
  activationDigest := world.activationDigest
  contentSession := world.contentSession
  contentEpoch := ⟨world.contentEpoch⟩

def PolicyViewWire.ofPolicy (policy : Policy) : PolicyViewWire where
  world := .ofSemantic policy.raw.world
  content := ⟨policy.raw.content.component, policy.raw.content.packDigest⟩
  missionId := policy.raw.missionId.value
  sessionId := policy.raw.sessionId
  missionDay := ⟨policy.raw.missionDay.contentEpoch.value, policy.raw.missionDay.dayIndex⟩
  watchOfficer := policy.raw.watchOfficer
  roster := policy.raw.roster.map fun seat => ⟨roleCode seat.role, seat.recipient⟩

def WorldWire.toJson (world : WorldWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex world.federationId) ++
  ",\"content_root\":" ++ jsonString (Emit.bytes32Hex world.contentRoot) ++
  ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex world.activationDigest) ++
  ",\"content_session\":" ++ jsonString (Emit.bytes32Hex world.contentSession) ++
  ",\"content_epoch\":" ++ toString world.contentEpoch ++ "}"

def ContentWire.toJson (content : ContentWire) : String :=
  "{\"component\":" ++ jsonString (Emit.bytes32Hex content.component) ++
  ",\"pack_digest\":" ++ jsonString (Emit.bytes32Hex content.packDigest) ++ "}"

def DayWire.toJson (day : DayWire) : String :=
  "{\"content_epoch\":" ++ toString day.contentEpoch ++
  ",\"day_index\":" ++ toString day.dayIndex ++ "}"

def OfficerWire.toJson (officer : OfficerWire) : String :=
  "{\"role\":" ++ toString officer.role ++
  ",\"recipient\":" ++ jsonString (Emit.bytes32Hex officer.recipient) ++ "}"

def PolicyViewWire.toJson (policy : PolicyViewWire) : String :=
  "{\"format\":" ++ jsonString POLICY_FORMAT ++
  ",\"world\":" ++ policy.world.toJson ++
  ",\"content\":" ++ policy.content.toJson ++
  ",\"mission_id\":" ++ toString policy.missionId ++
  ",\"session_id\":" ++ jsonString (Emit.bytes32Hex policy.sessionId) ++
  ",\"mission_day\":" ++ policy.missionDay.toJson ++
  ",\"watch_officer\":" ++ jsonString (Emit.bytes32Hex policy.watchOfficer) ++
  ",\"roster\":" ++ jsonArray (policy.roster.map OfficerWire.toJson) ++ "}"

/-! ## Public command wire — authority commands are unrepresentable -/

inductive PublicCommandWire where
  | claimServing (day : DayWire) (visitor : Digest32) (choice : Nat)
  | performMaintenance (actor : Digest32) (action : Nat)
  | deliverBriefing (role : Nat) (recipient : Digest32)
  | commitRoute (route : Nat)
  | choose (choice : Nat)
  | extract (choice : Nat)
  | completeRecoveryCalibration (officer : Digest32)
  | issueDebrief
deriving DecidableEq

def PublicCommandWire.toSemantic? : PublicCommandWire → Option NightWatchLoop.Command
  | .claimServing day visitor choice => do
      let serving ← servingOfCode? choice
      some (.claimServing ⟨⟨day.contentEpoch⟩, day.dayIndex⟩ visitor serving)
  | .performMaintenance actor action => do
      some (.performMaintenance actor (← maintenanceOfCode? action))
  | .deliverBriefing role recipient => do
      some (.deliverBriefing (← roleOfCode? role) recipient)
  | .commitRoute route => do some (.commitRoute (← routeOfCode? route))
  | .choose choice => do some (.choose (← choiceOfCode? choice))
  | .extract 0 => some (.extract .returnNow)
  | .extract 1 => some (.extract .descendFurther)
  | .extract _ => none
  | .completeRecoveryCalibration officer => some (.completeRecoveryCalibration officer)
  | .issueDebrief => some .issueDebrief

def PublicCommandWire.toJson (command : PublicCommandWire) : String :=
  let body := match command with
    | .claimServing day visitor choice =>
        "\"kind\":\"claim_serving\",\"day\":" ++ day.toJson ++
        ",\"visitor\":" ++ jsonString (Emit.bytes32Hex visitor) ++
        ",\"choice\":" ++ toString choice
    | .performMaintenance actor action =>
        "\"kind\":\"perform_maintenance\",\"actor\":" ++
        jsonString (Emit.bytes32Hex actor) ++ ",\"action\":" ++ toString action
    | .deliverBriefing role recipient =>
        "\"kind\":\"deliver_briefing\",\"role\":" ++ toString role ++
        ",\"recipient\":" ++ jsonString (Emit.bytes32Hex recipient)
    | .commitRoute route => "\"kind\":\"commit_route\",\"route\":" ++ toString route
    | .choose choice => "\"kind\":\"choose\",\"choice\":" ++ toString choice
    | .extract choice => "\"kind\":\"extract\",\"choice\":" ++ toString choice
    | .completeRecoveryCalibration officer =>
        "\"kind\":\"complete_recovery_calibration\",\"officer\":" ++
        jsonString (Emit.bytes32Hex officer)
    | .issueDebrief => "\"kind\":\"issue_debrief\""
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ "," ++ body ++ "}"

private def parseWorld (j : Json) : Except String WorldWire := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch"]
  let value : WorldWire := {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
  }
  if value.toSemantic.validB then pure value else throw "invalid world identity"

private def parseContent (j : Json) : Except String ContentWire := do
  exactKeys j ["component", "pack_digest"]
  pure ⟨← objectDigest j "component", ← objectDigest j "pack_digest"⟩

private def parseDay (j : Json) : Except String DayWire := do
  exactKeys j ["content_epoch", "day_index"]
  pure ⟨← objectNat j "content_epoch", ← objectNat j "day_index"⟩

private def parseOfficer (j : Json) : Except String OfficerWire := do
  exactKeys j ["role", "recipient"]
  let role ← objectNat j "role" 3
  if (roleOfCode? role).isNone then throw "unknown role"
  pure ⟨role, ← objectDigest j "recipient"⟩

private def parsePolicy (j : Json) : Except String PolicyViewWire := do
  exactKeys j ["format", "world", "content", "mission_id", "session_id", "mission_day",
    "watch_officer", "roster"]
  if (← j.getObjValAs? String "format") != POLICY_FORMAT then throw "wrong policy format"
  let policy : PolicyViewWire := {
    world := ← parseWorld (← j.getObjVal? "world")
    content := ← parseContent (← j.getObjVal? "content")
    missionId := ← objectNat j "mission_id"
    sessionId := ← objectDigest j "session_id"
    missionDay := ← parseDay (← j.getObjVal? "mission_day")
    watchOfficer := ← objectDigest j "watch_officer"
    roster := ← parseBoundedList (← j.getObjVal? "roster") 4 parseOfficer
  }
  if policy.roster.map OfficerWire.role != [0, 1, 2, 3] then throw "roster roles not exact"
  if !(policy.roster.map OfficerWire.recipient).Nodup then throw "duplicate roster recipient"
  if policy.missionDay.contentEpoch != policy.world.contentEpoch then throw "policy epoch mismatch"
  if policy.watchOfficer ∉ policy.roster.map OfficerWire.recipient then
    throw "watch officer outside roster"
  pure policy

private def parseCommand (j : Json) : Except String PublicCommandWire := do
  let kind ← j.getObjValAs? String "kind"
  let format ← j.getObjValAs? String "format"
  if format != COMMAND_FORMAT then throw "wrong command format"
  let command ← match kind with
    | "claim_serving" => do
        exactKeys j ["format", "kind", "day", "visitor", "choice"]
        pure (.claimServing (← parseDay (← j.getObjVal? "day"))
          (← objectDigest j "visitor") (← objectNat j "choice" 31))
    | "perform_maintenance" => do
        exactKeys j ["format", "kind", "actor", "action"]
        pure (.performMaintenance (← objectDigest j "actor") (← objectNat j "action" 6))
    | "deliver_briefing" => do
        exactKeys j ["format", "kind", "role", "recipient"]
        pure (.deliverBriefing (← objectNat j "role" 3) (← objectDigest j "recipient"))
    | "commit_route" => do
        exactKeys j ["format", "kind", "route"]
        pure (.commitRoute (← objectNat j "route" 2))
    | "choose" => do
        exactKeys j ["format", "kind", "choice"]
        pure (.choose (← objectNat j "choice" 999))
    | "extract" => do
        exactKeys j ["format", "kind", "choice"]
        pure (.extract (← objectNat j "choice" 1))
    | "complete_recovery_calibration" => do
        exactKeys j ["format", "kind", "officer"]
        pure (.completeRecoveryCalibration (← objectDigest j "officer"))
    | "issue_debrief" => do
        exactKeys j ["format", "kind"]
        pure .issueDebrief
    | "record_handoff" | "enroll_next_watch" | "activate_draft_settlement" =>
        throw "authority-bearing command unavailable on public wire"
    | _ => throw "unknown command kind"
  if command.toSemantic?.isSome then pure command else throw "unknown stable command code"

def decodeCommandWithLimit (limit : Nat) (bytes : String) : Option PublicCommandWire :=
  canonicalDecode parseCommand PublicCommandWire.toJson limit bytes

def decodeCommand (bytes : String) : Option PublicCommandWire :=
  decodeCommandWithLimit WIRE_BYTE_LIMIT bytes

def decodePolicyViewWithLimit (limit : Nat) (bytes : String) : Option PolicyViewWire :=
  canonicalDecode parsePolicy PolicyViewWire.toJson limit bytes

def decodePolicyView (bytes : String) : Option PolicyViewWire :=
  decodePolicyViewWithLimit WIRE_BYTE_LIMIT bytes

/-! ## Complete proof-erased state snapshot -/

structure VisitKeyWire where
  day : DayWire
  visitor : Digest32
deriving DecidableEq
structure ServingCountWire where
  day : DayWire
  choice : Nat
  served : Nat
deriving DecidableEq
structure ServingWire where
  day : DayWire
  visitor : Digest32
  rotation : Nat
  choice : Nat
  allocationOrdinal : Nat
  disposition : Nat
  nextFeaturedCount : Nat
  localService : Nat
deriving DecidableEq
structure ContributionWire where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  relics : List Nat
deriving DecidableEq
structure BriefingWire where
  role : Nat
  recipient : Digest32
  briefingId : Nat
deriving DecidableEq
structure HandoffWire where
  role : Nat
  signer : Digest32
  recipient : Digest32
  briefingId : Nat
  previousCounter : Nat
  counter : Nat
  route : Nat
  deepConsent : Bool
  signature : Digest32
deriving DecidableEq
structure FlagsWire where
  entryMarked : Bool
  navigationDebt : Bool
  pressureOpen : Bool
  sequenceComplete : Bool
  corridorOpen : Bool
  thresholdOpen : Bool
  cradleExchanged : Bool
deriving DecidableEq
structure InjuryWire where
  officer : Digest32
  terminal : Nat
deriving DecidableEq
structure RecoveryServingWire where
  injury : Nat
  terminal : Nat
  serving : ServingWire
deriving DecidableEq
structure OutcomeWire where
  terminal : Nat
  contribution : ContributionWire
  featuredArtifact : Nat
  recoveryGrade : Nat
  carriedRelics : List Nat
  debriefVersion : Nat
  terminalOperationalCost : Nat
deriving DecidableEq

inductive RecoveryWire where
  | fit
  | treatmentNeeded (officer : Digest32) (terminal : Nat)
  | calibrationNeeded (officer : Digest32) (terminal : Nat) (serving : ServingWire)
  | recovered (officer : Digest32) (terminal : Nat)
deriving DecidableEq

structure NextWatchWire where
  day : DayWire
  role : Nat
  recipient : Digest32
  admittedAtSequence : Nat
deriving DecidableEq

structure StateSnapshotWire where
  policy : PolicyViewWire
  sequence : Nat
  phase : Nat
  visitKeys : List VisitKeyWire
  servingCounts : List ServingCountWire
  servings : List ServingWire
  initialServing : Option ServingWire
  maintenanceProgress : Nat
  maintenanceActors : List Digest32
  maintenanceContribution : Option ContributionWire
  briefings : List BriefingWire
  handoffs : List HandoffWire
  handoffCounters : List Nat
  route : Option Nat
  encounterIndex : Nat
  turnsSpent : Nat
  operationalSpent : Nat
  suppliesSpent : Nat
  clueIntel : Nat
  evidence : List Nat
  flags : FlagsWire
  pendingInjury : Option InjuryWire
  pendingTerminal : Option Nat
  pendingRecoveryServing : Option RecoveryServingWire
  outcome : Option OutcomeWire
  recovery : RecoveryWire
  nextWatchEnrollments : List NextWatchWire
  debrief : Option (Nat × Nat)
deriving DecidableEq

def DayWire.ofSemantic (day : FinalizedDayId) : DayWire :=
  ⟨day.contentEpoch.value, day.dayIndex⟩

def ServingWire.ofSemantic (receipt : ServingReceipt) : ServingWire where
  day := .ofSemantic receipt.day
  visitor := receipt.visitor
  rotation := receipt.rotation.code
  choice := receipt.choice.code
  allocationOrdinal := receipt.allocationOrdinal
  disposition := match receipt.disposition with | .featured => 0 | .neighborlyAlternative => 1
  nextFeaturedCount := receipt.nextFeaturedCount
  localService := receipt.localService

def ContributionWire.ofSemantic (contribution : Contribution) : ContributionWire where
  intel := contribution.intel.val
  supplies := contribution.supplies.val
  cohesion := contribution.cohesion.val
  influence := contribution.influence.val
  score := contribution.score.val
  relics := [relicSilentBearing, relicIndexFilm, relicThresholdWedge].filterMap fun relic =>
    if relic ∈ contribution.relics then some relic.value else none

def OutcomeWire.ofSemantic (receipt : OutcomeReceipt) : OutcomeWire where
  terminal := receipt.terminal.code
  contribution := .ofSemantic receipt.contribution
  featuredArtifact := receipt.featuredArtifact.value
  recoveryGrade := gradeCode receipt.recoveryGrade
  carriedRelics := [relicSilentBearing, relicIndexFilm, relicThresholdWedge].filterMap fun relic =>
    if relic ∈ receipt.carriedRelics then some relic.value else none
  debriefVersion := receipt.debrief.schemaVersion
  terminalOperationalCost := receipt.terminalOperationalCost

def VisitKeyWire.toJson (key : VisitKeyWire) : String :=
  "{\"day\":" ++ key.day.toJson ++ ",\"visitor\":" ++
    jsonString (Emit.bytes32Hex key.visitor) ++ "}"
def ServingCountWire.toJson (row : ServingCountWire) : String :=
  "{\"day\":" ++ row.day.toJson ++ ",\"choice\":" ++ toString row.choice ++
    ",\"served\":" ++ toString row.served ++ "}"
def ServingWire.toJson (receipt : ServingWire) : String :=
  "{\"day\":" ++ receipt.day.toJson ++
  ",\"visitor\":" ++ jsonString (Emit.bytes32Hex receipt.visitor) ++
  ",\"rotation\":" ++ toString receipt.rotation ++ ",\"choice\":" ++ toString receipt.choice ++
  ",\"allocation_ordinal\":" ++ toString receipt.allocationOrdinal ++
  ",\"disposition\":" ++ toString receipt.disposition ++
  ",\"next_featured_count\":" ++ toString receipt.nextFeaturedCount ++
  ",\"local_service\":" ++ toString receipt.localService ++ "}"
def ContributionWire.toJson (value : ContributionWire) : String :=
  "{\"intel\":" ++ toString value.intel ++ ",\"supplies\":" ++ toString value.supplies ++
  ",\"cohesion\":" ++ toString value.cohesion ++ ",\"influence\":" ++ toString value.influence ++
  ",\"score\":" ++ toString value.score ++ ",\"relics\":" ++
    jsonArray (value.relics.map toString) ++ "}"
def BriefingWire.toJson (value : BriefingWire) : String :=
  "{\"role\":" ++ toString value.role ++ ",\"recipient\":" ++
    jsonString (Emit.bytes32Hex value.recipient) ++ ",\"briefing_id\":" ++
    toString value.briefingId ++ "}"
def HandoffWire.toJson (value : HandoffWire) : String :=
  "{\"role\":" ++ toString value.role ++ ",\"signer\":" ++ jsonString (Emit.bytes32Hex value.signer) ++
  ",\"recipient\":" ++ jsonString (Emit.bytes32Hex value.recipient) ++
  ",\"briefing_id\":" ++ toString value.briefingId ++
  ",\"previous_counter\":" ++ toString value.previousCounter ++ ",\"counter\":" ++ toString value.counter ++
  ",\"route\":" ++ toString value.route ++ ",\"deep_consent\":" ++ boolJson value.deepConsent ++
  ",\"signature\":" ++ jsonString (Emit.bytes32Hex value.signature) ++ "}"
def FlagsWire.toJson (value : FlagsWire) : String :=
  "{\"entry_marked\":" ++ boolJson value.entryMarked ++
  ",\"navigation_debt\":" ++ boolJson value.navigationDebt ++
  ",\"pressure_open\":" ++ boolJson value.pressureOpen ++
  ",\"sequence_complete\":" ++ boolJson value.sequenceComplete ++
  ",\"corridor_open\":" ++ boolJson value.corridorOpen ++
  ",\"threshold_open\":" ++ boolJson value.thresholdOpen ++
  ",\"cradle_exchanged\":" ++ boolJson value.cradleExchanged ++ "}"
def InjuryWire.toJson (value : InjuryWire) : String :=
  "{\"officer\":" ++ jsonString (Emit.bytes32Hex value.officer) ++
    ",\"terminal\":" ++ toString value.terminal ++ "}"
def RecoveryServingWire.toJson (value : RecoveryServingWire) : String :=
  "{\"injury\":" ++ toString value.injury ++ ",\"terminal\":" ++ toString value.terminal ++
    ",\"serving\":" ++ value.serving.toJson ++ "}"
def OutcomeWire.toJson (value : OutcomeWire) : String :=
  "{\"terminal\":" ++ toString value.terminal ++ ",\"contribution\":" ++ value.contribution.toJson ++
  ",\"featured_artifact\":" ++ toString value.featuredArtifact ++
  ",\"recovery_grade\":" ++ toString value.recoveryGrade ++
  ",\"carried_relics\":" ++ jsonArray (value.carriedRelics.map toString) ++
  ",\"debrief_version\":" ++ toString value.debriefVersion ++
  ",\"terminal_operational_cost\":" ++ toString value.terminalOperationalCost ++ "}"
def RecoveryWire.toJson : RecoveryWire → String
  | .fit => "{\"kind\":\"fit\"}"
  | .treatmentNeeded officer terminal =>
      "{\"kind\":\"treatment_needed\",\"officer\":" ++ jsonString (Emit.bytes32Hex officer) ++
      ",\"terminal\":" ++ toString terminal ++ "}"
  | .calibrationNeeded officer terminal serving =>
      "{\"kind\":\"calibration_needed\",\"officer\":" ++ jsonString (Emit.bytes32Hex officer) ++
      ",\"terminal\":" ++ toString terminal ++ ",\"serving\":" ++ serving.toJson ++ "}"
  | .recovered officer terminal =>
      "{\"kind\":\"recovered\",\"officer\":" ++ jsonString (Emit.bytes32Hex officer) ++
      ",\"terminal\":" ++ toString terminal ++ "}"
def NextWatchWire.toJson (value : NextWatchWire) : String :=
  "{\"day\":" ++ value.day.toJson ++ ",\"role\":" ++ toString value.role ++
  ",\"recipient\":" ++ jsonString (Emit.bytes32Hex value.recipient) ++
  ",\"admitted_at_sequence\":" ++ toString value.admittedAtSequence ++ "}"

def StateSnapshotWire.ofState (state : NightWatchLoop.State) : StateSnapshotWire where
  policy := .ofPolicy state.policy
  sequence := state.sequence
  phase := phaseCode state.phase
  visitKeys := state.servings.map fun serving =>
    ⟨.ofSemantic serving.day, serving.visitor⟩
  servingCounts := state.servingCounts.map fun row =>
    ⟨.ofSemantic row.day, row.choice.code, row.served⟩
  servings := state.servings.map ServingWire.ofSemantic
  initialServing := state.initialServing.map ServingWire.ofSemantic
  maintenanceProgress := state.maintenanceProgress
  maintenanceActors := state.policy.raw.roster.filterMap fun seat =>
    if seat.recipient ∈ state.maintenanceActors then some seat.recipient else none
  maintenanceContribution := state.maintenanceContribution.map ContributionWire.ofSemantic
  briefings := state.briefings.map fun value =>
    ⟨roleCode value.role, value.recipient, value.briefingId⟩
  handoffs := state.handoffs.map fun value => {
    role := roleCode value.role
    signer := value.signer
    recipient := value.recipient
    briefingId := value.briefingId
    previousCounter := value.previousCounter
    counter := value.counter
    route := value.recommendedRoute.code
    deepConsent := value.deepConsent
    signature := value.signature.value
  }
  handoffCounters := state.handoffCounters
  route := state.route.map Route.code
  encounterIndex := state.encounterIndex
  turnsSpent := state.turnsSpent
  operationalSpent := state.operationalSpent
  suppliesSpent := state.suppliesSpent
  clueIntel := state.clueIntel
  evidence := [artifactClearanceMotion, artifactMaintenanceLoadTrace,
    artifactPressureIntervalRecord, artifactGallerySequence, artifactShoalMotion,
    artifactThresholdHandoff, artifactCradleExchange, artifactReturnWindow].filterMap fun artifact =>
      if artifact ∈ state.evidence then some artifact.value else none
  flags := ⟨state.flags.entryMarked, state.flags.navigationDebt, state.flags.pressureOpen,
    state.flags.sequenceComplete, state.flags.corridorOpen, state.flags.thresholdOpen,
    state.flags.cradleExchanged⟩
  pendingInjury := state.pendingInjury.map fun (officer, _, terminal) =>
    ⟨officer, terminal.code⟩
  pendingTerminal := state.pendingTerminal.map TerminalId.code
  pendingRecoveryServing := state.pendingRecoveryServing.map fun (_, terminal, serving) =>
    ⟨0, terminal.code, .ofSemantic serving⟩
  outcome := state.outcome.map OutcomeWire.ofSemantic
  recovery := match state.recovery with
    | .fit => RecoveryWire.fit
    | .treatmentNeeded officer _ terminal => RecoveryWire.treatmentNeeded officer terminal.code
    | .calibrationNeeded officer _ terminal serving =>
        RecoveryWire.calibrationNeeded officer terminal.code (.ofSemantic serving)
    | .recovered officer _ terminal => RecoveryWire.recovered officer terminal.code
  nextWatchEnrollments := state.nextWatchEnrollments.map fun value =>
    ⟨.ofSemantic value.watchDay, roleCode value.role, value.recipient, value.admittedAtSequence⟩
  debrief := state.debrief.map fun value => (value.schemaVersion, value.terminal.code)

private def natPairJson (value : Nat × Nat) : String :=
  "{\"version\":" ++ toString value.1 ++ ",\"terminal\":" ++ toString value.2 ++ "}"

def StateSnapshotWire.toJson (state : StateSnapshotWire) : String :=
  "{\"format\":" ++ jsonString STATE_FORMAT ++
  ",\"policy\":" ++ state.policy.toJson ++
  ",\"sequence\":" ++ toString state.sequence ++ ",\"phase\":" ++ toString state.phase ++
  ",\"visit_keys\":" ++ jsonArray (state.visitKeys.map VisitKeyWire.toJson) ++
  ",\"serving_counts\":" ++ jsonArray (state.servingCounts.map ServingCountWire.toJson) ++
  ",\"servings\":" ++ jsonArray (state.servings.map ServingWire.toJson) ++
  ",\"initial_serving\":" ++ optionJson ServingWire.toJson state.initialServing ++
  ",\"maintenance_progress\":" ++ toString state.maintenanceProgress ++
  ",\"maintenance_actors\":" ++ jsonArray
    (state.maintenanceActors.map (jsonString ∘ Emit.bytes32Hex)) ++
  ",\"maintenance_contribution\":" ++ optionJson ContributionWire.toJson state.maintenanceContribution ++
  ",\"briefings\":" ++ jsonArray (state.briefings.map BriefingWire.toJson) ++
  ",\"handoffs\":" ++ jsonArray (state.handoffs.map HandoffWire.toJson) ++
  ",\"handoff_counters\":" ++ jsonArray (state.handoffCounters.map toString) ++
  ",\"route\":" ++ optionJson toString state.route ++
  ",\"encounter_index\":" ++ toString state.encounterIndex ++
  ",\"turns_spent\":" ++ toString state.turnsSpent ++
  ",\"operational_spent\":" ++ toString state.operationalSpent ++
  ",\"supplies_spent\":" ++ toString state.suppliesSpent ++
  ",\"clue_intel\":" ++ toString state.clueIntel ++
  ",\"evidence\":" ++ jsonArray (state.evidence.map toString) ++
  ",\"flags\":" ++ state.flags.toJson ++
  ",\"pending_injury\":" ++ optionJson InjuryWire.toJson state.pendingInjury ++
  ",\"pending_terminal\":" ++ optionJson toString state.pendingTerminal ++
  ",\"pending_recovery_serving\":" ++
    optionJson RecoveryServingWire.toJson state.pendingRecoveryServing ++
  ",\"outcome\":" ++ optionJson OutcomeWire.toJson state.outcome ++
  ",\"recovery\":" ++ state.recovery.toJson ++
  ",\"next_watch_enrollments\":" ++ jsonArray
    (state.nextWatchEnrollments.map NextWatchWire.toJson) ++
  ",\"debrief\":" ++ optionJson natPairJson state.debrief ++ "}"

private def parseVisitKey (j : Json) : Except String VisitKeyWire := do
  exactKeys j ["day", "visitor"]
  pure ⟨← parseDay (← j.getObjVal? "day"), ← objectDigest j "visitor"⟩

private def parseServingCount (j : Json) : Except String ServingCountWire := do
  exactKeys j ["day", "choice", "served"]
  let choice ← objectNat j "choice" 31
  if (servingOfCode? choice).isNone then throw "unknown serving code"
  pure ⟨← parseDay (← j.getObjVal? "day"), choice, ← objectNat j "served" 128⟩

private def parseServing (j : Json) : Except String ServingWire := do
  exactKeys j ["day", "visitor", "rotation", "choice", "allocation_ordinal",
    "disposition", "next_featured_count", "local_service"]
  let choice ← objectNat j "choice" 31
  let serving ← match servingOfCode? choice with
    | some value => pure value
    | none => throw "unknown serving code"
  let rotation ← objectNat j "rotation" 7
  if rotation != serving.rotation.code then throw "serving rotation mismatch"
  pure {
    day := ← parseDay (← j.getObjVal? "day")
    visitor := ← objectDigest j "visitor"
    rotation
    choice
    allocationOrdinal := ← objectNat j "allocation_ordinal" 128
    disposition := ← objectNat j "disposition" 1
    nextFeaturedCount := ← objectNat j "next_featured_count" 128
    localService := ← objectNat j "local_service" 32
  }

private def parseNatArray (j : Json) (limit count : Nat) : Except String (List Nat) :=
  parseBoundedList j count (fun value => parseNat value limit)

private def parseContribution (j : Json) : Except String ContributionWire := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  let value : ContributionWire := {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relics := ← parseNatArray (← j.getObjVal? "relics") 3 3
  }
  if !value.relics.Nodup || value.relics != value.relics.insertionSort (fun a b => a < b) then
    throw "noncanonical relic list"
  pure value

private def parseBriefing (j : Json) : Except String BriefingWire := do
  exactKeys j ["role", "recipient", "briefing_id"]
  let role ← objectNat j "role" 3
  let semantic ← match roleOfCode? role with | some value => pure value | none => throw "unknown role"
  let value := ⟨role, ← objectDigest j "recipient", ← objectNat j "briefing_id" 4⟩
  if value.briefingId != briefingIdFor semantic then throw "briefing id mismatch"
  pure value

private def parseHandoff (j : Json) : Except String HandoffWire := do
  exactKeys j ["role", "signer", "recipient", "briefing_id", "previous_counter", "counter",
    "route", "deep_consent", "signature"]
  let role ← objectNat j "role" 3
  let semantic ← match roleOfCode? role with | some value => pure value | none => throw "unknown role"
  let route ← objectNat j "route" 2
  if (routeOfCode? route).isNone then throw "unknown route"
  let value : HandoffWire := {
    role
    signer := ← objectDigest j "signer"
    recipient := ← objectDigest j "recipient"
    briefingId := ← objectNat j "briefing_id" 4
    previousCounter := ← objectNat j "previous_counter"
    counter := ← objectNat j "counter"
    route
    deepConsent := ← parseBool (← j.getObjVal? "deep_consent")
    signature := ← objectDigest j "signature"
  }
  if value.briefingId != briefingIdFor semantic then throw "handoff briefing mismatch"
  if value.counter != value.previousCounter + 1 then throw "handoff counter not dense"
  pure value

private def parseFlags (j : Json) : Except String FlagsWire := do
  exactKeys j ["entry_marked", "navigation_debt", "pressure_open", "sequence_complete",
    "corridor_open", "threshold_open", "cradle_exchanged"]
  pure ⟨← parseBool (← j.getObjVal? "entry_marked"),
    ← parseBool (← j.getObjVal? "navigation_debt"),
    ← parseBool (← j.getObjVal? "pressure_open"),
    ← parseBool (← j.getObjVal? "sequence_complete"),
    ← parseBool (← j.getObjVal? "corridor_open"),
    ← parseBool (← j.getObjVal? "threshold_open"),
    ← parseBool (← j.getObjVal? "cradle_exchanged")⟩

private def parseTerminalCode (j : Json) (key : String) : Except String Nat := do
  let code ← objectNat j key 104
  if (terminalOfCode? code).isSome then pure code else throw "unknown terminal code"

private def parseInjury (j : Json) : Except String InjuryWire := do
  exactKeys j ["officer", "terminal"]
  pure ⟨← objectDigest j "officer", ← parseTerminalCode j "terminal"⟩

private def parseRecoveryServing (j : Json) : Except String RecoveryServingWire := do
  exactKeys j ["injury", "terminal", "serving"]
  let injury ← objectNat j "injury" 0
  pure ⟨injury, ← parseTerminalCode j "terminal",
    ← parseServing (← j.getObjVal? "serving")⟩

private def parseOutcome (j : Json) : Except String OutcomeWire := do
  exactKeys j ["terminal", "contribution", "featured_artifact", "recovery_grade",
    "carried_relics", "debrief_version", "terminal_operational_cost"]
  let code ← parseTerminalCode j "terminal"
  let value : OutcomeWire := {
    terminal := code
    contribution := ← parseContribution (← j.getObjVal? "contribution")
    featuredArtifact := ← objectNat j "featured_artifact" 8
    recoveryGrade := ← objectNat j "recovery_grade" 5
    carriedRelics := ← parseNatArray (← j.getObjVal? "carried_relics") 3 3
    debriefVersion := ← objectNat j "debrief_version"
    terminalOperationalCost := ← objectNat j "terminal_operational_cost" 12
  }
  let terminal ← match terminalOfCode? code with
    | some terminal => pure terminal
    | none => throw "unknown terminal code"
  let expected ← match (outcomeReceipt? terminal).map OutcomeWire.ofSemantic with
    | some expected => pure expected
    | none => throw "terminal table refused"
  if value != expected then throw "outcome view does not match Lean terminal table"
  pure value

private def parseRecovery (j : Json) : Except String RecoveryWire := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "fit" => exactKeys j ["kind"]; pure .fit
  | "treatment_needed" =>
      exactKeys j ["kind", "officer", "terminal"]
      pure (.treatmentNeeded (← objectDigest j "officer") (← parseTerminalCode j "terminal"))
  | "calibration_needed" =>
      exactKeys j ["kind", "officer", "terminal", "serving"]
      pure (.calibrationNeeded (← objectDigest j "officer")
        (← parseTerminalCode j "terminal") (← parseServing (← j.getObjVal? "serving")))
  | "recovered" =>
      exactKeys j ["kind", "officer", "terminal"]
      pure (.recovered (← objectDigest j "officer") (← parseTerminalCode j "terminal"))
  | _ => throw "unknown recovery state"

private def parseNextWatch (j : Json) : Except String NextWatchWire := do
  exactKeys j ["day", "role", "recipient", "admitted_at_sequence"]
  let role ← objectNat j "role" 3
  if (roleOfCode? role).isNone then throw "unknown role"
  pure ⟨← parseDay (← j.getObjVal? "day"), role, ← objectDigest j "recipient",
    ← objectNat j "admitted_at_sequence"⟩

private def parseNatPair (j : Json) : Except String (Nat × Nat) := do
  exactKeys j ["version", "terminal"]
  pure (← objectNat j "version", ← parseTerminalCode j "terminal")

private def parseState (j : Json) : Except String StateSnapshotWire := do
  exactKeys j ["format", "policy", "sequence", "phase", "visit_keys", "serving_counts",
    "servings", "initial_serving", "maintenance_progress", "maintenance_actors",
    "maintenance_contribution", "briefings", "handoffs", "handoff_counters", "route",
    "encounter_index", "turns_spent", "operational_spent", "supplies_spent", "clue_intel",
    "evidence", "flags", "pending_injury", "pending_terminal", "pending_recovery_serving",
    "outcome", "recovery", "next_watch_enrollments", "debrief"]
  if (← j.getObjValAs? String "format") != STATE_FORMAT then throw "wrong state format"
  let state : StateSnapshotWire := {
    policy := ← parsePolicy (← j.getObjVal? "policy")
    sequence := ← objectNat j "sequence"
    phase := ← objectNat j "phase" 7
    visitKeys := ← parseBoundedList (← j.getObjVal? "visit_keys") 4096 parseVisitKey
    servingCounts := ← parseBoundedList (← j.getObjVal? "serving_counts") 4096 parseServingCount
    servings := ← parseBoundedList (← j.getObjVal? "servings") 4096 parseServing
    initialServing := ← parseOption (← j.getObjVal? "initial_serving") parseServing
    maintenanceProgress := ← objectNat j "maintenance_progress" 7
    maintenanceActors := ← parseBoundedList (← j.getObjVal? "maintenance_actors") 4 parseDigest
    maintenanceContribution := ← parseOption (← j.getObjVal? "maintenance_contribution") parseContribution
    briefings := ← parseBoundedList (← j.getObjVal? "briefings") 4 parseBriefing
    handoffs := ← parseBoundedList (← j.getObjVal? "handoffs") 4 parseHandoff
    handoffCounters := ← parseNatArray (← j.getObjVal? "handoff_counters") WIRE_U64_MAX 4
    route := ← parseOption (← j.getObjVal? "route") (fun value => parseNat value 2)
    encounterIndex := ← objectNat j "encounter_index" 5
    turnsSpent := ← objectNat j "turns_spent" TURN_BUDGET
    operationalSpent := ← objectNat j "operational_spent" OPERATIONAL_BUDGET
    suppliesSpent := ← objectNat j "supplies_spent" SUPPLY_SPEND_LIMIT
    clueIntel := ← objectNat j "clue_intel" CLUE_INTEL_LIMIT
    evidence := ← parseNatArray (← j.getObjVal? "evidence") 8 8
    flags := ← parseFlags (← j.getObjVal? "flags")
    pendingInjury := ← parseOption (← j.getObjVal? "pending_injury") parseInjury
    pendingTerminal := ← parseOption (← j.getObjVal? "pending_terminal")
      (fun value => do let code ← parseNat value 104; if (terminalOfCode? code).isSome then pure code else throw "unknown terminal")
    pendingRecoveryServing := ← parseOption (← j.getObjVal? "pending_recovery_serving") parseRecoveryServing
    outcome := ← parseOption (← j.getObjVal? "outcome") parseOutcome
    recovery := ← parseRecovery (← j.getObjVal? "recovery")
    nextWatchEnrollments := ← parseBoundedList
      (← j.getObjVal? "next_watch_enrollments") 32 parseNextWatch
    debrief := ← parseOption (← j.getObjVal? "debrief") parseNatPair
  }
  if (phaseOfCode? state.phase).isNone then throw "unknown phase"
  if state.visitKeys != state.servings.map (fun serving => ⟨serving.day, serving.visitor⟩) then
    throw "visit ledger does not match serving receipts"
  if state.handoffCounters.length != 4 then throw "handoff counter shape"
  let canonicalMaintenanceActors := state.policy.roster.filterMap fun officer =>
    if officer.recipient ∈ state.maintenanceActors then some officer.recipient else none
  if !state.maintenanceActors.Nodup ||
      state.maintenanceActors != canonicalMaintenanceActors then
    throw "maintenance actor set not canonical"
  if !state.evidence.Nodup || state.evidence != state.evidence.insertionSort (fun a b => a < b) then
    throw "evidence list not canonical"
  if state.evidence.any (fun artifact => artifact = 0 || 8 < artifact) then
    throw "unknown evidence id"
  match state.maintenanceContribution with
  | some contribution =>
      if contribution != ContributionWire.ofSemantic maintenanceContribution then
        throw "maintenance contribution mismatch"
  | none => pure ()
  pure state

def decodeStateViewWithLimit (limit : Nat) (bytes : String) : Option StateSnapshotWire :=
  canonicalDecode parseState StateSnapshotWire.toJson limit bytes

def decodeStateView (bytes : String) : Option StateSnapshotWire :=
  decodeStateViewWithLimit WIRE_BYTE_LIMIT bytes

/-! ## Accepted event-envelope views

The generic arrays have event-specific fixed positions checked by `validB`.
This keeps the wire finite without giving callers constructors for private
semantic receipts. -/

structure EventEnvelopeWire where
  sequence : Nat
  event : Nat
  codes : List Nat
  numbers : List Nat
  digests : List Digest32
  flags : List Bool
deriving DecidableEq

private def servingEventFields (receipt : ServingReceipt) :
    List Nat × List Nat × List Digest32 :=
  let disposition := match receipt.disposition with | .featured => 0 | .neighborlyAlternative => 1
  ([receipt.rotation.code, receipt.choice.code, disposition],
   [receipt.day.contentEpoch.value, receipt.day.dayIndex, receipt.allocationOrdinal,
    receipt.nextFeaturedCount, receipt.localService], [receipt.visitor])

def EventEnvelopeWire.ofSemantic? (event : NightWatchLoop.EventEnvelope) :
    Option EventEnvelopeWire :=
  let mk codes numbers digests flags := some ⟨event.sequence, event.payload.id.code,
    codes, numbers, digests, flags⟩
  match event.payload with
  | .servingAllocated receipt =>
      let fields := servingEventFields receipt
      mk fields.1 fields.2.1 fields.2.2 []
  | .maintenancePerformed actor index action => mk [action.code] [index] [actor] []
  | .briefingDelivered receipt =>
      mk [roleCode receipt.role] [receipt.briefingId] [receipt.recipient] []
  | .handoffRecorded .. => none
  | .routeCommitted route => mk [route.code] [] [] []
  | .choiceResolved receipt =>
      let artifacts := [artifactClearanceMotion, artifactMaintenanceLoadTrace,
        artifactPressureIntervalRecord, artifactGallerySequence, artifactShoalMotion,
        artifactThresholdHandoff, artifactCradleExchange, artifactReturnWindow].filterMap fun artifact =>
          if artifact ∈ receipt.delta.artifacts then some artifact.value else none
      mk ([receipt.encounter.code, receipt.choice.code] ++ artifacts)
        [receipt.delta.turnCost, receipt.delta.operationalCost, receipt.delta.supplyCost,
         receipt.delta.clueIntel, receipt.nextEncounterIndex] [] [receipt.delta.causesInjury]
  | .extractionResolved receipt =>
      let relics := [relicSilentBearing, relicIndexFilm, relicThresholdWedge].filterMap fun relic =>
        if relic ∈ receipt.carriedRelics then some relic.value else none
      mk ([receipt.terminal.code, receipt.featuredArtifact.value,
        gradeCode receipt.recoveryGrade] ++ relics)
        [receipt.contribution.intel.val, receipt.contribution.supplies.val,
         receipt.contribution.cohesion.val, receipt.contribution.influence.val,
         receipt.contribution.score.val, receipt.debrief.schemaVersion,
         receipt.terminalOperationalCost] [] []
  | .injuryRecorded receipt =>
      mk [roleCode receipt.role, 0, receipt.source.code] [] [receipt.officer] []
  | .recoveryServingRecorded receipt =>
      let fields := servingEventFields receipt.serving
      mk ([0, receipt.source.code] ++ fields.1) fields.2.1 fields.2.2 []
  | .recoveryCalibrationCompleted receipt =>
      mk [0, receipt.source.code] [] [receipt.officer] []
  | .nextWatchEnrolled _ => none
  | .draftSettlementActivated .. => none
  | .debriefIssued debrief => mk [debrief.terminal.code] [debrief.schemaVersion] [] []

def EventEnvelopeWire.validB (event : EventEnvelopeWire) : Bool :=
  decide (event.sequence ≤ WIRE_U64_MAX) &&
  decide (event.codes.length ≤ MAX_EVENT_VIEW_ITEMS) &&
  decide (event.numbers.length ≤ MAX_EVENT_VIEW_ITEMS) &&
  decide (event.digests.length ≤ MAX_EVENT_VIEW_ITEMS) &&
  decide (event.flags.length ≤ MAX_EVENT_VIEW_ITEMS) &&
  match event.event with
  | 1 => decide (event.codes.length = 3 ∧ event.numbers.length = 5 ∧
      event.digests.length = 1 ∧ event.flags = [])
  | 2 => decide (event.codes.length = 1 ∧ event.numbers.length = 1 ∧
      event.digests.length = 1 ∧ event.flags = [])
  | 3 => decide (event.codes.length = 1 ∧ event.numbers.length = 1 ∧
      event.digests.length = 1 ∧ event.flags = [])
  | 5 => decide (event.codes.length = 1 ∧ event.numbers = [] ∧
      event.digests = [] ∧ event.flags = [])
  | 6 => decide (2 ≤ event.codes.length ∧ event.codes.length ≤ 10 ∧
      event.numbers.length = 5 ∧ event.digests = [] ∧ event.flags.length = 1)
  | 7 => decide (3 ≤ event.codes.length ∧ event.codes.length ≤ 6 ∧
      event.numbers.length = 7 ∧ event.digests = [] ∧ event.flags = [])
  | 8 => decide (event.codes.length = 3 ∧ event.numbers = [] ∧
      event.digests.length = 1 ∧ event.flags = [])
  | 9 => decide (event.codes.length = 5 ∧ event.numbers.length = 5 ∧
      event.digests.length = 1 ∧ event.flags = [])
  | 10 => decide (event.codes.length = 2 ∧ event.numbers = [] ∧
      event.digests.length = 1 ∧ event.flags = [])
  | 11 => decide (event.codes.length = 1 ∧ event.numbers.length = 1 ∧
      event.digests = [] ∧ event.flags = [])
  | _ => false

def EventEnvelopeWire.toJson (event : EventEnvelopeWire) : String :=
  "{\"format\":" ++ jsonString EVENT_FORMAT ++
  ",\"sequence\":" ++ toString event.sequence ++
  ",\"event\":" ++ toString event.event ++
  ",\"codes\":" ++ jsonArray (event.codes.map toString) ++
  ",\"numbers\":" ++ jsonArray (event.numbers.map toString) ++
  ",\"digests\":" ++ jsonArray (event.digests.map (jsonString ∘ Emit.bytes32Hex)) ++
  ",\"flags\":" ++ jsonArray (event.flags.map boolJson) ++ "}"

private def parseEvent (j : Json) : Except String EventEnvelopeWire := do
  exactKeys j ["format", "sequence", "event", "codes", "numbers", "digests", "flags"]
  if (← j.getObjValAs? String "format") != EVENT_FORMAT then throw "wrong event format"
  let value : EventEnvelopeWire := {
    sequence := ← objectNat j "sequence"
    event := ← objectNat j "event" 13
    codes := ← parseNatArray (← j.getObjVal? "codes") WIRE_U64_MAX MAX_EVENT_VIEW_ITEMS
    numbers := ← parseNatArray (← j.getObjVal? "numbers") WIRE_U64_MAX MAX_EVENT_VIEW_ITEMS
    digests := ← parseBoundedList (← j.getObjVal? "digests") MAX_EVENT_VIEW_ITEMS parseDigest
    flags := ← parseBoundedList (← j.getObjVal? "flags") MAX_EVENT_VIEW_ITEMS parseBool
  }
  if value.validB then pure value else throw "invalid event shape"

def decodeEventViewWithLimit (limit : Nat) (bytes : String) : Option EventEnvelopeWire :=
  canonicalDecode parseEvent EventEnvelopeWire.toJson limit bytes

def decodeEventView (bytes : String) : Option EventEnvelopeWire :=
  decodeEventViewWithLimit WIRE_BYTE_LIMIT bytes

def denseEventSequenceB (beforeSequence : Nat) (events : List EventEnvelopeWire) : Bool :=
  events.map EventEnvelopeWire.sequence =
    (List.range events.length).map (fun index => beforeSequence + index + 1)

/-! ## Runtime planning input/output views -/

structure CoordinateWire where
  world : WorldWire
  commitOrdinal : Nat
  blockId : Digest32
  turnHash : Digest32
  receiptHash : Digest32
  actorRoot : Digest32
  signer : Digest32
deriving DecidableEq

structure HeadWire where
  world : WorldWire
  namespaceId : Digest32
  kind : Nat
  key : Digest32
  version : Nat
  sequence : Nat
  head : Digest32
deriving DecidableEq

structure PlanningInputWire where
  policy : PolicyViewWire
  state : StateSnapshotWire
  command : PublicCommandWire
  coordinate : CoordinateWire
  initialHeads : List HeadWire
deriving DecidableEq

inductive IntentWire where
  | semantic (event : EventEnvelopeWire)
  | maintenance (contribution : ContributionWire)
  | expedition (terminal : Nat) (contribution : ContributionWire)
      (featuredArtifact debriefVersion operationalCost : Nat)
  | custody (terminal relic destination : Nat) (marketEligible directTradeAllowed : Bool)
deriving DecidableEq

structure IndexedEventWire where
  eventIndex : Nat
  namespaceId : Digest32
  kind : Nat
  key : Digest32
  version : Nat
  sequence : Nat
  predecessor : Digest32
  payloadDigest : Digest32
  eventDigest : Digest32
deriving DecidableEq

structure BatchEnvelopeWire where
  coordinate : CoordinateWire
  events : List IndexedEventWire
  batchDigest : Digest32
deriving DecidableEq

structure PreparedOutputWire where
  policy : PolicyViewWire
  beforeSequence : Nat
  command : PublicCommandWire
  acceptedEvents : List EventEnvelopeWire
  after : StateSnapshotWire
  intents : List IntentWire
  initialHeads : List HeadWire
  batch : BatchEnvelopeWire
  successorHeads : List HeadWire
deriving DecidableEq

def CoordinateWire.ofSemantic (coordinate : EventBatch.FinalizedTurnCoordinate) : CoordinateWire where
  world := .ofSemantic coordinate.world
  commitOrdinal := coordinate.commitOrdinal
  blockId := coordinate.blockId
  turnHash := coordinate.turnHash
  receiptHash := coordinate.receiptHash
  actorRoot := coordinate.actorRoot
  signer := coordinate.signer

def CoordinateWire.toSemantic (coordinate : CoordinateWire) : EventBatch.FinalizedTurnCoordinate where
  world := coordinate.world.toSemantic
  commitOrdinal := coordinate.commitOrdinal
  blockId := coordinate.blockId
  turnHash := coordinate.turnHash
  receiptHash := coordinate.receiptHash
  actorRoot := coordinate.actorRoot
  signer := coordinate.signer

def HeadWire.ofSemantic (head : EventBatch.StreamHead) : HeadWire where
  world := .ofSemantic head.stream.world
  namespaceId := head.stream.aggregate.namespaceId
  kind := head.stream.aggregate.kind
  key := head.stream.aggregate.key
  version := head.stream.version.value
  sequence := head.sequence
  head := head.head

def HeadWire.toSemantic (head : HeadWire) : EventBatch.StreamHead where
  stream := {
    world := head.world.toSemantic
    aggregate := ⟨head.namespaceId, head.kind, head.key⟩
    version := ⟨head.version⟩
  }
  sequence := head.sequence
  head := head.head

def CoordinateWire.toJson (value : CoordinateWire) : String :=
  "{\"world\":" ++ value.world.toJson ++
  ",\"commit_ordinal\":" ++ toString value.commitOrdinal ++
  ",\"block_id\":" ++ jsonString (Emit.bytes32Hex value.blockId) ++
  ",\"turn_hash\":" ++ jsonString (Emit.bytes32Hex value.turnHash) ++
  ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex value.receiptHash) ++
  ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex value.actorRoot) ++
  ",\"signer\":" ++ jsonString (Emit.bytes32Hex value.signer) ++ "}"

def HeadWire.toJson (value : HeadWire) : String :=
  "{\"world\":" ++ value.world.toJson ++
  ",\"namespace_id\":" ++ jsonString (Emit.bytes32Hex value.namespaceId) ++
  ",\"kind\":" ++ toString value.kind ++
  ",\"key\":" ++ jsonString (Emit.bytes32Hex value.key) ++
  ",\"version\":" ++ toString value.version ++
  ",\"sequence\":" ++ toString value.sequence ++
  ",\"head\":" ++ jsonString (Emit.bytes32Hex value.head) ++ "}"

def PlanningInputWire.toJson (value : PlanningInputWire) : String :=
  "{\"format\":" ++ jsonString PLAN_INPUT_FORMAT ++
  ",\"policy\":" ++ value.policy.toJson ++
  ",\"state\":" ++ value.state.toJson ++
  ",\"command\":" ++ value.command.toJson ++
  ",\"coordinate\":" ++ value.coordinate.toJson ++
  ",\"initial_heads\":" ++ jsonArray (value.initialHeads.map HeadWire.toJson) ++ "}"

def IntentWire.toJson : IntentWire → String
  | .semantic event => "{\"kind\":\"semantic\",\"event\":" ++ event.toJson ++ "}"
  | .maintenance contribution =>
      "{\"kind\":\"maintenance\",\"contribution\":" ++ contribution.toJson ++ "}"
  | .expedition terminal contribution artifact version cost =>
      "{\"kind\":\"expedition\",\"terminal\":" ++ toString terminal ++
      ",\"contribution\":" ++ contribution.toJson ++
      ",\"featured_artifact\":" ++ toString artifact ++
      ",\"debrief_version\":" ++ toString version ++
      ",\"operational_cost\":" ++ toString cost ++ "}"
  | .custody terminal relic destination market trade =>
      "{\"kind\":\"custody\",\"terminal\":" ++ toString terminal ++
      ",\"relic\":" ++ toString relic ++ ",\"destination\":" ++ toString destination ++
      ",\"market_eligible\":" ++ boolJson market ++
      ",\"direct_trade_allowed\":" ++ boolJson trade ++ "}"

def IndexedEventWire.toJson (value : IndexedEventWire) : String :=
  "{\"event_index\":" ++ toString value.eventIndex ++
  ",\"namespace_id\":" ++ jsonString (Emit.bytes32Hex value.namespaceId) ++
  ",\"kind\":" ++ toString value.kind ++ ",\"key\":" ++ jsonString (Emit.bytes32Hex value.key) ++
  ",\"version\":" ++ toString value.version ++ ",\"sequence\":" ++ toString value.sequence ++
  ",\"predecessor\":" ++ jsonString (Emit.bytes32Hex value.predecessor) ++
  ",\"payload_digest\":" ++ jsonString (Emit.bytes32Hex value.payloadDigest) ++
  ",\"event_digest\":" ++ jsonString (Emit.bytes32Hex value.eventDigest) ++ "}"

def BatchEnvelopeWire.toJson (value : BatchEnvelopeWire) : String :=
  "{\"coordinate\":" ++ value.coordinate.toJson ++
  ",\"events\":" ++ jsonArray (value.events.map IndexedEventWire.toJson) ++
  ",\"batch_digest\":" ++ jsonString (Emit.bytes32Hex value.batchDigest) ++ "}"

def PreparedOutputWire.toJson (value : PreparedOutputWire) : String :=
  "{\"format\":" ++ jsonString PLAN_OUTPUT_FORMAT ++
  ",\"policy\":" ++ value.policy.toJson ++
  ",\"before_sequence\":" ++ toString value.beforeSequence ++
  ",\"command\":" ++ value.command.toJson ++
  ",\"accepted_events\":" ++ jsonArray (value.acceptedEvents.map EventEnvelopeWire.toJson) ++
  ",\"after\":" ++ value.after.toJson ++
  ",\"intents\":" ++ jsonArray (value.intents.map IntentWire.toJson) ++
  ",\"initial_heads\":" ++ jsonArray (value.initialHeads.map HeadWire.toJson) ++
  ",\"batch\":" ++ value.batch.toJson ++
  ",\"successor_heads\":" ++ jsonArray (value.successorHeads.map HeadWire.toJson) ++ "}"

private def parseCoordinate (j : Json) : Except String CoordinateWire := do
  exactKeys j ["world", "commit_ordinal", "block_id", "turn_hash", "receipt_hash",
    "actor_root", "signer"]
  let value : CoordinateWire := {
    world := ← parseWorld (← j.getObjVal? "world")
    commitOrdinal := ← objectNat j "commit_ordinal"
    blockId := ← objectDigest j "block_id"
    turnHash := ← objectDigest j "turn_hash"
    receiptHash := ← objectDigest j "receipt_hash"
    actorRoot := ← objectDigest j "actor_root"
    signer := ← objectDigest j "signer"
  }
  if value.toSemantic.validB then pure value else throw "invalid finalized coordinate"

private def parseHead (j : Json) : Except String HeadWire := do
  exactKeys j ["world", "namespace_id", "kind", "key", "version", "sequence", "head"]
  let value : HeadWire := {
    world := ← parseWorld (← j.getObjVal? "world")
    namespaceId := ← objectDigest j "namespace_id"
    kind := ← objectNat j "kind"
    key := ← objectDigest j "key"
    version := ← objectNat j "version"
    sequence := ← objectNat j "sequence"
    head := ← objectDigest j "head"
  }
  if value.toSemantic.stream.validB then pure value else throw "invalid stream head"

private def headIdentity (head : HeadWire) : WorldWire × Digest32 × Nat × Digest32 × Nat :=
  (head.world, head.namespaceId, head.kind, head.key, head.version)

private def parsePlanningInput (j : Json) : Except String PlanningInputWire := do
  exactKeys j ["format", "policy", "state", "command", "coordinate", "initial_heads"]
  if (← j.getObjValAs? String "format") != PLAN_INPUT_FORMAT then throw "wrong plan input format"
  let value : PlanningInputWire := {
    policy := ← parsePolicy (← j.getObjVal? "policy")
    state := ← parseState (← j.getObjVal? "state")
    command := ← parseCommand (← j.getObjVal? "command")
    coordinate := ← parseCoordinate (← j.getObjVal? "coordinate")
    initialHeads := ← parseBoundedList (← j.getObjVal? "initial_heads") MAX_HEADS parseHead
  }
  if value.policy != value.state.policy then throw "policy/state substitution"
  if value.coordinate.world != value.policy.world then throw "coordinate world substitution"
  if value.initialHeads.length != MAX_HEADS then throw "initial head count"
  if !(value.initialHeads.map headIdentity).Nodup then throw "duplicate stream head"
  if !value.initialHeads.all (fun head => head.world = value.policy.world) then
    throw "cross-world stream head"
  pure value

def decodePlanningInputWithLimit (limit : Nat) (bytes : String) : Option PlanningInputWire :=
  canonicalDecode parsePlanningInput PlanningInputWire.toJson limit bytes

def decodePlanningInput (bytes : String) : Option PlanningInputWire :=
  decodePlanningInputWithLimit WIRE_BYTE_LIMIT bytes

def IntentWire.ofSemantic? : NightWatchLoopRuntime.IntentPayload → Option IntentWire
  | .semantic event => .semantic <$> EventEnvelopeWire.ofSemantic? event
  | .worldContribution (.maintenance contribution) =>
      some (.maintenance (.ofSemantic contribution))
  | .worldContribution (.expedition terminal contribution artifact debrief cost) =>
      some (.expedition terminal.code (.ofSemantic contribution) artifact.value
        debrief.schemaVersion cost)
  | .custody intent =>
      let destination := match intent.destination with
        | .quarantine => 0 | .archive => 1
      some (.custody intent.terminal.code intent.relic.value destination
        intent.marketEligible intent.directTradeAllowed)

def IndexedEventWire.ofSemantic (value : EventBatch.IndexedEvent) : IndexedEventWire where
  eventIndex := value.eventIndex
  namespaceId := value.statement.aggregate.namespaceId
  kind := value.statement.aggregate.kind
  key := value.statement.aggregate.key
  version := value.statement.version.value
  sequence := value.statement.sequence
  predecessor := value.statement.predecessor
  payloadDigest := value.statement.payloadDigest
  eventDigest := value.eventDigest

private def outputOfPrepared? {before : NightWatchLoop.State}
    {command : NightWatchLoop.Command} (commandWire : PublicCommandWire)
    (initialHeads : List HeadWire)
    (prepared : NightWatchLoopRuntime.PreparedBatch before command) : Option PreparedOutputWire := do
  let events ← prepared.transition.events.mapM EventEnvelopeWire.ofSemantic?
  let intents ← prepared.payloads.mapM IntentWire.ofSemantic?
  some {
    policy := .ofPolicy before.policy
    beforeSequence := before.sequence
    command := commandWire
    acceptedEvents := events
    after := .ofState prepared.transition.after
    intents
    initialHeads
    batch := {
      coordinate := .ofSemantic prepared.envelope.statement.coordinate
      events := prepared.envelope.statement.events.map IndexedEventWire.ofSemantic
      batchDigest := prepared.envelope.batchDigest
    }
    successorHeads := prepared.applied.successorHeads.map HeadWire.ofSemantic
  }

inductive Error where
  | decode
  | coordinateSubstitution
  | headSubstitution
  | policySubstitution
  | stateSubstitution
  | trustedStreamScope
  | commandCode
  | commandRefused
  | unavailableAcceptedEvent
  | runtime (error : NightWatchLoopRuntime.Error)
deriving Repr, DecidableEq

def checkTrustedCarrier (finalizedCoordinate : EventBatch.FinalizedTurnCoordinate)
    (currentHeads : List EventBatch.StreamHead) (input : PlanningInputWire) : Except Error Unit :=
  if input.coordinate = CoordinateWire.ofSemantic finalizedCoordinate then
    if input.initialHeads = currentHeads.map HeadWire.ofSemantic then .ok ()
    else .error .headSubstitution
  else .error .coordinateSubstitution

/-- Sole public planning path.  `before`, `streams`, `boundary`, the finalized
coordinate, and the current stream heads are pre-existing trusted deployment
values.  The JSON copies of coordinate and heads are diagnostic expectations:
they must match exactly, but they are never passed to the runtime.  This
planner cannot authenticate finality or storage; that is the lower bridge's
obligation when supplying these typed arguments.  JSON supplies no authority
constructors. -/
def preparePublic (before : NightWatchLoop.State)
    (streams : NightWatchLoopRuntime.Streams)
    (boundary : NightWatchLoopRuntime.DigestBoundary)
    (finalizedCoordinate : EventBatch.FinalizedTurnCoordinate)
    (currentHeads : List EventBatch.StreamHead)
    (input : PlanningInputWire) : Except Error PreparedOutputWire :=
  match checkTrustedCarrier finalizedCoordinate currentHeads input with
  | .error error => .error error
  | .ok () => do
      let currentHeadViews := currentHeads.map HeadWire.ofSemantic
      if input.policy != PolicyViewWire.ofPolicy before.policy then throw .policySubstitution
      if input.state != StateSnapshotWire.ofState before then throw .stateSubstitution
      if currentHeads.map EventBatch.StreamHead.stream != streams.raw.list then
        throw .trustedStreamScope
      let command ← match input.command.toSemantic? with
        | some command => pure command
        | none => throw .commandCode
      let transition ← match NightWatchLoop.execute before command with
        | some transition => pure transition
        | none => throw .commandRefused
      let prepared ← (NightWatchLoopRuntime.prepareBatch streams boundary
        finalizedCoordinate currentHeads transition).mapError Error.runtime
      match outputOfPrepared? input.command currentHeadViews prepared with
      | some output => pure output
      | none => throw .unavailableAcceptedEvent

def preparePublicJson (before : NightWatchLoop.State)
    (streams : NightWatchLoopRuntime.Streams)
    (boundary : NightWatchLoopRuntime.DigestBoundary)
    (finalizedCoordinate : EventBatch.FinalizedTurnCoordinate)
    (currentHeads : List EventBatch.StreamHead)
    (bytes : String) : Except Error String := do
  let input ← match decodePlanningInput bytes with
    | some input => pure input
    | none => throw .decode
  pure (PreparedOutputWire.toJson (← preparePublic before streams boundary
    finalizedCoordinate currentHeads input))

theorem preparePublic_refuses_coordinate_substitution
    (before : NightWatchLoop.State) (streams : NightWatchLoopRuntime.Streams)
    (boundary : NightWatchLoopRuntime.DigestBoundary)
    (finalizedCoordinate : EventBatch.FinalizedTurnCoordinate)
    (currentHeads : List EventBatch.StreamHead) (input : PlanningInputWire)
    (substituted : input.coordinate ≠ CoordinateWire.ofSemantic finalizedCoordinate) :
    preparePublic before streams boundary finalizedCoordinate currentHeads input =
      .error .coordinateSubstitution := by
  simp [preparePublic, checkTrustedCarrier, substituted]

theorem preparePublic_refuses_head_substitution
    (before : NightWatchLoop.State) (streams : NightWatchLoopRuntime.Streams)
    (boundary : NightWatchLoopRuntime.DigestBoundary)
    (finalizedCoordinate : EventBatch.FinalizedTurnCoordinate)
    (currentHeads : List EventBatch.StreamHead) (input : PlanningInputWire)
    (coordinateExact : input.coordinate = CoordinateWire.ofSemantic finalizedCoordinate)
    (substituted : input.initialHeads ≠ currentHeads.map HeadWire.ofSemantic) :
    preparePublic before streams boundary finalizedCoordinate currentHeads input =
      .error .headSubstitution := by
  simp [preparePublic, checkTrustedCarrier, coordinateExact, substituted]

private def parseIntent (j : Json) : Except String IntentWire := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "semantic" =>
      exactKeys j ["kind", "event"]
      pure (.semantic (← parseEvent (← j.getObjVal? "event")))
  | "maintenance" =>
      exactKeys j ["kind", "contribution"]
      let contribution ← parseContribution (← j.getObjVal? "contribution")
      if contribution != ContributionWire.ofSemantic maintenanceContribution then
        throw "maintenance intent mismatch"
      pure (.maintenance contribution)
  | "expedition" =>
      exactKeys j ["kind", "terminal", "contribution", "featured_artifact",
        "debrief_version", "operational_cost"]
      let terminal ← parseTerminalCode j "terminal"
      let contribution ← parseContribution (← j.getObjVal? "contribution")
      let artifact ← objectNat j "featured_artifact" 8
      let version ← objectNat j "debrief_version"
      let cost ← objectNat j "operational_cost" 12
      let semantic ← match terminalOfCode? terminal with
        | some value => pure value | none => throw "unknown terminal"
      let receipt ← match outcomeReceipt? semantic with
        | some value => pure value | none => throw "terminal refused"
      if contribution != ContributionWire.ofSemantic receipt.contribution ||
          artifact != receipt.featuredArtifact.value || version != receipt.debrief.schemaVersion ||
          cost != receipt.terminalOperationalCost then throw "expedition intent mismatch"
      pure (.expedition terminal contribution artifact version cost)
  | "custody" =>
      exactKeys j ["kind", "terminal", "relic", "destination", "market_eligible",
        "direct_trade_allowed"]
      let terminal ← parseTerminalCode j "terminal"
      let relic ← objectNat j "relic" 3
      let destination ← objectNat j "destination" 1
      let market ← parseBool (← j.getObjVal? "market_eligible")
      let trade ← parseBool (← j.getObjVal? "direct_trade_allowed")
      if market || trade || relic = 0 then throw "custody policy mismatch"
      pure (.custody terminal relic destination market trade)
  | _ => throw "unknown intent kind"

private def parseIndexedEvent (j : Json) : Except String IndexedEventWire := do
  exactKeys j ["event_index", "namespace_id", "kind", "key", "version", "sequence",
    "predecessor", "payload_digest", "event_digest"]
  pure {
    eventIndex := ← objectNat j "event_index" 63
    namespaceId := ← objectDigest j "namespace_id"
    kind := ← objectNat j "kind"
    key := ← objectDigest j "key"
    version := ← objectNat j "version"
    sequence := ← objectNat j "sequence"
    predecessor := ← objectDigest j "predecessor"
    payloadDigest := ← objectDigest j "payload_digest"
    eventDigest := ← objectDigest j "event_digest"
  }

private def parseBatch (j : Json) : Except String BatchEnvelopeWire := do
  exactKeys j ["coordinate", "events", "batch_digest"]
  pure {
    coordinate := ← parseCoordinate (← j.getObjVal? "coordinate")
    events := ← parseBoundedList (← j.getObjVal? "events") 64 parseIndexedEvent
    batchDigest := ← objectDigest j "batch_digest"
  }

private def indexedMatchesHead (event : IndexedEventWire) (head : HeadWire) : Bool :=
  event.namespaceId = head.namespaceId && event.kind = head.kind &&
  event.key = head.key && event.version = head.version

private def IntentWire.streamIndex : IntentWire → Nat
  | .semantic event => if event.event = 1 then 0
      else if event.event = 2 || event.event = 5 || event.event = 6 || event.event = 7 then 1
      else 2
  | .maintenance _ | .expedition .. => 3
  | .custody .. => 4

private def intentMatchesIndexedHead (heads : List HeadWire)
    (intent : IntentWire) (event : IndexedEventWire) : Bool :=
  match heads[intent.streamIndex]? with
  | some head => indexedMatchesHead event head
  | none => false

private def semanticIntentEvents : List IntentWire → List EventEnvelopeWire
  | [] => []
  | .semantic event :: intents => event :: semanticIntentEvents intents
  | _ :: intents => semanticIntentEvents intents

private def advanceIndexedHead (heads : List HeadWire)
    (event : IndexedEventWire) : Option (List HeadWire) := do
  let head ← heads.find? (indexedMatchesHead event)
  if event.sequence != head.sequence + 1 || event.predecessor != head.head then none
  some (heads.map fun prior => if indexedMatchesHead event prior then
    { prior with sequence := event.sequence, head := event.eventDigest } else prior)

private def replayIndexedHeads : List HeadWire → List IndexedEventWire → Option (List HeadWire)
  | heads, [] => some heads
  | heads, event :: events => do
      let next ← advanceIndexedHead heads event
      replayIndexedHeads next events

private def parsePreparedOutput (j : Json) : Except String PreparedOutputWire := do
  exactKeys j ["format", "policy", "before_sequence", "command", "accepted_events", "after",
    "intents", "initial_heads", "batch", "successor_heads"]
  if (← j.getObjValAs? String "format") != PLAN_OUTPUT_FORMAT then throw "wrong plan output format"
  let value : PreparedOutputWire := {
    policy := ← parsePolicy (← j.getObjVal? "policy")
    beforeSequence := ← objectNat j "before_sequence"
    command := ← parseCommand (← j.getObjVal? "command")
    acceptedEvents := ← parseBoundedList
      (← j.getObjVal? "accepted_events") MAX_ACCEPTED_EVENTS parseEvent
    after := ← parseState (← j.getObjVal? "after")
    intents := ← parseBoundedList (← j.getObjVal? "intents") 64 parseIntent
    initialHeads := ← parseBoundedList (← j.getObjVal? "initial_heads") MAX_HEADS parseHead
    batch := ← parseBatch (← j.getObjVal? "batch")
    successorHeads := ← parseBoundedList (← j.getObjVal? "successor_heads") MAX_HEADS parseHead
  }
  if value.policy != value.after.policy then throw "output policy substitution"
  if value.acceptedEvents = [] || !denseEventSequenceB value.beforeSequence value.acceptedEvents then
    throw "accepted event sequence not dense"
  if value.after.sequence != value.beforeSequence + value.acceptedEvents.length then
    throw "after sequence mismatch"
  if value.initialHeads.length != MAX_HEADS || value.successorHeads.length != MAX_HEADS then
    throw "head count mismatch"
  if !(value.initialHeads.map headIdentity).Nodup ||
      value.initialHeads.map headIdentity != value.successorHeads.map headIdentity then
    throw "head identity substitution"
  if !value.initialHeads.all (fun head => head.world = value.policy.world) then
    throw "initial head world substitution"
  if value.batch.coordinate.world != value.policy.world then throw "batch world substitution"
  if value.batch.events.length != value.intents.length then throw "intent/batch count mismatch"
  if semanticIntentEvents value.intents != value.acceptedEvents then
    throw "semantic intent/event mismatch"
  if !(value.intents.zip value.batch.events).all fun pair =>
      intentMatchesIndexedHead value.initialHeads pair.1 pair.2 then
    throw "intent stream substitution"
  if value.batch.events.map IndexedEventWire.eventIndex != List.range value.batch.events.length then
    throw "batch event indexes not dense"
  if !value.batch.events.all (fun event => event.namespaceId = value.policy.world.federationId) then
    throw "batch namespace substitution"
  let replayed ← match replayIndexedHeads value.initialHeads value.batch.events with
    | some heads => pure heads
    | none => throw "batch predecessor sequence mismatch"
  if replayed != value.successorHeads then throw "successor head mismatch"
  pure value

def decodePreparedOutputWithLimit (limit : Nat) (bytes : String) : Option PreparedOutputWire :=
  canonicalDecode parsePreparedOutput PreparedOutputWire.toJson limit bytes

def decodePreparedOutput (bytes : String) : Option PreparedOutputWire :=
  decodePreparedOutputWithLimit WIRE_BYTE_LIMIT bytes

/-! ## Canonicality certificates

Every successful decoder fixes one byte spelling: decoding cannot silently
normalise key order, whitespace, decimal spelling, digest case, or unknown fields.
-/

theorem decodeCommandWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : PublicCommandWire}
    (accepted : decodeCommandWithLimit limit bytes = some value) :
    value.toJson = bytes :=
  canonicalDecode_reencodes parseCommand PublicCommandWire.toJson limit bytes value accepted

theorem decodePolicyViewWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : PolicyViewWire}
    (accepted : decodePolicyViewWithLimit limit bytes = some value) :
    value.toJson = bytes :=
  canonicalDecode_reencodes parsePolicy PolicyViewWire.toJson limit bytes value accepted

theorem decodeStateViewWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : StateSnapshotWire}
    (accepted : decodeStateViewWithLimit limit bytes = some value) :
    value.toJson = bytes :=
  canonicalDecode_reencodes parseState StateSnapshotWire.toJson limit bytes value accepted

theorem decodeEventViewWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : EventEnvelopeWire}
    (accepted : decodeEventViewWithLimit limit bytes = some value) :
    value.toJson = bytes :=
  canonicalDecode_reencodes parseEvent EventEnvelopeWire.toJson limit bytes value accepted

theorem decodePlanningInputWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : PlanningInputWire}
    (accepted : decodePlanningInputWithLimit limit bytes = some value) :
    value.toJson = bytes :=
  canonicalDecode_reencodes parsePlanningInput PlanningInputWire.toJson limit bytes value accepted

theorem decodePreparedOutputWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : PreparedOutputWire}
    (accepted : decodePreparedOutputWithLimit limit bytes = some value) :
    value.toJson = bytes :=
  canonicalDecode_reencodes parsePreparedOutput PreparedOutputWire.toJson limit bytes value accepted
