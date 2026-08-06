/-
# NightWatchCampaignWire — the canonical JSON boundary that makes one watch playable

`NightWatchCampaign` is a complete judged kernel with no way in.  It has zero
`@[export]` and no wire codec, so no browser, node, or curator can reach it.
This module is that boundary and nothing else: it is a JSON **codec**, not a
constraint system — no AIR, no gadget, no `air_accepts` lives here.

## The asymmetry, stated plainly

`NightWatchCampaign.State` is `private mk ::`.  Canonical JSON therefore
**cannot construct a state**, and this file deliberately does not try: there is
no state parser, and `StateViewWire` is encode-only.  A state is reached the one
legitimate way — `initialState` on an activated `Config`, then `replay` over the
player's own command log.  The host persists the COMMAND LIST, not the state.  A
state decoder would be an authority hole (it would let a caller assert any
sequence, evidence total, resource balance, or consumed-nullifier set), so the
absence is the design.

`no_state_view_decoder_can_be_sound` proves that absence is not merely a
convention: the published view is provably NOT injective on states, so no
function `StateViewWire → Option State` can round-trip.  The witness is two
states differing only in which nullifier they consumed.

`RawConfig` and `Command`, by contrast, ARE publicly constructible in the kernel
(`activate?` is the smart constructor and `Command` is a plain structure), so
they get real decoders — direct into the semantic types, with no mirror
structure that could drift.

## Fail-closed

Every decoder runs through `canonicalDecode`: parse, re-encode, and refuse
unless the bytes are byte-identical.  One JSON value therefore has exactly one
accepted spelling — key order, whitespace, decimal spelling, digest case, and
unknown fields are all fixed, not normalised.  `exactKeys` refuses missing and
unknown fields; every natural carries the kernel's own bound at the parser
(`MAX_RULES`, `MAX_HAZARD_CYCLE`, `MAX_RESOURCE`, `MAX_EVIDENCE`, `MAX_WOUNDS`,
`MAX_STRAIN`, `MAX_SHIFTS`, `METRIC_LIMIT`, `MAX_LOCAL_SERVICE`); unknown
station, task, role and action tags refuse.

## ⚑ THIS EXPORT CONFERS NO AUTHORITY — the config arrives in the caller's bytes

`InputWire` carries `config`, so `dregg_poa_night_watch_campaign_judge` is a
**pure function of the bytes it is handed** and reads no state.  `activate?`
checks that a config is *structurally* valid; nothing here checks that it is the
*authentic* one.  A caller who supplies a config whose every `riskThreshold` is
zero and whose every `successContribution` is maximal gets a judged, internally
consistent, entirely fraudulent watch — and every theorem in this file still
holds, because they are all conditional on the config that was supplied.

**The host must obtain the config from its own authenticated state and never
pass a player's copy through.**  The intended source is a curator-signed
`ActivatedContent` manifest component, the same way `authorizeEmbeddedGalleyPolicyForWorld?`
(`ActivatedContent.lean:314`) supplies Galley's policy; that witness constructor
does not exist for this organ yet, and until it does there is no authenticated
config anywhere and this export must not be mounted on a route.

This is the `dregg_poa_signal_slot_derive` discipline stated for this organ
(`SlotDeriveRuntime.lean:205-211`): the export is the derivation, not the
authority.  A node that forwards `InputWire.config` from a request body has
built an organ any player can forge, and no amount of proof in this file will
say so.

## Two things about the kernel a reader should know

* `configValidB` does **not** require `raw.logStream.validB`.  It constrains
  only `logStream.aggregate.namespaceId = progression.federationId`; the stream's
  `world` is otherwise unchecked, so an activated `Config` may name a zero world
  identity.  This wire does not add that check — semantic validity is
  `activate?`'s job and a wire that refuses more than the kernel is a second
  disagreeing shape.  It is named here so it is findable.
* Replay cost is quadratic, by derivation not measurement: `judge` tests
  `command.nullifier ∈ state.consumedActions` and then inserts into that
  `Finset Digest32`, both linear, so replaying `n` commands costs Θ(n²) digest
  comparisons.  `MAX_COMMAND_LOG` is the structural maximum (four commands per
  shift × `MAX_SHIFTS`), not a recommended one.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Games.PathOfAngels.NightWatchCampaign
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignWire

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## Wire constants -/

abbrev CONFIG_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-CONFIG-1"
abbrev COMMAND_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-COMMAND-1"
abbrev INPUT_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-OUT-1"

abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1
abbrev WIRE_BYTE_LIMIT : Nat := 4 * 1024 * 1024

/-- Four commands (claim, choose, resolve, debrief) complete one shift, so a
full campaign log is four times the shift ceiling. -/
abbrev MAX_COMMAND_LOG : Nat := 4 * NightWatchCampaign.MAX_SHIFTS

/-- The player view carries the tail of the logbook, not all of it. -/
abbrev MAX_HISTORY_VIEW : Nat := 32

/-! ## Canonical JSON helpers -/

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

/-- Written as an explicit `match` rather than a `do`-block so the refusal is a
one-step `split`, not a monad-unfolding argument. -/
private def parseBoundedList {T : Type} (j : Json) (limit : Nat)
    (parse : Json → Except String T) : Except String (List T) :=
  match j.getArr? with
  | .error message => .error message
  | .ok values =>
      if values.size > limit then .error "array exceeds wire bound"
      else values.toList.mapM parse

private def parseOption {T : Type} (j : Json)
    (parse : Json → Except String T) : Except String (Option T) :=
  match j with
  | .null => pure none
  | value => some <$> parse value

/-- Parse, then re-encode and demand byte identity.  One value, one spelling. -/
private def canonicalDecode {T : Type} (parse : Json → Except String T)
    (encode : T → String) (byteLimit : Nat) (bytes : String) : Option T :=
  if bytes.utf8ByteSize > byteLimit then none
  else match Json.parse bytes with
    | .error _ => none
    | .ok json => match parse json with
      | .error _ => none
      | .ok value => if _h : encode value = bytes then some value else none

theorem canonicalDecode_reencodes {T : Type} (parse : Json → Except String T)
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

/-- An array longer than its wire bound refuses, whatever the element parser is.
This is the general fact the per-field size checks are instances of. -/
theorem parseBoundedList_refuses_oversized_array {T : Type} (j : Json)
    (limit : Nat) (parse : Json → Except String T) (values : Array Json)
    (isArray : j.getArr? = Except.ok values) (oversized : limit < values.size) :
    parseBoundedList j limit parse = .error "array exceeds wire bound" := by
  simp [parseBoundedList, isArray, oversized]

#assert_axioms canonicalDecode_reencodes
#assert_axioms parseBoundedList_refuses_oversized_array

/-! ## Stable finite codes

The campaign's own `Station.tag`/`Task.tag` are the wire codes, so there is one
numbering rather than a second one that can drift from it.  Roles get a code
here because `CrewRole` carries none. -/

def stationOfTag? : Nat → Option NightWatchCampaign.Station
  | 1 => some .bridge
  | 2 => some .engineSpine
  | 3 => some .signalGallery
  | 4 => some .containment
  | 5 => some .galley
  | 6 => some .infirmary
  | _ => none

def taskOfTag? : Nat → Option NightWatchCampaign.Task
  | 1 => some .plotDrift
  | 2 => some .coolantBalance
  | 3 => some .traceSignal
  | 4 => some .inspectSeal
  | 5 => some .rationAudit
  | 6 => some .recoveryRound
  | _ => none

def roleCode : CrewRole → Nat
  | .pathfinder => 0
  | .engineer => 1
  | .containment => 2
  | .quartermaster => 3

def roleOfCode? : Nat → Option CrewRole
  | 0 => some .pathfinder
  | 1 => some .engineer
  | 2 => some .containment
  | 3 => some .quartermaster
  | _ => none

theorem stationOfTag_tag (station : NightWatchCampaign.Station) :
    stationOfTag? station.tag = some station := by
  cases station <;> rfl

theorem taskOfTag_tag (task : NightWatchCampaign.Task) :
    taskOfTag? task.tag = some task := by
  cases task <;> rfl

theorem roleOfCode_roleCode (role : CrewRole) : roleOfCode? (roleCode role) = some role := by
  cases role <;> rfl

#assert_axioms stationOfTag_tag
#assert_axioms taskOfTag_tag
#assert_axioms roleOfCode_roleCode

/-! ## Refusal labels — encode-only

`errorName` never appears on an input wire; it labels a refusal in the output
bytes.  The two theorems below say together that the label distinguishes every
refusal the kernel can raise. -/

def errorName : NightWatchCampaign.Error → String
  | .wrongSequence => "wrong_sequence"
  | .replayedAction => "replayed_action"
  | .shiftLimit => "shift_limit"
  | .wrongPhase => "wrong_phase"
  | .unknownOfficer => "unknown_officer"
  | .officerActorMismatch => "officer_actor_mismatch"
  | .unknownTask => "unknown_task"
  | .roleMismatch => "role_mismatch"
  | .insufficientResources => "insufficient_resources"
  | .evidenceBound => "evidence_bound"
  | .missingHealth => "missing_health"
  | .historyLimit => "history_limit"
  | .callerAuthoredOutcome => "caller_authored_outcome"

def allErrors : List NightWatchCampaign.Error :=
  [ .wrongSequence, .replayedAction, .shiftLimit, .wrongPhase, .unknownOfficer
  , .officerActorMismatch, .unknownTask, .roleMismatch, .insufficientResources
  , .evidenceBound, .missingHealth, .historyLimit
  , .callerAuthoredOutcome ]

theorem allErrors_is_exhaustive (error : NightWatchCampaign.Error) : error ∈ allErrors := by
  cases error <;> simp [allErrors]

theorem error_names_are_pairwise_distinct : (allErrors.map errorName).Nodup := by
  native_decide

#assert_axioms allErrors_is_exhaustive
#assert_compiled error_names_are_pairwise_distinct

/-! ## Curator-signed configuration — decode AND encode

Decoding lands directly in `NightWatchCampaign.RawConfig`; there is no mirror
structure, so there is nothing that can agree with the kernel today and disagree
with it later.  Admission to `Config` is still `activate?`'s alone. -/

def worldIdentityJson (world : EventBatch.WorldIdentity) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex world.federationId) ++
  ",\"content_root\":" ++ jsonString (Emit.bytes32Hex world.contentRoot) ++
  ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex world.activationDigest) ++
  ",\"content_session\":" ++ jsonString (Emit.bytes32Hex world.contentSession) ++
  ",\"content_epoch\":" ++ toString world.contentEpoch.value ++ "}"

def aggregateJson (aggregate : EventSourcing.AggregateId) : String :=
  "{\"namespace_id\":" ++ jsonString (Emit.bytes32Hex aggregate.namespaceId) ++
  ",\"kind\":" ++ toString aggregate.kind ++
  ",\"key\":" ++ jsonString (Emit.bytes32Hex aggregate.key) ++ "}"

def streamJson (stream : EventBatch.StreamId) : String :=
  "{\"world\":" ++ worldIdentityJson stream.world ++
  ",\"aggregate\":" ++ aggregateJson stream.aggregate ++
  ",\"version\":" ++ toString stream.version.value ++ "}"

def progressionJson (identity : ShipLifeProgression.ProgressionIdentity) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex identity.federationId) ++
  ",\"content_session\":" ++ jsonString (Emit.bytes32Hex identity.contentSession) ++
  ",\"content_epoch\":" ++ toString identity.contentEpoch.value ++
  ",\"season\":" ++ toString identity.season.value ++
  ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex identity.activationDigest) ++
  ",\"owner\":" ++ jsonString (Emit.bytes32Hex identity.owner) ++ "}"

def seatJson (seat : Seat) : String :=
  "{\"id\":" ++ toString seat.id.value ++
  ",\"player_key\":" ++ jsonString (Emit.bytes32Hex seat.playerKey) ++
  ",\"credential\":" ++ toString seat.credential.value ++
  ",\"role\":" ++ toString (roleCode seat.role) ++
  ",\"initial_counter\":" ++ toString seat.initialCounter ++ "}"

def contributionJson (value : NightWatchCampaign.ContributionDelta) : String :=
  "{\"intel\":" ++ toString value.intel ++
  ",\"supplies\":" ++ toString value.supplies ++
  ",\"cohesion\":" ++ toString value.cohesion ++
  ",\"influence\":" ++ toString value.influence ++
  ",\"score\":" ++ toString value.score ++ "}"

def resourcesJson (value : NightWatchCampaign.ShipResources) : String :=
  "{\"propellant\":" ++ toString value.propellant ++
  ",\"munitions\":" ++ toString value.munitions ++
  ",\"supplies\":" ++ toString value.supplies ++
  ",\"morale\":" ++ toString value.morale ++ "}"

def effectsJson (value : NightWatchCampaign.WorldEffects) : String :=
  "{\"spend_propellant\":" ++ toString value.spendPropellant ++
  ",\"spend_munitions\":" ++ toString value.spendMunitions ++
  ",\"spend_supplies\":" ++ toString value.spendSupplies ++
  ",\"spend_morale\":" ++ toString value.spendMorale ++
  ",\"gain_propellant\":" ++ toString value.gainPropellant ++
  ",\"gain_munitions\":" ++ toString value.gainMunitions ++
  ",\"gain_supplies\":" ++ toString value.gainSupplies ++
  ",\"gain_morale\":" ++ toString value.gainMorale ++ "}"

def healthEffectJson (value : NightWatchCampaign.HealthEffect) : String :=
  "{\"wounds_added\":" ++ toString value.woundsAdded ++
  ",\"strain_added\":" ++ toString value.strainAdded ++
  ",\"wounds_recovered\":" ++ toString value.woundsRecovered ++
  ",\"strain_recovered\":" ++ toString value.strainRecovered ++ "}"

def taskRuleJson (rule : NightWatchCampaign.TaskRule) : String :=
  "{\"station\":" ++ toString rule.station.tag ++
  ",\"task\":" ++ toString rule.task.tag ++
  ",\"role\":" ++ toString (roleCode rule.role) ++
  ",\"risk_threshold\":" ++ toString rule.riskThreshold ++
  ",\"success_contribution\":" ++ contributionJson rule.successContribution ++
  ",\"failure_contribution\":" ++ contributionJson rule.failureContribution ++
  ",\"success_effects\":" ++ effectsJson rule.successEffects ++
  ",\"failure_effects\":" ++ effectsJson rule.failureEffects ++
  ",\"success_health\":" ++ healthEffectJson rule.successHealth ++
  ",\"failure_health\":" ++ healthEffectJson rule.failureHealth ++
  ",\"success_evidence\":" ++ toString rule.successEvidence ++
  ",\"failure_evidence\":" ++ toString rule.failureEvidence ++
  ",\"local_service\":" ++ toString rule.localService.val ++
  ",\"beta_discovery\":" ++
    optionJson (fun (artifact : ContentContract.ArtifactId) => toString artifact.value)
      rule.betaDiscovery ++
  ",\"discovery_evidence_required\":" ++ toString rule.discoveryEvidenceRequired ++
  ",\"task_content_id\":" ++ jsonString (Emit.bytes32Hex rule.taskContentId) ++
  ",\"success_content_id\":" ++ jsonString (Emit.bytes32Hex rule.successContentId) ++
  ",\"failure_content_id\":" ++ jsonString (Emit.bytes32Hex rule.failureContentId) ++ "}"

def configJson (raw : NightWatchCampaign.RawConfig) : String :=
  "{\"format\":" ++ jsonString CONFIG_FORMAT ++
  ",\"schema_version\":" ++ toString raw.schemaVersion ++
  ",\"progression\":" ++ progressionJson raw.progression ++
  ",\"log_stream\":" ++ streamJson raw.logStream ++
  ",\"roster\":" ++ jsonArray (raw.roster.map seatJson) ++
  ",\"rules\":" ++ jsonArray (raw.rules.map taskRuleJson) ++
  ",\"hazard_cycle\":" ++ jsonArray (raw.hazardCycle.map toString) ++
  ",\"initial_resources\":" ++ resourcesJson raw.initialResources ++
  ",\"max_shifts\":" ++ toString raw.maxShifts ++ "}"

private def parseWorldIdentity (j : Json) : Except String EventBatch.WorldIdentity := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ⟨← objectNat j "content_epoch"⟩
  }

private def parseAggregate (j : Json) : Except String EventSourcing.AggregateId := do
  exactKeys j ["namespace_id", "kind", "key"]
  pure {
    namespaceId := ← objectDigest j "namespace_id"
    kind := ← objectNat j "kind"
    key := ← objectDigest j "key"
  }

private def parseStream (j : Json) : Except String EventBatch.StreamId := do
  exactKeys j ["world", "aggregate", "version"]
  pure {
    world := ← parseWorldIdentity (← j.getObjVal? "world")
    aggregate := ← parseAggregate (← j.getObjVal? "aggregate")
    version := ⟨← objectNat j "version"⟩
  }

private def parseProgression (j : Json) :
    Except String ShipLifeProgression.ProgressionIdentity := do
  exactKeys j ["federation_id", "content_session", "content_epoch", "season",
    "activation_digest", "owner"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ⟨← objectNat j "content_epoch"⟩
    season := ⟨← objectNat j "season"⟩
    activationDigest := ← objectDigest j "activation_digest"
    owner := ← objectDigest j "owner"
  }

private def parseSeat (j : Json) : Except String Seat := do
  exactKeys j ["id", "player_key", "credential", "role", "initial_counter"]
  let role ← match roleOfCode? (← objectNat j "role" 3) with
    | some value => pure value
    | none => throw "unknown crew role code"
  pure {
    id := ⟨← objectNat j "id" 3⟩
    playerKey := ← objectDigest j "player_key"
    credential := ⟨← objectNat j "credential"⟩
    role
    initialCounter := ← objectNat j "initial_counter"
  }

private def parseContribution (j : Json) :
    Except String NightWatchCampaign.ContributionDelta := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score"]
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
  }

private def parseResources (j : Json) : Except String NightWatchCampaign.ShipResources := do
  exactKeys j ["propellant", "munitions", "supplies", "morale"]
  pure {
    propellant := ← objectNat j "propellant" NightWatchCampaign.MAX_RESOURCE
    munitions := ← objectNat j "munitions" NightWatchCampaign.MAX_RESOURCE
    supplies := ← objectNat j "supplies" NightWatchCampaign.MAX_RESOURCE
    morale := ← objectNat j "morale" NightWatchCampaign.MAX_RESOURCE
  }

private def parseEffects (j : Json) : Except String NightWatchCampaign.WorldEffects := do
  exactKeys j ["spend_propellant", "spend_munitions", "spend_supplies", "spend_morale",
    "gain_propellant", "gain_munitions", "gain_supplies", "gain_morale"]
  pure {
    spendPropellant := ← objectNat j "spend_propellant" NightWatchCampaign.MAX_RESOURCE
    spendMunitions := ← objectNat j "spend_munitions" NightWatchCampaign.MAX_RESOURCE
    spendSupplies := ← objectNat j "spend_supplies" NightWatchCampaign.MAX_RESOURCE
    spendMorale := ← objectNat j "spend_morale" NightWatchCampaign.MAX_RESOURCE
    gainPropellant := ← objectNat j "gain_propellant" NightWatchCampaign.MAX_RESOURCE
    gainMunitions := ← objectNat j "gain_munitions" NightWatchCampaign.MAX_RESOURCE
    gainSupplies := ← objectNat j "gain_supplies" NightWatchCampaign.MAX_RESOURCE
    gainMorale := ← objectNat j "gain_morale" NightWatchCampaign.MAX_RESOURCE
  }

private def parseHealthEffect (j : Json) : Except String NightWatchCampaign.HealthEffect := do
  exactKeys j ["wounds_added", "strain_added", "wounds_recovered", "strain_recovered"]
  pure {
    woundsAdded := ← objectNat j "wounds_added" NightWatchCampaign.MAX_WOUNDS
    strainAdded := ← objectNat j "strain_added" NightWatchCampaign.MAX_STRAIN
    woundsRecovered := ← objectNat j "wounds_recovered" NightWatchCampaign.MAX_WOUNDS
    strainRecovered := ← objectNat j "strain_recovered" NightWatchCampaign.MAX_STRAIN
  }

private def parseTaskRule (j : Json) : Except String NightWatchCampaign.TaskRule := do
  exactKeys j ["station", "task", "role", "risk_threshold", "success_contribution",
    "failure_contribution", "success_effects", "failure_effects", "success_health",
    "failure_health", "success_evidence", "failure_evidence", "local_service",
    "beta_discovery", "discovery_evidence_required", "task_content_id",
    "success_content_id", "failure_content_id"]
  let station ← match stationOfTag? (← objectNat j "station" 6) with
    | some value => pure value
    | none => throw "unknown station tag"
  let task ← match taskOfTag? (← objectNat j "task" 6) with
    | some value => pure value
    | none => throw "unknown task tag"
  let role ← match roleOfCode? (← objectNat j "role" 3) with
    | some value => pure value
    | none => throw "unknown crew role code"
  let service ← objectNat j "local_service" GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE
  if bounded : service ≤ GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE then
    pure {
      station
      task
      role
      riskThreshold := ← objectNat j "risk_threshold" 100
      successContribution := ← parseContribution (← j.getObjVal? "success_contribution")
      failureContribution := ← parseContribution (← j.getObjVal? "failure_contribution")
      successEffects := ← parseEffects (← j.getObjVal? "success_effects")
      failureEffects := ← parseEffects (← j.getObjVal? "failure_effects")
      successHealth := ← parseHealthEffect (← j.getObjVal? "success_health")
      failureHealth := ← parseHealthEffect (← j.getObjVal? "failure_health")
      successEvidence := ← objectNat j "success_evidence" NightWatchCampaign.MAX_EVIDENCE
      failureEvidence := ← objectNat j "failure_evidence" NightWatchCampaign.MAX_EVIDENCE
      localService := ⟨service, Nat.lt_succ_of_le bounded⟩
      betaDiscovery := ← parseOption (← j.getObjVal? "beta_discovery")
        (fun value => do pure ⟨← parseNat value⟩)
      discoveryEvidenceRequired :=
        ← objectNat j "discovery_evidence_required" NightWatchCampaign.MAX_EVIDENCE
      taskContentId := ← objectDigest j "task_content_id"
      successContentId := ← objectDigest j "success_content_id"
      failureContentId := ← objectDigest j "failure_content_id"
    }
  else throw "local service exceeds the galley bound"

private def parseConfig (j : Json) : Except String NightWatchCampaign.RawConfig := do
  exactKeys j ["format", "schema_version", "progression", "log_stream", "roster", "rules",
    "hazard_cycle", "initial_resources", "max_shifts"]
  if (← j.getObjValAs? String "format") != CONFIG_FORMAT then throw "wrong config format"
  pure {
    schemaVersion := ← objectNat j "schema_version"
    progression := ← parseProgression (← j.getObjVal? "progression")
    logStream := ← parseStream (← j.getObjVal? "log_stream")
    roster := ← parseBoundedList (← j.getObjVal? "roster") CrewFieldMission.CREW_SIZE parseSeat
    rules := ← parseBoundedList (← j.getObjVal? "rules") NightWatchCampaign.MAX_RULES parseTaskRule
    hazardCycle := ← parseBoundedList (← j.getObjVal? "hazard_cycle")
      NightWatchCampaign.MAX_HAZARD_CYCLE (fun value => parseNat value 99)
    initialResources := ← parseResources (← j.getObjVal? "initial_resources")
    maxShifts := ← objectNat j "max_shifts" NightWatchCampaign.MAX_SHIFTS
  }

def decodeConfigWithLimit (limit : Nat) (bytes : String) :
    Option NightWatchCampaign.RawConfig :=
  canonicalDecode parseConfig configJson limit bytes

def decodeConfig (bytes : String) : Option NightWatchCampaign.RawConfig :=
  decodeConfigWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The player's submission -/

def actionJson : NightWatchCampaign.Action → String
  | .claimOfficer actor seat =>
      "{\"kind\":\"claim_officer\",\"actor\":" ++ jsonString (Emit.bytes32Hex actor) ++
      ",\"seat\":" ++ toString seat.value ++ "}"
  | .chooseTask station task =>
      "{\"kind\":\"choose_task\",\"station\":" ++ toString station.tag ++
      ",\"task\":" ++ toString task.tag ++ "}"
  | .resolve => "{\"kind\":\"resolve\"}"
  | .debrief => "{\"kind\":\"debrief\"}"

def commandJson (command : NightWatchCampaign.Command) : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++
  ",\"sequence\":" ++ toString command.sequence ++
  ",\"nullifier\":" ++ jsonString (Emit.bytes32Hex command.nullifier) ++
  ",\"action\":" ++ actionJson command.action ++ "}"

private def parseAction (j : Json) : Except String NightWatchCampaign.Action := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "claim_officer" => do
      exactKeys j ["kind", "actor", "seat"]
      pure (.claimOfficer (← objectDigest j "actor") ⟨← objectNat j "seat" 3⟩)
  | "choose_task" => do
      exactKeys j ["kind", "station", "task"]
      let station ← match stationOfTag? (← objectNat j "station" 6) with
        | some value => pure value
        | none => throw "unknown station tag"
      let task ← match taskOfTag? (← objectNat j "task" 6) with
        | some value => pure value
        | none => throw "unknown task tag"
      pure (.chooseTask station task)
  | "resolve" => do
      exactKeys j ["kind"]
      pure .resolve
  | "debrief" => do
      exactKeys j ["kind"]
      pure .debrief
  | _ => throw "unknown action kind"

private def parseCommand (j : Json) : Except String NightWatchCampaign.Command := do
  exactKeys j ["format", "sequence", "nullifier", "action"]
  if (← j.getObjValAs? String "format") != COMMAND_FORMAT then throw "wrong command format"
  pure {
    sequence := ← objectNat j "sequence"
    nullifier := ← objectDigest j "nullifier"
    action := ← parseAction (← j.getObjVal? "action")
  }

def decodeCommandWithLimit (limit : Nat) (bytes : String) : Option NightWatchCampaign.Command :=
  canonicalDecode parseCommand commandJson limit bytes

def decodeCommand (bytes : String) : Option NightWatchCampaign.Command :=
  decodeCommandWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The judge envelope

The host holds a curator-signed config and the player's own command log.  It
never holds a serialized state, because there is no way to serialize one back. -/

structure InputWire where
  config : NightWatchCampaign.RawConfig
  history : List NightWatchCampaign.Command
  command : NightWatchCampaign.Command
deriving DecidableEq

def inputJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
  ",\"config\":" ++ configJson input.config ++
  ",\"history\":" ++ jsonArray (input.history.map commandJson) ++
  ",\"command\":" ++ commandJson input.command ++ "}"

private def parseInput (j : Json) : Except String InputWire := do
  exactKeys j ["format", "config", "history", "command"]
  if (← j.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  pure {
    config := ← parseConfig (← j.getObjVal? "config")
    history := ← parseBoundedList (← j.getObjVal? "history") MAX_COMMAND_LOG parseCommand
    command := ← parseCommand (← j.getObjVal? "command")
  }

def decodeInputWithLimit (limit : Nat) (bytes : String) : Option InputWire :=
  canonicalDecode parseInput inputJson limit bytes

def decodeInput (bytes : String) : Option InputWire :=
  decodeInputWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The proof-erased player view — ENCODE ONLY

There is deliberately no `parseStateView`.  `no_state_view_decoder_can_be_sound`
below shows that adding one could not be faithful even in principle. -/

structure HealthViewWire where
  seat : Nat
  wounds : Nat
  strain : Nat
  recoveryObserved : Nat
deriving DecidableEq

structure MasteryViewWire where
  seat : Nat
  station : Nat
  xp : Nat
  level : Nat
deriving DecidableEq

inductive PhaseViewWire where
  | idle
  | claimed (seat : Nat)
  | assigned (seat : Nat) (station : Nat) (task : Nat)
  | awaitingDebrief (shift : Nat) (seat : Nat) (station : Nat) (task : Nat)
      (hazardRoll : Nat) (success : Bool)
deriving DecidableEq

structure HistoryRowWire where
  shift : Nat
  seat : Nat
  station : Nat
  task : Nat
  success : Bool
  hazardRoll : Nat
  riskThreshold : Nat
  evidenceAfter : Nat
  terminalContentId : Digest32
deriving DecidableEq

structure StateViewWire where
  sequence : Nat
  shift : Nat
  resources : NightWatchCampaign.ShipResources
  evidence : Nat
  health : List HealthViewWire
  mastery : List MasteryViewWire
  phase : PhaseViewWire
  historyLength : Nat
  recentHistory : List HistoryRowWire
  intentCount : Nat
  consumedActionCount : Nat
deriving DecidableEq

def HistoryRowWire.ofEntry (entry : NightWatchCampaign.LogbookEntry) : HistoryRowWire where
  shift := entry.shift
  seat := entry.seat.value
  station := entry.station.tag
  task := entry.task.tag
  success := entry.success
  hazardRoll := entry.hazardRoll
  riskThreshold := entry.riskThreshold
  evidenceAfter := entry.evidenceAfter
  terminalContentId := entry.terminalContentId

def StateViewWire.ofState (state : NightWatchCampaign.State) : StateViewWire where
  sequence := state.sequence
  shift := state.shift
  resources := state.resources
  evidence := state.evidence
  health := state.health.map fun row =>
    ⟨row.seat.value, row.wounds, row.strain, row.recoveryObserved⟩
  mastery := state.mastery.map fun row =>
    ⟨row.seat.value, row.station.tag, row.xp, row.level⟩
  phase := match state.phase with
    | .idle => .idle
    | .claimed officer => .claimed officer.id.value
    | .assigned officer rule => .assigned officer.id.value rule.station.tag rule.task.tag
    | .awaitingDebrief resolved =>
        .awaitingDebrief resolved.shift resolved.officer.id.value resolved.rule.station.tag
          resolved.rule.task.tag resolved.hazardRoll resolved.success
  historyLength := state.history.length
  recentHistory :=
    (state.history.drop (state.history.length - MAX_HISTORY_VIEW)).map HistoryRowWire.ofEntry
  intentCount := state.intents.length
  consumedActionCount := state.consumedActions.card

def healthViewJson (row : HealthViewWire) : String :=
  "{\"seat\":" ++ toString row.seat ++
  ",\"wounds\":" ++ toString row.wounds ++
  ",\"strain\":" ++ toString row.strain ++
  ",\"recovery_observed\":" ++ toString row.recoveryObserved ++ "}"

def masteryViewJson (row : MasteryViewWire) : String :=
  "{\"seat\":" ++ toString row.seat ++
  ",\"station\":" ++ toString row.station ++
  ",\"xp\":" ++ toString row.xp ++
  ",\"level\":" ++ toString row.level ++ "}"

def phaseViewJson : PhaseViewWire → String
  | .idle => "{\"kind\":\"idle\"}"
  | .claimed seat => "{\"kind\":\"claimed\",\"seat\":" ++ toString seat ++ "}"
  | .assigned seat station task =>
      "{\"kind\":\"assigned\",\"seat\":" ++ toString seat ++
      ",\"station\":" ++ toString station ++ ",\"task\":" ++ toString task ++ "}"
  | .awaitingDebrief shift seat station task hazardRoll success =>
      "{\"kind\":\"awaiting_debrief\",\"shift\":" ++ toString shift ++
      ",\"seat\":" ++ toString seat ++ ",\"station\":" ++ toString station ++
      ",\"task\":" ++ toString task ++ ",\"hazard_roll\":" ++ toString hazardRoll ++
      ",\"success\":" ++ boolJson success ++ "}"

def historyRowJson (row : HistoryRowWire) : String :=
  "{\"shift\":" ++ toString row.shift ++
  ",\"seat\":" ++ toString row.seat ++
  ",\"station\":" ++ toString row.station ++
  ",\"task\":" ++ toString row.task ++
  ",\"success\":" ++ boolJson row.success ++
  ",\"hazard_roll\":" ++ toString row.hazardRoll ++
  ",\"risk_threshold\":" ++ toString row.riskThreshold ++
  ",\"evidence_after\":" ++ toString row.evidenceAfter ++
  ",\"terminal_content_id\":" ++ jsonString (Emit.bytes32Hex row.terminalContentId) ++ "}"

def stateViewJson (view : StateViewWire) : String :=
  "{\"sequence\":" ++ toString view.sequence ++
  ",\"shift\":" ++ toString view.shift ++
  ",\"resources\":" ++ resourcesJson view.resources ++
  ",\"evidence\":" ++ toString view.evidence ++
  ",\"health\":" ++ jsonArray (view.health.map healthViewJson) ++
  ",\"mastery\":" ++ jsonArray (view.mastery.map masteryViewJson) ++
  ",\"phase\":" ++ phaseViewJson view.phase ++
  ",\"history_length\":" ++ toString view.historyLength ++
  ",\"recent_history\":" ++ jsonArray (view.recentHistory.map historyRowJson) ++
  ",\"intent_count\":" ++ toString view.intentCount ++
  ",\"consumed_action_count\":" ++ toString view.consumedActionCount ++ "}"

inductive OutputWire where
  | accepted (view : StateViewWire)
  | refused (error : NightWatchCampaign.Error)
deriving DecidableEq

def outputJson : OutputWire → String
  | .accepted view =>
      "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
      ",\"status\":\"accepted\",\"error\":null,\"state\":" ++ stateViewJson view ++ "}"
  | .refused error =>
      "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
      ",\"status\":\"refused\",\"error\":" ++ jsonString (errorName error) ++
      ",\"state\":null}"

/-! ## The entry point -/

/-- Activate the curator's config and rebuild the state the only legitimate way:
`initialState`, then `replay` over the player's own command log.  A config that
fails `activate?`, or a log that the kernel refuses, yields no judgement at all
— not a partial state. -/
def resolve? (input : InputWire) :
    Option (NightWatchCampaign.Config × NightWatchCampaign.State) :=
  match NightWatchCampaign.activate? input.config with
  | none => none
  | some config =>
      match NightWatchCampaign.replay config (NightWatchCampaign.initialState config)
          input.history with
      | .error _ => none
      | .ok before => some (config, before)

def outcome? (input : InputWire) : Option OutputWire :=
  match resolve? input with
  | none => none
  | some (config, before) =>
      match NightWatchCampaign.judge config before input.command with
      | .ok after => some (.accepted (StateViewWire.ofState after))
      | .error error => some (.refused error)

def judgeJson (bytes : String) : Option String :=
  match decodeInput bytes with
  | none => none
  | some input =>
      match outcome? input with
      | none => none
      | some output => some (outputJson output)

/-- The public boundary.  It takes no authority argument, so there is no
sponsor, operator, or override a caller could supply; and it returns the empty
string rather than a partial answer when anything refuses. -/
@[export dregg_poa_night_watch_campaign_judge]
def judgeFFI (bytes : String) : String := (judgeJson bytes).getD ""

/-- ⚑ THE WELD.  An accepted output is the campaign judge's own successor, not a
projection this module chose.  Replace `StateViewWire.ofState after` in
`outcome?` with any doctored view — say a state with one more evidence point —
and this goes red. -/
theorem accepted_output_is_the_campaign_judges_successor
    (input : InputWire) (view : StateViewWire)
    (published : outcome? input = some (.accepted view)) :
    ∃ config before after,
      resolve? input = some (config, before) ∧
      NightWatchCampaign.judge config before input.command = Except.ok after ∧
      view = StateViewWire.ofState after := by
  unfold outcome? at published
  split at published
  · simp at published
  · next config before resolved =>
      split at published
      · next after judged =>
          have step := Option.some.inj published
          injection step with viewEq
          exact ⟨config, before, after, resolved, judged, viewEq.symm⟩
      · next error _ => simp at published

#assert_axioms accepted_output_is_the_campaign_judges_successor

/-! ## Canonicality certificates -/

theorem decodeConfigWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : NightWatchCampaign.RawConfig}
    (accepted : decodeConfigWithLimit limit bytes = some value) :
    configJson value = bytes :=
  canonicalDecode_reencodes parseConfig configJson limit bytes value accepted

theorem decodeCommandWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : NightWatchCampaign.Command}
    (accepted : decodeCommandWithLimit limit bytes = some value) :
    commandJson value = bytes :=
  canonicalDecode_reencodes parseCommand commandJson limit bytes value accepted

theorem decodeInputWithLimit_reencodes {limit : Nat} {bytes : String} {value : InputWire}
    (accepted : decodeInputWithLimit limit bytes = some value) :
    inputJson value = bytes :=
  canonicalDecode_reencodes parseInput inputJson limit bytes value accepted

#assert_axioms decodeConfigWithLimit_reencodes
#assert_axioms decodeCommandWithLimit_reencodes
#assert_axioms decodeInputWithLimit_reencodes

/-! ## A reachable watch — the fixture the teeth bite on

These are deployment-free test vectors, not canon.  Digests are built by hand
(`markDigest`), never by hashing: `Poseidon2BabyBearW16.perm` reduces
exponentially and has no business in a codec. -/

def markDigest (mark : Fin 256) : Digest32 where
  bytes := List.replicate 31 (0 : Fin 256) ++ [mark]
  length_eq := by simp

def fixtureWorld : EventBatch.WorldIdentity where
  federationId := markDigest 1
  contentRoot := markDigest 2
  activationDigest := markDigest 3
  contentSession := markDigest 4
  contentEpoch := ⟨1⟩

def fixtureProgression : ShipLifeProgression.ProgressionIdentity where
  federationId := markDigest 1
  contentSession := markDigest 4
  contentEpoch := ⟨1⟩
  season := ⟨1⟩
  activationDigest := markDigest 3
  owner := markDigest 5

def fixtureStream : EventBatch.StreamId where
  world := fixtureWorld
  aggregate := { namespaceId := markDigest 1, kind := 21, key := markDigest 6 }
  version := ⟨1⟩

def fixtureSeat (index : Nat) (mark : Fin 256) (role : CrewRole) : Seat where
  id := ⟨index⟩
  playerKey := markDigest mark
  credential := ⟨index⟩
  role := role
  initialCounter := 0

def fixtureRoster : List Seat :=
  [ fixtureSeat 0 16 .pathfinder
  , fixtureSeat 1 17 .engineer
  , fixtureSeat 2 18 .containment
  , fixtureSeat 3 19 .quartermaster ]

def fixtureRule : NightWatchCampaign.TaskRule where
  station := .bridge
  task := .plotDrift
  role := .pathfinder
  riskThreshold := 40
  successContribution := ⟨2, 0, 1, 0, 3⟩
  failureContribution := NightWatchCampaign.ContributionDelta.zero
  successEffects := { gainSupplies := 1 }
  failureEffects := { spendMorale := 1 }
  successHealth := {}
  failureHealth := { strainAdded := 1 }
  successEvidence := 2
  failureEvidence := 0
  localService := ⟨0, by decide⟩
  betaDiscovery := none
  discoveryEvidenceRequired := 0
  taskContentId := markDigest 32
  successContentId := markDigest 33
  failureContentId := markDigest 34

def fixtureRaw : NightWatchCampaign.RawConfig where
  schemaVersion := 1
  progression := fixtureProgression
  logStream := fixtureStream
  roster := fixtureRoster
  rules := [fixtureRule]
  hazardCycle := [50]
  initialResources := ⟨10, 10, 10, 10⟩
  maxShifts := 4

/-- Well-formed on the wire, but every seat shares one player key, so `Nodup`
fails and `activate?` refuses. -/
def fixtureForgedRoster : NightWatchCampaign.RawConfig :=
  { fixtureRaw with
    roster := fixtureRoster.map fun seat => { seat with playerKey := markDigest 16 } }

def fixtureActor : Digest32 := markDigest 16

def fixtureClaim (nullifier : Digest32) : NightWatchCampaign.Command where
  sequence := 0
  nullifier := nullifier
  action := .claimOfficer fixtureActor ⟨0⟩

def fixtureConfig? : Option NightWatchCampaign.Config :=
  NightWatchCampaign.activate? fixtureRaw

def fixtureAfter? (nullifier : Digest32) : Option NightWatchCampaign.State := do
  let config ← fixtureConfig?
  (NightWatchCampaign.judge config (NightWatchCampaign.initialState config)
    (fixtureClaim nullifier)).toOption

def fixtureNullifierA : Digest32 := markDigest 200
def fixtureNullifierB : Digest32 := markDigest 201

theorem fixture_claim_with_nullifier_A_reaches_a_state :
    (fixtureAfter? fixtureNullifierA).isSome = true := by
  native_decide

theorem fixture_claim_with_nullifier_B_reaches_a_state :
    (fixtureAfter? fixtureNullifierB).isSome = true := by
  native_decide

def fixtureStateA : NightWatchCampaign.State :=
  (fixtureAfter? fixtureNullifierA).get fixture_claim_with_nullifier_A_reaches_a_state

def fixtureStateB : NightWatchCampaign.State :=
  (fixtureAfter? fixtureNullifierB).get fixture_claim_with_nullifier_B_reaches_a_state

def fixtureInput : InputWire where
  config := fixtureRaw
  history := []
  command := fixtureClaim fixtureNullifierA

def fixtureWrongSequenceInput : InputWire where
  config := fixtureRaw
  history := []
  command := { sequence := 7, nullifier := fixtureNullifierB, action := .resolve }

def fixtureReplayInput : InputWire where
  config := fixtureRaw
  history := [fixtureClaim fixtureNullifierA]
  command :=
    { sequence := 1, nullifier := fixtureNullifierA, action := .chooseTask .bridge .plotDrift }

#assert_compiled fixture_claim_with_nullifier_A_reaches_a_state
#assert_compiled fixture_claim_with_nullifier_B_reaches_a_state

/-! ## The teeth

Every one of these bites on the ACTUAL exported path (`decodeConfig`,
`decodeCommand`, `judgeJson`), not on a scratch model of it. -/

theorem fixture_config_round_trips_through_the_wire :
    decodeConfig (configJson fixtureRaw) = some fixtureRaw := by
  native_decide

theorem fixture_command_round_trips_through_the_wire :
    decodeCommand (commandJson (fixtureClaim fixtureNullifierA)) =
      some (fixtureClaim fixtureNullifierA) := by
  native_decide

theorem fixture_input_round_trips_through_the_wire :
    decodeInput (inputJson fixtureInput) = some fixtureInput := by
  native_decide

#assert_compiled fixture_config_round_trips_through_the_wire
#assert_compiled fixture_command_round_trips_through_the_wire
#assert_compiled fixture_input_round_trips_through_the_wire

def unknownActionKindBytes : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"sequence\":0,\"nullifier\":" ++
  jsonString (Emit.bytes32Hex (markDigest 200)) ++ ",\"action\":{\"kind\":\"seize_ship\"}}"

def unknownFieldBytes : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"sequence\":0,\"nullifier\":" ++
  jsonString (Emit.bytes32Hex (markDigest 200)) ++
  ",\"action\":{\"kind\":\"resolve\"},\"score\":9000}"

def reorderedKeyBytes : String :=
  "{\"sequence\":0,\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"nullifier\":" ++
  jsonString (Emit.bytes32Hex (markDigest 200)) ++ ",\"action\":{\"kind\":\"resolve\"}}"

def uppercaseDigestBytes : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"sequence\":0,\"nullifier\":" ++
  jsonString (String.ofList (List.replicate 62 '0') ++ "C8") ++
  ",\"action\":{\"kind\":\"resolve\"}}"

theorem command_with_unknown_action_kind_refuses :
    decodeCommand unknownActionKindBytes = none := by
  native_decide

theorem command_with_unknown_field_refuses : decodeCommand unknownFieldBytes = none := by
  native_decide

theorem command_with_reordered_keys_refuses : decodeCommand reorderedKeyBytes = none := by
  native_decide

theorem command_with_uppercase_digest_refuses : decodeCommand uppercaseDigestBytes = none := by
  native_decide

#assert_compiled command_with_unknown_action_kind_refuses
#assert_compiled command_with_unknown_field_refuses
#assert_compiled command_with_reordered_keys_refuses
#assert_compiled command_with_uppercase_digest_refuses

def oversizedRulesBytes : String :=
  configJson { fixtureRaw with rules := List.replicate (NightWatchCampaign.MAX_RULES + 1) fixtureRule }

def oversizedHazardBytes : String :=
  configJson { fixtureRaw with
    hazardCycle := List.replicate (NightWatchCampaign.MAX_HAZARD_CYCLE + 1) 1 }

def hazardAtHundredBytes : String :=
  configJson { fixtureRaw with hazardCycle := [100] }

def resourceAboveBoundBytes : String :=
  configJson { fixtureRaw with
    initialResources := ⟨NightWatchCampaign.MAX_RESOURCE + 1, 10, 10, 10⟩ }

theorem oversized_rule_list_refuses : decodeConfig oversizedRulesBytes = none := by
  native_decide

theorem oversized_hazard_cycle_refuses : decodeConfig oversizedHazardBytes = none := by
  native_decide

theorem hazard_roll_at_the_hundred_bound_refuses :
    decodeConfig hazardAtHundredBytes = none := by
  native_decide

theorem initial_resource_above_the_bound_refuses :
    decodeConfig resourceAboveBoundBytes = none := by
  native_decide

#assert_compiled oversized_rule_list_refuses
#assert_compiled oversized_hazard_cycle_refuses
#assert_compiled hazard_roll_at_the_hundred_bound_refuses
#assert_compiled initial_resource_above_the_bound_refuses

/-! ## End to end, over the exported bytes -/

theorem judge_publishes_the_accepted_state_view :
    judgeJson (inputJson fixtureInput) =
      some (outputJson (.accepted (StateViewWire.ofState fixtureStateA))) := by
  native_decide

theorem judge_publishes_the_wrong_sequence_refusal :
    judgeJson (inputJson fixtureWrongSequenceInput) =
      some (outputJson (.refused .wrongSequence)) := by
  native_decide

/-- The history really is replayed: the nullifier spent by the logged command is
already in `consumedActions` when the next command arrives. -/
theorem judge_replays_the_history_and_refuses_a_spent_nullifier :
    judgeJson (inputJson fixtureReplayInput) =
      some (outputJson (.refused .replayedAction)) := by
  native_decide

/-- A config that decodes perfectly can still fail `activate?`, and then there is
no judgement at all — the wire never manufactures a `Config`. -/
theorem forged_roster_config_decodes_but_yields_no_judgement :
    decodeConfig (configJson fixtureForgedRoster) = some fixtureForgedRoster ∧
      judgeJson (inputJson { fixtureInput with config := fixtureForgedRoster }) = none := by
  native_decide

theorem judgeFFI_returns_empty_on_undecodable_bytes : judgeFFI "{}" = "" := by
  native_decide

#assert_compiled judge_publishes_the_accepted_state_view
#assert_compiled judge_publishes_the_wrong_sequence_refusal
#assert_compiled judge_replays_the_history_and_refuses_a_spent_nullifier
#assert_compiled forged_roster_config_decodes_but_yields_no_judgement
#assert_compiled judgeFFI_returns_empty_on_undecodable_bytes

/-! ## ⚑ The view carries no authority

Two states reached by the same command with different nullifiers are DISTINCT —
their `consumedActions` differ — and publish the SAME view.  So `ofState` is not
injective, and the corollary is unconditional: no decoder from the published
view back to a `State` can be sound.  This is why there is no `parseStateView`,
and it is refutable — put the nullifier set in the view and the first conjunct
stays true while the second goes red. -/

theorem state_view_erases_the_consumed_nullifier_ledger :
    fixtureStateA ≠ fixtureStateB ∧
      StateViewWire.ofState fixtureStateA = StateViewWire.ofState fixtureStateB := by
  native_decide

theorem no_state_view_decoder_can_be_sound
    (decode : StateViewWire → Option NightWatchCampaign.State)
    (sound : ∀ state : NightWatchCampaign.State,
      decode (StateViewWire.ofState state) = some state) : False := by
  obtain ⟨distinct, sameView⟩ := state_view_erases_the_consumed_nullifier_ledger
  refine distinct (Option.some.inj ?_)
  rw [← sound fixtureStateA, ← sound fixtureStateB, sameView]

#assert_compiled state_view_erases_the_consumed_nullifier_ledger
#assert_compiled no_state_view_decoder_can_be_sound

end Dregg2.Games.PathOfAngels.NightWatchCampaignWire
