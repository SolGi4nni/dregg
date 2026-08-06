/-
# NightWatchCampaignAdmission — where a night-watch config STOPS being the caller's

`NightWatchCampaign.activate?` checks that a config is STRUCTURALLY valid.  It has
never checked that it is AUTHENTIC, and it still does not.  Until this module there
was no producer that did, so `dregg_poa_night_watch_campaign_judge` judged whatever
config arrived in its request body: a caller supplying all-zero `riskThreshold`s and
maximal `successContribution`s got a judged, internally consistent, entirely
fraudulent watch — and every theorem in the wire still held, because each one is
conditional on the config that was supplied.

This module is that producer.  `authorizeCampaignConfigForWorld?` is
`ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld?` for this organ: it takes a
world identity that persistence has already audited under its signed activation
lineage, and a validated activated manifest whose SHA-256 root IS that world's
`contentRoot`, locates `poa.night-watch-campaign.config.v1` by exact name, and admits
its bytes only if they decode canonically to a config which activates and whose
federation, content session and content epoch are the world's.  Every one of those is
a proof field on the witness, so the witness cannot be assembled by assertion:
`WorldScopedCampaignConfigMember.mk` is private and this is the only producer.

## Why the config CODEC lives here and not in the wire

Because a decoder whose output nobody authenticates is the hole above.  Keeping
`configJson`/`decodeConfig` in the same module as the witness means the bytes the
manifest carries and the bytes the judge decodes are the same function, and the wire
imports this module rather than the other way round — it has no way to reach a config
except through the witness.  The generic canonical-JSON plumbing lives here too
(`canonicalDecode`, `exactKeys`, the bounded parsers), shared with
`NightWatchCampaignWire` rather than mirrored into it: two decoders that agree today
are two decoders that disagree later.

## What this does NOT buy

Signature verification is `WorldActivation`'s, at the persistence seam, exactly as it
is for Galley — this module proves membership in a world it is HANDED, and a caller
that hands it a world nobody audited gets a witness about nothing.  That is the same
boundary `ActivatedContent`'s docblock draws, not a new one.

⚑ **The export is still MOUNTED NOWHERE.**  There is no route, no C shim, no
`build.rs` gate and no Rust binding for `dregg_poa_night_watch_campaign_judge`, and
none of that is in this change.  What IS now true is that mounting it no longer
requires a host to be trusted with the config: it requires an audited world and a
manifest.  ⚠ And nothing yet EMITS a `poa.night-watch-campaign.config.v1` component —
`Emit` has no renderer for one — so today the only manifests carrying one are the
fixtures below.

## Flag day

`RawConfig` lost `hazardCycle` and gained `mission_id`, `slot` and `slot_commitment`;
`risk_threshold` is bounded by `HAZARD_FACES = 256`, not 100.  Every
`POA-NIGHT-WATCH-CAMPAIGN-CONFIG-1` document re-emits, every manifest embedding one
re-hashes, and the world whose `contentRoot` is that manifest root is re-activated.
Old bytes REFUSE: `exactKeys` is exact and `hazard_cycle` is not a key any more.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.ActivatedContent
import Dregg2.Games.PathOfAngels.NightWatchCampaign
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## Wire constants -/

abbrev CONFIG_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-CONFIG-1"

/-- The canonical public name of the config component inside an activated manifest. -/
abbrev CONFIG_COMPONENT : String := "poa.night-watch-campaign.config.v1"

abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1
abbrev WIRE_BYTE_LIMIT : Nat := 4 * 1024 * 1024

/-! ## Canonical JSON plumbing — shared with `NightWatchCampaignWire`

Public deliberately: the wire imports these rather than keeping a second copy.  None
of it confers authority; it is parsing. -/

def jsonString (value : String) : String := String.quote value

def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

def optionJson {T : Type} (encode : T → String) : Option T → String
  | none => "null"
  | some value => encode value

def boolJson (value : Bool) : String := if value then "true" else "false"

def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

def boundedNat (limit value : Nat) : Except String Nat :=
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

def objectNat (j : Json) (key : String) (limit : Nat := WIRE_U64_MAX) :
    Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

def parseNat (j : Json) (limit : Nat := WIRE_U64_MAX) : Except String Nat := do
  boundedNat limit (← fromJson? j)

def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

/-- Written as an explicit `match` rather than a `do`-block so the refusal is a
one-step `split`, not a monad-unfolding argument. -/
def parseBoundedList {T : Type} (j : Json) (limit : Nat)
    (parse : Json → Except String T) : Except String (List T) :=
  match j.getArr? with
  | .error message => .error message
  | .ok values =>
      if values.size > limit then .error "array exceeds wire bound"
      else values.toList.mapM parse

def parseOption {T : Type} (j : Json)
    (parse : Json → Except String T) : Except String (Option T) :=
  match j with
  | .null => pure none
  | value => some <$> parse value

/-- Parse, then re-encode and demand byte identity.  One value, one spelling. -/
def canonicalDecode {T : Type} (parse : Json → Except String T)
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
numbering rather than a second one that can drift from it.  Roles get a code here
because `CrewRole` carries none. -/

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

/-! ## The curator's configuration — decode AND encode

Decoding lands directly in `NightWatchCampaign.RawConfig`; there is no mirror
structure, so there is nothing that can agree with the kernel today and disagree with
it later.  Admission to `Config` is still `activate?`'s alone, and admission to a
WORLD is the witness constructor at the bottom of this file. -/

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

/-- ⚠ No `hazard_cycle`.  What a config publishes about the hazard is
`slot_commitment`, which tells a reader which slot the run belongs to and NOTHING
about any roll.  `mission_id`, `slot` and `slot_commitment` are the three fields the
kernel's `ActivationBinds` pins a derivation to. -/
def configJson (raw : NightWatchCampaign.RawConfig) : String :=
  "{\"format\":" ++ jsonString CONFIG_FORMAT ++
  ",\"schema_version\":" ++ toString raw.schemaVersion ++
  ",\"mission_id\":" ++ toString raw.missionId.value ++
  ",\"progression\":" ++ progressionJson raw.progression ++
  ",\"log_stream\":" ++ streamJson raw.logStream ++
  ",\"slot\":" ++ toString raw.slot.value ++
  ",\"slot_commitment\":" ++ jsonString (Emit.bytes32Hex raw.slotCommitment) ++
  ",\"roster\":" ++ jsonArray (raw.roster.map seatJson) ++
  ",\"rules\":" ++ jsonArray (raw.rules.map taskRuleJson) ++
  ",\"initial_resources\":" ++ resourcesJson raw.initialResources ++
  ",\"max_shifts\":" ++ toString raw.maxShifts ++ "}"

/-- Public: the input wire parses the ACTIVATION world with this same parser, so the
two world spellings cannot drift apart. -/
def parseWorldIdentity (j : Json) : Except String EventBatch.WorldIdentity := do
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
      riskThreshold := ← objectNat j "risk_threshold" NightWatchCampaign.HAZARD_FACES
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
  exactKeys j ["format", "schema_version", "mission_id", "progression", "log_stream",
    "slot", "slot_commitment", "roster", "rules", "initial_resources", "max_shifts"]
  if (← j.getObjValAs? String "format") != CONFIG_FORMAT then throw "wrong config format"
  pure {
    schemaVersion := ← objectNat j "schema_version"
    missionId := ⟨← objectNat j "mission_id"⟩
    progression := ← parseProgression (← j.getObjVal? "progression")
    logStream := ← parseStream (← j.getObjVal? "log_stream")
    slot := ⟨← objectNat j "slot"⟩
    slotCommitment := ← objectDigest j "slot_commitment"
    roster := ← parseBoundedList (← j.getObjVal? "roster") CrewFieldMission.CREW_SIZE parseSeat
    rules := ← parseBoundedList (← j.getObjVal? "rules") NightWatchCampaign.MAX_RULES parseTaskRule
    initialResources := ← parseResources (← j.getObjVal? "initial_resources")
    maxShifts := ← objectNat j "max_shifts" NightWatchCampaign.MAX_SHIFTS
  }

def decodeConfigWithLimit (limit : Nat) (bytes : String) :
    Option NightWatchCampaign.RawConfig :=
  canonicalDecode parseConfig configJson limit bytes

def decodeConfig (bytes : String) : Option NightWatchCampaign.RawConfig :=
  decodeConfigWithLimit WIRE_BYTE_LIMIT bytes

theorem decodeConfigWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : NightWatchCampaign.RawConfig}
    (accepted : decodeConfigWithLimit limit bytes = some value) :
    configJson value = bytes :=
  canonicalDecode_reencodes parseConfig configJson limit bytes value accepted

theorem decodeConfig_reencodes {bytes : String} {value : NightWatchCampaign.RawConfig}
    (accepted : decodeConfig bytes = some value) : configJson value = bytes :=
  decodeConfigWithLimit_reencodes accepted

#assert_axioms decodeConfigWithLimit_reencodes
#assert_axioms decodeConfig_reencodes

/-! ## The world-scoped authenticated config

Modelled on `ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld?`
(`ActivatedContent.lean:321`), with the component lookup shared rather than mirrored. -/

/-- A config that is a member of an activated world, with every step of that claim as
a proof field.  `mk` is private; `authorizeCampaignConfigForWorld?` is the only
producer, and it traverses the manifest rather than believing a caller. -/
structure WorldScopedCampaignConfigMember where
  private mk ::
  world : WorldActivation.WorldIdentity
  manifest : ActivatedContent.ValidatedManifest
  component : ActivatedContent.Component
  raw : NightWatchCampaign.RawConfig
  config : NightWatchCampaign.Config
  root_and_scope_exact : manifest.raw.matchesWorldB world = true
  located : ActivatedContent.componentByName? manifest.raw.components CONFIG_COMPONENT
    = some component
  config_bytes_exact : component.bytesUtf8 = configJson raw
  activates : NightWatchCampaign.activate? raw = some config
  federation_exact : raw.progression.federationId = world.federationId
  session_exact : raw.progression.contentSession = world.contentSession
  epoch_exact : raw.progression.contentEpoch = world.contentEpoch

def authorizeCampaignConfigForWorld? (world : WorldActivation.WorldIdentity)
    (manifest : ActivatedContent.ValidatedManifest) :
    Option WorldScopedCampaignConfigMember :=
  if worldExact : manifest.raw.matchesWorldB world = true then
    match located : ActivatedContent.componentByName? manifest.raw.components CONFIG_COMPONENT with
    | none => none
    | some component =>
        match decoded : decodeConfig component.bytesUtf8 with
        | none => none
        | some raw =>
            match activated : NightWatchCampaign.activate? raw with
            | none => none
            | some config =>
                if federation : raw.progression.federationId = world.federationId then
                  if session : raw.progression.contentSession = world.contentSession then
                    if epoch : raw.progression.contentEpoch = world.contentEpoch then
                      some ⟨world, manifest, component, raw, config, worldExact, located,
                        (decodeConfig_reencodes decoded).symm, activated,
                        federation, session, epoch⟩
                    else none
                  else none
                else none
  else none

/-- `raw` and `config` are not two shapes that agree today: activation reports the
config it was given, so the authenticated BYTES and the judged `Config` are the same
document. -/
theorem WorldScopedCampaignConfigMember.the_judged_config_is_the_authenticated_document
    (member : WorldScopedCampaignConfigMember) : member.config.raw = member.raw :=
  NightWatchCampaign.activate_preserves_the_raw_config member.activates

/-- The bytes the manifest carries ARE this config's canonical encoding — so the
digest the manifest root commits to is a digest of exactly these rules. -/
theorem WorldScopedCampaignConfigMember.exact_config_bytes
    (member : WorldScopedCampaignConfigMember) :
    member.component.bytesUtf8 = configJson member.config.raw := by
  rw [member.the_judged_config_is_the_authenticated_document]
  exact member.config_bytes_exact

/-- The manifest this config came out of is the world's content root, not merely a
manifest that happens to name the same federation. -/
theorem WorldScopedCampaignConfigMember.exact_content_root
    (member : WorldScopedCampaignConfigMember) :
    ActivatedContent.manifestRoot? member.manifest.raw = some member.world.contentRoot := by
  have exact := member.root_and_scope_exact
  unfold ActivatedContent.Manifest.matchesWorldB at exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨_, root⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  exact of_decide_eq_true root

#assert_axioms WorldScopedCampaignConfigMember.the_judged_config_is_the_authenticated_document
#assert_axioms WorldScopedCampaignConfigMember.exact_config_bytes
#assert_axioms WorldScopedCampaignConfigMember.exact_content_root

/-! ## The fixture the teeth bite on — shared with `NightWatchCampaignWire`

Deployment-free test vectors, not canon.  Digests are built by hand (`markDigest`)
except the two that CANNOT be: `slotCommitment` is `HiddenInstance.commit` of the
fixture secret and the manifest root is a real SHA-256 of the manifest bytes.  Every
theorem touching either is `native_decide` and pinned `#assert_compiled`, because a
kernel `decide` through the Poseidon2 sponge is a 47 GB bomb. -/

def markDigest (mark : Fin 256) : Digest32 where
  bytes := List.replicate 31 (0 : Fin 256) ++ [mark]
  length_eq := by simp

/-- ⚠ `contentRoot` here is the LOG STREAM's world, not the activated world: the
activated world's root is the SHA-256 of the manifest that embeds this very config, so
putting it inside the config would be a cycle.  `configValidB` does not constrain
`logStream.world` at all — named in the wire docblock, unchanged by this file. -/
def fixtureStreamWorld : EventBatch.WorldIdentity where
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
  world := fixtureStreamWorld
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

/-- Threshold `102` is 60% odds in 256ths — the same rule the fixture always had, at
the same difficulty, re-expressed at the width the draw actually uses. -/
def fixtureRule : NightWatchCampaign.TaskRule where
  station := .bridge
  task := .plotDrift
  role := .pathfinder
  riskThreshold := 102
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

/-- The curator's slot secret.  It is here because a FIXTURE needs one; in a
deployment it never leaves node state and no emitter renders it. -/
def fixtureSecret : HiddenInstance.SlotSecret := ⟨markDigest 90⟩

def fixtureSlot : EpochId := ⟨7⟩

def fixtureMissionId : MissionId := ⟨4242⟩

/-- The published commitment: a function of the secret and the slot alone. -/
def fixtureCommitment : Digest32 := HiddenInstance.commit fixtureSecret fixtureSlot

def fixtureRaw : NightWatchCampaign.RawConfig where
  schemaVersion := 1
  missionId := fixtureMissionId
  progression := fixtureProgression
  logStream := fixtureStream
  slot := fixtureSlot
  slotCommitment := fixtureCommitment
  roster := fixtureRoster
  rules := [fixtureRule]
  initialResources := ⟨10, 10, 10, 10⟩
  maxShifts := 4

/-- Well-formed on the wire, but every seat shares one player key, so `Nodup` fails
and `activate?` refuses. -/
def fixtureForgedRoster : NightWatchCampaign.RawConfig :=
  { fixtureRaw with
    roster := fixtureRoster.map fun seat => { seat with playerKey := markDigest 16 } }

def fixtureComponent : ActivatedContent.Component where
  name := CONFIG_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (configJson fixtureRaw)).getD (markDigest 0)
  bytesUtf8 := configJson fixtureRaw

def fixtureManifest : ActivatedContent.Manifest where
  scope := {
    federationId := markDigest 1
    contentSession := markDigest 4
    contentEpoch := 1
  }
  legacyWholePackRoot := none
  components := [fixtureComponent]

def fixtureManifestBytes : String := fixtureManifest.toJson

def fixtureManifestRoot : Digest32 :=
  (ActivatedContent.manifestRoot? fixtureManifest).getD (markDigest 0)

/-- The activated world: its `contentRoot` IS the manifest root, which is what makes
the membership claim mean anything. -/
def fixtureWorld : WorldActivation.WorldIdentity where
  federationId := markDigest 1
  contentRoot := fixtureManifestRoot
  activationDigest := markDigest 3
  contentSession := markDigest 4
  contentEpoch := ⟨1⟩

/-! ### The node-side draw

What the NODE assembles for a run: the secret it holds, the commitment it published,
the seated officer the run belongs to, the context the config determines, and the seed
it derived through `dregg_poa_signal_slot_derive`.  `admitActivation?` re-derives the
last two and refuses on disagreement — that is the check, and it is a check only
because these values were derived independently of the kernel. -/

def fixtureMissionContext : HiddenInstance.MissionContext where
  missionId := fixtureMissionId
  epoch := ⟨1⟩
  federationId := markDigest 1
  contentSession := markDigest 4

/-- The pathfinder's seat key: the run's owner need not be the officer on watch. -/
def fixtureRunOwner : Digest32 := markDigest 16

def fixtureRunSeed : Digest32 :=
  HiddenInstance.runSeedFor
    { secret := fixtureSecret, slot := fixtureSlot, playerKey := fixtureRunOwner }
    fixtureMissionContext

def fixtureDraw : NightWatchCampaign.RawActivation where
  slot := fixtureSlot
  slotSecret := fixtureSecret
  slotCommitment := fixtureCommitment
  playerKey := fixtureRunOwner
  mission := fixtureMissionContext
  runSeed := fixtureRunSeed

def fixtureValidatedManifest? : Option ActivatedContent.ValidatedManifest :=
  ActivatedContent.decodeManifest fixtureManifestBytes

def fixtureMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← fixtureValidatedManifest?
  authorizeCampaignConfigForWorld? fixtureWorld manifest

/-! ## Teeth -/

theorem fixture_config_round_trips_through_the_wire :
    decodeConfig (configJson fixtureRaw) = some fixtureRaw := by
  native_decide

theorem fixture_manifest_decodes_canonically :
    fixtureValidatedManifest?.isSome = true := by
  native_decide

/-- ⚑ The one that closes the hole: a config the CURATOR published, located inside the
active world's own content root, is admitted. -/
theorem the_activated_world_admits_its_own_campaign_config :
    fixtureMember?.isSome = true := by
  native_decide

/-- A config with a different rule table re-hashes the manifest and therefore no
longer matches the activated world's content root: a player cannot swap the rules and
keep the world.  (The substituted config is internally valid — first conjunct — so the
refusal is the ROOT, not a malformed document.) -/
def forgedRaw : NightWatchCampaign.RawConfig :=
  { fixtureRaw with rules := [{ fixtureRule with riskThreshold := 0 }] }

def forgedComponent : ActivatedContent.Component where
  name := CONFIG_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (configJson forgedRaw)).getD (markDigest 0)
  bytesUtf8 := configJson forgedRaw

def forgedManifest : ActivatedContent.Manifest :=
  { fixtureManifest with components := [forgedComponent] }

def forgedMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest forgedManifest.toJson
  authorizeCampaignConfigForWorld? fixtureWorld manifest

theorem a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it :
    (NightWatchCampaign.activate? forgedRaw).isSome = true ∧
    (ActivatedContent.decodeManifest forgedManifest.toJson).isSome = true ∧
    forgedManifest.matchesWorldB fixtureWorld = false ∧
    forgedMember? = none := by
  native_decide

/-- The component name is exact.  ⚠ The world here is the one whose `contentRoot` IS
the misnamed manifest's root, so `matchesWorldB` PASSES — first conjunct — and the
refusal is isolated to the name lookup rather than riding on a changed root. -/
def misnamedManifest : ActivatedContent.Manifest :=
  { fixtureManifest with
    components := [{ fixtureComponent with name := "poa.night-watch-campaign.config.v2" }] }

def misnamedWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with
    contentRoot := (ActivatedContent.manifestRoot? misnamedManifest).getD (markDigest 0) }

def misnamedMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest misnamedManifest.toJson
  authorizeCampaignConfigForWorld? misnamedWorld manifest

theorem a_component_under_another_name_is_not_this_organs_config :
    misnamedManifest.matchesWorldB misnamedWorld = true ∧
    ActivatedContent.componentByName? misnamedManifest.components CONFIG_COMPONENT = none ∧
    misnamedMember? = none := by
  native_decide

/-- A world that is structurally fine and names a different content session cannot
consume this manifest, even though the manifest root is unchanged. -/
def crossSessionWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with contentSession := markDigest 77 }

def crossSessionMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← fixtureValidatedManifest?
  authorizeCampaignConfigForWorld? crossSessionWorld manifest

theorem a_config_cannot_be_carried_into_another_content_session :
    crossSessionMember? = none := by
  native_decide

/-- A config that decodes perfectly can still fail `activate?`, and then there is no
member — the witness never manufactures a `Config`. -/
def forgedRosterComponent : ActivatedContent.Component where
  name := CONFIG_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (configJson fixtureForgedRoster)).getD (markDigest 0)
  bytesUtf8 := configJson fixtureForgedRoster

def forgedRosterManifest : ActivatedContent.Manifest :=
  { fixtureManifest with components := [forgedRosterComponent] }

def forgedRosterWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with
    contentRoot := (ActivatedContent.manifestRoot? forgedRosterManifest).getD (markDigest 0) }

def forgedRosterMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest forgedRosterManifest.toJson
  authorizeCampaignConfigForWorld? forgedRosterWorld manifest

theorem an_invalid_config_in_an_exactly_matching_world_still_yields_no_member :
    (ActivatedContent.decodeManifest forgedRosterManifest.toJson).isSome = true ∧
    forgedRosterManifest.matchesWorldB forgedRosterWorld = true ∧
    NightWatchCampaign.activate? fixtureForgedRoster = none ∧
    forgedRosterMember? = none := by
  native_decide

/-! ## Config-shape refusals, on the real decoder -/

def oversizedRulesBytes : String :=
  configJson { fixtureRaw with
    rules := List.replicate (NightWatchCampaign.MAX_RULES + 1) fixtureRule }

def riskAboveTheFaceCountBytes : String :=
  configJson { fixtureRaw with
    rules := [{ fixtureRule with riskThreshold := NightWatchCampaign.HAZARD_FACES + 1 }] }

def resourceAboveBoundBytes : String :=
  configJson { fixtureRaw with
    initialResources := ⟨NightWatchCampaign.MAX_RESOURCE + 1, 10, 10, 10⟩ }

/-- The flag day, made findable: an otherwise byte-canonical current document with the
RETIRED `hazard_cycle` spliced back in refuses, rather than being read with the field
ignored.  `exactKeys` is exact in both directions. -/
def legacyHazardCycleBytes : String :=
  ((configJson fixtureRaw).dropEnd 1).toString ++ ",\"hazard_cycle\":[70,10,55]}"

theorem oversized_rule_list_refuses : decodeConfig oversizedRulesBytes = none := by
  native_decide

theorem a_risk_threshold_above_the_face_count_refuses :
    decodeConfig riskAboveTheFaceCountBytes = none := by
  native_decide

theorem initial_resource_above_the_bound_refuses :
    decodeConfig resourceAboveBoundBytes = none := by
  native_decide

theorem a_config_carrying_the_retired_hazard_cycle_refuses :
    decodeConfig legacyHazardCycleBytes = none := by
  native_decide

#assert_compiled fixture_config_round_trips_through_the_wire
#assert_compiled fixture_manifest_decodes_canonically
#assert_compiled the_activated_world_admits_its_own_campaign_config
#assert_compiled a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it
#assert_compiled a_component_under_another_name_is_not_this_organs_config
#assert_compiled a_config_cannot_be_carried_into_another_content_session
#assert_compiled an_invalid_config_in_an_exactly_matching_world_still_yields_no_member
#assert_compiled oversized_rule_list_refuses
#assert_compiled a_risk_threshold_above_the_face_count_refuses
#assert_compiled initial_resource_above_the_bound_refuses
#assert_compiled a_config_carrying_the_retired_hazard_cycle_refuses

end Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
