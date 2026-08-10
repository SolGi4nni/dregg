/-
# Path of Angels — strict Signal authority-genesis wire

This is the byte boundary for installing the first durable `PoaSignalHeadV1`.
The input does not claim to verify a deployment manifest or an Ed25519 content
signature.  Those checks happen outside Lean, against the exact genesis,
manifest, detached envelope, and independently pinned curator key.  This wire
then makes the resulting identities inseparable from the Lean-emitted Signal
configuration and empty Canon genesis.

In particular, `activationDigest` is the digest of the already verified
detached content envelope.  It is outside the POAG1 content-root preimage, which
avoids a content-root/activation circularity.  The external verifier must still
establish all of the following before invoking this boundary:

* `deploymentId`, `deploymentDigest`, `federationId`, `genesisSha256`,
  `manifestSha256`, and `policySha256` came from one verified production
  `poa-devnet.json` plus its exact genesis bytes;
* `manifestSha256`, `contentEpoch`, `activationCounter`, and `curatorKey` came
  from one signature-valid detached content envelope under an external key pin;
* `activationDigest` was recomputed from that exact envelope; and
* `contentRoot`, `sourceDigest`, and `signalContentDigest` came from the exact
  manifest-authenticated POAG1 bundle named by the envelope.

The accepted JSON is canonical byte-for-byte.  Unknown fields, reordered keys,
alternate digest spellings, duplicate/sorted-set aliases, whitespace, and
trailing bytes refuse.  Output carries the exact config/Canon JSON strings the
Rust ceremony must persist; a host must not reconstruct either semantic object.
-/
import Lean.Data.Json
import Mathlib.Data.Finset.Sort
import Dregg2.Bridge.MinaStateHashDerive
import Dregg2.Circuit.KeyLanes9
import Dregg2.Games.PathOfAngels.NetworkJudgeWire
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NetworkGenesisWire

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-SIGNAL-GENESIS-IN-2"
abbrev OUTPUT_FORMAT : String := "POA-SIGNAL-GENESIS-OUT-2"
abbrev DEPLOYMENT_SCHEMA : String := "dregg-poa-devnet-manifest-v1"
abbrev DEPLOYMENT_DOMAIN : String := "pathofangels.network/federation/v1"
abbrev CONTENT_SIGNATURE_SCHEMA : String := "POA-CONTENT-EPOCH-SIGNATURE-V1"
abbrev GENESIS_BYTE_LIMIT : Nat := 16 * 1024 * 1024

private def jsonString (s : String) : String := String.quote s
private def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def boundedNat (limit value : Nat) : Except String Nat :=
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def objectNat (j : Json) (key : String) (limit : Nat := WIRE_NAT_LIMIT) :
    Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def strictNatListB (limit : Nat) (xs : List Nat) : Bool :=
  xs.length ≤ limit && xs.all (· ≤ WIRE_ID_LIMIT) && decide (xs.Pairwise (· < ·))

private def parseNatList (j : Json) (limit : Nat) : Except String (List Nat) := do
  let values := (← j.getArr?).toList
  if values.length > limit then throw "list exceeds wire bound"
  let xs ← values.mapM (fun value => value.getNat?)
  if strictNatListB limit xs then pure xs else throw "list is not canonical"

/-! ## Exact ceremony input -/

structure DeploymentIdentityWire where
  schema : String
  deploymentDomain : String
  deploymentId : Digest32
  deploymentDigest : Digest32
  federationId : Digest32
  genesisSha256 : Digest32
  manifestSha256 : Digest32
  policySha256 : Digest32
deriving DecidableEq

structure ContentIdentityWire where
  signatureSchema : String
  manifestSha256 : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  sourceDigest : Digest32
  signalContentDigest : Digest32
  curatorKey : Digest32
  contentEpoch : Nat
  activationCounter : Nat
deriving DecidableEq

/-- The complete purported zero-transition state.  Carrying the empty
populations explicitly makes accidental restore/import state observable and
lets the syntax boundary reject duplicate replay/counter rows before the
semantic zero-state check. -/
structure InitialStateWire where
  world : WorldStateWire
  known : List ArtifactRefWire
  alpha : List ArtifactRefWire
  superseded : List ArtifactRefWire
  consumedRuns : List ReceiptKeyWire
  playerCounters : List PlayerCounterRowWire
  canonRevision : Nat
  curatorCounter : Nat
  transitionCount : Nat
  lastTransitionDigest : Digest32
deriving DecidableEq

structure GenesisInputWire where
  deployment : DeploymentIdentityWire
  content : ContentIdentityWire
  config : GameConfigWire
  initial : InitialStateWire
deriving DecidableEq

/-! ## Canonical input encoding -/

def DeploymentIdentityWire.toJson (d : DeploymentIdentityWire) : String :=
  "{\"schema\":" ++ jsonString d.schema ++
    ",\"deployment_domain\":" ++ jsonString d.deploymentDomain ++
    ",\"deployment_id\":" ++ jsonString (Emit.bytes32Hex d.deploymentId) ++
    ",\"deployment_digest\":" ++ jsonString (Emit.bytes32Hex d.deploymentDigest) ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex d.federationId) ++
    ",\"genesis_sha256\":" ++ jsonString (Emit.bytes32Hex d.genesisSha256) ++
    ",\"manifest_sha256\":" ++ jsonString (Emit.bytes32Hex d.manifestSha256) ++
    ",\"policy_sha256\":" ++ jsonString (Emit.bytes32Hex d.policySha256) ++ "}"

def ContentIdentityWire.toJson (c : ContentIdentityWire) : String :=
  "{\"signature_schema\":" ++ jsonString c.signatureSchema ++
    ",\"manifest_sha256\":" ++ jsonString (Emit.bytes32Hex c.manifestSha256) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex c.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex c.activationDigest) ++
    ",\"source_digest\":" ++ jsonString (Emit.bytes32Hex c.sourceDigest) ++
    ",\"signal_content_digest\":" ++ jsonString (Emit.bytes32Hex c.signalContentDigest) ++
    ",\"curator_key\":" ++ jsonString (Emit.bytes32Hex c.curatorKey) ++
    ",\"content_epoch\":" ++ toString c.contentEpoch ++
    ",\"activation_counter\":" ++ toString c.activationCounter ++ "}"

def InitialStateWire.toJson (s : InitialStateWire) : String :=
  "{\"world\":" ++ s.world.toJson ++
    ",\"known\":" ++ jsonArray (s.known.map ArtifactRefWire.toJson) ++
    ",\"alpha\":" ++ jsonArray (s.alpha.map ArtifactRefWire.toJson) ++
    ",\"superseded\":" ++ jsonArray (s.superseded.map ArtifactRefWire.toJson) ++
    ",\"consumed_runs\":" ++ jsonArray (s.consumedRuns.map ReceiptKeyWire.toJson) ++
    ",\"player_counters\":" ++ jsonArray (s.playerCounters.map PlayerCounterRowWire.toJson) ++
    ",\"canon_revision\":" ++ toString s.canonRevision ++
    ",\"curator_counter\":" ++ toString s.curatorCounter ++
    ",\"transition_count\":" ++ toString s.transitionCount ++
    ",\"last_transition_digest\":" ++
      jsonString (Emit.bytes32Hex s.lastTransitionDigest) ++ "}"

def GenesisInputWire.toJson (input : GenesisInputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"deployment\":" ++ input.deployment.toJson ++
    ",\"content\":" ++ input.content.toJson ++
    ",\"config\":" ++ input.config.toJson ++
    ",\"initial\":" ++ input.initial.toJson ++ "}"

/-! ## Strict input parser -/

private def parseArtifactRef (j : Json) : Except String ArtifactRefWire := do
  exactKeys j ["mission_id", "artifact_id", "source_digest", "content_digest"]
  pure {
    missionId := ← objectNat j "mission_id" WIRE_ID_LIMIT
    artifactId := ← objectNat j "artifact_id" WIRE_ID_LIMIT
    sourceDigest := ← objectDigest j "source_digest"
    contentDigest := ← objectDigest j "content_digest"
  }

private def canonicalArtifactsB (xs : List ArtifactRefWire) : Bool :=
  xs.length ≤ WIRE_ARTIFACT_LIMIT && decide (xs.Pairwise (· < ·))

private def canonicalReceiptsB (xs : List ReceiptKeyWire) : Bool :=
  xs.length ≤ WIRE_RECEIPT_LIMIT && decide (xs.Pairwise (· < ·))

open scoped Prod.Lex

private abbrev CounterOrderKey := Digest32 ×ₗ (Digest32 ×ₗ (Nat ×ₗ Digest32))

private def counterOrderKey (r : PlayerCounterRowWire) : CounterOrderKey :=
  toLex (r.federationId, toLex (r.contentSession, toLex (r.contentEpoch, r.playerKey)))

private def canonicalCounterRowsB (xs : List PlayerCounterRowWire) : Bool :=
  xs.length ≤ WIRE_COUNTER_LIMIT &&
    decide ((xs.map counterOrderKey).Pairwise (· < ·))

private def parseBoundedArray {T : Type} (j : Json) (limit : Nat)
    (parse : Json → Except String T) (canonical : List T → Bool) : Except String (List T) := do
  let values := (← j.getArr?).toList
  if values.length > limit then throw "list exceeds wire bound"
  let parsed ← values.mapM parse
  if canonical parsed then pure parsed else throw "list is not canonical"

private def parseBudget (j : Json) : Except String BudgetWire := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relics := ← objectNat j "relics" RELIC_LIMIT
  }

private def parsePrivacy : String → Except String PrivacyGrade
  | "public" => pure .public
  | "operator-visible-hiding-fri" => pure .operatorVisibleHidingFri
  | "process-separated-threshold" => pure .processSeparatedThreshold
  | "independent-operator-threshold" => pure .independentOperatorThreshold
  | _ => throw "unknown privacy grade"

private def parseBallot : String → Except String BallotRegime
  | "none" => pure .none
  | "one-player-one-voice" => pure .onePlayerOneVoice
  | "one-wallet-one-voice" => pure .oneWalletOneVoice
  | "capped-choir" => pure .cappedChoir
  | "prediction-oracle" => pure .predictionOracle
  | _ => throw "unknown ballot regime"

private def parseMission (j : Json) : Except String MissionWire := do
  exactKeys j ["mission_id", "artifact", "epoch", "federation_id", "content_root",
    "activation_digest", "content_session", "run_seed", "budget", "allowed_relics",
    "privacy", "ballot"]
  pure {
    missionId := ← objectNat j "mission_id" WIRE_ID_LIMIT
    artifact := ← parseArtifactRef (← j.getObjVal? "artifact")
    epoch := ← objectNat j "epoch"
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    runSeed := ← objectDigest j "run_seed"
    budget := ← parseBudget (← j.getObjVal? "budget")
    allowedRelics := ← parseNatList (← j.getObjVal? "allowed_relics") MISSION_RELIC_LIMIT
    privacy := ← parsePrivacy (← j.getObjValAs? String "privacy")
    ballot := ← parseBallot (← j.getObjValAs? String "ballot")
  }

private def parseContribution (j : Json) : Except String ContributionWire := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relics := ← parseNatList (← j.getObjVal? "relics") RELIC_LIMIT
  }

private def parseCode (j : Json) : Except String CodeWire := do
  exactKeys j ["low", "mid", "high"]
  pure {
    low := ← objectNat j "low" 5
    mid := ← objectNat j "mid" 5
    high := ← objectNat j "high" 5
  }

/-- ⚑ DELEGATED 2026-08-09.  This module used to carry its OWN copy of the config
parser — a second description of what an active configuration is, in the one place
whose whole job is to install one.  It now calls the judge's parser, so a genesis blob
is accepted here exactly when `decodeGameConfig` would accept it later, and the
game tag reaches genesis for free. -/
private def parseConfig (j : Json) : Except String GameConfigWire :=
  NetworkJudgeWire.parseGameConfig j

private def parseWorld (j : Json) : Except String WorldStateWire := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score",
    "discovered_relics", "beta_artifacts", "sequence"]
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    discoveredRelics := ←
      parseNatList (← j.getObjVal? "discovered_relics") WIRE_ARTIFACT_LIMIT
    betaArtifacts := ← parseBoundedArray (← j.getObjVal? "beta_artifacts")
      WIRE_ARTIFACT_LIMIT parseArtifactRef canonicalArtifactsB
    sequence := ← objectNat j "sequence"
  }

private def parseReceiptKey (j : Json) : Except String ReceiptKeyWire := do
  exactKeys j ["federation_id", "content_session", "content_epoch", "player_key",
    "player_counter"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    playerKey := ← objectDigest j "player_key"
    playerCounter := ← objectNat j "player_counter"
  }

private def parseCounterRow (j : Json) : Except String PlayerCounterRowWire := do
  exactKeys j ["federation_id", "content_session", "content_epoch", "player_key", "value"]
  let value ← objectNat j "value"
  if value = 0 then throw "explicit zero player counter is noncanonical"
  pure {
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    playerKey := ← objectDigest j "player_key"
    value
  }

private def parseDeployment (j : Json) : Except String DeploymentIdentityWire := do
  exactKeys j ["schema", "deployment_domain", "deployment_id", "deployment_digest",
    "federation_id", "genesis_sha256", "manifest_sha256", "policy_sha256"]
  pure {
    schema := ← j.getObjValAs? String "schema"
    deploymentDomain := ← j.getObjValAs? String "deployment_domain"
    deploymentId := ← objectDigest j "deployment_id"
    deploymentDigest := ← objectDigest j "deployment_digest"
    federationId := ← objectDigest j "federation_id"
    genesisSha256 := ← objectDigest j "genesis_sha256"
    manifestSha256 := ← objectDigest j "manifest_sha256"
    policySha256 := ← objectDigest j "policy_sha256"
  }

private def parseContent (j : Json) : Except String ContentIdentityWire := do
  exactKeys j ["signature_schema", "manifest_sha256", "content_root", "activation_digest",
    "source_digest", "signal_content_digest", "curator_key", "content_epoch",
    "activation_counter"]
  pure {
    signatureSchema := ← j.getObjValAs? String "signature_schema"
    manifestSha256 := ← objectDigest j "manifest_sha256"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    sourceDigest := ← objectDigest j "source_digest"
    signalContentDigest := ← objectDigest j "signal_content_digest"
    curatorKey := ← objectDigest j "curator_key"
    contentEpoch := ← objectNat j "content_epoch"
    activationCounter := ← objectNat j "activation_counter"
  }

private def parseInitial (j : Json) : Except String InitialStateWire := do
  exactKeys j ["world", "known", "alpha", "superseded", "consumed_runs",
    "player_counters", "canon_revision", "curator_counter", "transition_count",
    "last_transition_digest"]
  pure {
    world := ← parseWorld (← j.getObjVal? "world")
    known := ← parseBoundedArray (← j.getObjVal? "known") WIRE_ARTIFACT_LIMIT
      parseArtifactRef canonicalArtifactsB
    alpha := ← parseBoundedArray (← j.getObjVal? "alpha") WIRE_ARTIFACT_LIMIT
      parseArtifactRef canonicalArtifactsB
    superseded := ← parseBoundedArray (← j.getObjVal? "superseded") WIRE_ARTIFACT_LIMIT
      parseArtifactRef canonicalArtifactsB
    consumedRuns := ← parseBoundedArray (← j.getObjVal? "consumed_runs")
      WIRE_RECEIPT_LIMIT parseReceiptKey canonicalReceiptsB
    playerCounters := ← parseBoundedArray (← j.getObjVal? "player_counters")
      WIRE_COUNTER_LIMIT parseCounterRow canonicalCounterRowsB
    canonRevision := ← objectNat j "canon_revision"
    curatorCounter := ← objectNat j "curator_counter"
    transitionCount := ← objectNat j "transition_count"
    lastTransitionDigest := ← objectDigest j "last_transition_digest"
  }

private def parseInputJson (j : Json) : Except String GenesisInputWire := do
  exactKeys j ["format", "deployment", "content", "config", "initial"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong genesis input format"
  pure {
    deployment := ← parseDeployment (← j.getObjVal? "deployment")
    content := ← parseContent (← j.getObjVal? "content")
    config := ← parseConfig (← j.getObjVal? "config")
    initial := ← parseInitial (← j.getObjVal? "initial")
  }

private def canonicalDecode {T : Type} (parse : Json → Except String T) (encode : T → String)
    (bytes : String) : Option T :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json =>
      match parse json with
      | .error _ => none
      | .ok value => if encode value = bytes then some value else none

private theorem canonicalDecode_reencodes {T : Type} (parse : Json → Except String T)
    (encode : T → String) {bytes : String} {value : T}
    (accepted : canonicalDecode parse encode bytes = some value) : encode value = bytes := by
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  exact equal

def decodeGenesisInputWithLimit (limit : Nat) (bytes : String) : Option GenesisInputWire :=
  if bytes.utf8ByteSize ≤ limit then
    canonicalDecode parseInputJson GenesisInputWire.toJson bytes
  else none

def decodeGenesisInput (bytes : String) : Option GenesisInputWire :=
  decodeGenesisInputWithLimit GENESIS_BYTE_LIMIT bytes

theorem decodeGenesisInput_reencodes {bytes : String} {input : GenesisInputWire}
    (accepted : decodeGenesisInput bytes = some input) : input.toJson = bytes := by
  simp only [decodeGenesisInput, decodeGenesisInputWithLimit] at accepted
  split at accepted <;> try contradiction
  exact canonicalDecode_reencodes parseInputJson GenesisInputWire.toJson accepted

theorem decodeGenesisInput_refuses_oversized (bytes : String)
    (oversized : GENESIS_BYTE_LIMIT < bytes.utf8ByteSize) : decodeGenesisInput bytes = none := by
  simp [decodeGenesisInput, decodeGenesisInputWithLimit, Nat.not_le.mpr oversized]

/-! ## SHA-256 and genuinely faithful nine-lane coordinates -/

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def natByteHex (n : Nat) : String :=
  String.ofList [lowerHexDigit (n / 16), lowerHexDigit (n % 16)]

private def utf8Nats (s : String) : List Nat :=
  s.toUTF8.toList.map UInt8.toNat

/-- Raw SHA-256 of the exact UTF-8 wire bytes.  The reference compression
function is the same Lean implementation used by Mina state-hash derivation;
the final parse checks that it returned exactly 32 byte-valued outputs. -/
def sha256Wire? (s : String) : Option Digest32 :=
  Emit.parseBytes32Hex?
    (String.join ((Dregg2.Bridge.MinaStateHashDerive.sha256 (utf8Nats s)).map natByteHex))

/-- The canonical 32-byte value as a total `Fin 32 → Fin 256` key. -/
def Digest32.toBytes32 (digest : Digest32) : Dregg2.Circuit.FieldLanes9.Bytes32 := fun i =>
  digest.bytes.get ⟨i.val, by rw [digest.length_eq]; exact i.isLt⟩

/-- Nine base-2^29 coordinates.  Unlike an eight-BabyBear-limb fold, this map
does not reduce or discard any bit; it is the repository's proved injective
32-byte key carrier. -/
def faithfulLanes9 (digest : Digest32) : List Nat :=
  List.ofFn (Dregg2.Circuit.KeyLanes9.keyToLanes9 (Digest32.toBytes32 digest))

theorem faithfulLanes9_length (digest : Digest32) : (faithfulLanes9 digest).length = 9 := by
  simp [faithfulLanes9]

theorem Digest32.toBytes32_injective : Function.Injective Digest32.toBytes32 := by
  intro left right equal
  have bytesEqual : left.bytes = right.bytes := by
    apply List.ext_get
    · rw [left.length_eq, right.length_eq]
    · intro n leftBound rightBound
      have n32 : n < 32 := by simpa [left.length_eq] using leftBound
      have atIndex := congrFun equal ⟨n, n32⟩
      simpa [Digest32.toBytes32] using atIndex
  cases left
  cases right
  simp_all

theorem faithfulLanes9_injective : Function.Injective faithfulLanes9 := by
  intro left right equal
  apply Digest32.toBytes32_injective
  apply Dregg2.Circuit.KeyLanes9.keyToLanes9_injective
  funext i
  have atIndex := congrArg (fun xs => xs.getD i.val 0) equal
  fin_cases i <;> simpa [faithfulLanes9] using atIndex

/-! ## Exact persisted-head projection -/

structure GenesisOutputWire where
  authorityId : Digest32
  deploymentDigest : Digest32
  declaredDeploymentId : Digest32
  deploymentGenesisSha256 : Digest32
  deploymentManifestSha256 : Digest32
  deploymentPolicySha256 : Digest32
  manifestSha256 : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  curatorKey : Digest32
  contentEpoch : Nat
  activationCounter : Nat
  transitionCount : Nat
  worldSequence : Nat
  canonRevision : Nat
  lastTransitionDigest : Digest32
  configJson : String
  canonJson : String
  configSha256 : Digest32
  canonSha256 : Digest32
  authorityLanes9 : List Nat
  deploymentLanes9 : List Nat
  deploymentGenesisLanes9 : List Nat
  manifestLanes9 : List Nat
  contentRootLanes9 : List Nat
  activationLanes9 : List Nat
  curatorKeyLanes9 : List Nat
  configSha256Lanes9 : List Nat
  canonSha256Lanes9 : List Nat
deriving DecidableEq

def GenesisOutputWire.toJson (output : GenesisOutputWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"authority_id\":" ++ jsonString (Emit.bytes32Hex output.authorityId) ++
    ",\"deployment_digest\":" ++ jsonString (Emit.bytes32Hex output.deploymentDigest) ++
    ",\"declared_deployment_id\":" ++
      jsonString (Emit.bytes32Hex output.declaredDeploymentId) ++
    ",\"deployment_genesis_sha256\":" ++
      jsonString (Emit.bytes32Hex output.deploymentGenesisSha256) ++
    ",\"deployment_manifest_sha256\":" ++
      jsonString (Emit.bytes32Hex output.deploymentManifestSha256) ++
    ",\"deployment_policy_sha256\":" ++
      jsonString (Emit.bytes32Hex output.deploymentPolicySha256) ++
    ",\"manifest_sha256\":" ++ jsonString (Emit.bytes32Hex output.manifestSha256) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex output.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex output.activationDigest) ++
    ",\"curator_key\":" ++ jsonString (Emit.bytes32Hex output.curatorKey) ++
    ",\"content_epoch\":" ++ toString output.contentEpoch ++
    ",\"activation_counter\":" ++ toString output.activationCounter ++
    ",\"transition_count\":" ++ toString output.transitionCount ++
    ",\"world_sequence\":" ++ toString output.worldSequence ++
    ",\"canon_revision\":" ++ toString output.canonRevision ++
    ",\"last_transition_digest\":" ++
      jsonString (Emit.bytes32Hex output.lastTransitionDigest) ++
    ",\"config_json\":" ++ jsonString output.configJson ++
    ",\"canon_json\":" ++ jsonString output.canonJson ++
    ",\"config_sha256\":" ++ jsonString (Emit.bytes32Hex output.configSha256) ++
    ",\"canon_sha256\":" ++ jsonString (Emit.bytes32Hex output.canonSha256) ++
    ",\"authority_lanes9\":" ++ jsonArray (output.authorityLanes9.map toString) ++
    ",\"deployment_lanes9\":" ++ jsonArray (output.deploymentLanes9.map toString) ++
    ",\"deployment_genesis_lanes9\":" ++
      jsonArray (output.deploymentGenesisLanes9.map toString) ++
    ",\"manifest_lanes9\":" ++ jsonArray (output.manifestLanes9.map toString) ++
    ",\"content_root_lanes9\":" ++ jsonArray (output.contentRootLanes9.map toString) ++
    ",\"activation_lanes9\":" ++ jsonArray (output.activationLanes9.map toString) ++
    ",\"curator_key_lanes9\":" ++ jsonArray (output.curatorKeyLanes9.map toString) ++
    ",\"config_sha256_lanes9\":" ++ jsonArray (output.configSha256Lanes9.map toString) ++
    ",\"canon_sha256_lanes9\":" ++ jsonArray (output.canonSha256Lanes9.map toString) ++ "}"

private def parseLanes9 (j : Json) (key : String) : Except String (List Nat) := do
  let array ← (← j.getObjVal? key).getArr?
  let values := array.toList
  let lanes ← values.mapM (fun value => value.getNat?)
  if lanes.length != 9 then throw "faithful coordinate list must have nine lanes"
  if !lanes.all (· < Dregg2.Circuit.KeyLanes9.K) then throw "faithful coordinate exceeds radix"
  if !(lanes.getD 8 0 < Dregg2.Circuit.KeyLanes9.KTOP) then
    throw "faithful top coordinate exceeds 24 bits"
  pure lanes

private def parseOutputJson (j : Json) : Except String GenesisOutputWire := do
  exactKeys j ["format", "authority_id", "deployment_digest", "declared_deployment_id",
    "deployment_genesis_sha256", "deployment_manifest_sha256", "deployment_policy_sha256",
    "manifest_sha256", "content_root", "activation_digest", "curator_key", "content_epoch",
    "activation_counter", "transition_count", "world_sequence", "canon_revision",
    "last_transition_digest", "config_json", "canon_json", "config_sha256", "canon_sha256",
    "authority_lanes9", "deployment_lanes9", "deployment_genesis_lanes9", "manifest_lanes9",
    "content_root_lanes9", "activation_lanes9", "curator_key_lanes9",
    "config_sha256_lanes9", "canon_sha256_lanes9"]
  let format ← j.getObjValAs? String "format"
  if format != OUTPUT_FORMAT then throw "wrong genesis output format"
  pure {
    authorityId := ← objectDigest j "authority_id"
    deploymentDigest := ← objectDigest j "deployment_digest"
    declaredDeploymentId := ← objectDigest j "declared_deployment_id"
    deploymentGenesisSha256 := ← objectDigest j "deployment_genesis_sha256"
    deploymentManifestSha256 := ← objectDigest j "deployment_manifest_sha256"
    deploymentPolicySha256 := ← objectDigest j "deployment_policy_sha256"
    manifestSha256 := ← objectDigest j "manifest_sha256"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    curatorKey := ← objectDigest j "curator_key"
    contentEpoch := ← objectNat j "content_epoch"
    activationCounter := ← objectNat j "activation_counter"
    transitionCount := ← objectNat j "transition_count"
    worldSequence := ← objectNat j "world_sequence"
    canonRevision := ← objectNat j "canon_revision"
    lastTransitionDigest := ← objectDigest j "last_transition_digest"
    configJson := ← j.getObjValAs? String "config_json"
    canonJson := ← j.getObjValAs? String "canon_json"
    configSha256 := ← objectDigest j "config_sha256"
    canonSha256 := ← objectDigest j "canon_sha256"
    authorityLanes9 := ← parseLanes9 j "authority_lanes9"
    deploymentLanes9 := ← parseLanes9 j "deployment_lanes9"
    deploymentGenesisLanes9 := ← parseLanes9 j "deployment_genesis_lanes9"
    manifestLanes9 := ← parseLanes9 j "manifest_lanes9"
    contentRootLanes9 := ← parseLanes9 j "content_root_lanes9"
    activationLanes9 := ← parseLanes9 j "activation_lanes9"
    curatorKeyLanes9 := ← parseLanes9 j "curator_key_lanes9"
    configSha256Lanes9 := ← parseLanes9 j "config_sha256_lanes9"
    canonSha256Lanes9 := ← parseLanes9 j "canon_sha256_lanes9"
  }

/-- Syntax-only output decoder.  Acceptance proves canonical JSON shape and
transport bounds, not that Lean authorized the embedded genesis.  Authority
requires `NetworkGenesis.decodeValidatedGenesisOutput`, which recomputes the
entire expected output from an authorized input. -/
def decodeGenesisOutputSyntax (bytes : String) : Option GenesisOutputWire :=
  if bytes.utf8ByteSize ≤ GENESIS_BYTE_LIMIT then
    canonicalDecode parseOutputJson GenesisOutputWire.toJson bytes
  else none

theorem decodeGenesisOutputSyntax_reencodes {bytes : String} {output : GenesisOutputWire}
    (accepted : decodeGenesisOutputSyntax bytes = some output) : output.toJson = bytes := by
  simp only [decodeGenesisOutputSyntax] at accepted
  split at accepted <;> try contradiction
  exact canonicalDecode_reencodes parseOutputJson GenesisOutputWire.toJson accepted

#assert_axioms decodeGenesisInput_reencodes
#assert_axioms decodeGenesisInput_refuses_oversized
#assert_axioms faithfulLanes9_length
#assert_axioms Digest32.toBytes32_injective
#assert_axioms faithfulLanes9_injective
#assert_axioms decodeGenesisOutputSyntax_reencodes

end Dregg2.Games.PathOfAngels.NetworkGenesisWire
