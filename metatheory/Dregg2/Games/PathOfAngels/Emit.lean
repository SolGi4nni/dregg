/-
# Dregg2.Games.PathOfAngels.Emit — the POAG1 artifact boundary

This module is the single source of the bytes consumed by PoA hosts.  It projects
the Lean game declarations into a small, versioned bundle; TypeScript/Rust may
render these declarations, but they do not get a second copy of the rules.

`ingestManifest` is deliberately stricter than an ordinary JSON decoder:

* the object has exactly the POAG1 v1 fields;
* every artifact entry has exactly its five fields;
* the source digest is `sha256:` plus 64 lowercase hexadecimal digits;
* artifact paths, order, byte lengths, SHA-256 digests and FNV-1a byte pins must
  equal the bundle Lean itself renders.

The SHA-256 primitive is supplied by the reproducibility driver (which hashes the
named Lean sources and the signal descriptor bytes).  Lean parses the resulting
32-byte values, places them in `MissionSpec.ArtifactRef`, and owns every decision
about what those digests authorize.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SignalTriangulation
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.Emit

open Lean
open Dregg2.Games.PathOfAngels

abbrev FORMAT : String := "POAG1"
abbrev SCHEMA_VERSION : Nat := 1
abbrev AUTHORITY : String := "Dregg2.Games.PathOfAngels"

/-! ## Canonical JSON helpers -/

private def jsonString (s : String) : String :=
  String.quote s

private def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def jsonPrettyArray (xs : List String) : String :=
  match xs with
  | [] => "[]"
  | _ => "[\n" ++ String.intercalate ",\n" xs ++ "\n  ]"

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def hexNibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else none

def isLowerHexOfLength (n : Nat) (s : String) : Bool :=
  s.length == n && s.toList.all (hexNibble? · |>.isSome)

def validSha256 (s : String) : Bool :=
  s.startsWith "sha256:" &&
    isLowerHexOfLength 64 (String.ofList (s.toList.drop 7))

private def parseByte? (hi lo : Char) : Option (Fin 256) := do
  let h ← hexNibble? hi
  let l ← hexNibble? lo
  let n := 16 * h + l
  if hn : n < 256 then some ⟨n, hn⟩ else none

private def parseDigestList? : List Char → Option (List (Fin 256))
  | [] => some []
  | hi :: lo :: rest => do
      let b ← parseByte? hi lo
      return b :: (← parseDigestList? rest)
  | _ => none

/-- Parse the exact wire spelling used by POAG1 into Core's 32-byte type. -/
def parseDigest32? (s : String) : Option Digest32 := do
  if !validSha256 s then none else
    let bytes ← parseDigestList? (s.toList.drop 7)
    if h : bytes.length = 32 then
      some { bytes := bytes, length_eq := h }
    else none

/-- Parse an identifier whose wire encoding is 64 lowercase hexadecimal digits
without the `sha256:` claim.  Federation identifiers use this spelling. -/
def parseBytes32Hex? (s : String) : Option Digest32 :=
  if isLowerHexOfLength 64 s then parseDigest32? ("sha256:" ++ s) else none

/-- Explicit non-deployment vector for deterministic emitter tests.  Canonical
artifacts never use it; their id is supplied only by verified PoA genesis. -/
abbrev TEST_FEDERATION_ID_HEX : String :=
  "a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1"

theorem parseBytes32Hex_test_federation_vector :
    (parseBytes32Hex? TEST_FEDERATION_ID_HEX).isSome = true := by
  native_decide

theorem parseBytes32Hex_refuses_display_label :
    parseBytes32Hex? "POA-FED-1" = none := by
  native_decide

#assert_compiled parseBytes32Hex_test_federation_vector
#assert_compiled parseBytes32Hex_refuses_display_label

private def byteHex (b : Fin 256) : String :=
  String.ofList [lowerHexDigit (b.val / 16), lowerHexDigit (b.val % 16)]

def bytes32Hex (d : Digest32) : String :=
  String.join (d.bytes.map byteHex)

def digestHex (d : Digest32) : String :=
  "sha256:" ++ bytes32Hex d

/-! ## Stable byte pin -/

abbrev FNV_OFFSET : UInt64 := 14695981039346656037
abbrev FNV_PRIME : UInt64 := 1099511628211

/-- FNV-1a is an inexpensive deterministic drift/tamper pin, not a cryptographic
claim.  The source/content identities in `ArtifactRef` remain full SHA-256. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun acc byte => (acc ^^^ byte.toUInt64) * FNV_PRIME) FNV_OFFSET

private def uint64HexAux : Nat → UInt64 → List Char → List Char
  | 0, _, acc => acc
  | n + 1, x, acc =>
      uint64HexAux n (x / 16) (lowerHexDigit (x.toNat % 16) :: acc)

def fnv1a64Hex (s : String) : String :=
  String.ofList (uint64HexAux 16 (fnv1a64 s) [])

theorem fnv1a64_empty_vector : fnv1a64Hex "" = "cbf29ce484222325" := by
  native_decide

theorem fnv1a64_a_vector : fnv1a64Hex "a" = "af63dc4c8601ec8c" := by
  native_decide

#assert_compiled fnv1a64_empty_vector
#assert_compiled fnv1a64_a_vector

/-! ## POAG1 manifest and strict parser -/

structure ArtifactPin where
  path : String
  mediaType : String
  bytes : Nat
  sha256 : String
  fnv1a64 : String
deriving DecidableEq, Repr

structure Manifest where
  format : String
  schemaVersion : Nat
  sourceDigest : String
  authority : String
  artifacts : List ArtifactPin
deriving DecidableEq, Repr

structure ArtifactBytes where
  path : String
  mediaType : String
  contents : String
deriving DecidableEq, Repr

def ArtifactBytes.pin (a : ArtifactBytes) (sha256 : String) : ArtifactPin :=
  { path := a.path
    mediaType := a.mediaType
    bytes := a.contents.toUTF8.size
    sha256 := sha256
    fnv1a64 := fnv1a64Hex a.contents }

def ArtifactPin.toJson (p : ArtifactPin) : String :=
  "    {\"path\":" ++ jsonString p.path ++
    ",\"media_type\":" ++ jsonString p.mediaType ++
    ",\"bytes\":" ++ toString p.bytes ++
    ",\"sha256\":" ++ jsonString p.sha256 ++
    ",\"fnv1a64\":" ++ jsonString p.fnv1a64 ++ "}"

def Manifest.toJson (m : Manifest) : String :=
  "{\n  \"format\":" ++ jsonString m.format ++
    ",\n  \"schema_version\":" ++ toString m.schemaVersion ++
    ",\n  \"source_digest\":" ++ jsonString m.sourceDigest ++
    ",\n  \"authority\":" ++ jsonString m.authority ++
    ",\n  \"artifacts\":" ++ jsonPrettyArray (m.artifacts.map ArtifactPin.toJson) ++
    "\n}\n"

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then
    pure ()
  else
    throw s!"POAG1 object has missing or unknown fields; expected {allowed}"

private def parseArtifactPin (j : Json) : Except String ArtifactPin := do
  exactKeys j ["path", "media_type", "bytes", "sha256", "fnv1a64"]
  pure {
    path := ← j.getObjValAs? String "path"
    mediaType := ← j.getObjValAs? String "media_type"
    bytes := ← j.getObjValAs? Nat "bytes"
    sha256 := ← j.getObjValAs? String "sha256"
    fnv1a64 := ← j.getObjValAs? String "fnv1a64"
  }

private def parseArtifactPins (j : Json) : Except String (List ArtifactPin) := do
  let xs ← j.getArr?
  xs.toList.mapM parseArtifactPin

private def parseManifestJson (j : Json) : Except String Manifest := do
  exactKeys j ["format", "schema_version", "source_digest", "authority", "artifacts"]
  pure {
    format := ← j.getObjValAs? String "format"
    schemaVersion := ← j.getObjValAs? Nat "schema_version"
    sourceDigest := ← j.getObjValAs? String "source_digest"
    authority := ← j.getObjValAs? String "authority"
    artifacts := ← parseArtifactPins (← j.getObjVal? "artifacts")
  }

def parseManifest (bytes : String) : Except String Manifest := do
  parseManifestJson (← Json.parse bytes)

/-! ## Lean-owned wire projections -/

def privacyGradeTag : PrivacyGrade → String
  | .public => "public"
  | .operatorVisibleHidingFri => "operator-visible-hiding-fri"
  | .processSeparatedThreshold => "process-separated-threshold"
  | .independentOperatorThreshold => "independent-operator-threshold"

def ballotRegimeTag : BallotRegime → String
  | .none => "none"
  | .onePlayerOneVoice => "one-player-one-voice"
  | .oneWalletOneVoice => "one-wallet-one-voice"
  | .cappedChoir => "capped-choir"
  | .predictionOracle => "prediction-oracle"

def artifactRefJson (a : ArtifactRef) : String :=
  "{\"mission_id\":" ++ toString a.missionId.value ++
    ",\"artifact_id\":" ++ toString a.artifactId.value ++
    ",\"source_digest\":" ++ jsonString (digestHex a.sourceDigest) ++
    ",\"content_digest\":" ++ jsonString (digestHex a.contentDigest) ++ "}"

/-- Exact wire projection used to regression-test the emitter independently of
Core's proof-carrying digest representation. -/
structure ArtifactRefProjection where
  missionId : Nat
  artifactId : Nat
  sourceDigest : String
  contentDigest : String
deriving DecidableEq, Repr

/-- Parse an emitted ArtifactRef and reject any missing or additional unique key. -/
def parseArtifactRefProjection (bytes : String) : Except String ArtifactRefProjection := do
  let j ← Json.parse bytes
  exactKeys j ["mission_id", "artifact_id", "source_digest", "content_digest"]
  pure {
    missionId := ← j.getObjValAs? Nat "mission_id"
    artifactId := ← j.getObjValAs? Nat "artifact_id"
    sourceDigest := ← j.getObjValAs? String "source_digest"
    contentDigest := ← j.getObjValAs? String "content_digest"
  }

private def artifactRefTestDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

private def artifactRefTestVector : ArtifactRef :=
  { missionId := ⟨7⟩
    artifactId := ⟨11⟩
    sourceDigest := artifactRefTestDigest
    contentDigest := artifactRefTestDigest }

/-- Exact bytes make a repeated `source_digest` (or any fifth field) observable,
even though ordinary JSON object parsers conventionally collapse duplicate keys. -/
theorem artifactRefJson_exact_four_key_vector :
    artifactRefJson artifactRefTestVector =
      "{\"mission_id\":7,\"artifact_id\":11,\"source_digest\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\",\"content_digest\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}" := by
  native_decide

theorem artifactRefJson_parses_as_exact_four_key_projection :
    parseArtifactRefProjection (artifactRefJson artifactRefTestVector) = .ok {
      missionId := 7
      artifactId := 11
      sourceDigest :=
        "sha256:0000000000000000000000000000000000000000000000000000000000000000"
      contentDigest :=
        "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    } := by
  native_decide

#assert_compiled artifactRefJson_exact_four_key_vector
#assert_compiled artifactRefJson_parses_as_exact_four_key_projection

def contributionBudgetJson (b : ContributionBudget) : String :=
  "{\"intel\":" ++ toString b.intel.val ++
    ",\"supplies\":" ++ toString b.supplies.val ++
    ",\"cohesion\":" ++ toString b.cohesion.val ++
    ",\"influence\":" ++ toString b.influence.val ++
    ",\"score\":" ++ toString b.score.val ++
    ",\"relics\":" ++ toString b.relics.val ++ "}"

def contributionJsonWithRelics (c : Contribution) (relics : List RelicId) : String :=
  "{\"intel\":" ++ toString c.intel.val ++
    ",\"supplies\":" ++ toString c.supplies.val ++
    ",\"cohesion\":" ++ toString c.cohesion.val ++
    ",\"influence\":" ++ toString c.influence.val ++
    ",\"score\":" ++ toString c.score.val ++
    ",\"relics\":" ++ jsonArray (relics.map (toString ·.value)) ++ "}"

def worldStateJsonWith (w : WorldState) (relics : List RelicId)
    (artifacts : List ArtifactRef) : String :=
  "{\"intel\":" ++ toString w.intel.val ++
    ",\"supplies\":" ++ toString w.supplies.val ++
    ",\"cohesion\":" ++ toString w.cohesion.val ++
    ",\"influence\":" ++ toString w.influence.val ++
    ",\"score\":" ++ toString w.score.val ++
    ",\"discovered_relics\":" ++
      jsonArray (relics.map (toString ·.value)) ++
    ",\"beta_artifacts\":" ++
      jsonArray (artifacts.map artifactRefJson) ++
    ",\"sequence\":" ++ toString w.sequence ++ "}"

/-! ## Signal Triangulation executable descriptor and mission fixture -/

/-- Fixed-width domain identifiers for the beta devnet and this exact content
session.  They are identifiers, not hashes, so their wire spelling has no sha256
prefix. -/
private def taggedBytes32 (tag : List Nat) : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match tag[i.val]? with
    | some n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
    | none => 0
  length_eq := by simp

def signalContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 83, 73, 71, 45, 49]

/-- The complete precommitted run seed.  The unused 29 bytes are zero by
construction, so a host cannot grind them after seeing the play transcript. -/
def signalRunSeed : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match i.val with
    | 0 => ⟨2, by decide⟩
    | 1 => ⟨4, by decide⟩
    | 2 => ⟨1, by decide⟩
    | _ => 0
  length_eq := by simp

/-- The first beta mission's intercepted signal is derived by the authoritative
Lean function from the exact precommitted seed above. -/
def signalTarget : SignalTriangulation.Code :=
  SignalTriangulation.targetFromSeed signalRunSeed

theorem signalTarget_from_runSeed :
    signalTarget = SignalTriangulation.targetFromSeed signalRunSeed := rfl

theorem signalTarget_literal :
    signalTarget = { low := 2, mid := 4, high := 1 } := by
  native_decide

#assert_axioms signalTarget_from_runSeed
#assert_compiled signalTarget_literal

/-- Every legal three-band submission, in stable low/mid/high lexicographic order. -/
def signalAllCodes : List SignalTriangulation.Code :=
  (List.finRange 6).flatMap fun low =>
    (List.finRange 6).flatMap fun mid =>
      (List.finRange 6).map fun high => { low, mid, high }

theorem signalAllCodes_length : signalAllCodes.length = 216 := by
  native_decide

theorem signalAllCodes_nodup : signalAllCodes.Nodup := by
  native_decide

theorem signalAllCodes_complete (code : SignalTriangulation.Code) :
    code ∈ signalAllCodes := by
  rcases code with ⟨low, mid, high⟩
  simp [signalAllCodes]

structure SignalRow where
  guess : SignalTriangulation.Code
  exact : Nat
  present : Nat
  solved : Bool
deriving DecidableEq, Repr

/-- One row is computed by the authoritative Lean feedback function. -/
def signalRow (target guess : SignalTriangulation.Code) : SignalRow :=
  let f := SignalTriangulation.feedback target guess
  { guess := guess, exact := f.exact, present := f.present, solved := f.exact == 3 }

def signalRows (target : SignalTriangulation.Code) : List SignalRow :=
  signalAllCodes.map (signalRow target)

theorem signalRows_length (target : SignalTriangulation.Code) :
    (signalRows target).length = 216 := by
  simp [signalRows, signalAllCodes]

/-- Every emitted row is literally the output of the Lean rules oracle for one
member of the complete 216-code domain. -/
theorem signalRows_spec (target : SignalTriangulation.Code) (row : SignalRow)
    (h : row ∈ signalRows target) :
    ∃ guess, guess ∈ signalAllCodes ∧
      row.guess = guess ∧
      row.exact = (SignalTriangulation.feedback target guess).exact ∧
      row.present = (SignalTriangulation.feedback target guess).present ∧
      row.solved = ((SignalTriangulation.feedback target guess).exact == 3) := by
  simp only [signalRows, List.mem_map] at h
  obtain ⟨guess, hguess, rfl⟩ := h
  exact ⟨guess, hguess, rfl, rfl, rfl, rfl⟩

/-- The row's solved bit agrees with the actual step transition from every open
state, not merely with a separately rendered equality test. -/
theorem signalRow_matches_step (cfg : SignalTriangulation.Config)
    (s : SignalTriangulation.State) (guess : SignalTriangulation.Code)
    (hopen : SignalTriangulation.openB s = true) :
    (SignalTriangulation.step cfg s (.submit guess)).map (·.solved) =
      some (signalRow cfg.target guess).solved := by
  simp [SignalTriangulation.step, hopen, signalRow, SignalTriangulation.feedback]

#assert_compiled signalAllCodes_length
#assert_compiled signalAllCodes_nodup
#assert_axioms signalAllCodes_complete
#assert_axioms signalRows_length
#assert_axioms signalRows_spec
#assert_axioms signalRow_matches_step

private def signalCodeJson (c : SignalTriangulation.Code) : String :=
  "[" ++ toString c.low.val ++ "," ++ toString c.mid.val ++ "," ++
    toString c.high.val ++ "]"

private def signalRowJson (r : SignalRow) : String :=
  "    {\"guess\":" ++ signalCodeJson r.guess ++
    ",\"exact\":" ++ toString r.exact ++
    ",\"present\":" ++ toString r.present ++
    ",\"solved\":" ++ (if r.solved then "true" else "false") ++ "}"

def signalDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"signal-triangulation\",\n" ++
  "  \"ruleset\":\"signal-v1\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.SignalTriangulation\",\n" ++
  "  \"action_limit\":" ++ toString SignalTriangulation.MAX_TURNS ++ ",\n" ++
  "  \"run_seed\":" ++ jsonString (bytes32Hex signalRunSeed) ++ ",\n" ++
  "  \"target\":" ++ signalCodeJson signalTarget ++ ",\n" ++
  "  \"security\":{\"classification\":\"transparent-beta-demo\"," ++
    "\"target_visibility\":\"public\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"state\":{\"fields\":[\"turns\",\"solved\",\"last_feedback\"]},\n" ++
  "  \"action\":{\"tag\":\"submit\",\"code\":{\"bands\":3,\"alphabet\":6}},\n" ++
  "  \"feedback\":{\"exact_max\":3,\"present_max\":3,\"exact_plus_present_max\":3," ++
    "\"present_semantics\":\"multiplicity_intersection_minus_exact\",\"solved_when_exact\":3},\n" ++
  "  \"transition\":{\"open_when\":{\"solved\":false,\"turns_lt\":5}," ++
    "\"on_submit\":{\"lookup\":\"outcomes.guess\",\"turns\":\"increment\"," ++
    "\"solved\":\"row.solved\",\"last_feedback\":[\"row.exact\",\"row.present\"]}," ++
    "\"refuse_when\":[\"solved\",\"turns_gte_action_limit\"]},\n" ++
  "  \"output\":{\"requires\":\"solved\",\"contribution\":\"mission_reward\",\"artifact\":\"mission_artifact\"},\n" ++
  "  \"outcomes\":" ++ jsonPrettyArray ((signalRows signalTarget).map signalRowJson) ++ "\n" ++
  "}\n"

def signalBudget : ContributionBudget :=
  { intel := ⟨25, by decide⟩
    supplies := ⟨15, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨500, by decide⟩
    relics := ⟨1, by decide⟩ }

def signalReward : Contribution :=
  { intel := ⟨25, by decide⟩
    supplies := ⟨15, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨500, by decide⟩
    relics := {⟨1⟩}
    relics_bounded := by simp [RELIC_LIMIT] }

theorem signalReward_within : signalReward.within signalBudget = true := by
  decide

#assert_axioms signalReward_within

def signalArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨1⟩
    artifactId := ⟨1⟩
    sourceDigest := sourceDigest
    contentDigest := contentDigest }

def signalMission (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨1⟩
    artifact := signalArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId := federationId
    contentRoot := contentRoot
    activationDigest := activationDigest
    contentSession := signalContentSession
    runSeed := signalRunSeed
    budget := signalBudget
    allowedRelics := {⟨1⟩}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem signalReward_accepted
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (signalMission federationId sourceDigest contentDigest contentRoot activationDigest).acceptsContribution
      signalReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  constructor
  · exact signalReward_within
  · simp [signalMission, signalReward]

def signalConfig
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    SignalTriangulation.Config :=
  { target := signalTarget
    mission := signalMission federationId sourceDigest contentDigest contentRoot activationDigest
    reward := signalReward
    reward_accepted := signalReward_accepted federationId sourceDigest contentDigest contentRoot
      activationDigest
    target_eq := rfl }

theorem signalConfig_uses_precommitted_seed
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (signalConfig federationId sourceDigest contentDigest contentRoot activationDigest).mission.runSeed =
      signalRunSeed := rfl

theorem signalConfig_target_from_precommitted_seed
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (signalConfig federationId sourceDigest contentDigest contentRoot activationDigest).target =
      SignalTriangulation.targetFromSeed
        (signalConfig federationId sourceDigest contentDigest contentRoot activationDigest).mission.runSeed := rfl

#assert_axioms signalReward_accepted
#assert_axioms signalConfig_uses_precommitted_seed
#assert_axioms signalConfig_target_from_precommitted_seed

def signalPreview
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) : Option WorldState :=
  applyContribution (signalMission federationId sourceDigest contentDigest contentRoot activationDigest)
    signalReward
    WorldState.empty

def catalogJson (federationId sourceDigest contentDigest contentRoot : Digest32) : String :=
  /- The activation digest necessarily depends on the detached signature over the
  finished manifest, so it cannot occur inside that manifest without a hash cycle.
  Runtime activation replaces this zero only after signature verification. -/
  let inactiveActivation : Digest32 := taggedBytes32 []
  let mission := signalMission federationId sourceDigest contentDigest contentRoot inactiveActivation
  let preview := signalPreview federationId sourceDigest contentDigest contentRoot inactiveActivation
  "{\n" ++
  "  \"format\":\"POAG1-CATALOG\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"missions\":[{\n" ++
  "    \"mission_id\":" ++ toString mission.missionId.value ++ ",\n" ++
  "    \"title\":\"Signal Triangulation\",\n" ++
  "    \"engine_module\":\"Dregg2.Games.PathOfAngels.SignalTriangulation\",\n" ++
  "    \"ruleset\":\"signal-v1\",\n" ++
  "    \"reward_class\":\"non-economic-demo\",\n" ++
  "    \"action_limit\":" ++ toString SignalTriangulation.MAX_TURNS ++ ",\n" ++
  "    \"privacy_grade\":" ++ jsonString (privacyGradeTag mission.privacy) ++ ",\n" ++
  "    \"ballot_regime\":" ++ jsonString (ballotRegimeTag mission.ballot) ++ ",\n" ++
  "    \"epoch\":" ++ toString mission.epoch.value ++ ",\n" ++
  "    \"federation_id\":" ++ jsonString (bytes32Hex mission.federationId) ++ ",\n" ++
  "    \"content_root\":" ++ jsonString (digestHex mission.contentRoot) ++ ",\n" ++
  "    \"activation\":{\"state\":\"detached-signature-required\"," ++
    "\"digest_source\":\"POA-CONTENT-EPOCH-SIGNATURE-V1\"},\n" ++
  "    \"content_session\":" ++ jsonString (bytes32Hex mission.contentSession) ++ ",\n" ++
  "    \"run_seed\":" ++ jsonString (bytes32Hex mission.runSeed) ++ ",\n" ++
  "    \"budget\":" ++ contributionBudgetJson mission.budget ++ ",\n" ++
  "    \"allowed_relics\":" ++
    jsonArray ["1"] ++ ",\n" ++
  "    \"descriptor_path\":\"games/signal-triangulation.json\",\n" ++
  "    \"allowed_beta_discoveries\":[" ++ artifactRefJson mission.artifact ++ "]\n" ++
  "  }],\n" ++
  "  \"fixtures\":[{\n" ++
  "    \"id\":\"signal-solved-preview-v1\",\n" ++
  "    \"mission_id\":" ++ toString mission.missionId.value ++ ",\n" ++
  "    \"run_seed\":" ++ jsonString (bytes32Hex signalRunSeed) ++ ",\n" ++
  "    \"base_world\":" ++ worldStateJsonWith WorldState.empty [] [] ++ ",\n" ++
  "    \"contribution\":" ++ contributionJsonWithRelics signalReward [⟨1⟩] ++ ",\n" ++
  "    \"preview_world\":" ++
    (match preview with
     | none => "null"
     | some world => worldStateJsonWith world [⟨1⟩] [mission.artifact]) ++ "\n" ++
  "  }]\n" ++
  "}\n"

def schemaJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-SCHEMA\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"contract\":{\n" ++
  "    \"manifest_required\":[\"format\",\"schema_version\",\"source_digest\",\"authority\",\"artifacts\"],\n" ++
  "    \"artifact_pin_required\":[\"path\",\"media_type\",\"bytes\",\"sha256\",\"fnv1a64\"],\n" ++
  "    \"source_digest_pattern\":\"^sha256:[0-9a-f]{64}$\",\n" ++
  "    \"artifact_sha256_pattern\":\"^sha256:[0-9a-f]{64}$\",\n" ++
  "    \"bytes32_pattern\":\"^[0-9a-f]{64}$\",\n" ++
  "    \"fnv1a64_pattern\":\"^[0-9a-f]{16}$\",\n" ++
  "    \"content_root\":{\"algorithm\":\"sha256\"," ++
    "\"domain\":\"path-of-angels/content-root/v1\\u0000\"," ++
    "\"framing\":\"file_count_be64 || (path_len_be64 || path_utf8 || content_len_be64 || content_bytes)*\"," ++
    "\"entry_order\":\"path_ascending\"," ++
    "\"paths\":[\"games/signal-triangulation.json\"]},\n" ++
  "    \"activation_digest\":{\"algorithm\":\"sha256\"," ++
    "\"domain\":\"pathofangels.network/activation-digest/v1\\u0000\"," ++
    "\"framing\":\"schema_len_be64 || schema_utf8 || manifest_sha256_raw32 || curator_pubkey_raw32 || content_epoch_be64 || counter_be64 || signature_raw64\"," ++
    "\"location\":\"detached verified activation; excluded from manifest preimage\"},\n" ++
  "    \"unknown_fields\":\"reject\",\n" ++
  "    \"unknown_artifacts\":\"reject\"\n" ++
  "  }\n" ++
  "}\n"

def canonicalArtifacts (federationId sourceDigest contentDigest contentRoot : Digest32) :
    List ArtifactBytes :=
  [ { path := "schema.json", mediaType := "application/schema+json", contents := schemaJson }
  , { path := "catalog.json", mediaType := "application/json",
      contents := catalogJson federationId sourceDigest contentDigest contentRoot }
  , { path := "games/signal-triangulation.json", mediaType := "application/json",
      contents := signalDescriptorJson } ]

/-! SHA-256 is a deployed crypto primitive rather than a theorem implemented in
this emitter.  The driver measures these three exact Lean-rendered byte strings;
the signed content epoch anchors the resulting manifest. -/
structure ArtifactHashes where
  schema : String
  catalog : String
  signal : String
deriving DecidableEq, Repr

def ArtifactHashes.valid (h : ArtifactHashes) : Bool :=
  validSha256 h.schema && validSha256 h.catalog && validSha256 h.signal

def canonicalPins (federationId sourceDigest contentDigest contentRoot : Digest32)
    (hashes : ArtifactHashes) : List ArtifactPin :=
  match canonicalArtifacts federationId sourceDigest contentDigest contentRoot with
  | [schema, catalog, signal] =>
      [schema.pin hashes.schema, catalog.pin hashes.catalog, signal.pin hashes.signal]
  | _ => []

def manifestFor (sourceDigestString : String)
    (federationId sourceDigest contentDigest contentRoot : Digest32)
    (hashes : ArtifactHashes) : Manifest :=
  { format := FORMAT
    schemaVersion := SCHEMA_VERSION
    sourceDigest := sourceDigestString
    authority := AUTHORITY
    artifacts := canonicalPins federationId sourceDigest contentDigest contentRoot hashes }

/-- A manifest is accepted only if it is exactly the one reconstructed from the
Lean-owned artifact bytes and the externally measured full-width source digest. -/
def acceptsManifest (sourceDigestString : String)
    (federationId sourceDigest contentDigest contentRoot : Digest32)
    (hashes : ArtifactHashes) (candidate : Manifest) : Bool :=
  validSha256 sourceDigestString &&
    hashes.valid &&
    decide (digestHex sourceDigest = sourceDigestString) &&
    decide (digestHex contentDigest = hashes.signal) &&
    decide (candidate =
      manifestFor sourceDigestString federationId sourceDigest contentDigest contentRoot hashes)

theorem acceptsManifest_eq_true_iff
    (sourceDigestString : String) (federationId sourceDigest contentDigest contentRoot : Digest32)
    (hashes : ArtifactHashes) (candidate : Manifest) :
    acceptsManifest sourceDigestString federationId sourceDigest contentDigest contentRoot hashes candidate =
      true ↔
      validSha256 sourceDigestString = true ∧
      hashes.valid = true ∧
      digestHex sourceDigest = sourceDigestString ∧
      digestHex contentDigest = hashes.signal ∧
      candidate =
        manifestFor sourceDigestString federationId sourceDigest contentDigest contentRoot hashes := by
  simp [acceptsManifest, and_assoc]

/-- Parse plus exact reconstruction.  A parse error, version drift, field drift,
pin mismatch, reordered file, unknown file, or source mismatch is an error. -/
def ingestManifest (sourceDigestString : String)
    (federationId sourceDigest contentDigest contentRoot : Digest32)
    (hashes : ArtifactHashes) (bytes : String) : Except String Manifest := do
  let parsed ← parseManifest bytes
  if acceptsManifest sourceDigestString federationId sourceDigest contentDigest contentRoot hashes parsed then
    pure parsed
  else
    throw "POAG1 manifest does not exactly match the Lean-emitted bundle"

theorem ingestManifest_exact
    (sourceDigestString : String) (federationId sourceDigest contentDigest contentRoot : Digest32)
    (hashes : ArtifactHashes) (bytes : String) (accepted : Manifest)
    (h : ingestManifest sourceDigestString federationId sourceDigest contentDigest contentRoot hashes bytes =
      .ok accepted) :
    accepted =
      manifestFor sourceDigestString federationId sourceDigest contentDigest contentRoot hashes := by
  cases hm : parseManifest bytes with
  | error err =>
      simp only [ingestManifest, hm, bind, Except.bind] at h
      contradiction
  | ok parsed =>
      simp only [ingestManifest, hm, bind, Except.bind] at h
      split at h
      · rename_i ha
        injection h with h
        subst accepted
        exact (acceptsManifest_eq_true_iff _ _ _ _ _ _ _).mp ha |>.2.2.2.2
      · contradiction

#assert_axioms acceptsManifest_eq_true_iff
#assert_axioms ingestManifest_exact

end Dregg2.Games.PathOfAngels.Emit
