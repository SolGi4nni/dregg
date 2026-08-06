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
import Dregg2.Games.PathOfAngels.FiniteTables
import Dregg2.Games.PathOfAngels.BlackBoxReconstruction
import Dregg2.Games.PathOfAngels.HiddenInstance
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

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

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

/-! ## The instance is drawn per run, and no artifact carries it

⚠ `signalRunSeed`, `signalTarget`, `signalTarget_from_runSeed` and
`signalTarget_literal` are GONE, and so are `relayRunSeed`, `relayBoardIndex`,
`relayBoard`, `salvageRunSeed` and `salvageSeed` below.

Deleting the descriptor's `"target"` field alone would have closed nothing.  The
run seed was published in the descriptor AND in the catalog, and
`targetFromSeed` is public: a reader computed `[2,4,1]` either way.  The seed had
to stop being a constant, so it did.  `MissionSpec.runSeed` is now supplied per
run by `HiddenInstance.runSeedFor` from a slot secret the curator commits to
before the slot opens and opens after it closes.

Missions rendered into an artifact therefore carry `UNBOUND_RUN_SEED`, which is
not a seed and draws nothing.  A judge that is handed it produces the instance of
the all-zero seed, which is why `Judged.admissionChecks` requires the live seed to
equal the derivation and refuses this value outright. -/

/-- The run-seed slot of a template mission: thirty-two zero bytes, meaning "no
live draw has happened".  It is emitted nowhere; it exists so `MissionSpec` stays
total in the catalog. -/
def UNBOUND_RUN_SEED : Digest32 := taggedBytes32 []

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

/-! ### The rules, as the WHOLE oracle

The old descriptor carried `outcomes`: 216 rows of feedback against ONE target,
with the solving row flagged.  That table is the answer written out.

What is emitted instead is the complete function — a 216 by 216 table of feedback
classes, row indexed by target and column by guess.  It states every rule and
distinguishes no instance: every row solves at exactly its own index
(`signal_every_row_solves_at_exactly_its_own_index`), so the table is symmetric
under which row is live.  A real run learns one class per guess from the judge; a
practice run reads its own row, because it chose it.

Rows are strings over `class_alphabet`, one character per cell.  A cell the class
list cannot name renders `?`, and `validateSignalDescriptor` refuses it, so a
silent fold is impossible. -/

/-- The realizable feedback classes, generated in canonical `(exact, present)`
order and filtered by realizability against an all-distinct target — the richest
instance, which is why filtering against it does not lose a class.
`signalClassPairs_complete` is the check over the whole 216-by-216 domain. -/
def signalClassPairs : List (Nat × Nat) :=
  ((List.range 4).flatMap fun e => (List.range 4).map fun p => (e, p)).filter fun c =>
    signalAllCodes.any fun g =>
      let f := SignalTriangulation.feedback { low := 0, mid := 1, high := 2 } g
      f.exact == c.1 && f.present == c.2

abbrev SIGNAL_CLASS_ALPHABET : String := "0123456789"

/-- The character naming a feedback class.  `?` for a class the list cannot name;
the validator refuses that character, so the failure is loud rather than folded. -/
def signalClassChar (f : SignalTriangulation.Feedback) : Char :=
  match signalClassPairs.findIdx? (fun c => c.1 == f.exact && c.2 == f.present) with
  | some i => SIGNAL_CLASS_ALPHABET.toList.getD i '?'
  | none => '?'

def signalRulesRow (target : SignalTriangulation.Code) : String :=
  String.ofList (signalAllCodes.map fun g =>
    signalClassChar (SignalTriangulation.feedback target g))

def signalRulesTable : List String := signalAllCodes.map signalRulesRow

/-- Decode a rendered class character back to the `solved` bit its class carries.
`none` for a character `class_alphabet` does not name — a `?` cell decodes to a
REFUSAL, not to `false`, so a silent fold cannot survive the decode either. -/
def signalClassSolved? (c : Char) : Option Bool :=
  match SIGNAL_CLASS_ALPHABET.toList.findIdx? (fun a => a == c) with
  | some i => (signalClassPairs[i]?).map fun pair => pair.1 == 3
  | none => none

/-- The cell an emitted descriptor actually carries at (target, guess): row indexed by
the target's position in `rules.codes`, column by the guess's — exactly the lookup
`transition.on_submit` (`"rules.table[instance][guess]"`) tells a client to perform.
This reads the EMITTED table; it does not recompute `signalClassChar`. -/
def signalRulesCell (target guess : SignalTriangulation.Code) : Option Char :=
  match signalAllCodes.findIdx? (fun c => c == target),
        signalAllCodes.findIdx? (fun c => c == guess) with
  | some r, some c => (signalRulesTable[r]?).bind fun row => row.toList[c]?
  | _, _ => none

theorem signalClassPairs_length : signalClassPairs.length = 9 := by
  native_decide

/-- No cell of the emitted table is `?`: the nine classes name every feedback the
rules can produce over the complete 216-by-216 domain. -/
theorem signalClassPairs_complete :
    (signalAllCodes.all fun t => signalAllCodes.all fun g =>
      signalClassPairs.contains
        ((SignalTriangulation.feedback t g).exact,
         (SignalTriangulation.feedback t g).present)) = true := by
  native_decide

theorem signalRulesTable_length : signalRulesTable.length = 216 := by
  simp [signalRulesTable, signalAllCodes]

/-- ⚑ Every row of the emitted table solves at exactly one column, and that column
is the row's own index.  The table therefore names no instance: it is the whole
function, and no field of it distinguishes the live row. -/
theorem signal_every_row_solves_at_exactly_its_own_index :
    (signalAllCodes.all fun t =>
      (signalAllCodes.filter fun g => (SignalTriangulation.feedback t g).exact == 3).length == 1)
      = true := by
  native_decide

/-- The kernel fact underneath the table.  ⚠ RENAMED 2026-08-05: this carried the name
`signalClass_matches_step` and a docstring claiming the emitted cell agrees with the
kernel step, while its statement mentioned neither `signalRulesTable` nor
`signalClassChar` nor the descriptor.  It is a fact about `SignalTriangulation` alone,
and it is now named that.  The claim the old name made is
`signalRulesCell_matches_step` below, and it is proved. -/
theorem step_solved_is_exact_three (cfg : SignalTriangulation.Config)
    (s : SignalTriangulation.State) (guess : SignalTriangulation.Code)
    (hopen : SignalTriangulation.openB s = true) :
    (SignalTriangulation.step cfg s (.submit guess)).map (·.solved) =
      some ((SignalTriangulation.feedback cfg.target guess).exact == 3) := by
  simp [SignalTriangulation.step, hopen]

/-- Over the WHOLE 216-by-216 domain, the cell the emitted table carries — read the way
a client reads it, and decoded through the emitted alphabet — is exactly the kernel's
own `solved` bit.  Finite and total, so it is `native_decide`; the ∀-form below carries
it off the list. -/
theorem signalRulesTable_cells_decode_to_the_kernel_bit :
    (signalAllCodes.all fun t => signalAllCodes.all fun g =>
      (signalRulesCell t g).bind signalClassSolved? ==
        some ((SignalTriangulation.feedback t g).exact == 3)) = true := by
  native_decide

theorem signalRulesCell_decodes_to_the_kernel_bit
    (target guess : SignalTriangulation.Code) :
    (signalRulesCell target guess).bind signalClassSolved? =
      some ((SignalTriangulation.feedback target guess).exact == 3) := by
  have h := signalRulesTable_cells_decode_to_the_kernel_bit
  simp only [List.all_eq_true] at h
  have hrow := h target (signalAllCodes_complete target)
  simp only [List.all_eq_true] at hrow
  simpa using hrow guess (signalAllCodes_complete guess)

/-- ⚑ **The emitted cell IS the rule.**  What a client reads out of `rules.table` at
(its instance row, its guess column) and decodes through `class_alphabet` is exactly
the `solved` bit `SignalTriangulation.step` computes, from every open state.  This is
the statement the descriptor's `transition.on_submit` clause promises, made about the
actually emitted table rather than about `feedback` on its own. -/
theorem signalRulesCell_matches_step (cfg : SignalTriangulation.Config)
    (s : SignalTriangulation.State) (guess : SignalTriangulation.Code)
    (hopen : SignalTriangulation.openB s = true) :
    (SignalTriangulation.step cfg s (.submit guess)).map (·.solved) =
      (signalRulesCell cfg.target guess).bind signalClassSolved? := by
  rw [signalRulesCell_decodes_to_the_kernel_bit]
  exact step_solved_is_exact_three cfg s guess hopen

#assert_compiled signalAllCodes_length
#assert_compiled signalAllCodes_nodup
#assert_axioms signalAllCodes_complete
#assert_axioms signalRulesTable_length
#assert_axioms step_solved_is_exact_three
#assert_compiled signalRulesTable_cells_decode_to_the_kernel_bit
#assert_compiled signalRulesCell_decodes_to_the_kernel_bit
#assert_compiled signalRulesCell_matches_step
#assert_compiled signalClassPairs_length
#assert_compiled signalClassPairs_complete
#assert_compiled signal_every_row_solves_at_exactly_its_own_index

private def signalCodeJson (c : SignalTriangulation.Code) : String :=
  "[" ++ toString c.low.val ++ "," ++ toString c.mid.val ++ "," ++
    toString c.high.val ++ "]"

private def signalClassJson (c : Nat × Nat) : String :=
  "{\"exact\":" ++ toString c.1 ++ ",\"present\":" ++ toString c.2 ++
    ",\"solved\":" ++ jsonBool (c.1 == 3) ++ "}"

/-- The declaration every hidden-instance descriptor carries in place of its
instance.  It states WHERE the instance comes from and what a client must verify
before a run is scored; it states no value from which one can be computed.

The per-slot commitment itself is NOT in this artifact and cannot be: the bundle
is signed once per content epoch and slots open afterwards.  It is published per
slot in the run opening, whose shape `schemaJson` pins, and a client refuses a run
whose opening does not carry a curator-signed commitment for the slot it claims. -/
private def instanceDeclarationJson (disclosure : String) : String :=
  "{\"kind\":\"per-run-hidden-draw\"" ++
  ",\"derivation_module\":\"Dregg2.Games.PathOfAngels.HiddenInstance\"" ++
  ",\"disclosure\":" ++ jsonString disclosure ++
  ",\"commitment\":{\"published_in\":\"slot-opening\",\"domain\":\"POAC\"," ++
    "\"preimage\":[\"domain\",\"slot\",\"slot_secret\"]," ++
    "\"binding_bits\":124,\"opened_after\":\"slot-close\"}" ++
  ",\"draw\":{\"domain\":\"POAD\"," ++
    "\"preimage\":[\"domain\",\"purpose\",\"slot\",\"mission_id\",\"epoch\"," ++
      "\"slot_secret\",\"federation_id\",\"content_session\",\"player_key\"]," ++
    "\"purposes\":{\"judged\":1,\"practice\":2}}" ++
  ",\"sponge\":{\"permutation\":\"poseidon2-babybear-w16\",\"width\":16,\"rate\":8," ++
    "\"capacity\":8,\"lane_bytes\":1,\"lane_reject_at_or_above\":2013265920," ++
    "\"squeeze_blocks\":6}" ++
  ",\"practice\":{\"seed\":\"client-chosen\",\"scored\":false," ++
    "\"purpose_tag\":2,\"transcript_field\":\"mode\"}" ++
  ",\"operator_knows_instance\":true}"

def signalDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"signal-triangulation\",\n" ++
  "  \"ruleset\":\"signal-v2\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.SignalTriangulation\",\n" ++
  "  \"action_limit\":" ++ toString SignalTriangulation.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" ++ ",\n" ++
  "  \"state\":{\"fields\":[\"turns\",\"solved\",\"last_feedback\"]},\n" ++
  "  \"action\":{\"tag\":\"submit\",\"code\":{\"bands\":3,\"alphabet\":6}},\n" ++
  "  \"feedback\":{\"exact_max\":3,\"present_max\":3,\"exact_plus_present_max\":3," ++
    "\"present_semantics\":\"multiplicity_intersection_minus_exact\",\"solved_when_exact\":3},\n" ++
  "  \"transition\":{\"open_when\":{\"solved\":false,\"turns_lt\":5}," ++
    "\"on_submit\":{\"lookup\":\"rules.table[instance][guess]\",\"turns\":\"increment\"," ++
    "\"solved\":\"class.solved\",\"last_feedback\":[\"class.exact\",\"class.present\"]}," ++
    "\"refuse_when\":[\"solved\",\"turns_gte_action_limit\"]},\n" ++
  "  \"output\":{\"requires\":\"solved\",\"contribution\":\"mission_reward\",\"artifact\":\"mission_artifact\"},\n" ++
  "  \"rules\":{\"class_alphabet\":" ++ jsonString SIGNAL_CLASS_ALPHABET ++
    ",\"classes\":" ++ jsonArray (signalClassPairs.map signalClassJson) ++
    ",\"codes\":" ++ jsonArray (signalAllCodes.map signalCodeJson) ++
    ",\"table\":" ++ jsonPrettyArray (signalRulesTable.map fun row => "    " ++ jsonString row) ++
    "}\n" ++
  "}\n"

/-! ## Finite-table descriptors -/

/-! ### Two demonstration secrets, and what they refute

The descriptor is a constant.  Proving "a constant does not depend on the seed" is
`rfl` and says nothing, so the claim is made the other way round: with everything
an artifact carries held FIXED — mission, federation, content session, slot,
player — two slot secrets draw two different instances.  A reader of the artifact
therefore cannot name the instance, not even up to the domain.

These are demonstration values.  They are not the deployment's secrets: a
deployment secret never enters this module, and there is no function here that
would render one. -/

private def demoSecret (tag : Nat) : HiddenInstance.SlotSecret :=
  ⟨taggedBytes32 [68, 69, 77, 79, tag]⟩

private def demoPlayer : Digest32 := taggedBytes32 [80, 76, 65, 89, 69, 82]
private def demoSlot : EpochId := ⟨11⟩

/-- The live seed a run would draw.  `mission` is the template the catalog carries,
so every published value is fixed and only the secret moves. -/
private def demoLiveSeed (mission : MissionSpec) (tag : Nat) : Digest32 :=
  HiddenInstance.runSeedFor ⟨demoSecret tag, demoSlot, demoPlayer⟩
    (HiddenInstance.MissionContext.ofMission mission)

private def relayStateJson (board : RelayRepair.Board) (state : RelayRepair.State) : String :=
  "    {\"id\":" ++ jsonString (FiniteTables.relayStateId state) ++
    ",\"terminal\":" ++ jsonBool (RelayRepair.routedB state.panel) ++
    ",\"view\":{\"installed\":" ++
      jsonArray ((FiniteTables.relayInstalledActionIds state.panel).map jsonString) ++
    ",\"spares\":" ++ toString (RelayRepair.sparesLeft board state.panel) ++
    ",\"turns\":" ++ toString state.turns ++
    ",\"solved\":" ++ jsonBool (RelayRepair.routedB state.panel) ++
    ",\"stranded\":" ++ jsonBool (RelayRepair.strandedB board state) ++ "}}"

private def relayActionJson (action : RelayRepair.Action) : String :=
  "    {\"id\":" ++ jsonString (FiniteTables.relayActionId action) ++
    ",\"label\":" ++ jsonString (FiniteTables.relayActionLabel action) ++
    ",\"from\":" ++ jsonString (FiniteTables.relayActionFrom action) ++
    ",\"to\":" ++ jsonString (FiniteTables.relayActionTo action) ++ "}"

private def relayTransitionJson (board : RelayRepair.Board)
    (transition : FiniteTables.RelayTransition) : String :=
  let nextId := transition.next.map FiniteTables.relayStateId
  let reason := FiniteTables.relayRefusalReason board transition.state transition.action
  "    {\"state\":" ++ jsonString (FiniteTables.relayStateId transition.state) ++
    ",\"action\":" ++ jsonString (FiniteTables.relayActionId transition.action) ++
    ",\"verdict\":" ++ jsonString (if nextId.isSome then "accept" else "refuse") ++
    ",\"next\":" ++ (match nextId with | none => "null" | some id => jsonString id) ++
    ",\"reason\":" ++ (match reason with | none => "null" | some value => jsonString value) ++ "}"

private def relayBoardJson (index : Nat) (board : RelayRepair.Board) : String :=
  "    {\"index\":" ++ toString index ++
    ",\"spares\":" ++ toString board.spares ++
    ",\"costs\":{" ++ String.intercalate "," (FiniteTables.relayActions.map fun action =>
      jsonString (FiniteTables.relayActionId action) ++ ":" ++
        toString (RelayRepair.cost board action)) ++ "}}"

/-- The whole board FAMILY and no draw.  ⚠ `seed_byte` and `selected` are GONE:
they said which board was live, and the run seed they were answerable to was
published beside them, so between them they printed the instance twice.

Relay is a perfect-information puzzle — its player has to read the damage report
to play at all — so its instance is DISCLOSED, to its own player, at run start,
through the run opening.  What the split changes is that it is disclosed per run
instead of printed once for everyone, which is what kills the memorised line.  The
family stays public because the family is the rules. -/
private def relayInstanceJson : String :=
  "{\"modulus\":8" ++
    ",\"source\":\"alpha\",\"sink\":\"omega\"" ++
    ",\"draw\":" ++ instanceDeclarationJson "per-run-open" ++
    ",\"boards\":" ++ jsonPrettyArray
      ((List.finRange 8).map fun index =>
        relayBoardJson index.val (RelayRepair.boardAt index)) ++
    "}"

private def relayMachineJson (index : Fin 8) : String :=
  let board := RelayRepair.boardAt index
  let states := FiniteTables.relayStates board
  let transitions := FiniteTables.relayTransitions board
  "    {\"board\":" ++ toString index.val ++
    ",\"states\":" ++ jsonPrettyArray (states.map (relayStateJson board)) ++
    ",\"transitions\":" ++
      jsonPrettyArray (transitions.map (relayTransitionJson board)) ++ "}"

def relayDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"relay-repair\",\n" ++
  "  \"ruleset\":\"relay-v3\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.RelayRepair\",\n" ++
  "  \"action_limit\":" ++ toString RelayRepair.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"per-run-open\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ relayInstanceJson ++ ",\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (FiniteTables.relayStateId RelayRepair.initialState) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (FiniteTables.relayActions.map relayActionJson) ++ ",\n" ++
  "    \"machines\":" ++
    jsonPrettyArray ((List.finRange 8).map relayMachineJson) ++ "\n" ++
  "  },\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

private def salvageStateJson (state : SalvageLock.State) : String :=
  let exposed := match state.exposed with
    | none => "null"
    | some slot => toString slot.val
  "    {\"id\":" ++ jsonString (FiniteTables.salvageStateId state) ++
    ",\"terminal\":" ++ jsonBool (SalvageLock.solvedB state) ++
    ",\"view\":{\"cleared\":" ++
      jsonArray ((FiniteTables.salvageClearedSlots state).map (toString ·.val)) ++
    ",\"exposed\":" ++ exposed ++
    ",\"turns\":" ++ toString state.turns ++
    ",\"solved\":" ++ jsonBool (SalvageLock.solvedB state) ++ "}}"

/-- ⚠ `glyph_id` and `glyph_label` are GONE.  They named the glyph under each
plate, which is the whole board.  Removing them alone would have hidden nothing —
the successors said which exposures clear — which is why the transition rows below
changed shape at the same time. -/
private def salvageActionJson (action : SalvageLock.Action) : String :=
  "    {\"id\":" ++ jsonString (FiniteTables.salvageActionId action) ++
    ",\"label\":" ++ jsonString (FiniteTables.salvageActionLabel action) ++
    ",\"slot\":" ++ toString (SalvageLock.actionSlot action).val ++ "}"

/-- A parametric row.  `refuse` carries a reason and no successor; `accept` is a
first exposure and carries one; `resolve` is a second exposure and carries BOTH,
so the row states the rule and the judge's single bit states the instance. -/
private def salvageTransitionJson (transition : FiniteTables.ParametricTransition) : String :=
  let stateId := jsonString (FiniteTables.salvageStateId transition.state)
  let actionId := jsonString (FiniteTables.salvageActionId transition.action)
  let head :=
    "    {\"state\":" ++ stateId ++ ",\"action\":" ++ actionId ++ ",\"verdict\":"
  match transition.row with
  | .refuse reason =>
      head ++ "\"refuse\",\"reason\":" ++ jsonString reason ++
        ",\"next\":null,\"on_match\":null,\"on_mismatch\":null}"
  | .advance next =>
      head ++ "\"accept\",\"reason\":null,\"next\":" ++
        jsonString (FiniteTables.salvageStateId next) ++
        ",\"on_match\":null,\"on_mismatch\":null}"
  | .resolve onMatch onMismatch =>
      head ++ "\"resolve\",\"reason\":null,\"next\":null,\"on_match\":" ++
        jsonString (FiniteTables.salvageStateId onMatch) ++
        ",\"on_mismatch\":" ++ jsonString (FiniteTables.salvageStateId onMismatch) ++ "}"

/-- The whole ninety-board FAMILY, emitted so a browser can answer its OWN
practice run without carrying a second copy of `pairsOf` and `glyphNamesOf`.

Publishing the family is not publishing the instance.  The family was already
public — "six plates carrying two copies of each of three glyphs" determines it
completely, and `SalvageLock.seed_space_is_exactly_the_two_of_each_boards` proves
the ninety are exactly those boards.  What a reader cannot do is say which one a
given run drew.

A practice run picks a row here under a client-chosen seed and answers its own
match queries from it.  A judged run never touches this block: its bit comes from
the judge. -/
private def salvagePracticeBoardsJson : String :=
  jsonPrettyArray ((List.finRange SalvageLock.SEED_SPACE).map fun seed =>
    "    " ++ jsonArray ((SalvageLock.boardRow seed).map (toString ·.val)))

def salvageDescriptorJson : String :=
  let states := FiniteTables.salvageParametricStates
  let actions := FiniteTables.salvageActions
  let transitions := FiniteTables.salvageParametricTransitions
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"salvage-lock\",\n" ++
  "  \"ruleset\":\"salvage-v2\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.SalvageLock\",\n" ++
  "  \"action_limit\":" ++ toString SalvageLock.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" ++ ",\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (FiniteTables.salvageStateId SalvageLock.initialState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map salvageStateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (actions.map salvageActionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (transitions.map salvageTransitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"practice\":{\"instance_space\":" ++ toString SalvageLock.SEED_SPACE ++
    ",\"instance_shape\":\"two copies of each of three glyphs over six plates\"" ++
    ",\"scored\":false" ++
    ",\"boards\":" ++ salvagePracticeBoardsJson ++ "},\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

/-! ## Black Box Reconstruction — the ORACLE wire

Signal publishes a code-by-code feedback table; Salvage publishes a machine whose
second exposures name both branches.  Black Box can use neither shape.  Its state
is the SET of pairs a run has asked, so a total `(state, action)` table would have
`2^25` rows and cannot be written down at all.

What is small is the thing that actually matters: the ORACLE.  120 instances by 25
probes is 3000 cells, and those cells ARE the rules.  So the descriptor publishes
the complete question-and-answer function and says nothing whatever about which row
a given run drew — the client learns every rule and no instance.

`blackBox_table_is_the_kernel` reads the cells back out of the RENDERED descriptor
and compares each one against `BlackBoxReconstruction.hitB`, so the emitted table is
a projection of the kernel and not a second copy of the rules. -/

private def blackBoxProbes :
    List (BlackBoxReconstruction.Slot × BlackBoxReconstruction.Fragment) :=
  BlackBoxReconstruction.allSlots.flatMap fun slot =>
    BlackBoxReconstruction.allFragments.map fun fragment => (slot, fragment)

private def blackBoxProbeId
    (probe : BlackBoxReconstruction.Slot × BlackBoxReconstruction.Fragment) : String :=
  "probe-" ++ toString probe.1.val ++ "-" ++ toString probe.2.val

private def blackBoxProbeJson
    (probe : BlackBoxReconstruction.Slot × BlackBoxReconstruction.Fragment) : String :=
  "    {\"id\":" ++ jsonString (blackBoxProbeId probe) ++
    ",\"label\":" ++ jsonString ("Ask whether fragment " ++ toString probe.2.val ++
      " belongs at position " ++ toString probe.1.val) ++
    ",\"slot\":" ++ toString probe.1.val ++
    ",\"fragment\":" ++ toString probe.2.val ++ "}"

/-- One instance's answers to every probe, in `blackBoxProbes` order. -/
private def blackBoxOracleRow (order : Fin BlackBoxReconstruction.ORDER_SPACE) : String :=
  String.mk (blackBoxProbes.map fun probe =>
    if BlackBoxReconstruction.hitB order probe then '1' else '0')

private def blackBoxOracleTableJson : String :=
  jsonPrettyArray ((List.finRange BlackBoxReconstruction.ORDER_SPACE).map fun order =>
    "    " ++ jsonString (blackBoxOracleRow order))

def blackBoxDescriptorJson : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"black-box-reconstruction\",\n" ++
  "  \"ruleset\":\"blackbox-v2\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.BlackBoxReconstruction\",\n" ++
  "  \"action_limit\":" ++ toString BlackBoxReconstruction.MAX_TURNS ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" ++ ",\n" ++
  "  \"oracle\":{\n" ++
  "    \"instance_space\":" ++ toString BlackBoxReconstruction.ORDER_SPACE ++ ",\n" ++
  "    \"instance_shape\":\"a permutation of five fragments over five positions\",\n" ++
  "    \"required_per_instance\":" ++ toString BlackBoxReconstruction.SLOT_COUNT ++ ",\n" ++
  "    \"settles\":\"slot-and-fragment\",\n" ++
  "    \"class_alphabet\":\"01\",\n" ++
  "    \"classes\":[{\"id\":\"mismatch\",\"solving\":false}," ++
    "{\"id\":\"match\",\"solving\":true}],\n" ++
  "    \"probes\":" ++ jsonPrettyArray (blackBoxProbes.map blackBoxProbeJson) ++ ",\n" ++
  "    \"table\":" ++ blackBoxOracleTableJson ++ "\n" ++
  "  },\n" ++
  "  \"refusals\":[\"solved\",\"turn-limit\",\"repeated-probe\",\"settled-slot\"," ++
    "\"settled-fragment\"],\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

/-! Strict schema checks for the exact finite-table wire. -/

/-! ⚠ `run_seed` is no longer a descriptor key and `target_visibility` is no longer
a security key; `instance` is now required of every game.  The validators below
refuse the old shape rather than reinterpreting it, so a stale artifact fails to
load instead of being read as a hidden-instance one. -/

/-- The instance declaration is schema, not a free-form annex.  A descriptor that
carries no declaration, or one whose commitment or draw block has drifted, is a
parse error — this is the field that says the answer is elsewhere, so it is not
allowed to be optional. -/
private def validateInstanceDeclaration (block : Json) (disclosure : String) :
    Except String Unit := do
  exactKeys block ["kind", "derivation_module", "disclosure", "commitment", "draw",
    "sponge", "practice", "operator_knows_instance"]
  if (← block.getObjValAs? String "kind") != "per-run-hidden-draw" then
    throw "POAG1 instance declaration is not a per-run hidden draw"
  if (← block.getObjValAs? String "disclosure") != disclosure then
    throw s!"POAG1 instance disclosure is not {disclosure}"
  exactKeys (← block.getObjVal? "commitment")
    ["published_in", "domain", "preimage", "binding_bits", "opened_after"]
  exactKeys (← block.getObjVal? "draw") ["domain", "preimage", "purposes"]
  exactKeys (← block.getObjVal? "sponge")
    ["permutation", "width", "rate", "capacity", "lane_bytes",
     "lane_reject_at_or_above", "squeeze_blocks"]
  exactKeys (← block.getObjVal? "practice")
    ["seed", "scored", "purpose_tag", "transcript_field"]

private def validateHiddenSecurity (j : Json) (visibility : String) :
    Except String Unit := do
  let security ← j.getObjVal? "security"
  exactKeys security ["classification", "instance_visibility", "competitive_rewards",
    "economic_rewards"]
  if (← security.getObjValAs? String "instance_visibility") != visibility then
    throw s!"POAG1 descriptor does not declare instance_visibility {visibility}"

private def validateRelayTransitions (machine : Json) : Except String Unit := do
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "next", "reason"]

/-- ⚠ `seed_byte` and `selected` are refused, not ignored.  A relay descriptor that
still names a drawn board is the old shape and must not load. -/
private def validateRelayInstance (document : Json) : Except String Unit := do
  let block ← document.getObjVal? "instance"
  exactKeys block ["modulus", "source", "sink", "draw", "boards"]
  validateInstanceDeclaration (← block.getObjVal? "draw") "per-run-open"
  let modulus ← block.getObjValAs? Nat "modulus"
  let boards ← (block.getObjVal? "boards") >>= Json.getArr?
  if boards.size != modulus then
    throw s!"POAG1 relay instance declares {boards.size} boards for modulus {modulus}"
  let linkIds := FiniteTables.relayActions.map FiniteTables.relayActionId
  for board in boards do
    exactKeys board ["index", "spares", "costs"]
    exactKeys (← board.getObjVal? "costs") linkIds

def validateRelayDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  -- Relay's declaration lives inside `instance.draw`, so the outer instance block
  -- is checked by `validateRelayInstance` and the common check is told the shape.
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "state_machine", "output"]
  validateHiddenSecurity document "per-run-open"
  validateRelayInstance document
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "actions", "machines"]
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  for action in actions do
    exactKeys action ["id", "label", "from", "to"]
  let machines ← (machine.getObjVal? "machines") >>= Json.getArr?
  if machines.size != 8 then
    throw s!"POAG1 relay emits {machines.size} board machines, expected 8"
  for board in machines do
    exactKeys board ["board", "states", "transitions"]
    let states ← (board.getObjVal? "states") >>= Json.getArr?
    for state in states do
      exactKeys state ["id", "terminal", "view"]
      exactKeys (← state.getObjVal? "view")
        ["installed", "spares", "turns", "solved", "stranded"]
    validateRelayTransitions board

def validateSalvageDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "state_machine", "practice", "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  let practice ← document.getObjVal? "practice"
  exactKeys practice ["instance_space", "instance_shape", "scored", "boards"]
  let space ← practice.getObjValAs? Nat "instance_space"
  let boards ← (practice.getObjVal? "boards") >>= Json.getArr?
  if boards.size != space then
    throw s!"POAG1 salvage practice block emits {boards.size} boards for a space of {space}"
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "states", "actions", "transitions"]
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  for state in states do
    exactKeys state ["id", "terminal", "view"]
    exactKeys (← state.getObjVal? "view") ["cleared", "exposed", "turns", "solved"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  for action in actions do
    -- No `glyph_id`: an action row that carries one is the old shape and refuses.
    exactKeys action ["id", "label", "slot"]
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "reason", "next",
      "on_match", "on_mismatch"]

/-- Black Box publishes an `oracle` block instead of a `state_machine`: its state
space is a subset lattice and no total transition table exists for it.  The key set
is pinned exactly, like every other descriptor here. -/
def validateBlackBoxDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "oracle", "refusals", "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let oracle ← document.getObjVal? "oracle"
  exactKeys oracle ["instance_space", "instance_shape", "required_per_instance",
    "settles", "class_alphabet", "classes", "probes", "table"]
  let space ← oracle.getObjValAs? Nat "instance_space"
  if space != BlackBoxReconstruction.ORDER_SPACE then
    throw s!"POAG1 black-box declares an instance space of {space}"
  let probes ← (oracle.getObjVal? "probes") >>= Json.getArr?
  if probes.size != blackBoxProbes.length then
    throw s!"POAG1 black-box emits {probes.size} probes"
  for probe in probes do
    exactKeys probe ["id", "label", "slot", "fragment"]
  let classes ← (oracle.getObjVal? "classes") >>= Json.getArr?
  if classes.size != 2 then
    throw s!"POAG1 black-box emits {classes.size} observation classes, expected 2"
  for cls in classes do
    exactKeys cls ["id", "solving"]
  let table ← (oracle.getObjVal? "table") >>= Json.getArr?
  if table.size != space then
    throw s!"POAG1 black-box emits {table.size} oracle rows for a space of {space}"

/-- ⚑ **The emitted oracle is the kernel's, cell by cell.**  This reads the table
back out of the RENDERED descriptor — the bytes a client actually fetches — and
compares all 3000 cells against `BlackBoxReconstruction.hitB`.  Without it the
artifact would be an unchecked second statement of the rules. -/
def blackBoxTableRefinesKernel : Except String Unit := do
  let document ← Json.parse blackBoxDescriptorJson
  let oracle ← document.getObjVal? "oracle"
  let table ← (oracle.getObjVal? "table") >>= Json.getArr?
  for order in List.finRange BlackBoxReconstruction.ORDER_SPACE do
    match table[order.val]? with
    | none => throw s!"POAG1 black-box table has no row {order.val}"
    | some cell =>
        let row ← cell.getStr?
        let chars := row.toList
        if chars.length != blackBoxProbes.length then
          throw s!"POAG1 black-box row {order.val} is {chars.length} cells wide"
        for pair in blackBoxProbes.zip chars do
          let emitted := pair.2 == '1'
          if emitted != BlackBoxReconstruction.hitB order pair.1 then
            throw s!"POAG1 black-box cell ({order.val}, {blackBoxProbeId pair.1}) \
              disagrees with the kernel"

/-- Signal's descriptor is validated the same way, with the rules table checked for
the one thing that could silently fold: an unnameable class rendering as `?`. -/
def validateSignalDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "state", "action", "feedback", "transition",
    "output", "rules"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  let rules ← document.getObjVal? "rules"
  exactKeys rules ["class_alphabet", "classes", "codes", "table"]
  let alphabet ← rules.getObjValAs? String "class_alphabet"
  let classes ← (rules.getObjVal? "classes") >>= Json.getArr?
  for cls in classes do
    exactKeys cls ["exact", "present", "solved"]
  let codes ← (rules.getObjVal? "codes") >>= Json.getArr?
  let table ← (rules.getObjVal? "table") >>= Json.getArr?
  if table.size != codes.size then
    throw s!"POAG1 signal rules table has {table.size} rows for {codes.size} codes"
  let allowed := (alphabet.toList.take classes.size)
  for row in table do
    let text ← row.getStr?
    if text.length != codes.size then
      throw "POAG1 signal rules row is not one cell per code"
    if !text.toList.all (fun c => allowed.contains c) then
      throw "POAG1 signal rules table names a class outside the declared alphabet"

theorem relayDescriptor_exact_schema : validateRelayDescriptor relayDescriptorJson = .ok () := by
  native_decide

theorem blackBoxDescriptor_exact_schema :
    validateBlackBoxDescriptor blackBoxDescriptorJson = .ok () := by
  native_decide

theorem blackBox_table_is_the_kernel : blackBoxTableRefinesKernel = .ok () := by
  native_decide

theorem salvageDescriptor_exact_schema :
    validateSalvageDescriptor salvageDescriptorJson = .ok () := by
  native_decide

theorem signalDescriptor_exact_schema :
    validateSignalDescriptor signalDescriptorJson = .ok () := by
  native_decide

#assert_compiled relayDescriptor_exact_schema
#assert_compiled salvageDescriptor_exact_schema
#assert_compiled blackBoxDescriptor_exact_schema
#assert_compiled blackBox_table_is_the_kernel
#assert_compiled signalDescriptor_exact_schema

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

/-- ⚠ `runSeed` is now a PARAMETER.  Missions rendered into the catalog are given
`UNBOUND_RUN_SEED`; a judge is given `HiddenInstance.runSeedFor draw mission`.
There is no longer a mission whose seed is a constant of this module. -/
def signalMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨1⟩
    artifact := signalArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId := federationId
    contentRoot := contentRoot
    activationDigest := activationDigest
    contentSession := signalContentSession
    runSeed := runSeed
    budget := signalBudget
    allowedRelics := {⟨1⟩}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

/-- The draw context of a Signal mission does not depend on its run seed.  Stated on
the ACTUAL emitter and over OPEN digests, so a caller that needs it does not have to
close a `rfl` that would evaluate a digest to check it — which is what a node fixture
deriving its own live seed would otherwise be asking the kernel to do. -/
theorem signalMission_context_ignores_the_run_seed
    (runSeed runSeed' federationId sourceDigest contentDigest contentRoot
      activationDigest : Digest32) :
    HiddenInstance.MissionContext.ofMission
        (signalMission runSeed federationId sourceDigest contentDigest contentRoot
          activationDigest) =
      HiddenInstance.MissionContext.ofMission
        (signalMission runSeed' federationId sourceDigest contentDigest contentRoot
          activationDigest) := rfl

theorem signalReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (signalMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution signalReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  constructor
  · exact signalReward_within
  · simp [signalMission, signalReward]

def signalConfig (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    SignalTriangulation.Config :=
  { target := SignalTriangulation.targetFromSeed runSeed
    mission := signalMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest
    reward := signalReward
    reward_accepted := signalReward_accepted runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest
    target_eq := rfl }

/-- The judged target is the one the LIVE seed draws, for whatever seed the judge
was handed.  The kernel binding did not change; the seed did. -/
theorem signalConfig_target_from_live_seed (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (signalConfig runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).target =
      SignalTriangulation.targetFromSeed
        (signalConfig runSeed federationId sourceDigest contentDigest contentRoot
          activationDigest).mission.runSeed := rfl

/-- ⚑ **The artifact does not determine the code.**  Everything a client fetches is
held fixed here — the same template mission, the same federation, the same content
session, the same slot, the same player — and two slot secrets still draw two
different targets.  This is the statement `signalTarget_literal` could not make,
because there the published seed WAS the answer. -/
theorem signalDescriptor_does_not_determine_the_target :
    SignalTriangulation.targetFromSeed
        (demoLiveSeed (signalMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
          (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) 1) ≠
      SignalTriangulation.targetFromSeed
        (demoLiveSeed (signalMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
          (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) 2) := by
  native_decide

#assert_axioms signalMission_context_ignores_the_run_seed
#assert_axioms signalReward_accepted
#assert_axioms signalConfig_target_from_live_seed
#assert_compiled signalDescriptor_does_not_determine_the_target

def signalPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (signalMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    signalReward
    WorldState.empty

def relayContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 82, 69, 76, 65, 89, 45, 49]

def relayBudget : ContributionBudget :=
  { intel := ⟨10, by decide⟩
    supplies := ⟨40, by decide⟩
    cohesion := ⟨20, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨650, by decide⟩
    relics := ⟨1, by decide⟩ }

def relayReward : Contribution :=
  { intel := ⟨10, by decide⟩
    supplies := ⟨40, by decide⟩
    cohesion := ⟨20, by decide⟩
    influence := ⟨5, by decide⟩
    score := ⟨650, by decide⟩
    relics := {⟨2⟩}
    relics_bounded := by simp [RELIC_LIMIT] }

theorem relayReward_within : relayReward.within relayBudget = true := by
  decide

def relayArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨2⟩
    artifactId := ⟨2⟩
    sourceDigest
    contentDigest }

def relayMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨2⟩
    artifact := relayArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := relayContentSession
    runSeed := runSeed
    budget := relayBudget
    allowedRelics := {⟨2⟩}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem relayReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (relayMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution relayReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨relayReward_within, by simp [relayMission, relayReward]⟩

def relayConfig (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    RelayRepair.Config :=
  { board := RelayRepair.boardAt (RelayRepair.boardFromRunSeed runSeed)
    mission := relayMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest
    reward := relayReward
    reward_accepted := relayReward_accepted runSeed federationId sourceDigest contentDigest
      contentRoot activationDigest
    board_eq := rfl }

/-- The judged board is the one the LIVE seed draws.  A host still cannot reprice
the relay after a transcript; what changed is that the client is not shown which
board is live until its own run opens. -/
theorem relayConfig_board_is_the_live_draw (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (relayConfig runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).board =
      RelayRepair.boardAt (RelayRepair.boardFromRunSeed runSeed) := rfl

/-- ⚑ **The artifact does not determine the board.**  Eight demonstration secrets
against the same published template draw more than one board, so the emitted
family of eight is not a family of one wearing eight hats. -/
theorem relayDescriptor_does_not_determine_the_board :
    (((List.range 8).map fun tag =>
      (RelayRepair.boardFromRunSeed
        (demoLiveSeed (relayMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
          (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)).val).eraseDups.length
      != 1) = true := by
  native_decide

#assert_axioms relayConfig_board_is_the_live_draw
#assert_compiled relayDescriptor_does_not_determine_the_board

def relayPreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (relayMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    relayReward WorldState.empty

def salvageContentSession : Digest32 :=
  taggedBytes32 [80, 79, 65, 45, 83, 65, 76, 86, 65, 71, 69, 45, 49]

def salvageBudget : ContributionBudget :=
  { intel := ⟨30, by decide⟩
    supplies := ⟨25, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨15, by decide⟩
    score := ⟨750, by decide⟩
    relics := ⟨1, by decide⟩ }

def salvageReward : Contribution :=
  { intel := ⟨30, by decide⟩
    supplies := ⟨25, by decide⟩
    cohesion := ⟨10, by decide⟩
    influence := ⟨15, by decide⟩
    score := ⟨750, by decide⟩
    relics := {⟨3⟩}
    relics_bounded := by simp [RELIC_LIMIT] }

theorem salvageReward_within : salvageReward.within salvageBudget = true := by
  decide

def salvageArtifact (sourceDigest contentDigest : Digest32) : ArtifactRef :=
  { missionId := ⟨3⟩
    artifactId := ⟨3⟩
    sourceDigest
    contentDigest }

def salvageMission (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    MissionSpec :=
  { missionId := ⟨3⟩
    artifact := salvageArtifact sourceDigest contentDigest
    epoch := ⟨1⟩
    federationId
    contentRoot
    activationDigest
    contentSession := salvageContentSession
    runSeed := runSeed
    budget := salvageBudget
    allowedRelics := {⟨3⟩}
    privacy := .public
    ballot := .none
    artifact_matches := rfl
    allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT] }

theorem salvageReward_accepted (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    (salvageMission runSeed federationId sourceDigest contentDigest contentRoot
      activationDigest).acceptsContribution salvageReward = true := by
  apply (MissionSpec.acceptsContribution_eq_true_iff _ _).2
  exact ⟨salvageReward_within, by simp [salvageMission, salvageReward]⟩

/-- An `Option`, because a live seed whose byte stream is exhausted before the four
consuming draws finish names NO board.  That case refuses rather than folding to
board zero — the same discipline `SeedDraw` applies one level down. -/
def salvageConfig? (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option SalvageLock.Config :=
  match hseed : SalvageLock.seedFromRunSeed? runSeed with
  | none => none
  | some seed =>
      some
        { seed := seed
          mission := salvageMission runSeed federationId sourceDigest contentDigest contentRoot
            activationDigest
          reward := salvageReward
          reward_accepted := salvageReward_accepted runSeed federationId sourceDigest
            contentDigest contentRoot activationDigest
          seed_eq := hseed.symm }

/-- The board demonstration secret `tag` draws against the published salvage template.
`none` means that secret's byte stream was exhausted before the four consuming draws
finished, which names no board at all. -/
private def demoSalvageBoard? (tag : Nat) : Option Nat :=
  (SalvageLock.seedFromRunSeed?
    (demoLiveSeed (salvageMission UNBOUND_RUN_SEED (taggedBytes32 []) (taggedBytes32 [])
      (taggedBytes32 []) (taggedBytes32 []) (taggedBytes32 [])) tag)).map Fin.val

/-- ⚑ **The artifact does not determine the board.**

⚠ RESTATED 2026-08-05, because the previous form was VACUOUS-COMPATIBLE.  It compared
`Option Nat` values and asked only that the deduped list not be a singleton — which a
mix of `none` and `some` satisfies.  It therefore passed even if every RESOLVING secret
drew the SAME board, provided one secret exhausted its stream.

What is stated now leaves no room for that: every one of the eight demonstration
secrets RESOLVES, so no `none` can stand in for a difference, AND the boards they
resolve to are at least two distinct ones.

(The relay twin `relayDescriptor_does_not_determine_the_board` was checked for the same
defect and does not have it: `RelayRepair.boardFromRunSeed` is total, so its list is
`List Nat` with no `none` to launder.) -/
theorem salvageDescriptor_does_not_determine_the_board :
    ((List.range 8).all fun tag => (demoSalvageBoard? tag).isSome) = true ∧
      2 ≤ ((List.range 8).filterMap demoSalvageBoard?).eraseDups.length := by
  native_decide

def salvagePreview (runSeed : Digest32)
    (federationId sourceDigest contentDigest contentRoot activationDigest : Digest32) :
    Option WorldState :=
  applyContribution
    (salvageMission runSeed federationId sourceDigest contentDigest contentRoot activationDigest)
    salvageReward WorldState.empty

#assert_axioms relayReward_within
#assert_axioms relayReward_accepted
#assert_axioms salvageReward_within
#assert_axioms salvageReward_accepted
#assert_compiled salvageDescriptor_does_not_determine_the_board

structure GameContentDigests where
  signal : Digest32
  relay : Digest32
  salvage : Digest32
deriving DecidableEq

private def missionCatalogJson (mission : MissionSpec) (title engineModule ruleset : String)
    (actionLimit : Nat) (allowedRelics : List RelicId) (descriptorPath : String)
    (disclosure : String) : String :=
  "    {\"mission_id\":" ++ toString mission.missionId.value ++
  ",\"title\":" ++ jsonString title ++
  ",\"engine_module\":" ++ jsonString engineModule ++
  ",\"ruleset\":" ++ jsonString ruleset ++
  ",\"reward_class\":\"non-economic-demo\"" ++
  ",\"action_limit\":" ++ toString actionLimit ++
  ",\"privacy_grade\":" ++ jsonString (privacyGradeTag mission.privacy) ++
  ",\"ballot_regime\":" ++ jsonString (ballotRegimeTag mission.ballot) ++
  ",\"epoch\":" ++ toString mission.epoch.value ++
  ",\"federation_id\":" ++ jsonString (bytes32Hex mission.federationId) ++
  ",\"content_root\":" ++ jsonString (digestHex mission.contentRoot) ++
  ",\"activation\":{\"state\":\"detached-signature-required\"," ++
    "\"digest_source\":\"POA-CONTENT-EPOCH-SIGNATURE-V1\"}" ++
  ",\"content_session\":" ++ jsonString (bytes32Hex mission.contentSession) ++
  /- ⚠ `run_seed` is GONE from the catalog.  It named the instance of every game
  to anyone who fetched the bundle, which is the hole this split closes; a value
  that changes per run cannot live in an artifact signed once per content epoch.
  What is published instead is where the seed comes from. -/
  ",\"instance\":{\"binding\":\"per-run-hidden-draw\",\"disclosure\":" ++
    jsonString disclosure ++
    ",\"derivation_module\":\"Dregg2.Games.PathOfAngels.HiddenInstance\"" ++
    ",\"commitment_published_in\":\"slot-opening\"}" ++
  ",\"budget\":" ++ contributionBudgetJson mission.budget ++
  ",\"allowed_relics\":" ++ jsonArray (allowedRelics.map (toString ·.value)) ++
  ",\"descriptor_path\":" ++ jsonString descriptorPath ++
  ",\"allowed_beta_discoveries\":[" ++ artifactRefJson mission.artifact ++ "]}"

private def previewFixtureJson (id : String) (mission : MissionSpec) (reward : Contribution)
    (relics : List RelicId) (preview : Option WorldState) : String :=
  "    {\"id\":" ++ jsonString id ++
  ",\"mission_id\":" ++ toString mission.missionId.value ++
  ",\"base_world\":" ++ worldStateJsonWith WorldState.empty [] [] ++
  ",\"contribution\":" ++ contributionJsonWithRelics reward relics ++
  ",\"preview_world\":" ++
    (match preview with
     | none => "null"
     | some world => worldStateJsonWith world relics [mission.artifact]) ++ "}"

def catalogJson (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) : String :=
  /- The activation digest necessarily depends on the detached signature over the
  finished manifest, so it cannot occur inside that manifest without a hash cycle.
  Runtime activation replaces this zero only after signature verification. -/
  let inactiveActivation : Digest32 := taggedBytes32 []
  let unbound := UNBOUND_RUN_SEED
  let signal := signalMission unbound federationId sourceDigest digests.signal contentRoot inactiveActivation
  let relay := relayMission unbound federationId sourceDigest digests.relay contentRoot inactiveActivation
  let salvage := salvageMission unbound federationId sourceDigest digests.salvage contentRoot inactiveActivation
  let missions :=
    [ missionCatalogJson signal "Signal Triangulation"
        "Dregg2.Games.PathOfAngels.SignalTriangulation" "signal-v2"
        SignalTriangulation.MAX_TURNS [⟨1⟩] "games/signal-triangulation.json" "oracle-only"
    , missionCatalogJson relay "Relay Repair" "Dregg2.Games.PathOfAngels.RelayRepair"
        "relay-v3" RelayRepair.MAX_TURNS [⟨2⟩] "games/relay-repair.json" "per-run-open"
    , missionCatalogJson salvage "Salvage Lock" "Dregg2.Games.PathOfAngels.SalvageLock"
        "salvage-v2" SalvageLock.MAX_TURNS [⟨3⟩] "games/salvage-lock.json" "oracle-only" ]
  let fixtures :=
    [ previewFixtureJson "signal-solved-preview-v1" signal signalReward [⟨1⟩]
        (signalPreview unbound federationId sourceDigest digests.signal contentRoot inactiveActivation)
    , previewFixtureJson "relay-solved-preview-v1" relay relayReward [⟨2⟩]
        (relayPreview unbound federationId sourceDigest digests.relay contentRoot inactiveActivation)
    , previewFixtureJson "salvage-solved-preview-v1" salvage salvageReward [⟨3⟩]
        (salvagePreview unbound federationId sourceDigest digests.salvage contentRoot inactiveActivation) ]
  "{\n" ++
  "  \"format\":\"POAG1-CATALOG\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"missions\":" ++ jsonPrettyArray missions ++ ",\n" ++
  "  \"fixtures\":" ++ jsonPrettyArray fixtures ++ "\n" ++
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
    "\"paths\":[\"games/relay-repair.json\",\"games/salvage-lock.json\"," ++
      "\"games/signal-triangulation.json\"]},\n" ++
  "    \"activation_digest\":{\"algorithm\":\"sha256\"," ++
    "\"domain\":\"pathofangels.network/activation-digest/v1\\u0000\"," ++
    "\"framing\":\"schema_len_be64 || schema_utf8 || manifest_sha256_raw32 || curator_pubkey_raw32 || content_epoch_be64 || counter_be64 || signature_raw64\"," ++
    "\"location\":\"detached verified activation; excluded from manifest preimage\"},\n" ++
  /- The instance a game is played against is derived per run and appears in no
  artifact.  What a client must be handed before a scored run, and what it must
  refuse without, is pinned here.  The bundle is signed once per content epoch and
  slots open afterwards, so a per-slot commitment cannot live inside it: it is
  published in the slot opening below, curator-signed, and a client that accepts a
  run without one has no binding at all. -/
  "    \"slot_opening\":{\"required\":[\"slot\",\"mission_id\",\"commitment\"," ++
    "\"curator_pubkey\",\"signature\"]," ++
    "\"commitment\":{\"algorithm\":\"poseidon2-babybear-w16\"," ++
      "\"domain\":\"POAC\",\"preimage\":\"domain || slot || slot_secret\"," ++
      "\"binding_bits\":124}," ++
    "\"opened_after_close\":[\"slot\",\"slot_secret\"]," ++
    "\"verify\":\"commit(slot_secret, slot) == commitment\"," ++
    "\"missing_opening\":\"refuse\"},\n" ++
  "    \"run_instance\":{\"derivation_module\":\"Dregg2.Games.PathOfAngels.HiddenInstance\"," ++
    "\"function\":\"runSeedFor(draw, mission)\"," ++
    "\"preimage\":\"POAD || purpose || slot || mission_id || epoch || slot_secret " ++
      "|| federation_id || content_session || player_key\"," ++
    "\"purposes\":{\"judged\":1,\"practice\":2}," ++
    "\"published_anywhere\":false," ++
    "\"operator_knows_instance\":true," ++
    "\"practice\":{\"seed\":\"client-chosen\",\"scored\":false," ++
      "\"transcript_field\":\"mode\",\"judge_accepts\":false}},\n" ++
  "    \"unknown_fields\":\"reject\",\n" ++
  "    \"unknown_artifacts\":\"reject\"\n" ++
  "  }\n" ++
  "}\n"

def canonicalArtifacts (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) :
    List ArtifactBytes :=
  [ { path := "schema.json", mediaType := "application/schema+json", contents := schemaJson }
  , { path := "catalog.json", mediaType := "application/json",
      contents := catalogJson federationId sourceDigest contentRoot digests }
  , { path := "games/relay-repair.json", mediaType := "application/json",
      contents := relayDescriptorJson }
  , { path := "games/salvage-lock.json", mediaType := "application/json",
      contents := salvageDescriptorJson }
  , { path := "games/signal-triangulation.json", mediaType := "application/json",
      contents := signalDescriptorJson } ]

/-! SHA-256 is a deployed crypto primitive rather than a theorem implemented in
this emitter.  The driver measures these five exact Lean-rendered byte strings;
the signed content epoch anchors the resulting manifest. -/
structure ArtifactHashes where
  schema : String
  catalog : String
  relay : String
  salvage : String
  signal : String
deriving DecidableEq, Repr

def ArtifactHashes.valid (h : ArtifactHashes) : Bool :=
  validSha256 h.schema && validSha256 h.catalog && validSha256 h.relay &&
    validSha256 h.salvage && validSha256 h.signal

def canonicalPins (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) : List ArtifactPin :=
  match canonicalArtifacts federationId sourceDigest contentRoot digests with
  | [schema, catalog, relay, salvage, signal] =>
      [ schema.pin hashes.schema
      , catalog.pin hashes.catalog
      , relay.pin hashes.relay
      , salvage.pin hashes.salvage
      , signal.pin hashes.signal ]
  | _ => []

/-- ⚑ THE SIXTH ARTIFACT LANDMINE, DISARMED.

`canonicalPins` matches a LITERAL five-element list and falls through to `[]`.
So adding a sixth artifact — a fourth game — would not fail to compile; it would
silently emit a manifest **pinning nothing**, and the first thing to notice would
be a byte comparison somewhere downstream, if anything noticed at all.

This theorem is the detector. It relates the pin list to the artifact list rather
than to a literal `5`, so the moment `canonicalArtifacts` grows and the match
falls through, `0 = 6` fails and the BUILD goes red at the site of the mistake.

Do not "fix" a failure here by changing the expected length. Widen the match in
`canonicalPins` so every artifact is pinned, then this closes again by itself. -/
theorem canonicalPins_pins_every_canonical_artifact
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) :
    (canonicalPins federationId sourceDigest contentRoot digests hashes).length
      = (canonicalArtifacts federationId sourceDigest contentRoot digests).length := by
  rfl

#assert_axioms canonicalPins_pins_every_canonical_artifact

def manifestFor (sourceDigestString : String)
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) : Manifest :=
  { format := FORMAT
    schemaVersion := SCHEMA_VERSION
    sourceDigest := sourceDigestString
    authority := AUTHORITY
    artifacts := canonicalPins federationId sourceDigest contentRoot digests hashes }

/-- A manifest is accepted only if it is exactly the one reconstructed from the
Lean-owned artifact bytes and the externally measured full-width source digest. -/
def acceptsManifest (sourceDigestString : String)
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) (candidate : Manifest) : Bool :=
  validSha256 sourceDigestString &&
    hashes.valid &&
    decide (digestHex sourceDigest = sourceDigestString) &&
    decide (digestHex digests.signal = hashes.signal) &&
    decide (digestHex digests.relay = hashes.relay) &&
    decide (digestHex digests.salvage = hashes.salvage) &&
    decide (candidate =
      manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes)

theorem acceptsManifest_eq_true_iff
    (sourceDigestString : String) (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) (hashes : ArtifactHashes) (candidate : Manifest) :
    acceptsManifest sourceDigestString federationId sourceDigest contentRoot digests hashes candidate =
      true ↔
      validSha256 sourceDigestString = true ∧
      hashes.valid = true ∧
      digestHex sourceDigest = sourceDigestString ∧
      digestHex digests.signal = hashes.signal ∧
      digestHex digests.relay = hashes.relay ∧
      digestHex digests.salvage = hashes.salvage ∧
      candidate =
        manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes := by
  simp [acceptsManifest, and_assoc]

/-- Parse plus exact reconstruction.  A parse error, version drift, field drift,
pin mismatch, reordered file, unknown file, or source mismatch is an error. -/
def ingestManifest (sourceDigestString : String)
    (federationId sourceDigest contentRoot : Digest32) (digests : GameContentDigests)
    (hashes : ArtifactHashes) (bytes : String) : Except String Manifest := do
  let parsed ← parseManifest bytes
  if acceptsManifest sourceDigestString federationId sourceDigest contentRoot digests hashes parsed then
    pure parsed
  else
    throw "POAG1 manifest does not exactly match the Lean-emitted bundle"

theorem ingestManifest_exact
    (sourceDigestString : String) (federationId sourceDigest contentRoot : Digest32)
    (digests : GameContentDigests) (hashes : ArtifactHashes) (bytes : String) (accepted : Manifest)
    (h : ingestManifest sourceDigestString federationId sourceDigest contentRoot digests hashes bytes =
      .ok accepted) :
    accepted =
      manifestFor sourceDigestString federationId sourceDigest contentRoot digests hashes := by
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
        exact (acceptsManifest_eq_true_iff _ _ _ _ _ _ _).mp ha |>.2.2.2.2.2.2
      · contradiction

#assert_axioms acceptsManifest_eq_true_iff
#assert_axioms ingestManifest_exact

end Dregg2.Games.PathOfAngels.Emit
