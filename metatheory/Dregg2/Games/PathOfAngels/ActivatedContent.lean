/-
# ActivatedContent — exact, spoiler-safe component membership for a PoA world

The private author pack is not a runtime policy.  This module defines the
smaller activation object which may safely cross that boundary:

* every component has a canonical public name, exact UTF-8 bytes, and the
  SHA-256 of those bytes;
* component names are strictly ordered, hence unique;
* the active world's `contentRoot` is the SHA-256 of the entire canonical
  manifest, including every component byte;
* the manifest is scoped to the active federation, content session, and epoch;
* the only Galley witness constructor checks that the named component bytes
  are exactly `PolicyWire.toJson`, and that its federation/epoch agree with the
  active world.

There is deliberately no `audited : Bool` field.  A caller cannot turn policy
bytes into a member by assertion: the witness constructor is private and the
only producer traverses the activated manifest.

## Migration from the current private-pack root

The existing content tooling defines `contentRoot = SHA256(canonical whole
pack JSON)`.  That root does not expose named component membership and cannot
be reinterpreted as this manifest root.  A migration therefore requires a new
signed WorldActivation successor whose `contentRoot` is `manifestRoot?` below.
`legacyWholePackRoot` is curator-asserted provenance only: this schema cannot
prove it was the immediate predecessor root.  It is outside `components`, has
no membership constructor, and grants no runtime authority.  Persistence may
add a migration-specific predecessor check when that lineage fact matters.
This is a real root/schema transition, not a byte-compatible upgrade.

Signed active-world authority remains exclusively at the persistence seam in
`WorldActivation`.  The native runtime below only proves exact membership for
the all-five-field world which that seam has already audited in the same
writer.  In particular this module exports no caller-set
`nativeSignaturesVerified : Bool` authority shortcut.
-/
import Lean.Data.Json
import Dregg2.Bridge.MinaStateHashDerive
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime
import Dregg2.Games.PathOfAngels.WorldActivation
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ActivatedContent

open Lean
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev MANIFEST_FORMAT : String := "POA-ACTIVATED-CONTENT-MANIFEST-1"
abbrev GALLEY_POLICY_COMPONENT : String :=
  "poa.galley-maintenance-daily.policy.v1"
abbrev LEGACY_ROOT_RESERVED_COMPONENT : String := "legacy-whole-pack"
abbrev MANIFEST_BYTE_LIMIT : Nat := 1024 * 1024
abbrev COMPONENT_BYTE_LIMIT : Nat := 256 * 1024
abbrev COMPONENT_NAME_BYTE_LIMIT : Nat := 96
abbrev COMPONENT_LIMIT : Nat := 64
abbrev WIRE_U64_LIMIT : Nat := 2 ^ 64 - 1

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

private def nonzero (digest : Digest32) : Bool := digest != zeroDigest

private def jsonString (value : String) : String := String.quote value
private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def natByteHex (value : Nat) : String :=
  String.ofList [lowerHexDigit (value / 16), lowerHexDigit (value % 16)]

private def utf8Nats (value : String) : List Nat :=
  value.toUTF8.toList.map UInt8.toNat

/-- SHA-256 of the exact UTF-8 bytes, computed by the Lean reference SHA-256. -/
def sha256Utf8? (value : String) : Option Digest32 :=
  Emit.parseBytes32Hex? (String.join
    ((Dregg2.Bridge.MinaStateHashDerive.sha256 (utf8Nats value)).map natByteHex))

structure ManifestScope where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : Nat
deriving DecidableEq

/-- `bytesUtf8` are the exact runtime bytes.  `sha256` is checked from them;
neither field is a caller-authored summary of the other. -/
structure Component where
  name : String
  sha256 : Digest32
  bytesUtf8 : String
deriving DecidableEq

structure Manifest where
  scope : ManifestScope
  /-- Provenance only.  It is never searched by `exactMember?`. -/
  legacyWholePackRoot : Option Digest32
  components : List Component
deriving DecidableEq

def ManifestScope.toJson (scope : ManifestScope) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex scope.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex scope.contentSession) ++
    ",\"content_epoch\":" ++ toString scope.contentEpoch ++ "}"

def Component.toJson (component : Component) : String :=
  "{\"name\":" ++ jsonString component.name ++
    ",\"sha256\":" ++ jsonString (Emit.bytes32Hex component.sha256) ++
    ",\"bytes_utf8\":" ++ jsonString component.bytesUtf8 ++ "}"

def Manifest.toJson (manifest : Manifest) : String :=
  "{\"format\":" ++ jsonString MANIFEST_FORMAT ++
    ",\"scope\":" ++ manifest.scope.toJson ++
    ",\"legacy_whole_pack_sha256\":" ++
      (match manifest.legacyWholePackRoot with
       | none => "null"
       | some digest => jsonString (Emit.bytes32Hex digest)) ++
    ",\"components\":" ++ jsonArray (manifest.components.map Component.toJson) ++ "}"

/-- The new activation `contentRoot`: SHA-256 of the complete canonical manifest. -/
def manifestRoot? (manifest : Manifest) : Option Digest32 :=
  sha256Utf8? manifest.toJson

private def asciiLower (c : Char) : Bool :=
  decide ('a'.toNat ≤ c.toNat && c.toNat ≤ 'z'.toNat)

private def asciiDigit (c : Char) : Bool :=
  decide ('0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat)

private def componentNameChar (c : Char) : Bool :=
  asciiLower c || asciiDigit c || c = '-' || c = '_' || c = '.'

def validComponentNameB (name : String) : Bool :=
  decide (0 < name.utf8ByteSize) &&
  decide (name.utf8ByteSize ≤ COMPONENT_NAME_BYTE_LIMIT) &&
  name.toList.all componentNameChar

private def componentNameLess (left right : Component) : Bool :=
  left.name < right.name

private def componentNameLessP (left right : Component) : Prop :=
  componentNameLess left right = true

private instance componentNameLessPDecidable (left right : Component) :
    Decidable (componentNameLessP left right) := by
  unfold componentNameLessP componentNameLess
  infer_instance

def Component.validB (component : Component) : Bool :=
  validComponentNameB component.name &&
  decide (component.name ≠ LEGACY_ROOT_RESERVED_COMPONENT) &&
  decide (component.bytesUtf8.utf8ByteSize ≤ COMPONENT_BYTE_LIMIT) &&
  decide (sha256Utf8? component.bytesUtf8 = some component.sha256)

def Manifest.validB (manifest : Manifest) : Bool :=
  decide (manifest.toJson.utf8ByteSize ≤ MANIFEST_BYTE_LIMIT) &&
  nonzero manifest.scope.federationId &&
  nonzero manifest.scope.contentSession &&
  decide (0 < manifest.scope.contentEpoch) &&
  decide (manifest.scope.contentEpoch ≤ WIRE_U64_LIMIT) &&
  (match manifest.legacyWholePackRoot with
   | none => true
   | some digest => nonzero digest) &&
  decide (0 < manifest.components.length) &&
  decide (manifest.components.length ≤ COMPONENT_LIMIT) &&
  decide (manifest.components.Pairwise componentNameLessP) &&
  manifest.components.all Component.validB

/-- Public type, private constructor.  Parsing arbitrary JSON cannot construct
one unless all component hashes, bounds, names, and ordering checks pass. -/
structure ValidatedManifest where
  private mk ::
  raw : Manifest
  valid : raw.validB = true

def validateManifest? (manifest : Manifest) : Option ValidatedManifest :=
  if valid : manifest.validB = true then some ⟨manifest, valid⟩ else none

private theorem validateManifest_raw_exact {raw : Manifest}
    {validated : ValidatedManifest}
    (accepted : validateManifest? raw = some validated) : validated.raw = raw := by
  have mapped := congrArg (Option.map ValidatedManifest.raw) accepted
  simp [validateManifest?] at mapped
  exact mapped.2.symm

/-! ## Strict canonical manifest decoder -/

private def exactKeys (json : Json) (allowed : List String) : Except String Unit := do
  let object ← json.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def objectDigest (json : Json) (key : String) : Except String Digest32 := do
  let spelling ← json.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def objectNat (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  if value ≤ WIRE_U64_LIMIT then pure value else throw "integer exceeds u64"

private def parseOptionalDigest (json : Json) : Except String (Option Digest32) :=
  match json with
  | .null => pure none
  | .str spelling => match Emit.parseBytes32Hex? spelling with
      | some digest => pure (some digest)
      | none => throw "legacy root is not a canonical digest"
  | _ => throw "legacy root must be null or a digest"

private def parseScope (json : Json) : Except String ManifestScope := do
  exactKeys json ["federation_id", "content_session", "content_epoch"]
  pure {
    federationId := ← objectDigest json "federation_id"
    contentSession := ← objectDigest json "content_session"
    contentEpoch := ← objectNat json "content_epoch"
  }

private def parseComponent (json : Json) : Except String Component := do
  exactKeys json ["name", "sha256", "bytes_utf8"]
  pure {
    name := ← json.getObjValAs? String "name"
    sha256 := ← objectDigest json "sha256"
    bytesUtf8 := ← json.getObjValAs? String "bytes_utf8"
  }

private def parseManifest (json : Json) : Except String Manifest := do
  exactKeys json ["format", "scope", "legacy_whole_pack_sha256", "components"]
  if (← json.getObjValAs? String "format") != MANIFEST_FORMAT then
    throw "wrong manifest format"
  let values := (← (← json.getObjVal? "components").getArr?).toList
  if values.length > COMPONENT_LIMIT then throw "component count exceeds bound"
  pure {
    scope := ← parseScope (← json.getObjVal? "scope")
    legacyWholePackRoot := ←
      parseOptionalDigest (← json.getObjVal? "legacy_whole_pack_sha256")
    components := ← values.mapM parseComponent
  }

private def canonicalDecode (bytes : String) : Option ValidatedManifest :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json => match parseManifest json with
      | .error _ => none
      | .ok manifest =>
          if manifest.toJson = bytes then validateManifest? manifest else none

private def decodeManifestWithLimit (limit : Nat) (bytes : String) : Option ValidatedManifest :=
  if bytes.utf8ByteSize ≤ limit then canonicalDecode bytes else none

def decodeManifest (bytes : String) : Option ValidatedManifest :=
  decodeManifestWithLimit MANIFEST_BYTE_LIMIT bytes

theorem decodeManifest_reencodes {bytes : String} {manifest : ValidatedManifest}
    (accepted : decodeManifest bytes = some manifest) : manifest.raw.toJson = bytes := by
  simp only [decodeManifest, decodeManifestWithLimit] at accepted
  split at accepted <;> try contradiction
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i canonical
  rw [validateManifest_raw_exact accepted]
  exact canonical

theorem decodeManifest_refuses_oversized (bytes : String)
    (oversized : MANIFEST_BYTE_LIMIT < bytes.utf8ByteSize) :
    decodeManifest bytes = none := by
  simp [decodeManifest, decodeManifestWithLimit, Nat.not_le.mpr oversized]

/-! ## World-scoped exact members -/

def Manifest.matchesWorldB (manifest : Manifest)
    (world : WorldActivation.WorldIdentity) : Bool :=
  WorldActivation.validWorld world &&
  decide (manifestRoot? manifest = some world.contentRoot) &&
  decide (manifest.scope.federationId = world.federationId) &&
  decide (manifest.scope.contentSession = world.contentSession) &&
  decide (manifest.scope.contentEpoch = world.contentEpoch.value)

private def componentByName? : List Component → String → Option Component
  | [], _ => none
  | component :: rest, name =>
      if component.name = name then some component else componentByName? rest name

/-! ## Persistence-facing world-scoped Galley authority

Native persistence already owns the same-writer signed-active-world audit.  It
therefore needs a narrower Lean value which proves that the exact embedded
Galley bytes are a member of the candidate world it just audited, without
serializing a second copy of the activation lineage through this module. -/

structure WorldScopedGalleyPolicyMember where
  private mk ::
  world : WorldActivation.WorldIdentity
  manifest : ValidatedManifest
  component : Component
  policy : GalleyMaintenanceDailyRuntime.PolicyWire
  root_and_scope_exact : manifest.raw.matchesWorldB world = true
  located : componentByName? manifest.raw.components GALLEY_POLICY_COMPONENT = some component
  policy_bytes_exact : component.bytesUtf8 = policy.toJson
  policy_valid : policy.validB = true
  federation_exact : policy.federationId = world.federationId
  epoch_exact : policy.contentEpoch = world.contentEpoch.value

def authorizeEmbeddedGalleyPolicyForWorld? (world : WorldActivation.WorldIdentity)
    (manifest : ValidatedManifest) : Option WorldScopedGalleyPolicyMember :=
  if worldExact : manifest.raw.matchesWorldB world = true then
    match located : componentByName? manifest.raw.components GALLEY_POLICY_COMPONENT with
    | none => none
    | some component =>
        match decoded : GalleyMaintenanceDailyRuntime.decodePolicy component.bytesUtf8 with
        | none => none
        | some policy =>
            if valid : policy.validB = true then
              if federation : policy.federationId = world.federationId then
                if epoch : policy.contentEpoch = world.contentEpoch.value then
                  some ⟨world, manifest, component, policy, worldExact, located,
                    (GalleyMaintenanceDailyRuntime.decodePolicy_reencodes decoded).symm,
                    valid, federation, epoch⟩
                else none
              else none
            else none
  else none

theorem WorldScopedGalleyPolicyMember.exact_policy_bytes
    (member : WorldScopedGalleyPolicyMember) :
    member.component.bytesUtf8 = member.policy.toJson := member.policy_bytes_exact

theorem WorldScopedGalleyPolicyMember.exact_content_root
    (member : WorldScopedGalleyPolicyMember) :
    manifestRoot? member.manifest.raw = some member.world.contentRoot := by
  have exact := member.root_and_scope_exact
  unfold Manifest.matchesWorldB at exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨_, root⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  exact of_decide_eq_true root

#assert_axioms decodeManifest_reencodes
#assert_axioms decodeManifest_refuses_oversized
#assert_axioms WorldScopedGalleyPolicyMember.exact_policy_bytes
#assert_axioms WorldScopedGalleyPolicyMember.exact_content_root

end Dregg2.Games.PathOfAngels.ActivatedContent
