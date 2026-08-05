/-
# ActivatedContentRuntime — native exact-manifest authority wire

Persistence supplies the exact all-five-field world it has just authenticated
inside its redb writer and one proposed canonical manifest.  Lean decodes the
manifest, recomputes every component SHA-256 and the manifest root, scopes it
to that world, decodes the reserved Galley policy with the Galley runtime's own
parser, and emits the exact policy/genesis bytes persistence may seal.

This export does not decide which world is active.  That authority remains the
same-writer `WorldActivation` audit.  It decides only content membership under
the exact candidate world, and an absent export is a hard refusal.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.ActivatedContent

namespace Dregg2.Games.PathOfAngels.ActivatedContentRuntime

open Lean
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-ACTIVATED-CONTENT-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-ACTIVATED-CONTENT-OUT-1"
abbrev WIRE_BYTE_LIMIT : Nat := 4 * 1024 * 1024
abbrev WIRE_U64_LIMIT : Nat := 2 ^ 64 - 1

private def jsonString (value : String) : String := String.quote value

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

private def parseWorld (json : Json) : Except String WorldActivation.WorldIdentity := do
  exactKeys json ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch"]
  pure {
    federationId := ← objectDigest json "federation_id"
    contentRoot := ← objectDigest json "content_root"
    activationDigest := ← objectDigest json "activation_digest"
    contentSession := ← objectDigest json "content_session"
    contentEpoch := ⟨← objectNat json "content_epoch"⟩
  }

structure InputWire where
  world : WorldActivation.WorldIdentity
  manifestJson : String
deriving DecidableEq

def InputWire.toJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"world\":" ++ input.world.toJson ++
    ",\"manifest_json\":" ++ jsonString input.manifestJson ++ "}"

private def parseInput (json : Json) : Except String InputWire := do
  exactKeys json ["format", "world", "manifest_json"]
  if (← json.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  let manifestJson ← json.getObjValAs? String "manifest_json"
  if manifestJson.utf8ByteSize > ActivatedContent.MANIFEST_BYTE_LIMIT then
    throw "manifest exceeds bound"
  pure {
    world := ← parseWorld (← json.getObjVal? "world")
    manifestJson
  }

private def canonicalDecode (bytes : String) : Option InputWire :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json => match parseInput json with
      | .error _ => none
      | .ok input => if input.toJson = bytes then some input else none

def decodeInput (bytes : String) : Option InputWire :=
  if bytes.utf8ByteSize ≤ WIRE_BYTE_LIMIT then canonicalDecode bytes else none

structure OutputWire where
  world : WorldActivation.WorldIdentity
  manifestRoot : Digest32
  componentSha256 : Digest32
  policyJson : String
  genesisProjectionJson : String
deriving DecidableEq

def OutputWire.toJson (output : OutputWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"world\":" ++ output.world.toJson ++
    ",\"manifest_root\":" ++ jsonString (Emit.bytes32Hex output.manifestRoot) ++
    ",\"component_sha256\":" ++ jsonString (Emit.bytes32Hex output.componentSha256) ++
    ",\"policy_json\":" ++ jsonString output.policyJson ++
    ",\"genesis_projection_json\":" ++ jsonString output.genesisProjectionJson ++ "}"

def authorize? (input : InputWire) : Option OutputWire := do
  let manifest ← ActivatedContent.decodeManifest input.manifestJson
  let member ← ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? input.world manifest
  let root ← ActivatedContent.manifestRoot? manifest.raw
  pure {
    world := member.world
    manifestRoot := root
    componentSha256 := member.component.sha256
    policyJson := member.policy.toJson
    genesisProjectionJson :=
      (GalleyMaintenanceDailyRuntime.initialProjection member.policy).toJson
  }

@[export dregg_poa_activated_content_authorize]
def authorizeWire (bytes : String) : String :=
  match decodeInput bytes with
  | none => ""
  | some input => match authorize? input with
      | none => ""
      | some output => output.toJson

theorem decodeInput_reencodes {bytes : String} {input : InputWire}
    (accepted : decodeInput bytes = some input) : input.toJson = bytes := by
  simp only [decodeInput] at accepted
  split at accepted <;> try contradiction
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  exact equal

#assert_axioms decodeInput_reencodes

theorem decodeInput_rejects_oversize {bytes : String}
    (oversize : WIRE_BYTE_LIMIT < bytes.utf8ByteSize) : decodeInput bytes = none := by
  simp [decodeInput, Nat.not_le.mpr oversize]

#assert_axioms decodeInput_rejects_oversize

end Dregg2.Games.PathOfAngels.ActivatedContentRuntime
