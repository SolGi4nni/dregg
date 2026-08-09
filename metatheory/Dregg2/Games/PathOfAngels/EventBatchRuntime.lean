/-
# EventBatchRuntime — strict Lean planner for durable PoA EventBatch V2

This is the server-side seam between a game judge (Galley is the first caller)
and `PreparedPoaEventBatchV2`.  The host supplies one *already finalized*
coordinate, the exact durable stream heads it read, and the opaque event and
projection bytes emitted by the game judge.  Lean:

* strictly decodes one bounded canonical JSON value;
* re-hashes every payload and successor projection from its full bytes;
* re-hashes every EventSourcing statement and authors the batch digest;
* re-runs `EventBatch.applyBatch` over the exact initial semantic heads;
* derives every predecessor from the evolving head set, including repeated
  streams; and
* returns the complete, canonical persistence plan and successor heads.

`HostAuthorityWire` is deliberately redundant.  It lets this pure boundary
detect disagreement between the finalized carrier, game-judge result, and the
candidate plan.  JSON does NOT authenticate it.  The exported function is a
privileged, server-only FFI: the native host must construct `authority` only
after finalization and must never forward a network caller's purported
authority.  In particular, `storage_head_digest` values are opaque values from
the V2 persistence codec (SHA-256 over its canonical framed head).  Lean checks
their exact chaining and host-authority binding but makes no claim to implement
that native SHA/postcard boundary here.

The semantic payload/event/projection/batch digests below retain all eight
BabyBear sponge lanes.  This is a named deployment boundary, not a collision-
resistance theorem.
-/
import Lean.Data.Json
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EventBatchRuntime

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-EVENT-BATCH-RUNTIME-IN-2"
abbrev OUTPUT_FORMAT : String := "POA-EVENT-BATCH-PREPARED-3"
abbrev INITIAL_HEADS_INPUT_FORMAT : String := "POA-EVENT-BATCH-INITIAL-HEADS-IN-1"
abbrev INITIAL_HEADS_OUTPUT_FORMAT : String := "POA-EVENT-BATCH-INITIAL-HEADS-DIGEST-1"
abbrev WIRE_U32_MAX : Nat := 2 ^ 32 - 1
abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1
abbrev WIRE_BYTE_LIMIT : Nat := 64 * 1024 * 1024
abbrev MAX_COMPONENT_BYTES : Nat := 16 * 1024 * 1024
abbrev MAX_EVENTS : Nat := EventBatch.MAX_BATCH_EVENTS

abbrev PAYLOAD_DIGEST_DOMAIN : Nat := 0x50474150
abbrev EVENT_DIGEST_DOMAIN : Nat := 0x50474145
abbrev PROJECTION_DIGEST_DOMAIN : Nat := 0x50474152
abbrev BATCH_DIGEST_DOMAIN : Nat := 0x50474242
abbrev INITIAL_HEADS_DIGEST_DOMAIN : Nat := 0x50474248

private def jsonString (value : String) : String := String.quote value
private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def optionJson {T : Type} (encode : T → String) : Option T → String
  | none => "null"
  | some value => encode value

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def boundedNat (limit value : Nat) : Except String Nat :=
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def objectNat (j : Json) (key : String) (limit : Nat := WIRE_U64_MAX) :
    Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def hexNibble? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

private def parseHexBytes? : List Char → Option (List Nat)
  | [] => some []
  | hi :: lo :: rest => do
      let h ← hexNibble? hi
      let l ← hexNibble? lo
      pure ((16 * h + l) :: (← parseHexBytes? rest))
  | _ => none

private def byteHex (value : Nat) : String :=
  String.ofList [lowerHexDigit (value / 16), lowerHexDigit (value % 16)]

private def bytesHex (values : List Nat) : String :=
  String.join (values.map byteHex)

structure OpaqueBytes where
  bytes : List Nat
deriving DecidableEq

def OpaqueBytes.toHex (value : OpaqueBytes) : String := bytesHex value.bytes

def OpaqueBytes.validB (value : OpaqueBytes) : Bool :=
  !value.bytes.isEmpty && value.bytes.length ≤ MAX_COMPONENT_BYTES &&
    value.bytes.all (fun byte => byte < 256)

private def parseOpaqueBytes (j : Json) : Except String OpaqueBytes := do
  let spelling ← j.getStr?
  if spelling.length = 0 then throw "opaque component is empty"
  if spelling.length > 2 * MAX_COMPONENT_BYTES then throw "opaque component exceeds bound"
  let bytes ← match parseHexBytes? spelling.toList with
    | none => throw "opaque component must be lowercase even-length hexadecimal"
    | some bytes => pure bytes
  let value : OpaqueBytes := ⟨bytes⟩
  if value.validB && value.toHex = spelling then pure value
  else throw "opaque component is not canonical"

private def objectOpaqueBytes (j : Json) (key : String) : Except String OpaqueBytes := do
  parseOpaqueBytes (← j.getObjVal? key)

private def byte (n : Nat) : Fin 256 :=
  ⟨n % 256, Nat.mod_lt _ (by decide)⟩

private def u32le (n : Nat) : List (Fin 256) :=
  [byte n, byte (n / 256), byte (n / 65536), byte (n / 16777216)]

/-- A faithful 32-byte projection of all eight BabyBear hash lanes. -/
def digestBytes (domain : Nat) (bytes : List Nat) : Digest32 :=
  let lanes := Dregg2.Circuit.CommitmentTreeWide.hashTo8 domain bytes
  { bytes := (List.ofFn (fun lane : Fin 8 => u32le (lanes.getD lane.val 0))).flatten
    length_eq := by simp [u32le] }

def digestString (domain : Nat) (value : String) : Digest32 :=
  digestBytes domain (value.toUTF8.toList.map UInt8.toNat)

/-! ## Canonical proof-erased wire values -/

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

structure WorldWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
deriving DecidableEq

def WorldWire.validB (world : WorldWire) : Bool :=
  world.federationId != zeroDigest && world.contentRoot != zeroDigest &&
    world.activationDigest != zeroDigest && world.contentSession != zeroDigest &&
    world.contentEpoch != 0

structure CoordinateWire where
  world : WorldWire
  commitOrdinal : Nat
  blockId : Digest32
  turnHash : Digest32
  receiptHash : Digest32
  actorRoot : Digest32
  signer : Digest32
deriving DecidableEq

def CoordinateWire.validB (coordinate : CoordinateWire) : Bool :=
  coordinate.world.validB && coordinate.blockId != zeroDigest &&
    coordinate.turnHash != zeroDigest && coordinate.receiptHash != zeroDigest &&
    coordinate.actorRoot != zeroDigest && coordinate.signer != zeroDigest

structure StreamWire where
  world : WorldWire
  kind : Nat
  key : Digest32
  version : Nat
deriving DecidableEq

def StreamWire.validB (stream : StreamWire) : Bool :=
  stream.world.validB && stream.kind != 0 && stream.key != zeroDigest && stream.version != 0

structure HeadWire where
  stream : StreamWire
  sequence : Nat
  semanticHead : Digest32
  storageHeadDigest : Digest32
  projectionDigest : Digest32
  projection : OpaqueBytes
  origin : String
deriving DecidableEq

structure StatementWire where
  namespaceId : Digest32
  kind : Nat
  key : Digest32
  version : Nat
  sequence : Nat
  predecessor : Digest32
  payloadDigest : Digest32
deriving DecidableEq

structure CandidateEventWire where
  eventIndex : Nat
  statement : StatementWire
  eventDigest : Digest32
  payload : OpaqueBytes
  successorProjectionDigest : Digest32
  successorProjection : OpaqueBytes
deriving DecidableEq

/-- One result endorsed by the finalized native/game-judge seam.  The successor
storage digest is the native V2 head-codec digest and is opaque to this module. -/
structure AuthorityEventBindingWire where
  eventIndex : Nat
  receiptHash : Digest32
  actorRoot : Digest32
  signer : Digest32
  eventDigest : Digest32
  payloadDigest : Digest32
  successorProjectionDigest : Digest32
  successorStorageHeadDigest : Digest32
deriving DecidableEq

structure HostAuthorityWire where
  coordinate : CoordinateWire
  initialHeadsDigest : Digest32
  events : List AuthorityEventBindingWire
deriving DecidableEq

structure InputWire where
  authority : HostAuthorityWire
  coordinate : CoordinateWire
  initialHeads : List HeadWire
  events : List CandidateEventWire
deriving DecidableEq

/-- A narrow host-only request for the Lean-authored digest that welds one
exact, world-scoped durable head set into the privileged planner envelope. -/
structure InitialHeadsDigestInputWire where
  coordinate : CoordinateWire
  initialHeads : List HeadWire
deriving DecidableEq

structure InitialHeadsDigestOutputWire where
  initialHeadsDigest : Digest32
deriving DecidableEq

structure PreparedEventWire where
  eventIndex : Nat
  stream : StreamWire
  sequence : Nat
  expectedPredecessorHeadDigest : Digest32
  semanticPredecessor : Digest32
  eventDigest : Digest32
  payloadDigest : Digest32
  payload : OpaqueBytes
  successorProjectionDigest : Digest32
  successorProjection : OpaqueBytes
  genesisProjectionDigest : Option Digest32
  genesisProjection : Option OpaqueBytes
deriving DecidableEq

structure PreparedBatchWire where
  coordinate : CoordinateWire
  leanStatement : OpaqueBytes
  batchDigest : Digest32
  events : List PreparedEventWire
  successorHeads : List HeadWire
deriving DecidableEq

/-! ## Canonical encoders -/

def WorldWire.toJson (world : WorldWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex world.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex world.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex world.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex world.contentSession) ++
    ",\"content_epoch\":" ++ toString world.contentEpoch ++ "}"

def CoordinateWire.toJson (coordinate : CoordinateWire) : String :=
  "{\"world\":" ++ coordinate.world.toJson ++
    ",\"commit_ordinal\":" ++ toString coordinate.commitOrdinal ++
    ",\"block_id\":" ++ jsonString (Emit.bytes32Hex coordinate.blockId) ++
    ",\"turn_hash\":" ++ jsonString (Emit.bytes32Hex coordinate.turnHash) ++
    ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex coordinate.receiptHash) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex coordinate.actorRoot) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex coordinate.signer) ++ "}"

def StreamWire.toJson (stream : StreamWire) : String :=
  "{\"world\":" ++ stream.world.toJson ++
    ",\"kind\":" ++ toString stream.kind ++
    ",\"key\":" ++ jsonString (Emit.bytes32Hex stream.key) ++
    ",\"version\":" ++ toString stream.version ++ "}"

def HeadWire.toJson (head : HeadWire) : String :=
  "{\"stream\":" ++ head.stream.toJson ++
    ",\"sequence\":" ++ toString head.sequence ++
    ",\"semantic_head\":" ++ jsonString (Emit.bytes32Hex head.semanticHead) ++
    ",\"storage_head_digest\":" ++ jsonString (Emit.bytes32Hex head.storageHeadDigest) ++
    ",\"projection_hex\":" ++ jsonString head.projection.toHex ++
    ",\"origin\":" ++ jsonString head.origin ++ "}"

def StatementWire.toJson (statement : StatementWire) : String :=
  "{\"namespace_id\":" ++ jsonString (Emit.bytes32Hex statement.namespaceId) ++
    ",\"kind\":" ++ toString statement.kind ++
    ",\"key\":" ++ jsonString (Emit.bytes32Hex statement.key) ++
    ",\"version\":" ++ toString statement.version ++
    ",\"sequence\":" ++ toString statement.sequence ++
    ",\"predecessor\":" ++ jsonString (Emit.bytes32Hex statement.predecessor) ++
    ",\"payload_digest\":" ++ jsonString (Emit.bytes32Hex statement.payloadDigest) ++ "}"

def CandidateEventWire.toJson (event : CandidateEventWire) : String :=
  "{\"event_index\":" ++ toString event.eventIndex ++
    ",\"statement\":" ++ event.statement.toJson ++
    ",\"event_digest\":" ++ jsonString (Emit.bytes32Hex event.eventDigest) ++
    ",\"payload_hex\":" ++ jsonString event.payload.toHex ++
    ",\"successor_projection_digest\":" ++
      jsonString (Emit.bytes32Hex event.successorProjectionDigest) ++
    ",\"successor_projection_hex\":" ++ jsonString event.successorProjection.toHex ++ "}"

def AuthorityEventBindingWire.toJson (binding : AuthorityEventBindingWire) : String :=
  "{\"event_index\":" ++ toString binding.eventIndex ++
    ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex binding.receiptHash) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex binding.actorRoot) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex binding.signer) ++
    ",\"event_digest\":" ++ jsonString (Emit.bytes32Hex binding.eventDigest) ++
    ",\"payload_digest\":" ++ jsonString (Emit.bytes32Hex binding.payloadDigest) ++
    ",\"successor_projection_digest\":" ++
      jsonString (Emit.bytes32Hex binding.successorProjectionDigest) ++
    ",\"successor_storage_head_digest\":" ++
      jsonString (Emit.bytes32Hex binding.successorStorageHeadDigest) ++ "}"

def HostAuthorityWire.toJson (authority : HostAuthorityWire) : String :=
  "{\"coordinate\":" ++ authority.coordinate.toJson ++
    ",\"initial_heads_digest\":" ++ jsonString (Emit.bytes32Hex authority.initialHeadsDigest) ++
    ",\"events\":" ++ jsonArray (authority.events.map AuthorityEventBindingWire.toJson) ++ "}"

def InputWire.toJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"authority\":" ++ input.authority.toJson ++
    ",\"coordinate\":" ++ input.coordinate.toJson ++
    ",\"initial_heads\":" ++ jsonArray (input.initialHeads.map HeadWire.toJson) ++
    ",\"events\":" ++ jsonArray (input.events.map CandidateEventWire.toJson) ++ "}"

def InitialHeadsDigestInputWire.toJson (input : InitialHeadsDigestInputWire) : String :=
  "{\"format\":" ++ jsonString INITIAL_HEADS_INPUT_FORMAT ++
    ",\"coordinate\":" ++ input.coordinate.toJson ++
    ",\"initial_heads\":" ++ jsonArray (input.initialHeads.map HeadWire.toJson) ++ "}"

def InitialHeadsDigestOutputWire.toJson (output : InitialHeadsDigestOutputWire) : String :=
  "{\"format\":" ++ jsonString INITIAL_HEADS_OUTPUT_FORMAT ++
    ",\"initial_heads_digest\":" ++
      jsonString (Emit.bytes32Hex output.initialHeadsDigest) ++ "}"

def PreparedEventWire.toJson (event : PreparedEventWire) : String :=
  "{\"event_index\":" ++ toString event.eventIndex ++
    ",\"stream\":" ++ event.stream.toJson ++
    ",\"sequence\":" ++ toString event.sequence ++
    ",\"expected_predecessor_head_digest\":" ++
      jsonString (Emit.bytes32Hex event.expectedPredecessorHeadDigest) ++
    ",\"semantic_predecessor\":" ++ jsonString (Emit.bytes32Hex event.semanticPredecessor) ++
    ",\"event_digest\":" ++ jsonString (Emit.bytes32Hex event.eventDigest) ++
    ",\"payload_digest\":" ++ jsonString (Emit.bytes32Hex event.payloadDigest) ++
    ",\"payload_hex\":" ++ jsonString event.payload.toHex ++
    ",\"successor_projection_digest\":" ++
      jsonString (Emit.bytes32Hex event.successorProjectionDigest) ++
    ",\"successor_projection_hex\":" ++ jsonString event.successorProjection.toHex ++
    ",\"genesis_projection_digest\":" ++
      optionJson (fun digest => jsonString (Emit.bytes32Hex digest)) event.genesisProjectionDigest ++
    ",\"genesis_projection_hex\":" ++
      optionJson (fun bytes => jsonString bytes.toHex) event.genesisProjection ++ "}"

def PreparedBatchWire.toJson (batch : PreparedBatchWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"coordinate\":" ++ batch.coordinate.toJson ++
    ",\"lean_statement_hex\":" ++ jsonString batch.leanStatement.toHex ++
    ",\"batch_digest\":" ++ jsonString (Emit.bytes32Hex batch.batchDigest) ++
    ",\"events\":" ++ jsonArray (batch.events.map PreparedEventWire.toJson) ++
    ",\"successor_heads\":" ++ jsonArray (batch.successorHeads.map HeadWire.toJson) ++ "}"

/-! ## Strict decoders -/

private def parseWorld (j : Json) : Except String WorldWire := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
  }

private def parseCoordinate (j : Json) : Except String CoordinateWire := do
  exactKeys j ["world", "commit_ordinal", "block_id", "turn_hash", "receipt_hash",
    "actor_root", "signer"]
  pure {
    world := ← parseWorld (← j.getObjVal? "world")
    commitOrdinal := ← objectNat j "commit_ordinal"
    blockId := ← objectDigest j "block_id"
    turnHash := ← objectDigest j "turn_hash"
    receiptHash := ← objectDigest j "receipt_hash"
    actorRoot := ← objectDigest j "actor_root"
    signer := ← objectDigest j "signer"
  }

private def parseStream (j : Json) : Except String StreamWire := do
  exactKeys j ["world", "kind", "key", "version"]
  pure {
    world := ← parseWorld (← j.getObjVal? "world")
    kind := ← objectNat j "kind"
    key := ← objectDigest j "key"
    version := ← objectNat j "version"
  }

private def parseHead (j : Json) : Except String HeadWire := do
  exactKeys j ["stream", "sequence", "semantic_head", "storage_head_digest",
    "projection_hex", "origin"]
  let origin ← j.getObjValAs? String "origin"
  if origin != "existing" && origin != "genesis" then throw "unknown head origin"
  let projection ← objectOpaqueBytes j "projection_hex"
  let head : HeadWire := {
    stream := ← parseStream (← j.getObjVal? "stream")
    sequence := ← objectNat j "sequence"
    semanticHead := ← objectDigest j "semantic_head"
    storageHeadDigest := ← objectDigest j "storage_head_digest"
    projectionDigest := digestBytes PROJECTION_DIGEST_DOMAIN projection.bytes
    projection
    origin
  }
  if origin = "genesis" && head.sequence != 0 then throw "genesis head has nonzero sequence"
  pure head

private def parseHeads (j : Json) : Except String (List HeadWire) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_EVENTS then throw "initial head set exceeds bound"
  values.mapM parseHead

private def parseStatement (j : Json) : Except String StatementWire := do
  exactKeys j ["namespace_id", "kind", "key", "version", "sequence", "predecessor",
    "payload_digest"]
  pure {
    namespaceId := ← objectDigest j "namespace_id"
    kind := ← objectNat j "kind"
    key := ← objectDigest j "key"
    version := ← objectNat j "version"
    sequence := ← objectNat j "sequence"
    predecessor := ← objectDigest j "predecessor"
    payloadDigest := ← objectDigest j "payload_digest"
  }

private def parseCandidateEvent (j : Json) : Except String CandidateEventWire := do
  exactKeys j ["event_index", "statement", "event_digest", "payload_hex",
    "successor_projection_digest", "successor_projection_hex"]
  pure {
    eventIndex := ← objectNat j "event_index" WIRE_U32_MAX
    statement := ← parseStatement (← j.getObjVal? "statement")
    eventDigest := ← objectDigest j "event_digest"
    payload := ← objectOpaqueBytes j "payload_hex"
    successorProjectionDigest := ← objectDigest j "successor_projection_digest"
    successorProjection := ← objectOpaqueBytes j "successor_projection_hex"
  }

private def parseCandidateEvents (j : Json) : Except String (List CandidateEventWire) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_EVENTS then throw "event batch exceeds bound"
  values.mapM parseCandidateEvent

private def parseAuthorityBinding (j : Json) : Except String AuthorityEventBindingWire := do
  exactKeys j ["event_index", "receipt_hash", "actor_root", "signer", "event_digest",
    "payload_digest", "successor_projection_digest", "successor_storage_head_digest"]
  pure {
    eventIndex := ← objectNat j "event_index" WIRE_U32_MAX
    receiptHash := ← objectDigest j "receipt_hash"
    actorRoot := ← objectDigest j "actor_root"
    signer := ← objectDigest j "signer"
    eventDigest := ← objectDigest j "event_digest"
    payloadDigest := ← objectDigest j "payload_digest"
    successorProjectionDigest := ← objectDigest j "successor_projection_digest"
    successorStorageHeadDigest := ← objectDigest j "successor_storage_head_digest"
  }

private def parseAuthorityBindings (j : Json) : Except String (List AuthorityEventBindingWire) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_EVENTS then throw "authority event set exceeds bound"
  values.mapM parseAuthorityBinding

private def parseAuthority (j : Json) : Except String HostAuthorityWire := do
  exactKeys j ["coordinate", "initial_heads_digest", "events"]
  pure {
    coordinate := ← parseCoordinate (← j.getObjVal? "coordinate")
    initialHeadsDigest := ← objectDigest j "initial_heads_digest"
    events := ← parseAuthorityBindings (← j.getObjVal? "events")
  }

private def parseInputJson (j : Json) : Except String InputWire := do
  exactKeys j ["format", "authority", "coordinate", "initial_heads", "events"]
  if (← j.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  pure {
    authority := ← parseAuthority (← j.getObjVal? "authority")
    coordinate := ← parseCoordinate (← j.getObjVal? "coordinate")
    initialHeads := ← parseHeads (← j.getObjVal? "initial_heads")
    events := ← parseCandidateEvents (← j.getObjVal? "events")
  }

private def parseInitialHeadsDigestInputJson (j : Json) :
    Except String InitialHeadsDigestInputWire := do
  exactKeys j ["format", "coordinate", "initial_heads"]
  if (← j.getObjValAs? String "format") != INITIAL_HEADS_INPUT_FORMAT then
    throw "wrong initial-heads input format"
  pure {
    coordinate := ← parseCoordinate (← j.getObjVal? "coordinate")
    initialHeads := ← parseHeads (← j.getObjVal? "initial_heads")
  }

def canonicalDecode {T : Type} (parse : Json → Except String T) (encode : T → String)
    (bytes : String) : Option T :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json =>
      match parse json with
      | .error _ => none
      | .ok value => if encode value = bytes then some value else none

def decodeInputWithLimit (byteLimit : Nat) (bytes : String) : Option InputWire :=
  if bytes.length ≤ byteLimit then canonicalDecode parseInputJson InputWire.toJson bytes else none

def decodeInput (bytes : String) : Option InputWire :=
  decodeInputWithLimit WIRE_BYTE_LIMIT bytes

def decodeInitialHeadsDigestInputWithLimit (byteLimit : Nat) (bytes : String) :
    Option InitialHeadsDigestInputWire :=
  if bytes.length ≤ byteLimit then
    canonicalDecode parseInitialHeadsDigestInputJson InitialHeadsDigestInputWire.toJson bytes
  else none

def decodeInitialHeadsDigestInput (bytes : String) : Option InitialHeadsDigestInputWire :=
  decodeInitialHeadsDigestInputWithLimit WIRE_BYTE_LIMIT bytes

theorem canonicalDecode_reencodes {T : Type} (parse : Json → Except String T)
    (encode : T → String) {bytes : String} {value : T}
    (accepted : canonicalDecode parse encode bytes = some value) : encode value = bytes := by
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  exact equal

theorem decodeInput_reencodes {bytes : String} {input : InputWire}
    (accepted : decodeInput bytes = some input) : input.toJson = bytes := by
  simp only [decodeInput, decodeInputWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseInputJson InputWire.toJson accepted
  · contradiction

theorem decodeInput_refuses_oversized (bytes : String)
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeInput bytes = none := by
  simp [decodeInput, decodeInputWithLimit, Nat.not_le.mpr oversized]

/-! ## Semantic conversion and the single planning path -/

def WorldWire.toSemantic (world : WorldWire) : EventBatch.WorldIdentity := {
  federationId := world.federationId
  contentRoot := world.contentRoot
  activationDigest := world.activationDigest
  contentSession := world.contentSession
  contentEpoch := ⟨world.contentEpoch⟩
}

def CoordinateWire.toSemantic (coordinate : CoordinateWire) : EventBatch.FinalizedTurnCoordinate := {
  world := coordinate.world.toSemantic
  commitOrdinal := coordinate.commitOrdinal
  blockId := coordinate.blockId
  turnHash := coordinate.turnHash
  receiptHash := coordinate.receiptHash
  actorRoot := coordinate.actorRoot
  signer := coordinate.signer
}

def StreamWire.toSemantic (stream : StreamWire) : EventBatch.StreamId := {
  world := stream.world.toSemantic
  aggregate := {
    namespaceId := stream.world.federationId
    kind := stream.kind
    key := stream.key
  }
  version := ⟨stream.version⟩
}

def StreamWire.ofSemantic (stream : EventBatch.StreamId) : StreamWire := {
  world := {
    federationId := stream.world.federationId
    contentRoot := stream.world.contentRoot
    activationDigest := stream.world.activationDigest
    contentSession := stream.world.contentSession
    contentEpoch := stream.world.contentEpoch.value }
  kind := stream.aggregate.kind
  key := stream.aggregate.key
  version := stream.version.value
}

def StatementWire.toSemantic (statement : StatementWire) : EventStatement := {
  aggregate := {
    namespaceId := statement.namespaceId
    kind := statement.kind
    key := statement.key
  }
  version := ⟨statement.version⟩
  sequence := statement.sequence
  predecessor := statement.predecessor
  payloadDigest := statement.payloadDigest
}

def StatementWire.ofSemantic (statement : EventStatement) : StatementWire := {
  namespaceId := statement.aggregate.namespaceId
  kind := statement.aggregate.kind
  key := statement.aggregate.key
  version := statement.version.value
  sequence := statement.sequence
  predecessor := statement.predecessor
  payloadDigest := statement.payloadDigest
}

def CandidateEventWire.toIndexed (event : CandidateEventWire) : EventBatch.IndexedEvent := {
  eventIndex := event.eventIndex
  statement := event.statement.toSemantic
  eventDigest := event.eventDigest
}

private def semanticWorldToJson (world : EventBatch.WorldIdentity) : String :=
  (WorldWire.mk world.federationId world.contentRoot world.activationDigest world.contentSession
    world.contentEpoch.value).toJson

private def semanticCoordinateToJson (coordinate : EventBatch.FinalizedTurnCoordinate) : String :=
  "{\"world\":" ++ semanticWorldToJson coordinate.world ++
    ",\"commit_ordinal\":" ++ toString coordinate.commitOrdinal ++
    ",\"block_id\":" ++ jsonString (Emit.bytes32Hex coordinate.blockId) ++
    ",\"turn_hash\":" ++ jsonString (Emit.bytes32Hex coordinate.turnHash) ++
    ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex coordinate.receiptHash) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex coordinate.actorRoot) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex coordinate.signer) ++ "}"

private def semanticIndexedEventToJson (event : EventBatch.IndexedEvent) : String :=
  "{\"event_index\":" ++ toString event.eventIndex ++
    ",\"statement\":" ++ (StatementWire.ofSemantic event.statement).toJson ++
    ",\"event_digest\":" ++ jsonString (Emit.bytes32Hex event.eventDigest) ++ "}"

def semanticStatementToJson (statement : EventBatch.Statement) : String :=
  "{\"coordinate\":" ++ semanticCoordinateToJson statement.coordinate ++
    ",\"events\":" ++ jsonArray (statement.events.map semanticIndexedEventToJson) ++ "}"

def digestBoundary : EventBatch.DigestBoundary where
  eventDigest statement :=
    digestString EVENT_DIGEST_DOMAIN (StatementWire.ofSemantic statement).toJson
  batchDigest statement := digestString BATCH_DIGEST_DOMAIN (semanticStatementToJson statement)

def initialHeadsDigest (heads : List HeadWire) : Digest32 :=
  digestString INITIAL_HEADS_DIGEST_DOMAIN (jsonArray (heads.map HeadWire.toJson))

private def streamIds (heads : List HeadWire) : List StreamWire := heads.map HeadWire.stream

private def headFor? : List HeadWire → StreamWire → Option HeadWire
  | [], _ => none
  | head :: heads, stream => if head.stream = stream then some head else headFor? heads stream

private def replaceHead (heads : List HeadWire) (successor : HeadWire) : List HeadWire :=
  heads.map fun head => if head.stream = successor.stream then successor else head

private def inputHeadValidB (coordinate : CoordinateWire) (head : HeadWire) : Bool :=
  head.stream.world = coordinate.world && head.stream.validB &&
    head.stream.kind ≤ WIRE_U64_MAX && head.stream.version ≤ WIRE_U64_MAX &&
    head.sequence ≤ WIRE_U64_MAX && head.semanticHead != zeroDigest &&
    head.storageHeadDigest != zeroDigest && head.projectionDigest != zeroDigest &&
    head.projection.validB &&
    head.projectionDigest = digestBytes PROJECTION_DIGEST_DOMAIN head.projection.bytes &&
    (head.origin = "existing" || (head.origin = "genesis" && head.sequence = 0))

def initialHeadsDigestInput? (input : InitialHeadsDigestInputWire) :
    Option InitialHeadsDigestOutputWire := do
  if input.initialHeads.isEmpty || input.initialHeads.length > MAX_EVENTS then none else
  if !input.coordinate.validB then none else
  if input.coordinate.world.contentEpoch > WIRE_U64_MAX ||
      input.coordinate.commitOrdinal > WIRE_U64_MAX then none else
  if !(streamIds input.initialHeads).Nodup then none else
  if !input.initialHeads.all (inputHeadValidB input.coordinate) then none else
  let digest := initialHeadsDigest input.initialHeads
  if digest = zeroDigest then none else
  some { initialHeadsDigest := digest }

def initialHeadsDigestBytes? (bytes : String) : Option String := do
  let input ← decodeInitialHeadsDigestInput bytes
  let output ← initialHeadsDigestInput? input
  some output.toJson

private def candidateValidB (event : CandidateEventWire) : Bool :=
  event.eventIndex ≤ WIRE_U32_MAX && event.statement.kind ≤ WIRE_U64_MAX &&
    event.statement.version ≤ WIRE_U64_MAX && event.statement.sequence ≤ WIRE_U64_MAX &&
    event.statement.predecessor != zeroDigest && event.statement.payloadDigest != zeroDigest &&
    event.eventDigest != zeroDigest && event.successorProjectionDigest != zeroDigest &&
    event.payload.validB && event.successorProjection.validB &&
    event.statement.payloadDigest = digestBytes PAYLOAD_DIGEST_DOMAIN event.payload.bytes &&
    event.eventDigest = digestBoundary.eventDigest event.statement.toSemantic &&
    event.successorProjectionDigest =
      digestBytes PROJECTION_DIGEST_DOMAIN event.successorProjection.bytes

private def bindingMatchesB (coordinate : CoordinateWire) (event : CandidateEventWire)
    (binding : AuthorityEventBindingWire) : Bool :=
  binding.eventIndex = event.eventIndex && binding.receiptHash = coordinate.receiptHash &&
    binding.actorRoot = coordinate.actorRoot && binding.signer = coordinate.signer &&
    binding.eventDigest = event.eventDigest &&
    binding.payloadDigest = event.statement.payloadDigest &&
    binding.successorProjectionDigest = event.successorProjectionDigest &&
    binding.successorStorageHeadDigest != zeroDigest

private def eventBatchInitialHeads (heads : List HeadWire) : List EventBatch.StreamHead :=
  heads.map fun head => {
    stream := head.stream.toSemantic
    sequence := head.sequence
    head := head.semanticHead
  }

private def prepareEvents : CoordinateWire → Nat → List StreamWire → List HeadWire →
    List CandidateEventWire → List AuthorityEventBindingWire →
    Option (List PreparedEventWire × List HeadWire)
  | _, _, _, heads, [], [] => some ([], heads)
  | coordinate, expectedIndex, seen, heads, event :: events, binding :: bindings => do
      if event.eventIndex != expectedIndex then none else
      if !candidateValidB event then none else
      if !bindingMatchesB coordinate event binding then none else
      let stream := StreamWire.mk coordinate.world event.statement.kind
        event.statement.key event.statement.version
      let before ← headFor? heads stream
      if event.statement.sequence != before.sequence + 1 then none else
      if event.statement.predecessor != before.semanticHead then none else
      let firstUse := !decide (stream ∈ seen)
      let genesisProjection :=
        if firstUse && before.origin = "genesis" then some before.projection else none
      let genesisProjectionDigest :=
        if firstUse && before.origin = "genesis" then some before.projectionDigest else none
      let prepared : PreparedEventWire := {
        eventIndex := event.eventIndex
        stream
        sequence := event.statement.sequence
        expectedPredecessorHeadDigest := before.storageHeadDigest
        semanticPredecessor := event.statement.predecessor
        eventDigest := event.eventDigest
        payloadDigest := event.statement.payloadDigest
        payload := event.payload
        successorProjectionDigest := event.successorProjectionDigest
        successorProjection := event.successorProjection
        genesisProjectionDigest
        genesisProjection
      }
      let successor : HeadWire := {
        stream
        sequence := event.statement.sequence
        semanticHead := event.eventDigest
        storageHeadDigest := binding.successorStorageHeadDigest
        projectionDigest := event.successorProjectionDigest
        projection := event.successorProjection
        origin := "existing"
      }
      let (rest, successors) ← prepareEvents coordinate (expectedIndex + 1)
        (stream :: seen) (replaceHead heads successor) events bindings
      some (prepared :: rest, successors)
  | _, _, _, _, _, _ => none

def planInput? (input : InputWire) : Option PreparedBatchWire := do
  if input.events.isEmpty || input.events.length > MAX_EVENTS then none else
  if input.initialHeads.isEmpty || input.initialHeads.length > MAX_EVENTS then none else
  if input.authority.coordinate != input.coordinate then none else
  if !input.coordinate.validB then none else
  if input.coordinate.world.contentEpoch > WIRE_U64_MAX ||
      input.coordinate.commitOrdinal > WIRE_U64_MAX then none else
  if input.authority.initialHeadsDigest != initialHeadsDigest input.initialHeads then none else
  if input.authority.events.length != input.events.length then none else
  if !(streamIds input.initialHeads).Nodup then none else
  if !input.initialHeads.all (inputHeadValidB input.coordinate) then none else
  let statement : EventBatch.Statement := {
    coordinate := input.coordinate.toSemantic
    events := input.events.map CandidateEventWire.toIndexed
  }
  let batchDigest := digestBoundary.batchDigest statement
  if batchDigest = zeroDigest then none else
  let applied ← (EventBatch.applyBatch digestBoundary (eventBatchInitialHeads input.initialHeads)
    { statement, batchDigest }).toOption
  let (events, successorHeads) ← prepareEvents input.coordinate 0 [] input.initialHeads
    input.events input.authority.events
  if applied.events != statement.events then none else
  if applied.successorHeads != eventBatchInitialHeads successorHeads then none else
  let statementJson := semanticStatementToJson statement
  some {
    coordinate := input.coordinate
    leanStatement := ⟨statementJson.toUTF8.toList.map UInt8.toNat⟩
    batchDigest := applied.batchDigest
    events
    successorHeads
  }

def planBytes? (bytes : String) : Option String := do
  let input ← decodeInput bytes
  let prepared ← planInput? input
  some prepared.toJson

/-- Privileged host-only export.  JSON syntax is not authority; callers must
never be allowed to supply `authority` before the finalized native seam has
constructed it from the carrying CommitRecord and game-judge result. -/
@[export dregg_poa_event_batch_runtime_plan]
def planFFI (bytes : String) : String := (planBytes? bytes).getD ""

/-- Host-only digest adapter for the exact canonical
`POA-EVENT-BATCH-INITIAL-HEADS-IN-1` request.  It emits one canonical
`POA-EVENT-BATCH-INITIAL-HEADS-DIGEST-1` object, or the empty string on any
syntax, canonicality, bound, identity, duplicate-stream, or cross-world
failure.  This does not construct a native head or grant planner authority. -/
@[export dregg_poa_event_batch_runtime_initial_heads_digest]
def initialHeadsDigestFFI (bytes : String) : String :=
  (initialHeadsDigestBytes? bytes).getD ""

theorem planInput_deterministic (input : InputWire) (left right : PreparedBatchWire)
    (hl : planInput? input = some left) (hr : planInput? input = some right) : left = right := by
  rw [hl] at hr
  exact Option.some.inj hr

/-! ## Multi-stream fixture and hostile teeth

⚑ **THE TEETH NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target. The teeth's
STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition beside the
private fixture material; the EVALUATION — each `check_* = true`, pinned by
`native_decide` + `#assert_compiled` — lives in `EventBatchRuntimeFixtures.lean`, rooted
in the `PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a
stale fixture reds the guard library instead of the archive. The `@[export]` FFI surface
(`planFFI`, `initialHeadsDigestFFI`) is untouched. Fail-closed convention: plan-shape
checks match on `planInput?` and answer `false` on `none`. Named residue: none. -/

private def fixtureDigest (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def fixtureWorld : WorldWire := {
  federationId := fixtureDigest 1
  contentRoot := fixtureDigest 2
  activationDigest := fixtureDigest 3
  contentSession := fixtureDigest 4
  contentEpoch := 5
}

private def fixtureCoordinate : CoordinateWire := {
  world := fixtureWorld
  commitOrdinal := 7
  blockId := fixtureDigest 8
  turnHash := fixtureDigest 9
  receiptHash := fixtureDigest 10
  actorRoot := fixtureDigest 11
  signer := fixtureDigest 12
}

private def fixtureStream (kind key : Nat) : StreamWire := {
  world := fixtureWorld
  kind
  key := fixtureDigest key
  version := 1
}

private def fixtureBytes (values : List Nat) : OpaqueBytes := ⟨values⟩

private def fixtureHead (kind key genesis storage projection : Nat) : HeadWire :=
  let bytes := fixtureBytes [projection, projection + 1]
  {
    stream := fixtureStream kind key
    sequence := 0
    semanticHead := fixtureDigest genesis
    storageHeadDigest := fixtureDigest storage
    projectionDigest := digestBytes PROJECTION_DIGEST_DOMAIN bytes.bytes
    projection := bytes
    origin := "genesis"
  }

private def canonHead : HeadWire := fixtureHead 2 20 30 31 32
private def attendantHead : HeadWire := fixtureHead 10 21 40 41 42

private def fixtureEvent (eventIndex : Nat) (stream : StreamWire) (sequence : Nat)
    (predecessor : Digest32) (payload projection : List Nat) : CandidateEventWire :=
  let payloadBytes := fixtureBytes payload
  let projectionBytes := fixtureBytes projection
  let statement : StatementWire := {
    namespaceId := stream.world.federationId
    kind := stream.kind
    key := stream.key
    version := stream.version
    sequence
    predecessor
    payloadDigest := digestBytes PAYLOAD_DIGEST_DOMAIN payloadBytes.bytes
  }
  {
    eventIndex
    statement
    eventDigest := digestBoundary.eventDigest statement.toSemantic
    payload := payloadBytes
    successorProjectionDigest := digestBytes PROJECTION_DIGEST_DOMAIN projectionBytes.bytes
    successorProjection := projectionBytes
  }

private def firstCanon : CandidateEventWire :=
  fixtureEvent 0 canonHead.stream 1 canonHead.semanticHead [1, 2, 3] [10, 11]

private def attendant : CandidateEventWire :=
  fixtureEvent 1 attendantHead.stream 1 attendantHead.semanticHead [4, 5] [12, 13]

private def secondCanon : CandidateEventWire :=
  fixtureEvent 2 canonHead.stream 2 firstCanon.eventDigest [6, 7] [14, 15]

private def fixtureEvents : List CandidateEventWire := [firstCanon, attendant, secondCanon]

private def fixtureBinding (event : CandidateEventWire) (storage : Nat) :
    AuthorityEventBindingWire := {
  eventIndex := event.eventIndex
  receiptHash := fixtureCoordinate.receiptHash
  actorRoot := fixtureCoordinate.actorRoot
  signer := fixtureCoordinate.signer
  eventDigest := event.eventDigest
  payloadDigest := event.statement.payloadDigest
  successorProjectionDigest := event.successorProjectionDigest
  successorStorageHeadDigest := fixtureDigest storage
}

private def fixtureHeads : List HeadWire := [canonHead, attendantHead]

private def fixtureInput : InputWire := {
  authority := {
    coordinate := fixtureCoordinate
    initialHeadsDigest := initialHeadsDigest fixtureHeads
    events := [fixtureBinding firstCanon 50, fixtureBinding attendant 51,
      fixtureBinding secondCanon 52]
  }
  coordinate := fixtureCoordinate
  initialHeads := fixtureHeads
  events := fixtureEvents
}

private def fixtureInitialHeadsDigestInput : InitialHeadsDigestInputWire := {
  coordinate := fixtureCoordinate
  initialHeads := fixtureHeads
}

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_canonical_decode_accepts : Bool :=
  decide (decodeInput fixtureInput.toJson = some fixtureInput)

/-- Fail-closed: a refused plan answers `false`.
(Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_multi_stream_repeated_stream_plans : Bool :=
  match planInput? fixtureInput with
  | none => false
  | some prepared =>
      prepared.events.length == 3 &&
      (headFor? prepared.successorHeads canonHead.stream).map HeadWire.sequence == some 2 &&
      (headFor? prepared.successorHeads attendantHead.stream).map HeadWire.sequence == some 1

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_repeated_stream_uses_prior_successor_storage_digest : Bool :=
  match planInput? fixtureInput with
  | some prepared =>
      (prepared.events[2]?).map PreparedEventWire.expectedPredecessorHeadDigest ==
        some (fixtureDigest 50)
  | none => false

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_ffi_emits_nonempty_canonical_plan : Bool :=
  planFFI fixtureInput.toJson != ""

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_initial_heads_digest_export_is_exact : Bool :=
  decide (initialHeadsDigestFFI fixtureInitialHeadsDigestInput.toJson =
    (InitialHeadsDigestOutputWire.mk (initialHeadsDigest fixtureHeads)).toJson)

private def crossWorldHeadsInput : InitialHeadsDigestInputWire :=
  let foreignWorld := { fixtureWorld with contentSession := fixtureDigest 99 }
  let foreignStream := { canonHead.stream with world := foreignWorld }
  let foreignHead := { canonHead with stream := foreignStream }
  { fixtureInitialHeadsDigestInput with initialHeads := [foreignHead, attendantHead] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_initial_heads_digest_cross_world_refused : Bool :=
  decide (initialHeadsDigestFFI crossWorldHeadsInput.toJson = "")

private def zeroWorldHeadsInput : InitialHeadsDigestInputWire :=
  let zeroWorld := { fixtureWorld with contentEpoch := 0 }
  { fixtureInitialHeadsDigestInput with
    coordinate := { fixtureCoordinate with world := zeroWorld } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_initial_heads_digest_zero_world_refused : Bool :=
  decide (initialHeadsDigestFFI zeroWorldHeadsInput.toJson = "")

private def reorderedInput : InputWire :=
  { fixtureInput with events := [attendant, firstCanon, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_reorder_refused : Bool := (planInput? reorderedInput).isNone

private def payloadMutationInput : InputWire :=
  let changed := { firstCanon with payload := fixtureBytes [99, 2, 3] }
  { fixtureInput with events := [changed, attendant, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_payload_mutation_refused : Bool := (planInput? payloadMutationInput).isNone

private def projectionMutationInput : InputWire :=
  let changed := { attendant with successorProjection := fixtureBytes [99, 13] }
  { fixtureInput with events := [firstCanon, changed, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_projection_mutation_refused : Bool :=
  (planInput? projectionMutationInput).isNone

private def crossWorldInput : InputWire :=
  let foreignWorld := { fixtureWorld with activationDigest := fixtureDigest 99 }
  { fixtureInput with coordinate := { fixtureCoordinate with world := foreignWorld } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_cross_world_refused : Bool := (planInput? crossWorldInput).isNone

private def crossActorInput : InputWire :=
  { fixtureInput with coordinate := { fixtureCoordinate with actorRoot := fixtureDigest 99 } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_cross_actor_refused : Bool := (planInput? crossActorInput).isNone

private def forgedActorBindingInput : InputWire :=
  let first := { fixtureBinding firstCanon 50 with actorRoot := fixtureDigest 99 }
  { fixtureInput with authority := { fixtureInput.authority with events :=
    [first, fixtureBinding attendant 51, fixtureBinding secondCanon 52] } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_authority_actor_binding_refused : Bool :=
  (planInput? forgedActorBindingInput).isNone

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_noncanonical_trailing_byte_refused : Bool :=
  (decodeInput (fixtureInput.toJson ++ " ")).isNone

private def unknownFieldBytes : String :=
  (fixtureInput.toJson.dropEnd 1).toString ++ ",\"extra\":0}"

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_unknown_field_refused : Bool := (decodeInput unknownFieldBytes).isNone

private def emptyBatchInput : InputWire :=
  { fixtureInput with
    authority := { fixtureInput.authority with events := [] }
    events := [] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_empty_batch_refused : Bool := (planInput? emptyBatchInput).isNone

private def oversizedEventCountInput : InputWire :=
  { fixtureInput with
    authority := { fixtureInput.authority with
      events := List.replicate (MAX_EVENTS + 1) (fixtureBinding firstCanon 50) }
    events := List.replicate (MAX_EVENTS + 1) firstCanon }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_event_count_refused : Bool := (planInput? oversizedEventCountInput).isNone

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_wire_size_refused : Bool :=
  (decodeInputWithLimit 4 fixtureInput.toJson).isNone

private def u64OverflowInput : InputWire :=
  let coordinate := { fixtureCoordinate with
    world := { fixtureWorld with contentEpoch := 2 ^ 64 } }
  { fixtureInput with
    coordinate
    authority := { fixtureInput.authority with coordinate } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_u64_overflow_refused : Bool := (planInput? u64OverflowInput).isNone

private def sequenceOverflowInput : InputWire :=
  let event := { firstCanon with statement := { firstCanon.statement with sequence := 2 ^ 64 } }
  { fixtureInput with events := [event, attendant, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_sequence_overflow_refused : Bool :=
  (planInput? sequenceOverflowInput).isNone

#assert_axioms canonicalDecode_reencodes
#assert_axioms decodeInput_reencodes
#assert_axioms decodeInput_refuses_oversized
#assert_axioms planInput_deterministic

-- The twenty teeth pins (`#assert_compiled` + `native_decide`) live in
-- `EventBatchRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the teeth header
-- above.

end Dregg2.Games.PathOfAngels.EventBatchRuntime
