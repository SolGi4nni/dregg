/-
# WorldActivation — one active Path of Angels world, with signed lineage

An `EventBatch.WorldIdentity` is not active merely because a caller can spell
it.  This module owns the structural authority which selects the one exact
identity against which finalized PoA batches may be admitted.

The curator signature is intentionally an explicit native precondition.  Lean
does not claim to verify Ed25519 here: the host must verify the exact canonical
`ActivationStatement.toJson` bytes under an independently distributed key pin,
then pass `native_signature_verified = true`.  Lean still checks that the key
carried by the signed envelope is the external pin, and owns every transition,
counter, predecessor, epoch, rollback-lineage, and exact-world decision.

The first record is a bootstrap because this authority can be installed around
an already-active beta counter.  Every later advance increments both counter
and content epoch exactly once.  A rollback also increments the counter, names
an earlier envelope digest, and restores that record's entire `WorldIdentity`.
It is therefore a new auditable activation, never deletion or head rewinding.
-/
import Lean.Data.Json
import Dregg2.Bridge.MinaStateHashDerive
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.WorldActivation

open Lean
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev WorldIdentity := EventBatch.WorldIdentity

abbrev INPUT_FORMAT : String := "POA-WORLD-ACTIVATION-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-WORLD-ACTIVATION-OUT-1"
abbrev AUTHORIZE_INPUT_FORMAT : String := "POA-WORLD-AUTHORIZE-IN-1"
abbrev STATEMENT_SCHEMA : String := "POA-WORLD-ACTIVATION-STATEMENT-1"
abbrev WIRE_BYTE_LIMIT : Nat := 16 * 1024 * 1024
abbrev HISTORY_LIMIT : Nat := 4096
abbrev WIRE_U64_LIMIT : Nat := 2 ^ 64 - 1

structure Signature64 where
  bytes : List (Fin 256)
  length_eq : bytes.length = 64
deriving DecidableEq

inductive ActivationKind where
  | advance
  | rollback
deriving DecidableEq, Repr

structure ActivationStatement where
  world : WorldIdentity
  counter : Nat
  predecessorHead : Digest32
  kind : ActivationKind
  rollbackTarget : Option Digest32
deriving DecidableEq

structure SignedActivationEnvelope where
  statement : ActivationStatement
  curatorKey : Digest32
  signature : Signature64
deriving DecidableEq

structure ActivationRecord where
  envelope : SignedActivationEnvelope
  envelopeDigest : Digest32
deriving DecidableEq

/-- Chronological, append-only activation lineage.  The final record is active. -/
abbrev State := List ActivationRecord

inductive Error where
  | malformedWire
  | inputTooLarge
  | historyTooLarge
  | invalidHistory
  | worldHasZeroIdentity
  | integerOutOfRange
  | wrongCuratorKey
  | nativeSignatureNotVerified
  | wrongEnvelopeDigest
  | bootstrapMustAdvance
  | bootstrapHasPredecessor
  | bootstrapHasRollbackTarget
  | wrongCounter
  | wrongPredecessor
  | wrongFederation
  | staleOrSkippedEpoch
  | advanceHasRollbackTarget
  | rollbackTargetMissing
  | rollbackTargetsCurrentHead
  | rollbackWorldMismatch
deriving DecidableEq, Repr

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

private def nonzero (digest : Digest32) : Bool := digest != zeroDigest

def validWorld (world : WorldIdentity) : Bool :=
  nonzero world.federationId &&
  nonzero world.contentRoot &&
  nonzero world.activationDigest &&
  nonzero world.contentSession &&
  0 < world.contentEpoch.value && world.contentEpoch.value ≤ WIRE_U64_LIMIT

private def jsonString (value : String) : String := String.quote value
private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"
private def jsonBool (value : Bool) : String := if value then "true" else "false"

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def byteHex (byte : Fin 256) : String :=
  String.ofList [lowerHexDigit (byte.val / 16), lowerHexDigit (byte.val % 16)]

private def bytesHex (bytes : List (Fin 256)) : String :=
  String.join (bytes.map byteHex)

private def hexNibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else none

private def parseByte? (high low : Char) : Option (Fin 256) := do
  let h ← hexNibble? high
  let l ← hexNibble? low
  let value := 16 * h + l
  if bound : value < 256 then some ⟨value, bound⟩ else none

private def parseHexBytes? : List Char → Option (List (Fin 256))
  | [] => some []
  | high :: low :: rest => do
      let byte ← parseByte? high low
      pure (byte :: (← parseHexBytes? rest))
  | _ => none

private def parseSignature? (spelling : String) : Option Signature64 := do
  if !Emit.isLowerHexOfLength 128 spelling then none else
  let bytes ← parseHexBytes? spelling.toList
  if length : bytes.length = 64 then some { bytes, length_eq := length } else none

private def kindLabel : ActivationKind → String
  | .advance => "advance"
  | .rollback => "rollback"

def WorldIdentity.toJson (world : WorldIdentity) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex world.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex world.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex world.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex world.contentSession) ++
    ",\"content_epoch\":" ++ toString world.contentEpoch.value ++ "}"

def ActivationStatement.toJson (statement : ActivationStatement) : String :=
  "{\"schema\":" ++ jsonString STATEMENT_SCHEMA ++
    ",\"world\":" ++ statement.world.toJson ++
    ",\"counter\":" ++ toString statement.counter ++
    ",\"predecessor_head\":" ++ jsonString (Emit.bytes32Hex statement.predecessorHead) ++
    ",\"kind\":" ++ jsonString (kindLabel statement.kind) ++
    ",\"rollback_target\":" ++
      (match statement.rollbackTarget with
       | none => "null"
       | some digest => jsonString (Emit.bytes32Hex digest)) ++ "}"

def SignedActivationEnvelope.toJson (envelope : SignedActivationEnvelope) : String :=
  "{\"statement\":" ++ envelope.statement.toJson ++
    ",\"curator_key\":" ++ jsonString (Emit.bytes32Hex envelope.curatorKey) ++
    ",\"signature\":" ++ jsonString (bytesHex envelope.signature.bytes) ++ "}"

def ActivationRecord.toJson (record : ActivationRecord) : String :=
  "{\"envelope\":" ++ record.envelope.toJson ++
    ",\"envelope_digest\":" ++ jsonString (Emit.bytes32Hex record.envelopeDigest) ++ "}"

def stateToJson (state : State) : String :=
  "{\"history\":" ++ jsonArray (state.map ActivationRecord.toJson) ++ "}"

private def utf8Nats (value : String) : List Nat :=
  value.toUTF8.toList.map UInt8.toNat

private def natByteHex (value : Nat) : String :=
  String.ofList [lowerHexDigit (value / 16), lowerHexDigit (value % 16)]

/-- SHA-256 of the exact canonical signed-envelope bytes. -/
def envelopeDigest? (envelope : SignedActivationEnvelope) : Option Digest32 :=
  Emit.parseBytes32Hex? (String.join
    ((Dregg2.Bridge.MinaStateHashDerive.sha256 (utf8Nats envelope.toJson)).map natByteHex))

private def findRecord? (history : State) (digest : Digest32) : Option ActivationRecord :=
  history.find? fun record => record.envelopeDigest = digest

private def head? (history : State) : Option ActivationRecord := history.getLast?

private def applyStructural (pin : Digest32) (history : State)
    (envelope : SignedActivationEnvelope) : Except Error State := do
  if !nonzero pin || !nonzero envelope.curatorKey then throw .wrongCuratorKey
  if envelope.curatorKey != pin then throw .wrongCuratorKey
  if !validWorld envelope.statement.world then throw .worldHasZeroIdentity
  if envelope.statement.counter > WIRE_U64_LIMIT then throw .integerOutOfRange
  if history.length ≥ HISTORY_LIMIT then throw .historyTooLarge
  match head? history with
  | none =>
      if envelope.statement.kind != .advance then throw .bootstrapMustAdvance
      if envelope.statement.predecessorHead != zeroDigest then throw .bootstrapHasPredecessor
      if envelope.statement.rollbackTarget.isSome then throw .bootstrapHasRollbackTarget
      if envelope.statement.counter = 0 then throw .wrongCounter
  | some current =>
      if envelope.statement.counter != current.envelope.statement.counter + 1 then
        throw .wrongCounter
      if envelope.statement.predecessorHead != current.envelopeDigest then
        throw .wrongPredecessor
      if envelope.statement.world.federationId !=
          current.envelope.statement.world.federationId then
        throw .wrongFederation
      match envelope.statement.kind with
      | .advance =>
          if envelope.statement.rollbackTarget.isSome then throw .advanceHasRollbackTarget
          if envelope.statement.world.contentEpoch.value !=
              current.envelope.statement.world.contentEpoch.value + 1 then
            throw .staleOrSkippedEpoch
      | .rollback =>
          let targetDigest ← match envelope.statement.rollbackTarget with
            | none => throw .rollbackTargetMissing
            | some digest => pure digest
          if targetDigest = current.envelopeDigest then throw .rollbackTargetsCurrentHead
          let target ← match findRecord? history targetDigest with
            | none => throw .rollbackTargetMissing
            | some record => pure record
          if envelope.statement.world != target.envelope.statement.world then
            throw .rollbackWorldMismatch
  let digest ← match envelopeDigest? envelope with
    | none => throw .wrongEnvelopeDigest
    | some digest => pure digest
  pure (history ++ [{ envelope, envelopeDigest := digest }])

/-- Reconstruct and validate every structural edge, not only the final head. -/
def replayHistory (pin : Digest32) (records : State) : Except Error State :=
  records.foldlM (fun history record => do
    let digest ← match envelopeDigest? record.envelope with
      | none => throw .wrongEnvelopeDigest
      | some digest => pure digest
    if digest != record.envelopeDigest then throw .wrongEnvelopeDigest
    applyStructural pin history record.envelope) []

/-- Admit a native-signature-verified envelope against a fully replayed lineage. -/
def admit (externalPin : Digest32) (nativeSignatureVerified : Bool)
    (state : State) (envelope : SignedActivationEnvelope) : Except Error State := do
  if !nativeSignatureVerified then throw .nativeSignatureNotVerified
  let replayed ← replayHistory externalPin state
  if replayed != state then throw .invalidHistory
  applyStructural externalPin state envelope

/-- The exact active identity; no federation-only or epoch-only projection exists. -/
def activeWorld? (state : State) : Option WorldIdentity :=
  (head? state).map fun record => record.envelope.statement.world

/-- Future batch admission uses this equality against the durable active head. -/
def authorizesWorld (state : State) (candidate : WorldIdentity) : Bool :=
  activeWorld? state == some candidate

/-! ## Strict canonical JSON boundary -/

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

private def parseWorld (json : Json) : Except String WorldIdentity := do
  exactKeys json ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch"]
  pure {
    federationId := ← objectDigest json "federation_id"
    contentRoot := ← objectDigest json "content_root"
    activationDigest := ← objectDigest json "activation_digest"
    contentSession := ← objectDigest json "content_session"
    contentEpoch := ⟨← objectNat json "content_epoch"⟩
  }

private def parseKind : String → Except String ActivationKind
  | "advance" => pure .advance
  | "rollback" => pure .rollback
  | _ => throw "unknown activation kind"

private def parseOptionalDigest (json : Json) : Except String (Option Digest32) :=
  match json with
  | .null => pure none
  | .str spelling => match Emit.parseBytes32Hex? spelling with
      | some digest => pure (some digest)
      | none => throw "rollback target is not a canonical digest"
  | _ => throw "rollback target must be null or digest"

private def parseStatement (json : Json) : Except String ActivationStatement := do
  exactKeys json ["schema", "world", "counter", "predecessor_head", "kind", "rollback_target"]
  if (← json.getObjValAs? String "schema") != STATEMENT_SCHEMA then
    throw "wrong statement schema"
  pure {
    world := ← parseWorld (← json.getObjVal? "world")
    counter := ← objectNat json "counter"
    predecessorHead := ← objectDigest json "predecessor_head"
    kind := ← parseKind (← json.getObjValAs? String "kind")
    rollbackTarget := ← parseOptionalDigest (← json.getObjVal? "rollback_target")
  }

private def parseEnvelope (json : Json) : Except String SignedActivationEnvelope := do
  exactKeys json ["statement", "curator_key", "signature"]
  let signatureSpelling ← json.getObjValAs? String "signature"
  let signature ← match parseSignature? signatureSpelling with
    | none => throw "signature must be exactly 128 lowercase hexadecimal digits"
    | some signature => pure signature
  pure {
    statement := ← parseStatement (← json.getObjVal? "statement")
    curatorKey := ← objectDigest json "curator_key"
    signature
  }

private def parseRecord (json : Json) : Except String ActivationRecord := do
  exactKeys json ["envelope", "envelope_digest"]
  pure {
    envelope := ← parseEnvelope (← json.getObjVal? "envelope")
    envelopeDigest := ← objectDigest json "envelope_digest"
  }

private def parseState (json : Json) : Except String State := do
  exactKeys json ["history"]
  let values := (← (← json.getObjVal? "history").getArr?).toList
  if values.length > HISTORY_LIMIT then throw "history exceeds bound"
  values.mapM parseRecord

structure InputWire where
  externalCuratorKeyPin : Digest32
  nativeSignatureVerified : Bool
  state : State
  envelope : SignedActivationEnvelope
deriving DecidableEq

def InputWire.toJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"external_curator_key_pin\":" ++
      jsonString (Emit.bytes32Hex input.externalCuratorKeyPin) ++
    ",\"native_signature_verified\":" ++ jsonBool input.nativeSignatureVerified ++
    ",\"state\":" ++ stateToJson input.state ++
    ",\"envelope\":" ++ input.envelope.toJson ++ "}"

private def parseInput (json : Json) : Except String InputWire := do
  exactKeys json ["format", "external_curator_key_pin", "native_signature_verified", "state",
    "envelope"]
  if (← json.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  pure {
    externalCuratorKeyPin := ← objectDigest json "external_curator_key_pin"
    nativeSignatureVerified := ← json.getObjValAs? Bool "native_signature_verified"
    state := ← parseState (← json.getObjVal? "state")
    envelope := ← parseEnvelope (← json.getObjVal? "envelope")
  }

private def canonicalDecode (bytes : String) : Option InputWire :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json => match parseInput json with
      | .error _ => none
      | .ok input => if input.toJson = bytes then some input else none

def decodeInputWithLimit (limit : Nat) (bytes : String) : Option InputWire :=
  if bytes.utf8ByteSize ≤ limit then canonicalDecode bytes else none

def decodeInput (bytes : String) : Option InputWire := decodeInputWithLimit WIRE_BYTE_LIMIT bytes

structure AuthorizeInputWire where
  externalCuratorKeyPin : Digest32
  nativeSignaturesVerified : Bool
  state : State
  candidate : WorldIdentity
deriving DecidableEq

def AuthorizeInputWire.toJson (input : AuthorizeInputWire) : String :=
  "{\"format\":" ++ jsonString AUTHORIZE_INPUT_FORMAT ++
    ",\"external_curator_key_pin\":" ++
      jsonString (Emit.bytes32Hex input.externalCuratorKeyPin) ++
    ",\"native_signatures_verified\":" ++ jsonBool input.nativeSignaturesVerified ++
    ",\"state\":" ++ stateToJson input.state ++
    ",\"candidate\":" ++ input.candidate.toJson ++ "}"

private def parseAuthorizeInput (json : Json) : Except String AuthorizeInputWire := do
  exactKeys json ["format", "external_curator_key_pin", "native_signatures_verified", "state",
    "candidate"]
  if (← json.getObjValAs? String "format") != AUTHORIZE_INPUT_FORMAT then
    throw "wrong authorize input format"
  pure {
    externalCuratorKeyPin := ← objectDigest json "external_curator_key_pin"
    nativeSignaturesVerified := ← json.getObjValAs? Bool "native_signatures_verified"
    state := ← parseState (← json.getObjVal? "state")
    candidate := ← parseWorld (← json.getObjVal? "candidate")
  }

private def decodeAuthorizeInput (bytes : String) : Option AuthorizeInputWire :=
  if bytes.utf8ByteSize > WIRE_BYTE_LIMIT then none else
  match Json.parse bytes with
  | .error _ => none
  | .ok json => match parseAuthorizeInput json with
      | .error _ => none
      | .ok input => if input.toJson = bytes then some input else none

theorem decodeInput_reencodes {bytes : String} {input : InputWire}
    (accepted : decodeInput bytes = some input) : input.toJson = bytes := by
  simp only [decodeInput, decodeInputWithLimit] at accepted
  split at accepted <;> try contradiction
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  exact equal

private def Error.label : Error → String
  | .malformedWire => "malformed-wire"
  | .inputTooLarge => "input-too-large"
  | .historyTooLarge => "history-too-large"
  | .invalidHistory => "invalid-history"
  | .worldHasZeroIdentity => "world-has-zero-identity"
  | .integerOutOfRange => "integer-out-of-range"
  | .wrongCuratorKey => "wrong-curator-key"
  | .nativeSignatureNotVerified => "native-signature-not-verified"
  | .wrongEnvelopeDigest => "wrong-envelope-digest"
  | .bootstrapMustAdvance => "bootstrap-must-advance"
  | .bootstrapHasPredecessor => "bootstrap-has-predecessor"
  | .bootstrapHasRollbackTarget => "bootstrap-has-rollback-target"
  | .wrongCounter => "wrong-counter"
  | .wrongPredecessor => "wrong-predecessor"
  | .wrongFederation => "wrong-federation"
  | .staleOrSkippedEpoch => "stale-or-skipped-epoch"
  | .advanceHasRollbackTarget => "advance-has-rollback-target"
  | .rollbackTargetMissing => "rollback-target-missing"
  | .rollbackTargetsCurrentHead => "rollback-targets-current-head"
  | .rollbackWorldMismatch => "rollback-world-mismatch"

private def acceptedJson (state : State) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"status\":\"accepted\",\"state\":" ++ stateToJson state ++
    ",\"active_world\":" ++
      (match activeWorld? state with | none => "null" | some world => world.toJson) ++ "}"

private def refusedJson (error : Error) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"status\":\"refused\",\"reason\":" ++ jsonString error.label ++ "}"

/-- Callable authority.  `native_signature_verified` is an explicit native
precondition, not a Lean proof of Ed25519. -/
@[export dregg_poa_world_activation_judge]
def judgeWire (bytes : String) : String :=
  if bytes.utf8ByteSize > WIRE_BYTE_LIMIT then refusedJson .inputTooLarge else
  match decodeInput bytes with
  | none => refusedJson .malformedWire
  | some input => match admit input.externalCuratorKeyPin input.nativeSignatureVerified
      input.state input.envelope with
    | .error error => refusedJson error
    | .ok state => acceptedJson state

/-- Callable exact-world selector. Native persistence first re-verifies every Ed25519 signature;
this query then replays the entire structural lineage and makes the final all-five-field admission
decision in Lean rather than duplicating `authorizesWorld` in Rust. -/
@[export dregg_poa_world_activation_authorizes]
def authorizesWire (bytes : String) : String :=
  match decodeAuthorizeInput bytes with
  | none => "0"
  | some input =>
      if !input.nativeSignaturesVerified then "0" else
      match replayHistory input.externalCuratorKeyPin input.state with
      | .error _ => "0"
      | .ok replayed =>
          if replayed = input.state && authorizesWorld input.state input.candidate then "1" else "0"

/-! ## Executable honest and hostile witnesses -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def signatureByte (value : Nat) : Signature64 where
  bytes := List.replicate 64 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def world (epoch root activation session : Nat) : WorldIdentity where
  federationId := digestByte 1
  contentRoot := digestByte root
  activationDigest := digestByte activation
  contentSession := digestByte session
  contentEpoch := ⟨epoch⟩

private def pin := digestByte 90

private def bootstrapEnvelope : SignedActivationEnvelope where
  statement := {
    world := world 4 10 11 12
    counter := 4
    predecessorHead := zeroDigest
    kind := .advance
    rollbackTarget := none
  }
  curatorKey := pin
  signature := signatureByte 91

private def recordOf (envelope : SignedActivationEnvelope) : ActivationRecord where
  envelope
  envelopeDigest := (envelopeDigest? envelope).getD zeroDigest

private def bootstrapState : State := [recordOf bootstrapEnvelope]

private def successorEnvelope : SignedActivationEnvelope where
  statement := {
    world := world 5 20 21 22
    counter := 5
    predecessorHead := (recordOf bootstrapEnvelope).envelopeDigest
    kind := .advance
    rollbackTarget := none
  }
  curatorKey := pin
  signature := signatureByte 92

theorem honest_successor_accepts :
    (admit pin true bootstrapState successorEnvelope).isOk = true := by native_decide

theorem stale_epoch_refused :
    admit pin true bootstrapState
      { successorEnvelope with statement :=
        { successorEnvelope.statement with world := world 4 20 21 22 } } =
      .error .staleOrSkippedEpoch := by native_decide

theorem counter_skip_refused :
    admit pin true bootstrapState
      { successorEnvelope with statement := { successorEnvelope.statement with counter := 6 } } =
      .error .wrongCounter := by native_decide

theorem wrong_predecessor_refused :
    admit pin true bootstrapState
      { successorEnvelope with statement :=
        { successorEnvelope.statement with predecessorHead := digestByte 88 } } =
      .error .wrongPredecessor := by native_decide

theorem unrecorded_rollback_refused :
    let rollback := { successorEnvelope with statement :=
      { successorEnvelope.statement with
        world := bootstrapEnvelope.statement.world
        kind := .rollback
        rollbackTarget := some (digestByte 77) } }
    admit pin true bootstrapState rollback = .error .rollbackTargetMissing := by native_decide

theorem wrong_curator_key_refused :
    admit pin true bootstrapState { successorEnvelope with curatorKey := digestByte 89 } =
      .error .wrongCuratorKey := by native_decide

theorem unverified_native_signature_refused :
    admit pin false bootstrapState successorEnvelope =
      .error .nativeSignatureNotVerified := by native_decide

theorem same_federation_different_content_refused_by_active_world :
    authorizesWorld bootstrapState (world 4 99 11 12) = false := by native_decide

theorem same_federation_different_session_refused_by_active_world :
    authorizesWorld bootstrapState (world 4 10 11 99) = false := by native_decide

private def successorState : State :=
  (admit pin true bootstrapState successorEnvelope).toOption.getD []

private def rollbackEnvelope : SignedActivationEnvelope where
  statement := {
    world := bootstrapEnvelope.statement.world
    counter := 6
    predecessorHead := (recordOf successorEnvelope).envelopeDigest
    kind := .rollback
    rollbackTarget := some (recordOf bootstrapEnvelope).envelopeDigest
  }
  curatorKey := pin
  signature := signatureByte 93

theorem recorded_rollback_accepts_and_restores_exact_world :
    (admit pin true successorState rollbackEnvelope).map activeWorld? =
      .ok (some bootstrapEnvelope.statement.world) := by native_decide

theorem fixture_canonical_input_roundtrips :
    let input : InputWire := {
      externalCuratorKeyPin := pin
      nativeSignatureVerified := true
      state := bootstrapState
      envelope := successorEnvelope
    }
    decodeInput input.toJson = some input := by native_decide

theorem exact_world_query_accepts_head_and_refuses_other_content :
    let honest : AuthorizeInputWire := {
      externalCuratorKeyPin := pin
      nativeSignaturesVerified := true
      state := bootstrapState
      candidate := bootstrapEnvelope.statement.world
    }
    authorizesWire honest.toJson = "1" ∧
      authorizesWire { honest with candidate := world 4 99 11 12 }.toJson = "0" := by native_decide

#assert_axioms decodeInput_reencodes
#assert_compiled honest_successor_accepts
#assert_compiled stale_epoch_refused
#assert_compiled counter_skip_refused
#assert_compiled wrong_predecessor_refused
#assert_compiled unrecorded_rollback_refused
#assert_compiled wrong_curator_key_refused
#assert_compiled unverified_native_signature_refused
#assert_compiled same_federation_different_content_refused_by_active_world
#assert_compiled same_federation_different_session_refused_by_active_world
#assert_compiled recorded_rollback_accepts_and_restores_exact_world
#assert_compiled fixture_canonical_input_roundtrips
#assert_compiled exact_world_query_accepts_head_and_refuses_other_content

end Dregg2.Games.PathOfAngels.WorldActivation
