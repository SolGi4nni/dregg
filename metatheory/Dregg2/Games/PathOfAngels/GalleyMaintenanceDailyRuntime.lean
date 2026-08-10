/-
# Galley Maintenance Daily — THE Galley state machine, its wire, and its judge

⚑ THERE WAS A TWIN AND IT IS GONE (2026-08-05).  Until this commit there were two
Lean state machines named "Galley": this module's `reduce`, which is what
`@[export dregg_poa_galley_daily_judge]` runs and therefore the whole shipped
semantics, and `GalleyMaintenanceDaily.reduce` (ballot / authored procedure /
scarce commons / one finalized world output) plus `GalleyCommons` (settled-credit
commons economy) — ~5,100 lines with zero `@[export]`, no Rust call site, and a
capability/CAS tower whose contracts had no inhabitant anywhere in the tree.  The
two shared exactly one identifier, `MAX_LOCAL_SERVICE`, and no type, relation or
theorem.  The dark side is DELETED; the constant now lives here, where the wire
that uses it lives.  See `docs/poa/GALLEY-LAYER-CONTRACT.md` §0 for what proof
coverage went with it.

Lean is the only transition judge.  A request carries
the complete bounded event prefix, its claimed projection, one viewer, and
either no command or one opaque action token previously authored by this judge.
Lean replays the prefix from genesis, compares the complete projection, creates
the next event statement and both digests, applies it through `EventSourcing`,
and emits the complete successor projection, view, receipt, and replay witness.
`judge_command_projection_is_reduce` proves that the projection the judge
publishes is the one `reduce` returned, so the reducer facts below are facts
about the emitted bytes rather than about a function the export need not call.

The holder sponsor path is beta eligibility, not consensus holdings power.  Its
opaque authority records an RPC-attested binary holder class, exact signer/player
binding, deployment/daily/event context, one nullifier, and a short expiry.  It
contains no amount, weight, or governance privilege.  The only sponsor effect is
a bounded local-service acknowledgement; power, loot, and canon anchors are
definitionally carried unchanged.

The host remains responsible for deriving the policy/history from its durable
deployment and for issuing `BetaHolderAdmission` only after its signer and
short-lived holding-receipt checks.  The public string export cannot construct
that authority and therefore cannot execute a sponsor command.
-/
import Lean.Data.Json
import Mathlib.Data.List.Sort
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Games.PathOfAngels.EmitDigestHex
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime

open Lean
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-GALLEY-DAILY-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-GALLEY-DAILY-OUT-1"
abbrev BETA_HOLDER_FORMAT : String := "POA-GALLEY-BETA-HOLDER-1"
abbrev STREAM_KIND : Nat := 9
abbrev STREAM_VERSION : Nat := 1
abbrev WIRE_NAT_LIMIT : Nat := 2 ^ 64 - 1
abbrev WIRE_BYTE_LIMIT : Nat := 1024 * 1024
abbrev MAX_EVENTS : Nat := 64
/-- The type cap on one player's local-service score.  It used to be defined in
the deleted `GalleyMaintenanceDaily` kernel and re-exported here, which was the
twin's only remaining tether; it is now defined where the wire that bounds
`publicService` / `sponsorService` / `localService` against it lives.  Value
unchanged (100), so every emitted policy, fixture and pinned digest is
arithmetically identical. -/
abbrev MAX_LOCAL_SERVICE : Nat := 100
abbrev MAX_SPONSOR_SEQUENCE_TTL : Nat := 4

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

private def objectNat (j : Json) (key : String) (limit : Nat := WIRE_NAT_LIMIT) :
    Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

private def digestLess (left right : Digest32) : Bool :=
  Emit.bytes32Hex left < Emit.bytes32Hex right

private def digestLessP (left right : Digest32) : Prop :=
  digestLess left right = true

private instance digestLessPDecidable (left right : Digest32) :
    Decidable (digestLessP left right) := by
  unfold digestLessP digestLess
  infer_instance

private def canonicalDigestListB (values : List Digest32) : Bool :=
  values.length ≤ MAX_EVENTS && decide (values.Pairwise digestLessP)

private def insertDigest (value : Digest32) (values : List Digest32) : List Digest32 :=
  (value :: values).eraseDups.insertionSort digestLessP

/-! ## Proof-erased canonical wire values -/

structure PolicyWire where
  deploymentId : Digest32
  federationId : Digest32
  dailyId : Digest32
  genesisHead : Digest32
  dreggMint : Nat
  snapshotSlot : Nat
  contentEpoch : Nat
  eventId : Digest32
  rulesDigest : Digest32
  publicActivityId : Digest32
  sceneContentId : Digest32
  publicActionContentId : Digest32
  sponsorActionContentId : Digest32
  completeContentId : Digest32
  publicService : Nat
  sponsorService : Nat
  serviceTarget : Nat
  powerRoot : Digest32
  lootRoot : Digest32
  canonRoot : Digest32
  canonRevision : Nat
deriving DecidableEq

def PolicyWire.validB (policy : PolicyWire) : Bool :=
  decide (policy.publicService ≤ MAX_LOCAL_SERVICE) &&
  decide (policy.sponsorService ≤ MAX_LOCAL_SERVICE) &&
  decide (0 < policy.serviceTarget) &&
  decide (policy.serviceTarget ≤ MAX_EVENTS * MAX_LOCAL_SERVICE) &&
  decide (policy.canonRevision ≤ WIRE_NAT_LIMIT)

structure ViewerWire where
  player : Digest32
  playerCell : Digest32
  sponsorBeneficiary : Digest32
deriving DecidableEq

structure PayloadWire where
  kind : String
  actor : Digest32
  beneficiary : Digest32
  activityId : Digest32
  grantNullifier : Digest32
  authorityCommitment : Digest32
  localService : Nat
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

structure EventWire where
  statement : StatementWire
  payload : PayloadWire
  eventDigest : Digest32
deriving DecidableEq

structure ProjectionWire where
  sequence : Nat
  publicPlayers : List Digest32
  sponsors : List Digest32
  spentGrantNullifiers : List Digest32
  publicPlayCount : Nat
  sponsorshipCount : Nat
  localServiceTotal : Nat
  powerRoot : Digest32
  lootRoot : Digest32
  canonRoot : Digest32
  canonRevision : Nat
deriving DecidableEq

structure ActionRequestWire where
  kind : String
  token : Digest32
deriving DecidableEq

structure InputWire where
  mode : String
  policy : PolicyWire
  history : List EventWire
  claimedProjection : ProjectionWire
  viewer : ViewerWire
  action : ActionRequestWire
deriving DecidableEq

structure ActionTokenWire where
  kind : String
  token : Digest32
  actor : Digest32
  beneficiary : Digest32
  expiresAfterSequence : Nat
deriving DecidableEq

structure ViewWire where
  phase : String
  sceneContentId : Digest32
  statusContentId : Digest32
  progressCurrent : Nat
  progressTarget : Nat
  publicPlayCount : Nat
  sponsorshipCount : Nat
  availableActions : List ActionTokenWire
deriving DecidableEq

structure ReceiptWire where
  kind : String
  actor : Digest32
  beneficiary : Digest32
  sequence : Nat
  localService : Nat
  consumedGrantNullifier : Digest32
  authorityCommitment : Digest32
  powerDelta : Nat
  lootDelta : Nat
  canonRevisionDelta : Nat
deriving DecidableEq

structure ReplayWire where
  historyLength : Nat
  beforeSequence : Nat
  beforeHead : Digest32
  afterSequence : Nat
  afterHead : Digest32
  projectionDigest : Digest32
deriving DecidableEq

structure OutputWire where
  inputDigest : Digest32
  policyDigest : Digest32
  replay : ReplayWire
  projection : ProjectionWire
  view : ViewWire
  event : Option EventWire
  receipt : Option ReceiptWire
deriving DecidableEq

structure BetaHolderSealWire where
  deploymentId : Digest32
  federationId : Digest32
  dailyId : Digest32
  contentEpoch : Nat
  eventId : Digest32
  rulesDigest : Digest32
  signer : Digest32
  player : Digest32
  playerCell : Digest32
  beneficiary : Digest32
  grantNullifier : Digest32
  holdingReceiptId : Digest32
  serverToken : Digest32
  eventSequence : Nat
  expectedPredecessor : Digest32
  expiresAfterSequence : Nat
deriving DecidableEq

/-! ## Canonical encoders -/

def PolicyWire.toJson (policy : PolicyWire) : String :=
  "{\"deployment_id\":" ++ jsonString (Emit.bytes32Hex policy.deploymentId) ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex policy.federationId) ++
    ",\"daily_id\":" ++ jsonString (Emit.bytes32Hex policy.dailyId) ++
    ",\"genesis_head\":" ++ jsonString (Emit.bytes32Hex policy.genesisHead) ++
    ",\"dregg_mint\":" ++ toString policy.dreggMint ++
    ",\"snapshot_slot\":" ++ toString policy.snapshotSlot ++
    ",\"content_epoch\":" ++ toString policy.contentEpoch ++
    ",\"event_id\":" ++ jsonString (Emit.bytes32Hex policy.eventId) ++
    ",\"rules_digest\":" ++ jsonString (Emit.bytes32Hex policy.rulesDigest) ++
    ",\"public_activity_id\":" ++ jsonString (Emit.bytes32Hex policy.publicActivityId) ++
    ",\"scene_content_id\":" ++ jsonString (Emit.bytes32Hex policy.sceneContentId) ++
    ",\"public_action_content_id\":" ++ jsonString (Emit.bytes32Hex policy.publicActionContentId) ++
    ",\"sponsor_action_content_id\":" ++ jsonString (Emit.bytes32Hex policy.sponsorActionContentId) ++
    ",\"complete_content_id\":" ++ jsonString (Emit.bytes32Hex policy.completeContentId) ++
    ",\"public_service\":" ++ toString policy.publicService ++
    ",\"sponsor_service\":" ++ toString policy.sponsorService ++
    ",\"service_target\":" ++ toString policy.serviceTarget ++
    ",\"power_root\":" ++ jsonString (Emit.bytes32Hex policy.powerRoot) ++
    ",\"loot_root\":" ++ jsonString (Emit.bytes32Hex policy.lootRoot) ++
    ",\"canon_root\":" ++ jsonString (Emit.bytes32Hex policy.canonRoot) ++
    ",\"canon_revision\":" ++ toString policy.canonRevision ++ "}"

def ViewerWire.toJson (viewer : ViewerWire) : String :=
  "{\"player\":" ++ jsonString (Emit.bytes32Hex viewer.player) ++
    ",\"player_cell\":" ++ jsonString (Emit.bytes32Hex viewer.playerCell) ++
    ",\"sponsor_beneficiary\":" ++ jsonString (Emit.bytes32Hex viewer.sponsorBeneficiary) ++ "}"

def PayloadWire.toJson (payload : PayloadWire) : String :=
  "{\"kind\":" ++ jsonString payload.kind ++
    ",\"actor\":" ++ jsonString (Emit.bytes32Hex payload.actor) ++
    ",\"beneficiary\":" ++ jsonString (Emit.bytes32Hex payload.beneficiary) ++
    ",\"activity_id\":" ++ jsonString (Emit.bytes32Hex payload.activityId) ++
    ",\"grant_nullifier\":" ++ jsonString (Emit.bytes32Hex payload.grantNullifier) ++
    ",\"authority_commitment\":" ++ jsonString (Emit.bytes32Hex payload.authorityCommitment) ++
    ",\"local_service\":" ++ toString payload.localService ++ "}"

def StatementWire.toJson (statement : StatementWire) : String :=
  "{\"namespace_id\":" ++ jsonString (Emit.bytes32Hex statement.namespaceId) ++
    ",\"kind\":" ++ toString statement.kind ++
    ",\"key\":" ++ jsonString (Emit.bytes32Hex statement.key) ++
    ",\"version\":" ++ toString statement.version ++
    ",\"sequence\":" ++ toString statement.sequence ++
    ",\"predecessor\":" ++ jsonString (Emit.bytes32Hex statement.predecessor) ++
    ",\"payload_digest\":" ++ jsonString (Emit.bytes32Hex statement.payloadDigest) ++ "}"

def EventWire.toJson (event : EventWire) : String :=
  "{\"statement\":" ++ event.statement.toJson ++
    ",\"payload\":" ++ event.payload.toJson ++
    ",\"event_digest\":" ++ jsonString (Emit.bytes32Hex event.eventDigest) ++ "}"

def ProjectionWire.toJson (projection : ProjectionWire) : String :=
  "{\"sequence\":" ++ toString projection.sequence ++
    ",\"public_players\":" ++ jsonArray
      (projection.publicPlayers.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"sponsors\":" ++ jsonArray (projection.sponsors.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"spent_grant_nullifiers\":" ++ jsonArray
      (projection.spentGrantNullifiers.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"public_play_count\":" ++ toString projection.publicPlayCount ++
    ",\"sponsorship_count\":" ++ toString projection.sponsorshipCount ++
    ",\"local_service_total\":" ++ toString projection.localServiceTotal ++
    ",\"power_root\":" ++ jsonString (Emit.bytes32Hex projection.powerRoot) ++
    ",\"loot_root\":" ++ jsonString (Emit.bytes32Hex projection.lootRoot) ++
    ",\"canon_root\":" ++ jsonString (Emit.bytes32Hex projection.canonRoot) ++
    ",\"canon_revision\":" ++ toString projection.canonRevision ++ "}"

def ActionRequestWire.toJson (action : ActionRequestWire) : String :=
  "{\"kind\":" ++ jsonString action.kind ++
    ",\"token\":" ++ jsonString (Emit.bytes32Hex action.token) ++ "}"

def InputWire.toJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"mode\":" ++ jsonString input.mode ++
    ",\"policy\":" ++ input.policy.toJson ++
    ",\"history\":" ++ jsonArray (input.history.map EventWire.toJson) ++
    ",\"claimed_projection\":" ++ input.claimedProjection.toJson ++
    ",\"viewer\":" ++ input.viewer.toJson ++
    ",\"action\":" ++ input.action.toJson ++ "}"

def ActionTokenWire.toJson (action : ActionTokenWire) : String :=
  "{\"kind\":" ++ jsonString action.kind ++
    ",\"token\":" ++ jsonString (Emit.bytes32Hex action.token) ++
    ",\"actor\":" ++ jsonString (Emit.bytes32Hex action.actor) ++
    ",\"beneficiary\":" ++ jsonString (Emit.bytes32Hex action.beneficiary) ++
    ",\"expires_after_sequence\":" ++ toString action.expiresAfterSequence ++ "}"

def ViewWire.toJson (view : ViewWire) : String :=
  "{\"phase\":" ++ jsonString view.phase ++
    ",\"scene_content_id\":" ++ jsonString (Emit.bytes32Hex view.sceneContentId) ++
    ",\"status_content_id\":" ++ jsonString (Emit.bytes32Hex view.statusContentId) ++
    ",\"progress_current\":" ++ toString view.progressCurrent ++
    ",\"progress_target\":" ++ toString view.progressTarget ++
    ",\"public_play_count\":" ++ toString view.publicPlayCount ++
    ",\"sponsorship_count\":" ++ toString view.sponsorshipCount ++
    ",\"available_actions\":" ++ jsonArray (view.availableActions.map ActionTokenWire.toJson) ++ "}"

def ReceiptWire.toJson (receipt : ReceiptWire) : String :=
  "{\"kind\":" ++ jsonString receipt.kind ++
    ",\"actor\":" ++ jsonString (Emit.bytes32Hex receipt.actor) ++
    ",\"beneficiary\":" ++ jsonString (Emit.bytes32Hex receipt.beneficiary) ++
    ",\"sequence\":" ++ toString receipt.sequence ++
    ",\"local_service\":" ++ toString receipt.localService ++
    ",\"consumed_grant_nullifier\":" ++
      jsonString (Emit.bytes32Hex receipt.consumedGrantNullifier) ++
    ",\"authority_commitment\":" ++ jsonString (Emit.bytes32Hex receipt.authorityCommitment) ++
    ",\"power_delta\":" ++ toString receipt.powerDelta ++
    ",\"loot_delta\":" ++ toString receipt.lootDelta ++
    ",\"canon_revision_delta\":" ++ toString receipt.canonRevisionDelta ++ "}"

def ReplayWire.toJson (replay : ReplayWire) : String :=
  "{\"history_length\":" ++ toString replay.historyLength ++
    ",\"before_sequence\":" ++ toString replay.beforeSequence ++
    ",\"before_head\":" ++ jsonString (Emit.bytes32Hex replay.beforeHead) ++
    ",\"after_sequence\":" ++ toString replay.afterSequence ++
    ",\"after_head\":" ++ jsonString (Emit.bytes32Hex replay.afterHead) ++
    ",\"projection_digest\":" ++ jsonString (Emit.bytes32Hex replay.projectionDigest) ++ "}"

def OutputWire.toJson (output : OutputWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"input_digest\":" ++ jsonString (Emit.bytes32Hex output.inputDigest) ++
    ",\"policy_digest\":" ++ jsonString (Emit.bytes32Hex output.policyDigest) ++
    ",\"replay\":" ++ output.replay.toJson ++
    ",\"projection\":" ++ output.projection.toJson ++
    ",\"view\":" ++ output.view.toJson ++
    ",\"event\":" ++ optionJson EventWire.toJson output.event ++
    ",\"receipt\":" ++ optionJson ReceiptWire.toJson output.receipt ++ "}"

def BetaHolderSealWire.toJson (carrier : BetaHolderSealWire) : String :=
  "{\"format\":" ++ jsonString BETA_HOLDER_FORMAT ++
    ",\"deployment_id\":" ++ jsonString (Emit.bytes32Hex carrier.deploymentId) ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex carrier.federationId) ++
    ",\"daily_id\":" ++ jsonString (Emit.bytes32Hex carrier.dailyId) ++
    ",\"content_epoch\":" ++ toString carrier.contentEpoch ++
    ",\"event_id\":" ++ jsonString (Emit.bytes32Hex carrier.eventId) ++
    ",\"rules_digest\":" ++ jsonString (Emit.bytes32Hex carrier.rulesDigest) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex carrier.signer) ++
    ",\"player\":" ++ jsonString (Emit.bytes32Hex carrier.player) ++
    ",\"player_cell\":" ++ jsonString (Emit.bytes32Hex carrier.playerCell) ++
    ",\"beneficiary\":" ++ jsonString (Emit.bytes32Hex carrier.beneficiary) ++
    ",\"grant_nullifier\":" ++ jsonString (Emit.bytes32Hex carrier.grantNullifier) ++
    ",\"holding_receipt_id\":" ++ jsonString (Emit.bytes32Hex carrier.holdingReceiptId) ++
    ",\"server_token\":" ++ jsonString (Emit.bytes32Hex carrier.serverToken) ++
    ",\"event_sequence\":" ++ toString carrier.eventSequence ++
    ",\"expected_predecessor\":" ++ jsonString (Emit.bytes32Hex carrier.expectedPredecessor) ++
    ",\"expires_after_sequence\":" ++ toString carrier.expiresAfterSequence ++ "}"

/-! ## Strict, bounded, canonical decoders -/

private def parseDigest (j : Json) : Except String Digest32 := do
  let spelling ← j.getStr?
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def parseDigestList (j : Json) : Except String (List Digest32) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_EVENTS then throw "digest list exceeds bound"
  let parsed ← values.mapM parseDigest
  if canonicalDigestListB parsed then pure parsed else throw "digest list is not canonical"

private def parsePolicy (j : Json) : Except String PolicyWire := do
  exactKeys j ["deployment_id", "federation_id", "daily_id", "genesis_head", "dregg_mint",
    "snapshot_slot", "content_epoch", "event_id", "rules_digest", "public_activity_id",
    "scene_content_id", "public_action_content_id", "sponsor_action_content_id",
    "complete_content_id", "public_service", "sponsor_service", "service_target",
    "power_root", "loot_root", "canon_root", "canon_revision"]
  let policy : PolicyWire := {
    deploymentId := ← objectDigest j "deployment_id"
    federationId := ← objectDigest j "federation_id"
    dailyId := ← objectDigest j "daily_id"
    genesisHead := ← objectDigest j "genesis_head"
    dreggMint := ← objectNat j "dregg_mint"
    snapshotSlot := ← objectNat j "snapshot_slot"
    contentEpoch := ← objectNat j "content_epoch"
    eventId := ← objectDigest j "event_id"
    rulesDigest := ← objectDigest j "rules_digest"
    publicActivityId := ← objectDigest j "public_activity_id"
    sceneContentId := ← objectDigest j "scene_content_id"
    publicActionContentId := ← objectDigest j "public_action_content_id"
    sponsorActionContentId := ← objectDigest j "sponsor_action_content_id"
    completeContentId := ← objectDigest j "complete_content_id"
    publicService := ← objectNat j "public_service" MAX_LOCAL_SERVICE
    sponsorService := ← objectNat j "sponsor_service" MAX_LOCAL_SERVICE
    serviceTarget := ← objectNat j "service_target" (MAX_EVENTS * MAX_LOCAL_SERVICE)
    powerRoot := ← objectDigest j "power_root"
    lootRoot := ← objectDigest j "loot_root"
    canonRoot := ← objectDigest j "canon_root"
    canonRevision := ← objectNat j "canon_revision"
  }
  if policy.validB then pure policy else throw "invalid galley policy"

private def parseViewer (j : Json) : Except String ViewerWire := do
  exactKeys j ["player", "player_cell", "sponsor_beneficiary"]
  pure {
    player := ← objectDigest j "player"
    playerCell := ← objectDigest j "player_cell"
    sponsorBeneficiary := ← objectDigest j "sponsor_beneficiary"
  }

private def parsePayload (j : Json) : Except String PayloadWire := do
  exactKeys j ["kind", "actor", "beneficiary", "activity_id", "grant_nullifier",
    "authority_commitment", "local_service"]
  let kind ← j.getObjValAs? String "kind"
  if kind != "public-play" && kind != "holder-sponsor" then throw "unknown event kind"
  pure {
    kind
    actor := ← objectDigest j "actor"
    beneficiary := ← objectDigest j "beneficiary"
    activityId := ← objectDigest j "activity_id"
    grantNullifier := ← objectDigest j "grant_nullifier"
    authorityCommitment := ← objectDigest j "authority_commitment"
    localService := ← objectNat j "local_service" MAX_LOCAL_SERVICE
  }

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

private def parseEvent (j : Json) : Except String EventWire := do
  exactKeys j ["statement", "payload", "event_digest"]
  pure {
    statement := ← parseStatement (← j.getObjVal? "statement")
    payload := ← parsePayload (← j.getObjVal? "payload")
    eventDigest := ← objectDigest j "event_digest"
  }

private def parseEvents (j : Json) : Except String (List EventWire) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_EVENTS then throw "event history exceeds bound"
  values.mapM parseEvent

private def parseProjection (j : Json) : Except String ProjectionWire := do
  exactKeys j ["sequence", "public_players", "sponsors", "spent_grant_nullifiers",
    "public_play_count", "sponsorship_count", "local_service_total", "power_root",
    "loot_root", "canon_root", "canon_revision"]
  pure {
    sequence := ← objectNat j "sequence" MAX_EVENTS
    publicPlayers := ← parseDigestList (← j.getObjVal? "public_players")
    sponsors := ← parseDigestList (← j.getObjVal? "sponsors")
    spentGrantNullifiers := ← parseDigestList (← j.getObjVal? "spent_grant_nullifiers")
    publicPlayCount := ← objectNat j "public_play_count" MAX_EVENTS
    sponsorshipCount := ← objectNat j "sponsorship_count" MAX_EVENTS
    localServiceTotal := ← objectNat j "local_service_total" (MAX_EVENTS * MAX_LOCAL_SERVICE)
    powerRoot := ← objectDigest j "power_root"
    lootRoot := ← objectDigest j "loot_root"
    canonRoot := ← objectDigest j "canon_root"
    canonRevision := ← objectNat j "canon_revision"
  }

private def parseActionRequest (j : Json) : Except String ActionRequestWire := do
  exactKeys j ["kind", "token"]
  let kind ← j.getObjValAs? String "kind"
  if kind != "none" && kind != "public-play" && kind != "holder-sponsor" then
    throw "unknown action kind"
  pure { kind, token := ← objectDigest j "token" }

private def parseInputJson (j : Json) : Except String InputWire := do
  exactKeys j ["format", "mode", "policy", "history", "claimed_projection", "viewer", "action"]
  if (← j.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  let mode ← j.getObjValAs? String "mode"
  if mode != "view" && mode != "command" then throw "unknown input mode"
  let action ← parseActionRequest (← j.getObjVal? "action")
  if (mode = "view") != (action.kind = "none") then throw "mode/action mismatch"
  pure {
    mode
    policy := ← parsePolicy (← j.getObjVal? "policy")
    history := ← parseEvents (← j.getObjVal? "history")
    claimedProjection := ← parseProjection (← j.getObjVal? "claimed_projection")
    viewer := ← parseViewer (← j.getObjVal? "viewer")
    action
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

/-- Strict policy-only decoder for the activated-content boundary.  This is
the same parser and canonical encoder used by the game input decoder; the
content installer therefore does not need a Rust policy parser or a second
Lean policy grammar. -/
def decodePolicyWithLimit (byteLimit : Nat) (bytes : String) : Option PolicyWire :=
  if bytes.utf8ByteSize ≤ byteLimit then canonicalDecode parsePolicy PolicyWire.toJson bytes
  else none

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

def decodePolicy (bytes : String) : Option PolicyWire :=
  decodePolicyWithLimit WIRE_BYTE_LIMIT bytes

theorem decodePolicy_reencodes {bytes : String} {policy : PolicyWire}
    (accepted : decodePolicy bytes = some policy) : policy.toJson = bytes := by
  simp only [decodePolicy, decodePolicyWithLimit] at accepted
  split at accepted <;> try contradiction
  exact canonicalDecode_reencodes parsePolicy PolicyWire.toJson accepted

theorem decodeInput_reencodes {bytes : String} {input : InputWire}
    (accepted : decodeInput bytes = some input) : input.toJson = bytes := by
  simp only [decodeInput, decodeInputWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseInputJson InputWire.toJson accepted
  · contradiction

theorem decodeInput_refuses_oversized (bytes : String)
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeInput bytes = none := by
  simp [decodeInput, decodeInputWithLimit, Nat.not_le.mpr oversized]

/-! ## Faithful wide digests and replay semantics -/

private def byte (n : Nat) : Fin 256 :=
  ⟨n % 256, Nat.mod_lt _ (by decide)⟩

private def u32le (n : Nat) : List (Fin 256) :=
  [byte n, byte (n / 256), byte (n / 65536), byte (n / 16777216)]

private def stringBytes (value : String) : List Nat :=
  value.toUTF8.toList.map UInt8.toNat

/-- All eight BabyBear sponge lanes are retained as eight little-endian u32s. -/
def digestString (domain : Nat) (value : String) : Digest32 :=
  let lanes := Dregg2.Circuit.CommitmentTreeWide.hashTo8 domain (stringBytes value)
  { bytes := (List.ofFn (fun lane : Fin 8 => u32le (lanes.getD lane.val 0))).flatten
    length_eq := by simp [u32le] }

abbrev PAYLOAD_DIGEST_DOMAIN : Nat := 0x50474150
abbrev EVENT_DIGEST_DOMAIN : Nat := 0x50474145
abbrev INPUT_DIGEST_DOMAIN : Nat := 0x50474149
abbrev POLICY_DIGEST_DOMAIN : Nat := 0x5047414c
abbrev PROJECTION_DIGEST_DOMAIN : Nat := 0x50474152
abbrev ACTION_TOKEN_DOMAIN : Nat := 0x50474154
abbrev AUTHORITY_DIGEST_DOMAIN : Nat := 0x50474141

def streamSpec (policy : PolicyWire) : EventSourcing.StreamSpec := {
  aggregate := { namespaceId := policy.federationId, kind := STREAM_KIND, key := policy.dailyId }
  version := ⟨STREAM_VERSION⟩
  genesisHead := policy.genesisHead
}

def StatementWire.toSemantic (statement : StatementWire) : EventSourcing.EventStatement := {
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

def StatementWire.ofSemantic (statement : EventSourcing.EventStatement) : StatementWire := {
  namespaceId := statement.aggregate.namespaceId
  kind := statement.aggregate.kind
  key := statement.aggregate.key
  version := statement.version.value
  sequence := statement.sequence
  predecessor := statement.predecessor
  payloadDigest := statement.payloadDigest
}

def EventWire.toSemantic (event : EventWire) : EventSourcing.EventEnvelope PayloadWire := {
  statement := event.statement.toSemantic
  payload := event.payload
  eventDigest := event.eventDigest
}

def EventWire.ofSemantic (event : EventSourcing.EventEnvelope PayloadWire) : EventWire := {
  statement := .ofSemantic event.statement
  payload := event.payload
  eventDigest := event.eventDigest
}

def digestBoundary : EventSourcing.DigestBoundary PayloadWire where
  payloadDigest payload := digestString PAYLOAD_DIGEST_DOMAIN payload.toJson
  eventDigest statement := digestString EVENT_DIGEST_DOMAIN (StatementWire.ofSemantic statement).toJson

def initialProjection (policy : PolicyWire) : ProjectionWire := {
  sequence := 0
  publicPlayers := []
  sponsors := []
  spentGrantNullifiers := []
  publicPlayCount := 0
  sponsorshipCount := 0
  localServiceTotal := 0
  powerRoot := policy.powerRoot
  lootRoot := policy.lootRoot
  canonRoot := policy.canonRoot
  canonRevision := policy.canonRevision
}

private def anchorsExactB (policy : PolicyWire) (state : ProjectionWire) : Bool :=
  state.powerRoot = policy.powerRoot && state.lootRoot = policy.lootRoot &&
    state.canonRoot = policy.canonRoot && state.canonRevision = policy.canonRevision

/-- The entire gameplay reducer. Holder sponsorship is a local-service acknowledgement
only: the advantage/canon fields appear solely in the unchanged record update. -/
def reduce (policy : PolicyWire) : EventSourcing.Reducer ProjectionWire PayloadWire :=
  fun state payload =>
    if !anchorsExactB policy state then none
    else if state.sequence ≥ MAX_EVENTS then none
    else if payload.kind = "public-play" then
      if payload.activityId != policy.publicActivityId ||
          payload.beneficiary != payload.actor || payload.grantNullifier != zeroDigest ||
          payload.authorityCommitment != zeroDigest || payload.localService != policy.publicService ||
          decide (payload.actor ∈ state.publicPlayers) then none
      else some { state with
        sequence := state.sequence + 1
        publicPlayers := insertDigest payload.actor state.publicPlayers
        publicPlayCount := state.publicPlayCount + 1
        localServiceTotal := state.localServiceTotal + payload.localService }
    else if payload.kind = "holder-sponsor" then
      if payload.activityId != zeroDigest || payload.grantNullifier = zeroDigest ||
          payload.authorityCommitment = zeroDigest || payload.localService != policy.sponsorService ||
          decide (payload.actor ∈ state.sponsors) ||
          decide (payload.grantNullifier ∈ state.spentGrantNullifiers) then none
      else some { state with
        sequence := state.sequence + 1
        sponsors := insertDigest payload.actor state.sponsors
        spentGrantNullifiers := insertDigest payload.grantNullifier state.spentGrantNullifiers
        sponsorshipCount := state.sponsorshipCount + 1
        localServiceTotal := state.localServiceTotal + payload.localService }
    else none

def rebuild (policy : PolicyWire) (history : List EventWire) :
    Except EventSourcing.Error (EventSourcing.ReplayState ProjectionWire) :=
  EventSourcing.rebuild (streamSpec policy) digestBoundary (reduce policy)
    (initialProjection policy) (history.map EventWire.toSemantic)

theorem reduce_preserves_advantage_anchors (policy : PolicyWire) (before after : ProjectionWire)
    (payload : PayloadWire) (accepted : reduce policy before payload = some after) :
    after.powerRoot = before.powerRoot ∧ after.lootRoot = before.lootRoot ∧
      after.canonRoot = before.canonRoot ∧ after.canonRevision = before.canonRevision := by
  unfold reduce at accepted
  repeat' split at accepted
  all_goals try contradiction
  all_goals (cases accepted; simp)

theorem reduce_holder_sponsor_bounded (policy : PolicyWire) (before after : ProjectionWire)
    (payload : PayloadWire) (accepted : reduce policy before payload = some after)
    (holder : payload.kind = "holder-sponsor") (valid : policy.validB = true) :
    payload.localService ≤ MAX_LOCAL_SERVICE ∧
      after.powerRoot = before.powerRoot ∧ after.lootRoot = before.lootRoot ∧
      after.canonRoot = before.canonRoot ∧ after.canonRevision = before.canonRevision := by
  have anchors := reduce_preserves_advantage_anchors policy before after payload accepted
  have serviceBound : policy.sponsorService ≤ MAX_LOCAL_SERVICE := by
    simp only [PolicyWire.validB, Bool.and_eq_true, decide_eq_true_eq] at valid
    omega
  have serviceExact : payload.localService = policy.sponsorService := by
    unfold reduce at accepted
    simp only [holder, if_true] at accepted
    repeat' split at accepted
    all_goals try contradiction
    all_goals simp_all
  exact ⟨serviceExact.trans_le serviceBound, anchors⟩

/-! ## Opaque future holder authority -/

inductive EligibilityClass where
  | holder
deriving DecidableEq

/-- Reserved for a future authority bridge backed by an atomically consumable
wallet capability.  The constructor is private and the old caller-JSON admission
and native sponsor export are deliberately absent. -/
structure AdmittedBetaSponsor where
  private mk ::
  carrier : BetaHolderSealWire
  playerCell : Digest32
  eligibilityClass : EligibilityClass
  chamberPower : Nat
  chamber_power_zero : chamberPower = 0

def AdmittedBetaSponsor.authorityCommitment (authority : AdmittedBetaSponsor) : Digest32 :=
  digestString AUTHORITY_DIGEST_DOMAIN authority.carrier.toJson

theorem AdmittedBetaSponsor.no_chamber_power (authority : AdmittedBetaSponsor) :
    authority.chamberPower = 0 := authority.chamber_power_zero

private def authorityMatchesB (policy : PolicyWire) (viewer : ViewerWire)
    (cursor : EventSourcing.Cursor) (_now : Nat) (authority : AdmittedBetaSponsor) : Bool :=
  let carrier := authority.carrier
  carrier.deploymentId = policy.deploymentId && carrier.federationId = policy.federationId &&
    carrier.dailyId = policy.dailyId && carrier.contentEpoch = policy.contentEpoch &&
    carrier.eventId = policy.eventId && carrier.rulesDigest = policy.rulesDigest &&
    carrier.signer = viewer.player && carrier.player = viewer.player &&
    carrier.playerCell = viewer.playerCell && authority.playerCell = viewer.playerCell &&
    carrier.beneficiary = viewer.sponsorBeneficiary &&
    carrier.grantNullifier != zeroDigest && carrier.holdingReceiptId != zeroDigest &&
    carrier.serverToken != zeroDigest &&
    carrier.eventSequence = cursor.sequence + 1 && carrier.expectedPredecessor = cursor.head &&
    carrier.eventSequence ≤ carrier.expiresAfterSequence &&
    carrier.expiresAfterSequence ≤ carrier.eventSequence + MAX_SPONSOR_SEQUENCE_TTL &&
    authority.eligibilityClass = .holder &&
    authority.chamberPower = 0

/-! ## Lean-authored action discovery and commands -/

private def tokenPreimage (policy : PolicyWire) (cursor : EventSourcing.Cursor)
    (viewer : ViewerWire) (kind : String) (beneficiary authorityCommitment : Digest32)
    (nonce : Digest32) (expiresAfterSequence : Nat) : String :=
  "{\"format\":\"POA-GALLEY-ACTION-TOKEN-1\"" ++
    ",\"deployment_id\":" ++ jsonString (Emit.bytes32Hex policy.deploymentId) ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex policy.federationId) ++
    ",\"daily_id\":" ++ jsonString (Emit.bytes32Hex policy.dailyId) ++
    ",\"content_epoch\":" ++ toString policy.contentEpoch ++
    ",\"rules_digest\":" ++ jsonString (Emit.bytes32Hex policy.rulesDigest) ++
    ",\"expected_predecessor\":" ++ jsonString (Emit.bytes32Hex cursor.head) ++
    ",\"event_sequence\":" ++ toString (cursor.sequence + 1) ++
    ",\"action_kind\":" ++ jsonString kind ++
    ",\"player\":" ++ jsonString (Emit.bytes32Hex viewer.player) ++
    ",\"player_cell\":" ++ jsonString (Emit.bytes32Hex viewer.playerCell) ++
    ",\"beneficiary\":" ++ jsonString (Emit.bytes32Hex beneficiary) ++
    ",\"authority_commitment\":" ++ jsonString (Emit.bytes32Hex authorityCommitment) ++
    ",\"nonce\":" ++ jsonString (Emit.bytes32Hex nonce) ++
    ",\"expires_after_sequence\":" ++ toString expiresAfterSequence ++ "}"

private def publicAction (policy : PolicyWire) (state : EventSourcing.ReplayState ProjectionWire)
    (viewer : ViewerWire) : ActionTokenWire := {
  kind := "public-play"
  token := digestString ACTION_TOKEN_DOMAIN
    (tokenPreimage policy state.cursor viewer "public-play" viewer.player zeroDigest
      zeroDigest (state.cursor.sequence + 1))
  actor := viewer.player
  beneficiary := viewer.player
  expiresAfterSequence := state.cursor.sequence
}

private def sponsorAction (policy : PolicyWire) (state : EventSourcing.ReplayState ProjectionWire)
    (viewer : ViewerWire) (authority : AdmittedBetaSponsor) : ActionTokenWire := {
  kind := "holder-sponsor"
  token := digestString ACTION_TOKEN_DOMAIN
    (tokenPreimage policy state.cursor viewer "holder-sponsor" viewer.sponsorBeneficiary
      authority.authorityCommitment authority.carrier.serverToken
      authority.carrier.expiresAfterSequence)
  actor := viewer.player
  beneficiary := viewer.sponsorBeneficiary
  expiresAfterSequence := authority.carrier.expiresAfterSequence
}

def availableActions (policy : PolicyWire) (state : EventSourcing.ReplayState ProjectionWire)
    (viewer : ViewerWire) (now : Nat) (authority : Option AdmittedBetaSponsor) :
    List ActionTokenWire :=
  if state.projection.localServiceTotal ≥ policy.serviceTarget || state.cursor.sequence ≥ MAX_EVENTS then []
  else
    let publicActions := if decide (viewer.player ∈ state.projection.publicPlayers) then []
      else [publicAction policy state viewer]
    let sponsor := match authority with
      | none => []
      | some admitted =>
          if authorityMatchesB policy viewer state.cursor now admitted &&
              !decide (viewer.player ∈ state.projection.sponsors) &&
              !decide (admitted.carrier.grantNullifier ∈ state.projection.spentGrantNullifiers)
          then [sponsorAction policy state viewer admitted] else []
    publicActions ++ sponsor

def viewOf (policy : PolicyWire) (state : EventSourcing.ReplayState ProjectionWire)
    (viewer : ViewerWire) (now : Nat) (authority : Option AdmittedBetaSponsor) : ViewWire :=
  let complete := state.projection.localServiceTotal ≥ policy.serviceTarget
  let actions := if complete then [] else availableActions policy state viewer now authority
  {
    phase := if complete then "complete" else "service"
    sceneContentId := policy.sceneContentId
    statusContentId := if complete then policy.completeContentId else policy.publicActionContentId
    progressCurrent := min state.projection.localServiceTotal policy.serviceTarget
    progressTarget := policy.serviceTarget
    publicPlayCount := state.projection.publicPlayCount
    sponsorshipCount := state.projection.sponsorshipCount
    availableActions := actions
  }

private def validatedPrefix? (input : InputWire) :
    Option (EventSourcing.ReplayState ProjectionWire) := do
  if !input.policy.validB then none else
  if input.history.length > MAX_EVENTS then none else
  let state ← (rebuild input.policy input.history).toOption
  if state.projection != input.claimedProjection then none else
  if state.cursor.sequence != input.claimedProjection.sequence then none else
  if state.cursor.sequence != input.history.length then none else
  some state

private def nextEvent (policy : PolicyWire) (state : EventSourcing.ReplayState ProjectionWire)
    (payload : PayloadWire) : EventWire :=
  let statement : EventSourcing.EventStatement := {
    aggregate := (streamSpec policy).aggregate
    version := (streamSpec policy).version
    sequence := state.cursor.sequence + 1
    predecessor := state.cursor.head
    payloadDigest := digestBoundary.payloadDigest payload
  }
  { statement := .ofSemantic statement
    payload
    eventDigest := digestBoundary.eventDigest statement }

private def receiptOf (event : EventWire) : ReceiptWire := {
  kind := event.payload.kind
  actor := event.payload.actor
  beneficiary := event.payload.beneficiary
  sequence := event.statement.sequence
  localService := event.payload.localService
  consumedGrantNullifier := event.payload.grantNullifier
  authorityCommitment := event.payload.authorityCommitment
  powerDelta := 0
  lootDelta := 0
  canonRevisionDelta := 0
}

private def outputOf (inputBytes : String) (input : InputWire)
    (before after : EventSourcing.ReplayState ProjectionWire) (now : Nat)
    (authority : Option AdmittedBetaSponsor) (event : Option EventWire)
    (receipt : Option ReceiptWire) : OutputWire := {
  inputDigest := digestString INPUT_DIGEST_DOMAIN inputBytes
  policyDigest := digestString POLICY_DIGEST_DOMAIN input.policy.toJson
  replay := {
    historyLength := input.history.length
    beforeSequence := before.cursor.sequence
    beforeHead := before.cursor.head
    afterSequence := after.cursor.sequence
    afterHead := after.cursor.head
    projectionDigest := digestString PROJECTION_DIGEST_DOMAIN after.projection.toJson
  }
  projection := after.projection
  view := viewOf input.policy after input.viewer now authority
  event
  receipt
}

private def requestedAction? (input : InputWire)
    (state : EventSourcing.ReplayState ProjectionWire) (now : Nat)
    (authority : Option AdmittedBetaSponsor) : Option ActionTokenWire :=
  (availableActions input.policy state input.viewer now authority).find?
    (fun offered => offered.kind = input.action.kind && offered.token = input.action.token)

private def commandPayload? (input : InputWire)
    (state : EventSourcing.ReplayState ProjectionWire) (now : Nat)
    (authority : Option AdmittedBetaSponsor) : Option PayloadWire := do
  if input.action.kind = "public-play" then
    let offered ← requestedAction? input state now authority
    if offered.kind != "public-play" then none else
    some {
      kind := "public-play"
      actor := input.viewer.player
      beneficiary := input.viewer.player
      activityId := input.policy.publicActivityId
      grantNullifier := zeroDigest
      authorityCommitment := zeroDigest
      localService := input.policy.publicService
    }
  else if input.action.kind = "holder-sponsor" then
    let admitted ← authority
    let offered ← requestedAction? input state now authority
    if offered.kind != "holder-sponsor" then none else
    if !authorityMatchesB input.policy input.viewer state.cursor now admitted then none else
    some {
      kind := "holder-sponsor"
      actor := input.viewer.player
      beneficiary := input.viewer.sponsorBeneficiary
      activityId := zeroDigest
      grantNullifier := admitted.carrier.grantNullifier
      authorityCommitment := admitted.authorityCommitment
      localService := input.policy.sponsorService
    }
  else none

def judgeInput? (inputBytes : String) (input : InputWire) (now : Nat)
    (authority : Option AdmittedBetaSponsor) : Option OutputWire := do
  let before ← validatedPrefix? input
  if input.mode = "view" then
    if input.action.kind != "none" || input.action.token != zeroDigest then none else
    some (outputOf inputBytes input before before now authority none none)
  else if input.mode = "command" then
    let payload ← commandPayload? input before now authority
    let event := nextEvent input.policy before payload
    let applied ← (EventSourcing.applyEvent (streamSpec input.policy) digestBoundary
      (reduce input.policy) before event.toSemantic).toOption
    let after := applied.state
    some (outputOf inputBytes input before after now authority (some event)
      (some (receiptOf event)))
  else none

def judgeBytesWithAuthority? (bytes : String) (now : Nat)
    (authority : Option AdmittedBetaSponsor) : Option String := do
  let input ← decodeInput bytes
  let output ← judgeInput? bytes input now authority
  some output.toJson

/-- Public play and view export. It has no authority argument, so holder sponsorship
is structurally unavailable rather than represented by a caller-provided Boolean. -/
@[export dregg_poa_galley_daily_judge]
def judgeFFI (bytes : String) : String :=
  (judgeBytesWithAuthority? bytes 0 none).getD ""

/-! ## ⚑ The weld: the judge publishes the reducer's answer, not its own

`reduce_preserves_advantage_anchors` and `reduce_holder_sponsor_bounded` are
facts about `reduce`.  Nothing used to connect `reduce` to the bytes
`judgeFFI` returns: the judge obtains its successor through
`EventSourcing.applyEvent` and could have published any projection at all with
every reducer-level theorem still green.  These three theorems close that, over
the ACTUAL exported objects (`judgeInput?`, `InputWire`, `OutputWire`, `reduce`)
and with no hypothesis beyond "the judge accepted", which every `/status` poll
and every command satisfies.

⚑ REFUTATION.  Replace `let after := applied.state` in the command branch with
anything that is not the reducer's successor — e.g.
`{ applied.state with projection := { applied.state.projection with
localServiceTotal := applied.state.projection.localServiceTotal + 1 } }`, a
service bonus the reducer never granted — and `judge_command_projection_is_reduce`
goes red.  Measured against HEAD before this commit, that mutation passed every
other check in this file: `fixture_public_command_accepted` only tests `.isSome`,
`fixture_public_output_redecodes` re-decodes the tampered projection happily, and
`fixture_beta_sponsor_accepted_without_advantage` inspects only the four anchors.
-/

private theorem validatedPrefix?_claimed {input : InputWire}
    {state : EventSourcing.ReplayState ProjectionWire}
    (accepted : validatedPrefix? input = some state) :
    state.projection = input.claimedProjection := by
  simp only [validatedPrefix?, bind, Option.bind] at accepted
  repeat' (first | split at accepted | simp only [] at accepted)
  all_goals first
    | (simp at accepted
       done)
    | (simp_all
       done)

/-- The projection the judge publishes for an accepted command is EXACTLY
`reduce`'s successor of the claimed projection the caller supplied. -/
theorem judge_command_projection_is_reduce {inputBytes : String} {input : InputWire}
    {now : Nat} {authority : Option AdmittedBetaSponsor} {output : OutputWire}
    {event : EventWire}
    (accepted : judgeInput? inputBytes input now authority = some output)
    (emitted : output.event = some event) :
    reduce input.policy input.claimedProjection event.payload = some output.projection := by
  unfold judgeInput? at accepted
  cases hbefore : validatedPrefix? input with
  | none =>
      simp only [hbefore, bind, Option.bind] at accepted
      simp at accepted
  | some before =>
      simp only [hbefore, bind, Option.bind] at accepted
      by_cases hview : input.mode = "view"
      · rw [if_pos hview] at accepted
        split at accepted
        · simp at accepted
        · simp only [Option.some.injEq] at accepted
          subst accepted
          simp only [outputOf] at emitted
          simp at emitted
      · rw [if_neg hview] at accepted
        by_cases hcmd : input.mode = "command"
        · rw [if_pos hcmd] at accepted
          cases hpayload : commandPayload? input before now authority with
          | none =>
              simp only [hpayload] at accepted
              simp at accepted
          | some payload =>
              simp only [hpayload] at accepted
              cases happly : EventSourcing.applyEvent (streamSpec input.policy) digestBoundary
                  (reduce input.policy) before
                  (nextEvent input.policy before payload).toSemantic with
              | error e =>
                  simp only [happly, Except.toOption] at accepted
                  simp at accepted
              | ok applied =>
                  simp only [happly, Except.toOption, Option.some.injEq] at accepted
                  subst accepted
                  simp only [outputOf, Option.some.injEq] at emitted
                  subst emitted
                  rw [← validatedPrefix?_claimed hbefore]
                  exact EventSourcing.applyEvent_projection_is_reduce (streamSpec input.policy)
                    digestBoundary (reduce input.policy) before
                    (nextEvent input.policy before payload).toSemantic applied happly
        · rw [if_neg hcmd] at accepted
          simp at accepted

/-- A view answer moves nothing: with no emitted event the published projection
is byte-identically the caller's claimed projection. -/
theorem judge_view_projection_is_claimed {inputBytes : String} {input : InputWire}
    {now : Nat} {authority : Option AdmittedBetaSponsor} {output : OutputWire}
    (accepted : judgeInput? inputBytes input now authority = some output)
    (noEvent : output.event = none) :
    output.projection = input.claimedProjection := by
  unfold judgeInput? at accepted
  cases hbefore : validatedPrefix? input with
  | none =>
      simp only [hbefore, bind, Option.bind] at accepted
      simp at accepted
  | some before =>
      simp only [hbefore, bind, Option.bind] at accepted
      by_cases hview : input.mode = "view"
      · rw [if_pos hview] at accepted
        split at accepted
        · simp at accepted
        · simp only [Option.some.injEq] at accepted
          subst accepted
          simp only [outputOf]
          exact validatedPrefix?_claimed hbefore
      · rw [if_neg hview] at accepted
        by_cases hcmd : input.mode = "command"
        · rw [if_pos hcmd] at accepted
          cases hpayload : commandPayload? input before now authority with
          | none =>
              simp only [hpayload] at accepted
              simp at accepted
          | some payload =>
              simp only [hpayload] at accepted
              cases happly : EventSourcing.applyEvent (streamSpec input.policy) digestBoundary
                  (reduce input.policy) before
                  (nextEvent input.policy before payload).toSemantic with
              | error e =>
                  simp only [happly, Except.toOption] at accepted
                  simp at accepted
              | ok applied =>
                  simp only [happly, Except.toOption, Option.some.injEq] at accepted
                  subst accepted
                  simp only [outputOf] at noEvent
                  simp at noEvent
        · rw [if_neg hcmd] at accepted
          simp at accepted

/-- ⚑ The consumer-facing form.  `docs/poa/GALLEY-LAYER-CONTRACT.md` §2.6 tells a
consumer it may rely on the four advantage anchors being carried unchanged across
an accepted transition.  Until this theorem that was a claim about `reduce`, which
no consumer can see; this states it about the emitted `OutputWire` against the
caller's own `claimed_projection`, for BOTH modes. -/
theorem judge_output_preserves_advantage_anchors {inputBytes : String} {input : InputWire}
    {now : Nat} {authority : Option AdmittedBetaSponsor} {output : OutputWire}
    (accepted : judgeInput? inputBytes input now authority = some output) :
    output.projection.powerRoot = input.claimedProjection.powerRoot ∧
      output.projection.lootRoot = input.claimedProjection.lootRoot ∧
      output.projection.canonRoot = input.claimedProjection.canonRoot ∧
      output.projection.canonRevision = input.claimedProjection.canonRevision := by
  cases hevent : output.event with
  | none =>
      rw [judge_view_projection_is_claimed accepted hevent]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | some event =>
      exact reduce_preserves_advantage_anchors input.policy input.claimedProjection
        output.projection event.payload (judge_command_projection_is_reduce accepted hevent)

theorem receiptOf_has_no_advantage_delta (event : EventWire) :
    (receiptOf event).powerDelta = 0 ∧ (receiptOf event).lootDelta = 0 ∧
      (receiptOf event).canonRevisionDelta = 0 := by
  simp [receiptOf]

theorem no_authority_cannot_form_holder_payload (input : InputWire)
    (state : EventSourcing.ReplayState ProjectionWire) (now : Nat)
    (holder : input.action.kind = "holder-sponsor") :
    commandPayload? input state now none = none := by
  simp [commandPayload?, holder]

/-! ## Trusted-host beta sponsor ingress

The richer wallet/RPC certificate stays in the native admission bridge. This
narrow seal is intentionally a trusted-host input rather than a public gameplay
request. It is canonical, short-lived in stream-sequence space, replay-bound, and
contains neither balance nor weight. The separate public judge never parses it.
-/

private def parseBetaHolderSealJson (j : Json) : Except String BetaHolderSealWire := do
  exactKeys j ["format", "deployment_id", "federation_id", "daily_id", "content_epoch",
    "event_id", "rules_digest", "signer", "player", "player_cell", "beneficiary",
    "grant_nullifier", "holding_receipt_id", "server_token", "event_sequence",
    "expected_predecessor", "expires_after_sequence"]
  if (← j.getObjValAs? String "format") != BETA_HOLDER_FORMAT then
    throw "wrong beta holder seal format"
  pure {
    deploymentId := ← objectDigest j "deployment_id"
    federationId := ← objectDigest j "federation_id"
    dailyId := ← objectDigest j "daily_id"
    contentEpoch := ← objectNat j "content_epoch"
    eventId := ← objectDigest j "event_id"
    rulesDigest := ← objectDigest j "rules_digest"
    signer := ← objectDigest j "signer"
    player := ← objectDigest j "player"
    playerCell := ← objectDigest j "player_cell"
    beneficiary := ← objectDigest j "beneficiary"
    grantNullifier := ← objectDigest j "grant_nullifier"
    holdingReceiptId := ← objectDigest j "holding_receipt_id"
    serverToken := ← objectDigest j "server_token"
    eventSequence := ← objectNat j "event_sequence" MAX_EVENTS
    expectedPredecessor := ← objectDigest j "expected_predecessor"
    expiresAfterSequence := ← objectNat j "expires_after_sequence" (MAX_EVENTS + MAX_SPONSOR_SEQUENCE_TTL)
  }

def decodeBetaHolderSealWithLimit (byteLimit : Nat) (bytes : String) : Option BetaHolderSealWire :=
  if bytes.length ≤ byteLimit then
    canonicalDecode parseBetaHolderSealJson BetaHolderSealWire.toJson bytes
  else none

def decodeBetaHolderSeal (bytes : String) : Option BetaHolderSealWire :=
  decodeBetaHolderSealWithLimit 16384 bytes

theorem decodeBetaHolderSeal_reencodes {bytes : String} {carrier : BetaHolderSealWire}
    (accepted : decodeBetaHolderSeal bytes = some carrier) : carrier.toJson = bytes := by
  simp only [decodeBetaHolderSeal, decodeBetaHolderSealWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseBetaHolderSealJson BetaHolderSealWire.toJson accepted
  · contradiction

/-- Compatibility-shaped refusal surface for code which has not yet removed the
old sponsor call.  Caller JSON is never decoded and can never mint
`AdmittedBetaSponsor`; there is intentionally no native export for this function. -/
def runAdmittedBetaSponsorWire (_inputJson _sealJson : String) : String := ""

theorem sponsor_wire_is_unconditionally_disabled (inputJson sealJson : String) :
    runAdmittedBetaSponsorWire inputJson sealJson = "" := rfl

/-! ## Strict response decoder (clients can verify the same canonical bytes) -/

private def parseActionToken (j : Json) : Except String ActionTokenWire := do
  exactKeys j ["kind", "token", "actor", "beneficiary", "expires_after_sequence"]
  let kind ← j.getObjValAs? String "kind"
  if kind != "public-play" && kind != "holder-sponsor" then throw "unknown offered action"
  pure {
    kind
    token := ← objectDigest j "token"
    actor := ← objectDigest j "actor"
    beneficiary := ← objectDigest j "beneficiary"
    expiresAfterSequence := ← objectNat j "expires_after_sequence"
  }

private def parseActionTokens (j : Json) : Except String (List ActionTokenWire) := do
  let values := (← j.getArr?).toList
  if values.length > 2 then throw "too many offered actions"
  values.mapM parseActionToken

private def parseView (j : Json) : Except String ViewWire := do
  exactKeys j ["phase", "scene_content_id", "status_content_id", "progress_current",
    "progress_target", "public_play_count", "sponsorship_count", "available_actions"]
  let phase ← j.getObjValAs? String "phase"
  if phase != "service" && phase != "complete" then throw "unknown galley phase"
  let progressCurrent ← objectNat j "progress_current" (MAX_EVENTS * MAX_LOCAL_SERVICE)
  let progressTarget ← objectNat j "progress_target" (MAX_EVENTS * MAX_LOCAL_SERVICE)
  if progressCurrent > progressTarget then throw "progress exceeds target"
  pure {
    phase
    sceneContentId := ← objectDigest j "scene_content_id"
    statusContentId := ← objectDigest j "status_content_id"
    progressCurrent
    progressTarget
    publicPlayCount := ← objectNat j "public_play_count" MAX_EVENTS
    sponsorshipCount := ← objectNat j "sponsorship_count" MAX_EVENTS
    availableActions := ← parseActionTokens (← j.getObjVal? "available_actions")
  }

private def parseReceipt (j : Json) : Except String ReceiptWire := do
  exactKeys j ["kind", "actor", "beneficiary", "sequence", "local_service",
    "consumed_grant_nullifier", "authority_commitment", "power_delta", "loot_delta",
    "canon_revision_delta"]
  let kind ← j.getObjValAs? String "kind"
  if kind != "public-play" && kind != "holder-sponsor" then throw "unknown receipt kind"
  let receipt : ReceiptWire := {
    kind
    actor := ← objectDigest j "actor"
    beneficiary := ← objectDigest j "beneficiary"
    sequence := ← objectNat j "sequence" MAX_EVENTS
    localService := ← objectNat j "local_service" MAX_LOCAL_SERVICE
    consumedGrantNullifier := ← objectDigest j "consumed_grant_nullifier"
    authorityCommitment := ← objectDigest j "authority_commitment"
    powerDelta := ← objectNat j "power_delta"
    lootDelta := ← objectNat j "loot_delta"
    canonRevisionDelta := ← objectNat j "canon_revision_delta"
  }
  if receipt.powerDelta != 0 || receipt.lootDelta != 0 || receipt.canonRevisionDelta != 0 then
    throw "galley receipt claims forbidden advantage"
  pure receipt

private def parseReplay (j : Json) : Except String ReplayWire := do
  exactKeys j ["history_length", "before_sequence", "before_head", "after_sequence",
    "after_head", "projection_digest"]
  pure {
    historyLength := ← objectNat j "history_length" MAX_EVENTS
    beforeSequence := ← objectNat j "before_sequence" MAX_EVENTS
    beforeHead := ← objectDigest j "before_head"
    afterSequence := ← objectNat j "after_sequence" MAX_EVENTS
    afterHead := ← objectDigest j "after_head"
    projectionDigest := ← objectDigest j "projection_digest"
  }

private def parseOptionalEvent : Json → Except String (Option EventWire)
  | .null => pure none
  | value => some <$> parseEvent value

private def parseOptionalReceipt : Json → Except String (Option ReceiptWire)
  | .null => pure none
  | value => some <$> parseReceipt value

private def parseOutputJson (j : Json) : Except String OutputWire := do
  exactKeys j ["format", "input_digest", "policy_digest", "replay", "projection", "view",
    "event", "receipt"]
  if (← j.getObjValAs? String "format") != OUTPUT_FORMAT then throw "wrong output format"
  let output : OutputWire := {
    inputDigest := ← objectDigest j "input_digest"
    policyDigest := ← objectDigest j "policy_digest"
    replay := ← parseReplay (← j.getObjVal? "replay")
    projection := ← parseProjection (← j.getObjVal? "projection")
    view := ← parseView (← j.getObjVal? "view")
    event := ← parseOptionalEvent (← j.getObjVal? "event")
    receipt := ← parseOptionalReceipt (← j.getObjVal? "receipt")
  }
  if output.replay.afterSequence != output.projection.sequence then
    throw "replay/projection sequence mismatch"
  if output.replay.projectionDigest !=
      digestString PROJECTION_DIGEST_DOMAIN output.projection.toJson then
    throw "projection digest mismatch"
  if output.event.isSome != output.receipt.isSome then throw "event/receipt mismatch"
  pure output

def decodeOutputWithLimit (byteLimit : Nat) (bytes : String) : Option OutputWire :=
  if bytes.length ≤ byteLimit then canonicalDecode parseOutputJson OutputWire.toJson bytes else none

def decodeOutput (bytes : String) : Option OutputWire :=
  decodeOutputWithLimit WIRE_BYTE_LIMIT bytes

theorem decodeOutput_reencodes {bytes : String} {output : OutputWire}
    (accepted : decodeOutput bytes = some output) : output.toJson = bytes := by
  simp only [decodeOutput, decodeOutputWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseOutputJson OutputWire.toJson accepted
  · contradiction

theorem decodeOutput_refuses_oversized (bytes : String)
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeOutput bytes = none := by
  simp [decodeOutput, decodeOutputWithLimit, Nat.not_le.mpr oversized]

/-! ## Executable adversarial and end-to-end fixtures

⚑ **THE FIXTURES NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build root — and the seventeen `native_decide` pins
below ran at elaboration, so any fixture regression here was a hard failure of every Rust
proving target in the workspace (the compilation-unit coupling the stale-fixture outage
measured). The fixtures' STATEMENTS stay here, each as an evaluation-free `check_* : Bool`
definition (a `def` body elaborates without running), beside the private fixture policy, viewer,
carrier and authority they exercise — which `GalleyMaintenanceDailyRuntimeBoundary`'s
`adversarial_fixtures_are_private` requires stay private, and which stay private. The
EVALUATION — each `check_* = true`, pinned by `native_decide` + `#assert_compiled` — lives in
`GalleyMaintenanceDailyRuntimeFixtures.lean`, rooted in the `PathOfAngelsGuards` library: a
plain `lake build` still runs every pin, and a stale fixture reds the guard library instead of
the archive.

Fail-closed convention: a check whose judge call must SUCCEED before it can inspect the output
matches on the `Option` and answers `false` on `none` — a broken prerequisite fails the pin in
the guard library rather than wedging this module.

Named residue: NONE — no construction here demands a proof as data.
`fixture_sponsor_wire_refuses_valid_caller_json` stays below as a theorem because it is `rfl`
(the sponsor wire is unconditionally the empty string), not an evaluation.
-/

private def fixtureDigest (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def fixturePolicy : PolicyWire := {
  deploymentId := fixtureDigest 1
  federationId := fixtureDigest 2
  dailyId := fixtureDigest 3
  genesisHead := fixtureDigest 4
  dreggMint := 5
  snapshotSlot := 6
  contentEpoch := 7
  eventId := fixtureDigest 9
  rulesDigest := fixtureDigest 10
  publicActivityId := fixtureDigest 10
  sceneContentId := fixtureDigest 11
  publicActionContentId := fixtureDigest 12
  sponsorActionContentId := fixtureDigest 13
  completeContentId := fixtureDigest 14
  publicService := 3
  sponsorService := 2
  serviceTarget := 10
  powerRoot := fixtureDigest 15
  lootRoot := fixtureDigest 16
  canonRoot := fixtureDigest 17
  canonRevision := 18
}

private def fixtureViewer : ViewerWire := {
  player := fixtureDigest 21
  playerCell := fixtureDigest 22
  sponsorBeneficiary := fixtureDigest 23
}

private def fixtureState0 : EventSourcing.ReplayState ProjectionWire := {
  cursor := (streamSpec fixturePolicy).genesisCursor
  projection := initialProjection fixturePolicy
}

private def fixtureViewInput : InputWire := {
  mode := "view"
  policy := fixturePolicy
  history := []
  claimedProjection := initialProjection fixturePolicy
  viewer := fixtureViewer
  action := { kind := "none", token := zeroDigest }
}

private def fixturePublicPayload : PayloadWire := {
  kind := "public-play"
  actor := fixtureViewer.player
  beneficiary := fixtureViewer.player
  activityId := fixturePolicy.publicActivityId
  grantNullifier := zeroDigest
  authorityCommitment := zeroDigest
  localService := fixturePolicy.publicService
}

private def fixturePublicEvent : EventWire :=
  nextEvent fixturePolicy fixtureState0 fixturePublicPayload

private def fixtureProjection1 : ProjectionWire := {
  sequence := 1
  publicPlayers := [fixtureViewer.player]
  sponsors := []
  spentGrantNullifiers := []
  publicPlayCount := 1
  sponsorshipCount := 0
  localServiceTotal := fixturePolicy.publicService
  powerRoot := fixturePolicy.powerRoot
  lootRoot := fixturePolicy.lootRoot
  canonRoot := fixturePolicy.canonRoot
  canonRevision := fixturePolicy.canonRevision
}

private def fixturePublicCommand : InputWire := {
  fixtureViewInput with
  mode := "command"
  action := {
    kind := "public-play"
    token := (publicAction fixturePolicy fixtureState0 fixtureViewer).token
  }
}

private def fixtureAfterView : InputWire := {
  fixtureViewInput with
  history := [fixturePublicEvent]
  claimedProjection := fixtureProjection1
}

private def fixtureCarrier : BetaHolderSealWire := {
  deploymentId := fixturePolicy.deploymentId
  federationId := fixturePolicy.federationId
  dailyId := fixturePolicy.dailyId
  contentEpoch := fixturePolicy.contentEpoch
  eventId := fixturePolicy.eventId
  rulesDigest := fixturePolicy.rulesDigest
  signer := fixtureViewer.player
  player := fixtureViewer.player
  playerCell := fixtureViewer.playerCell
  beneficiary := fixtureViewer.sponsorBeneficiary
  grantNullifier := fixtureDigest 31
  holdingReceiptId := fixtureDigest 30
  serverToken := fixtureDigest 32
  eventSequence := 1
  expectedPredecessor := fixturePolicy.genesisHead
  expiresAfterSequence := 4
}

private def fixtureAuthority : AdmittedBetaSponsor :=
  ⟨fixtureCarrier, fixtureViewer.playerCell, .holder, 0, rfl⟩

private def fixtureSponsorCommand : InputWire := {
  fixtureViewInput with
  mode := "command"
  action := {
    kind := "holder-sponsor"
    token := (sponsorAction fixturePolicy fixtureState0 fixtureViewer fixtureAuthority).token
  }
}

private def fixtureWrongVersion : InputWire := {
  fixtureAfterView with
  history := [{ fixturePublicEvent with
    statement := { fixturePublicEvent.statement with version := STREAM_VERSION + 1 } }]
}

private def fixtureWrongPayloadDigest : InputWire := {
  fixtureAfterView with
  history := [{ fixturePublicEvent with
    statement := { fixturePublicEvent.statement with payloadDigest := zeroDigest } }]
}

private def fixtureStaleProjection : InputWire := {
  fixtureAfterView with
  claimedProjection := initialProjection fixturePolicy
}

private def fixtureForgedSponsor : InputWire := {
  fixtureViewInput with
  mode := "command"
  action := { kind := "holder-sponsor", token := fixtureDigest 99 }
}

/-- The authored fixture policy passes the wire validity predicate.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_policy_valid : Bool := fixturePolicy.validB

/-- The canonical input wire decodes back to the exact value that encoded it.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_input_roundtrip : Bool :=
  decide (decodeInput fixtureViewInput.toJson = some fixtureViewInput)

/-- A public view is judged. (Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_public_view_accepted : Bool :=
  (judgeBytesWithAuthority? fixtureViewInput.toJson 0 none).isSome

/-- A public play command is judged.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_public_command_accepted : Bool :=
  (judgeBytesWithAuthority? fixturePublicCommand.toJson 0 none).isSome

/-- The judged output bytes re-decode as an `OutputWire`.  Fail-closed: a refused command
answers `false`. (Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_public_output_redecodes : Bool :=
  match judgeBytesWithAuthority? fixturePublicCommand.toJson 0 none with
  | none => false
  | some bytes => (decodeOutput bytes).isSome

/-- Replaying the accepted event and claiming its projection is judged.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_replay_successor_accepted : Bool :=
  (judgeBytesWithAuthority? fixtureAfterView.toJson 0 none).isSome

/-- A holder sponsorship under a real admitted authority moves NO advantage anchor and issues a
receipt with zero power/loot/canon delta and bounded local service.  Fail-closed: a refused
command, or an accepted one with no receipt, answers `false`.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_beta_sponsor_accepted_without_advantage : Bool :=
  match judgeInput? fixtureSponsorCommand.toJson fixtureSponsorCommand 50 (some fixtureAuthority) with
  | none => false
  | some output =>
      output.projection.powerRoot = fixturePolicy.powerRoot &&
      output.projection.lootRoot = fixturePolicy.lootRoot &&
      output.projection.canonRoot = fixturePolicy.canonRoot &&
      output.projection.canonRevision = fixturePolicy.canonRevision &&
      match output.receipt with
      | none => false
      | some receipt => receipt.powerDelta = 0 && receipt.lootDelta = 0 &&
          receipt.canonRevisionDelta = 0 && receipt.localService ≤ MAX_LOCAL_SERVICE

/-- The beta holder seal carrier round-trips through its canonical encoding.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_beta_seal_roundtrip : Bool :=
  decide (decodeBetaHolderSeal fixtureCarrier.toJson = some fixtureCarrier)

theorem fixture_sponsor_wire_refuses_valid_caller_json :
    runAdmittedBetaSponsorWire fixtureSponsorCommand.toJson fixtureCarrier.toJson = "" := rfl

/-- The internally-authored sponsor action really is among the actions the view offers, so
the token the command carries is not a fixture-only spelling.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_internal_sponsor_view_authors_token : Bool :=
  decide ((sponsorAction fixturePolicy fixtureState0 fixtureViewer fixtureAuthority) ∈
    (viewOf fixturePolicy fixtureState0 fixtureViewer 50 (some fixtureAuthority)).availableActions)

/-- The disabled sponsor wire's output is not decodable as an `OutputWire` — it cannot be
mistaken for a judged result. (Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_fixture_sponsor_wire_output_never_decodes : Bool :=
  (decodeOutput (runAdmittedBetaSponsorWire fixtureSponsorCommand.toJson
    fixtureCarrier.toJson)).isNone

/-- A history event at the wrong stream version is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_wrong_version_refused : Bool :=
  (judgeBytesWithAuthority? fixtureWrongVersion.toJson 0 none).isNone

/-- A history event whose payload digest does not bind its payload is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_wrong_payload_digest_refused : Bool :=
  (judgeBytesWithAuthority? fixtureWrongPayloadDigest.toJson 0 none).isNone

/-- A claimed projection that is stale for the submitted history is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_stale_projection_refused : Bool :=
  (judgeBytesWithAuthority? fixtureStaleProjection.toJson 0 none).isNone

/-- A holder-sponsor command with a forged token and no admitted authority is refused.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_forged_sponsor_without_authority_refused : Bool :=
  (judgeBytesWithAuthority? fixtureForgedSponsor.toJson 0 none).isNone

/-- Canonical bytes plus one trailing space are not canonical.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_trailing_byte_refused : Bool :=
  (decodeInput (fixtureViewInput.toJson ++ " ")).isNone

/-- An unknown field is refused rather than ignored.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_unknown_field_refused : Bool :=
  (decodeInput "{\"format\":\"POA-GALLEY-DAILY-IN-1\",\"unknown\":0}").isNone

/-- The byte limit is enforced before parsing.
(Pinned `= true` in `GalleyMaintenanceDailyRuntimeFixtures`.) -/
def check_hostile_tiny_byte_limit_refused : Bool :=
  (decodeInputWithLimit 4 fixtureViewInput.toJson).isNone

#assert_axioms canonicalDecode_reencodes
#assert_axioms decodeInput_reencodes
#assert_axioms decodeInput_refuses_oversized
#assert_axioms decodePolicy_reencodes
#assert_axioms reduce_preserves_advantage_anchors
#assert_axioms reduce_holder_sponsor_bounded
#assert_axioms judge_command_projection_is_reduce
#assert_axioms judge_view_projection_is_claimed
#assert_axioms judge_output_preserves_advantage_anchors
#assert_axioms AdmittedBetaSponsor.no_chamber_power
#assert_axioms receiptOf_has_no_advantage_delta
#assert_axioms no_authority_cannot_form_holder_payload
#assert_axioms decodeBetaHolderSeal_reencodes
#assert_axioms sponsor_wire_is_unconditionally_disabled
#assert_axioms decodeOutput_reencodes
#assert_axioms decodeOutput_refuses_oversized
#assert_axioms fixture_sponsor_wire_refuses_valid_caller_json

-- The seventeen fixture pins (`native_decide` + `#assert_compiled`) live in
-- `GalleyMaintenanceDailyRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- fixture header above.
