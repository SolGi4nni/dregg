/-
# Path of Angels — strict Signal network wire

This is the deliberately small text boundary used by the internal Signal
evaluator.  The request is untrusted, but `config`/`canon`/`carrier` become
authoritative only when the node adapter derives them from persisted activated
state and the finalized SignedTurn; this codec does not authenticate their origin.
JSON is used only as a transport syntax.  Accepted bytes
must equal Lean's compact encoder byte-for-byte, so whitespace, reordered keys,
unknown fields, alternate number spellings, uppercase digests, and trailing bytes
all refuse.

Syntax parsing and semantic construction are separate.  The wire structures are
proof-erased and bounded; `SignalConfigWire.toSemantic?` and
`WorldStateWire.toSemantic?` rebuild the proof-carrying game types.
-/
import Lean.Data.Json
import Mathlib.Data.Finset.Sort
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Games.PathOfAngels.Canon
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NetworkJudgeWire

open Lean
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-SIGNAL-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-SIGNAL-OUT-1"

/-- Every integer admitted by this transport fits an unsigned 64-bit host word. -/
abbrev WIRE_NAT_LIMIT : Nat := 2 ^ 64 - 1
abbrev WIRE_ID_LIMIT : Nat := 2 ^ 32 - 1
abbrev WIRE_ARTIFACT_LIMIT : Nat := 4096
/-! `consumedRuns` is presently a bounded per-content-epoch replay window.  A
deployment must roll the epoch or replace the explicit population with an
authenticated accumulator before reaching this limit; silently dropping rows
would reopen replay. -/
abbrev WIRE_RECEIPT_LIMIT : Nat := 16384
/-- Sparse players are likewise bounded per content epoch; reaching this requires
epoch rollover or a committed sparse-map root before admitting another player. -/
abbrev WIRE_COUNTER_LIMIT : Nat := 16384
abbrev WIRE_ACTION_LIMIT : Nat := SignalTriangulation.MAX_TURNS
/-- Refuse oversized envelopes before invoking the JSON parser.  Collection
bounds remain the semantic limits; this is the outer allocation/CPU fuse. -/
abbrev WIRE_BYTE_LIMIT : Nat := 16 * 1024 * 1024

private def jsonString (s : String) : String := String.quote s
private def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then
    pure ()
  else
    throw "missing or unknown field"

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

/-! ## Proof-erased complete Signal input -/

structure ArtifactRefWire where
  missionId : Nat
  artifactId : Nat
  sourceDigest : Digest32
  contentDigest : Digest32
deriving DecidableEq

structure BudgetWire where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  relics : Nat
deriving DecidableEq, Repr

structure MissionWire where
  missionId : Nat
  artifact : ArtifactRefWire
  epoch : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  runSeed : Digest32
  budget : BudgetWire
  allowedRelics : List Nat
  privacy : PrivacyGrade
  ballot : BallotRegime
deriving DecidableEq

structure ContributionWire where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  relics : List Nat
deriving DecidableEq, Repr

structure CodeWire where
  low : Nat
  mid : Nat
  high : Nat
deriving DecidableEq, Repr

structure SignalConfigWire where
  target : CodeWire
  mission : MissionWire
  reward : ContributionWire
deriving DecidableEq

structure WorldStateWire where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  discoveredRelics : List Nat
  betaArtifacts : List ArtifactRefWire
  sequence : Nat
deriving DecidableEq

structure ReceiptKeyWire where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  playerKey : Digest32
  playerCounter : Nat
deriving DecidableEq

structure PlayerCounterRowWire where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  playerKey : Digest32
  value : Nat
deriving DecidableEq

/-- Complete finite projection of Canon.  All set/table members are carried as
canonical ascending lists; semantic decoding additionally checks subset and
disjointness invariants before constructing Canon state. -/
structure CanonStateWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  curatorKey : Digest32
  world : WorldStateWire
  known : List ArtifactRefWire
  alpha : List ArtifactRefWire
  superseded : List ArtifactRefWire
  consumedRuns : List ReceiptKeyWire
  playerCounters : List PlayerCounterRowWire
  revision : Nat
  curatorCounter : Nat
deriving DecidableEq

/-- ⚠ **This object carries the curator's slot SECRET.**  It is node-held state, it
is never a client claim, and `SignalInputWire` is the node→Lean transport only: these
bytes must not leave the node.  No output wire, descriptor or catalog renders a slot
secret, and `Emit` has no function that could.

The judge is handed the secret because it RE-DERIVES the run seed rather than
trusting one.  `Judged.admissionChecks` requires `commitment` to be
`HiddenInstance.commit secret slot`, and the live `runSeed` to be
`HiddenInstance.runSeedFor` of that same secret, slot and player — so a node that
published one commitment and then judged against a different secret is refused. -/
structure SlotStateWire where
  slot : Nat
  secret : Digest32
  commitment : Digest32
deriving DecidableEq

/-- ⚠ `runSeed` is GONE from the request.  A client that could state the live run
seed could compute its own instance, which is the whole hole.  What a client states
instead is the slot it played in and the commitment its run opening showed it; the
judge compares both against node state and derives the seed itself. -/
structure SignalRequestWire where
  missionId : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  slot : Nat
  slotCommitment : Digest32
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat
  expectedWorldSequence : Nat
  expectedCanonRevision : Nat
  actions : List CodeWire
deriving DecidableEq

/-- Facts authenticated by the finalized SignedTurn path.  This is intentionally
not reconstructed from the request: signer, pre-state root, and current counter
would otherwise be self-asserted. -/
structure FinalizedCarrierWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  actorRoot : Digest32
  playerKey : Digest32
  currentPlayerCounter : Nat
deriving DecidableEq

structure SignalInputWire where
  config : SignalConfigWire
  world : WorldStateWire
  canon : CanonStateWire
  carrier : FinalizedCarrierWire
  slotState : SlotStateWire
  request : SignalRequestWire
deriving DecidableEq

/-! Canonical collection order is semantic, not lexicographic decimal text. -/

open scoped Prod.Lex

private abbrev ArtifactWireOrderKey := Nat ×ₗ (Nat ×ₗ (Digest32 ×ₗ Digest32))

private def ArtifactRefWire.orderKey (a : ArtifactRefWire) : ArtifactWireOrderKey :=
  toLex (a.missionId, toLex (a.artifactId, toLex (a.sourceDigest, a.contentDigest)))

instance : LinearOrder ArtifactRefWire :=
  LinearOrder.lift' ArtifactRefWire.orderKey (by
    intro left right equal
    cases left
    cases right
    simp_all [ArtifactRefWire.orderKey])

private abbrev ReceiptWireOrderKey :=
  Digest32 ×ₗ (Digest32 ×ₗ (Nat ×ₗ (Digest32 ×ₗ Nat)))

private def ReceiptKeyWire.orderKey (r : ReceiptKeyWire) : ReceiptWireOrderKey :=
  toLex (r.federationId,
    toLex (r.contentSession, toLex (r.contentEpoch, toLex (r.playerKey, r.playerCounter))))

instance : LinearOrder ReceiptKeyWire :=
  LinearOrder.lift' ReceiptKeyWire.orderKey (by
    intro left right equal
    cases left
    cases right
    simp_all [ReceiptKeyWire.orderKey])

private abbrev CounterWireOrderKey := Digest32 ×ₗ (Digest32 ×ₗ (Nat ×ₗ Digest32))

private def PlayerCounterRowWire.orderKey (r : PlayerCounterRowWire) : CounterWireOrderKey :=
  toLex (r.federationId, toLex (r.contentSession, toLex (r.contentEpoch, r.playerKey)))

private def canonicalArtifactsB (limit : Nat) (xs : List ArtifactRefWire) : Bool :=
  xs.length ≤ limit && decide (xs.Pairwise (· < ·))

private def canonicalReceiptsB (xs : List ReceiptKeyWire) : Bool :=
  xs.length ≤ WIRE_RECEIPT_LIMIT && decide (xs.Pairwise (· < ·))

private def canonicalCounterRowsB (xs : List PlayerCounterRowWire) : Bool :=
  xs.length ≤ WIRE_COUNTER_LIMIT &&
    decide ((xs.map PlayerCounterRowWire.orderKey).Pairwise (· < ·))

/-! ## Canonical encoders -/

def ArtifactRefWire.toJson (a : ArtifactRefWire) : String :=
  "{\"mission_id\":" ++ toString a.missionId ++
    ",\"artifact_id\":" ++ toString a.artifactId ++
    ",\"source_digest\":" ++ jsonString (Emit.bytes32Hex a.sourceDigest) ++
    ",\"content_digest\":" ++ jsonString (Emit.bytes32Hex a.contentDigest) ++ "}"

def BudgetWire.toJson (b : BudgetWire) : String :=
  "{\"intel\":" ++ toString b.intel ++
    ",\"supplies\":" ++ toString b.supplies ++
    ",\"cohesion\":" ++ toString b.cohesion ++
    ",\"influence\":" ++ toString b.influence ++
    ",\"score\":" ++ toString b.score ++
    ",\"relics\":" ++ toString b.relics ++ "}"

private def privacyTag : PrivacyGrade → String
  | .public => "public"
  | .operatorVisibleHidingFri => "operator-visible-hiding-fri"
  | .processSeparatedThreshold => "process-separated-threshold"
  | .independentOperatorThreshold => "independent-operator-threshold"

private def ballotTag : BallotRegime → String
  | .none => "none"
  | .onePlayerOneVoice => "one-player-one-voice"
  | .oneWalletOneVoice => "one-wallet-one-voice"
  | .cappedChoir => "capped-choir"
  | .predictionOracle => "prediction-oracle"

def MissionWire.toJson (m : MissionWire) : String :=
  "{\"mission_id\":" ++ toString m.missionId ++
    ",\"artifact\":" ++ m.artifact.toJson ++
    ",\"epoch\":" ++ toString m.epoch ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex m.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex m.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex m.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex m.contentSession) ++
    ",\"run_seed\":" ++ jsonString (Emit.bytes32Hex m.runSeed) ++
    ",\"budget\":" ++ m.budget.toJson ++
    ",\"allowed_relics\":" ++ jsonArray (m.allowedRelics.map toString) ++
    ",\"privacy\":" ++ jsonString (privacyTag m.privacy) ++
    ",\"ballot\":" ++ jsonString (ballotTag m.ballot) ++ "}"

def ContributionWire.toJson (c : ContributionWire) : String :=
  "{\"intel\":" ++ toString c.intel ++
    ",\"supplies\":" ++ toString c.supplies ++
    ",\"cohesion\":" ++ toString c.cohesion ++
    ",\"influence\":" ++ toString c.influence ++
    ",\"score\":" ++ toString c.score ++
    ",\"relics\":" ++ jsonArray (c.relics.map toString) ++ "}"

def CodeWire.toJson (c : CodeWire) : String :=
  "{\"low\":" ++ toString c.low ++
    ",\"mid\":" ++ toString c.mid ++
    ",\"high\":" ++ toString c.high ++ "}"

def SignalConfigWire.toJson (c : SignalConfigWire) : String :=
  "{\"target\":" ++ c.target.toJson ++
    ",\"mission\":" ++ c.mission.toJson ++
    ",\"reward\":" ++ c.reward.toJson ++ "}"

def WorldStateWire.toJson (w : WorldStateWire) : String :=
  "{\"intel\":" ++ toString w.intel ++
    ",\"supplies\":" ++ toString w.supplies ++
    ",\"cohesion\":" ++ toString w.cohesion ++
    ",\"influence\":" ++ toString w.influence ++
    ",\"score\":" ++ toString w.score ++
    ",\"discovered_relics\":" ++ jsonArray (w.discoveredRelics.map toString) ++
    ",\"beta_artifacts\":" ++ jsonArray (w.betaArtifacts.map ArtifactRefWire.toJson) ++
    ",\"sequence\":" ++ toString w.sequence ++ "}"

def ReceiptKeyWire.toJson (r : ReceiptKeyWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex r.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex r.contentSession) ++
    ",\"content_epoch\":" ++ toString r.contentEpoch ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex r.playerKey) ++
    ",\"player_counter\":" ++ toString r.playerCounter ++ "}"

def PlayerCounterRowWire.toJson (r : PlayerCounterRowWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex r.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex r.contentSession) ++
    ",\"content_epoch\":" ++ toString r.contentEpoch ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex r.playerKey) ++
    ",\"value\":" ++ toString r.value ++ "}"

def CanonStateWire.toJson (c : CanonStateWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex c.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex c.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex c.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex c.contentSession) ++
    ",\"content_epoch\":" ++ toString c.contentEpoch ++
    ",\"curator_key\":" ++ jsonString (Emit.bytes32Hex c.curatorKey) ++
    ",\"world\":" ++ c.world.toJson ++
    ",\"known\":" ++ jsonArray (c.known.map ArtifactRefWire.toJson) ++
    ",\"alpha\":" ++ jsonArray (c.alpha.map ArtifactRefWire.toJson) ++
    ",\"superseded\":" ++ jsonArray (c.superseded.map ArtifactRefWire.toJson) ++
    ",\"consumed_runs\":" ++ jsonArray (c.consumedRuns.map ReceiptKeyWire.toJson) ++
    ",\"player_counters\":" ++ jsonArray (c.playerCounters.map PlayerCounterRowWire.toJson) ++
    ",\"revision\":" ++ toString c.revision ++
    ",\"curator_counter\":" ++ toString c.curatorCounter ++ "}"

def SignalRequestWire.toJson (r : SignalRequestWire) : String :=
  "{\"mission_id\":" ++ toString r.missionId ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex r.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex r.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex r.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex r.contentSession) ++
    ",\"content_epoch\":" ++ toString r.contentEpoch ++
    ",\"slot\":" ++ toString r.slot ++
    ",\"slot_commitment\":" ++ jsonString (Emit.bytes32Hex r.slotCommitment) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex r.actorRoot) ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex r.playerKey) ++
    ",\"previous_player_counter\":" ++ toString r.previousPlayerCounter ++
    ",\"expected_world_sequence\":" ++ toString r.expectedWorldSequence ++
    ",\"expected_canon_revision\":" ++ toString r.expectedCanonRevision ++
    ",\"actions\":" ++ jsonArray (r.actions.map CodeWire.toJson) ++ "}"

def SlotStateWire.toJson (s : SlotStateWire) : String :=
  "{\"slot\":" ++ toString s.slot ++
    ",\"secret\":" ++ jsonString (Emit.bytes32Hex s.secret) ++
    ",\"commitment\":" ++ jsonString (Emit.bytes32Hex s.commitment) ++ "}"

def FinalizedCarrierWire.toJson (c : FinalizedCarrierWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex c.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex c.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex c.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex c.contentSession) ++
    ",\"content_epoch\":" ++ toString c.contentEpoch ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex c.actorRoot) ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex c.playerKey) ++
    ",\"current_player_counter\":" ++ toString c.currentPlayerCounter ++ "}"

def SignalInputWire.toJson (input : SignalInputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"config\":" ++ input.config.toJson ++
    ",\"world\":" ++ input.world.toJson ++
    ",\"canon\":" ++ input.canon.toJson ++
    ",\"carrier\":" ++ input.carrier.toJson ++
    ",\"slot_state\":" ++ input.slotState.toJson ++
    ",\"request\":" ++ input.request.toJson ++ "}"

/-! ## Strict syntax parsers -/

private def parseArtifactRef (j : Json) : Except String ArtifactRefWire := do
  exactKeys j ["mission_id", "artifact_id", "source_digest", "content_digest"]
  pure {
    missionId := ← objectNat j "mission_id" WIRE_ID_LIMIT
    artifactId := ← objectNat j "artifact_id" WIRE_ID_LIMIT
    sourceDigest := ← objectDigest j "source_digest"
    contentDigest := ← objectDigest j "content_digest"
  }

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

private def parseConfig (j : Json) : Except String SignalConfigWire := do
  exactKeys j ["target", "mission", "reward"]
  pure {
    target := ← parseCode (← j.getObjVal? "target")
    mission := ← parseMission (← j.getObjVal? "mission")
    reward := ← parseContribution (← j.getObjVal? "reward")
  }

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
      parseNatList (← j.getObjVal? "discovered_relics") WORLD_RELIC_LIMIT
    betaArtifacts := ← parseBoundedArray (← j.getObjVal? "beta_artifacts")
      BETA_ARTIFACT_LIMIT parseArtifactRef (canonicalArtifactsB BETA_ARTIFACT_LIMIT)
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

private def parseCanon (j : Json) : Except String CanonStateWire := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch", "curator_key", "world", "known", "alpha", "superseded", "consumed_runs",
    "player_counters", "revision", "curator_counter"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    curatorKey := ← objectDigest j "curator_key"
    world := ← parseWorld (← j.getObjVal? "world")
    known := ← parseBoundedArray (← j.getObjVal? "known") WIRE_ARTIFACT_LIMIT
      parseArtifactRef (canonicalArtifactsB WIRE_ARTIFACT_LIMIT)
    alpha := ← parseBoundedArray (← j.getObjVal? "alpha") WIRE_ARTIFACT_LIMIT
      parseArtifactRef (canonicalArtifactsB WIRE_ARTIFACT_LIMIT)
    superseded := ← parseBoundedArray (← j.getObjVal? "superseded")
      WIRE_ARTIFACT_LIMIT parseArtifactRef (canonicalArtifactsB WIRE_ARTIFACT_LIMIT)
    consumedRuns := ← parseBoundedArray (← j.getObjVal? "consumed_runs")
      WIRE_RECEIPT_LIMIT parseReceiptKey canonicalReceiptsB
    playerCounters := ← parseBoundedArray (← j.getObjVal? "player_counters")
      WIRE_COUNTER_LIMIT parseCounterRow canonicalCounterRowsB
    revision := ← objectNat j "revision"
    curatorCounter := ← objectNat j "curator_counter"
  }

private def parseActions (j : Json) : Except String (List CodeWire) := do
  let values := (← j.getArr?).toList
  if values.length > WIRE_ACTION_LIMIT then throw "Signal transcript exceeds turn limit"
  values.mapM parseCode

private def parseSlotState (j : Json) : Except String SlotStateWire := do
  exactKeys j ["slot", "secret", "commitment"]
  pure {
    slot := ← objectNat j "slot"
    secret := ← objectDigest j "secret"
    commitment := ← objectDigest j "commitment"
  }

private def parseRequest (j : Json) : Except String SignalRequestWire := do
  exactKeys j ["mission_id", "federation_id", "content_root", "activation_digest",
    "content_session", "content_epoch", "slot", "slot_commitment", "actor_root", "player_key",
    "previous_player_counter", "expected_world_sequence", "expected_canon_revision", "actions"]
  pure {
    missionId := ← objectNat j "mission_id" WIRE_ID_LIMIT
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    slot := ← objectNat j "slot"
    slotCommitment := ← objectDigest j "slot_commitment"
    actorRoot := ← objectDigest j "actor_root"
    playerKey := ← objectDigest j "player_key"
    previousPlayerCounter := ← objectNat j "previous_player_counter"
    expectedWorldSequence := ← objectNat j "expected_world_sequence"
    expectedCanonRevision := ← objectNat j "expected_canon_revision"
    actions := ← parseActions (← j.getObjVal? "actions")
  }

private def parseCarrier (j : Json) : Except String FinalizedCarrierWire := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch", "actor_root", "player_key", "current_player_counter"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    actorRoot := ← objectDigest j "actor_root"
    playerKey := ← objectDigest j "player_key"
    currentPlayerCounter := ← objectNat j "current_player_counter"
  }

private def parseInputJson (j : Json) : Except String SignalInputWire := do
  exactKeys j ["format", "config", "world", "canon", "carrier", "slot_state", "request"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong Signal input format"
  pure {
    config := ← parseConfig (← j.getObjVal? "config")
    world := ← parseWorld (← j.getObjVal? "world")
    canon := ← parseCanon (← j.getObjVal? "canon")
    carrier := ← parseCarrier (← j.getObjVal? "carrier")
    slotState := ← parseSlotState (← j.getObjVal? "slot_state")
    request := ← parseRequest (← j.getObjVal? "request")
  }

/-- A generic canonicality seal.  The semantic parser is run first, then the exact
Lean encoder must reproduce the candidate bytes. -/
def canonicalDecode {T : Type} (parse : Json → Except String T) (encode : T → String)
    (bytes : String) : Option T :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json =>
      match parse json with
      | .error _ => none
      | .ok value => if encode value = bytes then some value else none

def decodeSignalInputWithLimit (byteLimit : Nat) (bytes : String) : Option SignalInputWire :=
  if bytes.length ≤ byteLimit then
    canonicalDecode parseInputJson SignalInputWire.toJson bytes
  else none

def decodeSignalInput (bytes : String) : Option SignalInputWire :=
  decodeSignalInputWithLimit WIRE_BYTE_LIMIT bytes

/-! ### Standalone Canon and config blobs

Persistence stores the retained genesis Canon and the active mission config as
their own exact byte blobs, not only as members of a Signal input.  A reader
that has those bytes must be able to decode them under the identical canonical
seal, rather than re-wrapping them in a synthetic request — that re-wrapping is
how a non-canonical stored blob would get silently canonicalized on the way in.
Both entry points are the same `canonicalDecode` over the same private parsers,
so acceptance here and acceptance inside `decodeSignalInput` cannot drift. -/

def decodeCanonStateWithLimit (byteLimit : Nat) (bytes : String) : Option CanonStateWire :=
  if bytes.length ≤ byteLimit then
    canonicalDecode parseCanon CanonStateWire.toJson bytes
  else none

def decodeCanonState (bytes : String) : Option CanonStateWire :=
  decodeCanonStateWithLimit WIRE_BYTE_LIMIT bytes

def decodeSignalConfigWithLimit (byteLimit : Nat) (bytes : String) : Option SignalConfigWire :=
  if bytes.length ≤ byteLimit then
    canonicalDecode parseConfig SignalConfigWire.toJson bytes
  else none

def decodeSignalConfig (bytes : String) : Option SignalConfigWire :=
  decodeSignalConfigWithLimit WIRE_BYTE_LIMIT bytes

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

theorem decodeSignalInput_reencodes {bytes : String} {input : SignalInputWire}
    (accepted : decodeSignalInput bytes = some input) : input.toJson = bytes :=
  by
    simp only [decodeSignalInput, decodeSignalInputWithLimit] at accepted
    split at accepted
    · exact canonicalDecode_reencodes parseInputJson SignalInputWire.toJson accepted
    · contradiction

theorem decodeSignalInput_refuses_oversized (bytes : String)
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeSignalInput bytes = none := by
  simp [decodeSignalInput, decodeSignalInputWithLimit, Nat.not_le.mpr oversized]

theorem decodeCanonState_reencodes {bytes : String} {canon : CanonStateWire}
    (accepted : decodeCanonState bytes = some canon) : canon.toJson = bytes := by
  simp only [decodeCanonState, decodeCanonStateWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseCanon CanonStateWire.toJson accepted
  · contradiction

theorem decodeSignalConfig_reencodes {bytes : String} {config : SignalConfigWire}
    (accepted : decodeSignalConfig bytes = some config) : config.toJson = bytes := by
  simp only [decodeSignalConfig, decodeSignalConfigWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseConfig SignalConfigWire.toJson accepted
  · contradiction

/-- The strict decoder is injective on accepted byte strings, independent of any
host JSON implementation. -/
theorem decodeSignalInput_accepted_bytes_injective {left right : String}
    {input : SignalInputWire} (hl : decodeSignalInput left = some input)
    (hr : decodeSignalInput right = some input) : left = right := by
  rw [← decodeSignalInput_reencodes hl, ← decodeSignalInput_reencodes hr]

/-! ## Semantic reconstruction (separate from syntax) -/

private def checkedMetric (value : Nat) : Option Metric :=
  if h : value ≤ METRIC_LIMIT then some ⟨value, Nat.lt_succ_of_le h⟩ else none

def ArtifactRefWire.toSemantic? (a : ArtifactRefWire) : Option ArtifactRef := do
  if a.missionId > WIRE_ID_LIMIT ∨ a.artifactId > WIRE_ID_LIMIT then none else
  some {
    missionId := ⟨a.missionId⟩
    artifactId := ⟨a.artifactId⟩
    sourceDigest := a.sourceDigest
    contentDigest := a.contentDigest
  }

def BudgetWire.toSemantic? (b : BudgetWire) : Option ContributionBudget := do
  let intel ← checkedMetric b.intel
  let supplies ← checkedMetric b.supplies
  let cohesion ← checkedMetric b.cohesion
  let influence ← checkedMetric b.influence
  let score ← checkedMetric b.score
  if h : b.relics < RELIC_LIMIT + 1 then
    some { intel, supplies, cohesion, influence, score, relics := ⟨b.relics, h⟩ }
  else none

def ContributionWire.toSemantic? (c : ContributionWire) : Option Contribution :=
  if strictNatListB RELIC_LIMIT c.relics then
    validateContribution {
      intel := c.intel
      supplies := c.supplies
      cohesion := c.cohesion
      influence := c.influence
      score := c.score
      relics := c.relics.map RelicId.mk
    }
  else none

def CodeWire.toSemantic? (c : CodeWire) : Option SignalTriangulation.Code := do
  if hl : c.low < 6 then
    if hm : c.mid < 6 then
      if hh : c.high < 6 then
        some { low := ⟨c.low, hl⟩, mid := ⟨c.mid, hm⟩, high := ⟨c.high, hh⟩ }
      else none
    else none
  else none

def MissionWire.toSemantic? (m : MissionWire) : Option MissionSpec := do
  if m.missionId > WIRE_ID_LIMIT ∨ m.epoch > WIRE_NAT_LIMIT then none else
  let artifact ← m.artifact.toSemantic?
  let budget ← m.budget.toSemantic?
  if !strictNatListB MISSION_RELIC_LIMIT m.allowedRelics then none else
  let allowedRelics := (m.allowedRelics.map RelicId.mk).toFinset
  if artifactMatch : artifact.missionId = ⟨m.missionId⟩ then
    if relicBound : allowedRelics.card ≤ MISSION_RELIC_LIMIT then
      some {
        missionId := ⟨m.missionId⟩
        artifact
        epoch := ⟨m.epoch⟩
        federationId := m.federationId
        contentRoot := m.contentRoot
        activationDigest := m.activationDigest
        contentSession := m.contentSession
        runSeed := m.runSeed
        budget
        allowedRelics
        privacy := m.privacy
        ballot := m.ballot
        artifact_matches := artifactMatch
        allowed_relics_bounded := relicBound
      }
    else none
  else none

def SignalConfigWire.toSemantic? (c : SignalConfigWire) : Option SignalTriangulation.Config := do
  let target ← c.target.toSemantic?
  let mission ← c.mission.toSemantic?
  let reward ← c.reward.toSemantic?
  if rewardAccepted : mission.acceptsContribution reward = true then
    if targetEq : target = SignalTriangulation.targetFromSeed mission.runSeed then
      some { target, mission, reward, reward_accepted := rewardAccepted, target_eq := targetEq }
    else none
  else none

def WorldStateWire.toSemantic? (w : WorldStateWire) : Option WorldState := do
  if w.sequence > WIRE_NAT_LIMIT then none else
  if !strictNatListB WORLD_RELIC_LIMIT w.discoveredRelics then none else
  if !canonicalArtifactsB BETA_ARTIFACT_LIMIT w.betaArtifacts then none else
  let intel ← checkedMetric w.intel
  let supplies ← checkedMetric w.supplies
  let cohesion ← checkedMetric w.cohesion
  let influence ← checkedMetric w.influence
  let score ← checkedMetric w.score
  let artifacts ← w.betaArtifacts.mapM ArtifactRefWire.toSemantic?
  let discoveredRelics := (w.discoveredRelics.map RelicId.mk).toFinset
  let betaArtifacts := artifacts.toFinset
  if relicBound : discoveredRelics.card ≤ WORLD_RELIC_LIMIT then
    if artifactBound : betaArtifacts.card ≤ BETA_ARTIFACT_LIMIT then
      some {
        intel, supplies, cohesion, influence, score
        discoveredRelics, betaArtifacts
        sequence := w.sequence
        relics_bounded := relicBound
        beta_bounded := artifactBound
      }
    else none
  else none

def ReceiptKeyWire.toSemantic? (r : ReceiptKeyWire) : Option ReceiptKey := do
  if r.contentEpoch > WIRE_NAT_LIMIT ∨ r.playerCounter > WIRE_NAT_LIMIT then none else
  some {
    federationId := r.federationId
    contentSession := r.contentSession
    contentEpoch := ⟨r.contentEpoch⟩
    playerKey := r.playerKey
    playerCounter := r.playerCounter
  }

def PlayerCounterRowWire.toSemantic? (r : PlayerCounterRowWire) :
    Option (PlayerCounterKey × PlayerCounter) := do
  if r.contentEpoch > WIRE_NAT_LIMIT ∨ r.value = 0 then none else
  let value ← checkedPlayerCounter r.value
  some (
    { federationId := r.federationId
      contentSession := r.contentSession
      contentEpoch := ⟨r.contentEpoch⟩
      playerKey := r.playerKey },
    value)

def CanonStateWire.toPlayerCounterTable? (c : CanonStateWire) : Option PlayerCounterTable := do
  if !canonicalCounterRowsB c.playerCounters then none else
  let rows ← c.playerCounters.mapM PlayerCounterRowWire.toSemantic?
  PlayerCounterTable.ofRows? rows

def CanonStateWire.toSemantic? (c : CanonStateWire) : Option CanonState := do
  if c.contentEpoch > WIRE_NAT_LIMIT ∨ c.revision > WIRE_NAT_LIMIT ∨
      c.curatorCounter > WIRE_NAT_LIMIT then none else
  if !canonicalArtifactsB WIRE_ARTIFACT_LIMIT c.known ∨
      !canonicalArtifactsB WIRE_ARTIFACT_LIMIT c.alpha ∨
      !canonicalArtifactsB WIRE_ARTIFACT_LIMIT c.superseded ∨
      !canonicalReceiptsB c.consumedRuns then none else
  let knownRows ← c.known.mapM ArtifactRefWire.toSemantic?
  let alphaRows ← c.alpha.mapM ArtifactRefWire.toSemantic?
  let supersededRows ← c.superseded.mapM ArtifactRefWire.toSemantic?
  let consumedRows ← c.consumedRuns.mapM ReceiptKeyWire.toSemantic?
  let playerCounters ← c.toPlayerCounterTable?
  let world ← c.world.toSemantic?
  let known := knownRows.toFinset
  let alpha := alphaRows.toFinset
  let superseded := supersededRows.toFinset
  let consumedRuns := consumedRows.toFinset
  if alphaKnown : alpha ⊆ known then
    if supersededKnown : superseded ⊆ known then
      if disjoint : Disjoint alpha superseded then
        some {
          federationId := c.federationId
          contentRoot := c.contentRoot
          activationDigest := c.activationDigest
          contentSession := c.contentSession
          contentEpoch := ⟨c.contentEpoch⟩
          curatorKey := c.curatorKey
          world
          known, alpha, superseded, consumedRuns, playerCounters
          revision := c.revision
          curatorCounter := c.curatorCounter
          alpha_known := alphaKnown
          superseded_known := supersededKnown
          alpha_disjoint_superseded := disjoint
        }
      else none
    else none
  else none

def FinalizedCarrierWire.toSemantic? (c : FinalizedCarrierWire) : Option FinalizedCarrier := do
  if c.contentEpoch > WIRE_NAT_LIMIT then none else
  let currentPlayerCounter ← checkedPlayerCounter c.currentPlayerCounter
  some {
    federationId := c.federationId
    contentRoot := c.contentRoot
    activationDigest := c.activationDigest
    contentSession := c.contentSession
    contentEpoch := ⟨c.contentEpoch⟩
    actorRoot := c.actorRoot
    playerKey := c.playerKey
    currentPlayerCounter
  }

/-- ⚠ `slot`, `slotSecret` and `slotCommitment` are node-held state carried through
from `SlotStateWire`.  They are what lets `NetworkJudge.activeOf` build an
`ActiveRunState` the admission gate can check: without the secret there is nothing to
re-derive the run seed from, and a judge that cannot re-derive it is a judge that
trusts a supplied one. -/
structure SemanticInput where
  config : SignalTriangulation.Config
  world : WorldState
  canon : CanonState
  carrier : FinalizedCarrier
  slot : EpochId
  slotSecret : HiddenInstance.SlotSecret
  slotCommitment : Digest32
  request : SignalRequestWire

/-- The portion of semantic input independent of Canon's curated set proofs.  The
network judge combines this with `CanonStateWire.toSemantic?` once constructing the
complete active Canon state. -/
def SignalInputWire.toSemantic? (input : SignalInputWire) : Option SemanticInput := do
  let config ← input.config.toSemantic?
  let world ← input.world.toSemantic?
  let canon ← input.canon.toSemantic?
  let carrier ← input.carrier.toSemantic?
  if input.slotState.slot > WIRE_NAT_LIMIT then none else
  if _worldExact : world = canon.world then
    some {
      config, world, canon, carrier
      slot := ⟨input.slotState.slot⟩
      slotSecret := ⟨input.slotState.secret⟩
      slotCommitment := input.slotState.commitment
      request := input.request
    }
  else none

def decodeSignalInputSemantic (bytes : String) : Option SemanticInput := do
  let wire ← decodeSignalInput bytes
  wire.toSemantic?

/-! ## Successor and semantic-receipt wire -/

/-- Complete proof-erased projection of Core's receipt.  The whole mission and
both worlds are present; callers cannot substitute a display id for an artifact or
omit the actor/domain/counter binding. -/
structure SignalReceiptWire where
  mission : MissionWire
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat
  playerCounter : Nat
  runSeed : Digest32
  preWorld : WorldStateWire
  postWorld : WorldStateWire
  contribution : ContributionWire
  transcriptDigest : Digest32
deriving DecidableEq

structure SignalOutputWire where
  receipt : SignalReceiptWire
  successorWorld : WorldStateWire
  successorCanon : CanonStateWire
deriving DecidableEq

def SignalReceiptWire.toJson (r : SignalReceiptWire) : String :=
  "{\"mission\":" ++ r.mission.toJson ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex r.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex r.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex r.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex r.contentSession) ++
    ",\"content_epoch\":" ++ toString r.contentEpoch ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex r.actorRoot) ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex r.playerKey) ++
    ",\"previous_player_counter\":" ++ toString r.previousPlayerCounter ++
    ",\"player_counter\":" ++ toString r.playerCounter ++
    ",\"run_seed\":" ++ jsonString (Emit.bytes32Hex r.runSeed) ++
    ",\"pre_world\":" ++ r.preWorld.toJson ++
    ",\"post_world\":" ++ r.postWorld.toJson ++
    ",\"contribution\":" ++ r.contribution.toJson ++
    ",\"transcript_digest\":" ++ jsonString (Emit.bytes32Hex r.transcriptDigest) ++ "}"

def SignalOutputWire.toJson (output : SignalOutputWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"receipt\":" ++ output.receipt.toJson ++
    ",\"successor_world\":" ++ output.successorWorld.toJson ++
    ",\"successor_canon\":" ++ output.successorCanon.toJson ++ "}"

private def parseReceipt (j : Json) : Except String SignalReceiptWire := do
  exactKeys j ["mission", "federation_id", "content_root", "activation_digest",
    "content_session", "content_epoch", "actor_root", "player_key",
    "previous_player_counter", "player_counter", "run_seed", "pre_world", "post_world",
    "contribution", "transcript_digest"]
  pure {
    mission := ← parseMission (← j.getObjVal? "mission")
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    actorRoot := ← objectDigest j "actor_root"
    playerKey := ← objectDigest j "player_key"
    previousPlayerCounter := ← objectNat j "previous_player_counter"
    playerCounter := ← objectNat j "player_counter"
    runSeed := ← objectDigest j "run_seed"
    preWorld := ← parseWorld (← j.getObjVal? "pre_world")
    postWorld := ← parseWorld (← j.getObjVal? "post_world")
    contribution := ← parseContribution (← j.getObjVal? "contribution")
    transcriptDigest := ← objectDigest j "transcript_digest"
  }

private def parseOutputJson (j : Json) : Except String SignalOutputWire := do
  exactKeys j ["format", "receipt", "successor_world", "successor_canon"]
  let format ← j.getObjValAs? String "format"
  if format != OUTPUT_FORMAT then throw "wrong Signal output format"
  pure {
    receipt := ← parseReceipt (← j.getObjVal? "receipt")
    successorWorld := ← parseWorld (← j.getObjVal? "successor_world")
    successorCanon := ← parseCanon (← j.getObjVal? "successor_canon")
  }

def decodeSignalOutputWithLimit (byteLimit : Nat) (bytes : String) : Option SignalOutputWire :=
  if bytes.length ≤ byteLimit then
    canonicalDecode parseOutputJson SignalOutputWire.toJson bytes
  else none


def decodeSignalOutput (bytes : String) : Option SignalOutputWire :=
  decodeSignalOutputWithLimit WIRE_BYTE_LIMIT bytes

theorem decodeSignalOutput_reencodes {bytes : String} {output : SignalOutputWire}
    (accepted : decodeSignalOutput bytes = some output) : output.toJson = bytes :=
  by
    simp only [decodeSignalOutput, decodeSignalOutputWithLimit] at accepted
    split at accepted
    · exact canonicalDecode_reencodes parseOutputJson SignalOutputWire.toJson accepted
    · contradiction

theorem decodeSignalOutput_refuses_oversized (bytes : String)
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeSignalOutput bytes = none := by
  simp [decodeSignalOutput, decodeSignalOutputWithLimit, Nat.not_le.mpr oversized]

theorem decodeSignalOutput_accepted_bytes_injective {left right : String}
    {output : SignalOutputWire} (hl : decodeSignalOutput left = some output)
    (hr : decodeSignalOutput right = some output) : left = right := by
  rw [← decodeSignalOutput_reencodes hl, ← decodeSignalOutput_reencodes hr]

structure SemanticOutput where
  receipt : RunReceipt
  successorWorld : WorldState
  successorCanon : CanonState
  successorWorld_exact : successorWorld = receipt.postWorld
  successorCanonWorld_exact : successorCanon.world = receipt.postWorld

def SignalReceiptWire.toSemantic? (r : SignalReceiptWire) : Option RunReceipt := do
  if r.contentEpoch > WIRE_NAT_LIMIT ∨ r.previousPlayerCounter > WIRE_NAT_LIMIT ∨
      r.playerCounter > WIRE_NAT_LIMIT then none else
  let mission ← r.mission.toSemantic?
  let preWorld ← r.preWorld.toSemantic?
  let postWorld ← r.postWorld.toSemantic?
  let contribution ← r.contribution.toSemantic?
  if federationMatch : r.federationId = mission.federationId then
    if rootMatch : r.contentRoot = mission.contentRoot then
      if activationMatch : r.activationDigest = mission.activationDigest then
        if sessionMatch : r.contentSession = mission.contentSession then
          if epochMatch : (⟨r.contentEpoch⟩ : EpochId) = mission.epoch then
            if seedMatch : r.runSeed = mission.runSeed then
              if counterAdvance : r.playerCounter = r.previousPlayerCounter + 1 then
                match applied : applyContribution mission contribution preWorld with
                | none => none
                | some computed =>
                    if postExact : computed = postWorld then
                      some {
                        mission
                        federationId := r.federationId
                        contentRoot := r.contentRoot
                        activationDigest := r.activationDigest
                        contentSession := r.contentSession
                        contentEpoch := ⟨r.contentEpoch⟩
                        actorRoot := r.actorRoot
                        playerKey := r.playerKey
                        previousPlayerCounter := r.previousPlayerCounter
                        playerCounter := r.playerCounter
                        runSeed := r.runSeed
                        preWorld, postWorld, contribution
                        transcriptDigest := r.transcriptDigest
                        federation_matches := federationMatch
                        content_root_matches := rootMatch
                        activation_matches := activationMatch
                        content_session_matches := sessionMatch
                        content_epoch_matches := epochMatch
                        run_seed_matches := seedMatch
                        player_counter_advances := counterAdvance
                        applied := by simpa [postExact] using applied
                      }
                    else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Parser-only reconstruction of proof-carrying Core shapes.  This checks the
generic contribution/world equations, but it does NOT prove that the output came
from a Signal replay or the preceding Canon state.  Authority consumers must call
`NetworkJudge.verifySignalTransition` with the exact input bytes instead. -/
def SignalOutputWire.toSemantic? (output : SignalOutputWire) : Option SemanticOutput := do
  let receipt ← output.receipt.toSemantic?
  let successorWorld ← output.successorWorld.toSemantic?
  let successorCanon ← output.successorCanon.toSemantic?
  if worldExact : successorWorld = receipt.postWorld then
    if canonWorldExact : successorCanon.world = receipt.postWorld then
      some {
        receipt := receipt
        successorWorld := successorWorld
        successorCanon := successorCanon
        successorWorld_exact := worldExact
        successorCanonWorld_exact := canonWorldExact }
    else none
  else none

/-- Non-authoritative standalone output inspection.  See `toSemantic?`; this is
not a settlement verifier. -/
def decodeSignalOutputSemantic (bytes : String) : Option SemanticOutput := do
  let wire ← decodeSignalOutput bytes
  wire.toSemantic?

/-! ## Total semantic projections used by the Lean judge's success encoder -/

open scoped Prod.Lex

instance : LinearOrder RelicId :=
  LinearOrder.lift' RelicId.value (by
    intro left right equal
    cases left
    cases right
    simp_all)

private abbrev ArtifactOrderKey := Nat ×ₗ (Nat ×ₗ (Digest32 ×ₗ Digest32))

private def artifactOrderKey (a : ArtifactRef) : ArtifactOrderKey :=
  toLex (a.missionId.value,
    toLex (a.artifactId.value, toLex (a.sourceDigest, a.contentDigest)))

instance : LinearOrder ArtifactRef :=
  LinearOrder.lift' artifactOrderKey (by
    intro left right equal
    cases left
    cases right
    case mk.mk missionId₁ artifactId₁ source₁ content₁ missionId₂ artifactId₂ source₂ content₂ =>
      cases missionId₁
      cases artifactId₁
      cases missionId₂
      cases artifactId₂
      simp_all [artifactOrderKey]
    )

private abbrev ReceiptOrderKey :=
  Digest32 ×ₗ (Digest32 ×ₗ (Nat ×ₗ (Digest32 ×ₗ Nat)))

private def receiptOrderKey (r : ReceiptKey) : ReceiptOrderKey :=
  toLex (r.federationId, toLex (r.contentSession,
    toLex (r.contentEpoch.value, toLex (r.playerKey, r.playerCounter))))

instance : LinearOrder ReceiptKey :=
  LinearOrder.lift' receiptOrderKey (by
    intro left right equal
    cases left
    cases right
    case mk.mk federation₁ session₁ epoch₁ player₁ counter₁
        federation₂ session₂ epoch₂ player₂ counter₂ =>
      cases epoch₁
      cases epoch₂
      simp_all [receiptOrderKey])

def ArtifactRefWire.ofSemantic (a : ArtifactRef) : ArtifactRefWire := {
  missionId := a.missionId.value
  artifactId := a.artifactId.value
  sourceDigest := a.sourceDigest
  contentDigest := a.contentDigest
}

def BudgetWire.ofSemantic (b : ContributionBudget) : BudgetWire := {
  intel := b.intel.val
  supplies := b.supplies.val
  cohesion := b.cohesion.val
  influence := b.influence.val
  score := b.score.val
  relics := b.relics.val
}

def MissionWire.ofSemantic (m : MissionSpec) : MissionWire := {
  missionId := m.missionId.value
  artifact := ArtifactRefWire.ofSemantic m.artifact
  epoch := m.epoch.value
  federationId := m.federationId
  contentRoot := m.contentRoot
  activationDigest := m.activationDigest
  contentSession := m.contentSession
  runSeed := m.runSeed
  budget := BudgetWire.ofSemantic m.budget
  allowedRelics := (m.allowedRelics.sort (· ≤ ·)).map RelicId.value
  privacy := m.privacy
  ballot := m.ballot
}

def ContributionWire.ofSemantic (c : Contribution) : ContributionWire := {
  intel := c.intel.val
  supplies := c.supplies.val
  cohesion := c.cohesion.val
  influence := c.influence.val
  score := c.score.val
  relics := (c.relics.sort (· ≤ ·)).map RelicId.value
}

def CodeWire.ofSemantic (c : SignalTriangulation.Code) : CodeWire :=
  { low := c.low.val, mid := c.mid.val, high := c.high.val }

def SignalConfigWire.ofSemantic (c : SignalTriangulation.Config) : SignalConfigWire := {
  target := CodeWire.ofSemantic c.target
  mission := MissionWire.ofSemantic c.mission
  reward := ContributionWire.ofSemantic c.reward
}

def WorldStateWire.ofSemantic (w : WorldState) : WorldStateWire := {
  intel := w.intel.val
  supplies := w.supplies.val
  cohesion := w.cohesion.val
  influence := w.influence.val
  score := w.score.val
  discoveredRelics := (w.discoveredRelics.sort (· ≤ ·)).map RelicId.value
  betaArtifacts := (w.betaArtifacts.sort (· ≤ ·)).map ArtifactRefWire.ofSemantic
  sequence := w.sequence
}

def SignalReceiptWire.ofSemantic (r : RunReceipt) : SignalReceiptWire := {
  mission := MissionWire.ofSemantic r.mission
  federationId := r.federationId
  contentRoot := r.contentRoot
  activationDigest := r.activationDigest
  contentSession := r.contentSession
  contentEpoch := r.contentEpoch.value
  actorRoot := r.actorRoot
  playerKey := r.playerKey
  previousPlayerCounter := r.previousPlayerCounter
  playerCounter := r.playerCounter
  runSeed := r.runSeed
  preWorld := WorldStateWire.ofSemantic r.preWorld
  postWorld := WorldStateWire.ofSemantic r.postWorld
  contribution := ContributionWire.ofSemantic r.contribution
  transcriptDigest := r.transcriptDigest
}

def ReceiptKeyWire.ofSemantic (r : ReceiptKey) : ReceiptKeyWire := {
  federationId := r.federationId
  contentSession := r.contentSession
  contentEpoch := r.contentEpoch.value
  playerKey := r.playerKey
  playerCounter := r.playerCounter
}

def PlayerCounterRowWire.ofSemantic
    (row : PlayerCounterKey × PlayerCounter) : PlayerCounterRowWire := {
  federationId := row.1.federationId
  contentSession := row.1.contentSession
  contentEpoch := row.1.contentEpoch.value
  playerKey := row.1.playerKey
  value := row.2.val
}

/-- Total canonical projection.  `ofSemantic?` below additionally refuses a
state larger than this deliberately bounded network surface. -/
def CanonStateWire.ofSemantic (c : CanonState) : CanonStateWire := {
  federationId := c.federationId
  contentRoot := c.contentRoot
  activationDigest := c.activationDigest
  contentSession := c.contentSession
  contentEpoch := c.contentEpoch.value
  curatorKey := c.curatorKey
  world := WorldStateWire.ofSemantic c.world
  known := (c.known.sort (· ≤ ·)).map ArtifactRefWire.ofSemantic
  alpha := (c.alpha.sort (· ≤ ·)).map ArtifactRefWire.ofSemantic
  superseded := (c.superseded.sort (· ≤ ·)).map ArtifactRefWire.ofSemantic
  consumedRuns := (c.consumedRuns.sort (· ≤ ·)).map ReceiptKeyWire.ofSemantic
  playerCounters := c.playerCounters.rows.map PlayerCounterRowWire.ofSemantic
  revision := c.revision
  curatorCounter := c.curatorCounter
}

def CanonStateWire.ofSemantic? (c : CanonState) : Option CanonStateWire :=
  let wire := CanonStateWire.ofSemantic c
  if canonicalArtifactsB WIRE_ARTIFACT_LIMIT wire.known &&
      canonicalArtifactsB WIRE_ARTIFACT_LIMIT wire.alpha &&
      canonicalArtifactsB WIRE_ARTIFACT_LIMIT wire.superseded &&
      canonicalReceiptsB wire.consumedRuns && canonicalCounterRowsB wire.playerCounters &&
      wire.contentEpoch ≤ WIRE_NAT_LIMIT && wire.revision ≤ WIRE_NAT_LIMIT &&
      wire.curatorCounter ≤ WIRE_NAT_LIMIT then some wire else none

/-- The explicit replay population fails closed at its per-epoch transport
capacity.  Epoch rollover or an authenticated accumulator is required to regain
liveness; the encoder never truncates replay history. -/
theorem CanonStateWire.ofSemantic_refuses_receipt_capacity (c : CanonState)
    (over : WIRE_RECEIPT_LIMIT < c.consumedRuns.card) :
    CanonStateWire.ofSemantic? c = none := by
  simp [CanonStateWire.ofSemantic?, CanonStateWire.ofSemantic,
    canonicalReceiptsB, Nat.not_le.mpr over]

theorem CanonStateWire.ofSemantic_refuses_player_capacity (c : CanonState)
    (over : WIRE_COUNTER_LIMIT < c.playerCounters.rows.length) :
    CanonStateWire.ofSemantic? c = none := by
  simp [CanonStateWire.ofSemantic?, CanonStateWire.ofSemantic,
    canonicalCounterRowsB, Nat.not_le.mpr over]

/-! ## Emitted Signal fixture -/

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

private def digestOrZero (hex : String) : Digest32 :=
  (Emit.parseBytes32Hex? hex).getD zeroDigest

abbrev FIXTURE_FEDERATION_HEX : String :=
  "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a"
abbrev FIXTURE_SOURCE_HEX : String :=
  "b2af50349f2fc4c14db2e3bdb7f9f03aa1dd59862c079d494e69c853f73b8895"
abbrev FIXTURE_CONTENT_HEX : String :=
  "c3a9603f84f1e5918c6a46f30c507a39b6c9d5fd57c9f3edec3b03597eec49bf"
abbrev FIXTURE_CONTENT_ROOT_HEX : String :=
  "679706a06ae8546a96b369a70dd7c5ee1c93fe47c789368087ab167c7b7dcebc"
abbrev FIXTURE_ACTIVATION_HEX : String :=
  "0101010101010101010101010101010101010101010101010101010101010101"
abbrev FIXTURE_ACTOR_HEX : String :=
  "4444444444444444444444444444444444444444444444444444444444444444"
abbrev FIXTURE_PLAYER_HEX : String :=
  "5555555555555555555555555555555555555555555555555555555555555555"
abbrev FIXTURE_CURATOR_HEX : String :=
  "6666666666666666666666666666666666666666666666666666666666666666"
/-- A DEMONSTRATION slot secret.  It is a fixture value and is not a deployment
secret: a deployment secret never enters this module, and there is no function here
that would render one into an artifact. -/
abbrev FIXTURE_SLOT_SECRET_HEX : String :=
  "7777777777777777777777777777777777777777777777777777777777777777"

def fixtureFederationId : Digest32 := digestOrZero FIXTURE_FEDERATION_HEX
def fixtureSourceDigest : Digest32 := digestOrZero FIXTURE_SOURCE_HEX
def fixtureContentDigest : Digest32 := digestOrZero FIXTURE_CONTENT_HEX
def fixtureContentRoot : Digest32 := digestOrZero FIXTURE_CONTENT_ROOT_HEX
def fixtureActivationDigest : Digest32 := digestOrZero FIXTURE_ACTIVATION_HEX
def fixtureActorRoot : Digest32 := digestOrZero FIXTURE_ACTOR_HEX
def fixturePlayerKey : Digest32 := digestOrZero FIXTURE_PLAYER_HEX
def fixtureCuratorKey : Digest32 := digestOrZero FIXTURE_CURATOR_HEX

def fixtureSlotSecret : HiddenInstance.SlotSecret := ⟨digestOrZero FIXTURE_SLOT_SECRET_HEX⟩
def fixtureSlot : EpochId := ⟨9⟩

/-- The published per-slot commitment, computed — not asserted.  `admissionChecks`
requires `active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot`,
so a fixture that stated a commitment by hand would simply be refused. -/
def fixtureSlotCommitment : Digest32 := HiddenInstance.commit fixtureSlotSecret fixtureSlot

/-- The draw context of the Signal mission, taken off the TEMPLATE mission — the one
whose run seed is `Emit.UNBOUND_RUN_SEED` — so that the seed below does not depend on
itself.  `HiddenInstance.context_ignores_the_run_seed` is why that is the same context
the live mission carries, and `fixtureMissionContext_is_the_live_context` checks it on
this exact fixture rather than trusting the general lemma to have been applied. -/
def fixtureMissionContext : HiddenInstance.MissionContext :=
  HiddenInstance.MissionContext.ofMission
    (Emit.signalMission Emit.UNBOUND_RUN_SEED fixtureFederationId fixtureSourceDigest
      fixtureContentDigest fixtureContentRoot fixtureActivationDigest)

/-- ⚠ The fixture's LIVE run seed is now DERIVED, not a stand-in constant.  It has to
be: `Judged.admissionChecks` refuses any active state whose run seed is not exactly
`HiddenInstance.runSeedFor` of the committed slot secret, this slot and this player, so
a hand-picked seed would make every fixture below refuse rather than settle.  A client
never sees this value; the fixture computes it because it is playing the node's part. -/
def fixtureRunSeed : Digest32 :=
  HiddenInstance.runSeedFor ⟨fixtureSlotSecret, fixtureSlot, fixturePlayerKey⟩
    fixtureMissionContext

def fixtureConfig : SignalTriangulation.Config :=
  Emit.signalConfig fixtureRunSeed fixtureFederationId fixtureSourceDigest
    fixtureContentDigest fixtureContentRoot fixtureActivationDigest

/-- The context the seed was drawn against is the context the LIVE mission carries, so
the derivation above is not a cycle dressed up.  It is an instance of
`Emit.signalMission_context_ignores_the_run_seed`, which is the general fact; stating
it here pins that the fixture actually applied it. -/
theorem fixtureMissionContext_is_the_live_context :
    HiddenInstance.MissionContext.ofMission fixtureConfig.mission = fixtureMissionContext :=
  Emit.signalMission_context_ignores_the_run_seed _ _ _ _ _ _ _

def fixtureCanon : CanonState :=
  CanonState.empty fixtureFederationId fixtureContentRoot fixtureActivationDigest
    fixtureConfig.mission.contentSession fixtureConfig.mission.epoch fixtureCuratorKey

def fixtureCarrier : FinalizedCarrier where
  federationId := fixtureFederationId
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivationDigest
  contentSession := fixtureConfig.mission.contentSession
  contentEpoch := fixtureConfig.mission.epoch
  actorRoot := fixtureActorRoot
  playerKey := fixturePlayerKey
  currentPlayerCounter := 0

def fixtureRequestWire : SignalRequestWire where
  missionId := fixtureConfig.mission.missionId.value
  federationId := fixtureFederationId
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivationDigest
  contentSession := fixtureConfig.mission.contentSession
  contentEpoch := fixtureConfig.mission.epoch.value
  slot := fixtureSlot.value
  slotCommitment := fixtureSlotCommitment
  actorRoot := fixtureActorRoot
  playerKey := fixturePlayerKey
  previousPlayerCounter := 0
  expectedWorldSequence := 0
  expectedCanonRevision := 0
  actions := [CodeWire.ofSemantic fixtureConfig.target]

def fixtureSlotStateWire : SlotStateWire where
  slot := fixtureSlot.value
  secret := fixtureSlotSecret.value
  commitment := fixtureSlotCommitment

def fixtureInput : SemanticInput where
  config := fixtureConfig
  world := WorldState.empty
  canon := fixtureCanon
  carrier := fixtureCarrier
  slot := fixtureSlot
  slotSecret := fixtureSlotSecret
  slotCommitment := fixtureSlotCommitment
  request := fixtureRequestWire

def fixtureInputWire : SignalInputWire where
  config := SignalConfigWire.ofSemantic fixtureConfig
  world := WorldStateWire.ofSemantic WorldState.empty
  canon := CanonStateWire.ofSemantic fixtureCanon
  carrier := {
    federationId := fixtureCarrier.federationId
    contentRoot := fixtureCarrier.contentRoot
    activationDigest := fixtureCarrier.activationDigest
    contentSession := fixtureCarrier.contentSession
    contentEpoch := fixtureCarrier.contentEpoch.value
    actorRoot := fixtureCarrier.actorRoot
    playerKey := fixtureCarrier.playerKey
    currentPlayerCounter := fixtureCarrier.currentPlayerCounter.val
  }
  slotState := fixtureSlotStateWire
  request := fixtureRequestWire

def fixtureInputBytes : String := fixtureInputWire.toJson

def fixturePostWorldWire : WorldStateWire where
  intel := 25
  supplies := 15
  cohesion := 10
  influence := 5
  score := 500
  discoveredRelics := [1]
  betaArtifacts := [fixtureInputWire.config.mission.artifact]
  sequence := 1

def fixtureSuccessorCanonWire : CanonStateWire where
  federationId := fixtureFederationId
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivationDigest
  contentSession := fixtureConfig.mission.contentSession
  contentEpoch := fixtureConfig.mission.epoch.value
  curatorKey := fixtureCuratorKey
  world := fixturePostWorldWire
  known := [fixtureInputWire.config.mission.artifact]
  alpha := []
  superseded := []
  consumedRuns := [{
    federationId := fixtureFederationId
    contentSession := fixtureConfig.mission.contentSession
    contentEpoch := fixtureConfig.mission.epoch.value
    playerKey := fixturePlayerKey
    playerCounter := 1
  }]
  playerCounters := [{
    federationId := fixtureFederationId
    contentSession := fixtureConfig.mission.contentSession
    contentEpoch := fixtureConfig.mission.epoch.value
    playerKey := fixturePlayerKey
    value := 1
  }]
  revision := 1
  curatorCounter := 0

def fixtureReceiptWire : SignalReceiptWire where
  mission := fixtureInputWire.config.mission
  federationId := fixtureFederationId
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivationDigest
  contentSession := fixtureConfig.mission.contentSession
  contentEpoch := fixtureConfig.mission.epoch.value
  actorRoot := fixtureActorRoot
  playerKey := fixturePlayerKey
  previousPlayerCounter := 0
  playerCounter := 1
  runSeed := fixtureConfig.mission.runSeed
  preWorld := fixtureInputWire.world
  postWorld := fixturePostWorldWire
  contribution := fixtureInputWire.config.reward
  transcriptDigest := SignalTriangulation.transcriptDigest [.submit fixtureConfig.target]

def fixtureOutputWire : SignalOutputWire where
  receipt := fixtureReceiptWire
  successorWorld := fixturePostWorldWire
  successorCanon := fixtureSuccessorCanonWire

def fixtureOutputBytes : String := fixtureOutputWire.toJson

theorem fixture_input_roundtrip :
    decodeSignalInput fixtureInputBytes = some fixtureInputWire := by
  native_decide

theorem fixture_input_refuses_tight_byte_cap :
    decodeSignalInputWithLimit (fixtureInputBytes.length - 1) fixtureInputBytes = none := by
  native_decide

theorem fixture_input_semantic_inhabited :
    fixtureInputWire.toSemantic?.isSome = true := by
  native_decide

theorem fixture_input_refuses_trailing_bytes :
    decodeSignalInput (fixtureInputBytes ++ "\n") = none := by
  native_decide

theorem fixture_input_refuses_uppercase_digest :
    decodeSignalInput
      (fixtureInputBytes.replace FIXTURE_FEDERATION_HEX (String.toUpper FIXTURE_FEDERATION_HEX)) = none := by
  native_decide

def oversizedActionsInput : SignalInputWire :=
  { fixtureInputWire with request := {
      fixtureInputWire.request with actions := List.replicate (WIRE_ACTION_LIMIT + 1) { low := 0, mid := 0, high := 0 }
    } }

theorem fixture_input_refuses_oversized_actions :
    decodeSignalInput oversizedActionsInput.toJson = none := by
  native_decide

def duplicateKnownInput : SignalInputWire :=
  { fixtureInputWire with canon := {
      fixtureInputWire.canon with
      known := [fixtureInputWire.config.mission.artifact, fixtureInputWire.config.mission.artifact]
    } }

theorem fixture_input_refuses_duplicate_canon_rows :
    decodeSignalInput duplicateKnownInput.toJson = none := by
  native_decide

def mismatchedWorldInput : SignalInputWire :=
  { fixtureInputWire with world := { fixtureInputWire.world with sequence := 1 } }

theorem fixture_semantics_refuses_world_canon_mismatch :
    mismatchedWorldInput.toSemantic?.isSome = false := by
  native_decide

def oversizedCarrierInput : SignalInputWire :=
  { fixtureInputWire with carrier := {
      fixtureInputWire.carrier with currentPlayerCounter := WIRE_NAT_LIMIT + 1
    } }

theorem fixture_input_refuses_oversized_carrier_counter :
    decodeSignalInput oversizedCarrierInput.toJson = none := by
  native_decide

theorem fixture_output_roundtrip :
    decodeSignalOutput fixtureOutputBytes = some fixtureOutputWire := by
  native_decide

theorem fixture_output_refuses_tight_byte_cap :
    decodeSignalOutputWithLimit (fixtureOutputBytes.length - 1) fixtureOutputBytes = none := by
  native_decide

theorem fixture_output_semantic_inhabited :
    fixtureOutputWire.toSemantic?.isSome = true := by
  native_decide

theorem fixture_output_refuses_trailing_bytes :
    decodeSignalOutput (fixtureOutputBytes ++ "\n") = none := by
  native_decide

#assert_axioms fixtureMissionContext_is_the_live_context
#assert_axioms canonicalDecode_reencodes
#assert_axioms decodeSignalInput_reencodes
#assert_axioms decodeSignalInput_accepted_bytes_injective
#assert_axioms decodeSignalInput_refuses_oversized
#assert_axioms decodeSignalOutput_reencodes
#assert_axioms decodeSignalOutput_accepted_bytes_injective
#assert_axioms decodeSignalOutput_refuses_oversized
#assert_axioms CanonStateWire.ofSemantic_refuses_receipt_capacity
#assert_axioms CanonStateWire.ofSemantic_refuses_player_capacity
#assert_axioms decodeCanonState_reencodes
#assert_axioms decodeSignalConfig_reencodes
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_input_refuses_tight_byte_cap
#assert_compiled fixture_input_semantic_inhabited
#assert_compiled fixture_input_refuses_trailing_bytes
#assert_compiled fixture_input_refuses_uppercase_digest
#assert_compiled fixture_input_refuses_oversized_actions
#assert_compiled fixture_input_refuses_duplicate_canon_rows
#assert_compiled fixture_semantics_refuses_world_canon_mismatch
#assert_compiled fixture_input_refuses_oversized_carrier_counter
#assert_compiled fixture_output_roundtrip
#assert_compiled fixture_output_refuses_tight_byte_cap
#assert_compiled fixture_output_semantic_inhabited
#assert_compiled fixture_output_refuses_trailing_bytes

end Dregg2.Games.PathOfAngels.NetworkJudgeWire
