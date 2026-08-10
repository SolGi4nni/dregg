/-
# RecordsRuntime — the Lean-authored read model behind the PoA Records surface

A player who finishes a Path of Angels run needs somewhere for that run to
*land*.  `FinalizedRunEventAggregate` already says what landing means: one
finalized turn, re-judged from its exact stored bytes, projected into Canon, the
Field Archive, a personal locker, an Attendant notice and an Editorial inbox
item.  Nothing exported that projection, so no reader could see it, and any host
that wanted to would have had to rebuild it in Rust.  This module is that
export.

The boundary is deliberately shaped so the host contributes **no semantics**:

* the host supplies the exact persisted config and Canon bytes of the retained
  genesis head, and, for every durable transition, its finalized coordinate plus
  the exact stored judge input/output bytes;
* Lean re-decodes both genesis blobs under `NetworkJudgeWire`'s canonical seal,
  re-runs the native Signal judge over every row through
  `FinalizedRunEventAggregate.checkPayload?`, and folds the one shared `reduce`,
  so the Canon chain is rebuilt here rather than trusted from storage;
* every published field is a projection of that fold.

Three properties of the surface are worth stating plainly.

**It shows the world before it shows any run.**  With zero rows the view is not
an empty list: it is the exact world identity, world meters, Canon revision and
playable mission a run would write into, decoded from the bytes the genesis
ceremony actually installed.  A node at height 0 has something true to display.

**It never publishes the answer, and the previous spelling of this paragraph was
wrong.**  It used to say that omitting `SignalConfigWire.target` was enough.  It
is not, and the fixture in this very file proved it: `ViewWire.mission` was a
full `MissionWire`, `MissionWire` carries `runSeed`, and
`SignalTriangulation.targetFromSeed?` is a public function — a rejection-sampled
draw from a published seed to the code.  A surface that omits `target` and
publishes `runSeed` has published the target.

Two things close it, and the second exists because the first is one edit away
from being undone:

* the published mission is `PublicMissionWire`, which has **no** `runSeed` field.
  `publicMission_ignores_the_run_seed` says that substituting *any* seed leaves
  the published value unchanged, so this is a theorem about the projection and
  not a promise about a filter;
* `project?` additionally **refuses** a config whose seed is not
  `Emit.UNBOUND_RUN_SEED`.  A retained genesis config is a mission TEMPLATE and
  carries the all-zero sentinel; a live seed appearing there means something
  upstream is wrong, and this read refuses rather than rendering it.

**It publishes nothing derived from the transcript, in any form.**
`RunWire.transcriptDigest` is gone.  `SignalTriangulation.transcriptDigest` is
**not a digest** — it is a fixed-width plaintext encoding, byte 0 the action
count and bytes 1..15 the submitted bands, so for a solved run its tail *is* the
target.  ⚠ And hashing it would be theatre, not a fix: an accepted transcript is
at most five guesses from 216, a space of about `2^39`, which brute-force
inverts on a laptop.  There is no safe encoding of a run's guesses on a public
route, so there is no such field.  What a player did is theirs; what they *won*
is the record.

**Coordinates come from the checked payload, not from a re-decoded carrier.**
`CheckedPayload` already proves the finalized `actorRoot`/`signer` equal the
settlement carrier fields, so the published values are both at once
(`runWireOf_coordinate_agrees_with_the_settlement_carrier`).  The host must
still supply those two from the finalized `SignedTurn` and durable receipt; when
it does, a substitution refuses here exactly as
`FinalizedRunEventAggregate.hostile_finalized_signer_substitution_refused`
requires.

Named deployment boundaries, unchanged by this module: that the coordinates came
from the real generic `CommitRecord`, the durable CAS, and collision resistance
of the persistence digests.  `MAX_ROWS` is a hard fuse, not pagination — a world
with more finalized runs than that refuses here and needs a windowed request
before it can be read again.  Each accepted row costs two native judge
invocations (`checkPayload?` for the record, `reduce` for the fold).
-/
import Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.RecordsRuntime

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

set_option autoImplicit false

abbrev RECORDS_INPUT_FORMAT : String := "POA-RECORDS-IN-1"

/-- ⚑ Bumped to `-2` when the published mission lost `runSeed`, the run record
lost `transcriptDigest`, and the chain coordinate moved under `chain`.  The
request shape did not change, so `RECORDS_INPUT_FORMAT` stays at `-1`.

A reader pinned to `POA-RECORDS-OUT-1` now fails its own format check instead of
silently finding two fields missing and a third moved.  That is the point of the
bump: the old shape must refuse to load rather than be reinterpreted. -/
abbrev RECORDS_OUTPUT_FORMAT : String := "POA-RECORDS-OUT-2"

abbrev RECORDS_U64_MAX : Nat := 2 ^ 64 - 1
/-- Outer allocation fuse, checked before the JSON parser runs. -/
abbrev RECORDS_BYTE_LIMIT : Nat := 64 * 1024 * 1024
/-- Per-component ceiling for one embedded exact byte blob. -/
abbrev MAX_COMPONENT_BYTES : Nat := 1024 * 1024
/-- The read fuse.  Above this the surface refuses rather than truncating a
history: a silently shortened Records view would be a false record. -/
abbrev MAX_ROWS : Nat := 256

/-! ## Exact-byte components

Embedded blobs travel as lowercase hexadecimal of their UTF-8 bytes.  A JSON
string would make acceptance depend on two independent escaping conventions
agreeing; hex has one spelling, and a disagreement would fail closed and
silently, which is the failure mode this transport exists to avoid. -/

private def jsonString (value : String) : String := String.quote value

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def byteHex (value : Nat) : String :=
  String.ofList [lowerHexDigit (value / 16), lowerHexDigit (value % 16)]

private def bytesHex (values : List Nat) : String := String.join (values.map byteHex)

private def hexNibble? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

/-- Accumulator-passing so a megabyte-scale blob does not build a recursion the
depth of its own byte count. -/
private def parseHexBytesAux : List Char → List Nat → Option (List Nat)
  | [], acc => some acc.reverse
  | hi :: lo :: rest, acc => do
      let h ← hexNibble? hi
      let l ← hexNibble? lo
      parseHexBytesAux rest ((16 * h + l) :: acc)
  | _, _ => none

private def parseHexBytes? (chars : List Char) : Option (List Nat) :=
  parseHexBytesAux chars []

/-- An exact persisted blob.  The wire spelling is hexadecimal; the semantic
value is the UTF-8 text the host stored. -/
structure OpaqueUtf8 where
  text : String
deriving DecidableEq

def OpaqueUtf8.toHex (value : OpaqueUtf8) : String :=
  bytesHex (value.text.toUTF8.toList.map UInt8.toNat)

/-! ## Request -/

structure RowWire where
  commitOrdinal : Nat
  turnHash : Digest32
  receiptHash : Digest32
  actorRoot : Digest32
  signer : Digest32
  judgeInput : OpaqueUtf8
  judgeOutput : OpaqueUtf8
deriving DecidableEq

/-- `genesisCanon`/`config` are the exact bytes the genesis ceremony installed,
never a re-encoding of a host struct.  `federationId` is the authority the node
claims to be serving; it must equal the one inside those bytes. -/
structure RequestWire where
  federationId : Digest32
  genesisCanon : OpaqueUtf8
  config : OpaqueUtf8
  rows : List RowWire
deriving DecidableEq

def RowWire.toJson (row : RowWire) : String :=
  "{\"commit_ordinal\":" ++ toString row.commitOrdinal ++
    ",\"turn_hash\":" ++ jsonString (Emit.bytes32Hex row.turnHash) ++
    ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex row.receiptHash) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex row.actorRoot) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex row.signer) ++
    ",\"judge_input\":" ++ jsonString row.judgeInput.toHex ++
    ",\"judge_output\":" ++ jsonString row.judgeOutput.toHex ++ "}"

def RequestWire.toJson (request : RequestWire) : String :=
  "{\"format\":" ++ jsonString RECORDS_INPUT_FORMAT ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex request.federationId) ++
    ",\"genesis_canon\":" ++ jsonString request.genesisCanon.toHex ++
    ",\"config\":" ++ jsonString request.config.toHex ++
    ",\"rows\":" ++ jsonArray (request.rows.map RowWire.toJson) ++ "}"

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def boundedNat (limit value : Nat) : Except String Nat :=
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def objectNat (j : Json) (key : String) (limit : Nat := RECORDS_U64_MAX) :
    Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def objectOpaque (j : Json) (key : String) : Except String OpaqueUtf8 := do
  let spelling ← j.getObjValAs? String key
  if spelling.length > 2 * MAX_COMPONENT_BYTES then throw "component exceeds wire bound"
  let bytes ← match parseHexBytes? spelling.toList with
    | some bytes => pure bytes
    | none => throw "component must be lowercase even-length hexadecimal"
  let array : ByteArray := ⟨(bytes.map (fun value => UInt8.ofNat value)).toArray⟩
  match String.fromUTF8? array with
  | none => throw "component is not UTF-8"
  | some text =>
      let value : OpaqueUtf8 := ⟨text⟩
      if value.toHex = spelling then pure value else throw "component is not canonical"

private def parseRow (j : Json) : Except String RowWire := do
  exactKeys j ["commit_ordinal", "turn_hash", "receipt_hash", "actor_root", "signer",
    "judge_input", "judge_output"]
  pure {
    commitOrdinal := ← objectNat j "commit_ordinal"
    turnHash := ← objectDigest j "turn_hash"
    receiptHash := ← objectDigest j "receipt_hash"
    actorRoot := ← objectDigest j "actor_root"
    signer := ← objectDigest j "signer"
    judgeInput := ← objectOpaque j "judge_input"
    judgeOutput := ← objectOpaque j "judge_output"
  }

private def parseRequestJson (j : Json) : Except String RequestWire := do
  exactKeys j ["format", "federation_id", "genesis_canon", "config", "rows"]
  let format ← j.getObjValAs? String "format"
  if format != RECORDS_INPUT_FORMAT then throw "wrong Records input format"
  let values := (← (← j.getObjVal? "rows").getArr?).toList
  if values.length > MAX_ROWS then throw "rows exceed the read fuse"
  pure {
    federationId := ← objectDigest j "federation_id"
    genesisCanon := ← objectOpaque j "genesis_canon"
    config := ← objectOpaque j "config"
    rows := ← values.mapM parseRow
  }

/-- The same canonicality seal the Signal wire uses, and literally the same
function: parse, then require Lean's own encoder to reproduce the bytes. -/
def decodeRequestWithLimit (byteLimit : Nat) (bytes : String) : Option RequestWire :=
  if bytes.length ≤ byteLimit then
    NetworkJudgeWire.canonicalDecode parseRequestJson RequestWire.toJson bytes
  else none

def decodeRequest (bytes : String) : Option RequestWire :=
  decodeRequestWithLimit RECORDS_BYTE_LIMIT bytes

theorem decodeRequest_reencodes {bytes : String} {request : RequestWire}
    (accepted : decodeRequest bytes = some request) : request.toJson = bytes := by
  simp only [decodeRequest, decodeRequestWithLimit] at accepted
  split at accepted
  · exact NetworkJudgeWire.canonicalDecode_reencodes parseRequestJson RequestWire.toJson accepted
  · contradiction

theorem decodeRequest_refuses_oversized (bytes : String)
    (oversized : RECORDS_BYTE_LIMIT < bytes.length) : decodeRequest bytes = none := by
  simp [decodeRequest, decodeRequestWithLimit, Nat.not_le.mpr oversized]

/-! ## View -/

private def statusTag : CanonStatus → String
  | .beta => "beta"
  | .alpha => "alpha"
  | .superseded => "superseded"

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

/-- Canon lifecycle is recomputed from the rebuilt Canon at read time; no status
label is ever carried in from storage. -/
structure ArtifactStatusWire where
  artifact : ArtifactRefWire
  status : String
deriving DecidableEq

/-! ## The visible ladder

A run can be in five places, and a reader must never have to guess which.  The
rungs are named on the wire because the alternative — an unlabelled list — is
how a local rehearsal comes to look like a settled record. -/

/-- Where a run stands.  ⚑ Only `finalized` means *this chain committed it*.

* `practice` — an instance the client drew for ITSELF through
  `HiddenInstance.practiceRunSeed`.  It is a real instance of the same family and
  a genuinely useful rehearsal, and it is scored by nobody:
  `HiddenInstance.practice_is_not_judged` is the refutation, because the purpose
  tag is inside the sponge preimage.
* `submitted` — a claim the node accepted for evaluation.  No verdict exists.
* `judged` — native Lean accepted it, and that is still not finality;
  `poa_signal_adapter` says so in its own words: an evaluated candidate is never
  a finalized receipt.
* `finalized` — re-judged from the exact durable bytes and folded into Canon.
  This is the only rung this surface emits.
* `refused` — the judge said no.  A refusal is a result, not an absence. -/
inductive RunStatus where
  | practice
  | submitted
  | judged
  | finalized
  | refused
deriving DecidableEq, Repr

def RunStatus.tag : RunStatus → String
  | .practice => "practice"
  | .submitted => "submitted"
  | .judged => "judged"
  | .finalized => "finalized"
  | .refused => "refused"

/-- The rungs are distinguishable on the wire: no two spell the same tag, so a
reader that switches on the string is switching on the rung. -/
theorem RunStatus.tag_injective {left right : RunStatus} (h : left.tag = right.tag) :
    left = right := by
  cases left <;> cases right <;> simp_all [RunStatus.tag]

/-- Where a run sits on THIS chain.  Its presence is what a settled record has and
nothing else may have. -/
structure ChainCoordinate where
  commitOrdinal : Nat
  turnHash : Digest32
  receiptHash : Digest32
  signer : Digest32
  actorRoot : Digest32
deriving DecidableEq

/-- One run, at whatever rung it stands on.

⚑ There is no transcript field, hashed or otherwise — see the header.  What is
published is who settled it, when, and which artifact it discovered. -/
structure RunWire where
  status : RunStatus
  coordinate : Option ChainCoordinate
  originKey : ReceiptKeyWire
  artifact : ArtifactRefWire
  contribution : ContributionWire
  worldSequence : Nat
deriving DecidableEq

/-- A record is coherent when its rung and its chain coordinate agree.  A
coordinate is exactly the evidence `finalized` claims, so anything else carrying
one is malformed and anything `finalized` without one is too. -/
def RunWire.coherentB (run : RunWire) : Bool :=
  match run.status, run.coordinate with
  | .finalized, some _ => true
  | .finalized, none => false
  | _, some _ => false
  | _, none => true

/-- ⚑ **A chain coordinate is the exclusive property of a settled record.**  This
is the statement that a practice entry cannot dress itself as one: not because a
renderer is careful, but because a coherent record with a coordinate is
`finalized` and there is no other case. -/
theorem only_finalized_carries_a_coordinate {run : RunWire}
    (coherent : run.coherentB = true) (settled : run.coordinate.isSome = true) :
    run.status = .finalized := by
  unfold RunWire.coherentB at coherent
  cases hstatus : run.status <;> cases hcoord : run.coordinate <;>
    simp_all

/-- And the converse: an unsettled rung has no coordinate at all. -/
theorem unsettled_has_no_coordinate {run : RunWire}
    (coherent : run.coherentB = true) (unsettled : run.status ≠ .finalized) :
    run.coordinate = none := by
  unfold RunWire.coherentB at coherent
  cases hstatus : run.status <;> cases hcoord : run.coordinate <;>
    simp_all

/-- The mission as a READER may see it.

⚑ It has no `runSeed` field, and that absence is the security property.  A live
`MissionSpec.runSeed` determines the Signal target through the public total
function `SignalTriangulation.targetFromSeed?`, so publishing the seed publishes
the answer.  `MissionWire` carries one; this does not. -/
structure PublicMissionWire where
  missionId : Nat
  artifact : ArtifactRefWire
  epoch : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  budget : BudgetWire
  allowedRelics : List Nat
  privacy : PrivacyGrade
  ballot : BallotRegime
deriving DecidableEq

def PublicMissionWire.ofMission (m : MissionWire) : PublicMissionWire where
  missionId := m.missionId
  artifact := m.artifact
  epoch := m.epoch
  federationId := m.federationId
  contentRoot := m.contentRoot
  activationDigest := m.activationDigest
  contentSession := m.contentSession
  budget := m.budget
  allowedRelics := m.allowedRelics
  privacy := m.privacy
  ballot := m.ballot

/-- ⚑ **The published mission does not depend on the run seed.**  Substituting an
arbitrary seed — the live one, the sentinel, an attacker's — leaves every
published field identical.  This is the field-by-field answer to "can a reader
reconstruct the instance from the mission": no, because the projection cannot
see the seed at all. -/
theorem publicMission_ignores_the_run_seed (m : MissionWire) (seed : Digest32) :
    PublicMissionWire.ofMission { m with runSeed := seed } =
      PublicMissionWire.ofMission m := rfl

/-- The four values a browser needs to draw a PRACTICE instance for itself are
exactly `missionId`, `epoch`, `federationId` and `contentSession` — which is
`HiddenInstance.MissionContext`, the projection that deliberately excludes the
run seed.  They are already published above, so there is no second shape here:
this theorem records that the public mission carries the practice context, and
that the context is seed-independent, without minting a duplicate wire record. -/
theorem public_mission_carries_the_practice_context (m : MissionWire) (seed : Digest32) :
    ((PublicMissionWire.ofMission { m with runSeed := seed }).missionId,
        (PublicMissionWire.ofMission { m with runSeed := seed }).epoch,
        (PublicMissionWire.ofMission { m with runSeed := seed }).federationId,
        (PublicMissionWire.ofMission { m with runSeed := seed }).contentSession) =
      ((PublicMissionWire.ofMission m).missionId, (PublicMissionWire.ofMission m).epoch,
        (PublicMissionWire.ofMission m).federationId,
        (PublicMissionWire.ofMission m).contentSession) := rfl

/-- Whether this world has ever had a run land.  Derived from the rebuilt rows,
so it cannot disagree with them. -/
inductive WorldStage where
  | awaitingFirstRun
  | active
deriving DecidableEq, Repr

def WorldStage.tag : WorldStage → String
  | .awaitingFirstRun => "awaiting-first-run"
  | .active => "active"

def stageOf : List RunWire → WorldStage
  | [] => .awaitingFirstRun
  | _ :: _ => .active

/-- The stage is a reading of the rows and not an independent claim: it says
"awaiting the first run" exactly when there is no run. -/
theorem stageOf_awaiting_iff_no_runs (runs : List RunWire) :
    stageOf runs = .awaitingFirstRun ↔ runs = [] := by
  cases runs <;> simp [stageOf]

/-- ⚑ There is deliberately no `target` field AND no `runSeed` field: this surface
publishes neither the Signal answer nor anything a reader can compute it from. -/
structure ViewWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  curatorKey : Digest32
  stage : WorldStage
  mission : PublicMissionWire
  reward : ContributionWire
  world : WorldStateWire
  canonRevision : Nat
  catalog : List ArtifactStatusWire
  runs : List RunWire
  archiveEntries : Nat
  lockerEntries : Nat
  attendantNotices : Nat
  editorialInbox : Nat
  consumedRuns : Nat
  players : Nat
deriving DecidableEq

def ArtifactStatusWire.toJson (entry : ArtifactStatusWire) : String :=
  "{\"artifact\":" ++ entry.artifact.toJson ++
    ",\"status\":" ++ jsonString entry.status ++ "}"

def ChainCoordinate.toJson (c : ChainCoordinate) : String :=
  "{\"commit_ordinal\":" ++ toString c.commitOrdinal ++
    ",\"turn_hash\":" ++ jsonString (Emit.bytes32Hex c.turnHash) ++
    ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex c.receiptHash) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex c.signer) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex c.actorRoot) ++ "}"

/-- `chain` is `null` on every rung but `finalized`, which is the wire image of
`only_finalized_carries_a_coordinate`. -/
def RunWire.toJson (run : RunWire) : String :=
  "{\"status\":" ++ jsonString run.status.tag ++
    ",\"chain\":" ++ (match run.coordinate with
      | none => "null"
      | some coordinate => coordinate.toJson) ++
    ",\"origin_key\":" ++ run.originKey.toJson ++
    ",\"artifact\":" ++ run.artifact.toJson ++
    ",\"contribution\":" ++ run.contribution.toJson ++
    ",\"world_sequence\":" ++ toString run.worldSequence ++ "}"

def PublicMissionWire.toJson (m : PublicMissionWire) : String :=
  "{\"mission_id\":" ++ toString m.missionId ++
    ",\"artifact\":" ++ m.artifact.toJson ++
    ",\"epoch\":" ++ toString m.epoch ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex m.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex m.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex m.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex m.contentSession) ++
    ",\"budget\":" ++ m.budget.toJson ++
    ",\"allowed_relics\":" ++ jsonArray (m.allowedRelics.map toString) ++
    ",\"privacy\":" ++ jsonString (privacyTag m.privacy) ++
    ",\"ballot\":" ++ jsonString (ballotTag m.ballot) ++ "}"

def ViewWire.toJson (view : ViewWire) : String :=
  "{\"format\":" ++ jsonString RECORDS_OUTPUT_FORMAT ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex view.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex view.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex view.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex view.contentSession) ++
    ",\"content_epoch\":" ++ toString view.contentEpoch ++
    ",\"curator_key\":" ++ jsonString (Emit.bytes32Hex view.curatorKey) ++
    ",\"stage\":" ++ jsonString view.stage.tag ++
    ",\"mission\":" ++ view.mission.toJson ++
    ",\"reward\":" ++ view.reward.toJson ++
    ",\"world\":" ++ view.world.toJson ++
    ",\"canon_revision\":" ++ toString view.canonRevision ++
    ",\"catalog\":" ++ jsonArray (view.catalog.map ArtifactStatusWire.toJson) ++
    ",\"runs\":" ++ jsonArray (view.runs.map RunWire.toJson) ++
    ",\"archive_entries\":" ++ toString view.archiveEntries ++
    ",\"locker_entries\":" ++ toString view.lockerEntries ++
    ",\"attendant_notices\":" ++ toString view.attendantNotices ++
    ",\"editorial_inbox\":" ++ toString view.editorialInbox ++
    ",\"consumed_runs\":" ++ toString view.consumedRuns ++
    ",\"players\":" ++ toString view.players ++ "}"

/-! ## The fold -/

structure Accumulated where
  projection : Projection
  runs : List RunWire

/-- Every published field of a run record is read off the checked payload: the
coordinate from the exact bytes the host committed to, the provenance from the
Field Archive projection of the re-judged receipt. -/
def runWireOf (checked : CheckedPayload) : RunWire :=
  let run := checked.settlement.judgedRun
  let entry := FieldArchive.ArchiveEntry.ofJudged run
  { status := .finalized
    coordinate := some
      { commitOrdinal := checked.raw.finalized.commitOrdinal
        turnHash := checked.raw.finalized.turnHash
        receiptHash := checked.raw.finalized.receiptHash
        signer := checked.raw.finalized.signer
        actorRoot := checked.raw.finalized.actorRoot }
    originKey := ReceiptKeyWire.ofSemantic entry.originKey
    artifact := ArtifactRefWire.ofSemantic entry.artifact
    contribution := ContributionWire.ofSemantic run.receipt.contribution
    worldSequence := run.receipt.postWorld.sequence }

/-- Every record this module emits is a settled one, and it is coherent, so
`only_finalized_carries_a_coordinate` applies to it. -/
theorem runWireOf_is_a_coherent_finalized_record (checked : CheckedPayload) :
    (runWireOf checked).status = .finalized ∧
      (runWireOf checked).coherentB = true ∧
      (runWireOf checked).coordinate.isSome = true :=
  ⟨rfl, rfl, rfl⟩

/-- The published identity is simultaneously the host's finalized coordinate and
the carrier the native judge actually settled against.  This is what makes
republishing a signer meaningful rather than decorative. -/
theorem runWireOf_coordinate_agrees_with_the_settlement_carrier (checked : CheckedPayload) :
    (runWireOf checked).coordinate = some
        { commitOrdinal := checked.raw.finalized.commitOrdinal
          turnHash := checked.raw.finalized.turnHash
          receiptHash := checked.raw.finalized.receiptHash
          signer := checked.settlement.carrier.playerKey
          actorRoot := checked.settlement.carrier.actorRoot } := by
  simp only [runWireOf, checked.signerExact, checked.actorRootExact]

/-- The archived provenance is the receipt's own replay key, not a host label. -/
theorem runWireOf_origin_is_the_receipt_key (checked : CheckedPayload) :
    (runWireOf checked).originKey =
        ReceiptKeyWire.ofSemantic checked.settlement.judgedRun.receipt.key ∧
      (runWireOf checked).artifact =
        ArtifactRefWire.ofSemantic checked.settlement.judgedRun.receipt.mission.artifact :=
  ⟨rfl, rfl⟩

private def orderedB (projection : Projection) (row : RowWire) : Bool :=
  match projection.lastFinalized with
  | none => true
  | some prior => decide (prior.commitOrdinal < row.commitOrdinal)

def payloadOf (federationId : Digest32) (row : RowWire) : Payload where
  finalized := {
    federationId := federationId
    commitOrdinal := row.commitOrdinal
    turnHash := row.turnHash
    receiptHash := row.receiptHash
    eventIndex := 0
    actorRoot := row.actorRoot
    signer := row.signer }
  judgeInput := row.judgeInput.text
  judgeOutput := row.judgeOutput.text

/-- The checked half of one durable row.  Refusal is total: a row out of commit
order, a row whose stored bytes are not the native judge's own, or a row whose
pre-Canon is not the projection rebuilt so far refuses the entire read rather
than being skipped. -/
def stepChecked (federationId : Digest32) (acc : Accumulated) (row : RowWire) :
    Option (CheckedPayload × Projection) :=
  if !orderedB acc.projection row then none
  else
    match checkPayload? (payloadOf federationId row) with
    | none => none
    | some checked =>
        match reduce acc.projection (payloadOf federationId row) with
        | none => none
        | some next => some (checked, next)

def step (federationId : Digest32) (acc : Accumulated) (row : RowWire) : Option Accumulated :=
  match stepChecked federationId acc row with
  | none => none
  | some (checked, next) =>
      some { projection := next, runs := acc.runs ++ [runWireOf checked] }

def foldRows (federationId : Digest32) : Accumulated → List RowWire → Option Accumulated
  | acc, [] => some acc
  | acc, row :: rest => do
      let next ← step federationId acc row
      foldRows federationId next rest

/-- An accepted row appends exactly one record, and that record is the one built
from the payload the judge accepted — no row can contribute two entries, and no
entry exists without an accepted row. -/
theorem step_appends_exactly_one_checked_run {federationId : Digest32}
    {acc after : Accumulated} {row : RowWire} (h : step federationId acc row = some after) :
    ∃ checked : CheckedPayload,
      stepChecked federationId acc row = some (checked, after.projection) ∧
        after.runs = acc.runs ++ [runWireOf checked] := by
  unfold step at h
  cases hs : stepChecked federationId acc row with
  | none =>
      rw [hs] at h
      simp at h
  | some pair =>
      obtain ⟨checked, next⟩ := pair
      rw [hs] at h
      injection h with heq
      subst heq
      refine ⟨checked, ?_, rfl⟩
      simp [hs]

/-! ## Projection -/

private def catalogOf (canon : CanonState) (known : List ArtifactRefWire) :
    Option (List ArtifactStatusWire) :=
  known.mapM fun wire => do
    let artifact ← wire.toSemantic?
    let status ← canon.status artifact
    some ({ artifact := wire, status := statusTag status } : ArtifactStatusWire)

/-- The complete read.  Every refusal below refuses the whole view: this surface
has no partial mode. -/
def project? (bytes : String) : Option ViewWire := do
  let request ← decodeRequest bytes
  let genesisWire ← decodeCanonState request.genesisCanon.text
  let configWire ← decodeGameConfig request.config.text
  -- ⚠ REFUSES rather than renders for a game with no constant payout. Vent Crawl pays
  -- what the banked rung pays, so there is no number to put here; publishing a zero or
  -- a ceiling would be publishing a payout no run receives. The Records read model does
  -- not render Vent Crawl yet and says so by declining, not by inventing.
  let reward ← configWire.reward?
  -- The claimed authority, the installed Canon and the installed mission must
  -- name one world; otherwise a Records read could publish a foreign world.
  if genesisWire.federationId != request.federationId then none
  else if configWire.mission.federationId != genesisWire.federationId then none
  else if configWire.mission.contentRoot != genesisWire.contentRoot then none
  else if configWire.mission.activationDigest != genesisWire.activationDigest then none
  else if configWire.mission.contentSession != genesisWire.contentSession then none
  else if configWire.mission.epoch != genesisWire.contentEpoch then none
  -- ⚑ The retained genesis config is a mission TEMPLATE and its seed must be the
  -- all-zero sentinel.  A live seed here would mean the node retained a drawn
  -- instance as if it were the template, and since `targetFromSeed?` is public
  -- that value IS an answer.  `PublicMissionWire` cannot publish it in any case;
  -- this refuses to serve the world at all, so the condition is detectable
  -- rather than silently tolerated.
  else if configWire.mission.runSeed != Emit.UNBOUND_RUN_SEED then none
  else do
    let genesisCanon ← genesisWire.toSemantic?
    -- Reconstructed only to refuse a config that is syntactically well formed
    -- but not a semantically constructible mission.
    let _semanticConfig ← configWire.toSemantic?
    let folded ← foldRows request.federationId
      { projection := Projection.initial genesisCanon, runs := [] } request.rows
    let canonNow ← folded.projection.canon.toSemantic?
    let catalog ← catalogOf canonNow folded.projection.canon.known
    some {
      federationId := folded.projection.canon.federationId
      contentRoot := folded.projection.canon.contentRoot
      activationDigest := folded.projection.canon.activationDigest
      contentSession := folded.projection.canon.contentSession
      contentEpoch := folded.projection.canon.contentEpoch
      curatorKey := folded.projection.canon.curatorKey
      stage := stageOf folded.runs
      mission := PublicMissionWire.ofMission configWire.mission
      reward
      world := folded.projection.canon.world
      canonRevision := folded.projection.canon.revision
      catalog := catalog
      runs := folded.runs
      archiveEntries := folded.projection.archive.entries.card
      lockerEntries := folded.projection.locker.entries.card
      attendantNotices := folded.projection.attendantNotices.card
      editorialInbox := folded.projection.editorialInbox.card
      consumedRuns := folded.projection.canon.consumedRuns.length
      players := folded.projection.canon.playerCounters.length }

def projectBytes? (bytes : String) : Option String := do
  let view ← project? bytes
  some view.toJson

/-- **`@[export dregg_poa_records_project]`** — the Records read boundary.

Empty output is the refusal sentinel, matching `dregg_poa_signal_judge`.  This
export authenticates nothing: it re-judges exactly the bytes it is handed.  The
host must have obtained them from finality and must check the durable chain
separately; availability of this function is evidence of neither. -/
@[export dregg_poa_records_project]
def recordsProjectFFI (bytes : String) : String := (projectBytes? bytes).getD ""

/-! ## Executable fixture and hostile paths

The fixture is the one the Signal judge and the finalized-run aggregate already
use, so a change to the judged transition moves these checks too.

⚑ **THE FIXTURES NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build root — and the seventeen `native_decide`
pins below ran at elaboration (each accepted row costing two native judge invocations), so
a stale Records fixture was a hard failure of every Rust proving target in the workspace
(the compilation-unit coupling the stale-fixture outage measured). The fixtures'
STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition (a `def`
body elaborates without running), beside the private fixture rows and views they must
see. The EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `RecordsRuntimeFixtures.lean`, rooted in the
`PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale
fixture reds the guard library instead of the archive.

Fail-closed convention: a check that reads fields off a projected VIEW matches on the
`Option` and answers `false` on `none` — a broken projection fails the pin in the guard
library rather than wedging this module.

Named residue: NONE — no construction here demands a proof as data. -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureGenesisWire : CanonStateWire := CanonStateWire.ofSemantic fixtureCanon

/-- ⚠ The TEMPLATE config — which is what a node actually retains and hands this
surface.  `poa_signal_genesis.rs` writes `run_seed: UNBOUND_RUN_SEED` because
genesis describes a mission with no instance; the live seed is drawn per run and
substituted into a COPY at judge time (`poa_signal_adapter.rs`).

The previous fixture handed this surface `fixtureConfig` — the LIVE config, whose
mission carries the derived `fixtureRunSeed` — so the fixture did not model what
production sends, and the emitted document therefore contained the live seed.
That exact previous fixture is retained below as
`hostile_live_run_seed_config_refused`. -/
private def fixtureTemplateConfig : SignalTriangulation.Config :=
  Emit.signalTemplateConfig fixtureFederationId fixtureSourceDigest
    fixtureContentDigest fixtureContentRoot fixtureActivationDigest

private def fixtureSignalConfigWire : SignalConfigWire :=
  SignalConfigWire.ofSemantic fixtureTemplateConfig

private def fixtureConfigWire : GameConfigWire := .signal fixtureSignalConfigWire

/-- The plaintext "transcript digest" of the fixture's single submitted action.
It exists here only to be searched for and not found. -/
private def fixtureTranscript : Digest32 :=
  SignalTriangulation.transcriptDigest [.submit fixtureConfig.target]

private def fixtureRow : RowWire where
  commitOrdinal := 7
  turnHash := digestByte 201
  receiptHash := digestByte 202
  actorRoot := fixtureCarrier.actorRoot
  signer := fixtureCarrier.playerKey
  judgeInput := ⟨fixtureInputBytes⟩
  judgeOutput := ⟨fixtureOutputBytes⟩

private def fixtureRequest (rows : List RowWire) : RequestWire where
  federationId := fixtureCarrier.federationId
  genesisCanon := ⟨fixtureGenesisWire.toJson⟩
  config := ⟨fixtureConfigWire.toJson⟩
  rows := rows

private def genesisOnlyView? : Option ViewWire := project? (fixtureRequest []).toJson

private def oneRunView? : Option ViewWire := project? (fixtureRequest [fixtureRow]).toJson

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_request_round_trips : Bool :=
  decide (decodeRequest (fixtureRequest [fixtureRow]).toJson =
    some (fixtureRequest [fixtureRow]))

/-- The point of the surface: with no finalized run at all, the view still
carries the exact world identity, world meters, Canon revision and playable
mission a run would land in — and says, in one word, that it is waiting for its
first run.  Height zero is not an empty page, and it is not a page pretending to
be full either.  Matches on the projected view; `none` answers `false`
(fail-closed). (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_genesis_only_view_is_a_real_world : Bool :=
  match genesisOnlyView? with
  | some view =>
      decide (view.federationId = fixtureCarrier.federationId) &&
      decide (view.contentSession = fixtureCanon.contentSession) &&
      decide (view.curatorKey = fixtureCanon.curatorKey) &&
      decide (view.stage = WorldStage.awaitingFirstRun) &&
      decide (view.mission.artifact =
        ArtifactRefWire.ofSemantic fixtureTemplateConfig.mission.artifact) &&
      decide (view.world = WorldStateWire.ofSemantic WorldState.empty) &&
      decide (view.canonRevision = 0) &&
      decide (view.runs = []) &&
      decide (view.archiveEntries = 0) &&
      decide (view.consumedRuns = 0)
  | none => false

/-- And one finalized run lands in every projection at once, with the artifact
carrying a Canon-derived beta status recomputed at read time.  The record's rung
is `finalized` and it carries the chain coordinate the host committed to.
Matches on the projected view; `none` answers `false` (fail-closed).
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_one_finalized_run_lands_in_every_projection : Bool :=
  match oneRunView? with
  | some view =>
      decide (view.stage = WorldStage.active) &&
      decide (view.runs.map RunWire.status = [RunStatus.finalized]) &&
      decide (view.runs.map RunWire.coordinate =
        [some { commitOrdinal := 7, turnHash := digestByte 201,
                receiptHash := digestByte 202, signer := fixtureCarrier.playerKey,
                actorRoot := fixtureCarrier.actorRoot }]) &&
      decide (view.runs.all RunWire.coherentB) &&
      decide (view.runs.map RunWire.artifact =
        [ArtifactRefWire.ofSemantic fixtureTemplateConfig.mission.artifact]) &&
      decide (view.catalog.map ArtifactStatusWire.status = ["beta"]) &&
      decide (view.archiveEntries = 1) &&
      decide (view.lockerEntries = 1) &&
      decide (view.attendantNotices = 1) &&
      decide (view.editorialInbox = 1) &&
      decide (view.canonRevision = 1) &&
      decide (view.consumedRuns = 1) &&
      decide (view.world.sequence = 1)
  | none => false

/-! ### The two published leaks, and their absence

⚠ Each needle below is checked to be a REAL needle before its absence is read.
A search for a string that is empty, or that is not actually the secret, would
pass while exercising nothing — an absence proof is only as good as the thing it
looked for. -/

/-- The live seed of this fixture's run is a genuine 64-character spelling and is
NOT the all-zero template sentinel.  Without this, the absence below would be
satisfiable by the needle simply being something the document never had.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_live_seed_is_a_real_needle : Bool :=
  decide ((Emit.bytes32Hex fixtureRunSeed).length = 64) &&
    decide (fixtureRunSeed ≠ Emit.UNBOUND_RUN_SEED)

/-- ⚑ **`transcriptDigest` is not a digest.**  Bytes 1..3 of the fixture's
"digest" are exactly the three submitted bands, and the submitted code of a
solved run is the target.  This is the reviewer's second defect, stated as a
check about the actual encoding rather than asserted in prose — and it is why
no transcript-derived field exists on this surface.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_transcript_is_plaintext_of_the_submitted_code : Bool :=
  decide ((fixtureTranscript.bytes.getD 1 0).val = fixtureConfig.target.low.val) &&
    decide ((fixtureTranscript.bytes.getD 2 0).val = fixtureConfig.target.mid.val) &&
    decide ((fixtureTranscript.bytes.getD 3 0).val = fixtureConfig.target.high.val) &&
    decide (some fixtureConfig.target = SignalTriangulation.targetFromSeed? fixtureRunSeed)

/-- ⚑ The emitted document does not contain the live run seed anywhere — not in
the mission, not in a record, not in any field.  `targetFromSeed?` of that seed is
the answer, so this is the load-bearing absence.  Matches on the projected view;
`none` answers `false` (fail-closed). (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_view_never_publishes_the_live_run_seed : Bool :=
  match oneRunView? with
  | some view =>
      decide ((view.toJson.splitOn (Emit.bytes32Hex fixtureRunSeed)).length = 1)
  | none => false

/-- And it does not contain the plaintext transcript either.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_view_never_publishes_the_transcript : Bool :=
  match oneRunView? with
  | some view =>
      decide ((view.toJson.splitOn (Emit.bytes32Hex fixtureTranscript)).length = 1)
  | none => false

/-- ⚑ **The previous fixture, kept as the falsifier.**  Handing this surface the
LIVE config — the one whose mission carries the derived seed, which is what the
old fixture did — is refused outright rather than rendered.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_live_run_seed_config_refused : Bool :=
  (project? { fixtureRequest [fixtureRow] with
    config := ⟨(GameConfigWire.signal (SignalConfigWire.ofSemantic fixtureConfig)).toJson⟩ }.toJson).isNone

/-- ⚠ The falsifier above really does substitute something: the live config's
bytes differ from the template's, and they differ in the run seed specifically.
Without this the refusal could be refusing an unchanged input.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_live_config_is_a_real_substitution : Bool :=
  decide ((GameConfigWire.signal (SignalConfigWire.ofSemantic fixtureConfig)).toJson ≠ fixtureConfigWire.toJson) &&
    decide ((SignalConfigWire.ofSemantic fixtureConfig).mission.runSeed ≠
      fixtureConfigWire.mission.runSeed)

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_substituted_signer_refused : Bool :=
  (project? (fixtureRequest [{ fixtureRow with signer := digestByte 250 }]).toJson).isNone

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_substituted_actor_root_refused : Bool :=
  (project? (fixtureRequest [{ fixtureRow with actorRoot := digestByte 251 }]).toJson).isNone

/-- A row cannot start from a Canon the projection has not reached: the fold
rebuilds the chain rather than trusting a stored successor.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_row_against_a_foreign_genesis_refused : Bool :=
  (project? { fixtureRequest [fixtureRow] with
    genesisCanon := ⟨fixtureSuccessorCanonWire.toJson⟩ }.toJson).isNone

/-- The same finalized run cannot land twice: Canon's consumed-receipt admission
is re-run inside the fold. (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_replayed_row_refused : Bool :=
  (project? (fixtureRequest
    [fixtureRow, { fixtureRow with commitOrdinal := 8 }]).toJson).isNone

/-- Rows must arrive in strict commit order; a reordered history refuses.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_out_of_order_rows_refused : Bool :=
  (project? (fixtureRequest
    [{ fixtureRow with commitOrdinal := 8 }, fixtureRow]).toJson).isNone

/-- A foreign authority cannot read this world's records under its own id.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_foreign_authority_refused : Bool :=
  (project? { fixtureRequest [] with federationId := digestByte 252 }.toJson).isNone

/-- A mission bound to another world cannot be published beside this Canon.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_mission_from_another_world_refused : Bool :=
  (project? { fixtureRequest [] with
    config := ⟨(GameConfigWire.signal { fixtureSignalConfigWire with
      mission := { fixtureSignalConfigWire.mission with
        contentRoot := digestByte 253 } }).toJson⟩ }.toJson).isNone

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_export_refuses_malformed : Bool :=
  decide (recordsProjectFFI ((fixtureRequest []).toJson ++ "\n") = "")

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms RunStatus.tag_injective
#assert_axioms only_finalized_carries_a_coordinate
#assert_axioms unsettled_has_no_coordinate
#assert_axioms publicMission_ignores_the_run_seed
#assert_axioms public_mission_carries_the_practice_context
#assert_axioms stageOf_awaiting_iff_no_runs
#assert_axioms runWireOf_is_a_coherent_finalized_record
#assert_axioms runWireOf_coordinate_agrees_with_the_settlement_carrier
#assert_axioms runWireOf_origin_is_the_receipt_key
#assert_axioms step_appends_exactly_one_checked_run

-- The seventeen fixture pins (`native_decide` + `#assert_compiled`) live in
-- `RecordsRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the fixtures
-- header above.

end Dregg2.Games.PathOfAngels.RecordsRuntime
