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

**It never publishes the answer.**  `ViewWire` has no field for
`SignalConfigWire.target`, so the emitter cannot leak the Signal solution.  That
is a type-level absence rather than a filter someone can forget — but it is not
a fix for the descriptor either: the target remains public in
`games/signal-triangulation.json`, and this surface merely declines to become a
second copy of it.

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
abbrev RECORDS_OUTPUT_FORMAT : String := "POA-RECORDS-OUT-1"

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

/-- Canon lifecycle is recomputed from the rebuilt Canon at read time; no status
label is ever carried in from storage. -/
structure ArtifactStatusWire where
  artifact : ArtifactRefWire
  status : String
deriving DecidableEq

/-- One landed run.  The coordinate fields are the finalized ones the host
supplied and which `CheckedPayload` binds to the judged carrier; the rest is the
Field Archive projection of the re-judged receipt. -/
structure RunWire where
  commitOrdinal : Nat
  turnHash : Digest32
  receiptHash : Digest32
  signer : Digest32
  actorRoot : Digest32
  originKey : ReceiptKeyWire
  artifact : ArtifactRefWire
  contribution : ContributionWire
  worldSequence : Nat
  transcriptDigest : Digest32
deriving DecidableEq

/-- There is deliberately no `target` field: this surface will not become a
second publisher of the Signal answer. -/
structure ViewWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  curatorKey : Digest32
  mission : MissionWire
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

def RunWire.toJson (run : RunWire) : String :=
  "{\"commit_ordinal\":" ++ toString run.commitOrdinal ++
    ",\"turn_hash\":" ++ jsonString (Emit.bytes32Hex run.turnHash) ++
    ",\"receipt_hash\":" ++ jsonString (Emit.bytes32Hex run.receiptHash) ++
    ",\"signer\":" ++ jsonString (Emit.bytes32Hex run.signer) ++
    ",\"actor_root\":" ++ jsonString (Emit.bytes32Hex run.actorRoot) ++
    ",\"origin_key\":" ++ run.originKey.toJson ++
    ",\"artifact\":" ++ run.artifact.toJson ++
    ",\"contribution\":" ++ run.contribution.toJson ++
    ",\"world_sequence\":" ++ toString run.worldSequence ++
    ",\"transcript_digest\":" ++ jsonString (Emit.bytes32Hex run.transcriptDigest) ++ "}"

def ViewWire.toJson (view : ViewWire) : String :=
  "{\"format\":" ++ jsonString RECORDS_OUTPUT_FORMAT ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex view.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex view.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex view.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex view.contentSession) ++
    ",\"content_epoch\":" ++ toString view.contentEpoch ++
    ",\"curator_key\":" ++ jsonString (Emit.bytes32Hex view.curatorKey) ++
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
  { commitOrdinal := checked.raw.finalized.commitOrdinal
    turnHash := checked.raw.finalized.turnHash
    receiptHash := checked.raw.finalized.receiptHash
    signer := checked.raw.finalized.signer
    actorRoot := checked.raw.finalized.actorRoot
    originKey := ReceiptKeyWire.ofSemantic entry.originKey
    artifact := ArtifactRefWire.ofSemantic entry.artifact
    contribution := ContributionWire.ofSemantic run.receipt.contribution
    worldSequence := run.receipt.postWorld.sequence
    transcriptDigest := run.receipt.transcriptDigest }

/-- The published identity is simultaneously the host's finalized coordinate and
the carrier the native judge actually settled against.  This is what makes
republishing a signer meaningful rather than decorative. -/
theorem runWireOf_coordinate_agrees_with_the_settlement_carrier (checked : CheckedPayload) :
    (runWireOf checked).signer = checked.raw.finalized.signer ∧
      (runWireOf checked).actorRoot = checked.raw.finalized.actorRoot ∧
      (runWireOf checked).signer = checked.settlement.carrier.playerKey ∧
      (runWireOf checked).actorRoot = checked.settlement.carrier.actorRoot :=
  ⟨rfl, rfl, checked.signerExact, checked.actorRootExact⟩

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
      exact ⟨checked, hs, rfl⟩

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
  let configWire ← decodeSignalConfig request.config.text
  -- The claimed authority, the installed Canon and the installed mission must
  -- name one world; otherwise a Records read could publish a foreign world.
  if genesisWire.federationId != request.federationId then none
  else if configWire.mission.federationId != genesisWire.federationId then none
  else if configWire.mission.contentRoot != genesisWire.contentRoot then none
  else if configWire.mission.activationDigest != genesisWire.activationDigest then none
  else if configWire.mission.contentSession != genesisWire.contentSession then none
  else if configWire.mission.epoch != genesisWire.contentEpoch then none
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
      mission := configWire.mission
      reward := configWire.reward
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
use, so a change to the judged transition moves these theorems too. -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureGenesisWire : CanonStateWire := CanonStateWire.ofSemantic fixtureCanon

private def fixtureConfigWire : SignalConfigWire := SignalConfigWire.ofSemantic fixtureConfig

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

theorem fixture_request_round_trips :
    decodeRequest (fixtureRequest [fixtureRow]).toJson = some (fixtureRequest [fixtureRow]) := by
  native_decide

/-- The point of the surface: with no finalized run at all, the view still
carries the exact world identity, world meters, Canon revision and playable
mission a run would land in.  Height zero is not an empty page. -/
theorem fixture_genesis_only_view_is_a_real_world :
    (genesisOnlyView?.map fun view =>
      decide (view.federationId = fixtureCarrier.federationId) &&
      decide (view.contentSession = fixtureCanon.contentSession) &&
      decide (view.curatorKey = fixtureCanon.curatorKey) &&
      decide (view.mission.artifact =
        ArtifactRefWire.ofSemantic fixtureConfig.mission.artifact) &&
      decide (view.world = WorldStateWire.ofSemantic WorldState.empty) &&
      decide (view.canonRevision = 0) &&
      decide (view.runs = []) &&
      decide (view.archiveEntries = 0) &&
      decide (view.consumedRuns = 0)) = some true := by
  native_decide

/-- And one finalized run lands in every projection at once, with the artifact
carrying a Canon-derived beta status recomputed at read time. -/
theorem fixture_one_finalized_run_lands_in_every_projection :
    (oneRunView?.map fun view =>
      decide (view.runs.map RunWire.signer = [fixtureCarrier.playerKey]) &&
      decide (view.runs.map RunWire.actorRoot = [fixtureCarrier.actorRoot]) &&
      decide (view.runs.map RunWire.commitOrdinal = [7]) &&
      decide (view.runs.map RunWire.artifact =
        [ArtifactRefWire.ofSemantic fixtureConfig.mission.artifact]) &&
      decide (view.catalog.map ArtifactStatusWire.status = ["beta"]) &&
      decide (view.archiveEntries = 1) &&
      decide (view.lockerEntries = 1) &&
      decide (view.attendantNotices = 1) &&
      decide (view.editorialInbox = 1) &&
      decide (view.canonRevision = 1) &&
      decide (view.consumedRuns = 1) &&
      decide (view.world.sequence = 1)) = some true := by
  native_decide

theorem hostile_substituted_signer_refused :
    project? (fixtureRequest [{ fixtureRow with signer := digestByte 250 }]).toJson = none := by
  native_decide

theorem hostile_substituted_actor_root_refused :
    project? (fixtureRequest [{ fixtureRow with actorRoot := digestByte 251 }]).toJson = none := by
  native_decide

/-- A row cannot start from a Canon the projection has not reached: the fold
rebuilds the chain rather than trusting a stored successor. -/
theorem hostile_row_against_a_foreign_genesis_refused :
    project? { fixtureRequest [fixtureRow] with
      genesisCanon := ⟨fixtureSuccessorCanonWire.toJson⟩ }.toJson = none := by
  native_decide

/-- The same finalized run cannot land twice: Canon's consumed-receipt admission
is re-run inside the fold. -/
theorem hostile_replayed_row_refused :
    project? (fixtureRequest
      [fixtureRow, { fixtureRow with commitOrdinal := 8 }]).toJson = none := by
  native_decide

/-- Rows must arrive in strict commit order; a reordered history refuses. -/
theorem hostile_out_of_order_rows_refused :
    project? (fixtureRequest
      [{ fixtureRow with commitOrdinal := 8 }, fixtureRow]).toJson = none := by
  native_decide

/-- A foreign authority cannot read this world's records under its own id. -/
theorem hostile_foreign_authority_refused :
    project? { fixtureRequest [] with federationId := digestByte 252 }.toJson = none := by
  native_decide

/-- A mission bound to another world cannot be published beside this Canon. -/
theorem hostile_mission_from_another_world_refused :
    project? { fixtureRequest [] with
      config := ⟨{ fixtureConfigWire with
        mission := { fixtureConfigWire.mission with
          contentRoot := digestByte 253 } }.toJson⟩ }.toJson = none := by
  native_decide

theorem fixture_export_refuses_malformed :
    recordsProjectFFI ((fixtureRequest []).toJson ++ "\n") = "" := by
  native_decide

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms runWireOf_coordinate_agrees_with_the_settlement_carrier
#assert_axioms runWireOf_origin_is_the_receipt_key
#assert_axioms step_appends_exactly_one_checked_run

#assert_compiled fixture_request_round_trips
#assert_compiled fixture_genesis_only_view_is_a_real_world
#assert_compiled fixture_one_finalized_run_lands_in_every_projection
#assert_compiled hostile_substituted_signer_refused
#assert_compiled hostile_substituted_actor_root_refused
#assert_compiled hostile_row_against_a_foreign_genesis_refused
#assert_compiled hostile_replayed_row_refused
#assert_compiled hostile_out_of_order_rows_refused
#assert_compiled hostile_foreign_authority_refused
#assert_compiled hostile_mission_from_another_world_refused
#assert_compiled fixture_export_refuses_malformed

end Dregg2.Games.PathOfAngels.RecordsRuntime
