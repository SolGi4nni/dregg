/-
# StationDailyRuntime — the READ boundary for the station's daily ritual

Substrate note: this is Lean-authored game semantics behind a canonical byte
wire.  Nothing here is an AIR, a constraint system or a gadget.  Rust carries
bytes to this module and back; it computes nothing.

PLATFORM-ROADMAP §7.3 pairs two rows, and both already exist and are proved:
`SalvageCrate` is the ritual and `ShipInstrumentPanel` is what the ritual moves.
Neither had an `@[export]`, so no reader could see either one.  This module is
that export, and it is deliberately a READ ONLY.

## ⚠ CORRECTED TWICE — and the second correction is the one that CLOSED the gap

This heading used to say the write path was "unreachable by type": that
`SalvageCrate.CurrentStateCapability` was `opaque` with no producer anywhere, so
no `@[export]` could ever reach `openCrate`.  **That was false at HEAD.**  The
capability is a sealed structure with a `private` constructor and two producers —
`SalvageCrate.genesis` (the one-time install) and the successor an ACCEPTED open
hands back — `StationCrateOpen` composes them with `ShipInstrumentPanel.observe`,
and `StationCrateOpenRuntime` exports the whole ceremony as
`dregg_poa_crate_open`.  A player can open the crate.

Then this module still served zeros, for a *second* and weaker reason: its
request carried no open history, so the read had nothing to fold.  Measured over
HTTP on 2026-08-07: the write path served `exact_total: 1, observed: 2` while
`/api/poa/station/…/panel` served `exact_total: 0, observed: 0`.  **That is what
this version fixes.**  `Request` now carries `history` — the node's durable open
log — and `servedStateOver` REPLAYS it.

What is still true, and is what keeps this wire receipt-free:

* `SalvageCrate.openCore` is `private`, so no module outside `SalvageCrate` can
  call it.
* `ShipInstrumentPanel.Receipt` has a private `mk` whose only producer is
  `ofSalvageOpen`, which consumes an accepted `SalvageCrate.OpenReceipt`.

That second point still decides this module's shape.  A wire that decoded JSON
into a `Receipt` would be a public constructor for the sealed type, and any
caller could then post a contribution the crate never authorized and move the
ship.  So **this wire carries no receipts** — it carries the LOG, and every
receipt is re-derived by replaying it through `SalvageCrate.openCrate` itself.

## ⚑ ONE FOLD, and it lives here because this is the module both halves import

`HistoryRow`, `priorOpens`, `envelopeOfRow`, `envelopesOfHistory` and `replayOver`
were authored in `StationCrateOpenRuntime` (the WRITE).  They are here now, and
the write ABBREVIATES them, because the alternative was a second fold: a read
that replayed the same log by its own arithmetic is two shapes that agree today
and disagree the first time either grows a field.  This module is the one both
runtimes import, so it is where the shared fold can live; the direction is the
same one that already collapsed `stationPanelRaw` into `StationCrateOpen.panelRaw`.

`the_served_ship_moves_when_the_log_records_an_opening` replaces
`the_served_ship_has_not_been_moved`, which was advertised as "the assertion that
goes RED the day a judged opening can be folded in" and did **not** go red when
that day came — because it was never about reachability, only about this request
type having no `history` field.  Its replacement is a PAIR over the same
deployment: an empty log serves zeros, and the one-row log an accepted open
leaves behind serves the moved ship.  Delete the fold and the second half reds.
`StationCrateOpenRuntime.the_station_read_serves_the_ship_this_write_published`
is the cross-module half: the document THIS read serves for the log the node
appends is bit-identical to the panel the WRITE published.

## ⚠ An unreplayable log is a REFUSAL, never a ship at zero

`readBytes?` is `none` — the `""` fail-closed sentinel — when the log does not
replay.  Serving `ShipInstrumentPanel.initial` there would render a corrupt or
foreign log as "nobody has opened the crate yet", which is exactly the reading a
player cannot distinguish from the truth.  `the_read_refuses_a_log_it_cannot_replay`
pins it.

## The two halves, and why one of them may be public at all

**The panel half is communal by construction.**  `ShipInstrumentPanel.State` has
no per-player field; `the_face_does_not_record_who_opened` proves two different
crew members drawing the same ticket leave identical faces.  The wire twin here
is `the_served_panel_does_not_depend_on_the_crew`: substituting *any* request
leaves every panel field of the served document bit-identical.  A reader
therefore reconstructs no attendance record, streak or leaderboard, because
there is no such state to reconstruct.

**The crate half is a VISIBLE ROTATION, not a hidden instance.**  `SalvageCrate`
is explicit that its mixer "is not an unpredictability source" and that the
beacon schedule is "curator-authored and visible", and `generatedRotation` hands
a player their whole rotation deliberately.  This module publishes exactly that
function of exactly that authored schedule
(`the_served_rotation_is_the_crate_rotation`,
`the_served_beacons_are_the_authored_schedule`).

⚠ The three arcade games' hidden instances live behind `HiddenInstance` /
`SlotDeriveRuntime`, and **this module's import cone contains neither**.  The
containment is structural rather than a filter: there is no run seed, slot
secret, commitment or target anywhere in the reply type, because the types that
carry them are not in scope.

⚠ And the standing condition the panel's own docblock names is carried forward
here unchanged: the visible rotation is fine *only because* the panel is
communal and unattributed.  **If anything attributable is ever hung off this
panel, this route stops being safe** and the rotation must leave it.

## The authored station

The crate is `SalvageCrateExamples.config` — already authored, already proved
valid, and its docblock already names "the web/game layer" as its consumer.  It
is reused rather than re-typed.

⚑ The panel is `StationCrateOpen.panel`, not a second one.  This module used to
author its own `stationPanelRaw` with the same fields, and `StationCrateOpen`
authored an identical one for the write path — two shapes that agreed today and
would have disagreed the first time either grew a dial.  There is now ONE panel
deployment and both halves abbreviate it.  It carries exactly one dial, because
`the_authored_table_moves_only_supplies` shows every row of the authored table
leaves intel, cohesion, influence and score at zero — a second dial would be one
that provably cannot move, which is decoration.  The panel's identity is read
off the crate's mission rather than re-typed, and
`the_panel_and_the_crate_are_one_deployment` proves the two agree, so a receipt
from this crate could never be refused by this panel as foreign.

⚠ The station content is Lean-authored, not installed by a genesis ceremony —
there is no station genesis and no activated-content component for it.  The
served `federation_id` is therefore the *authored* one and need not be the
node's.  The Rust route reports the node's own federation beside it rather than
implying they match.

## The wire

Request (`POA-STATION-DAILY-1`), key order pinned by `Request.toJson`:

    {"format":"POA-STATION-DAILY-1","crew":null,"history":[]}
    {"format":"POA-STATION-DAILY-1","crew":"<64 lowercase hex>",
     "history":[{"player":"<64 lowercase hex>","period":n},…]}

⚠ `history` is the node's DURABLE OPEN LOG, spelled exactly as the crate-open
wire spells it (`HistoryRow.toJson` is the same function).  It is not a value a
browser authors: the node reads it out of its own store.  A caller who edits a
row edits the log, and the log then fails to replay — `readBytes?` returns the
`""` refusal rather than a shorter or re-dated history.

Reply (`POA-STATION-DAILY-OUT-1`):

    {"format":"POA-STATION-DAILY-OUT-1",
     "federation_id":"<hex>","content_session":"<hex>","content_epoch":n,
     "gauges":[{"gauge":n,"meter":"supplies","exact_total":n,"full_at":n,
                "shown":n,"at_full":false}],
     "recovered_kinds":n,"observed":n,"admitted":n,
     "opens_at":n,"closes_at":n,"table_rows":n,"ticket_count":n,
     "crew":null | {"key":"<hex>","eligible":bool,
                    "rotation":[{"period":n,"beacon":"<hex>",
                                 "entry":null|{"id":n,"prize":"…","supplies":n}}]}}

Acceptance is `NetworkJudgeWire.canonicalDecode` — the same seal
`decodeSignalInput` and `dregg_poa_signal_slot_derive` use, imported rather than
re-typed.  An unknown field, a missing field, a transposed key, an uppercase hex
digit, a trailing byte or a re-spelled integer all fail the re-encode comparison
and the export returns `""`.

`exact_total` is the unclipped arithmetic and `shown` is the needle; both are
published so the display scale can never quietly become the bound.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.NetworkJudgeWire
import Dregg2.Games.PathOfAngels.ShipInstrumentPanel
import Dregg2.Games.PathOfAngels.SalvageCrateExamples
import Dregg2.Games.PathOfAngels.StationCrateOpen
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.StationDailyRuntime

open Lean (Json)
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-STATION-DAILY-1"
abbrev OUTPUT_FORMAT : String := "POA-STATION-DAILY-OUT-1"

/-- Outer allocation fuse.  Mirrors `MAX_POA_STATION_DAILY_WIRE_BYTES` in
`dregg-lean-ffi/src/poa_station_daily_ffi.rs`.  ⚠ RAISED from 16 KiB when this
request grew `history`: a full 4096-row log spells to about 390 KB, so the old
fuse would have refused every station read on a busy node — a fail-closed refusal
that looked exactly like a corrupt log.  This is a malformed-caller guard and not
a semantic bound; `MAX_HISTORY_ROWS` is the semantic one. -/
abbrev WIRE_BYTE_LIMIT : Nat := 1024 * 1024

/-- The log bound.  `ShipInstrumentPanel.observe` refuses past its own capacity,
so a longer log could not fold anyway; making the refusal happen at the parser
keeps the quadratic replay bounded.  Shared with the crate-open wire, which
abbreviates this. -/
abbrev MAX_HISTORY_ROWS : Nat := ShipInstrumentPanel.MAX_OBSERVED

/-- A period is a small authored ordinal; this only stops a caller posting an
integer whose decimal spelling is the whole allocation budget. -/
abbrev PERIOD_LIMIT : Nat := 4294967296

/-! ## The authored station

The crate is reused; only the panel deployment is authored here. -/

/-- The authored three-period rotation.  `SalvageCrateExamples` already proves
`configValidB` of it, so this is a reference and not a second config. -/
abbrev stationCrate : SalvageCrate.Config := SalvageCrateExamples.config

/-- ⭐ Every authored row leaves four of the five meters at zero, so the panel
below authors exactly one dial.  A second dial would be one that provably cannot
move — this fact is the reason there is not one.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_authored_table_moves_only_supplies : Bool :=
  stationCrate.raw.table.all (fun entry =>
    decide (entry.contribution.intel = 0) &&
    decide (entry.contribution.cohesion = 0) &&
    decide (entry.contribution.influence = 0) &&
    decide (entry.contribution.score = 0))

/-- The station's panel — `StationCrateOpen.panel`, the one the WRITE path folds
receipts into.  Identity is read off the crate's mission rather than re-typed;
`fullAt` is an authored display scale for the reclamation bins and is
deliberately not the mission budget, which bounds one contribution rather than
the communal total.  These two abbreviations exist so the names this module's
theorems already use keep resolving; they are not a second deployment. -/
abbrev stationPanelRaw : ShipInstrumentPanel.RawPanel := StationCrateOpen.panelRaw

theorem station_panel_valid :
    ShipInstrumentPanel.panelValidB stationPanelRaw = true :=
  StationCrateOpen.panel_valid

abbrev stationPanel : ShipInstrumentPanel.Panel := StationCrateOpen.panel

/-- ⭐ The panel and the crate are ONE deployment.  Without this the panel could
refuse every receipt the crate ever produced as `foreignDeployment`, and the
refusal would look like a quiet empty page. -/
theorem the_panel_and_the_crate_are_one_deployment :
    stationPanelRaw.federationId = stationCrate.raw.mission.federationId ∧
    stationPanelRaw.contentSession = stationCrate.raw.mission.contentSession ∧
    stationPanelRaw.contentEpoch = stationCrate.raw.mission.epoch :=
  ⟨rfl, rfl, rfl⟩

/-! ## The node's durable open log, and the ONE fold that replays it

⚑ These five definitions are the WRITE path's fold.  They were authored in
`StationCrateOpenRuntime`, which imports this module; they live here now and the
write abbreviates them, so the ship a reader sees and the ship a writer sees are
computed by one function rather than by two that agree today.

Everything is parameterized by `(config, deployment)` deliberately: the laws
below are properties of the FOLD, not of the station's particular content. -/

/-- One durable log row.  Counters and sequence numbers are deliberately ABSENT:
they are derived from the row's position, so a caller cannot advance a counter
without moving a row, and moving a row breaks the replay. -/
structure HistoryRow where
  player : Digest32
  period : Nat
deriving DecidableEq

/-- How many times this crew key already appears in the log.  This is the crate's
`playerCounters` value for that key after the replay, derived from position. -/
def priorOpens (history : List HistoryRow) (player : Digest32) : Nat :=
  history.countP (fun row => decide (row.player = player))

/-- The envelope the crate accepted for log row `index`.  `expectedSequence` is
the row's position because every accepted open advances `State.sequence` by one
and nothing else advances it. -/
def envelopeOfRow (config : SalvageCrate.Config) (history : List HistoryRow) (index : Nat)
    (row : HistoryRow) : SalvageCrate.OpenEnvelope :=
  let previous := priorOpens (history.take index) row.player
  StationCrateOpen.envFor config row.player ⟨row.period⟩ previous (previous + 1) index

def envelopesOfHistory (config : SalvageCrate.Config) (history : List HistoryRow) :
    List SalvageCrate.OpenEnvelope :=
  history.zipIdx.map (fun (row, index) => envelopeOfRow config history index row)

/-- Replay the node's durable log from the installed ship.  `none` exactly when
some row is not one this crate could have accepted in that position. -/
def replayOver (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (history : List HistoryRow) : Option (StationCrateOpen.Rolled config) :=
  StationCrateOpen.rollDay config deployment (StationCrateOpen.genesisRolled config deployment)
    (envelopesOfHistory config history)

/-- ⭐ The ship this read serves: the panel the node's own log folds to.  `none`
is a REFUSAL, not a ship at zero — see the module docblock.  With an empty log
this is `ShipInstrumentPanel.initial deployment`, which is what the station
served unconditionally before the log reached it. -/
def servedStateOver (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (history : List HistoryRow) : Option ShipInstrumentPanel.State :=
  (replayOver config deployment history).map StationCrateOpen.Rolled.panel

/-- The station's own deployment. -/
abbrev servedStateFor : List HistoryRow → Option ShipInstrumentPanel.State :=
  servedStateOver stationCrate stationPanel

/-! ## The two wire records -/

/-- ⚠ `history` is the node's durable open log, not a value any browser authors.
It is on the REQUEST because this read is otherwise a pure function of authored
content, and the log is the only thing that has happened. -/
structure Request where
  crew : Option Digest32
  history : List HistoryRow
deriving DecidableEq

structure GaugeWire where
  gauge : Nat
  meter : String
  exactTotal : Nat
  fullAt : Nat
  shown : Nat
  atFull : Bool
deriving DecidableEq

/-- The drawn row.  `prize` carries the relic/cosmetic/record id inside its
label, so no separate id list is needed and the reply has no `Finset` whose
`toList` order would have to be pinned. -/
structure EntryWire where
  id : Nat
  prize : String
  supplies : Nat
deriving DecidableEq

structure PeriodWire where
  period : Nat
  beacon : Digest32
  entry : Option EntryWire
deriving DecidableEq

structure CrewWire where
  key : Digest32
  eligible : Bool
  rotation : List PeriodWire
deriving DecidableEq

/-- Every field is either the authored deployment identity, a communal aggregate,
or the visible rotation of the crew key the caller named.  There is no
per-player row, no streak, no last-seen epoch, and no run seed. -/
structure Reply where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  gauges : List GaugeWire
  recoveredKinds : Nat
  observed : Nat
  admitted : Nat
  opensAt : Nat
  closesAt : Nat
  tableRows : Nat
  ticketCount : Nat
  crew : Option CrewWire
deriving DecidableEq

/-! ## Encoders — canonical by construction, key order pinned here -/

private def jsonString (s : String) : String := String.quote s

private def jsonBool (b : Bool) : String := if b then "true" else "false"

private def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

/-- The ONE spelling of a log row.  The crate-open wire uses this same function,
so the two requests cannot spell the node's log two ways. -/
def HistoryRow.toJson (row : HistoryRow) : String :=
  "{\"player\":" ++ jsonString (Emit.bytes32Hex row.player) ++
    ",\"period\":" ++ toString row.period ++ "}"

def Request.toJson (request : Request) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"crew\":" ++
      (match request.crew with
       | none => "null"
       | some key => jsonString (Emit.bytes32Hex key)) ++
    ",\"history\":" ++ jsonArray (request.history.map HistoryRow.toJson) ++ "}"

def GaugeWire.toJson (gauge : GaugeWire) : String :=
  "{\"gauge\":" ++ toString gauge.gauge ++
    ",\"meter\":" ++ jsonString gauge.meter ++
    ",\"exact_total\":" ++ toString gauge.exactTotal ++
    ",\"full_at\":" ++ toString gauge.fullAt ++
    ",\"shown\":" ++ toString gauge.shown ++
    ",\"at_full\":" ++ jsonBool gauge.atFull ++ "}"

def EntryWire.toJson (entry : EntryWire) : String :=
  "{\"id\":" ++ toString entry.id ++
    ",\"prize\":" ++ jsonString entry.prize ++
    ",\"supplies\":" ++ toString entry.supplies ++ "}"

def PeriodWire.toJson (period : PeriodWire) : String :=
  "{\"period\":" ++ toString period.period ++
    ",\"beacon\":" ++ jsonString (Emit.bytes32Hex period.beacon) ++
    ",\"entry\":" ++
      (match period.entry with
       | none => "null"
       | some entry => entry.toJson) ++ "}"

def CrewWire.toJson (crew : CrewWire) : String :=
  "{\"key\":" ++ jsonString (Emit.bytes32Hex crew.key) ++
    ",\"eligible\":" ++ jsonBool crew.eligible ++
    ",\"rotation\":" ++ jsonArray (crew.rotation.map PeriodWire.toJson) ++ "}"

def Reply.toJson (reply : Reply) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex reply.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex reply.contentSession) ++
    ",\"content_epoch\":" ++ toString reply.contentEpoch ++
    ",\"gauges\":" ++ jsonArray (reply.gauges.map GaugeWire.toJson) ++
    ",\"recovered_kinds\":" ++ toString reply.recoveredKinds ++
    ",\"observed\":" ++ toString reply.observed ++
    ",\"admitted\":" ++ toString reply.admitted ++
    ",\"opens_at\":" ++ toString reply.opensAt ++
    ",\"closes_at\":" ++ toString reply.closesAt ++
    ",\"table_rows\":" ++ toString reply.tableRows ++
    ",\"ticket_count\":" ++ toString reply.ticketCount ++
    ",\"crew\":" ++
      (match reply.crew with
       | none => "null"
       | some crew => crew.toJson) ++ "}"

/-! ## Strict parse

These accessors are the same shape as `NetworkJudgeWire`'s and
`SlotDeriveRuntime`'s private ones; the SEAL (`canonicalDecode`) is imported
rather than re-typed, which is the part that could drift meaningfully. -/

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then
    pure ()
  else
    throw "missing or unknown field"

/-- `null` and a 64-digit lowercase hex string are the only two accepted
spellings, and each has exactly one, so the canonical seal is total over this
field rather than tolerating a second encoding of "absent". -/
private def objectOptDigest (j : Json) (key : String) :
    Except String (Option Digest32) := do
  let value ← j.getObjVal? key
  match value with
  | .null => pure none
  | .str spelling =>
      match Emit.parseBytes32Hex? spelling with
      | some digest => pure (some digest)
      | none => throw "digest must be exactly 64 lowercase hexadecimal digits"
  | _ => throw "crew must be null or a digest string"

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def objectNat (j : Json) (key : String) (limit : Nat) : Except String Nat := do
  let value ← j.getObjValAs? Nat key
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def parseHistoryRow (j : Json) : Except String HistoryRow := do
  exactKeys j ["player", "period"]
  pure { player := ← objectDigest j "player", period := ← objectNat j "period" PERIOD_LIMIT }

private def parseHistory (j : Json) : Except String (List HistoryRow) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_HISTORY_ROWS then throw "open history exceeds wire bound"
  values.mapM parseHistoryRow

private def parseRequestJson (j : Json) : Except String Request := do
  exactKeys j ["format", "crew", "history"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong station-daily request format"
  pure { crew := ← objectOptDigest j "crew",
         history := ← parseHistory (← j.getObjVal? "history") }

def decodeRequestWithLimit (byteLimit : Nat) (bytes : String) : Option Request :=
  if bytes.length ≤ byteLimit then
    NetworkJudgeWire.canonicalDecode parseRequestJson Request.toJson bytes
  else none

def decodeRequest (bytes : String) : Option Request :=
  decodeRequestWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The projection -/

def meterLabel : ShipInstrumentPanel.Meter → String
  | .intel => "intel"
  | .supplies => "supplies"
  | .cohesion => "cohesion"
  | .influence => "influence"
  | .score => "score"

def prizeLabel : SalvageCrate.Prize → String
  | .common .packingFoam => "packing-foam"
  | .common .maintenanceSticker => "maintenance-sticker"
  | .common .warmAir => "warm-air"
  | .common .galleyCoupon => "galley-coupon"
  | .cosmetic id => "cosmetic:" ++ toString id.value
  | .record id => "record:" ++ toString id.value
  | .communalSalvage id => "communal-salvage:" ++ toString id.value

def gaugeWireOf (reading : ShipInstrumentPanel.Reading) : GaugeWire where
  gauge := reading.gauge.value
  meter := meterLabel reading.meter
  exactTotal := reading.exactTotal
  fullAt := reading.fullAt
  shown := reading.shown
  atFull := reading.atFull

def entryWireOf (entry : SalvageCrate.LootEntry) : EntryWire where
  id := entry.id.value
  prize := prizeLabel entry.prize
  supplies := entry.contribution.supplies.val

def periodWireOf (rotation : SalvageCrate.RotationEntry) : PeriodWire where
  period := rotation.period.value
  beacon := rotation.beacon
  entry := rotation.entry.map entryWireOf

/-- Eligibility is a membership predicate over the curator-authored roster.  It
is published because a crew member genuinely needs it; the roster itself is
authored content, so this reveals nothing a reader of the content does not
already have. -/
def crewWireOver (crate : SalvageCrate.Config) (key : Digest32) : CrewWire where
  key := key
  eligible := decide (key ∈ crate.raw.eligiblePlayers)
  rotation := (SalvageCrate.generatedRotation crate key).map periodWireOf

/-- The projection, over an ARBITRARY deployment.  The laws below are stated at
this generality deliberately: they are properties of the projection, not of the
station's particular content, so they hold without inheriting that content's
compiled validity check and can be pinned with the stronger `#assert_axioms`. -/
def replyOver (crate : SalvageCrate.Config) (panel : ShipInstrumentPanel.Panel)
    (state : ShipInstrumentPanel.State) (request : Request) : Reply where
  federationId := panel.raw.federationId
  contentSession := panel.raw.contentSession
  contentEpoch := panel.raw.contentEpoch.value
  gauges := (state.face panel).map gaugeWireOf
  recoveredKinds := state.recovered.card
  observed := state.observed.card
  admitted := state.admitted
  opensAt := crate.raw.opensAt.value
  closesAt := crate.raw.closesAt.value
  tableRows := crate.raw.table.length
  ticketCount := (SalvageCrate.ticketEntries crate.raw).length
  crew := request.crew.map (crewWireOver crate)

abbrev crewWireOf : Digest32 → CrewWire := crewWireOver stationCrate

abbrev replyFor : ShipInstrumentPanel.State → Request → Reply :=
  replyOver stationCrate stationPanel

/-- ⭐ The whole read: replay the node's log, then project.  `none` is the
fail-closed refusal — an unreplayable log never renders as an unmoved ship. -/
def readOver (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (request : Request) : Option Reply :=
  (servedStateOver config deployment request.history).map
    (fun state => replyOver config deployment state request)

abbrev readFor : Request → Option Reply := readOver stationCrate stationPanel

def readBytes? (bytes : String) : Option String := do
  let request ← decodeRequest bytes
  let reply ← readFor request
  some reply.toJson

/-- **`@[export dregg_poa_station_daily_read]`** — the station daily READ
boundary.  `""` is the fail-closed refusal sentinel, as in every other PoA
export; every accepted result is the canonical `POA-STATION-DAILY-OUT-1` JSON
this module emitted itself.

This export confers no authority and CANNOT WRITE.  ⚠ Not for the reason this
docblock used to give — `SalvageCrate.CurrentStateCapability` is NOT opaque and
`openCrate` IS reachable, and this export reaches it, once per log row, during
the replay.  It cannot write because it returns a DOCUMENT and nothing else:
every `OpenResult` the replay produces is consumed by the fold and dropped, no
row is appended (only `node/src/poa_crate_api.rs` appends, and only on an
accepted open), and the caller gets a projection.  Handing it a log it did not
earn buys nothing: a row the crate would not have accepted in that position makes
the whole replay `none`, and the reply is the `""` refusal.

It is a pure function of the bytes it is handed and of Lean-authored content. -/
@[export dregg_poa_station_daily_read]
def stationDailyReadFFI (bytes : String) : String := (readBytes? bytes).getD ""

/-! ## The seal, stated generally

None of the theorems in this section mentions a concrete document, so they are
`rfl`/`simp` and `#assert_axioms`-clean. -/

/-- Accepted bytes are the bytes this module would have written. -/
theorem decodeRequest_reencodes {bytes : String} {request : Request}
    (accepted : decodeRequest bytes = some request) : request.toJson = bytes := by
  simp only [decodeRequest, decodeRequestWithLimit] at accepted
  split at accepted
  · exact NetworkJudgeWire.canonicalDecode_reencodes parseRequestJson Request.toJson accepted
  · contradiction

/-- A second canonical spelling of one request does not merely get rejected
later — it does not exist. -/
theorem decodeRequest_accepted_bytes_injective {left right : String} {request : Request}
    (hleft : decodeRequest left = some request)
    (hright : decodeRequest right = some request) : left = right := by
  rw [← decodeRequest_reencodes hleft, ← decodeRequest_reencodes hright]

theorem decodeRequest_refuses_oversized {bytes : String}
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeRequest bytes = none := by
  simp [decodeRequest, decodeRequestWithLimit, Nat.not_le.mpr oversized]

/-- A wire the seal refuses gets the refusal sentinel and nothing else. -/
theorem stationDailyReadFFI_refuses_uncanonical {bytes : String}
    (refused : decodeRequest bytes = none) : stationDailyReadFFI bytes = "" := by
  simp [stationDailyReadFFI, readBytes?, refused]

/-! ## What the served document is -/

/-- ⭐ The wire twin of `the_face_does_not_record_who_opened`.  Substituting ANY
request leaves every communal field of the served document bit-identical, for
EVERY deployment and EVERY state — so a reader learns nothing about who opened
the crate, because the document does not depend on it.  This is the reason the
route may be unauthenticated. -/
theorem the_served_panel_does_not_depend_on_the_crew
    (crate : SalvageCrate.Config) (panel : ShipInstrumentPanel.Panel)
    (state : ShipInstrumentPanel.State) (left right : Request) :
    (replyOver crate panel state left).gauges = (replyOver crate panel state right).gauges ∧
    (replyOver crate panel state left).recoveredKinds =
      (replyOver crate panel state right).recoveredKinds ∧
    (replyOver crate panel state left).observed = (replyOver crate panel state right).observed ∧
    (replyOver crate panel state left).admitted = (replyOver crate panel state right).admitted ∧
    (replyOver crate panel state left).federationId =
      (replyOver crate panel state right).federationId ∧
    (replyOver crate panel state left).contentSession =
      (replyOver crate panel state right).contentSession :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐ The rotation this module publishes IS `SalvageCrate.generatedRotation` of
the deployed config — the function the crate's own docblock hands to players
deliberately.  No adapter, projection or runtime chose any of these draws. -/
theorem the_served_rotation_is_the_crate_rotation
    (crate : SalvageCrate.Config) (key : Digest32) :
    (crewWireOver crate key).rotation =
      (SalvageCrate.generatedRotation crate key).map periodWireOf := rfl

/-- ⭐ The periods and beacons served are exactly the curator-authored schedule,
for every deployment and every crew key.  Nothing derived from a secret reaches
this wire — there is no such value in the import cone. -/
theorem the_served_beacons_are_the_authored_schedule
    (crate : SalvageCrate.Config) (key : Digest32) :
    (crewWireOver crate key).rotation.map (fun period => (period.period, period.beacon)) =
      crate.raw.beacons.map (fun beacon => (beacon.period.value, beacon.value)) := by
  simp [crewWireOver, SalvageCrate.generatedRotation, periodWireOf, List.map_map,
    Function.comp_def]

/-- ⭐ The only field of the served document that can name a crew member is
`crew` itself.  Erasing it from a named-crew document yields, bit for bit, the
document an anonymous caller receives — so serving one player does not change
the ship anyone else sees. -/
theorem naming_a_crew_member_changes_only_the_crew_member
    (crate : SalvageCrate.Config) (panel : ShipInstrumentPanel.Panel)
    (state : ShipInstrumentPanel.State) (request : Request) :
    { replyOver crate panel state request with crew := none } =
      replyOver crate panel state { request with crew := none } := rfl

/-- ⭐ THE FAIL-CLOSED HALF.  A log this crate could not have produced yields NO
DOCUMENT, for every deployment — not a document reporting the installed ship.
The two are the difference between "this node's log is broken" and "nobody has
opened the crate yet", and a player cannot tell those apart by looking. -/
theorem the_read_refuses_a_log_it_cannot_replay
    (crate : SalvageCrate.Config) (panel : ShipInstrumentPanel.Panel) (request : Request)
    (unreplayable : replayOver crate panel request.history = none) :
    readOver crate panel request = none := by
  simp [readOver, servedStateOver, unreplayable]

/-- ⭐ The ship the read serves is the fold of the log and nothing else: for every
deployment and every request that produces a document at all, the gauges,
recovered kinds, observations and admissions are read off `servedStateOver`.
There is no branch on which this module invents a reading. -/
theorem the_served_ship_is_the_folded_log
    (crate : SalvageCrate.Config) (panel : ShipInstrumentPanel.Panel) (request : Request)
    (state : ShipInstrumentPanel.State)
    (folded : servedStateOver crate panel request.history = some state) :
    readOver crate panel request = some (replyOver crate panel state request) := by
  simp [readOver, folded]

/-! ## THE GATE, RE-STATED SO IT CAN FIRE

⚠ `the_served_ship_has_not_been_moved` is RETIRED, not renamed.  It asserted one
dial at zero with nothing observed or admitted, and its docblock called it "the
assertion that goes RED the day a judged opening can be folded in".  That day
came on 2026-08-07 and it stayed GREEN, because it was never a claim about
reachability: `Request` had no `history` field, so `servedState` was
`ShipInstrumentPanel.initial` **by construction** and no amount of judged
openings could have moved it.  A gate whose subject is a definitional identity
cannot fire.

What replaces it is a PAIR over one deployment, whose two halves differ in
exactly one log row.  The second half is the one that could not previously be
written down, and it is red the moment the fold is removed. -/

/-- The log a node holds after crew 41's accepted open of the installed period —
the row `node/src/poa_crate_api.rs` appends, spelled exactly as it stores it. -/
def theLogAfterOneOpen : List HistoryRow :=
  [{ player := StationCrateOpen.crew41, period := 31 }]

/-- The mutation is present before any reading is taken: the two logs below
really do differ by exactly one row, and it names the crew key and the installed
period.  Without this the pair could be two spellings of the empty log. -/
theorem the_mutation_is_exactly_one_logged_open :
    ([] : List HistoryRow) ≠ theLogAfterOneOpen ∧
    theLogAfterOneOpen.length = 1 ∧
    theLogAfterOneOpen = [{ player := StationCrateOpen.crew41, period := 31 }] := by
  refine ⟨by simp [theLogAfterOneOpen], rfl, rfl⟩

/-- The communal fields a reader takes off the served document for a given log —
hoisted so the gate check below has no `let` inside its `decide`. -/
private def servedSummaryFor (history : List HistoryRow) :
    Option (List GaugeWire × Nat × Nat × Nat) :=
  (readFor { crew := none, history }).map
    (fun reply => (reply.gauges, reply.recoveredKinds, reply.observed, reply.admitted))

/-- ⭐ THE SERVED SHIP MOVES WHEN THE LOG RECORDS AN OPENING.  Same deployment,
same anonymous request, one row of difference in the node's durable log: the
empty log serves one dial at zero with nothing observed or admitted, and the
one-row log serves supplies 1, one recovered kind, one observation and one
admission.

This is the assertion the retired one claimed to be.  Delete the fold — make
`servedStateOver` ignore its history and answer `ShipInstrumentPanel.initial` —
and the second half goes red immediately, because the two halves would then be
the same document. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_served_ship_moves_when_the_log_records_an_opening : Bool :=
  decide (servedSummaryFor [] =
    some ([{ gauge := 1, meter := "supplies", exactTotal := 0, fullAt := 64,
             shown := 0, atFull := false }], 0, 0, 0)) &&
  decide (servedSummaryFor theLogAfterOneOpen =
    some ([{ gauge := 1, meter := "supplies", exactTotal := 1, fullAt := 64,
             shown := 1, atFull := false }], 1, 1, 1))

/-- ⭐ And the two really are DIFFERENT DOCUMENTS on the wire, byte for byte, so
the move is visible to a reader who parses nothing.  A refusal is `""`, so this
cannot be satisfied by declining either one.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_two_logs_serve_different_documents : Bool :=
  decide (stationDailyReadFFI { crew := none, history := [] : Request }.toJson ≠ "") &&
  decide (stationDailyReadFFI
    { crew := none, history := theLogAfterOneOpen : Request }.toJson ≠ "") &&
  decide (stationDailyReadFFI { crew := none, history := [] : Request }.toJson ≠
    stationDailyReadFFI { crew := none, history := theLogAfterOneOpen : Request }.toJson)

/-- ⭐ A log that is not one this crate could have produced is REFUSED, and the
honest pole above shows the same wire shape does serve a document — so this is
the replay guard firing rather than the transport failing.  `period 32` is not
the period the crate is at, and a row is never silently re-dated.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_a_log_row_from_another_period_is_refused : Bool :=
  decide (stationDailyReadFFI
    { crew := none,
      history := [{ player := StationCrateOpen.crew41, period := 32 }] : Request }.toJson = "") &&
  decide (stationDailyReadFFI
    { crew := none,
      history := [{ player := SalvageCrateExamples.digest 77,
                    period := 31 }] : Request }.toJson = "")

/-! ## Executable fixture and hostile paths -/

def anonymousRequest : Request := { crew := none, history := [] }

def officerRequest : Request := { crew := some SalvageCrateExamples.officer, history := [] }

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_anonymous_request_round_trips : Bool :=
  decide (decodeRequest anonymousRequest.toJson = some anonymousRequest)

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_officer_request_round_trips : Bool :=
  decide (decodeRequest officerRequest.toJson = some officerRequest)

/-- The export really emits a document for both spellings; a refusal is `""`, so
this cannot be satisfied by declining. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_both_requests_are_served : Bool :=
  decide (stationDailyReadFFI anonymousRequest.toJson ≠ "") &&
  decide (stationDailyReadFFI officerRequest.toJson ≠ "")

/-- The authored officer is on the curator's roster and their whole rotation is
served: three authored periods, every one of them with a drawn row.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_officer_is_eligible_and_draws_every_authored_period : Bool :=
  (crewWireOf SalvageCrateExamples.officer).eligible &&
  decide ((crewWireOf SalvageCrateExamples.officer).rotation.length =
    stationCrate.raw.beacons.length) &&
  (crewWireOf SalvageCrateExamples.officer).rotation.all
    (fun period => period.entry.isSome)

/-! ### Hostile wires, each refused -/

/-- An extra field — the shape an attempt to smuggle a streak or an attendance
count would take. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_unknown_field_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"history\":[],\"streak\":3}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_transposed_keys_refuse : Bool :=
  decide (stationDailyReadFFI
    "{\"crew\":null,\"format\":\"POA-STATION-DAILY-1\",\"history\":[]}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_wrong_format_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-OUT-1\",\"crew\":null,\"history\":[]}" = "")

/-- `false` is not a spelling of "absent". (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_boolean_crew_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":false,\"history\":[]}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_short_digest_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":\"00\",\"history\":[]}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_trailing_byte_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"history\":[]} " = "")

/-- ⚠ THE OLD REQUEST SHAPE REFUSES TO LOAD.  `{"format":…,"crew":null}` was the
whole request until this module grew the log, and it is now a MISSING FIELD
rather than a request with an implicitly empty history.  A wire that defaulted it
would serve the installed ship to every caller of the old shape — which is
precisely the silent zero this change exists to remove.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_pre_history_request_shape_refuses : Bool :=
  decide (stationDailyReadFFI "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null}" = "")

/-- A log row carrying its own counter — the field the fold DERIVES — is not a
row this wire has a spelling for. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_row_with_a_counter_refuses : Bool :=
  decide (stationDailyReadFFI
    ("{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"history\":[{\"player\":\"" ++
      Emit.bytes32Hex StationCrateOpen.crew41 ++
      "\",\"period\":31,\"counter\":0}]}") = "")

/-! ## The pins, split honestly

Everything about the PROJECTION and the SEAL is kernel-clean and gets the strong
pin.  Everything about the STATION's particular authored content inherits that
content's `configValidB`/`panelValidB` compiled evaluation — which is a
compiled-evaluator fact and is labelled as one, exactly as `SlotDeriveRuntime`
splits its sponge theorems.

⚑ **THE FIXTURE PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).**  This module is in
the `Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made
every game-fixture regression a hard failure of every Rust proving target.  Every fixture
theorem above is now an evaluation-free `check_* : Bool` definition; the EVALUATION — each
`check_* = true`, pinned by `native_decide` + `#assert_compiled` — lives in
`StationDailyRuntimeFixtures.lean`, rooted in the `PathOfAngelsGuards` library.  A plain
`lake build` still runs every pin; `lake build Dregg2.FFI` never does.  This module keeps
NO `native_decide` residue: its panel proof is `StationCrateOpen.panel_valid`, cited by
name, and the general seal/projection laws stay kernel-clean below. -/

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_accepted_bytes_injective
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms the_served_panel_does_not_depend_on_the_crew
#assert_axioms the_served_rotation_is_the_crate_rotation
#assert_axioms the_served_beacons_are_the_authored_schedule
#assert_axioms naming_a_crew_member_changes_only_the_crew_member
#assert_axioms the_read_refuses_a_log_it_cannot_replay
#assert_axioms the_served_ship_is_the_folded_log
#assert_axioms the_mutation_is_exactly_one_logged_open
#assert_compiled the_panel_and_the_crate_are_one_deployment
#assert_compiled stationDailyReadFFI_refuses_uncanonical
#assert_compiled station_panel_valid

-- The sixteen fixture pins (`#assert_compiled` + `native_decide`) live in
-- `StationDailyRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the header above.

end Dregg2.Games.PathOfAngels.StationDailyRuntime
