/-
# StationDailyRuntime — the READ boundary for the station's daily ritual

Substrate note: this is Lean-authored game semantics behind a canonical byte
wire.  Nothing here is an AIR, a constraint system or a gadget.  Rust carries
bytes to this module and back; it computes nothing.

PLATFORM-ROADMAP §7.3 pairs two rows, and both already exist and are proved:
`SalvageCrate` is the ritual and `ShipInstrumentPanel` is what the ritual moves.
Neither had an `@[export]`, so no reader could see either one.  This module is
that export, and it is deliberately a READ ONLY.

## ⚠ CORRECTED 2026-08-07 — the write path exists now, and this READ does not see it

Everything under this heading used to say the write path was "unreachable by
type": that `SalvageCrate.CurrentStateCapability` was `opaque` with no producer
anywhere in the tree, so no `@[export]` could ever reach `openCrate`.  **That is
false at HEAD.**  The capability is a sealed structure with a `private`
constructor and two producers — `SalvageCrate.genesis` (the one-time install) and
the successor an ACCEPTED open hands back — `StationCrateOpen` composes them with
`ShipInstrumentPanel.observe`, and `StationCrateOpenRuntime` exports the whole
ceremony as `dregg_poa_crate_open`.  A player can open the crate.

What is still true, and is the reason this module is unchanged:

* `SalvageCrate.openCore` is `private`, so no module outside `SalvageCrate` can
  call it.
* `ShipInstrumentPanel.Receipt` has a private `mk` whose only producer is
  `ofSalvageOpen`, which consumes an accepted `SalvageCrate.OpenReceipt`.

That second point still decides this module's shape.  A wire that decoded JSON
into a `Receipt` would be a public constructor for the sealed type, and any
caller could then post a contribution the crate never authorized and move the
ship.  So **this wire carries no receipts.**

⚑ But the reason `servedState` is `ShipInstrumentPanel.initial` is now a
DIFFERENT reason, and a weaker one.  It is no longer "no accepted opening can
exist"; it is "**this request carries no open history, so this read has nothing
to fold**".  The accepted openings are real and they live in the node's durable
open log, which `StationCrateOpenRuntime` replays; `POA-STATION-DAILY-1` has no
field for that log, so the ship this read serves is the installed one while the
ship the write path publishes has moved.

`the_served_ship_has_not_been_moved` is therefore no longer an assertion about
REACHABILITY — it is an assertion about this request type, and it did NOT go red
when the write path landed, because nothing here consumes the log.  Closing the
gap is a change to the station READ's wire (`history`), its FFI arm and
`node/src/poa_station_api.rs`, i.e. to the station-wiring surface rather than to
this module alone.  Until that lands, a reader of `/api/poa/station/…/panel`
sees the installed ship and a caller of the crate-open route sees the moved one,
and the two disagree.

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

    {"format":"POA-STATION-DAILY-1","crew":null}
    {"format":"POA-STATION-DAILY-1","crew":"<64 lowercase hex>"}

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
`dregg-lean-ffi/src/poa_station_daily_ffi.rs`; the request is a format tag and at
most one digest, so this is a malformed-caller guard and not a semantic bound. -/
abbrev WIRE_BYTE_LIMIT : Nat := 16 * 1024

/-! ## The authored station

The crate is reused; only the panel deployment is authored here. -/

/-- The authored three-period rotation.  `SalvageCrateExamples` already proves
`configValidB` of it, so this is a reference and not a second config. -/
abbrev stationCrate : SalvageCrate.Config := SalvageCrateExamples.config

/-- ⭐ Every authored row leaves four of the five meters at zero, so the panel
below authors exactly one dial.  A second dial would be one that provably cannot
move — this theorem is the reason there is not one. -/
theorem the_authored_table_moves_only_supplies :
    stationCrate.raw.table.all (fun entry =>
      decide (entry.contribution.intel = 0) &&
      decide (entry.contribution.cohesion = 0) &&
      decide (entry.contribution.influence = 0) &&
      decide (entry.contribution.score = 0)) = true := by
  native_decide

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

/-- The ship as installed.  ⚠ This is the only state this module can reach
because **its request carries no open history to fold**, NOT because no accepted
opening can exist — accepted openings exist and `StationCrateOpenRuntime` serves
them.  Folding them here means giving `Request` a `history` field, which is a
change to the station-wiring surface (this wire, its FFI arm and
`node/src/poa_station_api.rs`) rather than to this definition. -/
def servedState : ShipInstrumentPanel.State := ShipInstrumentPanel.initial stationPanel

/-! ## The two wire records -/

structure Request where
  crew : Option Digest32
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

def Request.toJson (request : Request) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"crew\":" ++
      (match request.crew with
       | none => "null"
       | some key => jsonString (Emit.bytes32Hex key)) ++ "}"

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

private def parseRequestJson (j : Json) : Except String Request := do
  exactKeys j ["format", "crew"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong station-daily request format"
  pure { crew := ← objectOptDigest j "crew" }

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

def readBytes? (bytes : String) : Option String := do
  let request ← decodeRequest bytes
  some (replyFor servedState request).toJson

/-- **`@[export dregg_poa_station_daily_read]`** — the station daily READ
boundary.  `""` is the fail-closed refusal sentinel, as in every other PoA
export; every accepted result is the canonical `POA-STATION-DAILY-OUT-1` JSON
this module emitted itself.

This export confers no authority, reads no node state, and CANNOT WRITE: there
is no argument by which a caller reaches `SalvageCrate.openCrate`, whose
capability is `opaque`.  It is a pure function of the bytes it is handed and of
Lean-authored content. -/
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
      replyOver crate panel state { crew := none } := rfl

/-- ⭐ THE READ-PATH GAP, as a theorem rather than as a caveat.  The served ship
has not been moved: one dial, reading exactly zero, nothing observed, nothing
admitted, no salvage kinds recovered.

⚠ CORRECTED 2026-08-07.  This used to be labelled "honest today because no
accepted opening can exist … the assertion that will go RED the day one can".
An accepted opening CAN exist now — `StationCrateOpenRuntime` publishes moved
ships — and this did **not** go red, because it was never an assertion about
reachability.  It is an assertion about THIS REQUEST TYPE: `Request` has no
`history` field, so `servedState` has nothing to fold and is `initial` by
construction.  What would make it red is giving this wire the log, which is the
named station-wiring work.  Read as a reachability claim it was a gate that could
not fire. -/
theorem the_served_ship_has_not_been_moved :
    (replyFor servedState { crew := none }).gauges =
      [{ gauge := 1, meter := "supplies", exactTotal := 0, fullAt := 64,
         shown := 0, atFull := false }] ∧
    (replyFor servedState { crew := none }).observed = 0 ∧
    (replyFor servedState { crew := none }).admitted = 0 ∧
    (replyFor servedState { crew := none }).recoveredKinds = 0 := by
  native_decide

/-! ## Executable fixture and hostile paths -/

def anonymousRequest : Request := { crew := none }

def officerRequest : Request := { crew := some SalvageCrateExamples.officer }

theorem anonymous_request_round_trips :
    decodeRequest anonymousRequest.toJson = some anonymousRequest := by
  native_decide

theorem officer_request_round_trips :
    decodeRequest officerRequest.toJson = some officerRequest := by
  native_decide

/-- The export really emits a document for both spellings; a refusal is `""`, so
this cannot be satisfied by declining. -/
theorem both_requests_are_served :
    stationDailyReadFFI anonymousRequest.toJson ≠ "" ∧
    stationDailyReadFFI officerRequest.toJson ≠ "" := by
  native_decide

/-- The authored officer is on the curator's roster and their whole rotation is
served: three authored periods, every one of them with a drawn row. -/
theorem the_officer_is_eligible_and_draws_every_authored_period :
    (crewWireOf SalvageCrateExamples.officer).eligible = true ∧
    (crewWireOf SalvageCrateExamples.officer).rotation.length =
      stationCrate.raw.beacons.length ∧
    (crewWireOf SalvageCrateExamples.officer).rotation.all
      (fun period => period.entry.isSome) = true := by
  native_decide

/-! ### Hostile wires, each refused -/

/-- An extra field — the shape an attempt to smuggle a streak or an attendance
count would take. -/
theorem hostile_unknown_field_refuses :
    stationDailyReadFFI
      "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"streak\":3}" = "" := by
  native_decide

theorem hostile_transposed_keys_refuse :
    stationDailyReadFFI
      "{\"crew\":null,\"format\":\"POA-STATION-DAILY-1\"}" = "" := by
  native_decide

theorem hostile_wrong_format_refuses :
    stationDailyReadFFI
      "{\"format\":\"POA-STATION-DAILY-OUT-1\",\"crew\":null}" = "" := by
  native_decide

/-- `false` is not a spelling of "absent". -/
theorem hostile_boolean_crew_refuses :
    stationDailyReadFFI
      "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":false}" = "" := by
  native_decide

theorem hostile_short_digest_refuses :
    stationDailyReadFFI
      "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":\"00\"}" = "" := by
  native_decide

theorem hostile_trailing_byte_refuses :
    stationDailyReadFFI
      "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null} " = "" := by
  native_decide

/-! ## The pins, split honestly

Everything about the PROJECTION and the SEAL is kernel-clean and gets the strong
pin.  Everything about the STATION's particular authored content inherits that
content's `configValidB`/`panelValidB` compiled evaluation — which is a
compiled-evaluator fact and is labelled as one, exactly as `SlotDeriveRuntime`
splits its sponge theorems. -/

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_accepted_bytes_injective
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms the_served_panel_does_not_depend_on_the_crew
#assert_axioms the_served_rotation_is_the_crate_rotation
#assert_axioms the_served_beacons_are_the_authored_schedule
#assert_axioms naming_a_crew_member_changes_only_the_crew_member
#assert_compiled the_panel_and_the_crate_are_one_deployment
#assert_compiled stationDailyReadFFI_refuses_uncanonical
#assert_compiled the_authored_table_moves_only_supplies
#assert_compiled station_panel_valid
#assert_compiled the_served_ship_has_not_been_moved
#assert_compiled anonymous_request_round_trips
#assert_compiled officer_request_round_trips
#assert_compiled both_requests_are_served
#assert_compiled the_officer_is_eligible_and_draws_every_authored_period
#assert_compiled hostile_unknown_field_refuses
#assert_compiled hostile_transposed_keys_refuse
#assert_compiled hostile_wrong_format_refuses
#assert_compiled hostile_boolean_crew_refuses
#assert_compiled hostile_short_digest_refuses
#assert_compiled hostile_trailing_byte_refuses

end Dregg2.Games.PathOfAngels.StationDailyRuntime
