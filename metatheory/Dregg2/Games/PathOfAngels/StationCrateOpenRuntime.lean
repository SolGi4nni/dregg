/-
# StationCrateOpenRuntime — the WRITE boundary for the station's daily ritual

Substrate note: this is Lean-authored game semantics behind a canonical byte
wire.  Nothing here is an AIR, a constraint system or a gadget.  Rust carries
bytes to this module and back; it computes nothing.

`StationDailyRuntime` is the station's READ and says of itself that the write
path is "unreachable by type".  That was true when it was written and it is not
true now: `SalvageCrate.CurrentStateCapability` is a sealed structure with a
`private` constructor and two producers — `genesis` (the one-time install) and
the successor an ACCEPTED open hands back — so `openCrate` is reachable through
a genesis-rooted chain of accepted transitions.  `StationCrateOpen` composes
that chain with `ShipInstrumentPanel.observe` and proves both poles on real
crate output.  What was still missing was transport: no `@[export]`, so no
player could reach it.  **This module is that transport.**

## What the caller authors: identity and intent, and nothing else

The request carries a crew key and the node's durable open log.  It carries no
seed, no beacon, no date, no ticket index, no entry, no contribution, no
counter, no sequence number and no state.  Every one of those is DERIVED here:

* the **period** is `rolled.state.currentPeriod` — read off the crate state the
  replay produced, never off the wire.  A caller cannot ask for a different day.
* the **sequence** is the log's length, and the **player counter** is the number
  of times that crew key already appears in the log.  Both are positions in the
  log, so a caller who edits either edits the log itself — and the log then
  fails to replay (`history-refused`).
* the **entry**, its **contribution** and the moved gauges come from the crate's
  own accepted `OpenResult` and the panel's own `observe`.  This module chooses
  no number that any reader sees.

## ⚑ The node's log IS the replay authority, and that is a real assumption

`SalvageCrate`'s append-only `consumed` set is what refuses a second open of one
period, and this module reconstructs that set by replaying the log from
`genesis`.  So the replay guard is exactly as strong as the log:
`the_replay_guard_is_exactly_as_strong_as_the_node_log` states both halves as one
theorem — the same crew key, the same period, ACCEPTED when the log is empty and
REFUSED when the log contains the prior open.  A node that loses, truncates or
declines to append to its log re-opens the crate.  That is not a defect this
module can close from inside; it is the property the storage side must carry,
and it is written down here rather than left to be discovered.

## ⚠ The current period is the INSTALLED period, because nothing advances it

`SalvageCrate.advancePeriod` exists and is capability-gated, but no finality
adapter calls it, so `genesis`-rooted replay leaves `currentPeriod` at
`genesisPeriod` — the first authored beacon — forever.  This transport therefore
opens the installed day and only the installed day.  It is deliberately NOT
patched by letting the request name a period: that would hand the caller the one
value the crate uses to key replay.  The finality leg is named work, not a
caveat: until it lands, one crew key opens the crate exactly once.

A log row still carries its period, because the replay needs it to rebuild the
envelope the crate accepted, and because a row that names any other period must
be refused rather than silently re-dated
(`a_log_row_from_another_period_refuses`).

## The panel is the station's ONE panel

`ShipInstrumentPanel.observe` is called on `StationCrateOpen.panel`, which is the
same object `StationDailyRuntime.stationPanel` now abbreviates.  There is one
panel deployment, not two that agree today.

## The wire

Request (`POA-CRATE-OPEN-1`), key order pinned by `Request.toJson`:

    {"format":"POA-CRATE-OPEN-1","opener":"<64 lowercase hex>",
     "history":[{"player":"<64 lowercase hex>","period":n},…]}

Reply (`POA-CRATE-OPEN-OUT-1`):

    {"format":"POA-CRATE-OPEN-OUT-1",
     "federation_id":"<hex>","content_session":"<hex>","content_epoch":n,
     "opener":"<hex>","period":null|n,
     "opened":true,"refusal":null,
     "entry":{"id":n,"prize":"…","supplies":n},
     "panel":{"gauges":[{"gauge":n,"meter":"supplies","exact_total":n,
                         "full_at":n,"shown":n,"at_full":false}],
              "recovered_kinds":n,"observed":n,"admitted":n}}

    {"format":"POA-CRATE-OPEN-OUT-1", … ,
     "opened":false,"refusal":"already-opened-this-period",
     "entry":null,"panel":null}

A refused document carries **no gauge and no entry**
(`a_refused_open_publishes_no_gauge_and_no_entry`), so a reader can never mistake
a refusal for a move that happened to add zero.

Acceptance is `NetworkJudgeWire.canonicalDecode` — the same seal
`decodeSignalInput`, `dregg_poa_signal_slot_derive` and the station READ use,
imported rather than re-typed.  An unknown field, a missing field, a transposed
key, an uppercase hex digit, a trailing byte or a re-spelled integer all fail the
re-encode comparison and the export returns `""`.

The gauge and entry projections are `StationDailyRuntime`'s own
(`gaugeWireOf` / `entryWireOf` / `meterLabel` / `prizeLabel`), imported rather
than re-typed, so the ship a writer sees and the ship a reader sees are spelled
by one function.

## Cost

Replay is a fold over the log: one `openCrate` and one `observe` per row, and the
player counter is a count over the prefix, so the whole request is quadratic in
the log length.  `MAX_HISTORY_ROWS` is the panel's own `MAX_OBSERVED` (4096) —
beyond it `ShipInstrumentPanel.observe` refuses anyway, so this bound removes no
reachable behaviour.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.NetworkJudgeWire
import Dregg2.Games.PathOfAngels.StationCrateOpen
import Dregg2.Games.PathOfAngels.StationDailyRuntime
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.StationCrateOpenRuntime

open Lean (Json)
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-CRATE-OPEN-1"
abbrev OUTPUT_FORMAT : String := "POA-CRATE-OPEN-OUT-1"

/-- Outer allocation fuse.  Mirrors `MAX_POA_CRATE_OPEN_WIRE_BYTES` in
`dregg-lean-ffi/src/poa_crate_open_ffi.rs`.  A full 4096-row log spells to about
390 KB, so this is a malformed-caller guard and not a semantic bound. -/
abbrev WIRE_BYTE_LIMIT : Nat := 1024 * 1024

/-- The log bound, and the period fuse — both `StationDailyRuntime`'s, because
both wires carry the same log and a second bound is a second thing to drift. -/
abbrev MAX_HISTORY_ROWS : Nat := StationDailyRuntime.MAX_HISTORY_ROWS

abbrev PERIOD_LIMIT : Nat := StationDailyRuntime.PERIOD_LIMIT

/-! ## The deployment — one crate, one panel, both already authored -/

abbrev crate : SalvageCrate.Config := StationCrateOpen.crate
abbrev panel : ShipInstrumentPanel.Panel := StationCrateOpen.panel

/-! ## The two wire records -/

/-! ⚑ ONE LOG ROW TYPE, ONE SPELLING, ONE FOLD.  `HistoryRow` and the whole
replay (`priorOpens`, `envelopeOfRow`, `envelopesOfHistory`, `replayOver`) were
authored HERE and now live in `StationDailyRuntime`, which this module imports,
because the station READ folds the same log.  A read that replayed it by its own
arithmetic would be a second fold — two shapes that agree today and disagree the
first time either grows a field.  These are aliases, not a re-typing: the
`export` below makes the names resolve, and the objects are the same objects. -/

abbrev HistoryRow := StationDailyRuntime.HistoryRow
abbrev priorOpens := StationDailyRuntime.priorOpens
abbrev envelopeOfRow := StationDailyRuntime.envelopeOfRow
abbrev envelopesOfHistory := StationDailyRuntime.envelopesOfHistory
abbrev replayOver := StationDailyRuntime.replayOver

structure Request where
  opener : Digest32
  history : List HistoryRow
deriving DecidableEq

/-- The communal ship, exactly the aggregate the station READ publishes.  There
is no per-player field here for the same reason there is none in
`ShipInstrumentPanel.State`: there is no such state. -/
structure PanelWire where
  gauges : List StationDailyRuntime.GaugeWire
  recoveredKinds : Nat
  observed : Nat
  admitted : Nat
deriving DecidableEq

/-- Why the crate or the panel declined.  Every constructor is fired by a
theorem at the bottom of this file. -/
inductive Refusal where
  /-- The opener is not on the curator's roster. -/
  | ineligibleCrew
  /-- The opener already consumed the current period, per the node's own log. -/
  | alreadyOpenedThisPeriod
  /-- The crate declined for some other reason (counter exhaustion, capacity). -/
  | crateRefused
  /-- The node's log is not a log this crate could have produced. -/
  | historyRefused
  /-- The crate accepted and the panel declined the receipt. -/
  | panelRefused
deriving Repr, DecidableEq

def Refusal.label : Refusal → String
  | .ineligibleCrew => "ineligible-crew"
  | .alreadyOpenedThisPeriod => "already-opened-this-period"
  | .crateRefused => "crate-refused"
  | .historyRefused => "history-refused"
  | .panelRefused => "panel-refused"

/-- The verdict is a SUM, not a record with nullable fields, so "refused" and
"moved the ship" cannot both be readable off one document.  The encoder below
spells a refusal with `entry` and `panel` null, and that is forced by the type
rather than promised by a comment. -/
inductive Verdict where
  | opened (entry : StationDailyRuntime.EntryWire) (panel : PanelWire)
  | refused (why : Refusal)
deriving DecidableEq

def Verdict.openedB : Verdict → Bool
  | .opened _ _ => true
  | .refused _ => false

/-- The encoder reads the drawn row and the moved ship through these two
accessors and nowhere else, so "a refusal publishes no gauge" is a property of
`Verdict` rather than of the encoder's discipline. -/
def Verdict.entryWire? : Verdict → Option StationDailyRuntime.EntryWire
  | .opened entry _ => some entry
  | .refused _ => none

def Verdict.panelWire? : Verdict → Option PanelWire
  | .opened _ moved => some moved
  | .refused _ => none

def Verdict.refusalLabel? : Verdict → Option String
  | .opened _ _ => none
  | .refused why => some why.label

/-- Every field is the authored deployment identity, the opener the caller named,
the period the CRATE decided, or the crate's own accepted output. -/
structure Reply where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  opener : Digest32
  /-- `none` exactly when the node's log did not replay, in which case there is
  no crate state to read a current period off and none is invented. -/
  period : Option Nat
  verdict : Verdict
deriving DecidableEq

/-! ## Encoders — canonical by construction, key order pinned here -/

private def jsonString (s : String) : String := String.quote s

private def jsonBool (b : Bool) : String := if b then "true" else "false"

private def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

/-- The row spelling is `StationDailyRuntime.HistoryRow.toJson` — the SAME
function the station read's request uses, so the node cannot spell its own log
two ways on two wires. -/
def Request.toJson (request : Request) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"opener\":" ++ jsonString (Emit.bytes32Hex request.opener) ++
    ",\"history\":" ++
      jsonArray (request.history.map StationDailyRuntime.HistoryRow.toJson) ++ "}"

def PanelWire.toJson (wire : PanelWire) : String :=
  "{\"gauges\":" ++ jsonArray (wire.gauges.map StationDailyRuntime.GaugeWire.toJson) ++
    ",\"recovered_kinds\":" ++ toString wire.recoveredKinds ++
    ",\"observed\":" ++ toString wire.observed ++
    ",\"admitted\":" ++ toString wire.admitted ++ "}"

def Reply.toJson (reply : Reply) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex reply.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex reply.contentSession) ++
    ",\"content_epoch\":" ++ toString reply.contentEpoch ++
    ",\"opener\":" ++ jsonString (Emit.bytes32Hex reply.opener) ++
    ",\"period\":" ++ (match reply.period with
                       | none => "null"
                       | some value => toString value) ++
    ",\"opened\":" ++ jsonBool reply.verdict.openedB ++
    ",\"refusal\":" ++ (match reply.verdict.refusalLabel? with
                        | none => "null"
                        | some label => jsonString label) ++
    ",\"entry\":" ++ (match reply.verdict.entryWire? with
                      | none => "null"
                      | some entry => entry.toJson) ++
    ",\"panel\":" ++ (match reply.verdict.panelWire? with
                      | none => "null"
                      | some moved => moved.toJson) ++ "}"

/-! ## Strict parse

The accessors are the same shape as `NetworkJudgeWire`'s and
`StationDailyRuntime`'s private ones; the SEAL (`canonicalDecode`) is imported
rather than re-typed, which is the part that could drift meaningfully. -/

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then
    pure ()
  else
    throw "missing or unknown field"

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
  pure { player := ← objectDigest j "player",
         period := ← objectNat j "period" PERIOD_LIMIT : HistoryRow }

private def parseHistory (j : Json) : Except String (List HistoryRow) := do
  let values := (← j.getArr?).toList
  if values.length > MAX_HISTORY_ROWS then throw "open history exceeds wire bound"
  values.mapM parseHistoryRow

private def parseRequestJson (j : Json) : Except String Request := do
  exactKeys j ["format", "opener", "history"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong crate-open request format"
  pure { opener := ← objectDigest j "opener",
         history := ← parseHistory (← j.getObjVal? "history") }

def decodeRequestWithLimit (byteLimit : Nat) (bytes : String) : Option Request :=
  if bytes.length ≤ byteLimit then
    NetworkJudgeWire.canonicalDecode parseRequestJson Request.toJson bytes
  else none

def decodeRequest (bytes : String) : Option Request :=
  decodeRequestWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The ceremony, over an ARBITRARY deployment

The envelope builder is `StationCrateOpen.envFor` — the SAME one the two proved
poles use, so those poles witness the envelopes this transport actually submits
rather than a re-typed lookalike.

Everything here is parameterized by `(config, deployment)` deliberately: the
document laws below are properties of the CEREMONY, not of the station's
particular content, so they hold for every deployment and can carry the strong
`#assert_axioms` pin instead of inheriting this content's compiled
`configValidB`/`panelValidB` evaluation. -/

/-- The envelope for the NEW open: the opener the caller named, the period the
crate state is at, and the counter/sequence the log determines. -/
def newEnvelope (config : SalvageCrate.Config) (history : List HistoryRow) (opener : Digest32)
    (rolled : StationCrateOpen.Rolled config) : SalvageCrate.OpenEnvelope :=
  let previous := priorOpens history opener
  StationCrateOpen.envFor config opener rolled.state.currentPeriod previous (previous + 1)
    history.length

/-- Why the crate declined — read ONLY on a path where `openCrate` has already
returned `none`, so this is a diagnosis of a refusal and never a gate.  Both
tested conditions are reads of the crate's own authored roster and its own
append-only `consumed` set through its own `openKey`, not a re-derivation of its
transition rule. -/
def diagnose (config : SalvageCrate.Config) (rolled : StationCrateOpen.Rolled config)
    (opener : Digest32) : Refusal :=
  if opener ∉ config.raw.eligiblePlayers then .ineligibleCrew
  else if SalvageCrate.openKey config rolled.state.currentPeriod opener ∈ rolled.state.consumed then
    .alreadyOpenedThisPeriod
  else .crateRefused

def panelWireOf (deployment : ShipInstrumentPanel.Panel) (moved : ShipInstrumentPanel.State) :
    PanelWire where
  gauges := (moved.face deployment).map StationDailyRuntime.gaugeWireOf
  recoveredKinds := moved.recovered.card
  observed := moved.observed.card
  admitted := moved.admitted

private def replyWith (deployment : ShipInstrumentPanel.Panel) (opener : Digest32)
    (period : Option Nat) (verdict : Verdict) : Reply where
  federationId := deployment.raw.federationId
  contentSession := deployment.raw.contentSession
  contentEpoch := deployment.raw.contentEpoch.value
  opener := opener
  period := period
  verdict := verdict

/-- ⭐ The whole ceremony: replay the node's log from `genesis`, append the
caller's open, fold the crate's own receipt into the panel, and publish the moved
ship.  Every refusal on the way out carries a tag and no gauge. -/
def openOver (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (request : Request) : Reply :=
  match replayOver config deployment request.history with
  | none => replyWith deployment request.opener none (.refused .historyRefused)
  | some rolled =>
      match SalvageCrate.openCrate config rolled.state rolled.capability
              (newEnvelope config request.history request.opener rolled) with
      | none =>
          replyWith deployment request.opener (some rolled.state.currentPeriod.value)
            (.refused (diagnose config rolled request.opener))
      | some result =>
          match ShipInstrumentPanel.observe deployment rolled.panel
                  (ShipInstrumentPanel.ofSalvageOpen result.receipt) with
          | .error _ =>
              replyWith deployment request.opener (some rolled.state.currentPeriod.value)
                (.refused .panelRefused)
          | .ok moved =>
              replyWith deployment request.opener (some rolled.state.currentPeriod.value)
                (.opened (StationDailyRuntime.entryWireOf result.entry)
                  (panelWireOf deployment moved))

/-- The station's own deployment. -/
abbrev openFor : Request → Reply := openOver crate panel

def openBytes? (bytes : String) : Option String := do
  let request ← decodeRequest bytes
  some (openFor request).toJson

/-- **`@[export dregg_poa_crate_open]`** — the station crate-open WRITE
boundary.  `""` is the fail-closed refusal sentinel, as in every other PoA
export; every accepted result is the canonical `POA-CRATE-OPEN-OUT-1` JSON this
module emitted itself, and a document with `"opened":false` is a REFUSAL that
carries no gauge.

This export confers no authority the crate did not already grant.  It cannot
mint a receipt (`ShipInstrumentPanel.Receipt.mk` and `SalvageCrate.OpenReceipt.mk`
are private), cannot mint a capability (`CurrentStateCapability.mk` is private and
its only producers are `genesis` and an accepted transition's successor), and
cannot choose a draw, a period, a counter or a contribution — every one of those
is derived from the authored deployment and the node's log. -/
@[export dregg_poa_crate_open]
def crateOpenFFI (bytes : String) : String := (openBytes? bytes).getD ""

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
theorem crateOpenFFI_refuses_uncanonical {bytes : String}
    (refused : decodeRequest bytes = none) : crateOpenFFI bytes = "" := by
  simp [crateOpenFFI, openBytes?, refused]

/-! ## What a document can and cannot carry

Every theorem here is about the CEREMONY, for every crate and every panel, so
none of them inherits the station content's compiled validity evaluation. -/

/-- ⭐ A REFUSAL CARRIES NO GAUGE AND NO ENTRY — so a reader can never mistake
"the crate declined" for "the crate moved the ship by zero".  The encoder reads
`entry` and `panel` through `Verdict.entryWire?` / `Verdict.panelWire?` and
nowhere else, so this is forced by the sum type rather than promised by the
encoder. -/
theorem a_refused_open_publishes_no_gauge_and_no_entry
    (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (request : Request) (why : Refusal)
    (refused : (openOver config deployment request).verdict = .refused why) :
    (openOver config deployment request).verdict.entryWire? = none ∧
    (openOver config deployment request).verdict.panelWire? = none ∧
    (openOver config deployment request).verdict.openedB = false := by
  rw [refused]; exact ⟨rfl, rfl, rfl⟩

/-- ⭐ A PUBLISHED GAUGE IMPLIES AN ACCEPTED OPENING.  If a document carries a
panel at all then the node's log replayed AND the crate itself accepted the new
envelope — the transport has no path that publishes a ship without
`SalvageCrate.openCrate` having said yes.  This is the anti-fabrication
statement, and it is what makes the moved gauges below evidence rather than
decoration. -/
theorem a_published_gauge_implies_an_accepted_opening
    (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (request : Request) (entry : StationDailyRuntime.EntryWire) (moved : PanelWire)
    (opened : (openOver config deployment request).verdict = .opened entry moved) :
    (replayOver config deployment request.history).isSome = true ∧
    ∀ rolled, replayOver config deployment request.history = some rolled →
      (SalvageCrate.openCrate config rolled.state rolled.capability
        (newEnvelope config request.history request.opener rolled)).isSome = true := by
  unfold openOver at opened
  split at opened
  · simp only [replyWith] at opened; cases opened
  · rename_i rolled replayed
    refine ⟨by simp [replayed], ?_⟩
    intro other matched
    rw [replayed] at matched
    cases matched
    split at opened
    · simp only [replyWith] at opened; cases opened
    · rename_i result accepted; simp [accepted]

/-- ⭐ The published deployment identity is the PANEL's, for every request and
every deployment — so a document can never name a federation the ship it reports
does not belong to. -/
theorem the_document_names_the_panel_deployment
    (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (request : Request) :
    (openOver config deployment request).federationId = deployment.raw.federationId ∧
    (openOver config deployment request).contentSession = deployment.raw.contentSession ∧
    (openOver config deployment request).contentEpoch = deployment.raw.contentEpoch.value ∧
    (openOver config deployment request).opener = request.opener := by
  unfold openOver
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩

/-- ⭐ The period a document reports is the crate state's own current period,
never a value from the wire — the `Request` type has no period field at all, and
this says the reply's did not come from one anyway. -/
theorem the_published_period_is_the_crate_state_period
    (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel)
    (request : Request) (rolled : StationCrateOpen.Rolled config)
    (replayed : replayOver config deployment request.history = some rolled) :
    (openOver config deployment request).period = some rolled.state.currentPeriod.value := by
  simp only [openOver, replayed]
  repeat' split
  all_goals rfl

/-! ## The crew, and the two poles on ACTUAL crate output

`StationCrateOpen` already proves, on the same crate and the same panel, that
crew `digest 41` opening the genesis period draws the communal salvage and moves
the supplies gauge by exactly 1.  The requests below drive that same open through
the wire. -/

def crew41 : Digest32 := StationCrateOpen.crew41
def crew40 : Digest32 := StationCrateOpen.crew40
def crew42 : Digest32 := StationCrateOpen.crew42

/-- Not on the curator's roster: `SalvageCrateExamples.raw.eligiblePlayers` is
`{digest 40, digest 41, digest 42}`. -/
def stowaway : Digest32 := SalvageCrateExamples.digest 77

/-- The installed period — the first authored beacon, 31. -/
abbrev INSTALLED_PERIOD : Nat := 31

/-- A crew member arriving at a station whose log is empty. -/
def firstOpen (opener : Digest32) : Request := { opener := opener, history := [] }

/-- The SAME crew member arriving again, at a station whose log records their
earlier open of the same period.  This is the ONLY difference between the two
poles below. -/
def secondOpen (opener : Digest32) : Request :=
  { opener := opener, history := [{ player := opener, period := INSTALLED_PERIOD }] }

/-- The mutation is present before any verdict is read: the log the replay pole
is handed really does record crew 41 consuming period 31, and the honest pole's
log really is empty. -/
theorem the_mutation_is_exactly_one_logged_open :
    (firstOpen crew41).history = [] ∧
    (secondOpen crew41).history = [{ player := crew41, period := INSTALLED_PERIOD }] ∧
    (firstOpen crew41).opener = (secondOpen crew41).opener := ⟨rfl, rfl, rfl⟩

/-- The replay of that one-row log really did reach an accepted state that
consumed period 31 for crew 41 — so the refusal below is a replay guard firing,
not a log that failed to parse. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_logged_open_really_consumed_the_installed_period : Bool :=
  decide (((replayOver crate panel (secondOpen crew41).history).map
    (fun rolled =>
      decide (SalvageCrate.openKey crate ⟨INSTALLED_PERIOD⟩ crew41 ∈ rolled.state.consumed)))
    = some true)

/-- ⭐ THE RITUAL MOVES THE SHIP, THROUGH THE WIRE.  Crew 41 opens the installed
period from an empty log: the document is `opened`, the drawn row is the communal
salvage (loot id 13, one supply), and the published panel reads supplies 1 with
one recovered kind, one observed receipt and one admitted open.  A refusal is a
`.refused` verdict, so this cannot be met by declining.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_an_honest_crate_open_publishes_the_moved_ship : Bool :=
  decide ((openFor (firstOpen crew41)).period = some INSTALLED_PERIOD) &&
  decide ((openFor (firstOpen crew41)).verdict =
    .opened { id := 13, prize := "communal-salvage:55", supplies := 1 }
      { gauges := [{ gauge := 1, meter := "supplies", exactTotal := 1, fullAt := 64,
                     shown := 1, atFull := false }],
        recoveredKinds := 1, observed := 1, admitted := 1 })

/-- ⭐ AND THE SECOND OPEN OF THE SAME PERIOD IS REFUSED, with no gauge.  The
only difference from the pole above is the one log row, and the refusal names the
append-only guard that fired.  Together these two are
`the_replay_guard_is_exactly_as_strong_as_the_node_log`: the node's log is the
whole replay authority, and a node that does not append re-opens the crate.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_a_second_open_of_the_installed_period_is_refused : Bool :=
  decide ((openFor (secondOpen crew41)).period = some INSTALLED_PERIOD) &&
  decide ((openFor (secondOpen crew41)).verdict = .refused .alreadyOpenedThisPeriod)

/-- ⭐ The pair, as one statement, because the pair is the claim.  Same crew key,
same period, same deployment: ACCEPTED against an empty log and REFUSED against a
log that records the earlier open. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_replay_guard_is_exactly_as_strong_as_the_node_log : Bool :=
  (openFor (firstOpen crew41)).verdict.openedB &&
  !(openFor (secondOpen crew41)).verdict.openedB

/-! ### ⭐ THE LOOP, CLOSED

The write publishes a moved ship and the node appends one row.  The station READ
is handed that row and must serve the SAME ship.  Until 2026-08-07 it could not:
`POA-STATION-DAILY-1` had no field for the log, so over HTTP the write served
`exact_total: 1, observed: 2` while `/api/poa/station/…/panel` served
`exact_total: 0, observed: 0`.

The log below is `(secondOpen crew41).history` — not a third spelling of the row,
but the very log the replay pole above is refused against, so this theorem and
that one cannot drift. -/

/-- ⭐ THE READ SERVES THE SHIP THE WRITE PUBLISHED, as one equation between two
whole panels.  Left: the communal fields of the document `/panel` serves for the
log the node now holds.  Right: the panel the accepted open published.  Bit for
bit, one value.

This is red if either half stops folding, if the two folds diverge, or if the
read starts inventing a reading — and it is `Option`-valued on both sides, so it
cannot be satisfied by both of them refusing.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_station_read_serves_the_ship_this_write_published : Bool :=
  decide ((StationDailyRuntime.readFor
      { crew := none, history := (secondOpen crew41).history }).map
    (fun reply =>
      ({ gauges := reply.gauges, recoveredKinds := reply.recoveredKinds,
         observed := reply.observed, admitted := reply.admitted } : PanelWire)) =
    (openFor (firstOpen crew41)).verdict.panelWire?)

/-- ⚠ And it is not vacuous on either side: the write really published a panel
and the read really served a document.  Without this, two `none`s would satisfy
the equation above and the loop would be "closed" by both ends going dark.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_neither_side_of_the_loop_is_a_refusal : Bool :=
  ((openFor (firstOpen crew41)).verdict.panelWire?).isSome &&
  (StationDailyRuntime.readFor
    { crew := none, history := (secondOpen crew41).history }).isSome

/-- An ordinary day through the wire: crew 40 draws a bound record, is `opened`
and admitted, and every gauge reads zero.  Showing up on an ordinary day and not
showing up are the same ship — the roadmap's "missing a day is uninteresting", on
the transport. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_an_ordinary_open_publishes_an_unmoved_ship : Bool :=
  decide ((openFor (firstOpen crew40)).verdict =
    .opened { id := 12, prize := "record:8", supplies := 0 }
      { gauges := [{ gauge := 1, meter := "supplies", exactTotal := 0, fullAt := 64,
                     shown := 0, atFull := false }],
        recoveredKinds := 0, observed := 1, admitted := 1 })

/-- A crew member who is not on the curator's roster is refused by name.  The
honest pole above shows the same empty log DOES admit an eligible crew member, so
this is the roster refusing and not the transport failing.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_an_ineligible_crew_key_is_refused : Bool :=
  decide ((openFor (firstOpen stowaway)).verdict = .refused .ineligibleCrew)

/-- A log row that names a period the crate is not at is refused, and the whole
request with it: the reply carries `period: null` because there is no crate state
to read one off.  A row is never silently re-dated to the current period. -/
def logFromAnotherPeriod : Request :=
  { opener := crew42, history := [{ player := crew41, period := 32 }] }

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_a_log_row_from_another_period_refuses : Bool :=
  decide ((openFor logFromAnotherPeriod).period = none) &&
  decide ((openFor logFromAnotherPeriod).verdict = .refused .historyRefused)

/-- A log row naming a crew key the curator never enrolled is refused the same
way: the log is not one this crate could have produced. -/
def logWithAStowaway : Request :=
  { opener := crew41, history := [{ player := stowaway, period := INSTALLED_PERIOD }] }

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_a_log_row_naming_a_stowaway_refuses : Bool :=
  decide ((openFor logWithAStowaway).verdict = .refused .historyRefused)

/-- ⭐ The communal ship accumulates across the whole crew, and the panel counts
arrivals well enough to keep them apart and never well enough to rank them: after
crew 41 and crew 40 are in the log, crew 42 opening publishes supplies 1 (only
the one salvage draw), one recovered kind, and THREE observed receipts. -/
def theThirdCrewMember : Request :=
  { opener := crew42,
    history := [{ player := crew41, period := INSTALLED_PERIOD },
                { player := crew40, period := INSTALLED_PERIOD }] }

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_published_ship_accumulates_the_whole_crew : Bool :=
  decide ((openFor theThirdCrewMember).verdict =
    .opened { id := 10, prize := "warm-air", supplies := 0 }
      { gauges := [{ gauge := 1, meter := "supplies", exactTotal := 1, fullAt := 64,
                     shown := 1, atFull := false }],
        recoveredKinds := 1, observed := 3, admitted := 3 })

/-! ## Round trips and the export -/

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_first_open_request_round_trips : Bool :=
  decide (decodeRequest (firstOpen crew41).toJson = some (firstOpen crew41))

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_second_open_request_round_trips : Bool :=
  decide (decodeRequest (secondOpen crew41).toJson = some (secondOpen crew41))

/-- ⭐ The export really emits both documents, and they are DIFFERENT bytes: the
move and the refusal are distinguishable on the wire.  A refusal is `""`, so
neither half can be satisfied by declining.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_export_emits_a_move_and_a_refusal : Bool :=
  decide (crateOpenFFI (firstOpen crew41).toJson ≠ "") &&
  decide (crateOpenFFI (secondOpen crew41).toJson ≠ "") &&
  decide (crateOpenFFI (firstOpen crew41).toJson ≠ crateOpenFFI (secondOpen crew41).toJson)

/-! ### Hostile wires, each refused -/

/-- An extra field — the shape an attempt to smuggle a period, a counter or a
contribution would take. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_unknown_field_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[],\"period\":31}") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_transposed_keys_refuse : Bool :=
  decide (crateOpenFFI
    ("{\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"format\":\"POA-CRATE-OPEN-1\",\"history\":[]}") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_wrong_format_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-OUT-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[]}") = "")

/-- A log row carrying its own counter — the field this module DERIVES — is not a
row this wire has a spelling for. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_row_with_a_counter_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[{\"player\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"period\":31,\"counter\":0}]}") = "")

/-- `digest 41` spells as `29…`, which has no letters to case, so the mutation
would be a no-op on it.  `digest 77` spells as `4d…` and really does change.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_uppercase_mutation_is_not_a_no_op : Bool :=
  decide ((Emit.bytes32Hex stowaway).toUpper ≠ Emit.bytes32Hex stowaway)

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_uppercase_digest_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++
      (Emit.bytes32Hex stowaway).toUpper ++ "\",\"history\":[]}") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_trailing_byte_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[]} ") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_empty_wire_refuses : Bool :=
  decide (crateOpenFFI "" = "")

/-! ## The pins, split honestly

Everything about the SEAL and the DOCUMENT SHAPE is kernel-clean and gets the
strong pin.  Everything about the STATION's particular authored content inherits
that content's `configValidB` / `panelValidB` compiled evaluation — which is a
compiled-evaluator fact and is labelled as one.

⚑ **THE FIXTURE PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).**  This module is in
the `Dregg2.FFI` closure — the crypto archive's build; `dregg_poa_crate_open` is exported
from it — and a `native_decide` here made every game-fixture regression a hard failure of
every Rust proving target.  Every fixture theorem above is now an evaluation-free
`check_* : Bool` definition; the EVALUATION — each `check_* = true`, pinned by
`native_decide` + `#assert_compiled` — lives in `StationCrateOpenRuntimeFixtures.lean`,
rooted in the `PathOfAngelsGuards` library.  A plain `lake build` still runs every pin;
`lake build Dregg2.FFI` never does.  This module keeps NO `native_decide` residue: its
deployment is `StationCrateOpen`'s `crate`/`panel`, cited by name, and the general
seal/document laws stay kernel-clean below. -/

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_accepted_bytes_injective
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms a_refused_open_publishes_no_gauge_and_no_entry
#assert_axioms a_published_gauge_implies_an_accepted_opening
#assert_axioms the_document_names_the_panel_deployment
#assert_axioms the_published_period_is_the_crate_state_period
#assert_axioms the_mutation_is_exactly_one_logged_open
#assert_compiled crateOpenFFI_refuses_uncanonical

-- The twenty-two fixture pins (`#assert_compiled` + `native_decide`) live in
-- `StationCrateOpenRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the header above.

end Dregg2.Games.PathOfAngels.StationCrateOpenRuntime
