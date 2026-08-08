/-
# Vent Crawl — the POAG1 wire

Substrate note: this module renders bytes.  It authors no game semantics.  Every
verdict, successor, refusal reason and hazard numerator below is read out of
`Dregg2.Games.PathOfAngels.VentCrawl`, and `ventCrawlTableRefinesKernel` parses
the RENDERED bytes back and compares all 102 rows against `VentCrawl.rowFor`.
There is no second model of the crawl in this repository.

## Why this is not `Emit.lean`

`Emit.lean` and `EmitMain.lean` are held by the emit-authority lane this cycle,
and `DeckDescentEmit` set the precedent one game earlier: a new descriptor gets
its own module and states its splice rather than performing it inside a file
another lane is editing.  The handover is at the bottom of this file.

## What the descriptor carries, and what it cannot

The day's vein is THREE hidden bits and the descriptor names none of them.  What it
names instead is:

* the **hazard, in full** — `flood_below` per rung against `faces`, so a client
  can print the exact odds of the rung a crawler is about to enter and the exact
  odds of the one after it.  There is nothing hidden on the risk side and the
  descriptor is where that becomes checkable;
* the **whole vein family** — all eight yield ladders, so a client can show what
  each still-possible day would pay for the next rung;
* a **wager row per crawl** naming the flood successor and ONE SUCCESSOR PER
  STILL-POSSIBLE VEIN (`VentCrawl.step_lands_in_the_named_successors`).

⚑ The top-level block is called `vent`.  It must NOT be called `rules` or
`shaft`: `scripts/poa-design-gate.py` dispatches its backend on document SHAPE,
and those two keys route to the deduction and descent backends respectively.

⚑ It also must not become a place to put the day.  Everything in it is true on
all eight veins.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.VentCrawl
import Dregg2.Games.PathOfAngels.EmitJson
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.VentCrawlEmit

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EmitJson
open Dregg2.Games.PathOfAngels.VentCrawl

/-! ## The rows -/

/-- One emitted `(state, action)` row.  `row` is `VentCrawl.rowFor` applied to the
pair and is never recomputed by a second rule here. -/
structure VentRow where
  state : VentCrawl.State
  action : VentCrawl.Action
  row : VentCrawl.Row

def ventStates : List VentCrawl.State := VentCrawl.parametricStates

def ventActions : List VentCrawl.Action := VentCrawl.allActions

def ventRows : List VentRow :=
  ventStates.flatMap fun s =>
    ventActions.map fun a => { state := s, action := a, row := VentCrawl.rowFor s a }

/-! ## Rendering -/

private def veinListJson (vs : List VentCrawl.Vein) : String :=
  jsonArray (vs.map fun v => jsonString v.tag)

/-- The state view.  Everything the rules read is here — that is the property the
design gate's differential depends on, and `ventCrawlViewsRefineKernel` below is
the check that it holds.

`still_possible` is published deliberately.  It is a function of `depth` and
`carried` alone (`VentCrawl.consistentVeins`), so it reveals nothing a client
could not compute; without it a client cannot show a crawler which days are still
on the table, which is the entire read of the game. -/
private def stateJson (s : VentCrawl.State) : String :=
  "    {\"id\":" ++ jsonString (VentCrawl.stateId s) ++
    ",\"terminal\":" ++ jsonBool s.over ++
    ",\"view\":{\"depth\":" ++ toString s.depth ++
    ",\"carried\":" ++ toString s.carried ++
    ",\"outcome\":" ++ jsonString s.outcome.tag ++
    ",\"banked\":" ++ jsonBool (VentCrawl.solvedB s) ++
    ",\"drowned\":" ++ jsonBool (VentCrawl.drownedB s) ++
    ",\"still_possible\":" ++
      veinListJson (VentCrawl.consistentVeins s.depth s.carried) ++
    ",\"next_rung\":" ++ toString (s.depth + 1) ++
    ",\"next_flood_below\":" ++ toString (VentCrawl.floodBelow (s.depth + 1)) ++
    ",\"solved\":" ++ jsonBool (VentCrawl.solvedB s) ++ "}}"

private def actionJson (a : VentCrawl.Action) : String :=
  "    {\"id\":" ++ jsonString a.tag ++
    ",\"label\":" ++ jsonString a.label ++ "}"

private def haulJson (h : VentCrawl.Vein × VentCrawl.State) : String :=
  "{\"vein\":" ++ jsonString h.1.tag ++
    ",\"next\":" ++ jsonString (VentCrawl.stateId h.2) ++ "}"

/-- A row.  `refuse` carries a named reason and no successor; `accept` is the
bank, which consults nothing; `wager` is the crawl, which carries the PUBLIC
odds, the flood successor, and one successor per still-possible vein.

⚠ `flood_below` is the numerator the kernel's transition actually compares
against — `VentCrawl.the_wager_publishes_the_real_odds` — and not a second table
that happens to agree today. -/
private def transitionJson (t : VentRow) : String :=
  let stateId := jsonString (VentCrawl.stateId t.state)
  let actionId := jsonString t.action.tag
  let head :=
    "    {\"state\":" ++ stateId ++ ",\"action\":" ++ actionId ++ ",\"verdict\":"
  match t.row with
  | .refuse reason =>
      head ++ "\"refuse\",\"reason\":" ++ jsonString reason ++
        ",\"next\":null,\"flood_below\":null,\"on_flood\":null,\"hauls\":null}"
  | .advance next =>
      head ++ "\"accept\",\"reason\":null,\"next\":" ++
        jsonString (VentCrawl.stateId next) ++
        ",\"flood_below\":null,\"on_flood\":null,\"hauls\":null}"
  | .wager floodBelow onFlood hauls =>
      head ++ "\"wager\",\"reason\":null,\"next\":null,\"flood_below\":" ++
        toString floodBelow ++ ",\"on_flood\":" ++
        jsonString (VentCrawl.stateId onFlood) ++ ",\"hauls\":" ++
        jsonArray (hauls.map haulJson) ++ "}"

/-! ### The vent — the public rules, true on all eight veins -/

private def floodLadderJson : String :=
  jsonArray ((List.range VentCrawl.DEPTH_CAP).map fun i =>
    "[" ++ toString (i + 1) ++ "," ++ toString (VentCrawl.floodBelow (i + 1)) ++ "]")

private def veinJson (v : VentCrawl.Vein) : String :=
  "      {\"id\":" ++ jsonString v.tag ++
    ",\"yields\":" ++ jsonArray ((List.range VentCrawl.DEPTH_CAP).map fun i =>
      toString (v.yieldAt (i + 1))) ++
    ",\"carry\":" ++ jsonArray ((List.range (VentCrawl.DEPTH_CAP + 1)).map fun i =>
      toString (v.carriedAt i)) ++ "}"

/-- ⚑ The MAP ladders, as numbers rather than as the word `"depth"`.

A descriptor that says `{"drowned":{"intel":"depth"}}` has told a reader the
shape of the consolation and told a TOOL nothing: `scripts/poa-design-gate.py`
rebuilds every posture's payoff from the emitted bytes, and a posture that values
the map had to be given the rule in the gate's own source — which is a second
model of this payout and exactly the thing this file exists not to have.  So the
ladders are rendered from `VentCrawl.mapBanked` and `VentCrawl.mapDrowned`,
indexed by depth `0 … DEPTH_CAP`, and the gate reads them.

The discount is what makes the crawl a wager for a crawler who is paid in map;
`VentCrawl.the_map_that_drowns_is_never_worth_more` is the kernel side of it. -/
private def mapLadderJson (f : Nat → Nat) : String :=
  jsonArray ((List.range (VentCrawl.DEPTH_CAP + 1)).map fun i => toString (f i))

private def ventJson (mapBanked mapDrowned : Nat → Nat) : String :=
  "{\"depth_cap\":" ++ toString VentCrawl.DEPTH_CAP ++
  ",\"faces\":" ++ toString VentCrawl.FACES ++
  ",\"mouth_salvage\":" ++ toString VentCrawl.MOUTH_SALVAGE ++
  ",\"initial_depth\":" ++ toString VentCrawl.initialState.depth ++
  ",\"flood_below\":" ++ floodLadderJson ++
  ",\"veins\":" ++ jsonPrettyArray (VentCrawl.allVeins.map veinJson) ++
  ",\"vein_scope\":\"per-slot-shared\"" ++
  ",\"tape_scope\":\"per-player\"" ++
  ",\"bank_rule\":\"a live run may always bank; a crawl is refused at the depth cap\"" ++
  ",\"flood_effect\":{\"carried\":0,\"depth\":\"+1\",\"outcome\":\"drowned\"}" ++
  ",\"payout\":{\"banked\":{\"supplies\":\"carried\",\"score\":\"carried\"," ++
    "\"intel\":\"map_banked[depth]\",\"relic_at_depth_cap\":true}," ++
    "\"drowned\":{\"intel\":\"map_drowned[depth]\"}," ++
    "\"map_banked\":" ++ mapLadderJson mapBanked ++
    ",\"map_drowned\":" ++ mapLadderJson mapDrowned ++ "}" ++
  ",\"refusal_vocabulary\":" ++
    jsonArray (VentCrawl.declaredReasons.map jsonString) ++
  ",\"reserve\":\"none — the shaft is the clock: every accepted action goes one \
rung deeper or ends the run, so an accepted transcript is at most depth_cap \
actions long\"}"

/-! ## The descriptor -/

/-- The whole document, parameterised by the state list, the row list AND the two
map ladders so that a HOSTILE variant goes through the SAME renderer as the
honest one.  A falsifier built any other way tests a second encoder. -/
def descriptorFrom (states : List VentCrawl.State) (rows : List VentRow)
    (mapBanked mapDrowned : Nat → Nat) : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"vent-crawl\",\n" ++
  "  \"ruleset\":\"push-your-luck-v1\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.VentCrawl\",\n" ++
  "  \"action_limit\":" ++ toString VentCrawl.ACTION_LIMIT ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" (symbolDrawJson "rejection" [8, 8, 8, 8, 8, 8]) ++ ",\n" ++
  "  \"vent\":" ++ ventJson mapBanked mapDrowned ++ ",\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (VentCrawl.stateId VentCrawl.initialState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map stateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (ventActions.map actionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (rows.map transitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"computed_payout\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

def ventCrawlDescriptorJson : String :=
  descriptorFrom ventStates ventRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-! ## Validation — the key set, exactly -/

def validateVentCrawlDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "vent", "state_machine", "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let vent ← document.getObjVal? "vent"
  exactKeys vent ["depth_cap", "faces", "mouth_salvage", "initial_depth", "flood_below",
    "veins", "vein_scope", "tape_scope", "bank_rule", "flood_effect", "payout",
    "refusal_vocabulary", "reserve"]
  let veins ← (vent.getObjVal? "veins") >>= Json.getArr?
  if veins.size != VentCrawl.allVeins.length then
    throw s!"POAG1 vent-crawl emits {veins.size} veins, expected \
{VentCrawl.allVeins.length}"
  for vein in veins do
    exactKeys vein ["id", "yields", "carry"]
  let payout ← vent.getObjVal? "payout"
  exactKeys payout ["banked", "drowned", "map_banked", "map_drowned"]
  for key in ["map_banked", "map_drowned"] do
    let ladder ← (payout.getObjVal? key) >>= Json.getArr?
    if ladder.size != VentCrawl.DEPTH_CAP + 1 then
      throw s!"POAG1 vent-crawl {key} covers {ladder.size} depths, expected \
{VentCrawl.DEPTH_CAP + 1}"
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "states", "actions", "transitions"]
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  if states.size != ventStates.length then
    throw s!"POAG1 vent-crawl emits {states.size} states, expected {ventStates.length}"
  for state in states do
    exactKeys state ["id", "terminal", "view"]
    exactKeys (← state.getObjVal? "view")
      ["depth", "carried", "outcome", "banked", "drowned", "still_possible",
       "next_rung", "next_flood_below", "solved"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  if actions.size != ventActions.length then
    throw s!"POAG1 vent-crawl emits {actions.size} actions, expected {ventActions.length}"
  for action in actions do
    exactKeys action ["id", "label"]
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  if transitions.size != ventStates.length * ventActions.length then
    throw s!"POAG1 vent-crawl emits {transitions.size} rows for \
{ventStates.length} states by {ventActions.length} actions"
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "reason", "next",
      "flood_below", "on_flood", "hauls"]

/-! ## ⚑ The emitted table IS the kernel, row by row -/

private def expectStr (j : Json) (key : String) : Except String String :=
  j.getObjValAs? String key

private def expectNull (j : Json) (key what : String) : Except String Unit := do
  match ← j.getObjVal? key with
  | .null => pure ()
  | _ => throw s!"POAG1 vent-crawl {what} row names a {key}"

private def checkHauls (emitted : Json) (sid aid : String)
    (hauls : List (VentCrawl.Vein × VentCrawl.State)) : Except String Unit := do
  let arr ← (emitted.getObjVal? "hauls") >>= Json.getArr?
  if arr.size != hauls.length then
    throw s!"POAG1 vent-crawl {sid}/{aid} names {arr.size} hauls, kernel has \
{hauls.length}"
  let mut index := 0
  for h in hauls do
    match arr[index]? with
    | none => throw s!"POAG1 vent-crawl {sid}/{aid} has no haul {index}"
    | some entry =>
        exactKeys entry ["vein", "next"]
        if (← expectStr entry "vein") != h.1.tag then
          throw s!"POAG1 vent-crawl {sid}/{aid} haul {index} names another vein"
        if (← expectStr entry "next") != VentCrawl.stateId h.2 then
          throw s!"POAG1 vent-crawl {sid}/{aid} haul {index} names a state the kernel \
did not give"
    index := index + 1

/-- The row the kernel says, checked against the row the bytes carry.  Rows are
compared in emission order AND by the `state`/`action` ids they claim, so a
permuted or relabelled table fails here rather than being read positionally. -/
private def checkRow (emitted : Json) (t : VentRow) : Except String Unit := do
  let sid := VentCrawl.stateId t.state
  let aid := t.action.tag
  if (← expectStr emitted "state") != sid then
    throw s!"POAG1 vent-crawl row claims a state that is not {sid}"
  if (← expectStr emitted "action") != aid then
    throw s!"POAG1 vent-crawl row at {sid} claims an action that is not {aid}"
  let verdict ← expectStr emitted "verdict"
  match t.row with
  | .refuse reason =>
      if verdict != "refuse" then
        throw s!"POAG1 vent-crawl {sid}/{aid} is a refusal and the wire says {verdict}"
      if (← expectStr emitted "reason") != reason then
        throw s!"POAG1 vent-crawl {sid}/{aid} refuses for a reason the kernel did not give"
      if !VentCrawl.declaredReasons.contains reason then
        throw s!"POAG1 vent-crawl {sid}/{aid} refuses for an undeclared reason {reason}"
      expectNull emitted "next" "refusal"
      expectNull emitted "flood_below" "refusal"
      expectNull emitted "on_flood" "refusal"
      expectNull emitted "hauls" "refusal"
  | .advance next =>
      if verdict != "accept" then
        throw s!"POAG1 vent-crawl {sid}/{aid} advances and the wire says {verdict}"
      if (← expectStr emitted "next") != VentCrawl.stateId next then
        throw s!"POAG1 vent-crawl {sid}/{aid} advances into a state the kernel did not name"
      expectNull emitted "reason" "accept"
      expectNull emitted "flood_below" "accept"
      expectNull emitted "on_flood" "accept"
      expectNull emitted "hauls" "accept"
  | .wager floodBelow onFlood hauls =>
      if verdict != "wager" then
        throw s!"POAG1 vent-crawl {sid}/{aid} wagers and the wire says {verdict}"
      if (← emitted.getObjValAs? Nat "flood_below") != floodBelow then
        throw s!"POAG1 vent-crawl {sid}/{aid} publishes odds the kernel does not use"
      if (← expectStr emitted "on_flood") != VentCrawl.stateId onFlood then
        throw s!"POAG1 vent-crawl {sid}/{aid} names an on_flood the kernel did not give"
      if hauls.isEmpty then
        throw s!"POAG1 vent-crawl {sid}/{aid} wagers with no haul at all"
      checkHauls emitted sid aid hauls
      expectNull emitted "reason" "wager"
      expectNull emitted "next" "wager"

/-- Every emitted row, against the kernel.  Takes the bytes so the hostile
variants below run through exactly this checker. -/
def ventCrawlTableRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let machine ← document.getObjVal? "state_machine"
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  let rows := ventRows
  if transitions.size != rows.length then
    throw s!"POAG1 vent-crawl table has {transitions.size} rows, kernel has {rows.length}"
  let mut index := 0
  for t in rows do
    match transitions[index]? with
    | none => throw s!"POAG1 vent-crawl table has no row {index}"
    | some emitted => checkRow emitted t
    index := index + 1

/-- Every emitted state view, against the kernel state it claims to be.  This is
the half the table check cannot see: a table of correct verdicts over views that
misreport the sling or the next rung's odds would still pass above. -/
def ventCrawlViewsRefineKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let machine ← document.getObjVal? "state_machine"
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  if states.size != ventStates.length then
    throw s!"POAG1 vent-crawl emits {states.size} state views, kernel has \
{ventStates.length}"
  let mut index := 0
  for s in ventStates do
    match states[index]? with
    | none => throw s!"POAG1 vent-crawl has no state view {index}"
    | some emitted =>
        if (← expectStr emitted "id") != VentCrawl.stateId s then
          throw s!"POAG1 vent-crawl state view {index} claims another id"
        let view ← emitted.getObjVal? "view"
        if (← view.getObjValAs? Nat "depth") != s.depth then
          throw s!"POAG1 vent-crawl view {index} misreports the depth"
        if (← view.getObjValAs? Nat "carried") != s.carried then
          throw s!"POAG1 vent-crawl view {index} misreports the sling"
        if (← view.getObjValAs? String "outcome") != s.outcome.tag then
          throw s!"POAG1 vent-crawl view {index} misreports the outcome"
        if (← view.getObjValAs? Bool "banked") != VentCrawl.solvedB s then
          throw s!"POAG1 vent-crawl view {index} misreports the bank"
        if (← view.getObjValAs? Bool "drowned") != VentCrawl.drownedB s then
          throw s!"POAG1 vent-crawl view {index} misreports the drowning"
        if (← view.getObjValAs? Nat "next_flood_below")
            != VentCrawl.floodBelow (s.depth + 1) then
          throw s!"POAG1 vent-crawl view {index} misreports the odds of the next rung"
        if (← emitted.getObjValAs? Bool "terminal") != s.over then
          throw s!"POAG1 vent-crawl view {index} misreports terminality"
        let possible ← (view.getObjVal? "still_possible") >>= Json.getArr?
        let mine := VentCrawl.consistentVeins s.depth s.carried
        if possible.size != mine.length then
          throw s!"POAG1 vent-crawl view {index} names {possible.size} still-possible \
veins, kernel has {mine.length}"
        let mut vi := 0
        for v in mine do
          match possible[vi]? with
          | none => throw s!"POAG1 vent-crawl view {index} has no vein {vi}"
          | some entry =>
              if (← entry.getStr?) != v.tag then
                throw s!"POAG1 vent-crawl view {index} names another vein at {vi}"
          vi := vi + 1
    index := index + 1

/-- One map ladder, against the kernel function that renders it. -/
private def checkMapLadder (payout : Json) (key : String) (f : Nat → Nat) :
    Except String Unit := do
  let arr ← (payout.getObjVal? key) >>= Json.getArr?
  if arr.size != VentCrawl.DEPTH_CAP + 1 then
    throw s!"POAG1 vent-crawl {key} covers {arr.size} depths, kernel has \
{VentCrawl.DEPTH_CAP + 1}"
  for i in List.range (VentCrawl.DEPTH_CAP + 1) do
    match arr[i]? with
    | none => throw s!"POAG1 vent-crawl {key} has no entry for depth {i}"
    | some entry =>
        if (← entry.getNat?) != f i then
          throw s!"POAG1 vent-crawl {key} pays a map at depth {i} the kernel does not"

/-- ⚑ **The consolation on the wire IS the consolation the kernel pays.**  This is
the half `ventCrawlTableRefinesKernel` cannot see: the map ladders are not rows,
they are the payout, and `scripts/poa-design-gate.py` derives a whole risk
posture from them.  A descriptor whose `map_drowned` said `depth` where the
kernel pays `depth / 2` would carry a table that is right in every row and a
consolation that makes the deepest crawl a free roll — which is the exact defect
the pricing fixed.  `unpriced_map_is_caught` is that mutation, rendered by this
file's own encoder and refused here. -/
def ventCrawlPayoutRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let vent ← document.getObjVal? "vent"
  let payout ← vent.getObjVal? "payout"
  exactKeys payout ["banked", "drowned", "map_banked", "map_drowned"]
  checkMapLadder payout "map_banked" VentCrawl.mapBanked
  checkMapLadder payout "map_drowned" VentCrawl.mapDrowned

/-! ## ⚠ The falsifiers, built constructively from the live encoder

Each mutant is rendered by `descriptorFrom` — the SAME function that renders the
honest bytes — from a deliberately wrong row list.  A falsifier that edits a
string it expects to find has, twice in this repository, stopped falsifying when
the string left the fixture.  So each theorem below asserts the mutation HAPPENED
before it reads the verdict. -/

/-- The first wager, flattened into a plain accept on its first haul.  This is a
descriptor that tells a client the next rung is safe and pays a fixed amount:
schema-legal, and a lie about both the water and the day. -/
def flattenedWagerRows : List VentRow :=
  let flatten : VentRow → VentRow := fun t =>
    match t.row with
    | .wager _ _ ((_, n) :: _) => { t with row := .advance n }
    | _ => t
  match ventRows.findIdx? (fun t =>
      match t.row with | .wager _ _ (_ :: _) => true | _ => false) with
  | none => ventRows
  | some i => ventRows.modify i flatten

def flattenedWagerDescriptor : String :=
  descriptorFrom ventStates flattenedWagerRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-- ⚠ A row whose PUBLISHED ODDS are softened while its successors stay right.
This is the mutation the whole design is exposed to: the hazard is the one thing
the descriptor is trusted to state, and a client that renders 1/8 where the
kernel compares against 4/8 has been handed a game with different arithmetic and
identical behaviour on every transcript that does not drown. -/
def softenedOddsRows : List VentRow :=
  let soften : VentRow → VentRow := fun t =>
    match t.row with
    | .wager fb onFlood hauls => { t with row := .wager (fb - 1) onFlood hauls }
    | _ => t
  match ventRows.findIdx? (fun t =>
      match t.row with | .wager fb _ _ => 1 < fb | _ => false) with
  | none => ventRows
  | some i => ventRows.modify i soften

def softenedOddsDescriptor : String :=
  descriptorFrom ventStates softenedOddsRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-- ⚠ A wager that drops one of its hauls — a descriptor that has quietly ruled
out a day that is still on the table.  It is the mutation that would let a
descriptor leak the instance one vein at a time. -/
def prunedHaulRows : List VentRow :=
  let prune : VentRow → VentRow := fun t =>
    match t.row with
    | .wager fb onFlood hauls => { t with row := .wager fb onFlood hauls.tail }
    | _ => t
  match ventRows.findIdx? (fun t =>
      match t.row with | .wager _ _ hauls => 1 < hauls.length | _ => false) with
  | none => ventRows
  | some i => ventRows.modify i prune

def prunedHaulDescriptor : String :=
  descriptorFrom ventStates prunedHaulRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-- One row short.  Catches a table that is no longer total. -/
def truncatedDescriptor : String :=
  descriptorFrom ventStates ventRows.tail VentCrawl.mapBanked VentCrawl.mapDrowned

/-- ⚠ **The consolation, unpriced** — a descriptor that pays a drowned run the
WHOLE map instead of half of it.  Every row is right, every state view is right,
the schema is exact, and the game it describes has a free roll in it: a crawler
paid in map is never punished for going deeper, so one of the two verbs is
strictly better everywhere and there is no wager.  This is the mutation the
design gate's `posture-with-no-tradeoff` found in the real descriptor, rendered
here so the check that catches it cannot quietly stop catching it. -/
def unpricedMapDescriptor : String :=
  descriptorFrom ventStates ventRows VentCrawl.mapBanked VentCrawl.mapBanked

/-! ## The pins -/

theorem ventCrawlDescriptor_exact_schema :
    validateVentCrawlDescriptor ventCrawlDescriptorJson = .ok () := by
  native_decide

theorem ventCrawlDescriptor_table_is_the_kernel :
    ventCrawlTableRefinesKernel ventCrawlDescriptorJson = .ok () := by
  native_decide

theorem ventCrawlDescriptor_views_are_the_kernel :
    ventCrawlViewsRefineKernel ventCrawlDescriptorJson = .ok () := by
  native_decide

theorem ventCrawlDescriptor_payout_is_the_kernel :
    ventCrawlPayoutRefinesKernel ventCrawlDescriptorJson = .ok () := by
  native_decide

/-- ⚠ **The unpriced consolation is caught, and every other check passes it.**
The three conjuncts in the middle are the point: the mutation is schema-legal and
its table and views are byte-identical to the honest ones, so nothing but the
payout check can see it.  A wire that carried it would hand the design gate a
posture with no tradeoff and hand a player a crawl with no downside. -/
theorem unpriced_map_is_caught :
    unpricedMapDescriptor ≠ ventCrawlDescriptorJson ∧
    validateVentCrawlDescriptor unpricedMapDescriptor = .ok () ∧
    ventCrawlTableRefinesKernel unpricedMapDescriptor = .ok () ∧
    ventCrawlViewsRefineKernel unpricedMapDescriptor = .ok () ∧
    ventCrawlPayoutRefinesKernel unpricedMapDescriptor ≠ .ok () := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- ⚠ The mutation happened, and it is caught.  The first conjunct is the guard
against a falsifier that stopped falsifying: without it, a `flattenedWagerRows`
that found no wager would emit the honest bytes and this theorem would report a
working adversary while testing nothing. -/
theorem flattened_wager_is_caught :
    flattenedWagerDescriptor ≠ ventCrawlDescriptorJson ∧
    ventCrawlTableRefinesKernel flattenedWagerDescriptor ≠ .ok () := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

/-- ⚠ **The published odds are checked, not decorative.**  Softening one
numerator by one changes no successor and no verdict, and it is still caught. -/
theorem softened_odds_are_caught :
    softenedOddsDescriptor ≠ ventCrawlDescriptorJson ∧
    validateVentCrawlDescriptor softenedOddsDescriptor = .ok () ∧
    ventCrawlTableRefinesKernel softenedOddsDescriptor ≠ .ok () := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

theorem pruned_haul_is_caught :
    prunedHaulDescriptor ≠ ventCrawlDescriptorJson ∧
    ventCrawlTableRefinesKernel prunedHaulDescriptor ≠ .ok () := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

theorem truncated_table_is_caught :
    truncatedDescriptor ≠ ventCrawlDescriptorJson ∧
    validateVentCrawlDescriptor truncatedDescriptor ≠ .ok () ∧
    ventCrawlTableRefinesKernel truncatedDescriptor ≠ .ok () := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

#assert_compiled ventCrawlDescriptor_exact_schema
#assert_compiled ventCrawlDescriptor_table_is_the_kernel
#assert_compiled ventCrawlDescriptor_views_are_the_kernel
#assert_compiled ventCrawlDescriptor_payout_is_the_kernel
#assert_compiled flattened_wager_is_caught
#assert_compiled softened_odds_are_caught
#assert_compiled pruned_haul_is_caught
#assert_compiled truncated_table_is_caught
#assert_compiled unpriced_map_is_caught

/-! ## Handover — what has to be spliced, and by whom

Nothing below is performed here.  `Emit.lean`, `EmitMain.lean`, `poa/artifacts/`
and the mission-cap arithmetic belong to other lanes this cycle.

1. **`EmitMain.lean`** (emit-authority lane): `import
   Dregg2.Games.PathOfAngels.VentCrawlEmit` and, in `emitDescriptors`,
   `writeAtomic (dir / "games" / "vent-crawl.json")
   VentCrawlEmit.ventCrawlDescriptorJson`.  Until then
   `VentCrawlEmitMain.lean` writes the same bytes to a pending directory.

2. **`EmitJson.lean`** (no owner): NO new helper is needed.  This module uses
   `jsonString`, `jsonArray`, `jsonPrettyArray`, `jsonBool`, `exactKeys`,
   `validateInstanceDeclaration` and `validateHiddenSecurity` exactly as they
   stand.  ⚑ The one thing worth adding, and it is a convergence not a
   requirement: `jsonNat`, since three modules now write `toString n` inline.

3. **`scripts/check-poag1-artifacts.sh`** (curator act): add
   `games/vent-crawl.json` to `content_paths` and `expected`.  ⚑ This changes
   `content_root_sha`, so the manifest bytes change and the curator signature
   must be re-taken.  That is a rebuild, not a migration.

4. **`lakefile.toml`**: `PathOfAngelsGuards` must root
   `Dregg2.Games.PathOfAngels.VentCrawl`, `…VentCrawlEmit` and
   `…VentCrawlEmitMain`, or 58 `#assert_axioms` and 23 `#assert_compiled` run in
   no CI target.  ✅ DONE by this lane — a new module orphaned on arrival is
   exactly the wound that list exists to catch.

5. ⚑ **`scripts/poa-design-gate.baseline.json`** must gain any accepted
   `vent-crawl/*` findings IN THE SAME COMMIT that moves this descriptor into
   `poa/artifacts/poag1/games/`.  Measured on the descent lane one day earlier,
   both directions exit 1: baseline entries for a game the gate cannot see are
   VANISHED entries, and a game the gate can see with no entries raises UNKNOWN
   findings.

6. **`poa-web/`** (suite-rack lane): `ventcrawl-runtime.js` and
   `ventcrawl-controller.js` are written and self-contained.  The rack card and
   `mission-catalog.js` are the rack lane's; this lane touched neither.
-/

end Dregg2.Games.PathOfAngels.VentCrawlEmit
