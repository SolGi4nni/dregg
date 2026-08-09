/-
# Deck Descent — the POAG1 wire

Substrate note: this module renders bytes.  It authors no game semantics.  Every
verdict, successor and refusal reason below is read out of
`Dregg2.Games.PathOfAngels.DeckDescent`, and `descentDescriptorRefinesKernel`
parses the RENDERED bytes back and compares all 17,316 rows against `rowFor`.
There is no second model of the descent in this repository.

## Why this is not `Emit.lean`

`Emit.lean` and `EmitMain.lean` are held by the emit-authority lane this cycle.
The splice this module needs is four lines and it is stated at the bottom of this
file rather than performed in a file another lane is editing.

## What the descriptor carries, and what it cannot

The board is THREE hidden bits — does the mouth flood, does the west spur, does
the east spur — and the descriptor names none of them.  What it names instead is
a table in which every row that consults a bit carries BOTH successors
(`step_is_one_of_the_two_branches`), and a `shaft` block giving the public rules:
the topology, the two budgets, the carrying capacity, the bank target, how many
relics each chamber holds (two on the east spur — the measured junction repair)
and the tie-break the deck uses when a crossing overruns the sling.

⚑ The `shaft` block exists so `scripts/poa-design-gate.py` can rebuild the rule
from the descriptor and check every emitted row against its own reconstruction,
rather than analysing a table it has to take on trust.  It must NOT be called
`rules`: the gate dispatches its backend on document SHAPE, and a top-level
`rules` key routes to the deduction backend.

⚑ It also must not become a place to put the board.  Everything in it is a
statement about the shaft that is true on all eight instances.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.DeckDescent
import Dregg2.Games.PathOfAngels.EmitJson
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.DeckDescentEmit

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EmitJson
open Dregg2.Games.PathOfAngels.DeckDescent

/-! ## The rows -/

/-- One emitted `(state, action)` row.  `row` is `DeckDescent.rowFor` applied to
the pair and is never recomputed by a second rule here. -/
structure DescentRow where
  state : DeckDescent.State
  action : DeckDescent.Action
  row : DeckDescent.Row

def descentStates : List DeckDescent.State := DeckDescent.parametricStates

def descentActions : List DeckDescent.Action := DeckDescent.allActions

def descentRows : List DescentRow :=
  descentStates.flatMap fun s =>
    descentActions.map fun a => { state := s, action := a, row := DeckDescent.rowFor s a }

/-! ## Action metadata

`kind` and `line` are what let a reader rebuild `Action.target` from the shaft
block: a `spur` action reaches the node's spur child, a `main` action its main
child, and a `here` action reaches nothing — it acts where the body stands. -/

def actionKind : DeckDescent.Action → String
  | .survey | .surveyEast => "survey"
  | .shore | .shoreEast => "shore"
  | .descend | .descendEast => "descend"
  | .lift => "lift"
  | .ascend => "ascend"
  | .extract => "extract"

def actionLine : DeckDescent.Action → String
  | .surveyEast | .shoreEast | .descendEast => "spur"
  | .survey | .shore | .descend => "main"
  | .lift | .ascend | .extract => "here"

/-- ⚑ **`line` really does determine the target.**  A client that rebuilds
`Action.target` from the emitted `line` and the emitted child maps gets exactly
the kernel's answer, at every node.  Without this the metadata would be a label
and the gate's reconstruction would be a second rule. -/
theorem line_determines_target (a : DeckDescent.Action) (n : DeckDescent.Node) :
    a.target n =
      (if actionLine a = "spur" then n.eastChild
       else if actionLine a = "main" then n.mainChild
       else none) := by
  cases a <;> rfl

/-! ## Rendering -/

private def chamberListJson (cs : List DeckDescent.Chamber) : String :=
  jsonArray (cs.map fun c => jsonString c.tag)

private def loreJson (d : DeckDescent.Deck) : String :=
  "{" ++ String.intercalate "," (DeckDescent.allChambers.map fun c =>
    jsonString c.tag ++ ":" ++ jsonString (d.get c).lore.tag) ++ "}"

/-- A per-chamber count, as an object.  Counts, not chamber lists: the east spur
holds two relics, so "which chambers" under-describes both the deck and the
sling and the old list shape REFUSES to validate rather than collapsing a
count. -/
private def countMapJson (f : DeckDescent.Chamber → Nat) : String :=
  "{" ++ String.intercalate "," (DeckDescent.allChambers.map fun c =>
    jsonString c.tag ++ ":" ++ toString (f c)) ++ "}"

/-- The state view.  Everything the rules read is here — that is the property the
design gate's differential depends on, and `descentDescriptorRebuildsFromView`
below is the check that it holds.

`doomed` is published deliberately.  It is board-INDEPENDENT (`reachableBankB`
assumes every dark chamber sound, so it is a fact about what the player knows,
not about the draw), and without it a client cannot tell a player their run is
already dead — the exact `doomed-but-open` complaint the gate raises elsewhere. -/
private def stateJson (s : DeckDescent.State) : String :=
  "    {\"id\":" ++ jsonString (DeckDescent.stateId s) ++
    ",\"terminal\":" ++ jsonBool s.banked ++
    ",\"view\":{\"node\":" ++ jsonString s.position.tag ++
    ",\"air\":" ++ toString s.air ++
    ",\"shoring\":" ++ toString s.shoring ++
    ",\"damage\":" ++ toString s.damage ++
    ",\"capacity\":" ++ toString (DeckDescent.capacity s) ++
    ",\"lore\":" ++ loreJson s.deck ++
    ",\"taken\":" ++ countMapJson (fun c => (s.deck.get c).relicsTaken) ++
    ",\"sling\":" ++ countMapJson s.sling.get ++
    ",\"banked\":" ++ jsonBool s.banked ++
    ",\"turns\":" ++ toString (DeckDescent.turnsUsed s) ++
    ",\"doomed\":" ++ jsonBool (DeckDescent.doomedB s) ++
    ",\"solved\":" ++ jsonBool (DeckDescent.solvedB s) ++ "}}"

private def actionJson (a : DeckDescent.Action) : String :=
  "    {\"id\":" ++ jsonString a.tag ++
    ",\"label\":" ++ jsonString a.label ++
    ",\"kind\":" ++ jsonString (actionKind a) ++
    ",\"line\":" ++ jsonString (actionLine a) ++ "}"

/-- A parametric row.  `refuse` carries a named reason and no successor;
`accept` is board-independent and carries one; `resolve` consults one bit and
carries BOTH, so the row states the rule and the judge's bit states the
instance.

⚠ `on_match` is the SOUND reading and `on_mismatch` the FLOODED one, matching
`rowFor`'s `stepWith Lore.sound` / `stepWith Lore.flooded`.  A reader should not
have to take that on trust and does not have to: the two branch views differ in
exactly one chamber's `lore`, and that chamber's value in each branch says which
reading it is. -/
private def transitionJson (t : DescentRow) : String :=
  let stateId := jsonString (DeckDescent.stateId t.state)
  let actionId := jsonString t.action.tag
  let head :=
    "    {\"state\":" ++ stateId ++ ",\"action\":" ++ actionId ++ ",\"verdict\":"
  match t.row with
  | .refuse reason =>
      head ++ "\"refuse\",\"reason\":" ++ jsonString reason ++
        ",\"next\":null,\"on_match\":null,\"on_mismatch\":null}"
  | .advance next =>
      head ++ "\"accept\",\"reason\":null,\"next\":" ++
        jsonString (DeckDescent.stateId next) ++
        ",\"on_match\":null,\"on_mismatch\":null}"
  | .resolve onMatch onMismatch =>
      head ++ "\"resolve\",\"reason\":null,\"next\":null,\"on_match\":" ++
        jsonString (DeckDescent.stateId onMatch) ++
        ",\"on_mismatch\":" ++ jsonString (DeckDescent.stateId onMismatch) ++ "}"

/-! ### The shaft — the public rules, true on all eight boards -/

private def parentJson : String :=
  "{" ++ String.intercalate "," (DeckDescent.allChambers.map fun c =>
    jsonString c.tag ++ ":" ++ jsonString (DeckDescent.Node.inside c).parent.tag) ++ "}"

private def mainChildJson : String :=
  "{" ++ String.intercalate "," (DeckDescent.allNodes.filterMap fun n =>
    match n.mainChild with
    | none => none
    | some c => some (jsonString n.tag ++ ":" ++ jsonString c.tag)) ++ "}"

private def spurChildJson : String :=
  "{" ++ String.intercalate "," (DeckDescent.allNodes.filterMap fun n =>
    match n.eastChild with
    | none => none
    | some c => some (jsonString n.tag ++ ":" ++ jsonString c.tag)) ++ "}"

private def debtJson : String :=
  "{" ++ String.intercalate "," (DeckDescent.allNodes.map fun n =>
    jsonString n.tag ++ ":" ++ toString n.debt) ++ "}"

private def crossingsJson : String :=
  jsonPrettyArray (DeckDescent.allNodes.flatMap fun p =>
    DeckDescent.allNodes.map fun q =>
      "      [" ++ jsonString p.tag ++ "," ++ jsonString q.tag ++ "," ++
        toString (p.dist q) ++ "]")

/-- The tie-break the deck uses when a crossing overruns the sling: it keeps what
the run reached furthest for, west before east because the spurs are equally
deep.  `Sling.forfeit_is_deepest` proves the order respects depth;  the ORDER
ITSELF is a declaration and so it is declared, not left for a reader to infer
from a field ordering. -/
private def forfeitOrderJson : String :=
  jsonArray ([DeckDescent.Chamber.west, .east, .mouth].map fun c => jsonString c.tag)

private def shaftJson : String :=
  "{\"budgets\":{\"air\":" ++ toString DeckDescent.AIR ++
    ",\"shoring\":" ++ toString DeckDescent.SHORING ++
    ",\"base_capacity\":" ++ toString DeckDescent.BASE_CAPACITY ++
    ",\"bank_target\":" ++ toString DeckDescent.BANK_TARGET ++ "}" ++
  ",\"nodes\":" ++ jsonArray (DeckDescent.allNodes.map fun n => jsonString n.tag) ++
  ",\"surface\":\"hatch\"" ++
  ",\"chambers\":" ++ chamberListJson DeckDescent.allChambers ++
  ",\"relic_count\":" ++ countMapJson DeckDescent.Chamber.relicCount ++
  ",\"parent\":" ++ parentJson ++
  ",\"main_child\":" ++ mainChildJson ++
  ",\"spur_child\":" ++ spurChildJson ++
  ",\"crossings_to_hatch\":" ++ debtJson ++
  ",\"crossings\":" ++ crossingsJson ++
  ",\"forfeit_order\":" ++ forfeitOrderJson ++
  ",\"lore\":" ++ jsonArray ((["dark", "sound", "flooded", "shored"] : List String).map
      jsonString) ++
  ",\"damaging_lore\":" ++ jsonArray ([jsonString "flooded"]) ++
  ",\"air_per_action\":1" ++
  ",\"reserve\":\"cheapest ordered collection of the relics still needed - a \
chamber counts once per relic it still holds, one lift per relic - plus the \
extraction, on the most favourable board still consistent with what the run has \
seen\"}"

/-! ### The practice family — all eight boards, and no answer

⚑ **PUBLISHING THE FAMILY IS NOT PUBLISHING THE INSTANCE**, and here the family
was already public before this block existed.  `shaft` names three chambers and
declares `lore` and `damaging_lore`; every `resolve` row names two successors
whose views differ in exactly one chamber's reading, and those two readings ARE
`sound` and `flooded`.  From that alone `scripts/poa-design-gate.py` rebuilds all
eight boards and walks them — it did so before this block was written and reads
nothing from it now.  So the bits are all already there; what this block removes
is the RULE a client would otherwise have to carry ("each chamber is
independently sound or flooded") in order to enumerate them.  A lookup replaces a
second model of the game.

⚠ What it still says nothing about is WHICH board a run drew.  A judged run's
board comes from `HiddenInstance` under purpose tag 1 off a slot secret this
artifact does not contain and could not; a practice run picks a row here, under a
client-chosen index, and is `scored:false` in the block and `mode:"practice"` in
the transcript.  A reader who has not played can reconstruct the eight; nobody
can reconstruct the one. -/
private def boardLoreJson (b : DeckDescent.Board) : String :=
  "{" ++ String.intercalate "," (DeckDescent.allChambers.map fun c =>
    jsonString c.tag ++ ":" ++ jsonString (b.lore c).tag) ++ "}"

private def practiceBoardsJson (boards : List DeckDescent.Board) : String :=
  jsonPrettyArray (boards.map fun b => "      " ++ boardLoreJson b)

/-! ## The descriptor -/

/-- The whole document, parameterised by the state list, the row list and the
practice family so that a HOSTILE variant goes through the SAME renderer as the
honest one.  A falsifier built any other way tests a second encoder. -/
def descriptorFrom (states : List DeckDescent.State) (rows : List DescentRow)
    (boards : List DeckDescent.Board) : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"deck-descent\",\n" ++
  "  \"ruleset\":\"descent-v1\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.DeckDescent\",\n" ++
  "  \"action_limit\":" ++ toString DeckDescent.AIR ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" (symbolDrawJson "rejection" [2, 2, 2]) ++ ",\n" ++
  "  \"shaft\":" ++ shaftJson ++ ",\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++ jsonString (DeckDescent.stateId DeckDescent.initialState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map stateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (descentActions.map actionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (rows.map transitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"practice\":{\"instance_space\":" ++ toString boards.length ++
    ",\"instance_shape\":\"one passage per chamber, sound or flooded\"" ++
    ",\"scored\":false" ++
    ",\"boards\":" ++ practiceBoardsJson boards ++ "},\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

def descentPracticeBoards : List DeckDescent.Board := DeckDescent.boardTable

def deckDescentDescriptorJson : String :=
  descriptorFrom descentStates descentRows descentPracticeBoards

/-! ## Validation — the key set, exactly -/

def validateDescentDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "shaft", "state_machine", "practice",
    "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  let shaft ← document.getObjVal? "shaft"
  exactKeys shaft ["budgets", "nodes", "surface", "chambers", "relic_count",
    "parent", "main_child", "spur_child", "crossings_to_hatch", "crossings",
    "forfeit_order", "lore", "damaging_lore", "air_per_action", "reserve"]
  exactKeys (← shaft.getObjVal? "budgets")
    ["air", "shoring", "base_capacity", "bank_target"]
  let practice ← document.getObjVal? "practice"
  exactKeys practice ["instance_space", "instance_shape", "scored", "boards"]
  if (← practice.getObjValAs? Bool "scored") != false then
    throw "POAG1 descent practice block declares practice runs scored"
  let space ← practice.getObjValAs? Nat "instance_space"
  if space != DeckDescent.boardTable.length then
    throw s!"POAG1 descent practice declares a space of {space}, kernel family is \
{DeckDescent.boardTable.length}"
  let boards ← (practice.getObjVal? "boards") >>= Json.getArr?
  if boards.size != space then
    throw s!"POAG1 descent practice emits {boards.size} boards for a declared space \
of {space}"
  for board in boards do
    exactKeys board (DeckDescent.allChambers.map DeckDescent.Chamber.tag)
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "states", "actions", "transitions"]
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  if states.size != descentStates.length then
    throw s!"POAG1 descent emits {states.size} states, expected {descentStates.length}"
  for state in states do
    exactKeys state ["id", "terminal", "view"]
    exactKeys (← state.getObjVal? "view")
      ["node", "air", "shoring", "damage", "capacity", "lore", "taken", "sling",
       "banked", "turns", "doomed", "solved"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  if actions.size != descentActions.length then
    throw s!"POAG1 descent emits {actions.size} actions, expected {descentActions.length}"
  for action in actions do
    exactKeys action ["id", "label", "kind", "line"]
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  if transitions.size != descentStates.length * descentActions.length then
    throw s!"POAG1 descent emits {transitions.size} rows for \
{descentStates.length} states by {descentActions.length} actions"
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "reason", "next",
      "on_match", "on_mismatch"]

/-! ## ⚑ The emitted table IS the kernel, row by row

This reads the rows back out of the RENDERED bytes — the ones a client actually
fetches — and compares every one against `DeckDescent.rowFor`.  Without it the
descriptor would be an unchecked second statement of the rules, which is the
shape this whole module exists to avoid. -/

private def expectStr (j : Json) (key : String) : Except String String :=
  j.getObjValAs? String key

private def expectNull (j : Json) (key what : String) : Except String Unit := do
  match ← j.getObjVal? key with
  | .null => pure ()
  | _ => throw s!"POAG1 descent {what} row names a {key}"

/-- The row the kernel says, checked against the row the bytes carry.  Rows are
compared in emission order AND by the `state`/`action` ids they claim, so a
permuted or relabelled table fails here rather than being read positionally. -/
private def checkRow (emitted : Json) (t : DescentRow) : Except String Unit := do
  let sid := DeckDescent.stateId t.state
  let aid := t.action.tag
  if (← expectStr emitted "state") != sid then
    throw s!"POAG1 descent row claims a state that is not {sid}"
  if (← expectStr emitted "action") != aid then
    throw s!"POAG1 descent row at {sid} claims an action that is not {aid}"
  let verdict ← expectStr emitted "verdict"
  match t.row with
  | .refuse reason =>
      if verdict != "refuse" then
        throw s!"POAG1 descent {sid}/{aid} is a refusal and the wire says {verdict}"
      if (← expectStr emitted "reason") != reason then
        throw s!"POAG1 descent {sid}/{aid} refuses for a reason the kernel did not give"
      expectNull emitted "next" "refusal"
      expectNull emitted "on_match" "refusal"
      expectNull emitted "on_mismatch" "refusal"
  | .advance next =>
      if verdict != "accept" then
        throw s!"POAG1 descent {sid}/{aid} advances and the wire says {verdict}"
      if (← expectStr emitted "next") != DeckDescent.stateId next then
        throw s!"POAG1 descent {sid}/{aid} advances into a state the kernel did not name"
      expectNull emitted "reason" "accept"
      expectNull emitted "on_match" "accept"
      expectNull emitted "on_mismatch" "accept"
  | .resolve onMatch onMismatch =>
      if verdict != "resolve" then
        throw s!"POAG1 descent {sid}/{aid} resolves and the wire says {verdict}"
      if (← expectStr emitted "on_match") != DeckDescent.stateId onMatch then
        throw s!"POAG1 descent {sid}/{aid} names an on_match the kernel did not give"
      if (← expectStr emitted "on_mismatch") != DeckDescent.stateId onMismatch then
        throw s!"POAG1 descent {sid}/{aid} names an on_mismatch the kernel did not give"
      if onMatch = onMismatch then
        throw s!"POAG1 descent {sid}/{aid} resolves to the same state either way"
      expectNull emitted "reason" "resolve"
      expectNull emitted "next" "resolve"

/-- Every emitted row, against the kernel.  Takes the bytes so the hostile
variants below run through exactly this checker. -/
def descentTableRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let machine ← document.getObjVal? "state_machine"
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  let rows := descentRows
  if transitions.size != rows.length then
    throw s!"POAG1 descent table has {transitions.size} rows, kernel has {rows.length}"
  let mut index := 0
  for t in rows do
    match transitions[index]? with
    | none => throw s!"POAG1 descent table has no row {index}"
    | some emitted => checkRow emitted t
    index := index + 1

/-- Every emitted state view, against the kernel state it claims to be.  This is
the half `descentTableRefinesKernel` cannot see: a table of correct verdicts over
views that misreport the air, the damage or the doom would still pass above. -/
def descentViewsRefineKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let machine ← document.getObjVal? "state_machine"
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  if states.size != descentStates.length then
    throw s!"POAG1 descent emits {states.size} state views, kernel has \
{descentStates.length}"
  let mut index := 0
  for s in descentStates do
    match states[index]? with
    | none => throw s!"POAG1 descent has no state view {index}"
    | some emitted =>
        if (← expectStr emitted "id") != DeckDescent.stateId s then
          throw s!"POAG1 descent state view {index} claims another id"
        let view ← emitted.getObjVal? "view"
        if (← view.getObjValAs? String "node") != s.position.tag then
          throw s!"POAG1 descent view {index} misreports the node"
        if (← view.getObjValAs? Nat "air") != s.air then
          throw s!"POAG1 descent view {index} misreports the air"
        if (← view.getObjValAs? Nat "shoring") != s.shoring then
          throw s!"POAG1 descent view {index} misreports the shoring"
        if (← view.getObjValAs? Nat "damage") != s.damage then
          throw s!"POAG1 descent view {index} misreports the damage"
        if (← view.getObjValAs? Nat "capacity") != DeckDescent.capacity s then
          throw s!"POAG1 descent view {index} misreports the capacity"
        if (← view.getObjValAs? Nat "turns") != DeckDescent.turnsUsed s then
          throw s!"POAG1 descent view {index} misreports the clock"
        if (← view.getObjValAs? Bool "banked") != s.banked then
          throw s!"POAG1 descent view {index} misreports the bank"
        if (← view.getObjValAs? Bool "doomed") != DeckDescent.doomedB s then
          throw s!"POAG1 descent view {index} misreports the doom"
        if (← emitted.getObjValAs? Bool "terminal") != s.banked then
          throw s!"POAG1 descent view {index} misreports terminality"
        let lore ← view.getObjVal? "lore"
        for c in DeckDescent.allChambers do
          if (← lore.getObjValAs? String c.tag) != (s.deck.get c).lore.tag then
            throw s!"POAG1 descent view {index} misreports the lore of {c.tag}"
        let taken ← view.getObjVal? "taken"
        for c in DeckDescent.allChambers do
          if (← taken.getObjValAs? Nat c.tag) != (s.deck.get c).relicsTaken then
            throw s!"POAG1 descent view {index} misreports the relics taken at {c.tag}"
        let sling ← view.getObjVal? "sling"
        for c in DeckDescent.allChambers do
          if (← sling.getObjValAs? Nat c.tag) != s.sling.get c then
            throw s!"POAG1 descent view {index} misreports the sling count for {c.tag}"
    index := index + 1

/-- Every emitted practice board, against `DeckDescent.boardTable`.

Two things are checked and they are not the same thing.  The first is that each
row IS the kernel's board at that index, chamber by chamber — a client answering
its own rehearsal from a row that is not a board of the family would be
rehearsing a game nobody can be dealt.  The second is that the emitted rows are
DISTINCT and there are as many as the kernel has: a family short one member has
told a reader which board is not in play, and a family with a duplicate has told
them one is twice as likely. -/
def descentPracticeRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let practice ← document.getObjVal? "practice"
  let emitted ← (practice.getObjVal? "boards") >>= Json.getArr?
  let kernel := DeckDescent.boardTable
  if emitted.size != kernel.length then
    throw s!"POAG1 descent practice emits {emitted.size} boards, kernel family has \
{kernel.length}"
  let mut index := 0
  let mut seen : List String := []
  for b in kernel do
    match emitted[index]? with
    | none => throw s!"POAG1 descent practice has no board {index}"
    | some row =>
        let mut shape := ""
        for c in DeckDescent.allChambers do
          let emittedLore ← row.getObjValAs? String c.tag
          if emittedLore != (b.lore c).tag then
            throw s!"POAG1 descent practice board {index} reads {c.tag} as \
{emittedLore}, kernel says {(b.lore c).tag}"
          shape := shape ++ emittedLore
        if seen.contains shape then
          throw s!"POAG1 descent practice board {index} repeats a board the family \
already names"
        seen := shape :: seen
    index := index + 1

/-! ## ⚠ The falsifiers, built constructively from the live encoder

Each mutant is rendered by `descriptorFrom` — the SAME function that renders the
honest bytes — from a deliberately wrong row list.  A falsifier that edits a
string it expects to find has, twice in this repository, stopped falsifying when
the string left the fixture: the mutation replaced nothing and the hostile input
equalled the honest one.  So each theorem below asserts the mutation HAPPENED
before it reads the verdict. -/

/-- The first row that consults the instance, flattened into a plain accept on
its sound branch.  Schema-legal — it is a well-formed `accept` row — and wrong,
which is exactly the mutation a schema check cannot catch. -/
def flattenedResolveRows : List DescentRow :=
  let flatten : DescentRow → DescentRow := fun t =>
    match t.row with
    | .resolve m _ => { t with row := .advance m }
    | _ => t
  match descentRows.findIdx? (fun t => match t.row with | .resolve _ _ => true | _ => false) with
  | none => descentRows
  | some i => descentRows.modify i flatten

def flattenedResolveDescriptor : String :=
  descriptorFrom descentStates flattenedResolveRows descentPracticeBoards

/-- One row short.  Catches a table that is no longer total. -/
def truncatedDescriptor : String :=
  descriptorFrom descentStates descentRows.tail descentPracticeBoards

/-- Seven of the eight boards.  ⚠ This is a LEAK and not merely a shortage: a
family missing a member has told every reader which board the run is not playing,
which is one bit of the three the descriptor exists to withhold. -/
def sevenBoardDescriptor : String :=
  descriptorFrom descentStates descentRows (descentPracticeBoards.eraseIdx 3)

/-- Eight boards, one of them a duplicate of another — so the family is seven
distinct instances wearing eight names, and a reader who counts is told that one
board is twice as likely as the rest. -/
def duplicatedBoardDescriptor : String :=
  descriptorFrom descentStates descentRows
    (descentPracticeBoards.set 3
      { mouth := .sound, west := .sound, east := .flooded })

/-! ## The pins

⚑ **THE PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target (the compilation-unit
coupling the stale-fixture outage measured). Each pin's STATEMENT stays here, as an
evaluation-free `check_* : Bool` definition over the live validators and falsifiers (a
`def` body elaborates without running). The EVALUATION — each `check_* = true`, pinned by
`native_decide` + `#assert_compiled` — lives in `DeckDescentEmitFixtures.lean`, rooted in
the `PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale
descriptor reds the guard library instead of the archive.

Named residue: NONE — every pin moved. -/

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_exact_schema : Bool :=
  decide (validateDescentDescriptor deckDescentDescriptorJson = .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_table_is_the_kernel : Bool :=
  decide (descentTableRefinesKernel deckDescentDescriptorJson = .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_views_are_the_kernel : Bool :=
  decide (descentViewsRefineKernel deckDescentDescriptorJson = .ok ())

/-- ⚠ The mutation happened, and it is caught.  The first conjunct is the guard
against a falsifier that stopped falsifying: without it, a `flattenedResolveRows`
that found no resolve row would emit the honest bytes and this check would
report a working adversary while testing nothing.
(Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_flattened_resolve_is_caught : Bool :=
  decide (flattenedResolveDescriptor ≠ deckDescentDescriptorJson) &&
  decide (descentTableRefinesKernel flattenedResolveDescriptor ≠ .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_truncated_table_is_caught : Bool :=
  decide (truncatedDescriptor ≠ deckDescentDescriptorJson) &&
  decide (validateDescentDescriptor truncatedDescriptor ≠ .ok ()) &&
  decide (descentTableRefinesKernel truncatedDescriptor ≠ .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_practice_is_the_kernel : Bool :=
  decide (descentPracticeRefinesKernel deckDescentDescriptorJson = .ok ())

/-- ⚠ A family short one board, caught twice — once by the declared space and
once against the kernel's own table.
(Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_a_missing_board_is_caught : Bool :=
  decide (sevenBoardDescriptor ≠ deckDescentDescriptorJson) &&
  decide (validateDescentDescriptor sevenBoardDescriptor ≠ .ok ()) &&
  decide (descentPracticeRefinesKernel sevenBoardDescriptor ≠ .ok ())

/-- ⚠ The one a count cannot see.  Eight rows, so `instance_space` agrees and the
schema check passes; the family is still wrong, and only a comparison against the
kernel's boards catches it. (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_a_duplicated_board_is_caught : Bool :=
  decide (duplicatedBoardDescriptor ≠ deckDescentDescriptorJson) &&
  decide (validateDescentDescriptor duplicatedBoardDescriptor = .ok ()) &&
  decide (descentPracticeRefinesKernel duplicatedBoardDescriptor ≠ .ok ())

#assert_axioms line_determines_target

-- The eight descriptor pins (`#assert_compiled` + `native_decide`) live in
-- `DeckDescentEmitFixtures.lean`, rooted in `PathOfAngelsGuards` — see the pins
-- header above.

/-! ## Handover — what `Emit.lean` and `EmitMain.lean` must splice

Four edits, all additive except the third:

1. `EmitMain.lean`: `import Dregg2.Games.PathOfAngels.DeckDescentEmit` and, in
   `emitDescriptors`, `writeAtomic (dir / "games" / "deck-descent.json")
   DeckDescentEmit.deckDescentDescriptorJson`.
2. `scripts/check-poag1-artifacts.sh`: add `games/deck-descent.json` to
   `content_paths` and to `expected`, and pass its SHA-256 the way the other
   three are passed.  ⚑ This changes `content_root_sha`, so the manifest bytes
   change and the curator signature must be re-taken.  That is a rebuild, not a
   migration — but it is a CURATOR act, so it is named here and not performed.
3. `Emit.lean`: delete the private `jsonString`, `jsonArray`, `jsonPrettyArray`,
   `jsonBool`, `exactKeys`, `validateInstanceDeclaration` and
   `validateHiddenSecurity`, and `open Dregg2.Games.PathOfAngels.EmitJson`
   instead.  They are byte-identical to this module's copies TODAY; the reason to
   converge is that two copies of `instanceDeclarationJson` is two descriptions
   of where an instance comes from.
4. `lakefile.toml`: `PathOfAngelsGuards` roots `EmitJson`, `DeckDescentEmit` and
   `DeckDescentEmitMain`.  ✅ DONE 2026-08-06 by the descent lane; the whole
   target builds green on hbox (3179 jobs) and this module's five
   `#assert_compiled` pins run there.

5. ⚑ Baseline: NOTHING to add.  The enrollment commit used to owe
   `deck-descent/the-family-collapses` and `deck-descent/the-spurs-are-one-spur`
   in the same commit; those findings were REPAIRED on 2026-08-06 — the east
   spur's second relic broke the mirror (`Chamber.relicCount`,
   `the_mirror_is_broken`) — and the gate now reports 0 FAIL / 0 WARN for this
   game, measured on the re-emitted bytes.  So enrolling the descriptor into
   `poa/artifacts/poag1/games/` needs NO descent baseline entries — but re-run
   the gate at enrollment and believe ITS answer, not this comment: a baseline
   entry for a finding the gate does not produce is a VANISHED entry and exits
   1, exactly as an unbaselined new finding does.  `test-poa.sh` runs the gate
   with the checked-in baseline and no `--games-dir`, so today it sees three
   games and passes; the pending directory is why it is not already red.

Until (1) and (2) land, the descriptor is emitted by
`Dregg2/Games/PathOfAngels/DeckDescentEmitMain.lean` into
`poa/artifacts/poag1-pending/games/`, which is deliberately NOT the signed bundle
directory: `check-poag1-artifacts.sh` refuses any file under
`poa/artifacts/poag1/` that is not in its `expected` list, and a game the curator
has not signed for does not belong in a signed bundle. -/

end Dregg2.Games.PathOfAngels.DeckDescentEmit
