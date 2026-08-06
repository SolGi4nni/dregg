/-
# Artificer Logic — the POAG1 wire

Substrate note: this module renders bytes.  It authors no game semantics.  Every
verdict, successor, refusal reason and rule signature below is read out of
`Dregg2.Games.PathOfAngels.ArtificerLogic`, and the pins at the bottom parse the
RENDERED bytes back and compare all 28,728 rows against `rowFor`.  There is no
second model of the mechanism in this repository.

## Why this is not `Emit.lean`

`Emit.lean` and `EmitMain.lean` are held by the emit-authority lane this cycle,
and `DeckDescentEmit` is the descent lane's.  The splice this module needs is
stated at the bottom of this file rather than performed in files another lane is
editing.

## What the descriptor carries, and what it cannot

The instance is ONE hidden rule out of sixteen, and the descriptor names none of
them as the live one.  What it names instead is:

* the `manual` — the whole published lattice, every rule with the charges it
  engages on.  ⚑ This is PUBLIC BY DESIGN and it is the opposite of a leak: the
  game is fair precisely because the player can see the space they are narrowing.
  A descriptor that hid it would be classic Zendo, where a loss feels arbitrary.
  What stays hidden is WHICH entry the run seed drew.
* a `state_machine` in which every row that consults the draw carries BOTH
  successors (`step_is_one_of_the_two_branches`), and every row that does not
  carries one — and `advance_row_is_the_real_step` proves the one-successor rows
  are not guesses.

⚑ The manual block must NOT be called `rules`: the design gate dispatches its
backend on document SHAPE, and a top-level `rules` key routes to the deduction
backend.  It also must not be called `oracle`, which routes to the probe backend.

⚠ **Polarity.**  `on_match` is the ENGAGEMENT / the RIGHT NAMING, `on_mismatch`
is the SLIP / the WRONG one — matching `rowFor`'s `stepAns true` / `stepAns false`.  A
reader should not have to take that on trust and does not have to: on a probe row
the two branch views differ in their candidate sets, and the `on_match` set is
the one whose members all list the fed charge in their `engages`.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.ArtificerLogic
import Dregg2.Games.PathOfAngels.EmitJson
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ArtificerLogicEmit

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EmitJson
open Dregg2.Games.PathOfAngels.ArtificerLogic

/-! ## The rows -/

/-- One emitted `(state, action)` row.  `row` is `ArtificerLogic.rowFor` applied
to the pair and is never recomputed by a second rule here. -/
structure LogicRow where
  state : ArtificerLogic.State
  action : ArtificerLogic.Action
  row : ArtificerLogic.Row

def logicStates : List ArtificerLogic.State := ArtificerLogic.parametricStates

def logicActions : List ArtificerLogic.Action := ArtificerLogic.allActions

def logicRows : List LogicRow :=
  logicStates.flatMap fun s =>
    logicActions.map fun a => { state := s, action := a, row := ArtificerLogic.rowFor s a }

/-! ## The manual, rendered

`engagesOn` is a PARAMETER of the renderer rather than a call to `Rule.accepts`,
so the hostile variant at the bottom — a manual carrying a synonym pair — goes
through exactly this function and is not a second encoder. -/

def engagesOn (r : ArtificerLogic.Rule) : List ArtificerLogic.Charge :=
  ArtificerLogic.allCharges.filter (fun c => r.accepts c)

def manualFamilies : List String :=
  (ArtificerLogic.manual.map ArtificerLogic.Rule.family).eraseDups

private def chargeJson (ch : ArtificerLogic.Charge) : String :=
  "      {\"id\":" ++ jsonString ch.tag ++
    ",\"cogs\":" ++ jsonArray [jsonString ch.first.tag, jsonString ch.second.tag,
      jsonString ch.third.tag] ++
    ",\"brass\":" ++ toString (ch.count ArtificerLogic.Metal.brass) ++ "}"

private def ruleJson (engages : ArtificerLogic.Rule → List ArtificerLogic.Charge)
    (r : ArtificerLogic.Rule) : String :=
  "      {\"id\":" ++ jsonString r.tag ++
    ",\"family\":" ++ jsonString r.family ++
    ",\"label\":" ++ jsonString r.label ++
    ",\"engages\":" ++ jsonArray ((engages r).map fun c => jsonString c.tag) ++ "}"

/-- The published field manual.  ⚑ `probe_budget` and `refusal_reasons` are here
so the design gate can rebuild the rule from the descriptor and check every
emitted row against its own reconstruction, rather than analysing a table it has
to take on trust. -/
private def manualJson (engages : ArtificerLogic.Rule → List ArtificerLogic.Charge) : String :=
  "{\"cogs_per_charge\":3" ++
  ",\"metals\":" ++ jsonArray (ArtificerLogic.allMetals.map fun m => jsonString m.tag) ++
  ",\"seats\":" ++ jsonArray (ArtificerLogic.allSeats.map fun p => jsonString p.tag) ++
  ",\"families\":" ++ jsonArray (manualFamilies.map jsonString) ++
  ",\"charges\":" ++ jsonPrettyArray (ArtificerLogic.allCharges.map chargeJson) ++
  ",\"rules\":" ++ jsonPrettyArray (ArtificerLogic.manual.map (ruleJson engages)) ++
  ",\"probe_budget\":" ++ toString ArtificerLogic.PROBE_BUDGET ++
  ",\"refusal_reasons\":" ++
    jsonArray (ArtificerLogic.refusalVocabulary.map jsonString) ++
  ",\"answer\":\"the mechanism engages or it slips; on_match is the engagement\"" ++
  ",\"probe_admissible\":\"a charge is legal only while it separates two rules \
the evidence still permits, so no charge can be spent on a question already \
answered\"" ++
  ",\"declaration_admissible\":\"a naming is legal only for a rule the evidence \
still permits, and it ends the run either way\"" ++
  ",\"reserve\":\"a run is certifiable when some sequence of the charges it can \
still afford separates its surviving candidates down to one on every answer the \
mechanism could give\"}"

/-! ## Rendering the machine -/

private def ruleListJson (rs : List ArtificerLogic.Rule) : String :=
  jsonArray (rs.map fun r => jsonString r.tag)

/-- The state view.  Everything the rules read is here — that is the property the
design gate's differential depends on.

`certifiable` is published deliberately.  It is instance-INDEPENDENT (it is a
fact about the surviving candidate set and the remaining budget, not about the
draw), and without it a client cannot tell a player that their run can no longer
be won on skill — only on luck.  That is the honest analogue of a descent's
`doomed`, and a game that hides it is hiding what the budget is for. -/
private def stateJson (s : ArtificerLogic.State) : String :=
  "    {\"id\":" ++ jsonString (ArtificerLogic.stateId s) ++
    ",\"terminal\":" ++ jsonBool (ArtificerLogic.solvedB s) ++
    ",\"view\":{\"candidates\":" ++ ruleListJson s.candidates ++
    ",\"remaining\":" ++ toString s.candidates.length ++
    ",\"turns\":" ++ toString s.spent ++
    ",\"charges_left\":" ++ toString (ArtificerLogic.chargesLeft s) ++
    ",\"verdict\":" ++ jsonString s.verdict.tag ++
    ",\"certain\":" ++ jsonBool (ArtificerLogic.certainB s) ++
    ",\"certifiable\":" ++ jsonBool (ArtificerLogic.certifiableB s) ++
    ",\"doomed\":" ++ jsonBool (ArtificerLogic.doomedB s) ++
    ",\"solved\":" ++ jsonBool (ArtificerLogic.solvedB s) ++ "}}"

private def actionJson (a : ArtificerLogic.Action) : String :=
  "    {\"id\":" ++ jsonString a.tag ++
    ",\"label\":" ++ jsonString a.label ++
    (match a with
     | .probe c => ",\"kind\":\"probe\",\"charge\":" ++ jsonString c.tag ++ ",\"rule\":null"
     | .declare r => ",\"kind\":\"declare\",\"charge\":null,\"rule\":" ++ jsonString r.tag) ++
    "}"

private def transitionJson (t : LogicRow) : String :=
  let stateId := jsonString (ArtificerLogic.stateId t.state)
  let actionId := jsonString t.action.tag
  let head :=
    "    {\"state\":" ++ stateId ++ ",\"action\":" ++ actionId ++ ",\"verdict\":"
  match t.row with
  | .refuse reason =>
      head ++ "\"refuse\",\"reason\":" ++ jsonString reason ++
        ",\"next\":null,\"on_match\":null,\"on_mismatch\":null}"
  | .advance next =>
      head ++ "\"accept\",\"reason\":null,\"next\":" ++
        jsonString (ArtificerLogic.stateId next) ++
        ",\"on_match\":null,\"on_mismatch\":null}"
  | .resolve onTurn onJam =>
      head ++ "\"resolve\",\"reason\":null,\"next\":null,\"on_match\":" ++
        jsonString (ArtificerLogic.stateId onTurn) ++
        ",\"on_mismatch\":" ++ jsonString (ArtificerLogic.stateId onJam) ++ "}"

/-! ## The descriptor -/

/-- The whole document, parameterised by the manual's signature function, the
state list and the row list so that every HOSTILE variant goes through the SAME
renderer as the honest one.  A falsifier built any other way tests a second
encoder. -/
def descriptorFrom (engages : ArtificerLogic.Rule → List ArtificerLogic.Charge)
    (states : List ArtificerLogic.State) (rows : List LogicRow) : String :=
  "{\n" ++
  "  \"format\":\"POAG1-GAME\",\n" ++
  "  \"schema_version\":1,\n" ++
  "  \"game_id\":\"artificer-logic\",\n" ++
  "  \"ruleset\":\"artificer-v1\",\n" ++
  "  \"engine_module\":\"Dregg2.Games.PathOfAngels.ArtificerLogic\",\n" ++
  "  \"action_limit\":" ++ toString ArtificerLogic.ACTION_LIMIT ++ ",\n" ++
  "  \"security\":{\"classification\":\"committed-hidden-instance\"," ++
    "\"instance_visibility\":\"oracle-only\",\"competitive_rewards\":false," ++
    "\"economic_rewards\":false},\n" ++
  "  \"instance\":" ++ instanceDeclarationJson "oracle-only" ++ ",\n" ++
  "  \"manual\":" ++ manualJson engages ++ ",\n" ++
  "  \"practice\":{\"scored\":false,\"instance_space\":" ++
    toString ArtificerLogic.manual.length ++
    ",\"member_names\":\"manual.rules\",\"purpose_tag\":2},\n" ++
  "  \"state_machine\":{\n" ++
  "    \"initial_state\":" ++
    jsonString (ArtificerLogic.stateId ArtificerLogic.initialState) ++ ",\n" ++
  "    \"states\":" ++ jsonPrettyArray (states.map stateJson) ++ ",\n" ++
  "    \"actions\":" ++ jsonPrettyArray (logicActions.map actionJson) ++ ",\n" ++
  "    \"transitions\":" ++ jsonPrettyArray (rows.map transitionJson) ++ "\n" ++
  "  },\n" ++
  "  \"output\":{\"requires\":\"terminal\",\"contribution\":\"mission_reward\"," ++
    "\"artifact\":\"mission_artifact\"}\n" ++
  "}\n"

def artificerLogicDescriptorJson : String :=
  descriptorFrom engagesOn logicStates logicRows

/-! ## Validation — the key set, exactly -/

def validateLogicDescriptor (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  exactKeys document ["format", "schema_version", "game_id", "ruleset", "engine_module",
    "action_limit", "security", "instance", "manual", "practice", "state_machine",
    "output"]
  validateHiddenSecurity document "oracle-only"
  validateInstanceDeclaration (← document.getObjVal? "instance") "oracle-only"
  exactKeys (← document.getObjVal? "output") ["requires", "contribution", "artifact"]
  exactKeys (← document.getObjVal? "practice")
    ["scored", "instance_space", "member_names", "purpose_tag"]
  let manualBlock ← document.getObjVal? "manual"
  exactKeys manualBlock ["cogs_per_charge", "metals", "seats", "families", "charges",
    "rules", "probe_budget", "refusal_reasons", "answer", "probe_admissible",
    "declaration_admissible", "reserve"]
  let charges ← (manualBlock.getObjVal? "charges") >>= Json.getArr?
  if charges.size != ArtificerLogic.allCharges.length then
    throw s!"POAG1 artificer emits {charges.size} charges, expected \
{ArtificerLogic.allCharges.length}"
  for charge in charges do
    exactKeys charge ["id", "cogs", "brass"]
  let rules ← (manualBlock.getObjVal? "rules") >>= Json.getArr?
  if rules.size != ArtificerLogic.manual.length then
    throw s!"POAG1 artificer emits {rules.size} rules, expected \
{ArtificerLogic.manual.length}"
  for rule in rules do
    exactKeys rule ["id", "family", "label", "engages"]
  let machine ← document.getObjVal? "state_machine"
  exactKeys machine ["initial_state", "states", "actions", "transitions"]
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  if states.size != logicStates.length then
    throw s!"POAG1 artificer emits {states.size} states, expected {logicStates.length}"
  for state in states do
    exactKeys state ["id", "terminal", "view"]
    exactKeys (← state.getObjVal? "view")
      ["candidates", "remaining", "turns", "charges_left", "verdict", "certain",
       "certifiable", "doomed", "solved"]
  let actions ← (machine.getObjVal? "actions") >>= Json.getArr?
  if actions.size != logicActions.length then
    throw s!"POAG1 artificer emits {actions.size} actions, expected \
{logicActions.length}"
  for action in actions do
    exactKeys action ["id", "label", "kind", "charge", "rule"]
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  if transitions.size != logicStates.length * logicActions.length then
    throw s!"POAG1 artificer emits {transitions.size} rows for \
{logicStates.length} states by {logicActions.length} actions"
  for transition in transitions do
    exactKeys transition ["state", "action", "verdict", "reason", "next",
      "on_match", "on_mismatch"]

/-! ## ⚑ The emitted manual IS the kernel's

This is the half specific to an induction game, and it is the load-bearing one:
the design gate rebuilds DISTINGUISHABILITY from the emitted `turns` lists, so if
those lists were not the kernel's, the gate would be checking a manual nobody
plays.  `logicManualRefinesKernel` closes that, and
`logicManualIsDistinguishing` is the gate's own check, run here as well. -/

private def expectStr (j : Json) (key : String) : Except String String :=
  j.getObjValAs? String key

private def expectNull (j : Json) (key what : String) : Except String Unit := do
  match ← j.getObjVal? key with
  | .null => pure ()
  | _ => throw s!"POAG1 artificer {what} row names a {key}"

/-- Every emitted rule, against `Rule.accepts`. -/
def logicManualRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let manualBlock ← document.getObjVal? "manual"
  let rules ← (manualBlock.getObjVal? "rules") >>= Json.getArr?
  if rules.size != ArtificerLogic.manual.length then
    throw s!"POAG1 artificer manual has {rules.size} entries, kernel has \
{ArtificerLogic.manual.length}"
  let mut index := 0
  for r in ArtificerLogic.manual do
    match rules[index]? with
    | none => throw s!"POAG1 artificer manual has no entry {index}"
    | some emitted =>
        if (← expectStr emitted "id") != r.tag then
          throw s!"POAG1 artificer manual entry {index} claims another id"
        if (← expectStr emitted "family") != r.family then
          throw s!"POAG1 artificer manual entry {r.tag} claims another family"
        if (← expectStr emitted "label") != r.label then
          throw s!"POAG1 artificer manual entry {r.tag} claims another label"
        let engages ← (emitted.getObjVal? "engages") >>= Json.getArr?
        let expected := ArtificerLogic.allCharges.filter (fun c => r.accepts c)
        if engages.size != expected.length then
          throw s!"POAG1 artificer manual entry {r.tag} engages on {engages.size} \
charges, the kernel engages on {expected.length}"
        let mut j := 0
        for c in expected do
          match engages[j]? with
          | none => throw s!"POAG1 artificer manual entry {r.tag} has no charge {j}"
          | some emittedCharge =>
              match emittedCharge with
              | .str value =>
                  if value != c.tag then
                    throw s!"POAG1 artificer manual entry {r.tag} names a charge \
the kernel does not engage on"
              | _ => throw s!"POAG1 artificer manual entry {r.tag} names a \
non-string charge"
          j := j + 1
    index := index + 1

/-- ⚑ **THE DISTINGUISHABILITY CHECK, FROM THE BYTES.**  Read every rule's
signature out of the RENDERED manual and refuse if two of them agree.  This is
the same property `ArtificerLogic.manual_has_no_synonyms` proves over the kernel;
running it over the wire as well is what stops a descriptor from publishing a
lattice with an unwinnable pair in it while the kernel stays clean. -/
def logicManualIsDistinguishing (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let manualBlock ← document.getObjVal? "manual"
  let rules ← (manualBlock.getObjVal? "rules") >>= Json.getArr?
  let mut signatures : List (String × List String) := []
  for emitted in rules do
    let id ← expectStr emitted "id"
    let engages ← (emitted.getObjVal? "engages") >>= Json.getArr?
    let mut tags : List String := []
    for t in engages do
      match t with
      | .str value => tags := tags ++ [value]
      | _ => throw s!"POAG1 artificer manual entry {id} names a non-string charge"
    for (otherId, otherTags) in signatures do
      if otherTags == tags then
        throw s!"POAG1 artificer manual is not distinguishing: {id} and {otherId} \
engage on exactly the same charges, so a player who runs every legal experiment \
can still be handed a coin flip"
    signatures := signatures ++ [(id, tags)]

/-! ## ⚑ The emitted table IS the kernel, row by row -/

private def checkRow (emitted : Json) (t : LogicRow) : Except String Unit := do
  let sid := ArtificerLogic.stateId t.state
  let aid := t.action.tag
  if (← expectStr emitted "state") != sid then
    throw s!"POAG1 artificer row claims a state that is not {sid}"
  if (← expectStr emitted "action") != aid then
    throw s!"POAG1 artificer row at {sid} claims an action that is not {aid}"
  let verdict ← expectStr emitted "verdict"
  match t.row with
  | .refuse reason =>
      if verdict != "refuse" then
        throw s!"POAG1 artificer {sid}/{aid} is a refusal and the wire says {verdict}"
      if (← expectStr emitted "reason") != reason then
        throw s!"POAG1 artificer {sid}/{aid} refuses for a reason the kernel did not give"
      expectNull emitted "next" "refusal"
      expectNull emitted "on_match" "refusal"
      expectNull emitted "on_mismatch" "refusal"
  | .advance next =>
      if verdict != "accept" then
        throw s!"POAG1 artificer {sid}/{aid} advances and the wire says {verdict}"
      if (← expectStr emitted "next") != ArtificerLogic.stateId next then
        throw s!"POAG1 artificer {sid}/{aid} advances into a state the kernel did not name"
      expectNull emitted "reason" "accept"
      expectNull emitted "on_match" "accept"
      expectNull emitted "on_mismatch" "accept"
  | .resolve onTurn onJam =>
      if verdict != "resolve" then
        throw s!"POAG1 artificer {sid}/{aid} resolves and the wire says {verdict}"
      if (← expectStr emitted "on_match") != ArtificerLogic.stateId onTurn then
        throw s!"POAG1 artificer {sid}/{aid} names an on_match the kernel did not give"
      if (← expectStr emitted "on_mismatch") != ArtificerLogic.stateId onJam then
        throw s!"POAG1 artificer {sid}/{aid} names an on_mismatch the kernel did not give"
      if onTurn = onJam then
        throw s!"POAG1 artificer {sid}/{aid} resolves to the same state either way"
      expectNull emitted "reason" "resolve"
      expectNull emitted "next" "resolve"

def logicTableRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let machine ← document.getObjVal? "state_machine"
  let transitions ← (machine.getObjVal? "transitions") >>= Json.getArr?
  let rows := logicRows
  if transitions.size != rows.length then
    throw s!"POAG1 artificer table has {transitions.size} rows, kernel has {rows.length}"
  let mut index := 0
  for t in rows do
    match transitions[index]? with
    | none => throw s!"POAG1 artificer table has no row {index}"
    | some emitted => checkRow emitted t
    index := index + 1

/-- Every emitted state view, against the kernel state it claims to be.  This is
the half `logicTableRefinesKernel` cannot see: a table of correct verdicts over
views that misreport the surviving candidates or the remaining charges would
still pass above. -/
def logicViewsRefineKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let machine ← document.getObjVal? "state_machine"
  let states ← (machine.getObjVal? "states") >>= Json.getArr?
  if states.size != logicStates.length then
    throw s!"POAG1 artificer emits {states.size} state views, kernel has \
{logicStates.length}"
  let mut index := 0
  for s in logicStates do
    match states[index]? with
    | none => throw s!"POAG1 artificer has no state view {index}"
    | some emitted =>
        if (← expectStr emitted "id") != ArtificerLogic.stateId s then
          throw s!"POAG1 artificer state view {index} claims another id"
        let view ← emitted.getObjVal? "view"
        if (← view.getObjValAs? Nat "remaining") != s.candidates.length then
          throw s!"POAG1 artificer view {index} misreports the surviving count"
        if (← view.getObjValAs? Nat "turns") != s.spent then
          throw s!"POAG1 artificer view {index} misreports the clock"
        if (← view.getObjValAs? Nat "charges_left") != ArtificerLogic.chargesLeft s then
          throw s!"POAG1 artificer view {index} misreports the charges left"
        if (← view.getObjValAs? String "verdict") != s.verdict.tag then
          throw s!"POAG1 artificer view {index} misreports the verdict"
        if (← view.getObjValAs? Bool "certain") != ArtificerLogic.certainB s then
          throw s!"POAG1 artificer view {index} misreports certainty"
        if (← view.getObjValAs? Bool "certifiable") != ArtificerLogic.certifiableB s then
          throw s!"POAG1 artificer view {index} misreports whether the run can \
still be won on skill, which is the one field the budget exists to make true"
        if (← view.getObjValAs? Bool "doomed") != ArtificerLogic.doomedB s then
          throw s!"POAG1 artificer view {index} misreports the loss"
        if (← view.getObjValAs? Bool "solved") != ArtificerLogic.solvedB s then
          throw s!"POAG1 artificer view {index} misreports the win"
        if (← emitted.getObjValAs? Bool "terminal") != ArtificerLogic.solvedB s then
          throw s!"POAG1 artificer view {index} misreports terminality"
        let candidates ← (view.getObjVal? "candidates") >>= Json.getArr?
        if candidates.size != s.candidates.length then
          throw s!"POAG1 artificer view {index} lists the wrong number of survivors"
        let mut j := 0
        for r in s.candidates do
          match candidates[j]? with
          | none => throw s!"POAG1 artificer view {index} has no survivor {j}"
          | some entry =>
              match entry with
              | .str value =>
                  if value != r.tag then
                    throw s!"POAG1 artificer view {index} names a survivor the \
kernel did not"
              | _ => throw s!"POAG1 artificer view {index} names a non-string survivor"
          j := j + 1
    index := index + 1

/-! ## ⚠ The falsifiers, built constructively from the live encoder

Each mutant is rendered by `descriptorFrom` — the SAME function that renders the
honest bytes — from a deliberately wrong argument.  A falsifier that edits a
string it expects to find has, twice in this repository, stopped falsifying when
the string left the fixture: the mutation replaced nothing and the hostile input
equalled the honest one.  So each theorem below asserts the mutation HAPPENED
before it reads the verdict. -/

/-- ⚑ **THE FALSIFIER THAT MATTERS FOR THIS GAME.**  `even-brass` is rendered
carrying `mirrored`'s signature, so the published manual holds two entries no
experiment can separate.  Schema-legal — it is a well-formed manual — and it is
exactly the defect the distinguishability gate exists to catch: a player who runs
all eight charges perfectly is left with two candidates and a coin.

⚠ The rule is not otherwise touched, so the STATE MACHINE is unchanged and every
row still refines the kernel.  A gate that only checked rows would pass this. -/
def synonymTurns (r : ArtificerLogic.Rule) : List ArtificerLogic.Charge :=
  if r = ArtificerLogic.Rule.evenBrass then engagesOn ArtificerLogic.Rule.mirrored
  else engagesOn r

def synonymManualDescriptor : String := descriptorFrom synonymTurns logicStates logicRows

/-- The first row that consults the instance, flattened into a plain accept on its
turning branch.  Schema-legal and wrong, which is the mutation a schema check
cannot catch. -/
def flattenedResolveRows : List LogicRow :=
  let flatten : LogicRow → LogicRow := fun t =>
    match t.row with
    | .resolve m _ => { t with row := .advance m }
    | _ => t
  match logicRows.findIdx? (fun t => match t.row with | .resolve _ _ => true | _ => false) with
  | none => logicRows
  | some i => logicRows.modify i flatten

def flattenedResolveDescriptor : String :=
  descriptorFrom engagesOn logicStates flattenedResolveRows

/-- One row short.  Catches a table that is no longer total. -/
def truncatedDescriptor : String := descriptorFrom engagesOn logicStates logicRows.tail

/-! ## The pins -/

theorem logicDescriptor_exact_schema :
    validateLogicDescriptor artificerLogicDescriptorJson = .ok () := by
  native_decide

theorem logicDescriptor_manual_is_the_kernel :
    logicManualRefinesKernel artificerLogicDescriptorJson = .ok () := by
  native_decide

/-- ⚑ **The published lattice has no unwinnable pair**, checked against the bytes
a client downloads and not against the kernel's own definitions. -/
theorem logicDescriptor_manual_is_distinguishing :
    logicManualIsDistinguishing artificerLogicDescriptorJson = .ok () := by
  native_decide

theorem logicDescriptor_table_is_the_kernel :
    logicTableRefinesKernel artificerLogicDescriptorJson = .ok () := by
  native_decide

theorem logicDescriptor_views_are_the_kernel :
    logicViewsRefineKernel artificerLogicDescriptorJson = .ok () := by
  native_decide

/-- ⚠ **The synonym is caught, and ONLY by the manual check.**  The three
conjuncts are the whole argument: the mutation happened; the distinguishability
check refuses it; and the TABLE check still passes, which is why a row-by-row
differential is not sufficient for an induction game and this module carries a
second, manual-shaped one. -/
theorem synonym_manual_is_caught :
    synonymManualDescriptor ≠ artificerLogicDescriptorJson ∧
    logicManualIsDistinguishing synonymManualDescriptor ≠ .ok () ∧
    logicTableRefinesKernel synonymManualDescriptor = .ok () := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

theorem flattened_resolve_is_caught :
    flattenedResolveDescriptor ≠ artificerLogicDescriptorJson ∧
    logicTableRefinesKernel flattenedResolveDescriptor ≠ .ok () := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

theorem truncated_table_is_caught :
    truncatedDescriptor ≠ artificerLogicDescriptorJson ∧
    validateLogicDescriptor truncatedDescriptor ≠ .ok () ∧
    logicTableRefinesKernel truncatedDescriptor ≠ .ok () := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

#assert_compiled logicDescriptor_exact_schema
#assert_compiled logicDescriptor_manual_is_the_kernel
#assert_compiled logicDescriptor_manual_is_distinguishing
#assert_compiled logicDescriptor_table_is_the_kernel
#assert_compiled logicDescriptor_views_are_the_kernel
#assert_compiled synonym_manual_is_caught
#assert_compiled flattened_resolve_is_caught
#assert_compiled truncated_table_is_caught

/-! ## Handover — what other lanes must splice

⚠ NONE of these are performed here: every file named is another lane's this
cycle.

1. `EmitMain.lean` (emit-authority lane): `import
   Dregg2.Games.PathOfAngels.ArtificerLogicEmit` and, in `emitDescriptors`,
   `writeAtomic (dir / "games" / "artificer-logic.json")
   ArtificerLogicEmit.artificerLogicDescriptorJson`.
2. `scripts/check-poag1-artifacts.sh`: add `games/artificer-logic.json` to
   `content_paths` and `expected` with its SHA-256.  ⚑ This changes
   `content_root_sha`, so the manifest bytes change and the curator signature
   must be re-taken.  A rebuild, not a migration — but a CURATOR act, so it is
   named here and not performed.
3. `lakefile.toml`: `PathOfAngelsGuards` must root
   `Dregg2.Games.PathOfAngels.ArtificerLogic`,
   `Dregg2.Games.PathOfAngels.ArtificerLogicEmit` and
   `Dregg2.Games.PathOfAngels.ArtificerLogicEmitMain`, or the 82 + 8 pins across
   them run NOWHERE — the orphan class that block exists to catch.
4. `poa-web/` (suite-rack lane): `src/artificer-runtime.js` and
   `src/artificer-controller.js` are written by this lane and are self-contained.
   The SHARED files that must gain an entry are
   `src/poag1.js` (`POAG1_EXPECTED_ARTIFACTS`, in manifest order),
   `src/mission-catalog.js` (`GAME_SPECS` — and `missions.length` is hard-asserted
   equal to `GAME_SPECS.length`), `src/mission-launcher.js` (the `refuse` list and
   the dispatch arm), `src/app.js` (`missionCopy`, `practiceSession`, the boot
   wiring and the import), `minigames.css` (a `.artificer-logic` board grid), and
   `tests/canonical-descriptors.mjs`.
5. ⚑ `scripts/poa-design-gate.baseline.json` must gain any WARN this game raises
   IN THE SAME COMMIT that moves the descriptor into `poa/artifacts/poag1/games/`
   — measured on the descent lane, both directions exit 1: baseline entries for a
   game the gate cannot see are VANISHED entries, and a visible game with no
   entries raises UNKNOWN findings.

Until (1) and (2) land, the descriptor is emitted by
`ArtificerLogicEmitMain.lean` into `poa/artifacts/poag1-pending/games/`, which is
deliberately NOT the signed bundle directory: `check-poag1-artifacts.sh` refuses
any file under `poa/artifacts/poag1/` that is not in its `expected` list, and a
game the curator has not signed for does not belong in a signed bundle. -/

end Dregg2.Games.PathOfAngels.ArtificerLogicEmit
