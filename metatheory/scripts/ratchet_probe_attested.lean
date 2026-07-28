/-
Probe: would landing `hash4Injective_false_of_finite` (which makes `Hash4Injective` a DERIVED
refuted floor) put any declaration into `#floor_ratchet`'s carrier surface?

The root `lake build Dregg2` cannot answer today: it is red on 11 sibling-lane targets, so the
gate never runs. This asks the gate's OWN classifier the same question, directly, over the two
modules in question — no reimplementation, `FloorRatchet.antiFloor` is imported and called.

`content` is instantiated at exactly the fixpoint the gate would compute once `Hash4Injective`
becomes refuted: the floor itself, plus any Prop-def whose body mentions it. `Coll4`'s body does
not, so the set is the singleton — stated here so the assumption is visible and checkable.
-/
import Dregg2.Verify.FloorRatchet
import Dregg2.Circuit.Emit.AttestedFactsRootRegrounded

open Lean Meta Elab Command Dregg2.Verify

namespace RatchetProbe

/-- The refuted-floor content set as it WOULD be once the tooth lands. -/
def content : Name → Bool := fun n => n == `Dregg2.Circuit.Emit.AttestedFactsRootModel.Hash4Injective

/-- Every declaration in the two modules whose TYPE could possibly mention the floor, with the
verdict it must have. `true` = EXEMPT (antiFloor), `false` = would be a GATED CARRIER needing a
`FloorRatchetBaseline` entry. -/
def expected : List (Name × Bool) :=
  [ (`Dregg2.Circuit.Emit.AttestedFactsRootModel.coll4_breaks_hash4Injective, true)
  , (`Dregg2.Circuit.Emit.AttestedFactsRootRegrounded.hash4Injective_false_of_finite, true)
  , (`Dregg2.Circuit.Emit.AttestedFactsRootRegrounded.hash4Injective_false_babyBear, true)
  , (`Dregg2.Circuit.Emit.AttestedFactsRootRegrounded.hash4Injective_false_bool, true) ]

/-- The ported consumers and the residual: their types must not mention the floor AT ALL, which
is the stronger property (`antiFloor` never even gets consulted). -/
def mustNotMentionFloor : List Name :=
  [ `Dregg2.Circuit.Emit.AttestedFactsRootModel.attested_member_is_committed
  , `Dregg2.Circuit.Emit.AttestedFactsRootModel.fabricated_member_refused
  , `Dregg2.Circuit.Emit.AttestedFactsRootModel.attested_member_is_committed_or_collides
  , `Dregg2.Circuit.Emit.AttestedFactsRootModel.Coll4
  , `Dregg2.Circuit.Emit.AttestedFactsRootModel.coll4_self_false
  , `Dregg2.Circuit.Emit.AttestedFactsRootModel.coll4_of_constant
  , `Dregg2.Circuit.Emit.AttestedFactsRootModel.ftreeNode_injective ]

/-- Confirm the retired witness is really gone (it named the floor in its conclusion). -/
def mustBeAbsent : List Name :=
  [ `Dregg2.Circuit.Emit.AttestedFactsRootModel.hash4Injective_is_satisfiable ]

end RatchetProbe

run_cmd do
  let env ← getEnv
  let mut bad := 0
  for (n, want) in RatchetProbe.expected do
    let some ci := env.find? n | do logError m!"MISSING {n}"; bad := bad + 1; continue
    let got := FloorRatchet.antiFloor RatchetProbe.content ci.type
    if got != want then
      logError m!"VERDICT MOVED  {n}: antiFloor = {got}, expected {want}"
      bad := bad + 1
    else
      logInfo m!"ok  antiFloor={got}  {n}"
  for n in RatchetProbe.mustNotMentionFloor do
    let some ci := env.find? n | do logError m!"MISSING {n}"; bad := bad + 1; continue
    let hit := ci.type.foldConsts false (fun c a => a || RatchetProbe.content c)
    if hit then
      logError m!"STILL MENTIONS THE FLOOR (would be a gated carrier): {n}"
      bad := bad + 1
    else
      logInfo m!"ok  floor-free type  {n}"
  for n in RatchetProbe.mustBeAbsent do
    if (env.find? n).isSome then
      logError m!"STILL PRESENT (names the floor in its conclusion): {n}"
      bad := bad + 1
    else
      logInfo m!"ok  retired  {n}"
  if bad == 0 then
    logInfo m!"PROBE CLEAN — landing the tooth adds ZERO gated carriers."
  else
    throwError "PROBE DIRTY: {bad} problem(s)."
