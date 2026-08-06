/-
StepStatementProbe — the BASELINE, re-measured rather than relayed.

    cd metatheory && LEAN_PATH=$(lake env printenv LEAN_PATH) lean --run wip/StepStatementProbe.lean

Prints, for both assemblies, how many of the slots the rung derives agree with Mina's forty
(`MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED`, `PreparedStatement::to_public_input(40)`).
-/
import Dregg2.Circuit.Emit.KimchiStepWrapChain
open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiStepWrapChain
open Dregg2.Circuit.Emit.MinaWrapDeferredWords (WRAP_PUBLIC_INPUT_MEASURED)

set_option maxRecDepth 100000

def report (name : String) (slots : List Nat) (v : List Int) : IO Unit := do
  let hit := slots.filter (fun s => (v.getD s 0).toNat == WRAP_PUBLIC_INPUT_MEASURED.getD s 0)
  IO.println s!"{name}: {hit.length} of {slots.length} agree with Mina's forty"
  IO.println s!"    agreeing slots : {hit}"
  IO.println s!"    differing slots: {slots.filter (fun s => !hit.contains s)}"

def main : IO Unit := do
  let sw := wrapSlotsAt shapeWrap .bind
  IO.println s!"wrapSlotsAt shapeWrap  .bind = {sw}"
  report "tChain           " sw (wrapPublicAt tChain .bind)
  report "mkWrap shapeWrap " sw (wrapPublicAt (mkWrap shapeWrap) .bind)
  IO.println s!"shapeWrap.xhatEntries.length  = {shapeWrap.xhatEntries.length}"
  for (n, k) in [("key", Rung.key), ("xhat", Rung.xhat), ("split", Rung.split),
                 ("ftcomm", Rung.ftcomm), ("prev", Rung.prev), ("wraphack", Rung.wraphack),
                 ("combine", Rung.combine), ("bullet", Rung.bullet), ("close", Rung.close)] do
    report s!"mkWrap @ {n}" (wrapSlotsAt shapeWrap k) (wrapPublicAt (mkWrap shapeWrap) k)
