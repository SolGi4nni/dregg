/-
FloorProbe4 — WHAT IS `mkStep`'s 7 085 ms MADE OF? Arithmetic, or plumbing?

    cd metatheory && lake build Dregg2.Circuit.Emit.KimchiStepMainCore
    LEAN_PATH=$(lake env printenv LEAN_PATH) lean --run wip/FloorProbe4.lean

⚑ THE CLAIM UNDER TEST (derived, never measured, by the pass that shipped `95ed4f2ec`):
    "mkStep's residue is arithmetic, not recomputation — ~10⁴ sequential Fermat inversions,
     each 255 squarings."
`FloorProbe3` priced the two candidate primitives against each other and they are NOT the same
size, which is the whole question:
    one Fermat inversion (`fInv`)          0.229 ms
    one Poseidon permutation (`permStates`) 0.71  ms   ← 3.1× an inversion
So "how many inversions" is the wrong unit unless the sponges are cheap. This file runs each stage
of `mkStepWith` on its own and prices it in BOTH units.

⚑ Lean is strict here and `FloorProbe3` PROVED it: a deep walk of a prebuilt `StepData` (accs, blks,
bases, sums, lhsAccs, addCells, bp.gm, bp.scals, bp.gbCells, bp.rhsCells, bp.lhs, gXY) cost **0 ms**.
So forcing ONE scalar out of a stage's result forces that whole stage, and these rows are honest.
-/
import Dregg2.Circuit.Emit.KimchiStepMainCore
open Dregg2.Circuit.Emit.KimchiStepMain

set_option maxRecDepth 100000

def force (n : Nat) (what : String) : IO Nat := do
  if n == 0 then throw (IO.userError s!"probe: '{what}' produced nothing")
  pure n

def timed (what : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v ← force (f ()) what
  let t1 ← IO.monoMsNow
  IO.println s!"{t1 - t0} ms\tval={v}\t{what}"

def main : IO Unit := do
  let s := shapeStep
  let t := mkStep s
  let bs := stepBases s
  IO.println "-- 0. CANARY + the two primitives, priced per call --"
  timed "fInv x1000" (fun _ =>
    ((List.range 1000).foldl
      (fun acc k => acc + Dregg2.Circuit.Emit.KimchiRenderCompleteAdd.fInv (k + 7)) 1))
  timed "permStates x100" (fun _ =>
    (List.range 100).foldl
      (fun acc k => acc + ((permStates [k + 1, k + 2, k + 3]).getLastD []).getD 0 0) 1)
  IO.println "-- 1. the SPONGES (val = permutation count of that stage) --"
  timed "runSponge s bs (0,0)   [transcript, PASS 1 of 2]" (fun _ =>
    (runSponge s bs (0, 0)).perms.length)
  timed "runSeg (optSpec s)     [segment A]" (fun _ => (runSeg (optSpec s)).perms.length)
  timed "runSeg t.specB         [segment B / fr-sponge]" (fun _ => (runSeg t.specB).perms.length)
  timed "runSeg t.specC         [segment C]" (fun _ => (runSeg t.specC).perms.length)
  timed "runSeg t.specD         [segment D]" (fun _ => (runSeg t.specD).perms.length)
  IO.println "-- 2. the CURVE / field stages (these are where fInv lives) --"
  timed "stepBases s" (fun _ => (stepBases s).length)
  timed "runEndo x1 (32 endo blocks)" (fun _ => (runEndo s (0, 0) 12345).1.length)
  timed "runIpa s bs t.sp t.ftc.out (0,0)  [ipaRounds endo ladders]" (fun _ =>
    (runIpa s bs t.sp t.ftc.out (0, 0) (t.defc.pre.getD 0 0)).accs.length)
  timed "runMsm s bs (real scalars)" (fun _ =>
    (runMsm s bs (msmScalars s (chalOf s t.sp) (digestBeforeEvalsVal s t.sp) t.ft t.fin t.segC)).terms.length)
  timed "runFtc s t.ftw" (fun _ => (runFtc s t.ftw).terms.length)
  timed "runFt s t.sp" (fun _ => (runFt s t.sp).vals.size)
  IO.println "-- 3. the whole thing, for the accounting --"
  -- ⚠⚠ **THIS ROW READS 0 ms AND IT IS A THIRD HARNESS TRAP, NOT A RESULT.** `let t := mkStep s`
  -- above already evaluated `mkStep s`, and the compiler shares the identical closed application
  -- rather than re-running it — the same sharing that makes `FloorProbe3`'s REPEATED canary row
  -- read 0 ms after the first one costs 229 ms. `mkStep`'s real cost is 7 085 ms (`FloorProbe3`,
  -- where nothing bound `t` before the window) and 7 143 ms (`EmitStepMainJson`'s own "chain
  -- evaluation" line, an independent instrument). ⚑ A row is only a measurement if NOTHING earlier
  -- in the process already forced the same term.
  timed "mkStep shapeStep (SHARED with `t` above — reads 0, see note)" (fun _ => (mkStep s).gXY.1 + 1)
