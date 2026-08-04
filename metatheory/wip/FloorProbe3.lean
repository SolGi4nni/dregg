/-
FloorProbe3 — the per-family split of the `shapeStep` floor, in ONE cold process, against a
**FRESHLY BUILT** olean.

    cd metatheory && lake build Dregg2.Circuit.Emit.KimchiStepMainCore
    LEAN_PATH=$(lake env printenv LEAN_PATH) lean --run wip/FloorProbe3.lean

⚑ WHY THIS FILE EXISTS — two harness defects, both of which made the previous table announce a
   number that was not the number anyone wanted:

  1. `FloorProbe2`'s first draft took `(n : Nat)` and started the clock INSIDE `timed`. Lean is
     strict, so every argument was already forced at the CALL SITE and every row printed 0 ms.
     Fixed by thunking (`f : Unit → Nat`).
  2. ⚑⚑ …and the corrected run STILL measured the wrong program: `lean --run` loads the **olean**,
     and `.lake`'s `KimchiStepMainCore.olean` was stamped 19:24 while `cfc5783eb` (the `rungOwn`
     rewrite) landed at 20:06. The table said `rungRows .transcript` = 6 480 ms against
     `transcriptRows` = 92 ms, a 70×, and that 70× WAS the pre-rewrite `let`-above-`match` defect,
     faithfully measured on a stale artifact. **BUILD BEFORE YOU MEASURE.**

⚑ ROW 0 IS A CANARY WITH A KNOWN COST. A row whose true cost you already know is the only thing
that makes a broken harness announce itself instead of reporting a triumph. If `fInv x1000` reads
0 ms, STOP — nothing below it means anything.
-/
import Dregg2.Circuit.Emit.KimchiStepMainCore
open Dregg2.Circuit.Emit.KimchiStepMain

set_option maxRecDepth 100000

def force (n : Nat) (what : String) : IO Nat := do
  if n == 0 then throw (IO.userError s!"probe: '{what}' produced nothing")
  pure n

/-- Time a THUNK. The work happens between the two clock reads, and `force` inspects the result so
the compiler cannot sink it past the second one. -/
def timed (what : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v ← force (f ()) what
  let t1 ← IO.monoMsNow
  IO.println s!"{t1 - t0} ms\tval={v}\t{what}"

def main : IO Unit := do
  let s := shapeStep
  IO.println "-- 0. CANARY: a row whose cost is known independently --"
  timed "fInv x1000 (one Fermat inversion each)" (fun _ =>
    ((List.range 1000).foldl
      (fun acc k => acc + Dregg2.Circuit.Emit.KimchiRenderCompleteAdd.fInv (k + 7)) 1))
  IO.println "-- 1. the ARITHMETIC primitives, so the residue can be priced --"
  timed "permStates x100 (100 Poseidon permutations, 55 rounds each)" (fun _ =>
    (List.range 100).foldl
      (fun acc k => acc + ((permStates [k + 1, k + 2, k + 3]).getLastD []).getD 0 0) 1)
  timed "runEndo x1 (32 endo blocks)" (fun _ =>
    (runEndo s (0, 0) 12345).1.length)
  IO.println "-- 2. the layout chain --"
  timed "spLay shapeStep (.put length)" (fun _ => (spLay s).put.length)
  timed "tBlocks shapeStep" (fun _ => tBlocks s + 1)
  timed "baseFtc shapeStep (ONE variable name)" (fun _ => baseFtc s)
  timed "baseBp  shapeStep (ONE variable name)" (fun _ => baseBp s)
  IO.println "-- 3. mkStep, FORCED INSIDE THE WINDOW (the previous table timed a prebuilt `t`) --"
  timed "mkStep shapeStep FRESH, forced by gXY.1" (fun _ => (mkStep s).gXY.1 + 1)
  let t := mkStep s
  timed "t.gXY.1 on the PREBUILT t (the old row — should be ~0)" (fun _ => t.gXY.1 + 1)
  timed "DEEP walk of the prebuilt t (accs/blks/bases/sums/lhsAccs + bp)" (fun _ =>
    t.ipa.accs.length + t.ipa.blks.length + t.ipa.bases.length + t.ipa.sums.length
    + t.ipa.lhsAccs.length + t.ipa.addCells.length + t.bp.gm.length + t.bp.scals.length
    + t.bp.gbCells.length + t.bp.rhsCells.length + t.bp.lhs.1 + t.gXY.2 + 1)
  IO.println "-- 4. ⚑ THE 70× ISOLATION: four ways to ask for r1_transcript's rows --"
  timed "rungsUpto .transcript |>.length (expect 1)" (fun _ => (rungsUpto .transcript).length)
  timed "transcriptRows t.sh t.sp true" (fun _ => (transcriptRows t.sh t.sp true).length)
  timed "rungOwn t true .transcript" (fun _ => (rungOwn t true .transcript).length)
  timed "rungRows t .transcript true" (fun _ => (rungRows t .transcript true).length)
  IO.println "-- 5. the row families, each on its own --"
  timed "ipaRows" (fun _ => (ipaRows s t.ipa true).length)
  timed "msmRows" (fun _ => (msmRows s t.msm true).length)
  timed "ftcRows" (fun _ => (ftcRows s t.ftw t.ftc true).length)
  timed "bpRows" (fun _ => (bpRows s t.bp true).length)
  timed "finRows" (fun _ => (finRows s t.ft t.fin true).length)
  timed "absRows" (fun _ => (absRows t true).length)
  timed "ftRows" (fun _ => (ftRows s t.ft true).length)
  IO.println "-- 6. the whole objects the census forces --"
  timed "rungRows .opening (ALL fifteen)" (fun _ => (rungRows t .opening true).length)
  timed "rungRows .finalize" (fun _ => (rungRows t .finalize true).length)
  timed "circuitEnv tStep" (fun _ => (circuitEnv t).length)
  IO.println "-- 7. DRIFT CONTROL: repeat row 4's cheapest and row 0's canary --"
  timed "rungRows t .transcript true (REPEAT)" (fun _ => (rungRows t .transcript true).length)
  timed "fInv x1000 (REPEAT canary)" (fun _ =>
    ((List.range 1000).foldl
      (fun acc k => acc + Dregg2.Circuit.Emit.KimchiRenderCompleteAdd.fInv (k + 7)) 1))
