/-
StepCensusProbe — WHICH conjunct of `the_step_prover_choice_census` moved under §24, measured
rather than guessed. The helpers are `KimchiStepProverChoice`'s, inlined because that module is the
one that is red and its olean therefore does not exist.

    cd metatheory && LEAN_PATH=$(lake env printenv LEAN_PATH) lean --run wip/StepCensusProbe.lean
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture
open Dregg2.Circuit.Emit.KimchiStepMain
open Dregg2.Circuit.Emit.KimchiPlacement (PVar varIx)
open Dregg2.Circuit.Emit.KimchiTarget (K_PERMUTS)
open Dregg2.Circuit.Emit.WitnessBuilder (VarEnv envIxBound)

set_option maxRecDepth 100000

def isWitP : AOp → Bool | .wit _ => true | _ => false
def witSlotsP (prog : Array AOp) : List Nat :=
  (List.range prog.size).filter (fun i => isWitP (prog.getD i default))

def wiredIxsP (bound : Nat) (rows : List SRow) : Array Bool :=
  rows.foldl (fun a r =>
    (r.perm.take K_PERMUTS).foldl (fun a o =>
      match o with
      | none => a
      | some v => if varIx v < bound then a.set! (varIx v) true else a) a)
    (Array.replicate bound false)

def envVarsNoRowReadsP (env : VarEnv) (rows : List SRow) : List PVar :=
  let bound := envIxBound env + 1
  let w := wiredIxsP bound rows
  (env.foldl (fun (acc : Array Bool × List PVar) e =>
      let i := varIx e.1
      if i < bound then
        (if acc.1.getD i false then acc
         else (acc.1.set! i true, if w.getD i false then acc.2 else e.1 :: acc.2))
      else acc)
    (Array.replicate bound false, ([] : List PVar))).2.reverse

def occIxsP (bound : Nat) (rows : List SRow) : Array Nat :=
  rows.foldl (fun a r =>
    (r.perm.take K_PERMUTS).foldl (fun a o =>
      match o with
      | none => a
      | some v => if varIx v < bound then a.modify (varIx v) (· + 1) else a) a)
    (Array.replicate bound 0)

def occAtP (o : Array Nat) (v : PVar) : Nat := o.getD (varIx v) 0

def rowsStepP : List SRow := rungRows tStep .opening true
def occStepP : Array Nat := occIxsP (envIxBound (circuitEnv tStep) + 1) rowsStepP

def chk (name : String) (got was : Nat) : IO Unit :=
  let tag := if got == was then "  ok " else "MOVED"
  IO.println s!"{tag}  {name}: {got}  (census says {was})"

def main : IO Unit := do
  chk "witSlots ft           " (witSlotsP tStep.ft.fp.prog).length 1
  chk "witSlots fin          " (witSlotsP tStep.fin.fp.prog).length 9
  chk "envVarsNoRowReads step" (envVarsNoRowReadsP (circuitEnv tStep) rowsStepP).length 20
  chk "aeq count             "
    ((tStep.ft.fp.prog.toList ++ tStep.fin.fp.prog.toList).countP
      (fun o => match o with | .aeq _ _ => true | _ => false)) 17
  chk "occ vDHi 0            " (occAtP occStepP (vDHi shapeStep 0)) 0
  chk "occ vDHi 1            " (occAtP occStepP (vDHi shapeStep 1)) 2
  chk "occ vStmtWrapMsgs     " (occAtP occStepP (vStmtWrapMsgs shapeStep)) 1
  chk "occ vStmtLookup       " (occAtP occStepP (vStmtLookup shapeStep)) 1
  chk "occ bpZ1              " (occAtP occStepP (bpZ1 shapeStep)) 1
  chk "occ bpZ2              " (occAtP occStepP (bpZ2 shapeStep)) 1
  chk "occ vGx               " (occAtP occStepP (vGx shapeStep)) 5
  chk "occ vDomLog2          " (occAtP occStepP (vDomLog2 shapeStep)) 2
  chk "occ vTPad             " (occAtP occStepP (vTPad shapeStep)) 2
  IO.println s!"  flags all 0 = {(List.range 9).all (fun k => occAtP occStepP (vStmtFlag shapeStep k) == 0)}"
  IO.println s!"  vCipBit = bpOdd 0 = {vCipBit shapeStep == bpOdd shapeStep 0}"
  IO.println "-- context --"
  IO.println s!"  occ vCipShift = {occAtP occStepP (vCipShift shapeStep)}"
  IO.println s!"  occ vBShift   = {occAtP occStepP (vBShift shapeStep)}"
  IO.println s!"  occ vStmtWrapMsg0 = {occAtP occStepP (vStmtWrapMsg0 shapeStep)}"
