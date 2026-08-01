/-
# Dregg2.Circuit.Emit.EmitCurveGateJson — the `--run` emit driver for the CURVE-gate circuits

Thin executable: writes the Lean-assembled + Lean-placed + Lean-witnessed curve-gate circuits (the
`complete_add`, and — as they land — `var_base_mul` / `endo_mul` / `endo_mul_scalar`) to
`/tmp/pickles-curvegate/*.json`, which the `pickles-curvegate-harness` Rust crate proves + verifies.
Carries a `main` (kept OUT of the render modules so they root cleanly into `PicklesSynthesis`). Run:

    lake env lean --run Dregg2/Circuit/Emit/EmitCurveGateJson.lean

House Law #1: the CIRCUITS are Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMul

open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (endoMulScalarJson emsPlaced emsWitness n8val)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (varBaseMulJson vbmPlaced vbmWitness nNextVal)
open Dregg2.Circuit.Emit.KimchiRenderEndoMul (endoMulJson emPlaced emWitness)

def main : IO Unit := do
  let dir := "/tmp/pickles-curvegate"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/complete_add.json") completeAddJson
  IO.println s!"EmitCurveGateJson: wrote {dir}/complete_add.json"
  IO.println s!"  complete_add: gates = {caPlaced.length}  witness cols = {caWitness.length}  rows = 2"
  IO.println s!"  P = G, Q = [2]G, output (x3,y3) = [3]G = ({caCells.getD 4 0}, {caCells.getD 5 0})"
  IO.FS.writeFile (dir ++ "/endo_mul_scalar.json") endoMulScalarJson
  IO.println s!"EmitCurveGateJson: wrote {dir}/endo_mul_scalar.json"
  IO.println s!"  endo_mul_scalar: gates = {emsPlaced.length}  witness cols = {emsWitness.length}  rows = 2"
  IO.println s!"  reconstructed scalar n8 = {n8val}"
  IO.FS.writeFile (dir ++ "/var_base_mul.json") varBaseMulJson
  IO.println s!"EmitCurveGateJson: wrote {dir}/var_base_mul.json"
  IO.println s!"  var_base_mul: gates = {vbmPlaced.length}  witness cols = {vbmWitness.length}  rows = 2  n' = {nNextVal}"
  IO.FS.writeFile (dir ++ "/endo_mul.json") endoMulJson
  IO.println s!"EmitCurveGateJson: wrote {dir}/endo_mul.json"
  IO.println s!"  endo_mul: gates = {emPlaced.length}  witness cols = {emWitness.length}  rows = 2"
