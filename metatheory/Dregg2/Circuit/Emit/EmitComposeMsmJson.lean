/-
# Dregg2.Circuit.Emit.EmitComposeMsmJson — the `--run` emit driver for the 2-gate MSM composition

Thin executable: writes the Lean-assembled + Lean-placed + Lean-witnessed COMPOSED circuit (var_base_mul
→ complete_add with a cross-gate copy-permutation on the shared output point) and its UNWIRED control to
`/tmp/pickles-compose/*.json`, which the `pickles-compose-harness` Rust crate proves + verifies. Carries
a `main` (kept OUT of the render module so it roots cleanly into `PicklesSynthesis`). Run:

    lake env lean --run Dregg2/Circuit/Emit/EmitComposeMsmJson.lean

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiComposeMSM

open Dregg2.Circuit.Emit.KimchiComposeMSM

def main : IO Unit := do
  let dir := "/tmp/pickles-compose"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/compose_msm.json") composeMsmJson
  IO.FS.writeFile (dir ++ "/compose_msm_unwired.json") composeMsmUnwiredJson
  IO.println s!"EmitComposeMsmJson: wrote {dir}/compose_msm.json + compose_msm_unwired.json"
  IO.println s!"  gates = {composePlaced.length}  witness cols = {composeWitness.length}  rows = 4"
  IO.println s!"  var_base_mul output [n]T = (x5,y5) = ({outX}, {outY})"
  IO.println s!"  complete_add output acc' = (x3,y3) = ({caCells2.getD 4 0}, {caCells2.getD 5 0})"
  IO.println s!"  shared x5 class = cells (1,0)->(2,0)->(3,0) (cross-gate 3-cycle); probe cell = (col 0, row 3)"
