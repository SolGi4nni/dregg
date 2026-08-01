/-
# Dregg2.Circuit.Emit.EmitPoseidonJson — the `--run` emit driver for the Poseidon circuit (R4a-scaled)

Thin executable: writes `KimchiRenderPoseidon.poseidonJson` (the Lean-assembled + Lean-placed +
Lean-witnessed single Poseidon permutation) to `/tmp/pickles-poseidon/poseidon.json`, which the
`pickles-poseidon-harness` Rust crate proves + verifies. Carries the ONLY `main` in the Poseidon
render path (kept OUT of `KimchiRenderPoseidon` so that module roots cleanly into `PicklesSynthesis`
alongside `KimchiRender`, which carries that cone's other `main`). Run:

    lake env lean --run Dregg2/Circuit/Emit/EmitPoseidonJson.lean

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiRenderPoseidon

open Dregg2.Circuit.Emit.KimchiRenderPoseidon

def main : IO Unit := do
  let dir := "/tmp/pickles-poseidon"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/poseidon.json") poseidonJson
  IO.println s!"EmitPoseidonJson: wrote {dir}/poseidon.json"
  IO.println s!"  gates = {poseidonPlaced.length}  witness cols = {poseidonWitness.length}  rows = 12"
  IO.println s!"  output lane0 (= o1js Poseidon.hash([1]) = dregg Ref.hash [1]) = {(stateAt 55).getD 0 0}"
