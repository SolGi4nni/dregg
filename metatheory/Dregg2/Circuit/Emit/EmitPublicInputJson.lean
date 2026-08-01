/-
# Dregg2.Circuit.Emit.EmitPublicInputJson — the `--run` emit driver for the PUBLIC-INPUT circuits

Thin executable: writes the four `KimchiRenderPublicInput` circuits to `/tmp/pickles-publicinput/`,
which the `pickles-publicinput-harness` Rust crate proves + verifies. Carries the ONLY `main` in this
render path (kept OUT of `KimchiRenderPublicInput` so that module roots cleanly into
`PicklesSynthesis` — the same split as `EmitPoseidonJson` / `KimchiRenderPoseidon`). Run:

    lake env lean --run Dregg2/Circuit/Emit/EmitPublicInputJson.lean

⚠ `piWide` is 134 rows at `pubSize = 67`, and `KimchiPlacement.place` is QUADRATIC (the wall named in
`3c3f61b24`), so this driver takes minutes, not seconds. It is an OFFLINE emit — the harness reads
the committed JSON and never runs Lean.

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiRenderPublicInput

open Dregg2.Circuit.Emit.KimchiRenderPublicInput

def main : IO Unit := do
  let dir := "/tmp/pickles-publicinput"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/pi_mul_a.json") piMulJsonA
  IO.FS.writeFile (dir ++ "/pi_mul_b.json") piMulJsonB
  IO.FS.writeFile (dir ++ "/pi_nowire.json") piNoWireJson
  IO.println s!"EmitPublicInputJson: wrote {dir}/pi_mul_a.json, pi_mul_b.json, pi_nowire.json"
  IO.println s!"  piMul: pubSize = {piPub}  rows = {piRows}  gates = {piMulPlaced.length}"
  let cellStr (c : Dregg2.Circuit.Emit.KimchiPlacement.Cell) : String :=
    "(" ++ toString c.row ++ "," ++ toString c.col ++ ")"
  IO.println s!"  public cells -> circuit: {String.intercalate " " ((piMulPlaced.take piPub).map (fun g => cellStr (g.wires.headD ⟨0,0⟩)))}"
  IO.println s!"  emitting piWide (pubSize = {wideN}, rows = {piWideRows}) — place is quadratic, this is the slow one"
  IO.FS.writeFile (dir ++ "/pi_wide.json") piWideJson
  IO.println s!"  piWide: pubSize = {wideN}  rows = {piWideRows}  total pinned = {wideTotal}"
  IO.println s!"EmitPublicInputJson: wrote {dir}/pi_wide.json"
