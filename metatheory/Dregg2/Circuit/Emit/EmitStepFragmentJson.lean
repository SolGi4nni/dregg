/-
# Dregg2.Circuit.Emit.EmitStepFragmentJson — the `--run` emit driver for the multi-step step_main fragment

Thin executable: writes the Lean-assembled + Lean-placed + `WitnessBuilder`-composed multi-step MSM
fragment (K var_base_mul scalar multiplications + one endo_mul scalar multiplication, summed by a
`complete_add` chain) and its UNWIRED control to `/tmp/pickles-stepfragment/*.json`, which the
`pickles-stepfragment-harness` Rust crate proves + verifies. Carries a `main` (kept OUT of the
assembly module so it roots cleanly into `PicklesSynthesis`).

    lake env lean --run Dregg2/Circuit/Emit/EmitStepFragmentJson.lean            # the committed shape
    DREGG_SF_SHAPE=K,C,E lake env lean --run Dregg2/Circuit/Emit/EmitStepFragmentJson.lean   # a scale rung

(the shape comes through the environment, not `argv`: `lean --run` does not forward trailing
arguments to `main` through `lake env`, and a silently-ignored argument emitting the DEFAULT shape
under a scale-rung filename is exactly the measurement that lies.)

The scale form also reports the Lean-side wall-clock split three ways — chain evaluation, placement
(`place`), witness composition (`WitnessBuilder.compose`) — because that split, not the prover, is
what governs whether this assembly reaches full `step_main` (~17,806 rows). See the harness header.

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiComposeStepFragment

open Dregg2.Circuit.Emit.KimchiComposeStepFragment
open Dregg2.Circuit.Emit.KimchiPlacement (place)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (renderCircuit)

/-- Force a `Nat` before the next clock read. `let x := e` for pure `e` is FLOATABLE — the compiler
happily sinks the work past an `IO.monoMsNow`, which is how a phase split silently reports `0 ms` for
the phase that actually ran. An `IO` action that inspects the value pins it in place. -/
def force (n : Nat) : IO Nat := do
  if n == 0 then throw (IO.userError "emitShape: a phase produced nothing — the shape is degenerate")
  pure n

/-- Emit one shape, reporting the phase split. Returns the row count. -/
def emitShape (dir : String) (tag : String) (sh : Shape) : IO Nat := do
  let t0 ← IO.monoMsNow
  let f := mkFrag sh
  let nAcc ← force ((f.terms.map (fun td => td.accs.length)).foldl (· + ·) f.endoAccs.length)
  let t1 ← IO.monoMsNow
  let rows := fragRows f true
  let rowsU := fragRows f false
  let n := rows.length
  let _ ← force (n + rowsU.length)
  let t2 ← IO.monoMsNow
  let placed := place 0 (fragGates rows)
  let placedU := place 0 (fragGates rowsU)
  let nw ← force ((placed.map (fun g => g.wires.length)).foldl (· + ·) 0
                  + (placedU.map (fun g => g.wires.length)).foldl (· + ·) 0)
  let t3 ← IO.monoMsNow
  let w := fragWitness f
  let ncell ← force ((w.map (·.length)).foldl (· + ·) 0)
  let t4 ← IO.monoMsNow
  let js := renderCircuit s!"stepFragment_{tag}" 0 n placed w
  let jsU := renderCircuit s!"stepFragment_{tag}_UNWIRED" 0 n placedU w
  IO.FS.writeFile s!"{dir}/stepfragment_{tag}.json" js
  IO.FS.writeFile s!"{dir}/stepfragment_{tag}_unwired.json" jsU
  let t5 ← IO.monoMsNow
  IO.println s!"[{tag}] K={sh.terms} C={sh.chunks} E={sh.endoBlocks}  rows={n}  \
    cells={ncell} accs={nAcc} wires={nw}"
  IO.println s!"    chains {t1 - t0} ms | rows {t2 - t1} ms | place {t3 - t2} ms | \
compose {t4 - t3} ms | render+write {t5 - t4} ms | TOTAL {t5 - t0} ms"
  IO.println s!"    probe rows = {((rows.zip (List.range n)).filter (fun ri => ri.1.probe)).map (·.2)}"
  pure n

def main : IO Unit := do
  let dir := "/tmp/pickles-stepfragment"
  IO.FS.createDirAll dir
  let spec ← IO.getEnv "DREGG_SF_SHAPE"
  match (spec.getD "").splitOn "," with
  | [k, c, e] =>
      let sh : Shape := { terms := k.toNat!, chunks := c.toNat!, endoBlocks := e.toNat! }
      let _ ← emitShape dir s!"K{k}_C{c}_E{e}" sh
      pure ()
  | _ =>
      -- The committed fixture: emitted from the module's own nullary defs, so what the harness
      -- proves is byte-identically what the in-CI `#guard`s pinned.
      IO.FS.writeFile s!"{dir}/stepfragment.json" stepFragmentJson
      IO.FS.writeFile s!"{dir}/stepfragment_unwired.json" stepFragmentUnwiredJson
      IO.println s!"EmitStepFragmentJson: wrote {dir}/stepfragment.json + stepfragment_unwired.json"
      IO.println s!"  shape K={shapeS.terms} C={shapeS.chunks} E={shapeS.endoBlocks} \
→ rows={nRowsS}  gates={placedS.length}  witness cols={witnessS.length}"
      IO.println s!"  gate census: varBaseMul=48 endoMul=16 completeAdd=6 zero=62 (pinned in-module)"
      IO.println s!"  probe rows (Zero, σ-only) = {probeRowsS}"
      IO.println s!"  endo chain starts at row {endoStartS}; final MSM sum = {fragS.sums.getLastD (0,0)}"
