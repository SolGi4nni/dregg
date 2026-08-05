/-
# `mina_chain_emit` — the 46 witnesses of Mina devnet block 539508's phase-2 transcript.

`EmitPastaAlu.lean` renders the same objects through `lake env lean --run`, i.e. Lean's
INTERPRETER: one 2 048×469 trace costs **9 min 20 s** there (measured 2026-08-05), so the 46-link
chain would be seven hours of rendering. That is a codegen fact, not a cost of the chain — this file
is the same emit as a compiled `lean_exe`.

It authors nothing. Every cell comes from `MinaPhase2Chain.chainTrace`, i.e. `runRowsVecAt`, the
strict generator `runRowsVecAt_is_runRowsAt` welds to `runRowsAt`; every public input comes from
`MinaPhase2Chain.chainPIs`. House Law #1.

    lake build mina_chain_emit
    ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink

⚠ DELIBERATELY NOT IN `defaultTargets`, like `mina_sg_bench`: it drags the whole Pasta sponge cone
through C codegen. Build it explicitly.

The output is ~150 MB across 46 traces and is NOT tracked. The 46 PI vectors (~40 KB) are, because
they are the objects the fold's continuity claim is about and a reader can check the chain from
them alone.
-/
import Dregg2.Circuit.Emit.MinaPhase2Chain

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.MinaPhase2Chain

def render (r : List Int) : String := String.intercalate " " (r.map toString)

/-- Emit the descriptor, then each link's public inputs and trace, in chain order.

    `mina_chain_emit <dir> [count]` — `count` defaults to all 46.

⚑ **WHY `count` EXISTS.** The 46 traces are ~45 min of rendering, and a fold gate that needs all of
them before it can run is a gate every CI machine reports RED. §1–§4 of
`circuit-prove/tests/mina_phase2_chain_fold.rs` reach only links 0–3, so `mina_chain_emit <dir> 4`
is **~4 minutes** and makes the two-link fold, the four-link fold, both tamper polarities and the
`RecursionVk` determinism tooth live from a cold checkout. Only §5 (the whole chain) needs all 46.

The 46 PUBLIC-INPUT vectors are always emitted in full — they cost seconds, they are tracked, and
§0's continuity check is about them. -/
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "chainlink-witness"
  let count := match args.drop 1 with
    | c :: _ => min 46 (c.toNat!)
    | [] => 46
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/pasta-fq-chainlink.json") (emitVmJson2 chainDesc ++ "\n")
  IO.println s!"descriptor -> {dir}/pasta-fq-chainlink.json"

  -- The public inputs of ALL 46, always: seconds to render, and they are the objects the fold's
  -- continuity claim is about.
  let allPis := (List.range 46).map (fun j => render (chainPIs j))
  IO.FS.writeFile (dir ++ "/chainlink-pis.txt") (String.intercalate "\n" allPis ++ "\n")
  IO.println s!"all 46 public-input vectors -> {dir}/chainlink-pis.txt"

  for j in [0:count] do
    IO.FS.writeFile s!"{dir}/link-{j}-pis.txt" (allPis.getD j "" ++ "\n")
    let rows := (chainTrace j).map render
    IO.FS.writeFile s!"{dir}/link-{j}-trace.txt" (String.intercalate "\n" rows ++ "\n")
    IO.println s!"link {j}/{count} emitted ({rows.length} rows)"

  if count < 46 then
    IO.println s!"⚠ PARTIAL: {count}/46 traces. §5 (the whole chain) needs all 46."
  return 0
