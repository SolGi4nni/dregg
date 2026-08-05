/-
SCRATCH executable: emit the COMMITMENT-COMBINATION stage descriptors and their honest traces.

  lake env lean --run EmitCommitStages.lean sizes
  lake env lean --run EmitCommitStages.lean <name>       > ../circuit/descriptors/by-name/<file>.json
  lake env lean --run EmitCommitStages.lean <name>trace  > ../circuit/tests/fixtures/<file>-trace.txt
  lake env lean --run EmitCommitStages.lean <name>pis    > ../circuit/tests/fixtures/<file>-pis.txt

Names: `xi` (the ξ scalar vector), `pub` / `f` / `ft` / `agg` (the four group folds), `ladder`
(the scalar-multiplication ladder). This file only RENDERS; it authors nothing — every descriptor is
`EffectLower.lowerAir` of a Lean-authored `EffectAir` in
`Dregg2.Circuit.Emit.MinaWrapCommitStages`.
-/
import Dregg2.Circuit.Emit.MinaWrapCommitStages
import Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.MinaWrapCommitStages

def render (r : List Int) : String := String.intercalate " " (r.map toString)
def renderRows (rs : List (List Int)) : String :=
  String.intercalate "\n" (rs.map render) ++ "\n"

def sizes : IO Unit := do
  IO.println s!"xi      instrs={(xiProg).length}"
  IO.println s!"pub     instrs={(foldProg PUBLIC_TERMS).length} terms={PUBLIC_TERMS.length}"
  IO.println s!"f       instrs={(foldProg [toAff Dregg2.Circuit.Emit.MinaWrapGroupGate.fComm]).length} terms=1"
  IO.println s!"ft      instrs={(foldProg FT_TERMS).length} terms={FT_TERMS.length}"
  IO.println s!"agg     instrs={(foldProg XI_TERMS).length} terms={XI_TERMS.length}"
  IO.println s!"ladder  instrs={(ladderProg).length} planes={DEMO_PLANES} scalar={DEMO_SCALAR}"
  IO.println s!"width   {Dregg2.Circuit.Emit.MinaWrapCommitMachine.CM_WIDTH}"

def main (args : List String) : IO Unit :=
  match args with
  | ["sizes"]      => sizes
  | ["xi"]         => IO.println (emitVmJson2 xiDesc)
  | ["xitrace"]    => IO.print (renderRows xiTrace)
  | ["xipis"]      => IO.print (render xiPIs ++ "\n")
  | ["pub"]        => IO.println (emitVmJson2 publicCommDesc)
  | ["pubtrace"]   => IO.print (renderRows (foldTrace PUBLIC_TERMS))
  | ["pubpis"]     => IO.print (render (foldPIs PUBLIC_TERMS) ++ "\n")
  | ["f"]          => IO.println (emitVmJson2 fCommDesc)
  | ["ftrace"]     => IO.print (renderRows (foldTrace [toAff Dregg2.Circuit.Emit.MinaWrapGroupGate.fComm]))
  | ["fpis"]       => IO.print (render (foldPIs [toAff Dregg2.Circuit.Emit.MinaWrapGroupGate.fComm]) ++ "\n")
  | ["ft"]         => IO.println (emitVmJson2 ftCommDesc)
  | ["fttrace"]    => IO.print (renderRows (foldTrace FT_TERMS))
  | ["ftpis"]      => IO.print (render (foldPIs FT_TERMS) ++ "\n")
  | ["agg"]        => IO.println (emitVmJson2 xiAggDesc)
  | ["aggtrace"]   => IO.print (renderRows (foldTrace XI_TERMS))
  | ["aggpis"]     => IO.print (render (foldPIs XI_TERMS) ++ "\n")
  | ["ladder"]     => IO.println (emitVmJson2 ladderDesc)
  | ["laddertrace"]=> IO.print (renderRows ladderTrace)
  | ["ladderpis"]  => IO.print (render ladderPIs ++ "\n")
  -- ⚑ The `golds` case is DELETED. It printed each fold's output next to its o1-labs golden on
  -- adjacent lines, and a human agreeing the digits matched was the entire weld. The comparison is
  -- now four NAMED THEOREMS in `MinaWrapCommitStages` §6c —
  -- `the_xi_fold_is_o1_labs_aggregate` and its three siblings, plus
  -- `the_four_goldens_are_distinct` so they cannot all be satisfied by one collapsed constant.
  | ["aggmsm"]     => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm.xiAggMsmDesc)
  -- ⚑ The four o1-labs goldens as limb pairs, taken from the GATE CONSTANTS and never from any
  -- fold's own output. This is the anchor `circuit/tests/mina_commit_stages_prove.rs` recomputes
  -- against, so that test carries NO transcribed decimal: it reads the term points out of the
  -- emitted descriptor's ROM, folds them in Rust, and lands here.
  | ["goldlimbs"]  => do
      let emit (g : Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt) : IO Unit :=
        IO.println (render (piPair (toAff g).1 (toAff g).2))
      emit Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_COMM_GOLD
      emit Dregg2.Circuit.Emit.MinaWrapGroupGate.F_COMM_GOLD
      emit Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD
      emit Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD
  | _ => IO.eprintln
      "usage: EmitCommitStages.lean (sizes|xi|pub|f|ft|agg|ladder)[trace|pis] | aggmsm | goldlimbs"
