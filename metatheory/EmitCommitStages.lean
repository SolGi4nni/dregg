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
  | ["golds"]      => do
      IO.println s!"agg_out  {(sumOut XI_TERMS)}"
      IO.println s!"agg_gold {toAff Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD}"
      IO.println s!"pub_out  {(sumOut PUBLIC_TERMS)}"
      IO.println s!"pub_gold {toAff Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_COMM_GOLD}"
      IO.println s!"ft_out   {(sumOut FT_TERMS)}"
      IO.println s!"ft_gold  {toAff Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD}"
      IO.println s!"f_out    {(sumOut [toAff Dregg2.Circuit.Emit.MinaWrapGroupGate.fComm])}"
      IO.println s!"f_gold   {toAff Dregg2.Circuit.Emit.MinaWrapGroupGate.F_COMM_GOLD}"
  | _ => IO.eprintln "usage: EmitCommitStages.lean (sizes|golds|xi|pub|f|ft|agg|ladder)[trace|pis]"
