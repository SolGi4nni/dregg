/-
# EmitTableAirs — the byte source for the Lean-authored TABLE AIRs.

Prints one `<filename>\t<emitTableAirJson t>` line per checked-in table AIR, the same
`<file>\t<json>` shape `EmitByName.lean` uses, so the artifacts under
`circuit/descriptors/table-airs/` are regenerable FROM THE VERIFIED LEAN EMISSION rather than
hand-transcribed.

    lake env lean --run EmitTableAirs.lean

Law #1: the constraints are AUTHORED in `Dregg2/Circuit/Emit/*TableEmit.lean` (proved there, with
their `#guard` shape pins and byte golden); this file only SERIALIZES them.
-/
import Dregg2.Circuit.Emit.MapAbsentTableEmit
import Dregg2.Circuit.Emit.ByteTableEmit
import Dregg2.Circuit.Emit.MemBoundaryTableEmit

open Dregg2.Circuit.TableAirIR (TableAir emitTableAirJson)

/-- The routing table: artifact filename ↦ its Lean author. -/
def tableAirs : List (String × TableAir) :=
  [ ("dregg-ir2-map-absent-v1.json",   Dregg2.Circuit.Emit.MapAbsentTableEmit.mapAbsentTable)
  , ("dregg-ir2-byte-v1.json",         Dregg2.Circuit.Emit.ByteTableEmit.byteTable)
  , ("dregg-ir2-mem-boundary-v1.json", Dregg2.Circuit.Emit.MemBoundaryTableEmit.memBoundaryTable) ]

#guard tableAirs.length == 3

def main : IO Unit := do
  for (file, t) in tableAirs do
    IO.println s!"{file}\t{emitTableAirJson t}"
