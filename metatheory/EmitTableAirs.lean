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
import Dregg2.Circuit.Emit.MemoryTableEmit
import Dregg2.Circuit.Emit.UMemoryTableEmit
import Dregg2.Circuit.Emit.UMemBoundaryCohortTableEmit
import Dregg2.Circuit.Emit.UMemBoundaryTableEmit
import Dregg2.Circuit.Emit.MapOpsTableEmit
import Dregg2.Circuit.Emit.ChipTableEmit

open Dregg2.Circuit.TableAirIR (TableAir emitTableAirJson)

/-- The routing table: artifact filename ↦ its Lean author. -/
def tableAirs : List (String × TableAir) :=
  [ ("dregg-ir2-map-absent-v1.json",   Dregg2.Circuit.Emit.MapAbsentTableEmit.mapAbsentTable)
  , ("dregg-ir2-byte-v1.json",         Dregg2.Circuit.Emit.ByteTableEmit.byteTable)
  , ("dregg-ir2-mem-boundary-v1.json", Dregg2.Circuit.Emit.MemBoundaryTableEmit.memBoundaryTable)
  , ("dregg-ir2-memory-v1.json",       Dregg2.Circuit.Emit.MemoryTableEmit.memoryTable)
  , ("dregg-ir2-umemory-v1.json",      Dregg2.Circuit.Emit.UMemoryTableEmit.umemoryTable)
  , ("dregg-ir2-umem-boundary-cohort-v1.json",
      Dregg2.Circuit.Emit.UMemBoundaryCohortTableEmit.cohortTable)
  , ("dregg-ir2-umem-boundary-v1.json",
      Dregg2.Circuit.Emit.UMemBoundaryTableEmit.umemBoundaryTable)
  , ("dregg-ir2-map-ops-v1.json",      Dregg2.Circuit.Emit.MapOpsTableEmit.mapOpsTable)
  , ("dregg-ir2-chip-v1.json",         Dregg2.Circuit.Emit.ChipTableEmit.chipTable)
  , ("dregg-ir2-chip-state16-v1.json", Dregg2.Circuit.Emit.ChipTableEmit.chipState16Table) ]

#guard tableAirs.length == 10

def main : IO Unit := do
  for (file, t) in tableAirs do
    IO.println s!"{file}\t{emitTableAirJson t}"
