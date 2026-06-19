/-
# EmitCrossCellConservation — emit the TURN-WIDE CROSS-CELL CONSERVATION AIR descriptor (law #1)
as byte-exact JSON.

Prints the verified emission of `Dregg2/Circuit/CrossCellConservation.lean` — the byte source of
`circuit/descriptors/dregg-cross-cell-conservation-v1.json`. SCRATCH executable: run with
`lake env lean --run EmitCrossCellConservation.lean`.
-/
import Dregg2.Circuit.CrossCellConservation

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.CrossCellConservation (crossCellConservationDescriptor)

def main : IO Unit := do
  IO.println (emitVmJson2 crossCellConservationDescriptor)
