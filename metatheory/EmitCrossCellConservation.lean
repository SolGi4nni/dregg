/-
# EmitCrossCellConservation — emit the TURN-WIDE CROSS-CELL CONSERVATION AIR descriptor (law #1)
as byte-exact JSON.

Prints the verified emission of `Dregg2/Circuit/CrossCellConservation.lean` — the byte source of
`circuit/descriptors/dregg-cross-cell-conservation-v2.json` (the live artifact; this pointed at a `-v1.json` that does not exist — a fossil of the phantom-commit episode). SCRATCH executable: run with
`lake env lean --run EmitCrossCellConservation.lean`.
-/
import Dregg2.Circuit.CrossCellConservation

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.CrossCellConservation (crossCellConservationDescriptor)

def main : IO Unit := do
  IO.println (emitVmJson2 crossCellConservationDescriptor)
