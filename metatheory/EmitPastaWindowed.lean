/-
SCRATCH executable: emit the windowed Pasta RCB row descriptor as IR-v2 JSON.

  lake env lean --run EmitPastaWindowed.lean > ../circuit/descriptors/by-name/pasta-rcb-windowed.json

The descriptor is `Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc` — the Lean-authored
windowed AIR whose column bounds `windowedRowDesc_columns_in_bounds` already discharges in the
kernel. This file only RENDERS it; it authors nothing.
-/
import Dregg2.Circuit.Emit.PastaMsmWindowed

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmWindowed (windowedRowDesc)

def main : IO Unit := IO.println (emitVmJson2 windowedRowDesc)
