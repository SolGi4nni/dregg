/-
SCRATCH executable: emit ONE sliced Pasta RCB row descriptor as IR-v2 JSON.

  lake env lean --run EmitPastaSliced.lean <slices> <k> <width>
      > ../circuit/descriptors/by-name/pasta-rcb-sg-slice-<k>-of-<slices>.json

The descriptor is `Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc slices k width` — the
Lean-authored four-way cut whose column and public-input bounds
(`slicedRowDesc_columns_in_bounds`, `slicedRowDesc_pi_indices_in_bounds`) already discharge in the
kernel, and whose row template is `PastaMsmWindowed`'s verbatim
(`slicedRowDesc_extends_windowed`). This file only RENDERS it; it authors nothing.

⚠ The slice OFFSET is a literal inside the emitted constraint, so the four files are genuinely
different objects — running slice 3's descriptor and calling it slice 0 is refused by the
descriptor, not by a convention.
-/
import Dregg2.Circuit.Emit.PastaMsmSliced

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmSliced (slicedRowDesc)

def main (args : List String) : IO Unit := do
  let n := (args[0]?).bind String.toNat? |>.getD 4
  let k := (args[1]?).bind String.toNat? |>.getD 0
  let w := (args[2]?).bind String.toNat? |>.getD 8192
  IO.println (emitVmJson2 (slicedRowDesc n k w))
