/-
SCRATCH executable: emit ONE **contents-bound** sliced Pasta RCB descriptor as IR-v2 JSON, over the
REAL Mina devnet Wrap SRS generators.

  lake env lean --run EmitPastaBound.lean <k>
      > ../circuit/descriptors/by-name/pasta-rcb-sg-bound-<k>-of-4.json

The descriptor is `Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc 4 k 31 4 MinaWrapSrsG.SRS_G SCAL`
— the Lean-authored four-way cut with `PastaMsmSliced`'s 78 constraints as a PREFIX, plus the two
index threads, the first-row index pin and the ONE exact-public lookup whose manifest carries
`(row key, absolute generator index, digit, 27 generator limbs)` for **the real `srs.g[31k .. 31k+31)`**.
This file only RENDERS it; it authors nothing.

⚠ THIS EMITTER IS NOT IN `EmitByName.lean` AND MUST NOT BE. It imports `MinaWrapSrsG` (32,768 pinned
points, ~32 s just to elaborate, allowlisted out of the `Dregg2` root by
`scripts/lean-orphans-allow.txt`). Putting it in the by-name driver would drag that module into the
descriptor-drift gate's hot path. The emitted artifacts are sha256-pinned in
`circuit/tests/pasta_bound_sg_prove.rs` instead, which is the check that actually reads them.

⚠ THE SCALARS ARE SYNTHETIC, THE GENERATORS ARE NOT. `SCAL` below is a reproducible 4-bit sequence,
not the block's s-vector: binding the s-vector to the block's 15 IPA challenges is a DIFFERENT rung
(`MinaWrapSgCore.SVEC` derives it in the kernel, and nothing here touches that derivation). What this
descriptor forces is that the trace's `BIT` column carries the DECLARED digit and its `SRC` columns
carry the DECLARED generator — and the declared generators are Mina's.

  parameters:  4 slices x 31 generators = 124 real SRS generators
               4 bit planes  ⇒  4 * (31+1) = 128 trace rows = 128 manifest rows
               128 x 30 = 3,840 cells, against the deployed caps 128 rows / 4,096 cells.
-/
import Dregg2.Circuit.Emit.PastaMsmBound
import Dregg2.Circuit.Emit.MinaWrapSrsG

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmBound (boundRowDesc)

/-- The demonstration scalars: 4-bit, reproducible, no randomness in a build artifact. -/
def SCAL : List Nat := (List.range 124).map (fun i => (7 + 13 * i) % 16)

def main (args : List String) : IO Unit := do
  let k := (args[0]?).bind String.toNat? |>.getD 0
  IO.println (emitVmJson2
    (boundRowDesc 4 k 31 4 Dregg2.Circuit.Emit.MinaWrapSrsG.SRS_G SCAL))
