/-
SCRATCH executable: emit ONE **curve-gated, contents-bound** sliced Pasta RCB descriptor as IR-v2
JSON, over the REAL Mina devnet Wrap SRS generators.

  lake env lean --run EmitPastaOnCurve.lean <k>
      > ../circuit/tests/fixtures/pasta-sg-bound/pasta-rcb-sg-oncurve-<k>-of-4.json

The descriptor is `Dregg2.Circuit.Emit.PastaMsmOnCurve.onCurveRowDesc 4 k 31 4
MinaWrapSrsG.SRS_G SCAL` — `PastaMsmBound.boundRowDesc`'s 82 constraints and its exact-public
manifest verbatim (`onCurveRowDesc_extends_bound` proves the prefix in the kernel), plus the 16
ON-CURVE constraints that force both operands of every row's RCB add to be genuine points of the
Pallas curve with `Y` a unit. 98 constraints, 799 columns, manifest unchanged. This file only
RENDERS it; it authors nothing.

⚠ SAME REASON AS `EmitPastaBound.lean` FOR NOT BEING IN `EmitByName.lean`: it imports
`Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points, ~32 s just to elaborate), allowlisted out
of the `Dregg2` root by `scripts/lean-orphans-allow.txt`. The emitted artifacts are sha256-pinned in
`circuit/tests/pasta_oncurve_gate.rs` instead, which is the check that actually reads them.

⚠ `SCAL` is the SAME reproducible synthetic sequence `EmitPastaBound.lean` uses, so the on-curve
descriptor and the contents-bound descriptor differ in EXACTLY the 16 constraints and 270 columns —
which is what makes `pasta_oncurve_gate.rs`'s before/after a measurement of the gate rather than of
two unrelated objects.

  parameters:  4 slices x 31 generators = 124 real SRS generators
               4 bit planes  ⇒  4 * (31+1) = 128 trace rows = 128 manifest rows
-/
import Dregg2.Circuit.Emit.PastaMsmOnCurve
import Dregg2.Circuit.Emit.MinaWrapSrsG

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmOnCurve (onCurveRowDesc)

/-- The demonstration scalars — byte-identical to `EmitPastaBound.lean`'s. -/
def SCAL : List Nat := (List.range 124).map (fun i => (7 + 13 * i) % 16)

def main (args : List String) : IO Unit := do
  let k := (args[0]?).bind String.toNat? |>.getD 0
  IO.println (emitVmJson2
    (onCurveRowDesc 4 k 31 4 Dregg2.Circuit.Emit.MinaWrapSrsG.SRS_G SCAL))
