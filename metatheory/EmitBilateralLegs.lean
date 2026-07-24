/-
# EmitBilateralLegs — emit the bilateral-aggregation descriptor + its two LEG descriptors (the
CROSS-SIDE EXISTENCE and BUNDLE-TREE FOLD AIRs, all under law #1) as byte-exact JSON.

Prints three TSV lines from the verified emissions. The aggregation leg emits the COMPACTED v3
descriptor (`Dregg2/Circuit/Emit/BilateralAggregationCompact.lean`, `bilateralAggDescriptorV3` —
width 52, the tautological expected-block self-check DELETED, 13 identity-carry window gates added,
proven a strict strengthening of v2 against the deployed `Satisfied2`), the byte source of
`circuit/descriptors/dregg-bilateral-aggregation-v3.json`. The two legs emit
`circuit/descriptors/dregg-cross-side-existence-v2.json` and
`circuit/descriptors/dregg-bundle-tree-fold-v2.json` (`…CrossSide.lean`, `…BundleFold.lean`).
SCRATCH executable: run with `lake env lean --run EmitBilateralLegs.lean`.
-/
import Dregg2.Circuit.Emit.BilateralAggregationCompact
import Dregg2.Circuit.Emit.EffectVmEmitCrossSide
import Dregg2.Circuit.Emit.EffectVmEmitBundleFold

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.BilateralAggregationCompact (bilateralAggDescriptorV3)
open Dregg2.Circuit.Emit.EffectVmEmitCrossSide (crossSideDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitBundleFold (bundleFoldDescriptor)

def main : IO Unit := do
  IO.println s!"bilateralAggDescriptorV3\t{bilateralAggDescriptorV3.name}\t{emitVmJson2 bilateralAggDescriptorV3}"
  IO.println s!"crossSideDescriptor\t{crossSideDescriptor.name}\t{emitVmJson2 crossSideDescriptor}"
  IO.println s!"bundleFoldDescriptor\t{bundleFoldDescriptor.name}\t{emitVmJson2 bundleFoldDescriptor}"
