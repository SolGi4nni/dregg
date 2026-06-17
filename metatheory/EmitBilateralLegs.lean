/-
# EmitBilateralLegs — emit the two bilateral-aggregation LEG descriptors (the CROSS-SIDE
EXISTENCE and BUNDLE-TREE FOLD AIRs, now under law #1) as byte-exact JSON.

Prints three TSV lines from the verified emissions
(`Dregg2/Circuit/Emit/EffectVmEmitBilateralAgg.lean`, `…CrossSide.lean`, `…BundleFold.lean`),
the byte source of `circuit/descriptors/dregg-bilateral-aggregation-v2.json`,
`circuit/descriptors/dregg-cross-side-existence-v2.json` and
`circuit/descriptors/dregg-bundle-tree-fold-v2.json`. SCRATCH executable: run with
`lake env lean --run EmitBilateralLegs.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
import Dregg2.Circuit.Emit.EffectVmEmitCrossSide
import Dregg2.Circuit.Emit.EffectVmEmitBundleFold

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg (bilateralAggDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitCrossSide (crossSideDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitBundleFold (bundleFoldDescriptor)

def main : IO Unit := do
  IO.println s!"bilateralAggDescriptor\t{bilateralAggDescriptor.name}\t{emitVmJson2 bilateralAggDescriptor}"
  IO.println s!"crossSideDescriptor\t{crossSideDescriptor.name}\t{emitVmJson2 crossSideDescriptor}"
  IO.println s!"bundleFoldDescriptor\t{bundleFoldDescriptor.name}\t{emitVmJson2 bundleFoldDescriptor}"
