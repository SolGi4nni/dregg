/-
# EmitWideUMemWeldRegistryProbe — the Lean-emitted WIDE+UMEM WELDED registry TSV (STAGED slice).

Prints ONE TSV line per WELDED wide member, in the EXACT order + key set of
`CapOpenEmit.v3RegistryCapOpenWide` (so the welded registry is a member-for-member, name-stable
COVER of the wide registry's emit-source members):

  `<live key>\t<welded member.name>\t<emitVmJson2 (welded member)>`

Each welded member is the purely-ADDITIVE `weldUMemIntoWide host (wideKeyUMemDomain key)` of the
corresponding wide member — the single-domain cohort `umemOp` over 7 fresh columns + the
`umemory` / `umem_boundary` tables appended PAST the wide carriers, `piCount` UNCHANGED (the 16
wide-commit PIs / the 8-felt anchors ride through, NO narrowing).

This is the byte source of the ADDITIVE Rust artifact
`circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` (pinned by
`WIDE_UMEM_WELD_REGISTRY_FP`). NOTHING on the live wire changes — the deployed bare wide registry /
FP / VK are UNTOUCHED, `umem_witness_enabled` stays false.

SCRATCH executable: `lake env lean --run EmitWideUMemWeldRegistryProbe.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
import Dregg2.Deos.BareCohortFloorRefuseWide

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide (weldedWideRegistry)

-- THE GENTIAN DEPLOYED-DEFAULT FLIP (welded twin): the capacity-floor refuse rides the WELDED bare
-- cohort too (aux blocks PAST the welded member width — past the wide carriers AND the umem columns),
-- welded onto exactly the 36 bare cohort keys, mirroring the wide registry. The executor `require_welded`
-- path binds the welded twin for a single-cohort sovereign turn, so the refuse must ride it as well.
open Dregg2.Deos.BareCohortFloorRefuseWide (gentianWideBareRefuse)

/-- The 36 bare cohort keys — the settle-as-transfer/burn dodge routes the refuse is welded onto. -/
def bareCohortKeys : List String :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3RegistryBare.map (·.1)

/-- Weld the WIDE capacity-floor refuse onto a welded member IFF its key is a bare cohort route. -/
def weldWide (key : String) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  if bareCohortKeys.contains key then gentianWideBareRefuse d else d

def main : IO Unit := do
  for (key, d) in weldedWideRegistry do
    IO.println s!"{key}\t{(weldWide key d).name}\t{emitVmJson2 (weldWide key d)}"
