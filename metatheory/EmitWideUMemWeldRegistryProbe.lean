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

## The gentian refuse rides REFUSE-FIRST (welded onto the host, THEN the umem leg)

The gentian deployed-default flip welds the capacity-floor refuse onto the 36 bare cohort routes.
On the WELDED twin the refuse is applied to the wide HOST **before** the umem leg — i.e.
`weldUMemIntoWide (gentianWideBareRefuse host) dom` — so the refuse aux blocks ride PAST the wide
carriers (at `host.traceWidth`) and the umem leg rides PAST the refuse (at `host.traceWidth + 48`).
This is the EXACT composition the runtime producer takes: `prove_wide_umem_welded_staged` welds umem
onto the ALREADY-refuse-welded wide member it reads from `WIDE_REGISTRY_STAGED_TSV`
(`weld_umem_into_wide_descriptor(wide+refuse)`), and the Rust weld-parity tooth
(`wide_umem_weld_registry_parity_and_no_narrowing`) asserts each welded member equals exactly that.
Welding refuse AFTER umem (the earlier order) placed the refuse aux past the umem columns, so the
runtime producer's descriptor (refuse-first) and this verifier twin (refuse-last) diverged — an
honest umem-welded turn proved against one layout and verified against the other
(`OodEvaluationMismatch`). Refuse-first makes them coincide.

This is the byte source of the ADDITIVE Rust artifact
`circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` (pinned by
`WIDE_UMEM_WELD_REGISTRY_FP`). NOTHING on the live wire changes — the deployed bare wide registry /
FP / VK are UNTOUCHED, `umem_witness_enabled` stays false.

SCRATCH executable: `lake env lean --run EmitWideUMemWeldRegistryProbe.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
import Dregg2.Deos.BareCohortFloorRefuseWide

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
  (crownWideHosts weldedWriteTail weldedLiveOnlyTail weldUMemIntoWide wideKeyUMemDomain)

-- THE GENTIAN DEPLOYED-DEFAULT FLIP (welded twin): the capacity-floor refuse rides the WELDED bare
-- cohort too, welded onto the wide HOST BEFORE the umem leg (refuse aux at `host.traceWidth`, umem
-- PAST it) — exactly the runtime producer's `weld_umem_into_wide_descriptor(wide+refuse)` composition.
open Dregg2.Deos.BareCohortFloorRefuseWide (gentianWideBareRefuse)

/-- The 36 bare cohort keys — the settle-as-transfer/burn dodge routes the refuse is welded onto. -/
def bareCohortKeys : List String :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3RegistryBare.map (·.1)

/-- Weld the WIDE capacity-floor refuse onto a wide host IFF its key is a bare cohort route, then weld
the umem leg PAST it. A non-cohort key (cap-open / write / supplyMint / satisfaction) rides the umem
leg alone. Mirrors `EmitWideRegistryProbe.weldWide` (same refuse) composed with `weldUMemIntoWide`.
AVAILABILITY RETARGET: the transfer key's host is the AVAIL crown member
(`transferV3MembershipAvailWide`), whose caveat region rides the AVAIL-shifted base — its refuse is
`gentianDeployedBareRefuseAt (cavBaseOf AVAIL_WIDTH)` (the fixed-base `gentianWideBareRefuse` would
decode the WRONG columns), so its welded row is exactly the proven
`EffectVmEmitUMemWeldWide.weldedTransferAvailWide`. -/
def weldRefusedFirst (e : String × EffectVmDescriptor2) : String × EffectVmDescriptor2 :=
  let refused :=
    if e.1 == "transferVmDescriptor2R24" then
      Dregg2.Circuit.Emit.AvailWireMembers.gentianDeployedBareRefuseAt
        (Dregg2.Circuit.Emit.AvailWireMembers.cavBaseOf
          Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH) e.2
    -- AVAILABILITY RETARGET, the WIDE-BURN twin: the burn key's host is the burn AVAIL crown
    -- member (`burnV3AvailWide`), whose caveat region rides the burn-AVAIL-shifted base — its
    -- refuse is `gentianDeployedBareRefuseAt (cavBaseOf 196)`, so its welded row is exactly the
    -- proven `EffectVmEmitUMemWeldWide.weldedBurnAvailWide`.
    else if e.1 == "burnVmDescriptor2R24" then
      Dregg2.Circuit.Emit.AvailWireMembers.gentianDeployedBareRefuseAt
        (Dregg2.Circuit.Emit.AvailWireMembers.cavBaseOf
          Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH) e.2
    else if bareCohortKeys.contains e.1 then gentianWideBareRefuse e.2
    else e.2
  (e.1, weldUMemIntoWide refused (wideKeyUMemDomain e.1))

/-- The refuse-first welded registry: the 45 crown members refuse-then-umem, the 9 §10 write-tail +
3 live-only members umem-only (never bare cohort routes, so untouched by the refuse). -/
def weldedWideRegistryRefusedFirst : List (String × EffectVmDescriptor2) :=
  crownWideHosts.map weldRefusedFirst ++ weldedWriteTail ++ weldedLiveOnlyTail

def main : IO Unit := do
  for (key, d) in weldedWideRegistryRefusedFirst do
    IO.println s!"{key}\t{d.name}\t{emitVmJson2 d}"
