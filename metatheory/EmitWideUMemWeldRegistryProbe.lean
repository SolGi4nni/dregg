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
-- THE LAST-ROW ANCHOR FORGE CLOSURE (flag day), the welded twin: the SAME `hardenLastRow` the bare
-- wide probe applies, on the SAME final object shape. The umem weld appends its `umemOp` at the TAIL
-- and `hardenLastRow` is an order-preserving map that is the identity on `.umemOp`, so hardening
-- COMMUTES with the weld — the Rust byte-parity tooth
-- (`wide_umem_weld_registry_parity_and_no_narrowing`, which recomputes
-- `weld_umem_into_wide_descriptor(bare_wide_member, domain)` in Rust) still matches member for member.
import Dregg2.Circuit.Emit.LastRowFrameHardening
-- THE S2 DELETION (Epoch 1): the welded twins are compacted through the SAME verified
-- `compactS2` at the SAME per-key `bb` as the bare wide registry (the umem/refuse welds append
-- strictly PAST the S2 columns, so the geometry triple is identical), gated per member by
-- `compactOk` — the emit fails closed on any surprise.
import Dregg2.Circuit.Emit.WideCompactTable
-- THE E1 DELETION (Epoch-1 SECOND flag-day): each welded twin is E1-compacted at its DERIVED
-- kill-set, EXACTLY as the bare wide registry. The E1 kill-set is the dead v1-face bands in the
-- HOST region (below the refuse/umem welds, which append strictly PAST the S2 columns as live),
-- so `deadColsE1 welded 90 = deadColsE1 bare 90` — the SAME per-member kill-set the shared Rust
-- producer table carries by registry key. The runtime umem producer welds umem onto the already
-- E1-compact bare member (`generate_wide_descriptor_and_trace` E1-compacts before the weld, base =
-- `wide_desc.trace_width` auto-shifts); the `wide_umem_weld_registry_parity_and_no_narrowing` tooth
-- asserts this refuse/umem-vs-compact commutation byte-for-byte.
import Dregg2.Circuit.Emit.RotWideCompactE1

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
  (crownWideHosts weldedWriteTail weldedLiveOnlyTail weldUMemIntoWide wideKeyUMemDomain)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN)

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
  -- DELIVER #1 (welded twin): rebuild the custom wide host WITH the app-root field octet
  -- (`withAfterOctetPins … 4`, PIs 62..69 ahead of the 16 wide anchors; piCount 78 → 86) so the
  -- umem-welded custom member matches the bare wide member the fold binds. `host == e.2` for every
  -- other key, so the refuse/umem composition below is unchanged for them.
  let host :=
    if e.1 == "customVmDescriptor2R24" then
      Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withAfterFieldsRootPins
          (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withAfterOctetPins
            (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withDfaRcPins
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.customV3) 4))
        188 (188 + B_SPAN)
    else e.2
  let refused :=
    if e.1 == "transferVmDescriptor2R24" then
      Dregg2.Circuit.Emit.AvailWireMembers.gentianDeployedBareRefuseAt
        (Dregg2.Circuit.Emit.AvailWireMembers.cavBaseOf
          Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH) host
    -- AVAILABILITY RETARGET, the WIDE-BURN twin: the burn key's host is the burn AVAIL crown
    -- member (`burnV3AvailWide`), whose caveat region rides the burn-AVAIL-shifted base — its
    -- refuse is `gentianDeployedBareRefuseAt (cavBaseOf 196)`, so its welded row is exactly the
    -- proven `EffectVmEmitUMemWeldWide.weldedBurnAvailWide`.
    else if e.1 == "burnVmDescriptor2R24" then
      Dregg2.Circuit.Emit.AvailWireMembers.gentianDeployedBareRefuseAt
        (Dregg2.Circuit.Emit.AvailWireMembers.cavBaseOf
          Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH) host
    else if bareCohortKeys.contains e.1 then gentianWideBareRefuse host
    else host
  (e.1, weldUMemIntoWide refused (wideKeyUMemDomain e.1))

/-- The refuse-first welded registry: the 45 crown members refuse-then-umem, the 9 §10 write-tail +
3 live-only members umem-only (never bare cohort routes, so untouched by the refuse). -/
def weldedWideRegistryRefusedFirst : List (String × EffectVmDescriptor2) :=
  crownWideHosts.map weldRefusedFirst ++ weldedWriteTail ++ weldedLiveOnlyTail

/-- `deadColsE1 cm 90` with `liveCols` HOISTED (same fast, value-identical form as
`EmitWideRegistryProbe.deadColsE1Fast` — the proven def rebuilds `liveCols` once per column, which
the interpreter makes ~1 min/member). -/
def deadColsE1Fast (cm : EffectVmDescriptor2) (ceiling : Nat) : List Nat :=
  let live := Dregg2.Circuit.Emit.RotWideCompactE1.liveCols cm
  (List.range ceiling).filter (fun c => decide (90 ≤ c) && !live.contains c)

/-- The E1 kill-set CEILING for the WELDED member's S2-compacted `cm`: the pre-append host width, i.e.
`cm.traceWidth` MINUS the umem leg (`+7`, always) MINUS the gentian floor-refuse block
(`3·REFUSE_STRIDE`) IFF the member is a bare-cohort route. Both welds ride the TOP of `cm` past the
wide carriers (refuse at the host width, the umem leg PAST the refuse — `weldRefusedFirst`), and
NEITHER is emitted by the Rust wide producer: the umem leg is appended by the runtime umem producer and
the gentian aux is filled at PROVE time (`fill_refuse_aux`). So — exactly as the bare wide registry —
the E1 kill-set must stay in the HOST region: capping the scan here yields the SAME per-member kill-set
`deadColsE1 bare 90` the shared Rust producer table (`e1_compact_generated.rs`) carries by key, so the
runtime `weld_umem_into_wide_descriptor(compactE1(bare+refuse))` composition byte-matches this emit
(the `wide_umem_weld_registry_parity_and_no_narrowing` tooth). Non-cohort keys carry no gentian, so the
ceiling only excludes the umem leg. -/
def e1Ceiling (key : String) (cm : EffectVmDescriptor2) : Nat :=
  cm.traceWidth - 7
    - (if bareCohortKeys.contains key then 3 * Dregg2.Deos.BareCohortFloorRefuseDeployed.REFUSE_STRIDE else 0)

def main : IO Unit := do
  for (key, d) in weldedWideRegistryRefusedFirst do
    match Dregg2.Circuit.Emit.WideCompactTable.compactForEmit key d with
    | .ok (cm, _, _) =>
      -- E1 (the SECOND flag-day): delete the dead v1-face bands at the derived kill-set (floor 90),
      -- gated by the cheap `transitionCeilingOk` (`compactE1Ok_of_ceiling`). Same per-member kill-set
      -- as the bare wide registry — the refuse/umem welds append PAST the host, so the E1 scan is
      -- capped at the host width (`e1Ceiling`); the kill-set is a subset of `deadColsE1 cm 90`, and a
      -- subset of a `compactE1Ok`-valid pure-dead kill-set stays `compactE1Ok`-valid.
      if Dregg2.Circuit.Emit.RotWideCompactE1.transitionCeilingOk cm 90 then
        let e1cm := Dregg2.Circuit.Emit.RotWideCompactE1.compactE1 cm (deadColsE1Fast cm (e1Ceiling key cm))
        -- THE LAST-ROW HARDENING (see the import note): geometry-preserving, order-preserving, and
        -- the identity on the welded `.umemOp`, so it commutes with the weld.
        let hardened := Dregg2.Circuit.Emit.LastRowFrameHardening.hardenLastRow e1cm
        IO.println s!"{key}\t{hardened.name}\t{emitVmJson2 hardened}"
      else throw (IO.userError
          s!"E1-compact REFUSED for welded {key} — transitionCeilingOk failed (a `.transition` \
             reads a face column ≥ 90); the emit fails closed")
    | .error e => throw (IO.userError e)
