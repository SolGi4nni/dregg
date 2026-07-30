/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationV3Refused — the FLAG-DAY welded cohort.

The VK-EPOCH flag-day welds the DEPLOYED three-block capacity-floor refuse (escrow 17 / discharge 18 /
vault 19) onto every bare cohort member so the DEPLOYED VK bytes REFUSE a declared-capacity dodge, not
just the Lean keystone. This module is DOWNSTREAM of both `EffectVmEmitRotationV3` (the bare cohort +
`withDfaRcPins`) and `Dregg2.Deos.BareCohortFloorRefuseDeployed` (`gentianDeployedBareRefuse` + its
proven soundness), which resolves the import cycle (`BareCohortFloorRefuseDeployed` transitively imports
`EffectVmEmitRotationV3`, so the weld cannot live inside `v3Registry`'s def).

`v3RegistryRefused` maps `withDfaRcPins ∘ gentianDeployedBareRefuse` over `v3RegistryBare`: refuse FIRST
(widens `traceWidth` 1581→1626, appends the 39 refuse gates), then the uniform dsl rc-EMIT `withDfaRcPins`
(width-invariant, +4 tail PIs). So each welded member has `traceWidth = 1626`, `piCount = bare + 4`, and
constraints `bare ++ deployedRefuseGates ++ rcPins`. The apex re-keys `v3RegistryCapOpen` over THIS list;
the per-effect soundness rungs peel the weld (`satisfied2_of_withDfaRcPins` then
`satisfied2_of_gentianDeployedBareRefuse`) back to the bare face they are stated at. The anti-launder
proof is `BareCohortFloorRefuseDeployed.declared_capacity_unsat_deployed`: a declared-capacity turn is
UNSAT under `gentianDeployedBareRefuse d` for ANY bare `d`, so it is UNSAT under every welded cohort
member (the peel preserves the refuse block's membership).
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Deos.BareCohortFloorRefuseDeployed

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationV3Refused

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (v3RegistryBare withDfaRcPins withSelectorGate setFieldV3 withSetFieldCompletionPins)
open Dregg2.Deos.BareCohortFloorRefuseDeployed
  (gentianDeployedBareRefuse satisfied2_of_gentianDeployedBareRefuse)

set_option autoImplicit false

/-- **`v3RegistryRefused`** — the DEPLOYED flag-day cohort: every `v3RegistryBare` member welded with the
three-block capacity-floor refuse (`gentianDeployedBareRefuse`) THEN the uniform dsl rc-EMIT
(`withDfaRcPins`). Refuse is INNER (it widens `traceWidth`); the rc pins ride OUTERMOST (width-invariant,
the 4 route-commitment tail PIs). The emit runner + `v3RegistryCapOpen` re-key over this so the DEPLOYED
descriptors carry the refuse; the apex rungs peel back to the bare face. -/
def v3RegistryRefused : List (String × EffectVmDescriptor2) :=
  v3RegistryBare.map (fun (k, d) => (k, withDfaRcPins (gentianDeployedBareRefuse d)))

/-- **THE COMPOSED PEEL — `Satisfied2 (welded member) ⟹ Satisfied2 (bare face)`.** A satisfying witness
of a flag-day member (`withDfaRcPins (gentianDeployedBareRefuse d)`) is a fortiori a satisfying witness of
the bare face `d`: peel the rc pins (`satisfied2_of_withDfaRcPins`, at `gentianDeployedBareRefuse d`) then
the refuse gates (`satisfied2_of_gentianDeployedBareRefuse`). Every per-effect apex rung stated at
`Satisfied2 d` lifts to the DEPLOYED welded member through this one call. -/
theorem satisfied2_of_v3RefusedMember (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withDfaRcPins (gentianDeployedBareRefuse d)) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t :=
  satisfied2_of_gentianDeployedBareRefuse hash d
    (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.satisfied2_of_withDfaRcPins hash
      (gentianDeployedBareRefuse d) h)

section Witnesses

-- The flag-day cohort has the SAME 36-member shape as the bare cohort.
#guard v3RegistryRefused.length == 36
-- Every welded member widens over its OWN base by the refuse span (fcDep base 2 + 1 − base = 45) and
-- gains exactly the 4 rc tail PIs. Standard 1581 members → 1626; distinct-geometry 1553 members
-- (setFieldDyn / custom) → 1598 (per-member geometry, not the fixed 1626 that stranded a dead gap).
#guard (v3RegistryRefused.zip v3RegistryBare).all fun ((_, w), (_, b)) =>
  w.traceWidth == b.traceWidth + 45 && w.piCount == b.piCount + 4
-- The keys are name-stable (the deployed descriptor set is member-for-member the bare cohort).
#guard v3RegistryRefused.map (·.1) == v3RegistryBare.map (·.1)
-- Every welded member carries the 39 refuse gates over the bare constraints (+ the 4 rc pins).
#guard (v3RegistryRefused.zip v3RegistryBare).all fun ((_, w), (_, b)) =>
  w.constraints.length == b.constraints.length + 39 + 4

end Witnesses

/-! ## §VALUE8 — THE setField VALUE8 EPOCH IS THE DEPLOYED SHAPE (no parallel staged set).

`v3RegistrySetFieldValue8` — the parallel 8-member `setFieldValue8VmDescriptor2-{slot}R24` staging set —
is DELETED. It existed only because the deployed setField members rode the freeze-ALL wrap
(`v3OfFrozen (setFieldTickFace slot)`), which REJECTS an honest large-value write and leaves the written
slot's high 224 bits unbound in the light-client view. `v3RegistryBare` now carries the VALUE8 shape
DIRECTLY — `withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD (setFieldV3 slot))` — so the
DEPLOYED members (and every registry derived from them: `v3RegistryRefused`, `v3Registry`,
`v3RegistryCapOpen`, the wide cohort, the umem weld) are freeze-EXCEPT + value8-pinned. Keeping the staged
twin beside it would be two shapes that agree today and disagree later.

The deployed setField member is therefore `withDfaRcPins (gentianDeployedBareRefuse
(withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD (setFieldV3 slot))))`: `traceWidth = 1692`
(unchanged — the pins add no column) and `piCount = 57` (46 rotated prefix + 7 value8 + 4 rc). The
per-effect setField soundness rungs peel it as `satisfied2_of_v3RefusedMember` plus
`satisfied2_of_withSetFieldCompletionPins` (an appended `.piBinding` cohort). -/

section Value8Witnesses

/-- The eight DEPLOYED setField members of the flag-day cohort. -/
def deployedSetFieldMembers : List (String × EffectVmDescriptor2) :=
  v3RegistryRefused.filter (·.1.startsWith "setFieldVmDescriptor2-")

#guard deployedSetFieldMembers.length == 8
-- WIDTH IS UNMOVED by the value8 weld (the pins add no column): the live fixed-width setField trace
-- verifies against the deployed member unchanged.
#guard deployedSetFieldMembers.all fun (_, d) => d.traceWidth == 1692
-- PI LAYOUT: 46 rotated prefix + 7 value8 completion pins (46..52) + 4 rc pins (53..56) = 57.
#guard deployedSetFieldMembers.all fun (k, d) =>
  d.piCount == 57 && !d.name.isEmpty && !d.constraints.isEmpty
    && k.startsWith "setFieldVmDescriptor2-"

end Value8Witnesses

#assert_axioms satisfied2_of_v3RefusedMember

end Dregg2.Circuit.Emit.EffectVmEmitRotationV3Refused
