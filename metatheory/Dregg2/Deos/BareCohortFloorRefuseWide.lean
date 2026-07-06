/-
# Dregg2.Deos.BareCohortFloorRefuseWide — the WIDE-cohort bare-descriptor refuse (the GENTIAN
DEPLOYED-DEFAULT flip: the light client verifies capacity turns against the WIDE / WELDED registries,
so the capacity-floor refuse must ride the WIDE bare cohort, not only the V3 1-felt cohort).

`BareCohortFloorRefuseDeployed` welds the three-block capacity-floor refuse onto the V3 1-felt bare
cohort at aux columns `GRAD_ROT_WIDTH + b·REFUSE_STRIDE + …` (1593/1609/1625) — FREE headroom past the
1581-wide graduated rotation. But the DEPLOYED light client (`verify_effect_vm_rotated_with_cutover`,
`verify_one_cohort_run`) resolves the WIDE registry (`WIDE_REGISTRY_STAGED_TSV`, width 2493) and the
WELDED twin (`WIDE_UMEM_WELD_REGISTRY_TSV`), NOT the V3 1-felt cohort. On a wide member the V3 aux band
(1581+) is OCCUPIED by the two 13×8 BEFORE/AFTER wide carriers (`wideAppend` bases them at the host
width and runs to `w + 912`), so the V3 refuse cannot ride there.

This module lifts the refuse to a member whose aux blocks ride PAST the member's OWN `traceWidth` — free
headroom above the wide carriers — reusing the fully column-parametric keystone
`BareCohortFloorRefuseDeployed.declared_tag_unsat_at` (soundness) and the append-only peel shape
(`satisfied2_of_gentianDeployedBareRefuse`). The decode still reads the SAME deployed caveat type-tag
columns `ebDep k = 643/650/657/664` — which `wideAppend` preserves (it only appends past the host width
and retires the two 1-felt commit pins; the caveat region at `CAVEAT_BASE = 642` is untouched), so the
`hbind` hypothesis is discharged by the LIVE PI-45 caveat pin on the wide member exactly as on V3.

## The anti-launder keystone

`declared_capacity_unsat_wide`: a satisfying witness of `gentianWideBareRefuse d` (any wide bare member
`d`) on a cell whose COMMITTED manifest declares capacity tag `T` is FALSE — under only
`Poseidon2SpongeCR`, for a pure light client. This closes the bare-descriptor dodge on the DEPLOYED
default registries (the WIDE bare cohort + the WELDED twin). Rust deployed-column twin: the wide arm of
`circuit/src/effect_vm/bare_floor_refuse_weld.rs` (aux base = the wide member width).

## Axiom hygiene

`#assert_all_clean` at the close. No axiom, no `sorry`, no core edit; the soundness reduces through the
STABLE column-parametric `declared_tag_unsat_at`, the peel through the append-only `satisfied2` shape.
-/
import Dregg2.Deos.BareCohortFloorRefuseDeployed

namespace Dregg2.Deos.BareCohortFloorRefuseWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat (RotCaveatManifest caveatCommit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Deos.BareCohortFloorRefuse (floorZeroRefuseGate)
open Dregg2.Deos.CarrierBoundFloorGadget (manifestTags)
open Dregg2.Deos.ConstraintBinding (tagSettleEscrow tagDischargeObligation tagVaultDeposit)
open Dregg2.Deos.BareCohortFloorRefuseDeployed
  (REFUSE_STRIDE ccDep ebDep refuseGatesAt decodeGatesAt declared_tag_unsat_at manifestOf)

set_option autoImplicit false

/-! ## §1 — the WIDE aux column layout (aux base = the member's OWN width, past the wide carriers). -/

/-- The per-block disjoint decode-aux columns for a WIDE member: based at `auxBase` (the member's own
`traceWidth`, past the two wide carriers), block-strided by `REFUSE_STRIDE`. Rust twin: the wide arm of
`bare_floor_refuse_weld` with `GRAD_ROT_WIDTH` replaced by the wide member width. -/
def wideBc (auxBase b k : Nat) : Nat := auxBase + b * REFUSE_STRIDE + k
def wideIc (auxBase b k : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 4 + k
def wideOc (auxBase b j : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 8 + j
def wideFc (auxBase b : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 12

/-- The block-`b` refuse block for its capacity tag at a WIDE aux base (decode + `floorZeroRefuseGate`).
Reuses the deployed caveat tag columns `ebDep` (the wide member preserves them) and the deployed
per-slot refuse-block constructor `refuseGatesAt` (column-parametric). -/
def wideBlockGates (auxBase : Nat) (tag : ℤ) (b : Nat) : List VmConstraint2 :=
  refuseGatesAt tag ebDep (wideBc auxBase b) (wideIc auxBase b) (wideOc auxBase b) (wideFc auxBase b)

/-- The three-block WIDE refuse weld at aux base `auxBase`: escrow (17) block 0, discharge (18) block 1,
vault (19) block 2, each at its disjoint aux columns past the wide carriers. -/
def wideRefuseGates (auxBase : Nat) : List VmConstraint2 :=
  wideBlockGates auxBase (tagSettleEscrow : ℤ) 0
    ++ wideBlockGates auxBase (tagDischargeObligation : ℤ) 1
    ++ wideBlockGates auxBase (tagVaultDeposit : ℤ) 2

/-- **`gentianWideBareRefuse d`** — a WIDE bare cohort member `d` welded with the three-block refuse at
aux columns past its OWN width AND widened to cover them. The flag-day maps this over the WIDE bare
cohort (`EmitWideRegistryProbe.lean`) and the WELDED twin (`EmitWideUMemWeldRegistryProbe.lean`). The aux
base is `d.traceWidth`, so the blocks ride the free headroom ABOVE the wide carriers (which end at
`d.traceWidth`), never colliding with them — the honest flag-day geometry cost. -/
def gentianWideBareRefuse (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with
    name        := d.name ++ "-gentian-deployed-bare-refuse"
    traceWidth  := d.traceWidth + 3 * REFUSE_STRIDE
    constraints := d.constraints ++ wideRefuseGates d.traceWidth }

/-! ## §2 — the three blocks are members of the welded member's constraints. -/

/-- The block-`b`, tag-`T` decode gates are members of block `b`'s WIDE refuse block. -/
theorem wide_decode_mem_block (auxBase : Nat) (tag : ℤ) (b : Nat) (g : VmConstraint2)
    (hg : g ∈ decodeGatesAt tag ebDep (wideBc auxBase b) (wideIc auxBase b)
      (wideOc auxBase b) (wideFc auxBase b)) :
    g ∈ wideBlockGates auxBase tag b := by
  unfold wideBlockGates refuseGatesAt; exact List.mem_append_left _ hg

/-- The block-`b` refuse gate is a member of block `b`'s WIDE refuse block. -/
theorem wide_refuse_mem_block (auxBase : Nat) (tag : ℤ) (b : Nat) :
    floorZeroRefuseGate (wideFc auxBase b) ∈ wideBlockGates auxBase tag b := by
  unfold wideBlockGates refuseGatesAt
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- A member of ANY of the three WIDE blocks is a member of the welded member's constraints. -/
theorem wide_block_mem (d : EffectVmDescriptor2) (g : VmConstraint2)
    (hg : g ∈ wideBlockGates d.traceWidth (tagSettleEscrow : ℤ) 0
      ∨ g ∈ wideBlockGates d.traceWidth (tagDischargeObligation : ℤ) 1
      ∨ g ∈ wideBlockGates d.traceWidth (tagVaultDeposit : ℤ) 2) :
    g ∈ (gentianWideBareRefuse d).constraints := by
  unfold gentianWideBareRefuse wideRefuseGates
  refine List.mem_append_right d.constraints ?_
  simp only [List.mem_append]
  tauto

/-! ## §3 — THE WIDE ANTI-LAUNDER KEYSTONE (parametric `declared_tag_unsat_at` instantiated). -/

/-- **THE BARE-DESCRIPTOR DODGE CLOSED ON THE DEPLOYED WIDE DEFAULT.** For a cell whose committed
manifest declares capacity tag `T` at WIDE block `b` (escrow 0 / discharge 1 / vault 2), a satisfying
witness of the three-block WIDE bare member `gentianWideBareRefuse d` is FALSE. Same proof shape as
`BareCohortFloorRefuseDeployed.declared_capacity_unsat_deployed`, at the wide aux columns. -/
theorem declared_capacity_unsat_wide (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (tag : ℤ) (b : Nat) (d : EffectVmDescriptor2)
    (hblock : wideBlockGates d.traceWidth tag b
        = wideBlockGates d.traceWidth (tagSettleEscrow : ℤ) 0
      ∨ wideBlockGates d.traceWidth tag b = wideBlockGates d.traceWidth (tagDischargeObligation : ℤ) 1
      ∨ wideBlockGates d.traceWidth tag b = wideBlockGates d.traceWidth (tagVaultDeposit : ℤ) 2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianWideBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : tag ∈ manifestTags committedManifest) :
    False := by
  refine declared_tag_unsat_at hash hCR tag ccDep ebDep (wideBc d.traceWidth b) (wideIc d.traceWidth b)
    (wideOc d.traceWidth b) (wideFc d.traceWidth b)
    (gentianWideBareRefuse d) (fun g hg => wide_block_mem d g ?_)
    (wide_block_mem d _ ?_) hsat hi hnl committedManifest hbind hreq
  · rcases hblock with h | h | h
    · exact Or.inl (h ▸ wide_decode_mem_block d.traceWidth tag b g hg)
    · exact Or.inr (Or.inl (h ▸ wide_decode_mem_block d.traceWidth tag b g hg))
    · exact Or.inr (Or.inr (h ▸ wide_decode_mem_block d.traceWidth tag b g hg))
  · rcases hblock with h | h | h
    · exact Or.inl (h ▸ wide_refuse_mem_block d.traceWidth tag b)
    · exact Or.inr (Or.inl (h ▸ wide_refuse_mem_block d.traceWidth tag b))
    · exact Or.inr (Or.inr (h ▸ wide_refuse_mem_block d.traceWidth tag b))

/-- Escrow (block 0) is UNSAT under the WIDE bare member when the committed manifest declares it. -/
theorem declared_escrow_unsat_wide (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianWideBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagSettleEscrow : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_wide hash hCR _ 0 d (Or.inl rfl) hsat hi hnl committedManifest hbind hreq

/-- Discharge (block 1) is UNSAT under the WIDE bare member when the committed manifest declares it. -/
theorem declared_discharge_unsat_wide (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianWideBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagDischargeObligation : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_wide hash hCR _ 1 d (Or.inr (Or.inl rfl)) hsat hi hnl committedManifest
    hbind hreq

/-- Vault (block 2) is UNSAT under the WIDE bare member when the committed manifest declares it. -/
theorem declared_vault_unsat_wide (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianWideBareRefuse d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf ccDep ebDep (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagVaultDeposit : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_wide hash hCR _ 2 d (Or.inr (Or.inr rfl)) hsat hi hnl committedManifest
    hbind hreq

/-! ## §4 — THE PEEL: `Satisfied2 (gentianWideBareRefuse d) ⟹ Satisfied2 d`.

The weld only APPENDS pure `.base (.gate …)` constraints (`wideRefuseGates`, 39 pure gates — no mem-op /
map-op / range / hash-site) and WIDENS `traceWidth` (transparent to `Satisfied2`), so a satisfying
witness of the welded member is a fortiori a satisfying witness of the wide face `d`. Mirror of
`BareCohortFloorRefuseDeployed.satisfied2_of_gentianDeployedBareRefuse`; composes with the wide keystones
(`wideAppend_satisfied2_host`, `wideAppend_binds_published`) so the value/faithfulness rungs lift to the
welded wide member. -/

/-- The refuse gates are all `.base (.gate …)`, so they contribute NO mem-op. -/
theorem memOpsOf_gentianWideBareRefuse (d : EffectVmDescriptor2) :
    memOpsOf (gentianWideBareRefuse d) = memOpsOf d := by
  simp only [memOpsOf, gentianWideBareRefuse, List.filterMap_append,
    wideRefuseGates, wideBlockGates, refuseGatesAt, decodeGatesAt,
    Dregg2.Deos.BareCohortFloorRefuse.floorZeroRefuseGate,
    Dregg2.Deos.BareCohortFloorRefuse.isZeroDefGateT,
    Dregg2.Deos.BareCohortFloorRefuse.isZeroForceGateT,
    Dregg2.Deos.CarrierBoundFloorGadget.orSeedGate,
    Dregg2.Deos.CarrierBoundFloorGadget.orFoldGate,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    List.cons_append]

/-- The refuse gates contribute NO map-op. -/
theorem mapOpsOf_gentianWideBareRefuse (d : EffectVmDescriptor2) :
    mapOpsOf (gentianWideBareRefuse d) = mapOpsOf d := by
  simp only [mapOpsOf, gentianWideBareRefuse, List.filterMap_append,
    wideRefuseGates, wideBlockGates, refuseGatesAt, decodeGatesAt,
    Dregg2.Deos.BareCohortFloorRefuse.floorZeroRefuseGate,
    Dregg2.Deos.BareCohortFloorRefuse.isZeroDefGateT,
    Dregg2.Deos.BareCohortFloorRefuse.isZeroForceGateT,
    Dregg2.Deos.CarrierBoundFloorGadget.orSeedGate,
    Dregg2.Deos.CarrierBoundFloorGadget.orFoldGate,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    List.cons_append]

/-- **THE WIDE REFUSE PEEL — `Satisfied2 (gentianWideBareRefuse d) ⟹ Satisfied2 d`.** The weld only
APPENDS pure `.gate` constraints (and widens `traceWidth`): the inner constraints stay members, and the
mem / map logs are unchanged, so every existing wide soundness lemma lifts by peeling the weld first. -/
theorem satisfied2_of_gentianWideBareRefuse (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (gentianWideBareRefuse d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (gentianWideBareRefuse d) t = memLog d t := by
    simp [memLog, memOpsOf_gentianWideBareRefuse]
  have hmap : mapLog (gentianWideBareRefuse d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_gentianWideBareRefuse]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        show c ∈ (gentianWideBareRefuse d).constraints
        unfold gentianWideBareRefuse
        exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-! ## §5 — NON-VACUITY TEETH (`#guard`) at the deployed WIDE geometry. -/

section Witnesses

-- The wide refuse reads the SAME deployed caveat tag columns as V3 (643/650/657/664).
#guard ebDep 0 == 643
#guard ebDep 3 == 664
-- The three-block wide weld adds 3 × 13 = 39 gates (each block: 8 is-zero + 3 fold + 1 refuse = 13).
#guard (wideRefuseGates 2493).length == 39
-- The aux blocks ride PAST the wide member width (aux base = the member's own width; no carrier collision).
private def toyWide : EffectVmDescriptor2 :=
  { name := "toy-wide", traceWidth := 2493, piCount := 74, tables := [], constraints := [],
    hashSites := [], ranges := [] }
#guard (gentianWideBareRefuse toyWide).traceWidth == 2493 + 48
#guard (gentianWideBareRefuse toyWide).constraints.length == 39
#guard (gentianWideBareRefuse toyWide).piCount == 74
#guard (gentianWideBareRefuse toyWide).name == "toy-wide-gentian-deployed-bare-refuse"
-- The wide floor columns are all ≥ the member width (free headroom, disjoint from the wide carriers).
#guard wideFc 2493 0 == 2493 + 12
#guard wideFc 2493 1 == 2493 + 28
#guard wideFc 2493 2 == 2493 + 44
-- The 36 aux columns across the three blocks are disjoint (no bit/inv/or/floor alias).
#guard ([ wideBc 2493 0 0, wideBc 2493 0 1, wideBc 2493 0 2, wideBc 2493 0 3,
          wideIc 2493 0 0, wideIc 2493 0 1, wideIc 2493 0 2, wideIc 2493 0 3,
          wideOc 2493 0 0, wideOc 2493 0 1, wideOc 2493 0 2, wideFc 2493 0,
          wideBc 2493 1 0, wideBc 2493 1 1, wideBc 2493 1 2, wideBc 2493 1 3,
          wideIc 2493 1 0, wideIc 2493 1 1, wideIc 2493 1 2, wideIc 2493 1 3,
          wideOc 2493 1 0, wideOc 2493 1 1, wideOc 2493 1 2, wideFc 2493 1,
          wideBc 2493 2 0, wideBc 2493 2 1, wideBc 2493 2 2, wideBc 2493 2 3,
          wideIc 2493 2 0, wideIc 2493 2 1, wideIc 2493 2 2, wideIc 2493 2 3,
          wideOc 2493 2 0, wideOc 2493 2 1, wideOc 2493 2 2, wideFc 2493 2 ]).dedup.length == 36

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  wide_decode_mem_block,
  wide_refuse_mem_block,
  wide_block_mem,
  declared_capacity_unsat_wide,
  declared_escrow_unsat_wide,
  declared_discharge_unsat_wide,
  declared_vault_unsat_wide,
  memOpsOf_gentianWideBareRefuse,
  mapOpsOf_gentianWideBareRefuse,
  satisfied2_of_gentianWideBareRefuse
]

end Dregg2.Deos.BareCohortFloorRefuseWide
