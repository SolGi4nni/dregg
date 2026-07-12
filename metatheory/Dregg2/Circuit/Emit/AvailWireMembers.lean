/-
# Dregg2.Circuit.Emit.AvailWireMembers — the HARDENED transfer/burn WIRE members (the GAP #4
availability flip's emission objects).

## What this module is

The audit's two mint-from-nothing forgeries (`docs/FINDING-modp-wrap-forgery-audit.md`) are closed
IN-PROOF by the §11.7 / §8¾ availability welds (`transferVmDescriptorAvail` /
`burnVmDescriptorAvail`, 15-bit borrow-limb decomposition + no-final-borrow, lifted
`v3OfFrozenWide` and discharged end-to-end in `RotatedKernelRefinement{Avail,MintBurnAvail}`).
This module builds the DEPLOYABLE WIRE members for the two flipped registry keys
(`transferVmDescriptor2R24` / `burnVmDescriptor2R24`): the hardened rotated graduated descriptor
wrapped through the SAME two deployed wrappers every cohort member carries —

  * the three-block capacity-floor refuse (`gentianDeployedBareRefuseAt` — the
    `BareCohortFloorRefuseDeployed.gentianDeployedBareRefuse` weld at the AVAIL-SHIFTED caveat
    geometry: the hardened v1 face is `AVAIL_WIDTH` wide, so its rotated caveat region — and hence
    the type-tag columns the refuse decode reads — rides `AVAIL_WIDTH + CAVEAT_REGION_OFF`, not
    the bare `EFFECT_VM_WIDTH + CAVEAT_REGION_OFF`);
  * the uniform DSL rc-EMIT (`withDfaRcPinsAt` — `withDfaRcPins` at the shifted rc carrier
    columns).

Both wrappers are column-parametric twins of the deployed fixed-geometry defs; their soundness is
NOT re-proven from scratch — the refuse teeth instantiate the column-PARAMETRIC keystone
`BareCohortFloorRefuseDeployed.declared_tag_unsat_at`, and the peels mirror the deployed peels
structurally, so `Satisfied2 (wire member) ⟹ Satisfied2 (v3OfFrozenWide <hardened face>)` — the
EXACT object `RotatedKernelRefinementAvail.transferV3Avail` / `…MintBurnAvail.burnV3Avail` whose
availability discharge is proven (`availability_and_exact_move_forced` /
`burn_availability_and_exact_move_forced`).

## What consumes it

`EmitRotationV3.lean` (the descriptor emit executable) overrides the two cohort keys with these
members, so `scripts/emit-descriptors.sh` mints the hardened bytes into
`circuit/descriptors/rotation-v3-staged-registry.tsv` — the ember-gated VK regen then re-keys the
federation over them. The BARE defs (`transferVmDescriptor` / `burnVmDescriptor` and their whole
registry pipeline) stay untouched for the bare-path proofs; only the WIRE routes to hardened.
The named follow-up (HORIZONLOG): re-key the in-library `v3RegistryBare` transfer/burn entries +
the apex `Rfix` over these members so the committed-registry object and the wire coincide again
member-for-member.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Deos.BareCohortFloorRefuseDeployed

namespace Dregg2.Circuit.Emit.AvailWireMembers

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (CAVEAT_REGION_OFF C_RC_OFF v3OfFrozenWide)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduableWide)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat (RotCaveatManifest caveatCommit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Deos.BareCohortFloorRefuse (floorZeroRefuseGate isZeroDefGateT isZeroForceGateT)
open Dregg2.Deos.CarrierBoundFloorGadget (orSeedGate orFoldGate manifestTags)
open Dregg2.Deos.BareCohortFloorRefuseDeployed
  (REFUSE_STRIDE refuseGatesAt decodeGatesAt declared_tag_unsat_at manifestOf)
open Dregg2.Deos.ConstraintBinding (tagSettleEscrow tagDischargeObligation tagVaultDeposit)

set_option autoImplicit false

/-! ## §1 — the geometry-parametric wrappers. -/

/-- The rotated caveat-region base of a member whose v1 face is `w` wide (`rotateV3` appends the
appendix at `d.traceWidth`, so the caveat region rides `w + 2·B_SPAN = w + CAVEAT_REGION_OFF`). -/
def cavBaseOf (w : Nat) : Nat := w + CAVEAT_REGION_OFF

/-- The caveat entry-base / type-tag columns at caveat base `cavBase` (the
`BareCohortFloorRefuseDeployed.ebDep` twin, base-parametric). -/
def ebAt (cavBase : Nat) (k : Nat) : Nat := cavBase + 1 + 7 * k

/-- The per-block disjoint decode-aux columns at aux base `auxBase` (the `bcDep`/`icDep`/`ocDep`/
`fcDep` twins — same strides, the aux base is the member's OWN graduated width). -/
def bcAt (auxBase b k : Nat) : Nat := auxBase + b * REFUSE_STRIDE + k
def icAt (auxBase b k : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 4 + k
def ocAt (auxBase b j : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 8 + j
def fcAt (auxBase b : Nat) : Nat := auxBase + b * REFUSE_STRIDE + 12

/-- The block-`b` refuse block for its capacity tag at caveat base `cavBase` / aux base `auxBase`. -/
def blockGatesAt (cavBase auxBase : Nat) (tag : ℤ) (b : Nat) : List VmConstraint2 :=
  refuseGatesAt tag (ebAt cavBase) (bcAt auxBase b) (icAt auxBase b) (ocAt auxBase b)
    (fcAt auxBase b)

/-- The three-block deployed refuse weld at caveat base `cavBase` / aux base `auxBase` (the
`deployedRefuseGates` twin, caveat-base-parametric). -/
def deployedRefuseGatesAt (cavBase auxBase : Nat) : List VmConstraint2 :=
  blockGatesAt cavBase auxBase (tagSettleEscrow : ℤ) 0
    ++ blockGatesAt cavBase auxBase (tagDischargeObligation : ℤ) 1
    ++ blockGatesAt cavBase auxBase (tagVaultDeposit : ℤ) 2

/-- **`gentianDeployedBareRefuseAt cavBase d`** — `gentianDeployedBareRefuse` with the caveat
type-tag columns at a PARAMETRIC base: the aux blocks still ride `d.traceWidth` (the member's own
free headroom), the decode reads the caveat region at `cavBase` (for a hardened `…-v1-avail` face,
`cavBaseOf AVAIL_WIDTH` — the avail-shifted deployed caveat columns). At
`cavBase = cavBaseOf EFFECT_VM_WIDTH = 666` this is definitionally the deployed
`gentianDeployedBareRefuse`. -/
def gentianDeployedBareRefuseAt (cavBase : Nat) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with
    name        := d.name ++ "-gentian-deployed-bare-refuse"
    traceWidth  := fcAt d.traceWidth 2 + 1
    constraints := d.constraints ++ deployedRefuseGatesAt cavBase d.traceWidth }

/-- **`withDfaRcPinsAt w g`** — `withDfaRcPins` at a PARAMETRIC v1-face width `w`: the 4
`.piBinding .last` pins publish the caveat-region DFA route-commitment carrier at
`w + CAVEAT_REGION_OFF + C_RC_OFF + k` (for a hardened face, the avail-shifted rc columns). At
`w = EFFECT_VM_WIDTH` this is definitionally the deployed `withDfaRcPins`. -/
def withDfaRcPinsAt (w : Nat) (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 4
    constraints := g.constraints ++ (List.range 4).map (fun k =>
      VmConstraint2.base (.piBinding .last (w + CAVEAT_REGION_OFF + (C_RC_OFF + k))
        (g.piCount + k))) }

/-- The composed WIRE wrapper at v1-face width `w`: refuse INNER (widens `traceWidth`), rc pins
OUTERMOST (width-invariant, +4 tail PIs) — the exact `v3RegistryRefused` member shape. -/
def availWireOf (w : Nat) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  withDfaRcPinsAt w (gentianDeployedBareRefuseAt (cavBaseOf w) d)

/-! ## §2 — the two hardened wire members. -/

/-- **`transferV3AvailWire`** — the deployable hardened transfer wire member: the §11.7
availability-weld face `v3OfFrozenWide` (= `RotatedKernelRefinementAvail.transferV3Avail`) +
the capacity-floor refuse + the rc pins, all at the avail-shifted geometry. The
`transferVmDescriptor2R24` registry key's post-flip bytes. -/
def transferV3AvailWire : EffectVmDescriptor2 :=
  availWireOf Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH
    (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptorAvail)

/-- **`burnV3AvailWire`** — the deployable hardened burn wire member (the §8¾ face; =
`RotatedKernelRefinementMintBurnAvail.burnV3Avail` + the same wrappers). The
`burnVmDescriptor2R24` registry key's post-flip bytes. -/
def burnV3AvailWire : EffectVmDescriptor2 :=
  availWireOf Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH
    (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail)

/-- **`transferFeeV3AvailWire`** — the deployable hardened FEE'D-transfer wire member: the §11.8
fee availability face (`transferFeeVmDescriptorAvail` — MID-linked borrow/carry chains closing the
wrap forgery through BOTH debit legs, amount AND fee) lifted `v3OfFrozenFeeWide` (freeze → fee pin
→ WIDE graduation, `transferFeeV3`'s exact composition at the hardened face) + the uniform DSL
rc-EMIT at the fee-avail-shifted geometry (`withDfaRcPinsAt FEE_AVAIL_WIDTH`). NO capacity-floor
refuse wrapper: the DEPLOYED fee member (`withDfaRcPins transferFeeV3`, registry tail position 44,
PAST the 36 refused cohort members) carries none, and the hardened member mirrors the deployed
shape wrapper-for-wrapper. The `transferFeeVmDescriptor2R24` registry key's post-flip bytes. -/
def transferFeeV3AvailWire : EffectVmDescriptor2 :=
  withDfaRcPinsAt Dregg2.Circuit.Emit.EffectVmEmitTransfer.FEE_AVAIL_WIDTH
    (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3OfFrozenFeeWide
      Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferFeeVmDescriptorAvail)


/-! ## §3 — THE PEELS: `Satisfied2 (wire member) ⟹ Satisfied2 (hardened rotated face)`.

Structural mirrors of `satisfied2_of_withDfaRcPins` / `satisfied2_of_gentianDeployedBareRefuse`
(both wrappers only APPEND `.piBinding` / `.base (.gate …)` constraints — no mem-op / map-op /
range / hash-site), so every hardened-path theorem (`RotatedKernelRefinementAvail.*`,
`…MintBurnAvail.*`, stated at `Satisfied2 (v3OfFrozenWide <face>)`) consumes a satisfying wire
witness through ONE composed call. -/

theorem withDfaRcPinsAt_constraints (w : Nat) (g : EffectVmDescriptor2) :
    (withDfaRcPinsAt w g).constraints
      = g.constraints ++ (List.range 4).map (fun k =>
          VmConstraint2.base (.piBinding .last (w + CAVEAT_REGION_OFF + (C_RC_OFF + k))
            (g.piCount + k))) := rfl

/-- The rc pins are `.piBinding`s, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withDfaRcPinsAt (w : Nat) (g : EffectVmDescriptor2) :
    memOpsOf (withDfaRcPinsAt w g) = memOpsOf g := by
  simp [memOpsOf, withDfaRcPinsAt, List.filterMap_append, List.filterMap_map]

/-- The rc pins contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withDfaRcPinsAt (w : Nat) (g : EffectVmDescriptor2) :
    mapOpsOf (withDfaRcPinsAt w g) = mapOpsOf g := by
  simp [mapOpsOf, withDfaRcPinsAt, List.filterMap_append, List.filterMap_map]

/-- **THE rc PEEL (parametric)** — `Satisfied2 (withDfaRcPinsAt w g) ⟹ Satisfied2 g`. -/
theorem satisfied2_of_withDfaRcPinsAt (hash : List ℤ → ℤ) (w : Nat) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withDfaRcPinsAt w g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withDfaRcPinsAt w g) t = memLog g t := by
    simp [memLog, memOpsOf_withDfaRcPinsAt]
  have hmap : mapLog (withDfaRcPinsAt w g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withDfaRcPinsAt]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withDfaRcPinsAt_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- The refuse gates are all `.base (.gate …)`, so they contribute NO mem-op. -/
theorem memOpsOf_gentianDeployedBareRefuseAt (cavBase : Nat) (d : EffectVmDescriptor2) :
    memOpsOf (gentianDeployedBareRefuseAt cavBase d) = memOpsOf d := by
  simp only [memOpsOf, gentianDeployedBareRefuseAt, List.filterMap_append,
    deployedRefuseGatesAt, blockGatesAt, refuseGatesAt, decodeGatesAt,
    floorZeroRefuseGate, isZeroDefGateT, isZeroForceGateT, orSeedGate, orFoldGate,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    List.cons_append]

/-- The refuse gates contribute NO map-op. -/
theorem mapOpsOf_gentianDeployedBareRefuseAt (cavBase : Nat) (d : EffectVmDescriptor2) :
    mapOpsOf (gentianDeployedBareRefuseAt cavBase d) = mapOpsOf d := by
  simp only [mapOpsOf, gentianDeployedBareRefuseAt, List.filterMap_append,
    deployedRefuseGatesAt, blockGatesAt, refuseGatesAt, decodeGatesAt,
    floorZeroRefuseGate, isZeroDefGateT, isZeroForceGateT, orSeedGate, orFoldGate,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    List.cons_append]

/-- **THE REFUSE PEEL (parametric)** — `Satisfied2 (gentianDeployedBareRefuseAt cavBase d) ⟹
Satisfied2 d`. -/
theorem satisfied2_of_gentianDeployedBareRefuseAt (hash : List ℤ → ℤ) (cavBase : Nat)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (gentianDeployedBareRefuseAt cavBase d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (gentianDeployedBareRefuseAt cavBase d) t = memLog d t := by
    simp [memLog, memOpsOf_gentianDeployedBareRefuseAt]
  have hmap : mapLog (gentianDeployedBareRefuseAt cavBase d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_gentianDeployedBareRefuseAt]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        show c ∈ (gentianDeployedBareRefuseAt cavBase d).constraints
        unfold gentianDeployedBareRefuseAt
        exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **THE COMPOSED PEEL** — a satisfying wire-member witness is a fortiori a satisfying witness of
the HARDENED rotated face (`v3OfFrozenWide <avail face>` — the exact object the
`RotatedKernelRefinement{Avail,MintBurnAvail}` availability discharges are stated over). -/
theorem satisfied2_of_availWireOf (hash : List ℤ → ℤ) (w : Nat) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (availWireOf w d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t :=
  satisfied2_of_gentianDeployedBareRefuseAt hash (cavBaseOf w) d
    (satisfied2_of_withDfaRcPinsAt hash w (gentianDeployedBareRefuseAt (cavBaseOf w) d) h)

/-- **THE FEE PEEL** — a satisfying fee-wire witness is a fortiori a satisfying witness of the
hardened fee-pinned rotated face (`v3OfFrozenFeeWide transferFeeVmDescriptorAvail` — the exact
object `rotV3FrozenFeeWide_sound_v1` consumes down to the §11.8 availability discharge). The fee
wire carries ONLY the rc-pin wrapper (the deployed fee member's shape), so the peel is one call. -/
theorem satisfied2_of_transferFeeV3AvailWire (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash transferFeeV3AvailWire minit mfin maddrs t) :
    Satisfied2 hash
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3OfFrozenFeeWide
        Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferFeeVmDescriptorAvail)
      minit mfin maddrs t :=
  satisfied2_of_withDfaRcPinsAt hash _ _ h

/-! ## §4 — THE REFUSE TEETH at the avail geometry (the flag-day soundness carried over).

The refuse decode reads the AVAIL-SHIFTED caveat type-tag columns (`ebAt (cavBaseOf w)`), which
are exactly the columns the hardened member's deployed `caveatCommit` hash-site commits to PI 45 —
so `hbind` is discharged by the LIVE caveat pin exactly as on the bare cohort, and the
column-parametric keystone `declared_tag_unsat_at` closes each dodge. -/

/-- The tag-`T` decode gates are members of block `b`'s refuse block (at the avail geometry). -/
theorem decodeAt_mem_blockAt (cav aux : Nat) (tag : ℤ) (b : Nat) (g : VmConstraint2)
    (hg : g ∈ decodeGatesAt tag (ebAt cav) (bcAt aux b) (icAt aux b) (ocAt aux b) (fcAt aux b)) :
    g ∈ blockGatesAt cav aux tag b := by
  unfold blockGatesAt refuseGatesAt; exact List.mem_append_left _ hg

/-- The block-`b` refuse gate is a member of block `b`'s refuse block (at the avail geometry). -/
theorem refuseAt_mem_blockAt (cav aux : Nat) (tag : ℤ) (b : Nat) :
    floorZeroRefuseGate (fcAt aux b) ∈ blockGatesAt cav aux tag b := by
  unfold blockGatesAt refuseGatesAt
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- A member of ANY of the three blocks is a member of the WIRE member's constraints. -/
theorem blockAt_mem_wire (w : Nat) (d : EffectVmDescriptor2) (g : VmConstraint2)
    (hg : g ∈ blockGatesAt (cavBaseOf w) d.traceWidth (tagSettleEscrow : ℤ) 0
      ∨ g ∈ blockGatesAt (cavBaseOf w) d.traceWidth (tagDischargeObligation : ℤ) 1
      ∨ g ∈ blockGatesAt (cavBaseOf w) d.traceWidth (tagVaultDeposit : ℤ) 2) :
    g ∈ (availWireOf w d).constraints := by
  have hrefused : g ∈ (gentianDeployedBareRefuseAt (cavBaseOf w) d).constraints := by
    unfold gentianDeployedBareRefuseAt deployedRefuseGatesAt
    refine List.mem_append_right d.constraints ?_
    simp only [List.mem_append]
    tauto
  show g ∈ (withDfaRcPinsAt w (gentianDeployedBareRefuseAt (cavBaseOf w) d)).constraints
  rw [withDfaRcPinsAt_constraints]
  exact List.mem_append_left _ hrefused

/-- **THE THREE DODGES, CLOSED ON THE HARDENED WIRE MEMBER.** For a cell whose committed manifest
declares capacity tag `T` at wire block `b` (escrow 0 / discharge 1 / vault 2), a satisfying
witness of `availWireOf w d` is FALSE. -/
theorem declared_capacity_unsat_availWire (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (tag : ℤ) (b : Nat) (w : Nat) (d : EffectVmDescriptor2)
    (hblock : blockGatesAt (cavBaseOf w) d.traceWidth tag b
          = blockGatesAt (cavBaseOf w) d.traceWidth (tagSettleEscrow : ℤ) 0
        ∨ blockGatesAt (cavBaseOf w) d.traceWidth tag b
          = blockGatesAt (cavBaseOf w) d.traceWidth (tagDischargeObligation : ℤ) 1
        ∨ blockGatesAt (cavBaseOf w) d.traceWidth tag b
          = blockGatesAt (cavBaseOf w) d.traceWidth (tagVaultDeposit : ℤ) 2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (availWireOf w d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf (cavBaseOf w) (ebAt (cavBaseOf w)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : tag ∈ manifestTags committedManifest) :
    False := by
  refine declared_tag_unsat_at hash hCR tag (cavBaseOf w) (ebAt (cavBaseOf w))
    (bcAt d.traceWidth b) (icAt d.traceWidth b) (ocAt d.traceWidth b) (fcAt d.traceWidth b)
    (availWireOf w d)
    (fun g hg => blockAt_mem_wire w d g ?_)
    (blockAt_mem_wire w d _ ?_)
    hsat hi hnl hcanon htag committedManifest hbind hreq
  · -- decode-gate membership: route into the matching block via `hblock`.
    rcases hblock with h | h | h
    · exact Or.inl (h ▸ decodeAt_mem_blockAt (cavBaseOf w) d.traceWidth tag b g hg)
    · exact Or.inr (Or.inl (h ▸ decodeAt_mem_blockAt (cavBaseOf w) d.traceWidth tag b g hg))
    · exact Or.inr (Or.inr (h ▸ decodeAt_mem_blockAt (cavBaseOf w) d.traceWidth tag b g hg))
  · -- refuse-gate membership.
    rcases hblock with h | h | h
    · exact Or.inl (h ▸ refuseAt_mem_blockAt (cavBaseOf w) d.traceWidth tag b)
    · exact Or.inr (Or.inl (h ▸ refuseAt_mem_blockAt (cavBaseOf w) d.traceWidth tag b))
    · exact Or.inr (Or.inr (h ▸ refuseAt_mem_blockAt (cavBaseOf w) d.traceWidth tag b))

/-- Escrow (block 0) is UNSAT under the hardened wire member when the manifest declares it. -/
theorem declared_escrow_unsat_availWire (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (w : Nat) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (availWireOf w d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf (cavBaseOf w) (ebAt (cavBaseOf w)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagSettleEscrow : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_availWire hash hCR _ 0 w d (Or.inl rfl) hsat hi hnl hcanon (by decide)
    committedManifest hbind hreq

/-- Discharge (block 1) is UNSAT under the hardened wire member when the manifest declares it. -/
theorem declared_discharge_unsat_availWire (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (w : Nat) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (availWireOf w d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf (cavBaseOf w) (ebAt (cavBaseOf w)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagDischargeObligation : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_availWire hash hCR _ 1 w d (Or.inr (Or.inl rfl)) hsat hi hnl hcanon
    (by decide) committedManifest hbind hreq

/-- Vault (block 2) is UNSAT under the hardened wire member when the manifest declares it. -/
theorem declared_vault_unsat_availWire (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (w : Nat) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (availWireOf w d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (manifestOf (cavBaseOf w) (ebAt (cavBaseOf w)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagVaultDeposit : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_availWire hash hCR _ 2 w d (Or.inr (Or.inr rfl)) hsat hi hnl hcanon
    (by decide) committedManifest hbind hreq

/-! ## §5 — NON-VACUITY / geometry witnesses. -/

section Witnesses

-- The hardened v1 faces widen the bare face by the avail pads (transfer 10 / burn 8 / fee'd 16).
#guard Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH == EFFECT_VM_WIDTH + 10
#guard Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH == EFFECT_VM_WIDTH + 8
#guard Dregg2.Circuit.Emit.EffectVmEmitTransfer.FEE_AVAIL_WIDTH == EFFECT_VM_WIDTH + 16
-- Both hardened faces are WIDE-graduable (their 15-bit borrow teeth lower into the 15-bit table).
#guard graduableWide Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptorAvail
#guard graduableWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
-- The wide graduation declares the 15-bit range table beside the five EPOCH tables.
#guard (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptorAvail).tables.length == 6
#guard (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).tables.length == 6
-- The wire members: piCount 50 (42 v1 + 4 rotated commit pins + 4 rc), the avail-shifted widths
-- (transfer: graduated 1657 + 45 refuse = 1702; burn: 1655 + 45 = 1700), name-marked `-v1-avail`.
#guard transferV3AvailWire.piCount == 50
#guard burnV3AvailWire.piCount == 50
#guard transferV3AvailWire.traceWidth == 1702
#guard burnV3AvailWire.traceWidth == 1700
#guard transferV3AvailWire.name
  == "dregg-effectvm-transfer-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse"
#guard burnV3AvailWire.name
  == "dregg-effectvm-burn-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse"
-- The wrappers are exactly the deployed cohort shape: +39 refuse gates + 4 rc pins.
#guard transferV3AvailWire.constraints.length
  == (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptorAvail).constraints.length + 39 + 4
#guard burnV3AvailWire.constraints.length
  == (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).constraints.length + 39 + 4
-- The FEE'D hardened wire member: the fee-pinned wide face (piCount 47) + the 4 rc pins = 51 (the
-- deployed `withDfaRcPins transferFeeV3` PI shape); traceWidth = the wide-graduated fee face
-- (NO refuse block — the deployed fee member carries none); name-marked `-fee-avail`; the ONLY
-- constraint delta past the face is the 4 rc pins.
#guard transferFeeV3AvailWire.piCount == 51
#guard transferFeeV3AvailWire.traceWidth
  == (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3OfFrozenFeeWide
      Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferFeeVmDescriptorAvail).traceWidth
#guard (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3OfFrozenFeeWide
    Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferFeeVmDescriptorAvail).tables.length == 6
#guard transferFeeV3AvailWire.name == "dregg-effectvm-transfer-v1-fee-avail-rot24-v3-staged"
#guard transferFeeV3AvailWire.constraints.length
  == (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3OfFrozenFeeWide
      Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferFeeVmDescriptorAvail).constraints.length + 4

end Witnesses

#assert_axioms satisfied2_of_withDfaRcPinsAt
#assert_axioms satisfied2_of_gentianDeployedBareRefuseAt
#assert_axioms satisfied2_of_availWireOf
#assert_axioms satisfied2_of_transferFeeV3AvailWire
#assert_axioms declared_capacity_unsat_availWire
#assert_axioms declared_escrow_unsat_availWire
#assert_axioms declared_discharge_unsat_availWire
#assert_axioms declared_vault_unsat_availWire

end Dregg2.Circuit.Emit.AvailWireMembers
