/-
# Dregg2.Circuit.Emit.CapOpenEmit — the LIVE cap-membership open, emitted into a real descriptor.

`DeployedCapOpen.lean` PROVES the in-circuit cap-tree membership-open as a set of generic
`Lookup` + gate `VmConstraint2`s (`leafLookup` + 16 `nodeLookup` + `dirBoolGate`/`rootPinGate`/
`targetBindGate`/`transferFacetGate`/`facetHiGate`/`authTagGate`) over an abstract `CapOpenCols`
column layout, with the keystone `capOpen_sound`: a `Satisfied` row yields `MembersAt cap_root leaf ∧
leaf.target = src ∧ confersTransferLeaf vkOfTag .signature leaf` (the FAITHFUL two-axis tier × facet
gate). But nothing LAID THOSE CONSTRAINTS DOWN into a live `EffectVmDescriptor2`: the proof existed,
disconnected from the wire.

This file welds it. It (a) pins `CapOpenCols` to a concrete appendix of trace columns past the
rotated R=24 width (`capOpenCols`, §1), (b) assembles the proven constraints into the effect-GENERAL
constraint list `capOpenConstraintsEff n` (§5.F) — `leafLookup` + the 16 `nodeLookup`s as `.lookup`,
the genuine SUBMASK facet gate (`effBitGateFor`/`maskBitBoolGate`/`maskReconGate`/`selectedBitGate`)
+ the binding gates as `.base (.gate …)` — and (c) appends them to each effect's rotated base
(`transferCapOpenEffV3`/`attenuateCapOpenEffV3` + the 6 fan-out, §5.F), widening the trace by
`CAP_OPEN_SPAN` and welding the `capRoot`/`src` columns to the committed rotated before-block cap-root
and the turn's src.

The keystones (§5.K, `transferCapOpenEffV3_authorizes`/`attenuateCapOpenEffV3_authorizes`): a
`Satisfied2` witness of the LIVE membership descriptor — against a sound chip table — REBUILDS
`DeployedCapOpen.SatisfiedEff`, hence `capOpenEff_authorizes`, hence (via
`deployedCapOpen_implies_authorizedEffB` + `authorizedFacetB = authorizedFacetEffB … EFFECT_TRANSFER`)
the kernel's FAITHFUL `authorizedFacetB`. The `&[]` cap-path placeholder is GONE: the depth-16 fold the
descriptor carries IS the proof. The genuine submask facet (a BROAD honest cap PASSES) + the DECODED
tier are what the deployed prover routes AND what the apex authority leg refines — wire and proof are
ONE. (The Signature-pinned `capOpenAttenuateV3`/`transferCapOpenV3` are DELETED, §3.)

## Law #1

NO new constraint SEMANTICS live here: every constraint is a `DeployedCapOpen` `Lookup`/gate that the
Rust `descriptor_ir2.rs` interpreter ALREADY realizes generically (chip lookups on the P2 bus, base
gates on the transition builder). This file is pure PLUMBING — a column layout + a constraint list +
the bridge proof. The Rust registry twin (`V3_STAGED_REGISTRY_TSV`) carries the byte-identical wire
string emitted by `emitVmJson2`.

## The chip-rate seam (CLOSED — decision #1, `SchemeRealizedByChip` DISCHARGED)

`leafLookup` is a single chip absorb of the 7 leaf fields (arity 7); each `nodeLookup` a single chip
absorb of `[FACT_MARK, l, r]` (arity 3). The DEPLOYED cap primitives are NOW exactly these single chip
absorbs: the cap-tree is re-committed to `cap_root.rs::cap_chip_absorb` (mirrored as
`DeployedCapTree`'s one `chipAbsorb` carrier), so `capLeafDigest S = S.chipAbsorb ∘ leafFields` and
`nodeOf S l r = S.chipAbsorb [FACT_MARK, l, r]`. The chip's `sponge (leafFields)` IS `capLeafDigest S
leaf` and `sponge [FACT_MARK, l, r]` IS `nodeOf S l r` when `sponge := S.chipAbsorb`.

`DeployedCapOpen`'s named bridge `SchemeRealizedByChip hash S` is therefore DISCHARGED by
`chipAbsorb_realizes` (both equations hold by `rfl`), and the two keystone theorems below specialize
`hash := S.chipAbsorb` and supply the realization internally — it is no longer a carried hypothesis.
The prior revision's rate-4 `hash_many` leaf + capacity-tagged `hash_fact` node (the source of the
gap) are GONE; one in-circuit cap hash everywhere.

## Mask convention (the fork CLOSED — the faithful two-axis gate)

The earlier revision's `writeMaskGate` pinned the abstract `Auth` rights mask `mask_lo == 3` — a
DIFFERENT convention from the deployed `cap_root.rs::CapLeaf.mask_lo` (the low-16 of a `cell/facet.rs`
`EffectMask` effect-KIND bitmap). The cutover RESOLVES that fork onto the deployed convention: the
authority leg now emits the FAITHFUL two-axis gates — `transferFacetGate` (`mask_lo == EFFECT_TRANSFER`)
+ `facetHiGate` (`mask_hi == 0`) decode the `EffectMask` facet and check the `EFFECT_TRANSFER` bit, and
`authTagGate` (`auth_tag == 1`) decodes the `AuthRequired` tier (`Signature`). A `Satisfied` row thus
discharges `confersTransferLeaf` (facet permits the effect-kind AND tier is satisfied), which the
bridge turns into the deployed `authorizedFacetB`. Residual: the tier is pinned to `Signature` here
rather than read off the leaf's committed `auth_tag` generically (FacetAuthority §10 named residual).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters only as the named
`CapHashScheme.chipAbsorb`/`chipCR` floor (and the chip-soundness `ChipTableSound`), inherited
unchanged from `DeployedCapOpen`. No sorry/native_decide/:= True.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Circuit.Emit.CapOpenEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint EFFECT_VM_WIDTH)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily TableId Lookup VmConstraint2 EffectVmDescriptor2 ChipTableSound Satisfied2)
open Dregg2.Circuit.DeployedCapOpen
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (capLeafDigest MembersAt confersTransferLeaf DeployedFaithful
   deployedCapOpen_implies_authorizedB)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (attenuateV3 APPENDIX_SPAN B_CAP_ROOT v3Of v3OfFrozen withSelectorGate withSelectorGate_satisfied2)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority (AuthProvided FacetCaps authorizedFacetB)

set_option autoImplicit false

/-! ## §1 — the concrete column layout: the cap-open appendix past the rotated R=24 width.

The rotated attenuate trace is `EFFECT_VM_WIDTH + APPENDIX_SPAN = 320` columns wide. The cap-open
appendix starts at `CAP_OPEN_BASE` and carries, in order: 7 leaf-field columns, 1 leaf-digest
column, then for each of `DEPTH = 16` levels a `(sib, dir, node)` triple, then the `capRoot` and
`src` columns. Total `CAP_OPEN_SPAN = 7 + 1 + 16·3 + 2 = 58`. -/

/-- The base column of the cap-open appendix (the first column past the rotated R=24 width). -/
def CAP_OPEN_BASE : Nat := EFFECT_VM_WIDTH + APPENDIX_SPAN

/-- The cap-open appendix width: 7 leaf + 1 digest + 16·(sib,dir,node) + capRoot + src + effBit +
`MASK_BITS` mask-bit columns. The trailing `effBit` column carries the turn's ACTUAL effect-kind bit;
the `MASK_BITS` bit columns (residual (a) — GENUINE MEMBERSHIP) carry the 24-bit decomposition of the
leaf's low mask limb, against which the genuine SUBMASK gate `facetEffGate` (`maskBitBoolGate` +
`maskReconGate` + `selectedBitGate`) checks `(effBit &&& mask_lo) = effBit` — NOT the over-strict
equality `mask_lo == effBit`. The bit columns are appended at the END of the block to localize the shift. -/
def CAP_OPEN_SPAN : Nat := 7 + 1 + DEPTH * 3 + 3 + MASK_BITS
  + (Dregg2.Circuit.DescriptorIR2.CHIP_OUT_LANES - 1) * (DEPTH + 1)

/-- The concrete cap-open column layout, pinned to the appendix. Leaf fields 0..6 at
`CAP_OPEN_BASE..+6`; leaf digest at `+7`; level `lvl`'s sibling/direction/node at `+8+3·lvl`,
`+9+3·lvl`, `+10+3·lvl`; cap_root at `+56`; src at `+57`; effBit at `+58`; the 24 mask-bit columns at
`+59..+82` (`bit i = CAP_OPEN_BASE + 59 + i`). -/
def capOpenCols (w : Nat) : CapOpenCols :=
  { leaf       := fun i => w + i.val
  , leafDigest := w + 7
  , sib        := fun lvl => w + 8 + 3 * lvl
  , dir        := fun lvl => w + 9 + 3 * lvl
  , node       := fun lvl => w + 10 + 3 * lvl
  , capRoot    := w + 8 + 3 * DEPTH       -- = w + 56
  , src        := w + 8 + 3 * DEPTH + 1   -- = w + 57
  , effBit     := w + 8 + 3 * DEPTH + 2   -- = w + 58
  , bit        := fun i => w + 8 + 3 * DEPTH + 3 + i -- = w + 59 + i
    -- Phase B-GATE: the 17 chip absorbs (leaf + 16 nodes) each carry 7 exposed lanes 1..7. The
    -- `7·17 = 119` lane columns are appended at the END of the appendix (past the mask bits),
    -- block `k` (k=0 leaf, k=lvl+1 node) at `LANE_BASE + 7·k`.
  , lanes      := fun k =>
      (List.range (Dregg2.Circuit.DescriptorIR2.CHIP_OUT_LANES - 1)).map
        (w + 8 + 3 * DEPTH + 3 + MASK_BITS + (Dregg2.Circuit.DescriptorIR2.CHIP_OUT_LANES - 1) * k + ·) }

/-- The cap-open appendix width is 210 (the 91-col base+mask block + `7·17 = 119` lane columns). -/
theorem cap_open_span : CAP_OPEN_SPAN = 210 := by decide

/-! ## §2 — the constraint list: the proven `DeployedCapOpen` constraints, assembled.

`leafLookup` + the 16 `nodeLookup`s ride `.lookup` (the chip-bus lookups the Rust interpreter
realizes); the four gate equations ride `.base (.gate …)` (the transition-builder gates). The list
is EXACTLY the constraints `DeployedCapOpen.Satisfied` quantifies over. -/

/-- The 16 per-level node-absorb chip lookups (`nodeLookup (capOpenCols w) 0..15`). -/
def nodeLookups (w : Nat) : List VmConstraint2 :=
  (List.range DEPTH).map (fun lvl => .lookup (nodeLookup (capOpenCols w) lvl))

/-- The 16 per-level direction-boolean gates (`dirBoolGate (capOpenCols w) 0..15`). -/
def dirBoolGates (w : Nat) : List VmConstraint2 :=
  (List.range DEPTH).map (fun lvl => .base (.gate (dirBoolGate (capOpenCols w) lvl)))

/-- The `MASK_BITS` per-bit boolean gates for the `mask_lo` decomposition (`maskBitBoolGate
(capOpenCols w) 0..23`) — each `mask_lo` bit column is `0` or `1`. -/
def maskBitGates (w : Nat) : List VmConstraint2 :=
  (List.range MASK_BITS).map (fun i => .base (.gate (maskBitBoolGate (capOpenCols w) i)))

/-! ## §3 — (DELETED) the Signature-pinned `capOpenAttenuateV3`/`transferCapOpenV3` descriptors.

These were the over-strict (`mask_lo == effBit` equality + constant facet/tier pins) cap-open
descriptors, kept "for the apex/refinement proofs only". The apex authority leg now refines the LIVE
`…CapOpenEffV3` membership descriptors (`transferCapOpenEffV3_authorizes`, §5.K below), which is also
what the deployed prover routes — so nothing is proven about an unwired descriptor and both pinned
descriptors + their full lemma cohort (`capOpenConstraints`, `capOpenAttenuateV3*`,
`transferCapOpenV3*`) are DELETED (Stage D). The shared appendix helpers `nodeLookups`/`dirBoolGates`/
`maskBitGates` survive — the effect-general `capOpenConstraintsEff n` (§5.F) reuses them. -/

/-- The rotated TRANSFER cohort descriptor (`v3OfFrozen` of the transfer v1 face — transfer-via-cap is a
VALUE effect, so the authority-frame freeze welds apply). Same width invariant as `attenuateV3`
(`EFFECT_VM_WIDTH + APPENDIX_SPAN`), so the cap-open appendix at `CAP_OPEN_BASE` applies. It is the base of
the LIVE `transferCapOpenEffV3` (§5.F); freezing it forces AFTER-r23 == BEFORE-r23 (+ lifecycle) for the
transfer-via-cap leg too, matching `RotatedKernelRefinement.transferV3` (`v3OfFrozen` of the same face). -/
def transferV3 : EffectVmDescriptor2 :=
  v3OfFrozen Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor

/-! ## §5.F — THE FAN-OUT: the effect-GENERAL cap-open appendix + per-effect descriptors.

`capOpenConstraints` pins the facet to `EFFECT_TRANSFER` (the `effBitGate`/`transferFacetGate`/`authTagGate`
constants). The fan-out to the OTHER cap-authorized effects (delegate, introduce, grantCap, revoke,
refreshDelegation, …) reuses the WHOLE appendix EXCEPT those constant pins: `capOpenConstraintsEff n` swaps
`effBitGate` for `effBitGateFor (1 <<< n)` (THIS effect's bit) and DROPS `transferFacetGate`/`authTagGate`
(the general `facetEffGate` carries the facet axis; the tier rides the decoded `auth_tag`). A `Satisfied2`
witness of `<effect>V3 ++ capOpenConstraintsEff n` rebuilds `DeployedCapOpen.SatisfiedEff … n`, hence
`capOpenEff_authorizes` into `authorizedFacetEffB … (1 <<< n)` — the cap must permit THAT effect-kind. -/

open Dregg2.Circuit.DeployedCapOpen
  (SatisfiedEff MembershipCore effBitGateFor capOpenEff_authorizes satisfiedEff_rejects_wrong_facet)
open Dregg2.Exec.FacetAuthority (authorizedFacetEffB)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (DeployedFaithfulEff tierOfTag)

/-- **`capOpenConstraintsEff n`** — the effect-GENERAL cap-open constraint list for effect-kind bit
`1 <<< n`: the leaf lookup, the 16 node lookups, the 16 dir gates, the root pin, the target binding, the
high-limb pin, the committed effect-bit pin `effBitGateFor … (1 <<< n)`, and the general facet gate. The
transfer constant pins (`transferFacetGate`/`authTagGate`) are GONE — the facet is bound to the committed
effect-bit column, the tier to the decoded `auth_tag`. Count: 1 + 16 + 16 + 5 = 38. -/
def capOpenConstraintsEff (w : Nat) (n : Nat) : List VmConstraint2 :=
  .lookup (leafLookup (capOpenCols w))
  :: nodeLookups w
  ++ dirBoolGates w
  ++ maskBitGates w
  ++ [ .base (.gate (rootPinGate (capOpenCols w)))
     , .base (.gate (targetBindGate (capOpenCols w)))
     , .base (.gate (effBitGateFor (capOpenCols w) ((1 <<< n : Nat) : ℤ)))
     , .base (.gate (maskReconGate (capOpenCols w)))
     , .base (.gate (selectedBitGate (capOpenCols w) n)) ]

/-- The effect-general constraint count is 1 leaf + 16 node + 16 dir + 32 mask-bit + 5 binding gates
(rootPin, targetBind, effBitGateFor, maskRecon, selectedBit) = 70. (NO `facetHiGate` — the FULL mask is
decomposed, so a broad `EFFECT_ALL` cap with `mask_hi ≠ 0` is admitted.) -/
theorem capOpenConstraintsEff_length (w : Nat) (n : Nat) : (capOpenConstraintsEff w n).length = 70 := by
  simp [capOpenConstraintsEff, nodeLookups, dirBoolGates, maskBitGates, DEPTH, MASK_BITS]

/-- **`effCapOpenV3 base name n`** — the GENERIC per-effect cap-open descriptor: an effect's rotated base
descriptor `base` (a `v3Of …` member, same `EFFECT_VM_WIDTH + APPENDIX_SPAN` width) widened by the cap-open
appendix at `CAP_OPEN_BASE`, carrying `capOpenConstraintsEff n` (THIS effect's bit). Every fan-out effect is
`effCapOpenV3 <effect>V3 "dregg-…-capopen" n`. -/
def effCapOpenV3 (base : EffectVmDescriptor2) (name : String) (n : Nat) : EffectVmDescriptor2 :=
  { base with
    name        := name
    traceWidth  := base.traceWidth + CAP_OPEN_SPAN
    constraints := base.constraints ++ capOpenConstraintsEff base.traceWidth n }

/-- Every effect-general cap-open constraint is a constraint of the descriptor. -/
theorem effCapOpenV3_constraints_mem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ capOpenConstraintsEff base.traceWidth n) :
    c ∈ (effCapOpenV3 base name n).constraints :=
  List.mem_append_right _ hc

/-! ### The cap-open APPENDIX-STRIP bridge (`capOpen_satisfied2_strips_to_base`).

The cap-open APPENDIX (`capOpenConstraintsEff`) is all `.lookup`/`.base (.gate …)` — it surfaces NO map/mem
op. So a `Satisfied2` witness of `effCapOpenV3 base name n` restricts to a `Satisfied2` of the bare `base`
(the appendix reads no base column and contributes no offline-checking op), exactly as `withSelectorGate`
strips. This is the analog of `withSelectorGate_satisfied2` for the cap-open wrapper: it lets the per-effect
CLASS-A `_descriptorRefines_sat` rungs — stated over `<slot>WriteV3` — lift to the DEPLOYED cap-open-wrapped
descriptor the apex fan-out selects (`Rfix tag = capOpenWrapper base`, which is NOT defeq to `base`). -/

/-- `effCapOpenV3` gathers exactly `base`'s map ops (the appendix is all lookups + base gates). -/
theorem effCapOpenV3_mapOpsOf (base : EffectVmDescriptor2) (name : String) (n : Nat) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapOpenV3 base name n)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf base := by
  simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effCapOpenV3, capOpenConstraintsEff,
    nodeLookups, dirBoolGates, maskBitGates, List.filterMap_append, List.filterMap_map,
    List.filterMap_cons]

/-- `effCapOpenV3` gathers exactly `base`'s mem ops. -/
theorem effCapOpenV3_memOpsOf (base : EffectVmDescriptor2) (name : String) (n : Nat) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapOpenV3 base name n)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf base := by
  simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effCapOpenV3, capOpenConstraintsEff,
    nodeLookups, dirBoolGates, maskBitGates, List.filterMap_append, List.filterMap_map,
    List.filterMap_cons]

/-- ...so the gathered memory log is `base`'s, op-for-op. -/
theorem effCapOpenV3_memLog (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (effCapOpenV3 base name n) t
      = Dregg2.Circuit.DescriptorIR2.memLog base t := by
  simp [Dregg2.Circuit.DescriptorIR2.memLog, effCapOpenV3_memOpsOf]

/-- ...and the gathered map log is `base`'s. -/
theorem effCapOpenV3_mapLog (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (effCapOpenV3 base name n) t
      = Dregg2.Circuit.DescriptorIR2.mapLog base t := by
  simp [Dregg2.Circuit.DescriptorIR2.mapLog, effCapOpenV3_mapOpsOf]

/-- **`effCapOpenV3_satisfied2_strips_to_base`** — a `Satisfied2` of the cap-open-widened descriptor
restricts to a `Satisfied2` of the bare `base` (constraint-subset monotonicity + the appendix contributing
no map/mem op). The cap-open analog of `withSelectorGate_satisfied2`. -/
theorem effCapOpenV3_satisfied2_strips_to_base (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (n : Nat) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (h : Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  { rowConstraints := fun i hi c hc =>
      h.rowConstraints i hi c (by
        show c ∈ base.constraints ++ capOpenConstraintsEff base.traceWidth n
        exact List.mem_append_left _ hc)
    rowHashes := h.rowHashes
    rowRanges := h.rowRanges
    memAddrsNodup := h.memAddrsNodup
    memClosed := by have := h.memClosed; rwa [effCapOpenV3_memLog] at this
    memDisciplined := by have := h.memDisciplined; rwa [effCapOpenV3_memLog] at this
    memBalanced := by have := h.memBalanced; rwa [effCapOpenV3_memLog] at this
    memTableFaithful := by have := h.memTableFaithful; rwa [effCapOpenV3_memLog] at this
    mapTableFaithful := by have := h.mapTableFaithful; rwa [effCapOpenV3_mapLog] at this }

/-- **`capOpen_satisfied2_strips_to_base`** — THE FULL APEX BRIDGE: a `Satisfied2` of the DEPLOYED cap-open
WRAPPER `withSelectorGate s (effCapOpenV3 base name n)` (the shape `Rfix tag` returns for the cap effects)
restricts to a `Satisfied2` of the bare `base`. Composes the selector-gate strip
(`withSelectorGate_satisfied2`) with the cap-open appendix strip. The cap-open authority appendix + selector
tooth are ADDITIVE — stripping them preserves the base descriptor's satisfaction, so the base
`<slot>WriteV3`-level `_forces_write` keystones lift to the apex's wrapped descriptor. -/
theorem capOpen_satisfied2_strips_to_base (hash : List ℤ → ℤ) (s : Nat) (base : EffectVmDescriptor2)
    (name : String) (n : Nat) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (h : Satisfied2 hash (withSelectorGate s (effCapOpenV3 base name n)) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  effCapOpenV3_satisfied2_strips_to_base hash base name n minit mfin maddrs t
    (withSelectorGate_satisfied2 hash s (effCapOpenV3 base name n) minit mfin maddrs t h)

/-- **`effCapOpenV3_satisfiedEff`** — a `Satisfied2` witness of `effCapOpenV3 base name n` rebuilds
`DeployedCapOpen.SatisfiedEff … n` on every row (the appendix constraints are satisfied regardless of the
base — they read no base column). The fan-out analog of `transferCapOpenV3_satisfied`. -/
theorem effCapOpenV3_satisfiedEff (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    SatisfiedEff hash t.tf (capOpenCols base.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) n := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effCapOpenV3_constraints_mem base name n
  -- the cap-open `.gate` clauses bind under `when_transition()` — on this ACTIVE (non-last) row their
  -- body equation holds; `hlastf` reduces the row's `isLast` flag to `false`.
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine
    { core := ?_, targetBound := ?_, effBitPinned := ?_
    , maskBitsBool := ?_, maskRecon := ?_, facetEffBound := ?_ }
  · refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
    · have hin : VmConstraint2.lookup (leafLookup (capOpenCols base.traceWidth)) ∈ capOpenConstraintsEff base.traceWidth n := by
        simp [capOpenConstraintsEff]
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt] using h
    · intro lvl hlvl
      have hin : VmConstraint2.lookup (nodeLookup (capOpenCols base.traceWidth) lvl) ∈ capOpenConstraintsEff base.traceWidth n := by
        refine List.mem_cons_of_mem _ ?_
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
        exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt] using h
    · intro lvl hlvl
      have hin : VmConstraint2.base (.gate (dirBoolGate (capOpenCols base.traceWidth) lvl)) ∈ capOpenConstraintsEff base.traceWidth n := by
        refine List.mem_cons_of_mem _ ?_
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
        exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
      have h := hrow _ (hmem _ hin)
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h
    · have hin : VmConstraint2.base (.gate (rootPinGate (capOpenCols base.traceWidth))) ∈ capOpenConstraintsEff base.traceWidth n := by
        simp [capOpenConstraintsEff]
      have h := hrow _ (hmem _ hin)
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h
  · have hin : VmConstraint2.base (.gate (targetBindGate (capOpenCols base.traceWidth))) ∈ capOpenConstraintsEff base.traceWidth n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h
  · have hin : VmConstraint2.base (.gate (effBitGateFor (capOpenCols base.traceWidth) ((1 <<< n : Nat) : ℤ)))
        ∈ capOpenConstraintsEff base.traceWidth n := by simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h
  · intro j hj
    have hin : VmConstraint2.base (.gate (maskBitBoolGate (capOpenCols base.traceWidth) j)) ∈ capOpenConstraintsEff base.traceWidth n := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h
  · have hin : VmConstraint2.base (.gate (maskReconGate (capOpenCols base.traceWidth))) ∈ capOpenConstraintsEff base.traceWidth n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h
  · have hin : VmConstraint2.base (.gate (selectedBitGate (capOpenCols base.traceWidth) n)) ∈ capOpenConstraintsEff base.traceWidth n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h; simpa using h

/-- **`effCapOpenV3_authorizes` — THE FAN-OUT AUTHORITY LEG (generic, live).** A `Satisfied2` witness of
`effCapOpenV3 base name n` whose opened leaf IS the faithfulness contract's `(actor ⇒ src)` edge discharges
the kernel's GENERAL `authorizedFacetEffB … (1 <<< n)` for the turn — over effect-kind `1 <<< n` (NOT
transfer), under any `provided` satisfying the committed tier. Every fan-out effect's authority leg is THIS
theorem at its `<effect>V3`/`n`. -/
theorem effCapOpenV3_authorizes {State : Type} (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < MASK_BITS) (S : CapHashScheme State) (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols base.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols base.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols base.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpenEff_authorizes S t.tf (capOpenCols base.traceWidth) _ n hn vkOfTag provided hChip
    (effCapOpenV3_satisfiedEff base name n S.chipAbsorb minit mfin maddrs t hsat i hi hnotlast)
    caps leafAt hfaith actor src dst amt hsrc hedge htier

-- The effect-general cap-open shares the appendix width (+59) and adds 38 constraints (5 gate-pins).
section FanoutDescriptors

/-- The effect-kind bit exponents (`facet.rs` `1 <<< n`) for the cap-authorized fan-out effects. -/
def EFF_TRANSFER           : Nat := 1   -- transfer, attenuate-via-transfer-cap (EFFECT_TRANSFER)
def EFF_GRANT_CAPABILITY   : Nat := 2   -- grantCap, delegateAtten, attenuate (EFFECT_GRANT_CAPABILITY)
def EFF_REVOKE_CAPABILITY  : Nat := 3   -- revokeCapability (EFFECT_REVOKE_CAPABILITY)
def EFF_INTRODUCE          : Nat := 13  -- introduce (EFFECT_INTRODUCE)
def EFF_DELEGATION_OPS     : Nat := 16  -- delegate, revoke(Delegation), refreshDelegation (EFFECT_DELEGATION_OPS)

/-- The rotated INTRODUCE base (`v3Of` of the introduce v1 face). -/
def introduceV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitIntroduce.introduceVmDescriptor
/-- The rotated GRANT-CAP / DELEGATE-ATTEN base (`v3Of` of the attenuate-A v1 face — the deployed
grantCap base; `EffectVmEmitDelegateAtten.delegateAttenVmDescriptor` IS `attenuateVmDescriptor`, so
delegate-via-cap shares this base, distinguished only by the descriptor name string). -/
def grantCapV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptor
/-- The rotated REVOKE-DELEGATION base. -/
def revokeDelegationV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.revokeVmDescriptor
/-- The rotated REFRESH-DELEGATION base. -/
def refreshDelegationV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation.refreshVmDescriptor
/-- The rotated REVOKE-CAPABILITY base. -/
def revokeCapabilityBaseV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor

/-- **`delegateCapOpenV3`** — delegate-via-cap (the delegateAtten/attenuate base + the
`EFFECT_DELEGATION_OPS` appendix). The cross-vat delegate routes the in-circuit cap-membership open; the
cap must permit `EFFECT_DELEGATION_OPS` (`1 <<< 16`). -/
def delegateCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 grantCapV3 "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)
/-- **`introduceCapOpenV3`** — introduce-via-cap; the cap must permit `EFFECT_INTRODUCE` (`1 <<< 13`). -/
def introduceCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
    (effCapOpenV3 introduceV3 "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE)
/-- **`grantCapCapOpenV3`** — grantCap-via-cap; the cap must permit `EFFECT_GRANT_CAPABILITY` (`1 <<< 2`). -/
def grantCapCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 grantCapV3 "dregg-effectvm-grantCap-v1-rot24-v3-capopen" EFF_GRANT_CAPABILITY)
/-- **`revokeCapOpenV3`** — revoke(Delegation)-via-cap; the cap must permit `EFFECT_DELEGATION_OPS`. -/
def revokeCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
    (effCapOpenV3 revokeDelegationV3 "dregg-effectvm-revoke-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)
/-- **`refreshDelegationCapOpenV3`** — refreshDelegation-via-cap; cap must permit `EFFECT_DELEGATION_OPS`. -/
def refreshDelegationCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
    (effCapOpenV3 refreshDelegationV3 "dregg-effectvm-refresh-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)
/-- **`revokeCapabilityCapOpenV3`** — revokeCapability-via-cap; cap must permit `EFFECT_REVOKE_CAPABILITY`. -/
def revokeCapabilityCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
    (effCapOpenV3 revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY)

/-- **`spawnCapOpenV3`** — the AUTHORITY-ONLY spawn cap-open (the FROZEN `spawnV3` base + the
EFF_DELEGATION_OPS authority appendix). The membership crown is forced, but the cap handoff (cap-tree
write) rides the FROZEN `cap_root` (`gCapPass`) — the post child cap_root is host-trusted. This is the
spawn ROUTE-FORGE the verifier tooth (`is_forbidden_authority_only_cap_write_descriptor`) REJECTS: the
producer must prove the WRITE wrapper `spawnWriteCapOpenV3` (where the handoff is FORCED on the wire). The
genuine spawn route ALWAYS supplies the parent's c-list (a spawn confers a held cap), so the write wrapper
is the live route; THIS is the named, light-client-rejected fallback. Mirrors `revokeCapabilityCapOpenV3`. -/
def spawnCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmitSpawn.SEL_SPAWN_RT
    (effCapOpenV3 EffectVmEmitRotationV3.spawnV3 "dregg-effectvm-spawn-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)

/-! ### The WRITE-FORCING fan-out cap-open wrappers (the frozen-face close — guarantee A circuit-forced).

The wrappers above ride the FROZEN bases (`introduceV3`/`revokeDelegationV3` = `v3Of …` with `gCapPass`),
which force the authority READ but FREEZE the cap-tree WRITE off-row. These two ride the MOVING write bases
(`introduceWriteV3`/`revokeDelegationWriteV3` = `v3OfWith …Genuine [heldReadOp, insert/removeWriteOp]`), so
the deployed descriptor itself FORCES the cap-tree write (`Rfix tag` re-points here; the main loop wires).
Same `EFFECT_VM_WIDTH + APPENDIX_SPAN` base width, so the `CAP_OPEN_SPAN`-widened width is unchanged; the
authority appendix + `_authorizes` keystones apply verbatim (the appendix reads no base column). -/

/-- **`introduceWriteCapOpenV3`** — introduce-via-cap on the WRITE-FORCING base (`introduceWriteV3`): the
authority READ appendix + the deployed `insertWriteOp` (the cap-tree write FORCED, not frozen off-row). -/
def introduceWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
    (effCapOpenV3 EffectVmEmitRotationV3.introduceWriteV3
      "dregg-effectvm-introduce-v1-rot24-v3-write-capopen" EFF_INTRODUCE)

/-- **`revokeDelegationWriteCapOpenV3`** — revoke(Delegation)-via-cap on the WRITE-FORCING base
(`revokeDelegationWriteV3`): the authority READ appendix + the deployed `removeWriteOp` (the cap-tree REMOVE
FORCED, not frozen off-row). -/
def revokeDelegationWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
    (effCapOpenV3 EffectVmEmitRotationV3.revokeDelegationWriteV3
      "dregg-effectvm-revoke-v1-rot24-v3-write-capopen" EFF_DELEGATION_OPS)

/-- **`revokeCapabilityWriteCapOpenV3`** — revokeCapability-via-cap on the WRITE-FORCING base
(`revokeCapabilityV3` = the MOVING `…GenuineNoRecomputeTick` face + `[heldReadOpRot, removeWriteOpRot]`): the
authority READ appendix AT `EFF_REVOKE_CAPABILITY` + the deployed `removeWriteOpRot` (the cap-tree REMOVE
FORCED in-circuit on the rotated AFTER cap-root limb, var 264 — NOT frozen off-row). Unlike
`revokeCapabilityCapOpenV3` (base `revokeCapabilityBaseV3`, the FROZEN `v3Of` authority-ONLY leg whose
cap-root REMOVE rides UNBOUND on the light-client wire — the ROUTE-FORGE), THIS carries BOTH the authority
appendix AND the cap-tree REMOVE in the SINGLE descriptor the light client verifies. The SDK cap-open route
re-points here when the node supplies the c-list (the write witness); the authority-only wrapper is then
light-client-REJECTED. Mirrors `revokeDelegationWriteCapOpenV3` EXACTLY. -/
def revokeCapabilityWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
    (effCapOpenV3 EffectVmEmitRotationV3.revokeCapabilityV3
      "dregg-effectvm-revokeCapability-v1-rot24-v3-write-capopen" EFF_REVOKE_CAPABILITY)

/-- **`refreshDelegationWriteCapOpenV3`** — refreshDelegation-via-cap on the WRITE-FORCING base
(`refreshDelegationWriteV3`): the authority READ appendix + the deployed DELEG-tree UPDATE-write op (the
DELEGATIONS-tree write FORCED in-circuit, not the `delegRoot_runtime_column_pending` supplied digest). The
cap must permit `EFFECT_DELEGATION_OPS`. The apex (`Rfix 55` re-pointed) wires this for the FULL guarantee
A — refreshDelegation reaches Class-A. -/
def refreshDelegationWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
    (effCapOpenV3 EffectVmEmitRotationV3.refreshDelegationWriteV3
      "dregg-effectvm-refresh-v1-rot24-v3-write-capopen" EFF_DELEGATION_OPS)

/-- **`delegateWriteCapOpenV3`** — delegate-via-cap on the WRITE-FORCING base (`grantCapWriteV3` = the moving
attenuate-A face + `[heldReadOp, insertWriteOp]`): the authority READ appendix + the deployed `insertWriteOp`.
Unlike `delegateCapOpenV3` (base `grantCapV3`, no write leg, authority-only), THIS carries BOTH the authority
appendix AND the cap-tree write — the apex (`Rfix 1` re-pointed) wires it for the FULL guarantee A. -/
def delegateWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 EffectVmEmitRotationV3.grantCapWriteV3
      "dregg-effectvm-delegate-v1-rot24-v3-write-capopen" EFF_DELEGATION_OPS)

/-- **`spawnWriteCapOpenV3`** — spawn-via-cap on the WRITE-FORCING base (`spawnWriteV3` = the spawn actor
face REBASED onto the cap-WRITE rotation + the cells grow-gate INSERT + the cap-tree handoff INSERT). The
authority READ appendix (at `EFF_DELEGATION_OPS` — the parent confers a held cap PERMITTING delegation,
exactly like `delegate`) + the deployed cap-tree `insertWriteOpRot` (the parent→child cap handoff FORCED
in-circuit on the rotated AFTER cap-root limb, NOT frozen off-row). Unlike the authority-only spawn route,
THIS carries BOTH the authority appendix AND the cap-tree INSERT in the SINGLE descriptor the light client
verifies — so a forged after-cap-root / missing-anchor / colliding-child-key is REJECTED. Mirrors
`delegateWriteCapOpenV3` EXACTLY. -/
def spawnWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmitSpawn.SEL_SPAWN_RT
    (effCapOpenV3 EffectVmEmitRotationV3.spawnWriteV3
      "dregg-effectvm-spawn-v1-rot24-v3-write-capopen" EFF_DELEGATION_OPS)

/-- **`grantCapWriteCapOpenV3`** — grantCap-via-cap on the WRITE-FORCING base (`grantCapWriteV3`): authority
appendix + the deployed `insertWriteOp`. The apex (`Rfix` for grantCap re-pointed) wires it. -/
def grantCapWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 EffectVmEmitRotationV3.grantCapWriteV3
      "dregg-effectvm-grantCap-v1-rot24-v3-write-capopen" EFF_GRANT_CAPABILITY)

/-- **`delegateAttenWriteCapOpenV3`** — delegateAtten-via-cap on the WRITE-FORCING base (`delegateAttenV3` =
the moving attenuate-A face + `[heldReadOp, insertWriteOp, submaskLookup]`): authority appendix + the deployed
`insertWriteOp` + the `granted ⊑ held` submask (non-amplification). The apex (`Rfix 11` re-pointed) wires it. -/
def delegateAttenWriteCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 EffectVmEmitRotationV3.delegateAttenV3
      "dregg-effectvm-delegateAtten-v1-rot24-v3-write-capopen" EFF_GRANT_CAPABILITY)

-- The write-forcing wrappers add the SAME +71 constraints (70 appendix + selector tooth) over their
-- write base + `CAP_OPEN_SPAN` cols; the write base adds 2 map-ops over the frozen/genuine base.
#guard introduceWriteCapOpenV3.traceWidth == EffectVmEmitRotationV3.introduceWriteV3.traceWidth + CAP_OPEN_SPAN
#guard revokeDelegationWriteCapOpenV3.traceWidth == EffectVmEmitRotationV3.revokeDelegationWriteV3.traceWidth + CAP_OPEN_SPAN
#guard revokeCapabilityWriteCapOpenV3.traceWidth == EffectVmEmitRotationV3.revokeCapabilityV3.traceWidth + CAP_OPEN_SPAN
#guard introduceWriteCapOpenV3.constraints.length == EffectVmEmitRotationV3.introduceWriteV3.constraints.length + 71
#guard revokeDelegationWriteCapOpenV3.constraints.length == EffectVmEmitRotationV3.revokeDelegationWriteV3.constraints.length + 71
#guard revokeCapabilityWriteCapOpenV3.constraints.length == EffectVmEmitRotationV3.revokeCapabilityV3.constraints.length + 71
#guard spawnWriteCapOpenV3.traceWidth == EffectVmEmitRotationV3.spawnWriteV3.traceWidth + CAP_OPEN_SPAN
#guard spawnWriteCapOpenV3.constraints.length == EffectVmEmitRotationV3.spawnWriteV3.constraints.length + 71

/-- **`transferCapOpenEffV3`** (residual (a) — THE LIVE transfer cap-open) — the transfer base + the
effect-GENERAL appendix at `EFF_TRANSFER` (bit 1). Carries `capOpenConstraintsEff 1`: the genuine SUBMASK facet gate
(a BROAD honest transfer cap `mask_lo = 0xFFFF` PASSES — bit 1 set) and the DECODED tier (any committed
`auth_tag`, not pinned Signature). This is the descriptor the live `transferCapOpenVmDescriptor2R24`
routing proves through, so an honest transfer cap — broad mask, None/Signature tier — PROVES. -/
def transferCapOpenEffV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    (effCapOpenV3 transferV3 "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER)

/-- **`attenuateCapOpenEffV3`** (residual (a) — THE LIVE attenuate cap-open) — the attenuate base + the
effect-GENERAL appendix at `EFF_TRANSFER` (bit 1; the attenuate cap-open's leaf must permit
`EFFECT_TRANSFER`, mirroring the deployed `attenuateCapOpenVmDescriptor2R24` routing). Genuine submask
facet + decoded tier, so an honest broad/None-tier cap PROVES. -/
def attenuateCapOpenEffV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.ATTENUATE_CAPABILITY
    (effCapOpenV3 attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER)

-- The live transfer/attenuate effect-general descriptors share the appendix + the appended
-- `selectorGate` tooth: +70 appendix constraints +1 selector gate = +71; +91 cols (the gate is
-- a `.base`, no new column).
#guard transferCapOpenEffV3.constraints.length == transferV3.constraints.length + 71
#guard attenuateCapOpenEffV3.constraints.length == attenuateV3.constraints.length + 71
#guard transferCapOpenEffV3.traceWidth == transferV3.traceWidth + CAP_OPEN_SPAN
#guard attenuateCapOpenEffV3.traceWidth == attenuateV3.traceWidth + CAP_OPEN_SPAN

-- Each fan-out descriptor adds the 70-constraint effect-general appendix + the selector-gate tooth
-- (+71 constraints total) + 91 cols past its base.
#guard delegateCapOpenV3.constraints.length == grantCapV3.constraints.length + 71
#guard introduceCapOpenV3.constraints.length == introduceV3.constraints.length + 71
#guard grantCapCapOpenV3.constraints.length == grantCapV3.constraints.length + 71
#guard revokeCapOpenV3.constraints.length == revokeDelegationV3.constraints.length + 71
#guard refreshDelegationCapOpenV3.constraints.length == refreshDelegationV3.constraints.length + 71
#guard revokeCapabilityCapOpenV3.constraints.length == revokeCapabilityBaseV3.constraints.length + 71
#guard delegateCapOpenV3.traceWidth == grantCapV3.traceWidth + CAP_OPEN_SPAN
#guard introduceCapOpenV3.traceWidth == introduceV3.traceWidth + CAP_OPEN_SPAN
#guard grantCapCapOpenV3.traceWidth == grantCapV3.traceWidth + CAP_OPEN_SPAN
#guard revokeCapOpenV3.traceWidth == revokeDelegationV3.traceWidth + CAP_OPEN_SPAN
#guard refreshDelegationCapOpenV3.traceWidth == refreshDelegationV3.traceWidth + CAP_OPEN_SPAN
#guard revokeCapabilityCapOpenV3.traceWidth == revokeCapabilityBaseV3.traceWidth + CAP_OPEN_SPAN

end FanoutDescriptors

/-! ## §5.K — THE LIVE AUTHORITY KEYSTONES (`…CapOpenEffV3_authorizes`): the apex authority leg over
the DEPLOYED descriptor.

The apex authority leg (`RotatedKernelRefinementFacet.TransferAuthoritySource`) must refine the descriptor
the LIVE prover selects — `transferCapOpenEffV3` for `[Transfer]`, `attenuateCapOpenEffV3` for
`[AttenuateCapability]` (both at `EFF_TRANSFER`, the genuine SUBMASK facet + DECODED tier). These keystones
give the kernel's faithful `authorizedFacetB caps provided turn` —
`authorizedFacetB caps provided turn` — but over the membership descriptor's `Satisfied2`, routed through
`effCapOpenV3_authorizes` (membership ⟹ `authorizedFacetEffB … (1 <<< EFF_TRANSFER)`) and the kernel
identity `authorizedFacetB = authorizedFacetEffB … (turnEffectBit turn)` (both `= EFFECT_TRANSFER = 1 <<<
1`). No constant is re-pinned; the facet axis is the genuine submask, the tier is the committed decode. -/

open Dregg2.Exec.FacetAuthority (authorizedFacetEffB authorizedFacetB_eq_eff turnEffectBit EFFECT_TRANSFER)

/-- **`transferCapOpenEffV3_authorizes` — THE LIVE TRANSFER AUTHORITY KEYSTONE.** A `Satisfied2` witness of
the LIVE `transferCapOpenEffV3` descriptor (the genuine submask facet at `EFF_TRANSFER` + decoded tier)
whose opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges the kernel's `authorizedFacetB
caps provided turn`, over the descriptor the live `transferCapOpenVmDescriptor2R24` route proves through. The authority is FORCED by the
in-circuit depth-16 membership open, NOT carried; the tier is the genuine committed decode (`htier`). -/
theorem transferCapOpenEffV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb transferCapOpenEffV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_TRANSFER) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols transferV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols transferV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols transferV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  -- Strip the appended `selectorGate` tooth (constraint-subset monotonicity) before applying the
  -- bare keystone: the appendix reads no base/selector column, so the open is unaffected.
  have hsat := withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    _ minit mfin maddrs t hsat
  have h := effCapOpenV3_authorizes (State := State) transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER (by decide)
    S vkOfTag provided minit mfin maddrs t hChip hsat i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier
  refine ⟨?_, h.2⟩
  -- `authorizedFacetB = authorizedFacetEffB … (turnEffectBit turn)`, and `turnEffectBit _ =
  -- EFFECT_TRANSFER = 1 <<< 1 = 1 <<< EFF_TRANSFER`, so the membership conclusion IS the gate.
  rw [authorizedFacetB_eq_eff]
  exact h.1

/-- **`attenuateCapOpenEffV3_authorizes` — THE LIVE ATTENUATE AUTHORITY KEYSTONE.** As
`transferCapOpenEffV3_authorizes` but over the LIVE `attenuateCapOpenEffV3` descriptor (the attenuate base +
the `EFF_TRANSFER` submask appendix) — the descriptor the live `attenuateCapOpenVmDescriptor2R24` route
proves through. Same `authorizedFacetB caps provided turn` conclusion, forced from the in-circuit open. -/
theorem attenuateCapOpenEffV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb attenuateCapOpenEffV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_TRANSFER) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols attenuateV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols attenuateV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols attenuateV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hsat := withSelectorGate_satisfied2 S.chipAbsorb
    Dregg2.Circuit.Emit.EffectVmEmit.sel.ATTENUATE_CAPABILITY _ minit mfin maddrs t hsat
  have h := effCapOpenV3_authorizes (State := State) attenuateV3
    "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER (by decide)
    S vkOfTag provided minit mfin maddrs t hChip hsat i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier
  refine ⟨?_, h.2⟩
  rw [authorizedFacetB_eq_eff]
  exact h.1

/-- **`transferCapOpenEffV3_rejects_wrong_facet` (the LIVE transfer authority tooth).** A row of a
`transferCapOpenEffV3` witness whose leaf's `EFF_TRANSFER` mask bit is CLEAR (the cap does NOT carry the
transfer facet) CANNOT satisfy the appendix — the SELECTED-bit submask gate bites in-circuit. The negative
half of the live keystone (a wrong-facet cap ⟹ UNSAT), ported onto the deployed descriptor. -/
theorem transferCapOpenEffV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols transferV3.traceWidth).bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash transferCapOpenEffV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols transferV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_TRANSFER hclear
    (effCapOpenV3_satisfiedEff transferV3 "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER
      hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-- **`attenuateCapOpenEffV3_rejects_wrong_facet` (the LIVE attenuate authority tooth).** As above over
`attenuateCapOpenEffV3`: a leaf lacking the `EFF_TRANSFER` facet bit ⟹ the appendix is UNSAT. -/
theorem attenuateCapOpenEffV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols attenuateV3.traceWidth).bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash attenuateCapOpenEffV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols attenuateV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_TRANSFER hclear
    (effCapOpenV3_satisfiedEff attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER
      hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.ATTENUATE_CAPABILITY
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-! ## §5.F — THE FAN-OUT AUTHORITY KEYSTONES (`…CapOpenV3_authorizes`): the 6 cap-effects' apex
authority leg over their DEPLOYED fan-out descriptor.

`transfer`/`attenuate` ride `EFF_TRANSFER` (bit 1) and so collapse to `authorizedFacetB` (the
`turnEffectBit _ = EFFECT_TRANSFER` identity). The 6 fan-out effects ride DIFFERENT effect-kind bits
(introduce=13, delegate/revoke/refresh=16, grantCap=2, revokeCapability=3); their authority leg does NOT
collapse to `authorizedFacetB` — it is the GENERAL `authorizedFacetEffB caps provided (1 <<< n)` at the
effect's OWN bit, which is exactly what a per-effect authority gate needs (a cap permitting a DIFFERENT
effect-kind than the turn performs is REJECTED). Each keystone below is `effCapOpenV3_authorizes`
specialized to its `<effect>CapOpenV3`/`n`; each tooth is `satisfiedEff_rejects_wrong_facet` at the
effect's bit (the bit-clear leaf ⟹ the submask gate UNSAT). -/

/-- **`introduceCapOpenV3_authorizes` — THE LIVE INTRODUCE AUTHORITY KEYSTONE** (the BEACHHEAD). A
`Satisfied2` witness of the LIVE `introduceCapOpenV3` descriptor (the genuine submask facet at
`EFF_INTRODUCE` + decoded tier) whose opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges
the kernel's GENERAL `authorizedFacetEffB caps provided (1 <<< EFF_INTRODUCE)` for the turn — the
introduce facet, NOT the transfer facet. Forced by the in-circuit depth-16 membership open. -/
theorem introduceCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb introduceCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_INTRODUCE) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols introduceV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols introduceV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols introduceV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_INTRODUCE)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) introduceV3
    "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
      _ minit mfin maddrs t hsat) i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`delegateCapOpenV3_authorizes`** — the LIVE delegate-via-cap authority keystone (the delegateAtten
base + the `EFF_DELEGATION_OPS` appendix). Discharges `authorizedFacetEffB caps provided (1 <<<
EFF_DELEGATION_OPS)` — the delegation-ops facet — forced by the in-circuit open. -/
theorem delegateCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb delegateCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_DELEGATION_OPS) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols grantCapV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols grantCapV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols grantCapV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) grantCapV3
    "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen" EFF_DELEGATION_OPS (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
      _ minit mfin maddrs t hsat) i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`grantCapCapOpenV3_authorizes`** — the LIVE grantCap-via-cap authority keystone. Discharges
`authorizedFacetEffB caps provided (1 <<< EFF_GRANT_CAPABILITY)` — the grant-capability facet. -/
theorem grantCapCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb grantCapCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_GRANT_CAPABILITY) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols grantCapV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols grantCapV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols grantCapV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_GRANT_CAPABILITY)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) grantCapV3
    "dregg-effectvm-grantCap-v1-rot24-v3-capopen" EFF_GRANT_CAPABILITY (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
      _ minit mfin maddrs t hsat) i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`revokeCapOpenV3_authorizes`** — the LIVE revoke(Delegation)-via-cap authority keystone. Discharges
`authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)` — the delegation-ops facet. -/
theorem revokeCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb revokeCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_DELEGATION_OPS) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols revokeDelegationV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols revokeDelegationV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols revokeDelegationV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) revokeDelegationV3
    "dregg-effectvm-revoke-v1-rot24-v3-capopen" EFF_DELEGATION_OPS (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
      _ minit mfin maddrs t hsat) i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`refreshDelegationCapOpenV3_authorizes`** — the LIVE refreshDelegation-via-cap authority keystone.
Discharges `authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)` — the delegation-ops facet. -/
theorem refreshDelegationCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb refreshDelegationCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_DELEGATION_OPS) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols refreshDelegationV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols refreshDelegationV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols refreshDelegationV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) refreshDelegationV3
    "dregg-effectvm-refresh-v1-rot24-v3-capopen" EFF_DELEGATION_OPS (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
      _ minit mfin maddrs t hsat) i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`revokeCapabilityCapOpenV3_authorizes`** — the LIVE revokeCapability-via-cap authority keystone.
Discharges `authorizedFacetEffB caps provided (1 <<< EFF_REVOKE_CAPABILITY)` — the revoke-capability
facet. -/
theorem revokeCapabilityCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb revokeCapabilityCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_REVOKE_CAPABILITY) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols revokeCapabilityBaseV3.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols revokeCapabilityBaseV3.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols revokeCapabilityBaseV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_REVOKE_CAPABILITY)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) revokeCapabilityBaseV3
    "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
      _ minit mfin maddrs t hsat) i hi hnotlast caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-! ### The fan-out authority TEETH (`…CapOpenV3_rejects_wrong_facet`): a leaf lacking the effect's
facet bit ⟹ the SELECTED-bit submask gate bites ⟹ the appendix is UNSAT. Both-polarity per effect. -/

/-- **`introduceCapOpenV3_rejects_wrong_facet`** — a row whose leaf's `EFF_INTRODUCE` mask bit is CLEAR
cannot satisfy the introduce appendix (the submask gate bites in-circuit). -/
theorem introduceCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols introduceV3.traceWidth).bit EFF_INTRODUCE) = 0) :
    ¬ Satisfied2 hash introduceCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols introduceV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_INTRODUCE hclear
    (effCapOpenV3_satisfiedEff introduceV3 "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE
      hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-- **`delegateCapOpenV3_rejects_wrong_facet`** — a leaf lacking the `EFF_DELEGATION_OPS` bit ⟹ UNSAT. -/
theorem delegateCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols grantCapV3.traceWidth).bit EFF_DELEGATION_OPS) = 0) :
    ¬ Satisfied2 hash delegateCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols grantCapV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_DELEGATION_OPS hclear
    (effCapOpenV3_satisfiedEff grantCapV3 "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen"
      EFF_DELEGATION_OPS hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-- **`grantCapCapOpenV3_rejects_wrong_facet`** — a leaf lacking the `EFF_GRANT_CAPABILITY` bit ⟹ UNSAT. -/
theorem grantCapCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols grantCapV3.traceWidth).bit EFF_GRANT_CAPABILITY) = 0) :
    ¬ Satisfied2 hash grantCapCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols grantCapV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_GRANT_CAPABILITY hclear
    (effCapOpenV3_satisfiedEff grantCapV3 "dregg-effectvm-grantCap-v1-rot24-v3-capopen"
      EFF_GRANT_CAPABILITY hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-- **`revokeCapOpenV3_rejects_wrong_facet`** — a leaf lacking the `EFF_DELEGATION_OPS` bit ⟹ UNSAT. -/
theorem revokeCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols revokeDelegationV3.traceWidth).bit EFF_DELEGATION_OPS) = 0) :
    ¬ Satisfied2 hash revokeCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols revokeDelegationV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_DELEGATION_OPS hclear
    (effCapOpenV3_satisfiedEff revokeDelegationV3 "dregg-effectvm-revoke-v1-rot24-v3-capopen"
      EFF_DELEGATION_OPS hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-- **`refreshDelegationCapOpenV3_rejects_wrong_facet`** — a leaf lacking `EFF_DELEGATION_OPS` ⟹ UNSAT. -/
theorem refreshDelegationCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols refreshDelegationV3.traceWidth).bit EFF_DELEGATION_OPS) = 0) :
    ¬ Satisfied2 hash refreshDelegationCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols refreshDelegationV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_DELEGATION_OPS hclear
    (effCapOpenV3_satisfiedEff refreshDelegationV3 "dregg-effectvm-refresh-v1-rot24-v3-capopen"
      EFF_DELEGATION_OPS hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-- **`revokeCapabilityCapOpenV3_rejects_wrong_facet`** — a leaf lacking `EFF_REVOKE_CAPABILITY` ⟹ UNSAT. -/
theorem revokeCapabilityCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc ((capOpenCols revokeCapabilityBaseV3.traceWidth).bit EFF_REVOKE_CAPABILITY) = 0) :
    ¬ Satisfied2 hash revokeCapabilityCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf (capOpenCols revokeCapabilityBaseV3.traceWidth)
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_REVOKE_CAPABILITY hclear
    (effCapOpenV3_satisfiedEff revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen"
      EFF_REVOKE_CAPABILITY hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
        _ minit mfin maddrs t hsat) i hi hnotlast)

/-! ## §6 — the registry WITH the cap-open (F5 — `Rfix` ranges over the LIVE authority descriptor).

`EffectVmEmitRotationV3.v3Registry` is the 36-member cohort; it CANNOT itself name the cap-open
(`CapOpenEmit` imports `EffectVmEmitRotationV3`, so the dependency runs this way). The deployed wire
registry (`V3_STAGED_REGISTRY_TSV`) carries 45 lines — the 36 cohort members + the 6 fan-out cap-open
members + the 2 LIVE effect-general transfer/attenuate legs + the fee'd transfer at the tail
(`EmitRotationV3.lean` emits them). `v3RegistryCapOpen` is the Lean twin of that registry. The
soundness apex's `Rfix` ranges over positions 0..43 (unchanged); the fee'd transfer at 44 is re-keyed
over THIS list, so `registryCommit Rfix` ranges over the LIVE cap-open descriptor (`Rfix 12 =
attenuateCapOpenEffV3`) — the one in-circuit authority gadget the apex authority leg refines IS inside
the registry the apex's `StarkSound` quantifies over (F5 CLOSED, on the LIVE descriptor). -/

/-- **`v3RegistryCapOpen`** — the 45-member deployed registry: the 36 cohort members
(`EffectVmEmitRotationV3.v3Registry`) + the 6 fan-out cap-open members (delegate/introduce/grantCap/
revoke/refreshDelegation/revokeCapability) + the 2 LIVE effect-general legs
(`transferCapOpenEffV3`/`attenuateCapOpenEffV3`, the genuine-submask + decoded-tier descriptors the
deployed prover routes AND the apex authority leg refines). The Lean twin of the staged registry TSV;
the soundness apex's `Rfix` re-keys over it. -/
def v3RegistryCapOpen : List (String × EffectVmDescriptor2) :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry
    ++ [ -- THE FAN-OUT (residual (a) closed for these 6): each carries the effect-GENERAL appendix
         -- (`capOpenConstraintsEff n`) binding the cap to THAT effect-kind bit, not transfer.
         ("delegateCapOpenVmDescriptor2R24", delegateCapOpenV3)
       , ("introduceCapOpenVmDescriptor2R24", introduceCapOpenV3)
       , ("grantCapCapOpenVmDescriptor2R24", grantCapCapOpenV3)
       , ("revokeCapOpenVmDescriptor2R24", revokeCapOpenV3)
       , ("refreshDelegationCapOpenVmDescriptor2R24", refreshDelegationCapOpenV3)
       , ("revokeCapabilityCapOpenVmDescriptor2R24", revokeCapabilityCapOpenV3)
       -- residual (a) — THE LIVE transfer/attenuate cap-open members (genuine submask facet +
       -- DECODED tier). The live prover routes these `…-eff` descriptors AND the apex authority leg
       -- refines them (`transferCapOpenEffV3_authorizes`) — the wire and the proven descriptor are
       -- ONE. An honest broad/None-tier cap PROVES.
       , ("transferCapOpenEffVmDescriptor2R24", transferCapOpenEffV3)
       , ("attenuateCapOpenEffVmDescriptor2R24", attenuateCapOpenEffV3)
       -- THE FEE'D TRANSFER (trust-surface hole #5) — appended at the TAIL (index 44) so the 0..43
       -- positional apex is untouched. The deployed SOVEREIGN transfer routes HERE: the fee is
       -- debited in-circuit (`new = old − transfer − fee`) and pinned to the published fee PI (39
       -- PIs), so the fee debit is a PROVEN balance constraint — a ledgerless light client needs no
       -- trusted `+ turn.fee` reconstruction.
       , ("transferFeeVmDescriptor2R24",
          Dregg2.Circuit.Emit.EffectVmEmitRotationV3.transferFeeV3) ]

/-- The registry-with-cap-open has 45 members (36 cohort + 6 fan-out + 2 live `-eff`
transfer/attenuate + the fee'd transfer at the tail). The Signature-pinned
`capOpenAttenuateV3`/`transferCapOpenV3` are DELETED — the apex authority leg refines the LIVE
`…CapOpenEffV3` descriptors, so nothing is proven about an unwired descriptor. -/
theorem v3RegistryCapOpen_length : v3RegistryCapOpen.length = 45 := by
  simp [v3RegistryCapOpen, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry]

-- The cap-open authority members are positions 36..43; the 36 cohort members are unchanged at 0..35;
-- the fee'd transfer rides the tail at 44.
#guard v3RegistryCapOpen.length == 45
#guard (v3RegistryCapOpen[44]?.map (·.1)) == some "transferFeeVmDescriptor2R24"
#guard (v3RegistryCapOpen[36]?.map (·.1)) == some "delegateCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[37]?.map (·.1)) == some "introduceCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[38]?.map (·.1)) == some "grantCapCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[39]?.map (·.1)) == some "revokeCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[40]?.map (·.1)) == some "refreshDelegationCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[41]?.map (·.1)) == some "revokeCapabilityCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[42]?.map (·.1)) == some "transferCapOpenEffVmDescriptor2R24"
#guard (v3RegistryCapOpen[43]?.map (·.1)) == some "attenuateCapOpenEffVmDescriptor2R24"
#guard (v3RegistryCapOpen[0]?.map (·.1)) == some "transferVmDescriptor2R24"

/-- The LIVE transfer cap-open member of the registry IS `transferCapOpenEffV3` (position 42). -/
theorem v3RegistryCapOpen_transferEff :
    (v3RegistryCapOpen[42]?.map (·.2)) = some transferCapOpenEffV3 := rfl

/-- The LIVE attenuate cap-open member of the registry IS `attenuateCapOpenEffV3` (position 43). -/
theorem v3RegistryCapOpen_attenuateEff :
    (v3RegistryCapOpen[43]?.map (·.2)) = some attenuateCapOpenEffV3 := rfl

/-- The delegate fan-out member IS `delegateCapOpenV3` (position 36). -/
theorem v3RegistryCapOpen_delegate :
    (v3RegistryCapOpen[36]?.map (·.2)) = some delegateCapOpenV3 := rfl

/-- The revoke fan-out member IS `revokeCapOpenV3` (position 39). -/
theorem v3RegistryCapOpen_revoke :
    (v3RegistryCapOpen[39]?.map (·.2)) = some revokeCapOpenV3 := rfl

/-! ## §7 — Axiom hygiene. -/

#assert_axioms effCapOpenV3_satisfiedEff
#assert_axioms effCapOpenV3_authorizes
#assert_axioms transferCapOpenEffV3_authorizes
#assert_axioms attenuateCapOpenEffV3_authorizes
#assert_axioms transferCapOpenEffV3_rejects_wrong_facet
#assert_axioms attenuateCapOpenEffV3_rejects_wrong_facet
#assert_axioms introduceCapOpenV3_authorizes
#assert_axioms delegateCapOpenV3_authorizes
#assert_axioms grantCapCapOpenV3_authorizes
#assert_axioms revokeCapOpenV3_authorizes
#assert_axioms refreshDelegationCapOpenV3_authorizes
#assert_axioms revokeCapabilityCapOpenV3_authorizes
#assert_axioms introduceCapOpenV3_rejects_wrong_facet
#assert_axioms delegateCapOpenV3_rejects_wrong_facet
#assert_axioms grantCapCapOpenV3_rejects_wrong_facet
#assert_axioms revokeCapOpenV3_rejects_wrong_facet
#assert_axioms refreshDelegationCapOpenV3_rejects_wrong_facet
#assert_axioms revokeCapabilityCapOpenV3_rejects_wrong_facet
#assert_axioms v3RegistryCapOpen_length
#assert_axioms v3RegistryCapOpen_transferEff
#assert_axioms v3RegistryCapOpen_attenuateEff
#assert_axioms v3RegistryCapOpen_delegate
#assert_axioms v3RegistryCapOpen_revoke

/-! ## §9 — `v3RegistryCapOpenWide`: the WHOLE 45-member emit-source registry made 8-felt-wide.

`EffectVmEmitRotationWide.v3RegistryWide` (§8 there) wraps the 36-member cohort
(`EffectVmEmitRotationV3.v3Registry`) through the proven `wideAppend`. But the DEPLOYED wire registry
the TSV emits from is `v3RegistryCapOpen` (45 members) — the 36 cohort + the 9 cap-open / `-eff` / fee'd
members at positions 36..44. A mixed-width registry is incoherent (the global geometry binds all 45), so
the FAITHFUL state commitment is not complete until ALL 45 emit-source members are uniformly wide.

This section closes that final gap: it appends, onto `v3RegistryWide`, the 9 cap-open members each wrapped
through the SAME proven `wideAppend member bb (bb+51)`. The two faithfulness obligations lift identically —
the `wideAppend_*` keystones are GENERIC over any gated host `h` and any `(bb, ab)`; the 9 cap-open members
are gated hosts (`withSelectorGate sel (effCapOpenV3 base name n)`, or the fee'd `transferFeeV3`) exactly as
the cohort members are, so nothing about the cap-open appendix changes the lift.

ADDITIVE: a NEW def + its fold soundness. The live `v3RegistryCapOpen` / wire / geometry / PI / VK are
UNTOUCHED — the flip (next phase) repoints `v3RegistryCapOpen → v3RegistryCapOpenWide` + the Rust/executor
follow.

### §9.1 — the per-member `bb` table for the 9 (limb base = the underlying v1 FACE `traceWidth`)

Each cap-open member at positions 36..44 is `withSelectorGate sel (effCapOpenV3 base name n)` (36..43) or
the graduated fee'd transfer (44). In BOTH shapes the BEFORE limbs are laid by `rotateV3`/
`rotateV3FrozenAuthority` at the underlying v1 FACE's `traceWidth` (`weldsAt face.traceWidth STATE_BEFORE_BASE`),
and the cap-open appendix (`effCapOpenV3` appends at `base.traceWidth`, well PAST the face width) / the fee
pin (`rotateV3WithFeePin` appends only a `.piBinding`, touching NO limb column) / `graduateV1` chip lanes all
land STRICTLY PAST the limbs. So the limb base `bb` for each cap-open member is its underlying v1 FACE's
`traceWidth` — NOT `base.traceWidth`, NOT `member.traceWidth`. Symbolic (the face `.traceWidth`), so it tracks
any face refactor. `ab = bb + B_SPAN = bb + 51` for all. The base→face map:

  * 36 `delegateCapOpenV3`         = `withSelectorGate (effCapOpenV3 grantCapV3 …)`          → face `attenuateVmDescriptor` (`grantCapV3 = v3Of attenuate`)
  * 37 `introduceCapOpenV3`        = `withSelectorGate (effCapOpenV3 introduceV3 …)`         → face `introduceVmDescriptor`
  * 38 `grantCapCapOpenV3`         = `withSelectorGate (effCapOpenV3 grantCapV3 …)`          → face `attenuateVmDescriptor`
  * 39 `revokeCapOpenV3`           = `withSelectorGate (effCapOpenV3 revokeDelegationV3 …)`  → face `revokeVmDescriptor`        (RevokeDelegation)
  * 40 `refreshDelegationCapOpenV3`= `withSelectorGate (effCapOpenV3 refreshDelegationV3 …)` → face `refreshVmDescriptor`
  * 41 `revokeCapabilityCapOpenV3` = `withSelectorGate (effCapOpenV3 revokeCapabilityBaseV3 …)` → face `revokeCapabilityVmDescriptor`
  * 42 `transferCapOpenEffV3`      = `withSelectorGate (effCapOpenV3 transferV3 …)`          → face `transferVmDescriptor`      (`transferV3 = v3OfFrozen transfer`)
  * 43 `attenuateCapOpenEffV3`     = `withSelectorGate (effCapOpenV3 attenuateV3 …)`         → face `attenuateVmDescriptor`     (`attenuateV3 = v3OfWith attenuate …`)
  * 44 `transferFeeV3`             = `graduateV1 (rotateV3WithFeePin (rotateV3FrozenAuthority transferFee))` → face `transferFeeVmDescriptor`
-/

/-- The per-member BEFORE-limb base `bb` of each of the 9 cap-open / `-eff` / fee'd members
(`v3RegistryCapOpen` positions 36..44), aligned position-for-position with that tail: the underlying v1
FACE descriptor's `traceWidth` (where `rotateV3`/`rotateV3FrozenAuthority` laid the BEFORE limbs, PAST which
the cap-open appendix / fee pin / chip lanes all land). The AFTER base is `bb + 51` (`B_SPAN`). Symbolic. -/
def v3RegistryCapOpenWideBB : List Nat :=
  [ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth      -- 36 delegate  (grantCapV3 = v3Of attenuate)
  , Dregg2.Circuit.Emit.EffectVmEmitIntroduce.introduceVmDescriptor.traceWidth       -- 37 introduce
  , Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth      -- 38 grantCap  (grantCapV3 = v3Of attenuate)
  , Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.revokeVmDescriptor.traceWidth   -- 39 revoke    (RevokeDelegation)
  , Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation.refreshVmDescriptor.traceWidth -- 40 refreshDelegation
  , Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor.traceWidth -- 41 revokeCapability
  , Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth         -- 42 transferEff (transferV3 = v3OfFrozen transfer)
  , Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth      -- 43 attenuateEff(attenuateV3 = v3OfWith attenuate)
  , Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferFeeVmDescriptor.traceWidth ]    -- 44 transferFee

#guard v3RegistryCapOpenWideBB.length == 9

/-! ### §9.2 — `v3RegistryCapOpenWide`: the full 45-member wide registry.

`v3RegistryCapOpenWide` is `v3RegistryWide` (the 36 cohort, already wide) ++ the 9 cap-open tail members,
each wrapped through `wideAppend member bb (bb+51)` with its real per-member `bb` (the face width). A NEW def
— `v3RegistryCapOpen` is UNTOUCHED. The wide carriers/PIs land PAST each member's `traceWidth`/`piCount`
(past the cap-open appendix AND the limbs), so the host's gates and the wide 8-felt binding both hold
(§9.3). The tail is the same zip-and-`wideAppend` shape as §8 — the cap-open members are gated hosts. -/
def v3RegistryCapOpenWide : List (String × EffectVmDescriptor2) :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide
    ++ ((v3RegistryCapOpen.drop 36).zip v3RegistryCapOpenWideBB).map
        (fun (e : (String × EffectVmDescriptor2) × Nat) =>
          (e.1.1, Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend e.1.2 e.2 (e.2 + 51)))

theorem v3RegistryCapOpenWide_length : v3RegistryCapOpenWide.length = 45 := by
  have hcohort : Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide.length = 36 := by decide
  have hdrop : (v3RegistryCapOpen.drop 36).length = 9 := by
    simp [v3RegistryCapOpen, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry]
  have hbb : v3RegistryCapOpenWideBB.length = 9 := by decide
  simp only [v3RegistryCapOpenWide, List.length_append, List.length_map, List.length_zip,
    hcohort, hdrop, hbb, Nat.min_self]

#guard v3RegistryCapOpenWide.length == 45
-- the names are the live cap-open registry's, verbatim (the flip is a NAME-stable repoint).
#guard v3RegistryCapOpenWide.map (·.1) == v3RegistryCapOpen.map (·.1)

/-- Each `v3RegistryCapOpenWide` entry IS a `wideAppend` of a member of the live `v3RegistryCapOpen` at its
real `bb`. The structural witness the fold soundness consumes: a cohort entry's host is a `v3Registry` member
(via the §8 `v3RegistryWide_is_wideAppend`), a tail entry's host is a cap-open member at its face `bb`. In
both cases the host descriptor IS in `v3RegistryCapOpen.map (·.2)`. -/
theorem v3RegistryCapOpenWide_is_wideAppend :
    ∀ (i : Nat) (hi : i < v3RegistryCapOpenWide.length),
      ∃ (h : EffectVmDescriptor2) (bb : Nat),
        h ∈ v3RegistryCapOpen.map (·.2)
        ∧ v3RegistryCapOpenWide[i].2
            = Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend h bb (bb + 51) := by
  intro i hi
  by_cases hlt : i < Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide.length
  · -- cohort half: reuse the §8 structural witness; the host is a `v3Registry` member, which is a
    -- prefix of `v3RegistryCapOpen`, so it is a `v3RegistryCapOpen` member.
    obtain ⟨h, bb, hmem, heq⟩ :=
      Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide_is_wideAppend i hlt
    refine ⟨h, bb, ?_, ?_⟩
    · -- `v3Registry.map (·.2) ⊆ v3RegistryCapOpen.map (·.2)` (the cohort is the prefix).
      have : Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.2)
          <+: v3RegistryCapOpen.map (·.2) := by
        rw [v3RegistryCapOpen, List.map_append]; exact List.prefix_append _ _
      exact this.subset hmem
    · -- the wide entry is the cohort wide entry (the append's left part).
      have hget : v3RegistryCapOpenWide[i] = Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide[i]'hlt := by
        simp only [v3RegistryCapOpenWide]
        rw [List.getElem_append_left hlt]
      rw [hget]; exact heq
  · -- tail half: the cap-open member at index `i - 36`, wide-wrapped at its face `bb`.
    push_neg at hlt
    have hlen36 : Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide.length = 36 := by decide
    have hwidelen : v3RegistryCapOpenWide.length = 45 := v3RegistryCapOpenWide_length
    rw [hwidelen] at hi
    set j := i - 36 with hj
    have hi36 : 36 ≤ i := by rw [hlen36] at hlt; exact hlt
    have hjlt : j < 9 := by omega
    -- the tail list and its `bb` table both have length 9 and are zipped.
    have hdrop : (v3RegistryCapOpen.drop 36).length = 9 := by
      simp [v3RegistryCapOpen, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry]
    have hbblen : v3RegistryCapOpenWideBB.length = 9 := by decide
    have hzlen : ((v3RegistryCapOpen.drop 36).zip v3RegistryCapOpenWideBB).length = 9 := by
      rw [List.length_zip, hdrop, hbblen]; exact Nat.min_self 9
    -- index the host out of the tail.
    have hjdrop : j < (v3RegistryCapOpen.drop 36).length := by rw [hdrop]; exact hjlt
    have hjbb : j < v3RegistryCapOpenWideBB.length := by rw [hbblen]; exact hjlt
    have hjzip : j < ((v3RegistryCapOpen.drop 36).zip v3RegistryCapOpenWideBB).length := by
      rw [hzlen]; exact hjlt
    refine ⟨((v3RegistryCapOpen.drop 36)[j]'hjdrop).2, v3RegistryCapOpenWideBB[j]'hjbb, ?_, ?_⟩
    · -- the dropped member is a member of the full registry.
      have hmem : (v3RegistryCapOpen.drop 36)[j]'hjdrop ∈ v3RegistryCapOpen := by
        have := List.getElem_mem hjdrop
        exact (List.drop_subset 36 v3RegistryCapOpen) this
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    · -- the wide entry is the tail's `j`-th wide-append.
      have hidx : i - Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWide.length = j := by
        rw [hlen36]
      simp only [v3RegistryCapOpenWide]
      rw [List.getElem_append_right (by rw [hlen36]; omega)]
      simp only [hidx, List.getElem_map, List.getElem_zip]

/-! ### §9.3 — `v3RegistryCapOpenWide_sound` / `_binds`: the fold over all 45 members.

The two faithfulness obligations lift member-by-member through the GENERIC `wideAppend` keystones
(`wideAppend_satisfied2_host` / `wideAppend_binds_published`), exactly as §8 lifts them over the cohort — the
9 cap-open members are gated hosts, so the lift is identical (the cap-open appendix is a CONJUNCTION appended
past the host, untouched by the wide block). -/

/-- **`v3RegistryCapOpenWide_sound` — THE GATE-SURVIVAL FOLD over all 45.** Every wide entry preserves its
live `v3RegistryCapOpen` member's gates: a `Satisfied2` witness of the wide entry is a `Satisfied2` of the
underlying live member `h`, so EVERY soundness theorem `h` carries (its disc / perms-vk / grow / record-pin /
cap-open facet gates) holds of the wide witness unchanged. The wide block is a CONJUNCTION appended past the
host. -/
theorem v3RegistryCapOpenWide_sound (hash : List ℤ → ℤ)
    (i : Nat) (hi : i < v3RegistryCapOpenWide.length)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hsat : Satisfied2 hash v3RegistryCapOpenWide[i].2 minit mfin maddrs t) :
    ∃ (h : EffectVmDescriptor2) (bb : Nat),
      h ∈ v3RegistryCapOpen.map (·.2)
      ∧ Satisfied2 hash
          (Dregg2.Circuit.Emit.EffectVmEmitRotationWide.dropLegacyCommitPins1 h bb (bb + 51))
          minit mfin maddrs t := by
  obtain ⟨h, bb, hmem, heq⟩ := v3RegistryCapOpenWide_is_wideAppend i hi
  refine ⟨h, bb, hmem, ?_⟩
  rw [heq] at hsat
  exact Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend_satisfied2_host hash h bb (bb + 51)
    minit mfin maddrs t hsat

open Dregg2.Circuit.Emit.EffectVmEmitRotationR (Poseidon2WideCR Poseidon2Width8 wireCommitR8)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (preLimbsWide)
open Dregg2.Circuit.DescriptorIR2 (ChipTableSoundN VmTrace envAt)

/-- **`v3RegistryCapOpenWide_binds` — THE 8-FELT BINDING FOLD over all 45.** Every wide entry's published
8-felt BEFORE/AFTER commits BIND: two `Satisfied2` witnesses of the SAME wide entry publishing the same 8-felt
BEFORE commit and the same 8-felt AFTER commit agree on the WHOLE before-block 37-limb list + iroot AND the
whole after-block 37-limb list + iroot — the genuine ~124-bit binding via the faithful `wireCommitR8_binds`,
member-by-member over the full 45-member emit-source registry (cohort AND cap-open). -/
theorem v3RegistryCapOpenWide_binds (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW)
    (i : Nat) (hi : i < v3RegistryCapOpenWide.length)
    (h : EffectVmDescriptor2) (bb : Nat)
    (heq : v3RegistryCapOpenWide[i].2
        = Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend h bb (bb + 51))
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash v3RegistryCapOpenWide[i].2 minit mfin maddrs t)
    (hsat' : Satisfied2 hash v3RegistryCapOpenWide[i].2 minit' mfin' maddrs' t')
    (a b : Nat) (ha : a < t.rows.length) (hb : b < t'.rows.length)
    (hfirst : (a == 0) = true) (hfirst' : (b == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t a).pub (h.piCount + m) = (envAt t' b).pub (h.piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub (h.piCount + 8 + m) = (envAt t' l).pub (h.piCount + 8 + m)) :
    (preLimbsWide bb (envAt t a).loc = preLimbsWide bb (envAt t' b).loc
      ∧ (envAt t a).loc (bb + 37) = (envAt t' b).loc (bb + 37))
    ∧ (preLimbsWide (bb + 51) (envAt t k).loc = preLimbsWide (bb + 51) (envAt t' l).loc
      ∧ (envAt t k).loc (bb + 51 + 37) = (envAt t' l).loc (bb + 51 + 37)) := by
  rw [heq] at hsat hsat'
  exact Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend_binds_published
    hash permW hCR hW h bb (bb + 51)
    minit mfin maddrs t minit' mfin' maddrs' t' hchipN hchipN' hsat hsat'
    a b ha hb hfirst hfirst' k l hk hl hlast hlast' hpubBefore hpubAfter

#assert_axioms v3RegistryCapOpenWide_is_wideAppend
#assert_axioms v3RegistryCapOpenWide_sound
#assert_axioms v3RegistryCapOpenWide_binds
#assert_axioms v3RegistryCapOpenWide_length

/-! ### §9.4 — the ANTI-LAUNDERING tooth on a REPRESENTATIVE cap-open member.

The wide binding of a cap-open member (`transferCapOpenEffV3` — `withSelectorGate TRANSFER (effCapOpenV3
transferV3 …)`, a genuinely gated host carrying the cap-open membership appendix) is GENUINELY 8-felt: the
selector gate / cap-open appendix constrain the selector / membership columns, NOT a commit lane, so a
high-limb flip moves the published 8-felt commit (lane0 alone would collapse it). A high-limb flip is bound;
honest recompute is stable; the commit is 8 felts wide. -/
section CapOpenWideAntiLaundering
open Dregg2.Circuit.Emit.EffectVmEmitRotationR (refWide demoPre24)
-- the representative cap-open member IS a `wideAppend` at its face `bb` (position 42 = transferEff).
theorem v3RegistryCapOpenWide_transferEff_is_wideAppend :
    v3RegistryCapOpenWide[42]?.map (·.2)
      = some (Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend transferCapOpenEffV3
          Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth
          (Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth + 51)) := by
  rfl

-- a high-limb (>lane0) flip of the cap-open member's pre-limbs MOVES the published 8-felt commit:
-- the wide binding distinguishes it (a 1-felt lane0 squeeze could NOT).
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- a different iroot ⇒ a different commit (the iroot is bound).
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide demoPre24 8
-- honest recompute is stable.
#guard wireCommitR8 refWide demoPre24 7 == wireCommitR8 refWide demoPre24 7
-- the cap-open member's wide commit is 8 felts wide (NOT a 1-felt lane0 squeeze).
#guard (wireCommitR8 refWide demoPre24 7).length == 8

end CapOpenWideAntiLaundering

end Dregg2.Circuit.Emit.CapOpenEmit
