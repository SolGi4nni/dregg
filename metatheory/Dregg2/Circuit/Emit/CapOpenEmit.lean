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
rotated R=24 width (`capOpenCols`, §1), (b) assembles the proven constraints into a constraint list
(`capOpenConstraints`, §2) — `leafLookup` + the 16 `nodeLookup`s as `.lookup`, the six gates as
`.base (.gate …)` — and (c) appends them to the rotated attenuate descriptor (`capOpenAttenuateV3`,
§3), widening the trace by `CAP_OPEN_SPAN` and welding the `capRoot`/`src` columns to the committed
rotated before-block cap-root and the turn's src.

The keystone (§4, `capOpenAttenuateV3_authorizes`): a `Satisfied2` witness of the live descriptor —
against a sound chip table — REBUILDS `DeployedCapOpen.Satisfied`, hence `capOpen_sound`, hence (via
`deployedCapOpen_implies_authorizedB`) the kernel's FAITHFUL `authorizedFacetB`. The `&[]` cap-path
placeholder is GONE: the depth-16 fold the descriptor now carries IS the proof.

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
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (attenuateV3 APPENDIX_SPAN B_CAP_ROOT v3Of)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority (AuthProvided FacetCaps authorizedFacetB)

set_option autoImplicit false

/-! ## §1 — the concrete column layout: the cap-open appendix past the rotated R=24 width.

The rotated attenuate trace is `EFFECT_VM_WIDTH + APPENDIX_SPAN = 316` columns wide. The cap-open
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

/-- The concrete cap-open column layout, pinned to the appendix. Leaf fields 0..6 at
`CAP_OPEN_BASE..+6`; leaf digest at `+7`; level `lvl`'s sibling/direction/node at `+8+3·lvl`,
`+9+3·lvl`, `+10+3·lvl`; cap_root at `+56`; src at `+57`; effBit at `+58`; the 24 mask-bit columns at
`+59..+82` (`bit i = CAP_OPEN_BASE + 59 + i`). -/
def capOpenCols : CapOpenCols :=
  { leaf       := fun i => CAP_OPEN_BASE + i.val
  , leafDigest := CAP_OPEN_BASE + 7
  , sib        := fun lvl => CAP_OPEN_BASE + 8 + 3 * lvl
  , dir        := fun lvl => CAP_OPEN_BASE + 9 + 3 * lvl
  , node       := fun lvl => CAP_OPEN_BASE + 10 + 3 * lvl
  , capRoot    := CAP_OPEN_BASE + 8 + 3 * DEPTH       -- = CAP_OPEN_BASE + 56
  , src        := CAP_OPEN_BASE + 8 + 3 * DEPTH + 1   -- = CAP_OPEN_BASE + 57
  , effBit     := CAP_OPEN_BASE + 8 + 3 * DEPTH + 2   -- = CAP_OPEN_BASE + 58
  , bit        := fun i => CAP_OPEN_BASE + 8 + 3 * DEPTH + 3 + i } -- = CAP_OPEN_BASE + 59 + i

/-- The cap-open appendix width is 83 (the 59-col base + 24 mask-bit columns). -/
theorem cap_open_span : CAP_OPEN_SPAN = 91 := by decide

/-! ## §2 — the constraint list: the proven `DeployedCapOpen` constraints, assembled.

`leafLookup` + the 16 `nodeLookup`s ride `.lookup` (the chip-bus lookups the Rust interpreter
realizes); the four gate equations ride `.base (.gate …)` (the transition-builder gates). The list
is EXACTLY the constraints `DeployedCapOpen.Satisfied` quantifies over. -/

/-- The 16 per-level node-absorb chip lookups (`nodeLookup capOpenCols 0..15`). -/
def nodeLookups : List VmConstraint2 :=
  (List.range DEPTH).map (fun lvl => .lookup (nodeLookup capOpenCols lvl))

/-- The 16 per-level direction-boolean gates (`dirBoolGate capOpenCols 0..15`). -/
def dirBoolGates : List VmConstraint2 :=
  (List.range DEPTH).map (fun lvl => .base (.gate (dirBoolGate capOpenCols lvl)))

/-- The `MASK_BITS` per-bit boolean gates for the `mask_lo` decomposition (`maskBitBoolGate
capOpenCols 0..23`) — each `mask_lo` bit column is `0` or `1`. -/
def maskBitGates : List VmConstraint2 :=
  (List.range MASK_BITS).map (fun i => .base (.gate (maskBitBoolGate capOpenCols i)))

/-- **The full cap-open constraint list** — the leaf-digest lookup, the 16 node lookups, the 16
direction-boolean gates, the root pin, the target binding, and the FAITHFUL two-axis bindings: the
transfer-facet gate (`mask_lo = EFFECT_TRANSFER`), the facet-high-zero gate (`mask_hi = 0`), and the
tier gate (`auth_tag = Signature`). This is the set `DeployedCapOpen.Satisfied` enumerates, in
wire-emittable form. -/
def capOpenConstraints : List VmConstraint2 :=
  .lookup (leafLookup capOpenCols)
  :: nodeLookups
  ++ dirBoolGates
  ++ maskBitGates
  ++ [ .base (.gate (rootPinGate capOpenCols))
     , .base (.gate (targetBindGate capOpenCols))
     , .base (.gate (transferFacetGate capOpenCols))
     , .base (.gate (facetHiGate capOpenCols))
     , .base (.gate (authTagGate capOpenCols))
     , .base (.gate (effBitGate capOpenCols))
     , .base (.gate (maskReconGate capOpenCols))
     , .base (.gate (facetEffGate capOpenCols)) ]

/-- The cap-open constraint count: 1 leaf lookup + 16 node lookups + 16 dir gates + 24 mask-bit
gates + 8 binding gates (rootPin, targetBind, transferFacet, facetHi, authTag, effBit, maskRecon,
facetEffGate) = 73 (32 mask-bit gates + 8 bindings). -/
theorem capOpenConstraints_length : capOpenConstraints.length = 73 := by
  simp [capOpenConstraints, nodeLookups, dirBoolGates, maskBitGates, DEPTH, MASK_BITS]

/-! ## §3 — the live descriptor: the rotated attenuate WITH the cap-open appendix.

The descriptor IS `attenuateV3` plus the cap-open constraints, with the trace widened by
`CAP_OPEN_SPAN`. The Rust registry's `attenuateVmDescriptor2R24CapOpen` member carries the
byte-identical `emitVmJson2` of THIS value. -/

/-- **`capOpenAttenuateV3`** — the rotated attenuate descriptor carrying the IN-CIRCUIT cap-open. -/
def capOpenAttenuateV3 : EffectVmDescriptor2 :=
  { attenuateV3 with
    name        := "dregg-effectvm-attenuateA-v1-rot24-v3-capopen"
    traceWidth  := attenuateV3.traceWidth + CAP_OPEN_SPAN
    constraints := attenuateV3.constraints ++ capOpenConstraints }

/-- The live descriptor's trace width is the rotated width plus the cap-open appendix. -/
theorem capOpenAttenuateV3_width :
    capOpenAttenuateV3.traceWidth = attenuateV3.traceWidth + 91 := by
  simp [capOpenAttenuateV3, CAP_OPEN_SPAN, DEPTH, MASK_BITS]

/-- Every cap-open constraint is a constraint of the live descriptor. -/
theorem capOpenConstraints_mem (c : VmConstraint2) (hc : c ∈ capOpenConstraints) :
    c ∈ capOpenAttenuateV3.constraints :=
  List.mem_append_right _ hc

/-! ## §4 — the bridge: a `Satisfied2` witness REBUILDS `DeployedCapOpen.Satisfied`.

The keystone. A `Satisfied2` witness of the live descriptor, on ANY row, satisfies every cap-open
constraint (they are constraints of the descriptor). Reading them back gives exactly the fields of
`DeployedCapOpen.Satisfied`, so `capOpen_sound` fires: the row OPENS the committed cap-tree at a
transfer-conferring leaf (facet permits `EFFECT_TRANSFER`, tier satisfied) whose target is the turn's
src. -/

/-- A `Satisfied2` witness of the live descriptor reconstructs the proven `DeployedCapOpen.Satisfied`
on every row — the in-circuit cap-membership row IS satisfied. -/
theorem capOpenAttenuateV3_satisfied (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hsat : Satisfied2 hash capOpenAttenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    Satisfied hash t.tf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  refine
    { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_
    , rootPinned := ?_, targetBound := ?_
    , facetTransfer := ?_, facetHiZero := ?_, tierTagged := ?_
    , effBitTransfer := ?_, maskBitsBool := ?_, maskRecon := ?_, facetEffBound := ?_ }
  · -- leaf lookup
    have h := hrow (.lookup (leafLookup capOpenCols))
      (capOpenConstraints_mem _ (by simp [capOpenConstraints]))
    simpa [VmConstraint2.holdsAt] using h
  · -- node lookups
    intro lvl hlvl
    have hmem : VmConstraint2.lookup (nodeLookup capOpenCols lvl) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt] using h
  · -- direction-boolean gates
    intro lvl hlvl
    have hmem : VmConstraint2.base (.gate (dirBoolGate capOpenCols lvl)) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- root pin
    have hmem : VmConstraint2.base (.gate (rootPinGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- target binding
    have hmem : VmConstraint2.base (.gate (targetBindGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- transfer-facet binding (mask_lo = EFFECT_TRANSFER)
    have hmem : VmConstraint2.base (.gate (transferFacetGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- facet-high-zero binding (mask_hi = 0)
    have hmem : VmConstraint2.base (.gate (facetHiGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- tier binding (auth_tag = Signature)
    have hmem : VmConstraint2.base (.gate (authTagGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- effect-bit binding (effBit = EFFECT_TRANSFER) — residual (a)
    have hmem : VmConstraint2.base (.gate (effBitGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- mask-bit booleanity gates — residual (a) GENUINE MEMBERSHIP
    intro j hj
    have hmem : VmConstraint2.base (.gate (maskBitBoolGate capOpenCols j)) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- mask recomposition — residual (a) GENUINE MEMBERSHIP
    have hmem : VmConstraint2.base (.gate (maskReconGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · -- selected-bit gate (genuine submask: transfer bit 1 set) — residual (a)
    have hmem : VmConstraint2.base (.gate (facetEffGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **`capOpenAttenuateV3_sound` — the live cap-open is SOUND.** A `Satisfied2` witness of the live
descriptor (against a sound chip table) PRODUCES, on every row, the membership the kernel authority
bridge consumes: `MembersAt cap_root leaf ∧ leaf.target = src ∧ confersTransferLeaf vkOfTag .signature leaf`. The `&[]`
placeholder is discharged — the depth-16 fold the descriptor carries IS the proof. -/
theorem capOpenAttenuateV3_sound {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb capOpenAttenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    MembersAt S ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot)
        (leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i))
    ∧ (leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i)).target
        = (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src
    ∧ confersTransferLeaf vkOfTag .signature
        (leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i)) :=
  capOpen_sound S t.tf capOpenCols _ vkOfTag hChip
    (capOpenAttenuateV3_satisfied S.chipAbsorb minit mfin maddrs t hsat i hi)

/-- **`capOpenAttenuateV3_authorizes` — THE END-TO-END AUTHORITY LEG, LIVE.** Against the deployed
commitment relation, a `Satisfied2` witness of the live descriptor whose opened leaf IS the
faithfulness contract's `(actor ⇒ src)` edge discharges the kernel's `authorizedFacetB` for the turn —
from the IN-CIRCUIT depth-16 binary-Merkle membership proof the descriptor now carries. -/
theorem capOpenAttenuateV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb capOpenAttenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag .signature caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src) :
    authorizedFacetB caps .signature
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpen_authorizes S t.tf capOpenCols _ vkOfTag hChip
    (capOpenAttenuateV3_satisfied S.chipAbsorb minit mfin maddrs t hsat i hi)
    caps leafAt hfaith actor src dst amt hsrc hedge

/-- **`capOpenAttenuateV3_authorizes_tierGeneral` (F6) — THE LIVE AUTHORITY LEG, GENERAL TIER.** The
generalization of `capOpenAttenuateV3_authorizes` from the pinned `.signature` to ANY `provided` auth
that satisfies the tier DECODED off the committed leaf (`tierOfTag vkOfTag leaf.auth_tag`). A
`Satisfied2` witness of the live cap-open descriptor whose opened leaf IS the faithfulness contract's
`(actor ⇒ src)` edge discharges `authorizedFacetB caps provided turn` for the GENUINE committed tier —
the §10 tier residual closed end-to-end on the live wire. -/
theorem capOpenAttenuateV3_authorizes_tierGeneral {State : Type} (S : CapHashScheme State)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb capOpenAttenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag provided caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (Dregg2.Circuit.DeployedCapTree.CapHashScheme.tierOfTag vkOfTag
        (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpen_authorizes_tierGeneral S t.tf capOpenCols _ vkOfTag provided hChip
    (capOpenAttenuateV3_satisfied S.chipAbsorb minit mfin maddrs t hsat i hi)
    caps leafAt hfaith actor src dst amt hsrc hedge htier

/-! ## §5 — the wire face: the emitted JSON carries the cap-open constraints.

The Rust registry twin parses `emitVmJson2 capOpenAttenuateV3`. We pin the shape: the descriptor's
trace width is the rotated width + 59, and its constraint list is the attenuate's plus the 40
cap-open constraints (the 38 prior + the residual-(a) `effBitGate` + `facetEffGate`). The full
byte-golden lands in the Rust differential test (the wire string is large; `lake`'s `#guard` on the
constraint COUNT + width is the Lean-side pin). -/

-- The live descriptor adds exactly the 40 cap-open constraints past the attenuate base.
#guard capOpenAttenuateV3.constraints.length == attenuateV3.constraints.length + 73
-- The width grows by the 59-column cap-open appendix (58 prior + 1 effBit column).
#guard capOpenAttenuateV3.traceWidth == attenuateV3.traceWidth + 91
-- The cap-open appendix begins past the rotated width (316 = 187 base + 129 appendix, after the
-- commitments_root flag-day widened APPENDIX_SPAN 125→129).
#guard CAP_OPEN_BASE == 316
#guard CAP_OPEN_SPAN == 91
-- The five EPOCH tables are inherited unchanged (the cap-open rides the chip + main tables).
#guard capOpenAttenuateV3.tables.length == 5

/-! ## §5.T — residual (b): the TRANSFER-base cap-open descriptor (`transferCapOpenV3`).

`capOpenAttenuateV3` is the ATTENUATE base + the cap-open appendix; cross-vat authority for OTHER
effects had no cap-open base. `transferCapOpenV3` is the TRANSFER base + the SAME cap-open appendix:
the in-circuit depth-16 cap-membership open laid over the rotated transfer descriptor, so a cross-vat
Transfer-via-granted-cap (`actor ≠ src`, authority from a held transfer cap) routes a cap-open. The
appendix is base-agnostic (`CAP_OPEN_BASE = EFFECT_VM_WIDTH + APPENDIX_SPAN`, the SAME rotated width for
EVERY cohort member — `v3Registry`'s width invariant), so `capOpenCols`/`capOpenConstraints` apply
verbatim. The satisfied/sound/authorizes proofs are the attenuate ones with `transferV3` in place of
`attenuateV3` — the bridge is identical (the appendix constraints don't read the base). -/

/-- The rotated TRANSFER cohort descriptor (`v3Of` of the transfer v1 face). Same width invariant as
`attenuateV3` (`EFFECT_VM_WIDTH + APPENDIX_SPAN`), so the cap-open appendix at `CAP_OPEN_BASE` applies. -/
def transferV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor

/-- **`transferCapOpenV3`** — the rotated TRANSFER descriptor carrying the IN-CIRCUIT cap-open (the
cross-vat Transfer-via-granted-cap authority leg). Transfer base + the cap-open appendix; widened by
`CAP_OPEN_SPAN`, the cap-open constraints appended. -/
def transferCapOpenV3 : EffectVmDescriptor2 :=
  { transferV3 with
    name        := "dregg-effectvm-transfer-v1-rot24-v3-capopen"
    traceWidth  := transferV3.traceWidth + CAP_OPEN_SPAN
    constraints := transferV3.constraints ++ capOpenConstraints }

/-- The transfer cap-open descriptor's trace width is the rotated transfer width + the 59-col appendix. -/
theorem transferCapOpenV3_width :
    transferCapOpenV3.traceWidth = transferV3.traceWidth + 91 := by
  simp [transferCapOpenV3, CAP_OPEN_SPAN, DEPTH, MASK_BITS]

/-- Every cap-open constraint is a constraint of the transfer cap-open descriptor. -/
theorem transferCapOpenV3_constraints_mem (c : VmConstraint2) (hc : c ∈ capOpenConstraints) :
    c ∈ transferCapOpenV3.constraints :=
  List.mem_append_right _ hc

/-- **`transferCapOpenV3_satisfied`** — a `Satisfied2` witness of the transfer cap-open descriptor
rebuilds `DeployedCapOpen.Satisfied` on every row (the appendix constraints are satisfied regardless of
the base). Byte-for-byte the `capOpenAttenuateV3_satisfied` proof with the transfer-base membership. -/
theorem transferCapOpenV3_satisfied (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hsat : Satisfied2 hash transferCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    Satisfied hash t.tf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  refine
    { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_
    , rootPinned := ?_, targetBound := ?_
    , facetTransfer := ?_, facetHiZero := ?_, tierTagged := ?_
    , effBitTransfer := ?_, maskBitsBool := ?_, maskRecon := ?_, facetEffBound := ?_ }
  · have h := hrow (.lookup (leafLookup capOpenCols))
      (transferCapOpenV3_constraints_mem _ (by simp [capOpenConstraints]))
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hmem : VmConstraint2.lookup (nodeLookup capOpenCols lvl) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hmem : VmConstraint2.base (.gate (dirBoolGate capOpenCols lvl)) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (rootPinGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (targetBindGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (transferFacetGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (facetHiGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (authTagGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (effBitGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · intro j hj
    have hmem : VmConstraint2.base (.gate (maskBitBoolGate capOpenCols j)) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (maskReconGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hmem : VmConstraint2.base (.gate (facetEffGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **`transferCapOpenV3_authorizes` — THE CROSS-VAT TRANSFER AUTHORITY LEG, LIVE.** A `Satisfied2`
witness of the transfer cap-open descriptor whose opened leaf IS the faithfulness contract's
`(actor ⇒ src)` edge discharges the kernel's `authorizedFacetB` for the transfer turn — from the
in-circuit depth-16 cap-membership open the transfer descriptor now carries. The same end-to-end leg as
`capOpenAttenuateV3_authorizes`, over the TRANSFER base (the cross-vat Transfer-via-granted-cap). -/
theorem transferCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb transferCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag .signature caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src) :
    authorizedFacetB caps .signature
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpen_authorizes S t.tf capOpenCols _ vkOfTag hChip
    (transferCapOpenV3_satisfied S.chipAbsorb minit mfin maddrs t hsat i hi)
    caps leafAt hfaith actor src dst amt hsrc hedge

-- The transfer cap-open descriptor shares the appendix shape: +40 constraints, +59 cols.
#guard transferCapOpenV3.constraints.length == transferV3.constraints.length + 73
#guard transferCapOpenV3.traceWidth == transferV3.traceWidth + 91

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
def capOpenConstraintsEff (n : Nat) : List VmConstraint2 :=
  .lookup (leafLookup capOpenCols)
  :: nodeLookups
  ++ dirBoolGates
  ++ maskBitGates
  ++ [ .base (.gate (rootPinGate capOpenCols))
     , .base (.gate (targetBindGate capOpenCols))
     , .base (.gate (effBitGateFor capOpenCols ((1 <<< n : Nat) : ℤ)))
     , .base (.gate (maskReconGate capOpenCols))
     , .base (.gate (selectedBitGate capOpenCols n)) ]

/-- The effect-general constraint count is 1 leaf + 16 node + 16 dir + 32 mask-bit + 5 binding gates
(rootPin, targetBind, effBitGateFor, maskRecon, selectedBit) = 70. (NO `facetHiGate` — the FULL mask is
decomposed, so a broad `EFFECT_ALL` cap with `mask_hi ≠ 0` is admitted.) -/
theorem capOpenConstraintsEff_length (n : Nat) : (capOpenConstraintsEff n).length = 70 := by
  simp [capOpenConstraintsEff, nodeLookups, dirBoolGates, maskBitGates, DEPTH, MASK_BITS]

/-- **`effCapOpenV3 base name n`** — the GENERIC per-effect cap-open descriptor: an effect's rotated base
descriptor `base` (a `v3Of …` member, same `EFFECT_VM_WIDTH + APPENDIX_SPAN` width) widened by the cap-open
appendix at `CAP_OPEN_BASE`, carrying `capOpenConstraintsEff n` (THIS effect's bit). Every fan-out effect is
`effCapOpenV3 <effect>V3 "dregg-…-capopen" n`. -/
def effCapOpenV3 (base : EffectVmDescriptor2) (name : String) (n : Nat) : EffectVmDescriptor2 :=
  { base with
    name        := name
    traceWidth  := base.traceWidth + CAP_OPEN_SPAN
    constraints := base.constraints ++ capOpenConstraintsEff n }

/-- Every effect-general cap-open constraint is a constraint of the descriptor. -/
theorem effCapOpenV3_constraints_mem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ capOpenConstraintsEff n) :
    c ∈ (effCapOpenV3 base name n).constraints :=
  List.mem_append_right _ hc

/-- **`effCapOpenV3_satisfiedEff`** — a `Satisfied2` witness of `effCapOpenV3 base name n` rebuilds
`DeployedCapOpen.SatisfiedEff … n` on every row (the appendix constraints are satisfied regardless of the
base — they read no base column). The fan-out analog of `transferCapOpenV3_satisfied`. -/
theorem effCapOpenV3_satisfiedEff (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    SatisfiedEff hash t.tf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) n := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effCapOpenV3_constraints_mem base name n
  refine
    { core := ?_, targetBound := ?_, effBitPinned := ?_
    , maskBitsBool := ?_, maskRecon := ?_, facetEffBound := ?_ }
  · refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
    · have hin : VmConstraint2.lookup (leafLookup capOpenCols) ∈ capOpenConstraintsEff n := by
        simp [capOpenConstraintsEff]
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt] using h
    · intro lvl hlvl
      have hin : VmConstraint2.lookup (nodeLookup capOpenCols lvl) ∈ capOpenConstraintsEff n := by
        refine List.mem_cons_of_mem _ ?_
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
        exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt] using h
    · intro lvl hlvl
      have hin : VmConstraint2.base (.gate (dirBoolGate capOpenCols lvl)) ∈ capOpenConstraintsEff n := by
        refine List.mem_cons_of_mem _ ?_
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
        exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
    · have hin : VmConstraint2.base (.gate (rootPinGate capOpenCols)) ∈ capOpenConstraintsEff n := by
        simp [capOpenConstraintsEff]
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (targetBindGate capOpenCols)) ∈ capOpenConstraintsEff n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (effBitGateFor capOpenCols ((1 <<< n : Nat) : ℤ)))
        ∈ capOpenConstraintsEff n := by simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · intro j hj
    have hin : VmConstraint2.base (.gate (maskBitBoolGate capOpenCols j)) ∈ capOpenConstraintsEff n := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (maskReconGate capOpenCols)) ∈ capOpenConstraintsEff n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (selectedBitGate capOpenCols n)) ∈ capOpenConstraintsEff n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

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
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpenEff_authorizes S t.tf capOpenCols _ n hn vkOfTag provided hChip
    (effCapOpenV3_satisfiedEff base name n S.chipAbsorb minit mfin maddrs t hsat i hi)
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
  effCapOpenV3 grantCapV3 "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen" EFF_DELEGATION_OPS
/-- **`introduceCapOpenV3`** — introduce-via-cap; the cap must permit `EFFECT_INTRODUCE` (`1 <<< 13`). -/
def introduceCapOpenV3 : EffectVmDescriptor2 :=
  effCapOpenV3 introduceV3 "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE
/-- **`grantCapCapOpenV3`** — grantCap-via-cap; the cap must permit `EFFECT_GRANT_CAPABILITY` (`1 <<< 2`). -/
def grantCapCapOpenV3 : EffectVmDescriptor2 :=
  effCapOpenV3 grantCapV3 "dregg-effectvm-grantCap-v1-rot24-v3-capopen" EFF_GRANT_CAPABILITY
/-- **`revokeCapOpenV3`** — revoke(Delegation)-via-cap; the cap must permit `EFFECT_DELEGATION_OPS`. -/
def revokeCapOpenV3 : EffectVmDescriptor2 :=
  effCapOpenV3 revokeDelegationV3 "dregg-effectvm-revoke-v1-rot24-v3-capopen" EFF_DELEGATION_OPS
/-- **`refreshDelegationCapOpenV3`** — refreshDelegation-via-cap; cap must permit `EFFECT_DELEGATION_OPS`. -/
def refreshDelegationCapOpenV3 : EffectVmDescriptor2 :=
  effCapOpenV3 refreshDelegationV3 "dregg-effectvm-refresh-v1-rot24-v3-capopen" EFF_DELEGATION_OPS
/-- **`revokeCapabilityCapOpenV3`** — revokeCapability-via-cap; cap must permit `EFFECT_REVOKE_CAPABILITY`. -/
def revokeCapabilityCapOpenV3 : EffectVmDescriptor2 :=
  effCapOpenV3 revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY

/-- **`transferCapOpenEffV3`** (residual (a) — THE LIVE transfer cap-open) — the transfer base + the
effect-GENERAL appendix at `EFF_TRANSFER` (bit 1). Unlike the Signature-pinned `transferCapOpenV3` (kept
for the apex/refinement proofs), this carries `capOpenConstraintsEff 1`: the genuine SUBMASK facet gate
(a BROAD honest transfer cap `mask_lo = 0xFFFF` PASSES — bit 1 set) and the DECODED tier (any committed
`auth_tag`, not pinned Signature). This is the descriptor the live `transferCapOpenVmDescriptor2R24`
routing proves through, so an honest transfer cap — broad mask, None/Signature tier — PROVES. -/
def transferCapOpenEffV3 : EffectVmDescriptor2 :=
  effCapOpenV3 transferV3 "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER

/-- **`attenuateCapOpenEffV3`** (residual (a) — THE LIVE attenuate cap-open) — the attenuate base + the
effect-GENERAL appendix at `EFF_TRANSFER` (bit 1; the attenuate cap-open's leaf must permit
`EFFECT_TRANSFER`, mirroring the deployed `attenuateCapOpenVmDescriptor2R24` routing). Genuine submask
facet + decoded tier, so an honest broad/None-tier cap PROVES. The Signature-pinned `capOpenAttenuateV3`
is kept for the apex/refinement proofs. -/
def attenuateCapOpenEffV3 : EffectVmDescriptor2 :=
  effCapOpenV3 attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER

-- The live transfer/attenuate effect-general descriptors share the appendix: +63 constraints, +83 cols.
#guard transferCapOpenEffV3.constraints.length == transferV3.constraints.length + 70
#guard attenuateCapOpenEffV3.constraints.length == attenuateV3.constraints.length + 70
#guard transferCapOpenEffV3.traceWidth == transferV3.traceWidth + 91
#guard attenuateCapOpenEffV3.traceWidth == attenuateV3.traceWidth + 91

-- Each fan-out descriptor adds the 38-constraint effect-general appendix + 59 cols past its base.
#guard delegateCapOpenV3.constraints.length == grantCapV3.constraints.length + 70
#guard introduceCapOpenV3.constraints.length == introduceV3.constraints.length + 70
#guard grantCapCapOpenV3.constraints.length == grantCapV3.constraints.length + 70
#guard revokeCapOpenV3.constraints.length == revokeDelegationV3.constraints.length + 70
#guard refreshDelegationCapOpenV3.constraints.length == refreshDelegationV3.constraints.length + 70
#guard revokeCapabilityCapOpenV3.constraints.length == revokeCapabilityBaseV3.constraints.length + 70
#guard delegateCapOpenV3.traceWidth == grantCapV3.traceWidth + 91
#guard introduceCapOpenV3.traceWidth == introduceV3.traceWidth + 91
#guard grantCapCapOpenV3.traceWidth == grantCapV3.traceWidth + 91
#guard revokeCapOpenV3.traceWidth == revokeDelegationV3.traceWidth + 91
#guard refreshDelegationCapOpenV3.traceWidth == refreshDelegationV3.traceWidth + 91
#guard revokeCapabilityCapOpenV3.traceWidth == revokeCapabilityBaseV3.traceWidth + 91

end FanoutDescriptors

/-! ## §6 — the registry WITH the cap-open: the 37th member (F5 — `Rfix` ranges over the
authority descriptor).

`EffectVmEmitRotationV3.v3Registry` is the 36-member cohort; it CANNOT itself name the cap-open
(`CapOpenEmit` imports `EffectVmEmitRotationV3`, so the dependency runs this way). The deployed wire
registry (`V3_STAGED_REGISTRY_TSV`) carries 37 lines — the 36 cohort members + the cap-open as the
37th (`EmitRotationV3.lean` emits it). `v3RegistryCapOpen` is the Lean twin of that 37-line registry:
the cohort with `capOpenAttenuateV3` appended as the authority member. The soundness apex's `Rfix` is
re-keyed over THIS list, so `registryCommit Rfix` ranges over the cap-open descriptor — the one
in-circuit authority gadget is now inside the registry the apex's `StarkSound` quantifies over (F5
CLOSED). -/

/-- **`v3RegistryCapOpen`** — the 38-member deployed registry: the 36 cohort members
(`EffectVmEmitRotationV3.v3Registry`) plus `capOpenAttenuateV3` (the attenuate authority member,
position 36) and `transferCapOpenV3` (the cross-vat Transfer-via-cap authority member, position 37 —
residual (b)). The Lean twin of the staged registry TSV; the soundness apex's `Rfix` re-keys over it
(so BOTH cap-open authority descriptors are in the registry `registryCommit Rfix` commits). -/
def v3RegistryCapOpen : List (String × EffectVmDescriptor2) :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry
    ++ [ ("attenuateCapOpenVmDescriptor2R24", capOpenAttenuateV3)
       , ("transferCapOpenVmDescriptor2R24", transferCapOpenV3)
       -- THE FAN-OUT (residual (a) closed for these 6): each carries the effect-GENERAL appendix
       -- (`capOpenConstraintsEff n`) binding the cap to THAT effect-kind bit, not transfer.
       , ("delegateCapOpenVmDescriptor2R24", delegateCapOpenV3)
       , ("introduceCapOpenVmDescriptor2R24", introduceCapOpenV3)
       , ("grantCapCapOpenVmDescriptor2R24", grantCapCapOpenV3)
       , ("revokeCapOpenVmDescriptor2R24", revokeCapOpenV3)
       , ("refreshDelegationCapOpenVmDescriptor2R24", refreshDelegationCapOpenV3)
       , ("revokeCapabilityCapOpenVmDescriptor2R24", revokeCapabilityCapOpenV3)
       -- residual (a) — THE LIVE transfer/attenuate cap-open members (genuine submask facet +
       -- DECODED tier). The Signature-pinned `…CapOpenVmDescriptor2R24` at positions 36/37 are kept
       -- for the apex/refinement proofs; the live prover routes these `…-eff` descriptors so an
       -- honest broad/None-tier cap PROVES.
       , ("transferCapOpenEffVmDescriptor2R24", transferCapOpenEffV3)
       , ("attenuateCapOpenEffVmDescriptor2R24", attenuateCapOpenEffV3) ]

/-- The registry-with-cap-open has 46 members (36 cohort + 2 pinned transfer/attenuate + 6 fan-out +
2 live `-eff` transfer/attenuate). -/
theorem v3RegistryCapOpen_length : v3RegistryCapOpen.length = 46 := by
  simp [v3RegistryCapOpen, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry]

-- The cap-open authority members are positions 36..45; the 36 cohort members are unchanged at 0..35.
#guard v3RegistryCapOpen.length == 46
#guard (v3RegistryCapOpen[36]?.map (·.1)) == some "attenuateCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[37]?.map (·.1)) == some "transferCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[38]?.map (·.1)) == some "delegateCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[39]?.map (·.1)) == some "introduceCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[40]?.map (·.1)) == some "grantCapCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[41]?.map (·.1)) == some "revokeCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[42]?.map (·.1)) == some "refreshDelegationCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[43]?.map (·.1)) == some "revokeCapabilityCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[44]?.map (·.1)) == some "transferCapOpenEffVmDescriptor2R24"
#guard (v3RegistryCapOpen[45]?.map (·.1)) == some "attenuateCapOpenEffVmDescriptor2R24"
#guard (v3RegistryCapOpen[0]?.map (·.1)) == some "transferVmDescriptor2R24"

/-- The attenuate cap-open member of the registry IS `capOpenAttenuateV3` (position 36). -/
theorem v3RegistryCapOpen_capOpen :
    (v3RegistryCapOpen[36]?.map (·.2)) = some capOpenAttenuateV3 := rfl

/-- The transfer cap-open member of the registry IS `transferCapOpenV3` (position 37, residual (b)). -/
theorem v3RegistryCapOpen_transferCapOpen :
    (v3RegistryCapOpen[37]?.map (·.2)) = some transferCapOpenV3 := rfl

/-- The delegate fan-out member IS `delegateCapOpenV3` (position 38). -/
theorem v3RegistryCapOpen_delegate :
    (v3RegistryCapOpen[38]?.map (·.2)) = some delegateCapOpenV3 := rfl

/-- The revoke fan-out member IS `revokeCapOpenV3` (position 41). -/
theorem v3RegistryCapOpen_revoke :
    (v3RegistryCapOpen[41]?.map (·.2)) = some revokeCapOpenV3 := rfl

/-! ## §7 — Axiom hygiene. -/

#assert_axioms capOpenAttenuateV3_satisfied
#assert_axioms capOpenAttenuateV3_sound
#assert_axioms capOpenAttenuateV3_authorizes
#assert_axioms capOpenAttenuateV3_authorizes_tierGeneral
#assert_axioms transferCapOpenV3_satisfied
#assert_axioms transferCapOpenV3_authorizes
#assert_axioms effCapOpenV3_satisfiedEff
#assert_axioms effCapOpenV3_authorizes
#assert_axioms v3RegistryCapOpen_length
#assert_axioms v3RegistryCapOpen_capOpen
#assert_axioms v3RegistryCapOpen_transferCapOpen
#assert_axioms v3RegistryCapOpen_delegate
#assert_axioms v3RegistryCapOpen_revoke

end Dregg2.Circuit.Emit.CapOpenEmit
