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

/-- The cap-open appendix width: 7 leaf + 1 digest + 16·(sib,dir,node) + capRoot + src + effBit.
The trailing `effBit` column (residual (a)) carries the turn's ACTUAL effect-kind bit, against which
the general facet gate `facetEffGate` binds the leaf mask (NOT the constant `EFFECT_TRANSFER`). -/
def CAP_OPEN_SPAN : Nat := 7 + 1 + DEPTH * 3 + 3

/-- The concrete cap-open column layout, pinned to the appendix. Leaf fields 0..6 at
`CAP_OPEN_BASE..+6`; leaf digest at `+7`; level `lvl`'s sibling/direction/node at `+8+3·lvl`,
`+9+3·lvl`, `+10+3·lvl`; cap_root at `+56`; src at `+57`; effBit at `+58`. -/
def capOpenCols : CapOpenCols :=
  { leaf       := fun i => CAP_OPEN_BASE + i.val
  , leafDigest := CAP_OPEN_BASE + 7
  , sib        := fun lvl => CAP_OPEN_BASE + 8 + 3 * lvl
  , dir        := fun lvl => CAP_OPEN_BASE + 9 + 3 * lvl
  , node       := fun lvl => CAP_OPEN_BASE + 10 + 3 * lvl
  , capRoot    := CAP_OPEN_BASE + 8 + 3 * DEPTH       -- = CAP_OPEN_BASE + 56
  , src        := CAP_OPEN_BASE + 8 + 3 * DEPTH + 1   -- = CAP_OPEN_BASE + 57
  , effBit     := CAP_OPEN_BASE + 8 + 3 * DEPTH + 2 } -- = CAP_OPEN_BASE + 58

/-- The cap-open appendix width is 59. -/
theorem cap_open_span : CAP_OPEN_SPAN = 59 := by decide

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

/-- **The full cap-open constraint list** — the leaf-digest lookup, the 16 node lookups, the 16
direction-boolean gates, the root pin, the target binding, and the FAITHFUL two-axis bindings: the
transfer-facet gate (`mask_lo = EFFECT_TRANSFER`), the facet-high-zero gate (`mask_hi = 0`), and the
tier gate (`auth_tag = Signature`). This is the set `DeployedCapOpen.Satisfied` enumerates, in
wire-emittable form. -/
def capOpenConstraints : List VmConstraint2 :=
  .lookup (leafLookup capOpenCols)
  :: nodeLookups
  ++ dirBoolGates
  ++ [ .base (.gate (rootPinGate capOpenCols))
     , .base (.gate (targetBindGate capOpenCols))
     , .base (.gate (transferFacetGate capOpenCols))
     , .base (.gate (facetHiGate capOpenCols))
     , .base (.gate (authTagGate capOpenCols))
     , .base (.gate (effBitGate capOpenCols))
     , .base (.gate (facetEffGate capOpenCols)) ]

/-- The cap-open constraint count: 1 leaf lookup + 16 node lookups + 16 dir gates + 7 binding
gates = 40 (the 5 prior + the residual-(a) `effBitGate` + `facetEffGate`). -/
theorem capOpenConstraints_length : capOpenConstraints.length = 40 := by
  simp [capOpenConstraints, nodeLookups, dirBoolGates, DEPTH]

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
    capOpenAttenuateV3.traceWidth = attenuateV3.traceWidth + 59 := by
  simp [capOpenAttenuateV3, CAP_OPEN_SPAN, DEPTH]

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
    , effBitTransfer := ?_, facetEffBound := ?_ }
  · -- leaf lookup
    have h := hrow (.lookup (leafLookup capOpenCols))
      (capOpenConstraints_mem _ (by simp [capOpenConstraints]))
    simpa [VmConstraint2.holdsAt] using h
  · -- node lookups
    intro lvl hlvl
    have hmem : VmConstraint2.lookup (nodeLookup capOpenCols lvl) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt] using h
  · -- direction-boolean gates
    intro lvl hlvl
    have hmem : VmConstraint2.base (.gate (dirBoolGate capOpenCols lvl)) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
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
  · -- general facet binding (mask_lo = effBit) — residual (a)
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
#guard capOpenAttenuateV3.constraints.length == attenuateV3.constraints.length + 40
-- The width grows by the 59-column cap-open appendix (58 prior + 1 effBit column).
#guard capOpenAttenuateV3.traceWidth == attenuateV3.traceWidth + 59
-- The cap-open appendix begins past the rotated width (316 = 187 base + 129 appendix, after the
-- commitments_root flag-day widened APPENDIX_SPAN 125→129).
#guard CAP_OPEN_BASE == 316
#guard CAP_OPEN_SPAN == 59
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
    transferCapOpenV3.traceWidth = transferV3.traceWidth + 59 := by
  simp [transferCapOpenV3, CAP_OPEN_SPAN, DEPTH]

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
    , effBitTransfer := ?_, facetEffBound := ?_ }
  · have h := hrow (.lookup (leafLookup capOpenCols))
      (transferCapOpenV3_constraints_mem _ (by simp [capOpenConstraints]))
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hmem : VmConstraint2.lookup (nodeLookup capOpenCols lvl) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (transferCapOpenV3_constraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hmem : VmConstraint2.base (.gate (dirBoolGate capOpenCols lvl)) ∈ capOpenConstraints := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
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
#guard transferCapOpenV3.constraints.length == transferV3.constraints.length + 40
#guard transferCapOpenV3.traceWidth == transferV3.traceWidth + 59

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
       , ("transferCapOpenVmDescriptor2R24", transferCapOpenV3) ]

/-- The registry-with-cap-open has 38 members (36 cohort + the 2 cap-open authority members). -/
theorem v3RegistryCapOpen_length : v3RegistryCapOpen.length = 38 := by
  simp [v3RegistryCapOpen, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry]

-- The two cap-open authority members are the 37th/38th registry entries (positions 36/37).
#guard v3RegistryCapOpen.length == 38
#guard (v3RegistryCapOpen[36]?.map (·.1)) == some "attenuateCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[37]?.map (·.1)) == some "transferCapOpenVmDescriptor2R24"
-- The 36 cohort members are unchanged at positions 0..35 (the prefix is verbatim `v3Registry`).
#guard (v3RegistryCapOpen[0]?.map (·.1)) == some "transferVmDescriptor2R24"

/-- The attenuate cap-open member of the registry IS `capOpenAttenuateV3` (position 36). -/
theorem v3RegistryCapOpen_capOpen :
    (v3RegistryCapOpen[36]?.map (·.2)) = some capOpenAttenuateV3 := rfl

/-- The transfer cap-open member of the registry IS `transferCapOpenV3` (position 37, residual (b)). -/
theorem v3RegistryCapOpen_transferCapOpen :
    (v3RegistryCapOpen[37]?.map (·.2)) = some transferCapOpenV3 := rfl

/-! ## §7 — Axiom hygiene. -/

#assert_axioms capOpenAttenuateV3_satisfied
#assert_axioms capOpenAttenuateV3_sound
#assert_axioms capOpenAttenuateV3_authorizes
#assert_axioms capOpenAttenuateV3_authorizes_tierGeneral
#assert_axioms transferCapOpenV3_satisfied
#assert_axioms transferCapOpenV3_authorizes
#assert_axioms v3RegistryCapOpen_length
#assert_axioms v3RegistryCapOpen_capOpen
#assert_axioms v3RegistryCapOpen_transferCapOpen

end Dregg2.Circuit.Emit.CapOpenEmit
