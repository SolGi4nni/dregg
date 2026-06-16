/-
# Dregg2.Circuit.Emit.CapOpenEmit — the LIVE cap-membership open, emitted into a real descriptor.

`DeployedCapOpen.lean` PROVES the in-circuit cap-tree membership-open as a set of generic
`Lookup` + gate `VmConstraint2`s (`leafLookup` + 16 `nodeLookup` + `dirBoolGate`/`rootPinGate`/
`targetBindGate`/`writeMaskGate`) over an abstract `CapOpenCols` column layout, with the keystone
`capOpen_sound`: a `Satisfied` row yields `MembersAt cap_root leaf ∧ leaf.target = src ∧
confersWriteLeaf leaf`. But nothing LAID THOSE CONSTRAINTS DOWN into a live `EffectVmDescriptor2`:
the proof existed, disconnected from the wire.

This file welds it. It (a) pins `CapOpenCols` to a concrete appendix of trace columns past the
rotated R=24 width (`capOpenCols`, §1), (b) assembles the proven constraints into a constraint list
(`capOpenConstraints`, §2) — `leafLookup` + the 16 `nodeLookup`s as `.lookup`, the four gates as
`.base (.gate …)` — and (c) appends them to the rotated attenuate descriptor (`capOpenAttenuateV3`,
§3), widening the trace by `CAP_OPEN_SPAN` and welding the `capRoot`/`src` columns to the committed
rotated before-block cap-root and the turn's src.

The keystone (§4, `capOpenAttenuateV3_authorizes`): a `Satisfied2` witness of the live descriptor —
against a sound chip table — REBUILDS `DeployedCapOpen.Satisfied`, hence `capOpen_sound`, hence (via
`deployedCapOpen_implies_authorizedB`) the kernel's `authorizedB`. The `&[]` cap-path placeholder is
GONE: the depth-16 fold the descriptor now carries IS the proof.

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

## Mask convention (the NAMED fork — NOT faked here)

`writeMaskGate` pins `leaf.mask_lo == rightsMaskOf(endpoint[read,write]) = 3` (the abstract `Auth`
rights mask). The deployed `cap_root.rs::CapLeaf.mask_lo` is the low-16 of a `cell/facet.rs`
`EffectMask` (effect-KIND bitmap) — a DIFFERENT convention (HORIZONLOG MASK-CONVENTION RECONCILE,
an ember decision). This file emits `writeMaskGate` FAITHFULLY (`mask_lo == 3`): the write leg is
only satisfiable on a leaf whose committed `mask_lo` is literally the rights mask. NO constant is
faked to pretend the two conventions agree; the target-bind + root-pinned membership legs (which are
convention-INDEPENDENT) are the load-bearing authority production this file lands.

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
  (capLeafDigest MembersAt confersWriteLeaf DeployedFaithful
   deployedCapOpen_implies_authorizedB)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (attenuateV3 APPENDIX_SPAN B_CAP_ROOT)
open Dregg2.Authority (Caps Label)

set_option autoImplicit false

/-! ## §1 — the concrete column layout: the cap-open appendix past the rotated R=24 width.

The rotated attenuate trace is `EFFECT_VM_WIDTH + APPENDIX_SPAN = 311` columns wide. The cap-open
appendix starts at `CAP_OPEN_BASE` and carries, in order: 7 leaf-field columns, 1 leaf-digest
column, then for each of `DEPTH = 16` levels a `(sib, dir, node)` triple, then the `capRoot` and
`src` columns. Total `CAP_OPEN_SPAN = 7 + 1 + 16·3 + 2 = 58`. -/

/-- The base column of the cap-open appendix (the first column past the rotated R=24 width). -/
def CAP_OPEN_BASE : Nat := EFFECT_VM_WIDTH + APPENDIX_SPAN

/-- The cap-open appendix width: 7 leaf + 1 digest + 16·(sib,dir,node) + capRoot + src. -/
def CAP_OPEN_SPAN : Nat := 7 + 1 + DEPTH * 3 + 2

/-- The concrete cap-open column layout, pinned to the appendix. Leaf fields 0..6 at
`CAP_OPEN_BASE..+6`; leaf digest at `+7`; level `lvl`'s sibling/direction/node at `+8+3·lvl`,
`+9+3·lvl`, `+10+3·lvl`; cap_root at `+56`; src at `+57`. -/
def capOpenCols : CapOpenCols :=
  { leaf       := fun i => CAP_OPEN_BASE + i.val
  , leafDigest := CAP_OPEN_BASE + 7
  , sib        := fun lvl => CAP_OPEN_BASE + 8 + 3 * lvl
  , dir        := fun lvl => CAP_OPEN_BASE + 9 + 3 * lvl
  , node       := fun lvl => CAP_OPEN_BASE + 10 + 3 * lvl
  , capRoot    := CAP_OPEN_BASE + 8 + 3 * DEPTH       -- = CAP_OPEN_BASE + 56
  , src        := CAP_OPEN_BASE + 8 + 3 * DEPTH + 1 } -- = CAP_OPEN_BASE + 57

/-- The cap-open appendix width is 58. -/
theorem cap_open_span : CAP_OPEN_SPAN = 58 := by decide

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
direction-boolean gates, the root pin, the target binding, the write-mask binding. This is the
set `DeployedCapOpen.Satisfied` enumerates, in wire-emittable form. -/
def capOpenConstraints : List VmConstraint2 :=
  .lookup (leafLookup capOpenCols)
  :: nodeLookups
  ++ dirBoolGates
  ++ [ .base (.gate (rootPinGate capOpenCols))
     , .base (.gate (targetBindGate capOpenCols))
     , .base (.gate (writeMaskGate capOpenCols)) ]

/-- The cap-open constraint count: 1 leaf lookup + 16 node lookups + 16 dir gates + 3 binding
gates = 36. -/
theorem capOpenConstraints_length : capOpenConstraints.length = 36 := by
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
    capOpenAttenuateV3.traceWidth = attenuateV3.traceWidth + 58 := by
  simp [capOpenAttenuateV3, CAP_OPEN_SPAN, DEPTH]

/-- Every cap-open constraint is a constraint of the live descriptor. -/
theorem capOpenConstraints_mem (c : VmConstraint2) (hc : c ∈ capOpenConstraints) :
    c ∈ capOpenAttenuateV3.constraints :=
  List.mem_append_right _ hc

/-! ## §4 — the bridge: a `Satisfied2` witness REBUILDS `DeployedCapOpen.Satisfied`.

The keystone. A `Satisfied2` witness of the live descriptor, on ANY row, satisfies every cap-open
constraint (they are constraints of the descriptor). Reading them back gives exactly the fields of
`DeployedCapOpen.Satisfied`, so `capOpen_sound` fires: the row OPENS the committed cap-tree at a
write-mask leaf whose target is the turn's src. -/

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
    , rootPinned := ?_, targetBound := ?_, writeMasked := ?_ }
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
  · -- write-mask binding
    have hmem : VmConstraint2.base (.gate (writeMaskGate capOpenCols)) ∈ capOpenConstraints := by
      simp [capOpenConstraints]
    have h := hrow _ (capOpenConstraints_mem _ hmem)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **`capOpenAttenuateV3_sound` — the live cap-open is SOUND.** A `Satisfied2` witness of the live
descriptor (against a sound chip table) PRODUCES, on every row, the membership the kernel authority
bridge consumes: `MembersAt cap_root leaf ∧ leaf.target = src ∧ confersWriteLeaf leaf`. The `&[]`
placeholder is discharged — the depth-16 fold the descriptor carries IS the proof. -/
theorem capOpenAttenuateV3_sound {State : Type} (S : CapHashScheme State)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb capOpenAttenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    MembersAt S ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot)
        (leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i))
    ∧ (leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i)).target
        = (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src
    ∧ confersWriteLeaf (leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i)) :=
  capOpen_sound S t.tf capOpenCols _ hChip
    (capOpenAttenuateV3_satisfied S.chipAbsorb minit mfin maddrs t hsat i hi)

/-- **`capOpenAttenuateV3_authorizes` — THE END-TO-END AUTHORITY LEG, LIVE.** Against the deployed
commitment relation, a `Satisfied2` witness of the live descriptor whose opened leaf IS the
faithfulness contract's `(actor ⇒ src)` edge discharges the kernel's `authorizedB` for the turn —
from the IN-CIRCUIT depth-16 binary-Merkle membership proof the descriptor now carries. -/
theorem capOpenAttenuateV3_authorizes {State : Type} (S : CapHashScheme State)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb capOpenAttenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : Caps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src) :
    Dregg2.Exec.authorizedB caps
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpen_authorizes S t.tf capOpenCols _ hChip
    (capOpenAttenuateV3_satisfied S.chipAbsorb minit mfin maddrs t hsat i hi)
    caps leafAt hfaith actor src dst amt hsrc hedge

/-! ## §5 — the wire face: the emitted JSON carries the cap-open constraints.

The Rust registry twin parses `emitVmJson2 capOpenAttenuateV3`. We pin the shape: the descriptor's
trace width is the rotated width + 58, and its constraint list is the attenuate's plus the 36
cap-open constraints. The full byte-golden lands in the Rust differential test (the wire string is
large; `lake`'s `#guard` on the constraint COUNT + width is the Lean-side pin). -/

-- The live descriptor adds exactly the 36 cap-open constraints past the attenuate base.
#guard capOpenAttenuateV3.constraints.length == attenuateV3.constraints.length + 36
-- The width grows by the 58-column cap-open appendix.
#guard capOpenAttenuateV3.traceWidth == attenuateV3.traceWidth + 58
-- The cap-open appendix begins past the rotated R=24 width (311).
#guard CAP_OPEN_BASE == 311
#guard CAP_OPEN_SPAN == 58
-- The five EPOCH tables are inherited unchanged (the cap-open rides the chip + main tables).
#guard capOpenAttenuateV3.tables.length == 5

/-! ## §6 — Axiom hygiene. -/

#assert_axioms capOpenAttenuateV3_satisfied
#assert_axioms capOpenAttenuateV3_sound
#assert_axioms capOpenAttenuateV3_authorizes

end Dregg2.Circuit.Emit.CapOpenEmit
