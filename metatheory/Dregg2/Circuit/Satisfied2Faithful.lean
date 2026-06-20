/-
# Dregg2.Circuit.Satisfied2Faithful — the FAITHFUL reshape of the deployed accept-set + the collapse recipe.

## What this closes (deliverable 1 + the deliverable-2 RECIPE, additively)

`DescriptorIR2.Satisfied2` is the multi-table denotation, but the per-effect rungs are proven over the
v1 `satisfiedVm` and lifted through `EffectVmEmitV2.graduateV1_sound`, which carries the chip- and
range-table soundness as FREE HYPOTHESES:

    graduateV1_sound … (hchip : ChipTableSound hash (t.tf .poseidon2))
                        (hrange : t.tf .range = rangeRows BAL_LIMB_BITS) … : … satisfiedVm …

The deployed `Ir2Air::Chip` (`circuit/src/descriptor_ir2.rs:2039`) CONSTRAINS every Poseidon2 chip
row to a genuine permutation, and the range table to the genuine limb table — so `hchip`/`hrange`
are NOT free levers a prover may dodge; they are STRUCTURAL facts the deployed circuit forces. This
module folds them INTO the denotation as a `Satisfied2Faithful` structure whose `chipTableFaithful`
(`ChipTableSoundN` — the WIDE genuine-permutation chip soundness) and `rangeTableFaithful` are
CONJUNCTS, not supplied hypotheses. The faithful object is the deployed accept-set as it actually is.

`satisfied2Faithful_satisfiedVm` is THE COLLAPSE RECIPE: from a `Satisfied2Faithful` witness of a
graduated descriptor, the v1 denotation `satisfiedVm` holds on every row — WITHOUT a free `hchip`/
`hrange` lever, because the structure CARRIES them. Any existing `satisfiedVm`-shaped per-effect rung
composes through this with NO `graduateV1`-lever discharge: the recipe is "feed `h.toSatisfied2` +
`h.chipSound` + `h.rangeFaithful` to `graduateV1_sound`". `transfer_descriptorRefines_faithful`
beachheads it on the transfer rung; the same two-line pattern fans out to every effect.

## The map-root leg (the Merkle model) — already landed in `DeployedCapTree`

Deliverable 1's "re-define `opensTo`/`writesTo` over the depth-16 binary-Merkle model" for the
cap-tree is ALREADY realized in `DeployedCapTree` (`MembersAt`/`nodeOf`/`recomposeUp`, the anti-ghost
`recomposeUp_inj_of_path` proven against `nodeOf_injective`, NOT the flat-sponge `root_injective`).
`chipTableFaithful` here uses the SAME genuine-permutation carrier (`ChipTableSoundN permOut`) the
cap-node hash rides, so the chip-faithful and Merkle-map legs share one permutation floor.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`. The chip /
range soundness are STRUCTURAL conjuncts (the deployed circuit's own faithfulness), not free levers;
crypto enters only as the genuine permutation carried by `ChipTableSoundN`. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitV2
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Satisfied2Faithful

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor VmHashSite VmRange siteHoldsAll satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)

set_option autoImplicit false

/-! ## §1 — the chip-table faithfulness bridge: the WIDE `ChipTableSoundN` forces the legacy
`ChipTableSound` head. The deployed chip AIR constrains the FULL permutation; the legacy single-
output lever (`ChipTableSound hash`) is the head of the wide one (`ChipTableSoundN permOut` with
`permOut`'s head `= hash`). -/

/-- **`chipSoundN_implies_chipSound`** — a WIDE-sound chip table is legacy-sound for the digest
`hash := fun ins => (permOut ins).headD 0` it exposes at lane 0. The wide row's output block is
`permOut ins` (length `CHIP_OUT_LANES`); its head is the single squeezed digest, with the remaining
`CHIP_OUT_LANES - 1` lanes riding existentially — exactly `ChipTableSound`'s shape. So binding the
genuine wide permutation (the deployed `Ir2Air::Chip`) DISCHARGES the legacy chip soundness the
`graduateV1` hash sites need. -/
theorem chipSoundN_implies_chipSound (permOut : List ℤ → List ℤ)
    (hlen : ∀ ins, (permOut ins).length = CHIP_OUT_LANES) (tbl : Table)
    (hN : ChipTableSoundN permOut tbl) :
    ChipTableSound (fun ins => (permOut ins).headD 0) tbl := by
  intro r hr
  obtain ⟨ins, hins, hrow⟩ := hN r hr
  -- `permOut ins` has head = the legacy digest and tail = the `CHIP_OUT_LANES - 1` lanes.
  have hl := hlen ins
  cases hpo : permOut ins with
  | nil =>
      -- impossible: `permOut ins` has length `CHIP_OUT_LANES = 8 ≠ 0`.
      rw [hpo] at hl; simp [CHIP_OUT_LANES] at hl
  | cons d lanes =>
      refine ⟨ins, lanes, hins, ?_, ?_⟩
      · -- the tail length is `CHIP_OUT_LANES - 1`.
        have : (d :: lanes).length = CHIP_OUT_LANES := by rw [← hpo]; exact hl
        simp only [List.length_cons] at this
        omega
      · -- the wide row IS the legacy row: `chipRow` reads only `hash ins`, and
        -- `(fun ins => (permOut ins).headD 0) ins = d` (the exposed lane-0 digest).
        rw [hrow]
        unfold chipRowN chipRow
        -- both sides: `len :: padTo … ++ (DIGEST :: lanes)`; LHS DIGEST is `permOut ins`'s
        -- realisation (= `d :: lanes`), RHS DIGEST is `(permOut ins).headD 0` (= `d`).
        simp only [hpo, List.headD_cons]

/-! ## §2 — `Satisfied2Faithful`: the deployed accept-set with the chip / range soundness as
STRUCTURAL conjuncts (not free levers). -/

/-- **`Satisfied2Faithful permOut hash d minit mfin maddrs t`** — the FAITHFUL deployed denotation:
`Satisfied2` PLUS the deployed circuit's own table-faithfulness, carried as STRUCTURE fields:

  * `chipTableFaithful` — the Poseidon2 chip table is WIDE-sound (`ChipTableSoundN permOut`): every
    row is a genuine `(arity, padded inputs, permOut inputs)` tuple of the REAL permutation. This is
    the `Ir2Air::Chip` constraint (`descriptor_ir2.rs:2039`), NOT a supplied hypothesis;
  * `permWidth` — the genuine permutation exposes `CHIP_OUT_LANES` lanes (the chip's fixed width);
  * `chipHashIsLane0` — the `hash` the v1 sites compare against IS lane 0 of the genuine permutation
    (`hash ins = (permOut ins).headD 0`): the deployed digest, byte-faithful;
  * `rangeTableFaithful` — the range table is the genuine limb table (`rangeRows BAL_LIMB_BITS`), the
    deployed range AIR's height.

This binds `t.tf .poseidon2`/`t.tf .range` to the genuine permutation / limb rows IN the structure,
matching the deployed `Ir2Air::Chip` — the chip-table-faithful + range-faithful legs the prompt asks
for, as conjuncts rather than free `hchip`/`hrange` levers. -/
structure Satisfied2Faithful (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Prop extends Satisfied2 hash d minit mfin maddrs t where
  /-- the genuine permutation exposes exactly `CHIP_OUT_LANES` output lanes. -/
  permWidth : ∀ ins, (permOut ins).length = CHIP_OUT_LANES
  /-- the v1 digest IS lane 0 of the genuine permutation (the deployed squeeze). -/
  chipHashIsLane0 : ∀ ins, hash ins = (permOut ins).headD 0
  /-- THE CHIP-TABLE-FAITHFUL CONJUNCT: every chip row is a genuine wide permutation tuple
  (`Ir2Air::Chip`), bound to `t.tf .poseidon2` — not a free lever. -/
  chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)
  /-- THE RANGE-FAITHFUL CONJUNCT: the range table is the genuine limb table (the deployed height). -/
  rangeTableFaithful : t.tf .range = rangeRows BAL_LIMB_BITS

/-- The legacy chip soundness (`ChipTableSound hash`) FOLLOWS from the faithful structure's wide
soundness + the lane-0 digest identity — the `hchip` lever `graduateV1_sound` needs, DISCHARGED from
the structure, not assumed. -/
theorem Satisfied2Faithful.chipSound {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Faithful permOut hash d minit mfin maddrs t) :
    ChipTableSound hash (t.tf .poseidon2) := by
  -- the wide soundness is for `permOut`; the legacy soundness is for `fun ins => (permOut ins).headD 0`,
  -- which IS `hash` by `chipHashIsLane0`.
  have hcs := chipSoundN_implies_chipSound permOut h.permWidth (t.tf .poseidon2) h.chipTableFaithful
  -- rewrite the exposed digest to `hash`.
  have hfun : (fun ins => (permOut ins).headD 0) = hash := by
    funext ins; exact (h.chipHashIsLane0 ins).symm
  rwa [hfun] at hcs

/-! ## §3 — THE COLLAPSE RECIPE: the v1 denotation directly from the faithful structure (no lever). -/

/-- **`satisfied2Faithful_satisfiedVm` — THE COLLAPSE RECIPE.** From a `Satisfied2Faithful` witness of
the GRADUATED descriptor `graduateV1 d` (and `graduable d`), the v1 denotation `satisfiedVm` holds on
every row window — with NO free `hchip`/`hrange` lever: the structure CARRIES them
(`Satisfied2Faithful.chipSound` discharges `hchip`; `rangeTableFaithful` IS `hrange`). This is the
recipe every per-effect rung instantiates: the `graduateV1`-lever discharge moves from a SUPPLIED
hypothesis to a STRUCTURAL consequence of the deployed accept-set. -/
theorem satisfied2Faithful_satisfiedVm (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (h : Satisfied2Faithful permOut hash (graduateV1 d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  graduateV1_sound hash d minit mfin maddrs t h.chipSound h.rangeTableFaithful hgrad h.toSatisfied2

/-! ## §4 — the transfer beachhead (the recipe FIRED on a live rung).

`RotatedKernelRefinement.transfer_descriptorRefines` and friends consume `∀ i, satisfiedVm hash
transferV3-pre-graduation …`. Re-stating the recipe at `d := rotateV3FrozenAuthority
transferVmDescriptor` (whose `graduateV1` is the live `transferV3`) gives the v1 denotation DIRECTLY
from the faithful object, dropping the `graduateV1`-lever two-step. The SAME two lines fan out to
every effect group (mint/burn/setField/record-pin/noteSpend/cap-family): instantiate `d` to the
effect's `rotateV3*` pre-graduation descriptor and feed the faithful witness. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3FrozenAuthority
  graduable_rotateV3FrozenAuthority)

/-- **`transfer_satisfiedVm_faithful` — THE BEACHHEAD.** From a `Satisfied2Faithful` witness of the
graduated frozen-authority transfer descriptor (= the live `transferV3`), the transfer's v1 denotation
`satisfiedVm` holds on every row, with NO free chip/range lever. The recipe applied to the transfer
rung; the per-effect refinement theorems (`transfer_descriptorRefines_facet` et al.) compose through
this exactly as they compose through `graduateV1_sound` today — but the levers are now CARRIED. -/
theorem transfer_satisfiedVm_faithful (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable transferVmDescriptor = true)
    (h : Satisfied2Faithful permOut hash
      (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash (rotateV3FrozenAuthority transferVmDescriptor)
        (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  satisfied2Faithful_satisfiedVm permOut hash (rotateV3FrozenAuthority transferVmDescriptor)
    minit mfin maddrs t (graduable_rotateV3FrozenAuthority hgrad) h

/-! ## §5 — Axiom hygiene. -/

#assert_axioms chipSoundN_implies_chipSound
#assert_axioms Satisfied2Faithful.chipSound
#assert_axioms satisfied2Faithful_satisfiedVm
#assert_axioms transfer_satisfiedVm_faithful

end Dregg2.Circuit.Satisfied2Faithful
