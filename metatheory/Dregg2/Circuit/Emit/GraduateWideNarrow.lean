/-
# Dregg2.Circuit.Emit.GraduateWideNarrow — the NARROW-base mirror of the WIDE graduation tower.

The deployed WIDE graduation (`graduateV1Wide`, `v3OfFrozenWide`, `rotV3FrozenWide_sound_v1`,
`wideEmbedded_sound_v1`) sends every hash site to the 25-WIDE Poseidon2 chip bus (`siteLookup`),
carrying 7 witnessed lane columns per site (`CHIP_OUT_LANES - 1`) that a single-output site
denotation NEVER reads (they ride existentially in `chip_lookup_sound`). This module adds the
NARROW-base twin BESIDE it: single-output sites route to the 18-wide narrow chip bus
(`siteLookupNarrow`, `NarrowChip.lean`) — the SAME `out0 = hash inputs` equation, NO lane columns,
NO per-site lane block appended to the trace width. Everything else (the per-width 15-bit range
teeth of `graduableWide` / `rangeLookupW`, the frozen-authority rotation, the membership-parametric
collapse) is carried VERBATIM.

`graduateV1WideNarrow` = `graduateV1Wide` with `siteLookup -> siteLookupNarrow`, `mapIdx -> map`
(no per-site lane base), and `traceWidth := d.traceWidth` (the lane columns dropped). Its soundness
keystone `graduateV1WideNarrow_sound` mirrors `graduateV1Wide_sound`: the ONLY changed leg is the
hash-sites walk, which discharges through `siteLookupsNarrow_sound` (the already-proven 18-wide
`chip_lookup_sound_narrow` core) over `poseidon2narrow`, instead of the 25-wide `siteLookups_sound`
over `.poseidon2`. The base-constraint and per-width range legs are IDENTICAL to the wide keystone.

The two deployed collapse keystones are mirrored with narrow bases and conclusions byte-identical to
their wide twins:
  * `rotV3FrozenWideNarrow_sound_v1` — the narrow mirror of `rotV3FrozenWide_sound_v1`
    (`v3OfFrozenWideNarrow := graduateV1WideNarrow (rotateV3FrozenAuthority d)`);
  * `wideEmbeddedNarrow_sound_v1` — the narrow mirror of the membership-parametric
    `wideEmbedded_sound_v1`: from a narrow-wide-faithful witness of ANY descriptor `D` whose
    constraints EMBED the (legacy-pin-filtered) `v3OfFrozenWideNarrow d` constraint set, the FULL
    per-row v1 denotation `satisfiedVm hash d` returns (the FULL 3-conjunction is preserved — this
    is a PORT of the walk, not a removal of the obligation).

The faithful carrier is `Satisfied2FaithfulWideNarrow`, the minimal narrow mirror of
`Satisfied2FaithfulWide`: the wide structure carries a genuine-permutation chip
(`ChipTableSoundN permOut` + `hash = lane 0`) because the 25-wide chip's genuine rows are
permutation rows; the narrow chip's genuine rows encode `hash ins` DIRECTLY as out0
(`ChipTableSoundNarrow hash`), so there is no `permOut` indirection to carry — the narrow structure
holds `ChipTableSoundNarrow hash (t.tf poseidon2narrow)` as a field and the per-width range pins.

This is ADDITIVE: the deployed `graduateV1Wide` / `v3OfFrozenWide` / `rotV3FrozenWide_sound_v1` /
`wideEmbedded_sound_v1` / the deployed descriptors / registries are UNTOUCHED. A later (ember-gated)
step routes the single-output sites of the live wide descriptor to the narrow bus + regenerates the
VK; the `RotatedKernelRefinementCapOpenAvailWide` / `AvailWideFeeMember` / `AvailWideMembers`
downstream re-points ride these mirrors.

## Axiom hygiene
`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}` on every theorem. NO sorry, NO new axiom,
NO named crypto carrier: table soundness enters ONLY as the `ChipTableSoundNarrow` hypothesis /
`Satisfied2FaithfulWideNarrow.chipTableFaithfulNarrow` field (itself riding the clean
`chip_lookup_sound_narrow`), never an axiom.
-/
import Dregg2.Circuit.Emit.GraduateNarrow
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Circuit.Emit.EffectVmEmitV2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (rotateV3FrozenAuthority rotateV3FrozenAuthority_constraints v3OfFrozenWide
   graduableWide_rotateV3FrozenAuthority rotateV3FrozenAuthority_satisfiedVm_v1
   rotV3Appendix go_append_left B_STATE_COMMIT)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (isLegacyCommitPin1)

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 16000

/-! ## §1 — `graduateV1WideNarrow`: the narrow-base multi-width re-anchored emission.

Identical to `graduateV1Wide` EXCEPT: the trace width carries NO per-site lane columns (the win);
every hash site becomes an 18-wide NARROW chip lookup (`siteLookupNarrow`, no per-site lane base ⇒
`map`, not `mapIdx`). The per-width range teeth (`rangeLookupW`, the 15-bit borrow limbs into the
15-bit table) and the width-tagged range tables are carried VERBATIM from `graduateV1Wide`. -/

/-- **`graduateV1WideNarrow`** — `graduateV1Wide` with the narrow site leg + shrunk width. Constraints
embed, every hash site becomes an 18-wide narrow chip lookup, every range tooth lowers via
`rangeLookupW` into ITS OWN width's table; NO lane columns are appended to the trace width. -/
def graduateV1WideNarrow (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth
  , piCount     := d.piCount
  , tables      :=
      v2Tables d.traceWidth
        ++ (WIDE_RANGE_WIDTHS.filter (fun b => !(b == BAL_LIMB_BITS))).map
             (fun b => ⟨rangeTidW b, "range_w" ++ toString b, 1, .rangeLimb b⟩)
  , constraints :=
      d.constraints.map .base
        ++ narrowSites d.hashSites hAdm
        ++ d.ranges.map (fun r => .lookup (rangeLookupW r))
  , hashSites   := []
  , ranges      := [] }

/-! ## §2 — `graduateV1WideNarrow_sound`: THE narrow-base multi-width re-anchor keystone (mirror of
`graduateV1Wide_sound`).

A `Satisfied2` witness of the narrow-wide graduation — against a sound NARROW chip table and the
per-width faithful range tables — yields the FULL v1 denotation `satisfiedVm` (15-bit teeth bounded
`< 2^15` EXACTLY) on every row window. The base and per-width range legs are IDENTICAL to
`graduateV1Wide_sound`; the hash-sites leg discharges through `siteLookupsNarrow_sound` (the 18-wide
`chip_lookup_sound_narrow` core) over `poseidon2narrow` rather than the 25-wide `siteLookups_sound`
over `.poseidon2`. -/
theorem graduateV1WideNarrow_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSoundNarrow hash (t.tf poseidon2narrow))
    (hrangeW : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b)
    (hgrad : graduableWide d = true)
    (hsat : Satisfied2 hash (graduateV1WideNarrow d (sitesFit_admitted (graduableWide_spec hgrad).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduableWide_spec hgrad
  intro i hi
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the v1 constraints, embedded (IDENTICAL to `graduateV1Wide_sound`)
    intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1WideNarrow d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1WideNarrow
      simp only [List.mem_append, List.mem_map, mem_narrowSites]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrow _ hmem
  · -- the hash sites, via the NARROW chip-lookup induction (no lane base)
    refine siteLookupsNarrow_sound hash (t.tf poseidon2narrow) hchip (envAt t i) d.hashSites hwf
      (sitesFit_admitted hfit) ?_
    · intro j hj
      have hmem : VmConstraint2.lookup (siteLookupNarrow d.hashSites d.hashSites[j]
            (sitesFit_admitted hfit _ (List.getElem_mem hj)))
          ∈ (graduateV1WideNarrow d (sitesFit_admitted hfit)).constraints := by
        unfold graduateV1WideNarrow
        simp only [List.mem_append, List.mem_map, mem_narrowSites]
        exact Or.inl (Or.inr ⟨d.hashSites[j], List.getElem_mem hj, rfl⟩)
      exact hrow _ hmem
  · -- the range teeth, each via ITS OWN width's table (IDENTICAL to `graduateV1Wide_sound`)
    intro r hr
    have hb : r.bits ∈ WIDE_RANGE_WIDTHS := hbits r hr
    have hmem : VmConstraint2.lookup (rangeLookupW r) ∈ (graduateV1WideNarrow d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1WideNarrow
      simp only [List.mem_append, List.mem_map, mem_narrowSites]
      exact Or.inr ⟨r, hr, rfl⟩
    exact lookup_replaces_rangeW r.bits t.tf (hrangeW r.bits hb) (envAt t i) r.wire (hrow _ hmem)

/-! ## §3 — `Satisfied2FaithfulWideNarrow`: the minimal narrow-base faithful carrier.

The narrow mirror of `Satisfied2FaithfulWide`. The wide structure carries `permOut` and a
genuine-permutation chip (`ChipTableSoundN permOut` + `hash = lane 0`) because the 25-wide chip's
genuine rows ARE permutation rows. The narrow chip's genuine rows encode `hash ins` DIRECTLY as out0
(`ChipTableSoundNarrow hash`), so there is no `permOut` indirection: the narrow structure carries the
narrow chip soundness as a field, plus the per-width range pins (verbatim from the wide). -/
structure Satisfied2FaithfulWideNarrow (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Prop extends Satisfied2 hash d minit mfin maddrs t where
  /-- THE NARROW CHIP-TABLE-FAITHFUL CONJUNCT, bound to `t.tf poseidon2narrow` (the reserved
  `.custom 3` narrow bus): every row is a genuine `(arity, padded inputs, hash inputs)` tuple. -/
  chipTableFaithfulNarrow : ChipTableSoundNarrow hash (t.tf poseidon2narrow)
  /-- THE PER-WIDTH RANGE-FAITHFUL CONJUNCT (verbatim from `Satisfied2FaithfulWide`): every allowed
  width's table is its genuine limb table (subsumes the single `.range` pin at `b = BAL_LIMB_BITS`). -/
  rangeTablesWideFaithful : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b

/-- The narrow faithful object discharges the narrow chip soundness `graduateV1WideNarrow_sound`
consumes (not assumed — a projection of the structure's own field). -/
theorem Satisfied2FaithfulWideNarrow.chipSoundNarrow {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2FaithfulWideNarrow hash d minit mfin maddrs t) :
    ChipTableSoundNarrow hash (t.tf poseidon2narrow) :=
  h.chipTableFaithfulNarrow

/-- The narrow faithful witness of a narrow-wide graduation yields the v1 denotation on every row
(the narrow mirror of `satisfied2FaithfulWide_satisfiedVm`: `graduateV1WideNarrow_sound` fed the chip
+ range pins from the structure's own fields). -/
theorem satisfied2FaithfulWideNarrow_satisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hf : Satisfied2FaithfulWideNarrow hash (graduateV1WideNarrow d (sitesFit_admitted (graduableWide_spec hgrad).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  graduateV1WideNarrow_sound hash d minit mfin maddrs t
    hf.chipTableFaithfulNarrow hf.rangeTablesWideFaithful hgrad hf.toSatisfied2

/-! ## §4 — `rotV3FrozenWideNarrow_sound_v1`: the narrow mirror of `rotV3FrozenWide_sound_v1`.

`v3OfFrozenWideNarrow := graduateV1WideNarrow (rotateV3FrozenAuthority d)` — the narrow-base twin of
`v3OfFrozenWide`. A narrow-wide-faithful witness yields the full v1 denotation of the original
descriptor on every row. CONCLUSION byte-identical to `rotV3FrozenWide_sound_v1`. -/

/-- **`v3OfFrozenWideNarrow d`** — the narrow-base WIDE graduated rotated descriptor of a hardened
member (the narrow twin of `v3OfFrozenWide`): same rotation + authority-continuity weld, range teeth
lowered per-width, hash sites on the 18-wide narrow bus with NO lane columns. -/
def v3OfFrozenWideNarrow (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3FrozenAuthority d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  graduateV1WideNarrow (rotateV3FrozenAuthority d) hAdm

/-- **`rotV3FrozenWideNarrow_sound_v1`** — a `Satisfied2FaithfulWideNarrow` witness of the narrow-base
WIDE frozen graduation yields the full v1 denotation of the original descriptor on every row (the
narrow-base mirror of `rotV3FrozenWide_sound_v1`, conclusion byte-identical). -/
theorem rotV3FrozenWideNarrow_sound_v1 (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hf : Satisfied2FaithfulWideNarrow hash (v3OfFrozenWideNarrow d (sitesFit_admitted (graduableWide_spec (graduableWide_rotateV3FrozenAuthority hgrad)).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3FrozenAuthority_satisfiedVm_v1 hash d _ _ _
    (satisfied2FaithfulWideNarrow_satisfiedVm hash (rotateV3FrozenAuthority d) minit mfin maddrs
      t (graduableWide_rotateV3FrozenAuthority hgrad) hf i hi)

/-! ## §5 — `wideEmbeddedNarrow_sound_v1`: the narrow mirror of the membership-parametric collapse.

From a narrow-wide-faithful witness of ANY descriptor `D` whose constraints EMBED the
(legacy-pin-filtered) `v3OfFrozenWideNarrow d` constraint set, the FULL per-row v1 denotation of the
PRE-ROTATION face `d` returns — the FULL 3-conjunction (embedded base constraints / the chained
site-lookup walk / the per-width range teeth) preserved. Mirror of `wideEmbedded_sound_v1`: the ONLY
changed leg is the hash-sites walk, discharging through `siteLookupsNarrow_sound` over
`poseidon2narrow` (via the structure's own narrow chip field) instead of the 25-wide
`siteLookups_sound` over `.poseidon2`. CONCLUSION byte-identical. -/
theorem wideEmbeddedNarrow_sound_v1 (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (D : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hclean : ∀ c ∈ d.constraints,
      isLegacyCommitPin1 bb ab (VmConstraint2.base c) = false)
    (hemb : ∀ c ∈ (v3OfFrozenWideNarrow d (sitesFit_admitted (graduableWide_spec (graduableWide_rotateV3FrozenAuthority hgrad)).2.1)).constraints,
      isLegacyCommitPin1 bb ab c = false → c ∈ D.constraints)
    (hf : Satisfied2FaithfulWideNarrow hash D minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  have hgradr : graduableWide (rotateV3FrozenAuthority d) = true :=
    graduableWide_rotateV3FrozenAuthority hgrad
  obtain ⟨hwf, hfit, hbits⟩ := graduableWide_spec hgradr
  intro i hi
  have hrow := hf.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the ORIGINAL face's v1 constraints (never the retired pins — `hclean`)
    intro c hc
    have hcr : c ∈ (rotateV3FrozenAuthority d).constraints := by
      rw [rotateV3FrozenAuthority_constraints]
      exact List.mem_append_left _ (List.mem_append_left _ hc)
    have hmem : VmConstraint2.base c ∈ (v3OfFrozenWideNarrow d (sitesFit_admitted (graduableWide_spec hgradr).2.1)).constraints := by
      show VmConstraint2.base c ∈ (graduateV1WideNarrow (rotateV3FrozenAuthority d) (sitesFit_admitted hfit)).constraints
      unfold graduateV1WideNarrow
      simp only [List.mem_append, List.mem_map, mem_narrowSites]
      exact Or.inl (Or.inl ⟨c, hcr, rfl⟩)
    exact hrow _ (hemb _ hmem (hclean c hc))
  · -- the ORIGINAL face's hash sites: the FULL rotated chained NARROW walk, then the prefix
    have hall : siteHoldsAll hash (envAt t i) (rotateV3FrozenAuthority d).hashSites := by
      refine siteLookupsNarrow_sound hash (t.tf poseidon2narrow) hf.chipTableFaithfulNarrow
        (envAt t i) (rotateV3FrozenAuthority d).hashSites hwf (sitesFit_admitted hfit) ?_
      · intro j hj
        have hmem : VmConstraint2.lookup
            (siteLookupNarrow (rotateV3FrozenAuthority d).hashSites
              (rotateV3FrozenAuthority d).hashSites[j]
              (sitesFit_admitted hfit _ (List.getElem_mem hj)))
            ∈ (v3OfFrozenWideNarrow d (sitesFit_admitted (graduableWide_spec hgradr).2.1)).constraints := by
          show _ ∈ (graduateV1WideNarrow (rotateV3FrozenAuthority d) (sitesFit_admitted hfit)).constraints
          unfold graduateV1WideNarrow
          simp only [List.mem_append, List.mem_map, mem_narrowSites]
          exact Or.inl (Or.inr ⟨(rotateV3FrozenAuthority d).hashSites[j], List.getElem_mem hj, rfl⟩)
        exact hrow _ (hemb _ hmem rfl)
    exact go_append_left hash (envAt t i) [] d.hashSites (rotV3Appendix d.traceWidth) hall
  · -- the ORIGINAL face's range teeth, each via ITS OWN width's table (15-bit EXACT)
    intro r hr
    have hb : r.bits ∈ WIDE_RANGE_WIDTHS := hbits r hr
    have hmem : VmConstraint2.lookup (rangeLookupW r) ∈ (v3OfFrozenWideNarrow d (sitesFit_admitted (graduableWide_spec hgradr).2.1)).constraints := by
      show _ ∈ (graduateV1WideNarrow (rotateV3FrozenAuthority d) (sitesFit_admitted hfit)).constraints
      unfold graduateV1WideNarrow
      simp only [List.mem_append, List.mem_map, mem_narrowSites]
      exact Or.inr ⟨r, hr, rfl⟩
    exact lookup_replaces_rangeW r.bits t.tf (hf.rangeTablesWideFaithful r.bits hb)
      (envAt t i) r.wire (hrow _ (hemb _ hmem rfl))

/-! ## §6 — The width-shrink WIN (machine-checked).

The narrow-base wide graduation drops exactly the `CHIP_OUT_LANES - 1 = 7` lane columns per hash
site: `graduateV1WideNarrow d` is `7·(#hash sites)` columns narrower than `graduateV1Wide d`. -/

/-- **The wide-minus-narrow trace-width gap is exactly `7·(#hash sites)`.** `graduateV1Wide` appends
`(CHIP_OUT_LANES-1)·n` lane columns; `graduateV1WideNarrow` appends none. -/
theorem graduateV1WideNarrow_width_shrink (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    (graduateV1Wide d hAdm).traceWidth - (graduateV1WideNarrow d hAdm).traceWidth
      = (CHIP_OUT_LANES - 1) * d.hashSites.length := by
  show d.traceWidth + (CHIP_OUT_LANES - 1) * d.hashSites.length - d.traceWidth
      = (CHIP_OUT_LANES - 1) * d.hashSites.length
  omega

-- The concrete win on the live TRANSFER WIDE member (`v3OfFrozenWide transferVmDescriptorAvail` —
-- the hardened availability face the deployed wide registry hosts): the narrow-base wide graduation
-- of the SAME rotated face is `7·(#sites)` columns narrower than the deployed wide graduation.
#guard (v3OfFrozenWide EffectVmEmitTransfer.transferVmDescriptorAvail).traceWidth
        - (v3OfFrozenWideNarrow EffectVmEmitTransfer.transferVmDescriptorAvail).traceWidth
     == (CHIP_OUT_LANES - 1)
        * (rotateV3FrozenAuthority EffectVmEmitTransfer.transferVmDescriptorAvail).hashSites.length
-- Narrow-base wide trace width is the UNGRADUATED rotated width (no lane columns appended at all).
#guard (v3OfFrozenWideNarrow EffectVmEmitTransfer.transferVmDescriptorAvail).traceWidth
     == (rotateV3FrozenAuthority EffectVmEmitTransfer.transferVmDescriptorAvail).traceWidth
-- And it is STRICTLY narrower than the deployed wide graduation.
#guard (v3OfFrozenWideNarrow EffectVmEmitTransfer.transferVmDescriptorAvail).traceWidth
     < (v3OfFrozenWide EffectVmEmitTransfer.transferVmDescriptorAvail).traceWidth

#assert_axioms graduateV1WideNarrow_sound
#assert_axioms Satisfied2FaithfulWideNarrow.chipSoundNarrow
#assert_axioms satisfied2FaithfulWideNarrow_satisfiedVm
#assert_axioms rotV3FrozenWideNarrow_sound_v1
#assert_axioms wideEmbeddedNarrow_sound_v1
#assert_axioms graduateV1WideNarrow_width_shrink

end Dregg2.Circuit.Emit.EffectVmEmitV2
