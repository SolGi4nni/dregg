/-
# Dregg2.Circuit.Emit.GraduateNarrow — the NARROW graduation (`graduateV1Narrow`) + its soundness.

`graduateV1` (`EffectVmEmitV2.lean`) re-anchors a v1 descriptor onto IR-v2 by sending every hash site
to the 25-WIDE Poseidon2 chip bus (`siteLookup`), which carries 7 witnessed lane columns per site
(`CHIP_OUT_LANES - 1`) that the single-output site denotation NEVER reads (they ride existentially in
`chip_lookup_sound`). This module adds the NARROW graduation BESIDE it: single-output sites route to
the 18-wide narrow chip bus (`siteLookupNarrow`, `NarrowChip.lean`) — same `out0 = hash inputs`
equation, NO lane columns, NO per-site lane block appended to the trace width.

`graduateV1Narrow_sound` is the exact mirror of `graduateV1_sound`: a `Satisfied2` witness of the
narrow-graduated descriptor (against a SOUND NARROW chip table + the faithful range table) yields the
FULL v1 denotation `satisfiedVm` on every row. The base-constraint and range legs are IDENTICAL to the
wide keystone; ONLY the hash-sites leg changes — it discharges through `siteLookupsNarrow_sound` (the
narrow ordered-site induction, built on the ALREADY-PROVEN `chip_lookup_sound_narrow`) instead of the
25-wide `siteLookups_sound`. `graduateV1Narrow_width_shrink` is the machine-checked WIN: the narrow
descriptor's trace width is `7·(#hash sites)` columns narrower than the wide graduation's.

This is ADDITIVE: the deployed `graduateV1` / `graduateV1_sound` / the deployed descriptors / the
registries are UNTOUCHED. A later (ember-gated) step wires `graduateV1Narrow` in for the single-output
cohort + regenerates the VK.

## Axiom hygiene
`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}` on every theorem. NO sorry, NO new axiom,
NO named crypto carrier (the narrow chip soundness rides `chip_lookup_sound_narrow`, itself clean).
-/
import Dregg2.Circuit.Emit.EffectVmEmitV2
import Dregg2.Circuit.NarrowChip

namespace Dregg2.Circuit.Emit.EffectVmEmitV2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The narrow ordered-site induction: narrow chip lookups ⟹ the v1 hash-site walk.

The exact mirror of `go_of_siteLookups` / `siteLookups_sound`, discharging through the 18-wide
`chip_lookup_sound_narrow` instead of the 25-wide `chip_lookup_sound`. It is STRICTLY simpler: there
is no `width`/lane-base to thread (narrow lookups carry no per-site lane columns), so the per-site
positional offset the wide induction manages is gone. -/

/-- **The narrow soundness induction.** With the prefix invariant established, the suffix's NARROW
chip lookups (against a sound narrow chip table) realize the v1 site walk from the current
accumulator. Mirror of `go_of_siteLookups`, lane-base dropped. -/
theorem go_of_siteLookupsNarrow (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (env : VmRowEnv) (all : List VmHashSite)
    (rest : List VmHashSite) :
    ∀ (pre : List VmHashSite) (acc : List ℤ),
      all = pre ++ rest →
      acc.length = pre.length →
      (∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) →
      sitesWFAux acc.length rest = true →
      (∀ s ∈ rest, s.inputs.length ≤ CHIP_RATE) →
      (∀ i, (h : i < rest.length) →
        (siteLookupNarrow all rest[i]).tuple.map (·.eval env.loc) ∈ tbl) →
      siteHoldsAll.go hash env acc rest := by
  induction rest with
  | nil => intro pre acc _ _ _ _ _ _; trivial
  | cons s ss ih =>
    intro pre acc hall hlen hacc hwf hfit hlk
    simp only [sitesWFAux, Bool.and_eq_true] at hwf
    obtain ⟨hwfs, hwfss⟩ := hwf
    have hlk0 := hlk 0 (by simp)
    simp only [List.getElem_cons_zero, siteLookupNarrow] at hlk0
    have hchip := chip_lookup_sound_narrow hash tbl hSound env.loc
      (s.inputs.map (HashInput.toExpr all)) s.digestCol
      (by simpa [List.length_map] using hfit s List.mem_cons_self)
      hlk0
    rw [siteTuple_eval_resolved env all acc s hwfs hacc] at hchip
    refine ⟨hchip, ?_⟩
    apply ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)])
    · rw [hall, List.append_assoc]; rfl
    · simp [hlen]
    · exact hacc_extend env pre ss s acc _ all hall hlen hacc hchip
    · simpa using hwfss
    · exact fun s' hs' => hfit s' (List.mem_cons_of_mem s hs')
    · intro i hi
      have := hlk (i + 1) (by simpa using Nat.succ_lt_succ hi)
      simp only [List.getElem_cons_succ] at this
      exact this

/-- **`siteLookupsNarrow_sound`** — the whole ordered family: per-site NARROW chip lookups against a
sound narrow chip table ⟹ the full v1 hash-site denotation `siteHoldsAll`. Mirror of
`siteLookups_sound`, with NO lane base. -/
theorem siteLookupsNarrow_sound (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (env : VmRowEnv) (sites : List VmHashSite)
    (hwf : sitesWF sites = true)
    (hfit : ∀ s ∈ sites, s.inputs.length ≤ CHIP_RATE)
    (hlk : ∀ i, (h : i < sites.length) →
      (siteLookupNarrow sites sites[i]).tuple.map (·.eval env.loc) ∈ tbl) :
    siteHoldsAll hash env sites :=
  go_of_siteLookupsNarrow hash tbl hSound env sites sites [] [] rfl rfl
    (fun k hk => absurd hk (by simp)) hwf hfit hlk

/-! ## §2 — `graduateV1Narrow`: the narrow re-anchored emission.

Identical to `graduateV1` EXCEPT: the trace width carries NO per-site lane columns (the win); every
hash site becomes a NARROW chip lookup (`siteLookupNarrow`, no per-site base ⇒ `map`, not `mapIdx`). -/

/-- **`graduateV1Narrow`** — re-anchor a v1 descriptor onto IR-v2 via the NARROW chip bus. Constraints
embed, every hash site becomes an 18-wide narrow chip lookup, every range tooth becomes a range
lookup; NO lane columns are appended to the trace width. -/
def graduateV1Narrow (d : EffectVmDescriptor) : EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth
  , piCount     := d.piCount
  , tables      := v2Tables d.traceWidth
  , constraints :=
      d.constraints.map .base
        ++ d.hashSites.map (fun s => .lookup (siteLookupNarrow d.hashSites s))
        ++ d.ranges.map (fun r => .lookup (rangeLookup r))
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — `graduateV1Narrow_sound`: THE narrow re-anchor keystone (mirror of `graduateV1_sound`).

A `Satisfied2` witness of the narrow-graduated descriptor — against a sound NARROW chip table and the
faithful range table — yields the FULL v1 denotation `satisfiedVm` on every row window. The base and
range legs are IDENTICAL to `graduateV1_sound`; the hash-sites leg discharges through
`siteLookupsNarrow_sound` (the 18-wide `chip_lookup_sound_narrow` core) rather than the 25-wide
`siteLookups_sound`. -/
theorem graduateV1Narrow_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSoundNarrow hash (t.tf poseidon2narrow))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (graduateV1Narrow d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  intro i hi
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the v1 constraints, embedded
    intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1Narrow d).constraints := by
      unfold graduateV1Narrow
      simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrow _ hmem
  · -- the hash sites, via the NARROW chip-lookup induction (no lane base)
    apply siteLookupsNarrow_sound hash (t.tf poseidon2narrow) hchip (envAt t i) d.hashSites hwf
    · intro s hs
      exact of_decide_eq_true (List.all_eq_true.mp hfit s hs)
    · intro j hj
      have hmem : VmConstraint2.lookup (siteLookupNarrow d.hashSites d.hashSites[j])
          ∈ (graduateV1Narrow d).constraints := by
        unfold graduateV1Narrow
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨d.hashSites[j], List.getElem_mem hj, rfl⟩)
      exact hrow _ hmem
  · -- the range teeth, via the range-table lookup (IDENTICAL to `graduateV1_sound`)
    intro r hr
    obtain ⟨w, bits⟩ := r
    have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
    subst hb
    have hmem : VmConstraint2.lookup (rangeLookup ⟨w, BAL_LIMB_BITS⟩)
        ∈ (graduateV1Narrow d).constraints := by
      unfold graduateV1Narrow
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨⟨w, BAL_LIMB_BITS⟩, hr, rfl⟩
    exact lookup_replaces_range BAL_LIMB_BITS t.tf hrange (envAt t i) w (hrow _ hmem)

/-! ## §4 — The width-shrink WIN (machine-checked).

Narrow graduation drops exactly the `CHIP_OUT_LANES - 1 = 7` lane columns per single-output hash
site: the narrow descriptor is `7·(#hash sites)` columns narrower than the wide graduation. -/

/-- **The width shrink is exactly `7·(#hash sites)`.** `graduateV1` appends `(CHIP_OUT_LANES-1)·n`
lane columns; `graduateV1Narrow` appends none — so the wide-minus-narrow trace-width gap is precisely
the dropped lane block. -/
theorem graduateV1Narrow_width_shrink (d : EffectVmDescriptor) :
    (graduateV1 d).traceWidth - (graduateV1Narrow d).traceWidth
      = (CHIP_OUT_LANES - 1) * d.hashSites.length := by
  show d.traceWidth + (CHIP_OUT_LANES - 1) * d.hashSites.length - d.traceWidth
      = (CHIP_OUT_LANES - 1) * d.hashSites.length
  omega

-- The concrete win on the validated TRANSFER reference: wide-minus-narrow = 7·(#sites).
#guard (graduateV1 EffectVmEmitTransfer.transferVmDescriptor).traceWidth
        - (graduateV1Narrow EffectVmEmitTransfer.transferVmDescriptor).traceWidth
     == (CHIP_OUT_LANES - 1) * EffectVmEmitTransfer.transferVmDescriptor.hashSites.length
-- Narrow trace width is the UNGRADUATED v1 width (no lane columns appended at all).
#guard (graduateV1Narrow EffectVmEmitTransfer.transferVmDescriptor).traceWidth
     == EffectVmEmitTransfer.transferVmDescriptor.traceWidth
-- And it is STRICTLY narrower than the wide graduation whenever the descriptor hashes.
#guard (graduateV1Narrow EffectVmEmitTransfer.transferVmDescriptor).traceWidth
     < (graduateV1 EffectVmEmitTransfer.transferVmDescriptor).traceWidth

#assert_axioms go_of_siteLookupsNarrow
#assert_axioms siteLookupsNarrow_sound
#assert_axioms graduateV1Narrow_sound
#assert_axioms graduateV1Narrow_width_shrink

end Dregg2.Circuit.Emit.EffectVmEmitV2
