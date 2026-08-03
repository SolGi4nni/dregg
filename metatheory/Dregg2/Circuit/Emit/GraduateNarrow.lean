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
      (hfit : ∀ s ∈ rest, ChipArityAdmitted s.inputs.length) →
      (∀ i, (h : i < rest.length) →
        (siteLookupNarrow all rest[i] (hfit _ (List.getElem_mem h))).tuple.map
          (·.eval env.loc) ∈ tbl) →
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
    -- positional: `hfit` is now a NAMED binder the lookup hypothesis depends on.
    refine ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)])
      (by rw [hall, List.append_assoc]; rfl)
      (by simp [hlen])
      (hacc_extend env pre ss s acc _ all hall hlen hacc hchip)
      (by simpa using hwfss)
      (fun s' hs' => hfit s' (List.mem_cons_of_mem s hs')) ?_
    intro i hi
    have := hlk (i + 1) (by simpa using Nat.succ_lt_succ hi)
    simp only [List.getElem_cons_succ] at this
    exact this

/-- **`siteLookupsNarrow_sound`** — the whole ordered family: per-site NARROW chip lookups against a
sound narrow chip table ⟹ the full v1 hash-site denotation `siteHoldsAll`. Mirror of
`siteLookups_sound`, with NO lane base. -/
theorem siteLookupsNarrow_sound (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (env : VmRowEnv) (sites : List VmHashSite)
    (hwf : sitesWF sites = true)
    (hfit : ∀ s ∈ sites, ChipArityAdmitted s.inputs.length)
    (hlk : ∀ i, (h : i < sites.length) →
      (siteLookupNarrow sites sites[i] (hfit _ (List.getElem_mem h))).tuple.map
        (·.eval env.loc) ∈ tbl) :
    siteHoldsAll hash env sites :=
  go_of_siteLookupsNarrow hash tbl hSound env sites sites [] [] rfl rfl
    (fun k hk => absurd hk (by simp)) hwf hfit hlk

/-! ## §2 — `graduateV1Narrow`: the narrow re-anchored emission.

Identical to `graduateV1` EXCEPT: the trace width carries NO per-site lane columns (the win); every
hash site becomes a NARROW chip lookup (`siteLookupNarrow`, no per-site base ⇒ `map`, not `mapIdx`). -/

/-- One narrow-graduated hash site's chip lookup, carrying its own admission (`attach` transports
the family condition into the `map` lambda — the narrow mirror of `graduateSiteLookup`). -/
def narrowSiteConstraint (sites : List VmHashSite)
    (hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length)
    (s : {x : VmHashSite // x ∈ sites}) : VmConstraint2 :=
  .lookup (siteLookupNarrow sites s.1 (hAdm s.1 s.2))

/-- The narrow-graduated site block. -/
def narrowSites (sites : List VmHashSite)
    (hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length) : List VmConstraint2 :=
  sites.attach.map (narrowSiteConstraint sites hAdm)

/-- Membership in EXACTLY `List.mem_map`'s shape, so the admission threading costs no proof
restructuring downstream. -/
theorem mem_narrowSites {sites : List VmHashSite}
    {hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length} {c : VmConstraint2} :
    c ∈ narrowSites sites hAdm ↔
      ∃ (s : VmHashSite) (hs : s ∈ sites),
        VmConstraint2.lookup (siteLookupNarrow sites s (hAdm s hs)) = c := by
  rw [narrowSites, List.mem_map]
  constructor
  · rintro ⟨⟨x, hx⟩, _, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, List.mem_attach _ _, rfl⟩

/-- **`graduateV1Narrow`** — re-anchor a v1 descriptor onto IR-v2 via the NARROW chip bus.
Constraints embed, every hash site becomes an 18-wide narrow chip lookup, every range tooth becomes
a range lookup; NO lane columns are appended to the trace width.

⚑ `hAdm` is the same CONSTRUCTION obligation `graduateV1` takes, and it is not a weaker one here:
the narrow bus is served by the 18-PREFIX of the same physical chip rows, so it inherits the same
degree-7 admission product. -/
def graduateV1Narrow (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth
  , piCount     := d.piCount
  , tables      := v2Tables d.traceWidth
  , constraints :=
      d.constraints.map .base
        ++ narrowSites d.hashSites hAdm
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
    (hsat : Satisfied2 hash
      (graduateV1Narrow d (sitesFit_admitted (graduable_spec hgrad).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  intro i hi
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the v1 constraints, embedded
    intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1Narrow d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1Narrow
      simp only [List.mem_append, List.mem_map, mem_narrowSites]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrow _ hmem
  · -- the hash sites, via the NARROW chip-lookup induction (no lane base)
    refine siteLookupsNarrow_sound hash (t.tf poseidon2narrow) hchip (envAt t i) d.hashSites hwf
      (sitesFit_admitted hfit) ?_
    · intro j hj
      have hmem : VmConstraint2.lookup (siteLookupNarrow d.hashSites d.hashSites[j]
          (sitesFit_admitted hfit _ (List.getElem_mem hj)))
          ∈ (graduateV1Narrow d (sitesFit_admitted hfit)).constraints := by
        unfold graduateV1Narrow
        simp only [List.mem_append, List.mem_map, mem_narrowSites]
        exact Or.inl (Or.inr ⟨d.hashSites[j], List.getElem_mem hj, rfl⟩)
      exact hrow _ hmem
  · -- the range teeth, via the range-table lookup (IDENTICAL to `graduateV1_sound`)
    intro r hr
    obtain ⟨w, bits⟩ := r
    have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
    subst hb
    have hmem : VmConstraint2.lookup (rangeLookup ⟨w, BAL_LIMB_BITS⟩)
        ∈ (graduateV1Narrow d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1Narrow
      simp only [List.mem_append, List.mem_map, mem_narrowSites]
      exact Or.inr ⟨⟨w, BAL_LIMB_BITS⟩, hr, rfl⟩
    exact lookup_replaces_range BAL_LIMB_BITS t.tf hrange (envAt t i) w (hrow _ hmem)

/-! ## §4 — The width-shrink WIN (machine-checked).

Narrow graduation drops exactly the `CHIP_OUT_LANES - 1 = 7` lane columns per single-output hash
site: the narrow descriptor is `7·(#hash sites)` columns narrower than the wide graduation. -/

/-- **The width shrink is exactly `7·(#hash sites)`.** `graduateV1` appends `(CHIP_OUT_LANES-1)·n`
lane columns; `graduateV1Narrow` appends none — so the wide-minus-narrow trace-width gap is precisely
the dropped lane block. -/
theorem graduateV1Narrow_width_shrink (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    (graduateV1 d hAdm).traceWidth - (graduateV1Narrow d hAdm).traceWidth
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

/-! ## §5 — Completeness: a v1-satisfying row family BUILDS a satisfying NARROW v2 witness.

The exact mirror of §5 of `EffectVmEmitV2.lean` (`graduateV1_complete`/`graduateV1_faithful`), with the
25-wide chip lookups replaced by the 18-wide narrow ones. The narrow chip table is the gathered genuine
NARROW rows (`chipLogOfNarrow`, sound BY CONSTRUCTION via `go_siteLookups_complete_narrow`); the range
table is the faithful limb table; memory/map tables are empty (the graduated v1 face is inert there). No
lane base is threaded (narrow lookups carry no per-site lane columns), so the gathering is a plain `map`,
not a `mapIdx`. -/

/-- A narrow-graduated v1 descriptor's constraints are ONLY `.base`/`.lookup` (mirror of
`constraints_graduateV1_shapes`). -/
theorem constraints_graduateV1Narrow_shapes (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    ∀ c ∈ (graduateV1Narrow d hAdm).constraints,
      (∃ c₀, c = .base c₀) ∨ (∃ l, c = .lookup l) := by
  intro c hc
  unfold graduateV1Narrow at hc
  simp only [List.mem_append, List.mem_map, mem_narrowSites] at hc
  rcases hc with (⟨c₀, _, rfl⟩ | ⟨s, _, rfl⟩) | ⟨r, _, rfl⟩
  · exact Or.inl ⟨c₀, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- A narrow-graduated v1 descriptor declares no mem ops. -/
theorem memOpsOf_graduateV1Narrow (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    memOpsOf (graduateV1Narrow d hAdm) = [] := by
  unfold memOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1Narrow_shapes d hAdm c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- A narrow-graduated v1 descriptor declares no map ops. -/
theorem mapOpsOf_graduateV1Narrow (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    mapOpsOf (graduateV1Narrow d hAdm) = [] := by
  unfold mapOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1Narrow_shapes d hAdm c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- A narrow-graduated v1 descriptor's memory log is empty. -/
theorem memLog_graduateV1Narrow (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (t : VmTrace) :
    memLog (graduateV1Narrow d hAdm) t = [] := by
  unfold memLog
  rw [memOpsOf_graduateV1Narrow d hAdm]
  simp

/-- A narrow-graduated v1 descriptor's map-ops log is empty. -/
theorem mapLog_graduateV1Narrow (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (t : VmTrace) :
    mapLog (graduateV1Narrow d hAdm) t = [] := by
  unfold mapLog
  rw [mapOpsOf_graduateV1Narrow d hAdm]
  simp

/-- The gathered NARROW chip rows: every row's every narrow site lookup tuple, evaluated. No lane base
is threaded (narrow lookups carry no per-site lane columns), so this is a plain `map`, not `mapIdx`
(contrast `chipLogOf`). -/
def chipLogOfNarrow (sites : List VmHashSite)
    (hAdm : ∀ s ∈ sites, ChipArityAdmitted s.inputs.length) (rows : List Assignment) : Table :=
  rows.flatMap fun a =>
    sites.attach.map fun s =>
      (siteLookupNarrow sites s.1 (hAdm s.1 s.2)).tuple.map (·.eval a)

/-- **The narrow completeness induction.** Under the same prefix invariant, a v1 site walk makes every
suffix site's NARROW lookup tuple evaluate to a GENUINE 18-wide narrow chip row (`chipRowNarrow hash
ins`, NO lanes). Mirror of `go_siteLookups_complete`, lane block dropped (so no `base`, no `lanes`). -/
theorem go_siteLookups_complete_narrow (hash : List ℤ → ℤ) (env : VmRowEnv) (all : List VmHashSite)
    (rest : List VmHashSite) :
    ∀ (pre : List VmHashSite) (acc : List ℤ),
      all = pre ++ rest →
      acc.length = pre.length →
      (∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) →
      sitesWFAux acc.length rest = true →
      siteHoldsAll.go hash env acc rest →
      ∀ (hfit : ∀ s ∈ rest, ChipArityAdmitted s.inputs.length),
      ∀ s, ∀ hs : s ∈ rest, ∃ ins : List ℤ, ins.length = s.inputs.length
        ∧ (siteLookupNarrow all s (hfit s hs)).tuple.map (·.eval env.loc)
            = chipRowNarrow hash ins := by
  induction rest with
  | nil => intro pre acc _ _ _ _ _ _ s hs; cases hs
  | cons s ss ih =>
    intro pre acc hall hlen hacc hwf hgo hfit s' hs'
    simp only [sitesWFAux, Bool.and_eq_true] at hwf
    obtain ⟨hwfs, hwfss⟩ := hwf
    obtain ⟨hd, hgo'⟩ := hgo
    rcases List.mem_cons.mp hs' with rfl | hs''
    · -- the head site: its 18-wide narrow tuple IS a genuine narrow chip row (out0 = hash, no lanes)
      refine ⟨s'.resolvedInputs env acc, by simp [VmHashSite.resolvedInputs], ?_⟩
      have hev : (chipLookupTupleNarrow (s'.inputs.map (HashInput.toExpr all)) s'.digestCol
            (by simpa [List.length_map] using hfit s' hs')).map (·.eval env.loc)
          = ((s'.inputs.map (HashInput.toExpr all)).length : ℤ)
            :: padTo CHIP_RATE ((s'.inputs.map (HashInput.toExpr all)).map (·.eval env.loc))
            ++ [env.loc s'.digestCol] := by
        simp [chipLookupTupleNarrow, List.map_cons, List.map_append, map_eval_padToE,
          EmittedExpr.eval, List.map_map, Function.comp_def]
      show (chipLookupTupleNarrow (s'.inputs.map (HashInput.toExpr all)) s'.digestCol
          (by simpa [List.length_map] using hfit s' hs')).map (·.eval env.loc)
          = chipRowNarrow hash (s'.resolvedInputs env acc)
      rw [hev, siteTuple_eval_resolved env all acc s' hwfs hacc, hd]
      unfold chipRowNarrow
      simp [VmHashSite.resolvedInputs, List.length_map]
    · -- a later site: recurse with the extended prefix
      exact ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)])
        (by rw [hall, List.append_assoc]; rfl)
        (by simp [hlen])
        (hacc_extend env pre ss s acc _ all hall hlen hacc hd)
        (by simpa using hwfss)
        hgo' (fun x hx => hfit x (List.mem_cons_of_mem s hx)) s' hs''

/-- The gathered NARROW chip table is SOUND by construction (mirror of `chipLogOf_sound`). -/
theorem chipLogOfNarrow_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true)
    (hsat : ∀ i, i < rows.length →
      satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length)) :
    ChipTableSoundNarrow hash
      (chipLogOfNarrow d.hashSites (sitesFit_admitted (graduable_spec hgrad).2.1) rows) := by
  obtain ⟨hwf, hfit, _⟩ := graduable_spec hgrad
  intro r hr
  unfold chipLogOfNarrow at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨a, ha, hr⟩ := hr
  rw [List.mem_map] at hr
  obtain ⟨⟨s, hs⟩, _, rfl⟩ := hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hloc : (envOf rows pub i).loc = rows[i] := by
    simp [envOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hgo : siteHoldsAll hash (envOf rows pub i) d.hashSites := (hsat i hi).2.1
  obtain ⟨ins, hlen, heq⟩ := go_siteLookups_complete_narrow hash (envOf rows pub i)
    d.hashSites d.hashSites [] []
    rfl rfl (fun k hk => absurd hk (by simp)) hwf hgo (sitesFit_admitted hfit) s hs
  rw [hloc] at heq
  refine ⟨ins, ?_, heq⟩
  rw [hlen]
  exact sitesFit_admitted hfit s hs

/-- The constructed NARROW trace family: gathered narrow chip rows at `poseidon2narrow` (`.custom 3`),
the faithful range table, empty memory/map/other tables, main unconstrained. Mirror of `v2TF`. -/
def v2TFNarrow (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (rows : List Assignment) : TraceFamily := fun tid =>
  match tid with
  | .custom 3 => chipLogOfNarrow d.hashSites hAdm rows
  | .range => rangeRows BAL_LIMB_BITS
  | _ => []

/-- The constructed narrow multi-table witness over a v1-satisfying row family. -/
def v2TraceOfNarrow (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length)
    (rows : List Assignment) (pub : Assignment) : VmTrace :=
  { rows := rows, pub := pub, tf := v2TFNarrow d hAdm rows }

/-- The constructed narrow trace's family, projected (kept as a `rw` target: a bare `rfl` at the
`.range` use site sends the unifier whnf-ing `rangeRows 30` — the documented evaluation trap). -/
theorem v2TraceOfNarrow_tf (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length)
    (rows : List Assignment) (pub : Assignment) :
    (v2TraceOfNarrow d hAdm rows pub).tf = v2TFNarrow d hAdm rows := rfl

/-- The constructed narrow family's range table is the faithful limb table. -/
theorem v2TFNarrow_range (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (rows : List Assignment) :
    v2TFNarrow d hAdm rows .range = rangeRows BAL_LIMB_BITS := rfl

/-- **`graduateV1Narrow_complete`** — a v1-satisfying row family yields a `Satisfied2` witness of the
NARROW-graduated descriptor, over the constructed narrow tables, with the EMPTY memory boundary. The
byte-identical mirror of `graduateV1_complete` (`graduateV1 -> graduateV1Narrow`, `v2TraceOf ->
v2TraceOfNarrow`): the hash sites discharge through the gathered NARROW chip table `chipLogOfNarrow`. -/
theorem graduateV1Narrow_complete (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true)
    (hsat : ∀ i, i < rows.length →
      satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length)) :
    Satisfied2 hash (graduateV1Narrow d (sitesFit_admitted (graduable_spec hgrad).2.1))
      (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      (v2TraceOfNarrow d (sitesFit_admitted (graduable_spec hgrad).2.1) rows pub) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    unfold graduateV1Narrow at hc
    simp only [List.mem_append, List.mem_map, mem_narrowSites] at hc
    rcases hc with (⟨c₀, hc₀, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨r, hr, rfl⟩
    · exact (hsat i hi).1 c₀ hc₀
    · -- narrow chip lookup: membership in the gathered narrow table, by construction
      have hi' : i < rows.length := hi
      show (siteLookupNarrow d.hashSites s (sitesFit_admitted hfit s hs)).tuple.map
          (·.eval (envAt (v2TraceOfNarrow d (sitesFit_admitted hfit) rows pub) i).loc)
        ∈ chipLogOfNarrow d.hashSites (sitesFit_admitted hfit) rows
      have hloc : (envAt (v2TraceOfNarrow d (sitesFit_admitted hfit) rows pub) i).loc = rows[i] := by
        simp [v2TraceOfNarrow, envAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      rw [hloc]
      unfold chipLogOfNarrow
      rw [List.mem_flatMap]
      exact ⟨rows[i], List.getElem_mem hi',
        List.mem_map.mpr ⟨⟨s, hs⟩, List.mem_attach _ _, rfl⟩⟩
    · -- range lookup: completeness of the limb table (IDENTICAL to `graduateV1_complete`)
      obtain ⟨w, bits⟩ := r
      have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
      subst hb
      exact lookup_range_complete BAL_LIMB_BITS (v2TFNarrow d (sitesFit_admitted hfit) rows) rfl
        (envAt (v2TraceOfNarrow d (sitesFit_admitted hfit) rows pub) i) w ((hsat i hi).2.2 ⟨w, BAL_LIMB_BITS⟩ hr)
  · intro i hi; trivial
  · intro i hi r hr
    have hnil : (graduateV1Narrow d).ranges = [] := rfl
    rw [hnil] at hr
    cases hr
  · intro op hop
    rw [memLog_graduateV1Narrow] at hop
    cases hop
  · rw [memLog_graduateV1Narrow]
    trivial
  · rw [memLog_graduateV1Narrow]
    exact memCheck_nil _ _
  · rw [memLog_graduateV1Narrow]
    rfl
  · rw [mapLog_graduateV1Narrow]
    rfl

/-- **`graduateV1Narrow_faithful` — THE NARROW RE-ANCHOR ROUND TRIP.** A row family satisfies the v1
descriptor on every window IFF some multi-table witness over it (sound NARROW chip table, faithful
range table) satisfies the NARROW-graduated v2 descriptor. Byte-identical mirror of
`graduateV1_faithful` (`graduateV1 -> graduateV1Narrow`, `ChipTableSound -> ChipTableSoundNarrow`,
`.poseidon2 -> poseidon2narrow`): nothing gained, nothing lost — the narrow emission target moved; the
semantics did not. -/
theorem graduateV1Narrow_faithful (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true) :
    (∀ i, i < rows.length →
        satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length))
      ↔ ∃ t : VmTrace, t.rows = rows ∧ t.pub = pub
          ∧ ChipTableSoundNarrow hash (t.tf poseidon2narrow)
          ∧ t.tf .range = rangeRows BAL_LIMB_BITS
          ∧ Satisfied2 hash (graduateV1Narrow d (sitesFit_admitted (graduable_spec hgrad).2.1))
              (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] t := by
  constructor
  · intro h
    refine ⟨v2TraceOfNarrow d (sitesFit_admitted (graduable_spec hgrad).2.1) rows pub, rfl, rfl,
      chipLogOfNarrow_sound hash d rows pub hgrad h, ?_,
      graduateV1Narrow_complete hash d rows pub hgrad h⟩
    rw [v2TraceOfNarrow_tf]
    exact v2TFNarrow_range d _ rows
  · rintro ⟨t, rfl, rfl, hchip, hrange, hsat⟩
    exact graduateV1Narrow_sound hash d _ _ _ t hchip hrange hgrad hsat

#assert_axioms go_of_siteLookupsNarrow
#assert_axioms siteLookupsNarrow_sound
#assert_axioms graduateV1Narrow_sound
#assert_axioms graduateV1Narrow_width_shrink
#assert_axioms constraints_graduateV1Narrow_shapes
#assert_axioms memLog_graduateV1Narrow
#assert_axioms mapLog_graduateV1Narrow
#assert_axioms go_siteLookups_complete_narrow
#assert_axioms chipLogOfNarrow_sound
#assert_axioms graduateV1Narrow_complete
#assert_axioms graduateV1Narrow_faithful

end Dregg2.Circuit.Emit.EffectVmEmitV2
