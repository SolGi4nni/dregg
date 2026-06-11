/-
# Dregg2.Circuit.Emit.EffectVmEmitV2 — the FAITHFULNESS RE-ANCHOR onto descriptor IR v2.

`DescriptorIR2` (the EPOCH keystone) supplies the multi-table grammar: chip `Lookup`s for hash
sites, range `Lookup`s for range teeth, `MemOp`s for state accesses, `MapOp`s for boundary map
reconciliations — with `Satisfied2` as the multi-table denotation. THIS module moves the
PER-EFFECT EMISSION onto it:

  * **`graduateV1`** — the generic re-anchor: a v1 `EffectVmDescriptor`'s hash sites become
    Poseidon2-chip lookups (`siteLookup`), its range teeth become range-table lookups, its
    arithmetic/transition/boundary/PI constraints embed as `.base`. The graduated descriptor
    carries NO legacy `hashSites`/`ranges` — the v2 wire is lookup-shaped throughout.
  * **`graduateV1_sound`** — the keystone: a `Satisfied2` witness of the graduated descriptor
    (against a sound chip table + the faithful range table) yields the FULL v1 denotation
    `satisfiedVm` on every row window. So EVERY existing per-effect faithfulness /
    anti-ghost / full-state theorem (all stated against `satisfiedVm`) RE-STATES against v2
    by one composition — the refinement tower's shape is unchanged, only the emission target
    moved. The ordered-hash-site walk survives the move by the `go_of_siteLookups` induction
    (digest-chaining via result columns, the well-formedness `sitesWF` making earlier-site
    references meaningful).
  * **`graduateV1_complete`** + **`graduateV1_faithful`** — the round trip: a v1-satisfying
    row family CONSTRUCTS a satisfying multi-table v2 witness (`v2TraceOf`: the chip table is
    the gathered genuine permutation rows, sound BY CONSTRUCTION; memory/map tables empty).
    Nothing is gained or lost in the re-anchor.
  * **The SWEEP** (§6) — graduated v2 descriptors for the whole graduation cohort (the
    EmitGraduate 16 + attenuate + the 8 setField slots), each `#guard`-checked `graduable`;
    re-anchored corner theorems for the validated TRANSFER reference
    (`transferV2_pins_intent`) and the economic family (`burnV2_full_sound`,
    `mintV2_full_sound`).
  * **NEWLY EXPRESSIBLE I (§7)** — the Attenuate cap-crown phase-B circuit leg
    (`attenuateVmDescriptor2`): held-capability MEMBERSHIP authenticated against the before
    `cap_root` (a `MapOp.read` — under CR the row cannot lie: `opensTo_functional`), the post
    `cap_root` pinned to the GENUINE sorted write (`MapOp.write`), and `granted ⊑ held` as a
    BITWISE-SUBMASK lookup into the custom subset table (`subsetTable`,
    `subsetTable_mem_iff`) — the lattice compare the v1 IR could not express
    (`attenuateV2_non_amp`, `attenuateV2_held_determined`).
  * **NEWLY EXPRESSIBLE II (§8)** — SetField with a DYNAMIC slot index
    (`setFieldDynVmDescriptor2`): the field write is a `MemOp` at address `param[SLOT]` (one
    descriptor, not 8 per-slot circuits), the slot bounded by the degree-8 product gate, and
    the write→read transport carried by the PROVED memory argument with ZERO hashing
    (`setFieldDyn_readback_genuine` via `satisfied2_mem_consistent` = Blum applied).

## Honest boundary notes (do NOT over-read)

  * The custom subset table's CONTENTS are pinned by hypothesis (`t.tf (.custom SUBMASK_TID) =
    subsetTable MASK_BITS`) in the §7 theorems: `TableDef.RowSemantics` has no tag for emitted
    custom-table contents yet, so the wire manifest for custom tables is a small IR follow-up
    (the Rust assembly must generate the subset rows from the declared id). The chip / range
    table pins are the same shape (`ChipTableSound` / `tf .range = rangeRows`) — those are the
    per-table AIR faithfulness obligations the multi-table assembly discharges.
  * `setFieldDynVmDescriptor2` is the POST-FLAG-DAY shape: the 8 user-field cells live in the
    memory table at addresses `0..7` (the witness-generation restructure), not in per-slot
    state columns. The full-state spec triangle for the dynamic form composes with the memory
    argument; the per-slot static descriptors remain valid and graduated in the sweep.
  * `MASK_BITS := 30` matches the deployed effect-mask width; the deployed AIR splits masks
    into `mask_lo`/`mask_hi` limbs (`circuit/tests/effect_vm_attenuate_non_amp.rs`) — the
    two-limb split is a wire-layout choice over the SAME subset relation; the Lean denotation
    states it unsplit.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY
as the named `Poseidon2SpongeCR` (via the imported map-op functionality theorems); memory
consistency is the PROVED `memcheck_sound` import. No `sorry`, no `native_decide`. NEW file;
imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
-- NOT imported: Dregg2.Circuit.Emit.EffectVmEmitBridgeMint — that module does not build in the
-- current shared tree (`Unknown identifier recBalCredit_correct` at its line 315: its Exec-side
-- dependency moved under it mid-epoch; pre-existing, not introduced here). Its graduation is
-- one `graduateV1` line + one `graduable` #guard once its own lane repairs it.
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Emit.EffectVmEmitIntroduce
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Emit.EffectVmEmitSetField

namespace Dregg2.Circuit.Emit.EffectVmEmitV2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — Graduation side conditions (decidable, `#guard`-checkable per descriptor).

`sitesWF`: every `.digest k` input references a STRICTLY EARLIER site (the deterministic
`hash_sites()` order contract — the property that makes the result-column chaining meaningful).
`sitesFit`: every site's input list fits the chip rate. `graduable` bundles them with the
range-bits uniformity (the shared range table is the 30-bit limb table). -/

/-- One input is well-formed at site index `idx`: a `.digest k` reference must be earlier. -/
def siteInputWF (idx : Nat) : HashInput → Bool
  | .digest k => decide (k < idx)
  | _ => true

/-- All sites from index `idx` on reference only digests `<` their own index. -/
def sitesWFAux : Nat → List VmHashSite → Bool
  | _, [] => true
  | idx, s :: ss => s.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) ss

/-- The whole ordered site list is reference-well-formed. -/
def sitesWF (sites : List VmHashSite) : Bool := sitesWFAux 0 sites

/-- Every site's input tuple fits the chip rate. -/
def sitesFit (sites : List VmHashSite) : Bool :=
  sites.all fun s => decide (s.inputs.length ≤ CHIP_RATE)

/-- A v1 descriptor is GRADUABLE: well-formed site references, chip-rate fit, and every range
tooth at the shared limb width (`BAL_LIMB_BITS = 30` — the whole registry, surveyed). -/
def graduable (d : EffectVmDescriptor) : Bool :=
  sitesWF d.hashSites && sitesFit d.hashSites
    && d.ranges.all (fun r => r.bits == BAL_LIMB_BITS)

/-- Unpack the decidable `graduable` check into the three propositional side conditions. -/
theorem graduable_spec {d : EffectVmDescriptor} (h : graduable d = true) :
    sitesWF d.hashSites = true ∧ sitesFit d.hashSites = true
      ∧ ∀ r ∈ d.ranges, r.bits = BAL_LIMB_BITS := by
  unfold graduable at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun r hr => ?_⟩
  have := List.all_eq_true.mp h3 r hr
  simpa using this

/-! ## §2 — `graduateV1`: the re-anchored emission.

Hash sites → chip lookups (`siteLookup`, digest chaining via result columns); range teeth →
range-table lookups; the v1 constraint list embeds whole. The graduated descriptor carries NO
legacy `hashSites`/`ranges`: its v2 wire (`emitVmJson2`) is lookup-shaped throughout. -/

/-- The range-table lookup replacing a v1 `VmRange` tooth. -/
def rangeLookup (r : VmRange) : Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := .range, tuple := [.var r.wire] }

/-- **`graduateV1`** — re-anchor a v1 descriptor onto IR v2: constraints embed, every hash site
becomes a chip lookup, every range tooth becomes a range lookup; the five EPOCH tables are
declared; the legacy carriers empty. -/
def graduateV1 (d : EffectVmDescriptor) : EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth
  , piCount     := d.piCount
  , tables      := v2Tables d.traceWidth
  , constraints :=
      d.constraints.map .base
        ++ d.hashSites.map (fun s => .lookup (siteLookup d.hashSites s))
        ++ d.ranges.map (fun r => .lookup (rangeLookup r))
  , hashSites   := []
  , ranges      := [] }

/-- Every graduated constraint is a `.base` or a `.lookup` (no mem/map ops — those are the
NEWLY-EXPRESSIBLE sections' additions, not the v1 re-anchor's). -/
theorem constraints_graduateV1_shapes (d : EffectVmDescriptor) :
    ∀ c ∈ (graduateV1 d).constraints,
      (∃ c₀, c = .base c₀) ∨ (∃ l, c = .lookup l) := by
  intro c hc
  unfold graduateV1 at hc
  simp only [List.mem_append, List.mem_map] at hc
  rcases hc with (⟨c₀, _, rfl⟩ | ⟨s, _, rfl⟩) | ⟨r, _, rfl⟩
  · exact Or.inl ⟨c₀, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- A graduated v1 descriptor declares no mem ops. -/
theorem memOpsOf_graduateV1 (d : EffectVmDescriptor) : memOpsOf (graduateV1 d) = [] := by
  unfold memOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1_shapes d c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- A graduated v1 descriptor declares no map ops. -/
theorem mapOpsOf_graduateV1 (d : EffectVmDescriptor) : mapOpsOf (graduateV1 d) = [] := by
  unfold mapOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1_shapes d c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- A graduated v1 descriptor's memory log is empty. -/
theorem memLog_graduateV1 (d : EffectVmDescriptor) (t : VmTrace) :
    memLog (graduateV1 d) t = [] := by
  unfold memLog
  rw [memOpsOf_graduateV1]
  simp

/-- A graduated v1 descriptor's map-ops log is empty. -/
theorem mapLog_graduateV1 (d : EffectVmDescriptor) (t : VmTrace) :
    mapLog (graduateV1 d) t = [] := by
  unfold mapLog
  rw [mapOpsOf_graduateV1]
  simp

/-! ## §3 — The ordered-site induction: chip lookups ⟹ the v1 hash-site walk.

The v1 denotation `siteHoldsAll` walks the ordered site list with a digest ACCUMULATOR (site `i`
reads digests `[0..i)`); the graduated form is one chip lookup per site, the `.digest k` input
translated to the EARLIER site's result COLUMN. The bridge: as long as the processed prefix's
result columns carry the accumulated digests (the invariant the induction maintains), the
translated tuple evaluates to exactly the resolved inputs — so `chip_lookup_sound` forces each
result column to the genuine digest, re-establishing the invariant one site further. -/

/-- The translated input evaluates to the v1-resolved input, given the prefix invariant. -/
theorem toExpr_eval_eq_resolve (env : VmRowEnv) (all : List VmHashSite) (acc : List ℤ)
    (inp : HashInput)
    (hwf : siteInputWF acc.length inp = true)
    (hacc : ∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) :
    (HashInput.toExpr all inp).eval env.loc = inp.resolve env acc := by
  cases inp with
  | col c => rfl
  | digest k =>
    have hk : k < acc.length := by simpa [siteInputWF] using hwf
    simpa [HashInput.toExpr, HashInput.resolve, EmittedExpr.eval] using hacc k hk
  | zero => rfl

/-- The translated input TUPLE evaluates to the v1-resolved input list. -/
theorem siteTuple_eval_resolved (env : VmRowEnv) (all : List VmHashSite) (acc : List ℤ)
    (s : VmHashSite)
    (hwfs : s.inputs.all (siteInputWF acc.length) = true)
    (hacc : ∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) :
    (s.inputs.map (HashInput.toExpr all)).map (·.eval env.loc) = s.resolvedInputs env acc := by
  rw [List.map_map]
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro inp hin
  exact toExpr_eval_eq_resolve env all acc inp (List.all_eq_true.mp hwfs inp hin) hacc

/-- The prefix-extension step shared by both inductions: pushing the freshly-established digest
onto the accumulator preserves the result-column invariant. -/
theorem hacc_extend (env : VmRowEnv) (pre ss : List VmHashSite) (s : VmHashSite) (acc : List ℤ)
    (d : ℤ) (all : List VmHashSite)
    (hall : all = pre ++ s :: ss)
    (hlen : acc.length = pre.length)
    (hacc : ∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0)
    (hd : env.loc s.digestCol = d) :
    ∀ k, k < (acc ++ [d]).length →
      env.loc ((all.getD k default).digestCol) = (acc ++ [d]).getD k 0 := by
  intro k hk
  have hk' : k < acc.length + 1 := by simpa using hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk'' | rfl
  · have h2 : (acc ++ [d]).getD k 0 = acc.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk'']
    rw [h2]
    exact hacc k hk''
  · have h1 : all.getD acc.length default = s := by
      rw [hall, hlen, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (le_refl pre.length)]
      simp
    have h2 : (acc ++ [d]).getD acc.length 0 = d := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl acc.length)]
      simp
    rw [h1, h2]
    exact hd

/-- **The soundness induction.** With the prefix invariant established, the suffix's chip
lookups (against a sound chip table) realize the v1 site walk from the current accumulator. -/
theorem go_of_siteLookups (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (env : VmRowEnv) (all : List VmHashSite)
    (rest : List VmHashSite) :
    ∀ (pre : List VmHashSite) (acc : List ℤ),
      all = pre ++ rest →
      acc.length = pre.length →
      (∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) →
      sitesWFAux acc.length rest = true →
      (∀ s ∈ rest, s.inputs.length ≤ CHIP_RATE) →
      (∀ s ∈ rest, (siteLookup all s).tuple.map (·.eval env.loc) ∈ tbl) →
      siteHoldsAll.go hash env acc rest := by
  induction rest with
  | nil => intro pre acc _ _ _ _ _ _; trivial
  | cons s ss ih =>
    intro pre acc hall hlen hacc hwf hfit hlk
    simp only [sitesWFAux, Bool.and_eq_true] at hwf
    obtain ⟨hwfs, hwfss⟩ := hwf
    have hchip := chip_lookup_sound hash tbl hSound env.loc
      (s.inputs.map (HashInput.toExpr all)) s.digestCol
      (by simpa [List.length_map] using hfit s List.mem_cons_self)
      (hlk s List.mem_cons_self)
    rw [siteTuple_eval_resolved env all acc s hwfs hacc] at hchip
    refine ⟨hchip, ?_⟩
    apply ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)])
    · rw [hall, List.append_assoc]
      rfl
    · simp [hlen]
    · exact hacc_extend env pre ss s acc _ all hall hlen hacc hchip
    · simpa using hwfss
    · exact fun s' hs' => hfit s' (List.mem_cons_of_mem s hs')
    · exact fun s' hs' => hlk s' (List.mem_cons_of_mem s hs')

/-- **`siteLookups_sound`** — the whole ordered family: per-site chip lookups against a sound
chip table ⟹ the full v1 hash-site denotation `siteHoldsAll`. -/
theorem siteLookups_sound (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (env : VmRowEnv) (sites : List VmHashSite)
    (hwf : sitesWF sites = true)
    (hfit : ∀ s ∈ sites, s.inputs.length ≤ CHIP_RATE)
    (hlk : ∀ s ∈ sites, (siteLookup sites s).tuple.map (·.eval env.loc) ∈ tbl) :
    siteHoldsAll hash env sites :=
  go_of_siteLookups hash tbl hSound env sites sites [] [] rfl rfl
    (fun k hk => absurd hk (by simp)) hwf hfit hlk

/-! ## §4 — `graduateV1_sound`: THE re-anchor keystone.

A `Satisfied2` witness of the graduated descriptor — against a sound chip table and the faithful
range table — yields the FULL v1 denotation `satisfiedVm` on every row window. Every per-effect
faithfulness theorem composes through this. -/

theorem graduateV1_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (graduateV1 d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  intro i hi
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the v1 constraints, embedded
    intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1 d).constraints := by
      unfold graduateV1
      simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrow _ hmem
  · -- the hash sites, via the chip-lookup induction
    apply siteLookups_sound hash (t.tf .poseidon2) hchip (envAt t i) d.hashSites hwf
    · intro s hs
      exact of_decide_eq_true (List.all_eq_true.mp hfit s hs)
    · intro s hs
      have hmem : VmConstraint2.lookup (siteLookup d.hashSites s)
          ∈ (graduateV1 d).constraints := by
        unfold graduateV1
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
      exact hrow _ hmem
  · -- the range teeth, via the range-table lookup
    intro r hr
    obtain ⟨w, bits⟩ := r
    have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
    subst hb
    have hmem : VmConstraint2.lookup (rangeLookup ⟨w, BAL_LIMB_BITS⟩)
        ∈ (graduateV1 d).constraints := by
      unfold graduateV1
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨⟨w, BAL_LIMB_BITS⟩, hr, rfl⟩
    exact lookup_replaces_range BAL_LIMB_BITS t.tf hrange (envAt t i) w (hrow _ hmem)

/-! ## §5 — Completeness: a v1-satisfying row family BUILDS a satisfying v2 witness.

The chip table is the gathered genuine permutation rows (`chipLogOf`), sound BY CONSTRUCTION
(`chipLogOf_sound` — the mirror induction `go_siteLookups_complete`); the range table is the
faithful limb table; memory/map tables are empty (the graduated v1 face is inert there). So the
re-anchor loses nothing: `graduateV1_faithful` is the round trip. -/

/-- The row environment of a bare row family (what `envAt` reads — trace-family-free). -/
def envOf (rows : List Assignment) (pub : Assignment) (i : Nat) : VmRowEnv :=
  { loc := rows.getD i zeroAsg, nxt := rows.getD (i + 1) zeroAsg, pub := pub }

/-- The gathered chip rows: every row's every site lookup tuple, evaluated. -/
def chipLogOf (sites : List VmHashSite) (rows : List Assignment) : Table :=
  rows.flatMap fun a => sites.map fun s => (siteLookup sites s).tuple.map (·.eval a)

/-- **The completeness induction.** Under the same prefix invariant, a v1 site walk makes every
suffix site's lookup tuple evaluate to a GENUINE chip row. -/
theorem go_siteLookups_complete (hash : List ℤ → ℤ) (env : VmRowEnv) (all : List VmHashSite)
    (rest : List VmHashSite) :
    ∀ (pre : List VmHashSite) (acc : List ℤ),
      all = pre ++ rest →
      acc.length = pre.length →
      (∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) →
      sitesWFAux acc.length rest = true →
      siteHoldsAll.go hash env acc rest →
      ∀ s ∈ rest, ∃ ins : List ℤ, ins.length = s.inputs.length ∧
        (siteLookup all s).tuple.map (·.eval env.loc) = chipRow hash ins := by
  induction rest with
  | nil => intro pre acc _ _ _ _ _ s hs; cases hs
  | cons s ss ih =>
    intro pre acc hall hlen hacc hwf hgo s' hs'
    simp only [sitesWFAux, Bool.and_eq_true] at hwf
    obtain ⟨hwfs, hwfss⟩ := hwf
    obtain ⟨hd, hgo'⟩ := hgo
    rcases List.mem_cons.mp hs' with rfl | hs''
    · -- the head site: its tuple IS the genuine chip row of its resolved inputs
      refine ⟨s'.resolvedInputs env acc, by simp [VmHashSite.resolvedInputs], ?_⟩
      have hev : (chipLookupTuple (s'.inputs.map (HashInput.toExpr all)) s'.digestCol).map
            (·.eval env.loc)
          = ((s'.inputs.map (HashInput.toExpr all)).length : ℤ)
            :: padTo CHIP_RATE ((s'.inputs.map (HashInput.toExpr all)).map (·.eval env.loc))
            ++ [env.loc s'.digestCol] := by
        simp [chipLookupTuple, List.map_cons, List.map_append, map_eval_padToE,
          EmittedExpr.eval]
      show (chipLookupTuple (s'.inputs.map (HashInput.toExpr all)) s'.digestCol).map
          (·.eval env.loc) = chipRow hash (s'.resolvedInputs env acc)
      rw [hev, siteTuple_eval_resolved env all acc s' hwfs hacc, hd]
      unfold chipRow
      simp [VmHashSite.resolvedInputs, List.length_map]
    · -- a later site: recurse with the extended prefix
      exact ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)])
        (by rw [hall, List.append_assoc]; rfl)
        (by simp [hlen])
        (hacc_extend env pre ss s acc _ all hall hlen hacc hd)
        (by simpa using hwfss)
        hgo' s' hs''

/-- The gathered chip table is SOUND by construction. -/
theorem chipLogOf_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true)
    (hsat : ∀ i, i < rows.length →
      satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length)) :
    ChipTableSound hash (chipLogOf d.hashSites rows) := by
  obtain ⟨hwf, hfit, _⟩ := graduable_spec hgrad
  intro r hr
  unfold chipLogOf at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨a, ha, hr⟩ := hr
  rw [List.mem_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hloc : (envOf rows pub i).loc = rows[i] := by
    simp [envOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hgo : siteHoldsAll hash (envOf rows pub i) d.hashSites := (hsat i hi).2.1
  obtain ⟨ins, hlen, heq⟩ := go_siteLookups_complete hash (envOf rows pub i) d.hashSites
    d.hashSites [] [] rfl rfl (fun k hk => absurd hk (by simp)) hwf hgo s hs
  rw [hloc] at heq
  refine ⟨ins, ?_, heq.symm ▸ rfl⟩
  rw [hlen]
  exact of_decide_eq_true (List.all_eq_true.mp hfit s hs)

/-- The constructed trace family: gathered chip rows, the faithful range table, empty
memory/map/custom tables, main unconstrained. -/
def v2TF (d : EffectVmDescriptor) (rows : List Assignment) : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => chipLogOf d.hashSites rows
  | .range => rangeRows BAL_LIMB_BITS
  | _ => []

/-- The constructed multi-table witness over a v1-satisfying row family. -/
def v2TraceOf (d : EffectVmDescriptor) (rows : List Assignment) (pub : Assignment) : VmTrace :=
  { rows := rows, pub := pub, tf := v2TF d rows }

/-- The constructed trace's family, projected (kept as a `rw` target: a bare `rfl` at the
`.range` USE SITE sends the unifier whnf-ing `rangeRows 30` = `List.range 2^30` — the
documented evaluation trap; the projection equation itself is cheap). -/
theorem v2TraceOf_tf (d : EffectVmDescriptor) (rows : List Assignment) (pub : Assignment) :
    (v2TraceOf d rows pub).tf = v2TF d rows := rfl

/-- The constructed family's range table is the faithful limb table. -/
theorem v2TF_range (d : EffectVmDescriptor) (rows : List Assignment) :
    v2TF d rows .range = rangeRows BAL_LIMB_BITS := rfl

/-- **`graduateV1_complete`** — a v1-satisfying row family yields a `Satisfied2` witness of the
graduated descriptor, over the constructed tables, with the EMPTY memory boundary. -/
theorem graduateV1_complete (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true)
    (hsat : ∀ i, i < rows.length →
      satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length)) :
    Satisfied2 hash (graduateV1 d) (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      (v2TraceOf d rows pub) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    unfold graduateV1 at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨c₀, hc₀, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨r, hr, rfl⟩
    · exact (hsat i hi).1 c₀ hc₀
    · -- chip lookup: membership in the gathered table, by construction
      have hi' : i < rows.length := hi
      show (siteLookup d.hashSites s).tuple.map (·.eval (envAt (v2TraceOf d rows pub) i).loc)
        ∈ chipLogOf d.hashSites rows
      have hloc : (envAt (v2TraceOf d rows pub) i).loc = rows[i] := by
        simp [v2TraceOf, envAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      rw [hloc]
      unfold chipLogOf
      rw [List.mem_flatMap]
      exact ⟨rows[i], List.getElem_mem hi', List.mem_map.mpr ⟨s, hs, rfl⟩⟩
    · -- range lookup: completeness of the limb table
      obtain ⟨w, bits⟩ := r
      have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
      subst hb
      exact lookup_range_complete BAL_LIMB_BITS (v2TF d rows) rfl
        (envAt (v2TraceOf d rows pub) i) w ((hsat i hi).2.2 ⟨w, BAL_LIMB_BITS⟩ hr)
  · intro i hi; trivial
  · intro i hi r hr
    have hnil : (graduateV1 d).ranges = [] := rfl
    rw [hnil] at hr
    cases hr
  · intro op hop
    rw [memLog_graduateV1] at hop
    cases hop
  · rw [memLog_graduateV1]
    trivial
  · rw [memLog_graduateV1]
    exact memCheck_nil _ _
  · rw [memLog_graduateV1]
    rfl
  · rw [mapLog_graduateV1]
    rfl

/-- **`graduateV1_faithful` — THE RE-ANCHOR ROUND TRIP.** A row family satisfies the v1
descriptor on every window IFF some multi-table witness over it (sound chip table, faithful
range table) satisfies the graduated v2 descriptor. Nothing gained, nothing lost: the emission
target moved; the semantics did not. -/
theorem graduateV1_faithful (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true) :
    (∀ i, i < rows.length →
        satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length))
      ↔ ∃ t : VmTrace, t.rows = rows ∧ t.pub = pub
          ∧ ChipTableSound hash (t.tf .poseidon2)
          ∧ t.tf .range = rangeRows BAL_LIMB_BITS
          ∧ Satisfied2 hash (graduateV1 d) (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] t := by
  constructor
  · intro h
    refine ⟨v2TraceOf d rows pub, rfl, rfl, chipLogOf_sound hash d rows pub hgrad h, ?_,
      graduateV1_complete hash d rows pub hgrad h⟩
    rw [v2TraceOf_tf]
    exact v2TF_range d rows
  · rintro ⟨t, rfl, rfl, hchip, hrange, hsat⟩
    exact graduateV1_sound hash d _ _ _ t hchip hrange hgrad hsat

/-! ## §6 — THE SWEEP: the graduation cohort, re-anchored.

One v2 descriptor per cohort member (`graduateV1`), each `#guard`-checked `graduable` so
`graduateV1_sound`/`_complete`/`_faithful` apply by `by decide` discharge. The re-anchored
corner theorems are spelled for the validated TRANSFER reference and the economic family; every
other member's existing `satisfiedVm`-shaped theorem composes with `graduateV1_sound`
identically (one application). -/

def transferVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitTransfer.transferVmDescriptor
def burnVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitBurn.burnVmDescriptor
def mintVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitMint.mintVmDescriptor
def noteSpendVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitNoteSpend.noteSpendVmDescriptor
def noteCreateVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitNoteCreate.noteCreateVmDescriptor
def cellSealVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitCellSeal.cellSealVmDescriptor
def cellDestroyVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitCellDestroy.cellDestroyVmDescriptor
def refusalVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitRefusal.refusalVmDescriptor
def setPermsVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitSetPermissions.setPermsVmDescriptor
def setVKVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitSetVK.setVKVmDescriptor
def exerciseVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitExercise.exerciseVmDescriptor
def pipelinedSendVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
def refreshVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitRefreshDelegation.refreshVmDescriptor
def incrementNonceVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
def revokeVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitRevokeDelegation.revokeVmDescriptor
def introduceVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitIntroduce.introduceVmDescriptor
def attenuateVmDescriptor2Base : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitAttenuateA.attenuateVmDescriptor
def setFieldVmDescriptor2 (slot : Fin 8) : EffectVmDescriptor2 :=
  graduateV1 (EffectVmEmitSetField.setFieldVmDescriptor slot)

-- Every cohort member passes the graduation side conditions (so the §4/§5 theorems apply).
#guard graduable EffectVmEmitTransfer.transferVmDescriptor
#guard graduable EffectVmEmitBurn.burnVmDescriptor
#guard graduable EffectVmEmitMint.mintVmDescriptor
#guard graduable EffectVmEmitNoteSpend.noteSpendVmDescriptor
#guard graduable EffectVmEmitNoteCreate.noteCreateVmDescriptor
#guard graduable EffectVmEmitCellSeal.cellSealVmDescriptor
#guard graduable EffectVmEmitCellDestroy.cellDestroyVmDescriptor
#guard graduable EffectVmEmitRefusal.refusalVmDescriptor
#guard graduable EffectVmEmitSetPermissions.setPermsVmDescriptor
#guard graduable EffectVmEmitSetVK.setVKVmDescriptor
#guard graduable EffectVmEmitExercise.exerciseVmDescriptor
#guard graduable EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
#guard graduable EffectVmEmitRefreshDelegation.refreshVmDescriptor
#guard graduable EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
#guard graduable EffectVmEmitRevokeDelegation.revokeVmDescriptor
#guard graduable EffectVmEmitIntroduce.introduceVmDescriptor
#guard graduable EffectVmEmitAttenuateA.attenuateVmDescriptor
#guard (List.finRange 8).all fun slot =>
  graduable (EffectVmEmitSetField.setFieldVmDescriptor slot)

/-- **The validated reference, re-anchored.** A one-row `Satisfied2` witness of the graduated
TRANSFER descriptor — sound chip table, faithful range table — realizes `TransferRowIntent` and
publishes the post-state commitment: `transferVmDescriptor_pins_intent`, now against v2. -/
theorem transferV2_pins_intent (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hone : t.rows.length = 1)
    (hrow : EffectVmEmitTransfer.IsTransferRow (envAt t 0))
    (hsat : Satisfied2 hash transferVmDescriptor2 minit mfin maddrs t) :
    EffectVmEmitTransfer.TransferRowIntent (envAt t 0)
    ∧ (envAt t 0).loc (saCol state.STATE_COMMIT) = (envAt t 0).pub pi.NEW_COMMIT := by
  have h := graduateV1_sound hash EffectVmEmitTransfer.transferVmDescriptor
    minit mfin maddrs t hchip hrange (by decide) hsat 0 (by rw [hone]; exact Nat.one_pos)
  rw [hone] at h
  exact EffectVmEmitTransfer.transferVmDescriptor_pins_intent hash _ hrow h

/-- **The economic family, re-anchored (burn).** `burnDescriptor_full_sound` against v2: a
one-row graduated-burn witness forces the structured `CellBurnSpec` and the published
commitment. -/
theorem burnV2_full_sound (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hone : t.rows.length = 1)
    (hrow : EffectVmEmitBurn.IsBurnRow (envAt t 0))
    (pre post : EffectVmEmitTransferSound.CellState) (amt : ℤ)
    (henc : EffectVmEmitBurn.RowEncodes (envAt t 0) pre amt post)
    (hsat : Satisfied2 hash burnVmDescriptor2 minit mfin maddrs t) :
    EffectVmEmitBurn.CellBurnSpec pre amt post
    ∧ post.commit = (envAt t 0).pub pi.NEW_COMMIT := by
  have h := graduateV1_sound hash EffectVmEmitBurn.burnVmDescriptor
    minit mfin maddrs t hchip hrange (by decide) hsat 0 (by rw [hone]; exact Nat.one_pos)
  rw [hone] at h
  exact EffectVmEmitBurn.burnDescriptor_full_sound hash _ hrow pre post amt henc h

/-- **The economic family, re-anchored (mint).** `mintDescriptor_full_sound` against v2. -/
theorem mintV2_full_sound (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hone : t.rows.length = 1)
    (pre post : EffectVmEmitTransferSound.CellState) (amt : ℤ)
    (henc : EffectVmEmitMint.RowEncodes (envAt t 0) pre amt post)
    (hsat : Satisfied2 hash mintVmDescriptor2 minit mfin maddrs t) :
    EffectVmEmitMint.CellMintSpec pre amt post
    ∧ post.commit = (envAt t 0).pub pi.NEW_COMMIT := by
  have h := graduateV1_sound hash EffectVmEmitMint.mintVmDescriptor
    minit mfin maddrs t hchip hrange (by decide) hsat 0 (by rw [hone]; exact Nat.one_pos)
  rw [hone] at h
  exact EffectVmEmitMint.mintDescriptor_full_sound hash _ pre post amt henc h

/-! ## §7 — NEWLY EXPRESSIBLE I: the Attenuate cap-crown phase-B circuit leg.

The v1 IR could only PIN the post `cap_root` to a witness-supplied parameter (the
`EffectVmEmitAttenuateA` IR GAP: no in-circuit cap-table opening). The v2 `MapOp` IS that
opening: the held capability is READ out of the before cap-map (authenticated — under CR the
row cannot claim a value the root does not hold), the post root is the GENUINE sorted write of
the kept mask, and `granted ⊑ held` is a BITWISE-SUBMASK lookup into the subset table — the
lattice compare that blocked graduation, now a first-class constraint. -/

/-- The held-capability map key parameter column. -/
def CAP_KEY : Nat := 3
/-- The held rights-mask parameter column (authenticated against the before `cap_root`). -/
def HELD_MASK : Nat := 4
/-- The kept (granted) rights-mask parameter column (written to the post `cap_root`). -/
def KEEP_MASK : Nat := 5
/-- The effect-mask width (the deployed mask width; the deployed AIR splits this into
`mask_lo`/`mask_hi` limbs — same relation, two-limb wire layout). -/
def MASK_BITS : Nat := 30
/-- The custom-table id of the subset (submask) table. -/
def SUBMASK_TID : Nat := 0

/-- **The subset table**: rows `[a, b]` with `a &&& b = a` (i.e. `a ⊑ b` in the mask lattice),
both below `2^bits`. The custom-table realization of the lattice compare. -/
def subsetTable (bits : Nat) : Table :=
  (List.range (2 ^ bits)).flatMap fun (b : ℕ) =>
    ((List.range (2 ^ bits)).filter (fun (a : ℕ) => a &&& b == a)).map
      fun (a : ℕ) => [(a : ℤ), (b : ℤ)]

/-- Subset-table membership, characterized: `[x, y]` is a row iff `x`/`y` are mask naturals
with `x ⊑ y` bitwise. -/
theorem subsetTable_mem_iff (bits : Nat) (x y : ℤ) :
    [x, y] ∈ subsetTable bits ↔
      ∃ a b : Nat, a < 2 ^ bits ∧ b < 2 ^ bits ∧ a &&& b = a
        ∧ x = (a : ℤ) ∧ y = (b : ℤ) := by
  unfold subsetTable
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨b, hb, hmem⟩
    rw [List.mem_map] at hmem
    obtain ⟨a, ha, heq⟩ := hmem
    rw [List.mem_filter] at ha
    obtain ⟨ha, hsub⟩ := ha
    rw [List.mem_range] at ha
    rw [List.mem_range] at hb
    injection heq with h1 h2
    injection h2 with h2 _
    exact ⟨a, b, ha, hb, by simpa using hsub, h1.symm, h2.symm⟩
  · rintro ⟨a, b, ha, hb, hsub, rfl, rfl⟩
    refine ⟨b, List.mem_range.mpr hb, ?_⟩
    rw [List.mem_map]
    exact ⟨a, List.mem_filter.mpr ⟨List.mem_range.mpr ha, by simpa using hsub⟩, rfl⟩

-- Non-vacuity (witness TRUE and FALSE): 1 ⊑ 3 is a row; 2 ⋢ 1 is not; the strict pair refutes.
#guard ([1, 3] : List ℤ) ∈ subsetTable 2
#guard ([0, 0] : List ℤ) ∈ subsetTable 2
#guard ¬ (([2, 1] : List ℤ) ∈ subsetTable 2)
#guard ¬ (([3, 1] : List ℤ) ∈ subsetTable 2)

/-- The held-capability MEMBERSHIP read: the before `cap_root` opens at `param[CAP_KEY]` to
`param[HELD_MASK]` (root unchanged — a read). Guarded by the attenuate selector. -/
def heldReadOp : MapOp :=
  { guard   := .var EffectVmEmitAttenuateA.selA.ATTENUATE
  , root    := .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol HELD_MASK)
  , newRoot := .var (sbCol state.CAP_ROOT)
  , op      := .read }

/-- The attenuated WRITE: the post `cap_root` is the genuine sorted insert-or-update of
`param[KEEP_MASK]` at the same key. -/
def keepWriteOp : MapOp :=
  { guard   := .var EffectVmEmitAttenuateA.selA.ATTENUATE
  , root    := .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := .var (saCol state.CAP_ROOT)
  , op      := .write }

/-- The non-amplification lookup: `(keep, held)` must be a subset-table row. (On NoOp pad rows
the parameter columns are zero and `0 ⊑ 0` is a row, so pads pass.) -/
def submaskLookup : Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := .custom SUBMASK_TID
  , tuple := [.var (prmCol KEEP_MASK), .var (prmCol HELD_MASK)] }

/-- **`attenuateVmDescriptor2`** — the graduated attenuate descriptor PLUS the phase-B circuit
leg: held-membership map-read, attenuated map-write, and the submask lookup. -/
def attenuateVmDescriptor2 : EffectVmDescriptor2 :=
  { graduateV1 EffectVmEmitAttenuateA.attenuateVmDescriptor with
    constraints :=
      (graduateV1 EffectVmEmitAttenuateA.attenuateVmDescriptor).constraints
        ++ [.mapOp heldReadOp, .mapOp keepWriteOp, .lookup submaskLookup] }

/-- **`attenuateV2_non_amp` — cap-crown phase B, the circuit leg.** On an active attenuate row
of a `Satisfied2` witness (subset table faithful): (1) the held capability IS in the before
cap-map — some sorted heap behind `cap_root` carries `(key ↦ held)`; (2) the post `cap_root` is
the GENUINE sorted write of `(key ↦ keep)`; (3) `keep ⊑ held` BITWISE — non-amplification. The
v1 IR could express none of these. -/
theorem attenuateV2_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1) :
    opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (saCol state.CAP_ROOT))
    ∧ ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hread := hrowc (.mapOp heldReadOp) (by simp [attenuateVmDescriptor2])
  have hwrite := hrowc (.mapOp keepWriteOp) (by simp [attenuateVmDescriptor2])
  have hlook := hrowc (.lookup submaskLookup) (by simp [attenuateVmDescriptor2])
  have hr := hread hactive
  have hw := hwrite hactive
  refine ⟨hr.1, hw, ?_⟩
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

/-- **The held leaf is DETERMINED (anti-forgery, FORGERY-3 in Lean form).** Under CR, ANY
opening of the same before-root at the same key agrees with the satisfying row's held mask — a
forged held leaf with inflated rights is excluded by `opensTo_functional`. -/
theorem attenuateV2_held_determined (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1)
    (v : ℤ)
    (hclaim : opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some v)) :
    v = (envAt t i).loc (prmCol HELD_MASK) := by
  have h := (attenuateV2_non_amp hash minit mfin maddrs t hsub hsat i hi hactive).1
  have := opensTo_functional hash hCR hclaim h
  simpa using this

/-! ## §8 — NEWLY EXPRESSIBLE II: SetField with a DYNAMIC slot index.

ONE descriptor for all 8 slots: the field write is a `MemOp` at address `param[SLOT]` — the
dynamic indexing the v1 column IR could not express (it needed 8 per-slot descriptors). The
write→read transport is carried by the PROVED memory argument (`satisfied2_mem_consistent` =
Blum applied) with ZERO hashing. POST-FLAG-DAY shape: the 8 user-field cells are memory
addresses `0..7`. -/

/-- The dynamic slot-index parameter column. -/
def SLOT : Nat := 1
/-- The written value parameter column (`param.AMOUNT`, the same carrier the static setField
uses). -/
def NEW_VAL : Nat := EffectVmEmitSetField.VALUE
/-- The claimed previous value witness column. -/
def PREV_VAL : Nat := 2
/-- The claimed previous serial witness column. -/
def PREV_SERIAL : Nat := 6
/-- The read-back value column (the memory argument transports the write to it). -/
def READBACK : Nat := 7

/-- The slot expression. -/
def eSlot : EmittedExpr := .var (prmCol SLOT)
/-- `slot - c` as an expression. -/
def slotMinus (c : ℤ) : EmittedExpr := .add eSlot (.const (-c))

/-- The slot-range gate body: `∏_{j<8} (slot - j)` — the degree-8 product vanishing exactly on
`{0..7}`. (On pad rows the zeroed slot column makes the first factor vanish.) -/
def gSlotRange : EmittedExpr :=
  .mul (.mul (.mul (slotMinus 0) (slotMinus 1)) (.mul (slotMinus 2) (slotMinus 3)))
       (.mul (.mul (slotMinus 4) (slotMinus 5)) (.mul (slotMinus 6) (slotMinus 7)))

/-- The slot-range gate's denotation: the slot column carries a natural `< 8`. -/
theorem gSlotRange_holds_iff (env : VmRowEnv) (isFirst isLast : Bool) :
    (VmConstraint.gate gSlotRange).holdsVm env isFirst isLast ↔
      ∃ j : Nat, j < 8 ∧ env.loc (prmCol SLOT) = (j : ℤ) := by
  simp only [VmConstraint.holdsVm, gSlotRange, slotMinus, eSlot, EmittedExpr.eval]
  constructor
  · intro h
    have hx : env.loc (prmCol SLOT) = 0 ∨ env.loc (prmCol SLOT) = 1
        ∨ env.loc (prmCol SLOT) = 2 ∨ env.loc (prmCol SLOT) = 3
        ∨ env.loc (prmCol SLOT) = 4 ∨ env.loc (prmCol SLOT) = 5
        ∨ env.loc (prmCol SLOT) = 6 ∨ env.loc (prmCol SLOT) = 7 := by
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact Or.inl (by linarith)
          · exact Or.inr (Or.inl (by linarith))
        · rcases mul_eq_zero.mp h with h | h
          · exact Or.inr (Or.inr (Or.inl (by linarith)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
        · rcases mul_eq_zero.mp h with h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))))
    rcases hx with h | h | h | h | h | h | h | h
    · exact ⟨0, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨2, by norm_num, by simpa using h⟩
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨4, by norm_num, by simpa using h⟩
    · exact ⟨5, by norm_num, by simpa using h⟩
    · exact ⟨6, by norm_num, by simpa using h⟩
    · exact ⟨7, by norm_num, by simpa using h⟩
  · rintro ⟨j, hj, hs⟩
    interval_cases j <;> rw [hs] <;> norm_num

/-- The DYNAMIC field write: a memory-table write at address `param[SLOT]`. -/
def fieldWriteOp : MemOp :=
  { guard      := .var EffectVmEmitSetField.SEL_SET_FIELD
  , addr       := .var (prmCol SLOT)
  , value      := .var (prmCol NEW_VAL)
  , prevValue  := .var (prmCol PREV_VAL)
  , prevSerial := .var (prmCol PREV_SERIAL)
  , kind       := .write }

/-- The read-back: a memory-table read at the SAME dynamic address. Its claimed prev tuple is
the write's `(value, serial 1)`; the read discipline ties `value = prevValue`, both riding the
`READBACK` column. -/
def fieldReadbackOp : MemOp :=
  { guard      := .var EffectVmEmitSetField.SEL_SET_FIELD
  , addr       := .var (prmCol SLOT)
  , value      := .var (prmCol READBACK)
  , prevValue  := .var (prmCol READBACK)
  , prevSerial := .const 1
  , kind       := .read }

/-- **`setFieldDynVmDescriptor2`** — ONE setField descriptor for all 8 slots: selector binding,
slot-range gate, the dynamic write, the read-back. -/
def setFieldDynVmDescriptor2 : EffectVmDescriptor2 :=
  { name        := "dregg-effectvm-setfield-dyn-v2"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 34
  , tables      := v2Tables EFFECT_VM_WIDTH
  , constraints :=
      [ .base (.gate gSlotRange)
      , .base (selectorGate EffectVmEmitSetField.SEL_SET_FIELD)
      , .memOp fieldWriteOp
      , .memOp fieldReadbackOp ]
  , hashSites   := []
  , ranges      := [] }

/-- The gathered memory log of a one-row active setField-dyn trace: exactly the dynamic write
followed by the read-back. -/
theorem setFieldDyn_memLog (t : VmTrace) (hone : t.rows.length = 1)
    (hactive : (envAt t 0).loc EffectVmEmitSetField.SEL_SET_FIELD = 1) :
    memLog setFieldDynVmDescriptor2 t =
      [ ⟨.write, (envAt t 0).loc (prmCol SLOT), (envAt t 0).loc (prmCol NEW_VAL),
          (envAt t 0).loc (prmCol PREV_VAL), ((envAt t 0).loc (prmCol PREV_SERIAL)).toNat⟩
      , ⟨.read, (envAt t 0).loc (prmCol SLOT), (envAt t 0).loc (prmCol READBACK),
          (envAt t 0).loc (prmCol READBACK), 1⟩ ] := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hone
  have henv : (envAt t 0).loc = a := by
    simp [envAt, ha]
  rw [henv] at hactive
  unfold memLog memOpsOf setFieldDynVmDescriptor2
  rw [ha]
  simp [MemOp.opAt?, fieldWriteOp, fieldReadbackOp, EmittedExpr.eval, hactive, henv]

/-- **The dynamic write→read transport — Blum applied, zero hashing.** On a satisfying one-row
active trace, the read-back column carries EXACTLY the written value: the memory argument
(`satisfied2_mem_consistent` = the proved `memcheck_sound`) transports the dynamic write to the
dynamic read with no authenticated structure at all. -/
theorem setFieldDyn_readback_genuine (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hone : t.rows.length = 1)
    (hactive : (envAt t 0).loc EffectVmEmitSetField.SEL_SET_FIELD = 1)
    (hsat : Satisfied2 hash setFieldDynVmDescriptor2 minit mfin maddrs t) :
    (envAt t 0).loc (prmCol READBACK) = (envAt t 0).loc (prmCol NEW_VAL) := by
  have hcons := satisfied2_mem_consistent hash _ minit mfin maddrs t hsat
  rw [setFieldDyn_memLog t hone hactive] at hcons
  obtain ⟨_, hr, _⟩ := hcons
  have := hr rfl
  simpa [MemoryChecking.step] using this

/-- The slot is genuinely bounded on every row of a satisfying trace (the dynamic index cannot
escape the field block). -/
theorem setFieldDyn_slot_bounded (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash setFieldDynVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ∃ j : Nat, j < 8 ∧ (envAt t i).loc (prmCol SLOT) = (j : ℤ) := by
  have hmem : VmConstraint2.base (.gate gSlotRange) ∈ setFieldDynVmDescriptor2.constraints := by
    simp [setFieldDynVmDescriptor2]
  have h := hsat.rowConstraints i hi _ hmem
  exact (gSlotRange_holds_iff (envAt t i) (i == 0) (i + 1 == t.rows.length)).mp h

/-! ## §9 — The v2 registry + wire/shape tripwires. -/

/-- The graduated v2 registry (the wire strings are `emitVmJson2` of each; the regeneration
executable wires this list). -/
def v2Registry : List (String × EffectVmDescriptor2) :=
  [ ("transferVmDescriptor2", transferVmDescriptor2)
  , ("burnVmDescriptor2", burnVmDescriptor2)
  , ("mintVmDescriptor2", mintVmDescriptor2)
  , ("noteSpendVmDescriptor2", noteSpendVmDescriptor2)
  , ("noteCreateVmDescriptor2", noteCreateVmDescriptor2)
  , ("cellSealVmDescriptor2", cellSealVmDescriptor2)
  , ("cellDestroyVmDescriptor2", cellDestroyVmDescriptor2)
  , ("refusalVmDescriptor2", refusalVmDescriptor2)
  , ("setPermsVmDescriptor2", setPermsVmDescriptor2)
  , ("setVKVmDescriptor2", setVKVmDescriptor2)
  , ("exerciseVmDescriptor2", exerciseVmDescriptor2)
  , ("pipelinedSendVmDescriptor2", pipelinedSendVmDescriptor2)
  , ("refreshVmDescriptor2", refreshVmDescriptor2)
  , ("incrementNonceVmDescriptor2", incrementNonceVmDescriptor2)
  , ("revokeVmDescriptor2", revokeVmDescriptor2)
  , ("introduceVmDescriptor2", introduceVmDescriptor2)
  , ("attenuateVmDescriptor2", attenuateVmDescriptor2)
  , ("setFieldDynVmDescriptor2", setFieldDynVmDescriptor2) ]
  ++ (List.finRange 8).map fun slot =>
      (s!"setFieldVmDescriptor2-{slot.val}", setFieldVmDescriptor2 slot)

#guard v2Registry.length == 26

-- The graduated transfer: 36 embedded v1 constraints + 4 chip lookups + 2 range lookups; the
-- five EPOCH tables declared; NO legacy carriers (graduation means graduation).
#guard transferVmDescriptor2.constraints.length == 36 + 4 + 2
#guard transferVmDescriptor2.tables.length == 5
#guard transferVmDescriptor2.hashSites.length == 0
#guard transferVmDescriptor2.ranges.length == 0
#guard transferVmDescriptor2.name == "dregg-effectvm-transfer-v1"
-- The enriched attenuate carries exactly the 3 phase-B constraints past its graduated base.
#guard attenuateVmDescriptor2.constraints.length
        == attenuateVmDescriptor2Base.constraints.length + 3
-- The dyn setField is mem-op shaped: 2 mem ops, no map ops.
#guard (memOpsOf setFieldDynVmDescriptor2).length == 2
#guard (mapOpsOf setFieldDynVmDescriptor2).length == 0
-- Every registry entry emits a versioned v2 wire string.
#guard v2Registry.all fun (_, d) => (emitVmJson2 d).startsWith "{\"name\":\""

#assert_axioms graduable_spec
#assert_axioms constraints_graduateV1_shapes
#assert_axioms memOpsOf_graduateV1
#assert_axioms mapOpsOf_graduateV1
#assert_axioms memLog_graduateV1
#assert_axioms mapLog_graduateV1
#assert_axioms toExpr_eval_eq_resolve
#assert_axioms siteTuple_eval_resolved
#assert_axioms hacc_extend
#assert_axioms go_of_siteLookups
#assert_axioms siteLookups_sound
#assert_axioms graduateV1_sound
#assert_axioms go_siteLookups_complete
#assert_axioms chipLogOf_sound
#assert_axioms graduateV1_complete
#assert_axioms graduateV1_faithful
#assert_axioms transferV2_pins_intent
#assert_axioms burnV2_full_sound
#assert_axioms mintV2_full_sound
#assert_axioms subsetTable_mem_iff
#assert_axioms attenuateV2_non_amp
#assert_axioms attenuateV2_held_determined
#assert_axioms gSlotRange_holds_iff
#assert_axioms setFieldDyn_memLog
#assert_axioms setFieldDyn_readback_genuine
#assert_axioms setFieldDyn_slot_bounded

end Dregg2.Circuit.Emit.EffectVmEmitV2
