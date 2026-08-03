/-
# Dregg2.Circuit.ChipNarrowLookup — E7: the narrow bus is served by the SAME chip rows

The byte-safe proof half of backlog item E7 (by-name zoo re-emit,
`docs/EFFICIENCY-BACKLOG-circuit-minimality.md`). The census (2026-07-18, pure parse of the
deployed bytes) confirmed the graduated-lane idiom is endemic in the by-name descriptors: a
single-output chip site commits the digest PLUS the 7 unused permutation lanes, and those lane
columns are referenced ONLY at output positions 18..24 of the 25-wide `TID_P2` tuple — 387 of
1857 committed columns across the by-name zoo + cross-side/bundle-fold registry members are
lanes-only or fully unreferenced.

The narrow-bus VOCABULARY and LEVER already exist (`NarrowChip.lean`: `chipLookupTupleNarrow`,
`poseidon2narrow` = wire 8 = Rust `TID_P2_NARROW`, `chip_lookup_sound_narrow`,
`siteLookupNarrow`), and the rotated tower graduates through them (`GraduateNarrow.lean`). But
everything there takes `ChipTableSoundNarrow` as a HYPOTHESIS, or builds the narrow table as a
SEPARATE log (`chipLogOfNarrow`). The DEPLOYED Rust serves both buses from ONE physical chip:
`descriptor_ir2.rs::narrow_hist` derives each 18-wide narrow tuple from the SAME
`chip_absorb_all_lanes` row that serves the 25-wide bus. What was missing is the model of THAT —
this module supplies it:

* `narrowTable` — the narrow table AS the 18-prefix of the wide chip table (one physical chip,
  two buses);
* `narrowTable_sound` — THE SAME-ROWS BRIDGE: the prefix table is `ChipTableSoundNarrow`
  whenever the wide table is `ChipTableSound`, so every `NarrowChip`/`GraduateNarrow` conclusion
  fires against the DEPLOYED single-chip serving with no extra hypothesis;
* `chip_lookup_narrow_sound_of_wide_table` — soundness preserved end-to-end: against the
  prefix-served narrow bus a narrow lookup forces the IDENTICAL digest equation
  `a digestCol = hash ins` that the legacy 25-wide `chip_lookup_sound` forces (the lanes never
  entered the legacy conclusion — they ride existentially in `ChipTableSound`);
* `narrow_served_by_same_rows` / `narrow_lookup_holdsAt_of_wide` — COMPLETENESS preserved: any
  assignment serving a wide lookup serves the narrow one against the same rows (no honest
  witness is lost by the swap).

Byte-safe: NO emitted descriptor changes here — the by-name re-emit sweep is the staged,
Epoch-2-sequenced cutover (recipe in the backlog E7 entry + HORIZONLOG).
-/
import Dregg2.Circuit.NarrowChip

namespace Dregg2.Circuit.ChipNarrowLookup

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2

/-- One narrow row: the 18-prefix `[arity, ins(16), out0]` of a 25-wide chip row — exactly the
tuple the Rust prover's `narrow_hist` derives from the genuine permutation to serve the narrow
bus from the SAME chip rows. -/
def narrowRow (r : List ℤ) : List ℤ := r.take (1 + CHIP_RATE + 1)

/-- The narrow table: the SAME chip rows, 18-prefixed (one physical chip, two buses). -/
def narrowTable (tbl : Table) : Table := tbl.map narrowRow

-- Non-vacuity of the prefix arithmetic: arity + 16 padded inputs survive, out0 is kept,
-- the 7 lanes fall away.
#guard narrowRow ((4 : ℤ) :: List.replicate 16 0 ++ (7 :: List.replicate 7 9))
    == (4 : ℤ) :: List.replicate 16 0 ++ [7]

/-- Take one element past a full left block: `(l₁ ++ l₂).take (l₁.length + 1) = l₁ ++ l₂.take 1`.
(Local, name-stable form of the split; keeps the prefix lemma free of Mathlib name drift.) -/
private theorem take_len_succ {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).take (l₁.length + 1) = l₁ ++ l₂.take 1 := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The exact chip-row split: head element + a full-length middle block + the head of the
output block survive an 18-style prefix; the rest of the output block falls away. -/
private theorem take_cons_block {α : Type} (x y : α) (l₁ l₂ : List α) :
    (x :: (l₁ ++ y :: l₂)).take (l₁.length + 1 + 1) = x :: (l₁ ++ [y]) := by
  have h := take_len_succ (x :: l₁) (y :: l₂)
  simpa using h

/-- Prefixing a genuine wide chip row yields the genuine narrow row: arity + padded inputs
survive, the digest (`out0`, the HEAD of the output block) is kept, the 7 lanes fall away. -/
theorem narrowRow_chipRow (hash : List ℤ → ℤ) (ins lanes : List ℤ)
    (hlen : ins.length ≤ CHIP_RATE) :
    narrowRow (chipRow hash ins lanes) = chipRowNarrow hash ins := by
  have hp : (padTo CHIP_RATE ins).length = CHIP_RATE := padTo_length hlen
  have hkey := take_cons_block ((ins.length : ℤ)) (hash ins) (padTo CHIP_RATE ins) lanes
  rw [hp] at hkey
  unfold narrowRow chipRow chipRowNarrow
  rw [show 1 + CHIP_RATE + 1 = CHIP_RATE + 1 + 1 from by omega]
  exact hkey

/-- **THE SAME-ROWS BRIDGE.** The 18-prefix of a sound WIDE chip table is a sound NARROW chip
table — `ChipTableSoundNarrow` is DERIVED from the deployed `ChipTableSound`, not assumed. This
is the model of Rust's `narrow_hist`: one physical chip serves both buses, so the narrow lever
(`chip_lookup_sound_narrow`) and the whole `GraduateNarrow` tower fire against the deployed
serving with no extra soundness hypothesis. -/
theorem narrowTable_sound (hash : List ℤ → ℤ) (tbl : Table)
    (h : ChipTableSound hash tbl) :
    ChipTableSoundNarrow hash (narrowTable tbl) := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  obtain ⟨ins, lanes, hAdm, _hlanes, rfl⟩ := h r₀ hr₀
  exact ⟨ins, hAdm, narrowRow_chipRow hash ins lanes (chipArity_le_rate hAdm)⟩

/-- **SOUNDNESS PRESERVED END-TO-END.** Against the prefix-served narrow bus of a sound wide
chip table, an out0-only lookup forces the IDENTICAL digest equation the legacy 25-wide
`chip_lookup_sound` forces: `a digestCol = hash ins`. The 7 lanes never entered the legacy
conclusion, so the narrowed site forces exactly what the wide site forced. -/
theorem chip_lookup_narrow_sound_of_wide_table (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (a : Assignment)
    (ins : List EmittedExpr) (digestCol : Nat)
    (hAdm : ChipArityAdmitted ins.length)
    (hmem : (chipLookupTupleNarrow ins digestCol hAdm).map (·.eval a) ∈ narrowTable tbl) :
    a digestCol = hash (ins.map (·.eval a)) :=
  chip_lookup_sound_narrow hash (narrowTable tbl) (narrowTable_sound hash tbl hSound)
    a ins digestCol hAdm hmem

/-- **COMPLETENESS PRESERVED.** Any assignment whose 25-wide lookup tuple is served by the chip
table has its 18-wide narrow tuple served by the prefix table — the SAME rows serve both buses,
so no honest witness is lost by the swap. -/
theorem narrow_served_by_same_rows (tbl : Table) (a : Assignment)
    (ins : List EmittedExpr) (digestCol : Nat) (laneCols : List Nat)
    (hAdm : ChipArityAdmitted ins.length)
    (hwide : (chipLookupTuple ins digestCol laneCols hAdm).map (·.eval a) ∈ tbl) :
    (chipLookupTupleNarrow ins digestCol hAdm).map (·.eval a) ∈ narrowTable tbl := by
  refine List.mem_map.mpr ⟨(chipLookupTuple ins digestCol laneCols hAdm).map (·.eval a), hwide, ?_⟩
  have hev : (chipLookupTuple ins digestCol laneCols hAdm).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a))
          ++ (a digestCol :: laneCols.map a) := by
    simp [chipLookupTuple, List.map_cons, List.map_append, map_eval_padToE, EmittedExpr.eval,
      List.map_map, Function.comp_def]
  have hevN : (chipLookupTupleNarrow ins digestCol hAdm).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a)) ++ [a digestCol] := by
    simp [chipLookupTupleNarrow, List.map_cons, List.map_append, map_eval_padToE,
      EmittedExpr.eval]
  have hp : (padTo CHIP_RATE (ins.map (·.eval a))).length = CHIP_RATE :=
    padTo_length (by simpa [List.length_map] using chipArity_le_rate hAdm)
  have hkey := take_cons_block ((ins.length : ℤ)) (a digestCol)
    (padTo CHIP_RATE (ins.map (·.eval a))) (laneCols.map a)
  rw [hp] at hkey
  rw [hev, hevN]
  unfold narrowRow
  rw [show 1 + CHIP_RATE + 1 = CHIP_RATE + 1 + 1 from by omega]
  exact hkey

/-- Deployment-shaped keystone: against a trace family wiring the narrow bus to the 18-prefix of
the chip table (`tf poseidon2narrow = narrowTable (tf .poseidon2)` — exactly the Rust
`narrow_hist` serving), a narrow lookup that HOLDS forces the digest equation on the row. This
is the per-site obligation the re-emitted by-name descriptors discharge in their refinement
proofs, with the SAME conclusion the wide site's lever gave before the swap. -/
theorem narrow_lookup_holdsAt_sound (hash : List ℤ → ℤ) (tf : TraceFamily)
    (hwire : tf poseidon2narrow = narrowTable (tf .poseidon2))
    (hSound : ChipTableSound hash (tf .poseidon2))
    (env : Emit.EffectVmEmit.VmRowEnv) (ins : List EmittedExpr) (digestCol : Nat)
    (hAdm : ChipArityAdmitted ins.length)
    (hholds : (Lookup.holdsAt tf env
      { table := poseidon2narrow, tuple := chipLookupTupleNarrow ins digestCol hAdm })) :
    env.loc digestCol = hash (ins.map (·.eval env.loc)) := by
  have hmem : (chipLookupTupleNarrow ins digestCol hAdm).map (·.eval env.loc)
      ∈ narrowTable (tf .poseidon2) := by
    have h := hholds
    simp only [Lookup.holdsAt] at h
    rwa [hwire] at h
  exact chip_lookup_narrow_sound_of_wide_table hash (tf .poseidon2) hSound env.loc
    ins digestCol hAdm hmem

/-- Deployment-shaped completeness: a row serving the legacy wide lookup serves the narrow one
under the same family wiring — the honest prover's traces survive the swap unchanged (minus the
lane columns, which no longer exist to fill). -/
theorem narrow_lookup_holdsAt_of_wide (tf : TraceFamily)
    (hwire : tf poseidon2narrow = narrowTable (tf .poseidon2))
    (env : Emit.EffectVmEmit.VmRowEnv) (ins : List EmittedExpr) (digestCol : Nat)
    (laneCols : List Nat)
    (hAdm : ChipArityAdmitted ins.length)
    (hwide : (Lookup.holdsAt tf env
      { table := .poseidon2, tuple := chipLookupTuple ins digestCol laneCols hAdm })) :
    (Lookup.holdsAt tf env
      { table := poseidon2narrow, tuple := chipLookupTupleNarrow ins digestCol hAdm }) := by
  simp only [Lookup.holdsAt] at hwide ⊢
  rw [hwire]
  exact narrow_served_by_same_rows (tf .poseidon2) env.loc ins digestCol laneCols hAdm hwide

#assert_axioms narrowRow_chipRow
#assert_axioms narrowTable_sound
#assert_axioms chip_lookup_narrow_sound_of_wide_table
#assert_axioms narrow_served_by_same_rows
#assert_axioms narrow_lookup_holdsAt_sound
#assert_axioms narrow_lookup_holdsAt_of_wide

end Dregg2.Circuit.ChipNarrowLookup
