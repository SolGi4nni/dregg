import Dregg2.Circuit.DescriptorIR2

/-
# NarrowChip — the single-output (18-wide) chip lookup for the tuple-narrowing optimizer pass

THE OPTIMIZER'S FIRST PASS (validated by 3 planner-architects, 2026-07-13). The deployed
`chipLookupTuple` is 25-wide: `arity + CHIP_RATE(16) inputs + out0 + 7 lanes`. For SINGLE-OUTPUT sites
(the 133-site 1-felt Merkle–Damgård chain in the wide rotated descriptor), those 7 lane columns are
witnessed only to match the wide chip row and are — in the deployed Lean's own words
(`DescriptorIR2.lean:1144`) — "NOT constrained by the single-output site denotation". They are read by
NOTHING: `chip_lookup_sound` proves `a digestCol = hash inputs` with the lanes riding purely
EXISTENTIALLY, never entering the conclusion.

This file defines the NARROW variant (18-wide: `arity + CHIP_RATE inputs + out0`, no lanes) on a second
chip table, and proves it enforces the IDENTICAL out0 = hash equation. Routing the 134 single-output
sites to a narrow bus therefore drops 7 committed columns/site (~938 on the wide rotated descriptor,
2607→~1669 main) at ZERO soundness cost — a mechanical translation-validation refinement, no new crypto.
`chip_lookup_sound_narrow` is that refinement's soundness core; it is a strict simplification of
`chip_lookup_sound` (the existential lanes are gone).
-/

namespace Dregg2.Circuit.DescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit

/-- The NARROW chip ROW (18-wide): `arity :: padded inputs ++ [hash inputs]` — ONLY out0, no lanes. -/
def chipRowNarrow (hash : List ℤ → ℤ) (ins : List ℤ) : List ℤ :=
  (ins.length : ℤ) :: padTo CHIP_RATE ins ++ [hash ins]

/-- The NARROW chip LOOKUP tuple (18-wide): `arity :: padded input exprs ++ [out0 column]`. -/
def chipLookupTupleNarrow (ins : List EmittedExpr) (digestCol : Nat) : List EmittedExpr :=
  (.const (ins.length : ℤ)) :: padToE CHIP_RATE ins ++ [.var digestCol]

/-- A narrow chip table is SOUND when every row is a genuine `(arity, padded inputs, hash inputs)`
    tuple of the permutation — with NO existential lanes (the simplification over `ChipTableSound`). -/
def ChipTableSoundNarrow (hash : List ℤ → ℤ) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ ins : List ℤ, ins.length ≤ CHIP_RATE ∧ r = chipRowNarrow hash ins

/-- **THE NARROW LEVER.** Against a sound narrow chip table, a narrow lookup ENFORCES the SAME hash
    equation `a digestCol = hash inputs` that the 25-wide `chip_lookup_sound` does — carrying NO lane
    columns. This is why the 7 lanes/site are droppable for single-output sites at zero soundness cost. -/
theorem chip_lookup_sound_narrow (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (a : Assignment)
    (ins : List EmittedExpr) (digestCol : Nat) (hlen : ins.length ≤ CHIP_RATE)
    (hmem : (chipLookupTupleNarrow ins digestCol).map (·.eval a) ∈ tbl) :
    a digestCol = hash (ins.map (·.eval a)) := by
  obtain ⟨ws, hwlen, hrow⟩ := hSound _ hmem
  have hev : (chipLookupTupleNarrow ins digestCol).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a)) ++ [a digestCol] := by
    simp [chipLookupTupleNarrow, List.map_cons, List.map_append, map_eval_padToE, EmittedExpr.eval,
      List.map_map, Function.comp_def]
  rw [hev] at hrow
  unfold chipRowNarrow at hrow
  injection hrow with hl htail
  have hlens : (ins.map (·.eval a)).length = ws.length := by
    have hcast : (ins.length : ℤ) = (ws.length : ℤ) := hl
    have := Int.natCast_inj.mp hcast
    simpa [List.length_map] using this
  have hlenm : (ins.map (·.eval a)).length ≤ CHIP_RATE := by
    simpa [List.length_map] using hlen
  have hpads := List.append_inj htail (by rw [padTo_length hlenm, padTo_length hwlen])
  have hins : ins.map (·.eval a) = ws := padTo_inj hlens hpads.1
  have hd : a digestCol = hash ws := by
    have hblock : [a digestCol] = [hash ws] := hpads.2
    simpa using hblock
  rw [hins]; exact hd

/-- **The SITE-level narrow refinement** (mirrors `siteLookup_replaces_site`, lanes dropped). Against a
    sound narrow chip table, the narrow lookup of a site `s` enforces EXACTLY the site equation
    `loc digestCol = hash (resolved inputs)` — the v1 in-row Poseidon2 constraint — carrying no lanes.
    This is the unit the tuple-narrowing emit routing replaces per single-output site. -/
theorem siteLookupNarrow_replaces_site (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (env : VmRowEnv)
    (sites : List VmHashSite) (s : VmHashSite) (digs : List ℤ)
    (hdig : ∀ k, env.loc ((sites.getD k default).digestCol) = digs.getD k 0)
    (hlen : s.inputs.length ≤ CHIP_RATE)
    (hmem : (chipLookupTupleNarrow (s.inputs.map (HashInput.toExpr sites)) s.digestCol).map
              (·.eval env.loc) ∈ tbl) :
    env.loc s.digestCol = hash (s.resolvedInputs env digs) := by
  have h := chip_lookup_sound_narrow hash tbl hSound env.loc
    (s.inputs.map (HashInput.toExpr sites)) s.digestCol
    (by simpa [List.length_map] using hlen) hmem
  rw [h]
  congr 1
  rw [List.map_map]
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro i _
  cases i with
  | col c    => rfl
  | digest k =>
    have hk := hdig k
    simp only [List.getD_eq_getElem?_getD] at hk
    simp [HashInput.toExpr, HashInput.resolve, EmittedExpr.eval, hk]
  | zero     => rfl

-- Soundness core + site refinement: axiom-clean (only the standard trio — no sorry, no assumed carrier).
#assert_axioms chip_lookup_sound_narrow
#assert_axioms siteLookupNarrow_replaces_site

/-! ### The narrow chip TABLE ID + table def + the site-level narrow lookup (the emit-routing unit).

**Why `.custom 3` and not a fresh enum case.** The Rust decoder pins `TID_P2_NARROW = 8`
(`descriptor_ir2.rs:263`), and its own comment records "0..7 are taken" — the narrow bus RESERVES
the wire slot that `.custom 3` already serializes to (`TableId.wireId (.custom 3) = 5 + 3 = 8`). A
*fresh* `TableId` constructor cannot take wire id 8 without breaking the deployed
`TableId.wireId_injective`: `.custom n ↦ 5 + n` is a bijection onto `[5, ∞)`, so ANY fixed new id in
that range collides with some `.custom n` (here `.custom 3`), and injectivity — quantified over all
`n` — becomes false and un-provable. `.custom 3` is genuinely UNUSED (the deployed custom ids are
`0/1/2` = submask/umem/umem-boundary and `64 + bits` = the width-tagged range tables), so binding it
to the narrow bus is the faithful Lean twin of the Rust reservation, PURELY ADDITIVE: no edit to the
`TableId` inductive, to `wireId`, or to `wireId_injective`. -/

/-- The NARROW chip bus receiver's table id: the reserved `.custom 3` slot (wire id 8 =
`descriptor_ir2.rs::TID_P2_NARROW`). Single-output hash sites route their 18-wide `[arity, ins,
out0]` lookup here instead of the 25-wide `.poseidon2` bus. -/
def poseidon2narrow : TableId := .custom 3

/-- The NARROW Poseidon2 chip table: `1 (arity tag) + CHIP_RATE (padded inputs) + 1 (out0)` = 18
columns — the single-output shape with NO output lanes (the 7 lane columns the wide chip carries are
dropped for single-output sites). Served by the SAME genuine permutation rows as the wide chip. -/
def poseidon2NarrowChipTableDef : TableDef :=
  ⟨poseidon2narrow, "poseidon2_narrow_chip", CHIP_RATE + 1 + 1, .permutation⟩

/-- The NARROW chip lookup replacing single-output site `s` of the ordered family `sites`: the
18-wide tuple `[arity, padded inputs, digestCol]`. NO per-site lane base — narrow lookups carry no
lane columns, so there is nothing to offset (contrast `siteLookup`'s `base`). -/
def siteLookupNarrow (sites : List VmHashSite) (s : VmHashSite) : Lookup :=
  { table := poseidon2narrow
  , tuple := chipLookupTupleNarrow (s.inputs.map (HashInput.toExpr sites)) s.digestCol }

-- The narrow bus rides the reserved wire slot 8 (= Rust `TID_P2_NARROW`); the table is 18-wide.
#guard poseidon2narrow.wireId == 8
#guard poseidon2NarrowChipTableDef.arity == 18
#guard poseidon2NarrowChipTableDef.arity == CHIP_RATE + 1 + 1
-- The narrow id is DISTINCT from the wide chip / main / other tables (no wire collision).
#guard poseidon2narrow.wireId != TableId.poseidon2.wireId
#guard (poseidon2NarrowChipTableDef.arity + (CHIP_OUT_LANES - 1)) == poseidon2ChipTableDef.arity

end Dregg2.Circuit.DescriptorIR2
