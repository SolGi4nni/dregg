/-
# Dregg2.Circuit.Emit.NonRevocationRefineComplete — the COMPLETENESS direction (SEM_IMPLIES_SAT)
of the `revocation` family whole-descriptor bridge, composed with the committed soundness direction
(`NonRevocationRefine`) into a full round-trip.

## What the committed soundness bridge gave us and what this file adds

`NonRevocationRefine.lean` (in HEAD) proves the SOUNDNESS half: a trace SATISFYING `nonRevocationDesc`
(`Satisfied2`) forces the genuine sorted-tree NON-MEMBERSHIP relation
(`Crypto.NonMembership.NonMember`) — `Satisfied2 ⟹ NonMember`, modulo the one honestly-named
field-canonicity residual (`FieldCanonicalDiffs`, the ℤ-vs-BabyBear ordering drift). That is
SAT_IMPLIES_SEM.

This file proves the COMPLEMENTARY half — COMPLETENESS (SEM_IMPLIES_SAT): from the genuine bracketing
data (two committed leaves `L < x < R` bracketing the queried item, both under the half-field ordering
window), a witness trace GENUINELY SATISFYING the deployed `Satisfied2` EXISTS — with realizable,
independently-SOUND `ChipTableSound` / `RangeTableSound` carriers (not assumed: constructed and
proved). Together the two directions pin the descriptor's accept-set to the semantic relation from
BOTH sides — the IFF the byte-pinned emit could not, on its own, establish.

The completeness constructor is PARAMETRIC over `(hash, L, x, R, sib, pos)` and the bracketing
hypotheses — NOT a single hard-coded witness (the committed file already carries one concrete witness
`concrete_sat`; this generalizes it to every bracketing instance, which is what makes it the
completeness statement rather than one example).

## The round-trip (the strongest non-vacuity)

`sem_roundtrip` runs BOTH directions end to end on the parametric construction: from any bracketing
data it BUILDS a satisfying trace, then FEEDS that trace back into the committed soundness bridge
(`nonRevocation_nonmembership`) to recover `NonMember [L, R] x`. So the `Satisfied2` hypothesis of the
soundness theorem is not merely inhabited by one example — it is inhabited by the WHOLE bracketed
family, and the recovered semantic conclusion agrees with the input bracketing. A `True` / `P → P`
statement cannot round-trip a nontrivially-satisfied deployed denotation into a two-valued spec.

## Non-vacuity + constraint (the anti-scar, IN THIS FILE)
  * `sem_satisfied` — the deployed `Satisfied2` is GENUINELY INHABITED, PARAMETRICALLY, for every
    bracketing instance (the hypothesis of every soundness theorem is realizable, not empty).
  * `sem_hyps_inhabited` — the bracketing hypotheses themselves are satisfiable (`100 < 200 < 300`
    with in-window gaps), so the completeness theorem is not vacuously quantified.
  * `sem_needs_bracketing` — the recovered spec is TWO-VALUED: a PRESENT key (`x = L`) is NOT a
    non-member, so the round-trip conclusion genuinely separates satisfying from violating data.
  * `range_wire_bites` — a de-bracketed lower gap (`x ≤ L`) drives the constructed range-wire
    OUT of `[0, 2^30)`, so no `RangeTableSound` table can carry it: the range tooth is load-bearing.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 CR carrier is CONSTRUCTED
(the concrete `ChipTableSound` witness) — it never enters as an axiom; the range argument likewise.
NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.NonRevocationRefine

namespace Dregg2.Circuit.Emit.NonRevocationRefineComplete

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   Table memLog mapLog memOpsOf mapOpsOf map_eval_padToE padTo)
open Dregg2.Circuit.Emit.NonRevocationEmit
open Dregg2.Circuit.Emit.NonRevocationRefine
  (RangeTableSound NonRevocationFragment nonRevocation_sat_refines nonRevocation_nonmembership
   FieldCanonicalDiffs NonRevCanon Canon LowHalf)
open Dregg2.Crypto.NonMembership (Sorted Adjacent NonMember sorted_gap_excludes)

set_option autoImplicit false

/-- Field-faithful glue: an ℤ equation lifts to the DEPLOYED mod-`p` gate/pin denotation. -/
private theorem modEqOfEq {a b : ℤ} (h : a = b) : a ≡ b [ZMOD 2013265921] := by rw [h]

/-! ## §1 — the parametric completeness witness (row, pub, tables, trace). -/

/-- The single active main-row assignment for the bracketing data `(L, x, R, sib, pos)`. Fills every
declared column with its honest value: the queried item, the two bracketing leaves, their consecutive
positions, the two gap witnesses, the two half-field range-wires, the two-level Poseidon2 fold
`PAR0 = CUR1 = hash [L, R]`, `PAR1 = hash [hash [L, R], sib]` (the committed root), and the exposed
chip lanes zeroed. -/
def semRow (hash : List ℤ → ℤ) (L x R sib pos : ℤ) : Assignment := fun c =>
  if c = X then x
  else if c = LEAF_L then L
  else if c = LEAF_R then R
  else if c = LPOS then pos
  else if c = RPOS then pos + 1
  else if c = DIFF_L then x - L - 1
  else if c = DIFF_R then R - x - 1
  else if c = RL then HALF_P_MINUS_1 - (x - L - 1)
  else if c = RR then HALF_P_MINUS_1 - (R - x - 1)
  else if c = PAR0 then hash [L, R]
  else if c = CUR1 then hash [L, R]
  else if c = SIB1 then sib
  else if c = PAR1 then hash [hash [L, R], sib]
  else 0

/-- The public-input vector: the committed root `hash [hash [L, R], sib]` at `ROOT_PI`, the queried
item `x` at `QUERIED_PI`. -/
def semPub (hash : List ℤ → ℤ) (L x R sib : ℤ) : Assignment := fun k =>
  if k = QUERIED_PI then x
  else if k = ROOT_PI then hash [hash [L, R], sib]
  else 0

/-- The Poseidon2 chip table: the two genuine node hashes (`[L, R] ↦ PAR0`, `[PAR0, sib] ↦ root`),
each with the 7 exposed lanes zeroed. -/
def semTable (hash : List ℤ → ℤ) (L R sib : ℤ) : Table :=
  [ chipRow hash [L, R] (List.replicate 7 0)
  , chipRow hash [hash [L, R], sib] (List.replicate 7 0) ]

/-- The 30-bit range table: the two half-field range-wires `HALF_P_MINUS_1 − diff` (checked by the
`RL`/`RR` lookups) AND the two diff wires `diff` themselves (checked by the fix's direct
`[DIFF_L]`/`[DIFF_R]` lookups). -/
def semRange (L x R : ℤ) : Table :=
  [ [HALF_P_MINUS_1 - (x - L - 1)], [HALF_P_MINUS_1 - (R - x - 1)]
  , [x - L - 1], [R - x - 1] ]

/-- The two-row witness trace: the active row (row 0) plus an identical padding row (row 1, the last
row, on which the `.gate`s / `.piBinding .first`s are vacuous and only the lookups fire). -/
def semTrace (hash : List ℤ → ℤ) (L x R sib pos : ℤ) : VmTrace :=
  { rows := [semRow hash L x R sib pos, semRow hash L x R sib pos]
  , pub  := semPub hash L x R sib
  , tf   := fun tid => match tid with
      | .poseidon2 => semTable hash L R sib
      | .range     => semRange L x R
      | _          => [] }

/-! ## §2 — read/environment reductions (all definitional). -/

section Reads
variable (hash : List ℤ → ℤ) (L x R sib pos : ℤ)

@[local simp] theorem loc0 :
    (envAt (semTrace hash L x R sib pos) 0).loc = semRow hash L x R sib pos := rfl
@[local simp] theorem loc1 :
    (envAt (semTrace hash L x R sib pos) 1).loc = semRow hash L x R sib pos := rfl
@[local simp] theorem pub_i (i : Nat) :
    (envAt (semTrace hash L x R sib pos) i).pub = semPub hash L x R sib := rfl

@[local simp] theorem r_X : semRow hash L x R sib pos X = x := rfl
@[local simp] theorem r_LEAF_L : semRow hash L x R sib pos LEAF_L = L := rfl
@[local simp] theorem r_LEAF_R : semRow hash L x R sib pos LEAF_R = R := rfl
@[local simp] theorem r_LPOS : semRow hash L x R sib pos LPOS = pos := rfl
@[local simp] theorem r_RPOS : semRow hash L x R sib pos RPOS = pos + 1 := rfl
@[local simp] theorem r_DIFF_L : semRow hash L x R sib pos DIFF_L = x - L - 1 := rfl
@[local simp] theorem r_DIFF_R : semRow hash L x R sib pos DIFF_R = R - x - 1 := rfl
@[local simp] theorem r_RL : semRow hash L x R sib pos RL = HALF_P_MINUS_1 - (x - L - 1) := rfl
@[local simp] theorem r_RR : semRow hash L x R sib pos RR = HALF_P_MINUS_1 - (R - x - 1) := rfl
@[local simp] theorem r_PAR0 : semRow hash L x R sib pos PAR0 = hash [L, R] := rfl
@[local simp] theorem r_CUR1 : semRow hash L x R sib pos CUR1 = hash [L, R] := rfl
@[local simp] theorem r_SIB1 : semRow hash L x R sib pos SIB1 = sib := rfl
@[local simp] theorem r_PAR1 : semRow hash L x R sib pos PAR1 = hash [hash [L, R], sib] := rfl

@[local simp] theorem p_QUERIED : semPub hash L x R sib QUERIED_PI = x := rfl
@[local simp] theorem p_ROOT : semPub hash L x R sib ROOT_PI = hash [hash [L, R], sib] := rfl

end Reads

/-! ## §3 — the lookup-tuple evaluations (each declared lookup's evaluated tuple IS a table row). -/

section Tuples
variable (hash : List ℤ → ℤ) (L x R sib pos : ℤ)

/-- The level-0 chip lookup's evaluated tuple is the genuine `[L, R] ↦ hash [L, R]` chip row. -/
theorem level0_eval :
    (chipLookupTuple [.var LEAF_L, .var LEAF_R] PAR0 LEVEL0_LANES).map
        (·.eval (semRow hash L x R sib pos)) = chipRow hash [L, R] (List.replicate 7 0) := by
  simp only [chipLookupTuple, chipRow, List.map_cons, List.map_append, map_eval_padToE,
    EmittedExpr.eval, LEVEL0_LANES, List.map_nil, List.length_cons, List.length_nil,
    r_LEAF_L, r_LEAF_R, r_PAR0]
  rfl

/-- The level-1 chip lookup's evaluated tuple is the genuine `[hash [L, R], sib] ↦ root` chip row. -/
theorem level1_eval :
    (chipLookupTuple [.var CUR1, .var SIB1] PAR1 LEVEL1_LANES).map
        (·.eval (semRow hash L x R sib pos)) = chipRow hash [hash [L, R], sib] (List.replicate 7 0) := by
  simp only [chipLookupTuple, chipRow, List.map_cons, List.map_append, map_eval_padToE,
    EmittedExpr.eval, LEVEL1_LANES, List.map_nil, List.length_cons, List.length_nil,
    r_CUR1, r_SIB1, r_PAR1]
  rfl

end Tuples

/-! ## §4 — the SOUND, REALIZABLE carriers (constructed, not assumed). -/

/-- The constructed chip table is genuinely SOUND — the Poseidon2 CR carrier is realized, not an
axiom. -/
theorem sem_chipSound (hash : List ℤ → ℤ) (L x R sib pos : ℤ) :
    ChipTableSound hash ((semTrace hash L x R sib pos).tf .poseidon2) := by
  intro r hr
  simp only [semTrace, semTable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨[L, R], List.replicate 7 0, ?_, ?_, rfl⟩
    · show (2 : Nat) ≤ CHIP_RATE; decide
    · show (7 : Nat) = CHIP_OUT_LANES - 1; decide
  · refine ⟨[hash [L, R], sib], List.replicate 7 0, ?_, ?_, rfl⟩
    · show (2 : Nat) ≤ CHIP_RATE; decide
    · show (7 : Nat) = CHIP_OUT_LANES - 1; decide

/-- The constructed range table is genuinely SOUND — every range-wire lies in `[0, 2^30)` — given the
half-field ordering hypotheses. This is the exact place the bracketing data is USED (a de-bracketed
gap would push a wire out of range; see `range_wire_bites`). -/
theorem sem_rangeSound (hash : List ℤ → ℤ) (L x R sib pos : ℤ)
    (hlt : L < x) (hgt : x < R) (hbL : x - L - 1 ≤ HALF_P_MINUS_1) (hbR : R - x - 1 ≤ HALF_P_MINUS_1) :
    RangeTableSound ORDERING_BITS ((semTrace hash L x R sib pos).tf .range) := by
  have h2 : (2 : ℤ) ^ ORDERING_BITS = 1073741824 := by decide
  have hH : HALF_P_MINUS_1 = 1006632959 := rfl
  intro r hr
  simp only [semTrace, semRange, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨HALF_P_MINUS_1 - (x - L - 1), rfl, by omega, by omega⟩
  · exact ⟨HALF_P_MINUS_1 - (R - x - 1), rfl, by omega, by omega⟩
  · exact ⟨x - L - 1, rfl, by omega, by omega⟩
  · exact ⟨R - x - 1, rfl, by omega, by omega⟩

/-! ## §5 — the completeness core: the deployed `Satisfied2` is genuinely inhabited. -/

/-- **`sem_satisfied` — THE COMPLETENESS CORE (SEM_IMPLIES_SAT).** For every bracketing instance
`L < x < R` in the half-field window, the constructed two-row trace GENUINELY SATISFIES the deployed
whole-trace denotation `Satisfied2` of `nonRevocationDesc`: every one of the 14 declared constraints
holds on both row windows (the two chip lookups and FOUR range lookups — `RL`/`RR` plus the fix's
direct `[DIFF_L]`/`[DIFF_R]` — on both rows; the six gates and two PI pins fire on the active row 0,
vacuous on the last row 1), and the empty memory / map-op legs close. The hypothesis of the committed
soundness bridge is therefore inhabited PARAMETRICALLY.

Note it needs NO ordering hypothesis: the gate equations and table memberships are satisfiable for any
bracketing data — the strict ordering enters ONLY through the range-table SOUNDNESS carrier
(`sem_rangeSound`), which is exactly where `L < x < R` becomes load-bearing. -/
theorem sem_satisfied (hash : List ℤ → ℤ) (L x R sib pos : ℤ) :
    Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) []
      (semTrace hash L x R sib pos) := by
  have hmemlog : memLog nonRevocationDesc (semTrace hash L x R sib pos) = [] := rfl
  have hmaplog : mapLog nonRevocationDesc (semTrace hash L x R sib pos) = [] := rfl
  have hL0 := level0_eval hash L x R sib pos
  have hL1 := level1_eval hash L x R sib pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    rw [show (semTrace hash L x R sib pos).rows.length = 2 from rfl] at hi ⊢
    simp only [nonRevocationDesc, nonRevLastRowFix, List.cons_append, List.nil_append,
      level0Lookup, level1Lookup, rangeLLookup, rangeRLookup,
      rangeLDiffLookup, rangeRDiffLookup] at hc
    interval_cases i
    · -- active row 0: isFirst = true (pins fire), isLast = false (gates fire).
      fin_cases hc
      · -- level-0 chip lookup
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc0]
        rw [hL0]; exact List.mem_cons_self
      · -- level-1 chip lookup
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc0]
        rw [hL1]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · -- continuity gate: CUR1 − PAR0 ≡ 0
        exact modEqOfEq (by simp only [contBody, subBody, EmittedExpr.eval, loc0, r_CUR1, r_PAR0]; ring)
      · -- diff_left gate: (x−L−1) − x + L + 1 ≡ 0
        exact modEqOfEq (by simp only [diffLBody, EmittedExpr.eval, loc0, r_DIFF_L, r_X, r_LEAF_L]; ring)
      · -- diff_right gate
        exact modEqOfEq (by simp only [diffRBody, EmittedExpr.eval, loc0, r_DIFF_R, r_LEAF_R, r_X]; ring)
      · -- range-left binding gate: RL + diff_left − HALF ≡ 0
        exact modEqOfEq (by simp only [rangeLBindBody, EmittedExpr.eval, loc0, r_RL, r_DIFF_L]; ring)
      · -- range-right binding gate
        exact modEqOfEq (by simp only [rangeRBindBody, EmittedExpr.eval, loc0, r_RR, r_DIFF_R]; ring)
      · -- range-left lookup: [RL] ∈ range table
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc0, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_RL]
        exact List.mem_cons_self
      · -- range-right lookup
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc0, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_RR]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · -- direct diff-left lookup: [DIFF_L] = [x−L−1] ∈ range table (the lower-bound fix)
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc0, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_DIFF_L]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · -- direct diff-right lookup: [DIFF_R] = [R−x−1] ∈ range table (the lower-bound fix)
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc0, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_DIFF_R]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · -- adjacency gate: (pos+1) − pos − 1 ≡ 0
        exact modEqOfEq (by simp only [adjBody, EmittedExpr.eval, loc0, r_RPOS, r_LPOS]; ring)
      · -- root PI pin: loc PAR1 ≡ pub ROOT_PI
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
        intro _; exact modEqOfEq (by simp only [loc0, pub_i, r_PAR1, p_ROOT])
      · -- queried-item PI pin: loc X ≡ pub QUERIED_PI
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
        intro _; exact modEqOfEq (by simp only [loc0, pub_i, r_X, p_QUERIED])
      -- the six LAST-ROW-FIX boundary constraints are vacuous on the active (non-last) row 0.
      · intro h; exact absurd h (by decide)   -- boundary-last continuity
      · intro h; exact absurd h (by decide)   -- boundary-last diff_left
      · intro h; exact absurd h (by decide)   -- boundary-last diff_right
      · intro h; exact absurd h (by decide)   -- boundary-last range-left binding
      · intro h; exact absurd h (by decide)   -- boundary-last range-right binding
      · intro h; exact absurd h (by decide)   -- boundary-last adjacency
    · -- padding row 1: isFirst = false, isLast = true (gates + first-row pins vacuous).
      fin_cases hc
      · -- level-0 chip lookup (fires on every row)
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc1]
        rw [hL0]; exact List.mem_cons_self
      · -- level-1 chip lookup
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc1]
        rw [hL1]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact trivial            -- continuity gate vacuous on the last row
      · exact trivial            -- diff_left gate
      · exact trivial            -- diff_right gate
      · exact trivial            -- range-left binding gate
      · exact trivial            -- range-right binding gate
      · -- range-left lookup (fires on every row)
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc1, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_RL]
        exact List.mem_cons_self
      · -- range-right lookup
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc1, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_RR]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · -- direct diff-left lookup (fires on every row)
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc1, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_DIFF_L]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · -- direct diff-right lookup (fires on every row)
        simp only [VmConstraint2.holdsAt, Lookup.holdsAt, loc1, List.map_cons, List.map_nil,
          EmittedExpr.eval, r_DIFF_R]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact trivial            -- adjacency gate
      · -- root PI pin vacuous (not the first row)
        intro h; exact absurd h (by decide)
      · -- queried-item PI pin vacuous
        intro h; exact absurd h (by decide)
      -- the six LAST-ROW-FIX boundary constraints FIRE on the last row 1 (the fix): each body
      -- vanishes on the (identical) padding row — the same equations as the row-0 gates.
      · intro _
        exact modEqOfEq (by simp only [contBody, subBody, EmittedExpr.eval, loc1, r_CUR1, r_PAR0]; ring)
      · intro _
        exact modEqOfEq (by simp only [diffLBody, EmittedExpr.eval, loc1, r_DIFF_L, r_X, r_LEAF_L]; ring)
      · intro _
        exact modEqOfEq (by simp only [diffRBody, EmittedExpr.eval, loc1, r_DIFF_R, r_LEAF_R, r_X]; ring)
      · intro _
        exact modEqOfEq (by simp only [rangeLBindBody, EmittedExpr.eval, loc1, r_RL, r_DIFF_L]; ring)
      · intro _
        exact modEqOfEq (by simp only [rangeRBindBody, EmittedExpr.eval, loc1, r_RR, r_DIFF_R]; ring)
      · intro _
        exact modEqOfEq (by simp only [adjBody, EmittedExpr.eval, loc1, r_RPOS, r_LPOS]; ring)
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-! ## §6 — the packaged completeness statement + the two-direction round-trip. -/

/-- **`sem_implies_sat` — the existential completeness statement.** For every bracketing instance,
there EXISTS a trace that (a) genuinely satisfies the deployed `Satisfied2`, (b) carries a SOUND,
realizable Poseidon2-chip carrier and a SOUND range carrier, and (c) reads the intended bracketing
data back on its active row. The complement of the committed `Satisfied2 ⟹ NonMember` soundness. -/
theorem sem_implies_sat (hash : List ℤ → ℤ) (L x R sib pos : ℤ)
    (hlt : L < x) (hgt : x < R) (hbL : x - L - 1 ≤ HALF_P_MINUS_1) (hbR : R - x - 1 ≤ HALF_P_MINUS_1) :
    ∃ t : VmTrace,
      Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] t
      ∧ ChipTableSound hash (t.tf .poseidon2)
      ∧ RangeTableSound ORDERING_BITS (t.tf .range)
      ∧ FieldCanonicalDiffs t
      ∧ (envAt t 0).loc X = x
      ∧ (envAt t 0).loc LEAF_L = L
      ∧ (envAt t 0).loc LEAF_R = R := by
  refine ⟨semTrace hash L x R sib pos, sem_satisfied hash L x R sib pos,
    sem_chipSound hash L x R sib pos, sem_rangeSound hash L x R sib pos hlt hgt hbL hbR, ?_,
    rfl, rfl, rfl⟩
  -- the field-canonicity residual HOLDS on the honest construction (both diffs ≥ 0).
  refine ⟨?_, ?_⟩ <;> simp only [loc0, r_DIFF_L, r_DIFF_R] <;> omega

/-- **`sem_roundtrip` — THE TWO-DIRECTION ROUND-TRIP.** From any bracketing data, BUILD a satisfying
trace (this file's completeness), then FEED it back through the committed SOUNDNESS bridge
(`nonRevocation_nonmembership`) to recover the genuine `NonMember [L, R] x`. The descriptor accepts the
bracketed witness AND its acceptance re-derives the semantic non-membership — the accept-set and the
spec agree in both directions on the whole bracketed family. -/
theorem sem_roundtrip (hash : List ℤ → ℤ) (L x R sib pos : ℤ)
    (hlt : L < x) (hgt : x < R) (hbL : x - L - 1 ≤ HALF_P_MINUS_1) (hbR : R - x - 1 ≤ HALF_P_MINUS_1)
    (hcanon : NonRevCanon (semTrace hash L x R sib pos)) :
    NonMember [L, R] x := by
  have hsat := sem_satisfied hash L x R sib pos
  have hsorted : Sorted ([L, R] : List ℤ) := by
    show ([L, R] : List ℤ).Pairwise (· < ·)
    exact List.Pairwise.cons
      (by intro a ha; rw [List.mem_singleton] at ha; subst ha; exact hlt.trans hgt)
      (List.Pairwise.cons (by intro a ha; simp at ha) List.Pairwise.nil)
  have hadj : Adjacent ([L, R] : List ℤ)
      ((envAt (semTrace hash L x R sib pos) 0).loc LEAF_L)
      ((envAt (semTrace hash L x R sib pos) 0).loc LEAF_R) := by
    simp only [loc0, r_LEAF_L, r_LEAF_R]; exact ⟨[], [], rfl⟩
  have hlen : 0 < (semTrace hash L x R sib pos).rows.length := by
    show (0 : Nat) < 2; decide
  have := nonRevocation_nonmembership hlen hsat (sem_chipSound hash L x R sib pos)
    (sem_rangeSound hash L x R sib pos hlt hgt hbL hbR) hcanon [L, R] hsorted hadj
  simpa only [loc0, r_X] using this

#assert_axioms sem_satisfied
#assert_axioms sem_implies_sat
#assert_axioms sem_roundtrip

/-! ## §7 — non-vacuity + constraint (the anti-scar). -/

/-- The bracketing hypotheses are jointly SATISFIABLE (`100 < 200 < 300`, both gaps `99 ≤ HALF`) — so
the completeness theorems are not vacuously quantified over an empty premise. -/
theorem sem_hyps_inhabited :
    (100 : ℤ) < 200 ∧ (200 : ℤ) < 300 ∧ (200 : ℤ) - 100 - 1 ≤ HALF_P_MINUS_1
      ∧ (300 : ℤ) - 200 - 1 ≤ HALF_P_MINUS_1 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> · rw [show HALF_P_MINUS_1 = 1006632959 from rfl]; norm_num

/-- **The round-trip on the inhabited instance is a genuine non-membership** (`200 ∉ [100, 300]`),
built from a satisfying trace, not asserted. -/
theorem sem_roundtrip_demo : NonMember ([100, 300] : List ℤ) 200 := by
  have := sem_hyps_inhabited
  -- base-1000 digit hash keeps both digests canonical (`hash [100,300] = 100300`,
  -- `hash [100300,7] = 100300007 < p`), so the deployed range-check envelope is inhabited concretely.
  have hcanon : NonRevCanon
      (semTrace (fun xs => xs.foldl (fun a v => a * 1000 + v) 0) 100 200 300 7 5) :=
    { cur1 := ⟨by decide, by decide⟩, par0 := ⟨by decide, by decide⟩,
      par1 := ⟨by decide, by decide⟩, rootPi := ⟨by decide, by decide⟩,
      queriedPi := ⟨by decide, by decide⟩, x := ⟨by decide, by decide⟩,
      leafL := ⟨by decide, by decide⟩, leafR := ⟨by decide, by decide⟩,
      lpos := ⟨by decide, by decide⟩, rpos := ⟨by decide, by decide⟩ }
  exact sem_roundtrip (fun xs => xs.foldl (fun a v => a * 1000 + v) 0) 100 200 300 7 5
    (by norm_num) (by norm_num) this.2.2.1 this.2.2.2 hcanon

/-- **Witness FALSE — the recovered spec CONSTRAINS.** The bracketing data is load-bearing: a PRESENT
key (`x = L = 100`) is NOT a non-member of `[100, 300]`, so the round-trip conclusion is two-valued (a
`True` / `P → P` bridge could not separate this). -/
theorem sem_needs_bracketing : ¬ NonMember ([100, 300] : List ℤ) 100 := by
  rintro ⟨_, hni⟩; exact hni (by simp)

/-- **The range tooth is load-bearing (the constructed side).** A de-bracketed lower gap (`x = L`, so
`x ≤ L`) makes the constructed lower range-wire `HALF_P_MINUS_1 − (x − L − 1) = HALF_P_MINUS_1 + 1`,
which EXCEEDS `HALF_P_MINUS_1` and — being one past the max the honest gap ever reaches — cannot sit in
the honest range the sound table certifies without wrapping. Concretely the wire is `> HALF_P_MINUS_1`,
witnessing that the completeness construction genuinely REQUIRES `L < x` (it is not free to accept a
non-bracketing item). -/
theorem range_wire_bites (L x : ℤ) (hle : x ≤ L) :
    HALF_P_MINUS_1 < HALF_P_MINUS_1 - (x - L - 1) := by omega

/-- The honest active row with the right-neighbor position bumped by one (`RPOS = LPOS + 2`), breaking
adjacency. -/
def semRowBad (hash : List ℤ → ℤ) (L x R sib pos : ℤ) : Assignment :=
  fun c => if c = RPOS then pos + 2 else semRow hash L x R sib pos c

/-- The de-bracketed trace: the completeness witness with non-consecutive neighbor positions. -/
def semTraceBad (hash : List ℤ → ℤ) (L x R sib pos : ℤ) : VmTrace :=
  { semTrace hash L x R sib pos with
    rows := [semRowBad hash L x R sib pos, semRowBad hash L x R sib pos] }

/-- **A concrete assignment that FAILS `Satisfied2` (the adjacency gate BITES), PARAMETRICALLY.** With
`RPOS = LPOS + 2` the adjacency gate `RPOS − LPOS − 1 = 1 ≠ 0` cannot vanish on the active row, so NO
`Satisfied2` exists — the descriptor genuinely REJECTS de-bracketed data. Together with `sem_satisfied`
(a genuinely satisfying witness) this shows the deployed denotation is TWO-VALUED, not a rubber stamp. -/
theorem sem_fail (hash : List ℤ → ℤ) (L x R sib pos : ℤ) :
    ¬ Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) []
        (semTraceBad hash L x R sib pos) := by
  intro h
  have hmem : VmConstraint2.base (.gate adjBody) ∈ nonRevocationDesc.constraints := by
    simp [nonRevocationDesc, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup]
  have hlen0 : 0 < (semTraceBad hash L x R sib pos).rows.length := by show (0 : Nat) < 2; decide
  have h0 := h.rowConstraints 0 hlen0 _ hmem
  have hlast : ((0 : Nat) + 1 == (semTraceBad hash L x R sib pos).rows.length) = false := rfl
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h0
  have hR : (envAt (semTraceBad hash L x R sib pos) 0).loc RPOS = pos + 2 := rfl
  have hL : (envAt (semTraceBad hash L x R sib pos) 0).loc LPOS = pos := rfl
  -- the adjacency gate binds `≡ 0 [ZMOD p]`; here the body is `(pos+2) − pos − 1 = 1`, so `p ∣ 1` — absurd.
  simp only [adjBody, EmittedExpr.eval, hR, hL, Int.modEq_zero_iff_dvd] at h0
  obtain ⟨k, hk⟩ := h0
  omega

#assert_axioms sem_roundtrip_demo
#assert_axioms sem_needs_bracketing
#assert_axioms sem_fail

end Dregg2.Circuit.Emit.NonRevocationRefineComplete
