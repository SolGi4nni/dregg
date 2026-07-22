/-
# Dregg2.Circuit.Emit.PredicatesCompoundWeakCountermodel

An exact regression for the remaining semantic gap in the CURRENT compound-predicate descriptor.

`compoundPredicateDesc` correctly enforces its authored `CompoundClassified` relation, including on
the last row.  But that relation deliberately treats `AND_INT` as a prover-supplied wire: selecting
AND only forces `COMPOSED = AND_INT`; no emitted gate recomputes `AND_INT` from `sub_result[0..7]`.

This file exhibits the consequence against the whole deployed acceptance predicate.  The two-row
trace `weakAndWitness`

* has all eight sub-results equal to false,
* selects AND,
* supplies `AND_INT = 1` and publishes `COMPOSED = 1`, and
* nevertheless `Satisfied2`s the current byte-pinned descriptor.

It therefore satisfies `CompoundClassified` while refuting the genuine AND functional law.  This is
not the old last-row-vacuity bug: both rows carry the same values, and the descriptor's derived
`compoundLastFix` constraints also vanish.  The missing lift is a gate (or a sound committed
sub-proof carrier) binding `AND_INT` to the conjunction of the eight sub-results.

Standalone regression only: no central import and no edits to the descriptor.
-/
import Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine

namespace Dregg2.Circuit.Emit.PredicatesCompoundWeakCountermodel

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine

set_option autoImplicit false

/-! ## §1 — The genuine AND specification absent from `CompoundClassified`. -/

/-- For a selected AND operator, an asserted true result must mean every sub-result is true.  The
reverse implication is not needed to expose the soundness gap, so this is the smallest load-bearing
soundness law. -/
def GenuineAndSound (env : VmRowEnv) : Prop :=
  env.loc OP_AND = 1 → env.loc COMPOSED = 1 → ∀ j, j < 8 → env.loc j = 1

/-! ## §2 — A concrete accepted witness with eight false inputs and a true AND result. -/

/-- All eight sub-results are `0`; AND is selected; the free intermediate and composed result are
both `1`.  Every commitment and auxiliary wire is `0`. -/
def weakAndRow : Assignment := fun c =>
  if c = OP_AND then 1 else if c = COMPOSED then 1 else if c = AND_INT then 1 else 0

/-- The descriptor publishes `COMPOSED` in `pi[0]`; all other public inputs remain `0`. -/
def weakAndPub : Assignment := fun i => if i = 0 then 1 else 0

/-- Two rows ensure row `0` is a transition row.  Identical values on row `1` also satisfy every
last-row twin from `compoundLastFix`. -/
def weakAndWitness : VmTrace :=
  { rows := [weakAndRow, weakAndRow]
  , pub := weakAndPub
  , tf := fun _ => [] }

/-- The weak AND witness satisfies the entire current descriptor, not merely an isolated gate. -/
theorem weakAndWitness_satisfies :
    Satisfied2 hash0 compoundPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] weakAndWitness where
  rowConstraints := by
    intro i hi c hc
    have g0 : ((0 : Nat) + 1 == weakAndWitness.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == weakAndWitness.rows.length) = true := rfl
    have hi2 : i < 2 := hi
    clear hi
    simp only [compoundPredicateDesc, compoundConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm,
        gate, piFirst, g0, g1] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp only [compoundPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    rw [cmemLog] at hop
    simp at hop
  memDisciplined := by rw [cmemLog]; trivial
  memBalanced := by rw [cmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [cmemLog]; rfl
  mapTableFaithful := by rw [cmapLog]; rfl

/-- Every value read by the refinement theorem is canonical in the BabyBear field window. -/
theorem weakAndWitness_canon : CompCanon weakAndWitness := by
  refine ⟨?_, ?_, ?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  · intro j hj; interval_cases j <;> exact ⟨by decide, by decide⟩
  · intro j hj; interval_cases j <;> exact ⟨by decide, by decide⟩
  · intro j hj; interval_cases j <;> exact ⟨by decide, by decide⟩
  · intro j hj; interval_cases j <;> exact ⟨by decide, by decide⟩

/-! ## §3 — Exact countermodel: weak spec accepted, genuine AND rejected. -/

theorem weakAndWitness_all_subresults_false :
    ∀ j, j < 8 → (envAt weakAndWitness 0).loc j = 0 := by
  intro j hj
  interval_cases j <;> decide

theorem weakAndWitness_claims_true_and :
    (envAt weakAndWitness 0).loc OP_AND = 1 ∧
      (envAt weakAndWitness 0).loc AND_INT = 1 ∧
      (envAt weakAndWitness 0).loc COMPOSED = 1 ∧
      (envAt weakAndWitness 0).pub 0 = 1 := by
  decide

/-- The current whole-descriptor refinement theorem accepts the witness into its authored, weaker
functional relation. -/
theorem weakAndWitness_compoundClassified :
    CompoundClassified (envAt weakAndWitness 0) :=
  compound_sat_imp_sem (t := weakAndWitness) (by decide) weakAndWitness_satisfies
    weakAndWitness_canon

/-- Yet the witness refutes the genuine AND soundness law: sub-result `0` is false while the selected
AND result is true. -/
theorem weakAndWitness_not_genuineAnd :
    ¬ GenuineAndSound (envAt weakAndWitness 0) := by
  intro h
  have h0 := h (by decide) (by decide) 0 (by decide)
  exact absurd h0 (by decide)

/-- **Countermodel capstone.** `CompoundClassified` is strictly too weak to imply genuine AND
semantics, and the countermodel is inhabited by a trace accepted by `Satisfied2`. -/
theorem satisfied_compound_but_not_genuine_and :
    Satisfied2 hash0 compoundPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] weakAndWitness ∧
      CompoundClassified (envAt weakAndWitness 0) ∧
      ¬ GenuineAndSound (envAt weakAndWitness 0) :=
  ⟨weakAndWitness_satisfies, weakAndWitness_compoundClassified, weakAndWitness_not_genuineAnd⟩

/-! ## §4 — Axiom hygiene. -/

#assert_axioms weakAndWitness_satisfies
#assert_axioms weakAndWitness_canon
#assert_axioms weakAndWitness_all_subresults_false
#assert_axioms weakAndWitness_claims_true_and
#assert_axioms weakAndWitness_compoundClassified
#assert_axioms weakAndWitness_not_genuineAnd
#assert_axioms satisfied_compound_but_not_genuine_and

end Dregg2.Circuit.Emit.PredicatesCompoundWeakCountermodel
