/-
# Verified optimizations for direct logic arithmetization

This module turns two recurring compiler ideas into kernel-checked rewrites.

1. Grounded finite quantifiers use a singleton-aware fold.  The reference
   `PositiveFormula.all`/`any` folds a final element against the identity, so
   every nonempty fold materializes one semantically redundant gate.  The
   optimized fold removes exactly that gate.  Theorems below prove source
   semantics and exact equation/multiplication/witness counts.

2. A common Boolean factor is shared before lowering to `BoolGraph.Graph`:

       (p and q) or (p and r)   ~~>   p and (q or r)

   and dually.  The rewrite is field-independent and its symbolic saving is
   exactly one compilation of `p` plus one binary Boolean gate.  This is the
   local theorem needed by a hash-consing/DAG front end when it discovers two
   branches with an identical dominating subformula; it does not assume that
   syntactic equality discovery itself is free.

All cost claims use `ArithmetizationCost.BackendCost`.  They are symbolic
relation counts, not wall-clock or prover-throughput claims.
-/

import Dregg2.Metatheory.ArithmetizationCost

namespace Dregg2.Metatheory.DirectLogicOptimization

open Dregg2.Metatheory.FOLArithmetizationCorrected
open Dregg2.Metatheory.ArithmetizationCost
open Dregg2.Metatheory.ArithmetizationCost.BackendCost

/-! ## 1. Singleton-aware finite quantifier folds -/

namespace QuantifierFold

open PositiveFormula

/-- Grounded universal fold with no gate against `top` in the singleton case. -/
def allOpt {Atom : Type*} : List (PositiveFormula Atom) → PositiveFormula Atom
  | [] => .top
  | [p] => p
  | p :: q :: ps => .and p (allOpt (q :: ps))
termination_by ps => ps.length

/-- Grounded existential fold with no gate against `bottom` in the singleton case. -/
def anyOpt {Atom : Type*} : List (PositiveFormula Atom) → PositiveFormula Atom
  | [] => .bottom
  | [p] => p
  | p :: q :: ps => .or p (anyOpt (q :: ps))
termination_by ps => ps.length

theorem holds_allOpt {Atom : Type*} (truth : Atom → Prop)
    (ps : List (PositiveFormula Atom)) :
    Holds truth (allOpt ps) ↔ ∀ p, p ∈ ps → Holds truth p := by
  induction ps with
  | nil => simp [allOpt, Holds]
  | cons p ps ih =>
      cases ps with
      | nil => simp [allOpt]
      | cons q qs => simp [allOpt, Holds, ih]

theorem holds_anyOpt {Atom : Type*} (truth : Atom → Prop)
    (ps : List (PositiveFormula Atom)) :
    Holds truth (anyOpt ps) ↔ ∃ p, p ∈ ps ∧ Holds truth p := by
  induction ps with
  | nil => simp [anyOpt, Holds]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs => simp [anyOpt, Holds, ih]

/-- The optimized fold has exactly the same logical meaning as the original
reference fold, including both empty-range conventions. -/
theorem allOpt_iff_all {Atom : Type*} (truth : Atom → Prop)
    (ps : List (PositiveFormula Atom)) :
    Holds truth (allOpt ps) ↔ Holds truth (PositiveFormula.all ps) := by
  rw [holds_allOpt, PositiveFormula.holds_all]

theorem anyOpt_iff_any {Atom : Type*} (truth : Atom → Prop)
    (ps : List (PositiveFormula Atom)) :
    Holds truth (anyOpt ps) ↔ Holds truth (PositiveFormula.any ps) := by
  rw [holds_anyOpt, PositiveFormula.holds_any]

open Dregg2.Metatheory.ArithmetizationCost.Positive

theorem allOpt_equations {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (allOpt ps)).equations =
      (ps.map fun p => (cost atomCost p).equations).sum + (ps.length - 1) := by
  induction ps with
  | nil => simp [allOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [allOpt]
      | cons q qs =>
          simp only [allOpt, cost, combine_equations, positiveAndGateCost]
          rw [ih]
          simp
          omega

theorem anyOpt_equations {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (anyOpt ps)).equations =
      (ps.map fun p => (cost atomCost p).equations).sum + (ps.length - 1) := by
  induction ps with
  | nil => simp [anyOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs =>
          simp only [anyOpt, cost, combine_equations, positiveOrGateCost]
          rw [ih]
          simp
          omega

theorem allOpt_multiplications {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (allOpt ps)).multiplications =
      (ps.map fun p => (cost atomCost p).multiplications).sum := by
  induction ps with
  | nil => simp [allOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [allOpt]
      | cons q qs =>
          simp only [allOpt, cost, combine_multiplications, positiveAndGateCost]
          rw [ih]
          simp

theorem anyOpt_multiplications {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (anyOpt ps)).multiplications =
      (ps.map fun p => (cost atomCost p).multiplications).sum + (ps.length - 1) := by
  induction ps with
  | nil => simp [anyOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs =>
          simp only [anyOpt, cost, combine_multiplications, positiveOrGateCost]
          rw [ih]
          simp
          omega

theorem allOpt_witnesses {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (allOpt ps)).witnesses =
      (ps.map fun p => (cost atomCost p).witnesses).sum + (ps.length - 1) := by
  induction ps with
  | nil => simp [allOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [allOpt]
      | cons q qs =>
          simp only [allOpt, cost, combine_witnesses, positiveAndGateCost]
          rw [ih]
          simp
          omega

theorem anyOpt_witnesses {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (anyOpt ps)).witnesses =
      (ps.map fun p => (cost atomCost p).witnesses).sum + (ps.length - 1) := by
  induction ps with
  | nil => simp [anyOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs =>
          simp only [anyOpt, cost, combine_witnesses, positiveOrGateCost]
          rw [ih]
          simp
          omega

/-- Witness recurrence for the reference universal fold. -/
theorem reference_all_witnesses {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (PositiveFormula.all ps)).witnesses =
      (ps.map fun p => (cost atomCost p).witnesses).sum + ps.length := by
  induction ps with
  | nil => simp [PositiveFormula.all, cost, zero]
  | cons p ps ih =>
      simp [PositiveFormula.all, cost, ih, positiveAndGateCost,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem reference_any_witnesses {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (PositiveFormula.any ps)).witnesses =
      (ps.map fun p => (cost atomCost p).witnesses).sum + ps.length := by
  induction ps with
  | nil => simp [PositiveFormula.any, cost, zero]
  | cons p ps ih =>
      simp [PositiveFormula.any, cost, ih, positiveOrGateCost,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every nonempty universal fold removes exactly one equation and one fresh
wire from the reference construction.  Universal conjunction-as-addition has
no multiplication to remove. -/
theorem all_nonempty_exact_saving {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) (hne : ps ≠ []) :
    (cost atomCost (PositiveFormula.all ps)).equations =
        (cost atomCost (allOpt ps)).equations + 1 ∧
    (cost atomCost (PositiveFormula.all ps)).multiplications =
        (cost atomCost (allOpt ps)).multiplications ∧
    (cost atomCost (PositiveFormula.all ps)).witnesses =
        (cost atomCost (allOpt ps)).witnesses + 1 := by
  have hlen : 0 < ps.length := by
    cases ps with
    | nil => contradiction
    | cons p ps => simp
  constructor
  · rw [Positive.all_equations, allOpt_equations]
    omega
  constructor
  · rw [Positive.all_multiplications, allOpt_multiplications]
  · rw [reference_all_witnesses, allOpt_witnesses]
    omega

/-- Every nonempty existential fold removes exactly one multiplication, one
equation, and one fresh wire: the product with the `bottom` identity. -/
theorem any_nonempty_exact_saving {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) (hne : ps ≠ []) :
    (cost atomCost (PositiveFormula.any ps)).equations =
        (cost atomCost (anyOpt ps)).equations + 1 ∧
    (cost atomCost (PositiveFormula.any ps)).multiplications =
        (cost atomCost (anyOpt ps)).multiplications + 1 ∧
    (cost atomCost (PositiveFormula.any ps)).witnesses =
        (cost atomCost (anyOpt ps)).witnesses + 1 := by
  have hlen : 0 < ps.length := by
    cases ps with
    | nil => contradiction
    | cons p ps => simp
  constructor
  · rw [Positive.any_equations, anyOpt_equations]
    omega
  constructor
  · rw [Positive.any_multiplications, anyOpt_multiplications]
    omega
  · rw [reference_any_witnesses, anyOpt_witnesses]
    omega

end QuantifierFold

/-! ## 2. Common-factor sharing for the exact Boolean graph -/

namespace CommonFactor

open Dregg2.Logic.BoolGraph
open Dregg2.Metatheory.ArithmetizationCost.BooleanGraph

/-- Tree-shaped source before a common conjunction factor is shared. -/
def duplicatedAnd {Atom : Type*} (p q r : Formula Atom) : Formula Atom :=
  .or (.and p q) (.and p r)

/-- Factored source: `p` is compiled once and its output wire is fanned out. -/
def sharedAnd {Atom : Type*} (p q r : Formula Atom) : Formula Atom :=
  .and p (.or q r)

/-- Dual tree-shaped source before a common disjunction factor is shared. -/
def duplicatedOr {Atom : Type*} (p q r : Formula Atom) : Formula Atom :=
  .and (.or p q) (.or p r)

/-- Dual factored source. -/
def sharedOr {Atom : Type*} (p q r : Formula Atom) : Formula Atom :=
  .or p (.and q r)

theorem sharedAnd_eval_iff {F Atom : Type*} [Field F]
    (residual : Atom → F) (p q r : Formula Atom) :
    Eval residual (sharedAnd p q r) ↔ Eval residual (duplicatedAnd p q r) := by
  simp [sharedAnd, duplicatedAnd, Eval, and_or_left]

theorem sharedOr_eval_iff {F Atom : Type*} [Field F]
    (residual : Atom → F) (p q r : Formula Atom) :
    Eval residual (sharedOr p q r) ↔ Eval residual (duplicatedOr p q r) := by
  simp [sharedOr, duplicatedOr, Eval, or_and_left]

/-- The actual corrected compiler accepts the shared and duplicated forms in
exactly the same field environments. -/
theorem sharedAnd_accepts_iff {F Atom : Type*} [Field F]
    (residual : Atom → F) (p q r : Formula Atom) :
    Accepts residual (sharedAnd p q r) ↔ Accepts residual (duplicatedAnd p q r) := by
  rw [compile_exact, compile_exact, sharedAnd_eval_iff]

theorem sharedOr_accepts_iff {F Atom : Type*} [Field F]
    (residual : Atom → F) (p q r : Formula Atom) :
    Accepts residual (sharedOr p q r) ↔ Accepts residual (duplicatedOr p q r) := by
  rw [compile_exact, compile_exact, sharedOr_eval_iff]

/-! ### Arbitrary fanout -/

/-- Singleton-aware Boolean disjunction.  Unlike `OrFoldGraph`, this source
constructor does not materialize a gate against the false identity. -/
def anyOpt {Atom : Type*} : List (Formula Atom) → Formula Atom
  | [] => .bot
  | [p] => p
  | p :: q :: ps => .or p (anyOpt (q :: ps))
termination_by ps => ps.length

theorem eval_anyOpt {F Atom : Type*} [Field F] (residual : Atom → F)
    (ps : List (Formula Atom)) :
    Eval residual (anyOpt ps) ↔ ∃ p, p ∈ ps ∧ Eval residual p := by
  induction ps with
  | nil => simp [anyOpt, Eval]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs => simp [anyOpt, Eval, ih]

/-- Tree expansion of a common factor over an arbitrary fanout. -/
def duplicatedAndMany {Atom : Type*} (p : Formula Atom)
    (qs : List (Formula Atom)) : Formula Atom :=
  anyOpt (qs.map fun q => .and p q)

/-- DAG-friendly form: compile `p` once, then fan its output into the fold. -/
def sharedAndMany {Atom : Type*} (p : Formula Atom)
    (qs : List (Formula Atom)) : Formula Atom :=
  match qs with
  | [] => .bot
  | _ :: _ => .and p (anyOpt qs)

theorem sharedAndMany_eval_iff {F Atom : Type*} [Field F]
    (residual : Atom → F) (p : Formula Atom) (qs : List (Formula Atom)) :
    Eval residual (sharedAndMany p qs) ↔
      Eval residual (duplicatedAndMany p qs) := by
  cases qs with
  | nil => simp [sharedAndMany, duplicatedAndMany, anyOpt, Eval]
  | cons q qs =>
      rw [duplicatedAndMany, eval_anyOpt]
      simp only [List.mem_map]
      rw [show sharedAndMany p (q :: qs) = .and p (anyOpt (q :: qs)) by rfl]
      rw [Eval, eval_anyOpt]
      constructor
      · rintro ⟨hp, r, hr, hqr⟩
        exact ⟨.and p r, ⟨r, hr, rfl⟩, hp, hqr⟩
      · rintro ⟨candidate, ⟨r, hr, rfl⟩, hp, hqr⟩
        exact ⟨hp, r, hr, hqr⟩

theorem sharedAndMany_accepts_iff {F Atom : Type*} [Field F]
    (residual : Atom → F) (p : Formula Atom) (qs : List (Formula Atom)) :
    Accepts residual (sharedAndMany p qs) ↔
      Accepts residual (duplicatedAndMany p qs) := by
  rw [compile_exact, compile_exact, sharedAndMany_eval_iff]

theorem anyOpt_equations {Atom : Type*} (ps : List (Formula Atom)) :
    (cost (anyOpt ps)).equations =
      (ps.map fun p => (cost p).equations).sum + 2 * (ps.length - 1) := by
  induction ps with
  | nil => simp [anyOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs =>
          simp only [anyOpt, cost, combine_equations, booleanBinaryGateCost]
          rw [ih]
          simp
          omega

theorem anyOpt_multiplications {Atom : Type*} (ps : List (Formula Atom)) :
    (cost (anyOpt ps)).multiplications =
      (ps.map fun p => (cost p).multiplications).sum + 2 * (ps.length - 1) := by
  induction ps with
  | nil => simp [anyOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs =>
          simp only [anyOpt, cost, combine_multiplications, booleanBinaryGateCost]
          rw [ih]
          simp
          omega

theorem anyOpt_witnesses {Atom : Type*} (ps : List (Formula Atom)) :
    (cost (anyOpt ps)).witnesses =
      (ps.map fun p => (cost p).witnesses).sum + (ps.length - 1) := by
  induction ps with
  | nil => simp [anyOpt, cost, zero]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs =>
          simp only [anyOpt, cost, combine_witnesses, booleanBinaryGateCost]
          rw [ih]
          simp
          omega

theorem mappedAnd_equations {Atom : Type*} (p : Formula Atom)
    (qs : List (Formula Atom)) :
    ((qs.map fun q => .and p q).map fun f => (cost f).equations).sum =
      qs.length * ((cost p).equations + 2) +
        (qs.map fun q => (cost q).equations).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_map] at ih ⊢
      simp [cost, booleanBinaryGateCost, ih, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem mappedAnd_multiplications {Atom : Type*} (p : Formula Atom)
    (qs : List (Formula Atom)) :
    ((qs.map fun q => .and p q).map fun f => (cost f).multiplications).sum =
      qs.length * ((cost p).multiplications + 2) +
        (qs.map fun q => (cost q).multiplications).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_map] at ih ⊢
      simp [cost, booleanBinaryGateCost, ih, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem mappedAnd_witnesses {Atom : Type*} (p : Formula Atom)
    (qs : List (Formula Atom)) :
    ((qs.map fun q => .and p q).map fun f => (cost f).witnesses).sum =
      qs.length * ((cost p).witnesses + 1) +
        (qs.map fun q => (cost q).witnesses).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_map] at ih ⊢
      simp [cost, booleanBinaryGateCost, ih, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- With `n` consumers of a common `p`, factoring saves exactly `n-1`
compilations of `p` and `n-1` binary Boolean gates. -/
theorem sharedAndMany_exact_saving {Atom : Type*} (p : Formula Atom)
    (qs : List (Formula Atom)) (hne : qs ≠ []) :
    (cost (duplicatedAndMany p qs)).equations =
        (cost (sharedAndMany p qs)).equations +
          (qs.length - 1) * ((cost p).equations + 2) ∧
    (cost (duplicatedAndMany p qs)).multiplications =
        (cost (sharedAndMany p qs)).multiplications +
          (qs.length - 1) * ((cost p).multiplications + 2) ∧
    (cost (duplicatedAndMany p qs)).witnesses =
        (cost (sharedAndMany p qs)).witnesses +
          (qs.length - 1) * ((cost p).witnesses + 1) := by
  constructor
  · rw [duplicatedAndMany, anyOpt_equations, mappedAnd_equations]
    cases qs with
    | nil => contradiction
    | cons q qs =>
        simp only [sharedAndMany, List.map_cons, List.sum_cons, List.length_cons,
          cost, combine_equations, booleanBinaryGateCost]
        rw [anyOpt_equations]
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  constructor
  · rw [duplicatedAndMany, anyOpt_multiplications, mappedAnd_multiplications]
    cases qs with
    | nil => contradiction
    | cons q qs =>
        simp only [sharedAndMany, List.map_cons, List.sum_cons, List.length_cons,
          cost, combine_multiplications, booleanBinaryGateCost]
        rw [anyOpt_multiplications]
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · rw [duplicatedAndMany, anyOpt_witnesses, mappedAnd_witnesses]
    cases qs with
    | nil => contradiction
    | cons q qs =>
        simp only [sharedAndMany, List.map_cons, List.sum_cons, List.length_cons,
          cost, combine_witnesses, booleanBinaryGateCost]
        rw [anyOpt_witnesses]
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact cost delta of common-factor sharing: the duplicated form compiles
one extra copy of `p` and one extra binary gate. -/
theorem sharedAnd_exact_saving {Atom : Type*} (p q r : Formula Atom) :
    (cost (duplicatedAnd p q r)).equations =
        (cost (sharedAnd p q r)).equations + (cost p).equations + 2 ∧
    (cost (duplicatedAnd p q r)).multiplications =
        (cost (sharedAnd p q r)).multiplications + (cost p).multiplications + 2 ∧
    (cost (duplicatedAnd p q r)).witnesses =
        (cost (sharedAnd p q r)).witnesses + (cost p).witnesses + 1 := by
  constructor <;> simp [duplicatedAnd, sharedAnd, cost, booleanBinaryGateCost,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sharedOr_exact_saving {Atom : Type*} (p q r : Formula Atom) :
    (cost (duplicatedOr p q r)).equations =
        (cost (sharedOr p q r)).equations + (cost p).equations + 2 ∧
    (cost (duplicatedOr p q r)).multiplications =
        (cost (sharedOr p q r)).multiplications + (cost p).multiplications + 2 ∧
    (cost (duplicatedOr p q r)).witnesses =
        (cost (sharedOr p q r)).witnesses + (cost p).witnesses + 1 := by
  constructor <;> simp [duplicatedOr, sharedOr, cost, booleanBinaryGateCost,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem duplicatedAnd_degree_eq_two {Atom : Type*} (p q r : Formula Atom) :
    (cost (duplicatedAnd p q r)).maxDegree = 2 := by
  have hp := degree_le_two p
  have hq := degree_le_two q
  have hr := degree_le_two r
  simp [duplicatedAnd, cost, booleanBinaryGateCost,
    Nat.max_eq_right hp, Nat.max_eq_right hq, Nat.max_eq_right hr]

theorem sharedAnd_degree_eq_two {Atom : Type*} (p q r : Formula Atom) :
    (cost (sharedAnd p q r)).maxDegree = 2 := by
  have hp := degree_le_two p
  have hq := degree_le_two q
  have hr := degree_le_two r
  simp [sharedAnd, cost, booleanBinaryGateCost,
    Nat.max_eq_right hp, Nat.max_eq_right hq, Nat.max_eq_right hr]

theorem duplicatedOr_degree_eq_two {Atom : Type*} (p q r : Formula Atom) :
    (cost (duplicatedOr p q r)).maxDegree = 2 := by
  have hp := degree_le_two p
  have hq := degree_le_two q
  have hr := degree_le_two r
  simp [duplicatedOr, cost, booleanBinaryGateCost,
    Nat.max_eq_right hp, Nat.max_eq_right hq, Nat.max_eq_right hr]

theorem sharedOr_degree_eq_two {Atom : Type*} (p q r : Formula Atom) :
    (cost (sharedOr p q r)).maxDegree = 2 := by
  have hp := degree_le_two p
  have hq := degree_le_two q
  have hr := degree_le_two r
  simp [sharedOr, cost, booleanBinaryGateCost,
    Nat.max_eq_right hp, Nat.max_eq_right hq, Nat.max_eq_right hr]

/-! ### Concrete nontrivial specimen -/

def specimenP : Formula Nat := .and (.atom 0) (.not (.atom 1))
def specimenQ : Formula Nat := .or (.atom 2) (.atom 3)
def specimenR : Formula Nat := .and (.atom 4) (.atom 5)

/-- Sharing the two-gate `specimenP` saves its entire 10-equation compilation
plus one two-equation binary gate: 12 equations total. -/
theorem specimen_equations :
    (cost (duplicatedAnd specimenP specimenQ specimenR)).equations = 42 ∧
    (cost (sharedAnd specimenP specimenQ specimenR)).equations = 30 := by
  decide

theorem specimen_multiplications :
    (cost (duplicatedAnd specimenP specimenQ specimenR)).multiplications = 40 ∧
    (cost (sharedAnd specimenP specimenQ specimenR)).multiplications = 29 := by
  decide

theorem specimen_witnesses :
    (cost (duplicatedAnd specimenP specimenQ specimenR)).witnesses = 25 ∧
    (cost (sharedAnd specimenP specimenQ specimenR)).witnesses = 18 := by
  decide

end CommonFactor

#assert_all_clean [
  QuantifierFold.holds_allOpt,
  QuantifierFold.holds_anyOpt,
  QuantifierFold.allOpt_iff_all,
  QuantifierFold.anyOpt_iff_any,
  QuantifierFold.allOpt_equations,
  QuantifierFold.anyOpt_equations,
  QuantifierFold.allOpt_multiplications,
  QuantifierFold.anyOpt_multiplications,
  QuantifierFold.allOpt_witnesses,
  QuantifierFold.anyOpt_witnesses,
  QuantifierFold.reference_all_witnesses,
  QuantifierFold.reference_any_witnesses,
  QuantifierFold.all_nonempty_exact_saving,
  QuantifierFold.any_nonempty_exact_saving,
  CommonFactor.sharedAnd_eval_iff,
  CommonFactor.sharedOr_eval_iff,
  CommonFactor.sharedAnd_accepts_iff,
  CommonFactor.sharedOr_accepts_iff,
  CommonFactor.eval_anyOpt,
  CommonFactor.sharedAndMany_eval_iff,
  CommonFactor.sharedAndMany_accepts_iff,
  CommonFactor.anyOpt_equations,
  CommonFactor.anyOpt_multiplications,
  CommonFactor.anyOpt_witnesses,
  CommonFactor.mappedAnd_equations,
  CommonFactor.mappedAnd_multiplications,
  CommonFactor.mappedAnd_witnesses,
  CommonFactor.sharedAndMany_exact_saving,
  CommonFactor.sharedAnd_exact_saving,
  CommonFactor.sharedOr_exact_saving,
  CommonFactor.duplicatedAnd_degree_eq_two,
  CommonFactor.sharedAnd_degree_eq_two,
  CommonFactor.duplicatedOr_degree_eq_two,
  CommonFactor.sharedOr_degree_eq_two,
  CommonFactor.specimen_equations,
  CommonFactor.specimen_multiplications,
  CommonFactor.specimen_witnesses
]

end Dregg2.Metatheory.DirectLogicOptimization
