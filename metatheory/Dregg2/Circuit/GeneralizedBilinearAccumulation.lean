/-
# Dregg2.Circuit.GeneralizedBilinearAccumulation — an algebraic accumulation floor.

The paper "Proof-Carrying Data via Holography Accumulation" (IACR ePrint 2026/538)
uses generalized bilinear forms to describe public polynomial-evaluation checks which can
be accumulated across recursive steps.  This file deliberately does **not** formalize that
paper's protocol.  It installs a small Dregg-owned algebraic foundation which later protocol
models can refine:

* `GeneralizedBilinearForm F Left Right Out` is a map with possibly different left/right
  modules and an arbitrary output module, linear in each input;
* a `PublicCheck` records one evaluation equality `form left right = target`;
* a finite family is accumulated by a supplied coefficient for each check;
* `accumulation_preserves_check` proves the honest algebraic direction: if every component
  equality holds, then the weighted accumulated equality holds.

## Exact boundary — no cryptographic overclaim

The coefficients are arbitrary data.  This module proves no converse from an accumulated
equality to the component equalities.  Indeed, `cancelling_accumulation_accepts_invalid_family`
below gives two invalid checks whose errors cancel even though both public coefficients are
nonzero.  A protocol-level converse needs additional, explicitly named facts such as random
challenge unpredictability, a field/cardinality bound, an error-polynomial degree bound, and a
commitment/transcript binding theorem.  Nothing here claims SNARK soundness, knowledge extraction,
zero knowledge, hiding, binding, stateless PCD, or compatibility with a concrete polynomial
commitment scheme.

This is therefore an algebra lemma which a future holographic-check model may consume, not a
security theorem and not a drop-in implementation of ePrint 2026/538.
-/
import Mathlib.LinearAlgebra.BilinearMap
import Dregg2.Tactics

namespace Dregg2.Circuit.GeneralizedBilinearAccumulation

universe uF uL uR uO uI

section Algebra

variable {F : Type uF} [CommSemiring F]
variable {Left : Type uL} [AddCommMonoid Left] [Module F Left]
variable {Right : Type uR} [AddCommMonoid Right] [Module F Right]
variable {Out : Type uO} [AddCommMonoid Out] [Module F Out]

/-- A generalized bilinear form: the two input modules may differ and the result may live in
an arbitrary `F`-module.  The nested `LinearMap` type stores linearity in both inputs; no
polynomial, commitment, transcript, or proof-system interpretation is built into the type. -/
abbrev GeneralizedBilinearForm := Left →ₗ[F] Right →ₗ[F] Out

/-- Additivity in the left input, exposed as part of the local foundation's public surface. -/
@[simp] theorem map_add_left (form : GeneralizedBilinearForm (F := F) (Left := Left)
    (Right := Right) (Out := Out)) (x x' : Left) (y : Right) :
    form (x + x') y = form x y + form x' y := by
  simp

/-- Homogeneity in the left input. -/
@[simp] theorem map_smul_left (form : GeneralizedBilinearForm (F := F) (Left := Left)
    (Right := Right) (Out := Out)) (a : F) (x : Left) (y : Right) :
    form (a • x) y = a • form x y := by
  simp

/-- Additivity in the right input. -/
@[simp] theorem map_add_right (form : GeneralizedBilinearForm (F := F) (Left := Left)
    (Right := Right) (Out := Out)) (x : Left) (y y' : Right) :
    form x (y + y') = form x y + form x y' := by
  simp

/-- Homogeneity in the right input. -/
@[simp] theorem map_smul_right (form : GeneralizedBilinearForm (F := F) (Left := Left)
    (Right := Right) (Out := Out)) (a : F) (x : Left) (y : Right) :
    form x (a • y) = a • form x y := by
  simp

/-- Finite public linear combinations of generalized bilinear forms remain generalized
bilinear forms.  This is a purely algebraic combination; `coeff` has no randomness semantics. -/
def weightedForm {I : Type uI} [Fintype I] (coeff : I → F)
    (forms : I → GeneralizedBilinearForm (F := F) (Left := Left)
      (Right := Right) (Out := Out)) :
    GeneralizedBilinearForm (F := F) (Left := Left) (Right := Right) (Out := Out) :=
  ∑ i, coeff i • forms i

/-- Evaluation commutes with the finite weighted combination of forms. -/
@[simp] theorem weightedForm_apply {I : Type uI} [Fintype I] (coeff : I → F)
    (forms : I → GeneralizedBilinearForm (F := F) (Left := Left)
      (Right := Right) (Out := Out)) (x : Left) (y : Right) :
    weightedForm coeff forms x y = ∑ i, coeff i • forms i x y := by
  change ((∑ i, coeff i • forms i) x) y = _
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  simp

/-! ## Minimal finite-family public-check model. -/

/-- One algebraic public check.  "Public" identifies the intended protocol role of the four
values; it does not assert that they are committed, authenticated, or derived by a verifier. -/
structure PublicCheck where
  form : GeneralizedBilinearForm (F := F) (Left := Left) (Right := Right) (Out := Out)
  left : Left
  right : Right
  target : Out

namespace PublicCheck

/-- The component check's exact algebraic predicate. -/
def Holds (check : PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out)) : Prop :=
  check.form check.left check.right = check.target

end PublicCheck

/-- Every check in a finite indexed family holds individually. -/
def FamilyHolds {I : Type uI}
    (checks : I → PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out)) : Prop :=
  ∀ i, (checks i).Holds

/-- The weighted sum of the evaluated left-hand sides. -/
def accumulatedEvaluation {I : Type uI} [Fintype I] (coeff : I → F)
    (checks : I → PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out)) : Out :=
  ∑ i, coeff i • (checks i).form (checks i).left (checks i).right

/-- The weighted sum of the claimed targets. -/
def accumulatedTarget {I : Type uI} [Fintype I] (coeff : I → F)
    (checks : I → PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out)) : Out :=
  ∑ i, coeff i • (checks i).target

/-- The single equality checked by this minimal accumulator. -/
def AccumulatedHolds {I : Type uI} [Fintype I] (coeff : I → F)
    (checks : I → PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out)) : Prop :=
  accumulatedEvaluation coeff checks = accumulatedTarget coeff checks

/-- **Honest algebraic accumulation.** If every component public equality holds, its finite
weighted accumulation also holds.  No property of the coefficients beyond being scalars is used. -/
theorem accumulation_preserves_check {I : Type uI} [Fintype I] (coeff : I → F)
    (checks : I → PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out))
    (holds : FamilyHolds checks) : AccumulatedHolds coeff checks := by
  unfold AccumulatedHolds accumulatedEvaluation accumulatedTarget
  apply Finset.sum_congr rfl
  intro i _hi
  rw [holds i]

/-- Zero coefficients make the accumulated equality hold for every family, independently of
the component checks.  This generic fact is one reason no converse is stated here. -/
theorem zero_coefficients_accumulate_every_family {I : Type uI} [Fintype I]
    (checks : I → PublicCheck (F := F) (Left := Left) (Right := Right) (Out := Out)) :
    AccumulatedHolds (fun _ => 0) checks := by
  simp [AccumulatedHolds, accumulatedEvaluation, accumulatedTarget]

#assert_axioms map_add_left
#assert_axioms map_smul_left
#assert_axioms map_add_right
#assert_axioms map_smul_right
#assert_axioms weightedForm_apply
#assert_axioms accumulation_preserves_check
#assert_axioms zero_coefficients_accumulate_every_family

end Algebra

/-! ## Non-vacuity and the explicit refusal of a soundness converse. -/

namespace Reference

/-- Integer multiplication as a generalized bilinear form. -/
def intMul : GeneralizedBilinearForm (F := ℤ) (Left := ℤ) (Right := ℤ) (Out := ℤ) :=
  LinearMap.lsmul ℤ ℤ

/-- A genuine equality `2·3 = 6`. -/
def validCheck : PublicCheck (F := ℤ) (Left := ℤ) (Right := ℤ) (Out := ℤ) where
  form := intMul
  left := 2
  right := 3
  target := 6

theorem validCheck_holds : validCheck.Holds := by
  norm_num [PublicCheck.Holds, validCheck, intMul]

/-- The headline fires with a nonzero coefficient on a genuinely valid singleton family. -/
theorem nonzero_singleton_accumulation_holds :
    AccumulatedHolds (I := Fin 1) (fun _ => (7 : ℤ)) (fun _ => validCheck) :=
  accumulation_preserves_check _ _ (fun _ => validCheck_holds)

/-- Two individually false equations, `1 = 0` and `1 = 2`.  Their signed errors cancel. -/
def cancellingFamily : Bool → PublicCheck (F := ℤ) (Left := ℤ) (Right := ℤ) (Out := ℤ)
  | false => { form := intMul, left := 1, right := 1, target := 0 }
  | true => { form := intMul, left := 1, right := 1, target := 2 }

/-- Both component checks cannot hold. -/
theorem cancellingFamily_not_holds : ¬ FamilyHolds cancellingFamily := by
  intro holds
  have h := holds false
  norm_num [PublicCheck.Holds, cancellingFamily, intMul] at h

/-- **No deterministic converse.** Both public coefficients are `1`, yet the two invalid
component equalities sum to the valid accumulated equality `2 = 2`.  Turning an accumulated
check into a sound probabilistic test is a separate cryptographic/probabilistic theorem. -/
theorem cancelling_accumulation_accepts_invalid_family :
    AccumulatedHolds (fun _ : Bool => (1 : ℤ)) cancellingFamily := by
  norm_num [AccumulatedHolds, accumulatedEvaluation, accumulatedTarget,
    cancellingFamily, intMul]

#assert_axioms validCheck_holds
#assert_axioms nonzero_singleton_accumulation_holds
#assert_axioms cancellingFamily_not_holds
#assert_axioms cancelling_accumulation_accepts_invalid_family

end Reference

end Dregg2.Circuit.GeneralizedBilinearAccumulation
