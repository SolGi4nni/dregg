/-
# Dregg2.Metatheory.FOLArithmetizationCounterexamples

Executable countermodels for unsound finite-field readings of Gabbay's
zero-means-true arithmetization of first-order logic, and for the published
BitLogic swap relation.

Gabbay's actual soundness argument is over nonnegative rational-valued
denotations.  There, `a + b = 0` iff both nonnegative operands are zero, so
addition represents conjunction (and a finite sum represents universal
quantification).  A field has no compatible positive cone: nonzero residuals
can cancel.  The generic theorem and the BabyBear instance below make that
failure concrete without criticizing the characteristic-zero construction.

The second counterexample is independent of finite-field cancellation.  The
published BitLogic swap polynomial multiplies three constraints and accepts
when the product is zero.  Under zero-means-true, multiplication is logical OR:
one satisfied factor makes the entire relation accept.  The concrete witness
below satisfies the balance-change factor while violating the pricing and
constant-product factors.

This file is deliberately a standalone attack/regression artifact.  It is not
yet imported by `Dregg2.lean`: the eventual corrected compiler should import it
as a negative conformance suite, alongside positive soundness theorems.
-/
import Dregg2.Tactics
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace Dregg2.Metatheory.FOLArithmetizationCounterexamples

/-! ## Zero-means-true operations -/

/-- The conventional squared residual for equality.  It is zero exactly when
the two inputs agree over a field. -/
def eqResidual {R : Type*} [Ring R] (x y : R) : R := (x - y) ^ 2

/-- Gabbay's conjunction operation: addition of nonnegative residuals. -/
def gabbayAnd {R : Type*} [Add R] (a b : R) : R := a + b

/-- Gabbay's disjunction operation: multiplication of residuals. -/
def gabbayOr {R : Type*} [Mul R] (a b : R) : R := a * b

/-- Multiplying zero-means-true residuals has OR, not AND, semantics in an
integral domain.  This is the connective reversal in the BitLogic formulas. -/
theorem zero_of_mul_iff_or {R : Type*} [CommRing R] [IsDomain R] (a b : R) :
    gabbayOr a b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [gabbayOr]

/-- Any ring containing a square root of `-1` has a two-residual cancellation:
`1` and `r²` are both nonzero, but their purported conjunction is zero.
The nonzero facts are explicit hypotheses because they characterize the
unsound model independently of any particular field. -/
theorem false_and_false_can_accept {R : Type*} [CommRing R]
    (r : R) (hone : (1 : R) ≠ 0) (hr : r ^ 2 = -1) (hr0 : r ^ 2 ≠ 0) :
    (1 : R) ≠ 0 ∧ r ^ 2 ≠ 0 ∧ gabbayAnd 1 (r ^ 2) = 0 := by
  refine ⟨hone, hr0, ?_⟩
  simp [gabbayAnd, hr]

/-! ## A circuit-field countermodel: BabyBear -/

/-- The BabyBear prime used by many STARK implementations. -/
abbrev BabyBear : Type := ZMod 2013265921

local instance babyBearNontrivial : Fact (1 < 2013265921) := ⟨by norm_num⟩

/-- A square root of `-1` in BabyBear. -/
def babyBearSqrtNegOne : BabyBear := 1728404513

theorem babyBear_sqrt_neg_one : babyBearSqrtNegOne ^ 2 = (-1 : BabyBear) := by
  change (((1728404513 : ℤ) : BabyBear) ^ 2) = ((-1 : ℤ) : BabyBear)
  rw [← Int.cast_pow, ZMod.intCast_eq_intCast_iff']
  norm_num

theorem babyBear_sqrt_neg_one_sq_ne_zero :
    babyBearSqrtNegOne ^ 2 ≠ (0 : BabyBear) := by
  rw [babyBear_sqrt_neg_one]
  exact neg_ne_zero.mpr one_ne_zero

/-- **Finite-field conjunction attack.** Both equalities are false, hence both
squared equality residuals are nonzero, but the compiled conjunction is zero
and therefore accepts under the advertised zero-means-true convention. -/
theorem babyBear_false_and_false_accepted :
    eqResidual (0 : BabyBear) 1 ≠ 0 ∧
    eqResidual (0 : BabyBear) babyBearSqrtNegOne ≠ 0 ∧
    gabbayAnd
      (eqResidual (0 : BabyBear) 1)
      (eqResidual (0 : BabyBear) babyBearSqrtNegOne) = 0 := by
  constructor
  · simpa [eqResidual] using (one_ne_zero : (1 : BabyBear) ≠ 0)
  constructor
  · rw [eqResidual, zero_sub, neg_sq, babyBear_sqrt_neg_one]
    exact neg_ne_zero.mpr one_ne_zero
  · rw [eqResidual, eqResidual, zero_sub, zero_sub, neg_sq, neg_sq,
      babyBear_sqrt_neg_one]
    simp [gabbayAnd]

/-- The same cancellation attacks a finite universal quantifier compiled as a
sum: every point in this two-element domain is false, but the sum accepts. -/
theorem babyBear_false_forall_accepted :
    (1 : BabyBear) ≠ 0 ∧ babyBearSqrtNegOne ^ 2 ≠ 0 ∧
    ([1, babyBearSqrtNegOne ^ 2] : List BabyBear).sum = 0 := by
  refine ⟨one_ne_zero, babyBear_sqrt_neg_one_sq_ne_zero, ?_⟩
  simp [babyBear_sqrt_neg_one]

/-- `1 - P` is not a sound general negation operation for residuals.  For the
false residual `P = 2`, the alleged negation is also nonzero (therefore false).
It works only after residuals have first been Booleanized to `{0,1}`. -/
theorem babyBear_one_sub_is_not_general_negation :
    (2 : BabyBear) ≠ 0 ∧ (1 - (2 : BabyBear)) ≠ 0 := by
  constructor
  · intro h
    exact (by norm_num : ¬ 2013265921 ∣ 2)
      ((ZMod.natCast_eq_zero_iff 2 2013265921).mp h)
  · have h : (1 - (2 : BabyBear)) = -1 := by ring
    rw [h]
    exact neg_ne_zero.mpr one_ne_zero

/-! ## Connective and quantifier reversal regressions -/

/-- A product cannot represent universal quantification under zero-means-true:
one true point makes the aggregate accept even though another point is false.
This is the finite-list form of the product-as-OR theorem above. -/
theorem product_is_not_zero_true_forall :
    ([0, 7] : List ℤ).prod = 0 ∧ (7 : ℤ) ≠ 0 := by
  norm_num

/-- A sum cannot represent existential quantification without a positive cone
or Booleanization: two false residuals can cancel and make the aggregate
accept, despite there being no zero residual witness. -/
theorem sum_is_not_zero_true_exists :
    ([1, -1] : List ℤ).sum = 0 ∧
      (1 : ℤ) ≠ 0 ∧ (-1 : ℤ) ≠ 0 := by
  norm_num

/-! ## Published BitLogic swap relation -/

/-- The swap relation printed in the public BitLogic document:

`(A' - A + k) * (B' - B - f(k,s)) * (A*B - A'*B')`.

The document declares zero to mean acceptance. -/
def bitLogicSwapPolynomial {R : Type*} [CommRing R]
    (A B A' B' k quotedOutput : R) : R :=
  (A' - A + k) * (B' - B - quotedOutput) * (A * B - A' * B')

/-- **Transaction-shaped accepting forgery.**  The published relation accepts
this witness because the first factor is zero.  Yet the output/price factor and
the constant-product factor are both nonzero.  This counterexample holds over
the integers and therefore does not depend on field cancellation. -/
theorem published_swap_accepts_invalid_witness :
    let A : ℤ := 10
    let B : ℤ := 10
    let k : ℤ := 1
    let quotedOutput : ℤ := 1
    let A' : ℤ := 9
    let B' : ℤ := 999
    bitLogicSwapPolynomial A B A' B' k quotedOutput = 0 ∧
      B' - B - quotedOutput ≠ 0 ∧
      A * B - A' * B' ≠ 0 := by
  norm_num [bitLogicSwapPolynomial]

/-- The structural reason for the swap forgery: once the balance-change factor
is satisfied, the product accepts regardless of the other two constraints. -/
theorem published_swap_first_factor_bypasses_rest {R : Type*} [CommRing R]
    (A B A' B' k quotedOutput : R) (h : A' - A + k = 0) :
    bitLogicSwapPolynomial A B A' B' k quotedOutput = 0 := by
  simp [bitLogicSwapPolynomial, h]

/-- The bypass is a polynomial identity, not a lucky evaluation point.  Setting
`A' = A - k` makes the published relation vanish for every choice of all other
inputs.  Consequently, evaluating it at a random challenge cannot detect the
two unconstrained downstream relations. -/
theorem published_swap_bypass_is_polynomial_identity {R : Type*} [CommRing R]
    (A B B' k quotedOutput : R) :
    bitLogicSwapPolynomial A B (A - k) B' k quotedOutput = 0 := by
  simp [bitLogicSwapPolynomial]

#assert_all_clean [zero_of_mul_iff_or, false_and_false_can_accept,
  babyBear_sqrt_neg_one, babyBear_sqrt_neg_one_sq_ne_zero,
  babyBear_false_and_false_accepted, babyBear_false_forall_accepted,
  babyBear_one_sub_is_not_general_negation,
  product_is_not_zero_true_forall, sum_is_not_zero_true_exists,
  published_swap_accepts_invalid_witness,
  published_swap_first_factor_bypasses_rest,
  published_swap_bypass_is_polynomial_identity]

end Dregg2.Metatheory.FOLArithmetizationCounterexamples
