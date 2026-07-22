/-
# Sound projection of integer and rational zero claims to prime fields

Characteristic-zero arithmetic does not become a sound finite-field relation
merely by reducing its result modulo a prime.  This file isolates the exact
obligations for that boundary:

* an integer maps to zero modulo `p` exactly when `p` divides it;
* therefore a nonzero integer has only a finite, explicitly enumerated set of
  bad primes;
* a deterministic `natAbs < p` bound rules every such prime out;
* a rational projection is defined only with an invertible denominator, and
  its zero test then reduces exactly to the numerator zero test;
* these facts compose with the positive-formula compiler without adding any
  probabilistic assumption.

The bounds here are sufficient, deliberately simple, and theorem-bearing.
They are not represented as performance claims: symbolic relation costs remain
in `ArithmetizationCost`, while choosing and checking a modulus is a compilation
boundary obligation.
-/
import Dregg2.Metatheory.ArithmetizationCost
import Mathlib.Data.Int.Basic

namespace Dregg2.Metatheory.IntegerProjectionSoundness

open Dregg2.Metatheory.FOLArithmetizationCorrected
open Dregg2.Metatheory.FOLArithmetizationCorrected.PositiveFormula

/-! ## Integer projection and its exact obstruction -/

/-- The native integer projection used at the characteristic-zero/field
boundary.  Naming the map makes it harder to confuse equality in `Int` with
equality after reduction. -/
def integerProjection (p : Nat) (z : Int) : ZMod p := z

/-- Reduction accepts an integer zero claim exactly when the modulus divides
the claimed integer.  Primality is not needed for this statement. -/
theorem integerProjection_eq_zero_iff_dvd (p : Nat) (z : Int) :
    integerProjection p z = 0 <-> (p : Int) ∣ z := by
  exact ZMod.intCast_zmod_eq_zero_iff_dvd z p

/-- A deterministic no-wrap theorem.  If the modulus is larger than the
absolute value of the integer, field zero is equivalent to integer zero.
This is stronger than a probabilistic bad-prime estimate and does not even
require that the modulus be prime. -/
theorem integerProjection_eq_zero_iff_of_natAbs_lt {p : Nat} {z : Int}
    (hbound : z.natAbs < p) :
    integerProjection p z = 0 <-> z = 0 := by
  constructor
  · intro hzero
    have hdvd : (p : Int) ∣ z :=
      (integerProjection_eq_zero_iff_dvd p z).mp hzero
    by_contra hz
    have hle : p ≤ z.natAbs := by
      simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hz
    exact (Nat.not_lt_of_ge hle) hbound
  · rintro rfl
    simp [integerProjection]

/-- All possible bad primes for a fixed integer are explicitly contained in
this finite set.  Filtering by divisibility makes the set exact for nonzero
integers, rather than merely bounding its cardinality. -/
def badPrimes (z : Int) : Finset Nat :=
  (Finset.range (z.natAbs + 1)).filter
    (fun p => Nat.Prime p ∧ (p : Int) ∣ z)

/-- For a nonzero integer, membership in `badPrimes` is exactly "prime and the
field projection accepts".  This is the finite bad-prime obstruction. -/
theorem mem_badPrimes_iff {z : Int} (hz : z ≠ 0) (p : Nat) :
    p ∈ badPrimes z <-> Nat.Prime p ∧ integerProjection p z = 0 := by
  constructor
  · intro h
    have h' : Nat.Prime p ∧ (p : Int) ∣ z :=
      (Finset.mem_filter.mp h).2
    exact ⟨h'.1, (integerProjection_eq_zero_iff_dvd p z).mpr h'.2⟩
  · rintro ⟨hp, hzero⟩
    have hdvd : (p : Int) ∣ z :=
      (integerProjection_eq_zero_iff_dvd p z).mp hzero
    have hle : p ≤ z.natAbs := by
      simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hz
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle), hp, hdvd⟩

/-- Concrete tooth: reduction modulo the bad prime five accepts the false
integer statement `5 = 0`. -/
theorem bad_prime_five_accepts_false_integer :
    integerProjection 5 5 = 0 ∧ (5 : Int) ≠ 0 := by
  constructor
  · apply (integerProjection_eq_zero_iff_dvd 5 5).mpr
    exact ⟨1, by norm_num⟩
  · norm_num

/-! ## Rational projection: denominator obligations are explicit -/

/-- Project a native rational through its canonical numerator and denominator.
The prime-field instance is explicit in the type.  Sound use additionally
requires `rationalDenominatorAdmissible`, proved or checked below. -/
def rationalProjection {p : Nat} [Fact p.Prime] (q : Rat) : ZMod p :=
  (q.num : ZMod p) * (q.den : ZMod p)⁻¹

/-- The characteristic-zero canonical denominator is always nonzero. -/
theorem rational_denominator_ne_zero (q : Rat) : q.den ≠ 0 :=
  q.den_ne_zero

/-- Field well-definedness is a separate obligation: the canonical
denominator must remain nonzero after reduction. -/
def rationalDenominatorAdmissible (p : Nat) (q : Rat) : Prop :=
  (q.den : ZMod p) ≠ 0

/-- Denominator admissibility is exactly non-divisibility by the modulus. -/
theorem rationalDenominatorAdmissible_iff (p : Nat) (q : Rat) :
    rationalDenominatorAdmissible p q <-> ¬p ∣ q.den := by
  simp [rationalDenominatorAdmissible, ZMod.natCast_eq_zero_iff]

/-- An explicit denominator bound is a sufficient field-well-definedness
certificate. -/
theorem rationalDenominatorAdmissible_of_lt {p : Nat} {q : Rat}
    (hden : q.den < p) : rationalDenominatorAdmissible p q := by
  intro hzero
  have : q.den = 0 :=
    (FOLArithmetizationCorrected.zmod_natCast_eq_zero_iff_of_lt hden).mp hzero
  exact q.den_ne_zero this

/-- Once the denominator is admissible, a rational projection is zero exactly
when its numerator projection is zero. -/
theorem rationalProjection_eq_zero_iff_numCast {p : Nat} [Fact p.Prime]
    {q : Rat} (hden : rationalDenominatorAdmissible p q) :
    rationalProjection (p := p) q = 0 <-> (q.num : ZMod p) = 0 := by
  unfold rationalDenominatorAdmissible at hden
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hnum | hinv
    · exact hnum
    · exact False.elim (hden (inv_eq_zero.mp hinv))
  · intro hnum
    simp [rationalProjection, hnum]

/-- Equivalently, rational projection accepts exactly when the modulus divides
the canonical numerator, provided the denominator is admissible. -/
theorem rationalProjection_eq_zero_iff_num_dvd {p : Nat} [Fact p.Prime]
    {q : Rat} (hden : rationalDenominatorAdmissible p q) :
    rationalProjection (p := p) q = 0 <-> (p : Int) ∣ q.num := by
  rw [rationalProjection_eq_zero_iff_numCast hden]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd q.num p

/-- Complete deterministic rational no-wrap theorem.  The denominator bound
ensures that the projection is defined in the field; the numerator bound rules
out every bad prime. -/
theorem rationalProjection_eq_zero_iff_of_bounds {p : Nat} [Fact p.Prime]
    {q : Rat} (hnum : q.num.natAbs < p) (hden : q.den < p) :
    rationalProjection (p := p) q = 0 <-> q = 0 := by
  rw [rationalProjection_eq_zero_iff_numCast
    (rationalDenominatorAdmissible_of_lt hden)]
  change integerProjection p q.num = 0 <-> q = 0
  rw [integerProjection_eq_zero_iff_of_natAbs_lt hnum]
  exact Rat.zero_iff_num_zero.symm

/-- For a false rational zero claim with an admissible denominator, every
accepting prime lies in the finite bad-prime set of its numerator. -/
theorem false_rational_acceptance_mem_badPrimes {p : Nat} [Fact p.Prime]
    {q : Rat} (hq : q ≠ 0) (hden : rationalDenominatorAdmissible p q)
    (haccept : rationalProjection (p := p) q = 0) :
    p ∈ badPrimes q.num := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  apply (mem_badPrimes_iff hnum p).mpr
  refine ⟨Fact.out, ?_⟩
  exact (rationalProjection_eq_zero_iff_numCast hden).mp haccept

/-! ## Composition with the exact positive-formula compiler -/

/-- Integers with a nonnegativity invariant satisfy the same zero-true laws as
Gabbay's nonnegative rationals. -/
def nonnegativeIntegerLaws : ZeroTrueLaws Int where
  good z := 0 ≤ z
  zero_good := by norm_num
  one_good := by norm_num
  add_good := by intro a b ha hb; omega
  mul_good := by intro a b ha hb; exact mul_nonneg ha hb
  add_eq_zero_iff := by
    intro a b ha hb
    constructor
    · intro h
      constructor <;> omega
    · rintro ⟨rfl, rfl⟩
      simp
  mul_eq_zero_iff := by
    intro a b _ _
    exact mul_eq_zero

/-- Integer positive formulas remain exact after projection whenever the
complete characteristic-zero residual satisfies the no-wrap bound. -/
theorem integer_positive_formula_projection_sound
    {Atom : Type*} {p : Nat}
    (truth : Atom -> Prop) (atomResidual : Atom -> Int)
    (hatomGood : forall a, 0 ≤ atomResidual a)
    (hatomCorrect : forall a, atomResidual a = 0 <-> truth a)
    (formula : PositiveFormula Atom)
    (hbound : (residual atomResidual formula).natAbs < p) :
    integerProjection p (residual atomResidual formula) = 0 <->
      Holds truth formula := by
  rw [integerProjection_eq_zero_iff_of_natAbs_lt hbound]
  exact residual_eq_zero_iff nonnegativeIntegerLaws truth atomResidual
    hatomGood hatomCorrect formula

/-- Rational positive formulas likewise compose soundly.  Both numerator and
denominator bounds are attached to the final compiled residual, so no hidden
per-gate or probabilistic premise is smuggled into the result. -/
theorem rational_positive_formula_projection_sound
    {Atom : Type*} {p : Nat} [Fact p.Prime]
    (truth : Atom -> Prop) (atomResidual : Atom -> Rat)
    (hatomGood : forall a, 0 ≤ atomResidual a)
    (hatomCorrect : forall a, atomResidual a = 0 <-> truth a)
    (formula : PositiveFormula Atom)
    (hnum : (residual atomResidual formula).num.natAbs < p)
    (hden : (residual atomResidual formula).den < p) :
    rationalProjection (p := p) (residual atomResidual formula) = 0 <->
      Holds truth formula := by
  rw [rationalProjection_eq_zero_iff_of_bounds hnum hden]
  exact residual_eq_zero_iff nonnegativeRationalLaws truth atomResidual
    hatomGood hatomCorrect formula

#assert_all_clean [
  integerProjection_eq_zero_iff_dvd,
  integerProjection_eq_zero_iff_of_natAbs_lt,
  mem_badPrimes_iff,
  bad_prime_five_accepts_false_integer,
  rational_denominator_ne_zero,
  rationalDenominatorAdmissible_iff,
  rationalDenominatorAdmissible_of_lt,
  rationalProjection_eq_zero_iff_numCast,
  rationalProjection_eq_zero_iff_num_dvd,
  rationalProjection_eq_zero_iff_of_bounds,
  false_rational_acceptance_mem_badPrimes,
  integer_positive_formula_projection_sound,
  rational_positive_formula_projection_sound]

end Dregg2.Metatheory.IntegerProjectionSoundness
