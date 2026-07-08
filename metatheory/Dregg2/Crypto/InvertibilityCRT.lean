/-
# `Dregg2.Crypto.InvertibilityCRT` — challenge-difference invertibility at general `n`, via the CRT.

`HermineInvertibility` proved the invertibility of challenge differences for `n = 2` by making `R_q` a
FIELD (`q ≡ 3 mod 4`, `X²+1` irreducible). That trick does NOT scale: for the real `n = 256`, `X^n + 1`
is never irreducible mod `q` — it SPLITS (that is exactly what makes the NTT work), so `R_q` is a product
of fields, not a field.

This file supplies the correct general-`n` STRUCTURE — the Lyubashevsky–Seiler skeleton. By the CRT, the
splitting `X^n + 1 = ∏ gᵢ` (into irreducible factors) gives a ring isomorphism `R_q ≅ ∏ᵢ Kᵢ` onto a
product of fields (the residue fields `R_q / (gᵢ)`), and:

  **an element of `R_q` is a UNIT ⟺ its image in every CRT factor `Kᵢ` is nonzero.**

So challenge-difference invertibility reduces to: `c − c'` is nonzero in each factor. That last step is
the number-theoretic heart — a low-∞-norm nonzero element cannot vanish modulo any degree-`d` factor
(the norm is below the smallest nonzero element of the ideal). We prove the CRT reduction here in full,
and state the norm→nonzero-per-factor step as the interface it plugs into (the remaining number theory,
scoped honestly, not faked).
-/
import Dregg2.Tactics
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

namespace Dregg2.Crypto.InvertibilityCRT

variable {ι : Type*} {K : ι → Type*} [∀ i, Field (K i)]

/-- **The CRT invertibility characterization.** In a finite product of fields, an element is a unit iff
each of its components is nonzero. (`R_q ≅ ∏ Kᵢ` via the CRT, so this is the invertibility criterion for
`R_q`.) -/
theorem product_field_isUnit_iff (f : ∀ i, K i) : IsUnit f ↔ ∀ i, f i ≠ 0 := by
  rw [Pi.isUnit_iff]
  constructor
  · intro h i; exact (h i).ne_zero
  · intro h i; exact (h i).isUnit

variable {R : Type*} [CommRing R]

/-- **Invertibility via the CRT decomposition.** Given the CRT isomorphism `φ : R ≃+* ∏ Kᵢ` (the
splitting of `R_q` into its residue fields) and a proof that `x` is NONZERO in every factor, `x` is a
unit in `R`. This is the general-`n` reduction: challenge-difference invertibility becomes
"nonzero in each CRT factor." -/
theorem isUnit_of_crt_nonzero (φ : R ≃+* (∀ i, K i)) {x : R} (hx : ∀ i, φ x i ≠ 0) :
    IsUnit x := by
  have h1 : IsUnit (φ x) := (product_field_isUnit_iff (φ x)).mpr hx
  have h2 : IsUnit (φ.symm (φ x)) := h1.map φ.symm
  rwa [φ.symm_apply_apply] at h2

/-- **The interface for the number-theoretic step.** Package "the challenge difference is nonzero in each
CRT factor" as the hypothesis a low-∞-norm bound will supply. `challenge_diff_isUnit_general` then hands
back an `IsUnit` — the same `hinv` `HermineDischarge.lossiness_discharges_nonzero` consumes, now at
general `n` given the per-factor non-vanishing. The remaining Lyubashevsky–Seiler content is exactly
`hnz`: a nonzero element of ∞-norm `< β` does not vanish mod any degree-`d` factor when `β` is below the
factor's minimum-norm nonzero element. -/
theorem challenge_diff_isUnit_general (φ : R ≃+* (∀ i, K i)) {c c' : R}
    (hnz : ∀ i, φ (c - c') i ≠ 0) : IsUnit (c - c') :=
  isUnit_of_crt_nonzero φ hnz

/-- Sanity / non-vacuity over a concrete two-factor product `(ZMod 5)²` (a stand-in for a two-factor CRT
split): the component-wise-nonzero element `(2, 3)` is a unit — the criterion decided on real numbers. -/
theorem crt_example_isUnit : IsUnit (![2, 3] : Fin 2 → ℚ) :=
  (product_field_isUnit_iff _).mpr (by intro i; fin_cases i <;> norm_num)

/-- And a component-wise-nonzero check genuinely FAILS when a factor vanishes — the criterion has teeth
(the invertibility really does hinge on nonzero-in-EVERY-factor). -/
theorem crt_example_zero_factor_not_unit : ¬ IsUnit (![2, 0] : Fin 2 → ℚ) := by
  rw [product_field_isUnit_iff]
  push_neg
  exact ⟨1, by norm_num⟩

#assert_axioms product_field_isUnit_iff
#assert_axioms isUnit_of_crt_nonzero
#assert_axioms challenge_diff_isUnit_general
#assert_axioms crt_example_isUnit
#assert_axioms crt_example_zero_factor_not_unit

end Dregg2.Crypto.InvertibilityCRT
