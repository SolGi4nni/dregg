/-
# `Dregg2.Crypto.InvertibilityD2` — the concrete DEGREE-2 factor case: n = 4, q = 13, two
irreducible quadratics.

`InvertibilityNormGen` made the Lyubashevsky–Seiler bound (IACR 2018/786) PARAMETRIC — but only at
`d = 1` (linear factors: the split `n = 2` family and the fully-split `q ≡ 1 mod 8` quartic family).
The only `d = 2` evidence so far was the parent file's single point `q = 5`. This file extends the
`d = 2` lane to a second, sharper point: **`q = 13 ≡ 5 (mod 8)`**, where

  `X⁴ + 1 = (X² − 5)(X² + 5)  (mod 13)`

(since `(X²−5)(X²+5) = X⁴ − 25 ≡ X⁴ + 1`, as `5² = 25 ≡ −1`), and BOTH quadratic factors are
IRREDUCIBLE (`5` and `−5 = 8` are non-squares mod 13 — the squares are `{0,1,3,4,9,10,12}`), so each
residue ring is the field `𝔽_{13²}`.

**What is PROVED here (no `sorry`, every theorem `#assert_axioms`-clean, kernel `decide` only):**

1. **THE MIN-NORM OF BOTH QUADRATIC IDEALS IS EXACTLY B = 3** (`minNorm_quad_factor`,
   `minNorm_quad_factor'`): every NONZERO multiple `(h₀ + h₁X)(X² ∓ 5)` — the ideal is exactly the
   169 such multiples, and the kernel-elements-are-multiples step is proved ALGEBRAICALLY
   (`toQuad 5 f = 0 ⇒ c0 = −5c2, c1 = −5c3`), with the 169-case minimum then decided — has centered
   coefficient ∞-norm ≥ 3. The Lyubashevsky–Seiler threshold shape at `d = 2, n = 4` is
   `q^(d/n) = 13^(1/2) = √13 ≈ 3.61`; the TRUE min over the 169 multiples is 3 (their constant-loss
   `1/s` is real), and 3 is ACHIEVED (`minNorm_exactly_three`) — the bound proved is the best one.

2. **THE d = 2 UNIT THEOREM** (`low_norm_isUnit_d2_q13`): every nonzero `f ∈ ℤ₁₃[X]/(X⁴+1)` with
   `‖f‖∞ < 3` is a UNIT — below both ideals' min-norm ⇒ nonzero in both quadratic CRT factors
   (the constructed `crtEquiv` of the parent file, instantiated at `r = 5`) ⇒ unit in each `𝔽_{169}`
   (explicit anisotropic-norm inverses) ⇒ unit.

3. **The challenge-difference form** (`challenge_diff_isUnit_d2_q13`): distinct challenges with
   `‖c − c'‖∞ < 3` have invertible difference.

4. **Anti-vacuity, both directions**: the challenge difference `δ = 1 − X²` (norm 1 ≤ 2) is a unit
   with EXHIBITED inverse `7 + 7X²` (`δ·δ⁻¹ = 1` decided on the negacyclic arithmetic), AND the
   bound has TEETH at exactly B = 3: `3 + 2X² = 2·(X² − 5)` is a nonzero norm-3 element of the first
   ideal and is NOT a unit (`sharpD2_not_unit`) — `< 3` cannot be weakened to `≤ 3`.

**Honest scope**: this is the achievable CONCRETE `d = 2` evidence (one more point beyond the
parent's `q = 5`, at a `q` where the threshold is sharp on both sides). The GENERAL parametric
`d ≥ 2` min-norm — LS Lemma 2.2 via the complex resultant `Res(f, Xⁿ+1) = ∏ f(ζ)` over `2n`-th
roots of unity with `|f(ζ)| ≤ n‖f‖` — needs analytic/geometry-of-numbers infrastructure that
Mathlib does not have; the ideal's norm form at `d = 2, q ≡ 5 (mod 8)` is QUATERNARY, so the
sum-of-two-squares shortcut that powered the parametric `d = 1` bounds does not apply. That gap is
stated, not faked.
-/
import Dregg2.Crypto.InvertibilityNorm
import Mathlib.Tactic.NormNum.Prime

namespace Dregg2.Crypto.InvertibilityD2

open Dregg2.Crypto.InvertibilityNorm
open Quart (caval normInf)

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-! ## 1. The splitting data: `X⁴ + 1 = (X² − 5)(X² + 5)` mod 13, both factors irreducible -/

/-- `5² = 25 = −1` in `ℤ₁₃`: `5` is the square root of `−1` that produces the quadratic
splitting `X⁴ + 1 = (X² − 5)(X² + 5)`. -/
theorem five_sq : (5 : ZMod 13) * 5 = -1 := by decide

/-- `8 = −5` in `ℤ₁₃`: the second factor's parameter. -/
theorem eight_eq_neg_five : (8 : ZMod 13) = -(5 : ZMod 13) := by decide

/-- `2 · 7 = 14 = 1` in `ℤ₁₃`: `half = 7` for the CRT interpolation. -/
theorem two_mul_seven : (2 : ZMod 13) * 7 = 1 := by decide

/-- `5` is a NON-square mod 13 (the squares are `{0,1,3,4,9,10,12}`) — so `X² − 5` is
IRREDUCIBLE and its residue ring is the field `𝔽_{169}`. This is what makes q = 13 a genuine
`d = 2` case. -/
theorem nonsquare_five : ∀ x : ZMod 13, x * x ≠ 5 := by decide

/-- `8 = −5` is a NON-square mod 13 — so `X² + 5` is irreducible too. -/
theorem nonsquare_eight : ∀ x : ZMod 13, x * x ≠ 8 := by decide

/-- The splitting is REAL in the quotient: the images of `X² − 5` and `X² + 5` multiply to
`X⁴ − 25 = −1 − 25 = −26 = 0` in `ℤ₁₃[X]/(X⁴+1)` — a genuine zero-divisor pair, so the ring is
NOT a field and per-factor reasoning is genuinely needed. -/
theorem factors_multiply_to_zero :
    ((⟨8, 0, 1, 0⟩ : Quart 13) * ⟨5, 0, 1, 0⟩) = 0 := by decide

/-- The concrete CRT isomorphism `ℤ₁₃[X]/(X⁴+1) ≃+* 𝔽₁₆₉ × 𝔽₁₆₉` — the parent file's
CONSTRUCTED `crtEquiv` (algebraic, not decided) instantiated at `r = 5, r' = 8, half = 7`. -/
def crt13 : Quart 13 ≃+* Quad 13 5 × Quad 13 8 :=
  crtEquiv five_sq eight_eq_neg_five two_mul_seven

/-! ## 2. THE MIN-NORM OF THE QUADRATIC IDEALS: B = 3

The ideal `(X² − 5)` is exactly the 169 multiples `(h₀ + h₁X)(X² − 5) = −5h₀ − 5h₁X + h₀X² + h₁X³`.
That kernel characterization is proved ALGEBRAICALLY (no enumeration of the 28 561-element ring);
the minimum over the 169 multiples is then a kernel `decide`. -/

set_option maxRecDepth 20000 in
/-- The 169 multiples of `X² − 5`, enumerated: every nonzero one has ∞-norm ≥ 3. -/
theorem minNorm_pairs₁ : ∀ a b : ZMod 13, ¬(a = 0 ∧ b = 0) →
    3 ≤ normInf (⟨-5 * a, -5 * b, a, b⟩ : Quart 13) := by decide

set_option maxRecDepth 20000 in
/-- The 169 multiples of `X² + 5`, enumerated: every nonzero one has ∞-norm ≥ 3. -/
theorem minNorm_pairs₂ : ∀ a b : ZMod 13, ¬(a = 0 ∧ b = 0) →
    3 ≤ normInf (⟨-8 * a, -8 * b, a, b⟩ : Quart 13) := by decide

/-- **THE MIN-NORM OF THE IDEAL `(X² − 5)` IN `ℤ₁₃[X]/(X⁴+1)`: every nonzero element has centered
∞-norm ≥ 3.** The kernel of the factor map `toQuad 5` is characterized algebraically as the set of
multiples `(c2 + c3·X)(X² − 5)` (i.e. `c0 = −5c2`, `c1 = −5c3`), and the 169-case minimum is
decided. Note `3 ≤ √13 = q^(d/n) ≈ 3.61`: the Lyubashevsky–Seiler `d = 2` threshold shape, with
the true minimum one notch below the ceiling (`minNorm_exactly_three` shows 3 is achieved). -/
theorem minNorm_quad_factor : ∀ f : Quart 13, toQuad 5 f = 0 → f ≠ 0 → 3 ≤ normInf f := by
  intro f hker hf
  obtain ⟨a0, a1, a2, a3⟩ := f
  have hre : a0 + 5 * a2 = 0 := congrArg Quad.re hker
  have him : a1 + 5 * a3 = 0 := congrArg Quad.im hker
  have hc0 : a0 = -5 * a2 := by linear_combination hre
  have hc1 : a1 = -5 * a3 := by linear_combination him
  subst hc0; subst hc1
  refine minNorm_pairs₁ a2 a3 ?_
  rintro ⟨rfl, rfl⟩
  exact hf (by ext <;> simp)

/-- The same min-norm ≥ 3 for the conjugate ideal `(X² + 5)` (factor map `toQuad 8`). -/
theorem minNorm_quad_factor' : ∀ f : Quart 13, toQuad 8 f = 0 → f ≠ 0 → 3 ≤ normInf f := by
  intro f hker hf
  obtain ⟨a0, a1, a2, a3⟩ := f
  have hre : a0 + 8 * a2 = 0 := congrArg Quad.re hker
  have him : a1 + 8 * a3 = 0 := congrArg Quad.im hker
  have hc0 : a0 = -8 * a2 := by linear_combination hre
  have hc1 : a1 = -8 * a3 := by linear_combination him
  subst hc0; subst hc1
  refine minNorm_pairs₂ a2 a3 ?_
  rintro ⟨rfl, rfl⟩
  exact hf (by ext <;> simp)

/-! ## 3. THE d = 2 UNIT THEOREM at q = 13, and the challenge-difference form -/

/-- **THE d = 2 LYUBASHEVSKY–SEILER UNIT THEOREM, CONCRETE AT q = 13**: every nonzero
`f ∈ ℤ₁₃[X]/(X⁴+1)` with centered ∞-norm `< 3` is a UNIT. Norm below both quadratic ideals'
min-norm ⇒ nonzero in both CRT factors ⇒ unit in each residue FIELD `𝔽₁₆₉` (`5, 8` non-squares,
explicit anisotropic-norm inverses) ⇒ unit, pulled back through the constructed CRT iso. -/
theorem low_norm_isUnit_d2_q13 {f : Quart 13} (hf : f ≠ 0) (hν : normInf f < 3) : IsUnit f := by
  have h₁ : toQuad 5 f ≠ 0 :=
    factor_nonzero_of_norm_lt (toQuad 5) normInf 3 (fun x => minNorm_quad_factor x) hf hν
  have h₂ : toQuad 8 f ≠ 0 :=
    factor_nonzero_of_norm_lt (toQuad 8) normInf 3 (fun x => minNorm_quad_factor' x) hf hν
  refine isUnit_of_map_isUnit crt13 ?_
  rw [show crt13 f = (toQuad 5 f, toQuad 8 f) from rfl]
  exact Prod.isUnit_iff.mpr
    ⟨Quad.isUnit_of_ne_zero nonsquare_five h₁, Quad.isUnit_of_ne_zero nonsquare_eight h₂⟩

/-- **The challenge-difference form, d = 2, q = 13**: distinct challenges whose difference has
∞-norm `< 3` have INVERTIBLE difference. -/
theorem challenge_diff_isUnit_d2_q13 {c c' : Quart 13} (hcc : c ≠ c')
    (hν : normInf (c - c') < 3) : IsUnit (c - c') :=
  low_norm_isUnit_d2_q13 (sub_ne_zero.mpr hcc) hν

/-! ## 4. Anti-vacuity, both directions -/

/-- First fork challenge: `c = 1 + X` (binary coefficients, like a real challenge set). -/
def cD2 : Quart 13 := ⟨1, 1, 0, 0⟩

/-- Second fork challenge: `c' = X + X²`. -/
def cD2' : Quart 13 := ⟨0, 1, 1, 0⟩

/-- The challenge difference `δ = c − c' = 1 − X²`, through the ring's own subtraction. -/
def δD2 : Quart 13 := ⟨1, 0, 12, 0⟩

/-- The EXHIBITED inverse: `(1 − X²)(7 + 7X²) = 7 − 7X⁴ = 7 + 7 = 14 = 1`. -/
def δD2Inv : Quart 13 := ⟨7, 0, 7, 0⟩

theorem cD2_distinct : cD2 ≠ cD2' := by decide

theorem cD2_diff_eq : cD2 - cD2' = δD2 := by decide

theorem δD2_ne_zero : δD2 ≠ 0 := by decide

/-- `δ` has ∞-norm exactly 1 — comfortably inside the `< 3` threshold (norm ≤ 2 suffices). -/
theorem δD2_norm : normInf δD2 = 1 := by decide

/-- Anti-vacuity leg 1a: the exhibited inverse VERIFIES on the negacyclic arithmetic. -/
theorem δD2_mul_inv : δD2 * δD2Inv = 1 := by decide

theorem δD2_inv_mul : δD2Inv * δD2 = 1 := by decide

/-- `IsUnit δ` from the exhibited, verified inverse. -/
theorem δD2_isUnit : IsUnit δD2 := ⟨⟨δD2, δD2Inv, δD2_mul_inv, δD2_inv_mul⟩, rfl⟩

/-- The concrete challenge-difference invertibility, exhibited-inverse route. -/
theorem concrete_diff_isUnit_d2 : IsUnit (cD2 - cD2') := cD2_diff_eq ▸ δD2_isUnit

/-- Cross-check: the SAME fact from the d = 2 norm theorem alone — distinctness plus the decided
norm bound, no inverse supplied. The two routes agree on a real element. -/
theorem concrete_diff_isUnit_d2' : IsUnit (cD2 - cD2') :=
  challenge_diff_isUnit_d2_q13 cD2_distinct (by decide)

/-- The sharpness element `3 + 2X² = 2·(X² − 5)`: a nonzero multiple of the first factor with
∞-norm EXACTLY 3 = B. -/
def sharpD2 : Quart 13 := ⟨3, 0, 2, 0⟩

theorem sharpD2_ne_zero : sharpD2 ≠ 0 := by decide

theorem sharpD2_norm : normInf sharpD2 = 3 := by decide

/-- `sharpD2` vanishes in the first CRT factor (`3 + 5·2 = 13 = 0`): it IS in the ideal. -/
theorem sharpD2_ker : toQuad 5 sharpD2 = 0 := by decide

/-- The min-norm 3 is ACHIEVED: the ideal `(X² − 5)` contains a nonzero element of norm exactly 3,
so `minNorm_quad_factor`'s bound is the exact minimum over the 169 multiples — `B = 3`, one notch
below the LS ceiling `√13 ≈ 3.61`. -/
theorem minNorm_exactly_three :
    ∃ f : Quart 13, toQuad 5 f = 0 ∧ f ≠ 0 ∧ normInf f = 3 :=
  ⟨sharpD2, sharpD2_ker, sharpD2_ne_zero, sharpD2_norm⟩

/-- **Anti-vacuity leg 2 — the bound has TEETH and is SHARP at B = 3**: `3 + 2X²` is a nonzero
element of ∞-norm exactly 3 and is NOT a unit (a unit would stay a unit in the residue field
`𝔽₁₆₉`, but it maps to 0 there). So `normInf f < 3` in `low_norm_isUnit_d2_q13` cannot be
weakened to `≤ 3`: the threshold is exactly the ideal's min-norm. -/
theorem sharpD2_not_unit : ¬ IsUnit sharpD2 := by
  intro h
  have hu := h.map (toQuadHom five_sq)
  rw [toQuadHom_apply, sharpD2_ker] at hu
  exact absurd (isUnit_zero_iff.mp hu) (by decide)

/-- The sharpness statement, packaged: the norm-3 frontier contains a nonzero NON-unit. -/
theorem norm_bound_sharp_d2 :
    ∃ f : Quart 13, f ≠ 0 ∧ normInf f = 3 ∧ ¬ IsUnit f :=
  ⟨sharpD2, sharpD2_ne_zero, sharpD2_norm, sharpD2_not_unit⟩

/-! ## Axiom hygiene — every theorem kernel-clean (`decide` only; no `native_decide`) -/

#assert_axioms five_sq
#assert_axioms eight_eq_neg_five
#assert_axioms two_mul_seven
#assert_axioms nonsquare_five
#assert_axioms nonsquare_eight
#assert_axioms factors_multiply_to_zero
#assert_axioms crt13
#assert_axioms minNorm_pairs₁
#assert_axioms minNorm_pairs₂
#assert_axioms minNorm_quad_factor
#assert_axioms minNorm_quad_factor'
#assert_axioms low_norm_isUnit_d2_q13
#assert_axioms challenge_diff_isUnit_d2_q13
#assert_axioms cD2_distinct
#assert_axioms cD2_diff_eq
#assert_axioms δD2_ne_zero
#assert_axioms δD2_norm
#assert_axioms δD2_mul_inv
#assert_axioms δD2_inv_mul
#assert_axioms δD2_isUnit
#assert_axioms concrete_diff_isUnit_d2
#assert_axioms concrete_diff_isUnit_d2'
#assert_axioms sharpD2_ne_zero
#assert_axioms sharpD2_norm
#assert_axioms sharpD2_ker
#assert_axioms minNorm_exactly_three
#assert_axioms sharpD2_not_unit
#assert_axioms norm_bound_sharp_d2

end Dregg2.Crypto.InvertibilityD2
