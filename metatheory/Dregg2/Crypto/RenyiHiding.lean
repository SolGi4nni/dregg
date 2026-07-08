/-
# `Dregg2.Crypto.RenyiHiding` — the Rényi-divergence key-hiding bound: the TIGHT noise-flooding tool.

`Smudging` + `HermineHiding` give key-hiding via total-variation distance with uniform noise — sound,
but TV forces the noise width to dwarf EVERYTHING (`σ ≫ Q·B` over `Q` queries, distances ADD). Raccoon's
actual analysis replaces TV with the **Rényi divergence**, which has two properties TV lacks and which
together make it the right tool for noise-flooding with Gaussian-style noise:

* **Multiplicativity** over independent coordinates: `R_a(∏ Pᵢ ‖ ∏ Qᵢ) = ∏ R_a(Pᵢ‖Qᵢ)`. An
  n-coordinate signature's divergence is the PRODUCT of per-coordinate divergences, each `1 + tiny`,
  so `n` coordinates (or `Q` queries) cost `(1 + tiny)^n ≈ 1 + n·tiny` — versus TV's additive `n·ε`
  paid against a linear budget. This is what buys `σ ≳ √Q·‖shift‖` instead of `σ ≫ Q·‖shift‖`.
* **Probability preservation**: an event with probability `ε` under `P` has probability
  `≥ ε^(a/(a-1)) / R_a(P‖Q)` under `Q`. A forgery against the REAL scheme (`P`) transfers to a forgery
  against the secret-free SIMULATOR (`Q`) with only polynomial loss — unforgeability transfers back.

This file formalizes the **order-2 (collision) case** — the most-used one — over exact rationals with
finite support, mirroring `Smudging`'s style (no measure theory). We work with the divergence's SUM
FORM `renyiDiv2 s P Q = ∑ x ∈ s, P x ^ 2 / Q x` (for order 2 the sum form IS the multiplicative-form
divergence: `R₂ = ∑ P²/Q`, no outer root). Landed, all non-vacuous:

* `renyiDiv2_self` — identity of indiscernibles direction: `renyiDiv2 s P P = ∑ P = 1` for a distribution;
* `one_le_renyiDiv2` — `R₂ ≥ 1` for any pair of distributions (via Cauchy–Schwarz in Engel form);
* `renyiDiv2_mul` — **multiplicativity** over a two-coordinate independent product (the structural lemma);
* `renyi_probability_preservation` — **the preservation bound** `P(E)² ≤ R₂(P‖Q) · Q(E)`, i.e.
  `Q(E) ≥ P(E)²/R₂` (order-2 Cauchy–Schwarz), plus its division form and the forgery-transfer corollary;
* concrete instances with `R₂ = 5/4 > 1` where the bound is checked numerically, and the product
  instance multiplying to `25/16`.

Further tightening (noted, not done here): general order `a` (the exponent `a/(a-1) → 1` as `a → ∞`)
and the discrete-Gaussian instantiation `R₂(N_{σ,c} ‖ N_{σ,0}) ≤ exp(‖c‖²/σ²)`, which plugged into
`renyiDiv2_mul` + preservation yields Raccoon's `σ ≳ √(queries)·‖c·s‖` parameter law.
-/
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Dregg2.Crypto.RenyiHiding

variable {α β : Type*}

/-- General order-`a` Rényi divergence, sum form, over exact rationals with finite support:
`∑ x ∈ s, P x ^ a / Q x ^ (a - 1)`. (The multiplicative-form divergence is this sum raised to
`1/(a-1)`; over ℚ we work with the sum form, which for `a = 2` coincides with the divergence itself.) -/
def renyiSum (a : ℕ) (s : Finset α) (P Q : α → ℚ) : ℚ :=
  ∑ x ∈ s, P x ^ a / Q x ^ (a - 1)

/-- **Order-2 (collision) Rényi divergence** `R₂(P‖Q) = ∑ x ∈ s, P x ² / Q x` — the workhorse case:
here the sum form needs no outer root, so multiplicativity and preservation are exact ℚ statements. -/
def renyiDiv2 (s : Finset α) (P Q : α → ℚ) : ℚ :=
  ∑ x ∈ s, P x ^ 2 / Q x

/-- The order-2 divergence is the `a = 2` instance of the general sum form. -/
theorem renyiSum_two (s : Finset α) (P Q : α → ℚ) :
    renyiSum 2 s P Q = renyiDiv2 s P Q := by
  unfold renyiSum renyiDiv2
  simp [pow_one]

/-- **No divergence from yourself** (identity-of-indiscernibles direction): `R₂(P‖P) = ∑ P` — which is
`1` when `P` is a distribution, the minimum possible (see `one_le_renyiDiv2`). Holds unconditionally
over ℚ: on any zero of `P` the term is `0 = P x` under the `0/0 = 0` convention. -/
theorem renyiDiv2_self (s : Finset α) (P : α → ℚ) :
    renyiDiv2 s P P = ∑ x ∈ s, P x := by
  unfold renyiDiv2
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : P x = 0
  · simp [h]
  · rw [sq, mul_div_assoc, div_self h, mul_one]

/-- `R₂(P‖P) = 1` for a distribution: divergence bottoms out at `1` exactly when the distributions
coincide. -/
theorem renyiDiv2_self_eq_one (s : Finset α) (P : α → ℚ) (hP : ∑ x ∈ s, P x = 1) :
    renyiDiv2 s P P = 1 := by
  rw [renyiDiv2_self, hP]

/-- **`R₂ ≥ 1` for distributions** — the divergence of any pair of probability distributions is at
least the no-divergence value `1` (Cauchy–Schwarz in Engel form: `(∑ P)²/(∑ Q) ≤ ∑ P²/Q`). Together
with `renyiDiv2_self_eq_one` this is the sanity floor: `R₂ ≥ 1`, with equality at `P = Q`. -/
theorem one_le_renyiDiv2 (s : Finset α) (P Q : α → ℚ)
    (hP : ∑ x ∈ s, P x = 1) (hQ : ∑ x ∈ s, Q x = 1) (hQpos : ∀ x ∈ s, 0 < Q x) :
    1 ≤ renyiDiv2 s P Q := by
  have h := Finset.sq_sum_div_le_sum_sq_div s P hQpos
  rw [hP, hQ] at h
  simpa [renyiDiv2] using h

/-- **MULTIPLICATIVITY** — the load-bearing structural lemma. For independent coordinates the order-2
divergence of the product distribution is the PRODUCT of the per-coordinate divergences:
`R₂(P₁×P₂ ‖ Q₁×Q₂) = R₂(P₁‖Q₁) · R₂(P₂‖Q₂)`.

This is why Rényi beats TV for noise-flooding: an n-coordinate signature (or an n-query transcript)
has divergence `∏ (1 + tinyᵢ) ≈ 1 + ∑ tinyᵢ`, so per-coordinate closeness need only be
`O(1/n)`-small in the EXPONENT — versus TV distances adding against a fixed budget. Iterating this
two-coordinate form gives any finite product. Holds for arbitrary mass functions (the `0/0 = 0`
convention makes the pointwise factorization `(xy)²/(uv) = (x²/u)(y²/v)` unconditional in ℚ). -/
theorem renyiDiv2_mul (s : Finset α) (t : Finset β) (P₁ Q₁ : α → ℚ) (P₂ Q₂ : β → ℚ) :
    renyiDiv2 (s ×ˢ t) (fun p => P₁ p.1 * P₂ p.2) (fun p => Q₁ p.1 * Q₂ p.2)
      = renyiDiv2 s P₁ Q₁ * renyiDiv2 t P₂ Q₂ := by
  unfold renyiDiv2
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_pow, div_mul_div_comm]

/-- **PROBABILITY PRESERVATION (order 2)** — THE theorem: why unforgeability under the simulator
transfers to the real scheme. For any event `E ⊆ s`,

`P(E)² ≤ R₂(P‖Q) · Q(E)`   i.e.   `Q(E) ≥ P(E)² / R₂(P‖Q)`.

Crypto reading (`P` = the REAL signature distribution, `Q` = the secret-free SIMULATOR): an adversary
forging against the real scheme with probability `ε = P(E)` forges against the simulator with
probability `≥ ε²/R₂`. The simulator knows no secret, so its forgery probability is bounded by the
MSIS hardness; hence `ε ≤ √(R₂ · negligible)` — the real scheme is unforgeable whenever `R₂` is
polynomially bounded, which noise-flooding guarantees. Proof is exactly order-2 Cauchy–Schwarz:
`(∑_{x∈E} P x)² ≤ (∑_{x∈E} P x²/Q x)(∑_{x∈E} Q x) ≤ R₂ · Q(E)`. -/
theorem renyi_probability_preservation (s E : Finset α) (P Q : α → ℚ)
    (hE : E ⊆ s) (hQpos : ∀ x ∈ s, 0 < Q x) :
    (∑ x ∈ E, P x) ^ 2 ≤ renyiDiv2 s P Q * ∑ x ∈ E, Q x := by
  have hQE : ∀ x ∈ E, 0 < Q x := fun x hx => hQpos x (hE hx)
  -- Cauchy–Schwarz on E: (∑ P)² ≤ (∑ P²/Q)(∑ Q), via r = P, f = P²/Q, g = Q with r² = f·g.
  have hCS : (∑ x ∈ E, P x) ^ 2 ≤ (∑ x ∈ E, P x ^ 2 / Q x) * ∑ x ∈ E, Q x :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul E
      (fun x hx => div_nonneg (sq_nonneg _) (hQE x hx).le)
      (fun x hx => (hQE x hx).le)
      (fun x hx => (div_mul_cancel₀ (P x ^ 2) (hQE x hx).ne').ge)
  -- Monotonicity in the support: ∑_E P²/Q ≤ ∑_s P²/Q = R₂ (every term nonneg on s).
  have hmono : (∑ x ∈ E, P x ^ 2 / Q x) ≤ renyiDiv2 s P Q :=
    Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun x hx _ => div_nonneg (sq_nonneg _) (hQpos x hx).le)
  calc (∑ x ∈ E, P x) ^ 2
      ≤ (∑ x ∈ E, P x ^ 2 / Q x) * ∑ x ∈ E, Q x := hCS
    _ ≤ renyiDiv2 s P Q * ∑ x ∈ E, Q x :=
        mul_le_mul_of_nonneg_right hmono (Finset.sum_nonneg fun x hx => (hQE x hx).le)

/-- Preservation, division form: `Q(E) ≥ P(E)² / R₂(P‖Q)` — the shape quoted in the Raccoon
analysis (order-2 instance of `Q(E) ≥ P(E)^{a/(a-1)} / R_a(P‖Q)`). -/
theorem renyi_probability_preservation_div (s E : Finset α) (P Q : α → ℚ)
    (hE : E ⊆ s) (hQpos : ∀ x ∈ s, 0 < Q x) (hR : 0 < renyiDiv2 s P Q) :
    (∑ x ∈ E, P x) ^ 2 / renyiDiv2 s P Q ≤ ∑ x ∈ E, Q x := by
  rw [div_le_iff₀ hR, mul_comm]
  exact renyi_probability_preservation s E P Q hE hQpos

/-- **Forgery transfer** — the security corollary in the form the reduction uses: if forging against
the secret-free simulator succeeds with probability at most `δ` (bounded by MSIS hardness), and the
divergence between real and simulated transcripts is at most `R` (bounded by noise-flooding), then
forging against the REAL scheme succeeds with probability `ε` satisfying `ε² ≤ R·δ`. Polynomial `R`
plus negligible `δ` forces `ε` negligible: signing with flooded noise does not help the forger. -/
theorem renyi_forgery_transfer (s E : Finset α) (P Q : α → ℚ) (R δ : ℚ)
    (hE : E ⊆ s) (hQpos : ∀ x ∈ s, 0 < Q x)
    (hR : renyiDiv2 s P Q ≤ R) (hδ : ∑ x ∈ E, Q x ≤ δ) :
    (∑ x ∈ E, P x) ^ 2 ≤ R * δ := by
  have hQE : (0:ℚ) ≤ ∑ x ∈ E, Q x :=
    Finset.sum_nonneg fun x hx => (hQpos x (hE hx)).le
  have hR0 : (0:ℚ) ≤ R := le_trans
    (Finset.sum_nonneg fun x hx => div_nonneg (sq_nonneg _) (hQpos x hx).le) hR
  calc (∑ x ∈ E, P x) ^ 2
      ≤ renyiDiv2 s P Q * ∑ x ∈ E, Q x := renyi_probability_preservation s E P Q hE hQpos
    _ ≤ R * ∑ x ∈ E, Q x := mul_le_mul_of_nonneg_right hR hQE
    _ ≤ R * δ := mul_le_mul_of_nonneg_left hδ hR0

/-! ## Concrete non-vacuous instances

`P = (3/4, 1/4)` versus `Q = (1/2, 1/2)` on `{0, 1} ⊂ ℤ`: two genuine distributions, genuinely
different, with `R₂(P‖Q) = (9/16)/(1/2) + (1/16)/(1/2) = 5/4` — a real number strictly `> 1`. -/

/-- The real (shifted) distribution `(3/4, 1/4)` on `{0,1}`. -/
def exP : ℤ → ℚ := fun x => if x = 0 then 3/4 else 1/4

/-- The simulated (centered) distribution `(1/2, 1/2)` on `{0,1}`. -/
def exQ : ℤ → ℚ := fun _ => 1/2

/-- `R₂(exP‖exQ) = 5/4` exactly — strictly above the `R₂ = 1` floor, so the divergence is doing real
work (this pair is NOT the degenerate `P = Q` case). -/
theorem renyi_example_div : renyiDiv2 ({0, 1} : Finset ℤ) exP exQ = 5/4 := by
  unfold renyiDiv2 exP exQ
  norm_num

/-- The preservation bound holds concretely and non-trivially: for the event `E = {0}`,
`P(E)² = 9/16 ≤ (5/4)·(1/2) = R₂ · Q(E) = 10/16` — a tight-ish live check (slack `1/16`). -/
theorem renyi_example_preservation :
    (∑ x ∈ ({0} : Finset ℤ), exP x) ^ 2
      ≤ renyiDiv2 ({0, 1} : Finset ℤ) exP exQ * ∑ x ∈ ({0} : Finset ℤ), exQ x := by
  refine renyi_probability_preservation _ _ _ _ ?_ ?_
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  · intro x _
    norm_num [exQ]

/-- The same, checked NUMERICALLY (`9/16 ≤ 5/8`), independent of the general theorem — the instance
is not an artifact of vacuous hypotheses. -/
theorem renyi_example_preservation_numeric :
    (∑ x ∈ ({0} : Finset ℤ), exP x) ^ 2
      ≤ renyiDiv2 ({0, 1} : Finset ℤ) exP exQ * ∑ x ∈ ({0} : Finset ℤ), exQ x := by
  unfold renyiDiv2 exP exQ
  norm_num

/-- Multiplicativity, live: the two-coordinate product transcript has divergence
`(5/4)² = 25/16` — per-coordinate divergences MULTIPLY, the mechanism that lets n-coordinate
signatures pay only `(1 + tiny)ⁿ`. -/
theorem renyi_example_product :
    renyiDiv2 (({0, 1} : Finset ℤ) ×ˢ ({0, 1} : Finset ℤ))
      (fun p => exP p.1 * exP p.2) (fun p => exQ p.1 * exQ p.2) = 25/16 := by
  rw [renyiDiv2_mul, renyi_example_div]
  norm_num

#assert_axioms renyiSum_two
#assert_axioms renyiDiv2_self
#assert_axioms renyiDiv2_self_eq_one
#assert_axioms one_le_renyiDiv2
#assert_axioms renyiDiv2_mul
#assert_axioms renyi_probability_preservation
#assert_axioms renyi_probability_preservation_div
#assert_axioms renyi_forgery_transfer
#assert_axioms renyi_example_div
#assert_axioms renyi_example_preservation
#assert_axioms renyi_example_preservation_numeric
#assert_axioms renyi_example_product

end Dregg2.Crypto.RenyiHiding
