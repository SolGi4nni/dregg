/-
# `Dregg2.Crypto.GaussianRenyi` — the discrete-Gaussian order-2 Rényi bound: the Gaussian tightening.

`RenyiHiding` supplies the abstract order-2 machinery — `renyiDiv2 s P Q = ∑ P²/Q`, multiplicativity
over independent coordinates, and the preservation bound `P(E)² ≤ R₂ · Q(E)` — but leaves the concrete
`R₂` for the ACTUAL noise Hermine floods with as the named gap. This file closes it, over `ℝ` with
`Real.exp` and genuine infinite sums (`tsum` over `ℤ`), no finite-support surrogate.

**What lands here (all proved, no `sorry`, `#assert_axioms`-clean):**

* `gaussian_ratio_exponent` — the algebraic HEART: the pointwise ratio identity
  `ρ_σ(x)² / ρ_σ(x−δ) = ρ_σ(x) · exp(−(2xδ − δ²)/(2σ²))` for the unnormalized weight
  `ρ_σ(x) = exp(−x²/(2σ²))`, by real `exp` algebra. Holds for ALL real `σ, δ, x`.
* `gaussian_ratio_shift` — the completed square: `ρ_σ(x)²/ρ_σ(x−δ) = exp(δ²/σ²) · ρ_σ(x+δ)`.
  This is the telescoping form: the Rényi numerator is a δ-SHIFTED Gaussian weight, scaled by
  exactly the divergence constant.
* `summable_gaussianWeight` / `thetaSum` — the discrete-Gaussian normalization `S = ∑_{x∈ℤ} ρ_σ(x)`
  exists (geometric-tail comparison) and is positive; `tsum_gaussianWeight_add`/`_sub` — `S` is
  invariant under INTEGER shifts (reindexing `ℤ ≃ ℤ`), the exact fact that makes the discrete case
  as clean as the continuous one.
* `gaussian_renyiDiv2_eq` — **the divergence is EXACT, not just bounded**: for `σ ≠ 0` and any
  integer shift `δ`, the normalized discrete Gaussian `D_σ(x) = ρ_σ(x)/S` and its shift
  `D_{σ,δ}(x) = ρ_σ(x−δ)/S` (same `S`, by shift invariance) satisfy
  `∑'_{x∈ℤ} D_σ(x)²/D_{σ,δ}(x) = exp(δ²/σ²)` — full infinite-sum normalization included.
  `gaussian_renyi2_le` is the quoted `≤` form; `one_le_gaussian_renyi2` the sanity floor.
* `gaussian_probability_preservation` — the transfer, for the REAL noise: any finite event `E ⊆ ℤ`
  has `(∑_{E} D_σ)² ≤ exp(δ²/σ²) · ∑_{E} D_{σ,δ}` (Cauchy–Schwarz on `E`, then the finite partial
  sum of `P²/Q` is dominated by the full `tsum = exp(δ²/σ²)`). This is
  `RenyiHiding.renyi_probability_preservation` instantiated at the actual Gaussian `R₂`;
  `gaussian_forgery_transfer` is the reduction-shaped corollary `ε² ≤ exp(δ²/σ²)·δ_sim`.
* `gaussian_renyi2_pair` — two independent coordinates multiply: the pair transcript has divergence
  exactly `exp(2δ²/σ²)` — the concrete instance of `renyiDiv2_mul`'s mechanism; iterating gives
  `exp(n·δ²/σ²)` for `n` coordinates, hence Raccoon's parameter law `σ ≳ √n·δ` keeps `R₂ = O(1)`.
* Concrete instance `σ = 2, δ = 1`: `R₂ = exp(1/4)` exactly, with real-number teeth
  `1 < exp(1/4) < 4/3` (via `Real.add_one_le_exp` and `exp_one_lt_d9`), and the preservation bound
  instantiated. Non-vacuous: the divergence is strictly above the floor and strictly below the
  Raccoon budget.

**Honest remaining gap:** the shift `δ` must be an INTEGER (`δ : ℤ`) for the exactness — that is
the case the signature needs (`δ = c·s` has integer entries), and only integer shifts leave `ℤ`
invariant. For non-integer real shifts the shifted support is a coset `ℤ + δ` and the two theta
normalizations differ by a bounded theta-ratio factor; that refinement (and general order `a`) is
not formalized here. The n-fold product for arbitrary `n` is given at `n = 2` (`gaussian_renyi2_pair`);
the general `Fin n` product is a routine induction over `renyiDiv2_mul`-style reindexing not needed
by the per-coordinate law.
-/
import Dregg2.Tactics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Dregg2.Crypto.GaussianRenyi

/-! ## The unnormalized Gaussian weight and the pointwise ratio identity -/

/-- The (unnormalized) Gaussian weight `ρ_σ(x) = exp(−x²/(2σ²))` — the mask density Hermine's
noise-flooding actually uses, up to the theta normalization handled below. -/
noncomputable def gaussianWeight (σ x : ℝ) : ℝ := Real.exp (-(x ^ 2) / (2 * σ ^ 2))

/-- Gaussian weights never vanish — the `0/0` edge cases of the ℚ development simply do not arise. -/
theorem gaussianWeight_pos (σ x : ℝ) : 0 < gaussianWeight σ x := Real.exp_pos _

/-- `exp a ² / exp b = exp (a + a − b)` — the exponent bookkeeping used by both ratio identities. -/
private theorem exp_sq_div (a b : ℝ) :
    Real.exp a ^ 2 / Real.exp b = Real.exp (a + a - b) := by
  rw [sq, ← Real.exp_add, Real.exp_sub]

/-- **The algebraic heart** — the pointwise Rényi-numerator ratio:
`ρ_σ(x)² / ρ_σ(x−δ) = ρ_σ(x) · exp(−(2xδ − δ²)/(2σ²))`.

The order-2 numerator against the δ-shifted denominator is the weight itself times a factor whose
exponent is LINEAR in `x` — squaring costs one extra Gaussian factor and a linear tilt, nothing
worse. Real `Real.exp` algebra; holds for all real `σ, δ, x` (at `σ = 0` every exponent degrades
to `0` consistently under the `x/0 = 0` convention). -/
theorem gaussian_ratio_exponent (σ δ x : ℝ) :
    gaussianWeight σ x ^ 2 / gaussianWeight σ (x - δ)
      = gaussianWeight σ x * Real.exp (-(2 * x * δ - δ ^ 2) / (2 * σ ^ 2)) := by
  unfold gaussianWeight
  rw [exp_sq_div, ← Real.exp_add]
  congr 1
  ring

/-- **The completed square** — the same ratio, telescoped: the linear tilt absorbed into a
`+δ`-shifted weight, with the divergence constant `exp(δ²/σ²)` split off:
`ρ_σ(x)² / ρ_σ(x−δ) = exp(δ²/σ²) · ρ_σ(x+δ)`.

Summing this over `x ∈ ℤ` is what makes the discrete divergence EXACT: the right side sums to
`exp(δ²/σ²) · S` by integer-shift invariance of the theta sum. -/
theorem gaussian_ratio_shift (σ δ x : ℝ) :
    gaussianWeight σ x ^ 2 / gaussianWeight σ (x - δ)
      = Real.exp (δ ^ 2 / σ ^ 2) * gaussianWeight σ (x + δ) := by
  unfold gaussianWeight
  rw [exp_sq_div, ← Real.exp_add]
  congr 1
  ring

/-! ## The discrete Gaussian over ℤ: summability and the theta normalization -/

/-- The Gaussian weight is summable over `ℤ` (for `σ ≠ 0`): comparison against the geometric
series `exp(−n/(2σ²))`, since `n ≤ n²`. This is the existence of the theta normalization. -/
theorem summable_gaussianWeight {σ : ℝ} (hσ : σ ≠ 0) :
    Summable fun x : ℤ => gaussianWeight σ (x : ℝ) := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := lt_of_le_of_ne (sq_nonneg σ) (Ne.symm (pow_ne_zero 2 hσ))
  have hc : -(1 / (2 * σ ^ 2)) < 0 := by
    rw [neg_lt_zero]
    positivity
  have hkey : ∀ y : ℝ, gaussianWeight σ y = Real.exp (-(1 / (2 * σ ^ 2)) * y ^ 2) := by
    intro y
    unfold gaussianWeight
    congr 1
    ring
  have hnat : Summable fun n : ℕ => Real.exp (-(1 / (2 * σ ^ 2)) * (n : ℝ) ^ 2) :=
    Real.summable_exp_nat_mul_of_ge hc fun i => by exact_mod_cast Nat.le_self_pow two_ne_zero i
  refine Summable.of_nat_of_neg ?_ ?_
  · exact hnat.congr fun n => by rw [hkey]; norm_num
  · refine hnat.congr fun n => ?_
    rw [hkey]
    push_cast
    rw [neg_sq]

/-- The theta normalization `S(σ) = ∑_{x∈ℤ} ρ_σ(x)` of the discrete Gaussian. -/
noncomputable def thetaSum (σ : ℝ) : ℝ := ∑' x : ℤ, gaussianWeight σ (x : ℝ)

/-- The normalization is strictly positive — the discrete Gaussian is a genuine distribution. -/
theorem thetaSum_pos {σ : ℝ} (hσ : σ ≠ 0) : 0 < thetaSum σ :=
  (summable_gaussianWeight hσ).tsum_pos (fun _ => (gaussianWeight_pos σ _).le) 0
    (gaussianWeight_pos σ _)

/-- **Integer-shift invariance of the theta sum** (`+` form): `∑_{x∈ℤ} ρ_σ(x+δ) = S(σ)` for `δ : ℤ`.
Reindexing along the bijection `x ↦ x + δ` of `ℤ` — the exact discrete substitute for translation
invariance of Lebesgue measure, and the reason the divergence computation closes with no error
term. Unconditional in `σ` (both sides are `0` when not summable). -/
theorem tsum_gaussianWeight_add (σ : ℝ) (δ : ℤ) :
    ∑' x : ℤ, gaussianWeight σ ((x : ℝ) + (δ : ℝ)) = thetaSum σ :=
  calc ∑' x : ℤ, gaussianWeight σ ((x : ℝ) + (δ : ℝ))
      = ∑' x : ℤ, gaussianWeight σ (((Equiv.addRight δ) x : ℤ) : ℝ) :=
        tsum_congr fun x => by rw [Equiv.coe_addRight]; norm_cast
    _ = ∑' x : ℤ, gaussianWeight σ (x : ℝ) :=
        (Equiv.addRight δ).tsum_eq fun x : ℤ => gaussianWeight σ (x : ℝ)
    _ = thetaSum σ := rfl

/-- Integer-shift invariance, `−` form: `∑_{x∈ℤ} ρ_σ(x−δ) = S(σ)` — the SHIFTED discrete Gaussian
has the SAME normalization as the centered one. -/
theorem tsum_gaussianWeight_sub (σ : ℝ) (δ : ℤ) :
    ∑' x : ℤ, gaussianWeight σ ((x : ℝ) - (δ : ℝ)) = thetaSum σ :=
  calc ∑' x : ℤ, gaussianWeight σ ((x : ℝ) - (δ : ℝ))
      = ∑' x : ℤ, gaussianWeight σ (((Equiv.subRight δ) x : ℤ) : ℝ) :=
        tsum_congr fun x => by rw [Equiv.subRight_apply]; norm_cast
    _ = ∑' x : ℤ, gaussianWeight σ (x : ℝ) :=
        (Equiv.subRight δ).tsum_eq fun x : ℤ => gaussianWeight σ (x : ℝ)
    _ = thetaSum σ := rfl

/-! ## The normalized discrete Gaussian and its δ-shift -/

/-- The discrete Gaussian distribution on `ℤ`: `D_σ(x) = ρ_σ(x) / S(σ)` — the SIMULATOR's mask. -/
noncomputable def discreteGaussian (σ : ℝ) (x : ℤ) : ℝ := gaussianWeight σ (x : ℝ) / thetaSum σ

/-- The δ-shifted discrete Gaussian: `D_{σ,δ}(x) = ρ_σ(x−δ) / S(σ)` — the REAL signature's mask,
recentred at the secret-dependent shift `δ = c·s`. Same normalization `S(σ)` by
`tsum_gaussianWeight_sub`, so this is the genuine shifted distribution, not a proxy. -/
noncomputable def shiftedGaussian (σ : ℝ) (δ : ℤ) (x : ℤ) : ℝ :=
  gaussianWeight σ ((x : ℝ) - (δ : ℝ)) / thetaSum σ

theorem discreteGaussian_pos {σ : ℝ} (hσ : σ ≠ 0) (x : ℤ) : 0 < discreteGaussian σ x :=
  div_pos (gaussianWeight_pos _ _) (thetaSum_pos hσ)

theorem shiftedGaussian_pos {σ : ℝ} (hσ : σ ≠ 0) (δ x : ℤ) : 0 < shiftedGaussian σ δ x :=
  div_pos (gaussianWeight_pos _ _) (thetaSum_pos hσ)

/-- `D_σ` is a probability distribution: `∑'_{x∈ℤ} D_σ(x) = 1`. -/
theorem tsum_discreteGaussian {σ : ℝ} (hσ : σ ≠ 0) : ∑' x : ℤ, discreteGaussian σ x = 1 := by
  unfold discreteGaussian
  rw [tsum_div_const]
  exact div_self (thetaSum_pos hσ).ne'

/-- The shifted `D_{σ,δ}` is ALSO a probability distribution — non-vacuity of the pair: both sides
of the divergence are genuine distributions over the same countable support. -/
theorem tsum_shiftedGaussian {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) :
    ∑' x : ℤ, shiftedGaussian σ δ x = 1 := by
  unfold shiftedGaussian
  rw [tsum_div_const, tsum_gaussianWeight_sub]
  exact div_self (thetaSum_pos hσ).ne'

/-! ## The order-2 divergence: an exact identity -/

/-- Per-term normalized form of `gaussian_ratio_shift`: each Rényi term is the constant
`exp(δ²/σ²)/S` times a `+δ`-shifted weight. -/
theorem gaussian_renyi_term {σ : ℝ} (hσ : σ ≠ 0) (δ x : ℤ) :
    discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x
      = Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) / thetaSum σ * gaussianWeight σ ((x : ℝ) + (δ : ℝ)) := by
  have hS : thetaSum σ ≠ 0 := (thetaSum_pos hσ).ne'
  have hb : gaussianWeight σ ((x : ℝ) - (δ : ℝ)) ≠ 0 := (gaussianWeight_pos _ _).ne'
  have h1 : discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x
      = gaussianWeight σ (x : ℝ) ^ 2 / gaussianWeight σ ((x : ℝ) - (δ : ℝ)) / thetaSum σ := by
    unfold discreteGaussian shiftedGaussian
    rw [div_pow]
    field_simp
  rw [h1, gaussian_ratio_shift, mul_div_right_comm]

/-- **THE GAUSSIAN TIGHTENING — the divergence is exact.** For `σ ≠ 0` and any integer shift `δ`,
the order-2 Rényi divergence of the discrete Gaussian against its δ-shift, WITH the full
infinite-sum theta normalization, is

`R₂(D_σ ‖ D_{σ,δ}) = ∑'_{x∈ℤ} D_σ(x)² / D_{σ,δ}(x) = exp(δ²/σ²)` — equality, not just `≤`.

Proof: each term telescopes to `(exp(δ²/σ²)/S) · ρ_σ(x+δ)` (`gaussian_renyi_term`), the shifted
theta sum is again `S` (`tsum_gaussianWeight_add`), and `S` cancels. This is the concrete `R₂`
that `RenyiHiding.renyiDiv2_mul` multiplies across coordinates: `n` coordinates cost
`exp(n·δ²/σ²)`, so Raccoon's `σ ≳ √n·δ` keeps the total `O(1)`. -/
theorem gaussian_renyiDiv2_eq {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) :
    ∑' x : ℤ, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x
      = Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) :=
  calc ∑' x : ℤ, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x
      = ∑' x : ℤ, Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) / thetaSum σ
          * gaussianWeight σ ((x : ℝ) + (δ : ℝ)) :=
        tsum_congr fun x => gaussian_renyi_term hσ δ x
    _ = Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) / thetaSum σ
          * ∑' x : ℤ, gaussianWeight σ ((x : ℝ) + (δ : ℝ)) := tsum_mul_left
    _ = Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) / thetaSum σ * thetaSum σ := by
        rw [tsum_gaussianWeight_add]
    _ = Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) := div_mul_cancel₀ _ (thetaSum_pos hσ).ne'

/-- The bound as quoted in the Raccoon analysis: `R₂(D_σ ‖ D_{σ,δ}) ≤ exp(δ²/σ²)`. (Here with
slack zero — the discrete integer-shift case is exact.) -/
theorem gaussian_renyi2_le {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) :
    ∑' x : ℤ, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x
      ≤ Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) :=
  le_of_eq (gaussian_renyiDiv2_eq hσ δ)

/-- Sanity floor, matching `RenyiHiding.one_le_renyiDiv2`: the Gaussian `R₂` is `≥ 1`
(and `= 1` exactly at `δ = 0`, where the distributions coincide). -/
theorem one_le_gaussian_renyi2 {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) :
    1 ≤ ∑' x : ℤ, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x := by
  rw [gaussian_renyiDiv2_eq hσ δ]
  have h0 : (0 : ℝ) ≤ (δ : ℝ) ^ 2 / σ ^ 2 := by positivity
  linarith [Real.add_one_le_exp ((δ : ℝ) ^ 2 / σ ^ 2)]

/-- The Rényi term function is summable — needed to dominate finite partial sums by the full
divergence in the preservation bound. -/
theorem summable_gaussian_renyi_term {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) :
    Summable fun x : ℤ => discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x := by
  have h : Summable fun x : ℤ => gaussianWeight σ ((x : ℝ) + (δ : ℝ)) := by
    refine ((Equiv.addRight δ).summable_iff.mpr (summable_gaussianWeight hσ)).congr fun x => ?_
    simp only [Function.comp_apply, Equiv.coe_addRight]
    norm_cast
  exact (h.mul_left _).congr fun x => (gaussian_renyi_term hσ δ x).symm

/-! ## Probability preservation for the actual Gaussian noise -/

/-- **Preservation at the Gaussian** — `RenyiHiding.renyi_probability_preservation` instantiated
with the real noise: for ANY finite event `E ⊆ ℤ`,

`(∑_{x∈E} D_σ(x))² ≤ exp(δ²/σ²) · ∑_{x∈E} D_{σ,δ}(x)`.

Crypto reading: an adversary distinguishing/forging on event `E` against the centered simulator
transfers to the shifted real scheme with loss exactly the Gaussian `R₂` — with `σ ≳ √n·δ` that
loss is `O(1)`. Proof: order-2 Cauchy–Schwarz on `E` (same Engel-form step as the abstract ℚ
theorem), then the finite partial sum `∑_E P²/Q` is dominated by the full `tsum`, which
`gaussian_renyiDiv2_eq` evaluates exactly. -/
theorem gaussian_probability_preservation {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) (E : Finset ℤ) :
    (∑ x ∈ E, discreteGaussian σ x) ^ 2
      ≤ Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) * ∑ x ∈ E, shiftedGaussian σ δ x := by
  have hQpos : ∀ x : ℤ, 0 < shiftedGaussian σ δ x := shiftedGaussian_pos hσ δ
  have hCS : (∑ x ∈ E, discreteGaussian σ x) ^ 2
      ≤ (∑ x ∈ E, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x)
          * ∑ x ∈ E, shiftedGaussian σ δ x :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul E
      (fun x _ => div_nonneg (sq_nonneg _) (hQpos x).le)
      (fun x _ => (hQpos x).le)
      (fun x _ => (div_mul_cancel₀ _ (hQpos x).ne').ge)
  have hle : (∑ x ∈ E, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x)
      ≤ Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) := by
    rw [← gaussian_renyiDiv2_eq hσ δ]
    exact (summable_gaussian_renyi_term hσ δ).sum_le_tsum E
      fun x _ => div_nonneg (sq_nonneg _) (hQpos x).le
  calc (∑ x ∈ E, discreteGaussian σ x) ^ 2
      ≤ (∑ x ∈ E, discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x)
          * ∑ x ∈ E, shiftedGaussian σ δ x := hCS
    _ ≤ Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) * ∑ x ∈ E, shiftedGaussian σ δ x :=
        mul_le_mul_of_nonneg_right hle (Finset.sum_nonneg fun x _ => (hQpos x).le)

/-- **Forgery transfer at the Gaussian** — the reduction-shaped corollary, mirroring
`RenyiHiding.renyi_forgery_transfer`: if the event has probability at most `d` under the SHIFTED
(real, secret-bearing) distribution, the centered simulator sees it with probability `ε` where
`ε² ≤ exp(δ²/σ²)·d` — and symmetrically. Polynomially bounded `exp(δ²/σ²)` (noise-flooding) plus
negligible `d` (MSIS hardness) forces `ε` negligible. -/
theorem gaussian_forgery_transfer {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) (E : Finset ℤ) (d : ℝ)
    (hd : ∑ x ∈ E, shiftedGaussian σ δ x ≤ d) :
    (∑ x ∈ E, discreteGaussian σ x) ^ 2 ≤ Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) * d :=
  le_trans (gaussian_probability_preservation hσ δ E)
    (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)

/-! ## Two independent coordinates: the divergence constant multiplies

The concrete instance of `RenyiHiding.renyiDiv2_mul`'s mechanism at the Gaussian: a two-coordinate
transcript pays `exp(δ²/σ²)² = exp(2δ²/σ²)` — exponents ADD, so `n` coordinates pay `exp(n·δ²/σ²)`
and the Raccoon law `σ ≳ √n·δ` keeps the total constant. -/

/-- Two-coordinate multiplicativity at the Gaussian, exact: the product transcript's divergence is
`exp(2δ²/σ²)`. -/
theorem gaussian_renyi2_pair {σ : ℝ} (hσ : σ ≠ 0) (δ : ℤ) :
    ∑' p : ℤ × ℤ, (discreteGaussian σ p.1 * discreteGaussian σ p.2) ^ 2
        / (shiftedGaussian σ δ p.1 * shiftedGaussian σ δ p.2)
      = Real.exp (2 * (δ : ℝ) ^ 2 / σ ^ 2) := by
  have hpt : ∀ p : ℤ × ℤ,
      (discreteGaussian σ p.1 * discreteGaussian σ p.2) ^ 2
          / (shiftedGaussian σ δ p.1 * shiftedGaussian σ δ p.2)
        = (discreteGaussian σ p.1 ^ 2 / shiftedGaussian σ δ p.1)
            * (discreteGaussian σ p.2 ^ 2 / shiftedGaussian σ δ p.2) := by
    intro p
    rw [mul_pow, div_mul_div_comm]
  have hterm := summable_gaussian_renyi_term hσ δ
  have htermnn : ∀ x : ℤ, 0 ≤ discreteGaussian σ x ^ 2 / shiftedGaussian σ δ x :=
    fun x => div_nonneg (sq_nonneg _) (shiftedGaussian_pos hσ δ x).le
  have hprod : Summable fun p : ℤ × ℤ =>
      (discreteGaussian σ p.1 ^ 2 / shiftedGaussian σ δ p.1)
        * (discreteGaussian σ p.2 ^ 2 / shiftedGaussian σ δ p.2) :=
    hterm.mul_of_nonneg hterm htermnn htermnn
  calc ∑' p : ℤ × ℤ, (discreteGaussian σ p.1 * discreteGaussian σ p.2) ^ 2
        / (shiftedGaussian σ δ p.1 * shiftedGaussian σ δ p.2)
      = ∑' p : ℤ × ℤ, (discreteGaussian σ p.1 ^ 2 / shiftedGaussian σ δ p.1)
          * (discreteGaussian σ p.2 ^ 2 / shiftedGaussian σ δ p.2) := tsum_congr hpt
    _ = (∑' a : ℤ, discreteGaussian σ a ^ 2 / shiftedGaussian σ δ a)
          * ∑' b : ℤ, discreteGaussian σ b ^ 2 / shiftedGaussian σ δ b :=
        (hterm.tsum_mul_tsum hterm hprod).symm
    _ = Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) * Real.exp ((δ : ℝ) ^ 2 / σ ^ 2) := by
        rw [gaussian_renyiDiv2_eq hσ δ]
    _ = Real.exp (2 * (δ : ℝ) ^ 2 / σ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## Concrete non-vacuous instance: σ = 2, δ = 1

The per-coordinate divergence is exactly `exp(1/4)`, a real number strictly between `1` (the
`R₂` floor — the distributions genuinely differ) and `4/3` (comfortably inside a Raccoon-style
`O(1)` budget). The preservation bound is instantiated for every finite event. -/

/-- Concrete divergence: at `σ = 2, δ = 1`, `R₂ = exp(1/4)` exactly. -/
theorem gaussian_renyi2_concrete :
    ∑' x : ℤ, discreteGaussian 2 x ^ 2 / shiftedGaussian 2 1 x = Real.exp (1 / 4) := by
  rw [show (1 / 4 : ℝ) = ((1 : ℤ) : ℝ) ^ 2 / 2 ^ 2 by norm_num]
  exact gaussian_renyiDiv2_eq (by norm_num) 1

/-- The concrete divergence is strictly above the floor: `1 < exp(1/4)` — the shifted pair is NOT
the degenerate `P = Q` case; the bound does real work. -/
theorem one_lt_gaussian_renyi2_concrete :
    1 < ∑' x : ℤ, discreteGaussian 2 x ^ 2 / shiftedGaussian 2 1 x := by
  rw [gaussian_renyi2_concrete]
  linarith [Real.add_one_le_exp (1 / 4 : ℝ)]

/-- The concrete divergence is strictly below `4/3`: real-number teeth via `exp(1/4)⁴ = e < 2.72
< (4/3)⁴ = 256/81`. So the per-coordinate Rényi cost of a full unit shift at `σ = 2` is under
`34%` — the `O(1)` budget the parameter law promises. -/
theorem gaussian_renyi2_concrete_lt :
    ∑' x : ℤ, discreteGaussian 2 x ^ 2 / shiftedGaussian 2 1 x < 4 / 3 := by
  rw [gaussian_renyi2_concrete]
  refine lt_of_pow_lt_pow_left₀ 4 (by norm_num) ?_
  have h4 : Real.exp (1 / 4) ^ (4 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h4]
  calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    _ < (4 / 3 : ℝ) ^ (4 : ℕ) := by norm_num

/-- Preservation, concretely: at `σ = 2, δ = 1` EVERY finite event transfers with loss `exp(1/4)`:
`P(E)² ≤ exp(1/4) · Q(E)` — the Gaussian key-hiding bound in the exact shape
`RenyiHiding.renyi_probability_preservation` consumes. -/
theorem gaussian_preservation_concrete (E : Finset ℤ) :
    (∑ x ∈ E, discreteGaussian 2 x) ^ 2
      ≤ Real.exp (1 / 4) * ∑ x ∈ E, shiftedGaussian 2 1 x := by
  rw [show (1 / 4 : ℝ) = ((1 : ℤ) : ℝ) ^ 2 / 2 ^ 2 by norm_num]
  exact gaussian_probability_preservation (by norm_num) 1 E

#assert_axioms gaussianWeight_pos
#assert_axioms gaussian_ratio_exponent
#assert_axioms gaussian_ratio_shift
#assert_axioms summable_gaussianWeight
#assert_axioms thetaSum_pos
#assert_axioms tsum_gaussianWeight_add
#assert_axioms tsum_gaussianWeight_sub
#assert_axioms discreteGaussian_pos
#assert_axioms shiftedGaussian_pos
#assert_axioms tsum_discreteGaussian
#assert_axioms tsum_shiftedGaussian
#assert_axioms gaussian_renyi_term
#assert_axioms gaussian_renyiDiv2_eq
#assert_axioms gaussian_renyi2_le
#assert_axioms one_le_gaussian_renyi2
#assert_axioms summable_gaussian_renyi_term
#assert_axioms gaussian_probability_preservation
#assert_axioms gaussian_forgery_transfer
#assert_axioms gaussian_renyi2_pair
#assert_axioms gaussian_renyi2_concrete
#assert_axioms one_lt_gaussian_renyi2_concrete
#assert_axioms gaussian_renyi2_concrete_lt
#assert_axioms gaussian_preservation_concrete

end Dregg2.Crypto.GaussianRenyi
