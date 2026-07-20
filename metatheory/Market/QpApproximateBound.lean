/-
# Market.QpApproximateBound — an honest quantitative meaning for inexact stationarity.

The deployed OSQP-shaped checker accepts three residuals at a positive tolerance.  That fact alone
does not imply exact global optimality: approximate primal feasibility and approximate projection
membership need their own error analysis.  There is nevertheless a useful proof-carrying rung that
does not overclaim.

If the candidate is exactly feasible, its dual is exactly in the constraint-box normal cone, and
only stationarity is inexact with coordinatewise error at most `epsilon`, convexity proves

    f(x) <= f(x') + epsilon * ||x' - x||_1

for every feasible competitor `x'`.  A relying product with an independently certified feasible-set
diameter `R` immediately gets an `epsilon * R` additive optimality guarantee.  This is the precise
distance term that disappears when stationarity is exact.

Wire parsing, fixed-point scaling, an `R` certificate, and reduction of the deployed positive primal
and normal residuals remain outside this theorem.
-/

import Market.CertQpRustDenotation
import Dregg2.Tactics

namespace Market.QpApproximateBound

set_option autoImplicit false

open Matrix

/-- Coordinatewise exact-rational stationarity error bound. -/
def StationarityResidualAtMost {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (x : Fin n -> ℚ) (y : Fin mc -> ℚ)
    (epsilon : ℚ) : Prop :=
  ∀ j, |Market.rustPTimes prob x j + prob.q j + Market.rustATTimes prob y j| ≤ epsilon

/-- The exact feasible/normal-cone envelope with bounded, possibly nonzero stationarity. -/
structure DistanceBoundedKkt {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (x : Fin n -> ℚ) (y : Fin mc -> ℚ)
    (epsilon : ℚ) : Prop where
  epsilon_nonneg : 0 ≤ epsilon
  feasible : Market.RustQpFeasible prob x
  stationarity : StationarityResidualAtMost prob x y epsilon
  normalCone : Market.RustQpNormalCone prob x y

/-- L1 displacement from the certified point to a competitor. -/
def l1Distance {n : Nat} (x x' : Fin n -> ℚ) : ℚ :=
  ∑ j, |x' j - x j|

theorem residual_dot_lower_bound {n : Nat} {r delta : Fin n -> ℚ} {epsilon : ℚ}
    (hres : ∀ j, |r j| ≤ epsilon) :
    -(epsilon * ∑ j, |delta j|) ≤ r ⬝ᵥ delta := by
  have hterm : ∀ j, -(epsilon * |delta j|) ≤ r j * delta j := by
    intro j
    have hlo : -epsilon ≤ r j := by
      have habs := neg_abs_le (r j)
      linarith [hres j]
    have hhi : r j ≤ epsilon := le_trans (le_abs_self (r j)) (hres j)
    by_cases hdelta : 0 ≤ delta j
    · have hmul := mul_le_mul_of_nonneg_right hlo hdelta
      simpa [abs_of_nonneg hdelta] using hmul
    · have hdelta' : delta j ≤ 0 := le_of_not_ge hdelta
      have hmul := mul_le_mul_of_nonpos_right hhi hdelta'
      rw [abs_of_nonpos hdelta']
      linarith
  rw [dotProduct]
  calc
    -(epsilon * ∑ j, |delta j|) = ∑ j, -(epsilon * |delta j|) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    _ ≤ ∑ j, r j * delta j := Finset.sum_le_sum fun j _ => hterm j

/-- **Approximate KKT distance law.** Exact feasibility and exact normal-cone membership turn a
coordinatewise stationarity tolerance into a quantitative objective bound, rather than a false exact
optimality claim. -/
theorem approximate_kkt_distance_bound {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (hP : Market.PsdSymm prob.p)
    {x : Fin n -> ℚ} {y : Fin mc -> ℚ} {epsilon : ℚ}
    (cert : DistanceBoundedKkt prob x y epsilon)
    {x' : Fin n -> ℚ} (hfeas' : Market.RustQpFeasible prob x') :
    Market.rustQpObjective prob x ≤
      Market.rustQpObjective prob x' + epsilon * l1Distance x x' := by
  let residual : Fin n -> ℚ := fun j =>
    Market.rustPTimes prob x j + prob.q j + Market.rustATTimes prob y j
  have hnormalPoint : ∀ i,
      y i * (Market.rustATimes prob x' i - Market.rustATimes prob x i) ≤ 0 := by
    intro i
    exact Market.rustClamp_fixed_normal (cert.feasible i).1 (cert.feasible i).2
      (hfeas' i).1 (hfeas' i).2 (cert.normalCone i)
  have hnormalSum :
      y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) ≤ 0 := by
    rw [dotProduct]
    apply Finset.sum_nonpos
    intro i _hi
    simpa [Market.rustATimes_eq_mulVec] using hnormalPoint i
  have hdecomp : prob.p *ᵥ x + prob.q = residual - (y ᵥ* prob.a) := by
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, residual]
    rw [← Market.rustPTimes_eq_mulVec, ← Market.rustATTimes_eq_vecMul]
    ring
  have hgrad :
      (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) =
        residual ⬝ᵥ (x' - x) -
          y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) := by
    rw [hdecomp, sub_dotProduct, ← dotProduct_mulVec, mulVec_sub]
  have hres : ∀ j, |residual j| ≤ epsilon := by
    intro j
    exact cert.stationarity j
  have hresLower :
      -(epsilon * l1Distance x x') ≤ residual ⬝ᵥ (x' - x) := by
    simpa [l1Distance] using
      (residual_dot_lower_bound (r := residual) (delta := x' - x)
        hres)
  let core : Market.QP (Fin n) (Fin 0) :=
    { P := prob.p
      q := prob.q
      A := fun i => i.elim0
      b := fun i => i.elim0
      l := fun _ => 0
      u := fun _ => 0
      ε := 0 }
  have hconv := Market.quad_convex_ge (qp := core) hP x x'
  change (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) ≤
    Market.rustQpObjective prob x' - Market.rustQpObjective prob x at hconv
  rw [hgrad] at hconv
  linarith

/-- A separately certified feasible-set radius removes the competitor-dependent term. -/
theorem approximate_kkt_radius_bound {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (hP : Market.PsdSymm prob.p)
    {x : Fin n -> ℚ} {y : Fin mc -> ℚ} {epsilon radius : ℚ}
    (cert : DistanceBoundedKkt prob x y epsilon)
    (hradius : ∀ x', Market.RustQpFeasible prob x' -> l1Distance x x' ≤ radius)
    {x' : Fin n -> ℚ} (hfeas' : Market.RustQpFeasible prob x') :
    Market.rustQpObjective prob x ≤ Market.rustQpObjective prob x' + epsilon * radius := by
  have hbase := approximate_kkt_distance_bound prob hP cert hfeas'
  have hscale := mul_le_mul_of_nonneg_left (hradius x' hfeas') cert.epsilon_nonneg
  linarith

/-! ## Executable/non-vacuous one-dimensional tooth. -/

def approximateFixture : DistanceBoundedKkt Market.rustQpOne
    Market.rustApproxWitness.x Market.rustApproxWitness.y 1 where
  epsilon_nonneg := by norm_num
  feasible := by
    intro i
    fin_cases i
    norm_num [Market.rustQpOne, Market.rustApproxWitness, Market.rustATimes]
  stationarity := by
    intro j
    fin_cases j
    norm_num [StationarityResidualAtMost, Market.rustQpOne, Market.rustApproxWitness,
      Market.rustPTimes, Market.rustATTimes]
  normalCone := by
    intro i
    fin_cases i
    norm_num [Market.rustQpOne, Market.rustApproxWitness, Market.rustATimes, Market.rustClamp]

/-- The accepted positive stationarity tolerance does not claim that `x=0` beats the true feasible
optimum `x'=1`; it proves only the honest additive-distance bound. -/
theorem approximateFixture_bound :
    Market.rustQpObjective Market.rustQpOne Market.rustApproxWitness.x ≤
      Market.rustQpObjective Market.rustQpOne (fun _ => 1) +
        1 * l1Distance Market.rustApproxWitness.x (fun _ => 1) := by
  apply approximate_kkt_distance_bound Market.rustQpOne Market.qp1_psd approximateFixture
  intro i
  fin_cases i
  norm_num [Market.rustQpOne, Market.rustATimes]

#guard Market.rustQpObjective Market.rustQpOne (fun _ => 1) <
  Market.rustQpObjective Market.rustQpOne Market.rustApproxWitness.x

#assert_axioms residual_dot_lower_bound
#assert_axioms approximate_kkt_distance_bound
#assert_axioms approximate_kkt_radius_bound
#assert_axioms approximateFixture_bound

#assert_not_depends_on Market.QpApproximateBound.StationarityResidualAtMost [
  Market.PsdSymm,
  Market.RustQpFeasible,
  Market.RustQpNormalCone]

#assert_all_clean [
  Market.QpApproximateBound.residual_dot_lower_bound,
  Market.QpApproximateBound.approximate_kkt_distance_bound,
  Market.QpApproximateBound.approximate_kkt_radius_bound,
  Market.QpApproximateBound.approximateFixture_bound]

end Market.QpApproximateBound
