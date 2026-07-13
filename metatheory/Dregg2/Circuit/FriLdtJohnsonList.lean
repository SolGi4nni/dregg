import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Dregg2.Circuit.FriLdtJohnson

/-!
# `RSListBound` at `L > 1` up to the Johnson radius — the combinatorial (Fisher/packing) bound.

`FriLdtJohnson.lean` proves `RSListBound C e 1` at the *unique-decoding* radius (the list is a
singleton: `rsListBound_uniqueDecoding`, from the Hamming triangle + minimum distance). The residual
it names is `RSListBound (codeC 6 ω) eJ L` for `L > 1` up to the Johnson radius
`eJ = ⌊(7/8)·128⌋ = 112`. This file DISCHARGES that residual for the deployed rate-`1/64` code.

## The math (elementary, for this code): a Fisher-type packing bound.

The deployed code `codeC 6 ω = {x ↦ a + b·ω^x}` has dimension `2`, so distinct codewords agree on
**at most one** point (minimum distance `127`, `wrap_minDist`). This collapses the general
Johnson/inner-product argument (`ℝ^{n·q}` indicator embedding) to a purely combinatorial one over
`Finset`s — no field-size embedding needed.

Let `c₁,…,c_L` be codewords each within Hamming distance `eJ` of a word `f`, and let
`Sᵢ = {x : cᵢ x = f x}` be their agreement sets. Then

* `|Sᵢ| ≥ a := n − eJ`   (each is `eJ`-close to `f`), and
* `|Sᵢ ∩ Sⱼ| ≤ 1` for `i ≠ j`   (where both agree with `f` they agree with each other, but distinct
  codewords agree on `≤ 1` point).

Writing `dₓ = #{i : x ∈ Sᵢ}` and `T = ∑ₓ dₓ = ∑ᵢ |Sᵢ| ≥ L·a`, double counting gives
`∑ₓ dₓ² = ∑_{i,j} |Sᵢ ∩ Sⱼ| ≤ T + L(L−1)`, and Cauchy–Schwarz gives `T² ≤ n·∑ₓ dₓ²`. Hence

    T² ≤ n·(T + L(L−1)),   with   T ≥ L·a.

For the deployed code `n = 128`, `a = 128 − 112 = 16`, this forces `L ≤ 15`
(`rsListBound_johnson_112`). The Johnson condition `a² > n` (here `256 > 128`) is exactly what makes
the quadratic bite; it is the combinatorial form of `δ < 1 − √ρ`.

## What is proved here (no `axiom`, no `sorry`).

* `packing_sum_sq_le`   — the double-counting upper bound `∑ₓ dₓ² ≤ T + L(L−1)`.
* `packing_sum_ge`      — the agreement lower bound `T ≥ L·a`.
* `packing_card_bound`  — the combined quadratic `T² ≤ n·(T + L(L−1))` with `L·a ≤ T`.
* `rsListBound_johnson_112` — `RSListBound (codeC 6 ω) 112 15` for the deployed code, the named
  `L > 1` residual, discharged at the Johnson radius `112 = ⌊(7/8)·128⌋`.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Dregg2.Circuit.FriLdtJohnson

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriDeployedInstance (omega128)

open scoped BigOperators

variable {F : Type*} [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The combinatorial packing core. -/

/-- `agreeCount f s x` — the number of functions in `s` that agree with `f` at the point `x`
(the `dₓ` of the packing argument). -/
def agreeCount (f : ι → F) (s : Finset (ι → F)) (x : ι) : ℕ :=
  (s.filter (fun g => g x = f x)).card

/-- **Column/row swap.** `∑ₓ dₓ = ∑_{g∈s} |{x : g x = f x}|` — total agreements counted by point or
by codeword. -/
theorem sum_agreeCount_swap (f : ι → F) (s : Finset (ι → F)) :
    ∑ x : ι, agreeCount f s x
      = ∑ g ∈ s, (Finset.univ.filter (fun x => g x = f x)).card := by
  unfold agreeCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **Agreement lower bound.** If every function in `s` agrees with `f` on `≥ a` points, then the
total agreement count is `≥ |s|·a`. This is `T ≥ L·a`. -/
theorem packing_sum_ge (f : ι → F) (s : Finset (ι → F)) (a : ℕ)
    (hclose : ∀ g ∈ s, a ≤ (Finset.univ.filter (fun x => g x = f x)).card) :
    s.card * a ≤ ∑ x : ι, agreeCount f s x := by
  rw [sum_agreeCount_swap]
  calc s.card * a = ∑ _g ∈ s, a := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ g ∈ s, (Finset.univ.filter (fun x => g x = f x)).card := Finset.sum_le_sum hclose

/-- Product of two `0/1` indicators is the indicator of the conjunction (over `ℕ`). -/
theorem ite_mul_ite_nat (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℕ) else 0) * (if Q then (1 : ℕ) else 0) = if P ∧ Q then (1 : ℕ) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- **`∑ₓ dₓ² = ∑_{g,g'∈s} |{x : g x = f x ∧ g' x = f x}|`** — expand the square of the column count
into a double sum of pairwise common-agreement counts. -/
theorem sum_sq_agreeCount_eq (f : ι → F) (s : Finset (ι → F)) :
    ∑ x : ι, (agreeCount f s x) ^ 2
      = ∑ g ∈ s, ∑ g' ∈ s,
          (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card := by
  have hpoint : ∀ x : ι, (agreeCount f s x) ^ 2
      = ∑ g ∈ s, ∑ g' ∈ s,
          (if g x = f x ∧ g' x = f x then (1 : ℕ) else 0) := by
    intro x
    unfold agreeCount
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun g' _ => ?_))
    exact ite_mul_ite_nat _ _
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g' _ => ?_)
  rw [Finset.card_filter]

/-- **The packing upper bound.** If distinct functions of `s` share `≤ 1` common agreement point
with `f`, then `∑ₓ dₓ² ≤ T + |s|·(|s|−1)` where `T = ∑ₓ dₓ`. This is the Fisher double-count:
the diagonal `g = g'` contributes `T`, and each of the `L(L−1)` off-diagonal pairs contributes `≤ 1`. -/
theorem packing_sum_sq_le (f : ι → F) (s : Finset (ι → F))
    (hpair : ∀ g ∈ s, ∀ g' ∈ s, g ≠ g' →
      (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card ≤ 1) :
    ∑ x : ι, (agreeCount f s x) ^ 2
      ≤ (∑ x : ι, agreeCount f s x) + s.card * (s.card - 1) := by
  rw [sum_sq_agreeCount_eq]
  -- Split each inner sum into its diagonal term `g' = g` and the erased remainder.
  have hsplit : ∀ g ∈ s,
      ∑ g' ∈ s, (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card
        = (Finset.univ.filter (fun x => g x = f x)).card
          + ∑ g' ∈ s.erase g, (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card := by
    intro g hg
    rw [← Finset.add_sum_erase s _ hg]
    congr 1
    simp only [and_self]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  gcongr ?_ + ?_
  · -- diagonal equals `T`
    exact le_of_eq (sum_agreeCount_swap f s).symm
  · -- off-diagonal: each ≤ 1, over `∑ g, |s.erase g| = |s|(|s|-1)` terms.
    calc ∑ g ∈ s, ∑ g' ∈ s.erase g,
              (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card
        ≤ ∑ g ∈ s, ∑ _g' ∈ s.erase g, 1 := by
          refine Finset.sum_le_sum (fun g hg => Finset.sum_le_sum (fun g' hg' => ?_))
          exact hpair g hg g' (Finset.mem_of_mem_erase hg') (Finset.ne_of_mem_erase hg').symm
      _ = ∑ g ∈ s, (s.erase g).card := by
          refine Finset.sum_congr rfl (fun g _ => ?_); rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ _g ∈ s, (s.card - 1) := by
          refine Finset.sum_congr rfl (fun g hg => ?_); rw [Finset.card_erase_of_mem hg]
      _ = s.card * (s.card - 1) := by rw [Finset.sum_const, smul_eq_mul]

/-- **The combined quadratic packing bound.** With `n = |ι|`, `L = |s|`, `T = ∑ₓ dₓ`: the agreement
lower bound `L·a ≤ T` and the quadratic `T² ≤ n·(T + L(L−1))`. Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) supplies `T² ≤ n·∑ₓ dₓ²`, chained with `packing_sum_sq_le`. -/
theorem packing_card_bound (f : ι → F) (s : Finset (ι → F)) (a : ℕ)
    (hclose : ∀ g ∈ s, a ≤ (Finset.univ.filter (fun x => g x = f x)).card)
    (hpair : ∀ g ∈ s, ∀ g' ∈ s, g ≠ g' →
      (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card ≤ 1) :
    s.card * a ≤ ∑ x : ι, agreeCount f s x ∧
    (∑ x : ι, agreeCount f s x) ^ 2
      ≤ Fintype.card ι * ((∑ x : ι, agreeCount f s x) + s.card * (s.card - 1)) := by
  refine ⟨packing_sum_ge f s a hclose, ?_⟩
  have hcs : (∑ x : ι, agreeCount f s x) ^ 2
      ≤ Fintype.card ι * ∑ x : ι, (agreeCount f s x) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := agreeCount f s)
    simpa [Finset.card_univ] using this
  calc (∑ x : ι, agreeCount f s x) ^ 2
      ≤ Fintype.card ι * ∑ x : ι, (agreeCount f s x) ^ 2 := hcs
    _ ≤ Fintype.card ι * ((∑ x : ι, agreeCount f s x) + s.card * (s.card - 1)) := by
        gcongr; exact packing_sum_sq_le f s hpair

/-! ## §2. The deployed code: distinct codewords agree on `≤ 1` point. -/

/-- **Distinct deployed codewords agree on `≤ 1` point.** From `wrap_minDist` (minimum distance
`> 126`): the disagreement set has `> 126` points out of `128`, so the agreement set has `< 2`. -/
theorem wrap_agree_le_one {g g' : Fin (2 ^ 7) → BabyBear}
    (hg : g ∈ codeC 6 omega128) (hg' : g' ∈ codeC 6 omega128) (hne : g ≠ g') :
    (Finset.univ.filter (fun x => g x = g' x)).card ≤ 1 := by
  have hd : 126 < (disagree g g').card := wrap_minDist g hg g' hg' hne
  have hcompl : (Finset.univ.filter (fun x : Fin (2 ^ 7) => g x = g' x))
      = (disagree g g')ᶜ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_disagree, Finset.mem_compl,
      ne_eq, not_not]
  rw [hcompl, Finset.card_compl]
  have hcard : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
  rw [hcard]
  omega

/-! ## §3. The Johnson list bound for the deployed code at radius `112 = ⌊(7/8)·128⌋`. -/

set_option maxRecDepth 4000 in
/-- **`RSListBound (codeC 6 ω) 112 15`** — the named `L > 1` residual, DISCHARGED for the deployed
rate-`1/64` RS code at the Johnson radius `112 = ⌊(7/8)·128⌋`.

At most `15` codewords lie within Hamming distance `112` of any word `f`. The proof takes the actual
list as a `Finset` (finite, since `BabyBear` is a `Fintype`), and bounds its card by the packing
argument: each listed codeword agrees with `f` on `≥ 16` points, distinct listed codewords share
`≤ 1` agreement point, and Cauchy–Schwarz then forces `|list|² ` down — the Johnson condition
`16² = 256 > 128 = n` is what closes it. -/
theorem rsListBound_johnson_112 : RSListBound (codeC 6 omega128) 112 15 := by
  intro f
  -- the decoding list as a finset (finite: it is a subset of a finite type)
  have hfin : {g : Fin (2 ^ 7) → BabyBear | g ∈ codeC 6 omega128 ∧ (disagree f g).card ≤ 112}.Finite :=
    Set.toFinite _
  refine ⟨hfin.toFinset, ?_, by rw [hfin.coe_toFinset]⟩
  set L := hfin.toFinset with hLdef
  -- membership unfold
  have hmem : ∀ g, g ∈ L ↔ g ∈ codeC 6 omega128 ∧ (disagree f g).card ≤ 112 := by
    intro g; rw [hLdef]; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  -- each codeword agrees with f on ≥ 16 points
  have hclose : ∀ g ∈ L, 16 ≤ (Finset.univ.filter (fun x => g x = f x)).card := by
    intro g hg
    obtain ⟨_, hclose'⟩ := (hmem g).mp hg
    have hcompl : (Finset.univ.filter (fun x : Fin (2 ^ 7) => g x = f x)) = (disagree f g)ᶜ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_disagree, Finset.mem_compl,
        ne_eq, not_not, eq_comm]
    rw [hcompl, Finset.card_compl]
    have hcard : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
    rw [hcard]; omega
  -- distinct listed codewords share ≤ 1 agreement point with f
  have hpair : ∀ g ∈ L, ∀ g' ∈ L, g ≠ g' →
      (Finset.univ.filter (fun x => g x = f x ∧ g' x = f x)).card ≤ 1 := by
    intro g hg g' hg' hne
    obtain ⟨hgC, _⟩ := (hmem g).mp hg
    obtain ⟨hg'C, _⟩ := (hmem g').mp hg'
    refine le_trans (Finset.card_le_card ?_) (wrap_agree_le_one hgC hg'C hne)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hx.1, hx.2]
  -- apply the packing bound
  obtain ⟨hge, hsq⟩ := packing_card_bound f L 16 hclose hpair
  have hn : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
  rw [hn] at hsq
  set T := ∑ x : Fin (2 ^ 7), agreeCount f L x with hT
  -- now: 16*|L| ≤ T  and  T² ≤ 128*(T + |L|*(|L|-1)).  Conclude |L| ≤ 15.
  by_contra hcon
  rw [not_le] at hcon     -- 15 < L.card, i.e. 16 ≤ L.card
  set c := L.card with hc
  have h16 : 16 ≤ c := hcon
  have h1 : 1 ≤ c := by omega
  -- forget that `T` and `c` are giant sums / cardinalities: treat as opaque naturals.
  clear_value T c
  -- cast to reals and finish by nlinarith
  have hgeR : (16 : ℝ) * c ≤ T := by rw [Nat.mul_comm] at hge; exact_mod_cast hge
  have h16R : (16 : ℝ) ≤ c := by exact_mod_cast h16
  have hsqR : (T : ℝ) ^ 2 ≤ 128 * ((T : ℝ) + (c : ℝ) * ((c : ℝ) - 1)) := by
    have hcast : ((T ^ 2 : ℕ) : ℝ) ≤ ((128 * (T + c * (c - 1)) : ℕ) : ℝ) := by exact_mod_cast hsq
    push_cast [Nat.cast_sub h1] at hcast
    linarith
  -- The equations `hT`, `hc` (and the Finset hypotheses) carry the giant `∑`/`Finset` terms; drop
  -- them so `nlinarith`'s context scan stays on the opaque naturals `T`, `c`.
  clear hT hc hge hsq hmem hclose hpair hn hcon
  have hTge : (128 : ℝ) ≤ T := by linarith [hgeR, h16R]
  -- The packing "product ≥ 0": `(T − 16c)(T + 16c − 128) ≥ 0`, both factors nonneg.
  have hp1 : (0 : ℝ) ≤ ((T : ℝ) - 16 * c) * ((T : ℝ) + 16 * c - 128) :=
    mul_nonneg (by linarith) (by linarith)
  have hexp : ((T : ℝ) - 16 * c) * ((T : ℝ) + 16 * c - 128)
      = (T : ℝ) ^ 2 - 128 * T - 256 * c ^ 2 + 2048 * c := by ring
  rw [hexp] at hp1                    -- hp1 : 0 ≤ T² − 128T − 256c² + 2048c
  -- The Cauchy–Schwarz side, in expanded form.
  have hB : (T : ℝ) ^ 2 ≤ 128 * T + 128 * c ^ 2 - 128 * c := by nlinarith [hsqR]
  -- Chain: 256c² − 2048c ≤ T²−128T ≤ 128c² − 128c ⟹ 128c² ≤ 1920c.
  have hC : 128 * (c : ℝ) ^ 2 ≤ 1920 * c := by linarith [hp1, hB]
  -- But c ≥ 16 gives c² ≥ 16c, so 2048c ≤ 128c² ≤ 1920c ⟹ 128c ≤ 0 — contradiction.
  have hD : 16 * (c : ℝ) ≤ c ^ 2 := by nlinarith [h16R]
  linarith [hC, hD, h16R]

/-! ## §4. Axiom hygiene. -/

#assert_axioms sum_agreeCount_swap
#assert_axioms packing_sum_ge
#assert_axioms sum_sq_agreeCount_eq
#assert_axioms packing_sum_sq_le
#assert_axioms packing_card_bound
#assert_axioms wrap_agree_le_one
#assert_axioms rsListBound_johnson_112

end Dregg2.Circuit.FriLdtJohnson
