/-
# `Dregg2.Circuit.FriQuerySamplingBias` — the QUANTITATIVE uniformity-defect term for the
deployed `Challenger.sampleBits` query indices.

This is the well-defined next sub-lemma of the FRI extraction floor: **blocker (b)** of
`FriVerifierCompose.friLdtExtractV3_rom_of_legs`
(`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5, Stages 4–5).

## The gap this closes

Stage 5 (`FriVerifierCompose`) proved the deployed query indices are QUALITATIVELY
non-uniform: `babybear_sampleBits_not_balanced` shows `toNat(squeeze) % 2^logN` cannot have
equal-sized residue buckets at any shipped `logN` — because `|F| = 2013265921` is ODD, so
`2^logN ∤ |F|` (`babybear_order_not_divisible_by_two` + pigeonhole). But it left the defect
UNQUANTIFIED. In its own words:

> "the bias is small (`≈ 2^logN / |F|` relative) but it is NONZERO and NO in-tree theorem
> accounts for it. Composing `εQuery` over the oracle therefore needs a uniformity-defect term
> that does not exist."

This file supplies exactly that term. `εQuery` (`FriVerifierQuery.epsilon_query_layer_carried`)
models the `k` query indices as UNIFORM draws `Q : Fin k → κ` and bounds a `δ`-far word's
per-index survival by `(1 − δ)`. The deployed index is `n % m` with `n` a uniform squeeze value
over `N := |F|` and `m := 2^logN = |κ|`. `residue_reduction_prob_le` below bounds, for ANY
residue event `E : Finset ℕ`,

    Pr_{n unif range N}[ n % m ∈ E ]  ≤  |E| / m  +  m / N.

The first addend is the uniform probability `εQuery` already uses; the SECOND, `m / N =
2^logN / |F|`, IS the uniformity-defect term (`babybear_query_bias_le`). Taking `E` the per-index
MISS set (`|E| = m − |D|`, uniform miss `= 1 − δ`) upgrades the deployed per-index survival to
`(1 − δ) + 2^logN/|F|`, so a bias-aware `εQuery` composes as `L/|F| + ((1−δ) + 2^logN/|F|)^k` —
the sampling defect enters as a single explicit addend, PROVEN, not papered.

## Non-vacuity / what makes it false

The defect term is LOAD-BEARING, not slack. `residue_bias_defect_load_bearing` exhibits
`N = 3, m = 2, E = {0}` where `Pr[n % 2 ∈ {0}] = 2/3` STRICTLY EXCEEDS the naive uniform value
`|E|/m = 1/2` — so the bound WITHOUT the `+ m/N` addend is FALSE, and `m/N` is exactly what a
non-dividing `m ∤ N` (the deployed regime) forces. The core counting lemma `residueClassCard_le`
would be false if a residue class held more than `⌊N/m⌋ + 1` elements of `range N` — it cannot,
by the injection `n ↦ n / m` (within one class `n = m·(n/m) + j` is recovered, and `n < N`
forces `n/m ≤ N/m`).

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`,
no `native_decide`.
-/
import Dregg2.Circuit.FriVerifierCompose

set_option autoImplicit false

namespace Dregg2.Circuit.FriQuerySamplingBias

open Finset

/-! ## 1. The core counting fact — a residue class of `range N` has `≤ ⌊N/m⌋ + 1` elements. -/

/-- **A RESIDUE CLASS IS SMALL.** Among `{0, …, N−1}`, at most `⌊N/m⌋ + 1` numbers are
congruent to `j` mod `m`. The injection is `n ↦ n / m`: within one residue class `n` is recovered
from `n / m` (as `m·(n/m) + j`), and `n < N` forces `n / m ≤ N / m`. (No `0 < m` needed: at
`m = 0` the class is `{j}` and `N / 0 + 1 = 1`, so the bound holds a fortiori.) -/
theorem residueClassCard_le (N m j : ℕ) :
    ((Finset.range N).filter (fun n => n % m = j)).card ≤ N / m + 1 := by
  classical
  rw [← Finset.card_range (N / m + 1)]
  refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
  · intro n hn
    obtain ⟨hnN, _⟩ := Finset.mem_filter.1 hn
    have hle : n / m ≤ N / m := Nat.div_le_div_right (le_of_lt (Finset.mem_range.1 hnN))
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hle)
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hab' : a / m = b / m := hab
    calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
      _ = m * (b / m) + b % m := by rw [hab', ha.2, hb.2]
      _ = b := Nat.div_add_mod b m

/-- **A RESIDUE EVENT IS SMALL.** For any set `E` of residues, at most `|E| · (⌊N/m⌋ + 1)`
numbers in `{0, …, N−1}` reduce into `E` mod `m` — the residue-class bound summed over `E`. -/
theorem residueSetCard_le (N m : ℕ) (E : Finset ℕ) :
    ((Finset.range N).filter (fun n => n % m ∈ E)).card ≤ E.card * (N / m + 1) := by
  classical
  have hsplit : (Finset.range N).filter (fun n => n % m ∈ E)
      = E.biUnion (fun j => (Finset.range N).filter (fun n => n % m = j)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨hn, hmem⟩; exact ⟨n % m, hmem, hn, rfl⟩
    · rintro ⟨j, hj, hn, hnj⟩; exact ⟨hn, hnj ▸ hj⟩
  rw [hsplit]
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_card_nsmul E _ (N / m + 1) (fun j _ => residueClassCard_le N m j)).trans ?_
  rw [smul_eq_mul]

/-! ## 2. ⚑ THE UNIFORMITY-DEFECT TERM. -/

/-- **⚑ THE MODULAR-REDUCTION SAMPLING BIAS, BOUNDED.** For `n` uniform over `{0, …, N−1}` and
any residue event `E` (with `|E| ≤ m`), the reduced index `n % m` lands in `E` with probability
at most `|E|/m + m/N`. The first addend is the value a UNIFORM index would give; the second,
`m/N`, is the uniformity-defect term the deployed `sampleBits` reduction incurs — the term
`FriVerifierCompose` names as missing. -/
theorem residue_reduction_prob_le (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (E : Finset ℕ)
    (hE : E.card ≤ m) :
    (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) / (N : ℝ)
      ≤ (E.card : ℝ) / (m : ℝ) + (m : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  -- The Nat numerator bound, cast to `ℝ`.
  set B : ℝ := (E.card : ℝ) * (((N / m : ℕ) : ℝ) + 1) with hBdef
  have hnumR : (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) ≤ B := by
    have h := (Nat.cast_le (α := ℝ)).2 (residueSetCard_le N m E)
    rw [hBdef]; push_cast at h ⊢; linarith
  -- `⌊N/m⌋ ≤ N/m` as reals.
  have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR]; exact_mod_cast Nat.div_mul_le_self N m
  -- Bound `B` by `|E|·N/m + m`, using `|E| ≤ m` for the trailing `+ |E|`.
  have hEcardR : (E.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hE
  have hB : B ≤ (E.card : ℝ) * (N : ℝ) / (m : ℝ) + (m : ℝ) := by
    have h1 : (E.card : ℝ) * ((N / m : ℕ) : ℝ) ≤ (E.card : ℝ) * ((N : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    have hBexp : B = (E.card : ℝ) * ((N / m : ℕ) : ℝ) + (E.card : ℝ) := by rw [hBdef]; ring
    rw [hBexp]
    have hmul : (E.card : ℝ) * ((N : ℝ) / (m : ℝ)) = (E.card : ℝ) * (N : ℝ) / (m : ℝ) := by ring
    linarith [h1, hEcardR, hmul.le, hmul.ge]
  -- Assemble: numerator ≤ B ≤ (|E|·N/m + m), then divide by N.
  have hfin : ((E.card : ℝ) * (N : ℝ) / (m : ℝ) + (m : ℝ)) / (N : ℝ)
      = (E.card : ℝ) / (m : ℝ) + (m : ℝ) / (N : ℝ) := by
    field_simp
  calc (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) / (N : ℝ)
      ≤ B / (N : ℝ) := by gcongr
    _ ≤ ((E.card : ℝ) * (N : ℝ) / (m : ℝ) + (m : ℝ)) / (N : ℝ) := by gcongr
    _ = (E.card : ℝ) / (m : ℝ) + (m : ℝ) / (N : ℝ) := hfin

/-! ## 3. The deployed instantiation — `m = 2^logN` buckets, `N = |F| = 2013265921`. -/

/-- **⚑ THE DEPLOYED QUERY-INDEX BIAS, BOUNDED.** `m = 2^logN` query buckets, `N = |F| =
2013265921` squeeze values. Any residue event's biased probability exceeds its uniform value
`|E|/2^logN` by at most `2^logN / |F|`. This is the QUANTITATIVE companion to
`FriVerifierCompose.babybear_sampleBits_not_balanced`: that theorem shows the buckets are UNEQUAL;
this one bounds BY HOW MUCH any event's probability can be inflated by that inequality — the
uniformity-defect addend `εQuery` must carry over the deployed non-uniform indices. -/
theorem babybear_query_bias_le (logN : ℕ) (E : Finset ℕ) (hE : E.card ≤ 2 ^ logN) :
    (((Finset.range 2013265921).filter (fun n => n % (2 ^ logN) ∈ E)).card : ℝ) / (2013265921 : ℝ)
      ≤ (E.card : ℝ) / ((2 : ℝ) ^ logN) + ((2 : ℝ) ^ logN) / (2013265921 : ℝ) := by
  have h := residue_reduction_prob_le 2013265921 (2 ^ logN) (by norm_num)
    (pow_pos (by norm_num : (0 : ℕ) < 2) logN) E hE
  have hcast : (((2 ^ logN : ℕ)) : ℝ) = (2 : ℝ) ^ logN := by push_cast; ring
  rw [hcast] at h
  exact h

/-! ## 4. FIRE — the defect term is load-bearing (its omission makes the bound FALSE). -/

/-- The concrete biased probability at `N = 3, m = 2, E = {0}`: `Pr[n % 2 = 0] = 2/3`. -/
theorem residue_bias_fires :
    (((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / (3 : ℝ) = 2 / 3 := by
  have hc : ((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card = 2 := by decide
  rw [hc]; norm_num

/-- **⚑ THE `+ m/N` TERM IS NECESSARY.** At `N = 3, m = 2, E = {0}` the biased probability `2/3`
STRICTLY EXCEEDS the naive uniform value `|E|/m = 1/2`. So `residue_reduction_prob_le` WITHOUT its
`+ m/N` addend would be FALSE — the defect term is load-bearing exactly in the `m ∤ N` regime the
deployed `sampleBits` lives in (`babybear_sampleBits_not_balanced`). -/
theorem residue_bias_defect_load_bearing :
    (1 : ℝ) / 2 < (((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / (3 : ℝ) := by
  rw [residue_bias_fires]; norm_num

/-- Sanity: the full bound (with the defect term) DOES hold at that same witness — `2/3 ≤ 1/2 +
2/3`. The `+ m/N` is what restores truth. -/
theorem residue_bias_bound_holds :
    (((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / ((3 : ℕ) : ℝ)
      ≤ ((({0} : Finset ℕ).card : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) :=
  residue_reduction_prob_le 3 2 (by norm_num) (by norm_num) ({0} : Finset ℕ) (by decide)

#assert_all_clean [
  residueClassCard_le,
  residueSetCard_le,
  residue_reduction_prob_le,
  babybear_query_bias_le,
  residue_bias_fires,
  residue_bias_defect_load_bearing,
  residue_bias_bound_holds
]

end Dregg2.Circuit.FriQuerySamplingBias
