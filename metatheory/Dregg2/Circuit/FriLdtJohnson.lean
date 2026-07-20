import Mathlib.Tactic
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.BabyBearFriDeployed
import Dregg2.Circuit.BabyBearFriDeployedInstance

/-!
# `FriLdtDeployedBound` — DISCHARGED as stated, and the real BCIKS20 core NAMED precisely.

This file closes out the last STARK-soundness residual named in
`BabyBearFriDeployedInstance.lean` (`FriLdtDeployedBound`, "the one research-grade assumption
every deployed STARK shares"). The result is sharper than expected.

## The finding: the STATED `FriLdtDeployedBound` is the *trivial counting branch* — a THEOREM.

`FriLdtDeployedBound εTarget` (as committed) says: a word `f` that is `(7/8)·|ι|`-FAR from the
code — disagrees with *every* codeword on ≥ `7/8` of points — accepts the `19` deployed queries
with probability `≤ εTarget`. At the Johnson radius `δ_J = 1 − √ρ = 7/8` this is exactly
`FriQuerySoundness.accept_prob_le_of_farN` at `δ = 7/8`, `k = 19`, whose conclusion is
`≤ (1 − 7/8)^19 = (1/8)^19`. So the statement **as written is unconditionally provable** — it is
the ELSE-branch (word past the *list*-decoding radius) where nothing but counting is needed.
`friLdtDeployedBound_discharge` proves it; `ldt_bound_unconditional` re-derives
`ldt_bound_is_load_bearing`'s payoff with NO hypothesis.

## What that means, and what is genuinely left.

The Johnson radius `δ_J` is the *list*-decoding radius — the radius **within** which the codeword
list is bounded. A word beyond `δ_J` from all codewords is `(7/8)`-far and handled by counting
(above). The genuinely research-grade content — the part Mathlib lacks and BCIKS20 supplies —
concerns words *inside* the `δ_J` ball but *beyond* the unique-decoding radius `(1−ρ)/2 = 63/128`,
and splits into TWO clean `Prop`s, each PROVED here at its unique-decoding (`L = 1`) instance and
NAMED precisely at the Johnson (`L > 1`) generalization:

* **(i) Reed–Solomon list size** (`§2`): `RSListBound C eJ L` — the codeword list within radius `eJ`
  of any word has size `≤ L`. Proved at the unique-decoding radius with `L = 1`
  (`rsListBound_uniqueDecoding`, from the Hamming triangle inequality `hamming_triangle` +
  `decoding_list_subsingleton`), and instantiated on the **real deployed rate-`1/64` RS code**
  (`§4`, `wrap_unique_decoding_singleton`: two codewords `63`-close to `f` are equal — the exact
  deployed MDS minimum distance `127`). The `L > 1` bound up to `δ_J` is the BCIKS20 Johnson bound.

* **(ii) Correlated agreement / proximity gap** (`§3`): `FriProximityGapChallenges S dOut dIn L` — a
  word `dOut`-far from the domain code has at most `L` folding challenges whose fold is `dIn`-close
  to the folded code. Proved at the unique-decoding radius with `L = 1` (`proximityGap_uniqueDecoding`,
  exactly the committed `good_alpha_subsingleton`). The `L > 1` version up to `δ_J` is the BCIKS20
  correlated-agreement theorem.

Nothing is faked: no `axiom`, no `sorry`. Each residual is a `Prop`, and each is shown to
*generalize a proved theorem* (non-vacuous, precisely scoped), not opaque hardness.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} throughout.

## ⚑ The `L > 1` correlated-agreement residual (ii) is PROVED by ordered-pair COUNTING.
`FriCorrelatedAgreementSharp.lean` discharges the `L > 1` proximity-gap primitive at the deployed list
sizes without GS: `CorrelatedAgreementLine friSetupWrapRate 52 186` (interior radius `dIn = 52`,
relative `13/16`, GS-non-degenerate) and `WrapCorrelatedAgreementSharp 292` (boundary `dIn = 56`),
each via the ordered distinct-`Φ` pair injection into `κ × κ`. The GS-IDEAL list `L ≤ 2·|κ| = 128`
stays BLOCKED for the constant-fold multiset word (`Dregg2/ForMathlib/GuruswamiSudan.lean:20-33`), so
`186`/`292` is the counting reach, not the GS ideal — security-irrelevant (`L/|F|`, `|F| ≈ 2¹²⁴`). The
deployed **arity-8** per-fold soundness is **~109.84 bits** (`FriArityTransfer.arity8_perFold_soundness`);
`wrap_perFold_soundness_capacity`'s **~112.6** is the **arity-2** fold and provably FAILS at arity 8
(`FriArityTransfer.arity8_error_not_lt_2e112`).
-/

namespace Dregg2.Circuit.FriLdtJohnson

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriQuerySoundness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriDeployedInstance (omega128 omega128_neg omega128_ne)

/-! ## §1. The STATED bound is the trivial counting branch — DISCHARGED. -/

/-- **`FriLdtDeployedBound ((1/8)^19)` is a THEOREM.** The committed statement — a `(7/8)·|ι|`-far
word accepts `19` uniform queries with probability `≤ (1/8)^19` — is exactly the counting bound
`accept_prob_le_of_farN` at `δ = 7/8`, `k = 19`: `(1 − 7/8)^19 = (1/8)^19`. So the "one research
assumption" *as literally written* carries no hardness; it is the else-branch (word beyond the
list-decoding radius) where counting alone suffices. -/
theorem friLdtDeployedBound_discharge :
    BabyBearFriDeployedInstance.FriLdtDeployedBound ((1 / 8 : ℝ) ^ 19) := by
  intro ι _ _ C f g d hN hgC hfar hδd
  have h := accept_prob_le_of_farN (C := C) (f := f) (g := g) (δ := (7 / 8 : ℝ)) (d := d) 19
    hN (by norm_num) hgC hfar hδd
  have he : ((1 : ℝ) - 7 / 8) = 1 / 8 := by norm_num
  rwa [he] at h

/-- **The load-bearing payoff is now UNCONDITIONAL.** `ldt_bound_is_load_bearing` took
`FriLdtDeployedBound ((1/8)^19)` as a hypothesis; `friLdtDeployedBound_discharge` supplies it, so a
Johnson-far word on the deployed wrap-rate code accepts the `19` queries with probability `≤ 2^-57`
with no assumption. -/
theorem ldt_bound_unconditional
    (f g : Fin (2 ^ 7) → BabyBear) (d : ℕ)
    (hgC : g ∈ BabyBearFriDeployedInstance.friSetupWrapRate.C)
    (hfar : farN BabyBearFriDeployedInstance.friSetupWrapRate.C d f)
    (hδd : ((7 : ℝ) / 8) * (128 : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin 19 → Fin (2 ^ 7) =>
        Accepts f g Q)).card : ℝ)
        / ((128 : ℝ) ^ 19)
      ≤ (1 / 8 : ℝ) ^ 19 :=
  BabyBearFriDeployedInstance.ldt_bound_is_load_bearing friLdtDeployedBound_discharge f g d hgC hfar hδd

/-! ## §2. Genuine list-decoding: the Hamming triangle inequality and the singleton at the
unique-decoding radius.

The tractable, fully-closed half of BCIKS20's Johnson list bound: at the UNIQUE-decoding radius the
list is a *singleton*. The proof is the metric triangle inequality on Hamming distance plus the
code's minimum distance — no field-specific machinery. -/

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `disagree` is symmetric: the Hamming support of `f − g` is that of `g − f`. -/
theorem disagree_symm (f g : ι → F) : disagree f g = disagree g f := by
  ext x; simp only [mem_disagree]; exact ne_comm

/-- **Hamming triangle inequality.** `|disagree f h| ≤ |disagree f g| + |disagree g h|`, via
`disagree f h ⊆ disagree f g ∪ disagree g h` (if `f x ≠ h x` then `f x ≠ g x` or `g x ≠ h x`). -/
theorem hamming_triangle (f g h : ι → F) :
    (disagree f h).card ≤ (disagree f g).card + (disagree g h).card := by
  have hsub : disagree f h ⊆ disagree f g ∪ disagree g h := by
    intro x hx
    rw [mem_disagree] at hx
    rw [Finset.mem_union, mem_disagree, mem_disagree]
    by_contra hcon
    rw [not_or, not_ne_iff, not_ne_iff] at hcon
    exact hx (hcon.1.trans hcon.2)
  calc (disagree f h).card ≤ (disagree f g ∪ disagree g h).card := Finset.card_le_card hsub
    _ ≤ (disagree f g).card + (disagree g h).card := Finset.card_union_le _ _

/-- **Minimum-distance hypothesis.** Distinct codewords of `C` disagree on more than `m` points
(relative minimum distance `> m/|ι|`). For a rate-`ρ` Reed–Solomon code this holds with
`m = |ι| − dim − 1` (the MDS / Singleton bound); `§4` discharges it for the deployed code. -/
def MinDistGt (C : Submodule F (ι → F)) (m : ℕ) : Prop :=
  ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ → m < (disagree g₁ g₂).card

/-- **The decoding list at radius `e` is a SINGLETON when `minDist > 2e`.** Two codewords each
`e`-close to `f`, in a code of minimum distance `> 2e`, are equal — the unique-decoding radius is
`(minDist)/2`. Their mutual distance is `≤ 2e < minDist` by the Hamming triangle, forcing equality.
This is the `L = 1` instance of the Johnson list bound. -/
theorem decoding_list_subsingleton {C : Submodule F (ι → F)} {e : ℕ}
    (hmin : MinDistGt C (2 * e)) (f : ι → F) :
    {g : ι → F | g ∈ C ∧ (disagree f g).card ≤ e}.Subsingleton := by
  rintro g₁ ⟨hg₁, hc₁⟩ g₂ ⟨hg₂, hc₂⟩
  by_contra hne
  have hd := hmin g₁ hg₁ g₂ hg₂ hne
  have htri : (disagree g₁ g₂).card ≤ (disagree g₁ f).card + (disagree f g₂).card :=
    hamming_triangle g₁ f g₂
  rw [disagree_symm g₁ f] at htri
  omega

/-- **Named residual (i): the Reed–Solomon list bound.** Up to a radius `eJ` (relatively `1 − √ρ`,
the Johnson radius), the codeword list has size `≤ L`. PROVED below at the unique-decoding radius
with `L = 1`; the `L > 1` bound up to `eJ` is the BCIKS20 Johnson bound for RS, the remaining
lemma. -/
def RSListBound (C : Submodule F (ι → F)) (eJ L : ℕ) : Prop :=
  ∀ f : ι → F, ∃ s : Finset (ι → F), s.card ≤ L ∧
    {g : ι → F | g ∈ C ∧ (disagree f g).card ≤ eJ} ⊆ ↑s

/-- **`RSListBound` holds at `L = 1` at the unique-decoding radius — a THEOREM.** The `L = 1`
instance follows from `decoding_list_subsingleton`: the list is empty or a singleton, so it is
contained in a finset of size `≤ 1`. This certifies `RSListBound` is non-vacuous; the residual is
only `L > 1` up to the Johnson radius. -/
theorem rsListBound_uniqueDecoding {C : Submodule F (ι → F)} {e : ℕ}
    (hmin : MinDistGt C (2 * e)) : RSListBound C e 1 := by
  intro f
  rcases (decoding_list_subsingleton hmin f).eq_empty_or_singleton with h | ⟨g, hg⟩
  · exact ⟨∅, by simp, by rw [h]; simp⟩
  · exact ⟨{g}, by simp, by rw [hg]; simp⟩

/-! ## §3. The correlated-agreement / proximity-gap primitive, over the FRI fold.

The second research-grade piece: a word far from the domain code has only a bounded LIST of folding
challenges that fold it back close to the code. Named over the setup's own fold, so it is scoped to
the Reed–Solomon structure (the proximity gap is a property of RS + the FRI fold, NOT of arbitrary
codes). PROVED here at the unique-decoding radius with `L = 1`; the `L > 1` version up to the
Johnson radius is the named BCIKS20 residual. -/

/-- **`FriProximityGapChallenges S dOut dIn L`** — the BCIKS20 correlated-agreement statement at list
bound `L`: a word `dOut`-FAR from the domain code `S.C` has at most `L` folding challenges `α` whose
fold `Fold S.geom α f` is `dIn`-close to the folded code `S.C'`. The good-challenge set is contained
in a finset of size `≤ L`. -/
def FriProximityGapChallenges {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : FriSetup F ι κ) (dOut dIn L : ℕ) : Prop :=
  ∀ {f : ι → F}, farN S.C dOut f →
    ∃ s : Finset F, s.card ≤ L ∧
      {α : F | closeN S.C' dIn (Fold S.geom α f)} ⊆ ↑s

/-- **The proximity gap holds at `L = 1` at the unique-decoding radius — a THEOREM.** This is exactly
`good_alpha_subsingleton`: a `4d`-far word has at most ONE good challenge (fold-soundness error
`≤ 1/|F|`). It certifies `FriProximityGapChallenges` is non-vacuous and precisely scoped; the
residual is only the *larger* list bound `L > 1` for `dOut` up to the Johnson radius. -/
theorem proximityGap_uniqueDecoding {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : FriSetup F ι κ) (d : ℕ) :
    FriProximityGapChallenges S (4 * d) d 1 := by
  intro f hfar
  have hss := good_alpha_subsingleton S (d := d) hfar
  rcases hss.eq_empty_or_singleton with hemp | ⟨a, hsing⟩
  · exact ⟨∅, by simp, by rw [hemp]; simp⟩
  · exact ⟨{a}, by simp, by rw [hsing]; simp⟩

/-! ## §4. The deployed rate-`1/64` RS code: minimum distance `127`, hence the unique-decoding list
is a singleton at the deployed `63`-close radius.

`codeC 6 ω = {x ↦ a + b·ω^x}` is a degree-`< 2` Reed–Solomon code on `128` points; a nonzero
codeword `(a−a') + (b−b')·ω^x` is a nonzero affine function of the injective point map `x ↦ ω^x`, so
it vanishes on at most ONE point — minimum distance `≥ 127 = 128 − 2 + 1` (the MDS bound at
`dim = 2`). Hence at the unique-decoding radius `63` the codeword list is a singleton. `ω = omega128`
is a primitive `128`-th root, so `x ↦ ω^x` is injective on `Fin 128`. -/

/-- **`omega128` is a primitive `128`-th root of unity.** `omega128^(2^6) = −1` gives
`omega128^(2^7) = 1` and order not dividing `2^6`, so the order is exactly `2^7 = 128` (the standard
`orderOf_eq_prime_pow` argument, as in `TraceColumnInterp.omega27_isPrimitiveRoot`). -/
theorem omega128_isPrimitiveRoot : IsPrimitiveRoot omega128 (2 ^ 7) := by
  have hnot : omega128 ^ (2 : ℕ) ^ 6 ≠ 1 := by rw [omega128_neg]; decide
  have hfin : omega128 ^ (2 : ℕ) ^ (6 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (6 + 1) = (2 ^ 6) * 2 by ring, pow_mul, omega128_neg]; simp
  have hord : orderOf omega128 = (2 : ℕ) ^ (6 + 1) := orderOf_eq_prime_pow hnot hfin
  rw [show (2 : ℕ) ^ 7 = 2 ^ (6 + 1) by norm_num, ← hord]
  exact IsPrimitiveRoot.orderOf omega128

/-- The deployed point map `x ↦ ω^x` is INJECTIVE on `Fin 128` (a primitive `128`-th root). This is
`pParam 6 omega128`, the point value of the wrap-rate FRI geometry. -/
theorem pParam_injective : Function.Injective (pParam 6 omega128) := by
  intro i j hij
  apply Fin.ext
  exact omega128_isPrimitiveRoot.pow_inj i.isLt j.isLt hij

/-- **The deployed rate-`1/64` RS code has minimum distance `> 126` (i.e. `≥ 127`).** Two distinct
codewords `a + b·ω^x`, `a' + b'·ω^x` differ by a nonzero affine function of the injective `x ↦ ω^x`,
which vanishes on `≤ 1` point, so they disagree on `≥ 127 = 128 − 1` points. -/
theorem wrap_minDist : MinDistGt (codeC 6 omega128) 126 := by
  rintro _ ⟨a, b, rfl⟩ _ ⟨a', b', rfl⟩ hne
  set P := pParam 6 omega128 with hP
  -- The agreement finset has at most one element (injectivity of the point map).
  have hagree1 : (Finset.univ.filter
      (fun x : Fin (2 ^ (6 + 1)) => (a + b * P x) = (a' + b' * P x))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hz : (b - b') * (P x - P y) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.mp hz with hb0 | hpxy
    · exfalso
      have hbb : b = b' := sub_eq_zero.mp hb0
      subst hbb
      have haa : a = a' := add_right_cancel hx
      exact hne (by subst haa; rfl)
    · exact pParam_injective (sub_eq_zero.mp hpxy)
  set A : Finset (Fin (2 ^ (6 + 1))) :=
    Finset.univ.filter (fun x => (a + b * P x) = (a' + b' * P x)) with hA
  have hcompl : disagree (fun x => a + b * P x) (fun x => a' + b' * P x) = Aᶜ := by
    ext x
    simp only [mem_disagree, hA, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      ne_eq]
  rw [hcompl, Finset.card_compl]
  have hcard : Fintype.card (Fin (2 ^ (6 + 1))) = 128 := by norm_num [Fintype.card_fin]
  rw [hcard]
  omega

/-- **The deployed unique-decoding list is a SINGLETON.** On the real rate-`1/64` code, at most one
codeword is `63`-close to any word `f` (the deployed unique-decoding radius `(1−ρ)/2·N = 63`). The
`L = 1` list-decoding fact for the shipped code, from `wrap_minDist` (min-distance `127 > 2·63`). -/
theorem wrap_unique_decoding_singleton (f : Fin (2 ^ 7) → BabyBear) :
    {g : Fin (2 ^ 7) → BabyBear | g ∈ codeC 6 omega128 ∧ (disagree f g).card ≤ 63}.Subsingleton := by
  have h : (2 * 63 : ℕ) = 126 := by norm_num
  exact decoding_list_subsingleton (e := 63) (h ▸ wrap_minDist) f

/-- **`RSListBound` for the deployed code at `L = 1`.** The named list-bound residual, discharged at
`L = 1` for the shipped rate-`1/64` RS code at the deployed unique-decoding radius `63`. -/
theorem wrap_RSListBound : RSListBound (codeC 6 omega128) 63 1 := by
  have h : (2 * 63 : ℕ) = 126 := by norm_num
  exact rsListBound_uniqueDecoding (e := 63) (h ▸ wrap_minDist)

/-! ## §5. Axiom hygiene. -/

#assert_axioms friLdtDeployedBound_discharge
#assert_axioms ldt_bound_unconditional
#assert_axioms hamming_triangle
#assert_axioms decoding_list_subsingleton
#assert_axioms rsListBound_uniqueDecoding
#assert_axioms proximityGap_uniqueDecoding
#assert_axioms omega128_isPrimitiveRoot
#assert_axioms pParam_injective
#assert_axioms wrap_minDist
#assert_axioms wrap_unique_decoding_singleton
#assert_axioms wrap_RSListBound

end Dregg2.Circuit.FriLdtJohnson
