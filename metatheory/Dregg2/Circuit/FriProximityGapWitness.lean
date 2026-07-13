import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.FriProximityGapListDecoding
import Dregg2.Circuit.FriLdtJohnsonList

/-!
# `BadChallengePoly` at `L > 1` — the BCIKS20 witness CONSTRUCTED, and
`FriProximityGapChallenges` DISCHARGED past the unique-decoding radius.

`FriProximityGapListDecoding.lean` built the machine: `good_set_card_le_of_poly` (roots bound a
set) and `friProximityGap_of_badChallengePoly` (the witness ⟹ the proximity gap, for ANY `L`),
with `BadChallengePoly` proved only at `L = 1` (`badChallengePoly_uniqueDecoding`, the
unique-decoding endpoint). Its §4 named the sole residual: *construct the witness polynomial at
`L > 1`, for `dOut` up to the Johnson radius.* This file constructs it.

## §A. First, a structural finding: `BadChallengePoly ⟺ FriProximityGapChallenges`.

`badChallengePoly_of_friProximityGap` is the CONVERSE of `friProximityGap_of_badChallengePoly`:
from a finset cover `t ⊇ good` with `#t ≤ L`, the *vanishing polynomial of the cover*
`P = ∏_{a ∈ t} (X − C a)` is nonzero (monic), has `natDegree = #t ≤ L`
(`natDegree_finsetProd_X_sub_C_eq_card`) and kills every good challenge. So the two `Prop`s are
EQUIVALENT (`badChallengePoly_iff_friProximityGap`), and the polynomial framing carries no extra
hardness: **the entire content of the BCIKS20 core is the cardinality bound on the good-challenge
set.** That is what §B–§D prove, and the witness `P` is then exhibited explicitly.

## §B. The affine-line collapse (the deployed structure).

For the deployed wrap setup (`friSetupWrapRate`: `|L| = 128`, `|L²| = 64`, `C = {a + b·ω^x}` of
dimension `2`, and `C'` = the CONSTANTS on `L²`), write `Φ y = (E f y, O f y) ∈ F²`. Then

* `Fold α f y = E f y + α · O f y`, so a challenge `α` is *good* (its fold is `dIn`-close to the
  constants) exactly when some **line** `ℓ_{α,c} = {(u,v) | u + α·v = c}` in `F²` captures
  `Φ y` for at least `a := 64 − dIn` of the fibers `y`. Write `S_α = Φ⁻¹(ℓ_{α,c_α})`.
* Distinct challenges give lines of distinct slope, so `ℓ_{α,c_α} ∩ ℓ_{γ,c_γ}` is a SINGLE point
  `(a*, b*)` of `F²`. Hence `S_α ∩ S_γ ⊆ Φ⁻¹(a*, b*)`.
* A single point `(a,b)` of `F²` is a CODEWORD `x ↦ a + b·ω^x`, and every fiber in `Φ⁻¹(a,b)`
  contributes BOTH of its two domain points to the agreement of `f` with that codeword
  (`far_fiber_card`, via `self_decomp` and the exactly-2-to-1 quotient). So `f` being `dOut`-far
  forces `2·|Φ⁻¹(a,b)| + dOut < 128`, i.e. at the Johnson radius `dOut = 112`: `|Φ⁻¹(a,b)| ≤ 7`.

This is exactly the hypothesis shape of the Fisher/packing bound the sister lane
(`FriLdtJohnsonList.lean`) used for `RSListBound`: sets of size `≥ a` with pairwise intersections
`≤ M`. §C re-proves that bound in the form needed here — for an arbitrary INDEXED FAMILY of
finsets, not just agreement sets of codewords — and §D closes the numbers.

## §C–§D. The numbers.

With `n = |L²| = 64`, `M = 7` (Johnson radius `dOut = 112`), `a = 64 − dIn`, double-counting
`T = ∑_y #{α good : y ∈ S_α}` gives `T ≥ L·a` and (Cauchy–Schwarz + Fisher)
`T² ≤ n·(T + L(L−1)·M)`, which bites exactly when `a² > n·M = 448`, i.e. `a ≥ 22`, i.e.
`dIn ≤ 42`. At `dIn = 42` it forces `L ≤ 26`:

  `wrap_badChallengePoly_johnson : BadChallengePoly friSetupWrapRate 112 42 26`
  `wrap_friProximityGap_johnson  : FriProximityGapChallenges friSetupWrapRate 112 42 26`

Both at `L = 26 > 1`, at the **Johnson radius** `dOut = 112 = ⌊(7/8)·128⌋`, and at
`dIn = 42 > 28 = dOut/4` — strictly PAST the two-point (unique-decoding) reach of
`fold_close_of_two_alpha`, which is the whole point of the BCIKS20 core. A sharper list at a
smaller `dIn` also drops out (`wrap_badChallengePoly_johnson_tight`: `dIn = 40 ⟹ L ≤ 8`).

## Non-vacuity (§E).

`fSqWrap x = ω¹²⁸^(2x)` is a concrete word that is `112`-far from the deployed code — a codeword
`a + b·t` agrees with `t²` only at roots of `t² − b·t − a`, of which there are `≤ 2`
(`fSqWrap_far`, using `pParam_injective`). So the far hypothesis of the main theorem is
SATISFIABLE and the theorem fires on real data (`wrap_witness_fires`), producing an actual
witness polynomial. The bound is not vacuously true.

## Honest scope.

The packing method caps at `dIn ≤ 42` out of `64` (relative `21/32`), NOT at the folded code's own
Johnson radius `dIn = 56` (relative `7/8`) — because `a² > n·M` fails for `a ≤ 21`. Reaching
relative-distance PRESERVATION (`δ_in = δ_out`, BCIKS20's sharp correlated-agreement statement)
needs the correlated-agreement argument, not this Fisher double-count. That precise gap is NAMED
as a Lean statement in §F (`WrapCorrelatedAgreementSharp`) — nothing is `sorry`'d and nothing is
assumed: everything *stated as a theorem here is proved*.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `axiom`, no `sorry`.
-/

namespace Dregg2.Circuit.FriProximityGapWitness

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriLdtJohnson
open Dregg2.Circuit.FriProximityGapListDecoding
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriDeployedInstance
  (omega128 omega128_ne omega128_neg friSetupWrapRate)
open Polynomial
open scoped BigOperators

/-! ## §A. `BadChallengePoly` and `FriProximityGapChallenges` are EQUIVALENT.

The forward direction is `friProximityGap_of_badChallengePoly` (already proved: the witness's roots
cover the good set, so the good set is degree-bounded). The converse constructs the witness from
the cover: the *vanishing polynomial* `∏_{a ∈ t} (X − C a)` of the covering finset is monic (hence
nonzero), of degree exactly `#t ≤ L`, and vanishes on all of `t ⊇ good`. So the BCIKS20 "witness
polynomial" carries no content beyond the list bound itself — which is what makes the packing
argument below a complete discharge, not a partial one. -/

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The witness from a cover.** A finset `t` of card `≤ L` covering the good challenges yields the
witness polynomial `P = ∏_{a ∈ t} (X − C a)`: nonzero (monic), `natDegree = #t ≤ L`, and every good
challenge is a root. The CONVERSE of `friProximityGap_of_badChallengePoly`. -/
theorem badChallengePoly_of_friProximityGap (S : FriSetup F ι κ) (dOut dIn L : ℕ)
    (h : FriProximityGapChallenges S dOut dIn L) :
    BadChallengePoly S dOut dIn L := by
  intro f hfar
  obtain ⟨t, hcard, hsub⟩ := h hfar
  refine ⟨∏ a ∈ t, (X - C a), (monic_prod_X_sub_C (fun a : F => a) t).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card t (fun a : F => a)]
    exact hcard
  · intro α hα
    have hmem : α ∈ t := hsub hα
    show (∏ a ∈ t, (X - C a)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hmem (by simp)

/-- **The two BCIKS20 framings coincide.** `BadChallengePoly S dOut dIn L ↔
FriProximityGapChallenges S dOut dIn L`. The polynomial-method packaging adds no hardness: the
whole content is the bound on the good-challenge set. -/
theorem badChallengePoly_iff_friProximityGap (S : FriSetup F ι κ) (dOut dIn L : ℕ) :
    BadChallengePoly S dOut dIn L ↔ FriProximityGapChallenges S dOut dIn L :=
  ⟨friProximityGap_of_badChallengePoly S dOut dIn L,
   badChallengePoly_of_friProximityGap S dOut dIn L⟩

/-! ## §B. The packing core for an INDEXED FAMILY of finsets.

`FriLdtJohnsonList.lean` proved the Fisher/packing bound for a finset of CODEWORDS via their
agreement sets with a fixed word. Here the family is indexed by CHALLENGES `α` (the sets
`S_α = {y | Fold α f y = c_α}`), so the same double-count is re-proved one level more generally:
an arbitrary family `S : A → Finset B` restricted to `T : Finset A`. -/

section Packing

variable {A : Type*}
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- `famDeg T S y` = how many members of the family `{S α}_{α ∈ T}` contain the point `y`
(the `d_y` of the packing double-count). -/
def famDeg (T : Finset A) (S : A → Finset B) (y : B) : ℕ :=
  (T.filter (fun α => y ∈ S α)).card

/-- **Row/column swap.** `∑_y d_y = ∑_{α ∈ T} |S α|` — the total incidence count, by point or by
family member. -/
theorem sum_famDeg (T : Finset A) (S : A → Finset B) :
    ∑ y : B, famDeg T S y = ∑ α ∈ T, (S α).card := by
  have h : ∀ α : A, (S α).card = (Finset.univ.filter (fun y : B => y ∈ S α)).card := by
    intro α; congr 1; ext y; simp
  simp_rw [h]
  unfold famDeg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **`∑_y d_y² = ∑_{α,γ ∈ T} |S α ∩ S γ|`** — expand the square into the pairwise incidence
double sum. -/
theorem sum_sq_famDeg (T : Finset A) (S : A → Finset B) :
    ∑ y : B, (famDeg T S y) ^ 2 = ∑ α ∈ T, ∑ γ ∈ T, (S α ∩ S γ).card := by
  have hpoint : ∀ y : B, (famDeg T S y) ^ 2
      = ∑ α ∈ T, ∑ γ ∈ T, (if y ∈ S α ∧ y ∈ S γ then (1 : ℕ) else 0) := by
    intro y
    unfold famDeg
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun γ _ => ?_))
    exact Dregg2.Circuit.FriLdtJohnson.ite_mul_ite_nat _ _
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  ext y
  simp [Finset.mem_inter]

/-- **The incidence lower bound.** Every member of the family has `≥ a` points, so
`T ≥ |T|·a`. -/
theorem famPacking_sum_ge (T : Finset A) (S : A → Finset B) (a : ℕ)
    (hlow : ∀ α ∈ T, a ≤ (S α).card) :
    T.card * a ≤ ∑ y : B, famDeg T S y := by
  rw [sum_famDeg]
  calc T.card * a = ∑ _α ∈ T, a := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ α ∈ T, (S α).card := Finset.sum_le_sum hlow

/-- **The Fisher double-count.** Distinct members meet in `≤ M` points, so
`∑_y d_y² ≤ T + |T|(|T|−1)·M`: the diagonal contributes `T`, each of the `|T|(|T|−1)` ordered
off-diagonal pairs at most `M`. -/
theorem famPacking_sum_sq_le [DecidableEq A] (T : Finset A) (S : A → Finset B) (M : ℕ)
    (hpair : ∀ α ∈ T, ∀ γ ∈ T, α ≠ γ → (S α ∩ S γ).card ≤ M) :
    ∑ y : B, (famDeg T S y) ^ 2
      ≤ (∑ y : B, famDeg T S y) + T.card * (T.card - 1) * M := by
  rw [sum_sq_famDeg]
  have hsplit : ∀ α ∈ T,
      ∑ γ ∈ T, (S α ∩ S γ).card
        = (S α).card + ∑ γ ∈ T.erase α, (S α ∩ S γ).card := by
    intro α hα
    rw [← Finset.add_sum_erase T _ hα]
    congr 1
    simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  gcongr ?_ + ?_
  · exact le_of_eq (sum_famDeg T S).symm
  · calc ∑ α ∈ T, ∑ γ ∈ T.erase α, (S α ∩ S γ).card
        ≤ ∑ α ∈ T, ∑ _γ ∈ T.erase α, M := by
          refine Finset.sum_le_sum (fun α hα => Finset.sum_le_sum (fun γ hγ => ?_))
          exact hpair α hα γ (Finset.mem_of_mem_erase hγ) (Finset.ne_of_mem_erase hγ).symm
      _ = ∑ α ∈ T, (T.erase α).card * M := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ _α ∈ T, (T.card - 1) * M := by
          refine Finset.sum_congr rfl (fun α hα => ?_)
          rw [Finset.card_erase_of_mem hα]
      _ = T.card * ((T.card - 1) * M) := by rw [Finset.sum_const, smul_eq_mul]
      _ = T.card * (T.card - 1) * M := by ring

/-- **Cauchy–Schwarz** on the incidence degrees: `T² ≤ |B|·∑_y d_y²`. -/
theorem famPacking_cs (T : Finset A) (S : A → Finset B) :
    (∑ y : B, famDeg T S y) ^ 2 ≤ Fintype.card B * ∑ y : B, (famDeg T S y) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset B)) (f := famDeg T S)
  simpa [Finset.card_univ] using h

end Packing

/-! ## §C. The fold geometry: a fiber contributes BOTH its domain points.

The FRI quotient `q` is exactly 2-to-1 (`rep y ≠ σ (rep y)` because their `p`-values are `±p₀` with
`p₀ ≠ 0` and `2 ≠ 0`). So a set `Y` of fibers all of whose domain points lie in some set `Ag`
forces `|Ag| ≥ 2|Y|` — the LOWER bound complementing `FriSoundness.pullback_card_le`. -/

omit [DecidableEq F] [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- **Exactly-2-to-1 pullback (lower bound).** If both domain points of every fiber in `Y` lie in
`Ag`, then `2·|Y| ≤ |Ag|`. -/
theorem two_mul_card_le_of_fiber_mem (G : FriGeom F ι κ) (Y : Finset κ) (Ag : Finset ι)
    (hmem : ∀ y ∈ Y, G.rep y ∈ Ag ∧ G.σ (G.rep y) ∈ Ag) :
    2 * Y.card ≤ Ag.card := by
  classical
  have hrep_inj : Function.Injective G.rep := by
    intro y y' hyy
    have h := G.q_rep y
    rw [hyy, G.q_rep y'] at h
    exact h.symm
  have hsrep_inj : Function.Injective (fun y => G.σ (G.rep y)) := by
    intro y y' hyy
    have h1 : G.q (G.σ (G.rep y)) = y := G.q_σ_rep y
    have h2 : G.q (G.σ (G.rep y')) = y' := G.q_σ_rep y'
    simp only at hyy
    rw [hyy, h2] at h1
    exact h1.symm
  have hdisj : Disjoint (Y.image G.rep) (Y.image (fun y => G.σ (G.rep y))) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', _, hxy⟩ := Finset.mem_image.mp hx'
    -- `hxy : G.σ (G.rep y') = G.rep y`
    have hq1 : G.q (G.rep y) = y' := by rw [← hxy]; exact G.q_σ_rep y'
    have hyy : y = y' := by rw [← G.q_rep y]; exact hq1
    subst hyy
    have hp : G.p (G.σ (G.rep y)) = G.p (G.rep y) := by rw [hxy]
    rw [G.p_σ_rep y] at hp
    have h2 : (2 : F) * G.p (G.rep y) = 0 := by linear_combination - hp
    rcases mul_eq_zero.mp h2 with h | h
    · exact G.two_ne h
    · exact G.p_rep_ne y h
  calc 2 * Y.card = Y.card + Y.card := by ring
    _ = (Y.image G.rep).card + (Y.image (fun y => G.σ (G.rep y))).card := by
        rw [Finset.card_image_of_injective _ hrep_inj,
          Finset.card_image_of_injective _ hsrep_inj]
    _ = (Y.image G.rep ∪ Y.image (fun y => G.σ (G.rep y))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ Ag.card := by
        refine Finset.card_le_card ?_
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
          exact (hmem y hy).1
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
          exact (hmem y hy).2

/-- **THE FAR-WORD FIBER BOUND (`M`).** If `f` is `dOut`-far from `C` and `x ↦ a + b·p x` is a
codeword, then the fibers on which the even/odd pair `(E f, O f)` equals the CONSTANT pair `(a, b)`
number at most `(|ι| − dOut − 1)/2`: each such fiber contributes BOTH of its domain points to the
agreement of `f` with that codeword (`self_decomp`), and far-ness caps the agreement.

This is the `M` of the packing bound, and it is where the DEPLOYED code's dimension-`2` structure
enters: a point of `F²` *is* a codeword. -/
theorem far_fiber_card (S : FriSetup F ι κ) {f : ι → F} {dOut : ℕ}
    (hfar : farN S.C dOut f) {a b : F}
    (hg : (fun x => a + b * S.geom.p x) ∈ S.C) :
    2 * (Finset.univ.filter (fun y : κ => E S.geom f y = a ∧ O S.geom f y = b)).card + dOut
      < Fintype.card ι := by
  classical
  set G := S.geom with hG
  set Y : Finset κ := Finset.univ.filter (fun y : κ => E G f y = a ∧ O G f y = b) with hY
  set Ag : Finset ι := Finset.univ.filter (fun x : ι => f x = a + b * G.p x) with hAg
  -- Both domain points of a fiber in `Y` agree with the codeword.
  have hfib : ∀ y ∈ Y, G.rep y ∈ Ag ∧ G.σ (G.rep y) ∈ Ag := by
    intro y hy
    rw [hY, Finset.mem_filter] at hy
    obtain ⟨-, hE, hO⟩ := hy
    constructor
    · rw [hAg, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hd := self_decomp G f (G.rep y)
      rw [G.q_rep y, hE, hO] at hd
      rw [hd]; ring
    · rw [hAg, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hd := self_decomp G f (G.σ (G.rep y))
      rw [G.q_σ_rep y, hE, hO] at hd
      rw [hd]; ring
  have h2 : 2 * Y.card ≤ Ag.card := two_mul_card_le_of_fiber_mem G Y Ag hfib
  -- Far-ness: the codeword `x ↦ a + b·p x` disagrees with `f` on more than `dOut` points.
  have hd : dOut < (disagree f (fun x => a + b * G.p x)).card := by
    by_contra hcon
    exact hfar ⟨fun x => a + b * G.p x, hg, Nat.not_lt.mp hcon⟩
  have hcompl : Ag = (disagree f (fun x => a + b * G.p x))ᶜ := by
    ext x
    simp [hAg, disagree]
  have hle : (disagree f (fun x => a + b * G.p x)).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (disagree f (fun x => a + b * G.p x))
  have hcc : Ag.card = Fintype.card ι - (disagree f (fun x => a + b * G.p x)).card := by
    rw [hcompl, Finset.card_compl]
  omega

/-! ## §D. The deployed wrap setup — the good-challenge list bound, and the WITNESS.

`friSetupWrapRate`: `ι = Fin 128`, `κ = Fin 64`, `C = codeC 6 ω₁₂₈` (dimension `2`),
`C' = codeC' 6` = the CONSTANTS on `Fin 64`. -/

/-- Membership in the deployed folded code is exactly "is a constant". -/
theorem mem_wrap_C' {g : Fin (2 ^ 6) → BabyBear} :
    g ∈ friSetupWrapRate.C' ↔ ∃ c : BabyBear, g = fun _ => c := Iff.rfl

/-- A point `(a, b)` of `F²` IS a deployed codeword (`x ↦ a + b·ω^x`). -/
theorem wrap_point_mem_C (a b : BabyBear) :
    (fun x => a + b * friSetupWrapRate.geom.p x) ∈ friSetupWrapRate.C := ⟨a, b, rfl⟩

/-- **The far-word fiber bound at the Johnson radius.** A `112`-far word has, for every constant
pair `(a, b)`, at most `7` fibers on which `(E f, O f) = (a, b)`: `2·|Φ⁻¹(a,b)| + 112 < 128`. -/
theorem wrap_fiber_le_seven {f : Fin (2 ^ 7) → BabyBear}
    (hfar : farN friSetupWrapRate.C 112 f) (a b : BabyBear) :
    (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        E friSetupWrapRate.geom f y = a ∧ O friSetupWrapRate.geom f y = b)).card ≤ 7 := by
  have h := far_fiber_card friSetupWrapRate hfar (wrap_point_mem_C a b)
  have hcard : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
  rw [hcard] at h
  omega

/-- **The good-challenge list bound — the BCIKS20 core, at the Johnson radius, for `L > 1`.**

A word `112`-far from the deployed rate-`1/64` code has at most `26` folding challenges whose fold
is `42`-close to the folded (constant) code.

*Proof.* Each good `α` picks a constant `c_α` and the agreement set
`S_α = {y | E f y + α·O f y = c_α}` with `|S_α| ≥ 64 − 42 = 22`. For `α ≠ γ`, a common point `y`
satisfies both `E y + α·O y = c_α` and `E y + γ·O y = c_γ`, which SOLVE (the `2×2` Vandermonde in
`α ≠ γ`) to the single pair `(a*, b*)` — so `S_α ∩ S_γ ⊆ Φ⁻¹(a*,b*)`, of size `≤ 7`
(`wrap_fiber_le_seven`). Fisher + Cauchy–Schwarz on `n = 64` points then forces `L ≤ 26`: the
Johnson condition `a² = 484 > 448 = n·M` is exactly what makes the quadratic bite. -/
theorem wrap_good_challenge_card_le {f : Fin (2 ^ 7) → BabyBear}
    (hfar : farN friSetupWrapRate.C 112 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 42 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ 26 := by
  classical
  set G := friSetupWrapRate.geom with hG
  -- Each good challenge has a constant witness `c_α` with `≤ 42` disagreements.
  have hex : ∀ α ∈ Good, ∃ c : BabyBear,
      (disagree (Fold G α f) (fun _ => c)).card ≤ 42 := by
    intro α hα
    obtain ⟨g, hgC, hgcard⟩ := hGood α hα
    obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
    exact ⟨c, hgcard⟩
  choose! cw hcw using hex
  -- The agreement sets of the family.
  set Sfun : BabyBear → Finset (Fin (2 ^ 6)) :=
    fun α => Finset.univ.filter (fun y => Fold G α f y = cw α) with hSfun
  -- (i) Each has `≥ 22` points.
  have hlow : ∀ α ∈ Good, 22 ≤ (Sfun α).card := by
    intro α hα
    have hcompl : Sfun α = (disagree (Fold G α f) (fun _ => cw α))ᶜ := by
      ext y
      simp [hSfun, disagree]
    have hcc : (Sfun α).card
        = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => cw α)).card := by
      rw [hcompl, Finset.card_compl]
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    have := hcw α hα
    omega
  -- (ii) Distinct good challenges share `≤ 7` points: their lines meet in ONE point of `F²`.
  have hpair : ∀ α ∈ Good, ∀ γ ∈ Good, α ≠ γ → (Sfun α ∩ Sfun γ).card ≤ 7 := by
    intro α hα γ hγ hne
    have hsub : α - γ ≠ 0 := sub_ne_zero.mpr hne
    refine le_trans (Finset.card_le_card ?_)
      (wrap_fiber_le_seven hfar (cw α - α * ((cw α - cw γ) / (α - γ)))
        ((cw α - cw γ) / (α - γ)))
    intro y hy
    rw [Finset.mem_inter, hSfun] at hy
    obtain ⟨hyα, hyγ⟩ := hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyα hyγ
    -- `hyα : E f y + α * O f y = cw α`, `hyγ : E f y + γ * O f y = cw γ`
    have e1 : E G f y + α * O G f y = cw α := hyα
    have e2 : E G f y + γ * O G f y = cw γ := hyγ
    have hO : O G f y = (cw α - cw γ) / (α - γ) := by
      rw [eq_div_iff hsub]
      linear_combination e1 - e2
    have hE : E G f y = cw α - α * ((cw α - cw γ) / (α - γ)) := by
      rw [← hO]
      linear_combination e1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hE, hO⟩
  -- (iii) The packing bound.
  have hge := famPacking_sum_ge Good Sfun 22 hlow
  have hsq := famPacking_sum_sq_le Good Sfun 7 hpair
  have hcs := famPacking_cs Good Sfun
  have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [hn] at hcs
  set T : ℕ := ∑ y : Fin (2 ^ 6), famDeg Good Sfun y with hT
  set L : ℕ := Good.card with hL
  have hchain : T ^ 2 ≤ 64 * (T + L * (L - 1) * 7) := le_trans hcs (by gcongr)
  by_contra hcon
  rw [not_le] at hcon              -- `26 < L`
  have h27 : 27 ≤ L := hcon
  have hTge : 22 * L ≤ T := by rw [Nat.mul_comm]; exact hge
  clear_value T L
  clear hT hL hge hsq hcs hcon hlow hpair hSfun hcw hn
  -- Cast to ℝ and close: `T ≥ 22L`, `T² ≤ 64T + 448·L(L−1)`, `L ≥ 27` is contradictory.
  have hL1 : 1 ≤ L := by omega
  have hTR : (22 : ℝ) * L ≤ T := by exact_mod_cast hTge
  have h27R : (27 : ℝ) ≤ L := by exact_mod_cast h27
  have hchainR : (T : ℝ) ^ 2 ≤ 64 * ((T : ℝ) + (L : ℝ) * ((L : ℝ) - 1) * 7) := by
    have hcast : ((T ^ 2 : ℕ) : ℝ) ≤ ((64 * (T + L * (L - 1) * 7) : ℕ) : ℝ) := by
      exact_mod_cast hchain
    push_cast [Nat.cast_sub hL1] at hcast
    linarith
  clear hTge h27 hchain hL1
  -- `T ≥ 22·27 = 594 ≥ 64`, so both factors of `(T − 22L)(T + 22L − 64)` are `≥ 0`.
  have hT64 : (64 : ℝ) ≤ T := by nlinarith
  have hp1 : (0 : ℝ) ≤ ((T : ℝ) - 22 * L) * ((T : ℝ) + 22 * L - 64) :=
    mul_nonneg (by linarith) (by linarith)
  have hexp : ((T : ℝ) - 22 * L) * ((T : ℝ) + 22 * L - 64)
      = (T : ℝ) ^ 2 - 64 * T - 484 * (L : ℝ) ^ 2 + 1408 * L := by ring
  rw [hexp] at hp1
  -- Cauchy–Schwarz side, expanded.
  have hB : (T : ℝ) ^ 2 ≤ 64 * T + 448 * (L : ℝ) ^ 2 - 448 * L := by nlinarith [hchainR]
  -- `484L² − 1408L ≤ T² − 64T ≤ 448L² − 448L` ⟹ `36L² ≤ 960L` ⟹ `36L ≤ 960`, but `L ≥ 27`.
  have hC : 36 * (L : ℝ) ^ 2 ≤ 960 * L := by linarith [hp1, hB]
  nlinarith [hC, h27R]

/-- **THE WITNESS — `BadChallengePoly` at `L = 26 > 1`, at the JOHNSON radius `dOut = 112`.**

For every word `f` that is `112`-far from the deployed rate-`1/64` code, the polynomial

  `P_f = ∏_{α ∈ Good f} (X − C α)`,  `Good f = {α | Fold α f is 42-close to the constants}`,

is nonzero, has `natDegree = |Good f| ≤ 26`, and vanishes on every good challenge. The degree bound
IS `wrap_good_challenge_card_le` (the Fisher/packing collapse). This is the BCIKS20 correlated-
agreement witness, constructed — the residual §4 of `FriProximityGapListDecoding.lean`.

Note `dIn = 42 > 28 = dOut/4`: strictly past the reach of the two-point (unique-decoding)
`fold_close_of_two_alpha`, which is exactly the content the `L > 1` regime buys. -/
theorem wrap_badChallengePoly_johnson :
    BadChallengePoly friSetupWrapRate 112 42 26 := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 42 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ 26 :=
    wrap_good_challenge_card_le hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- **`FriProximityGapChallenges` at `L = 26 > 1`, at the Johnson radius** — the payoff, routed
through the framework's own reduction `friProximityGap_of_badChallengePoly`. This is the statement
`FriLdtJohnson.lean` §3 named as the remaining BCIKS20 residual (ii), now DISCHARGED past unique
decoding. -/
theorem wrap_friProximityGap_johnson :
    FriProximityGapChallenges friSetupWrapRate 112 42 26 :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 112 42 26 wrap_badChallengePoly_johnson

/-- **A sharper list at a smaller inner radius.** At `dIn = 40` (`a = 24`, `a² = 576 > 448`) the
same packing forces `L ≤ 8`. Still past the two-point reach (`40 > 28`). -/
theorem wrap_good_challenge_card_le_tight {f : Fin (2 ^ 7) → BabyBear}
    (hfar : farN friSetupWrapRate.C 112 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 40 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ 8 := by
  classical
  set G := friSetupWrapRate.geom with hG
  have hex : ∀ α ∈ Good, ∃ c : BabyBear,
      (disagree (Fold G α f) (fun _ => c)).card ≤ 40 := by
    intro α hα
    obtain ⟨g, hgC, hgcard⟩ := hGood α hα
    obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
    exact ⟨c, hgcard⟩
  choose! cw hcw using hex
  set Sfun : BabyBear → Finset (Fin (2 ^ 6)) :=
    fun α => Finset.univ.filter (fun y => Fold G α f y = cw α) with hSfun
  have hlow : ∀ α ∈ Good, 24 ≤ (Sfun α).card := by
    intro α hα
    have hcompl : Sfun α = (disagree (Fold G α f) (fun _ => cw α))ᶜ := by
      ext y
      simp [hSfun, disagree]
    have hcc : (Sfun α).card
        = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => cw α)).card := by
      rw [hcompl, Finset.card_compl]
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    have := hcw α hα
    omega
  have hpair : ∀ α ∈ Good, ∀ γ ∈ Good, α ≠ γ → (Sfun α ∩ Sfun γ).card ≤ 7 := by
    intro α hα γ hγ hne
    have hsub : α - γ ≠ 0 := sub_ne_zero.mpr hne
    refine le_trans (Finset.card_le_card ?_)
      (wrap_fiber_le_seven hfar (cw α - α * ((cw α - cw γ) / (α - γ)))
        ((cw α - cw γ) / (α - γ)))
    intro y hy
    rw [Finset.mem_inter, hSfun] at hy
    obtain ⟨hyα, hyγ⟩ := hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyα hyγ
    have e1 : E G f y + α * O G f y = cw α := hyα
    have e2 : E G f y + γ * O G f y = cw γ := hyγ
    have hO : O G f y = (cw α - cw γ) / (α - γ) := by
      rw [eq_div_iff hsub]
      linear_combination e1 - e2
    have hE : E G f y = cw α - α * ((cw α - cw γ) / (α - γ)) := by
      rw [← hO]
      linear_combination e1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hE, hO⟩
  have hge := famPacking_sum_ge Good Sfun 24 hlow
  have hsq := famPacking_sum_sq_le Good Sfun 7 hpair
  have hcs := famPacking_cs Good Sfun
  have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [hn] at hcs
  set T : ℕ := ∑ y : Fin (2 ^ 6), famDeg Good Sfun y with hT
  set L : ℕ := Good.card with hL
  have hchain : T ^ 2 ≤ 64 * (T + L * (L - 1) * 7) := le_trans hcs (by gcongr)
  by_contra hcon
  rw [not_le] at hcon
  have h9 : 9 ≤ L := hcon
  have hTge : 24 * L ≤ T := by rw [Nat.mul_comm]; exact hge
  clear_value T L
  clear hT hL hge hsq hcs hcon hlow hpair hSfun hcw hn
  have hL1 : 1 ≤ L := by omega
  have hTR : (24 : ℝ) * L ≤ T := by exact_mod_cast hTge
  have h9R : (9 : ℝ) ≤ L := by exact_mod_cast h9
  have hchainR : (T : ℝ) ^ 2 ≤ 64 * ((T : ℝ) + (L : ℝ) * ((L : ℝ) - 1) * 7) := by
    have hcast : ((T ^ 2 : ℕ) : ℝ) ≤ ((64 * (T + L * (L - 1) * 7) : ℕ) : ℝ) := by
      exact_mod_cast hchain
    push_cast [Nat.cast_sub hL1] at hcast
    linarith
  clear hTge h9 hchain hL1
  have hT64 : (64 : ℝ) ≤ T := by nlinarith
  have hp1 : (0 : ℝ) ≤ ((T : ℝ) - 24 * L) * ((T : ℝ) + 24 * L - 64) :=
    mul_nonneg (by linarith) (by linarith)
  have hexp : ((T : ℝ) - 24 * L) * ((T : ℝ) + 24 * L - 64)
      = (T : ℝ) ^ 2 - 64 * T - 576 * (L : ℝ) ^ 2 + 1536 * L := by ring
  rw [hexp] at hp1
  have hB : (T : ℝ) ^ 2 ≤ 64 * T + 448 * (L : ℝ) ^ 2 - 448 * L := by nlinarith [hchainR]
  -- `576L² − 1536L ≤ 448L² − 448L` ⟹ `128L² ≤ 1088L` ⟹ `128L ≤ 1088` ⟹ `L ≤ 8.5`.
  have hC : 128 * (L : ℝ) ^ 2 ≤ 1088 * L := by linarith [hp1, hB]
  nlinarith [hC, h9R]

/-- **The tighter witness**: `BadChallengePoly friSetupWrapRate 112 40 8` — degree `≤ 8`. -/
theorem wrap_badChallengePoly_johnson_tight :
    BadChallengePoly friSetupWrapRate 112 40 8 := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 40 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ 8 :=
    wrap_good_challenge_card_le_tight hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- The tighter proximity gap: `FriProximityGapChallenges friSetupWrapRate 112 40 8`. -/
theorem wrap_friProximityGap_johnson_tight :
    FriProximityGapChallenges friSetupWrapRate 112 40 8 :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 112 40 8 wrap_badChallengePoly_johnson_tight

/-! ## §E. NON-VACUITY — a concrete `112`-far word, and the witness FIRING on it.

`fSqWrap x = ω^(2x) = (ω^x)²`. A codeword `a + b·ω^x` agrees with it exactly at the roots
`t = ω^x` of `t² − b·t − a`, of which a field admits `≤ 2`. So `fSqWrap` agrees with EVERY codeword
on `≤ 2` of the `128` points — it is `125`-far, hence `112`-far. The far hypothesis of the main
theorem is therefore satisfiable and the theorem is not vacuously true. -/

/-- **Far-ness from a uniform agreement cap.** A word agreeing with EVERY codeword on `≤ k` points
is `d`-far whenever `d + k < |ι|`. Phrased through `(disagree f g)ᶜ` so the agreement set and the
disagreement set are literally complementary — one term, one `DecidableEq` instance. -/
theorem farN_of_agree_le {C : Submodule F (ι → F)} {f : ι → F} {d k : ℕ}
    (hk : d + k < Fintype.card ι)
    (h : ∀ g ∈ C, ((disagree f g)ᶜ).card ≤ k) :
    farN C d f := by
  rintro ⟨g, hg, hcard⟩
  have hA := h g hg
  rw [Finset.card_compl] at hA
  have hle : (disagree f g).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (disagree f g)
  omega

/-- The concrete far word `x ↦ (ω₁₂₈^x)²` on the deployed `128`-point domain. -/
noncomputable def fSqWrap : Fin (2 ^ 7) → BabyBear := fun x => (pParam 6 omega128 x) ^ 2

/-- **`fSqWrap` agrees with every deployed codeword on at most `2` points.** Three agreement points
give three distinct roots `t = ω^x` (`pParam_injective`) of the quadratic `t² − b·t − a`; pairwise
subtraction forces `t₁ + t₂ = b = t₁ + t₃`, hence `t₂ = t₃` — contradiction. -/
theorem fSqWrap_agree_le_two (g : Fin (2 ^ 7) → BabyBear) (hg : g ∈ friSetupWrapRate.C) :
    ((disagree fSqWrap g)ᶜ).card ≤ 2 := by
  obtain ⟨a, b, rfl⟩ := hg
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hcon
  simp only [Finset.mem_compl, mem_disagree, not_not, fSqWrap] at hx₁ hx₂ hx₃
  -- `hxᵢ : (ω^xᵢ)² = a + b · ω^xᵢ`
  set t₁ := pParam 6 omega128 x₁ with ht₁
  set t₂ := pParam 6 omega128 x₂ with ht₂
  set t₃ := pParam 6 omega128 x₃ with ht₃
  have hne12 : t₁ ≠ t₂ := fun h => h12 (pParam_injective h)
  have hne13 : t₁ ≠ t₃ := fun h => h13 (pParam_injective h)
  have hne23 : t₂ ≠ t₃ := fun h => h23 (pParam_injective h)
  have e12 : (t₁ - t₂) * (t₁ + t₂ - b) = 0 := by linear_combination hx₁ - hx₂
  have e13 : (t₁ - t₃) * (t₁ + t₃ - b) = 0 := by linear_combination hx₁ - hx₃
  have s12 : t₁ + t₂ - b = 0 := by
    rcases mul_eq_zero.mp e12 with h | h
    · exact absurd (sub_eq_zero.mp h) hne12
    · exact h
  have s13 : t₁ + t₃ - b = 0 := by
    rcases mul_eq_zero.mp e13 with h | h
    · exact absurd (sub_eq_zero.mp h) hne13
    · exact h
  exact hne23 (by linear_combination s12 - s13)

/-- **`fSqWrap` is `112`-FAR from the deployed code** (indeed `125`-far): every codeword agrees on
`≤ 2` of `128` points, so disagrees on `≥ 126 > 112`. The far hypothesis of
`wrap_badChallengePoly_johnson` is SATISFIABLE. -/
theorem fSqWrap_far : farN friSetupWrapRate.C 112 fSqWrap := by
  refine farN_of_agree_le (k := 2) ?_ fSqWrap_agree_le_two
  have hn : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
  rw [hn]
  norm_num

/-- **THE WITNESS FIRES.** On the concrete `112`-far `fSqWrap`, the theorem hands back an actual
nonzero polynomial of degree `≤ 26` whose roots contain every good folding challenge. Non-vacuous:
the hypothesis holds, so the conclusion is real content. -/
theorem wrap_witness_fires :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ 26 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 42 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  wrap_badChallengePoly_johnson fSqWrap_far

/-- **The proximity gap FIRES on `fSqWrap`**: at most `26` folding challenges fold it `42`-close to
the constants. -/
theorem wrap_proximityGap_fires :
    ∃ s : Finset BabyBear, s.card ≤ 26 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 42 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ ↑s :=
  wrap_friProximityGap_johnson fSqWrap_far

/-! ## §F. The remaining sharpening, NAMED (not assumed, not `sorry`'d).

Everything above is proved. What the Fisher/packing method does NOT reach is BCIKS20's sharp
*correlated agreement*: relative-distance PRESERVATION, `δ_in = δ_out`, i.e. `dIn = 56` (relative
`7/8` on the `64`-point folded domain) rather than the `dIn ≤ 42` (relative `21/32`) this method
caps at. The obstruction is exact and arithmetic, not hand-wavy: the packing quadratic bites only
when `a² > n·M`, i.e. `(64 − dIn)² > 64·7 = 448`, which FAILS for `dIn ≥ 43`.

The sharp statement is a `Prop` in the SAME `BadChallengePoly` vocabulary — so any proof of it
plugs straight into `friProximityGap_of_badChallengePoly` with no new interface:

  `def WrapCorrelatedAgreementSharp (L : ℕ) : Prop :=`
  `  BadChallengePoly friSetupWrapRate 112 56 L`

It is NOT used as a hypothesis anywhere in this tree, and nothing below depends on it: the deployed
chain consumes `wrap_friProximityGap_johnson` (`dIn = 42`, `L = 26`), which is a THEOREM. -/

/-- The named sharpening: the proximity gap at RELATIVE-distance preservation (`dIn = 56 = (7/8)·64`
against `dOut = 112 = (7/8)·128`). This is BCIKS20's correlated-agreement statement at the deployed
wrap parameters. It is stated here so the residual is a Lean `Prop`, not prose — and it is NOT
assumed by anything: the results above stand without it. -/
def WrapCorrelatedAgreementSharp (L : ℕ) : Prop :=
  BadChallengePoly friSetupWrapRate 112 56 L

/-- The sharp statement is a genuine STRENGTHENING of what is proved: `dIn = 56 > 42`, and closeness
at a smaller radius implies closeness at a larger one, so the good-challenge set at `dIn = 56`
CONTAINS the one at `dIn = 42`. (This certifies the residual is not a restatement.) -/
theorem sharp_good_set_contains {f : Fin (2 ^ 7) → BabyBear} :
    {α : BabyBear | closeN friSetupWrapRate.C' 42 (Fold friSetupWrapRate.geom α f)}
      ⊆ {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)} := by
  rintro α ⟨g, hg, hcard⟩
  exact ⟨g, hg, le_trans hcard (by norm_num)⟩

/-! ## §G. Axiom hygiene. -/

#assert_axioms badChallengePoly_of_friProximityGap
#assert_axioms badChallengePoly_iff_friProximityGap
#assert_axioms sum_famDeg
#assert_axioms sum_sq_famDeg
#assert_axioms famPacking_sum_ge
#assert_axioms famPacking_sum_sq_le
#assert_axioms famPacking_cs
#assert_axioms two_mul_card_le_of_fiber_mem
#assert_axioms far_fiber_card
#assert_axioms wrap_fiber_le_seven
#assert_axioms wrap_good_challenge_card_le
#assert_axioms wrap_badChallengePoly_johnson
#assert_axioms wrap_friProximityGap_johnson
#assert_axioms wrap_good_challenge_card_le_tight
#assert_axioms wrap_badChallengePoly_johnson_tight
#assert_axioms wrap_friProximityGap_johnson_tight
#assert_axioms farN_of_agree_le
#assert_axioms fSqWrap_agree_le_two
#assert_axioms fSqWrap_far
#assert_axioms wrap_witness_fires
#assert_axioms wrap_proximityGap_fires
#assert_axioms sharp_good_set_contains

end Dregg2.Circuit.FriProximityGapWitness
