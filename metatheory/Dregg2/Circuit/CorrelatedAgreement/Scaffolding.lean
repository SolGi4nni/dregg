/-
# Dregg2.Circuit.CorrelatedAgreement.Scaffolding — rung L0 of the UD-regime correlated agreement

Rung L0 of the DAG in `docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md` §6.
This is Lean-authored proof over `Polynomial`/`Finset` (there is no Rust AIR here and there
must not be): the actual RS code object, generic in the field `F` and the parameters,
instantiated at the deployed (n = 2²⁴, k = 2²¹, r = 7340028) only at the end.

- L0.1 `RScode pt k : Submodule F (ι → F)` — evaluations on `pt` of degree-<k polynomials
  (the image of `Polynomial.degreeLT F k` under the evaluation linear map `evalOn pt`).
- L0.2 `closeN V r f` — some `v ∈ V` within absolute Hamming distance `r` of `f`
  (Mathlib `hammingDist`).
- L0.3 `interleavedClose C u e` — Δ([u_j], C^m) ≤ e: a COMMON agreement set `S`,
  `|S| ≥ n − e`, with `u j = g j` on `S` for all `j`, each `g j ∈ C`; proven equivalent
  to the full-simultaneous-agreement-filter form the target Props use.
- L0.4 RS minimum distance ≥ n − k + 1 from `Polynomial.card_roots'`, and UNIQUE DECODING
  (`rs_unique_decoding`, the load-bearing lemma): a radius-r ball with 2r + k ≤ n contains
  at most one codeword.
- The doc-§4 target Props `CorrelatedAgreementPairUD` / `CorrelatedAgreementCurveUD`
  (STATEMENTS ONLY at this rung — they are the L5/L6 goals, nothing here claims them).

Non-vacuity teeth: a concrete RS(4,1)/ZMod 5 instance on which `rs_unique_decoding` FIRES
(the radius-1 ball around ![2,2,2,3] pins any codeword to the constant-2 codeword, and that
ball is inhabited), a NONZERO codeword of `RScode`, `#guard`s that the distances compute and
that the min-distance conclusion is TIGHT, and the deployed-parameter arithmetic
(2·7340028 + 2²¹ = 2²⁴ − 8 ≤ 2²⁴, so the deployed radius sits strictly inside the UD regime:
`deployed_unique_decoding`).
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Dregg2.Tactics

namespace Dregg2.Circuit.CorrelatedAgreement

open Polynomial

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## L0.1 — the Reed–Solomon code as a `Submodule` -/

/-- Pointwise evaluation of a polynomial on the domain `pt : ι → F`, as an `F`-linear map. -/
noncomputable def evalOn (pt : ι → F) : F[X] →ₗ[F] (ι → F) :=
  LinearMap.pi fun i => Polynomial.leval (pt i)

@[simp] theorem evalOn_apply (pt : ι → F) (p : F[X]) (i : ι) :
    evalOn pt p i = p.eval (pt i) := rfl

/-- L0.1: the Reed–Solomon code `RS[F, pt, k]` — evaluations on the domain `pt` of the
polynomials of degree < k. A `Submodule` for free, as the image of `Polynomial.degreeLT`. -/
noncomputable def RScode (pt : ι → F) (k : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F k).map (evalOn pt)

theorem mem_RScode {pt : ι → F} {k : ℕ} {f : ι → F} :
    f ∈ RScode pt k ↔ ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ i, f i = p.eval (pt i) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, Polynomial.mem_degreeLT.mp hp, fun i => rfl⟩
  · rintro ⟨p, hp, hf⟩
    exact ⟨p, Polynomial.mem_degreeLT.mpr hp, funext fun i => (hf i).symm⟩

/-! ## L0.2 — closeness via Mathlib `hammingDist` -/

/-- L0.2: `closeN V r f` — some element of `V` lies within (ABSOLUTE) Hamming distance `r`
of `f`. This is the `Δ(f, V) ≤ r` of the papers, in absolute (not relative) radius. -/
def closeN (V : Set (ι → F)) (r : ℕ) (f : ι → F) : Prop :=
  ∃ v ∈ V, hammingDist f v ≤ r

theorem closeN_mono {V : Set (ι → F)} {r r' : ℕ} (h : r ≤ r') {f : ι → F} :
    closeN V r f → closeN V r' f :=
  fun ⟨v, hv, hd⟩ => ⟨v, hv, hd.trans h⟩

theorem closeN_of_mem {V : Set (ι → F)} {f : ι → F} (hf : f ∈ V) (r : ℕ) : closeN V r f :=
  ⟨f, hf, by simp⟩

/-! ## L0.3 — the interleaved code `C^m` and its distance Δ -/

/-- L0.3: `interleavedClose C u e` — `Δ([u_0,…,u_{m−1}], C^m) ≤ e`: there is ONE common
agreement set `S` with `|S| ≥ n − e` on which EVERY row `u j` agrees with a codeword `g j ∈ C`
(simultaneous agreement — the whole content of "interleaved" vs row-by-row closeness). -/
def interleavedClose (C : Set (ι → F)) {m : ℕ} (u : Fin m → ι → F) (e : ℕ) : Prop :=
  ∃ g : Fin m → ι → F, (∀ j, g j ∈ C) ∧
    ∃ S : Finset ι, Fintype.card ι - e ≤ S.card ∧ ∀ j : Fin m, ∀ x ∈ S, u j x = g j x

/-- The common-set form of Δ equals the cardinality bound on the FULL simultaneous
agreement set — the shape the §4 target Props use. -/
theorem interleavedClose_iff_filter (C : Set (ι → F)) {m : ℕ} (u : Fin m → ι → F) (e : ℕ) :
    interleavedClose C u e ↔
      ∃ g : Fin m → ι → F, (∀ j, g j ∈ C) ∧
        Fintype.card ι - e ≤ (Finset.univ.filter fun x => ∀ j, u j x = g j x).card := by
  constructor
  · rintro ⟨g, hg, S, hS, hagree⟩
    refine ⟨g, hg, le_trans hS (Finset.card_le_card ?_)⟩
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun j => hagree j x hx
  · rintro ⟨g, hg, hcard⟩
    exact ⟨g, hg, _, hcard, fun j x hx => (Finset.mem_filter.mp hx).2 j⟩

/-- The pair (m = 2) instance of `interleavedClose`, in the exact `∃ gu ∃ gv` shape of the
target Prop `CorrelatedAgreementPairUD`'s conclusion. -/
theorem interleavedClose_pair_iff (C : Set (ι → F)) (u v : ι → F) (e : ℕ) :
    interleavedClose C ![u, v] e ↔
      ∃ gu ∈ C, ∃ gv ∈ C,
        Fintype.card ι - e ≤ (Finset.univ.filter fun x => u x = gu x ∧ v x = gv x).card := by
  rw [interleavedClose_iff_filter]
  constructor
  · rintro ⟨g, hg, hcard⟩
    refine ⟨g 0, hg 0, g 1, hg 1, le_trans hcard (Finset.card_le_card ?_)⟩
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨by simpa using hx 0, by simpa using hx 1⟩
  · rintro ⟨gu, hgu, gv, hgv, hcard⟩
    refine ⟨![gu, gv], ?_, le_trans hcard (Finset.card_le_card ?_)⟩
    · intro j; fin_cases j
      · simpa using hgu
      · simpa using hgv
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro j; fin_cases j
      · simpa using hx.1
      · simpa using hx.2

/-! ## L0.4 — RS minimum distance and UNIQUE DECODING (the load-bearing lemma) -/

/-- Two distinct degree-<k polynomials agree on FEWER than k points of an injective domain
— `Polynomial.card_roots'` on their difference. The counting engine under L0.4. -/
theorem card_agreeSet_lt {pt : ι → F} (hpt : Function.Injective pt) {k : ℕ}
    {p q : F[X]} (hp : p.degree < (k : WithBot ℕ)) (hq : q.degree < (k : WithBot ℕ))
    (hne : p ≠ q) :
    (Finset.univ.filter fun i => p.eval (pt i) = q.eval (pt i)).card < k := by
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p - q).degree < (k : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le p q) (max_lt hp hq)
  have hnat : (p - q).natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hd0).mpr hdeg
  have himg : (Finset.univ.filter fun i => p.eval (pt i) = q.eval (pt i)).image pt
      ⊆ (p - q).roots.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hd0]
    simp [Polynomial.IsRoot, hi]
  calc (Finset.univ.filter fun i => p.eval (pt i) = q.eval (pt i)).card
      = ((Finset.univ.filter fun i => p.eval (pt i) = q.eval (pt i)).image pt).card :=
        (Finset.card_image_of_injective _ hpt).symm
    _ ≤ (p - q).roots.toFinset.card := Finset.card_le_card himg
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ < k := hnat

/-- `hammingDist` IS the cardinality of the disagreement filter (definitional bridge). -/
theorem hammingDist_eq_card_filter (f g : ι → F) :
    hammingDist f g = (Finset.univ.filter fun i => f i ≠ g i).card := rfl

/-- L0.4a: RS MINIMUM DISTANCE — distinct codewords of `RScode pt k` (injective `pt`) are at
Hamming distance ≥ n − k + 1 (the MDS bound), from `Polynomial.card_roots'`. -/
theorem rs_min_distance {pt : ι → F} (hpt : Function.Injective pt) {k : ℕ}
    {f g : ι → F} (hf : f ∈ RScode pt k) (hg : g ∈ RScode pt k) (hne : f ≠ g) :
    Fintype.card ι - k + 1 ≤ hammingDist f g := by
  obtain ⟨p, hp, hfp⟩ := mem_RScode.mp hf
  obtain ⟨q, hq, hgq⟩ := mem_RScode.mp hg
  have hpq : p ≠ q := by
    rintro rfl
    exact hne (funext fun i => (hfp i).trans (hgq i).symm)
  have hagree := card_agreeSet_lt hpt hp hq hpq
  have hfilter : (Finset.univ.filter fun i => f i = g i)
      = (Finset.univ.filter fun i => p.eval (pt i) = q.eval (pt i)) :=
    Finset.filter_congr fun i _ => by rw [hfp i, hgq i]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => f i = g i)
  rw [Finset.card_univ] at hsplit
  have hdist : hammingDist f g = (Finset.univ.filter fun i => ¬ (f i = g i)).card :=
    hammingDist_eq_card_filter f g
  have hpos : hammingDist f g ≠ 0 := hammingDist_ne_zero.mpr hne
  rw [hfilter] at hsplit
  omega

/-- L0.4b — UNIQUE DECODING, the load-bearing lemma of rung L0: when `2r + k ≤ n`
(equivalently `r < d/2` for the MDS distance `d = n − k + 1`), any two codewords within
Hamming distance `r` of a common word coincide — the radius-`r` ball around ANY word
contains AT MOST ONE codeword. Triangle inequality + `rs_min_distance`. -/
theorem rs_unique_decoding {pt : ι → F} (hpt : Function.Injective pt) {k r : ℕ}
    (hkr : 2 * r + k ≤ Fintype.card ι)
    {w f g : ι → F} (hf : f ∈ RScode pt k) (hg : g ∈ RScode pt k)
    (hwf : hammingDist w f ≤ r) (hwg : hammingDist w g ≤ r) : f = g := by
  by_contra hne
  have hmd := rs_min_distance hpt hf hg hne
  have htri : hammingDist f g ≤ hammingDist w f + hammingDist w g :=
    hammingDist_triangle_left f g w
  omega

/-- L0.4b, ball form: the set of codewords in the radius-`r` ball is a subsingleton. -/
theorem rs_ball_subsingleton {pt : ι → F} (hpt : Function.Injective pt) {k r : ℕ}
    (hkr : 2 * r + k ≤ Fintype.card ι) (w : ι → F) :
    {f | f ∈ RScode pt k ∧ hammingDist w f ≤ r}.Subsingleton :=
  fun _ hf _ hg => rs_unique_decoding hpt hkr hf.1 hg.1 hf.2 hg.2

/-! ## The §4 target Props — the L5/L6 GOALS (statements only at rung L0)

Generic in `(n, V, r)`; the deployed instantiation (n = 2²⁴, k = 2²¹, r = 7340028) is below.
NOTHING at this rung claims these Props — they are what rungs L1–L6 must prove. -/

/-- Doc §4, line version, generic parameters: if `u + α·v` is `r`-close to `V` for more than
`r + 1` values of `α`, then `u` and `v` are SIMULTANEOUSLY `r`-close to `V` (common
agreement set of size ≥ n − r). -/
def CorrelatedAgreementPairUDParam (F : Type*) [Field F] [DecidableEq F]
    (n : ℕ) (V : Set (Fin n → F)) (r : ℕ) : Prop :=
  ∀ (u v : Fin n → F) (Good : Finset F),
    (∀ α ∈ Good, closeN V r (fun x => u x + α * v x)) →
    r + 1 < Good.card →
    ∃ gu ∈ V, ∃ gv ∈ V,
      n - r ≤ (Finset.univ.filter fun x => u x = gu x ∧ v x = gv x).card

/-- Doc §4, m-term power-curve version, generic parameters: threshold `(m − 1)·(r + 1)`. -/
def CorrelatedAgreementCurveUDParam (F : Type*) [Field F] [DecidableEq F]
    (n : ℕ) (V : Set (Fin n → F)) (r : ℕ) (m : ℕ) : Prop :=
  ∀ (u : Fin m → Fin n → F) (Good : Finset F),
    (∀ α ∈ Good, closeN V r (fun x => ∑ j : Fin m, α ^ (j : ℕ) * u j x)) →
    (m - 1) * (r + 1) < Good.card →
    ∃ g : Fin m → Fin n → F, (∀ j, g j ∈ V) ∧
      n - r ≤ (Finset.univ.filter fun x => ∀ j, u j x = g j x).card

/-- DEPLOYED instantiation (doc §4 verbatim): V = RS of degree < 2²¹ on a 2²⁴-point domain
(rate ρ = 1/8), decoding radius r = 7340028 = e* − 4 (the intrinsic Θ(1/n) shave below
δ_code/2; e* = (n−k)/2 = 7340032). -/
def CorrelatedAgreementPairUD (pt : Fin (2 ^ 24) → F) : Prop :=
  CorrelatedAgreementPairUDParam F (2 ^ 24)
    (RScode pt (2 ^ 21) : Set (Fin (2 ^ 24) → F)) 7340028

/-- DEPLOYED m-term power-curve instantiation (doc §4 verbatim): threshold
`(m − 1) · 7340029 < |Good|`. -/
def CorrelatedAgreementCurveUD (pt : Fin (2 ^ 24) → F) (m : ℕ) : Prop :=
  CorrelatedAgreementCurveUDParam F (2 ^ 24)
    (RScode pt (2 ^ 21) : Set (Fin (2 ^ 24) → F)) 7340028 m

/-- The deployed Prop unfolds to EXACTLY the doc-§4 text (literal thresholds and all) —
certifies the `Param` indirection changed nothing. -/
theorem CorrelatedAgreementPairUD_def (pt : Fin (2 ^ 24) → F) :
    CorrelatedAgreementPairUD pt ↔
      ∀ (u v : Fin (2 ^ 24) → F) (Good : Finset F),
        (∀ α ∈ Good, closeN (RScode pt (2 ^ 21) : Set (Fin (2 ^ 24) → F)) 7340028
          (fun x => u x + α * v x)) →
        7340029 < Good.card →
        ∃ gu ∈ RScode pt (2 ^ 21), ∃ gv ∈ RScode pt (2 ^ 21),
          2 ^ 24 - 7340028 ≤ (Finset.univ.filter fun x => u x = gu x ∧ v x = gv x).card :=
  Iff.rfl

/-- The deployed curve Prop unfolds to EXACTLY the doc-§4 text. -/
theorem CorrelatedAgreementCurveUD_def (pt : Fin (2 ^ 24) → F) (m : ℕ) :
    CorrelatedAgreementCurveUD pt m ↔
      ∀ (u : Fin m → Fin (2 ^ 24) → F) (Good : Finset F),
        (∀ α ∈ Good, closeN (RScode pt (2 ^ 21) : Set (Fin (2 ^ 24) → F)) 7340028
          (fun x => ∑ j : Fin m, α ^ (j : ℕ) * u j x)) →
        (m - 1) * 7340029 < Good.card →
        ∃ g : Fin m → Fin (2 ^ 24) → F, (∀ j, g j ∈ RScode pt (2 ^ 21)) ∧
          2 ^ 24 - 7340028 ≤ (Finset.univ.filter fun x => ∀ j, u j x = g j x).card :=
  Iff.rfl

/-! ## Deployed-parameter facts -/

-- e* = (n − k)/2 = 7340032 and the deployed radius is the e* − 4 shave (doc §4(i)).
#guard (2 ^ 24 - 2 ^ 21) / 2 = 7340032
#guard 7340032 - 4 = 7340028
-- The UD side condition HOLDS at deployed params with room: 2r + k = n − 8.
#guard 2 * 7340028 + 2 ^ 21 = 2 ^ 24 - 8
#guard 2 * 7340028 + 2 ^ 21 ≤ 2 ^ 24
-- The agreement floor the Props assert: n − r = 9437188 (doc §4(i)).
#guard 2 ^ 24 - 7340028 = 9437188

/-- The deployed radius r = 7340028 sits STRICTLY inside the unique-decoding regime
(2r + k = n − 8 ≤ n): radius-r balls around any word contain at most ONE deployed codeword.
This is L0.4 instantiated at (n, k, r) = (2²⁴, 2²¹, 7340028) — the fact L5 consumes. -/
theorem deployed_unique_decoding {pt : Fin (2 ^ 24) → F} (hpt : Function.Injective pt)
    {w f g : Fin (2 ^ 24) → F}
    (hf : f ∈ RScode pt (2 ^ 21)) (hg : g ∈ RScode pt (2 ^ 21))
    (hwf : hammingDist w f ≤ 7340028) (hwg : hammingDist w g ≤ 7340028) : f = g :=
  rs_unique_decoding hpt (by simp only [Fintype.card_fin]; norm_num) hf hg hwf hwg

/-! ## Non-vacuity — a concrete small instance: RS(n = 4, k = 1) over ZMod 5

Domain {0,1,2,3} ⊂ ZMod 5, constant polynomials as the code. d = n − k + 1 = 4, and
r = 1 satisfies 2r + k = 3 ≤ 4, so unique decoding applies at radius 1. -/
section NonVacuity

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The 4-point domain 0,1,2,3 in ZMod 5. -/
def pt5 : Fin 4 → ZMod 5 := fun i => (i.val : ZMod 5)

theorem pt5_inj : Function.Injective pt5 := by decide

/-- `RScode` is inhabited by a NONZERO codeword (the evaluation of X, k = 2). -/
theorem rscode_nonzero_inhabited : ∃ f ∈ RScode pt5 2, f ≠ 0 := by
  refine ⟨evalOn pt5 Polynomial.X,
    ⟨Polynomial.X, Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt Polynomial.degree_X_le (by exact_mod_cast Nat.one_lt_two)), rfl⟩, ?_⟩
  intro h
  have h1 : (Polynomial.X : (ZMod 5)[X]).eval (pt5 1) = 0 := congrFun h 1
  rw [Polynomial.eval_X] at h1
  exact absurd h1 (by decide)

/-- The constant-2 codeword of RS(4, 1). -/
def c2 : Fin 4 → ZMod 5 := fun _ => 2

theorem c2_mem : c2 ∈ RScode pt5 1 :=
  ⟨Polynomial.C 2, Polynomial.mem_degreeLT.mpr (by simpa using Polynomial.degree_C_lt),
    funext fun _ => Polynomial.eval_C⟩

/-- The constant-0 codeword of RS(4, 1). -/
def c0 : Fin 4 → ZMod 5 := fun _ => 0

theorem c0_mem : c0 ∈ RScode pt5 1 :=
  ⟨Polynomial.C 0, Polynomial.mem_degreeLT.mpr (by simp),
    funext fun _ => Polynomial.eval_C⟩

/-- The concrete received word ![2,2,2,3] — distance 1 from `c2` (computed below), so the
unique-decoding hypothesis is SATISFIABLE (the firing below is not vacuous). -/
def w4 : Fin 4 → ZMod 5 := ![2, 2, 2, 3]

-- the distances COMPUTE, and the ball around w4 is inhabited at radius 1
#guard hammingDist w4 c2 = 1
#guard hammingDist w4 c0 = 4
-- the min-distance conclusion below is TIGHT: dist(c0, c2) is exactly n − k + 1 = 4
#guard hammingDist c0 c2 = 4

/-- `rs_min_distance` FIRES on the concrete instance: 4 = n − k + 1 ≤ dist(c0, c2)
(and the `#guard` above shows the bound is attained — full strength, not slack). -/
theorem min_distance_fires : 4 - 1 + 1 ≤ hammingDist c0 c2 := by
  have h := rs_min_distance pt5_inj c0_mem c2_mem
    (by intro h; exact absurd (congrFun h 0) (by decide))
  simpa using h

/-- THE LOAD-BEARING LEMMA FIRES: unique decoding at the concrete instance — ANY RS(4,1)
codeword within radius 1 of ![2,2,2,3] IS the constant-2 codeword. (Inhabited: `c2` itself,
per the `#guard hammingDist w4 c2 = 1` above.) -/
theorem unique_decoding_fires (g : Fin 4 → ZMod 5)
    (hg : g ∈ RScode pt5 1) (hclose : hammingDist w4 g ≤ 1) : g = c2 :=
  rs_unique_decoding pt5_inj (by decide) hg c2_mem hclose (by decide)

end NonVacuity

/-! ## Axiom hygiene — every lemma pinned to the three kernel axioms -/

#assert_all_clean [evalOn_apply, mem_RScode, closeN_mono, closeN_of_mem,
  interleavedClose_iff_filter, interleavedClose_pair_iff, card_agreeSet_lt,
  hammingDist_eq_card_filter, rs_min_distance, rs_unique_decoding, rs_ball_subsingleton,
  CorrelatedAgreementPairUD_def, CorrelatedAgreementCurveUD_def, deployed_unique_decoding,
  pt5_inj, rscode_nonzero_inhabited, c2_mem, c0_mem, min_distance_fires,
  unique_decoding_fires]

end Dregg2.Circuit.CorrelatedAgreement
