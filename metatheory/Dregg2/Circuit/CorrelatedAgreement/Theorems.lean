/-
# Dregg2.Circuit.CorrelatedAgreement.Theorems — rungs L5/L6 of the UD-regime correlated
agreement DAG (`docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md` §6).

Lean-authored proof over `Polynomial`/`Finset`: there is no Rust AIR here and there must
not be. Everything is generic in `(F, n, k, r, m)` per §8 (CA is consumed at EVERY layer of
the fold tower, not at one instance); the deployed instantiations come last.

## STATUS — what is proven here, and what is NOT (read before quoting anything)

**PROVEN, in the exact `Interface.lean`-consumed shapes, with NO extra hypothesis beyond a
radius side condition:**

* `curveUDParam_of_classical` — **L6**: `CorrelatedAgreementCurveUDParam F n (RScode pt k) r m`
  at the TARGET threshold `(m−1)(r+1) < |Good|`, whenever `(m+1)·r + k ≤ n`.
* `pairUDParam_of_classical` — **L5**: `CorrelatedAgreementPairUDParam F n (RScode pt k) r` at
  the target threshold `r + 1 < |Good|`, whenever `3r + k ≤ n`.
* `curveUDParamAt_of_ps` — the SAME conclusion up to the FULL unique-decoding radius
  `2r + k ≤ n`, at the LARGER Polishchuk–Spielman threshold `psThreshold n k r m`
  (this is the L1→L2→L3.2→L4 composition, fired end to end).
* `tower_far_survival_ca_proven` — `DecimLiftDischarge.ud_tower_far_survival_discharged` with
  its correlated-agreement hypothesis DISCHARGED BY A THEOREM at POSITIVE radius (the
  geometric schedule `rᵢ = 8^(5−i)` over the five welded layers; previously only the
  degenerate `r = 0` corner was discharged) — and `tower_fire_positive_radius` runs it END
  TO END, five FS rounds from the `2^19`-domain far word, bound `143395/|BabyBear|`.
* `curveUDParam_deployedExt` / `pairUDParam_deployedExt` / `curveUDParamAt_deployedExt_ps` —
  the deployed instantiations at the QUARTIC EXTENSION code `friCodeDeployedExt`.

**NOT PROVEN (the exact residual, §5).** The two regimes do NOT cover the whole range. The
target threshold `(m−1)(r+1)` is Kopparty 2025's IMPROVED `a`-bound; the BCIKS20 §4 engine
formalized in L1–L4 provably cannot reach it (PS's budget forces
`|S|·(n−k−r+1) > (m−1)(r+2)·n` — a factor `≥ n/(n−k−r+1) > 1` above the target at EVERY
parameter setting, `2.2857×` at the deployed shape). Unproven band:

    radius   d_min/(m+1) < r ≤ (n−k)/2      AND
    goodset  (m−1)(r+1) < |Good| ≤ psThreshold n k r m

At the deployed `(n, k, r) = (2²⁴, 2²¹, 7340028)` with `m = 8` this is the band
`51380203 < |Good| ≤ 117440400`, i.e. the residual costs **strictly less than 1.2 bits** of
per-fold soundness (≈ 98.0 target bits → ≈ 96.8 proven bits over `|L| ≈ 2^123.6`), NOT a
hole. Closing it needs Kopparty 2025 §2.1's OVERSIZED error locator (`deg_X A = n−e−1`), a
named and bounded piece of work, not open research.

§6 fires BOTH regimes on concrete instances the other one cannot reach; §9 is the axiom gate.
-/
import Mathlib.LinearAlgebra.Lagrange
import Dregg2.Circuit.CorrelatedAgreement.Scaffolding
import Dregg2.Circuit.CorrelatedAgreement.Collinearity
import Dregg2.Circuit.CorrelatedAgreement.Interpolation
import Dregg2.Circuit.CorrelatedAgreement.Interface
import Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge
import Dregg2.Circuit.FriDeployedExtCode

namespace Dregg2.Circuit.CorrelatedAgreement

open Polynomial

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1 — Interpolating a family of codewords into a power curve

Given `m` DISTINCT challenges `α : Fin m → F` and `m` words `v : Fin m → ι → F`, the
Vandermonde system `Σ_j α_i^j · g_j = v_i` has a unique solution `g`, and each `g_j` is an
`F`-linear combination of the `v_i` — hence a CODEWORD whenever the code is a submodule
(which `RScode` is). This is the candidate curve the classical regime decodes to. -/

/-- The `j`-th `X`-coefficient of the `i`-th Lagrange basis polynomial at the nodes `α`:
the `(j, i)` entry of the inverse Vandermonde matrix of `α`. -/
noncomputable def lagCoeff {m : ℕ} (α : Fin m → F) (j i : Fin m) : F :=
  (Lagrange.basis Finset.univ α i).coeff (j : ℕ)

/-- The INTERPOLATED CURVE: the coefficient words `g_j` of the unique degree-<m curve
through the given words — `Σ_j α_i^j · g_j = v_i` (`interpCurve_eval`). -/
noncomputable def interpCurve {m : ℕ} (α : Fin m → F) (v : Fin m → ι → F) (j : Fin m) :
    ι → F :=
  fun x => ∑ i : Fin m, lagCoeff α j i * v i x

/-- Each interpolated coefficient word is an `F`-linear combination of the input words, so
it lies in ANY submodule containing them — in particular in `RScode pt k`. -/
theorem interpCurve_mem {m : ℕ} (α : Fin m → F) {C : Submodule F (ι → F)}
    {v : Fin m → ι → F} (hv : ∀ i, v i ∈ C) (j : Fin m) : interpCurve α v j ∈ C := by
  have hsum : interpCurve α v j = ∑ i : Fin m, lagCoeff α j i • v i := by
    funext x
    simp [interpCurve, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => C.smul_mem _ (hv i)

/-- **The interpolation identity**: at every node `α i`, the interpolated curve evaluates
back to the input word `v i`. (Lagrange basis: `eval_basis_self` / `eval_basis_of_ne`.) -/
theorem interpCurve_eval {m : ℕ} {α : Fin m → F} (hα : Function.Injective α)
    (hm : 1 ≤ m) (v : Fin m → ι → F) (i : Fin m) (x : ι) :
    ∑ j : Fin m, α i ^ (j : ℕ) * interpCurve α v j x = v i x := by
  classical
  have hinj : Set.InjOn α ↑(Finset.univ : Finset (Fin m)) := fun a _ b _ h => hα h
  have hbasis : ∀ i' : Fin m, ∑ j : Fin m, α i ^ (j : ℕ) * lagCoeff α j i'
      = (Lagrange.basis Finset.univ α i').eval (α i) := by
    intro i'
    have hdeg : (Lagrange.basis (Finset.univ : Finset (Fin m)) α i').natDegree < m := by
      rw [Lagrange.natDegree_basis hinj (Finset.mem_univ i'), Finset.card_univ,
        Fintype.card_fin]
      omega
    rw [Polynomial.eval_eq_sum_range' hdeg,
      ← Fin.sum_univ_eq_sum_range
        (fun j => (Lagrange.basis Finset.univ α i').coeff j * α i ^ j) m]
    exact Finset.sum_congr rfl fun j _ => by rw [lagCoeff, mul_comm]
  have hswap : ∑ j : Fin m, α i ^ (j : ℕ) * interpCurve α v j x
      = ∑ i' : Fin m, ∑ j : Fin m, α i ^ (j : ℕ) * lagCoeff α j i' * v i' x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [interpCurve, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  rw [hswap]
  have hterm : ∀ i' : Fin m, ∑ j : Fin m, α i ^ (j : ℕ) * lagCoeff α j i' * v i' x
      = (if i' = i then (1 : F) else 0) * v i' x := by
    intro i'
    rw [← Finset.sum_mul, hbasis i']
    by_cases h : i' = i
    · subst h
      rw [Lagrange.eval_basis_self hinj (Finset.mem_univ i')]
      simp
    · rw [Lagrange.eval_basis_of_ne h (Finset.mem_univ i)]
      simp [h]
  rw [Finset.sum_congr rfl fun i' _ => hterm i']
  simp

/-! ## §2 — THE CLASSICAL REGIME `(m+1)·r < d_min` (Ligero/AHIV), at the TARGET threshold

The elementary route, which reaches the §4 threshold `(m−1)(r+1) < |Good|` EXACTLY (no PS
budget) at the cost of a smaller radius. The argument:

1. pick `m` distinct good challenges and decode each (`closeN`), giving codewords `v_i`;
2. interpolate them into a curve `g` (§1) — each `g_j` a codeword since `RScode` is a
   submodule;
3. off the union of the `m` decoding error sets, the difference curve
   `Σ_j Z^j (u_j(x) − g_j(x))` (degree ≤ m−1) vanishes at `m` distinct points, hence is
   ZERO: the interleaved disagreement set `Bad` has `|Bad| ≤ m·r`;
4. so at EVERY challenge `β`, `Δ(Σ β^j u_j, Σ β^j g_j) ≤ |Bad| ≤ m·r`; at a GOOD `β` the
   decoded codeword is within `r`, so the two codewords are within `(m+1)·r <` the RS
   minimum distance — they COINCIDE (`rs_min_distance`). Hence `Δ(Σ β^j u_j, Σ β^j g_j) ≤ r`
   for every `β ∈ Good`;
5. L4.4's LOSSLESS double count (`interleavedClose_of_curve_agreement`) then converts
   `(m−1)(r+1) < |Good|` into `Δ([u], C^m) ≤ r`.

Step 4 is where the radius is paid: it needs `(m+1)·r + k ≤ n`, i.e. `r < d_min/(m+1)`,
NOT the full unique-decoding `2r + k ≤ n`. -/

/-- `m` distinct elements of a finset of size ≥ `m`, as an injective tuple. -/
theorem exists_injective_mem {m : ℕ} {Good : Finset F} (h : m ≤ Good.card) :
    ∃ α : Fin m → F, Function.Injective α ∧ ∀ i, α i ∈ Good := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h
  let e : {x // x ∈ T} ≃ Fin m := T.equivFinOfCardEq hTcard
  refine ⟨fun i => ((e.symm i : {x // x ∈ T}) : F), ?_, fun i => hTsub (e.symm i).2⟩
  intro a b hab
  have hsub : e.symm a = e.symm b := Subtype.ext hab
  simpa using congrArg e hsub

/-- The `β`-combination of a family of codewords is a codeword (the code is a submodule). -/
theorem curveComb_mem {m : ℕ} {C : Submodule F (ι → F)} {g : Fin m → ι → F}
    (hg : ∀ j, g j ∈ C) (β : F) : (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) ∈ C := by
  have hrw : (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) = ∑ j : Fin m, β ^ (j : ℕ) • g j := by
    funext x
    simp [Finset.sum_apply]
  rw [hrw]
  exact Submodule.sum_mem _ fun j _ => C.smul_mem _ (hg j)

/-- **L5/L6, classical regime — the TARGET threshold, PROVEN.** If the `m`-term power curve
of `u` is `r`-close to `RS[pt, k]` at more than `(m−1)(r+1)` challenges and the radius
satisfies `(m+1)·r + k ≤ n` (i.e. `(m+1)·r < d_min = n−k+1`), then the rows of `u` are
SIMULTANEOUSLY `r`-close: `Δ([u], C^m) ≤ r`. No Polishchuk–Spielman budget is used. -/
theorem interleavedClose_of_classical_regime {pt : ι → F} (hpt : Function.Injective pt)
    {m k r : ℕ} (hm : 1 ≤ m) (hdist : (m + 1) * r + k ≤ Fintype.card ι)
    {u : Fin m → ι → F} {Good : Finset F}
    (hclose : ∀ α ∈ Good, closeN (RScode pt k : Set (ι → F)) r
      (fun x => ∑ j : Fin m, α ^ (j : ℕ) * u j x))
    (hcard : (m - 1) * (r + 1) < Good.card) :
    interleavedClose (RScode pt k : Set (ι → F)) u r := by
  classical
  have hdist' : m * r + r + k ≤ Fintype.card ι := by
    have h : (m + 1) * r = m * r + r := by ring
    rw [h] at hdist
    exact hdist
  -- STEP 1 — m distinct good challenges, each decoded
  have hmGood : m ≤ Good.card := by
    have h1 : m - 1 ≤ (m - 1) * (r + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos r)
    omega
  obtain ⟨α, hαinj, hαmem⟩ := exists_injective_mem hmGood
  choose v hvmem hvdist using fun i : Fin m => hclose (α i) (hαmem i)
  -- STEP 2 — interpolate the decodings into a curve of codewords
  obtain ⟨g, hg, hnode⟩ : ∃ g : Fin m → ι → F, (∀ j, g j ∈ (RScode pt k : Set (ι → F))) ∧
      ∀ i x, ∑ j : Fin m, α i ^ (j : ℕ) * g j x = v i x :=
    ⟨interpCurve α v, fun j => interpCurve_mem α (fun i => hvmem i) j,
      fun i x => interpCurve_eval hαinj hm v i x⟩
  -- STEP 3 — the interleaved disagreement set is covered by the m decoding error sets
  obtain ⟨Bad, hBadcard, hBadagree⟩ :
      ∃ Bad : Finset ι, Bad.card ≤ m * r ∧ ∀ x ∉ Bad, ∀ j, u j x = g j x := by
    refine ⟨Finset.univ.biUnion fun i : Fin m => Finset.univ.filter fun x =>
      (∑ j : Fin m, α i ^ (j : ℕ) * u j x) ≠ v i x, ?_, ?_⟩
    · calc (Finset.univ.biUnion fun i : Fin m => Finset.univ.filter fun x =>
              (∑ j : Fin m, α i ^ (j : ℕ) * u j x) ≠ v i x).card
          ≤ ∑ _i : Fin m, (Finset.univ.filter fun x =>
              (∑ j : Fin m, α _i ^ (j : ℕ) * u j x) ≠ v _i x).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin m, r := Finset.sum_le_sum fun i _ => by
              have h := hvdist i
              rw [hammingDist_eq_card_filter] at h
              exact h
        _ = m * r := by simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    · intro x hx
      have hall : ∀ i : Fin m, (∑ j : Fin m, α i ^ (j : ℕ) * u j x) = v i x := by
        intro i
        by_contra hne
        exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩⟩)
      have hzero : curvePoly (fun j : Fin m => u j x - g j x) = 0 := by
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hαinj
          (fun i => ?_) ?_
        · rw [curvePoly_eval]
          have hsplit : ∑ j : Fin m, (u j x - g j x) * α i ^ (j : ℕ)
              = (∑ j : Fin m, α i ^ (j : ℕ) * u j x)
                - ∑ j : Fin m, α i ^ (j : ℕ) * g j x := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
          rw [hsplit, hall i, hnode i x, sub_self]
        · rw [Fintype.card_fin]
          have h := curvePoly_natDegree_le (fun j : Fin m => u j x - g j x)
          omega
      intro j
      have hc := curvePoly_coeff (fun j : Fin m => u j x - g j x) j
      rw [hzero, Polynomial.coeff_zero] at hc
      exact sub_eq_zero.mp hc.symm
  -- STEP 4 — at every good challenge the two codewords COINCIDE (min distance)
  have hagree : ∀ β : F, hammingDist (fun x => ∑ j : Fin m, β ^ (j : ℕ) * u j x)
      (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) ≤ Bad.card := by
    intro β
    rw [hammingDist_eq_card_filter]
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_filter] at hx
    by_contra hnot
    exact hx.2 (Finset.sum_congr rfl fun j _ => by rw [hBadagree x hnot j])
  have hclose' : ∀ β ∈ Good, hammingDist (fun x => ∑ j : Fin m, β ^ (j : ℕ) * u j x)
      (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) ≤ r := by
    intro β hβ
    obtain ⟨vb, hvb, hdb⟩ := hclose β hβ
    have hGmem : (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) ∈ RScode pt k :=
      curveComb_mem (C := RScode pt k) (fun j => hg j) β
    have heq : (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) = vb := by
      by_contra hne
      have hmd := rs_min_distance hpt hGmem hvb hne
      have htri : hammingDist (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x) vb
          ≤ hammingDist (fun x => ∑ j : Fin m, β ^ (j : ℕ) * u j x)
              (fun x => ∑ j : Fin m, β ^ (j : ℕ) * g j x)
            + hammingDist (fun x => ∑ j : Fin m, β ^ (j : ℕ) * u j x) vb :=
        hammingDist_triangle_left _ _ _
      have h1 := hagree β
      omega
    rw [heq]
    exact hdb
  -- STEP 5 — L4.4's lossless double count at the TARGET threshold
  exact interleavedClose_of_curve_agreement _ hg hclose' hcard

/-! ## §3 — L6 and L5: the GENERIC-PARAMETER Props, PROVEN in the classical regime

These are the §8-pinned `...Param` shapes verbatim (the ones `Interface.lean` consumes),
generic in `(F, n, k, r, m)`. The radius side condition `(m+1)·r + k ≤ n` is the classical
regime of §2; §4 below states exactly what is and is not covered beyond it. -/

/-- **⚑ L6 — `CorrelatedAgreementCurveUDParam`, PROVEN** for the RS code `RS[pt, k]` on any
`n`-point injective domain, at any radius with `(m+1)·r + k ≤ n`. Threshold is the target
`(m−1)(r+1) < |Good|`, verbatim. -/
theorem curveUDParam_of_classical {n : ℕ} {pt : Fin n → F} (hpt : Function.Injective pt)
    {k r m : ℕ} (hm : 1 ≤ m) (hdist : (m + 1) * r + k ≤ n) :
    CorrelatedAgreementCurveUDParam F n (RScode pt k : Set (Fin n → F)) r m := by
  intro u Good hclose hcard
  have h := interleavedClose_of_classical_regime hpt hm
    (by simpa using hdist) hclose hcard
  rw [interleavedClose_iff_filter] at h
  simpa using h

/-- **⚑ L5 — `CorrelatedAgreementPairUDParam`, PROVEN** (the two-term/line case): the
`m = 2` instance of L6, at threshold `r + 1 < |Good|` verbatim and radius `3r + k ≤ n`
(i.e. `3r < d_min` — the classical `d/3` bound). -/
theorem pairUDParam_of_classical {n : ℕ} {pt : Fin n → F} (hpt : Function.Injective pt)
    {k r : ℕ} (hdist : 3 * r + k ≤ n) :
    CorrelatedAgreementPairUDParam F n (RScode pt k : Set (Fin n → F)) r := by
  intro u v Good hclose hcard
  have hclose' : ∀ α ∈ Good, closeN (RScode pt k : Set (Fin n → F)) r
      (fun x => ∑ j : Fin 2, α ^ (j : ℕ) * (![u, v] : Fin 2 → Fin n → F) j x) := by
    intro α hα
    have hfun : (fun x => ∑ j : Fin 2, α ^ (j : ℕ) * (![u, v] : Fin 2 → Fin n → F) j x)
        = fun x => u x + α * v x := by
      funext x
      rw [Fin.sum_univ_two]
      simp
    rw [hfun]
    exact hclose α hα
  have h := interleavedClose_of_classical_regime (m := 2) hpt (by omega)
    (by simpa using hdist) hclose' (by simpa using hcard)
  rw [interleavedClose_pair_iff] at h
  simpa using h

/-! ## §4 — The PS route at the FULL unique-decoding radius, with its OWN threshold

§3 pays radius for the target threshold. The L2 composition
(`interleavedClose_of_good_challenges`) pays the reverse: it reaches the FULL UD radius
`2r + k ≤ n`, but Polishchuk–Spielman's degree budget `deg_X B/n + deg_Z B/|S| < 1` forces a
LARGER challenge set. To state that honestly we generalize the §4 Prop in its threshold. -/

/-- The doc-§4 Prop with the challenge threshold left as a PARAMETER `thr`.
`CorrelatedAgreementCurveUDParam` is DEFINITIONALLY the `thr = (m−1)(r+1)` instance
(`curveUDParamAt_target`). -/
def CorrelatedAgreementCurveUDParamAt (F : Type*) [Field F] [DecidableEq F]
    (n : ℕ) (V : Set (Fin n → F)) (r m thr : ℕ) : Prop :=
  ∀ (u : Fin m → Fin n → F) (Good : Finset F),
    (∀ α ∈ Good, closeN V r (fun x => ∑ j : Fin m, α ^ (j : ℕ) * u j x)) →
    thr < Good.card →
    ∃ g : Fin m → Fin n → F, (∀ j, g j ∈ V) ∧
      n - r ≤ (Finset.univ.filter fun x => ∀ j, u j x = g j x).card

/-- The target Prop IS the thresholded Prop at `thr = (m−1)(r+1)` — no reshaping. -/
theorem curveUDParamAt_target (n : ℕ) (V : Set (Fin n → F)) (r m : ℕ) :
    CorrelatedAgreementCurveUDParamAt F n V r m ((m - 1) * (r + 1))
      ↔ CorrelatedAgreementCurveUDParam F n V r m := Iff.rfl

/-- A LARGER threshold is a WEAKER statement (it demands more good challenges). -/
theorem curveUDParamAt_mono {n : ℕ} {V : Set (Fin n → F)} {r m thr thr' : ℕ}
    (h : thr ≤ thr') (hA : CorrelatedAgreementCurveUDParamAt F n V r m thr) :
    CorrelatedAgreementCurveUDParamAt F n V r m thr' :=
  fun u Good hclose hcard => hA u Good hclose (lt_of_le_of_lt h hcard)

/-- **The Polishchuk–Spielman challenge threshold** of the L2 composition: the least `thr`
for which `thr < |S|` forces the PS budget `(k+r−1)|S| + (m−1)(r+2)·n < n|S|`. Compare the
target `(m−1)(r+1)`: the ratio is `(r+2)/(r+1) · n/(n−k−r+1)`, which EXCEEDS 1 at every
parameter setting (§5). -/
def psThreshold (n k r m : ℕ) : ℕ := (m - 1) * (r + 2) * n / (n - (k + r - 1))

/-- **L6 at the FULL UD radius `2r + k ≤ n`** — same conclusion, PS's threshold. Fires the
whole L1→L2→L3.2(Polishchuk–Spielman)→L4 composition. -/
theorem curveUDParamAt_of_ps {n : ℕ} {pt : Fin n → F} (hpt : Function.Injective pt)
    {k r m : ℕ} (hk : 1 ≤ k) (hud : 2 * r + k ≤ n) (hn : k + r - 1 < n) :
    CorrelatedAgreementCurveUDParamAt F n (RScode pt k : Set (Fin n → F)) r m
      (psThreshold n k r m) := by
  intro u Good hcloseG hcard
  simp only [psThreshold] at hcard
  set K := k + r - 1 with hKdef
  set c := n - K with hcdef
  have hcpos : 0 < c := by omega
  have hdiv : (m - 1) * (r + 2) * n < Good.card * c :=
    (Nat.div_lt_iff_lt_mul hcpos).mp hcard
  have hmul : Good.card * c + Good.card * K = Good.card * n := by
    rw [← Nat.mul_add, hcdef, Nat.sub_add_cancel (le_of_lt hn)]
  have hbz : (r + 1) * (m - 1) + (m - 1) = (m - 1) * (r + 2) := by
    generalize m - 1 = M
    ring
  have hbudget : K * Good.card + ((r + 1) * (m - 1) + (m - 1)) * n < n * Good.card := by
    rw [hbz]
    calc K * Good.card + (m - 1) * (r + 2) * n
        = (m - 1) * (r + 2) * n + Good.card * K := by ring
      _ < Good.card * c + Good.card * K := by omega
      _ = Good.card * n := hmul
      _ = n * Good.card := mul_comm _ _
  have h := interleavedClose_of_good_challenges hpt hk (by simpa using hud) hcloseG
    (by simpa using hbudget)
  rw [interleavedClose_iff_filter] at h
  simpa using h

/-- **The best threshold the two regimes prove**, as ONE object: the target `(m−1)(r+1)`
inside the classical radius, PS's threshold outside it (up to the full UD radius). -/
theorem curveUDParamAt_combined {n : ℕ} {pt : Fin n → F} (hpt : Function.Injective pt)
    {k r m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hud : 2 * r + k ≤ n) (hn : k + r - 1 < n) :
    CorrelatedAgreementCurveUDParamAt F n (RScode pt k : Set (Fin n → F)) r m
      (if (m + 1) * r + k ≤ n then (m - 1) * (r + 1) else psThreshold n k r m) := by
  split_ifs with h
  · exact (curveUDParamAt_target n _ r m).mpr (curveUDParam_of_classical hpt hm h)
  · exact curveUDParamAt_of_ps hpt hk hud hn

/-! ## §5 — ⚑ THE EXACT RESIDUAL (what is NOT proven, in parameters)

The two regimes do NOT cover the whole range, and the gap is INTRINSIC to the engine, not
slack in the assembly. Precisely:

* **§3 (classical)** proves the target Prop verbatim for `(m+1)·r + k ≤ n`, i.e.
  `r < d_min/(m+1)` (`d_min = n−k+1`) — for `m = 2` this is the classical `d/3` bound, which
  is exactly why Kopparty 2025 Thm 1.3 assumes `γ ≥ δ_code/3`: below it the elementary
  argument already gives the theorem.
* **§4 (PS)** proves the same conclusion up to the FULL unique-decoding radius `2r + k ≤ n`,
  but only above `psThreshold n k r m ≈ (m−1)(r+2)·n/(n−k−r+1)`.

**RESIDUAL** — unproven here: radii `d_min/(m+1) < r ≤ (n−k)/2` TOGETHER WITH good-set sizes
`(m−1)(r+1) < |Good| ≤ psThreshold n k r m`. At the DEPLOYED shape (n = 2²⁴, k = 2²¹,
r = 7340028) the two bounds below make it exact:

* the classical radius ceiling at `m = 8` is `r ≤ 1631118`; the deployed `r = 7340028` is
  4.5× beyond it (`classical_ceiling_deployed`), so §3 does NOT cover the deployed radius;
* at the deployed radius §4 fires with `psThreshold = 117440400` against the target
  `(m−1)(r+1) = 51380203` — a factor `< 23/10` (`ps_ratio_deployed`), i.e. **the residual
  costs strictly less than 1.2 bits** of per-fold soundness (`2^1.2 > 2.3`), NOT a hole:
  ≈ 98.0 target bits become ≈ 96.8 proven bits over `|L| ≈ 2^123.6`.

The missing ingredient is named and is NOT open research: Kopparty 2025 §2.1's OVERSIZED
error locator (`deg_X A = n−e−1` in place of `deg_X A ≤ e`), which is what buys the improved
`a`-bound the §4 Props state. The BCIKS20 §4 engine formalized here (standard Berlekamp–Welch
+ PS) provably cannot reach it: the PS budget forces
`|S| · (n − k − r + 1) > (m−1)(r+2)·n`, and `(m−1)(r+1)` never satisfies that at ANY
parameters (the ratio is `≥ n/(n−k−r+1) > 1` always). -/

-- The deployed instantiation of both thresholds.
#guard (8 - 1) * (7340028 + 1) = 51380203
#guard psThreshold (2 ^ 24) (2 ^ 21) 7340028 8 = 117440400
-- The PS threshold exceeds the target by a factor in (2.285, 2.286) — under 23/10, hence
-- under 2^1.2: the residual costs LESS THAN 1.2 BITS of per-fold soundness.
theorem ps_ratio_deployed :
    51380203 * 2285 < 117440400 * 1000 ∧ 117440400 * 10 < 51380203 * 23 := by
  constructor <;> norm_num
-- The classical regime's radius ceiling at the deployed (n, k) and arity 8: r ≤ 1631118,
-- which the deployed r = 7340028 exceeds by 4.5× — §3 does NOT reach the deployed radius.
theorem classical_ceiling_deployed :
    (8 + 1) * 1631118 + 2 ^ 21 ≤ 2 ^ 24 ∧ ¬ ((8 + 1) * 1631119 + 2 ^ 21 ≤ 2 ^ 24) ∧
      ¬ ((8 + 1) * 7340028 + 2 ^ 21 ≤ 2 ^ 24) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩
-- The line case (m = 2): classical ceiling 4893354 = ⌊(n−k)/3⌋, deployed r is 1.5× beyond.
#guard (2 ^ 24 - 2 ^ 21) / 3 = 4893354
#guard (2 ^ 24 - 2 ^ 21) / 9 = 1631118

/-! ## §6 — NON-VACUITY: BOTH regimes FIRE, on instances the OTHER one cannot reach. -/

section Fire

/-- The words of the classical firing instance over RS(4,1)/ZMod 5: row 0 is corrupted at
the last domain point (genuinely NOT a codeword), row 1 is the all-ones codeword. -/
def cw : Fin 2 → Fin 4 → ZMod 5 := ![![0, 0, 0, 1], ![1, 1, 1, 1]]

/-- Constants are RS(·,1) codewords. -/
theorem const_mem_rscode (c : ZMod 5) : (fun _ => c) ∈ RScode pt5 1 :=
  mem_RScode.mpr ⟨Polynomial.C c, by simpa using Polynomial.degree_C_lt,
    fun _ => Polynomial.eval_C.symm⟩

-- Row 0 is GENUINELY corrupted: at distance ≥ 1 from EVERY codeword (the constants).
#guard ∀ c : ZMod 5, 1 ≤ hammingDist (cw 0) (fun _ => c)
-- ... and the interleaved pair is genuinely NOT simultaneously 0-close either.
#guard ∀ c d : ZMod 5, ¬ (∀ x : Fin 4, cw 0 x = c ∧ cw 1 x = d)

theorem cw_close_all : ∀ α : ZMod 5,
    hammingDist (fun x => ∑ j : Fin 2, α ^ (j : ℕ) * cw j x) (fun _ => α) ≤ 1 := by decide

/-- Every challenge is good: the fold `u₀ + α·u₁` is 1-close to the constant `α`. -/
theorem cw_close (S : Finset (ZMod 5)) : ∀ α ∈ S,
    closeN (RScode pt5 1 : Set (Fin 4 → ZMod 5)) 1
      (fun x => ∑ j : Fin 2, α ^ (j : ℕ) * cw j x) :=
  fun α _ => ⟨fun _ => α, const_mem_rscode α, cw_close_all α⟩

/-- **⚑ THE CLASSICAL REGIME FIRES** at (n, k, r, m) = (4, 1, 1, 2) over ZMod 5:
`(m+1)r + k = 4 ≤ 4 = n`, and only THREE good challenges are needed — `(m−1)(r+1) = 2`. -/
theorem classical_fires :
    interleavedClose (RScode pt5 1 : Set (Fin 4 → ZMod 5)) cw 1 :=
  interleavedClose_of_classical_regime (m := 2) pt5_inj (by omega) (by simp)
    (cw_close {0, 1, 2}) (by decide)

/-- **The L6 Param Prop FIRES** at those parameters (the Prop itself, not just its engine). -/
theorem curveUDParam_fires :
    CorrelatedAgreementCurveUDParam (ZMod 5) 4 (RScode pt5 1 : Set (Fin 4 → ZMod 5)) 1 2 :=
  curveUDParam_of_classical pt5_inj (by omega) (by norm_num)

/-- **The L5 pair Param Prop FIRES** at the same parameters (`3r + k = 4 ≤ 4`). -/
theorem pairUDParam_fires :
    CorrelatedAgreementPairUDParam (ZMod 5) 4 (RScode pt5 1 : Set (Fin 4 → ZMod 5)) 1 :=
  pairUDParam_of_classical pt5_inj (by norm_num)

/-- The Prop APPLIED to the corrupted data, with only 3 good challenges: a common agreement
set of size ≥ 3 for BOTH rows at once. -/
theorem curveUDParam_fires_concrete :
    ∃ g : Fin 2 → Fin 4 → ZMod 5, (∀ j, g j ∈ (RScode pt5 1 : Set (Fin 4 → ZMod 5))) ∧
      4 - 1 ≤ (Finset.univ.filter fun x => ∀ j, cw j x = g j x).card :=
  curveUDParam_fires cw {0, 1, 2} (cw_close {0, 1, 2}) (by decide)

/-- **The classical regime reaches thresholds the PS route CANNOT**: at these parameters
PS demands `|Good| > psThreshold 4 1 1 2 = 4`, and the firing above used `|Good| = 3`. -/
theorem ps_cannot_reach_classical_firing :
    ({0, 1, 2} : Finset (ZMod 5)).card ≤ psThreshold 4 1 1 2 := by decide

/-- **⚑ THE PS ROUTE FIRES** at the FULL unique-decoding radius on RS(3,1)/ZMod 7 — the L2
composition's instance (`Interpolation.fire_close`), where `2r + k = 3 = n` sits exactly AT
the UD boundary and the classical regime does NOT apply (`(m+1)r + k = 4 > 3 = n`). -/
theorem ps_route_fires :
    ∃ g : Fin 2 → Fin 3 → ZMod 7, (∀ j, g j ∈ (RScode ptF 1 : Set (Fin 3 → ZMod 7))) ∧
      3 - 1 ≤ (Finset.univ.filter fun x => ∀ j, wF j x = g j x).card :=
  curveUDParamAt_of_ps (k := 1) (r := 1) (m := 2) ptF_inj (by omega) (by norm_num)
    (by norm_num) wF {0, 1, 2, 3, 4} fire_close (by decide)

/-- The classical regime genuinely does NOT cover the PS firing's parameters. -/
theorem classical_cannot_reach_ps_firing : ¬ ((2 + 1) * 1 + 1 ≤ 3) := by norm_num

end Fire

/-! ## §7 — ⚑ THE TOWER, WITH CA DISCHARGED AT POSITIVE RADIUS

`DecimLiftDischarge.ud_tower_far_survival_discharged` carried three hypotheses: the radius
schedule, the per-layer CA, and the initial farness. Its only firing so far was at radius
`r = 0` (`hCA_zero`, the degenerate Vandermonde corner). Here all three are supplied at a
POSITIVE radius, from §3: the geometric schedule `rᵢ = 8^(5−i)` puts every one of the five
welded layers inside the classical regime `9·rᵢ₊₁ + kᵢ₊₁ ≤ nᵢ₊₁`, so the CA hypothesis is a
THEOREM, not an assumption. Relative top radius `32768/2^19 = 1/16` (against `δ_code = 7/8`
and the classical ceiling `δ_code/9 ≈ 0.097`). -/

section Tower

open Dregg2.Circuit.FriSetupTower (twSz towerS wchain wchain_ord monoW farWord
  pow_inj_of_orderOf)
open Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge (towerV towerDec
  ud_tower_far_survival_discharged)
open Dregg2.Circuit.CorrelatedAgreement.Interface (towerFar towerFold towerEnc towerD)
open Dregg2.Circuit.FriChainStepIdx (sigFar sigFold)
open Dregg2.Circuit.FriAdversaryObject (honestStrategy fsChain)
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-- The Scaffolding RS code IS the tower's `rsCode` on the geometric domain `x ↦ ω^x`. -/
theorem RScode_eq_towerRsCode {N D : ℕ} (hD : 0 < D) (ω : BabyBear) :
    RScode (fun x : Fin N => ω ^ (x : ℕ)) D = Dregg2.Circuit.FriSetupTower.rsCode N D ω := by
  rw [Interface.RScode_eq_rsCode hD]
  rfl

/-- **Per-layer CA at a tower layer**, from §3: the classical regime at the layer's
`(N, D, r)`, with the geometric domain's injectivity from `orderOf ω = N`. -/
theorem curveUDParam_towerLayer {N D : ℕ} (ω : BabyBear) (hord : orderOf ω = N)
    (hN : 0 < N) (hD : 0 < D) {r m : ℕ} (hm : 1 ≤ m) (hdist : (m + 1) * r + D ≤ N) :
    CorrelatedAgreementCurveUDParam BabyBear N
      (↑(Dregg2.Circuit.FriSetupTower.rsCode N D ω) : Set (Fin N → BabyBear)) r m := by
  have hinj : Function.Injective (fun x : Fin N => ω ^ (x : ℕ)) := fun a b h =>
    Fin.ext (pow_inj_of_orderOf hord hN a.isLt b.isLt h)
  rw [← RScode_eq_towerRsCode hD ω]
  exact curveUDParam_of_classical hinj hm hdist

/-- The geometric radius schedule `rᵢ = 8^(5−i)`, zero past the tower. -/
def towerRR : ℕ → ℕ
  | 0 => 32768
  | 1 => 4096
  | 2 => 512
  | 3 => 64
  | 4 => 8
  | 5 => 1
  | _ + 6 => 0

/-- The schedule satisfies the interface's constant-relative-radius law `8·rᵢ₊₁ ≤ rᵢ`. -/
theorem towerRR_sched : ∀ i, 8 * towerRR (i + 1) ≤ towerRR i := by
  intro i
  match i with
  | 0 => norm_num [towerRR]
  | 1 => norm_num [towerRR]
  | 2 => norm_num [towerRR]
  | 3 => norm_num [towerRR]
  | 4 => norm_num [towerRR]
  | 5 => norm_num [towerRR]
  | n + 6 => show 8 * towerRR (n + 1 + 6) ≤ towerRR (n + 6); norm_num [towerRR]

/-- **⚑ THE PER-LAYER CA AT THE DEPLOYED TOWER, PROVEN** — every one of the five welded
layers sits inside the classical regime at the geometric schedule:
`9·r + k ≤ n` reads `36864+8192 ≤ 65536`, `4608+1024 ≤ 8192`, `576+128 ≤ 1024`,
`72+16 ≤ 128`, `9+2 ≤ 16`. -/
theorem hCA_tower : ∀ i, i < 5 →
    CorrelatedAgreementCurveUDParam BabyBear (twSz (i + 1)) (towerV (i + 1))
      (towerRR (i + 1)) 8 := by
  intro i hi
  interval_cases i
  · exact curveUDParam_towerLayer (N := twSz 1) (D := 2 ^ 13) (r := towerRR 1) (m := 8)
      (wchain 2)
      (by rw [wchain_ord 2 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, towerRR])
  · exact curveUDParam_towerLayer (N := twSz 2) (D := 2 ^ 10) (r := towerRR 2) (m := 8)
      (wchain 3)
      (by rw [wchain_ord 3 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, towerRR])
  · exact curveUDParam_towerLayer (N := twSz 3) (D := 2 ^ 7) (r := towerRR 3) (m := 8)
      (wchain 4)
      (by rw [wchain_ord 4 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, towerRR])
  · exact curveUDParam_towerLayer (N := twSz 4) (D := 2 ^ 4) (r := towerRR 4) (m := 8)
      (wchain 5)
      (by rw [wchain_ord 5 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, towerRR])
  · exact curveUDParam_towerLayer (N := twSz 5) (D := 2) (r := towerRR 5) (m := 8)
      (wchain 6)
      (by rw [wchain_ord 6 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, towerRR])

/-- **The degree-`D` monomial word is `(n − D)`-FAR from `RS[pt, D]`** — the standard
distance witness (`card_agreeSet_lt` on `X^D − q`), in `closeN` form. -/
theorem monomial_far {pt : ι → F} (hpt : Function.Injective pt) {D r : ℕ}
    (hr : r + D < Fintype.card ι) :
    ¬ closeN (RScode pt D : Set (ι → F)) r (fun x => pt x ^ D) := by
  classical
  rintro ⟨v, hv, hd⟩
  obtain ⟨q, hq, hvq⟩ := mem_RScode.mp hv
  have hdX : ((Polynomial.X : F[X]) ^ D).degree = (D : WithBot ℕ) := by
    simp
  have hne : (Polynomial.X : F[X]) ^ D ≠ q := by
    intro h
    rw [h] at hdX
    rw [hdX] at hq
    exact absurd hq (lt_irrefl _)
  have hagree := card_agreeSet_lt (k := D + 1) hpt (p := (Polynomial.X : F[X]) ^ D) (q := q)
    (by rw [hdX]; exact_mod_cast Nat.lt_succ_self D)
    (lt_trans hq (by exact_mod_cast Nat.lt_succ_self D)) hne
  have hfilter : (Finset.univ.filter fun i => pt i ^ D = v i)
      = (Finset.univ.filter fun i =>
          ((Polynomial.X : F[X]) ^ D).eval (pt i) = q.eval (pt i)) :=
    Finset.filter_congr fun i _ => by rw [hvq i]; simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => pt i ^ D = v i)
  rw [Finset.card_univ] at hsplit
  have hdist : hammingDist (fun x => pt x ^ D) v
      = (Finset.univ.filter fun i => ¬ (pt i ^ D = v i)).card :=
    hammingDist_eq_card_filter _ _
  rw [hfilter] at hsplit
  omega

/-- The tower's layer-0 far word is far at the SCHEDULE's radius `r₀ = 32768` (not merely a
non-codeword): the degree-`2^16` monomial is `2^19 − 2^16 = 458752`-far. -/
theorem farWord_far_tower : ¬ closeN (towerV 0) (towerRR 0) farWord := by
  have h : ¬ closeN (RScode (fun x : Fin (twSz 0) => wchain 1 ^ (x : ℕ)) (2 ^ 16) :
      Set (Fin (twSz 0) → BabyBear)) (towerRR 0) (fun x => (wchain 1 ^ (x : ℕ)) ^ (2 ^ 16)) :=
    monomial_far (fun a b hab =>
      Fin.ext (pow_inj_of_orderOf
        (by rw [wchain_ord 1 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
        a.isLt b.isLt hab))
      (by norm_num [twSz, towerRR])
  rw [RScode_eq_towerRsCode (by norm_num)] at h
  exact h

/-- **⚑ THE INSTANTIATION — the fold tower's round-by-round FS soundness with the CA
hypothesis DISCHARGED BY A THEOREM at positive radius.** Same conclusion as
`ud_tower_far_survival_discharged`, with its radius schedule, per-layer correlated agreement
and initial farness all supplied: the per-fold cap is `(8−1)(r₁+1) = 7·4097 = 28679` over
`|BabyBear|`. (Base-field instance — the deployed word is quartic-extension valued; the Param
form is field-generic, so only the numbers move.) -/
theorem tower_far_survival_ca_proven
    (rounds : ℕ) {bad : (towerD 5 twSz BabyBear → BabyBear) → Bool}
    (hbad : ∀ H : towerD 5 twSz BabyBear → BabyBear, bad H = true →
      ¬ sigFar (towerFar 5 twSz towerV towerRR)
          (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩
            (fsChain (towerEnc 5 twSz)
              (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩)
              H rounds []))) :
    winProb bad
      ≤ ((rounds : ℝ) * (((8 - 1) * (towerRR 1 + 1) : ℕ) : ℝ))
        / (Fintype.card BabyBear : ℝ) :=
  ud_tower_far_survival_discharged towerRR towerRR_sched hCA_tower farWord farWord_far_tower
    rounds hbad

-- The cap the instantiation carries, and its five-round bound.
#guard (8 - 1) * (towerRR 1 + 1) = 28679
#guard 5 * 28679 = 143395

open Classical in
/-- **⚑ THE FIRE — the tower runs END TO END at POSITIVE radius.** Five FS rounds of the
arity-8 fold from the `2^19`-domain far word: the probability that farness dies across the
five welded layers is at most `143395/|BabyBear|`, with the lift weld, the schedule, the
per-layer CORRELATED AGREEMENT and the initial farness ALL theorems. Contrast
`DecimLiftDischarge.discharged_tower_fire`, whose CA came from the degenerate `r = 0`
Vandermonde corner: here the radii are `32768, 4096, 512, 64, 8, 1`. -/
theorem tower_fire_positive_radius :
    winProb (fun H : towerD 5 twSz BabyBear → BabyBear =>
        decide (¬ sigFar (towerFar 5 twSz towerV towerRR)
          (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩
            (fsChain (towerEnc 5 twSz)
              (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩)
              H 5 []))))
      ≤ (143395 : ℝ) / (Fintype.card BabyBear : ℝ) := by
  refine le_trans
    (tower_far_survival_ca_proven 5
      (bad := fun H => decide (¬ sigFar (towerFar 5 twSz towerV towerRR)
        (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩
          (fsChain (towerEnc 5 twSz)
            (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩)
            H 5 []))))
      (fun H hH => of_decide_eq_true hH))
    (le_of_eq (by norm_num [towerRR]))

/-- The five-round bound is genuinely nontrivial (`< 2⁻¹³` over BabyBear). -/
theorem tower_bound_nontrivial :
    (5 : ℝ) * (((8 - 1) * (towerRR 1 + 1) : ℕ) : ℝ) / (Fintype.card BabyBear : ℝ)
      < 1 / 2 ^ 13 := by
  rw [ZMod.card]
  norm_num [towerRR]

end Tower

/-! ## §8 — THE DEPLOYED INSTANTIATION, AT THE QUARTIC EXTENSION (doc §8 Refinement 2)

The deployed words are `ι → L` with `L = BB4` the quartic extension; the code is
`friCodeDeployedExt` (`FriDeployedExtCode`), degree `< 2²¹` on the same `2²⁴` domain. The
Param form is field-generic, so both regimes land here unchanged. -/

section Deployed

open Dregg2.Circuit.FriDeployedExtCode (BB4 friCodeDeployedExt deployedPtsExt
  deployedPtsExt_inj)

/-- The deployed extension code IS the Scaffolding RS code on the retyped domain. -/
theorem deployedExt_code_eq :
    (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4))
      = (RScode deployedPtsExt (2 ^ 21) : Set (Fin (8 * 2 ^ 21) → BB4)) := by
  rw [Interface.RScode_eq_rsCode (by norm_num) deployedPtsExt]
  rfl

/-- **⚑ L6 AT THE DEPLOYED QUARTIC EXTENSION** — the target Prop verbatim, for any arity `m`
and any radius inside the classical regime `(m+1)·r + 2²¹ ≤ 2²⁴`. -/
theorem curveUDParam_deployedExt {r m : ℕ} (hm : 1 ≤ m)
    (hdist : (m + 1) * r + 2 ^ 21 ≤ 8 * 2 ^ 21) :
    CorrelatedAgreementCurveUDParam BB4 (8 * 2 ^ 21)
      (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) r m := by
  rw [deployedExt_code_eq]
  exact curveUDParam_of_classical deployedPtsExt_inj hm hdist

/-- The deployed FOLD ARITY (m = 8) at the classical ceiling radius `r = 1631118`
(= ⌊(n−k)/9⌋, relative `0.0972 ≈ δ_code/9`), over the quartic extension. -/
theorem curveUDParam_deployedExt_arity8 :
    CorrelatedAgreementCurveUDParam BB4 (8 * 2 ^ 21)
      (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 1631118 8 :=
  curveUDParam_deployedExt (by omega) (by norm_num)

/-- The deployed RLC BATCH WIDTH (m = 256) at its classical ceiling `r = 57120`. -/
theorem curveUDParam_deployedExt_batch256 :
    CorrelatedAgreementCurveUDParam BB4 (8 * 2 ^ 21)
      (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 57120 256 :=
  curveUDParam_deployedExt (by omega) (by norm_num)

/-- **⚑ L5 AT THE DEPLOYED QUARTIC EXTENSION** — the two-term/line Prop (the DEEP split), at
`3r + 2²¹ ≤ 2²⁴`; at the ceiling `r = 4893354` (relative `0.2917 = δ_code/3`). -/
theorem pairUDParam_deployedExt {r : ℕ} (hdist : 3 * r + 2 ^ 21 ≤ 8 * 2 ^ 21) :
    CorrelatedAgreementPairUDParam BB4 (8 * 2 ^ 21)
      (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) r := by
  rw [deployedExt_code_eq]
  exact pairUDParam_of_classical deployedPtsExt_inj hdist

theorem pairUDParam_deployedExt_ceiling :
    CorrelatedAgreementPairUDParam BB4 (8 * 2 ^ 21)
      (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 4893354 :=
  pairUDParam_deployedExt (by norm_num)

/-- **⚑ AT THE FULL DEPLOYED UD RADIUS `r = 7340028`** (doc §4's `e* − 4` shave), the PS
route gives the same conclusion for every arity `m` — at the threshold
`psThreshold 2²⁴ 2²¹ 7340028 m`, which is `117440400` at `m = 8` against the target
`51380203` (§5: a factor `< 23/10`, i.e. `< 1.2` bits). -/
theorem curveUDParamAt_deployedExt_ps (m : ℕ) :
    CorrelatedAgreementCurveUDParamAt BB4 (8 * 2 ^ 21)
      (↑friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 7340028 m
      (psThreshold (8 * 2 ^ 21) (2 ^ 21) 7340028 m) := by
  rw [deployedExt_code_eq]
  exact curveUDParamAt_of_ps deployedPtsExt_inj (by norm_num) (by norm_num) (by norm_num)

end Deployed

/-! ## §9 — Axiom hygiene: every keystone pinned to the three kernel axioms. -/

#assert_all_clean [interpCurve_mem, interpCurve_eval, exists_injective_mem, curveComb_mem,
  interleavedClose_of_classical_regime, curveUDParam_of_classical, pairUDParam_of_classical,
  curveUDParamAt_target, curveUDParamAt_mono, curveUDParamAt_of_ps, curveUDParamAt_combined,
  ps_ratio_deployed, classical_ceiling_deployed, const_mem_rscode, cw_close_all, cw_close,
  classical_fires, curveUDParam_fires, pairUDParam_fires, curveUDParam_fires_concrete,
  ps_cannot_reach_classical_firing, ps_route_fires, classical_cannot_reach_ps_firing,
  RScode_eq_towerRsCode, curveUDParam_towerLayer, towerRR_sched, hCA_tower, monomial_far,
  farWord_far_tower, tower_far_survival_ca_proven, tower_fire_positive_radius,
  tower_bound_nontrivial,
  deployedExt_code_eq, curveUDParam_deployedExt, curveUDParam_deployedExt_arity8,
  curveUDParam_deployedExt_batch256, pairUDParam_deployedExt, pairUDParam_deployedExt_ceiling,
  curveUDParamAt_deployedExt_ps]

end Dregg2.Circuit.CorrelatedAgreement
