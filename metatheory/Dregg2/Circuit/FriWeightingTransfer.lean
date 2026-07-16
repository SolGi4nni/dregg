import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Tactics

/-!
# `FriWeightingTransfer` — the WEIGHTING TRANSFER is `[Sta25]`-free (BCIKS20 Lemmas 7.5 + 7.6, mechanized)

**Why this file exists — the `+17…+31`-bit question, made honest.** The deployed FRI commit-phase
proven posture is `~61` bits (`FriLedger.friCommitLedger`, `FriLedgerSound.ledger_epsC_soundness`),
and it BINDS because BCIKS20's `ε_C` carries a term `∝ |D⁽⁰⁾|² / |F|` — the `O(n²)` exceptional-set
bound of its correlated-agreement theorem (`n = |D⁽⁰⁾|`). **BCSS25** (Ben-Sasson–Carmon–Haböck–
Kopparty–Saraf, *On Proximity Gaps for Reed–Solomon Codes*, ECCC TR25-169 = eprint 2025/2055) improves
that exceptional set to `O(n)` up to the Johnson radius (Thm 1.5 / Thm 4.2), which would make `ε_C`
LINEAR in `|D⁽⁰⁾|` — worth `~+log₂|D⁽⁰⁾| ≈ +17…+31` bits at our heights.

`FriLedger.lean`'s header refuses to bank those bits, on a specific and correct ground: **BCSS25
states no FRI soundness theorem, and the WEIGHTED correlated-agreement theorem FRI's round-by-round
analysis actually consumes (BCSS25 Corollary 4.4) is derived there from Theorem 4.3, which BCSS25 says
is "obtained by plugging in the improved bounds in the proof of `[Sta25, Theorem 22]`" — and `[Sta25]`
(the StarkWare S-two whitepaper) is a PERSONAL COMMUNICATION, not public.** A number resting on a
citation nobody outside StarkWare can read is the named-carrier pattern this tree rejects.

**This file proves the refusal is stronger than it needs to be: the `[Sta25]` dependency is
ELIMINABLE for the FRI application.** The route (verified against the primary sources, not a summary):

* BCIKS20 (eprint 2020/654) §7.1 derives its WEIGHTED curve theorem (Thm 7.2) from the UNWEIGHTED one
  plus a single structural fact — **co-curvilinearity on a large set `S′`**: the codewords `v₀,…,v_l`
  the unweighted argument finds satisfy `∑_j zʲ vⱼ = P_z` (the proximate) for every `z ∈ S′`
  (BCIKS20 Proposition 5.5). The transfer itself is BCIKS20 **Lemmas 7.5 and 7.6** — elementary
  double-counting over `D`, no personal communication (BCIKS20 §7.2, fully public).
* BCSS25 §3.2, **Step 4** STATES exactly that co-curvilinear `S′` — "a subset `S′ ⊂ S` such that
  `P(X, z) = P_z(X)` for each `z ∈ S′`", with `P(X,Z) = v₀(X) + Z·v₁(X)`, `deg_X P ≤ k` — and states it
  with the IMPROVED interpolant, whose `Z`-degree is `O(1)` in `n` at fixed rate (`D_Z = ⅓(m+½)²·(n/k)`,
  which is `n`-free only THROUGH the rate `n/k = 1/ρ`; `D_X = (m+½)√(kn)` is NOT `n`-free), making `S′`
  only LARGER. Step 5 closes it "using Lemma 2.4", which is BCSS25's own §2.3 lemma (public).
  **⚑ It does not PROVE Step 4** — see the residual section below; an earlier version of this header
  claimed it did, and the paper says otherwise in as many words.
* The weighted bound FRI's round analysis needs is therefore reachable by the BCIKS20 §7.1 route —
  co-curvilinearity `⟶` Lemmas 7.5/7.6 — feeding BCSS25's IMPROVED `S′`. The `[Sta25]`-backed
  Theorem 4.3 is a STRONGER statement (adversarial agreement sets `{A_z}`) that the FRI weighting
  application does not require; the round analysis needs the transfer applied to the `µ`-agreement
  sets, and that is exactly what Lemmas 7.5/7.6 do.

**⚑ The precise scope, audited (2026-07-16), against over-claiming.** The public route closes for the
DENOMINATOR-BOUNDED weights FRI actually uses — NOT for BCSS25 Corollary 4.4 in its full stated
generality (arbitrary real weights `w(x) ∈ [0,1]`). Lemma 7.5 loses a strictly positive `l/(|S′|−l)`;
Lemma 7.6 removes that loss ONLY by rounding on the rational grid `1/(M|D|)ℤ`, which exists exactly
when the weights have common denominator `M`. BCIKS20 Lemma 8.2's weights `µ⁽ⁱ⁾` are subtree-acceptance
probabilities with denominator `M = |D⁽⁰⁾|/|D⁽ⁱ⁺¹⁾|` — on the grid, so Lemma 7.6 fires and the FRI
statement is `[Sta25]`-free. For arbitrary real weights there is no grid and Theorem 4.3 is genuinely
doing the extra work; so the honest claim is **"`[Sta25]` is eliminable for the FRI application", not
"the public ingredients reproduce Corollary 4.4"**. A codex-driven constant reconstruction
(`scratchpad/BCSS25-COMMIT-DERIVATION.md`, checked line-by-line against BCSS25 Lemma 3.1 / Thm 4.2 and
BCIKS20 §7.2) confirms both halves and pins the improved LINEAR exceptional bound
`|S| > d·( 2(m+½)⁵/(3ρ^{3/2})·n + (m+½)/√ρ·(W·n+1) )` — reproducing BCSS25 Thm 4.2 exactly at the
unweighted target `W = 1`, `T = d(γn+1)`.

**⚑ The bits this WOULD buy — CONDITIONAL on the residual below, which is NOT discharged.** Recomputed
with the improved linear `ε_C`,
composed through ethSTARK eq. (20), optimized over `m ≥ 3`: the deployed wrap moves **`~64 → ~71`
(+7 bits)**, the leaf `~70 → ~72` (+1.7), the outer `~66 → ~71` (+5.5) — **NOT the `+17…+31`** the
naive `log₂|D⁽⁰⁾|` estimate suggested. Two reasons the raw improvement is capped: (i) once `ε_C` clears
the query column, the `min` in eq. (20) is set by `ζ − s·log₂ α ≈ 72`, so the composed bits saturate
at the query ceiling; (ii) the arity-8 fold is a degree-`7` CURVE, and the public curve theorem
(BCSS25 Thm 4.2) requires the multiplicity parameter `m = 2h` where the binary line (Thm 1.5) allows
`m = h`, inflating the `(m+½)⁵` constant. The win is real, low-rate-robust, and modest.

**What is mechanized here.** BCIKS20 **Lemma 7.5** — the load-bearing, `[Sta25]`-free heart of the
transfer — in full, kernel-clean, `sorry`-free, over an arbitrary finite domain and field. Its two
pieces:

1. `curveAgree_forces_pointwise` — the polynomial-roots core: if the curve of `u` and the curve of `v`
   agree at a point `x` for MORE than `l` (= the curve degree) challenges `z`, then `u` and `v` agree
   at `x` in EVERY coordinate. (`∑_j zʲ (uⱼ x − vⱼ x)` is a degree-`≤ l` polynomial in `z` with `> l`
   roots, hence zero.) This is the whole reason weighting transfers — and it is a two-line polynomial
   fact, not an unreadable citation.
2. `weighting_transfer_double_count` — the double-count inequality that IS Lemma 7.5:
   `α · |S′| ≤ W(D′) · |S′| + (W_tot − W(D′)) · l`, where `W` is any non-negative weight measure on the
   domain, `D′` is the correlated-agreement domain, and the hypothesis is that at every `z ∈ S′` the
   weighted agreement of the two curves is `≥ α`. Rearranged (`weighting_transfer_bound`) this is
   BCIKS20's `µ(D′) ≥ α − l/(|S′| − l)`.
3. **NEW (2026-07-16)** — BCIKS20 **Lemma 7.6** (§5): `weighting_transfer_rounded`, the grid rounding
   that REMOVES 7.5's loss for denominator-bounded weights, giving `µ(D′) ≥ α` EXACTLY. This file
   previously proved only the lossy 7.5 and asserted the rounding in a docstring. This is the FRI-
   specific step — precisely where Cor 4.4's arbitrary real weights would need `[Sta25]`'s Thm 4.3.

**Anti-mirror check (the generalization recovers the published instance).** `weighting_transfer_rounded`'s
threshold `|S′| ≥ N·l + l = l·(N+1)` with `N = W·n` is `BCSS25-COMMIT-DERIVATION.md`'s (3.3)
`|S′| ≥ Wnd + d = d(Wn+1)` verbatim (`d` = curve degree = our `l`), and its conclusion `µ(D′) ≥ α` is
that document's (3.4). At the FRI round `i`, `W·n = |D⁽⁰⁾|`, so the threshold is `(|D⁽⁰⁾|+1)·l` — the
number this header quotes. The constant is READ OFF the source, not reverse-engineered to close a proof.

**Mutation canary (2026-07-16).** Both load-bearing pieces of Lemma 7.6 were broken and the file WENT
RED, then restored: (i) weakening the threshold `N·l + l ≤ |S′|` to `l < |S′|` — 4 errors; (ii)
weakening the strictness hypothesis `0 < α` to `0 ≤ α` — 4 errors. The `α > 0` is not decoration: it is
what makes the loss STRICTLY sub-grid-step, which is the whole rounding argument.

**⚑⚑ TWO CORRECTIONS PAID FOR ON 2026-07-16, both against this file's own earlier claims.**

**(1) `CoCurvilinearity` was VACUOUS — the residual was a mirror.** The `Prop` quantified `∃ v, …` over
ARBITRARY words `v`, with the codeword constraint living only in a docstring aside ("each `vⱼ` a
codeword of the RS code, *tracked by the caller*"). Nothing tracked it. Taking `v := u` proves the
statement outright — `coCurvilinearity_unconstrained_is_vacuous` (§4) is that six-line proof. So
"discharging" the residual as stated would have earned **zero bits**: the composed theorem would hand
back `v = u`, `D′ = univ`, i.e. `u` agrees with ITSELF everywhere — no proximity to the code asserted.
The header advertised "a real `Prop` with a CONCRETE FALSIFIER, explicitly NOT `:= True`"; the
advertised falsifier ("any `(u,v)` whose curves fail to agree") refutes the MATRIX of an existential,
not the existential. **FIXED**: `CoCurvilinearity` now carries `∀ j ≤ l, IsRSCodeword pt k (v j)`, and
non-vacuity is PROVED, not asserted — `coCurvilinearity_has_a_falsifier` exhibits a `u` at which the
`Prop` is FALSE. The two teeth bracket it: drop the codeword constraint and it is a theorem; keep it
and it is refutable.

**(2) The residual is public but MUCH larger than "~15pp of BCSS25 §3".** Read against the primary
source, BCSS25 §3.2 does **not** prove Step 4. It opens: *"The following is a brief summary of the
steps from **[BCI⁺20, Section 5]**… the underlying field is the field of rational functions
`K = 𝔽_q(Z)`, and the required finite extension is an **algebraic function field**, which makes
concrete computations **quite technical**."* And Step 4 itself: *"Reaching this conclusion is **the
major part of the proof, comprising sections 5.2.5 – 5.2.7 as well as Appendix A of [BCI⁺20]**."*
BCSS25 §3.2's own contribution is only the BOOKKEEPING — tightening `|S| > 2D_X D_Y³ D_Z` to
`|S| > 2D_X D_Y² D_Z + (γn+1)·D_Y`. **The `[Sta25]`-free headline SURVIVES** (BCI⁺20 is public, eprint
2020/654), but the obligation is a Hensel lift over an algebraic function field, not 15 pages of
bookkeeping.

**The honest residual, restated:**

> *mechanize BCI⁺20 §5.2.5–5.2.7 + Appendix A (the Hensel lift over the algebraic function field
> `K[X,Y]/H(X,Y)`, `K = 𝔽_q(Z)`) to obtain Step-4's co-curvilinear `S′`, PLUS BCSS25 §3.2's improved
> bookkeeping so that `S′` clears Lemma 7.6's threshold `|S′| ≥ M·|D|·l + l = (|D⁽⁰⁾| + 1)·l`.*

That obligation names no `[Sta25]` and no `[Hab25]`. It is public, and it is large.

**The Mathlib gap, scoped (2026-07-16), because feasibility is part of the answer.** Mathlib at the
pinned rev has **no error-correcting code theory at all** — no Reed–Solomon, no linear codes, no
minimum distance, no Johnson bound, no list decoding (hence `IsRSCodeword` is defined here from the
polynomial library). For the Guruswami–Sudan layer: bivariate polynomials EXIST
(`Polynomial.Bivariate`, `MvPolynomial`, `equivMvPolynomial`) and the interpolation-by-counting step is
nearly free (`LinearMap.ker_ne_bot_of_finrank_lt` is literally it, with `MvPolynomial.basisMonomials`);
`RatFunc F` is well developed, so `K = 𝔽_q(Z)` is available. But **weighted degree has a definition and
no API** (`MvPolynomial.weightedTotalDegree` has four lemmas; no `_add_le`, no `_mul_le` — and the GS
degree bound IS a statement about weighted degree of products); **bivariate multiplicity does not exist**
(no multivariate Hasse derivative, no `rootMultiplicity` off the univariate case, no MvPolynomial Taylor
shift); and **bivariate root extraction is unbuilt**. The GS interpolant layer alone scopes at
**~3000–6000 lines**. The Hensel lift over an algebraic function field sits ON TOP of that and is not
scoped here. **This is a multi-month-to-paper job, not a week.**

**⚑ The bits are NOT earned.** `weighting_transfer_bound` never carried `CoCurvilinearity` as a
hypothesis (it is and always was a theorem); the consumer is `weighted_agreement_of_coCurvilinear`. The
`~61 → ~68` (our fixed-`bciksM` accounting) / `64 → 71` (m-optimized) remains **unbanked**, and
`FriLedger`'s column is untouched. What this pass banks is smaller and real: **Lemma 7.6 is now
mechanized** (§5) — previously the file proved only the lossy Lemma 7.5 and asserted the grid rounding
in prose. That closes the FRI-specific half at the Lean level: given `CoCurvilinearity`, grid weights
now yield `µ(D′) ≥ α` EXACTLY (`exact_weighted_agreement_of_coCurvilinear`), which is the shape
BCIKS20 Lemma 8.2 consumes.

`#assert_axioms` is blind to hypotheses: `weighted_agreement_of_coCurvilinear` and
`exact_weighted_agreement_of_coCurvilinear` carry `CoCurvilinearity` exactly because that is the
residual, and the axiom check does not see it. **Axiom-clean ≠ hypothesis-free.**
-/

namespace Dregg2.Circuit.FriWeightingTransfer

open Polynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## §1. The curve of a word, and the polynomial that witnesses pointwise agreement. -/

/-- **The degree-`l` curve of a word family.** `curve l a z x = ∑_{j ≤ l} zʲ · aⱼ(x)` — the arity-
`(l+1)` batch/fold of the words `a₀,…,a_l` at challenge `z`, evaluated at the domain point `x`. At
`l = 1` this is the affine line `a₀(x) + z·a₁(x)`; at the deployed arity-8 fold it is the degree-`7`
moment curve (`l = 7`). `a : ℕ → ι → F`, junk above `l` is never read. -/
def curve (l : ℕ) (a : ℕ → ι → F) (z : F) (x : ι) : F :=
  ∑ j ∈ Finset.range (l + 1), z ^ j * a j x

/-- **The pointwise difference polynomial.** `curveDiff l u v x = ∑_{j ≤ l} C(uⱼ x − vⱼ x) · Xʲ` — the
degree-`≤ l` polynomial in the challenge whose evaluation at `z` is `curve u z x − curve v z x`. Its
roots are exactly the challenges at which the two curves agree at `x`. -/
noncomputable def curveDiff (l : ℕ) (u v : ℕ → ι → F) (x : ι) : F[X] :=
  ∑ j ∈ Finset.range (l + 1), C (u j x - v j x) * X ^ j

theorem curveDiff_eval (l : ℕ) (u v : ℕ → ι → F) (x : ι) (z : F) :
    (curveDiff l u v x).eval z = curve l u z x - curve l v z x := by
  simp only [curveDiff, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, curve,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem curveDiff_natDegree_le (l : ℕ) (u v : ℕ → ι → F) (x : ι) :
    (curveDiff l u v x).natDegree ≤ l := by
  refine natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

theorem curveDiff_coeff (l : ℕ) (u v : ℕ → ι → F) (x : ι) {j : ℕ} (hj : j ≤ l) :
    (curveDiff l u v x).coeff j = u j x - v j x := by
  rw [curveDiff, finsetSum_coeff, Finset.sum_eq_single j]
  · simp [sub_mul, coeff_C_mul, coeff_X_pow]
  · intro i _ hij
    simp [sub_mul, coeff_C_mul, coeff_X_pow, Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h

/-- **THE POLYNOMIAL-ROOTS CORE — the whole reason weighting transfers.** If the curves of `u` and `v`
agree at the point `x` for MORE than `l` distinct challenges (`l` = curve degree), then `u` and `v`
agree at `x` in every coordinate `j ≤ l`. Because `curveDiff` has degree `≤ l`, `> l` roots forces it
to be the zero polynomial, and its coefficients are exactly the coordinate differences.

This is BCIKS20 Lemma 7.5's opening move ("`w(x,·)` and `w̃(x,·)` are degree-`≤ l` polynomials in `z`,
so if they agree on more than `l` values they are identical"), and it is entirely elementary — no
`[Sta25]`, no correlated-agreement machinery. -/
theorem curveAgree_forces_pointwise (l : ℕ) (u v : ℕ → ι → F) (x : ι)
    (Z : Finset F) (hZ : l < (Z.filter (fun z => curve l u z x = curve l v z x)).card) :
    ∀ j ≤ l, u j x = v j x := by
  classical
  -- The agreement challenges are roots of `curveDiff`.
  by_cases hne : curveDiff l u v x = 0
  · intro j hj
    have := curveDiff_coeff l u v x hj
    rw [hne, coeff_zero] at this
    exact sub_eq_zero.mp this.symm
  · -- A nonzero degree-`≤ l` polynomial has `≤ l` roots, contradicting `> l` agreement challenges.
    exfalso
    have hsub : Z.filter (fun z => curve l u z x = curve l v z x)
        ⊆ (curveDiff l u v x).roots.toFinset := by
      intro z hz
      simp only [Finset.mem_filter] at hz
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, curveDiff_eval]
      rw [hz.2, sub_self]
    have hcard : (Z.filter (fun z => curve l u z x = curve l v z x)).card ≤ l := by
      calc (Z.filter (fun z => curve l u z x = curve l v z x)).card
          ≤ (curveDiff l u v x).roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card (curveDiff l u v x).roots := (curveDiff l u v x).roots.toFinset_card_le
        _ ≤ (curveDiff l u v x).natDegree := card_roots' _
        _ ≤ l := curveDiff_natDegree_le l u v x
    omega

/-! ## §2. The weighted double count — BCIKS20 Lemma 7.5 in full. -/

/-- **The correlated-agreement domain** `D′ = {x | ∀ j ≤ l, uⱼ(x) = vⱼ(x)}` — the points where the
whole interleaved word matches the codeword tuple. This is what weighted correlated agreement lower-
bounds (in `µ`-measure). -/
def coAgreeDomain (l : ℕ) (u v : ℕ → ι → F) : Finset ι :=
  Finset.univ.filter (fun x => ∀ j ≤ l, u j x = v j x)

/-- The agreement set at a challenge `z`: the domain points where the two curves coincide. -/
def agreeSet (l : ℕ) (u v : ℕ → ι → F) (z : F) : Finset ι :=
  Finset.univ.filter (fun x => curve l u z x = curve l v z x)

/-- Total weight of a finset under a weight function `µ`. -/
def wsum (μ : ι → ℝ) (A : Finset ι) : ℝ := ∑ x ∈ A, μ x

theorem wsum_nonneg {μ : ι → ℝ} (hμ : ∀ x, 0 ≤ μ x) (A : Finset ι) : 0 ≤ wsum μ A :=
  Finset.sum_nonneg (fun x _ => hμ x)

theorem wsum_le_total {μ : ι → ℝ} (hμ : ∀ x, 0 ≤ μ x) (A : Finset ι) :
    wsum μ A ≤ wsum μ Finset.univ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun x _ _ => hμ x)

/-- **THE DOUBLE COUNT — BCIKS20 Lemma 7.5, mechanized.** Let `µ ≥ 0` be any weight function on the
domain, `l` the curve degree, and `S′` a challenge set with `|S′| > l`. If at EVERY `z ∈ S′` the two
curves have weighted agreement `≥ α` (`wsum µ (agreeSet z) ≥ α`), then

  `α · |S′| ≤ W(D′) · |S′| + (W_tot − W(D′)) · l` ,

where `W(D′) = wsum µ (coAgreeDomain)` and `W_tot = wsum µ univ`.

*Proof (BCIKS20 §7.2, verbatim structure).* Double-count `∑_{z ∈ S′} W(agreeSet z)` by swapping to
sum over domain points: each `x` contributes `µ(x) · |{z ∈ S′ : x ∈ agreeSet z}|`. A point in `D′`
lies in every `agreeSet z` (its curves agree at all `z`), contributing `µ(x)·|S′|`. A point NOT in
`D′` lies in at most `l` of them — `curveAgree_forces_pointwise`, since `|S′| > l` agreement
challenges would force it into `D′`. Summing gives the bound; the hypothesis `≥ α` gives the LHS. ∎

No `[Sta25]`: the only non-elementary input is the polynomial-roots count of §1. -/
theorem weighting_transfer_double_count (l : ℕ) (u v : ℕ → ι → F)
    (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (S' : Finset F) (hS' : l < S'.card) (α : ℝ)
    (hagree : ∀ z ∈ S', α ≤ wsum μ (agreeSet l u v z)) :
    α * S'.card ≤ wsum μ (coAgreeDomain l u v) * S'.card
      + (wsum μ Finset.univ - wsum μ (coAgreeDomain l u v)) * l := by
  classical
  set D' := coAgreeDomain l u v with hD'
  -- For each x, the number of challenges in S' whose curves agree at x.
  set cnt : ι → ℕ := fun x => (S'.filter (fun z => curve l u z x = curve l v z x)).card with hcnt
  -- (1) Sum of weighted agreements = weighted sum of counts (double count / swap).
  have hswap : ∑ z ∈ S', wsum μ (agreeSet l u v z) = ∑ x, μ x * cnt x := by
    simp only [wsum, agreeSet]
    -- ∑_{z∈S'} ∑_{x ∈ filter} μ x  =  ∑_x μ x * card (filter over z)
    have hinner : ∀ z ∈ S',
        (∑ x ∈ Finset.univ.filter (fun x => curve l u z x = curve l v z x), μ x)
          = ∑ x, (if curve l u z x = curve l v z x then μ x else 0) := by
      intro z _; rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [hcnt]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- (2) LHS lower bound: each term ≥ α, |S'| terms.
  have hlow : α * S'.card ≤ ∑ z ∈ S', wsum μ (agreeSet l u v z) := by
    calc α * S'.card = ∑ _z ∈ S', α := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ z ∈ S', wsum μ (agreeSet l u v z) := Finset.sum_le_sum hagree
  -- (3) Per-point count bound: |S'| on D', ≤ l off D'.
  have hcntD' : ∀ x ∈ D', cnt x = S'.card := by
    intro x hx
    simp only [hcnt]
    have hall : ∀ z ∈ S', curve l u z x = curve l v z x := by
      intro z _
      simp only [hD', coAgreeDomain, Finset.mem_filter] at hx
      simp only [curve]
      exact Finset.sum_congr rfl (fun j hj => by rw [hx.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))])
    rw [Finset.filter_true_of_mem hall]
  have hcntOff : ∀ x ∉ D', cnt x ≤ l := by
    intro x hx
    by_contra hgt
    push_neg at hgt
    simp only [hcnt] at hgt
    apply hx
    simp only [hD', coAgreeDomain, Finset.mem_filter, Finset.mem_univ, true_and]
    exact curveAgree_forces_pointwise l u v x S' hgt
  -- (4) Weighted count ≤ W(D')·|S'| + W(D'ᶜ)·l.
  have hupper : ∑ x, μ x * cnt x
      ≤ wsum μ D' * S'.card + wsum μ D'ᶜ * l := by
    rw [← Finset.sum_add_sum_compl D' (fun x => μ x * cnt x)]
    gcongr ?_ + ?_
    · -- on D': cnt = |S'|
      simp only [wsum, Finset.sum_mul]
      refine Finset.sum_le_sum (fun x hx => ?_)
      exact le_of_eq (by rw [hcntD' x hx])
    · -- off D': cnt ≤ l, μ ≥ 0
      simp only [wsum, Finset.sum_mul]
      refine Finset.sum_le_sum (fun x hx => ?_)
      have hxoff : x ∉ D' := (Finset.mem_compl.mp hx)
      have hcl : (cnt x : ℝ) ≤ (l : ℝ) := by exact_mod_cast hcntOff x hxoff
      exact mul_le_mul_of_nonneg_left hcl (hμ x)
  -- (5) Assemble, and rewrite W(D'ᶜ) = W_tot − W(D').
  have hcompl : wsum μ D'ᶜ = wsum μ Finset.univ - wsum μ D' := by
    simp only [wsum]
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_compl_add_sum D' μ
  calc α * S'.card ≤ ∑ z ∈ S', wsum μ (agreeSet l u v z) := hlow
    _ = ∑ x, μ x * cnt x := hswap
    _ ≤ wsum μ D' * S'.card + wsum μ D'ᶜ * l := hupper
    _ = wsum μ D' * S'.card + (wsum μ Finset.univ - wsum μ D') * l := by rw [hcompl]

/-- **BCIKS20 Lemma 7.5, the rearranged form** — `µ(D′) ≥ α − l/(|S′| − l)` (unnormalized `W`,
`W_tot ≤ 1` scaling suppressed). From the double count: `W(D′)·(|S′| − l) ≥ α·|S′| − W_tot·l`, so
`W(D′) ≥ α − (W_tot − α)·l/(|S′| − l)`. This is the statement BCIKS20's Lemma 7.6 rounds to
`µ(D′) ≥ α` once `|S′| ≥ M|D|l + l`. -/
theorem weighting_transfer_bound (l : ℕ) (u v : ℕ → ι → F)
    (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (S' : Finset F) (hS' : l < S'.card) (α : ℝ)
    (hagree : ∀ z ∈ S', α ≤ wsum μ (agreeSet l u v z)) :
    wsum μ (coAgreeDomain l u v) * (S'.card - l)
      ≥ α * S'.card - wsum μ Finset.univ * l := by
  have h := weighting_transfer_double_count l u v μ hμ S' hS' α hagree
  have hcard : (l : ℝ) ≤ S'.card := by exact_mod_cast le_of_lt hS'
  nlinarith [h]

/-! ## §3. The residual — `CoCurvilinearity`, stated so that it is NOT vacuous.

`weighting_transfer_bound` is the whole transfer. What it CONSUMES is the co-curvilinear set `S′`: a
large challenge set on which the proximates lie on the curve of a single **codeword** tuple `v`.

**⚑ The word "codeword" is the entire content, and an earlier version of this file dropped it.** See
`coCurvilinearity_unconstrained_is_vacuous` below: with `v` ranging over ARBITRARY words, the `Prop` is
proved by `v := u` and asserts nothing whatsoever. The `∃ v` shape is what hides this — the "falsifier"
the earlier docstring advertised ("any `(u,v)` whose curves fail to agree") refutes the MATRIX of the
existential, not the existential; exhibiting a bad `v` is no refutation when the statement gets to
choose `v`. The teeth in §4 pin both halves: the unconstrained shape is a theorem (vacuous), and the
codeword-constrained shape is FALSE at a concrete instance (has real content). -/

/-- **RS codeword.** `w` is the evaluation on the domain (embedded by `pt`) of a polynomial of degree
`< k`. This is BCSS25's `C = RS[F_q, D, k]`. Mathlib has NO coding theory (no RS code, no linear code,
no minimum distance, no list decoding), so this predicate is defined here from the polynomial library. -/
def IsRSCodeword (pt : ι → F) (k : ℕ) (w : ι → F) : Prop :=
  ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ x, w x = p.eval (pt x)

/-- **`CoCurvilinearity`** — the structural fact the Guruswami–Sudan argument delivers, stated over the
exact quantities the weighting transfer needs, WITH the codeword constraint that carries its content.

There is a tuple `v : ℕ → ι → F` with **every `vⱼ` an RS codeword** and a challenge set `S′` with
`|S′| > l` such that on all of `S′` the two curves have weighted agreement `≥ α`. This is BCSS25 §3.2
Step 4's conclusion — `P(X,Z) = v₀(X) + Z·v₁(X)` with `deg_X P ≤ k` (the `vⱼ` ARE codewords, verbatim)
and `P(X,z) = P_z(X)` for `z ∈ S′` — fed through weighted agreement.

Non-vacuity is PROVED, not asserted: `coCurvilinearity_has_a_falsifier` exhibits a `u` at which this
`Prop` is FALSE. Drop `hv` and it becomes a theorem (`coCurvilinearity_unconstrained_is_vacuous`). -/
def CoCurvilinearity (pt : ι → F) (k l : ℕ) (u : ℕ → ι → F) (μ : ι → ℝ) (α : ℝ) : Prop :=
  ∃ (v : ℕ → ι → F) (S' : Finset F),
    (∀ j ≤ l, IsRSCodeword pt k (v j)) ∧
    l < S'.card ∧ ∀ z ∈ S', α ≤ wsum μ (agreeSet l u v z)

/-- **THE REDUCTION, COMPOSED — weighted correlated agreement from co-curvilinearity ALONE.** Given
`CoCurvilinearity`, there is a tuple of **RS codewords** `v` whose correlated-agreement domain `D′`
carries weighted measure at least `α − (W_tot − α)·l/(|S′| − l)`. `[Sta25]` appears NOWHERE:
`curveAgree_forces_pointwise` (polynomial roots) and `weighting_transfer_double_count` (double count)
are the only inputs.

The codeword conclusion is what the caller needs and what makes this say something: `D′` is now a
correlated-agreement domain with the CODE, not with an arbitrary re-authored word.
`#assert_axioms` is blind to the `CoCurvilinearity` hypothesis — that hypothesis IS the residual. -/
theorem weighted_agreement_of_coCurvilinear (pt : ι → F) (k l : ℕ) (u : ℕ → ι → F)
    (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) (α : ℝ)
    (hco : CoCurvilinearity pt k l u μ α) :
    ∃ (v : ℕ → ι → F) (S' : Finset F), (∀ j ≤ l, IsRSCodeword pt k (v j)) ∧ l < S'.card ∧
      wsum μ (coAgreeDomain l u v) * (S'.card - l) ≥ α * S'.card - wsum μ Finset.univ * l := by
  obtain ⟨v, S', hv, hcard, hagree⟩ := hco
  exact ⟨v, S', hv, hcard, weighting_transfer_bound l u v μ hμ S' hcard α hagree⟩

/-! ## §4. Anti-vacuity — the transfer is not empty, and its hypothesis is not free.

A transfer theorem whose agreement hypothesis is unsatisfiable, or whose `S′` never exceeds `l`, would
prove nothing. Four teeth — two for the transfer, two for the residual `Prop` itself. -/

/-- **⚑ THE TOOTH THAT CAUGHT A MIRROR — the codeword constraint IS the content.** Strip `IsRSCodeword`
from `CoCurvilinearity` and what remains is a THEOREM: take `v := u`, every curve agrees with itself
everywhere, and the weighted agreement is `W_tot ≥ α` for free. So the unconstrained shape is provable
outright and earns exactly zero bits — `weighted_agreement_of_coCurvilinear` would hand back `v = u`
and `D′ = univ`, a statement about `u`'s agreement with ITSELF, which says nothing about proximity to
the code.

This file previously carried that unconstrained shape as its named residual, advertised as "a real
`Prop` with a concrete falsifier, NOT `:= True`". It was not `:= True`; it was worse, because it looked
like work. `:= True` at least announces itself. -/
theorem coCurvilinearity_unconstrained_is_vacuous (l : ℕ) (u : ℕ → ι → F) (μ : ι → ℝ) (α : ℝ)
    (hα : α ≤ wsum μ Finset.univ) (S₀ : Finset F) (hS₀ : l < S₀.card) :
    ∃ (v : ℕ → ι → F) (S' : Finset F),
      l < S'.card ∧ ∀ z ∈ S', α ≤ wsum μ (agreeSet l u v z) := by
  refine ⟨u, S₀, hS₀, fun z _ => ?_⟩
  have : agreeSet l u u z = Finset.univ := by
    rw [agreeSet, Finset.filter_true_of_mem (fun x _ => rfl)]
  rw [this]; exact hα

/-- **⚑ THE FALSIFIER — with the codeword constraint restored, `CoCurvilinearity` has real content.**
At the trivial code `k = 0` (whose only codeword is `0`) against the word `u₀ ≡ 1`, `u₁ ≡ 0` with
uniform weight and `α = 1`, the `Prop` is FALSE: every codeword curve is identically `0`, the input
curve is identically `1`, so every agreement set is EMPTY and carries weight `0 < 1 = α`.

This is the concrete falsifier the previous statement claimed to have and did not. It is what
distinguishes a residual from a mirror: a `Prop` you can be WRONG about. -/
theorem coCurvilinearity_has_a_falsifier (pt : Fin 1 → F) :
    ¬ CoCurvilinearity pt 0 1 (fun j (_ : Fin 1) => if j = 0 then (1:F) else 0)
        (fun _ => (1:ℝ)) 1 := by
  rintro ⟨v, S', hv, hcard, hag⟩
  obtain ⟨z, hz⟩ : ∃ z, z ∈ S' := Finset.card_pos.mp (by omega) |>.imp (fun _ h => h)
  have hv0 : ∀ j, j ≤ 1 → ∀ x, v j x = 0 := by
    intro j hj x
    obtain ⟨p, hdeg, hp⟩ := hv j hj
    rw [Nat.cast_zero] at hdeg
    have : p = 0 := degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hdeg)
    rw [hp x, this, eval_zero]
  have hempty : agreeSet 1 (fun j (_ : Fin 1) => if j = 0 then (1:F) else 0) v z = ∅ := by
    ext x
    simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    simp only [curve, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hv0 0 (by omega) x, hv0 1 (by omega) x]
    norm_num
  have := hag z hz
  rw [hempty] at this
  simp [wsum] at this
  linarith

/-- **The transfer FIRES on the trivial-but-real instance `u = v`.** When the words already equal the
codewords, every curve agrees everywhere, `D′` is the whole domain, and the bound is tight. This shows
`weighting_transfer_double_count` is not vacuous (its hypothesis is satisfiable) and its conclusion is
sharp at the top. -/
theorem transfer_fires_at_equal (l : ℕ) (u : ℕ → ι → F) (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (S' : Finset F) (hS' : l < S'.card) :
    coAgreeDomain l u u = Finset.univ ∧
      ∀ z ∈ S', wsum μ Finset.univ ≤ wsum μ (agreeSet l u u z) := by
  refine ⟨?_, ?_⟩
  · rw [coAgreeDomain, Finset.filter_true_of_mem (fun x _ => fun j _ => rfl)]
  · intro z _
    have : agreeSet l u u z = Finset.univ := by
      rw [agreeSet, Finset.filter_true_of_mem (fun x _ => rfl)]
    rw [this]

/-- **The `|S′| > l` hypothesis is LOAD-BEARING — a both-truth tooth.** At `|S′| = l` (agreement on
exactly `l` challenges, one short) the pointwise conclusion FAILS: a point can sit on the curves'
agreement for `l` challenges without the coordinates matching (the difference polynomial has degree
`l` and is allowed `l` roots). Concretely at `l = 1` (the affine line): `u₀ = v₀` everywhere and
`u₁ ≠ v₁` at some `x`, then the line agrees at `x` for exactly one `z` (`z = 0`), yet `u₁ x ≠ v₁ x`.
So the strict `l <` in `curveAgree_forces_pointwise` cannot be weakened to `≤`. -/
theorem strict_card_needed :
    ∃ (u v : ℕ → Fin 1 → F) (x : Fin 1) (z : F),
      curve 1 u z x = curve 1 v z x ∧ ¬ (∀ j ≤ 1, u j x = v j x) := by
  refine ⟨fun _ _ => 0, fun j _ => if j = 1 then 1 else 0, 0, 0, ?_, ?_⟩
  · simp [curve, Finset.sum_range_succ]
  · intro h
    have := h 1 (le_refl 1)
    simp at this

/-! ## §5. BCIKS20 Lemma 7.6 — the grid rounding that REMOVES Lemma 7.5's loss.

Lemma 7.5 (§2) is lossy: it gives `µ(D′) ≥ α − l/(|S′| − l)`, and that loss is strictly positive for
every finite `S′`. **This is exactly where BCSS25 needs its `[Sta25]`-backed Theorem 4.3** for
Corollary 4.4's arbitrary real weights `w(x) ∈ [0,1]` — such weights admit no grid, so the loss cannot
be rounded away (`BCSS25-COMMIT-DERIVATION.md` §3.3).

**FRI's weights are not arbitrary.** BCIKS20 Lemma 8.2's `µ⁽ⁱ⁾` are subtree-acceptance probabilities
with common denominator, so every value of `µ` lies on the grid `(1/N)ℤ` with `N = W·|D|`. On a grid,
a strict inequality within `1/N` ROUNDS UP to equality — and the loss vanishes. That is Lemma 7.6, and
mechanizing it here is what makes the FRI-application claim `[Sta25]`-free at the Lean level rather
than in prose: previously this file asserted the rounding in a docstring and proved only the lossy 7.5.

The threshold `|S′| ≥ N·l + l = l·(W|D| + 1)` is (3.3) of the derivation doc, and it is LOAD-BEARING —
see the canary note in the header. -/

/-- A real on the grid `(1/N)ℤ` — the values a denominator-`N` weight measure can take. -/
def OnGrid (N : ℕ) (r : ℝ) : Prop := ∃ i : ℤ, r = (i : ℝ) / (N : ℝ)

omit [Fintype ι] in
/-- Weighted sums of grid weights stay on the grid. -/
theorem onGrid_wsum {N : ℕ} {μ : ι → ℝ} (h : ∀ x, OnGrid N (μ x)) (A : Finset ι) :
    OnGrid N (wsum μ A) := by
  classical
  induction A using Finset.induction with
  | empty => exact ⟨0, by simp [wsum]⟩
  | insert x s hx ih =>
      obtain ⟨i, hi⟩ := h x
      obtain ⟨j, hj⟩ := ih
      refine ⟨i + j, ?_⟩
      rw [wsum, Finset.sum_insert hx, ← wsum, hi, hj]
      push_cast; ring

/-- **The rounding step.** Two points of the grid `(1/N)ℤ` separated by strictly less than one grid
step are ordered: `b − 1/N < a` forces `b ≤ a`. (`a = i/N`, `b = j/N`, `j − 1 < i` in `ℤ` ⟹ `j ≤ i`.) -/
theorem grid_round {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : OnGrid N a) (hb : OnGrid N b) (h : b - 1 / (N:ℝ) < a) : b ≤ a := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  subst hi hj
  rw [div_sub_div_same, div_lt_div_iff_of_pos_right hNR] at h
  have hz : ((j - 1 : ℤ) : ℝ) < ((i : ℤ) : ℝ) := by push_cast; linarith
  have : (j - 1 : ℤ) < i := by exact_mod_cast hz
  have hji : (j : ℤ) ≤ i := by omega
  have : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
  gcongr

/-- **BCIKS20 LEMMA 7.6, MECHANIZED — the transfer with NO loss, for grid weights.** If `µ` takes
values on `(1/N)ℤ`, `α` is on the grid, `W_tot ≤ 1`, `α > 0`, `l > 0`, and the challenge set clears
`|S′| ≥ N·l + l`, then weighted agreement `≥ α` at every `z ∈ S′` gives `µ(D′) ≥ α` — EXACTLY, with
Lemma 7.5's `l/(|S′| − l)` loss rounded away.

*Proof.* Lemma 7.5 gives `W(D′)·(|S′|−l) ≥ α|S′| − W_tot·l`, i.e. `W(D′) ≥ α − l(W_tot−α)/(|S′|−l)`.
The threshold gives `|S′| − l ≥ N·l`, so `l/(|S′|−l) ≤ 1/N`; and `W_tot − α < 1` (as `W_tot ≤ 1`,
`α > 0`) makes the loss STRICTLY less than `1/N`. So `W(D′) > α − 1/N` with both `W(D′)` and `α` on
the grid — and `grid_round` closes it. The strictness is why `α > 0` is a hypothesis and not decoration.

No `[Sta25]`: the inputs are Lemma 7.5 (§2) and integer arithmetic. -/
theorem weighting_transfer_rounded (l : ℕ) (hl : 0 < l) (u v : ℕ → ι → F)
    (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (N : ℕ) (hN : 0 < N) (hgrid : ∀ x, OnGrid N (μ x))
    (α : ℝ) (hα : 0 < α) (hgridα : OnGrid N α)
    (htot : wsum μ Finset.univ ≤ 1)
    (S' : Finset F) (hS' : (N : ℝ) * l + l ≤ (S'.card : ℝ))
    (hagree : ∀ z ∈ S', α ≤ wsum μ (agreeSet l u v z)) :
    α ≤ wsum μ (coAgreeDomain l u v) := by
  set W := wsum μ (coAgreeDomain l u v) with hW
  set T := wsum μ (Finset.univ : Finset ι) with hT
  set c := (S'.card : ℝ) with hc
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hlR : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  have hNl : (N:ℝ) * l ≤ c - l := by linarith
  have hcl : (0:ℝ) < c - l := lt_of_lt_of_le (by positivity) hNl
  have hlc : (l:ℝ) < c := by nlinarith
  have hcard : l < S'.card := by rw [hc] at hlc; exact_mod_cast hlc
  -- Lemma 7.5, the lossy form.
  have hb := weighting_transfer_bound l u v μ hμ S' hcard α hagree
  -- The threshold `|S'| ≥ l(N+1)` is what makes the loss strictly sub-grid-step.
  have hlNpos : (0:ℝ) < (l:ℝ) * N := by positivity
  have hkey2 : (T - α) * ((l:ℝ) * N) < c - l := by
    rcases le_or_gt (T - α) 0 with h | h
    · nlinarith [mul_nonneg (neg_nonneg.mpr h) (le_of_lt hlNpos)]
    · nlinarith [mul_lt_mul_of_pos_right (show T - α < 1 by linarith) hlNpos]
  have h1 : (α - W) * (c - l) ≤ (T - α) * l := by nlinarith [hb]
  have hkey : (α - W) * (N:ℝ) < 1 := by nlinarith [h1, hkey2, hcl, hNR]
  have hlt : α - 1 / (N:ℝ) < W := by
    have : α - W < 1 / (N:ℝ) := by rw [lt_div_iff₀ hNR]; linarith [hkey]
    linarith
  exact grid_round hN (onGrid_wsum hgrid _) hgridα hlt

/-- **The composed FRI statement — exact weighted correlated agreement with the CODE, `[Sta25]`-free.**
`CoCurvilinearity` (the residual) plus grid weights (which FRI has) gives codewords `v` whose
correlated-agreement domain carries weighted measure `≥ α` EXACTLY. This is the shape BCIKS20 Lemma 8.2
consumes. Everything below `CoCurvilinearity` is now mechanized; `CoCurvilinearity` itself is the
residual, and the header states precisely how large it is. -/
theorem exact_weighted_agreement_of_coCurvilinear (pt : ι → F) (k l : ℕ) (hl : 0 < l)
    (u : ℕ → ι → F) (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (N : ℕ) (hN : 0 < N) (hgrid : ∀ x, OnGrid N (μ x))
    (α : ℝ) (hα : 0 < α) (hgridα : OnGrid N α)
    (htot : wsum μ Finset.univ ≤ 1)
    (hco : ∃ (v : ℕ → ι → F) (S' : Finset F),
      (∀ j ≤ l, IsRSCodeword pt k (v j)) ∧
      (N : ℝ) * l + l ≤ (S'.card : ℝ) ∧ ∀ z ∈ S', α ≤ wsum μ (agreeSet l u v z)) :
    ∃ v : ℕ → ι → F, (∀ j ≤ l, IsRSCodeword pt k (v j)) ∧
      α ≤ wsum μ (coAgreeDomain l u v) := by
  obtain ⟨v, S', hv, hcard, hagree⟩ := hco
  exact ⟨v, hv, weighting_transfer_rounded l hl u v μ hμ N hN hgrid α hα hgridα htot S' hcard hagree⟩

/-! ## §6. Axiom hygiene.

Kernel-clean, `sorry`-free, no `axiom`. `#assert_axioms` is BLIND TO HYPOTHESES:
`weighted_agreement_of_coCurvilinear` carries `CoCurvilinearity` — that is the residual (BCSS25 §3, all
public), not slack the axiom check could catch. The WEIGHTING TRANSFER itself
(`weighting_transfer_double_count`, `weighting_transfer_bound`) carries no such hypothesis: it is a
theorem, and it names no personal communication. -/

#assert_axioms curveDiff_eval
#assert_axioms curveDiff_natDegree_le
#assert_axioms curveDiff_coeff
#assert_axioms curveAgree_forces_pointwise
#assert_axioms weighting_transfer_double_count
#assert_axioms weighting_transfer_bound
#assert_axioms weighted_agreement_of_coCurvilinear
#assert_axioms transfer_fires_at_equal
#assert_axioms strict_card_needed
#assert_axioms coCurvilinearity_unconstrained_is_vacuous
#assert_axioms coCurvilinearity_has_a_falsifier
#assert_axioms onGrid_wsum
#assert_axioms grid_round
#assert_axioms weighting_transfer_rounded
#assert_axioms exact_weighted_agreement_of_coCurvilinear

end Dregg2.Circuit.FriWeightingTransfer
