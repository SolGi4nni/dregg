/-
# Dregg2.Circuit.CorrelatedAgreement.Collinearity — rung L4 (Part C) of the UD-regime
# correlated agreement: degree control + the collinearity double count

Rung L4 of the DAG in `docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md` §6
(Part C = BCIKS20 §4.3.3–4.3.5 + Kopparty 2025 Lemma 2.4/Remark 2.5, p.20–21).
Lean-authored proof over `Polynomial`/`Finset` — there is no Rust AIR here and there must
not be. Everything is generic in the field `F` and the parameters `(n, k, e, m)`; no
deployed constant is baked in.

L4 consumes the `Q` produced by L3.2 (`Dregg2.PS.polishchuk_spielman`, PROVEN): `B = A * Q`
with `sdeg Q ≤ bX − aX` and `Q.natDegree ≤ bZ − aZ`. `Q` and its degree bounds enter as
HYPOTHESES, so this rung is independent of how `Q` was obtained (the sibling L1/L2 lane).

- **L4.1** (`sdeg_le_of_horizontal_lines` / `natDegree_le_of_vertical_lines`) — the plan's
  "high coefficients vanish at more points than their degree" argument, standalone: if every
  horizontal line `Q(X,z)`, `z ∈ S`, has `X`-degree ≤ c and `|S| > deg_Z Q`, then
  `deg_X Q ≤ c` (and the swapped twin). NOTE: with the Cramer-FIXED L3.2 these bounds also
  arrive inside the PS conclusion itself (`sdeg Q ≤ bX − aX`, the plan's `deg_X P ≤ k`), so
  the packaged L4.3 below takes them as hypotheses; the standalone lemmas keep L4 usable
  from any PS variant that yields bare divisibility.
- **L4.2** (`quotient_agrees_on_lines`) — `Q(x,Z) = w(x,Z)` on ≥ `n − deg_X A` domain
  points: cancel `A(x,Z)` in `A(x,Z)·w = B(x,Z) = A(x,Z)·Q(x,Z)` wherever the vertical
  line of `A` is nonzero; `A` vanishes on ≤ `sdeg A` vertical lines.
- **L4.3** (`interleavedClose_of_bw_factorization`, CURVE form; pair wrapper below) —
  `Q = Σ_j Z^j·v_j` with every `v_j = Q.coeff j` of degree < k, hence
  `evalOn pt v_j ∈ RScode pt k`, and comparing `Z`-coefficients on the L4.2 agreement set
  gives SIMULTANEOUS agreement: `interleavedClose (RScode pt k) u (deg_X A)`. (No Lagrange
  interpolation is needed on this route: membership comes from `coeff_natDegree_le_sdeg` +
  the PS degree bound. The `deg_Z Q ≤ M` bound is NOT needed for this direction and is
  deliberately not a hypothesis.)
- **L4.4** (`collinearity_double_count`, CURVE form = Kopparty Lemma 2.4 with loss
  `M/(a−M)`; line case `M = 1` is `collinearity_double_count_pair`) — the collinearity
  double count, INDEPENDENT of L3/Q, hypothesis-free beyond the per-challenge closeness:
  each disagreement point `x` is "repaired" by at most `M = m−1` challenges (the roots of
  the nonzero degree-≤M polynomial `Σ_j (u_j(x)−p_j(x))·Z^j`), and every good challenge
  must repair ≥ `d − e` of the `d` disagreements; double counting gives
  `(a − M)·d ≤ a·e`. The LOSSLESS corollary (`interleavedClose_of_curve_agreement`):
  `(m−1)·(e+1) < a ⟹ d ≤ e` — the un-halved agreement floor `n − e`, phrased in
  `interleavedClose` with the pinned-interface threshold `(m−1)·(r+1) < |Good|`.

Non-vacuity teeth (all over `ZMod 5`): the double count FIRES and its bound is ATTAINED
(the Kopparty Remark 2.5 configuration at `a = 2, e = 1, d = 2`: both sides equal 2), the
lossless threshold is SHARP (the same instance sits at `a = (m−1)(e+1)` exactly and
violates `d ≤ e`), the lossless corollary FIRES with a genuinely-1-far word, the BW
factorization theorem FIRES on a bivariate instance with a genuinely vanishing `A`-line
and a word that disagrees with its codewords exactly there, and the L4.1 degree-control
lemmas FIRE with an exact (not slack) conclusion. `#assert_all_clean` pins every keystone.
-/
import Dregg2.Circuit.CorrelatedAgreement.Scaffolding
import Dregg2.ForMathlib.PolishchukSpielman

namespace Dregg2.Circuit.CorrelatedAgreement

open Polynomial
open scoped Polynomial.Bivariate
open Dregg2.PS

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The power-curve polynomial `Σ_j c_j · Z^j` and its coefficient API -/

/-- The power-curve polynomial `Σ_{j<m} c_j · Z^j` through the values `c : Fin m → F`.
At `m = 2` this is the line `c₀ + Z·c₁`. -/
noncomputable def curvePoly {m : ℕ} (c : Fin m → F) : Polynomial F :=
  ∑ j : Fin m, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

theorem curvePoly_coeff {m : ℕ} (c : Fin m → F) (j : Fin m) :
    (curvePoly c).coeff (j : ℕ) = c j := by
  rw [curvePoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · intro b _ hb
    have hne : (j : ℕ) ≠ (b : ℕ) := Fin.val_injective.ne hb.symm
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem curvePoly_natDegree_le {m : ℕ} (c : Fin m → F) :
    (curvePoly c).natDegree ≤ m - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  have := j.isLt
  omega

theorem curvePoly_eval {m : ℕ} (c : Fin m → F) (z : F) :
    (curvePoly c).eval z = ∑ j : Fin m, c j * z ^ (j : ℕ) := by
  rw [curvePoly, Polynomial.eval_finsetSum]
  simp

/-- The `m = 2` instance is the line `c₀ + Z·c₁` — the shape L5 consumes. -/
theorem curvePoly_pair (a b : F) :
    curvePoly ![a, b] = Polynomial.C a + Polynomial.C b * Polynomial.X := by
  rw [curvePoly, Fin.sum_univ_two]
  simp

/-! ## The two arithmetic endgames (pure ℕ counting) -/

/-- From the double count `a·(d−e) ≤ M·d` extract `(a−M)·d ≤ a·e` —
Kopparty Lemma 2.4's inequality in ℕ-truncated form (no side conditions needed). -/
private theorem double_count_arith {a M d e : ℕ} (h : a * (d - e) ≤ M * d) :
    (a - M) * d ≤ a * e := by
  rcases Decidable.em (d ≤ e) with hde | hde
  · exact Nat.mul_le_mul (Nat.sub_le a M) hde
  · have hde' : e < d := not_le.mp hde
    rcases Decidable.em (a ≤ M) with haM | haM
    · rw [Nat.sub_eq_zero_of_le haM, zero_mul]
      exact Nat.zero_le _
    · have haM' : M < a := not_le.mp haM
      zify [hde'.le, haM'.le] at h ⊢
      nlinarith [h]

/-- LOSSLESS threshold: `(a−M)·d ≤ a·e` and `M·(e+1) < a` force `d ≤ e`. -/
private theorem lossless_arith {a M d e : ℕ} (h : (a - M) * d ≤ a * e)
    (hth : M * (e + 1) < a) : d ≤ e := by
  by_contra hcon'
  have hcon : e < d := not_le.mp hcon'
  have hM : M ≤ a := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * (e + 1) := Nat.mul_le_mul_left M (by omega)
      _ ≤ a := hth.le
  zify [hM] at h
  zify at hth hcon
  nlinarith [h, hth, hcon,
    mul_le_mul_of_nonneg_left (show (e : ℤ) + 1 ≤ d by linarith)
      (show (0 : ℤ) ≤ (a : ℤ) - M by linarith)]

/-! ## L4.4 — the collinearity double count (Kopparty 2025 Lemma 2.4, p.20)

INDEPENDENT of L3/Q, and independent even of codeword membership: pure counting over
functions. `E` = the simultaneous-disagreement set (`|E| = d`); for `x ∈ E` the challenge
polynomial `φ_x(Z) = Σ_j (u_j(x) − p_j(x))·Z^j` is NONZERO of degree ≤ `M = m−1`, so at
most `M` challenges repair the disagreement at `x`; a challenge `z` with
`Δ(Σ z^j u_j, Σ z^j p_j) ≤ e` must repair ≥ `d − e` of them. Counting the repair pairs
`(z, x)` both ways: `a·(d−e) ≤ M·d`, i.e. `(a−M)·d ≤ a·e`. -/

/-- **L4.4, curve form** (loss `M/(a−M)`): if `Δ(Σ_j z^j·u_j, Σ_j z^j·p_j) ≤ e` for every
`z` in `Z`, then `(|Z| − (m−1)) · Δ([u_j], [p_j]) ≤ |Z| · e`, where `Δ([u_j], [p_j])` is
the SIMULTANEOUS disagreement count. Line case (`m = 2`): `(a−1)·d ≤ a·e`, i.e.
`d ≤ (a/(a−1))·e` — Kopparty Lemma 2.4 verbatim (absolute radii). -/
theorem collinearity_double_count {m : ℕ} (u p : Fin m → ι → F) (e : ℕ) (Z : Finset F)
    (hclose : ∀ z ∈ Z, hammingDist (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x)
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * p j x) ≤ e) :
    (Z.card - (m - 1)) *
      (Finset.univ.filter fun x : ι => ¬ ∀ j, u j x = p j x).card ≤ Z.card * e := by
  classical
  set E := Finset.univ.filter fun x : ι => ¬ ∀ j, u j x = p j x with hE
  -- Step 1: every good challenge repairs all but ≤ e of the d disagreements.
  have hAz : ∀ z ∈ Z, E.card - e ≤ (E.filter fun x =>
      ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card := by
    intro z hz
    have hsplit := Finset.card_filter_add_card_filter_not (s := E)
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x)
    have hnot : (E.filter fun x =>
        ¬ (∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x)).card
        ≤ e := by
      refine le_trans ?_ (hclose z hz)
      rw [hammingDist_eq_card_filter]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩
    omega
  -- Step 2: each disagreement point is repaired by at most M = m−1 challenges
  -- (roots of the nonzero degree-≤M challenge polynomial φ_x).
  have hxz : ∀ x ∈ E, (Z.filter fun z =>
      ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card ≤ m - 1 := by
    intro x hx
    rw [hE, Finset.mem_filter] at hx
    have hx2 := hx.2
    rw [not_forall] at hx2
    obtain ⟨j₀, hj₀⟩ := hx2
    set φ : Polynomial F := curvePoly (fun j => u j x - p j x) with hφ
    have hφ0 : φ ≠ 0 := by
      intro h0
      apply hj₀
      have hc := curvePoly_coeff (fun j => u j x - p j x) j₀
      rw [← hφ, h0, Polynomial.coeff_zero] at hc
      exact sub_eq_zero.mp hc.symm
    have heval : ∀ z : F, φ.eval z
        = (∑ j : Fin m, z ^ (j : ℕ) * u j x) - ∑ j : Fin m, z ^ (j : ℕ) * p j x := by
      intro z
      rw [hφ, curvePoly_eval, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hfeq : (Z.filter fun z =>
        ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x)
        = Z.filter fun z => φ.eval z = 0 := by
      refine Finset.filter_congr fun z _ => ?_
      rw [heval z]
      exact sub_eq_zero.symm
    rw [hfeq]
    exact le_trans (card_filter_eval_zero_le Z hφ0)
      (by rw [hφ]; exact curvePoly_natDegree_le _)
  -- Step 3: double count the repair pairs (z, x).
  have hcount : ∑ z ∈ Z, (E.filter fun x =>
      ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card
      = ∑ x ∈ E, (Z.filter fun z =>
      ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : Z.card * (E.card - e) ≤ ∑ z ∈ Z, (E.filter fun x =>
      ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card := by
    have h := Finset.card_nsmul_le_sum Z _ (E.card - e) hAz
    simpa [smul_eq_mul] using h
  have hup : ∑ x ∈ E, (Z.filter fun z =>
      ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card
      ≤ (m - 1) * E.card := by
    calc ∑ x ∈ E, (Z.filter fun z =>
        ∑ j : Fin m, z ^ (j : ℕ) * u j x = ∑ j : Fin m, z ^ (j : ℕ) * p j x).card
        ≤ ∑ _x ∈ E, (m - 1) := Finset.sum_le_sum hxz
      _ = (m - 1) * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  exact double_count_arith (le_trans hlow (le_trans (le_of_eq hcount) hup))

/-- **L4.4, line form** — Kopparty Lemma 2.4 verbatim (`M = 1`, absolute radii):
good challenges `z` have `Δ(u₀ + z·u₁, p₀ + z·p₁) ≤ e`, and then
`(a − 1)·Δ([u₀,u₁],[p₀,p₁]) ≤ a·e`. -/
theorem collinearity_double_count_pair (u₀ u₁ p₀ p₁ : ι → F) (e : ℕ) (Z : Finset F)
    (hclose : ∀ z ∈ Z, hammingDist (fun x => u₀ x + z * u₁ x)
      (fun x => p₀ x + z * p₁ x) ≤ e) :
    (Z.card - 1) *
      (Finset.univ.filter fun x : ι => ¬ (u₀ x = p₀ x ∧ u₁ x = p₁ x)).card
      ≤ Z.card * e := by
  classical
  have h := collinearity_double_count (u := ![u₀, u₁]) (p := ![p₀, p₁]) e Z ?_
  · have hfeq : (Finset.univ.filter fun x : ι =>
        ¬ ∀ j : Fin 2, (![u₀, u₁] : Fin 2 → ι → F) j x = (![p₀, p₁] : Fin 2 → ι → F) j x)
        = Finset.univ.filter fun x : ι => ¬ (u₀ x = p₀ x ∧ u₁ x = p₁ x) := by
      refine Finset.filter_congr fun x _ => ?_
      rw [Fin.forall_fin_two]
      simp
    rw [hfeq] at h
    simpa using h
  · intro z hz
    have h1 : (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * (![u₀, u₁] : Fin 2 → ι → F) j x)
        = fun x => u₀ x + z * u₁ x := by
      funext x
      rw [Fin.sum_univ_two]
      simp
    have h2 : (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * (![p₀, p₁] : Fin 2 → ι → F) j x)
        = fun x => p₀ x + z * p₁ x := by
      funext x
      rw [Fin.sum_univ_two]
      simp
    rw [h1, h2]
    exact hclose z hz

/-- **L4.4, LOSSLESS corollary, curve form** — the engine piece L5/L6 consume, phrased in
`interleavedClose` with the pinned-interface threshold: if the curve through codewords
`g_j ∈ C` is `e`-close to the curve through `u_j` for MORE than `(m−1)·(e+1)` challenges,
then `Δ([u_j], C^m) ≤ e` — the UN-HALVED floor `n − e` (not `n − 2e`), realized by the
very codewords `g`. -/
theorem interleavedClose_of_curve_agreement (C : Set (ι → F)) {m : ℕ}
    {u g : Fin m → ι → F} (hg : ∀ j, g j ∈ C) {e : ℕ} {Z : Finset F}
    (hclose : ∀ z ∈ Z, hammingDist (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x)
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * g j x) ≤ e)
    (hcard : (m - 1) * (e + 1) < Z.card) :
    interleavedClose C u e := by
  classical
  have hd : (Finset.univ.filter fun x : ι => ¬ ∀ j, u j x = g j x).card ≤ e :=
    lossless_arith (collinearity_double_count u g e Z hclose) hcard
  refine ⟨g, hg, Finset.univ.filter fun x : ι => ∀ j, u j x = g j x, ?_, ?_⟩
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun x : ι => ∀ j, u j x = g j x)
    rw [Finset.card_univ] at hsplit
    omega
  · intro j x hx
    exact (Finset.mem_filter.mp hx).2 j

/-- **L4.4, LOSSLESS corollary, line form** (threshold `e + 1 < |Z|`, the pinned
`r + 1 < |Good|`): the shape `CorrelatedAgreementPairUDParam`'s conclusion needs, via
`interleavedClose_pair_iff`. -/
theorem interleavedClose_pair_of_line_agreement (C : Set (ι → F))
    {u₀ u₁ g₀ g₁ : ι → F} (hg₀ : g₀ ∈ C) (hg₁ : g₁ ∈ C) {e : ℕ} {Z : Finset F}
    (hclose : ∀ z ∈ Z, hammingDist (fun x => u₀ x + z * u₁ x)
      (fun x => g₀ x + z * g₁ x) ≤ e)
    (hcard : e + 1 < Z.card) :
    interleavedClose C ![u₀, u₁] e := by
  refine interleavedClose_of_curve_agreement C (g := ![g₀, g₁]) (Z := Z) ?_ ?_ ?_
  · intro j
    fin_cases j
    · simpa using hg₀
    · simpa using hg₁
  · intro z hz
    have h1 : (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * (![u₀, u₁] : Fin 2 → ι → F) j x)
        = fun x => u₀ x + z * u₁ x := by
      funext x
      rw [Fin.sum_univ_two]
      simp
    have h2 : (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * (![g₀, g₁] : Fin 2 → ι → F) j x)
        = fun x => g₀ x + z * g₁ x := by
      funext x
      rw [Fin.sum_univ_two]
      simp
    rw [h1, h2]
    exact hclose z hz
  · simpa using hcard

/-! ## L4.1 — degree control from lines (the "high coefficients vanish" argument)

With the Cramer-fixed L3.2 the quotient degree bounds arrive in the PS conclusion, so the
packaged L4.3 takes them as hypotheses. These standalone lemmas are the plan's original
L4.1 route (BCIKS20 §4.3.3): they recover the same bounds from bare per-line degree facts,
keeping L4 composable with any divisibility-only PS variant. -/

/-- **L4.1**: if more than `deg_Z Q` horizontal lines of `Q` have `X`-degree ≤ c, then
`deg_X Q ≤ c` — each `X`-coefficient of `Q` beyond `c` (a polynomial in `Z` of degree
≤ `deg_Z Q`) vanishes on all of `S`, hence is zero. -/
theorem sdeg_le_of_horizontal_lines {Q : F[X][Y]} {c : ℕ} {S : Finset F}
    (hcard : Q.natDegree < S.card)
    (hline : ∀ z ∈ S, (Q.eval (Polynomial.C z)).natDegree ≤ c) :
    sdeg Q ≤ c := by
  classical
  rw [sdeg_def]
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
  by_contra hne
  have hroots : ∀ z ∈ S, ((Polynomial.Bivariate.swap Q).coeff j).eval z = 0 := by
    intro z hz
    have h1 : ((Polynomial.Bivariate.swap Q).map (evalRingHom z)).coeff j
        = ((Polynomial.Bivariate.swap Q).coeff j).eval z := by
      rw [Polynomial.coeff_map, coe_evalRingHom]
    rw [← h1, swap_map_evalRingHom]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hline z hz) hj)
  have hcount : S.card ≤ ((Polynomial.Bivariate.swap Q).coeff j).natDegree := by
    have h := card_filter_eval_zero_le S hne
    rwa [Finset.filter_true_of_mem hroots] at h
  have hbound : ((Polynomial.Bivariate.swap Q).coeff j).natDegree ≤ Q.natDegree := by
    have h := coeff_natDegree_le_sdeg (Polynomial.Bivariate.swap Q) j
    rwa [sdeg_swap] at h
  omega

/-- **L4.1, swapped twin** (the plan's `deg_Z P ≤ 1` route): if more than `deg_X Q`
vertical lines of `Q` have degree ≤ c, then `deg_Z Q ≤ c`. -/
theorem natDegree_le_of_vertical_lines {Q : F[X][Y]} {c : ℕ} {T : Finset F}
    (hcard : sdeg Q < T.card)
    (hline : ∀ x ∈ T, (Q.map (evalRingHom x)).natDegree ≤ c) :
    Q.natDegree ≤ c := by
  have h := sdeg_le_of_horizontal_lines (Q := Polynomial.Bivariate.swap Q) (c := c)
    (S := T) hcard (fun x hx => by
      rw [← map_evalRingHom_eq_eval_swap]
      exact hline x hx)
  rwa [sdeg_swap] at h

/-! ## L4.2 — the quotient agrees with the word on ≥ n − deg_X A vertical lines -/

/-- **L4.2**: from the Berlekamp–Welch identity `B(x,Z) = A(x,Z)·w_x(Z)` on every domain
point and the L3 factorization `B = A·Q`, the quotient's vertical line equals `w_x` on a
set of ≥ `n − sdeg A` points — cancel `A(x,Z)` wherever it is nonzero; it vanishes
identically on at most `sdeg A` vertical lines (`card_filter_vertical_zero_le`). Generic
in the line word `w` (any shape the L1/L2 lane produces). -/
theorem quotient_agrees_on_lines {pt : ι → F} (hpt : Function.Injective pt)
    {A B Q : F[X][Y]} (hA : A ≠ 0) (w : ι → Polynomial F)
    (hBW : ∀ i, B.map (evalRingHom (pt i)) = A.map (evalRingHom (pt i)) * w i)
    (hfac : B = A * Q) :
    ∃ S : Finset ι, Fintype.card ι - sdeg A ≤ S.card ∧
      ∀ i ∈ S, Q.map (evalRingHom (pt i)) = w i := by
  classical
  refine ⟨Finset.univ.filter fun i : ι => ¬ A.map (evalRingHom (pt i)) = 0, ?_, ?_⟩
  · have hbad : (Finset.univ.filter fun i : ι => A.map (evalRingHom (pt i)) = 0).card
        ≤ sdeg A := by
      calc (Finset.univ.filter fun i : ι => A.map (evalRingHom (pt i)) = 0).card
          = ((Finset.univ.filter fun i : ι =>
              A.map (evalRingHom (pt i)) = 0).image pt).card :=
            (Finset.card_image_of_injective _ hpt).symm
        _ ≤ ((Finset.univ.image pt).filter fun x => A.map (evalRingHom x) = 0).card := by
            refine Finset.card_le_card ?_
            intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨i, hi, rfl⟩ := hy
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨Finset.mem_image_of_mem pt (Finset.mem_univ i), hi.2⟩
        _ ≤ sdeg A := card_filter_vertical_zero_le (Finset.univ.image pt) hA
    rw [Finset.filter_not, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
    exact Nat.sub_le_sub_left hbad _
  · intro i hi
    rw [Finset.mem_filter] at hi
    have h1 : A.map (evalRingHom (pt i)) * Q.map (evalRingHom (pt i))
        = A.map (evalRingHom (pt i)) * w i := by
      rw [← Polynomial.map_mul, ← hfac]
      exact hBW i
    exact mul_left_cancel₀ hi.2 h1

/-! ## L4.3 — the quotient IS a curve of codewords: packaged direct agreement -/

/-- **L4.3, curve form** (packages L4.1 + L4.2): given the BW identity with the
power-curve word `w_x = Σ_j u_j(x)·Z^j`, the factorization `B = A·Q`, and the PS degree
bound `deg_X Q < k`, the words `u_j` are SIMULTANEOUSLY close to `RScode pt k` at radius
`deg_X A`: the codewords are the evaluations of the `Z`-coefficients `v_j = Q.coeff j`
(degree < k by `coeff_natDegree_le_sdeg`), and on the L4.2 agreement set every
`Z`-coefficient of `Q(x,·) = w_x` matches. NOTE `deg_Z Q ≤ m−1` is NOT needed. -/
theorem interleavedClose_of_bw_factorization {pt : ι → F} (hpt : Function.Injective pt)
    {m : ℕ} (u : Fin m → ι → F) {A B Q : F[X][Y]} (hA : A ≠ 0) {aX k : ℕ}
    (hAX : sdeg A ≤ aX) (hQX : sdeg Q < k)
    (hBW : ∀ i, B.map (evalRingHom (pt i))
      = A.map (evalRingHom (pt i)) * curvePoly fun j => u j i)
    (hfac : B = A * Q) :
    interleavedClose (RScode pt k : Set (ι → F)) u aX := by
  classical
  obtain ⟨S, hScard, hSagree⟩ := quotient_agrees_on_lines hpt hA _ hBW hfac
  refine ⟨fun j i => (Q.coeff (j : ℕ)).eval (pt i), fun j => ?_, S, ?_, ?_⟩
  · exact mem_RScode.mpr ⟨Q.coeff (j : ℕ),
      lt_of_le_of_lt Polynomial.degree_le_natDegree
        (by exact_mod_cast lt_of_le_of_lt (coeff_natDegree_le_sdeg Q _) hQX),
      fun i => rfl⟩
  · exact le_trans (Nat.sub_le_sub_left hAX _) hScard
  · intro j i hi
    have hline := congrArg (fun q => q.coeff (j : ℕ)) (hSagree i hi)
    simp only [Polynomial.coeff_map, coe_evalRingHom, curvePoly_coeff] at hline
    exact hline.symm

/-- **L4.3, line form** — the `m = 2` wrapper in the exact `![u₀, u₁]` shape
`interleavedClose_pair_iff` converts to the target Prop's conclusion. -/
theorem interleavedClose_pair_of_bw_factorization {pt : ι → F}
    (hpt : Function.Injective pt) (u₀ u₁ : ι → F) {A B Q : F[X][Y]} (hA : A ≠ 0)
    {aX k : ℕ} (hAX : sdeg A ≤ aX) (hQX : sdeg Q < k)
    (hBW : ∀ i, B.map (evalRingHom (pt i)) = A.map (evalRingHom (pt i)) *
      (Polynomial.C (u₀ i) + Polynomial.C (u₁ i) * Polynomial.X))
    (hfac : B = A * Q) :
    interleavedClose (RScode pt k : Set (ι → F)) ![u₀, u₁] aX := by
  refine interleavedClose_of_bw_factorization hpt ![u₀, u₁] hA hAX hQX ?_ hfac
  intro i
  rw [hBW i]
  congr 1
  have hvec : (fun j => (![u₀, u₁] : Fin 2 → ι → F) j i) = ![u₀ i, u₁ i] := by
    funext j
    fin_cases j <;> rfl
  rw [hvec, curvePoly_pair]

/-! ## Non-vacuity — every rung FIRES, and L4.4's bound is TIGHT

Instance TIGHT (Kopparty Remark 2.5 at `a = 2, e = 1, d = 2 = a·e/(a−1)`): over `ZMod 5`
on a 2-point domain, `u = (![1,2], ![1,1])` against `p = 0`; the challenges `z = 3, 4`
each repair exactly one of the two disagreement points (`z·u₁(x) + u₀(x) = 0` at
`z = −u₀(x)/u₁(x)`), so both distances are 1 but the pair-distance is 2. -/
section NonVacuity

/-- Disagreement rows of the tightness instance. -/
def tu : Fin 2 → Fin 2 → ZMod 5 := ![![1, 2], ![1, 1]]

/-- The zero reference pair of the tightness instance. -/
def tp : Fin 2 → Fin 2 → ZMod 5 := fun _ _ => 0

/-- The closeness hypothesis of L4.4 HOLDS on the tightness instance: both challenges
`z ∈ {3, 4}` bring the curve within distance 1 (each repairs one disagreement). -/
theorem tight_hyp_fires : ∀ z ∈ ({3, 4} : Finset (ZMod 5)),
    hammingDist (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * tu j x)
      (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * tp j x) ≤ 1 := by decide

/-- **L4.4 FIRES** on the tightness instance: `(2−1)·d ≤ 2·1` with `d` the genuine
simultaneous disagreement count. -/
theorem double_count_fires :
    (({3, 4} : Finset (ZMod 5)).card - 1) *
      (Finset.univ.filter fun x : Fin 2 => ¬ ∀ j, tu j x = tp j x).card
      ≤ ({3, 4} : Finset (ZMod 5)).card * 1 :=
  collinearity_double_count tu tp 1 _ tight_hyp_fires

/-- **L4.4's bound is TIGHT** (not a weak restatement): on the same instance BOTH sides
equal 2 — the inequality of `double_count_fires` is an equality (`d = a·e/(a−1)` exactly,
the Remark 2.5 extremal configuration), so the constant `a/(a−1)` cannot be improved. -/
theorem double_count_tight :
    (({3, 4} : Finset (ZMod 5)).card - 1) *
      (Finset.univ.filter fun x : Fin 2 => ¬ ∀ j, tu j x = tp j x).card
      = ({3, 4} : Finset (ZMod 5)).card * 1 := by decide

-- both sides really are 2, and the instance really has a = 2, d = 2:
#guard ({3, 4} : Finset (ZMod 5)).card = 2
#guard (Finset.univ.filter fun x : Fin 2 => ¬ ∀ j, tu j x = tp j x).card = 2

/-- **The lossless threshold is SHARP**: this instance sits at `|Z| = (m−1)·(e+1) = 2`
EXACTLY (threshold not exceeded) and its simultaneous distance is `2 > e = 1` — so the
strict inequality `(m−1)·(e+1) < |Z|` in `interleavedClose_of_curve_agreement` cannot be
weakened to `≤`. -/
theorem lossless_threshold_sharp :
    ¬ (Finset.univ.filter fun x : Fin 2 => ¬ ∀ j, tu j x = tp j x).card ≤ 1 := by decide

/-! Instance LOSSLESS (the corollary fires): `RS(3,1)/ZMod 5`, `u = (![1,0,0], 0)` against
the zero codewords, ALL 5 challenges are 1-close (`5 > (m−1)(e+1) = 2`), and the
conclusion `interleavedClose (RScode pt3 1) u 1` is genuinely 1-far (not 0-far). -/

/-- The 3-point domain 0,1,2 in `ZMod 5`. -/
def pt3 : Fin 3 → ZMod 5 := fun i => (i.val : ZMod 5)

theorem pt3_inj : Function.Injective pt3 := by decide

/-- The words of the lossless instance: `u₀ = ![1,0,0]` (1-far from the constants),
`u₁ = 0`. -/
def lu : Fin 2 → Fin 3 → ZMod 5 := ![![1, 0, 0], ![0, 0, 0]]

/-- **The lossless corollary FIRES**: every challenge in all of `ZMod 5` is 1-close, the
threshold `(m−1)(e+1) = 2 < 5` holds, and the corollary produces simultaneous 1-closeness
to RS(3,1). -/
theorem lossless_fires :
    interleavedClose (RScode pt3 1 : Set (Fin 3 → ZMod 5)) lu 1 := by
  refine interleavedClose_of_curve_agreement _ (g := fun _ => (0 : Fin 3 → ZMod 5))
    (fun j => Submodule.zero_mem _) (Z := (Finset.univ : Finset (ZMod 5))) ?_ (by decide)
  decide

-- the conclusion is NOT vacuous: lu 0 really is 1-far from the zero codeword (d = e = 1),
-- so the agreement floor n − e = 2 is met with equality:
#guard (Finset.univ.filter fun x : Fin 3 => ∀ j, lu j x = 0).card = 2

/-! Instance BW (L4.2 + L4.3 fire): over `ZMod 5` on the Scaffolding domain `pt5`
(0,1,2,3), take `A = X` (inner; its vertical line VANISHES at the domain point 0),
`Q = X + 3·Z` (so `v₀ = X`, `v₁ = 3`, both of degree < 2), `B = A·Q`, and the word pair
`u₀ = ![4,1,2,3]`, `u₁ = ![0,3,3,3]` — equal to `(v₀, v₁)` evaluated EXCEPT at the point
0, where the BW identity is vacuous (`A(0,Z) = 0`) and the words genuinely disagree. -/

/-- `A = X` (inner variable): the error locator with a real zero at domain point 0. -/
noncomputable def Ac : (ZMod 5)[X][Y] := Polynomial.C Polynomial.X

/-- `Q = X + 3·Z`: the L3 quotient; `Z`-coefficients `v₀ = X`, `v₁ = C 3`. -/
noncomputable def Qc : (ZMod 5)[X][Y] :=
  Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C 3) * Polynomial.X

/-- The word pair: agrees with `(v₀, v₁)` evaluated on 1,2,3; genuinely disagrees at 0. -/
def cu : Fin 2 → Fin 4 → ZMod 5 := ![![4, 1, 2, 3], ![0, 3, 3, 3]]

theorem Ac_ne_zero : Ac ≠ 0 := by
  intro h
  have := Polynomial.C_injective (h.trans (map_zero Polynomial.C).symm)
  exact Polynomial.X_ne_zero this

theorem Ac_sdeg : sdeg Ac = 1 := by
  rw [Ac, sdeg_def, Polynomial.Bivariate.swap_C,
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, Polynomial.natDegree_X]

theorem Ac_line (x : ZMod 5) : Ac.map (evalRingHom x) = Polynomial.C x := by
  rw [Ac, Polynomial.map_C, coe_evalRingHom, Polynomial.eval_X]

theorem Qc_line (x : ZMod 5) :
    Qc.map (evalRingHom x) = Polynomial.C x + Polynomial.C 3 * Polynomial.X := by
  rw [Qc, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
    Polynomial.map_X, coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C]

theorem Qc_coeff_bound : ∀ n, (Qc.coeff n).natDegree ≤ 1 := by
  intro n
  match n with
  | 0 =>
    have h : Qc.coeff 0 = Polynomial.X := by
      simp [Qc, Polynomial.coeff_C]
    rw [h, Polynomial.natDegree_X]
  | 1 =>
    have h : Qc.coeff 1 = Polynomial.C 3 := by
      simp [Qc]
    simp [h]
  | (n + 2) =>
    have h : Qc.coeff (n + 2) = 0 := by
      simp [Qc]
    simp [h]

theorem Qc_sdeg_lt : sdeg Qc < 2 :=
  lt_of_le_of_lt (sdeg_le_of_coeff_natDegree_le Qc_coeff_bound) (by omega)

/-- The Berlekamp–Welch identity holds at every domain point — VACUOUSLY at the point 0
(where `A`'s vertical line is zero and the words disagree with the codewords), and by
genuine agreement at 1, 2, 3. -/
theorem cu_bw : ∀ i : Fin 4, (Ac * Qc).map (evalRingHom (pt5 i))
    = Ac.map (evalRingHom (pt5 i)) * curvePoly fun j => cu j i := by
  have hcurve : ∀ i : Fin 4, curvePoly (fun j => cu j i)
      = Polynomial.C (cu 0 i) + Polynomial.C (cu 1 i) * Polynomial.X := by
    intro i
    have hvec : (fun j => cu j i) = ![cu 0 i, cu 1 i] := by
      funext j
      fin_cases j <;> rfl
    rw [hvec, curvePoly_pair]
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · -- point 0: A-line = C 0 = 0, both sides vanish
    rw [Polynomial.map_mul, show pt5 0 = 0 by decide, Ac_line 0]
    simp
  · -- points 1, 2, 3: the word pair equals the codeword pair, so Q-line = curve
    have hvals : cu 0 i = pt5 i ∧ cu 1 i = 3 := by
      fin_cases i
      · exact absurd (by decide) hi
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
    rw [Polynomial.map_mul, hcurve i, hvals.1, hvals.2, Qc_line]

/-- **L4.2 + L4.3 FIRE**: the packaged BW-factorization theorem produces simultaneous
1-closeness of `cu` to RS(4,2) — through a genuinely vanishing `A`-line and a word pair
that genuinely disagrees with its codewords there. -/
theorem bw_factorization_fires :
    interleavedClose (RScode pt5 2 : Set (Fin 4 → ZMod 5)) cu 1 :=
  interleavedClose_of_bw_factorization pt5_inj cu Ac_ne_zero
    (le_of_eq Ac_sdeg) Qc_sdeg_lt cu_bw rfl

-- the radius 1 is EXACT: cu agrees with (v₀, v₁) = (X, 3) evaluated on exactly 3 of the
-- 4 domain points (the disagreement at 0 is real):
#guard (Finset.univ.filter fun i : Fin 4 => cu 0 i = pt5 i ∧ cu 1 i = 3).card = 3
#guard ¬ (cu 0 0 = pt5 0)

/-! Instance DEGREE-CONTROL (L4.1 fires, EXACTLY): on `Q = X + 3·Z`, three horizontal
lines of degree ≤ 1 pin `deg_X Q ≤ 1`, and the bound is attained (`v₀ = X`). -/

/-- **L4.1 FIRES with an exact conclusion**: `sdeg Qc = 1`, upper bound via
`sdeg_le_of_horizontal_lines` on the 3 lines `z ∈ {0,1,2}` (each `Q(X,z) = X + C(3z)` has
degree 1), lower bound from the coefficient `v₀ = X`. -/
theorem sdeg_control_fires : sdeg Qc = 1 := by
  have hup : sdeg Qc ≤ 1 := by
    refine sdeg_le_of_horizontal_lines (S := ({0, 1, 2} : Finset (ZMod 5))) ?_ ?_
    · have hd : Qc.natDegree ≤ 1 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · simp
        · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
            (le_of_eq Polynomial.natDegree_X)
      have hc : ({0, 1, 2} : Finset (ZMod 5)).card = 3 := by decide
      omega
    · intro z hz
      have hline : Qc.eval (Polynomial.C z) = Polynomial.X + Polynomial.C (3 * z) := by
        rw [Qc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_C, Polynomial.eval_X, ← Polynomial.C_mul]
      rw [hline, Polynomial.natDegree_X_add_C]
  have hlo : 1 ≤ sdeg Qc := by
    have h := coeff_natDegree_le_sdeg Qc 0
    have hc0 : Qc.coeff 0 = Polynomial.X := by
      simp [Qc, Polynomial.coeff_C]
    rwa [hc0, Polynomial.natDegree_X] at h
  omega

/-- **L4.1's swapped twin FIRES**: three vertical lines of degree ≤ 1 pin
`deg_Z Qc ≤ 1` (`sdeg Qc = 1 < 3` supplies the line count). -/
theorem natDegree_control_fires : Qc.natDegree ≤ 1 := by
  refine natDegree_le_of_vertical_lines (T := ({0, 1, 2} : Finset (ZMod 5))) ?_ ?_
  · rw [sdeg_control_fires]
    decide
  · intro x hx
    rw [Qc_line x]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · simp
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_of_eq Polynomial.natDegree_X)

end NonVacuity

/-! ## Axiom hygiene — every keystone pinned to the three kernel axioms -/

#assert_all_clean [curvePoly_coeff, curvePoly_natDegree_le, curvePoly_eval,
  curvePoly_pair, collinearity_double_count, collinearity_double_count_pair,
  interleavedClose_of_curve_agreement, interleavedClose_pair_of_line_agreement,
  sdeg_le_of_horizontal_lines, natDegree_le_of_vertical_lines,
  quotient_agrees_on_lines, interleavedClose_of_bw_factorization,
  interleavedClose_pair_of_bw_factorization, tight_hyp_fires, double_count_fires,
  double_count_tight, lossless_threshold_sharp, pt3_inj, lossless_fires,
  Ac_ne_zero, Ac_sdeg, Qc_sdeg_lt, cu_bw, bw_factorization_fires,
  sdeg_control_fires, natDegree_control_fires]

end Dregg2.Circuit.CorrelatedAgreement
