/-
# Dregg2.Circuit.CorrelatedAgreement.Interpolation — rung L2: the bivariate lift

Rung L2 of the DAG in `docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md` §6:
the LAST connector of the UD-regime correlated-agreement engine, joining L1
(`BerlekampWelch.lean`) to L3.2 (`Dregg2.PS.polishchuk_spielman`) and L4
(`Collinearity.lean`). Generic in `F` and `(n, k, e, m)` — no deployed constants.
All proven; no `sorry`; 20 keystones `#assert_all_clean`.

THE ENGINE (`exists_kernel_of_minors_vanish`): an `ι × N` matrix over `F[Z]` whose
maximal minors all vanish has a NONZERO kernel vector over `F[Z]` ITSELF whose entries
are signed minors — Cramer through the largest nonvanishing minor (`Nat.findGreatest` +
Laplace expansion `det_snoc_expansion` along a bordered row). No fraction field and no
denominator clearing, which is exactly why `deg_Z` stays controlled; a bare
rank-over-`F(Z)` argument loses that control.

- **L2.1** (`bwMatrix_minor_eq_zero`, via `bwMatrix_specialized_kernel` +
  `bwMatrix_natDegree_le`/`bwMatrix_degree_budget`): every maximal minor `R(Z)` of the
  BW matrix (`bwMatrix`: columns `x^s·w_x(Z)` and `−x^t`, `w_x = Σ_j Z^j u_j(x)`) has
  `deg R ≤ (e+1)(m−1)` (at `m = 2`: `e+1`) and vanishes at every good challenge — the
  L1 solution's coefficient vector is a kernel vector of the specialization — hence
  `(e+1)(m−1) < |S|` good challenges force `R ≡ 0`.
- **L2.2** (`bw_bivariate_solution_of_closeN`): the engine turns L2.1 into a NONZERO
  bivariate pair with `deg_X A ≤ e`, `deg_X B ≤ k+e−1`, `deg_Z A, deg_Z B ≤ (e+1)(m−1)`
  and the vertical identity `B(pt i, Z) = A(pt i, Z)·w_i(Z)` at EVERY domain point —
  verbatim L4's `hBW`, with PS's `hvert` quotient `curvePoly (u · i)` of degree ≤ m−1.
  `A ≠ 0` because `A = 0` would kill `B` on `n ≥ k+e` distinct vertical lines.
- **L2.3** (`bw_horizontal_line`): at each good `z` the horizontal line divides in PS's
  `hhoriz` shape with quotient degree ≤ `k−1`: if `A(X,z) ≠ 0` the specialized pair is
  a `bwSolution` and L1.2 (`bw_solution_eq_mul`, UD) makes the quotient the close
  codeword polynomial; if `A(X,z) = 0` then `B(X,z)` dies on the whole domain.
- **THE COMPOSITION** (`interleavedClose_of_good_challenges`): fires L2.2 + L2.3 into
  `Dregg2.PS.polishchuk_spielman` at `(a_X, a_Z, b_X, b_Z) =
  (e, (e+1)(m−1), k+e−1, (e+1)(m−1)+(m−1))`, `S_X` = the domain image, `S_Z = S`, then
  L4.3 `interleavedClose_of_bw_factorization` (PS's `sdeg Q ≤ k−1 < k`), concluding
  `interleavedClose (RScode pt k) u e` from: `pt` injective, `k ≥ 1`, UD `2e+k ≤ n`,
  per-challenge closeness on `S`, and the PS budget
  `(k+e−1)·|S| + ((e+1)(m−1)+(m−1))·n < n·|S|`.

⚠ INTERFACE FINDING (for L5): the PS budget makes the composition's challenge demand
`|S| > ((e+1)(m−1)+(m−1))·n / (n−(k+e−1))` — at the deployed shape (ρ = 1/8,
e ≈ (n−k)/2) that is ≈ (16/7)·(m−1)·(e+2) ≈ 2.3× the target Props' literal threshold
`(m−1)·(r+1) < |Good|`. So L2+PS alone does NOT reach the doc-§4 Props at their stated
threshold: L5 must fire this composition on a challenge set that clears the budget
(any |S| ≳ 2.3·(m−1)·e — e.g. most of a large field) to OBTAIN the codewords g_j, and
then Kopparty's lossless double count (L4.4 `interleavedClose_of_curve_agreement`,
threshold exactly `(m−1)(e+1) < |Z|`) carries the small-|Good| regime. Both consumers'
hypotheses are met EXACTLY as stated — no mismatch in shape, only this threshold gap,
which is intrinsic to the Polishchuk–Spielman budget `b_X/n_X + b_Z/n_Z < 1`.

Non-vacuity: the whole chain FIRES end to end on RS(3,1)/ZMod 7 —
`correlated_agreement_fires` runs L1 → kernel → PS → L4 on the genuinely-corrupted pair
`u₀ = ![0,0,1]` (distance exactly 1 from every constant, `#guard`ed), `u₁ = 0`, with
5 good challenges against budget `1·5 + 3·3 = 14 < 15`; `bw_bivariate_fires` pins L2.2
alone. `#assert_all_clean` on all 20 keystones.
-/
import Dregg2.Circuit.CorrelatedAgreement.BerlekampWelch
import Dregg2.Circuit.CorrelatedAgreement.Collinearity

namespace Dregg2.Circuit.CorrelatedAgreement

open Polynomial
open scoped Polynomial.Bivariate
open Dregg2.PS

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Determinant degree bound, arbitrary finite index -/

/-- Degree bound for the determinant of a polynomial matrix with per-column degree
bounds — `Dregg2.PS.natDegree_det_le` generalized from `Fin N` to any finite index. -/
theorem natDegree_det_le_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (Polynomial F)) (d : κ → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_intCast, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  exact Finset.sum_le_sum (fun j _ => h (σ j) j)

/-! ## Coefficient-vector polynomials (the bivariate-lift builder) -/

/-- The polynomial `Σ_{s<q} c_s · X^s` with prescribed coefficient vector `c` — used at
`R = F[Z]` to assemble the bivariate `A` and `B` from a kernel vector. -/
noncomputable def ofCoeffs {R : Type*} [CommRing R] {q : ℕ} (c : Fin q → R) : Polynomial R :=
  ∑ s : Fin q, Polynomial.C (c s) * Polynomial.X ^ (s : ℕ)

theorem ofCoeffs_coeff {R : Type*} [CommRing R] {q : ℕ} (c : Fin q → R) (s : Fin q) :
    (ofCoeffs c).coeff (s : ℕ) = c s := by
  rw [ofCoeffs, Polynomial.finsetSum_coeff, Finset.sum_eq_single s]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · intro b _ hb
    have hne : (s : ℕ) ≠ (b : ℕ) := Fin.val_injective.ne hb.symm
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem ofCoeffs_coeff_of_le {R : Type*} [CommRing R] {q : ℕ} (c : Fin q → R) {n : ℕ}
    (hn : q ≤ n) : (ofCoeffs c).coeff n = 0 := by
  rw [ofCoeffs, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hne : n ≠ (s : ℕ) := by have := s.isLt; omega
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]

theorem ofCoeffs_natDegree_lt {R : Type*} [CommRing R] {q : ℕ} (c : Fin q → R)
    (hq : 0 < q) : (ofCoeffs c).natDegree < q := by
  have h : (ofCoeffs c).natDegree ≤ q - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _)
      (le_trans (Polynomial.natDegree_X_pow_le _) ?_)
    have := s.isLt
    omega
  omega

theorem ofCoeffs_eval {R : Type*} [CommRing R] {q : ℕ} (c : Fin q → R) (x : R) :
    (ofCoeffs c).eval x = ∑ s : Fin q, c s * x ^ (s : ℕ) := by
  rw [ofCoeffs, Polynomial.eval_finsetSum]
  simp

theorem ofCoeffs_eq_zero_iff {R : Type*} [CommRing R] {q : ℕ} (c : Fin q → R) :
    ofCoeffs c = 0 ↔ ∀ s, c s = 0 := by
  constructor
  · intro h s
    have := ofCoeffs_coeff c s
    rw [h, Polynomial.coeff_zero] at this
    exact this.symm
  · intro h
    rw [ofCoeffs]
    exact Finset.sum_eq_zero fun s _ => by rw [h s, map_zero, zero_mul]

/-! ## The kernel-from-vanishing-minors engine -/

/-- Appending a fresh element to an injective tuple stays injective. -/
theorem snoc_injective_of_notMem {α : Type*} {r : ℕ} {T : Fin r → α}
    (hT : Function.Injective T) {i : α} (hi : ∀ s, T s ≠ i) :
    Function.Injective (Fin.snoc T i : Fin (r + 1) → α) := by
  intro a b hab
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
    exact congrArg Fin.castSucc (hT hab)
  · rw [Fin.snoc_castSucc, Fin.snoc_last] at hab
    exact absurd hab (hi a')
  · rw [Fin.snoc_last, Fin.snoc_castSucc] at hab
    exact absurd hab.symm (hi b')
  · rfl

/-- Laplace expansion of a bordered minor along its appended last row: rows `T` plus the
extra row `i`, columns `C'`; the `t`-th cofactor drops column `t` of `C'`. -/
theorem det_snoc_expansion {R : Type*} [CommRing R] {ι' κ : Type*} {r : ℕ}
    (M : Matrix ι' κ R) (T : Fin r → ι') (C' : Fin (r + 1) → κ) (i : ι') :
    (M.submatrix (Fin.snoc T i : Fin (r + 1) → ι') C').det =
      ∑ t : Fin (r + 1), (-1) ^ (r + (t : ℕ)) * M i (C' t) *
        (M.submatrix T (C' ∘ t.succAbove)).det := by
  rw [Matrix.det_succ_row _ (Fin.last r)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hrow : (Fin.snoc T i : Fin (r + 1) → ι') ∘ Fin.castSucc = T := by
    funext s
    simp
  rw [Matrix.submatrix_apply, Fin.snoc_last, Matrix.submatrix_submatrix,
    Fin.succAbove_last, hrow, Fin.val_last]

/-- **The kernel engine**: if every maximal (`N×N`) minor of the `ι' × N` polynomial
matrix `M` vanishes, then `M` has a nonzero kernel vector over `F[Z]` itself whose
entries are signed minors of `M` — in particular each entry's degree is bounded by the
total column degree budget `Σ_j d j`. (Cramer through the largest nonvanishing minor;
no fraction field, no denominator clearing, hence the degree control that a bare
rank-over-`F(Z)` argument cannot give.) -/
theorem exists_kernel_of_minors_vanish {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {N : ℕ}
    (M : Matrix ι' (Fin N) (Polynomial F)) (d : Fin N → ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d j)
    (hminor : ∀ (T : Fin N → ι') (C : Fin N → Fin N), Function.Injective T →
      Function.Injective C → (M.submatrix T C).det = 0) :
    ∃ v : Fin N → Polynomial F, v ≠ 0 ∧ M.mulVec v = 0 ∧
      ∀ j, (v j).natDegree ≤ ∑ j', d j' := by
  classical
  -- the largest size carrying a NONvanishing minor
  set P : ℕ → Prop := fun s => ∃ (T : Fin s → ι') (C : Fin s → Fin N),
    Function.Injective T ∧ Function.Injective C ∧ (M.submatrix T C).det ≠ 0 with hP
  have hP0 : P 0 := ⟨Fin.elim0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, by
    rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  have hPN : ¬ P N := by
    rintro ⟨T, C, hT, hC, hne⟩
    exact hne (hminor T C hT hC)
  set r : ℕ := Nat.findGreatest P N with hrdef
  have hPr : P r := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hrN : r < N := by
    rcases lt_or_eq_of_le (Nat.findGreatest_le (P := P) (n := N)) with h | h
    · exact h
    · exact absurd (h ▸ hPr) hPN
  have hmax : ∀ (T : Fin (r + 1) → ι') (C : Fin (r + 1) → Fin N), Function.Injective T →
      Function.Injective C → (M.submatrix T C).det = 0 := by
    intro T C hT hC
    by_contra hne
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hrN ⟨T, C, hT, hC, hne⟩
  obtain ⟨T, C, hT, hC, hdet⟩ := hPr
  -- a fresh column outside the range of C
  have hfresh : ∃ c : Fin N, ∀ t, C t ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective C := fun c => hcon c
    have hle := Fintype.card_le_of_surjective C hsurj
    simp only [Fintype.card_fin] at hle
    omega
  obtain ⟨c, hc⟩ := hfresh
  set C' : Fin (r + 1) → Fin N := Fin.snoc C c with hC'
  have hC'inj : Function.Injective C' := snoc_injective_of_notMem hC hc
  -- the candidate kernel entries: signed r-minors dropping one column of C'
  set mnr : Fin (r + 1) → Polynomial F := fun t =>
    (-1 : Polynomial F) ^ (r + (t : ℕ)) * (M.submatrix T (C' ∘ t.succAbove)).det with hmnr
  set v : Fin N → Polynomial F := fun j => ∑ t, if C' t = j then mnr t else 0 with hv
  -- (1) mulVec v = the bordered determinant, row by row
  have hexpand : ∀ i : ι',
      M.mulVec v i = (M.submatrix (Fin.snoc T i : Fin (r + 1) → ι') C').det := by
    intro i
    have hmv : M.mulVec v i = ∑ j, M i j * v j := rfl
    rw [hmv, det_snoc_expansion]
    have hswap : ∀ j, M i j * v j = ∑ t, if C' t = j then M i j * mnr t else 0 := by
      intro j
      rw [hv]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [mul_ite, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => hswap j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (C' t) (fun j => M i j * mnr t),
      if_pos (Finset.mem_univ _), hmnr]
    ring
  -- (2) every bordered determinant vanishes: repeated row, or an (r+1)-minor
  have hker : M.mulVec v = 0 := by
    funext i
    rw [Pi.zero_apply, hexpand i]
    by_cases hiT : ∃ s, T s = i
    · obtain ⟨s₀, rfl⟩ := hiT
      refine Matrix.det_zero_of_row_eq (i := Fin.castSucc s₀) (j := Fin.last r)
        (Fin.ne_of_lt (Fin.castSucc_lt_last s₀)) ?_
      funext t
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last]
    · push Not at hiT
      exact hmax _ _ (snoc_injective_of_notMem hT hiT) hC'inj
  -- (3) the fresh-column entry is the pivot minor, hence nonzero
  have hvc : v (C' (Fin.last r)) = mnr (Fin.last r) := by
    rw [hv]
    refine (Finset.sum_eq_single (Fin.last r) ?_ ?_).trans (if_pos rfl)
    · intro t _ ht
      exact if_neg fun h => ht (hC'inj h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hmnr_last : mnr (Fin.last r) ≠ 0 := by
    have hcols : C' ∘ (Fin.last r).succAbove = C := by
      funext u
      rw [Function.comp_apply, Fin.succAbove_last_apply, hC', Fin.snoc_castSucc]
    rw [hmnr]
    simp only []
    rw [hcols]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdet
  have hv0 : v ≠ 0 := fun h0 => hmnr_last (by rw [← hvc, h0, Pi.zero_apply])
  -- (4) degree bounds: every entry is 0 or a signed r-minor over a column subset
  refine ⟨v, hv0, hker, fun j => ?_⟩
  rw [hv]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  split_ifs with h
  · rw [hmnr]
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : ((-1 : Polynomial F) ^ (r + (t : ℕ))).natDegree = 0 := by
      rw [show (-1 : Polynomial F) = Polynomial.C (-1) by rw [map_neg, map_one], ← map_pow,
        Polynomial.natDegree_C]
    rw [h1, zero_add]
    refine le_trans (natDegree_det_le_sum _ (fun u => d (C' (t.succAbove u)))
      (fun s u => hdeg (T s) (C' (t.succAbove u)))) ?_
    have hinj : Function.Injective (C' ∘ t.succAbove) :=
      hC'inj.comp Fin.succAbove_right_injective
    calc ∑ u : Fin r, d (C' (t.succAbove u))
        = ∑ j' ∈ Finset.univ.image (C' ∘ t.succAbove), d j' :=
          (Finset.sum_image fun a _ b _ hab => hinj hab).symm
      _ ≤ ∑ j', d j' := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · simp

/-! ## L2.1 — the Berlekamp–Welch matrix over `F[Z]` and its minors -/

/-- The bivariate Berlekamp–Welch system matrix at parameters `(k, e)` for the curve word
`w_i(Z) = Σ_{j<m} Z^j · u_j(i)`: the first `e+1` columns carry `(pt i)^s · w_i(Z)` (the
`A`-side), the last `k+e` columns carry `−(pt i)^t` (the `B`-side). A kernel vector over
`F[Z]` is exactly the coefficient vector of a bivariate BW pair `(A, B)`; a kernel vector
of the specialization at `Z = z` is a univariate BW solution at the folded word. -/
noncomputable def bwMatrix (pt : ι → F) {m : ℕ} (u : Fin m → ι → F) (k e : ℕ) :
    Matrix ι (Fin ((e + 1) + (k + e))) (Polynomial F) :=
  Matrix.of fun i => Fin.addCases
    (fun s : Fin (e + 1) => Polynomial.C ((pt i) ^ (s : ℕ)) * curvePoly (fun j => u j i))
    (fun t : Fin (k + e) => -Polynomial.C ((pt i) ^ (t : ℕ)))

/-- The per-column degree bounds of `bwMatrix`: `m − 1` on the `A`-side, `0` on the
`B`-side. -/
theorem bwMatrix_natDegree_le (pt : ι → F) {m : ℕ} (u : Fin m → ι → F) (k e : ℕ)
    (i : ι) (j : Fin ((e + 1) + (k + e))) :
    (bwMatrix pt u k e i j).natDegree ≤
      Fin.addCases (fun _ : Fin (e + 1) => m - 1) (fun _ : Fin (k + e) => 0) j := by
  induction j using Fin.addCases with
  | left s =>
    simp only [bwMatrix, Matrix.of_apply, Fin.addCases_left]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (curvePoly_natDegree_le _)
  | right t =>
    simp only [bwMatrix, Matrix.of_apply, Fin.addCases_right, Polynomial.natDegree_neg,
      Polynomial.natDegree_C, le_refl]

/-- The total column degree budget of `bwMatrix` is `(e+1)·(m−1)` — the L2.1 degree
bound on every maximal minor `R(Z)` (at `m = 2` this is the prompt's `e + 1`). -/
theorem bwMatrix_degree_budget (k e m : ℕ) :
    ∑ j : Fin ((e + 1) + (k + e)),
      (Fin.addCases (fun _ : Fin (e + 1) => m - 1) (fun _ : Fin (k + e) => 0) j : ℕ)
      = (e + 1) * (m - 1) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]

/-- **L2.1, solvability transfer**: at a good challenge `z`, the specialization of the
BW matrix at `Z = z` has a nontrivial kernel — the coefficient vector of the L1
Berlekamp–Welch solution at the folded word. -/
theorem bwMatrix_specialized_kernel {pt : ι → F} {m : ℕ} {u : Fin m → ι → F} {k e : ℕ}
    (hke : 1 ≤ k + e) {z : F}
    (hclose : closeN (RScode pt k : Set (ι → F)) e
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x)) :
    ∃ vz : Fin ((e + 1) + (k + e)) → F, vz ≠ 0 ∧
      ((bwMatrix pt u k e).map (evalRingHom z)).mulVec vz = 0 := by
  obtain ⟨A, B, hsol⟩ := bw_solvable_of_closeN hclose
  obtain ⟨hA0, hAdeg, hBdeg, hid⟩ := hsol
  have hAnat : A.natDegree < e + 1 := Nat.lt_succ_of_le hAdeg
  have hBnat : B.natDegree < k + e := by
    rcases eq_or_ne B 0 with rfl | hB0
    · simp only [Polynomial.natDegree_zero]
      omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt hB0).mpr hBdeg
  refine ⟨Fin.addCases (fun s => A.coeff (s : ℕ)) (fun t => B.coeff (t : ℕ)), ?_, ?_⟩
  · intro h0
    have hlc := congrFun h0 (Fin.castAdd (k + e) ⟨A.natDegree, hAnat⟩)
    rw [Fin.addCases_left, Pi.zero_apply] at hlc
    exact Polynomial.leadingCoeff_ne_zero.mpr hA0 hlc
  · funext i
    have hmv : ((bwMatrix pt u k e).map (evalRingHom z)).mulVec
        (Fin.addCases (fun s => A.coeff (s : ℕ)) (fun t => B.coeff (t : ℕ))) i
        = ∑ j, ((bwMatrix pt u k e).map (evalRingHom z)) i j
            * Fin.addCases (fun s => A.coeff (s : ℕ)) (fun t => B.coeff (t : ℕ)) j := rfl
    rw [Pi.zero_apply, hmv, Fin.sum_univ_add]
    simp only [Matrix.map_apply, bwMatrix, Matrix.of_apply, Fin.addCases_left,
      Fin.addCases_right, Polynomial.coe_evalRingHom, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_neg]
    have h1 : ∑ s : Fin (e + 1),
        pt i ^ (s : ℕ) * (curvePoly fun j => u j i).eval z * A.coeff (s : ℕ)
        = (curvePoly fun j => u j i).eval z * A.eval (pt i) := by
      rw [Polynomial.eval_eq_sum_range' hAnat,
        ← Fin.sum_univ_eq_sum_range (fun s => A.coeff s * pt i ^ s) (e + 1),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h2 : ∑ t : Fin (k + e), -(pt i ^ (t : ℕ)) * B.coeff (t : ℕ)
        = -B.eval (pt i) := by
      rw [Polynomial.eval_eq_sum_range' hBnat,
        ← Fin.sum_univ_eq_sum_range (fun t => B.coeff t * pt i ^ t) (k + e),
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [h1, h2]
    have hcv : (curvePoly fun j => u j i).eval z = ∑ j : Fin m, z ^ (j : ℕ) * u j i := by
      rw [curvePoly_eval]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hcv]
    linear_combination hid i

/-- **L2.1**: every maximal minor `R(Z)` of the BW matrix has `natDegree ≤ (e+1)·(m−1)`
(at `m = 2`: `≤ e + 1`) and vanishes at every good challenge `z ∈ S` (apply L1 at `z`);
with `(e+1)·(m−1) < |S|` good challenges it therefore vanishes IDENTICALLY. -/
theorem bwMatrix_minor_eq_zero {pt : ι → F} {m : ℕ} {u : Fin m → ι → F} {k e : ℕ}
    (hke : 1 ≤ k + e) {S : Finset F}
    (hclose : ∀ z ∈ S, closeN (RScode pt k : Set (ι → F)) e
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x))
    (hS : (e + 1) * (m - 1) < S.card)
    (T : Fin ((e + 1) + (k + e)) → ι) (C : Fin ((e + 1) + (k + e)) → Fin ((e + 1) + (k + e)))
    (hT : Function.Injective T) (hC : Function.Injective C) :
    ((bwMatrix pt u k e).submatrix T C).det = 0 := by
  classical
  have hCbij : Function.Bijective C := Finite.injective_iff_bijective.mp hC
  -- (a) the minor is a polynomial in Z of degree ≤ (e+1)(m−1)
  have hdeg : ((bwMatrix pt u k e).submatrix T C).det.natDegree ≤ (e + 1) * (m - 1) := by
    refine le_trans (natDegree_det_le_sum _
      (fun t => Fin.addCases (fun _ : Fin (e + 1) => m - 1) (fun _ : Fin (k + e) => 0) (C t))
      (fun s t => by exact bwMatrix_natDegree_le pt u k e (T s) (C t))) ?_
    rw [Function.Bijective.sum_comp hCbij
      (fun j => (Fin.addCases (fun _ : Fin (e + 1) => m - 1) (fun _ : Fin (k + e) => 0) j : ℕ))]
    exact le_of_eq (bwMatrix_degree_budget k e m)
  -- (b) it vanishes at every good challenge, via the L1 kernel vector
  have hvan : ∀ z ∈ S, ((bwMatrix pt u k e).submatrix T C).det.eval z = 0 := by
    intro z hz
    obtain ⟨vz, hvz0, hvzk⟩ := bwMatrix_specialized_kernel hke (hclose z hz)
    have hmapdet : ((bwMatrix pt u k e).submatrix T C).det.eval z
        = ((((bwMatrix pt u k e).map (evalRingHom z)).submatrix T C)).det := by
      rw [← Polynomial.coe_evalRingHom, RingHom.map_det, Matrix.submatrix_map]
      rfl
    rw [hmapdet]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨vz ∘ C, ?_, ?_⟩
    · intro h0
      apply hvz0
      funext j
      obtain ⟨j', rfl⟩ := hCbij.2 j
      exact congrFun h0 j'
    · funext s
      have hrow : (((bwMatrix pt u k e).map (evalRingHom z)).submatrix T C).mulVec
          (vz ∘ C) s
          = ∑ t, ((bwMatrix pt u k e).map (evalRingHom z)) (T s) (C t) * vz (C t) := rfl
      rw [hrow, Function.Bijective.sum_comp hCbij
        (fun j => ((bwMatrix pt u k e).map (evalRingHom z)) (T s) j * vz j)]
      exact congrFun hvzk (T s)
  -- (c) more roots than degree ⟹ identically zero
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S hvan
    (lt_of_le_of_lt hdeg hS)

/-! ## L2.2 — the bivariate Berlekamp–Welch solution -/

/-- **L2.2**: with more good challenges than `(e+1)·(m−1)`, the bivariate BW system has a
NONZERO polynomial solution `(A, B)` over `F[X][Z]` with full degree control —
`deg_X A ≤ e`, `deg_X B ≤ k+e−1`, `deg_Z A, deg_Z B ≤ (e+1)·(m−1)` — whose vertical line
at EVERY domain point carries the curve word: `B(pt i, Z) = A(pt i, Z)·w_i(Z)` with
`w_i = curvePoly (u · i)`. The identity is EXACTLY L4's `hBW` and PS's `hvert` shape.
(Rank drop over `F(Z)` is realized as a minor-entry kernel vector over `F[Z]` itself —
no denominators, hence the `deg_Z` control.) -/
theorem bw_bivariate_solution_of_closeN {pt : ι → F} (hpt : Function.Injective pt)
    {m : ℕ} {u : Fin m → ι → F} {k e : ℕ}
    (hke : 1 ≤ k + e) (hn : k + e ≤ Fintype.card ι) {S : Finset F}
    (hclose : ∀ z ∈ S, closeN (RScode pt k : Set (ι → F)) e
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x))
    (hS : (e + 1) * (m - 1) < S.card) :
    ∃ A B : F[X][Y], A ≠ 0 ∧ sdeg A ≤ e ∧ A.natDegree ≤ (e + 1) * (m - 1) ∧
      sdeg B ≤ k + e - 1 ∧ B.natDegree ≤ (e + 1) * (m - 1) ∧
      ∀ i, B.map (evalRingHom (pt i))
        = A.map (evalRingHom (pt i)) * curvePoly fun j => u j i := by
  classical
  obtain ⟨v, hv0, hvker, hvdeg⟩ := exists_kernel_of_minors_vanish (bwMatrix pt u k e)
    (fun j => Fin.addCases (fun _ : Fin (e + 1) => m - 1) (fun _ : Fin (k + e) => 0) j)
    (fun i j => bwMatrix_natDegree_le pt u k e i j)
    (fun T C hT hC => bwMatrix_minor_eq_zero hke hclose hS T C hT hC)
  have hbudget := bwMatrix_degree_budget k e m
  set a : Fin (e + 1) → Polynomial F := fun s => v (Fin.castAdd (k + e) s) with ha
  set b : Fin (k + e) → Polynomial F := fun t => v (Fin.natAdd (e + 1) t) with hb
  set Asw : Polynomial (Polynomial F) := ofCoeffs a with hAswdef
  set Bsw : Polynomial (Polynomial F) := ofCoeffs b with hBswdef
  -- the vertical identity, in the pre-swap world
  have hvert : ∀ i, Bsw.eval (Polynomial.C (pt i))
      = Asw.eval (Polynomial.C (pt i)) * curvePoly (fun j => u j i) := by
    intro i
    have h0 : ∑ j, bwMatrix pt u k e i j * v j = 0 := by
      have := congrFun hvker i
      rwa [Pi.zero_apply] at this
    rw [Fin.sum_univ_add] at h0
    simp only [bwMatrix, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right] at h0
    have hA : Asw.eval (Polynomial.C (pt i))
        = ∑ s : Fin (e + 1), a s * Polynomial.C (pt i) ^ (s : ℕ) := ofCoeffs_eval a _
    have hB : Bsw.eval (Polynomial.C (pt i))
        = ∑ t : Fin (k + e), b t * Polynomial.C (pt i) ^ (t : ℕ) := ofCoeffs_eval b _
    have h1 : ∑ s : Fin (e + 1),
        Polynomial.C (pt i ^ (s : ℕ)) * curvePoly (fun j => u j i) * v (Fin.castAdd (k + e) s)
        = Asw.eval (Polynomial.C (pt i)) * curvePoly (fun j => u j i) := by
      rw [hA, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ha, Polynomial.C_pow]
      ring
    have h2 : ∑ t : Fin (k + e),
        -Polynomial.C (pt i ^ (t : ℕ)) * v (Fin.natAdd (e + 1) t)
        = -Bsw.eval (Polynomial.C (pt i)) := by
      rw [hB, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hb, Polynomial.C_pow]
      ring
    rw [h1, h2] at h0
    linear_combination -h0
  refine ⟨Polynomial.Bivariate.swap Asw, Polynomial.Bivariate.swap Bsw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A ≠ 0: else the a-half vanishes, the vertical identities kill Bsw on n ≥ k+e
    -- distinct points C (pt i), so the b-half vanishes too — contradicting v ≠ 0.
    intro hA0
    have hAsw0 : Asw = 0 := by
      by_contra hne
      exact swap_ne_zero hne hA0
    have hBsw0 : Bsw = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Bsw
        (f := fun i : ι => Polynomial.C (pt i))
        (fun i i' hii' => hpt (Polynomial.C_injective hii')) (fun i => ?_) ?_
      · rw [hvert i, hAsw0]
        simp
      · exact lt_of_lt_of_le (ofCoeffs_natDegree_lt b (by omega)) hn
    apply hv0
    funext j
    induction j using Fin.addCases with
    | left s => exact (ofCoeffs_eq_zero_iff a).mp hAsw0 s
    | right t => exact (ofCoeffs_eq_zero_iff b).mp hBsw0 t
  · -- deg_X A ≤ e
    rw [sdeg_swap]
    have hlt : Asw.natDegree < e + 1 := ofCoeffs_natDegree_lt a (by omega)
    omega
  · -- deg_Z A ≤ (e+1)(m−1)
    rw [show (Polynomial.Bivariate.swap Asw).natDegree = sdeg Asw from (sdeg_def Asw).symm]
    refine sdeg_le_of_coeff_natDegree_le fun n => ?_
    rcases lt_or_ge n (e + 1) with hlt | hge
    · have hcoeff : Asw.coeff n = a ⟨n, hlt⟩ := ofCoeffs_coeff a ⟨n, hlt⟩
      rw [hcoeff]
      exact le_trans (hvdeg _) (le_of_eq hbudget)
    · rw [hAswdef, ofCoeffs_coeff_of_le a hge]
      simp
  · -- deg_X B ≤ k+e−1
    rw [sdeg_swap]
    have hlt : Bsw.natDegree < k + e := ofCoeffs_natDegree_lt b (by omega)
    omega
  · -- deg_Z B ≤ (e+1)(m−1)
    rw [show (Polynomial.Bivariate.swap Bsw).natDegree = sdeg Bsw from (sdeg_def Bsw).symm]
    refine sdeg_le_of_coeff_natDegree_le fun n => ?_
    rcases lt_or_ge n (k + e) with hlt | hge
    · have hcoeff : Bsw.coeff n = b ⟨n, hlt⟩ := ofCoeffs_coeff b ⟨n, hlt⟩
      rw [hcoeff]
      exact le_trans (hvdeg _) (le_of_eq hbudget)
    · rw [hBswdef, ofCoeffs_coeff_of_le b hge]
      simp
  · -- the vertical identity at every domain point (L4's hBW / PS's hvert)
    intro i
    rw [map_evalRingHom_eq_eval_swap, map_evalRingHom_eq_eval_swap,
      Polynomial.Bivariate.swap_swap_apply, Polynomial.Bivariate.swap_swap_apply]
    exact hvert i

/-! ## L2.3 — both line families in Polishchuk–Spielman shape -/

/-- **L2.3, horizontal lines**: at a good challenge `z`, the horizontal line of any pair
satisfying the L2.2 vertical identity divides with quotient degree ≤ `k − 1` — PS's
`hhoriz` shape. If `A(X,z) ≠ 0` the specialized pair is a `bwSolution` at the folded
word and L1.2 (`bw_solution_eq_mul`, UD regime) hands the quotient = the close codeword
polynomial; if `A(X,z) = 0` then `B(X,z)` vanishes on the whole `≥ k+e`-point domain,
hence is 0 and the quotient is 0. (The vertical family is already PS-shaped: the
quotient at `pt i` is `curvePoly (u · i)` of degree ≤ `m − 1`.) -/
theorem bw_horizontal_line {pt : ι → F} (hpt : Function.Injective pt)
    {m : ℕ} {u : Fin m → ι → F} {k e : ℕ}
    (hn : 2 * e + k ≤ Fintype.card ι) (hke : 1 ≤ k + e) {A B : F[X][Y]}
    (hAX : sdeg A ≤ e) (hBX : sdeg B ≤ k + e - 1)
    (hBW : ∀ i, B.map (evalRingHom (pt i))
      = A.map (evalRingHom (pt i)) * curvePoly fun j => u j i)
    {z : F}
    (hclose : closeN (RScode pt k : Set (ι → F)) e
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x)) :
    ∃ q : Polynomial F, B.eval (Polynomial.C z) = A.eval (Polynomial.C z) * q ∧
      q.natDegree ≤ k - 1 := by
  classical
  set Az : Polynomial F := A.eval (Polynomial.C z) with hAz
  set Bz : Polynomial F := B.eval (Polynomial.C z) with hBz
  -- the specialized pointwise identity, with the curve evaluated to the folded word
  have hpoint : ∀ i, Az.eval (pt i) * (∑ j : Fin m, z ^ (j : ℕ) * u j i)
      = Bz.eval (pt i) := by
    intro i
    have h := congrArg (Polynomial.eval z) (hBW i)
    rw [Polynomial.eval_mul, Polynomial.map_evalRingHom_eval,
      Polynomial.map_evalRingHom_eval] at h
    have hcv : (curvePoly fun j => u j i).eval z = ∑ j : Fin m, z ^ (j : ℕ) * u j i := by
      rw [curvePoly_eval]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hcv] at h
    exact h.symm
  have hAzdeg : Az.natDegree ≤ e := le_trans (natDegree_eval_C_le A z) hAX
  have hBzdeg : Bz.natDegree ≤ k + e - 1 := le_trans (natDegree_eval_C_le B z) hBX
  rcases eq_or_ne Az 0 with hAz0 | hAz0
  · -- vanishing line: B(X,z) dies on the whole domain
    refine ⟨0, ?_, by simp⟩
    have hBz0 : Bz = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Bz hpt
        (fun i => ?_) (by omega)
      have h := hpoint i
      rw [hAz0, Polynomial.eval_zero, zero_mul] at h
      exact h.symm
    rw [hBz0, mul_zero]
  · -- live line: the specialized pair is a bwSolution at the folded word
    have hsol : bwSolution pt k e (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x) Az Bz := by
      refine ⟨hAz0, hAzdeg, ?_, fun i => hpoint i⟩
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast (by omega : Bz.natDegree < k + e)
    obtain ⟨v, hv, hdist⟩ := hclose
    obtain ⟨P, hPdeg, hvP⟩ := mem_RScode.mp hv
    have hveq : v = evalOn pt P := funext fun i => hvP i
    rw [hveq] at hdist
    refine ⟨P, ?_, ?_⟩
    · exact bw_solution_eq_mul hpt hn hsol hPdeg hdist
    · rcases eq_or_ne P 0 with rfl | hP0
      · simp
      · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
        omega

/-! ## The composition — L1 → L2 → L3.2 (Polishchuk–Spielman) → L4 -/

/-- **The connector's payoff**: in the unique-decoding regime (`2e + k ≤ n`, `pt`
injective, `k ≥ 1`), if the folded word `Σ_j z^j·u_j` is `e`-close to `RS[pt, k]` at
every challenge of a set `S` satisfying the Polishchuk–Spielman budget
`(k+e−1)·|S| + ((e+1)·(m−1) + (m−1))·n < n·|S|`, then the rows are SIMULTANEOUSLY
`e`-close: `interleavedClose (RScode pt k) u e`. Fires L2.2 (the bivariate pair), L2.3
(the horizontal lines), `Dregg2.PS.polishchuk_spielman` at
`(a_X, a_Z, b_X, b_Z) = (e, (e+1)(m−1), k+e−1, (e+1)(m−1)+(m−1))`, and L4's
`interleavedClose_of_bw_factorization`. -/
theorem interleavedClose_of_good_challenges {pt : ι → F} (hpt : Function.Injective pt)
    {m : ℕ} {u : Fin m → ι → F} {k e : ℕ} (hk : 1 ≤ k)
    (hn : 2 * e + k ≤ Fintype.card ι) {S : Finset F}
    (hclose : ∀ z ∈ S, closeN (RScode pt k : Set (ι → F)) e
      (fun x => ∑ j : Fin m, z ^ (j : ℕ) * u j x))
    (hbudget : (k + e - 1) * S.card + ((e + 1) * (m - 1) + (m - 1)) * Fintype.card ι
      < Fintype.card ι * S.card) :
    interleavedClose (RScode pt k : Set (ι → F)) u e := by
  classical
  have hke : 1 ≤ k + e := by omega
  have hkn : k + e ≤ Fintype.card ι := by omega
  -- the budget clears the L2.2 threshold
  have hthresh : (e + 1) * (m - 1) + (m - 1) < S.card := by
    refine Nat.lt_of_mul_lt_mul_left (a := Fintype.card ι) ?_
    calc Fintype.card ι * ((e + 1) * (m - 1) + (m - 1))
        = ((e + 1) * (m - 1) + (m - 1)) * Fintype.card ι := mul_comm _ _
      _ ≤ (k + e - 1) * S.card + ((e + 1) * (m - 1) + (m - 1)) * Fintype.card ι :=
          Nat.le_add_left _ _
      _ < Fintype.card ι * S.card := hbudget
  have hS : (e + 1) * (m - 1) < S.card := by omega
  -- L2.2: the bivariate BW pair
  obtain ⟨A, B, hA0, hAX, hAZ, hBX, hBZ, hBW⟩ :=
    bw_bivariate_solution_of_closeN hpt hke hkn hclose hS
  -- the two PS line families (L2.3)
  have hvert : ∀ x ∈ Finset.univ.image pt, ∃ q : Polynomial F,
      B.map (evalRingHom x) = A.map (evalRingHom x) * q ∧
        q.natDegree ≤ ((e + 1) * (m - 1) + (m - 1)) - (e + 1) * (m - 1) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨curvePoly fun j => u j i, hBW i, ?_⟩
    have := curvePoly_natDegree_le fun j => u j i
    omega
  have hhoriz : ∀ z ∈ S, ∃ q : Polynomial F,
      B.eval (Polynomial.C z) = A.eval (Polynomial.C z) * q ∧
        q.natDegree ≤ (k + e - 1) - e := by
    intro z hz
    obtain ⟨q, hq, hqd⟩ := bw_horizontal_line hpt hn hke hAX hBX hBW (hclose z hz)
    exact ⟨q, hq, by omega⟩
  have hcardX : (Finset.univ.image pt).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hpt, Finset.card_univ]
  have hbud : (k + e - 1) * S.card
      + ((e + 1) * (m - 1) + (m - 1)) * (Finset.univ.image pt).card
      < (Finset.univ.image pt).card * S.card := by
    rw [hcardX]
    exact hbudget
  -- L3.2: Polishchuk–Spielman
  obtain ⟨Q, hfac, hQX, hQZ⟩ := polishchuk_spielman A B e ((e + 1) * (m - 1))
    (k + e - 1) ((e + 1) * (m - 1) + (m - 1)) (Finset.univ.image pt) S
    hAX hAZ hBX (le_trans hBZ (Nat.le_add_right _ _)) (by omega) (Nat.le_add_right _ _)
    hvert hhoriz hbud
  -- L4: the factorization closes the interleaved distance
  exact interleavedClose_of_bw_factorization hpt u hA0 hAX (by omega) hBW hfac

/-! ## Non-vacuity — the composition FIRES end to end on RS(3,1)/ZMod 7

Domain {0,1,2} ⊂ ZMod 7, constants as the code (k = 1), radius e = 1 (UD: 2·1+1 = 3 ≤ 3),
words `u₀ = ![0,0,1]` (GENUINELY 1-far from every constant), `u₁ = 0`, challenges
S = {0,1,2,3,4}: every fold `u₀ + z·u₁ = u₀` is 1-close, and the PS budget holds with
room to spare: `1·5 + 3·3 = 14 < 15 = 3·5`. -/
section Fire

/-- The 3-point domain 0,1,2 in ZMod 7. -/
def ptF : Fin 3 → ZMod 7 := fun i => (i.val : ZMod 7)

theorem ptF_inj : Function.Injective ptF := by decide

/-- The word pair of the firing instance: `u₀` is corrupted at the point 2, `u₁ = 0`. -/
def wF : Fin 2 → Fin 3 → ZMod 7 := ![![0, 0, 1], ![0, 0, 0]]

-- u₀ really is 1-far from the closest codeword (distance EXACTLY 1, and ≥ 1 from every
-- constant): the conclusion below is not vacuously 0-far.
#guard hammingDist (wF 0) (fun _ => (0 : ZMod 7)) = 1
#guard ∀ c : ZMod 7, 1 ≤ hammingDist (wF 0) (fun _ => c)

/-- Every challenge in S = {0,…,4} is good: the fold collapses to `u₀`, 1-close to the
zero codeword. -/
theorem fire_close : ∀ z ∈ ({0, 1, 2, 3, 4} : Finset (ZMod 7)),
    closeN (RScode ptF 1 : Set (Fin 3 → ZMod 7)) 1
      (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * wF j x) := by
  intro z _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  have hfold : (fun x => ∑ j : Fin 2, z ^ (j : ℕ) * wF j x) = wF 0 := by
    funext x
    rw [Fin.sum_univ_two]
    have h1 : wF 1 x = 0 := by fin_cases x <;> rfl
    rw [h1, mul_zero, add_zero]
    norm_num
  rw [hfold]
  decide

/-- **L2.2 FIRES**: the bivariate BW pair exists on the real corrupted instance, with
every degree bound inhabited at the stated values. -/
theorem bw_bivariate_fires :
    ∃ A B : (ZMod 7)[X][Y], A ≠ 0 ∧ sdeg A ≤ 1 ∧ A.natDegree ≤ 2 ∧ sdeg B ≤ 1 ∧
      B.natDegree ≤ 2 ∧ ∀ i, B.map (evalRingHom (ptF i))
        = A.map (evalRingHom (ptF i)) * curvePoly fun j => wF j i :=
  bw_bivariate_solution_of_closeN ptF_inj (by omega) (by decide) fire_close (by decide)

/-- **THE COMPOSITION FIRES END TO END**: L1 kernels → L2 bivariate pair →
Polishchuk–Spielman → L4 factorization, concluding simultaneous 1-closeness of the
genuinely-corrupted pair to RS(3,1). -/
theorem correlated_agreement_fires :
    interleavedClose (RScode ptF 1 : Set (Fin 3 → ZMod 7)) wF 1 :=
  interleavedClose_of_good_challenges ptF_inj (by omega) (by decide) fire_close (by decide)

end Fire

/-! ## Axiom hygiene — every keystone pinned to the three kernel axioms -/

#assert_all_clean [natDegree_det_le_sum, ofCoeffs_coeff, ofCoeffs_coeff_of_le,
  ofCoeffs_natDegree_lt, ofCoeffs_eval, ofCoeffs_eq_zero_iff, snoc_injective_of_notMem,
  det_snoc_expansion, exists_kernel_of_minors_vanish, bwMatrix_natDegree_le,
  bwMatrix_degree_budget, bwMatrix_specialized_kernel, bwMatrix_minor_eq_zero,
  bw_bivariate_solution_of_closeN, bw_horizontal_line,
  interleavedClose_of_good_challenges, ptF_inj, fire_close, bw_bivariate_fires,
  correlated_agreement_fires]

end Dregg2.Circuit.CorrelatedAgreement
