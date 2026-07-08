/-
# `Dregg2.Crypto.InvertibilityHadamard` — GENERAL-n challenge-difference invertibility,
via the algebra-norm + Hadamard argument. ANY `n = 2^k`, ANY prime `q`.

`InvertibilityNorm`/`InvertibilityNormGen` reached `n = 2` (all odd primes) and `n = 4`
(fully-split family) with `d`-dependent anisotropic-form tricks. THIS file closes the general
case those approaches could not: for EVERY power-of-two `n` and EVERY prime `q`, a nonzero
integer challenge difference `v` with `‖v‖₂ⁿ < q` is a UNIT in `R_q = ℤ_q[X]/(Xⁿ+1)` —
no resultant-height infrastructure, no per-splitting-type case analysis.

**THE ARGUMENT** (each step a theorem below):
1. `R = ℤ[X]/(Xⁿ+1)` acts on itself; multiplication by `v` has an `n×n` integer matrix
   `mulMat v` in the power basis (`Algebra.leftMulMatrix`). Multiplication by `root` is a
   SIGNED CYCLIC SHIFT of coordinates (`rootⁿ = −1`), so every column of `mulMat v` has the
   same squared Euclidean norm `∑ vᵢ² = ‖v‖₂²` (`sum_sq_col`) — no closed-form entries needed.
2. **Hadamard.** `(det mulMat v)² ≤ (∑ vᵢ²)ⁿ`, i.e. `|det| ≤ ‖v‖₂ⁿ` (`sq_det_le_pow_int`).
   Mathlib has NO Hadamard determinant inequality (checked: only `Matrix.det_le`, the
   `n!·xⁿ` Leibniz bound — the names `Matrix.det_le_prod_norm`/`abs_det_le_prod_norm` do not
   exist), so we PROVE the form we need: for a real matrix whose columns all have squared
   norm `c`, `det² = det(MᴴM) = ∏λᵢ ≤ (∑λᵢ/n)ⁿ = cⁿ` — spectral theorem
   (`IsHermitian.det_eq_prod_eigenvalues`, `trace_eq_sum_eigenvalues`,
   `PosSemidef.eigenvalues_nonneg`) plus weighted AM-GM
   (`Real.geom_mean_le_arith_mean_weighted`). For equal-norm columns this AM-GM form EQUALS
   Hadamard's bound (and is stronger in general).
3. **Nonvanishing.** For `n = 2^k`, `Xⁿ + 1 = Φ_{2n}` is irreducible over ℚ
   (`cyclotomic_prime_pow_eq_geom_sum` + `cyclotomic.irreducible_rat`), so `ℚ[X]/(Xⁿ+1)` is a
   FIELD and `v ≠ 0 ⟹ det mulMat v ≠ 0` over ℤ (`det_mulMat_ne_zero`) — this is
   `N(v) = det(mult-by-v) ≠ 0`, the norm-of-a-nonzero-element step, done at the matrix level.
4. **Combine.** If `v̄` were a NON-unit in `R_q` then (finite ring, `det ≠ 0 ⟹` unit via the
   inverse matrix, `isUnit_eltv_of_det_ne_zero`) `det ≡ 0 mod q`, so `q ∣ det ≠ 0`, so
   `q ≤ |det| ≤ ‖v‖₂ⁿ`. Contrapositive: `v ≠ 0 ∧ ‖v‖₂ⁿ < q ⟹ IsUnit v̄`
   (`norm_sq_lt_isUnit` in the ℤ-exact squared form `(∑vᵢ²)ⁿ < q²`; `norm_lt_isUnit` in the
   literal `‖v‖₂ⁿ < q` real form; `inf_norm_lt_isUnit` in ∞-norm form).

**HEADLINES:**
- `norm_lt_isUnit` / `norm_sq_lt_isUnit`: general-`(n, q)` low-norm ⟹ unit.
- `challenge_diff_isUnit_general_n`: distinct challenges with `‖c−c'‖₂ⁿ < q` have invertible
  difference — feeds `HermineDischarge.lossiness_discharges_nonzero` at GENERAL `n`
  (instantiated as `lossiness_discharges_nonzero_general_n`).
- Non-vacuity: fires concretely at `n = 8, q = 17` (`demo8_diff_isUnit` — beyond every prior
  file's reach) and `n = 4, q = 5` (`demo4_diff_isUnit`), with `norm_num`-discharged bounds.

**HONEST LIMITS:** the threshold is the Hadamard `q^(1/n)` shape (`‖v‖₂ⁿ < q`), WEAKER than
the tight Lyubashevsky–Seiler `q^(d/n)` (which needs the ideal-norm multiplicity `q^d ∣ N(v)`
per degree-`d` factor — genuinely more arithmetic than the norm bound). But it is FULLY
GENERAL in `n` (any power of two) and `q` (any prime), which no prior file achieved. For
ternary/sparse challenge differences (`‖v‖₂² ≤ 2·weight`) this already gives real parameter
coverage at every `n`.
-/
import Dregg2.Tactics
import Dregg2.Crypto.HermineDischarge
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Real.StarOrdered

set_option linter.unusedSectionVars false

namespace Dregg2.Crypto.InvertibilityHadamard

open Polynomial
open Module (Basis)
open scoped Matrix

/-! ## 1. The negacyclic ring `R[X]/(Xⁿ+1)` over an arbitrary base, with its power basis -/

section Ring

variable (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n]

/-- The negacyclic modulus `Xⁿ + 1`. -/
noncomputable def fpoly : R[X] := X ^ n + 1

theorem fpoly_monic : (fpoly R n).Monic := by
  have h1 : fpoly R n = X ^ n + C 1 := by rw [C_1]; rfl
  rw [h1]
  exact monic_X_pow_add_C _ (NeZero.ne n)

theorem fpoly_natDegree : (fpoly R n).natDegree = n := by
  have h1 : fpoly R n = X ^ n + C 1 := by rw [C_1]; rfl
  rw [h1, natDegree_X_pow_add_C]

/-- `Aq R n = R[X]/(Xⁿ+1)` — the negacyclic ring over base `R`. At `R = ZMod q` this is the
challenge ring `R_q`; at `R = ℚ` (with `n = 2^k`) it is the cyclotomic field. -/
abbrev Aq := AdjoinRoot (fpoly R n)

/-- The power basis `1, root, …, root^(n-1)` of `Aq R n`, reindexed to `Fin n`. -/
noncomputable def bas : Basis (Fin n) R (Aq R n) :=
  ((AdjoinRoot.powerBasis' (fpoly_monic R n)).basis).reindex
    (finCongr (fpoly_natDegree R n))

theorem bas_apply (i : Fin n) :
    bas R n i = AdjoinRoot.root (fpoly R n) ^ (i : ℕ) := by
  rw [bas, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp
  rfl

/-- The defining relation: `rootⁿ = −1`. -/
theorem root_pow_eq_neg_one :
    AdjoinRoot.root (fpoly R n) ^ n = -1 := by
  have h : (X ^ n + 1 : R[X]).eval₂ (AdjoinRoot.of (fpoly R n))
      (AdjoinRoot.root (fpoly R n)) = 0 := AdjoinRoot.eval₂_root (fpoly R n)
  simp only [eval₂_add, eval₂_X_pow, eval₂_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The element of `Aq R n` with coefficient vector `v` — `∑ vᵢ·rootⁱ`, packaged through the
basis' coordinate linear equivalence. -/
noncomputable def eltv (v : Fin n → R) : Aq R n := (bas R n).equivFun.symm v

theorem eltv_def' (v : Fin n → R) : eltv R n v = ∑ i, v i • bas R n i := by
  rw [eltv, Basis.equivFun_symm_apply]

theorem repr_eltv (v : Fin n → R) (i : Fin n) :
    (bas R n).repr (eltv R n v) i = v i := by
  rw [eltv, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem eltv_sub (v w : Fin n → R) :
    eltv R n (v - w) = eltv R n v - eltv R n w := by
  rw [eltv, eltv, eltv, map_sub]

theorem eltv_eq_zero_iff (v : Fin n → R) : eltv R n v = 0 ↔ v = 0 := by
  rw [eltv, LinearEquiv.map_eq_zero_iff]

/-- The multiplication-by-`eltv v` matrix in the power basis. Its columns are the coordinate
vectors of `v, X·v, …, X^(n−1)·v`; over ℤ its determinant is `Algebra.norm ℤ (eltv v)` — the
matrix form of the algebra norm (`Algebra.norm_eq_matrix_det`), used here directly. -/
noncomputable def mulMat (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (bas R n) (eltv R n v)

theorem mulMat_apply (v : Fin n → R) (i j : Fin n) :
    mulMat R n v i j = (bas R n).repr (eltv R n v * bas R n j) i :=
  Algebra.leftMulMatrix_eq_repr_mul _ _ _ _

/-! ## 2. Multiplication by `root` is a signed cyclic shift ⟹ all columns have norm `‖v‖₂` -/

/-- Multiplication by `root`, in coordinates: the signed cyclic shift. `root·y` has
coordinates `(−y_{n−1}, y_0, …, y_{n−2})`, because `root·rootⁱ = rootⁱ⁺¹` and `rootⁿ = −1`. -/
theorem root_mul_eq {m : ℕ} (y : Aq R (m + 1)) :
    AdjoinRoot.root (fpoly R (m + 1)) * y
      = eltv R (m + 1)
          (Fin.cons (-((bas R (m + 1)).repr y (Fin.last m)))
            (fun j => (bas R (m + 1)).repr y j.castSucc)) := by
  have hterm : ∀ i : Fin (m + 1),
      AdjoinRoot.root (fpoly R (m + 1)) * ((bas R (m + 1)).repr y i • bas R (m + 1) i)
        = (bas R (m + 1)).repr y i •
            AdjoinRoot.root (fpoly R (m + 1)) ^ ((i : ℕ) + 1) := by
    intro i
    rw [bas_apply, mul_smul_comm, ← pow_succ']
  conv_lhs => rw [← Basis.sum_repr (bas R (m + 1)) y, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]
  rw [eltv_def', Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, bas_apply, Fin.val_zero, pow_zero,
    Fin.val_castSucc, Fin.val_succ, Fin.val_last]
  rw [root_pow_eq_neg_one, smul_neg, neg_smul]
  exact add_comm _ _

theorem repr_root_mul {m : ℕ} (y : Aq R (m + 1)) (i : Fin (m + 1)) :
    (bas R (m + 1)).repr (AdjoinRoot.root (fpoly R (m + 1)) * y) i
      = (Fin.cons (-((bas R (m + 1)).repr y (Fin.last m)))
          (fun j => (bas R (m + 1)).repr y j.castSucc) : Fin (m + 1) → R) i := by
  rw [root_mul_eq, repr_eltv]

/-- The signed shift preserves the sum of squared coordinates. -/
theorem sum_sq_repr_root_mul {m : ℕ} (y : Aq R (m + 1)) :
    ∑ i, ((bas R (m + 1)).repr (AdjoinRoot.root (fpoly R (m + 1)) * y) i) ^ 2
      = ∑ i, ((bas R (m + 1)).repr y i) ^ 2 := by
  simp only [repr_root_mul]
  rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ, neg_sq]
  exact add_comm _ _

theorem sum_sq_repr_root_pow_mul (k : ℕ) (y : Aq R n) :
    ∑ i, ((bas R n).repr (AdjoinRoot.root (fpoly R n) ^ k * y) i) ^ 2
      = ∑ i, ((bas R n).repr y i) ^ 2 := by
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
    subst hm
    have hx : AdjoinRoot.root (fpoly R (m + 1)) ^ (k + 1) * y
        = AdjoinRoot.root (fpoly R (m + 1))
            * (AdjoinRoot.root (fpoly R (m + 1)) ^ k * y) := by
      rw [pow_succ', mul_assoc]
    simp only [hx]
    rw [sum_sq_repr_root_mul]
    exact ih

/-- **Every column of the multiplication matrix has squared norm `∑ vᵢ²`** — column `j` is the
coordinate vector of `rootʲ·v`, a `j`-fold signed shift of `v`. -/
theorem sum_sq_col (v : Fin n → R) (j : Fin n) :
    ∑ i, (mulMat R n v i j) ^ 2 = ∑ i, (v i) ^ 2 := by
  simp only [mulMat_apply]
  have h : eltv R n v * bas R n j
      = AdjoinRoot.root (fpoly R n) ^ (j : ℕ) * eltv R n v := by
    rw [bas_apply, mul_comm]
  simp only [h, sum_sq_repr_root_pow_mul, repr_eltv]

end Ring

/-! ## 3. Base-change transport: the multiplication matrix commutes with `ℤ → ℚ`, `ℤ → ZMod q` -/

section Transport

variable (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n]
variable (S : Type*) [CommRing S] [Nontrivial S]

theorem fpoly_map (g : R →+* S) : (fpoly R n).map g = fpoly S n := by
  simp [fpoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]

/-- The base-change ring hom `R[X]/(Xⁿ+1) → S[X]/(Xⁿ+1)` induced by `g : R →+* S`. -/
noncomputable def mapHom (g : R →+* S) : Aq R n →+* Aq S n :=
  AdjoinRoot.map g (fpoly R n) (fpoly S n) (by rw [fpoly_map R n S g])

theorem mapHom_root (g : R →+* S) :
    mapHom R n S g (AdjoinRoot.root (fpoly R n)) = AdjoinRoot.root (fpoly S n) := by
  simp [mapHom]

theorem mapHom_of (g : R →+* S) (a : R) :
    mapHom R n S g (AdjoinRoot.of (fpoly R n) a) = AdjoinRoot.of (fpoly S n) (g a) := by
  simp [mapHom]

theorem mapHom_bas (g : R →+* S) (i : Fin n) :
    mapHom R n S g (bas R n i) = bas S n i := by
  rw [bas_apply, bas_apply, map_pow, mapHom_root]

theorem mapHom_eltv (g : R →+* S) (v : Fin n → R) :
    mapHom R n S g (eltv R n v) = eltv S n (fun i => g (v i)) := by
  rw [eltv_def', eltv_def', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.algebraMap_eq, mapHom_bas, mapHom_of]

theorem repr_mapHom (g : R →+* S) (x : Aq R n) (i : Fin n) :
    (bas S n).repr (mapHom R n S g x) i = g ((bas R n).repr x i) := by
  have hx : eltv R n (fun j => (bas R n).repr x j) = x := by
    rw [eltv, ← Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  rw [← hx, mapHom_eltv, repr_eltv, repr_eltv]

theorem mulMat_map (g : R →+* S) (v : Fin n → R) :
    (mulMat R n v).map g = mulMat S n (fun i => g (v i)) := by
  ext i j
  rw [Matrix.map_apply, mulMat_apply, mulMat_apply, ← repr_mapHom, map_mul,
    mapHom_eltv, mapHom_bas]

/-- Determinants transport: `det(mulMat_S (g∘v)) = g(det(mulMat_ℤ v))`. This is the
"norm commutes with reduction" step, at the matrix level. -/
theorem det_mulMat_map (g : R →+* S) (v : Fin n → R) :
    (mulMat S n (fun i => g (v i))).det = g ((mulMat R n v).det) := by
  rw [← mulMat_map]
  exact (g.map_det (mulMat R n v)).symm

end Transport

/-! ## 4. The Hadamard-type determinant bound (proved — absent from Mathlib)

For a real square matrix all of whose columns have squared norm `c`:
`det² = det(MᴴM) = ∏λᵢ ≤ (∑λᵢ/N)ᴺ = cᴺ` (spectral theorem + AM-GM). For equal-norm columns
this coincides with Hadamard's inequality `|det| ≤ ∏‖colⱼ‖`. -/

theorem sq_det_le_pow_of_columns {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℝ) {c : ℝ} (hc : ∀ j, ∑ i, M i j ^ 2 = c) :
    M.det ^ 2 ≤ c ^ N := by
  have hc0 : 0 ≤ c := by
    rw [← hc ⟨0, hN⟩]
    positivity
  set A := Mᴴ * M with hA
  have hherm : A.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hpsd : A.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hdiag : ∀ j, A j j = c := by
    intro j
    rw [hA, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, star_trivial]
    simp_rw [← sq]
    exact hc j
  have htrace : A.trace = (N : ℝ) * c := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hdiag]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnn : ∀ i, 0 ≤ hherm.eigenvalues i := hpsd.eigenvalues_nonneg
  have hsum : ∑ i, hherm.eigenvalues i = (N : ℝ) * c := by
    have h := hherm.trace_eq_sum_eigenvalues
    rw [htrace] at h
    simpa [RCLike.ofReal_real_eq_id] using h.symm
  have hprod : A.det = ∏ i, hherm.eigenvalues i := by
    have h := hherm.det_eq_prod_eigenvalues
    simpa [RCLike.ofReal_real_eq_id] using h
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  -- AM-GM with uniform weights 1/N
  have hgm : ∏ i, hherm.eigenvalues i ^ ((N : ℝ)⁻¹)
      ≤ ∑ i, (N : ℝ)⁻¹ * hherm.eigenvalues i :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ _ _
      (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp)
      (fun i _ => hnn i)
  have hgm' : ∏ i, hherm.eigenvalues i ^ ((N : ℝ)⁻¹) ≤ c := by
    refine hgm.trans_eq ?_
    rw [← Finset.mul_sum, hsum]
    field_simp
  have hP0 : 0 ≤ ∏ i, hherm.eigenvalues i ^ ((N : ℝ)⁻¹) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hnn i) _
  have hpow : (∏ i, hherm.eigenvalues i ^ ((N : ℝ)⁻¹)) ^ N = ∏ i, hherm.eigenvalues i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (hherm.eigenvalues i ^ ((N : ℝ)⁻¹)) N,
      ← Real.rpow_mul (hnn i), inv_mul_cancel₀ hN', Real.rpow_one]
  have hdet2 : A.det = M.det ^ 2 := by
    rw [hA, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, sq]
  calc M.det ^ 2 = A.det := hdet2.symm
    _ = ∏ i, hherm.eigenvalues i := hprod
    _ = (∏ i, hherm.eigenvalues i ^ ((N : ℝ)⁻¹)) ^ N := hpow.symm
    _ ≤ c ^ N := by gcongr
    _ = c ^ N := rfl

/-- The integer form: an `n×n` integer matrix whose columns all have squared norm `c`
satisfies `det² ≤ cⁿ` — i.e. `|det| ≤ ‖col‖₂ⁿ`, Hadamard's bound for equal-norm columns. -/
theorem sq_det_le_pow_int {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℤ) {c : ℤ} (hc : ∀ j, ∑ i, M i j ^ 2 = c) :
    M.det ^ 2 ≤ c ^ N := by
  have hcols : ∀ j, ∑ i, (M.map (Int.cast : ℤ → ℝ)) i j ^ 2 = (c : ℝ) := by
    intro j
    simp only [Matrix.map_apply]
    rw [← hc j]
    push_cast
    rfl
  have hr := sq_det_le_pow_of_columns hN (M.map (Int.cast : ℤ → ℝ)) hcols
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det = ((M.det : ℤ) : ℝ) := by
    have h := (Int.castRingHom ℝ).map_det M
    exact h.symm
  rw [hdet] at hr
  exact_mod_cast hr

/-! ## 5. Nonvanishing over ℤ: irreducibility of `Xⁿ+1 = Φ_{2n}` for `n = 2^k` -/

/-- For `n = 2^k`, `Xⁿ + 1` is the `2n`-th cyclotomic polynomial, irreducible over ℚ. -/
theorem fpoly_irreducible_rat (k : ℕ) : Irreducible (fpoly ℚ (2 ^ k)) := by
  have h1 : fpoly ℚ (2 ^ k) = Polynomial.cyclotomic (2 ^ (k + 1)) ℚ := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two,
      Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
    rw [fpoly, add_comm]
  rw [h1]
  exact Polynomial.cyclotomic.irreducible_rat (pow_pos (by norm_num) _)

/-- **The nonvanishing-norm step**: for `n = 2^k` and `v ≠ 0` over ℤ, `det(mulMat v) ≠ 0`.
(`ℚ[X]/(Xⁿ+1)` is a field, so multiplication by the nonzero `v` is invertible there; the
determinant transports.) This is `Algebra.norm ℤ (eltv v) ≠ 0` in matrix form. -/
theorem det_mulMat_ne_zero {n : ℕ} [NeZero n] (hn2 : ∃ k, n = 2 ^ k)
    (v : Fin n → ℤ) (hv : v ≠ 0) : (mulMat ℤ n v).det ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn2
  haveI : Fact (Irreducible (fpoly ℚ (2 ^ k))) := ⟨fpoly_irreducible_rat k⟩
  -- the element is nonzero in the cyclotomic FIELD
  have hne : eltv ℚ (2 ^ k) (fun i => ((v i : ℤ) : ℚ)) ≠ 0 := by
    rw [Ne, eltv_eq_zero_iff]
    intro h0
    apply hv
    funext i
    have hi := congrFun h0 i
    simp only [Pi.zero_apply] at hi ⊢
    exact_mod_cast hi
  have hunit : IsUnit (eltv ℚ (2 ^ k) (fun i => ((v i : ℤ) : ℚ))) :=
    isUnit_iff_ne_zero.mpr hne
  have hMunit : IsUnit (mulMat ℚ (2 ^ k) (fun i => ((v i : ℤ) : ℚ))) :=
    hunit.map (Algebra.leftMulMatrix (bas ℚ (2 ^ k)))
  have hdetU : IsUnit (mulMat ℚ (2 ^ k) (fun i => ((v i : ℤ) : ℚ))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hMunit
  have htr := det_mulMat_map ℤ (2 ^ k) ℚ (Int.castRingHom ℚ) v
  simp only [Int.coe_castRingHom] at htr
  intro h0
  rw [h0] at htr
  simp only [Int.cast_zero] at htr
  exact hdetU.ne_zero htr

/-! ## 6. The finite-field side: nonzero determinant ⟹ unit in `R_q` -/

/-- Finite commutative ring: a non-zero-divisor is a unit. -/
theorem isUnit_of_mul_cancel {A : Type*} [CommRing A] [Finite A] {f : A}
    (hcancel : ∀ g : A, f * g = 0 → g = 0) : IsUnit f := by
  have hinj : Function.Injective (fun g : A => f * g) := by
    intro g g' h
    have hsub : f * (g - g') = 0 := by
      simp only at h
      rw [mul_sub, h, sub_self]
    exact sub_eq_zero.mp (hcancel _ hsub)
  obtain ⟨g, hg⟩ := Finite.injective_iff_surjective.mp hinj 1
  exact ⟨⟨f, g, hg, by rw [mul_comm]; exact hg⟩, rfl⟩

/-- Over a finite field `K`: if `det(mulMat v) ≠ 0` then `eltv v` is a unit in `K[X]/(Xⁿ+1)`.
(Multiplication by `eltv v` is injective — invert the matrix — hence `eltv v` is a
non-zero-divisor, hence a unit in the finite ring.) -/
theorem isUnit_eltv_of_det_ne_zero (K : Type*) [Field K] [Finite K] (n : ℕ) [NeZero n]
    (v : Fin n → K) (hdet : (mulMat K n v).det ≠ 0) : IsUnit (eltv K n v) := by
  haveI : Finite (Aq K n) := Finite.of_equiv (Fin n → K) (bas K n).equivFun.toEquiv.symm
  apply isUnit_of_mul_cancel
  intro y hy
  have h1 := Algebra.leftMulMatrix_mulVec_repr (bas K n) (eltv K n v) y
  rw [hy, map_zero] at h1
  -- h1 : mulMat *ᵥ ⇑(repr y) = 0 (as functions)
  have h2 : (⇑((bas K n).repr y) : Fin n → K) = 0 := by
    have hMdet : IsUnit (mulMat K n v).det := isUnit_iff_ne_zero.mpr hdet
    have hinv := Matrix.nonsing_inv_mul (mulMat K n v) hMdet
    calc (⇑((bas K n).repr y) : Fin n → K)
        = ((mulMat K n v)⁻¹ * mulMat K n v) *ᵥ ⇑((bas K n).repr y) := by
          rw [hinv, Matrix.one_mulVec]
      _ = (mulMat K n v)⁻¹ *ᵥ (mulMat K n v *ᵥ ⇑((bas K n).repr y)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (mulMat K n v)⁻¹ *ᵥ (Algebra.leftMulMatrix (bas K n) (eltv K n v)
            *ᵥ ⇑((bas K n).repr y)) := rfl
      _ = 0 := by rw [h1]; simp
  have h3 : (bas K n).repr y = 0 := by
    ext i
    simpa using congrFun h2 i
  exact ((bas K n).repr.map_eq_zero_iff).mp h3

/-! ## 7. THE GENERAL THEOREM: any `n = 2^k`, any prime `q` -/

section Main

variable {n q : ℕ} [NeZero n] [Fact q.Prime]

/-- **THE GENERAL-`(n, q)` INVERTIBILITY LEMMA, squared (ℤ-exact) form.** For ANY power of
two `n` and ANY prime `q`: a nonzero integer vector `v` with `(∑ vᵢ²)ⁿ < q²` — that is,
`‖v‖₂ⁿ < q` — reduces to a UNIT in `R_q = ℤ_q[X]/(Xⁿ+1)`. One proof, every `n = 2^k`, every
prime `q`: were `v̄` a non-unit, `q` would divide the nonzero norm `det(mulMat v)`, forcing
`q² ≤ det² ≤ (∑vᵢ²)ⁿ` by the Hadamard bound. -/
theorem norm_sq_lt_isUnit (hn2 : ∃ k, n = 2 ^ k) (v : Fin n → ℤ) (hv : v ≠ 0)
    (hbound : (∑ i, v i ^ 2) ^ n < (q : ℤ) ^ 2) :
    IsUnit (eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))) := by
  by_contra hnu
  -- the determinant over `ZMod q` must vanish
  have hdq : (mulMat (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))).det = 0 := by
    by_contra hd
    exact hnu (isUnit_eltv_of_det_ne_zero (ZMod q) n _ hd)
  -- transport: `q ∣ det(mulMat ℤ v)`
  have htr := det_mulMat_map ℤ n (ZMod q) (Int.castRingHom (ZMod q)) v
  simp only [Int.coe_castRingHom] at htr
  have hcast0 : (((mulMat ℤ n v).det : ℤ) : ZMod q) = 0 := by
    rw [← htr]
    exact hdq
  have hdvd : (q : ℤ) ∣ (mulMat ℤ n v).det :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcast0
  -- the determinant is nonzero (norm of a nonzero element of the cyclotomic order)
  have hd0 : (mulMat ℤ n v).det ≠ 0 := det_mulMat_ne_zero hn2 v hv
  -- so `q ≤ |det|`, hence `q² ≤ det²`
  have hqle : (q : ℤ) ≤ |(mulMat ℤ n v).det| :=
    Int.le_of_dvd (abs_pos.mpr hd0) ((dvd_abs _ _).mpr hdvd)
  have hq2 : (q : ℤ) ^ 2 ≤ ((mulMat ℤ n v).det) ^ 2 := by
    rw [← sq_abs ((mulMat ℤ n v).det)]
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
    nlinarith [hqle, hq0]
  -- Hadamard: `det² ≤ (∑ vᵢ²)ⁿ`
  have hHad : ((mulMat ℤ n v).det) ^ 2 ≤ (∑ i, v i ^ 2) ^ n :=
    sq_det_le_pow_int (Nat.pos_of_ne_zero (NeZero.ne n)) (mulMat ℤ n v)
      (sum_sq_col ℤ n v)
  linarith [hbound, hq2, hHad]

/-- **THE HEADLINE, literal `‖v‖₂ⁿ < q` form.** For any `n = 2^k` and prime `q`: `v ≠ 0` with
`(√(∑vᵢ²))ⁿ < q` is a unit in `R_q`. -/
theorem norm_lt_isUnit (hn2 : ∃ k, n = 2 ^ k) (v : Fin n → ℤ) (hv : v ≠ 0)
    (hbound : (Real.sqrt (∑ i, (v i : ℝ) ^ 2)) ^ n < (q : ℝ)) :
    IsUnit (eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))) := by
  apply norm_sq_lt_isUnit hn2 v hv
  have hS : (0 : ℝ) ≤ ∑ i, (v i : ℝ) ^ 2 := by positivity
  have hsq : ((Real.sqrt (∑ i, (v i : ℝ) ^ 2)) ^ n) ^ 2 < (q : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (Real.sqrt (∑ i, (v i : ℝ) ^ 2)) ^ n := by positivity
    nlinarith [hbound, h0]
  rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt hS] at hsq
  have hcast : ((∑ i, v i ^ 2 : ℤ) : ℝ) = ∑ i, (v i : ℝ) ^ 2 := by push_cast; rfl
  rw [← hcast] at hsq
  exact_mod_cast hsq

/-- The ∞-norm corollary: `‖v‖∞ ≤ B` with `(n·B²)ⁿ < q²` (i.e. `(√n·B)ⁿ < q`) ⟹ unit.
This is the form challenge sets are usually specified in. -/
theorem inf_norm_lt_isUnit (hn2 : ∃ k, n = 2 ^ k) (v : Fin n → ℤ) (hv : v ≠ 0)
    {B : ℤ} (hB : ∀ i, |v i| ≤ B) (hbound : ((n : ℤ) * B ^ 2) ^ n < (q : ℤ) ^ 2) :
    IsUnit (eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))) := by
  apply norm_sq_lt_isUnit hn2 v hv
  refine lt_of_le_of_lt ?_ hbound
  have hsum : ∑ i, v i ^ 2 ≤ (n : ℤ) * B ^ 2 := by
    calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin n, B ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs (v i)]
          have h0 : (0 : ℤ) ≤ |v i| := abs_nonneg _
          nlinarith [hB i]
      _ = (n : ℤ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h0 : (0 : ℤ) ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact pow_le_pow_left₀ h0 hsum n

/-- **THE CHALLENGE-DIFFERENCE FORM, GENERAL `n`.** Distinct integer challenges `c ≠ c'` whose
difference satisfies `‖c − c'‖₂ⁿ < q` (squared form) have INVERTIBLE difference in `R_q` —
exactly the `IsUnit (c − c')` that `HermineDischarge.lossiness_discharges_nonzero` consumes,
now at every power-of-two `n` and every prime `q`. -/
theorem challenge_diff_isUnit_general_n (hn2 : ∃ k, n = 2 ^ k)
    (c c' : Fin n → ℤ) (hcc : c ≠ c')
    (hbound : (∑ i, (c i - c' i) ^ 2) ^ n < (q : ℤ) ^ 2) :
    IsUnit (eltv (ZMod q) n (fun i => ((c i : ℤ) : ZMod q))
      - eltv (ZMod q) n (fun i => ((c' i : ℤ) : ZMod q))) := by
  have h1 : eltv (ZMod q) n (fun i => ((c i : ℤ) : ZMod q))
      - eltv (ZMod q) n (fun i => ((c' i : ℤ) : ZMod q))
      = eltv (ZMod q) n (fun i => (((c - c') i : ℤ) : ZMod q)) := by
    rw [← eltv_sub]
    congr 1
    funext i
    simp only [Pi.sub_apply]
    push_cast
    rfl
  rw [h1]
  refine norm_sq_lt_isUnit hn2 (c - c') (sub_ne_zero.mpr hcc) ?_
  simpa only [Pi.sub_apply] using hbound

/-- **The discharge weld at general `n`**: `lossiness_discharges_nonzero`, instantiated with
the challenge ring `R_q = ℤ_q[X]/(Xⁿ+1)` at ANY `n = 2^k` — the `IsUnit (c − c')` leg is now
supplied by the general norm bound instead of a per-`(n, q)` decision. -/
theorem lossiness_discharges_nonzero_general_n (hn2 : ∃ k, n = 2 ^ k)
    {M : Type*} [AddCommGroup M] [Module (Aq (ZMod q) n) M] [Lattice.ShortNorm M]
    (s s' : M) (z z' : M) (hss : s ≠ s') (c c' : Fin n → ℤ) (hcc : c ≠ c')
    (hbound : (∑ i, (c i - c' i) ^ 2) ^ n < (q : ℤ) ^ 2) :
    (z - z') - (eltv (ZMod q) n (fun i => ((c i : ℤ) : ZMod q))
        - eltv (ZMod q) n (fun i => ((c' i : ℤ) : ZMod q))) • s ≠ 0
      ∨ (z - z') - (eltv (ZMod q) n (fun i => ((c i : ℤ) : ZMod q))
        - eltv (ZMod q) n (fun i => ((c' i : ℤ) : ZMod q))) • s' ≠ 0 :=
  HermineDischarge.lossiness_discharges_nonzero s s' _ _ z z' hss
    (challenge_diff_isUnit_general_n hn2 c c' hcc hbound)

end Main

/-! ## 8. Non-vacuity: the theorem FIRES at `n = 8, q = 17` (beyond every prior file) and
`n = 4, q = 5`, with `norm_num`-level hypotheses -/

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Challenge difference `1 − X` over `n = 8`: `∑ vᵢ² = 2`, and `2⁸ = 256 < 289 = 17²`. -/
def v8 : Fin 8 → ℤ := ![1, -1, 0, 0, 0, 0, 0, 0]

theorem v8_ne_zero : v8 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [v8] at h0

/-- **General theorem firing at `n = 8 = 2³, q = 17`** — `R₁₇ = ℤ₁₇[X]/(X⁸+1)` has 17⁸ ≈ 7×10⁹
elements, far beyond any `decide`; the bound `2⁸ < 17²` is a `norm_num` fact. No prior file
reached any `n = 8` instance. -/
theorem demo8_diff_isUnit :
    IsUnit (eltv (ZMod 17) 8 (fun i => ((v8 i : ℤ) : ZMod 17))) := by
  refine norm_sq_lt_isUnit ⟨3, by norm_num⟩ v8 v8_ne_zero ?_
  have hsum : (∑ i, v8 i ^ 2) = 2 := by
    simp [v8, Fin.sum_univ_eight]
  rw [hsum]
  norm_num

/-- Challenge difference `1 − X` over `n = 4`: `∑ vᵢ² = 2`, and `2⁴ = 16 < 25 = 5²`. -/
def v4 : Fin 4 → ℤ := ![1, -1, 0, 0]

theorem v4_ne_zero : v4 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [v4] at h0

/-- The parent files' `n = 4, q = 5` point, recovered from the GENERAL theorem (no 625-element
`decide`, no CRT factor analysis — the same `norm_num` bound). -/
theorem demo4_diff_isUnit :
    IsUnit (eltv (ZMod 5) 4 (fun i => ((v4 i : ℤ) : ZMod 5))) := by
  refine norm_sq_lt_isUnit ⟨2, by norm_num⟩ v4 v4_ne_zero ?_
  have hsum : (∑ i, v4 i ^ 2) = 2 := by
    simp [v4, Fin.sum_univ_four]
  rw [hsum]
  norm_num

/-- The demo instance in literal challenge-difference form: `c = 1, c' = X` at `n = 8, q = 17`
have invertible difference — fed through `challenge_diff_isUnit_general_n` itself. -/
def c8 : Fin 8 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0]

def c8' : Fin 8 → ℤ := ![0, 1, 0, 0, 0, 0, 0, 0]

theorem c8_distinct : c8 ≠ c8' := by
  intro h
  have h0 := congrFun h 0
  simp [c8, c8'] at h0

theorem demo8_challenge_diff :
    IsUnit (eltv (ZMod 17) 8 (fun i => ((c8 i : ℤ) : ZMod 17))
      - eltv (ZMod 17) 8 (fun i => ((c8' i : ℤ) : ZMod 17))) := by
  refine challenge_diff_isUnit_general_n ⟨3, by norm_num⟩ c8 c8' c8_distinct ?_
  have hsum : (∑ i, (c8 i - c8' i) ^ 2) = 2 := by
    simp [c8, c8', Fin.sum_univ_eight]
  rw [hsum]
  norm_num

/-! ### Teeth: the conclusions are substantive and the hypothesis is load-bearing -/

/-- The general ring `R[X]/(Xⁿ+1)` is NONTRIVIAL — `IsUnit` conclusions have content. -/
theorem zero_ne_one_aq (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n] :
    (0 : Aq R n) ≠ 1 := by
  intro h
  have hb : (1 : Aq R n) = bas R n 0 := by
    rw [bas_apply]
    norm_num
  have h1 : (bas R n).repr (1 : Aq R n) 0 = 1 := by
    rw [hb, Basis.repr_self]
    simp
  rw [← h] at h1
  simp at h1

/-- Evaluation at `6`, an eighth root of `−1` mod 17 (`6⁸ = (6²)⁴ = 2⁴ = 16 = −1`):
one CRT factor map of `R₁₇ = ℤ₁₇[X]/(X⁸+1)`. -/
noncomputable def eval6 : Aq (ZMod 17) 8 →+* ZMod 17 :=
  AdjoinRoot.lift (RingHom.id (ZMod 17)) 6
    (by simp [fpoly]; decide)

/-- The element `X − 6` of `R₁₇` (as a coefficient vector). -/
noncomputable def sharp8 : Aq (ZMod 17) 8 :=
  eltv (ZMod 17) 8 ![(-6 : ZMod 17), 1, 0, 0, 0, 0, 0, 0]

theorem sharp8_ne_zero : sharp8 ≠ 0 := by
  rw [sharp8, Ne, eltv_eq_zero_iff]
  intro h
  have h1 := congrFun h 1
  simp at h1

/-- **TEETH at `n = 8, q = 17`**: `X − 6` is a nonzero NON-unit (it dies in the `eval6` CRT
factor) — so the low-norm hypothesis is load-bearing, not decoration. Its shortest ℤ-lift
`(−6, 1, 0, …)` has `∑vᵢ² = 37` with `37⁸ ≫ 17²`, correctly OUTSIDE the theorem's threshold
(`threshold_necessary_at_8`). -/
theorem sharp8_not_unit : ¬ IsUnit sharp8 := by
  intro h
  have h6 := h.map eval6
  have he : eval6 sharp8 = 0 := by
    rw [sharp8, eltv_def', map_sum]
    simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, bas_apply, map_mul, map_pow,
      eval6, AdjoinRoot.lift_of, AdjoinRoot.lift_root, RingHom.id_apply]
    rw [Fin.sum_univ_eight]
    decide
  rw [he] at h6
  exact not_isUnit_zero h6

/-- The norm threshold correctly EXCLUDES the non-unit's lift: `37⁸ ≥ 17²`. -/
theorem threshold_necessary_at_8 : ¬ ((37 : ℤ) ^ 8 < (17 : ℤ) ^ 2) := by norm_num

/-! ## 9. Axiom hygiene -/

#assert_axioms fpoly_monic
#assert_axioms fpoly_natDegree
#assert_axioms bas_apply
#assert_axioms root_pow_eq_neg_one
#assert_axioms repr_eltv
#assert_axioms eltv_sub
#assert_axioms eltv_eq_zero_iff
#assert_axioms mulMat_apply
#assert_axioms root_mul_eq
#assert_axioms repr_root_mul
#assert_axioms sum_sq_repr_root_mul
#assert_axioms sum_sq_repr_root_pow_mul
#assert_axioms sum_sq_col
#assert_axioms fpoly_map
#assert_axioms mapHom_root
#assert_axioms mapHom_of
#assert_axioms mapHom_bas
#assert_axioms mapHom_eltv
#assert_axioms repr_mapHom
#assert_axioms mulMat_map
#assert_axioms det_mulMat_map
#assert_axioms sq_det_le_pow_of_columns
#assert_axioms sq_det_le_pow_int
#assert_axioms fpoly_irreducible_rat
#assert_axioms det_mulMat_ne_zero
#assert_axioms isUnit_of_mul_cancel
#assert_axioms isUnit_eltv_of_det_ne_zero
#assert_axioms norm_sq_lt_isUnit
#assert_axioms norm_lt_isUnit
#assert_axioms inf_norm_lt_isUnit
#assert_axioms challenge_diff_isUnit_general_n
#assert_axioms lossiness_discharges_nonzero_general_n
#assert_axioms v8_ne_zero
#assert_axioms demo8_diff_isUnit
#assert_axioms v4_ne_zero
#assert_axioms demo4_diff_isUnit
#assert_axioms c8_distinct
#assert_axioms demo8_challenge_diff
#assert_axioms zero_ne_one_aq
#assert_axioms sharp8_ne_zero
#assert_axioms sharp8_not_unit
#assert_axioms threshold_necessary_at_8

end Dregg2.Crypto.InvertibilityHadamard
