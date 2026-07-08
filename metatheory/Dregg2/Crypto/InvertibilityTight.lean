/-
# `Dregg2.Crypto.InvertibilityTight` — the TIGHT Lyubashevsky–Seiler invertibility
threshold `q^(d/n)`, via residue-degree multiplicity `q^d ∣ N(v)`.

`InvertibilityHadamard` proved the general-`(n, q)` bound at the `q^(1/n)` (Hadamard)
threshold: `‖v‖₂ⁿ < q ⟹ IsUnit v̄`, from `q ∣ N(v) ≠ 0 ⟹ q ≤ |N(v)| ≤ ‖v‖₂ⁿ`. THIS file
strengthens the LOWER bound on `|N(v)|` from `q` to `q^d`, where `d` is the residue degree
of the prime the non-unit `v̄` falls into — giving the tight threshold `‖v‖₂ⁿ < q^d`.

**THE ONE MISSING FACT, and how it is proved here** (`residue_card_dvd_det` /
`q_pow_residueDeg_dvd_det`): if `v ≠ 0` reduces to a non-unit in `R_q = ℤ_q[X]/(Xⁿ+1)`,
it lies in a maximal ideal `m` of `R_q`; pulling back along the surjection
`R = ℤ[X]/(Xⁿ+1) → R_q → R_q/m` gives a prime `P = ker ψ ∋ v` with residue field
`R/P ≅ R_q/m ≅ 𝔽_{q^d}` (`d` = the `𝔽_q`-dimension of the residue field, i.e. the residue
degree `f(P)`). Then the IDEAL-NORM multiplicity:

  `q^d = |R/P|  ∣  |R/(v)| = |N(v)|`

- `|R/P| ∣ |R/(v)|` is subgroup-index divisibility (`AddSubgroup.index_dvd_of_le`,
  since `(v) ≤ P` — this is exactly `N(P) ∣ N(v)` for the absolute ideal norm, done at the
  index level so that NO `IsDedekindDomain` instance is needed; in this Mathlib
  `Ideal.absNorm` demands Dedekind, but the two facts feeding the bound do not).
- `|R/(v)| = |N(v)|` is the Smith-normal-form lattice-index theorem
  (`Submodule.natAbs_det_equiv`, only needs `R` free finite over ℤ + `IsDomain R`;
  `IsDomain` comes from irreducibility of `Xⁿ+1 = Φ_{2n}` over ℤ — `n = 2^k`, so `2n` is a
  prime power and `ℤ[X]/(Xⁿ+1) = ℤ[ζ_{2n}]`, though the full ring-of-integers
  identification is never needed).
- `|R_q/m| = q^d` is finite-field cardinality (`Module.card_eq_pow_finrank`).

Combined with the parent's Hadamard bound `|N(v)| ≤ ‖v‖₂ⁿ` (`sq_det_le_pow_int`):
`q^d ≤ ‖v‖₂ⁿ`, contrapositive `‖v‖₂ⁿ < q^d ⟹ IsUnit v̄`.

**HEADLINES:**
- `q_pow_residueDeg_dvd_det` — the multiplicity itself: `q^{f(P)} ∣ |N(v)|`.
- `norm_sq_lt_isUnit_tight` / `norm_lt_isUnit_tight` — `v ≠ 0`, every prime above `q` has
  residue degree `≥ d`, `‖v‖₂ⁿ < q^d` ⟹ `IsUnit v̄`. At `d = 1` this recovers Hadamard;
  at `d = n` (inert) the hypothesis is `‖v‖₂ⁿ < qⁿ` — any `‖v‖₂ < q` works, matching
  `R_q` being a field.
- Residue-degree dischargers, both proved:
  - `finrank_ge_two_of_no_root` — `Xⁿ+1` has NO root in `𝔽_q` (a `decide`-able check)
    ⟹ every residue degree `≥ 2`. (A degree-1 residue field forces an `𝔽_q`-point of
    `Xⁿ+1`, via the image of `root` under `R_q → R_q/m ≅ 𝔽_q`.)
  - `le_finrank_of_isCoprime` — `Xⁿ+1` coprime to `X^{q^e} − X` for all `0 < e < d`
    ⟹ every residue degree `≥ d`. (The image `a` of `root` GENERATES the residue field
    `L = 𝔽_q[a]`, `|L| = q^e`, so `a` is a common root of `Xⁿ+1` and `X^{q^e} − X`;
    a Bézout certificate evaluates to `0 = 1`.) This is the fully-general-`d` bridge —
    the classical fact that the degree-`< d` irreducible factors of `Xⁿ+1` mod `q` are
    exactly its common factors with `X^{q^e} − X`.
- The weld: `challenge_diff_isUnit_tight` + `lossiness_discharges_nonzero_tight`
  (feeds `HermineDischarge.lossiness_discharges_nonzero`, same seam as the parent).
- **Non-vacuity STRICTLY BEYOND Hadamard**: at `n = 2, q = 3` (inert, `d = 2`) the vector
  `v = (2,2)` with `‖v‖₂² = 8` satisfies the tight bound `8² = 64 < 81 = 3⁴` but MISSES the
  Hadamard bound (`64 ≥ 9 = 3²`) — `demo2_tight_isUnit` + `hadamard_misses_w2`. Same at
  `n = 4, q = 3` (`d = 2`, `3` has order 2 mod 8) for the literal challenge difference
  `1 − X`: `2⁴ = 16 < 81` but `16 ≥ 9` — `demo4_challenge_diff_tight`.

**HONEST GAP:** `d` enters as a LOWER bound on all residue degrees (the useful direction),
discharged decidably for `d = 2` (no-root) and by Bézout certificate for general `d`
(`le_finrank_of_isCoprime`). The exact equality `d = ord_{2n}(q)` (the multiplicative-order
formula for the splitting of `q` in `ℚ(ζ_{2n})`) is NOT formalized — it is not needed for
the invertibility direction, only for computing the optimal `d` per `(n, q)` on paper.
Concrete instances at `d > 2` therefore need a supplied coprimality certificate rather
than a `decide`.
-/
import Dregg2.Crypto.InvertibilityHadamard
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Index
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Norm.Defs

set_option linter.unusedSectionVars false

namespace Dregg2.Crypto.InvertibilityTight

open Dregg2.Crypto.InvertibilityHadamard
open Polynomial
open Module (Basis)

/-! ## 1. `R = ℤ[X]/(Xⁿ+1)` is a DOMAIN for `n = 2^k` (irreducibility of `Φ_{2n}` over ℤ) -/

theorem fpoly_int_eq_cyclotomic (k : ℕ) :
    fpoly ℤ (2 ^ k) = Polynomial.cyclotomic (2 ^ (k + 1)) ℤ := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two,
    Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  rw [fpoly, add_comm]

theorem fpoly_int_irreducible (k : ℕ) : Irreducible (fpoly ℤ (2 ^ k)) := by
  rw [fpoly_int_eq_cyclotomic]
  exact Polynomial.cyclotomic.irreducible (pow_pos (by norm_num) _)

theorem fpoly_int_prime (k : ℕ) : Prime (fpoly ℤ (2 ^ k)) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (fpoly_int_irreducible k)

theorem aqZ_isDomain (k : ℕ) : IsDomain (Aq ℤ (2 ^ k)) := by
  haveI : (Ideal.span {fpoly ℤ (2 ^ k)}).IsPrime :=
    (Ideal.span_singleton_prime (fpoly_int_prime k).ne_zero).mpr (fpoly_int_prime k)
  exact Ideal.Quotient.isDomain _

/-! ## 2. The lattice-index value of a principal ideal: `|R/(r)| = |N(r)|`
(the Smith-normal-form step, general free-finite ℤ-domain — no Dedekind needed) -/

theorem natCard_quot_span_singleton {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ S) {r : S} (hr : r ≠ 0) :
    Nat.card (S ⧸ (Ideal.span {r} : Ideal S)) = (Algebra.norm ℤ r).natAbs := by
  haveI : Module.Free ℤ S := Module.Free.of_basis b
  haveI : Module.Finite ℤ S := Module.Finite.of_basis b
  have hcard : Nat.card (S ⧸ (Ideal.span {r} : Ideal S))
      = Nat.card (S ⧸ ((Ideal.span {r} : Ideal S).restrictScalars ℤ)) :=
    (Nat.card_congr
      (Submodule.Quotient.restrictScalarsEquiv ℤ
        (Ideal.span {r} : Ideal S)).toEquiv).symm
  -- the Smith-normal-form index theorem, against the basis `(r·bᵢ)` of `(r)`
  have hdet := Submodule.natAbs_det_basis_change b
      ((Ideal.span {r} : Ideal S).restrictScalars ℤ) (Ideal.basisSpanSingleton b hr)
  -- the element norm is the SAME determinant
  have hnorm : Algebra.norm ℤ r = b.det (fun i => r * b i) := by
    rw [Algebra.norm_eq_matrix_det b, Module.Basis.det_apply]
    congr 1
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.toMatrix_apply]
  rw [hcard, ← hdet]
  congr 1
  rw [hnorm]
  congr 1

/-! ## 3. Surjectivity of the reduction `ℤ[X]/(Xⁿ+1) → ℤ_q[X]/(Xⁿ+1)` -/

theorem mapHom_zmod_surjective (n q : ℕ) [NeZero n] [Fact q.Prime] :
    Function.Surjective (mapHom ℤ n (ZMod q) (Int.castRingHom (ZMod q))) := by
  intro y
  choose w hw using fun i => ZMod.intCast_surjective ((bas (ZMod q) n).repr y i)
  refine ⟨eltv ℤ n w, ?_⟩
  rw [mapHom_eltv]
  have hcoe : (fun i => (Int.castRingHom (ZMod q)) (w i))
      = fun i => (bas (ZMod q) n).repr y i := by
    funext i
    simpa only [Int.coe_castRingHom] using hw i
  rw [hcoe, eltv, ← Basis.equivFun_apply, LinearEquiv.symm_apply_apply]

/-! ## 4. Residue-field cardinality: `|R_q/m| = q^d`, `d` = the residue degree -/

section ResidueField

variable {n q : ℕ} [NeZero n] [Fact q.Prime]

theorem natCard_quot_eq_pow_finrank (m : Ideal (Aq (ZMod q) n)) :
    Nat.card (Aq (ZMod q) n ⧸ m)
      = q ^ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) := by
  haveI : Finite (Aq (ZMod q) n) :=
    Finite.of_equiv _ (bas (ZMod q) n).equivFun.toEquiv.symm
  haveI : Finite (Aq (ZMod q) n ⧸ m) :=
    Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Fintype (Aq (ZMod q) n ⧸ m) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]

/-- The residue degree is positive (the residue field of a maximal ideal is a nontrivial
finite `𝔽_q`-space). Proved from the cardinality formula, avoiding torsion-free instances. -/
theorem finrank_quot_pos (m : Ideal (Aq (ZMod q) n)) (hm : m.IsMaximal) :
    0 < Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) := by
  haveI : Finite (Aq (ZMod q) n) :=
    Finite.of_equiv _ (bas (ZMod q) n).equivFun.toEquiv.symm
  haveI : Finite (Aq (ZMod q) n ⧸ m) :=
    Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Nontrivial (Aq (ZMod q) n ⧸ m) :=
    Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  by_contra h
  have h0 : Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) = 0 := by omega
  have hcard := natCard_quot_eq_pow_finrank m
  rw [h0, pow_zero] at hcard
  have h2 : 1 < Nat.card (Aq (ZMod q) n ⧸ m) := Finite.one_lt_card
  omega

end ResidueField

/-! ## 5. THE ONE MISSING FACT: `q^d = |R/P| ∣ |N(v)|` for the prime `P` over the
maximal ideal `m ∋ v̄` — the ideal-norm multiplicity, at the subgroup-index level -/

section Core

variable {n q : ℕ} [NeZero n] [Fact q.Prime]

/-- **The residue-field cardinality divides the element norm.** If `v̄ ∈ m` (any proper
ideal of `R_q`), then `|R_q/m|` divides `|N(v)| = |det(mulMat v)|`. Instantiated at a
maximal `m` this is `N(P) ∣ N((v))` for the prime `P` above `q` containing `v`. -/
theorem residue_card_dvd_det (hn2 : ∃ k, n = 2 ^ k) (v : Fin n → ℤ) (hv : v ≠ 0)
    (m : Ideal (Aq (ZMod q) n))
    (hmem : eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q)) ∈ m) :
    Nat.card (Aq (ZMod q) n ⧸ m) ∣ ((mulMat ℤ n v).det).natAbs := by
  obtain ⟨k, rfl⟩ := hn2
  haveI : IsDomain (Aq ℤ (2 ^ k)) := aqZ_isDomain k
  haveI : Module.Free ℤ (Aq ℤ (2 ^ k)) := Module.Free.of_basis (bas ℤ (2 ^ k))
  haveI : Module.Finite ℤ (Aq ℤ (2 ^ k)) := Module.Finite.of_basis (bas ℤ (2 ^ k))
  have hx0 : eltv ℤ (2 ^ k) v ≠ 0 := by
    rw [Ne, eltv_eq_zero_iff]; exact hv
  -- the composite reduction map `R → R_q → R_q/m`, and its kernel `P`
  let ψ : Aq ℤ (2 ^ k) →+* (Aq (ZMod q) (2 ^ k) ⧸ m) :=
    (Ideal.Quotient.mk m).comp (mapHom ℤ (2 ^ k) (ZMod q) (Int.castRingHom (ZMod q)))
  have hsurj : Function.Surjective ψ :=
    Ideal.Quotient.mk_surjective.comp (mapHom_zmod_surjective (2 ^ k) q)
  have hxker : eltv ℤ (2 ^ k) v ∈ RingHom.ker ψ := by
    rw [RingHom.mem_ker]
    show (Ideal.Quotient.mk m)
      (mapHom ℤ (2 ^ k) (ZMod q) (Int.castRingHom (ZMod q)) (eltv ℤ (2 ^ k) v)) = 0
    rw [mapHom_eltv]
    simp only [Int.coe_castRingHom]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  -- `R/P ≅ R_q/m` (first isomorphism theorem)
  have hquot : Nat.card (Aq (ZMod q) (2 ^ k) ⧸ m)
      = Nat.card (Aq ℤ (2 ^ k) ⧸ RingHom.ker ψ) :=
    (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm
  -- index divisibility `(v) ≤ P ⟹ |R/P| ∣ |R/(v)|` — this is `N(P) ∣ N((v))`
  have hle : Ideal.span {eltv ℤ (2 ^ k) v} ≤ RingHom.ker ψ :=
    (Ideal.span_singleton_le_iff_mem _).mpr hxker
  have hdvd : Nat.card (Aq ℤ (2 ^ k) ⧸ RingHom.ker ψ)
      ∣ Nat.card (Aq ℤ (2 ^ k) ⧸ Ideal.span {eltv ℤ (2 ^ k) v}) := by
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact AddSubgroup.index_dvd_of_le fun a ha => hle ha
  -- the principal-ideal index is the norm (Smith normal form)
  have hval : Nat.card (Aq ℤ (2 ^ k) ⧸ Ideal.span {eltv ℤ (2 ^ k) v})
      = (Algebra.norm ℤ (eltv ℤ (2 ^ k) v)).natAbs :=
    natCard_quot_span_singleton (bas ℤ (2 ^ k)) hx0
  have hnorm : Algebra.norm ℤ (eltv ℤ (2 ^ k) v) = (mulMat ℤ (2 ^ k) v).det :=
    Algebra.norm_eq_matrix_det (bas ℤ (2 ^ k)) (eltv ℤ (2 ^ k) v)
  rw [hquot]
  rw [hval, hnorm] at hdvd
  exact hdvd

/-- **THE MULTIPLICITY, in its named form: `q^{f(P)} ∣ N(v)`.** The residue degree
`f(P) = dim_{𝔽_q}(R_q/m)` of the prime containing `v` gives `q^{f(P)}` dividing the
integer norm of `v` — the fact the Hadamard file could not reach (it only had `q¹ ∣ N(v)`). -/
theorem q_pow_residueDeg_dvd_det (hn2 : ∃ k, n = 2 ^ k) (v : Fin n → ℤ) (hv : v ≠ 0)
    (m : Ideal (Aq (ZMod q) n))
    (hmem : eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q)) ∈ m) :
    q ^ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) ∣ ((mulMat ℤ n v).det).natAbs := by
  rw [← natCard_quot_eq_pow_finrank m]
  exact residue_card_dvd_det hn2 v hv m hmem

end Core

/-! ## 6. THE TIGHT THEOREM: `‖v‖₂ⁿ < q^d ⟹ IsUnit v̄`, `d` ≤ every residue degree -/

section Main

variable {n q : ℕ} [NeZero n] [Fact q.Prime]

/-- **THE TIGHT LYUBASHEVSKY–SEILER BOUND, squared (ℤ-exact) form.** If every maximal
ideal of `R_q` has residue degree `≥ d` (equivalently: every irreducible factor of
`Xⁿ+1` mod `q` has degree `≥ d`), then a nonzero integer vector `v` with
`(∑ vᵢ²)ⁿ < q^(2d)` — that is, `‖v‖₂ⁿ < q^d` — is a UNIT in `R_q`. At `d = 1` this is
the parent's Hadamard bound; at `d = n` (inert `q`) it is the field case. -/
theorem norm_sq_lt_isUnit_tight (hn2 : ∃ k, n = 2 ^ k) (d : ℕ)
    (hd : ∀ m : Ideal (Aq (ZMod q) n), m.IsMaximal →
      d ≤ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m))
    (v : Fin n → ℤ) (hv : v ≠ 0)
    (hbound : (∑ i, v i ^ 2) ^ n < (q : ℤ) ^ (2 * d)) :
    IsUnit (eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))) := by
  by_contra hnu
  haveI : Nontrivial (Aq (ZMod q) n) := ⟨0, 1, zero_ne_one_aq (ZMod q) n⟩
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)
  have hdvd := residue_card_dvd_det hn2 v hv m hmem
  have hdet0 : (mulMat ℤ n v).det ≠ 0 := det_mulMat_ne_zero hn2 v hv
  have hq : q.Prime := Fact.out
  -- `q^d ≤ |R_q/m| ≤ |N(v)|`
  have hqd : q ^ d ≤ ((mulMat ℤ n v).det).natAbs := by
    have h1 : q ^ d ≤ Nat.card (Aq (ZMod q) n ⧸ m) := by
      rw [natCard_quot_eq_pow_finrank m]
      exact Nat.pow_le_pow_right hq.pos (hd m hm)
    exact h1.trans (Nat.le_of_dvd (Int.natAbs_pos.mpr hdet0) hdvd)
  have hZ : (q : ℤ) ^ d ≤ |(mulMat ℤ n v).det| := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hqd
  have hsq : (q : ℤ) ^ (2 * d) ≤ ((mulMat ℤ n v).det) ^ 2 := by
    have h0 : (0 : ℤ) ≤ (q : ℤ) ^ d := by positivity
    calc (q : ℤ) ^ (2 * d) = ((q : ℤ) ^ d) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ |(mulMat ℤ n v).det| ^ 2 := pow_le_pow_left₀ h0 hZ 2
      _ = ((mulMat ℤ n v).det) ^ 2 := sq_abs _
  have hHad : ((mulMat ℤ n v).det) ^ 2 ≤ (∑ i, v i ^ 2) ^ n :=
    sq_det_le_pow_int (Nat.pos_of_ne_zero (NeZero.ne n)) (mulMat ℤ n v)
      (sum_sq_col ℤ n v)
  linarith

/-- **THE HEADLINE, literal `‖v‖₂ⁿ < q^d` form.** -/
theorem norm_lt_isUnit_tight (hn2 : ∃ k, n = 2 ^ k) (d : ℕ)
    (hd : ∀ m : Ideal (Aq (ZMod q) n), m.IsMaximal →
      d ≤ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m))
    (v : Fin n → ℤ) (hv : v ≠ 0)
    (hbound : (Real.sqrt (∑ i, (v i : ℝ) ^ 2)) ^ n < (q : ℝ) ^ d) :
    IsUnit (eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))) := by
  apply norm_sq_lt_isUnit_tight hn2 d hd v hv
  have hS : (0 : ℝ) ≤ ∑ i, (v i : ℝ) ^ 2 := by positivity
  have hsq : ((Real.sqrt (∑ i, (v i : ℝ) ^ 2)) ^ n) ^ 2 < ((q : ℝ) ^ d) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (Real.sqrt (∑ i, (v i : ℝ) ^ 2)) ^ n := by positivity
    nlinarith [hbound, h0]
  rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt hS, ← pow_mul, mul_comm d 2] at hsq
  have hcast : ((∑ i, v i ^ 2 : ℤ) : ℝ) = ∑ i, (v i : ℝ) ^ 2 := by push_cast; rfl
  rw [← hcast] at hsq
  exact_mod_cast hsq

end Main

/-! ## 7. Residue-degree dischargers (both PROVED — they turn checkable polynomial
conditions into the `hd` hypothesis) -/

section Dischargers

variable {n q : ℕ} [NeZero n] [Fact q.Prime]

/-- **`d ≥ 2` from no roots.** If `Xⁿ + 1` has no root in `𝔽_q` (decidable for concrete
`(n, q)`), every residue field has `𝔽_q`-dimension `≥ 2`. A dimension-1 residue field
`L = 𝔽_q·1` would make the image of `root` an `𝔽_q`-scalar `c` with `cⁿ + 1 = 0`. -/
theorem finrank_ge_two_of_no_root (hroot : ∀ a : ZMod q, a ^ n + 1 ≠ 0)
    (m : Ideal (Aq (ZMod q) n)) (hm : m.IsMaximal) :
    2 ≤ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) := by
  haveI := hm
  haveI : Nontrivial (Aq (ZMod q) n ⧸ m) :=
    Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  by_contra hlt
  have h1 : Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) = 1 := by
    have hpos := finrank_quot_pos m hm
    omega
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h1
    (one_ne_zero : (1 : Aq (ZMod q) n ⧸ m) ≠ 0)
    (Ideal.Quotient.mk m (AdjoinRoot.root (fpoly (ZMod q) n)))
  have haL : algebraMap (ZMod q) (Aq (ZMod q) n ⧸ m) c
      = Ideal.Quotient.mk m (AdjoinRoot.root (fpoly (ZMod q) n)) := by
    rw [← hc, Algebra.smul_def, mul_one]
  have key : algebraMap (ZMod q) (Aq (ZMod q) n ⧸ m) (c ^ n + 1) = 0 := by
    rw [map_add, map_pow, map_one, haL, ← map_pow, root_pow_eq_neg_one, map_neg,
      map_one, neg_add_cancel]
  have hinj : Function.Injective (algebraMap (ZMod q) (Aq (ZMod q) n ⧸ m)) :=
    RingHom.injective _
  exact hroot c (hinj (by rw [key, map_zero]))

/-- **General `d` from Bézout certificates.** If `Xⁿ + 1` is coprime to `X^{q^e} − X` in
`𝔽_q[X]` for every `0 < e < d`, then every residue field has `𝔽_q`-dimension `≥ d`.
The image `a` of `root` generates the residue field `L` (so `|L| = q^e` with
`e = dim L`), satisfies `aⁿ + 1 = 0`, and satisfies `a^{q^e} = a` (Frobenius);
a Bézout identity `u·(Xⁿ+1) + w·(X^{q^e}−X) = 1` evaluated at `a` yields `0 = 1`. -/
theorem le_finrank_of_isCoprime (d : ℕ)
    (hcop : ∀ e : ℕ, 0 < e → e < d →
      IsCoprime (fpoly (ZMod q) n) ((X : (ZMod q)[X]) ^ q ^ e - X))
    (m : Ideal (Aq (ZMod q) n)) (hm : m.IsMaximal) :
    d ≤ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) := by
  haveI := hm
  haveI : Finite (Aq (ZMod q) n) :=
    Finite.of_equiv _ (bas (ZMod q) n).equivFun.toEquiv.symm
  haveI : Finite (Aq (ZMod q) n ⧸ m) :=
    Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Fintype (Aq (ZMod q) n ⧸ m) := Fintype.ofFinite _
  haveI : Nontrivial (Aq (ZMod q) n ⧸ m) :=
    Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  letI : Field (Aq (ZMod q) n ⧸ m) := Ideal.Quotient.field m
  by_contra hlt
  obtain ⟨u, w, huw⟩ := hcop _ (finrank_quot_pos m hm) (not_le.mp hlt)
  set a : Aq (ZMod q) n ⧸ m :=
    Ideal.Quotient.mk m (AdjoinRoot.root (fpoly (ZMod q) n)) with ha
  have han : a ^ n = -1 := by
    rw [ha, ← map_pow, root_pow_eq_neg_one, map_neg, map_one]
  have hf0 : Polynomial.aeval a (fpoly (ZMod q) n) = 0 := by
    simp only [fpoly, map_add, map_pow, Polynomial.aeval_X, map_one, han,
      neg_add_cancel]
  have hcardL : Fintype.card (Aq (ZMod q) n ⧸ m)
      = q ^ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) := by
    have h := natCard_quot_eq_pow_finrank m
    rwa [Nat.card_eq_fintype_card] at h
  have hg0 : Polynomial.aeval a
      ((X : (ZMod q)[X]) ^ q ^ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m) - X) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, ← hcardL, FiniteField.pow_card, sub_self]
  have h01 := congrArg (Polynomial.aeval a) huw
  rw [map_add, map_mul, map_mul, hf0, hg0, mul_zero, mul_zero, add_zero, map_one] at h01
  exact zero_ne_one h01

/-- The `d = 2` tight theorem with the decidable no-root hypothesis, packaged:
`Xⁿ+1` rootless mod `q` and `(∑ vᵢ²)ⁿ < q⁴` ⟹ unit. This DOUBLES the Hadamard
log-threshold whenever `q` is a quadratic nonresidue situation for `Xⁿ+1`. -/
theorem norm_sq_lt_isUnit_of_no_root (hn2 : ∃ k, n = 2 ^ k)
    (hroot : ∀ a : ZMod q, a ^ n + 1 ≠ 0)
    (v : Fin n → ℤ) (hv : v ≠ 0)
    (hbound : (∑ i, v i ^ 2) ^ n < (q : ℤ) ^ 4) :
    IsUnit (eltv (ZMod q) n (fun i => ((v i : ℤ) : ZMod q))) := by
  refine norm_sq_lt_isUnit_tight hn2 2
    (fun m hm => finrank_ge_two_of_no_root hroot m hm) v hv ?_
  norm_num
  exact hbound

end Dischargers

/-! ## 8. The challenge-difference form + the `HermineDischarge` weld -/

section Weld

variable {n q : ℕ} [NeZero n] [Fact q.Prime]

/-- **Challenge differences at the TIGHT threshold**: distinct challenges with
`‖c − c'‖₂ⁿ < q^d` (squared form) have invertible difference in `R_q`. -/
theorem challenge_diff_isUnit_tight (hn2 : ∃ k, n = 2 ^ k) (d : ℕ)
    (hd : ∀ m : Ideal (Aq (ZMod q) n), m.IsMaximal →
      d ≤ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m))
    (c c' : Fin n → ℤ) (hcc : c ≠ c')
    (hbound : (∑ i, (c i - c' i) ^ 2) ^ n < (q : ℤ) ^ (2 * d)) :
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
  refine norm_sq_lt_isUnit_tight hn2 d hd (c - c') (sub_ne_zero.mpr hcc) ?_
  simpa only [Pi.sub_apply] using hbound

/-- **The discharge weld at the tight threshold**: `lossiness_discharges_nonzero` with the
`IsUnit (c − c')` leg supplied by the `q^(d/n)` bound instead of the `q^(1/n)` one —
admitting strictly larger challenge sets at the same `(n, q)`. -/
theorem lossiness_discharges_nonzero_tight (hn2 : ∃ k, n = 2 ^ k) (d : ℕ)
    (hd : ∀ m : Ideal (Aq (ZMod q) n), m.IsMaximal →
      d ≤ Module.finrank (ZMod q) (Aq (ZMod q) n ⧸ m))
    {M : Type*} [AddCommGroup M] [Module (Aq (ZMod q) n) M] [Lattice.ShortNorm M]
    (s s' : M) (z z' : M) (hss : s ≠ s') (c c' : Fin n → ℤ) (hcc : c ≠ c')
    (hbound : (∑ i, (c i - c' i) ^ 2) ^ n < (q : ℤ) ^ (2 * d)) :
    (z - z') - (eltv (ZMod q) n (fun i => ((c i : ℤ) : ZMod q))
        - eltv (ZMod q) n (fun i => ((c' i : ℤ) : ZMod q))) • s ≠ 0
      ∨ (z - z') - (eltv (ZMod q) n (fun i => ((c i : ℤ) : ZMod q))
        - eltv (ZMod q) n (fun i => ((c' i : ℤ) : ZMod q))) • s' ≠ 0 :=
  HermineDischarge.lossiness_discharges_nonzero s s' _ _ z z' hss
    (challenge_diff_isUnit_tight hn2 d hd c c' hcc hbound)

end Weld

/-! ## 9. Non-vacuity STRICTLY BEYOND the Hadamard threshold

At `n = 2, q = 3`: `X² + 1` has no root mod 3, so `q = 3` is INERT (`d = 2 = n`,
`R₃ = 𝔽₉`). The vector `v = (2, 2)` has `‖v‖₂² = 8`:
- tight bound FIRES: `8² = 64 < 81 = 3⁴`;
- Hadamard bound MISSES: `¬(8² < 9 = 3²)`.
At `n = 4, q = 3` (`3` has order 2 mod 8, so all factors of `X⁴+1` mod 3 are quadratic,
`d = 2`): the literal challenge difference `1 − X` fires the tight bound where Hadamard
misses. -/

section Demos

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem no_root_n2_q3 : ∀ a : ZMod 3, a ^ 2 + 1 ≠ 0 := by decide

def w2 : Fin 2 → ℤ := ![2, 2]

theorem w2_ne_zero : w2 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [w2] at h0

/-- **The tight theorem firing beyond Hadamard's reach**: `v = (2,2)` at `n = 2, q = 3`. -/
theorem demo2_tight_isUnit :
    IsUnit (eltv (ZMod 3) 2 (fun i => ((w2 i : ℤ) : ZMod 3))) := by
  refine norm_sq_lt_isUnit_of_no_root ⟨1, by norm_num⟩ no_root_n2_q3 w2 w2_ne_zero ?_
  have hsum : (∑ i, w2 i ^ 2) = 8 := by
    simp [w2, Fin.sum_univ_two]
  rw [hsum]
  norm_num

/-- The SAME vector is outside the Hadamard hypothesis: `¬(8² < 3²)`. The upgrade is real. -/
theorem hadamard_misses_w2 : ¬ ((8 : ℤ) ^ 2 < (3 : ℤ) ^ 2) := by norm_num

theorem no_root_n4_q3 : ∀ a : ZMod 3, a ^ 4 + 1 ≠ 0 := by decide

def c4 : Fin 4 → ℤ := ![1, 0, 0, 0]

def c4' : Fin 4 → ℤ := ![0, 1, 0, 0]

theorem c4_distinct : c4 ≠ c4' := by
  intro h
  have h0 := congrFun h 0
  simp [c4, c4'] at h0

/-- The challenge difference `1 − X` at `n = 4, q = 3` — invertible via the TIGHT bound
(`2⁴ = 16 < 81 = 3⁴`), while the Hadamard hypothesis fails (`¬(16 < 9)`). -/
theorem demo4_challenge_diff_tight :
    IsUnit (eltv (ZMod 3) 4 (fun i => ((c4 i : ℤ) : ZMod 3))
      - eltv (ZMod 3) 4 (fun i => ((c4' i : ℤ) : ZMod 3))) := by
  refine challenge_diff_isUnit_tight ⟨2, by norm_num⟩ 2
    (fun m hm => finrank_ge_two_of_no_root no_root_n4_q3 m hm) c4 c4' c4_distinct ?_
  have hsum : (∑ i, (c4 i - c4' i) ^ 2) = 2 := by
    simp [c4, c4', Fin.sum_univ_four]
  rw [hsum]
  norm_num

theorem hadamard_misses_c4_diff : ¬ ((2 : ℤ) ^ 4 < (3 : ℤ) ^ 2) := by norm_num

/-- The no-root hypothesis is LOAD-BEARING, not vacuously available: at `q = 5`
(`5 ≡ 1 mod 4`) `X² + 1` HAS a root mod 5, so the `d = 2` discharger correctly
refuses to fire there. -/
theorem q5_has_root : ¬ (∀ a : ZMod 5, a ^ 2 + 1 ≠ 0) := by decide

end Demos

/-! ## 10. Axiom hygiene -/

#assert_axioms fpoly_int_eq_cyclotomic
#assert_axioms fpoly_int_irreducible
#assert_axioms fpoly_int_prime
#assert_axioms aqZ_isDomain
#assert_axioms natCard_quot_span_singleton
#assert_axioms mapHom_zmod_surjective
#assert_axioms natCard_quot_eq_pow_finrank
#assert_axioms finrank_quot_pos
#assert_axioms residue_card_dvd_det
#assert_axioms q_pow_residueDeg_dvd_det
#assert_axioms norm_sq_lt_isUnit_tight
#assert_axioms norm_lt_isUnit_tight
#assert_axioms finrank_ge_two_of_no_root
#assert_axioms le_finrank_of_isCoprime
#assert_axioms norm_sq_lt_isUnit_of_no_root
#assert_axioms challenge_diff_isUnit_tight
#assert_axioms lossiness_discharges_nonzero_tight
#assert_axioms no_root_n2_q3
#assert_axioms w2_ne_zero
#assert_axioms demo2_tight_isUnit
#assert_axioms hadamard_misses_w2
#assert_axioms no_root_n4_q3
#assert_axioms c4_distinct
#assert_axioms demo4_challenge_diff_tight
#assert_axioms hadamard_misses_c4_diff
#assert_axioms q5_has_root

end Dregg2.Crypto.InvertibilityTight
