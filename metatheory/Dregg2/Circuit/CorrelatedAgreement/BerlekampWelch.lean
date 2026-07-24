/-
# Dregg2.Circuit.CorrelatedAgreement.BerlekampWelch — rung L1: univariate Berlekamp–Welch

Rung L1 of the DAG in `docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md` §6,
over the L0 objects of `Scaffolding.lean` (`evalOn`, `RScode`, `closeN`). Generic in the
field `F` and the parameters `(n, k, e)` — no deployed constants here. All proven; no
`sorry`, every keystone `#assert_all_clean`.

The system (`bwSolution pt k e w A B`): `A ≠ 0`, `deg A ≤ e`, `deg B < k + e` (the
classical `≤ k + e − 1`, `degree`-strict so `B = 0` needs no case split), and
`A(pt i)·w i = B(pt i)` on the whole domain.

- **L1.1 solvability** (`bw_certified_of_closeN`, no injectivity/UD needed): `closeN`
  yields a solution built from the ERROR LOCATOR `A = ∏_{w i ≠ v i} (X − pt i)`, `B = A·P`
  — carrying the decoding certificate `A ∣ B ∧ deg (B/A) < k` for free.
- **L1.1 the honest iff** (`closeN_iff_bw_certified`): closeness ⟺ solvability WITH that
  certificate. ⚠ The NAIVE converse (bare solvability ⟹ closeness) is FALSE even under
  `2e + k ≤ n` — `bw_naive_converse_false` refutes it concretely: over ZMod 7 on 5 points
  at `(k,e) = (1,2)` the root-free pair `(X²+1, X²)` solves the system at the
  rational-function word ![0,4,5,3,3], which is 3-far from the constant code. This is why
  the iff carries the certificate; it is also harmless downstream — the L2 bivariate lift
  consumes only the solvability direction, and Polishchuk–Spielman hands L4.3 the
  factorization (`hfac : B = A·Q`) it needs.
- **L1.2** (`bw_solution_eq_mul`, + `bw_dvd`/`bw_div_eq`/`bw_decodes`): in the UD regime
  `2e + k ≤ n` with `pt` injective, EVERY solution satisfies `B = A·P` for ANY close
  degree-<k `P` (the `N = B − A·P` vanishing count: deg N < k+e but N kills ≥ n−e ≥ k+e
  points), hence `A ∣ B`, `B/A = P`, and `evalOn pt (B/A)` is the UNIQUE codeword within
  `e` (via L0's `rs_unique_decoding`) — the closest codeword.
- **L1.3** (`close_of_bw_dvd`, UNCONDITIONAL — no UD, no `deg B` bound): any pair with
  `A ≠ 0`, `deg A ≤ e`, the BW identity and `A ∣ B` has
  `hammingDist w (evalOn pt (B/A)) ≤ e` — disagreements live under the ≤ e roots of `A`.

Non-vacuity: L1 FIRES on L0's concrete instance RS(4,1)/ZMod 5 at the corrupted word
`w4 = ![2,2,2,3]` — `bw_solvable_fires` (system solvable at a real corrupted word),
`bw_explicit_solution` (the hand-checked pair `(X − 3, 2·(X − 3))`), `bw_explicit_decodes`
(`B/A` evaluates to EXACTLY the constant-2 codeword `c2`), `bw_decodes_fires` (end-to-end:
membership + distance ≤ 1 + uniqueness).
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Dregg2.Circuit.CorrelatedAgreement.Scaffolding

namespace Dregg2.Circuit.CorrelatedAgreement

open Polynomial

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The Berlekamp–Welch system -/

/-- The Berlekamp–Welch system for the received word `w` at parameters `(k, e)`:
an error-locator candidate `A ≠ 0` of degree ≤ e and a candidate numerator `B` of degree
< k + e (the CLASSICAL bound `deg B ≤ k + e − 1`, stated `degree`-strict so `B = 0` needs
no case split) with the pointwise identity `A(pt i)·w i = B(pt i)` on the whole domain. -/
def bwSolution (pt : ι → F) (k e : ℕ) (w : ι → F) (A B : F[X]) : Prop :=
  A ≠ 0 ∧ A.natDegree ≤ e ∧ B.degree < ((k + e : ℕ) : WithBot ℕ) ∧
    ∀ i, A.eval (pt i) * w i = B.eval (pt i)

/-- The `natDegree`-form bound on the numerator (`deg B ≤ k + e`) is implied. -/
theorem bwSolution.natDegree_B_le {pt : ι → F} {k e : ℕ} {w : ι → F} {A B : F[X]}
    (h : bwSolution pt k e w A B) : B.natDegree ≤ k + e :=
  Polynomial.natDegree_le_iff_degree_le.mpr (le_of_lt h.2.2.1)

/-- A nonzero polynomial vanishes on at most `natDegree` points of an injective domain —
the `Polynomial.card_roots'` count, in the filter form both L1.2 and L1.3 consume. -/
theorem card_eval_zero_le {pt : ι → F} (hpt : Function.Injective pt) {A : F[X]} (hA : A ≠ 0) :
    (Finset.univ.filter fun i => A.eval (pt i) = 0).card ≤ A.natDegree := by
  have himg : (Finset.univ.filter fun i => A.eval (pt i) = 0).image pt
      ⊆ A.roots.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hA]
    exact hi
  calc (Finset.univ.filter fun i => A.eval (pt i) = 0).card
      = ((Finset.univ.filter fun i => A.eval (pt i) = 0).image pt).card :=
        (Finset.card_image_of_injective _ hpt).symm
    _ ≤ A.roots.toFinset.card := Finset.card_le_card himg
    _ ≤ Multiset.card A.roots := Multiset.toFinset_card_le _
    _ ≤ A.natDegree := Polynomial.card_roots' _

/-- Degree bookkeeping shared by L1.1 and L1.2: `deg A ≤ e` and `deg P < k` force
`deg (A·P) < k + e` (with `P = 0` and `A = 0` absorbed by `⊥`). -/
theorem degree_mul_lt_bw {A P : F[X]} {e k : ℕ} (hA : A.natDegree ≤ e)
    (hP : P.degree < (k : WithBot ℕ)) :
    (A * P).degree < ((k + e : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_mul]
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  rcases eq_or_ne A 0 with rfl | hA0
  · simp
  rw [Polynomial.degree_eq_natDegree hA0, Polynomial.degree_eq_natDegree hP0]
  have hPk : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
  exact_mod_cast by omega

/-! ## L1.1 — solvability: a close codeword yields a CERTIFIED BW solution -/

/-- **L1.1, solvability direction**: if `w` is within distance `e` of `RScode pt k`, the
Berlekamp–Welch system is solvable — witnessed by the ERROR LOCATOR
`A = ∏_{i : w i ≠ v i} (X − pt i)` and `B = A·P` — and the solution carries the full
decoding certificate: `A ∣ B` with quotient of degree < k. No injectivity of `pt` and no
unique-decoding side condition is needed for this direction. -/
theorem bw_certified_of_closeN {pt : ι → F} {k e : ℕ} {w : ι → F}
    (h : closeN (RScode pt k : Set (ι → F)) e w) :
    ∃ A B : F[X], bwSolution pt k e w A B ∧ A ∣ B ∧ (B / A).degree < (k : WithBot ℕ) := by
  obtain ⟨v, hv, hdist⟩ := h
  obtain ⟨P, hPdeg, hvP⟩ := mem_RScode.mp hv
  classical
  set E : Finset ι := Finset.univ.filter fun i => w i ≠ v i with hE
  set A : F[X] := ∏ i ∈ E, (Polynomial.X - Polynomial.C (pt i)) with hA
  have hmonic : A.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (pt i)
  have hA0 : A ≠ 0 := hmonic.ne_zero
  have hAdeg : A.natDegree ≤ e := by
    rw [hA, Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero (pt i)]
    simp only [Polynomial.natDegree_X_sub_C]
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    calc E.card = hammingDist w v := (hammingDist_eq_card_filter w v).symm
      _ ≤ e := hdist
  refine ⟨A, A * P, ⟨hA0, hAdeg, degree_mul_lt_bw hAdeg hPdeg, ?_⟩, dvd_mul_right A P,
    by rw [mul_div_cancel_left₀ _ hA0]; exact hPdeg⟩
  intro i
  rw [Polynomial.eval_mul]
  rcases eq_or_ne (w i) (v i) with hwi | hwi
  · rw [hwi, hvP i]
  · have hAi : A.eval (pt i) = 0 := by
      rw [hA, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hwi⟩) ?_
      simp
    rw [hAi, zero_mul, zero_mul]

/-- The prompt-shape corollary: closeness makes the NAIVE system (no certificate) solvable. -/
theorem bw_solvable_of_closeN {pt : ι → F} {k e : ℕ} {w : ι → F}
    (h : closeN (RScode pt k : Set (ι → F)) e w) :
    ∃ A B : F[X], bwSolution pt k e w A B :=
  let ⟨A, B, hsol, _, _⟩ := bw_certified_of_closeN h
  ⟨A, B, hsol⟩

/-! ## L1.2 — every solution factors through the close codeword -/

/-- **L1.2, core identity**: under the unique-decoding side condition `2e + k ≤ n`, EVERY
Berlekamp–Welch solution `(A, B)` satisfies `B = A·P` for ANY degree-<k polynomial `P`
whose evaluation is within distance `e` of `w`. The classical vanishing argument:
`N = B − A·P` has degree < k + e but vanishes on the ≥ n − e ≥ k + e agreement points. -/
theorem bw_solution_eq_mul {pt : ι → F} (hpt : Function.Injective pt) {k e : ℕ}
    (hn : 2 * e + k ≤ Fintype.card ι) {w : ι → F} {A B : F[X]}
    (hsol : bwSolution pt k e w A B) {P : F[X]} (hPdeg : P.degree < (k : WithBot ℕ))
    (hclose : hammingDist w (evalOn pt P) ≤ e) : B = A * P := by
  obtain ⟨hA0, hAdeg, hBdeg, hid⟩ := hsol
  by_contra hne
  have hN0 : B - A * P ≠ 0 := sub_ne_zero.mpr hne
  have hNdeg : (B - A * P).degree < ((k + e : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le B (A * P))
      (max_lt hBdeg (degree_mul_lt_bw hAdeg hPdeg))
  have hNnat : (B - A * P).natDegree < k + e :=
    (Polynomial.natDegree_lt_iff_degree_lt hN0).mpr hNdeg
  -- the agreement points are roots of N
  have hsub : (Finset.univ.filter fun i => w i = P.eval (pt i))
      ⊆ (Finset.univ.filter fun i => (B - A * P).eval (pt i) = 0) := by
    intro i hi
    have hwi : w i = P.eval (pt i) := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Polynomial.eval_sub,
      Polynomial.eval_mul]
    rw [← hid i, hwi]
    ring
  have hroots := le_trans (Finset.card_le_card hsub) (card_eval_zero_le hpt hN0)
  -- but there are at least n − e ≥ k + e agreement points
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => w i = P.eval (pt i))
  rw [Finset.card_univ] at hsplit
  have hdist : hammingDist w (evalOn pt P)
      = (Finset.univ.filter fun i => ¬ (w i = P.eval (pt i))).card :=
    hammingDist_eq_card_filter w (evalOn pt P)
  omega

/-- **L1.2, divisibility**: every BW solution has `A ∣ B` once SOME close degree-<k
codeword exists (UD regime). -/
theorem bw_dvd {pt : ι → F} (hpt : Function.Injective pt) {k e : ℕ}
    (hn : 2 * e + k ≤ Fintype.card ι) {w : ι → F} {A B : F[X]}
    (hsol : bwSolution pt k e w A B) {P : F[X]} (hPdeg : P.degree < (k : WithBot ℕ))
    (hclose : hammingDist w (evalOn pt P) ≤ e) : A ∣ B :=
  ⟨P, bw_solution_eq_mul hpt hn hsol hPdeg hclose⟩

/-- **L1.2, decoding**: the quotient `B / A` IS the close codeword's polynomial. -/
theorem bw_div_eq {pt : ι → F} (hpt : Function.Injective pt) {k e : ℕ}
    (hn : 2 * e + k ≤ Fintype.card ι) {w : ι → F} {A B : F[X]}
    (hsol : bwSolution pt k e w A B) {P : F[X]} (hPdeg : P.degree < (k : WithBot ℕ))
    (hclose : hammingDist w (evalOn pt P) ≤ e) : B / A = P := by
  rw [bw_solution_eq_mul hpt hn hsol hPdeg hclose, mul_div_cancel_left₀ _ hsol.1]

/-! ## L1.3 — a divisible solution decodes within radius e (UNCONDITIONAL) -/

/-- **L1.3**: for any pair with `A ≠ 0`, `deg A ≤ e`, the BW identity, and `A ∣ B`, the
quotient `P = B / A` satisfies `hammingDist w (evalOn pt P) ≤ e`: wherever `A(pt i) ≠ 0`
the identity forces `w i = P(pt i)`, and `A` vanishes on ≤ deg A ≤ e points of an
injective domain. NO unique-decoding side condition and NO degree bound on `B` is needed
— but note `B / A` need not lie in `RScode pt k` without the `(B / A).degree < k`
certificate (see `closeN_iff_bw_certified` below). -/
theorem close_of_bw_dvd {pt : ι → F} (hpt : Function.Injective pt) {e : ℕ} {w : ι → F}
    {A B : F[X]} (hA0 : A ≠ 0) (hAdeg : A.natDegree ≤ e)
    (hid : ∀ i, A.eval (pt i) * w i = B.eval (pt i)) (hdvd : A ∣ B) :
    hammingDist w (evalOn pt (B / A)) ≤ e := by
  have hBA : A * (B / A) = B := EuclideanDomain.mul_div_cancel' hA0 hdvd
  rw [hammingDist_eq_card_filter]
  have hsub : (Finset.univ.filter fun i => w i ≠ evalOn pt (B / A) i)
      ⊆ (Finset.univ.filter fun i => A.eval (pt i) = 0) := by
    intro i hi
    have hwi : w i ≠ (B / A).eval (pt i) := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hAi
    refine hwi (mul_left_cancel₀ hAi ?_)
    calc A.eval (pt i) * w i = B.eval (pt i) := hid i
      _ = (A * (B / A)).eval (pt i) := by rw [hBA]
      _ = A.eval (pt i) * (B / A).eval (pt i) := Polynomial.eval_mul
  exact le_trans (Finset.card_le_card hsub) (le_trans (card_eval_zero_le hpt hA0) hAdeg)

/-! ## L1.1, the honest iff — solvability WITH the decoding certificate ⟺ closeness -/

/-- **L1.1**: `w` is within distance `e` of `RScode pt k` **iff** the Berlekamp–Welch
system has a solution carrying the decoding certificate `A ∣ B ∧ deg (B/A) < k`.

⚠ The NAIVE converse — a bare `bwSolution` implies closeness — is FALSE, even under the
unique-decoding side condition `2e + k ≤ n`: pick coprime `A, B` with `A` root-free on the
domain (e.g. an irreducible quadratic) and let `w i = B(pt i)/A(pt i)`; then `(A, B)`
solves the system while every codeword agrees with `w` on < k + e points, so `w` is FAR
whenever `n` is large enough. `bw_naive_converse_false` below pins this on a concrete
instance. The certificate is exactly what restores the equivalence — and it is what the
L2 bivariate lift produces anyway (Polishchuk–Spielman hands L4.3 the factorization). -/
theorem closeN_iff_bw_certified {pt : ι → F} (hpt : Function.Injective pt) {k e : ℕ}
    {w : ι → F} :
    closeN (RScode pt k : Set (ι → F)) e w ↔
      ∃ A B : F[X], bwSolution pt k e w A B ∧ A ∣ B ∧ (B / A).degree < (k : WithBot ℕ) := by
  constructor
  · exact bw_certified_of_closeN
  · rintro ⟨A, B, hsol, hdvd, hdivdeg⟩
    exact ⟨evalOn pt (B / A), mem_RScode.mpr ⟨B / A, hdivdeg, fun i => rfl⟩,
      close_of_bw_dvd hpt hsol.1 hsol.2.1 hsol.2.2.2 hdvd⟩

/-- **L1.2 packaged**: in the UD regime, ANY solution of the system decodes the received
word — `evalOn pt (B / A)` is a codeword within distance `e` of `w`, and it is the UNIQUE
such codeword (so it realizes the closest codeword). -/
theorem bw_decodes {pt : ι → F} (hpt : Function.Injective pt) {k e : ℕ}
    (hn : 2 * e + k ≤ Fintype.card ι) {w : ι → F} {A B : F[X]}
    (hsol : bwSolution pt k e w A B)
    (hclose : closeN (RScode pt k : Set (ι → F)) e w) :
    evalOn pt (B / A) ∈ RScode pt k ∧ hammingDist w (evalOn pt (B / A)) ≤ e ∧
      ∀ g ∈ RScode pt k, hammingDist w g ≤ e → g = evalOn pt (B / A) := by
  obtain ⟨v, hv, hdist⟩ := hclose
  obtain ⟨P, hPdeg, hvP⟩ := mem_RScode.mp hv
  have hveq : v = evalOn pt P := funext fun i => hvP i
  subst hveq
  have hdiv : B / A = P := bw_div_eq hpt hn hsol hPdeg hdist
  rw [hdiv]
  exact ⟨hv, hdist, fun g hg hgdist => rs_unique_decoding hpt hn hg hv hgdist hdist⟩

/-! ## Non-vacuity — L1 FIRES on the L0 concrete instance: RS(4,1)/ZMod 5, w4 = ![2,2,2,3]

The corrupted word `w4` (distance 1 from the constant-2 codeword `c2`, per L0's `#guard`s)
at `(k, e) = (1, 1)`: `2e + k = 3 ≤ 4 = n`, the UD regime. -/
section Fire

/-- `w4` is 1-close to the code — the closeness premise is INHABITED (not vacuous). -/
theorem w4_closeN : closeN (RScode pt5 1 : Set (Fin 4 → ZMod 5)) 1 w4 :=
  ⟨c2, c2_mem, by decide⟩

/-- **L1.1 FIRES**: the BW system at the real corrupted word ![2,2,2,3] is solvable,
certificate included. -/
theorem bw_solvable_fires :
    ∃ A B : (ZMod 5)[X], bwSolution pt5 1 1 w4 A B ∧ A ∣ B ∧
      (B / A).degree < ((1 : ℕ) : WithBot ℕ) :=
  bw_certified_of_closeN w4_closeN

/-- The EXPLICIT hand-checked solution: error locator `A = X − 3` (the corruption sits at
domain point 3), numerator `B = 2·(X − 3) = A · C 2`. Verified pointwise on all 4 points. -/
theorem bw_explicit_solution :
    bwSolution pt5 1 1 w4 (Polynomial.X - Polynomial.C 3)
      (Polynomial.C 2 * (Polynomial.X - Polynomial.C 3)) := by
  refine ⟨Polynomial.X_sub_C_ne_zero 3, le_of_eq (Polynomial.natDegree_X_sub_C 3), ?_, ?_⟩
  · rw [Polynomial.degree_mul, Polynomial.degree_C (by decide : (2 : ZMod 5) ≠ 0),
      Polynomial.degree_X_sub_C, zero_add]
    exact_mod_cast by omega
  · intro i
    fin_cases i <;>
      simp [pt5, w4, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] <;>
      decide

/-- **L1.3 FIRES**: dividing the explicit numerator by the explicit error locator decodes
`w4` to EXACTLY the constant-2 codeword `c2`. -/
theorem bw_explicit_decodes :
    evalOn pt5 ((Polynomial.C 2 * (Polynomial.X - Polynomial.C 3) : (ZMod 5)[X])
      / (Polynomial.X - Polynomial.C 3)) = c2 := by
  rw [mul_comm (Polynomial.C (2 : ZMod 5)) (Polynomial.X - Polynomial.C 3),
    mul_div_cancel_left₀ _ (Polynomial.X_sub_C_ne_zero (3 : ZMod 5))]
  funext i
  simp [c2]

/-- **L1.2 FIRES end-to-end**: `bw_decodes` at the explicit solution — the decoded word is
a codeword within distance 1 of `w4` and is the UNIQUE such codeword. -/
theorem bw_decodes_fires :
    evalOn pt5 ((Polynomial.C 2 * (Polynomial.X - Polynomial.C 3) : (ZMod 5)[X])
        / (Polynomial.X - Polynomial.C 3)) ∈ RScode pt5 1 ∧
      hammingDist w4 (evalOn pt5 ((Polynomial.C 2 * (Polynomial.X - Polynomial.C 3) :
        (ZMod 5)[X]) / (Polynomial.X - Polynomial.C 3))) ≤ 1 ∧
      ∀ g ∈ RScode pt5 1, hammingDist w4 g ≤ 1 →
        g = evalOn pt5 ((Polynomial.C 2 * (Polynomial.X - Polynomial.C 3) : (ZMod 5)[X])
          / (Polynomial.X - Polynomial.C 3)) :=
  bw_decodes pt5_inj (by decide) bw_explicit_solution w4_closeN

/-- **L1.3 FIRES on its own hypotheses** (no UD condition consumed): the explicit pair,
its identity, and `A ∣ B` alone bound the decode distance at the corrupted word. -/
theorem close_of_bw_dvd_fires :
    hammingDist w4 (evalOn pt5 ((Polynomial.C 2 * (Polynomial.X - Polynomial.C 3) :
      (ZMod 5)[X]) / (Polynomial.X - Polynomial.C 3))) ≤ 1 :=
  close_of_bw_dvd pt5_inj (Polynomial.X_sub_C_ne_zero 3)
    (le_of_eq (Polynomial.natDegree_X_sub_C 3)) bw_explicit_solution.2.2.2
    (dvd_mul_left _ _)

end Fire

/-! ## ⚠ Both-truth tooth — the NAIVE converse is FALSE, even in the UD regime

Over `ZMod 7` on the 5-point domain `{0,…,4}` at `(k, e) = (1, 2)` — so `2e + k = 5 ≤ 5`,
the unique-decoding side condition HOLDS — the root-free pair `(X² + 1, X²)` solves the
naive BW system at the rational-function word `w7 i = pt i² / (pt i² + 1)`, yet `w7` is
at distance ≥ 3 from every constant codeword. Bare solvability does not witness
closeness; the `A ∣ B ∧ deg (B/A) < k` certificate in `closeN_iff_bw_certified` is
load-bearing. -/
section NaiveConverseFalse

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The 5-point domain 0,…,4 in ZMod 7. -/
def pt7 : Fin 5 → ZMod 7 := fun i => (i.val : ZMod 7)

/-- The rational-function word `w7 i = pt7 i ² / (pt7 i ² + 1)` (denominator `X² + 1` is
root-free in ZMod 7 since −1 is a non-residue): ![0, 1/2, 4/5, 2/3, 2/3] = ![0,4,5,3,3]. -/
def w7 : Fin 5 → ZMod 7 := ![0, 4, 5, 3, 3]

/-- `(X² + 1, X²)` solves the NAIVE system at `w7` — pointwise `(x² + 1)·w7 = x²`. -/
theorem bw_naive_solution :
    bwSolution pt7 1 2 w7 (Polynomial.X ^ 2 + Polynomial.C 1) (Polynomial.X ^ 2) := by
  refine ⟨(Polynomial.monic_X_pow_add_C _ (by norm_num)).ne_zero,
    le_of_eq Polynomial.natDegree_X_pow_add_C, ?_, ?_⟩
  · rw [Polynomial.degree_X_pow]
    exact_mod_cast by omega
  · intro i
    fin_cases i <;>
      simp [pt7, w7, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] <;>
      decide

/-- `w7` is NOT 2-close to the constant code: every constant disagrees on ≥ 3 points. -/
theorem w7_far : ¬ closeN (RScode pt7 1 : Set (Fin 5 → ZMod 7)) 2 w7 := by
  rintro ⟨v, hv, hdist⟩
  obtain ⟨P, hPdeg, hvP⟩ := mem_RScode.mp hv
  have hPC : P = Polynomial.C (P.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero
      (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hPdeg))
  have hveq : v = fun _ => P.coeff 0 := funext fun i => by
    rw [hvP i]
    conv_lhs => rw [hPC]
    exact Polynomial.eval_C
  rw [hveq] at hdist
  exact absurd hdist
    ((by decide : ∀ c : ZMod 7, ¬ hammingDist w7 (fun _ => c) ≤ 2) (P.coeff 0))

/-- **THE TOOTH**: naive solvability does NOT imply closeness (UD condition and all). -/
theorem bw_naive_converse_false :
    ¬ (∀ w : Fin 5 → ZMod 7, (∃ A B : (ZMod 7)[X], bwSolution pt7 1 2 w A B) →
        closeN (RScode pt7 1 : Set (Fin 5 → ZMod 7)) 2 w) := fun h =>
  w7_far (h w7 ⟨_, _, bw_naive_solution⟩)

end NaiveConverseFalse

/-! ## Axiom hygiene — every keystone pinned to the three kernel axioms -/

#assert_all_clean [bwSolution.natDegree_B_le, card_eval_zero_le, degree_mul_lt_bw,
  bw_certified_of_closeN, bw_solvable_of_closeN, bw_solution_eq_mul, bw_dvd, bw_div_eq,
  close_of_bw_dvd, closeN_iff_bw_certified, bw_decodes, w4_closeN, bw_solvable_fires,
  bw_explicit_solution, bw_explicit_decodes, close_of_bw_dvd_fires, bw_decodes_fires,
  bw_naive_solution, w7_far, bw_naive_converse_false]

end Dregg2.Circuit.CorrelatedAgreement
