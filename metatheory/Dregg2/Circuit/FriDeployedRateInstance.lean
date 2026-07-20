/-
# `Dregg2.Circuit.FriDeployedRateInstance` — the REALISTIC-DOMAIN, DEPLOYED-RATE `FriSetupK`
(the folding closure `BabyBearFriDeployed.lean:30-31` flags as unwritten), the positive-radius
payment FIRING on it — and the REFUTATION of the diagnosis that domain size was the blocker.

## The honest first sentence

`FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8` proved both premises of
`far_oracle_query_payment` are uninhabited at `friSetupK8` (`|ι| = 16`, `|κ| = 2`) for `d ≥ 1`, and
diagnosed the residual as a MODEL-RESOLUTION gap: "a non-vacuous positive-radius payment needs a
`FriSetupK` whose `|ι| > n²·d` and `|κ| > d` — the domain sharpened toward realistic size". This
file supplies exactly that instance and shows the diagnosis is **half right and half wrong**:

* **RIGHT** — §4/§5: at `|L| = 2^24`, arity `8`, `|L^8| = 2^21`, degree-`< 2^21` Reed–Solomon code
  (rate `2^-3 = 1/8`, the DEPLOYED `PROD_FRI_LOG_BLOWUP = 3`), folded degree-`< 2^18` (rate `1/8`
  PRESERVED), both premises ARE inhabited and the payment FIRES with a genuine sub-`1` bound
  (`deployed_positive_radius_payment_fires`, paid `(9/10)^38 < 1/50`). The folding closure — the
  "separate (unwritten) proof" of `BabyBearFriDeployed.lean:30-31` — is `friSetupR`, proved here in
  full generality (`unfold_closed` + `foldC_mem` over any `(n, M, D')`).

* **WRONG** — §6: enlarging the domain does NOT recover the advertised soundness. For **every**
  `FriSetupK F ι κ n` whatsoever, at **every** domain size, the two premises of
  `far_oracle_query_payment` are jointly satisfiable only when `n·δ < 1`
  (`arity_payment_delta_cap`). The reason is structural, not modelling: farness caps at `|ι|`,
  `|ι| ≤ n·|κ|` is forced by `FriFoldArity.pullback_card_le`, and the keystone's reconstruction
  constant is `n²·d`. So `n²·d < |ι| ≤ n·|κ|` gives `n·d < |κ|`, and `δ·|κ| ≤ d` then gives
  `n·δ < 1`. At the deployed arity `n = 8` this caps `δ < 1/8`, STRICTLY BELOW the rate-`1/8`
  unique-decoding radius `δ = 7/16` that `FriQuerySoundness.deployed_query_error_lt` prices at
  `< 2^-31`. The composed payment at `k = 38` queries is therefore bounded BELOW by
  `(7/8)^38 > 2^-8` (`deployed_arity8_payment_floor`) — it can never reach `2^-31`
  (`deployed_composed_payment_cannot_reach_2pow31`), at any domain size.

## The finding, stated plainly

`friSetupK8`'s vacuity was a symptom, not the disease. The disease is the `n²` LOSS in the
deterministic size-`n` Vandermonde keystone `fold_close_of_arity_challenges`: it shrinks the usable
radius by `n²` while the fold shrinks the domain by only `n`, so the usable relative radius is
divided by `n`. `δ = 7/16` is unreachable through this route at ANY parameters; the ~24-bit shortfall
(`2^-7.3` achievable vs `2^-31` advertised) is a CONSTANT-LOSS gap. Closing it needs the
PROBABILISTIC proximity-gap theorem (BCIKS20 / DEEP-FRI), where a `δ`-far word's folds stay `≈δ`-far
with high probability over `α` rather than losing `n²` deterministically — which is precisely the
conjectural content NAMED in `εQuery`'s Johnson carrier and NOT proved in this tree.

None of this asserts the deployed prover is unsound. It bounds what THIS proof chain delivers.

## What is quantified over what (the sufficient test)

Every probabilistic statement here is a COUNTING bound over the verifier's uniform query sample
`Q : Fin k → κ`, quantified over ALL words `f` (no efficiency hypothesis is needed or used — FRI
query soundness is statistical, and smuggling a hardness carrier here would be a defect). The
refutation `arity_payment_delta_cap` is quantified over ALL `FriSetupK` instances and is pure
finite arithmetic. The deployed-parameter `ε` is explicit throughout: `n = 8`, `k = 38`,
`|L| = 2^24`, rate `1/8`, `δ < 1/8`, paid `> 2^-8`.

## Coordination
Reuses `FriQuerySamplingBias.epsQueryBias` (codex, committed) for the bias-aware corollary — not
forked. Reuses `FriFoldArity.{FriGeomK, FriSetupK, Fold, Cj, comps, fiberV, reassemble,
pullback_card_le, chal8}` and `FriPositiveRadiusPayment.far_oracle_query_payment` verbatim.

## Discipline
Sorry-free; no `axiom`; no `def …Sound`/`…Hard` carrier; additive new file; all imports read-only.
`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Logic.Equiv.Fin.Basic
import Dregg2.Circuit.FriPositiveRadiusPayment
import Dregg2.Circuit.FriQuerySamplingBias

namespace Dregg2.Circuit.FriDeployedRateInstance

open Dregg2.Circuit.FriSoundness (closeN farN disagree)
open Dregg2.Circuit.FriFoldArity
  (FriGeomK FriSetupK Fold Cj comps fiberV fvec reassemble mulVec_eq fiberV_isUnit_det
   pullback_card_le chal8 chal8_inj)
open Dregg2.Circuit.FriPositiveRadiusPayment (far_oracle_query_payment)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open scoped BigOperators Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## §0 — Two-power root order: the only field input the construction needs.

Every primitivity fact below reduces to a single hypothesis of the form `ω ^ (2^a) = -1`. That
hypothesis pins `orderOf ω = 2^(a+1)` EXACTLY (§0.1), which is what makes both the evaluation map
injective (needed for the code's distance) and the fiber values pairwise distinct (needed for the
arity-`n` Vandermonde). Crucially the argument is SIZE-INDEPENDENT — it is `Nat.dvd_prime_pow`, not
a `decide` over the domain — so it survives the jump from `|L| = 16` to `|L| = 2^24`. -/

/-- **`ω ^ (2^a) = -1` pins the order at `2^(a+1)`.** `ω^(2^(a+1)) = (ω^(2^a))² = 1` gives
`orderOf ω ∣ 2^(a+1)`, so `orderOf ω = 2^b` with `b ≤ a+1`; if `b ≤ a` then `ω^(2^a)` is a power of
`ω^(2^b) = 1`, hence `1 ≠ -1`. No enumeration of the domain — this is the lemma that scales. -/
theorem orderOf_eq_of_pow_two_eq_neg_one {ω : F} {a : ℕ} (h : ω ^ (2 ^ a) = -1)
    (hne : (-1 : F) ≠ 1) : orderOf ω = 2 ^ (a + 1) := by
  have h2 : ω ^ (2 ^ (a + 1)) = 1 := by
    rw [pow_succ, pow_mul, h]; ring
  have hdvd : orderOf ω ∣ 2 ^ (a + 1) := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨b, hb, hbeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.lt_or_ge b (a + 1) with hlt | hge
  · exfalso
    have hsplit : (2 : ℕ) ^ a = 2 ^ b * 2 ^ (a - b) := by
      rw [← pow_add]; congr 1; omega
    have hone : ω ^ (2 ^ a) = 1 := by
      rw [hsplit, pow_mul, ← hbeq, pow_orderOf_eq_one, one_pow]
    rw [h] at hone
    exact hne hone
  · rw [hbeq]; congr 1; omega

/-- **Evaluation is injective on `Fin Nn` when `Nn ≤ orderOf ω`** — `pow_injOn_Iio_orderOf`. This
is the Reed–Solomon evaluation domain being genuinely `Nn` DISTINCT points. -/
theorem pow_inj_of_le_orderOf {ω : F} {Nn : ℕ} (h : Nn ≤ orderOf ω) :
    Function.Injective (fun x : Fin Nn => ω ^ (x : ℕ)) := by
  intro i i' hii
  exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr (lt_of_lt_of_le i.isLt h))
    (Set.mem_Iio.mpr (lt_of_lt_of_le i'.isLt h)) hii)

/-! ## §1 — The evaluation (Reed–Solomon) code and its MDS distance.

`rsCode p Dd = {x ↦ Σ_{s<Dd} c_s · p(x)^s}` — the degree-`< Dd` RS code on the evaluation points
`p`. §1.2 proves the ONE distance fact the positive-radius payment needs a witness for: the
degree-`Dd` monomial word `x ↦ p(x)^Dd` is at distance `≥ |ι| − Dd` from the WHOLE code, because
`X^Dd − Σ c_s X^s` is a nonzero polynomial of degree exactly `Dd` and so has `≤ Dd` roots. -/

/-- The degree-`< Dd` Reed–Solomon code on evaluation points `p`. -/
noncomputable def rsCode {ι : Type*} [Fintype ι] (p : ι → F) (Dd : ℕ) :
    Submodule F (ι → F) where
  carrier := {f | ∃ c : Fin Dd → F, f = fun x => ∑ s : Fin Dd, c s * (p x) ^ (s : ℕ)}
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨c, rfl⟩ ⟨c', rfl⟩
    refine ⟨c + c', ?_⟩
    funext x
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by simp [add_mul])
  smul_mem' := by
    rintro a f ⟨c, rfl⟩
    refine ⟨a • c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by rw [mul_assoc])

theorem mem_rsCode {ι : Type*} [Fintype ι] {p : ι → F} {Dd : ℕ} {f : ι → F} :
    f ∈ rsCode p Dd ↔ ∃ c : Fin Dd → F, f = fun x => ∑ s : Fin Dd, c s * (p x) ^ (s : ℕ) :=
  Iff.rfl

/-- The degree-`Dd` monomial word `x ↦ p(x)^Dd` — one degree ABOVE the code. -/
noncomputable def monoWord {ι : Type*} (p : ι → F) (Dd : ℕ) : ι → F := fun x => (p x) ^ Dd

/-- **THE MDS DISTANCE BOUND.** The monomial word disagrees with EVERY codeword of `rsCode p Dd` in
at least `|ι| − Dd` places. Proof: agreement at `x` makes `p x` a root of
`P = X^Dd − Σ_{s<Dd} C(c_s)·X^s`, whose degree is exactly `Dd` (the subtracted sum has degree
`< Dd`), so `P ≠ 0` and it has at most `Dd` roots; `p` injective transports that to the agreement
set. This is the witness that makes the positive-radius far premise INHABITED at a real radius. -/
theorem monoWord_disagree_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → F} (hp : Function.Injective p) (Dd : ℕ)
    {g : ι → F} (hg : g ∈ rsCode p Dd) :
    Fintype.card ι - Dd ≤ (disagree (monoWord p Dd) g).card := by
  classical
  obtain ⟨c, rfl⟩ := hg
  set Q : Polynomial F := ∑ s : Fin Dd, Polynomial.C (c s) * Polynomial.X ^ (s : ℕ) with hQ
  set P : Polynomial F := Polynomial.X ^ Dd - Q with hP
  -- The subtracted sum has degree `< Dd`.
  have hQdeg : Q.degree < (Dd : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe Dd)]
    intro s _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast s.isLt)
  have hXdeg : (Polynomial.X ^ Dd : Polynomial F).degree = (Dd : ℕ) := Polynomial.degree_X_pow Dd
  have hPdeg : P.degree = (Dd : ℕ) := by
    rw [hP, Polynomial.degree_sub_eq_left_of_degree_lt (by rw [hXdeg]; exact hQdeg), hXdeg]
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.degree_zero] at hPdeg
    exact absurd hPdeg (by simp)
  have hPnat : P.natDegree = Dd := Polynomial.natDegree_eq_of_degree_eq_some hPdeg
  -- Evaluation of `P`.
  have heval : ∀ z : F, P.eval z = z ^ Dd - ∑ s : Fin Dd, c s * z ^ (s : ℕ) := by
    intro z
    rw [hP, hQ]
    simp [Polynomial.eval_finsetSum]
  -- The agreement set.
  set A : Finset ι := Finset.univ.filter
    (fun x => monoWord p Dd x = (fun x => ∑ s : Fin Dd, c s * (p x) ^ (s : ℕ)) x) with hA
  have hAroot : ∀ x ∈ A, (P.eval (p x)) = 0 := by
    intro x hx
    rw [hA, Finset.mem_filter] at hx
    have := hx.2
    simp only [monoWord] at this
    rw [heval, this, sub_self]
  have hAsub : (A.image p).val ⊆ P.roots := by
    refine Multiset.subset_iff.mpr ?_
    intro z hz
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp (by simpa using hz)
    exact Polynomial.mem_roots'.mpr ⟨hP0, hAroot x hxA⟩
  have hAcard : A.card ≤ Dd := by
    have h := Polynomial.card_le_degree_of_subset_roots hAsub
    rwa [Finset.card_image_of_injective _ hp, hPnat] at h
  -- Disagreement is the complement of agreement.
  have hsplit : A.card + (disagree (monoWord p Dd)
      (fun x => ∑ s : Fin Dd, c s * (p x) ^ (s : ℕ))).card = Fintype.card ι := by
    rw [hA]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι))
      (p := fun x => monoWord p Dd x = (fun x => ∑ s : Fin Dd, c s * (p x) ^ (s : ℕ)) x)
    simpa [disagree, Finset.card_univ] using this
  omega

/-- **THE FAR WITNESS.** The monomial word is `r`-FAR from `rsCode p Dd` for every
`r < |ι| − Dd`. This inhabits the far premise that `friSetupK8`'s size-16 domain could not. -/
theorem monoWord_farN {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → F} (hp : Function.Injective p) (Dd r : ℕ) (hr : r < Fintype.card ι - Dd) :
    farN (rsCode p Dd) r (monoWord p Dd) := by
  rintro ⟨g, hgC, hle⟩
  have := monoWord_disagree_card hp Dd hgC
  omega

/-! ## §2 — The arity-`n` geometry on a size-`n·M` domain, general in `(n, M)`.

`L = {ω^0, …, ω^(nM−1)}` indexed by `Fin (n·M)`; the power-`n` quotient is `x ↦ x mod M` onto
`Fin M`, whose fiber over `y` is `{y, y+M, …, y+(n−1)M}`. Fiber VALUES are
`ω^y · (ω^M)^i`, pairwise distinct exactly when `ω^M` has order `≥ n` — the honest arity-`n`
primitive-root condition of `FriGeomK`. Every proof here is Nat modular arithmetic, general in
`(n, M)`: nothing enumerates the domain, so `M = 2^21` costs the same as `M = 2`. -/

variable (n M : ℕ)

/-- The evaluation point `p(x) = ω^x` on the size-`n·M` domain. -/
noncomputable def pR (ω : F) : Fin (n * M) → F := fun x => ω ^ (x : ℕ)

/-- The folded evaluation point `p'(y) = (ω^n)^y` on the size-`M` folded domain. -/
noncomputable def pkR (ω : F) : Fin M → F := fun y => (ω ^ n) ^ (y : ℕ)

/-- The power-`n` quotient `q(x) = x mod M`. -/
def qR (hM : 0 < M) : Fin (n * M) → Fin M := fun x => ⟨(x : ℕ) % M, Nat.mod_lt _ hM⟩

/-- The `n` fiber representatives `reps y i = y + M·i` (no wraparound: `y < M`, `i < n`). -/
def repsR : Fin M → Fin n → Fin (n * M) := fun y i =>
  ⟨(y : ℕ) + M * (i : ℕ), by
    have hy : (y : ℕ) < M := y.isLt
    have h1 : (i : ℕ) + 1 ≤ n := i.isLt
    calc (y : ℕ) + M * (i : ℕ) < M + M * (i : ℕ) := Nat.add_lt_add_right hy _
      _ = M * ((i : ℕ) + 1) := by ring
      _ ≤ M * n := Nat.mul_le_mul_left M h1
      _ = n * M := Nat.mul_comm M n⟩

theorem qR_repsR (hM : 0 < M) (y : Fin M) (i : Fin n) : qR n M hM (repsR n M y i) = y := by
  apply Fin.ext
  show ((y : ℕ) + M * (i : ℕ)) % M = (y : ℕ)
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]

theorem qR_fiber (hM : 0 < M) (x : Fin (n * M)) : ∃ i, x = repsR n M (qR n M hM x) i := by
  refine ⟨⟨(x : ℕ) / M, (Nat.div_lt_iff_lt_mul hM).mpr x.isLt⟩, ?_⟩
  apply Fin.ext
  show (x : ℕ) = (x : ℕ) % M + M * ((x : ℕ) / M)
  exact (Nat.mod_add_div _ _).symm

/-- **The fiber values are pairwise distinct** — `ω^(y + M·i) = ω^y · (ω^M)^i` and `ω^y ≠ 0`. -/
theorem pR_repsR_inj (ω : F) (hωne : ω ≠ 0)
    (hfib : Function.Injective (fun i : Fin n => (ω ^ M) ^ (i : ℕ))) (y : Fin M) :
    Function.Injective (fun i : Fin n => pR n M ω (repsR n M y i)) := by
  intro i i' h
  apply hfib
  have hy : ω ^ (y : ℕ) ≠ 0 := pow_ne_zero _ hωne
  have h' : ω ^ (y : ℕ) * (ω ^ M) ^ (i : ℕ) = ω ^ (y : ℕ) * (ω ^ M) ^ (i' : ℕ) := by
    have hL : pR n M ω (repsR n M y i) = ω ^ (y : ℕ) * (ω ^ M) ^ (i : ℕ) := by
      show ω ^ ((y : ℕ) + M * (i : ℕ)) = _
      rw [pow_add, pow_mul]
    have hR : pR n M ω (repsR n M y i') = ω ^ (y : ℕ) * (ω ^ M) ^ (i' : ℕ) := by
      show ω ^ ((y : ℕ) + M * (i' : ℕ)) = _
      rw [pow_add, pow_mul]
    rw [← hL, ← hR]; exact h
  exact mul_left_cancel₀ hy h'

/-- **The arity-`n` geometry at a size-`n·M` domain** — every `FriGeomK` axiom proved generally. -/
noncomputable def friGeomR (hM : 0 < M) (ω : F) (hωne : ω ≠ 0)
    (hfib : Function.Injective (fun i : Fin n => (ω ^ M) ^ (i : ℕ))) :
    FriGeomK F (Fin (n * M)) (Fin M) n where
  q := qR n M hM
  p := pR n M ω
  reps := repsR n M
  q_reps := qR_repsR n M hM
  p_reps_inj := pR_repsR_inj n M ω hωne hfib
  q_fiber := qR_fiber n M hM

/-- **The quotient is the power map on VALUES**: `p'(q x) = p(x)^n`. Needs only `ω^(nM) = 1`. -/
theorem pkR_qR (hM : 0 < M) (ω : F) (hωN : ω ^ (n * M) = 1) (x : Fin (n * M)) :
    pkR n M ω (qR n M hM x) = (pR n M ω x) ^ n := by
  show (ω ^ n) ^ ((x : ℕ) % M) = (ω ^ (x : ℕ)) ^ n
  have hexp : n * M * ((x : ℕ) / M) + n * ((x : ℕ) % M) = (x : ℕ) * n := by
    have hdm : M * ((x : ℕ) / M) + (x : ℕ) % M = (x : ℕ) := Nat.div_add_mod _ _
    calc n * M * ((x : ℕ) / M) + n * ((x : ℕ) % M)
        = n * (M * ((x : ℕ) / M) + (x : ℕ) % M) := by ring
      _ = n * (x : ℕ) := by rw [hdm]
      _ = (x : ℕ) * n := by ring
  have hz : ω ^ (n * M * ((x : ℕ) / M)) = 1 := by
    rw [pow_mul ω (n * M) ((x : ℕ) / M), hωN, one_pow]
  calc (ω ^ n) ^ ((x : ℕ) % M)
      = ω ^ (n * ((x : ℕ) % M)) := by rw [← pow_mul]
    _ = ω ^ ((x : ℕ) * n) := by
        rw [← hexp, pow_add, hz, one_mul]
    _ = (ω ^ (x : ℕ)) ^ n := by rw [pow_mul]

/-! ## §3 — THE FOLDING CLOSURE (the proof `BabyBearFriDeployed.lean:30-31` flags as unwritten).

`BabyBearFriDeployed` could match the deployed RATE only at `|L| = 16` (degree-`2` code) because a
large domain at rate `1/8` needs a degree-`2^(m−2)` code, "whose folding closure is a separate
(unwritten) proof". Here it is, in both directions and general in `(n, M, D')`:

* `unfold_closed` — reassembling `n` folded codewords of degree `< D'` lands in degree `< D'·n`;
* `foldC_mem`   — each arity-`n` component of a degree-`< D'·n` codeword has degree `< D'`.

Both are the SAME reindexing `s ↔ (t, j)`, `s = j + n·t` (`finProdFinEquiv`), plus `p'(q x) = p(x)^n`.
This is what makes the rate EXACTLY PRESERVED under folding: `(D'·n)/(n·M) = D'/M`. -/

/-- The reindexing `Fin (D'·n) ≃ Fin D' × Fin n`, `s = j + n·t`, transported to sums. -/
theorem sum_fin_mul_split {A : Type*} [AddCommMonoid A] {D' : ℕ} (H : Fin (D' * n) → ℕ → A) :
    ∑ s : Fin (D' * n), H s (s : ℕ)
      = ∑ t : Fin D', ∑ j : Fin n, H (finProdFinEquiv (t, j)) ((j : ℕ) + n * (t : ℕ)) := by
  rw [← Equiv.sum_comp finProdFinEquiv fun s => H s (s : ℕ), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  rfl

/-- The `j`-th arity-`n` component of the degree-`< D'·n` codeword with coefficients `c`. -/
noncomputable def foldComp {D' : ℕ} (ω : F) (c : Fin (D' * n) → F) (j : Fin n) : Fin M → F :=
  fun y => ∑ t : Fin D', c (finProdFinEquiv (t, j)) * (pkR n M ω y) ^ (t : ℕ)

theorem foldComp_mem {D' : ℕ} (ω : F) (c : Fin (D' * n) → F) (j : Fin n) :
    foldComp n M ω c j ∈ rsCode (pkR n M ω) D' :=
  ⟨fun t => c (finProdFinEquiv (t, j)), rfl⟩

/-- **THE DECOMPOSITION IDENTITY.** A degree-`< D'·n` codeword is `Σ_j p(x)^j · Cⱼ(q x)` with each
`Cⱼ` of degree `< D'` — the exact shape `FriGeomK`'s fiber Vandermonde inverts. -/
theorem rs_decomp (hM : 0 < M) {D' : ℕ} (ω : F) (hωN : ω ^ (n * M) = 1)
    (c : Fin (D' * n) → F) (x : Fin (n * M)) :
    (∑ s : Fin (D' * n), c s * (pR n M ω x) ^ (s : ℕ))
      = ∑ j : Fin n, (pR n M ω x) ^ (j : ℕ) * foldComp n M ω c j (qR n M hM x) := by
  rw [sum_fin_mul_split n (fun s m => c s * (pR n M ω x) ^ m), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [foldComp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pkR_qR n M hM ω hωN]
  ring

/-- **THE DEPLOYED-RATE `FriSetupK`, general in `(n, M, D')`** — arity `n`, domain `n·M`, folded
domain `M`, degree-`< D'·n` domain code, degree-`< D'` folded code. The RATE `D'/M` is preserved
exactly. Both closure obligations PROVED (not assumed). -/
noncomputable def friSetupR (D' : ℕ) (hM : 0 < M) (ω : F) (hωne : ω ≠ 0)
    (hfib : Function.Injective (fun i : Fin n => (ω ^ M) ^ (i : ℕ))) (hωN : ω ^ (n * M) = 1) :
    FriSetupK F (Fin (n * M)) (Fin M) n where
  geom := friGeomR n M hM ω hωne hfib
  C := rsCode (pR n M ω) (D' * n)
  C' := rsCode (pkR n M ω) D'
  unfold_closed := by
    intro Dv hDv
    choose e he using hDv
    refine ⟨fun s => e (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm s).1, ?_⟩
    funext x
    simp only [reassemble, friGeomR, he]
    rw [sum_fin_mul_split n
      (fun s m => e (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm s).1 * (pR n M ω x) ^ m),
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Equiv.symm_apply_apply, pkR_qR n M hM ω hωN]
    show pR n M ω x ^ (j : ℕ) * (e j t * (pR n M ω x ^ n) ^ (t : ℕ))
        = e j t * pR n M ω x ^ ((j : ℕ) + n * (t : ℕ))
    ring
  foldC_mem := by
    intro f hf j
    obtain ⟨c, rfl⟩ := hf
    refine ⟨fun t => c (finProdFinEquiv (t, j)), ?_⟩
    funext y
    have hfvec : fvec (friGeomR n M hM ω hωne hfib)
        (fun x => ∑ s : Fin (D' * n), c s * (pR n M ω x) ^ (s : ℕ)) y
        = fiberV (friGeomR n M hM ω hωne hfib) y *ᵥ
            (fun j' : Fin n => foldComp n M ω c j' y) := by
      funext i
      rw [mulVec_eq]
      show (∑ s : Fin (D' * n), c s * (pR n M ω (repsR n M y i)) ^ (s : ℕ)) = _
      rw [rs_decomp n M hM ω hωN c (repsR n M y i), qR_repsR n M hM y i]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [fiberV, Matrix.vandermonde_apply]
      rfl
    show comps (friGeomR n M hM ω hωne hfib) _ y j = _
    rw [comps, hfvec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (fiberV_isUnit_det (friGeomR n M hM ω hωne hfib) y),
      Matrix.one_mulVec]
    rfl

/-! ## §4 — THE DEPLOYED INSTANCE: `|L| = 2^24`, arity `8`, rate `1/8`.

`circuit/src/plonky3_prover.rs:96-100` — `PROD_FRI_LOG_BLOWUP = 3` (rate `2^-3`),
`PROD_FRI_MAX_LOG_ARITY = 3` (fold `8`-to-1), `PROD_FRI_NUM_QUERIES = 38`. Instantiate at
`n = 8`, `M = 2^21`, `D' = 2^18`:

| object        | size / degree      | rate  |
|---------------|--------------------|-------|
| `L`           | `n·M = 2^24`       |       |
| `C`           | deg `< D'·n = 2^21`| `1/8` |
| `L^8`         | `M = 2^21`         |       |
| `C'`          | deg `< D' = 2^18`  | `1/8` |

`2^24` is a REALISTIC production domain (`padded_trace_height × 2^log_blowup`, capped by BabyBear's
`2^27` 2-adicity). The root `ω₂₄ = ω₂₇^8` reuses `BabyBearFriDeployed.omega27_neg`'s squaring chain
— no new numeral work, and NO `decide` over the `2^24`-point domain. -/

/-- `ω₂₄ = ω₂₇^8` — a primitive `2^24`-th root of unity in BabyBear. -/
noncomputable def omega24 : BabyBear := Dregg2.Circuit.BabyBearFriDeployed.omega27 ^ 8

theorem omega24_neg : omega24 ^ (2 ^ 23) = -1 := by
  show (Dregg2.Circuit.BabyBearFriDeployed.omega27 ^ 8) ^ (2 ^ 23) = -1
  rw [← pow_mul, show 8 * 2 ^ 23 = 2 ^ 26 by norm_num]
  exact Dregg2.Circuit.BabyBearFriDeployed.omega27_neg

theorem babyBear_neg_one_ne_one : (-1 : BabyBear) ≠ 1 := by decide

/-- `orderOf ω₂₄ = 2^24` — the domain is genuinely `2^24` distinct points. -/
theorem omega24_orderOf : orderOf omega24 = 2 ^ 24 :=
  orderOf_eq_of_pow_two_eq_neg_one omega24_neg babyBear_neg_one_ne_one

theorem omega24_ne : omega24 ≠ 0 := by
  intro h
  have := omega24_neg
  rw [h, zero_pow (by norm_num)] at this
  exact absurd this.symm (by decide)

/-- `orderOf (ω₂₄^(2^21)) = 8` — the arity-`8` fiber values are `8` distinct points. -/
theorem omega24_fiber_orderOf : orderOf (omega24 ^ (2 ^ 21)) = 2 ^ 3 := by
  refine orderOf_eq_of_pow_two_eq_neg_one ?_ babyBear_neg_one_ne_one
  rw [← pow_mul, show 2 ^ 21 * 2 ^ 2 = 2 ^ 23 by norm_num]
  exact omega24_neg

/-- `orderOf (ω₂₄^8) = 2^21` — the FOLDED domain is genuinely `2^21` distinct points. -/
theorem omega24_folded_orderOf : orderOf (omega24 ^ 8) = 2 ^ 21 := by
  refine orderOf_eq_of_pow_two_eq_neg_one ?_ babyBear_neg_one_ne_one
  rw [← pow_mul, show 8 * 2 ^ 20 = 2 ^ 23 by norm_num]
  exact omega24_neg

theorem omega24_pow_domain : omega24 ^ (8 * 2 ^ 21) = 1 := by
  rw [show 8 * 2 ^ 21 = 2 ^ 23 * 2 by norm_num, pow_mul, omega24_neg]
  ring

theorem omega24_fiber_inj :
    Function.Injective (fun i : Fin 8 => (omega24 ^ (2 ^ 21)) ^ (i : ℕ)) :=
  pow_inj_of_le_orderOf (by rw [omega24_fiber_orderOf]; norm_num)

/-- **⚑ THE REALISTIC-DOMAIN, DEPLOYED-RATE FRI SETUP.** `|L| = 8·2^21 = 2^24`, arity `8`,
`|L^8| = 2^21`, domain code degree `< 2^18·8 = 2^21` (rate `1/8`), folded code degree `< 2^18`
(rate `1/8`). Folding closure PROVED by `friSetupR`. -/
noncomputable def friSetupDeployed :
    FriSetupK BabyBear (Fin (8 * 2 ^ 21)) (Fin (2 ^ 21)) 8 :=
  friSetupR 8 (2 ^ 21) (2 ^ 18) (by norm_num) omega24 omega24_ne omega24_fiber_inj
    omega24_pow_domain

/-- The DEPLOYED rate is `1/8` on the domain code: `deg/|L| = 2^21/2^24`. -/
theorem friSetupDeployed_rate :
    ((2 ^ 18 * 8 : ℕ) : ℝ) / ((8 * 2 ^ 21 : ℕ) : ℝ) = 1 / 8 := by norm_num

/-- The rate is PRESERVED by the fold: `deg'/|L^8| = 2^18/2^21 = 1/8`. -/
theorem friSetupDeployed_folded_rate :
    ((2 ^ 18 : ℕ) : ℝ) / ((2 ^ 21 : ℕ) : ℝ) = 1 / 8 := by norm_num

/-! ## §5 — THE PAYMENT FIRES: both premises inhabited, `(1−δ)^38` genuinely paid.

The far witness is the degree-`2^21` monomial word, at distance `≥ 2^24 − 2^21 = 14680064` from the
whole code (§1). Take `d = 229375`: then `n²·d = 64·229375 = 14680000 < 14680064`, so the
`(n²·d)`-far ORACLE premise is INHABITED (contrast `friSetupK8_no_positive_far_oracle`), and
`δ·|κ| = (1/10)·2^21 = 209715.2 ≤ 229375 = d`, so the payment is admissible at `δ = 1/10`. -/

/-- The evaluation map of the deployed domain is injective (`2^24` distinct points). -/
theorem pR_deployed_inj :
    Function.Injective (pR 8 (2 ^ 21) omega24) :=
  pow_inj_of_le_orderOf (by rw [omega24_orderOf]; norm_num)

/-- **THE FAR ORACLE, EXHIBITED.** The degree-`2^21` monomial word is `14680000`-FAR from the
deployed rate-`1/8` code — the premise `friSetupK8` could not inhabit. -/
theorem deployed_far_oracle :
    farN friSetupDeployed.C (8 ^ 2 * 229375)
      (monoWord (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8)) := by
  have h : farN (rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8)) (8 ^ 2 * 229375)
      (monoWord (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8)) := by
    refine monoWord_farN pR_deployed_inj _ _ ?_
    rw [Fintype.card_fin]
    norm_num
  exact h

/-- **⚑⚑ THE POSITIVE-RADIUS PAYMENT FIRES AT REALISTIC PARAMETERS.** At `|L| = 2^24`, deployed
rate `1/8`, deployed arity `8`, deployed `k = 38` queries and `δ = 1/10`, the `(n²·d)`-far oracle
premise is INHABITED (`deployed_far_oracle`) and `far_oracle_query_payment` yields a fold whose
`38`-query check passes with probability `≤ (9/10)^38 < 1/50` — a genuine `(1−δ)^k` PAID at a
positive radius, not the `Pr = 0` deterministic collapse and not the `d ≥ 1` vacuity of
`friSetupK8`. The domain half of `FriPositiveRadiusPayment`'s diagnosis is CONFIRMED. -/
theorem deployed_positive_radius_payment_fires :
    ∃ i : Fin 8, ((Finset.univ.filter (fun Q : Fin 38 → Fin (2 ^ 21) =>
          Dregg2.Circuit.FriQuerySoundness.Accepts
            (Fold friSetupDeployed.geom (chal8 i)
              (monoWord (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8)))
            (0 : Fin (2 ^ 21) → BabyBear) Q)).card : ℝ)
        / ((Fintype.card (Fin (2 ^ 21)) : ℝ) ^ 38)
      ≤ (1 - (1 / 10 : ℝ)) ^ 38 :=
  far_oracle_query_payment chal8_inj deployed_far_oracle friSetupDeployed.C'.zero_mem
    (by rw [Fintype.card_fin]; norm_num) (by norm_num)
    (by rw [Fintype.card_fin]; norm_num)

/-- The paid term is a REAL probability, well below `1`. -/
theorem deployed_payment_value : (1 - (1 / 10 : ℝ)) ^ 38 < 1 / 50 := by norm_num

/-! ## §6 — ⚑⚑⚑ THE REFUTATION: domain size was NEVER the whole blocker.

`FriPositiveRadiusPayment` diagnosed the residual as MODEL RESOLUTION — "the domain sharpened
toward realistic size". §5 confirms that unblocks NON-VACUITY. It does NOT unblock the advertised
SOUNDNESS, and no domain ever will. The obstruction is structural and holds for EVERY `FriSetupK`:

* farness caps at the domain: an inhabited `farN C (n²·d)` forces `n²·d < |ι|`;
* the fiber structure forces `|ι| ≤ n·|κ|` (`FriFoldArity.pullback_card_le` at `P = univ`);
* hence `n·d < |κ|`, and with the payment's own `δ·|κ| ≤ d`, **`n·δ < 1`**.

The keystone divides the radius by `n²` while the fold divides the domain by only `n`. The usable
RELATIVE radius is therefore divided by `n` — a constant loss no enlargement recovers. -/

/-- **⚑⚑⚑ THE ARITY CAP — a no-go over ALL `FriSetupK` instances at ALL domain sizes.** If the
`(n²·d)`-far oracle premise of `far_oracle_query_payment` is INHABITED and its rate side-condition
`δ·|κ| ≤ d` holds, then necessarily `n·δ < 1`. Nothing about the field, the code, the rate or the
domain size enters — only `pullback_card_le` and the fact that farness caps at `|ι|`. So the two
premises are JOINTLY satisfiable only strictly below relative radius `1/n`. -/
theorem arity_payment_delta_cap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {nn : ℕ} (S : FriSetupK F ι κ nn)
    (hn : 0 < nn) (hκ : 0 < Fintype.card κ) {d : ℕ} {δ : ℝ}
    (hinhab : ∃ f : ι → F, farN S.C (nn ^ 2 * d) f)
    (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    (nn : ℝ) * δ < 1 := by
  obtain ⟨f, hf⟩ := hinhab
  -- (1) An inhabited far premise forces the radius below the domain size.
  have h1 : nn ^ 2 * d < Fintype.card ι := by
    by_contra hge
    rw [not_lt] at hge
    have hcard : (disagree f (0 : ι → F)).card ≤ Fintype.card ι := by
      simpa [Finset.card_univ] using Finset.card_le_univ (disagree f (0 : ι → F))
    exact hf ⟨0, S.C.zero_mem, le_trans hcard hge⟩
  -- (2) The fiber structure forces `|ι| ≤ n·|κ|`.
  have h2 : Fintype.card ι ≤ nn * Fintype.card κ := by
    have hfilter : (Finset.univ.filter (fun x : ι => S.geom.q x ∈ (Finset.univ : Finset κ)))
        = Finset.univ := Finset.filter_true_of_mem (fun x _ => Finset.mem_univ _)
    have hp := pullback_card_le S.geom (Finset.univ : Finset κ)
    rw [hfilter, Finset.card_univ, Finset.card_univ] at hp
    exact hp
  -- (3) Cancel one factor of `n`.
  have h3 : nn * d < Fintype.card κ := by
    have hmul : nn * (nn * d) < nn * Fintype.card κ := by
      calc nn * (nn * d) = nn ^ 2 * d := by ring
        _ < Fintype.card ι := h1
        _ ≤ nn * Fintype.card κ := h2
    exact Nat.lt_of_mul_lt_mul_left hmul
  -- (4) Push through the rate side-condition.
  have hκR : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hκ
  have hnR : (0 : ℝ) < (nn : ℝ) := by exact_mod_cast hn
  have h3R : (nn : ℝ) * (d : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast h3
  nlinarith [mul_le_mul_of_nonneg_left hδd (le_of_lt hnR), h3R, hκR, hnR]

/-- **THE DEPLOYED-ARITY CAP.** At `PROD_FRI_MAX_LOG_ARITY = 3` (`n = 8`) the composed payment is
admissible only at `δ < 1/8` — strictly below the rate-`1/8` code's unique-decoding radius
`δ = 7/16` that `FriQuerySoundness` prices at `< 2^-31`. -/
theorem arity8_payment_delta_lt_eighth {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (S : FriSetupK F ι κ 8)
    (hκ : 0 < Fintype.card κ) {d : ℕ} {δ : ℝ}
    (hinhab : ∃ f : ι → F, farN S.C (8 ^ 2 * d) f)
    (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    δ < 1 / 8 := by
  have h := arity_payment_delta_cap S (by norm_num) hκ hinhab hδd
  norm_num at h
  linarith

/-- **⚑⚑ THE ADVERTISED `δ = 7/16` IS UNREACHABLE.** The deployed unique-decoding radius cannot
be attached to the arity-`8` positive-radius payment on ANY `FriSetupK` at ANY domain size: its
premises are then jointly UNINHABITABLE. This refutes, as a theorem, the reading that a bigger
domain restores `FriQuerySoundness.deployed_query_error_lt`'s `2^-31` through this route. -/
theorem deployed_delta_seven_sixteenths_unreachable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (S : FriSetupK F ι κ 8)
    (hκ : 0 < Fintype.card κ) {d : ℕ}
    (hinhab : ∃ f : ι → F, farN S.C (8 ^ 2 * d) f) :
    ¬ ((7 / 16 : ℝ) * (Fintype.card κ : ℝ) ≤ (d : ℝ)) := by
  intro hδd
  have := arity8_payment_delta_lt_eighth S hκ hinhab hδd
  norm_num at this

/-- **⚑⚑⚑ THE PAYMENT FLOOR AT DEPLOYED PARAMETERS.** Whatever `δ` the arity-`8` payment is
admissible at, the paid `(1−δ)^38` EXCEEDS `2^-8`. The composed positive-radius payment therefore
delivers strictly under `8` bits of per-round query soundness — against the `> 31` bits
`FriQuerySoundness.deployed_query_error_lt` advertises at `δ = 7/16`. A ≥ 23-bit shortfall, and it
is a property of the `n²` reconstruction constant, not of any parameter choice. -/
theorem deployed_arity8_payment_floor {δ : ℝ} (_hδ0 : 0 ≤ δ) (hcap : (8 : ℝ) * δ < 1) :
    (1 / 2 : ℝ) ^ 8 < (1 - δ) ^ 38 := by
  have hδ : δ < 1 / 8 := by linarith
  have hbase : (7 / 8 : ℝ) < 1 - δ := by linarith
  have hlt : (1 / 2 : ℝ) ^ 8 < (7 / 8 : ℝ) ^ 38 := by norm_num
  refine lt_of_lt_of_le hlt ?_
  exact pow_le_pow_left₀ (by norm_num) (le_of_lt hbase) 38

/-- **⚑⚑⚑ THE COMPOSED PAYMENT CANNOT REACH `2^-31`.** The headline: at the deployed arity `8`
and `k = 38`, the `(1−δ)^38` obtainable through `far_oracle_query_payment` is bounded BELOW by
`2^-8`, hence never below `2^-31`. `FriQuerySoundness.deployed_query_error_lt`'s `(9/16)^38 < 2^-31`
is a statement about a SINGLE oracle-vs-codeword check at `δ = 7/16`; it does NOT survive
composition with the arity-`n` keystone, because that composition caps `δ < 1/8`. -/
theorem deployed_composed_payment_cannot_reach_2pow31 {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hcap : (8 : ℝ) * δ < 1) : (1 / 2 : ℝ) ^ 31 < (1 - δ) ^ 38 :=
  lt_trans (by norm_num) (deployed_arity8_payment_floor hδ0 hcap)

/-- **The cap survives codex's SAMPLING-BIAS defect too — it can only get worse.** Composing the
arity cap with `FriQuerySamplingBias.epsQueryBias` (the deployed `sampleBits` `+ 2^logN/|F|`
defect, at `logN = 24` = this file's domain, `k = 38`, list size `1`): the bias-aware `εQuery` at
any admissible `δ` still exceeds `2^-8`. The defect addend is nonnegative, so it cannot rescue the
shortfall — it deepens it. -/
theorem deployed_biased_epsQuery_floor {δ : ℝ} (hδ0 : 0 ≤ δ) (hcap : (8 : ℝ) * δ < 1) :
    (1 / 2 : ℝ) ^ 8 <
      Dregg2.Circuit.FriQuerySamplingBias.epsQueryBias 2013265921 24 38 1 δ := by
  have hfloor := deployed_arity8_payment_floor hδ0 hcap
  have hδ : δ < 1 / 8 := by linarith
  have hb : (0 : ℝ) ≤ 1 - δ := by linarith
  have hmono : (1 - δ) ^ 38 ≤ ((1 - δ) + ((2 : ℝ) ^ 24) / (2013265921 : ℝ)) ^ 38 :=
    pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 38
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / (2013265921 : ℝ) := by norm_num
  unfold Dregg2.Circuit.FriQuerySamplingBias.epsQueryBias
  push_cast
  linarith

/-! ## §7 — Teeth: both polarities, so neither §5 nor §6 is decoration.

FIRES (§5 is real): the far premise `friSetupK8` could not inhabit IS inhabited here, and the paid
probability is `< 1/50`. BITES (§6 is real): at the ADVERTISED `δ = 7/16` the same premise set is
uninhabitable on the very instance §5 builds — the two sections are about the same object. -/

/-- **BITES, on the concrete deployed instance.** On `friSetupDeployed` itself — realistic `2^24`
domain, deployed rate `1/8` — no radius `d` admits the advertised `δ = 7/16` while keeping the
far-oracle premise inhabited. The instance that FIXES the vacuity does NOT fix the bound. -/
theorem deployed_instance_rejects_seven_sixteenths {d : ℕ}
    (hinhab : ∃ f : Fin (8 * 2 ^ 21) → BabyBear, farN friSetupDeployed.C (8 ^ 2 * d) f) :
    ¬ ((7 / 16 : ℝ) * (Fintype.card (Fin (2 ^ 21)) : ℝ) ≤ (d : ℝ)) :=
  deployed_delta_seven_sixteenths_unreachable friSetupDeployed
    (by rw [Fintype.card_fin]; norm_num) hinhab

/-- **FIRES, on the same instance.** The `d = 229375` far premise IS inhabited — so
`deployed_instance_rejects_seven_sixteenths` is not vacuous silence: there is a real radius here,
it is just necessarily below `1/8` relative. -/
theorem deployed_instance_far_premise_inhabited :
    ∃ f : Fin (8 * 2 ^ 21) → BabyBear, farN friSetupDeployed.C (8 ^ 2 * 229375) f :=
  ⟨_, deployed_far_oracle⟩

/-- The two sections meet: at `d = 229375` the ADMISSIBLE `δ` really is `< 1/8`, and the
advertised `7/16` really is refused. -/
theorem deployed_instance_delta_cap :
    ∀ δ : ℝ, δ * (Fintype.card (Fin (2 ^ 21)) : ℝ) ≤ (229375 : ℕ) → δ < 1 / 8 :=
  fun δ hδ => arity8_payment_delta_lt_eighth friSetupDeployed
    (by rw [Fintype.card_fin]; norm_num) deployed_instance_far_premise_inhabited hδ

/-! ## §8 — Axiom hygiene. -/

#assert_axioms orderOf_eq_of_pow_two_eq_neg_one
#assert_axioms pow_inj_of_le_orderOf
#assert_axioms monoWord_disagree_card
#assert_axioms monoWord_farN
#assert_axioms pkR_qR
#assert_axioms rs_decomp
#assert_axioms omega24_orderOf
#assert_axioms omega24_folded_orderOf
#assert_axioms deployed_far_oracle
#assert_axioms deployed_positive_radius_payment_fires
#assert_axioms arity_payment_delta_cap
#assert_axioms arity8_payment_delta_lt_eighth
#assert_axioms deployed_delta_seven_sixteenths_unreachable
#assert_axioms deployed_arity8_payment_floor
#assert_axioms deployed_composed_payment_cannot_reach_2pow31
#assert_axioms deployed_biased_epsQuery_floor
#assert_axioms deployed_instance_rejects_seven_sixteenths
#assert_axioms deployed_instance_far_premise_inhabited

end Dregg2.Circuit.FriDeployedRateInstance
