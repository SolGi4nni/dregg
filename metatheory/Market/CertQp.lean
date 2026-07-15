/-
# Market.CertQp — the fhEgg convex-QP soundness core: `CertQp` (KKT / complementarity-gap ⇒ ε-optimality).

**The verify-not-find keystone for the SECOND convex product on the same engine.** `fhegg-solver/src/qp.rs`
(the deployed residual checker) and `docs/deos/PRIVATE-CONVEX-ENGINE.md §2.5, §3` name the QP sibling of the
flow-LP `Cert-F`: the private convex engine is not one program but a FAMILY — *a product is a convex
program + a prox + its duality certificate*. Here the program is the convex quadratic program

    minimize   ½ xᵀP x + qᵀx     subject to   A x = b,   l ≤ x ≤ u

with `P ⪰ 0` symmetric and **public** (the covariance / Hessian structure; `A` the public equality
operator). The private data are `q, b, l, u` and the certified `x`. A **KKT certificate** — a primal-dual
tuple `(x, ν, λ⁻, λ⁺)` with `λ⁻, λ⁺ ≥ 0`, exact stationarity `Px + q + Aᵀν − λ⁻ + λ⁺ = 0`, and small
**complementarity gap** `γ = λ⁻ᵀ(x−l) + λ⁺ᵀ(u−x) ≤ ε` — CERTIFIES that `x` is ε-optimal, **independent of
how `(x, ν, λ⁻, λ⁺)` was found.** The T iterations of the OSQP/ADMM solver (`solve_admm`) are an
*untrusted search*; this stronger certificate is the intended proof-carrying output. This is the exact
QP analogue of `Market/CertF.lean`'s `certifies_epsilon_optimal`.

**Important deployed distinction.** This proposition is NOT what Rust `CertQp::check` currently
checks. Rust uses OSQP form `l ≤ Ax ≤ u` with one dual vector `y` and accepts bounded infinity residuals
for constraint violation, stationarity, and the normal-cone identity
`Ax = clamp(Ax+y,l,u)`. It does not construct the explicit lower/upper multipliers or scalar
complementarity-gap bound used here. The exact-rational source denotation, exact-zero optimality theorem,
and a positive-tolerance non-equivalence tooth live in `Market/CertQpRustDenotation.lean`. Relating the
bounded floating-point residual certificate to an inexact optimality theorem remains named; it is not
smuggled into this exact keystone.

## What is proved (honest scope)

  * **`quad_convex_ge` (the engine of it all — convex weak duality for the QP).** For P symmetric PSD and
    the objective `f x = ½ xᵀP x + qᵀx`, EVERY pair `x, x'` obeys the gradient inequality
    `∇f(x)ᵀ(x'−x) ≤ f(x') − f(x)` with `∇f(x) = Px + q`. The defect is *exactly* `½(x'−x)ᵀP(x'−x) ≥ 0`
    (PSD) — the convexity of the quadratic, the QP replacement for `Cert-F`'s linear weak duality. Uses
    nothing about how either point arose.
  * **`qp_certifies_epsilon_optimal` (THE KEYSTONE).** If `(x, ν, λ⁻, λ⁺)` is a `CertifiedQP` tuple
    (primal-feasible `x`, `λ ≥ 0`, exact stationarity, gap `γ ≤ ε`), then for EVERY primal-feasible `x'`:
    `f(x) ≤ f(x') + ε`. So no feasible point beats the certified `x` by more than `ε` — `x` is ε-optimal —
    and the proof reads ONLY the certificate. Convexity gives `f(x') − f(x) ≥ ∇f(x)ᵀ(x'−x)`; stationarity
    rewrites `∇f(x) = −Aᵀν + λ⁻ − λ⁺`; the equality `A(x'−x)=0` kills the `ν` term; `λ ≥ 0` against the
    box bounds the remaining terms below by `−γ ≥ −ε`. The certificate stands entirely on its own.
  * **`qp_gap_nonneg`** — the complementarity gap `γ` is `≥ 0` (each summand a nonneg dot of nonnegs), so a
    "certificate" claiming a negative gap is vacuous and the target `ε` it certifies is forced `≥ 0`.

**Honest scope — VERIFYING is cheap and proved; SELECTING is NOT this theorem's job.** This core proves
the CERTIFICATE is sound: a KKT check ⇒ ε-optimality. The solver (`solve_admm`) that produces the tuple is
UNTRUSTED and OUT OF SCOPE — exactly dregg's verify-not-find. **Named residual (precise):** the keystone
requires EXACT stationarity `Px + q + Aᵀν − λ⁻ + λ⁺ = 0` (mirroring `Cert-F`'s exact dual feasibility). The
deployed OSQP check instead accepts bounded nonzero primal, stationarity, and normal-cone residuals.
Deriving an optimality bound from that different certificate requires a dual/sign interpretation plus
rounding and box-diameter terms; this is the named **QP-KKT edge case** — not proved here.

**Emittability.** The stationarity rows are LINEAR in the witness (`P, A` public); the gap `γ` is
quadratic-then-linear (`λ·(x−l)` products). Demonstrated on a worked 1-D instance: the AIR system is
`satisfied` ⇔ the KKT certificate's arithmetic holds. `O(n + nnz A + nnz P)`, NOT `O(T·n)`.

Pure.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Dregg2.Circuit
import Dregg2.Tactics

namespace Market

open Matrix

/-! ## 1. The convex QP (public symmetric PSD `P`, public `A`, private data). -/

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- **The convex QP** `min ½ xᵀP x + qᵀx s.t. A x = b, l ≤ x ≤ u` — the QP product of
`PRIVATE-CONVEX-ENGINE.md §3` (private Markowitz / mean-variance). `P` is the **public symmetric PSD**
Hessian (covariance structure), `A` the **public** equality operator; `q, b, l, u` and the certified `x`
are the private data. `ε` is the public accuracy target (`gap ≤ ε` ⇒ `ε`-optimal). -/
structure QP (n m : Type*) where
  /-- The public symmetric PSD Hessian (the objective's curvature). -/
  P : Matrix n n ℚ
  /-- The linear objective term. -/
  q : n → ℚ
  /-- The public equality operator `A x = b`. -/
  A : Matrix m n ℚ
  /-- The equality right-hand side. -/
  b : m → ℚ
  /-- The box lower bound. -/
  l : n → ℚ
  /-- The box upper bound. -/
  u : n → ℚ
  /-- The public accuracy target. -/
  ε : ℚ

/-- The quadratic form `xᵀP x`. -/
def quadForm (P : Matrix n n ℚ) (x : n → ℚ) : ℚ := x ⬝ᵥ P *ᵥ x

/-- **The QP objective** `f x = ½ xᵀP x + qᵀx`. -/
def qpObj (qp : QP n m) (x : n → ℚ) : ℚ := (1/2) * quadForm qp.P x + qp.q ⬝ᵥ x

/-- **`P` is symmetric PSD** — the convexity hypothesis: `P` equals its transpose and every quadratic
value `zᵀP z` is nonnegative. This is the *public* structural fact the engine relies on (the covariance is
PSD by construction); it is what makes `f` convex and the certificate sound. -/
structure PsdSymm (P : Matrix n n ℚ) : Prop where
  /-- `P` is symmetric (`Pᵀ = P`). -/
  symm : Matrix.IsSymm P
  /-- `P` is positive semidefinite (`0 ≤ zᵀP z` for all `z`). -/
  psd : ∀ z : n → ℚ, 0 ≤ quadForm P z

/-- **Primal feasibility** — `x` satisfies the equality and lies in the box `l ≤ x ≤ u`. -/
def PrimalFeasibleQP (qp : QP n m) (x : n → ℚ) : Prop :=
  qp.A *ᵥ x = qp.b ∧ qp.l ≤ x ∧ x ≤ qp.u

/-- **A `CertQp` KKT certificate** — a primal-dual tuple whose complementarity gap is `≤ ε`:

  * `x` primal-feasible;
  * `λ⁻, λ⁺ ≥ 0` (the box multipliers, `ν` the equality multiplier — free);
  * **exact stationarity** `Px + q + Aᵀν − λ⁻ + λ⁺ = 0` (the KKT gradient of the Lagrangian; `ν ᵥ* A = Aᵀν`);
  * **complementarity gap** `γ = λ⁻ᵀ(x−l) + λ⁺ᵀ(u−x) ≤ ε`.

The entire exact proof-carrying object needed by `qp_certifies_epsilon_optimal`, independent of how the
tuple was found. This is the intended stronger certificate, not a description of the deployed Rust
residual-only checker; see `Market.CertQpRustDenotation`. -/
def CertifiedQP (qp : QP n m) (x : n → ℚ) (ν : m → ℚ) (lamL lamU : n → ℚ) : Prop :=
  PrimalFeasibleQP qp x ∧
    (0 ≤ lamL ∧ 0 ≤ lamU ∧
      qp.P *ᵥ x + qp.q + ν ᵥ* qp.A - lamL + lamU = 0) ∧
    lamL ⬝ᵥ (x - qp.l) + lamU ⬝ᵥ (qp.u - x) ≤ qp.ε

/-! ## 2. Convex weak duality — the gradient inequality of the PSD quadratic. -/

/-- **The quadratic form is symmetric in its argument split** — `y ⬝ᵥ P *ᵥ x = x ⬝ᵥ P *ᵥ y` when `P` is
symmetric. The one bilinear fact the gradient identity needs. -/
theorem quad_bilin_symm {P : Matrix n n ℚ} (h : Matrix.IsSymm P) (x y : n → ℚ) :
    y ⬝ᵥ P *ᵥ x = x ⬝ᵥ P *ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, h.eq]
  exact dotProduct_comm _ _

/-- The quadratic form of a difference expands into the four cross dot products. -/
theorem quadForm_sub_expand {P : Matrix n n ℚ} (x x' : n → ℚ) :
    quadForm P (x' - x)
      = x' ⬝ᵥ P *ᵥ x' - x' ⬝ᵥ P *ᵥ x - x ⬝ᵥ P *ᵥ x' + x ⬝ᵥ P *ᵥ x := by
  simp only [quadForm, mulVec_sub, dotProduct_sub, sub_dotProduct]
  ring

/-- The gradient functional `(Px+q)ᵀ(x'−x)` expands, using symmetry to fold both `P`-cross terms. -/
theorem qpGrad_expand {qp : QP n m} (h : Matrix.IsSymm qp.P) (x x' : n → ℚ) :
    (qp.P *ᵥ x + qp.q) ⬝ᵥ (x' - x)
      = x ⬝ᵥ qp.P *ᵥ x' - x ⬝ᵥ qp.P *ᵥ x + qp.q ⬝ᵥ x' - qp.q ⬝ᵥ x := by
  have hs : x' ⬝ᵥ qp.P *ᵥ x = x ⬝ᵥ qp.P *ᵥ x' := quad_bilin_symm h x x'
  simp only [add_dotProduct, dotProduct_sub]
  rw [dotProduct_comm (qp.P *ᵥ x) x', dotProduct_comm (qp.P *ᵥ x) x, hs]
  ring

/-- **The convexity identity — the gradient defect is exactly `½(x'−x)ᵀP(x'−x)`.** For the objective
`f x = ½ xᵀP x + qᵀx` with `P` symmetric, `f(x') − f(x) − ∇f(x)ᵀ(x'−x) = ½ (x'−x)ᵀP(x'−x)`, where
`∇f(x) = Px + q`. The quadratic self-term of a symmetric bilinear form. -/
theorem qpObj_grad_identity {qp : QP n m} (h : Matrix.IsSymm qp.P) (x x' : n → ℚ) :
    qpObj qp x' - qpObj qp x - (qp.P *ᵥ x + qp.q) ⬝ᵥ (x' - x)
      = (1/2) * quadForm qp.P (x' - x) := by
  have hs : x' ⬝ᵥ qp.P *ᵥ x = x ⬝ᵥ qp.P *ᵥ x' := quad_bilin_symm h x x'
  rw [qpGrad_expand h, quadForm_sub_expand]
  simp only [qpObj, quadForm]
  rw [hs]; ring

/-- **`quad_convex_ge` — convex weak duality for the QP.** The gradient underestimates the objective:
`∇f(x)ᵀ(x'−x) ≤ f(x') − f(x)` for EVERY `x, x'`, because the defect is `½(x'−x)ᵀP(x'−x) ≥ 0` (PSD). This
is the QP replacement for `Cert-F`'s linear `weak_duality` — it reads only that `P` is PSD, nothing about
how either point arose. -/
theorem quad_convex_ge {qp : QP n m} (hP : PsdSymm qp.P) (x x' : n → ℚ) :
    (qp.P *ᵥ x + qp.q) ⬝ᵥ (x' - x) ≤ qpObj qp x' - qpObj qp x := by
  have hid := qpObj_grad_identity hP.symm x x'
  have hpsd := hP.psd (x' - x)
  linarith [hid, hpsd]

/-! ## 3. THE KEYSTONE — a `CertQp` certificate ⇒ ε-optimality (verify-not-find). -/

/-- **`qp_gap_nonneg` — the complementarity gap is `≥ 0`.** With `λ⁻, λ⁺ ≥ 0` and `l ≤ x ≤ u`, each summand
`λ⁻ᵀ(x−l)` and `λ⁺ᵀ(u−x)` is a dot product of nonnegatives, so `γ ≥ 0`. A "certificate" asserting a
strictly negative gap is impossible, and the target `ε` it certifies is forced `≥ 0`. -/
theorem qp_gap_nonneg {qp : QP n m} {x lamL lamU : n → ℚ}
    (hxl : qp.l ≤ x) (hxu : x ≤ qp.u) (hlamL : 0 ≤ lamL) (hlamU : 0 ≤ lamU) :
    0 ≤ lamL ⬝ᵥ (x - qp.l) + lamU ⬝ᵥ (qp.u - x) := by
  have h1 : (0 : ℚ) ≤ lamL ⬝ᵥ (x - qp.l) := by
    have hle : (0 : n → ℚ) ≤ x - qp.l := by
      rw [Pi.le_def]; intro i; simp only [Pi.sub_apply, Pi.zero_apply]; linarith [hxl i]
    simpa using dotProduct_le_dotProduct_of_nonneg_left hle hlamL
  have h2 : (0 : ℚ) ≤ lamU ⬝ᵥ (qp.u - x) := by
    have hle : (0 : n → ℚ) ≤ qp.u - x := by
      rw [Pi.le_def]; intro i; simp only [Pi.sub_apply, Pi.zero_apply]; linarith [hxu i]
    simpa using dotProduct_le_dotProduct_of_nonneg_left hle hlamU
  linarith

/-- **`qp_certifies_epsilon_optimal` — the certificate CERTIFIES `x` is ε-optimal.** Given a `CertifiedQP`
tuple `(x, ν, λ⁻, λ⁺)` (gap `≤ ε`), EVERY primal-feasible `x'` obeys `f(x) ≤ f(x') + ε`: no feasible point
out-scores the certified one by more than `ε`. The proof reads ONLY the certificate:

  * convexity: `f(x') − f(x) ≥ ∇f(x)ᵀ(x'−x)` (`quad_convex_ge`);
  * stationarity rewrites `∇f(x) = Px+q = −Aᵀν + λ⁻ − λ⁺`;
  * `A(x'−x) = Ax' − Ax = b − b = 0` kills the `ν` term;
  * `λ⁻ ≥ 0, x' ≥ l` gives `λ⁻ᵀ(x'−x) ≥ λ⁻ᵀ(l−x)`; `λ⁺ ≥ 0, x' ≤ u` gives `−λ⁺ᵀ(x'−x) ≥ λ⁺ᵀ(x−u)`;
  * so `∇f(x)ᵀ(x'−x) ≥ −γ ≥ −ε`.

**Independent of how the tuple was found** — the untrusted `solve_admm` search is never re-examined; the
KKT certificate stands alone. This is the "checked output" half of the fhEgg QP engine. -/
theorem qp_certifies_epsilon_optimal {qp : QP n m} (hP : PsdSymm qp.P)
    {x : n → ℚ} {ν : m → ℚ} {lamL lamU : n → ℚ}
    (hcert : CertifiedQP qp x ν lamL lamU)
    {x' : n → ℚ} (hx' : PrimalFeasibleQP qp x') :
    qpObj qp x ≤ qpObj qp x' + qp.ε := by
  obtain ⟨⟨hAx, hxl, hxu⟩, ⟨hlamL, hlamU, hstat⟩, hgap⟩ := hcert
  obtain ⟨hAx', hx'l, hx'u⟩ := hx'
  set g := qp.P *ᵥ x + qp.q with hg
  -- Stationarity ⇒ g = λ⁻ − λ⁺ − (ν ᵥ* A).
  have hgeq : g = lamL - lamU - ν ᵥ* qp.A := by
    funext i
    have hi := congrFun hstat i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    linarith
  -- The equality term vanishes: A(x'−x) = 0.
  have hnu : (ν ᵥ* qp.A) ⬝ᵥ (x' - x) = 0 := by
    rw [← dotProduct_mulVec, mulVec_sub, hAx', hAx, sub_self, dotProduct_zero]
  -- The gradient functional, resolved on the certificate's own duals.
  have hgval : g ⬝ᵥ (x' - x) = lamL ⬝ᵥ (x' - x) - lamU ⬝ᵥ (x' - x) := by
    rw [hgeq, sub_dotProduct, sub_dotProduct, hnu, sub_zero]
  -- Box bounds (λ ≥ 0 against the box), and the sign normalisations to the gap.
  have hlx : qp.l - x ≤ x' - x := by
    rw [Pi.le_def]; intro i; simp only [Pi.sub_apply]; linarith [hx'l i]
  have hxu2 : x - qp.u ≤ x - x' := by
    rw [Pi.le_def]; intro i; simp only [Pi.sub_apply]; linarith [hx'u i]
  have hL : lamL ⬝ᵥ (qp.l - x) ≤ lamL ⬝ᵥ (x' - x) :=
    dotProduct_le_dotProduct_of_nonneg_left hlx hlamL
  have hU : lamU ⬝ᵥ (x - qp.u) ≤ lamU ⬝ᵥ (x - x') :=
    dotProduct_le_dotProduct_of_nonneg_left hxu2 hlamU
  have eL : lamL ⬝ᵥ (qp.l - x) = -(lamL ⬝ᵥ (x - qp.l)) := by
    rw [← dotProduct_neg, neg_sub]
  have eU1 : lamU ⬝ᵥ (x - qp.u) = -(lamU ⬝ᵥ (qp.u - x)) := by
    rw [← dotProduct_neg, neg_sub]
  have eU2 : lamU ⬝ᵥ (x - x') = -(lamU ⬝ᵥ (x' - x)) := by
    rw [← dotProduct_neg, neg_sub]
  have hconv := quad_convex_ge hP x x'
  rw [← hg] at hconv
  linarith [hconv, hgval, hL, hU, hgap, eL, eU1, eU2]

/-! ## 4. NON-VACUITY, positive polarity — a worked 1-D QP (`min ½x² − x` on `[0,2]`).

The unconstrained minimiser of `½x² − x` is `x = 1` (gradient `x − 1 = 0`), interior to the box `[0,2]`,
so no box multiplier is active: the certificate is `x = 1`, `ν = ⟨⟩` (no equality), `λ⁻ = λ⁺ = 0`, gap `0`.
Objective at the optimum: `½ − 1 = −½`. -/

/-- The worked QP: `n = Fin 1`, no equality (`m = Fin 0`), `P = [1]`, `q = −1`, box `[0, 2]`, `ε = 0`. -/
def qp1 : QP (Fin 1) (Fin 0) :=
  { P := fun _ _ => 1, q := fun _ => -1, A := Matrix.of fun (i : Fin 0) (_ : Fin 1) => i.elim0,
    b := fun (i : Fin 0) => i.elim0, l := fun _ => 0, u := fun _ => 2, ε := 0 }

/-- `P = [1]` is symmetric PSD: `quadForm P z = (z 0)² ≥ 0`. -/
theorem qp1_psd : PsdSymm qp1.P := by
  refine ⟨?_, ?_⟩
  · ext i j; rfl
  · intro z
    simp only [quadForm, qp1, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    have : z 0 * (1 * z 0) = (z 0)^2 := by ring
    rw [this]; positivity

/-- The optimal primal (`x = 1`), the empty equality multiplier, and the zero box multipliers. -/
def x1 : Fin 1 → ℚ := fun _ => 1
def ν1 : Fin 0 → ℚ := fun i => i.elim0
def lamL1 : Fin 1 → ℚ := fun _ => 0
def lamU1 : Fin 1 → ℚ := fun _ => 0

/-- **THE CERTIFICATE VERIFIES — the worked tuple is `CertifiedQP` with gap exactly `0`.** `x = 1` is box
feasible (`0 ≤ 1 ≤ 2`), the equality is vacuous, `λ⁻ = λ⁺ = 0 ≥ 0`, stationarity `1·1 + (−1) − 0 + 0 = 0`
holds, and the complementarity gap is `0 ≤ ε = 0`. A concrete, non-vacuous `CertQp` certificate. -/
theorem qp1_cert_valid : CertifiedQP qp1 x1 ν1 lamL1 lamU1 := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · funext i; exact i.elim0
  · intro i; fin_cases i; norm_num [qp1, x1]
  · intro i; fin_cases i; norm_num [qp1, x1]
  · intro i; fin_cases i; norm_num [lamL1]
  · intro i; fin_cases i; norm_num [lamU1]
  · funext i; fin_cases i
    simp only [qp1, x1, lamL1, lamU1, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_one, Fin.sum_univ_zero]
    norm_num
  · simp only [qp1, x1, lamL1, lamU1, dotProduct, Fin.sum_univ_one, Pi.sub_apply]
    norm_num

/-- **THE KEYSTONE, INSTANTIATED — the certificate proves `x = 1` is optimal.** Every box-feasible `x'`
has `f(1) ≤ f(x')`, i.e. `−½ ≤ ½(x'₀)² − x'₀`: no point in `[0,2]` beats the certified objective `−½`.
`qp_certifies_epsilon_optimal` on the worked certificate — the untrusted solver's `x = 1` is proven
optimal by the KKT certificate alone. -/
theorem qp1_optimal {x' : Fin 1 → ℚ} (hx' : PrimalFeasibleQP qp1 x') :
    qpObj qp1 x1 ≤ qpObj qp1 x' := by
  have h := qp_certifies_epsilon_optimal qp1_psd qp1_cert_valid hx'
  simpa [qp1] using h

/-! ## 5. NON-VACUITY, negative polarity — the teeth (an unsound tuple is REFUSED). -/

/-- An OUT-OF-BOX primal: `x = 3` violates `x ≤ u = 2`. -/
def xBad : Fin 1 → ℚ := fun _ => 3

/-- **TOOTH (feasibility): an out-of-box `x` is REFUSED.** `xBad = 3` exceeds the cap `u = 2`, so it fails
`PrimalFeasibleQP` — it cannot anchor any certificate. The box half of `CertQp` has real refusing power. -/
theorem xBad_infeasible : ¬ PrimalFeasibleQP qp1 xBad := by
  rintro ⟨-, -, hxu⟩
  have := hxu 0
  norm_num [qp1, xBad] at this

/-- **TOOTH (the certificate cannot certify a NON-OPTIMAL `x`).** Suppose the corner `x = 0` (feasible,
objective `0`) carried a `CertQp` certificate at `ε = 0`. Then `qp_certifies_epsilon_optimal` forces
`f(0) ≤ f(1) + 0 = −½` — but `f(0) = 0 > −½`. So NO dual can certify the sub-optimal corner `0` as
optimal: the certificate refuses to certify a point that is not actually ε-best. (`0` is `PrimalFeasibleQP`
— a real feasible point.) -/
theorem xZero_not_certifiable (ν : Fin 0 → ℚ) (lamL lamU : Fin 1 → ℚ) :
    ¬ CertifiedQP qp1 (fun _ => 0) ν lamL lamU := by
  intro hcert
  have hfeas1 : PrimalFeasibleQP qp1 x1 := qp1_cert_valid.1
  have h := qp_certifies_epsilon_optimal qp1_psd hcert hfeas1
  simp only [qpObj, quadForm, qp1, x1, dotProduct, Fin.sum_univ_one, Matrix.mulVec] at h
  norm_num at h

/-- The corner `x = 0`, and the honest box multipliers that saturate stationarity there
(`λ⁻ = 0`, `λ⁺ = 1`: `P·0 + q + λ⁺ = 0 + (−1) + 1 = 0`). -/
def xZero : Fin 1 → ℚ := fun _ => 0
def lamLz : Fin 1 → ℚ := fun _ => 0
def lamUz : Fin 1 → ℚ := fun _ => 1

/-- **TOOTH (gap > ε): an off-optimal primal with VALID stationarity is REFUSED by the gap clause.** The
corner `x = 0` with `(λ⁻, λ⁺) = (0, 1)` is box-feasible, `λ ≥ 0`, and stationarity holds exactly
(`0 − 1 + 1 = 0`) — yet the complementarity gap `λ⁻ᵀ(x−l) + λ⁺ᵀ(u−x) = 0 + 1·(2−0) = 2 > 0 = ε`, so the
gap clause fails. A large gap is exactly the certificate detecting "this point is `2` short of KKT-tight."
Mirrors `Cert-F`'s `zeroFlow_gap_refused`. -/
theorem xZero_gap_refused : ¬ CertifiedQP qp1 xZero ν1 lamLz lamUz := by
  rintro ⟨-, -, hgap⟩
  simp only [qp1, xZero, lamLz, lamUz, dotProduct, Fin.sum_univ_one, Pi.sub_apply] at hgap
  norm_num at hgap

/-! ## 6. EMITTABILITY — the KKT check as AIR `Constraint`s (`Dregg2.Circuit`).

For the worked 1-D instance: wire `0 = x`, wire `1 = λ⁻`, wire `2 = λ⁺`. The stationarity gate
`P·x + q − λ⁻ + λ⁺ = 0` is LINEAR (`x − 1 − λ⁻ + λ⁺ = 0`, emitted as `x + λ⁺ = 1 + λ⁻`); the gap gate
`γ = λ⁻·(x − 0) + λ⁺·(2 − x) = 0` is quadratic-then-linear (the `λ·x` products). Integer-valued witness. -/

open Dregg2.Circuit

/-- Lay a certificate's primal `x` and box multipliers `λ⁻, λ⁺` out as an AIR witness: `x` on wire 0,
`λ⁻` on wire 1, `λ⁺` on wire 2. -/
def encodeCertQp (x lamL lamU : ℤ) : Assignment
  | 0 => x | 1 => lamL | 2 => lamU
  | _ => 0

/-- **The stationarity gate** `P·x + q − λ⁻ + λ⁺ = 0` for the 1-D instance (`1·x − 1 − λ⁻ + λ⁺ = 0`),
emitted with both sides nonnegative as `x + λ⁺ = 1 + λ⁻`. One linear gate — `O(n + nnz P + nnz A)`. -/
def statGate : Constraint :=
  { lhs := .add (.var 0) (.var 2), rhs := .add (.const 1) (.var 1) }

/-- **The complementarity gap as a functional** `γ = λ⁻·x + λ⁺·(2 − x)` (the `l = 0`, `u = 2` box), one
`Expr` over the witness — quadratic-then-linear (`λ·x` products), the "gap is a cheap check" claim emitted. -/
def gapExprQp : Expr :=
  .add (.mul (.var 1) (.var 0))
       (.mul (.var 2) (.add (.const 2) (.mul (.const (-1)) (.var 0))))

/-- **The emitted TIGHT KKT certificate check** — the stationarity gate plus the exact-optimum gate
`γ = 0` (`ε = 0`). The general `γ ≤ ε` rides the standard AIR range/comparison gadget; the tight optimal
case is this exact arithmetic gate. -/
def certCircuitQp : ConstraintSystem :=
  [ statGate, { lhs := gapExprQp, rhs := .const 0 } ]

/-- **THE EMIT BRIDGE — the AIR system is `satisfied` ⇔ the KKT certificate's arithmetic holds.**
`satisfied certCircuitQp (encodeCertQp x λ⁻ λ⁺)` iff stationarity `x + λ⁺ = 1 + λ⁻` AND the gap
`λ⁻·x + λ⁺·(2 − x) = 0`. Checking the circuit IS checking the certificate, on the worked instance. -/
theorem certCircuitQp_sound (x lamL lamU : ℤ) :
    satisfied certCircuitQp (encodeCertQp x lamL lamU)
      ↔ (x + lamU = 1 + lamL) ∧ (lamL * x + lamU * (2 + (-1) * x) = 0) := by
  simp only [satisfied, certCircuitQp, statGate, gapExprQp, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, Constraint.holds, Expr.eval, encodeCertQp]
  tauto

/-- **THE VALID CERTIFICATE IS ACCEPTED by the emitted circuit** — the worked optimal certificate
(`x = 1`, `λ⁻ = λ⁺ = 0`) satisfies `certCircuitQp` (stationarity `1 + 0 = 1 + 0`, gap `0`). -/
theorem certCircuitQp_accepts : satisfied certCircuitQp (encodeCertQp 1 0 0) := by
  rw [certCircuitQp_sound]; norm_num

/-- **A gap-violating certificate is REJECTED by the emitted circuit** — the corner `x = 0` with
`(λ⁻, λ⁺) = (0, 1)` satisfies stationarity (`0 + 1 = 1 + 0`) but has emitted gap `0·0 + 1·(2 − 0) = 2 ≠ 0`,
so it fails `certCircuitQp`. The circuit's gap gate has the same refusing power as `xZero_gap_refused`. -/
theorem certCircuitQp_rejects : ¬ satisfied certCircuitQp (encodeCertQp 0 0 1) := by
  rw [certCircuitQp_sound]; rintro ⟨-, hg⟩; norm_num at hg

/-! ### `#guard` smoke — the KKT arithmetic is COMPUTED, not asserted. -/

-- the worked certificate's gap is exactly 0 (tight optimum):
#guard gapExprQp.eval (encodeCertQp 1 0 0) == 0
-- the sub-optimal corner (x = 0) against the honest dual has gap 2 (= how far from KKT-tight):
#guard gapExprQp.eval (encodeCertQp 0 0 1) == 2
-- the emitted KKT check has one stationarity gate + one gap gate:
#guard certCircuitQp.length == 2

/-! ### Axiom hygiene — the `CertQp` keystones pinned kernel-clean. -/

#assert_all_clean [Market.quad_bilin_symm, Market.quadForm_sub_expand, Market.qpGrad_expand,
  Market.qpObj_grad_identity, Market.quad_convex_ge, Market.qp_gap_nonneg,
  Market.qp_certifies_epsilon_optimal, Market.qp1_psd, Market.qp1_cert_valid, Market.qp1_optimal,
  Market.xBad_infeasible, Market.xZero_not_certifiable, Market.xZero_gap_refused,
  Market.certCircuitQp_sound, Market.certCircuitQp_accepts, Market.certCircuitQp_rejects]

end Market
