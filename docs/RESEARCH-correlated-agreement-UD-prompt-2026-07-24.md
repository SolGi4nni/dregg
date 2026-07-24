# UD-regime correlated agreement — RESOLVED to a "formalize THIS proof" task

**Date:** 2026-07-24 (rewritten from the "reconstruct BCIKS20 Thm 4.1" prompt).
**Status:** the research is **closed**. The complete, explicit-constant proof is on disk. What
remains is a **Lean/Mathlib formalization**, not a reconstruction. The single load-bearing
non-Mathlib import is identified (the Polishchuk–Spielman bivariate divisibility lemma).

## What changed

The earlier version of this doc said "we have never had access to the paper body" and framed the
job as corralling a strong model to *reconstruct* BCIKS20 Theorem 4.1. That premise is now false.
We have, on disk in `pdfs/`, **two independent, complete, self-contained proofs** of exactly the
UD-regime correlated-agreement theorem we need — one of them (Kopparty 2025) by a BCIKS20 co-author,
with an *improved* and cleaner argument and fully explicit constants. The mathematics is done. The
job is mechanization.

---

## 1. The literature verdict (which paper proves our theorem)

Papers fetched / read (paths absolute under `/Users/ember/dev/breadstuffs/pdfs/`):

- **`kopparty-improved-rs-proximity-2025.pdf`** — Ben-Sasson, Carmon, **Haböck**, **Kopparty**, Saraf,
  *"On Proximity Gaps for Reed–Solomon Codes"*, 11 Nov 2025. **THE primary source.** §2 is a
  from-scratch, improved reproof of the UD-regime correlated agreement with **explicit constants**.
  (Haböck is a co-author, so this *is* the current, improved successor of the "Haböck 2022/1216
  cleanest exposition" — that older summary is subsumed.)
- **`bciks20-proximity-gaps-2020-654.pdf`** — Ben-Sasson–Carmon–Ishai–Kopparty–Saraf, *"Proximity
  Gaps for Reed–Solomon Codes"*, eprint 2020/654 (ECCC TR20-083, rev.1, 48pp). **The canonical
  source.** §4 (pp.14–17) is the original UD-regime proof (Theorem 4.1), Lemma 4.3 is the
  Polishchuk–Spielman lemma, Appendix D (p.46–47) reduces Lemma 4.3 to `[Spi95, Lemma 4.2.18]`.
- **`improved-line-point-ldt-2311-12752.pdf`** — Harsha–Kumar–Saptharishi–Sudan, *"An Improved
  Line-Point Low-Degree Test"*, 2023. **Tangential to the RS theorem** (it is a multivariate
  low-degree *test*, not RS correlated agreement) — BUT its §2–§3 is a modern, elementary,
  self-contained proof of a *close cousin* of the Polishchuk–Spielman lemma ("low-degree roots on
  restrictions ⟹ a global low-degree root"), built precisely from the Mathlib primitives listed in
  §6. It is the best available template for formalizing the one hard lemma.

**The 2026 folded-RS shortcut does NOT exist.** arXiv 2601.10047 (Jeronimo–Liu–Rajpal, *"Optimal
Proximity Gap for Folded Reed–Solomon Codes via Subspace Designs"*) was **withdrawn 2026-06-10**
("subsumed by the prior work of Goyal and Guruswami"), and in any case targeted the **capacity /
list-decoding regime** (radius up to δ−ε), not the unique-decoding regime we need. It is not a route.
Goyal–Guruswami [GG25] (random-RS proximity gaps to δ−η) is likewise a *list-decoding-regime* result,
harder and unnecessary for us.

**STIR / WHIR / BaseFold are tangential to the correlated-agreement CORE.** They consume correlated
agreement (often the *constrained/weighted* strengthenings, Kopparty §4.2–§4.3) as a black box to do
query-reduction and build PCS; they do not give a simpler proof of the core. Not relevant to this
keystone.

---

## 2. The theorems we can now cite (explicit constants)

Notation reconciliation (this is where the earlier doc's "δ = 7/16" collides with the papers' "δ"):
the papers write **δ_code = 1 − ρ** for the code's *minimum distance* and **γ** for the *proximity /
decoding radius*. Our deployed "δ = 7/16" is their **γ**. So:

| our name | value | papers' name |
|---|---|---|
| rate ρ = k/n | 1/8 | ρ |
| code min-distance (relative) | 7/8 | δ_code = 1 − ρ |
| decoding radius (relative) | 7/16 = δ_code/2 | γ |
| UD radius (absolute) e* | 7340032 = (n−k)/2 | γ·n at γ = δ_code/2 |

n = 2²⁴ = 16777216, k(dim) = 2²¹ = 2097152, q = 2013265921⁴ ≈ 2^123.6, MDS min-distance
d = n−k+1 = 14680065, e* = ⌊(d−1)/2⌋ = (n−k)/2 = 7340032.

### THEOREM 1 — line version (the core ask)

> **Kopparty 2025, Theorem 1.3** (`kopparty-…-2025.pdf` p.8, p.17). Let C = RS[F_q, D, k],
> n = |D|, min-distance δ_code = 1 − k/n. Let **γ ∈ [δ_code/3, δ_code/2 − 1/n]**. For u₀,u₁ : D → F_q,
> if S = {z ∈ F_q : Δ(u₀+z·u₁, C) ≤ γ} has size
> **a ≥ (δ_code/γ − 1)·1/(δ_code − 2γ)**, then **Δ([u₀,u₁], C²) ≤ (1 + 1/(a−1))·γ**.
> For distance loss ε\* it suffices to take a ≥ max( (δ_code/γ−1)/(δ_code−2γ), 1 + γ/ε\* ).

> **Kopparty 2025, Corollary 1.4** (LOSSLESS, ε\*=0; p.8). For δ_code ≥ 3√2/√n and
> **γ ∈ [δ_code/3, δ_code/2 − 3/(δ_code·n)]**: if **a > γ·n + 1** then **Δ([u₀,u₁], C²) ≤ γ**.
> This matches the tight AHIV17/RZ18 bound and is optimal on its range.

`Δ([u₀,u₁], C²) ≤ γ` is *exactly* our ask: ∃ ĝu, ĝv ∈ C and a common set S, |S| ≥ (1−γ)n, with
u₀|_S = ĝu|_S **and** u₁|_S = ĝv|_S (simultaneous). BCIKS20 Theorem 4.1 (p.14) is the same statement
with a = n and ε\*=0; Kopparty's improvement is only in the *size of a* (O(1) vs n), which **we do
not need** (see §5).

### THEOREM 2 — power-curve / m-term version

> **Kopparty 2025, Theorem 4.1** (curves, up to δ/2; p.26). C = RS[F_q,D,k], dim k+1,
> δ_code ≥ 3√2/√n. For **γ ∈ [δ_code/3, δ_code/2 − 3/(δ_code·n)]** and u₀,…,u_M : D → F_q:
> if | { z : Δ(u₀ + z·u₁ + … + z^M·u_M, C) ≤ γ } | > **M·(γ·n + 1)**, then
> **Δ([u₀,…,u_M], C^{M+1}) ≤ γ** (simultaneous agreement of all M+1 words on one common set of
> density ≥ 1−γ). This is BCIKS20 Theorem 1.5's curve case with the improved a-bound.

For a batch of **m = M+1** words the threshold is **a > (m−1)·(γn+1)**. Fold arity m=8 ⟹ M=7;
batch width m ≈ 256 ⟹ M=255.

---

## 3. The proof ENGINE (what to formalize)

Both papers use the **same three-part engine**; BCIKS20 §4 is the cleanest to mechanize (standard
Berlekamp–Welch, no oversized error-locator). The word is lifted to the rational function field
𝕂 = F_q(Z): `w(x) = u₀(x) + Z·u₁(x)` (curves: `w(x) = Σ_j Z^j u_j(x)`).

**Part A — bivariate Berlekamp–Welch interpolation over 𝕂** (BCIKS20 §4.3.1–4.3.2, p.15).
Find A(X,Z), B(X,Z) ∈ F_q[X,Z], A ≠ 0, deg_X A ≤ e, deg_X B ≤ k+e, deg_Z A ≤ e, deg_Z B ≤ e+1, with
`A(x,Z)·w(x) = B(x,Z)` for **all** x ∈ D. Existence: set up the n×(k+2e+2) matrix M(Z) over F_q[Z]
(entries deg ≤ 1); a (k+2e+2)-minor determinant R(Z) has deg ≤ e+1 and vanishes at every z ∈ S
(because the per-z univariate BW system is solvable there, `Lemma 4.2`), so if |S| > e+1 then R ≡ 0,
so rank < k+2e+2 over 𝕂, so a nonzero solution over 𝕂 exists; clear denominators.
Consequence: **A(x,Z) | B(x,Z)** in F_q[Z] for all n values of x, and **A(X,z) | B(X,z)** in F_q[X]
for all |S| values of z.
(Kopparty's variant §2.1 replaces the determinant by pure dimension counting with an *oversized*
error-locator deg_X A = n−e−1; cleaner a-bound, more bookkeeping. Not needed for us.)

**Part B — Polishchuk–Spielman bivariate divisibility** (BCIKS20 Lemma 4.3, p.14; the CRUX).
From "A | B on n vertical lines and |S| horizontal lines" + the degree budget
`deg_X B/n + deg_Z B/|S| < 1`, conclude **A(X,Z) | B(X,Z) globally in F_q[X,Z]**. Set P = B/A.

**Part C — degree control + collinearity** (BCIKS20 §4.3.3–4.3.5, p.16).
P has deg_X ≤ k and deg_Z ≤ 1 (substitute z ∈ S, use k+1-point interpolation uniqueness), so
P(X,Z) = v₀(X) + Z·v₁(X) with v₀,v₁ ∈ C, and P(x,Z) = w(x,Z) on ≥ n−e points ⟹ Δ(w, v₀+Zv₁) ≤ γ.
The final "many good z ⟹ small interleaved distance" step is Kopparty's **Lemma 2.4** (p.20):
if p₀,p₁ ∈ C and Δ(u₀+zu₁, p₀+zp₁) ≤ γ for a ≥ 2 values of z, then Δ([u₀,u₁],[p₀,p₁]) ≤
(a/(a−1))·⌊γn⌋ — elementary double counting over the disagreement set. Curves: same, with loss
M/(a−M) instead of 1/(a−1).

**Note on the "known-failing routes":** the UD proof uses **Berlekamp–Welch (multiplicity 1)**, NOT
Guruswami–Sudan. The GS interpolation blockage recorded in the old prompt (empty degree window at
support 2, fold multiplicities) is a *Johnson-regime* obstacle (BCIKS20 §5 / Kopparty §3) and is
**irrelevant to the UD proof** — we never form the GS system. Two-point reconstruction's halved floor
n−2γn is superseded: the bivariate BW-over-𝕂 + PS argument reaches the un-halved floor n−γn directly.

---

## 4. The Props to mint, CORRECTED

Two honest corrections to the earlier Props:

**(i) Boundary shave (Θ(1/n)).** At γ = δ_code/2 *exactly* (radius e* = 7340032) the bound blows up
(δ_code − 2γ = 0; a → ∞). This is **intrinsic**, not a proof artifact — every known proof, BCIKS20
included, excludes exactly-δ/2. The theorem holds for any decoding radius **r ≤ ⌊(δ_code/2 −
3/(δ_code·n))·n⌋ = 7340028** (lossless) or r ≤ e*−1 = 7340031 (with negligible loss). Shaving 4
positions out of 16.7M costs **2.4×10⁻⁷ relative** decoding radius — cryptographically free, and it
actually *increases* the agreement floor to n − 7340028 = 9437188. The deployed FRI decoder should
use r = 7340028 (or generally e* − O(1)), and the hypothesis `closeN` must be stated at that r
(closeness at the larger e* does not imply closeness at r).

**(ii) Curve threshold carries the (m−1) factor.** The old Prop's `2^24 < Good.card` is correct only
for the line version. The m-term version needs **`(m−1)·(r+1) < Good.card`** (which exceeds n once
m ≥ 3). For m = 256 that is Good.card > 1.87×10⁹; soundness error = (m−1)(r+1)/q ≈ 2^-92.8 (~93 bits).

```lean
-- V = RS of degree < 2^21 on the 2^24-point domain {ω₂₄^x} (rate ρ = 1/8);
-- decoding radius r = 7340028  (= UD radius e* − 4, the Θ(1/n) shave; δ_code = 7/8).
def CorrelatedAgreementPairUD : Prop :=
  ∀ (u v : Fin (2^24) → F) (Good : Finset F),
    (∀ α ∈ Good, closeN V 7340028 (fun x => u x + α * v x)) →
    7340029 < Good.card →                       -- r + 1 < |Good|  (2^24 is amply sufficient)
    ∃ gu ∈ V, ∃ gv ∈ V,
      2^24 - 7340028 ≤ (Finset.univ.filter (fun x => u x = gu x ∧ v x = gv x)).card

-- m-term power curve: w_α = Σ_{j<m} α^j u_j ; M = m−1.
def CorrelatedAgreementCurveUD (m : ℕ) : Prop :=
  ∀ (u : Fin m → Fin (2^24) → F) (Good : Finset F),
    (∀ α ∈ Good, closeN V 7340028 (fun x => ∑ j, α ^ (j:ℕ) * u j x)) →
    (m - 1) * 7340029 < Good.card →             -- (m−1)·(r+1) < |Good|
    ∃ g : Fin m → (Fin (2^24) → F), (∀ j, g j ∈ V) ∧
      2^24 - 7340028 ≤ (Finset.univ.filter (fun x => ∀ j, u j x = g j x)).card
```

---

## 5. Formalizability VERDICT

**Direct Lean/Mathlib formalization is feasible in bounded (but nontrivial) effort. This is a
"formalize THIS proof" task, not a strong-model reconstruction.** Reasons:

- The complete explicit-constant proof exists on disk with no "standard argument" gaps **except one
  cited lemma** (Part B).
- The UD proof **avoids every piece of machinery Mathlib lacks**: no Guruswami–Sudan multiplicities,
  no Hensel lifting over *algebraic function fields*, no irreducible/separable factorization over
  F_q(Z)[Y] — all of which the *Johnson-regime* proof (BCIKS20 §5, Kopparty §3, Appendices B/C) needs
  and which would make it a genuine research-formalization. **We only need UD, so we skip all of it.**
- Field size q ≈ 2^123.6 means we do **not** need Kopparty's O(1) list-size improvement. The simpler
  original **BCIKS20 §4 (a = n, ε\*=0)** is the right formalization target.

**Mathlib inventory (verified present in the tree's mathlib):**
- `Polynomial.card_roots'` — the RS/MDS min-distance engine (a nonzero deg-<k poly has < k roots).
- `Lagrange.interpolate` — k+1-point uniqueness (Part A/C, Part C Step 5).
- `MvPolynomial` + `Degrees` / `Division` — bivariate polynomials and degree bookkeeping.
- `RingTheory/Polynomial/Resultant/Basic` — full resultant API incl. `resultant_eq_zero_iff`
  (res = 0 ↔ non-coprime), `resultant_ne_zero` (coprime ⟹ res ≠ 0), `resultant_mul_left`,
  `resultant_prod_left` — the core tool for Part B.
- `Polynomial.hasseDeriv`, `Algebra.Squarefree`, `MvPolynomial.schwartz_zippel_totalDegree`,
  `RingTheory/Henselian` — exactly the ingredients the line-point-LDT template (§2–3) uses for a
  self-contained PS-style lemma.
- `Matrix.det`, `Matrix.rank`, finite-dim rank-nullity — Part A existence.
- `InformationTheory/Hamming` — Hamming distance on `∀ i, β i` (reuse for Δ on D → F).

**The one genuine gap = Part B, the Polishchuk–Spielman lemma.** It is:
- **NOT in Mathlib.**
- **NOT self-contained in either on-disk RS paper** — BCIKS20 App. D and Kopparty §2.2 both *cite*
  `[Spi95, Lemma 4.2.18]` / `[PS94]`.
- Known to have a **subtle gap in the original** (fixed by Cramer & Nardi, per Kopparty §2.2) — so we
  must formalize a *correct* statement, not transcribe Spielman.
- **Buildable** on the Mathlib primitives above; the line-point-LDT paper (`…ldt-2311-12752.pdf`
  §2.1, §3, Lemma 3.1, pp.14–17) is a modern, elementary, self-contained proof of a close cousin
  (root-lifting form Y−P(X) | A) using resultant + Hasse derivative + squarefree + Newton iteration
  (`Lemma 2.10`, the one sub-ingredient needing Mathlib work on top of `Henselian`) + Schwartz–Zippel.

**Effort estimate:** the scaffolding (RS/Hamming/interleaved-code, Berlekamp–Welch facts, Part A
existence, collinearity counting) is routine Mathlib engineering. **Part B (the PS lemma) is a
bounded research-grade sub-project** and is the honest majority of the work — but it is *engineering
with all primitives present*, not open mathematics.

---

## 6. The Lean lemma DAG (the plan)

```
L0  Scaffolding
  L0.1  RScode  : Submodule F (D → F)         -- {evalOn D p | deg p < k}
  L0.2  hammingDist (f g : D → F) : ℕ ; closeN V r f := ∃ v∈V, hammingDist f v ≤ r
  L0.3  interleaved C² and Δ([u,v],C²)         -- ∃ common S, |S|≥(1-γ)n, u=v₀,v=v₁ on S
  L0.4  RS min distance / unique decoding      -- from card_roots': deg-<k ⟹ <k roots
                                                  ⟹ ball radius <d/2 has ≤1 codeword

L1  Berlekamp–Welch facts  (BCIKS20 Lemma 4.2)          [needs L0.4, Lagrange, card_roots']
  L1.1  BW system solvable ⟺ Δ(w,V) ≤ e (nonzero A,B)
  L1.2  nonzero solution ⟹ A | B and B/A realizes closest codeword
  L1.3  A | B ⟹ P=B/A has Δ(w,P) ≤ e

L2  Part A — bivariate interpolation over 𝕂=F_q(Z)      [needs L1, Matrix.det/rank]
  L2.1  minor determinant R(Z), deg ≤ e+1, vanishes on S (via L1.1)
  L2.2  |S| > e+1 ⟹ R ≡ 0 ⟹ ∃ nonzero A,B ∈ F_q[X,Z] with A(x,Z)w(x)=B(x,Z) ∀x∈D
  L2.3  ⟹ A(x,Z)|B(x,Z) (n x's)  and  A(X,z)|B(X,z) (|S| z's, via L1.2)

L3  Part B — POLISHCHUK–SPIELMAN  (BCIKS20 Lemma 4.3 / Spi95 4.2.18)   ★ THE CRUX ★
  L3.1  leading-coeff argument ⟹ deg_X A ≤ deg_X B, deg_Z A ≤ deg_Z B  (App. D)
  L3.2  core: A|B on n_X vert + n_Z horiz lines, deg_X B/n_X + deg_Z B/n_Z < 1
        ⟹ A | B in F_q[X,Z]                        [resultant + hasseDeriv + squarefree
                                                     + Newton/Henselian + schwartz_zippel;
                                                     template = ldt paper §2–3]
  ⟹  P := B/A ∈ F_q[X,Z]

L4  Part C — degree control + collinearity              [needs L3, Lagrange]
  L4.1  deg_X P ≤ k              (substitute z∈S, high X-coeffs vanish at >e+1 pts)
  L4.2  P(x,Z)=w(x,Z) on ≥ n−e points x
  L4.3  deg_Z P ≤ 1, P = v₀+Z·v₁, v₀,v₁∈C   (k+1-point interpolation uniqueness)
  L4.4  Lemma 2.4 collinearity double-count ⟹ Δ([u₀,u₁],[v₀,v₁]) ≤ γ

L5  THEOREM 1 (line)   = assemble L2–L4 at r=7340028   ⟹ CorrelatedAgreementPairUD
L6  THEOREM 2 (curve)  = L2–L4 with Z-degree M, Lemma 2.4 curve variant
                         ⟹ CorrelatedAgreementCurveUD m  (threshold (m−1)(r+1))
```

Critical-path risk is **L3** alone. L0–L2, L4–L6 are standard. A sensible split: land L0–L2 + L4–L6
against an `axiom` stub of L3.2, in parallel with a dedicated L3.2 sub-project templated on the
line-point-LDT paper.

---

## 7. Honest fragility

- **The PS lemma (L3.2) is the whole ballgame.** If it resists formalization, everything above is a
  conditional proof modulo one cited lemma. It is elementary (no AG/function fields) and every
  primitive is in Mathlib, but it is a real theorem with a known-subtle correct proof. Do not
  under-scope it.
- **Exact-δ/2 is unreachable and that's fine.** We take r = e*−4. If some downstream consumer truly
  needs radius e* exactly, that is a *different* (and likely false-at-these-constants) statement — flag
  it, don't paper over it. Weakening r further (e.g. e*−o(n)) only makes the proof easier and is free.
- **Full FRI soundness needs more than the plain theorem.** The plain Theorems 1/2 give the keystone,
  but the round-by-round FRI extractor (repo `DecodedLdtLink`) may consume the **constrained /
  weighted / list ("mutual")** correlated-agreement strengthenings — Kopparty §4.2–§4.3
  (Theorems 4.3, 4.5, 4.6), which the paper obtains by "minor strengthenings of Lemma 2.4" (our L4.4).
  These are *incremental* over this plan (strengthen L4.4), not a new engine — but they are additional
  Lean work and should be scoped when L5/L6 land.
- **Substrate reminder:** this is Lean-authored proof over `Polynomial`/`MvPolynomial`/`Finset`. There
  is no Rust AIR here and there must not be. The output is a machine-checked theorem about the actual
  RS code object, not a Rust `air_accepts` predicate.

---

## Appendix — fallback prompt (if handing L3.2 or the whole proof to a strong model)

> **Formalize (Lean 4 / Mathlib) the following, no reconstruction needed — the proof is given.**
> Target: `CorrelatedAgreementPairUD` and `CorrelatedAgreementCurveUD` above. Follow the DAG in §6.
> The mathematics is BCIKS20 (eprint 2020/654) §4 for the line case and Kopparty et al. 2025
> ("On Proximity Gaps for RS Codes", 11 Nov 2025) Theorem 4.1 for curves; use the improved explicit
> constants from Kopparty Cor 1.4 / Thm 4.1. Engine = bivariate Berlekamp–Welch over F_q(Z) (Part A)
> → Polishchuk–Spielman bivariate divisibility (Part B, BCIKS20 Lemma 4.3) → collinearity double count
> (Part C, Kopparty Lemma 2.4). The **only** non-Mathlib lemma is Part B; formalize it from the
> line-point-LDT template (Harsha–Kumar–Saptharishi–Sudan 2023, §2–3) using Mathlib `resultant`,
> `hasseDeriv`, `Squarefree`, `Henselian`, `schwartz_zippel`. Take decoding radius r = 7340028
> (= e*−4, the intrinsic Θ(1/n) shave below δ_code/2). Forbid vacuous/tautological statements; each
> lemma must be the real statement over `Polynomial F` / `MvPolynomial (Fin 2) F` / `Finset`.
