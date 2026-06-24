# INTENT-REFS — Tensor Categories, Hyperdoctrines & the Structural-Factoring Layer

**Pillar:** how the dregg adjoints *factor across structures* — module categories (EGNO/Ostrik), the Lawvere
hyperdoctrine triple `∃⊣q*⊣∀`, and the **honest** escrow↔∃ weld. The L0–L4 stack's L1–L3.
**Companions:** `INTENT-REFS-centers.md` (the monoidal/Drinfeld layer + the projection-formula trio),
`INTENT-REFS-resources.md`, `INTENT-AS-CO-RECEIPT.md`.
**Status:** the **corrected** synthesis — two studies (EGNO `Tensor Categories`; the Lawvere-hyperdoctrine
corpus) + an adversarial critique that **refuted two overclaims and one lethal vacuity**. Where the studies
disagreed, this doc records the *critique-verified* verdict. The build plan (§5) is the actionable output.

---

## 0. The frame: dregg is a multi-graded structure, not one category

`INTENT-AS-CO-RECEIPT` + the centers/fairness studies establish dregg as a **graded structure over a
Coecke–Fritz resource SMC**, NOT a single tensor category. The layers (the "L0–L4 stack"):

```
L0  resource SMC + convertibility ⪰              Intent/Resource.lean (BUILT). no extra hypotheses.
L1  module-category factorization                EGNO/Ostrik: positions = Mod_C(A), A = internal End.
L2  the Lawvere hyperdoctrine ∃_a⊣q_a*⊣∀_a        graded modalities over Laws.lean (Predicate⊣Witness base).
L3  the escrow↔∃ weld                             FLP Cor 3.11 monad morphism (NOT a literal Frobenius id).
L4  privacy = a view-comonad / epistemic modality SEPARATE structure (Noninterference.lean is a fragment).
```

dregg's resource theory is **constitutively non-fusion**: irreversibility-first (the `⪰` preorder IS the
second law), partial (the `Resource.lean` camera's `valid`), only *partially* rigid (fungible resources have
duals; NFTs/`Excl` do not), not k-linear/abelian/finite. So EGNO is the wrong *ambient* theory but a right
*source of constructions* — harvest the constructions, drop the finite/fusion classification.

---

## 1. EGNO module categories (L1) — the constructive escrow pool (Ostrik)

From Etingof–Gelaki–Nikshych–Ostrik, *Tensor Categories* (AMS MSM 205) `[pdfs/egnobookfinal.pdf]`, Ch 7:

- **Internal Hom (Def 7.9.2):** `Hom_M(X ⊗ M₁, M₂) ≅ Hom_C(X, Hom(M₁,M₂))` (7.21) — the action functor's
  partial right adjoint. **This IS the receipt⊣intent adjoint, factored through the module structure.**
- **The internal-End algebra:** `A := Hom(M,M)` is an algebra object in `C`; `F : N ↦ Hom(M,N) : M →
  Mod_C(A)` is a module functor. **Ostrik's Theorem (7.10.1):** for finite multitensor `C`, `M ≃ Mod_C(A)` —
  **positions = modules over the escrow pool `A`**, with `A` *reconstructed* (`A = internal End`).
- **`Mod_C(A)` is a tensor category ⟺ `A` is a commutative central algebra** — precisely the
  `CommCentralMonoid` (`Centers.lean`). So EGNO gives the *constructive* pool where FLP was abstract.

⚠ **Import-with-care:** Ostrik's *equivalence* needs **finite multitensor + exactness**, which dregg's
resource theory does NOT have. **Lift the constructions** (internal Hom, `A = Hom(M,M)`, `Mod_C(A)`); **drop**
Ostrik's equivalence + Frobenius–Perron. The constructions need only closedness/representability, not fusion.

---

## 2. The Lawvere hyperdoctrine (L2) — posetal triple, the witness reading

From the Lawvere corpus `[pdfs/lawvere-adjointness-in-foundations-1969-tac-reprint-16.pdf,
lawvere-equality-hyperdoctrines-comprehension-adjoint-1970.pdf, seely-…-beck-condition-1983.pdf,
pitts-tripos-theory{,-in-retrospect}.pdf, awodey-…-categorical-logic-ch3.pdf]`:

- **The triple (Lawvere 1969):** for `q : Γ → Δ`, reindexing `q*` has both adjoints `∃_q ⊣ q* ⊣ ∀_q`, with
  **Beck-Chevalley** (substitution commutes with quantifiers; proving BC for `∃` suffices, Awodey 3.1.28) and
  **Frobenius reciprocity** `∃_q(φ ∧ q*ψ) ≅ ∃_qφ ∧ ψ` (Lawvere 1970: ⟺ substitution preserves `⇒`).
- **mathlib feet (verified, v4.30):** the triple IS two named GaloisConnections —
  `Set.image_preimage` (`∃ ⊣ q*`) and `Set.preimage_kernImage` (`q* ⊣ ∀`), `Data/Set/Lattice/Image.lean:54,57`;
  posetal Frobenius IS `Set.image_inter_preimage` (`Image.lean:441`). **K1/K2/K5 are one-liners.**
- **Tripos / witness reading (Pitts):** the realizability hyperdoctrine where `Φ ≤ Φ'` iff *a realizer
  transforms witnesses for Φ into witnesses for Φ'* — the exact categorical home of "to know X is to hold a
  witness." A tripos = a hyperdoctrine with a generic predicate.
- **Equality-as-adjoint `Θ_X = ∃_Δ⊤` (Lawvere 1970): DO NOT BUILD** — the diagonal is not cartesian in a
  linear resource SMC (`Resource.lean` deliberately omits `CartesianMonoidalCategory`); Track K needs
  modalities/agreement/adjudication, none of which need internal `=`. Route any "two witnesses equal" through
  a hom/profunctor object.

---

## 3. The corrected weld (L3) — the critique's load-bearing fixes ⚠

The studies' headline "FLP `lproj` IS Frobenius reciprocity `∃_a(φ⊗q_a*ψ) ≅ ∃_aφ⊗ψ`" is **a polarity-flipped
overclaim**, refuted against the code:

- **Escrow `T_M = (–⊗M)` (`Centers.lean`) is the RIGHT/lax adjoint `RG`; hyperdoctrine `∃` is a LEFT adjoint**
  (the actual `∃`-side is the `Match.lean` coend). They sit on opposite sides — `lproj` cannot be `∃`'s Frobenius.
- On the built object FLP Lemma 5.11 gives `lproj = id` → the iso form degrades to vacuous `IsIso 𝟙`.
- **The HONEST weld is FLP Cor 3.11 (unconditional):** `lproj_{–,1} : (– ⊗ R1) ⟹ RG` is a **monad morphism**
  — the escrow-tensor monad maps canonically into the fulfillment monad `RG`. It upgrades to an **iso exactly
  under RIGIDITY** (Cor 3.19/3.20). `Resource.lean` is `SymmetricCategory` with **no duals** → rigidity is
  NOT free on the built model; "compositionality is free" would be the overclaim.

**The linear-vs-Heyting fibre decision (the headline model-shape call — resolved: KEEP SEPARATE):**
- **Four grades are genuinely posetal/idempotent** — agent-view (`Knows`), disclosure, causal/frame time,
  capability-attenuation. Fibre = `Set Γ` (Heyting); the triple = the two mathlib GaloisConnections. Faithful, free.
- **The escrow grade is monoidal/non-idempotent** (two escrows ≠ one; `μ = A◁mul` *coalesces*). Forcing it into
  `Set Γ` would impose `φ⊗φ=φ` (false). It lives as the **linear layer in `Centers.lean`**, touching the posetal
  doctrine **only at Frobenius/the Cor-3.11 morphism**. (Matches the existing "escrow KEPT SEPARATE" decision.)

⚠ **The faithful epistemic fibre is NOT the clean mathlib triple.** `Frame.Indist` (`EpistemicConsensus.lean`)
is deliberately **non-equivalence** (models dead/Byzantine agents). `∀_a = Knows` in relation-form has no
proven left adjoint `q*` (so no `kernImage` triple). The clean `kernImage` triple is the *posetal special
case* (a labeled toy); the faithful relation-form object is **unbuilt and possibly non-BC** → DEFER.

---

## 4. K8 — the novel theorem, rescoped ⚠

The intended `reflector_failure ≅ dual-H¹(Byzantine non-gluing)` is **NOT buildable as advertised**:
`dual-H¹` needs an abelian-site sheaf-cohomology stack (`Sheaf J AddCommGrpCat` + Čech/Ext) that mathlib has
but `EpistemicSheaf.lean` is nowhere near instantiating (its `byzantine_section_does_not_glue` is `5≠99` on two
hardcoded records; it deliberately names no H¹ object). The data-`Equiv` fallback is a toy-to-toy re-encoding.
**Rewrite:** build the **Condorcet-collapse `R_vote` ClosureOperator** — a genuine reflector that *actually*
collapses `TRUE≡FALSE` on a concrete Condorcet 3-cycle (the Arrow-escape) — as a standalone theorem with teeth.
The bijection to non-gluing waits until `EpistemicSheaf` grows a real cover-parametrized non-gluing theorem.

---

## 5. THE BUILD PLAN (ranked, critique-verified)

**BUILD FIRST (highest leverage, honest):**
1. **`escrowMonadHom` (FLP Cor 3.11)** in `Centers.lean` — the unconditional monad morphism `(–⊗R1) ⟹ RG`.
   M-effort; feet present (`Adjunction.IsMonoidal`, `rightAdjointLaxMonoidal`, `Adjunction.toMonad`); sidesteps
   the deferred `monoidalKleisli`; **kills the live `IsIso 𝟙` overclaim.**
2. **`escrow_projection_iso_of_rigid` (Cor 3.20) + a refuted non-rigid sibling** — the teeth. Must use a NEW
   non-discrete, non-rigid witness (the built `Resource.lean`/`DemoRes` are vacuous — no duals).

**BUILD (cheap honest assembly — LABEL as the posetal `Set`-doctrine SPECIAL CASE, not "the faithful
hyperdoctrine"):** `Metatheory/Lawvere.lean` —
3. K1/K2/K3 the triple (`Set.image_preimage` + `Set.preimage_kernImage`); K5 posetal Frobenius
   (`Set.image_inter_preimage`); K4 Beck-Chevalley (posetal set-chase) + T2 (BC fails on a non-pullback);
   K6 agreement=limit (restate `EpistemicConsensus.DistKnows`); K7 adjudication = `ClosureOperator` over
   `Disputation.upheld` (the Arrow-escape `byzantine_majority_cannot_uphold` gives it content). Teeth T1
   (`∃_a ≠ ∀_a` on a ≥2-element context).

**DEFER:** the faithful relation-form `∀_a = Knows` triple with BC/Frobenius (investigate whether it even has
the triple before scaffolding). **REWRITE:** K8 → the Condorcet-collapse `R_vote` (above). **DROP:** Lawvere
equality-as-adjoint; the single "THE WELD" diagram (it's two theorems on two layers).

---

## 6. Corpus notes (⚠ mislabels — re-pull if exact axioms are needed)

- `pdfs/maietti-trotta-frobenius-equivalence-beck-chevalley-doctrines-2404.15443.pdf` is actually **van
  Woerkom–van den Berg, AWFS Frobenius/Beck-Chevalley** (weak factorization systems — wrong subject).
- `pdfs/maietti-trotta-quantifier-completions-lawvere-doctrines-2010.09111.pdf` is actually **Trotta–Spadetto,
  *Quantifier completions…*** (this one IS a real Frobenius-reciprocity source: `∃_j(φ∧j*ψ)=∃_jφ∧ψ`, Thm 28).
- The genuine **Maietti–Trotta linear-doctrine** paper and a readable **Gaboardi grading** copy are NOT in the
  corpus (the grading paper couldn't be read) — re-pull if the exact grade-monoid axioms / linear-doctrine
  Frobenius are needed beyond the Trotta–Spadetto + Lawvere-1970 surrogate.

Key files: `Metatheory/Lawvere.lean` (new, Track K), `Dregg2/Intent/Centers.lean` (escrowMonadHom target),
`Dregg2/Intent/Resource.lean` (not rigid — the load-bearing gap), `Dregg2/Apps/EpistemicSheaf.lean`
(K8's deferred (B)-side), `Metatheory/{Disputation,EpistemicConsensus}.lean` (K7/K6), `Dregg2/Laws.lean` (base).
