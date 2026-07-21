/-
# `Dregg2.Circuit.FriEpsFriComposedAdversary` — the HONEST composed `εFri` over a `Q`-bounded
# adversary run, at the design §4.3 target shape.

`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §4.3. Wave-1 (`FriVerifierCompose`) composed three
closed legs over one shared oracle and stated the query leg's blockers; the follow-on
(`FriQueryAdversary`) attached the query leg to a `Q`-bounded adversary (`epsQueryAdv = Q · εQuery`),
gave codex's `epsQueryBias` its adversary form, and PROVED that adversary leg deployed-VACUOUS at
`Q = 2^31`. This file assembles those into the ONE statement the design asks for:

    Pr[ verifyAlgoO accepts ∧ ¬ (honest extraction succeeds) ]  ≤  εFri(Q, params)

over `A : OracleComp permSpec, QueryBounded A Q`, with the ADVERSARY-quantified error

    εFriᵃ = εFS + εGrind + εMerkle + εQueryᵃ        (εQueryᵃ = Q · εQuery)

— every addend an event of ONE adversary's single run against ONE shared oracle `H`, union-bounded
(`condProb_or4_le`), with NO independence assumed anywhere. It reuses `epsFri_compose` (:368) and
`condProb_or4_le` (:353) from wave-1 and the adversary legs from `FriQueryAdversary`; it authors NO
new probabilistic content and modifies NO deployed spec.

## The SHAPE CHANGE from wave-1's `epsFri`, and why it is the honest one

`FriVerifierCompose.epsFri` (:340) adds a BUDGET-INDEPENDENT `epsQuery` — the arithmetic of the
verifier's own honest sampling. That is not the error against an ADVERSARY: an adversary that
re-randomises its commitment gets `Q` independent shots at a lucky challenge (the standard
Fiat–Shamir grinding attack, why deployed FRI ships `PROD_FRI_QUERY_POW_BITS`). The honest composed
error therefore carries the factor `Q` on the query leg: `εFriᵃ` here is `epsFri` with `epsQuery`
replaced by `epsQueryAdv = Q · epsQuery`, and `epsFri_le_epsFriAdv` records that `εFriᵃ ≥ εFri`
whenever `Q ≥ 1` — the adversary error DOMINATES the verifier arithmetic, as it must.

## What is PROVEN here

  * `epsFriAdv_compose` — the four-leg union bound over ONE shared oracle, with the adversary query
    leg; `condProb_or4_le` supplies subadditivity, no independence.
  * `friLdtExtractV3_rom_adv_of_legs` — ⚑ THE DELIVERABLE: the design §4.3 target shape,
    `Pr[accepts ∧ ¬extraction] ≤ εFriᵃ`, over a `Q`-bounded adversary, with the query leg
    adversary-quantified and the composed error NAMED.
  * `query_leg_discharged_over_run` / `epsFriAdv_run` — the abstract theorem's query hypothesis is
    DISCHARGED over an ACTUAL `QueryBounded Q A` run (via `epsQuery_adversary` / `epsFri_four_legs`),
    so the composition connects to reality and the hypotheses are not self-implied.
  * `epsFri_compose_subsumed` — the explicit reuse of wave-1's `epsFri_compose`: the honest-verifier
    composition chains into `εFriᵃ`, i.e. the wave-1 statement is the `Q = 1` corner.
  * `epsFriBiasAdv_*` — the same over codex's DEPLOYED biased sampler (`epsQueryBias`): the "+bias"
    form, dominating the uniform one (`epsFriAdv_le_epsFriBiasAdv`).
  * `epsFriAdv_lt_half_example` — the composed bound is `< 1/2` at an informative parameterisation
    (it genuinely constrains a `Q`-bounded adversary), `epsFriAdv_mono` — and it grows with `Q`.
  * `epsFriAdv_deployed_vacuous_at_2_31` / `_at_2_112` — ⚑ THE HONEST VERDICT: the WHOLE composed
    bound is `≥ 1` (vacuous) at the deployed parameters (`δ = 7/16`, BabyBear `|F|`, `k = 38`,
    `Q = 2^31`), because its `epsQueryAdv` addend ALONE is `≥ 1` there. The composition is REAL; its
    deployed instantiation carries no information — exactly wave-1's finding, now for the full sum.

## What is NOT claimed (verify before optimism as well as pessimism)

  * `accepts_and_fails` is an ABSTRACT `Bool` event with a covering hypothesis `hcover`. Connecting
    it to a literal `verifyAlgoO`-accepts-and-extraction-bundle-fails is exactly blocker (a) — the
    word↔proof bridge (`FriVerifierCompose.WordProofBridge` = `DeployedFriEmbedding`, point-indexed
    per `FriQueryAdversary` §6). This file does NOT discharge `hcover` and does not pretend to.
  * The radius is the PROVEN `L = 1` unique-decoding line `δ = 7/16`. No Johnson upgrade, and NO
    bit-count is read out of this composition — the bit-reading question is the deployed-vacuity of
    the leg (wave-1), not this lane's assembly.

## Discipline
ADDITIVE: imports every input read-only, modifies nothing. `#assert_all_clean` over the keystones;
no `sorry`, no fresh `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.FriQueryAdversary
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false

namespace Dregg2.Circuit.FriEpsFriComposedAdversary

open Dregg2.Crypto.RomOracle
open Dregg2.Crypto.RomCounting
  (cyl condProb condProb_nonneg condProb_le_one condProb_le_of_imp)
open Dregg2.Circuit.FriVerifierCompose
  (epsFS epsGrind epsMerkle epsQuery epsFri hitWin hit_cond condProb_or4_le epsFri_compose)
open Dregg2.Circuit.FriQueryAdversary
  (epsQueryAdv epsQueryBiasAdv epsQuery_nonneg epsQueryAdv_mono
   epsQueryAdv_deployed_vacuous_at_2_31 epsFri_four_legs epsQuery_adversary
   FibreBalanced badAnswers epsQueryAdv_le_epsQueryBiasAdv)
open Dregg2.Circuit.FriQuerySamplingBias (epsQueryBias)

set_option linter.unusedSectionVars false

/-! ## §1 — the adversary-quantified composed error `εFriᵃ`. -/

/-- **⚑ `εFriᵃ` — the composed error against a `Q`-bounded adversary, at the honest radius.**

    εFriᵃ = εFS + εGrind + εMerkle + εQueryᵃ ,   εQueryᵃ = Q · εQuery

Identical to `FriVerifierCompose.epsFri` EXCEPT the query addend carries the factor `Q`: the
adversary's `Q` retries at a lucky folding challenge. Each of the first three addends is the
Stage-2/3 leg value; the fourth is `FriQueryAdversary.epsQueryAdv`, the adversary-quantified query
leg. -/
noncomputable def epsFriAdv (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ) : ℝ :=
  epsFS Q degBound cardF + epsGrind Q powBits + epsMerkle Q cardA + epsQueryAdv Q cardF k δ

/-- The decomposition, definitionally: `εFriᵃ = (εFS + εGrind + εMerkle) + Q·εQuery`. -/
theorem epsFriAdv_eq (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ) :
    epsFriAdv Q degBound cardF powBits cardA k δ
      = epsFS Q degBound cardF + epsGrind Q powBits + epsMerkle Q cardA
        + epsQueryAdv Q cardF k δ := rfl

/-- `εFriᵃ ≥ 0` at any radius `δ ≤ 1` — the sanity fact the composition rests on. -/
theorem epsFriAdv_nonneg (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) :
    0 ≤ epsFriAdv Q degBound cardF powBits cardA k δ := by
  have h1 : 0 ≤ epsFS Q degBound cardF := by unfold epsFS; positivity
  have h2 : 0 ≤ epsGrind Q powBits := by unfold epsGrind; positivity
  have h3 : 0 ≤ epsMerkle Q cardA := by unfold epsMerkle; positivity
  have h4 : 0 ≤ epsQueryAdv Q cardF k δ := by
    unfold epsQueryAdv
    exact mul_nonneg (Nat.cast_nonneg Q) (epsQuery_nonneg cardF k δ hδ1)
  unfold epsFriAdv; linarith

/-! ## §2 — the composition, over ONE shared oracle for ONE `Q`-bounded adversary. -/

section Compose

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- **⚑⚑ THE `εFriᵃ` UNION BOUND — over ONE shared oracle, for ONE `Q`-query adversary.**

Given the four legs' per-run bounds (three closed unconditionally in wave-1, the fourth the
adversary-quantified query leg `≤ Q·εQuery`), the probability that ANY leg fails on the adversary's
single run is `≤ εFriᵃ`. `condProb_or4_le` (:353) supplies subadditivity; the events are all events
of ONE run against ONE `H` under ONE conditioning, so NO independence is assumed — a coupled
adversary cannot violate it. This is `FriVerifierCompose.epsFri_compose` with the query slot moved to
the adversary-quantified value. -/
theorem epsFriAdv_compose
    (C : Finset (D → R)) (wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQueryAdv Q cardF k δ) :
    condProb C (fun H => wFS H || wGrind H || wMerkle H || wQuery H)
      ≤ epsFriAdv Q degBound cardF powBits cardA k δ := by
  refine le_trans (condProb_or4_le C wFS wGrind wMerkle wQuery) ?_
  unfold epsFriAdv
  linarith

/-- **⚑⚑ THE DELIVERABLE — the design §4.3 target, over a `Q`-BOUNDED ADVERSARY.**

    Pr[ accepts ∧ ¬ extraction ]  ≤  εFriᵃ(Q, params)

`accepts_and_fails H` is "the adversary's run against `H` accepts AND the honest extraction bundle
fails" (the abstract stand-in for `verifyAlgoO`-accepts-∧-bundle-fails). `hcover` says that event is
contained in the union of the four bad events — this is the ONLY place blocker (a) (the word↔proof
bridge) enters, and it is left as an explicit hypothesis, NEVER discharged here. Given it and the
four leg bounds, `condProb_le_of_imp` + `epsFriAdv_compose` deliver the bound. The query leg is
adversary-quantified: this is the honest composed FRI soundness over a `Q`-bounded adversary. -/
theorem friLdtExtractV3_rom_adv_of_legs
    (C : Finset (D → R)) (accepts_and_fails wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hcover : ∀ H ∈ C, accepts_and_fails H = true →
      (wFS H || wGrind H || wMerkle H || wQuery H) = true)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQueryAdv Q cardF k δ) :
    condProb C accepts_and_fails ≤ epsFriAdv Q degBound cardF powBits cardA k δ :=
  le_trans (condProb_le_of_imp hcover)
    (epsFriAdv_compose C wFS wGrind wMerkle wQuery Q degBound cardF powBits cardA k δ
      hFS hGrind hMerkle hQuery)

/-- **`εFri ≤ εFriᵃ` for `Q ≥ 1` — the adversary error dominates the verifier arithmetic.** The only
addend that differs is the query leg: `epsQuery ≤ Q·epsQuery` since `Q ≥ 1` and `epsQuery ≥ 0`. So
`FriVerifierCompose.epsFri` is a LOWER bound on the honest adversary error, never the reverse. -/
theorem epsFri_le_epsFriAdv (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hδ1 : δ ≤ 1) (hQ : 1 ≤ Q) :
    epsFri Q degBound cardF powBits cardA k δ
      ≤ epsFriAdv Q degBound cardF powBits cardA k δ := by
  have hnn := epsQuery_nonneg cardF k δ hδ1
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hq : epsQuery cardF k δ ≤ epsQueryAdv Q cardF k δ := by
    unfold epsQueryAdv; nlinarith [hnn, hQR]
  unfold epsFri epsFriAdv; linarith

/-- **⚑ THE REUSE OF `epsFri_compose` — wave-1's composition is the `Q = 1` corner of `εFriᵃ`.**
Fed the honest-verifier leg bounds (query `≤ epsQuery`, no `Q`), `FriVerifierCompose.epsFri_compose`
gives `≤ epsFri`, which chains through `epsFri_le_epsFriAdv` to `≤ εFriᵃ`. So the adversary bound
literally SUBSUMES the wave-1 statement — nothing is lost by moving to the `Q`-quantified error. -/
theorem epsFri_compose_subsumed
    (C : Finset (D → R)) (wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) (hQ : 1 ≤ Q)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQuery cardF k δ) :
    condProb C (fun H => wFS H || wGrind H || wMerkle H || wQuery H)
      ≤ epsFriAdv Q degBound cardF powBits cardA k δ :=
  le_trans
    (epsFri_compose C wFS wGrind wMerkle wQuery Q degBound cardF powBits cardA k δ
      hFS hGrind hMerkle hQuery)
    (epsFri_le_epsFriAdv Q degBound cardF powBits cardA k δ hδ1 hQ)

end Compose

/-! ## §3 — the query hypothesis DISCHARGED over an ACTUAL adversary run.

The abstract §4.3 theorem takes `hQuery : condProb C wQuery ≤ epsQueryAdv Q cardF k δ` as a
hypothesis. §3 discharges it over a real `QueryBounded Q A` run — so the composition is not a
self-implication: the antecedent is met by actual adversaries (`epsQuery_adversary` supplies it), and
its conclusion is about a DIFFERENT event (`accepts_and_fails`, bridged by `hcover`), never among the
hypotheses. -/

section Run

variable {D R Ω AnsT : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype Ω] [DecidableEq Ω]

open Dregg2.Crypto.RomQueryFloor (collWin)

/-- **THE QUERY LEG, DISCHARGED — `εFriᵃ`'s fourth hypothesis is a THEOREM over a real run.**

For a `Q`-bounded adversary `A`, the probability its run EVER reads an answer whose derived challenge
is exceptional for the word committed at that point is `≤ epsQueryAdv Q cardF k δ` — instantiating
`FriQueryAdversary.epsQuery_adversary`'s supplied density at the honest `εQuery` value. The
`Bad`/`FibreBalanced` carriers are exactly the ones `FriQueryAdversary` §3/§6 name (the extractor and
the deployed-sampler idealisation); this file inherits them unchanged and instantiates neither. -/
theorem query_leg_discharged_over_run {Q w nBad cardF k : ℕ}
    (A : OracleComp D R AnsT) (hA : QueryBounded Q A)
    (chal : D → R → Ω) (Bad : D → Finset Ω)
    (hbal : FibreBalanced chal w) (hcard : Fintype.card R = w * Fintype.card Ω)
    (hnBad : ∀ d, (Bad d).card ≤ nBad) (hw : 0 < w) (hΩ : 0 < Fintype.card Ω)
    (δ : ℝ) (hεΩ : (nBad : ℝ) / (Fintype.card Ω : ℝ) ≤ epsQuery cardF k δ)
    (S : Finset D) (σ : D → R) (hσ : ∀ d ∈ S, chal d (σ d) ∉ Bad d) :
    condProb (cyl S σ) (hitWin (badAnswers chal Bad) A) ≤ epsQueryAdv Q cardF k δ := by
  have h := epsQuery_adversary A hA chal Bad hbal hcard hnBad hw hΩ
    (epsQuery cardF k δ) hεΩ S σ hσ
  simpa only [epsQueryAdv] using h

/-- **⚑ THE FULLY-DISCHARGED FOUR-LEG BOUND over ONE run, with the NAMED adversary query addend.**

Every leg is an event of the SAME `QueryBounded Q A` run against the SAME conditioning `cyl S σ`; the
three closed legs are discharged by `hit_cond`/`birthday_cond` and the query leg by
`hit_cond_density` — all inside `FriQueryAdversary.epsFri_four_legs`, whose supplied density we pin at
`epsQuery cardF k δ` so the fourth addend is EXACTLY `epsQueryAdv Q cardF k δ`. This is the honest
composed bound realised over an actual adversary — no independence, no supplied per-leg ε left
abstract except the ones §3 names. -/
theorem epsFriAdv_run {Q L degBound maskBound bQuery cardF k : ℕ}
    (A : OracleComp D R AnsT) (hA : QueryBounded Q A)
    (Mc : OracleComp D R (D × D)) (hMc : QueryBounded L Mc)
    (EFS EPow EQuery : D → Finset R)
    (hEFS : ∀ d, (EFS d).card ≤ degBound) (hEPow : ∀ d, (EPow d).card ≤ maskBound)
    (hEQuery : ∀ d, (EQuery d).card ≤ bQuery)
    (δ : ℝ) (hdens : (bQuery : ℝ) / (Fintype.card R : ℝ) ≤ epsQuery cardF k δ)
    (S : Finset D) (σ : D → R)
    (hσcoll : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b)
    (hσFS : ∀ d ∈ S, σ d ∉ EFS d) (hσPow : ∀ d ∈ S, σ d ∉ EPow d)
    (hσQuery : ∀ d ∈ S, σ d ∉ EQuery d) :
    condProb (cyl S σ)
        (fun H => hitWin EFS A H || hitWin EPow A H || collWin Mc H || hitWin EQuery A H)
      ≤ ((Q : ℝ) * (degBound : ℝ)) / (Fintype.card R : ℝ)
        + ((Q : ℝ) * (maskBound : ℝ)) / (Fintype.card R : ℝ)
        + ((L : ℝ) * (S.card : ℝ) + (L : ℝ) * (L : ℝ) + 1) / (Fintype.card R : ℝ)
        + epsQueryAdv Q cardF k δ := by
  have h := epsFri_four_legs A hA Mc hMc EFS EPow EQuery hEFS hEPow hEQuery
    (epsQuery cardF k δ) hdens S σ hσcoll hσFS hσPow hσQuery
  simpa only [epsQueryAdv] using h

end Run

/-! ## §4 — the DEPLOYED biased sampler: the "+bias" composed error.

Codex's `epsQueryBias` (`FriQuerySamplingBias:305`) carries the `Challenger.sampleBits` modular-
reduction defect. `epsQueryBiasAdv = Q · epsQueryBias` is its adversary form (`FriQueryAdversary`).
§4 composes it exactly as §2 did the uniform leg. -/

/-- **⚑ `εFriᵇ` — the composed error over the DEPLOYED biased query sampler.** The query addend is the
bias-aware `epsQueryBiasAdv = Q · epsQueryBias`, whose survival base carries the `+ 2^logN/|F|`
`sampleBits` defect. -/
noncomputable def epsFriBiasAdv (Q degBound cardF powBits cardA logN k L : ℕ) (δ : ℝ) : ℝ :=
  epsFS Q degBound cardF + epsGrind Q powBits + epsMerkle Q cardA
    + epsQueryBiasAdv Q cardF logN k L δ

section ComposeBias

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- **THE BIAS-AWARE FOUR-LEG UNION BOUND**, over one shared oracle for one `Q`-query adversary. -/
theorem epsFriBiasAdv_compose
    (C : Finset (D → R)) (wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA logN k L : ℕ) (δ : ℝ)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQueryBiasAdv Q cardF logN k L δ) :
    condProb C (fun H => wFS H || wGrind H || wMerkle H || wQuery H)
      ≤ epsFriBiasAdv Q degBound cardF powBits cardA logN k L δ := by
  refine le_trans (condProb_or4_le C wFS wGrind wMerkle wQuery) ?_
  unfold epsFriBiasAdv
  linarith

/-- **THE §4.3 TARGET over the DEPLOYED biased sampler.** Same shape as
`friLdtExtractV3_rom_adv_of_legs`, with the query leg at `epsQueryBiasAdv`. -/
theorem friLdtExtractV3_rom_biasadv_of_legs
    (C : Finset (D → R)) (accepts_and_fails wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA logN k L : ℕ) (δ : ℝ)
    (hcover : ∀ H ∈ C, accepts_and_fails H = true →
      (wFS H || wGrind H || wMerkle H || wQuery H) = true)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQueryBiasAdv Q cardF logN k L δ) :
    condProb C accepts_and_fails ≤ epsFriBiasAdv Q degBound cardF powBits cardA logN k L δ :=
  le_trans (condProb_le_of_imp hcover)
    (epsFriBiasAdv_compose C wFS wGrind wMerkle wQuery Q degBound cardF powBits cardA logN k L δ
      hFS hGrind hMerkle hQuery)

end ComposeBias

/-- **THE DEFECT ONLY WEAKENS THE BOUND — `εFriᵃ ≤ εFriᵇ` at list size `L = 1`.** The biased query
leg dominates the uniform one (`epsQueryAdv_le_epsQueryBiasAdv`), so substituting the honest deployed
sampler moves the composed bound in the SOUND direction, never the reverse. -/
theorem epsFriAdv_le_epsFriBiasAdv (Q degBound cardF powBits cardA logN k : ℕ) (δ : ℝ)
    (hδ1 : δ ≤ 1) :
    epsFriAdv Q degBound cardF powBits cardA k δ
      ≤ epsFriBiasAdv Q degBound cardF powBits cardA logN k 1 δ := by
  have hq := epsQueryAdv_le_epsQueryBiasAdv Q cardF logN k δ hδ1
  unfold epsFriAdv epsFriBiasAdv; linarith

/-! ## §5 — the budget dial: monotone, informative below, VACUOUS at deployed parameters. -/

/-- **THE BUDGET DIAL IS MONOTONE.** More budget, more error — so a vacuity witness at one budget
lifts to every larger one. Each addend is nondecreasing in `Q`; the query addend by
`epsQueryAdv_mono`. -/
theorem epsFriAdv_mono {Q Q' : ℕ} (degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hδ1 : δ ≤ 1) (hQ : Q ≤ Q') :
    epsFriAdv Q degBound cardF powBits cardA k δ
      ≤ epsFriAdv Q' degBound cardF powBits cardA k δ := by
  have hQR : (Q : ℝ) ≤ (Q' : ℝ) := by exact_mod_cast hQ
  unfold epsFriAdv
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_)
    (epsQueryAdv_mono cardF k δ hδ1 hQ)
  · unfold epsFS; gcongr
  · unfold epsGrind; gcongr
  · unfold epsMerkle; gcongr

/-- **⚑ THE COMPOSED BOUND IS INFORMATIVE where the legs are — `< 1/2` at a live parameterisation.**
`epsFriAdv 2 1 1000 8 1000 10 (1/2)` sums the three closed legs (as in
`FriVerifierCompose.epsClosedLegs_lt_half_example`) with the adversary query leg
`2·(1/1000 + (1/2)^10)`, and lands comfortably below `1/2`: the bound genuinely constrains a
`Q`-query adversary rather than restating `≤ 1`. -/
theorem epsFriAdv_lt_half_example :
    epsFriAdv 2 1 1000 8 1000 10 (1 / 2) < 1 / 2 := by
  unfold epsFriAdv epsFS epsGrind epsMerkle epsQueryAdv epsQuery
  norm_num

/-- **⚑⚑ THE HONEST VERDICT — the WHOLE composed bound is VACUOUS at the deployed parameters.**

At `Q = 2^31`, BabyBear `|F| = 2013265921`, `k = 38` spot-checks, radius `δ = 7/16`, the composed
`εFriᵃ` is `≥ 1` for ANY `degBound, powBits, cardA` — because its `epsQueryAdv` addend ALONE is `≥ 1`
(`FriQueryAdversary.epsQueryAdv_deployed_vacuous_at_2_31`) and the other three addends are `≥ 0`. A
probability bound of `≥ 1` asserts nothing. So the composition is REAL and sound, but its deployed
instantiation carries NO information against a `2^31`-query adversary — this is wave-1's vacuity
finding, now for the full four-leg sum, not merely the query leg. No bit-count is read out; the
verdict is that none CAN be, through this pipeline, at these parameters. -/
theorem epsFriAdv_deployed_vacuous_at_2_31 (degBound powBits cardA : ℕ) :
    (1 : ℝ) ≤ epsFriAdv (2 ^ 31) degBound 2013265921 powBits cardA 38 (7 / 16) := by
  have hq : (1 : ℝ) ≤ epsQueryAdv (2 ^ 31) 2013265921 38 (7 / 16) :=
    epsQueryAdv_deployed_vacuous_at_2_31
  have h1 : 0 ≤ epsFS (2 ^ 31) degBound 2013265921 := by unfold epsFS; positivity
  have h2 : 0 ≤ epsGrind (2 ^ 31) powBits := by unfold epsGrind; positivity
  have h3 : 0 ≤ epsMerkle (2 ^ 31) cardA := by unfold epsMerkle; positivity
  -- `linarith` mishandles the concrete-numeral opaque atoms; the monotone `gcongr` path is robust.
  unfold epsFriAdv
  calc (1 : ℝ) = 0 + 0 + 0 + 1 := by ring
    _ ≤ epsFS (2 ^ 31) degBound 2013265921 + epsGrind (2 ^ 31) powBits
          + epsMerkle (2 ^ 31) cardA + epsQueryAdv (2 ^ 31) 2013265921 38 (7 / 16) := by gcongr

/-- **AND VACUOUS ALL THE WAY UP** — by monotonicity, the composed bound is `≥ 1` at `Q = 2^112`, so
no reading of this composition supports the `~112`-bit query column: it sits at a budget where the
bound this pipeline proves says nothing at all. -/
theorem epsFriAdv_deployed_vacuous_at_2_112 (degBound powBits cardA : ℕ) :
    (1 : ℝ) ≤ epsFriAdv (2 ^ 112) degBound 2013265921 powBits cardA 38 (7 / 16) :=
  (epsFriAdv_deployed_vacuous_at_2_31 degBound powBits cardA).trans
    (epsFriAdv_mono degBound 2013265921 powBits cardA 38 (7 / 16) (by norm_num)
      (by norm_num))

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  epsFriAdv_eq,
  epsFriAdv_nonneg,
  epsFriAdv_compose,
  friLdtExtractV3_rom_adv_of_legs,
  epsFri_le_epsFriAdv,
  epsFri_compose_subsumed,
  query_leg_discharged_over_run,
  epsFriAdv_run,
  epsFriBiasAdv_compose,
  friLdtExtractV3_rom_biasadv_of_legs,
  epsFriAdv_le_epsFriBiasAdv,
  epsFriAdv_mono,
  epsFriAdv_lt_half_example,
  epsFriAdv_deployed_vacuous_at_2_31,
  epsFriAdv_deployed_vacuous_at_2_112
]

end Dregg2.Circuit.FriEpsFriComposedAdversary
