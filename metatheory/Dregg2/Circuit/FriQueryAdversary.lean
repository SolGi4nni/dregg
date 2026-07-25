/-
# `Dregg2.Circuit.FriQueryAdversary` — `εQuery` ATTACHED TO A `Q`-BOUNDED ADVERSARY, and the
# arithmetic verdict that follows.

`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5, Stage 5 follow-on. This file closes the
QUANTIFIER gap in the query leg, composes it with the three closed legs over the SHARED oracle,
gives `FriQuerySamplingBias.epsQueryBias` its first consumer — and then reports what the resulting
bound is WORTH at the deployed parameters, which is the part that matters.

## The gap this file addresses

`FriVerifierQuery.epsilon_query_layer` (`:267`) and `epsilon_query_deployed` (`:289`) are quantified
over WORDS, not adversaries:

    ∀ (f : ι → F) (f' : κ → F), farN S.C (4*d) f → f' ∈ S.C' →
      |{(α, Q) ∈ F × (Fin k → κ) | Accepts f' (Fold α f) Q}| / |F × (Fin k → κ)|
        ≤ 1/|F| + (1−δ)^k

The far word `f` is FIXED IN ADVANCE and universally quantified; `(α, Q)` is the VERIFIER's own
honest uniform sampling. There is no strategy, no adaptivity, no query budget — nothing an adversary
does appears anywhere in the statement. It is a DENSITY fact about a product sample space.

That is not a defect of the theorem; it is the theorem's honest content. The defect is that nothing
converted it into a statement about an adversary. §2–§4 do the conversion.

## ⚑ THE CONVERSION, AND WHY IT IS THE RIGHT ONE

The uniform `εQuery` is EXACTLY the object `hit_cond` (`FriVerifierCompose:190`) consumes: a
DENSITY BOUND ON AN EXCEPTIONAL ANSWER SET. In the ROM the adversary does not sample `(α, Q)` — it
QUERIES the permutation at a transcript point `d` and reads the challenge off the answer `r`. So

  * `chal d r` = the `(α, Q)` derived from answer `r` at transcript point `d`;
  * `Bad d`    = the challenges that are exceptional for the word committed at `d`;
  * `badAnswers chal Bad d` = `{r | chal d r ∈ Bad d}` — the ANSWERS that hand the adversary a win.

`εQuery` bounds `|Bad d| / |Ω|`. §2 pushes that forward to `|badAnswers d| / |R|`, and `hit_cond`
then pays `Q` times it, over the adversary's ACTUAL run, with NO freshness premise and NO excluded
adversary class (the honest prover included — §1.1 of Stage 5 is what earned that).

    ⚑  εQuery^adv(Q) = Q · εQuery

The factor `Q` is not slack: an adversary that re-randomises its commitment gets `Q` independent
shots at a lucky challenge. This is the standard Fiat–Shamir grinding attack, and it is why
deployed FRI ships `PROD_FRI_QUERY_POW_BITS`. The union bound is tight up to constants.

## ⚑ THE VERDICT AT DEPLOYED PARAMETERS — a REFUTATION, not a lemma

Once the `Q` is attached, the query leg is worth far less than the pipeline's headline numbers
suggest, and §5 proves it as arithmetic rather than asserting it:

    εQuery(|F| = 2013265921, k = 38, δ = 7/16) = 1/|F| + (9/16)^38 ≈ 2^−30.19

    Q · εQuery ≥ 1   already at   Q = 2^31.

So `Q · εQuery` is VACUOUS — it asserts a probability bound `≥ 1`, i.e. nothing at all — at every
budget from `2^31` upward (`epsQueryAdv_deployed_vacuous_at_2_31`, lifted by monotonicity to
`2^112` in `epsQueryAdv_deployed_vacuous_at_2_112`). **The `~112.6`-bit and `~73`-bit query columns
are not merely unproven through this pipeline; they are UNREACHABLE through it, by counting.** The
query leg caps at `≈ 29` bits (`epsQueryAdv_deployed_lt_half_at_2_28` brackets it from below).

The cause is structural and worth naming precisely: with `k = 38` spot-checks at the honest
unique-decoding radius `δ = 7/16`, the per-run error is `2^−31.5`, and once an adversary gets `Q`
retries no union bound can deliver more than `−log₂ εQuery ≈ 30` bits. **More FRI queries would not
help**: at `k = 38` the query term `(9/16)^38 ≈ 2^−31.54` has already sunk BELOW the fold term
`1/|F| ≈ 2^−30.91`, so the binding constraint is the size of the field the folding challenge is
drawn from, not `k`.

⚑ AND A LIVE MISMATCH WITH DEPLOYED CODE, in the conservative direction. `FriVerifierQuery:304`
reads the fold term as `1/|F| ≈ 2^−31` "at BabyBear" — i.e. it instantiates `cardF` at the BASE
field. The deployed folding challenge is drawn from the degree-4 extension: `circuit/src/
plonky3_prover.rs` `PROD_EXT_DEGREE = 4`, `EF = BinomialExtensionField<BabyBear, 4>`,
`|EF| ≈ 2^123.6`, whose own comment says it "is the denominator of every per-fold proximity-gap
bound". So the modelled fold term is ~2^92 times PESSIMISTIC. Correcting it does NOT rescue the
verdict — it moves the cap from `2^29.19` to `2^30.54`, i.e. it buys ONE bit
(`epsQueryAdv_ext_still_vacuous_at_2_32` with its sharpness witness
`epsQueryAdv_ext_not_vacuous_at_2_31`), because the query term `(9/16)^38` then dominates and is
itself only `2^−31.54`. The mismatch is reported as a finding; it is NOT load-bearing for the
conclusion.

## What is PROVEN here, what is NAMED

PROVEN:
  * `hit_cond_density` — `hit_cond` in real-valued density form: `≤ Q · ε`.
  * `badAnswers_card_le` / `badAnswers_density_le` — the pushforward from challenge-space density to
    answer-space density, through the derivation map's fibres.
  * `epsQuery_adversary` — ⚑ THE DELIVERABLE: the adversary-quantified `εQuery`, over a `Q`-bounded
    `OracleComp` run against the shared oracle.
  * `epsQueryBias_adversary` — the same over the DEPLOYED biased sampler; the first consumer of
    codex's `FriQuerySamplingBias.epsQueryBias`.
  * `epsFri_four_legs` — all FOUR legs over ONE oracle, ONE adversary: the composition
    `epsFri_closed_legs` (`FriVerifierCompose:392`) was missing its fourth leg.
  * `miss_density_of_far` — ⚑ CLOSES a gap the lane was asked to close-or-name: codex's `hmiss`
    hypothesis (`(E.card)/m ≤ 1 − δ`) is DERIVED from `δ`-farness by counting, not assumed.
  * §5's arithmetic: the vacuity of the composed bound at deployed parameters.
  * §6.2's `transcriptWordCommitment_exists_iff_binding` — ⚑ the transcript→committed-word residual
    is EXACTLY transcript-binding (an iff, both directions content), and
    `transcriptBinding_of_absorbInjective_and_merkleBinding` factors that into the FS-absorb
    (sponge-collision) and Merkle-binding legs, which are the ones already priced in `εMerkle`.

NAMED, not discharged (each is a REAL obligation, and none is faked here):
  * The DEPLOYED instance of §6.2's `TranscriptWordCommitment` — the map from a transcript point to
    the word committed there. `Bad d` is not well-defined without it; it is a PARAMETER in §3, never
    an instance. ⚑ Classified, not assumed-open: blocker (a) is PARTIALLY closed in-tree —
    `WordProofBridgeDeployed` (`wordProofBridge_of_embedding`) connects the predicate to
    `DeployedFriEmbedding`, `FriFarnessReconcile` reconciles the bridge's 0-farness with `εQuery`'s
    `(4·d)`-farness, and `FriPositiveRadiusPayment` wires the `(1−δ)^k` payment at positive radius.
    What those leave — and what this file therefore still leaves — is (i) the radii coincide only by
    DETERMINISTIC COLLAPSE (both events empty under `accept ⟹ ∈ C`), not by paying at a positive
    radius, (ii) the positive-radius payment is VACUOUS at the deployed `friSetupK8` model
    (`|L| = 16`), a MODEL-RESOLUTION gap, and (iii) the two legs §6.2 reduces the residual to are
    themselves only except-with-`εMerkle` facts, and NEITHER is instantiated at the deployed FS
    absorb / `merkleRecomputeZ` here. What §6 now delivers is the residual's exact shape and its
    decomposition — not the deployed extractor.
  * ⚠ §6.1 records that this residual was previously named by a TAUTOLOGY
    (`TranscriptWordCommitmentTrivial`, `∀ d, isFar (commit d) ∨ ¬ isFar (commit d)` =
    `Classical.em` pointwise). It is retained, proved universally true, and shown blind to the
    distinction the real obligation makes (`trivial_holds_where_contentful_fails`), so the empty
    shape cannot be reintroduced. Nothing ever consumed it.
  * `FibreBalanced` at the deployed sampler. §2's clean density transfer assumes the derivation map
    has equinumerous fibres. Codex PROVED that is FALSE for `Challenger.sampleBits`
    (`babybear_sampleBits_not_balanced`). §4 therefore routes the deployed case through
    `epsQueryBias`, whose `+ 2^logN/|F|` addend is exactly the defect. §6 records that the balanced
    hypothesis is an IDEALISATION, not the deployed sampler.
  * The `n % m` ↔ `Challenger.sampleBits` grounding: still no lemma links the abstract modular
    reduction to the deployed Rust squeeze. NAMED in §6, not papered.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`,
no `native_decide`. ADDITIVE: no existing file is modified.
-/
import Dregg2.Circuit.FriQuerySamplingBias
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false

namespace Dregg2.Circuit.FriQueryAdversary

open Dregg2.Crypto.RomOracle
open Dregg2.Crypto.RomCounting (cyl condProb condProb_nonneg condProb_le_one)
open Dregg2.Circuit.FriVerifierCompose
  (hitWin hit_cond epsQuery epsFS epsGrind epsMerkle epsFri condProb_or4_le)
open Dregg2.Circuit.FriQuerySamplingBias (epsQueryBias epsQueryBias_ge_epsQuery)

set_option linter.unusedSectionVars false

/-! ## §1 — `hit_cond` in DENSITY form.

`hit_cond` pays `Q·b/|R|` for an integer cardinality cap `b`. `εQuery` is a REAL density. This
section is the (trivial, but load-bearing) adapter: a density cap `b/|R| ≤ ε` yields `Q·ε`. -/

section Density

variable {D R A : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **`hit_cond`, PAID IN DENSITY.** A `Q`-query adversary whose per-point exceptional answer set has
density at most `ε` lands in it, at SOME query along its actual run, with probability at most `Q·ε`.

This is `hit_cond` with the integer cap converted to a real density — the form in which an `εQuery`
value (a fraction of a sample space) can be consumed. No new probabilistic content; the content is
`hit_cond`'s tree induction. -/
theorem hit_cond_density {Q b : ℕ} {M : OracleComp D R A} (hM : QueryBounded Q M)
    (E : D → Finset R) (hE : ∀ d, (E d).card ≤ b)
    (ε : ℝ) (hdens : (b : ℝ) / (Fintype.card R : ℝ) ≤ ε)
    (S : Finset D) (σ : D → R) (hσ : ∀ d ∈ S, σ d ∉ E d) :
    condProb (cyl S σ) (hitWin E M) ≤ (Q : ℝ) * ε := by
  refine (hit_cond hM E hE S σ hσ).trans ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hdens (Nat.cast_nonneg Q)

end Density

/-! ## §2 — THE PUSHFORWARD: challenge-space density → answer-space density.

The adversary never samples a challenge; it reads one off an oracle answer. `badAnswers` is the
preimage of the exceptional challenge set under the derivation map, and its density is what
`hit_cond_density` needs. -/

section Pushforward

variable {D R Ω : Type} [Fintype R] [DecidableEq R] [Fintype Ω] [DecidableEq Ω]

/-- **THE EXCEPTIONAL ANSWER SET.** At transcript point `d`, the oracle answers `r` whose derived
challenge `chal d r` is exceptional for the word committed at `d`. This is the `E` that `hit_cond`
takes: it is defined pointwise in `d`, with NO reference to what the adversary does. -/
def badAnswers (chal : D → R → Ω) (Bad : D → Finset Ω) (d : D) : Finset R :=
  Finset.univ.filter (fun r => chal d r ∈ Bad d)

/-- **THE DERIVATION MAP'S FIBRE CAP.** Every challenge has at most `w` answers mapping to it.
⚑ This is an IDEALISATION at the deployed sampler — see §6 and
`FriQuerySamplingBias.babybear_sampleBits_not_balanced`, which proves the deployed `% 2^logN`
reduction does NOT have equinumerous fibres. It is stated to make the clean transfer's cost
explicit, and the deployed route (§4) does not use it. -/
def FibreBalanced (chal : D → R → Ω) (w : ℕ) : Prop :=
  ∀ d ω, (Finset.univ.filter (fun r => chal d r = ω)).card ≤ w

/-- **THE PUSHFORWARD, IN CARDINALITY.** The exceptional answer set is covered by the fibres over
the exceptional challenges, so it has at most `w · |Bad d|` elements. -/
theorem badAnswers_card_le (chal : D → R → Ω) (Bad : D → Finset Ω) (w : ℕ)
    (hbal : FibreBalanced chal w) (d : D) :
    (badAnswers chal Bad d).card ≤ w * (Bad d).card := by
  have hcover : badAnswers chal Bad d
      = (Bad d).biUnion (fun ω => Finset.univ.filter (fun r => chal d r = ω)) := by
    ext r
    simp only [badAnswers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨chal d r, h, rfl⟩
    · rintro ⟨ω, hω, hr⟩
      rw [hr]; exact hω
  rw [hcover]
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ ω ∈ Bad d, (Finset.univ.filter (fun r => chal d r = ω)).card
      ≤ ∑ _ω ∈ Bad d, w := Finset.sum_le_sum (fun ω _ => hbal d ω)
    _ = (Bad d).card * w := by rw [Finset.sum_const, smul_eq_mul]
    _ = w * (Bad d).card := by ring

/-- **THE PUSHFORWARD, IN DENSITY.** When the derivation map is exactly `w`-to-one
(`|R| = w · |Ω|`), the challenge-space density transfers to the answer space UNCHANGED. This is the
statement that lets an `εQuery` value be spent as an `ε` in `hit_cond_density`. -/
theorem badAnswers_density_le (chal : D → R → Ω) (Bad : D → Finset Ω) (w nBad : ℕ)
    (hbal : FibreBalanced chal w) (hcard : Fintype.card R = w * Fintype.card Ω)
    (hnBad : ∀ d, (Bad d).card ≤ nBad) (hw : 0 < w) (hΩ : 0 < Fintype.card Ω)
    (εΩ : ℝ) (hεΩ : (nBad : ℝ) / (Fintype.card Ω : ℝ) ≤ εΩ) (d : D) :
    (((badAnswers chal Bad d).card : ℝ)) / (Fintype.card R : ℝ) ≤ εΩ := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hΩR : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  have hRR : (Fintype.card R : ℝ) = (w : ℝ) * (Fintype.card Ω : ℝ) := by
    rw [hcard]; push_cast; ring
  have hnum : ((badAnswers chal Bad d).card : ℝ) ≤ (w : ℝ) * (nBad : ℝ) := by
    have h1 : (badAnswers chal Bad d).card ≤ w * nBad :=
      (badAnswers_card_le chal Bad w hbal d).trans (Nat.mul_le_mul_left w (hnBad d))
    exact_mod_cast h1
  rw [hRR]
  rw [div_le_iff₀ (by positivity)]
  have : (nBad : ℝ) ≤ εΩ * (Fintype.card Ω : ℝ) := by
    rw [div_le_iff₀ hΩR] at hεΩ; exact hεΩ
  nlinarith [hnum, this, hwR.le]

end Pushforward

/-! ## §3 — ⚑ THE DELIVERABLE: `εQuery` over a `Q`-BOUNDED ADVERSARY RUN. -/

section Adversary

variable {D R Ω AnsT : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype Ω] [DecidableEq Ω]

/-- **⚑⚑ `εQuery`, QUANTIFIED OVER ADVERSARIES.**

For ANY `Q`-query oracle adversary `A` — no strategy restriction, no freshness premise, no excluded
class, the honest prover included — the probability that `A`'s run EVER receives an answer whose
derived challenge is exceptional for the word committed at that point is at most `Q · εΩ`, where
`εΩ` is the uniform challenge-space density that `FriVerifierQuery.epsilon_query_layer` supplies.

⚑ WHAT MOVED. The hypothesis `hεΩ` is a density fact about the CHALLENGE SPACE (`|Bad|/|Ω| ≤ εΩ`)
— precisely the shape `epsilon_query_layer` proves, with `Ω = F × (Fin k → κ)`. The CONCLUSION is
about the adversary's actual run against the shared oracle. Nothing here is implied by its own
antecedent: the antecedent is a counting statement about a fixed finite set, the consequent a
probability over an adaptive `Q`-query run, and the bridge is `hit_cond`'s tree induction.

⚑ WHAT IS STILL CARRIED. `Bad : D → Finset Ω` is a PARAMETER. Instantiating it — "the exceptional
challenges for the word committed at transcript point `d`" — requires §6.2's
`TranscriptWordCommitment`, which §6.2 proves is EXACTLY transcript-binding of the deployed
`(accepts, pt, committed)` triple, and §6.4 shows is precisely what turns `Bad` into a point-indexed
set (`badSet_pointIndexed`). The deployed instance is undischarged. This theorem does not touch it
and does not pretend to. -/
theorem epsQuery_adversary {Q w nBad : ℕ}
    (A : OracleComp D R AnsT) (hA : QueryBounded Q A)
    (chal : D → R → Ω) (Bad : D → Finset Ω)
    (hbal : FibreBalanced chal w) (hcard : Fintype.card R = w * Fintype.card Ω)
    (hnBad : ∀ d, (Bad d).card ≤ nBad) (hw : 0 < w) (hΩ : 0 < Fintype.card Ω)
    (εΩ : ℝ) (hεΩ : (nBad : ℝ) / (Fintype.card Ω : ℝ) ≤ εΩ)
    (S : Finset D) (σ : D → R) (hσ : ∀ d ∈ S, chal d (σ d) ∉ Bad d) :
    condProb (cyl S σ) (hitWin (badAnswers chal Bad) A) ≤ (Q : ℝ) * εΩ := by
  refine hit_cond_density hA (badAnswers chal Bad) (b := w * nBad) ?_ εΩ ?_ S σ ?_
  · intro d
    exact (badAnswers_card_le chal Bad w hbal d).trans (Nat.mul_le_mul_left w (hnBad d))
  · have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
    have hΩR : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
    have hRR : (Fintype.card R : ℝ) = (w : ℝ) * (Fintype.card Ω : ℝ) := by
      rw [hcard]; push_cast; ring
    rw [hRR, div_le_iff₀ (by positivity)]
    have hb : (nBad : ℝ) ≤ εΩ * (Fintype.card Ω : ℝ) := by
      rw [div_le_iff₀ hΩR] at hεΩ; exact hεΩ
    push_cast
    nlinarith [hb, hwR.le]
  · intro d hd
    simp only [badAnswers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hσ d hd

/-- **⚑ THE DEPLOYED-SAMPLER FORM — the first consumer of codex's `epsQueryBias`.**

Same statement, with the ε instantiated at the BIAS-AWARE query error
`epsQueryBias cardF logN k L δ = L/|F| + ((1−δ) + 2^logN/|F|)^k`
(`FriQuerySamplingBias:305`), whose second addend carries the `Challenger.sampleBits` modular-
reduction defect. This is the value the query leg composes to over the DEPLOYED non-uniform query
indices, now attached to a `Q`-bounded adversary.

The density hypothesis is left as a hypothesis on purpose: supplying it is supplying the pushforward
through the ACTUAL deployed derivation map, which is the `n % m` ↔ `sampleBits` grounding named in
§6. What this theorem establishes is that ONCE that density is in hand, the adversary bound is
`Q · epsQueryBias` and not something worse. -/
theorem epsQueryBias_adversary {Q b : ℕ}
    (A : OracleComp D R AnsT) (hA : QueryBounded Q A)
    (E : D → Finset R) (hE : ∀ d, (E d).card ≤ b)
    (cardF logN k L : ℕ) (δ : ℝ)
    (hdens : (b : ℝ) / (Fintype.card R : ℝ) ≤ epsQueryBias cardF logN k L δ)
    (S : Finset D) (σ : D → R) (hσ : ∀ d ∈ S, σ d ∉ E d) :
    condProb (cyl S σ) (hitWin E A) ≤ (Q : ℝ) * epsQueryBias cardF logN k L δ :=
  hit_cond_density hA E hE _ hdens S σ hσ

end Adversary

/-! ## §4 — THE FOUR-LEG COMPOSITION over ONE oracle, ONE adversary.

`epsFri_closed_legs` (`FriVerifierCompose:392`) discharged three legs and left `εQuery` off the
disjunction entirely. With §3 the fourth leg is an event of the SAME run against the SAME `H`, so it
joins the union bound directly. -/

section Compose

variable {D R AnsT : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

open Dregg2.Crypto.RomQueryFloor (collWin birthday_cond)

/-- **⚑⚑ ALL FOUR LEGS, OVER A SHARED ORACLE, FOR ONE `Q`-QUERY ADVERSARY.**

`εFS + εGrind + εMerkle + εQuery^adv` — where the query leg is now `Q · εQ`, an event of the SAME
adversary's SAME run, not a detached density over a product space. No independence is assumed
anywhere: all four are events over one `H` under one conditioning, which is what makes the union
bound legitimate against a coupled adversary.

⚑ Note the SHAPE CHANGE from `FriVerifierCompose.epsFri`: the query addend is `Q · εQ`, not `εQ`.
`epsFri` as defined (`:340`) adds a BUDGET-INDEPENDENT `epsQuery`, which is the arithmetic of a
verifier's honest sampling, not of an adversary with `Q` retries. §5 is about what that factor
costs. -/
theorem epsFri_four_legs
    {Q L degBound maskBound bQuery : ℕ}
    (A : OracleComp D R AnsT) (hA : QueryBounded Q A)
    (Mc : OracleComp D R (D × D)) (hMc : QueryBounded L Mc)
    (EFS EPow EQuery : D → Finset R)
    (hEFS : ∀ d, (EFS d).card ≤ degBound) (hEPow : ∀ d, (EPow d).card ≤ maskBound)
    (hEQuery : ∀ d, (EQuery d).card ≤ bQuery)
    (εQ : ℝ) (hdens : (bQuery : ℝ) / (Fintype.card R : ℝ) ≤ εQ)
    (S : Finset D) (σ : D → R)
    (hσcoll : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b)
    (hσFS : ∀ d ∈ S, σ d ∉ EFS d) (hσPow : ∀ d ∈ S, σ d ∉ EPow d)
    (hσQuery : ∀ d ∈ S, σ d ∉ EQuery d) :
    condProb (cyl S σ)
        (fun H => hitWin EFS A H || hitWin EPow A H || collWin Mc H || hitWin EQuery A H)
      ≤ ((Q : ℝ) * (degBound : ℝ)) / (Fintype.card R : ℝ)
        + ((Q : ℝ) * (maskBound : ℝ)) / (Fintype.card R : ℝ)
        + ((L : ℝ) * (S.card : ℝ) + (L : ℝ) * (L : ℝ) + 1) / (Fintype.card R : ℝ)
        + (Q : ℝ) * εQ := by
  refine (condProb_or4_le _ _ _ _ _).trans ?_
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact hit_cond hA EFS hEFS S σ hσFS
  · exact hit_cond hA EPow hEPow S σ hσPow
  · exact (birthday_cond hMc S σ hσcoll).trans (le_of_eq (by ring))
  · exact hit_cond_density hA EQuery hEQuery εQ hdens S σ hσQuery

end Compose

/-! ## §5 — ⚑ THE ARITHMETIC VERDICT AT DEPLOYED PARAMETERS.

`circuit/src/plonky3_prover.rs`: `PROD_FRI_LOG_BLOWUP = 3` (rate `1/8`, unique-decoding radius
`δ = 7/16`), `PROD_FRI_NUM_QUERIES = 38`. `FriVerifierQuery:289` instantiates `cardF` at BabyBear
`|F| = 2013265921`.

This section is the REFUTATION. It is arithmetic, `norm_num`-decided, over the actual deployed
constants — not a modelling remark. -/

/-- The adversary-quantified query leg as a function of the budget: `Q · εQuery`. Named separately
from `FriVerifierCompose.epsQuery` so the two can never be confused — the latter has no `Q`. -/
noncomputable def epsQueryAdv (Q cardF k : ℕ) (δ : ℝ) : ℝ := (Q : ℝ) * epsQuery cardF k δ

/-- The bias-aware adversary-quantified query leg (§3's deployed form) as a function of budget. -/
noncomputable def epsQueryBiasAdv (Q cardF logN k L : ℕ) (δ : ℝ) : ℝ :=
  (Q : ℝ) * epsQueryBias cardF logN k L δ

/-- `epsQuery` is non-negative at any radius `δ ≤ 1` — the sanity fact the monotonicity needs. -/
theorem epsQuery_nonneg (cardF k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) : 0 ≤ epsQuery cardF k δ := by
  unfold epsQuery
  have h1 : (0 : ℝ) ≤ 1 / (cardF : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (1 - δ) ^ k := pow_nonneg (by linarith) k
  linarith

/-- **THE BUDGET DIAL IS MONOTONE.** More budget, more error — so a vacuity witness at one budget
lifts to every larger budget. -/
theorem epsQueryAdv_mono {Q Q' : ℕ} (cardF k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) (hQ : Q ≤ Q') :
    epsQueryAdv Q cardF k δ ≤ epsQueryAdv Q' cardF k δ := by
  unfold epsQueryAdv
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (epsQuery_nonneg cardF k δ hδ1)

/-- **⚑⚑ THE REFUTATION — the adversary-quantified query leg is VACUOUS at `Q = 2^31`.**

`2^31 · (1/2013265921 + (9/16)^38) ≥ 1`. A "probability bound" of `≥ 1` asserts NOTHING: every
event satisfies it. So at the deployed parameters the query leg carries no information whatsoever
against a `2^31`-query adversary.

⚑ This is a WITNESS, not a hedge. The numbers are the shipped ones (`PROD_FRI_NUM_QUERIES = 38`,
rate `1/8` ⟹ `δ = 7/16`, BabyBear `|F|`), and the inequality is decided by `norm_num` over exact
rationals. -/
theorem epsQueryAdv_deployed_vacuous_at_2_31 :
    (1 : ℝ) ≤ epsQueryAdv (2 ^ 31) 2013265921 38 (7 / 16) := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **THE BRACKET FROM BELOW — the leg is still meaningful at `Q = 2^28`.** `2^28 · εQuery < 1/2`.
Together with the vacuity at `2^31` this pins the query leg's capacity to `≈ 29` bits: the bound is
informative below `2^29` and empty above `2^31`. It is a real function of `Q`, not a constant. -/
theorem epsQueryAdv_deployed_lt_half_at_2_28 :
    epsQueryAdv (2 ^ 28) 2013265921 38 (7 / 16) < 1 / 2 := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **⚑⚑ THE `112`-BIT COLUMN IS UNREACHABLE THROUGH THIS PIPELINE.** By monotonicity from
`2^31`, the adversary-quantified query leg is `≥ 1` — i.e. vacuous — at `Q = 2^112`.

So no reading of this composition supports "≈112.6 bits", and none supports the `73`-bit Johnson
query column either: both sit at budgets where the bound this pipeline can prove says nothing at
all. Raising the radius to Johnson changes `δ`, not the fact that a `Q`-retry union bound cannot
exceed `−log₂ εQuery ≈ 30` bits at `k = 38`. -/
theorem epsQueryAdv_deployed_vacuous_at_2_112 :
    (1 : ℝ) ≤ epsQueryAdv (2 ^ 112) 2013265921 38 (7 / 16) :=
  epsQueryAdv_deployed_vacuous_at_2_31.trans
    (epsQueryAdv_mono 2013265921 38 (7 / 16) (by norm_num) (by norm_num))

/-- **⚑ THE EXTENSION-FIELD CORRECTION DOES NOT RESCUE IT — it buys ONE bit.**

`FriVerifierQuery:304` reads the fold term at the BASE field; the deployed folding challenge lives
in the degree-4 extension (`PROD_EXT_DEGREE = 4`, `|EF| = 2013265921^4 ≈ 2^123.6`). Instantiating
`cardF` at the extension makes the fold term negligible — and the leg is STILL vacuous at `2^32`,
because the surviving query term `(9/16)^38 ≈ 2^−31.54` is itself only just below `2^−31`.

⚑ THE EXACT COST OF THE CORRECTION, recorded honestly: at the extension field the leg is NOT yet
vacuous at `2^31` (`2^31 · ε ≈ 0.686 < 1`) — it becomes vacuous at `2^32`. So the base-field
mismatch understates the cap by ~1.35 bits, moving it from `≈2^29.19` to `≈2^30.54`. That is the
whole effect. The mismatch is a FINDING about doc-comment fidelity (and it is conservative: the
modelled fold term is ~2^92 too pessimistic), NOT the cause of the verdict. -/
theorem epsQueryAdv_ext_still_vacuous_at_2_32 :
    (1 : ℝ) ≤ epsQueryAdv (2 ^ 32) (2013265921 ^ 4) 38 (7 / 16) := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **AND THE ONE-BIT GAIN IS REAL, NOT ROUNDING.** At the extension field the leg is genuinely
still informative at `2^31` — `2^31 · ε < 1`. Stated so the previous theorem's `2^32` cannot be
mistaken for slack in the arithmetic: `2^31` is the LAST budget the extension instantiation
survives, and `2^32` is the first it does not. -/
theorem epsQueryAdv_ext_not_vacuous_at_2_31 :
    epsQueryAdv (2 ^ 31) (2013265921 ^ 4) 38 (7 / 16) < 1 := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **THE QUERY TERM HAS ALREADY SUNK BELOW THE FOLD TERM AT `k = 38`.** `(9/16)^38 < 1/|F|` at
BabyBear. Consequence: **increasing the number of FRI spot-checks cannot improve the base-field
instantiation** — the binding constraint is the size of the field the folding challenge is drawn
from. This is why §5's cap is insensitive to `k`, and it is the same `~31`-bit ceiling
[[reference-umem-boundary-31bit]] and the felt-width campaign keep surfacing. -/
theorem deployed_query_term_below_fold_term :
    (9 / 16 : ℝ) ^ 38 < 1 / 2013265921 := by norm_num

/-- **THE DEPLOYED BIAS COSTS ALMOST NOTHING — the defect is real but not the problem.** At
`L = 1` the bias-aware adversary leg dominates the uniform one (codex's `epsQueryBias_ge_epsQuery`,
scaled by the budget). Composed with §5's vacuity this says: the `sampleBits` non-uniformity moves
the bound in the sound direction and is nowhere near large enough to be what caps the leg. -/
theorem epsQueryAdv_le_epsQueryBiasAdv (Q cardF logN k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) :
    epsQueryAdv Q cardF k δ ≤ epsQueryBiasAdv Q cardF logN k 1 δ := by
  unfold epsQueryAdv epsQueryBiasAdv
  exact mul_le_mul_of_nonneg_left (epsQueryBias_ge_epsQuery cardF logN k δ hδ1)
    (Nat.cast_nonneg Q)

/-! ## §6 — ⚑ CLOSING codex's `hmiss`, and NAMING what remains.

Two grounding gaps were in scope: (i) `hmiss` assumed rather than derived from `δ`-farness, and
(ii) no lemma linking the abstract `n % m` to the deployed `Challenger.sampleBits`. (i) is CLOSED
here by counting. (ii) is NAMED, with the obligation stated as a definition so nothing here can be
mistaken for a discharge. -/

/-- **⚑ `hmiss` IS A THEOREM, NOT A HYPOTHESIS — derived from `δ`-farness by counting.**

Codex's `biased_query_survival_pow_le` (`FriQuerySamplingBias:260`) takes
`hmiss : (E.card)/m ≤ 1 − δ` as an assumption. When `E` is the AGREEMENT set of a `δ`-far word —
which is what the FRI spot-check survival event actually is — that hypothesis FOLLOWS: agreement and
disagreement partition the index set, so `δ`-farness (`disagree > δ·|κ|`) forces
`|agree| < (1−δ)·|κ|`.

This removes an assumption from the bias-aware query bound rather than adding one: the miss density
is now a CONSEQUENCE of the farness that `εQuery` already hypothesises. -/
theorem miss_density_of_far {κ F : Type} [Fintype κ] [DecidableEq κ] [DecidableEq F]
    (f g : κ → F) (δ : ℝ) (hκ : 0 < Fintype.card κ)
    (hfar : δ * (Fintype.card κ : ℝ)
      < ((Finset.univ.filter (fun i => f i ≠ g i)).card : ℝ)) :
    ((Finset.univ.filter (fun i => f i = g i)).card : ℝ) / (Fintype.card κ : ℝ) ≤ 1 - δ := by
  have hκR : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hκ
  have hpart : (Finset.univ.filter (fun i => f i = g i)).card
      + (Finset.univ.filter (fun i => ¬ (f i = g i))).card = Fintype.card κ := by
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset κ)) (p := fun i => f i = g i)
  have hpartR : ((Finset.univ.filter (fun i => f i = g i)).card : ℝ)
      + ((Finset.univ.filter (fun i => f i ≠ g i)).card : ℝ) = (Fintype.card κ : ℝ) := by
    have := hpart
    push_cast [← this]
    ring
  rw [div_le_iff₀ hκR]
  linarith

/-! ### §6.1 — the transcript→committed-word map: the CONTENT-FREE shape, RETAINED as a record.

`Bad d` in §3 is "the challenges exceptional for the word committed at transcript point `d`". That
phrase presupposes a map from a transcript POINT to a word — Merkle extraction/binding.

⚑ CLASSIFIED HONESTLY (verify before pessimism as well as optimism). This is NOT simply blocker (a)
restated: `WordProofBridgeDeployed.wordProofBridge_of_embedding` already derives `WordProofBridge`
from `DeployedFriEmbedding`, over the real `decodeColumn` encoding. But that bridge is PER-PROOF
(`committed : Proof → Word`), whereas `hit_cond` needs the commitment indexed by the ORACLE QUERY
POINT `d`, because the exceptional set must be fixed BEFORE the answer at `d` is drawn.

⚠ THIS RESIDUAL WAS ONCE NAMED BY A TAUTOLOGY. The predicate below — `∀ d, isFar (commit d) ∨
¬ isFar (commit d)` — is `Classical.em` pointwise: TRUE of every `commit` and every `isFar`,
demanding nothing of either. It is kept here, under a name that says what it is, so that the
emptiness is a RECORDED fact and the shape cannot be silently reintroduced as though it were an
obligation. §6.2 states the obligation WITH CONTENT and proves exactly what it demands. -/

/-- **⚠ CONTENT-FREE — the shape this residual USED to carry, retained under an honest name.**

`∀ d, isFar (commit d) ∨ ¬ isFar (commit d)` is excluded middle at each point. It constrains neither
`commit` nor `isFar`, mentions no verifier, and supplying it supplies nothing
(`transcriptWordCommitmentTrivial_always`). It is not a weak form of the extraction obligation — it
is not a form of it at all: `trivial_holds_where_contentful_fails` exhibits one `commit` that
satisfies THIS and refutes §6.2's `TranscriptWordCommitment` on the same data. -/
def TranscriptWordCommitmentTrivial {D Word : Type} (commit : D → Word) (isFar : Word → Prop) :
    Prop :=
  ∀ d : D, isFar (commit d) ∨ ¬ isFar (commit d)

/-- **THE RECORD — the content-free shape is TRUE OF EVERYTHING.** No hypothesis on `commit`, none
on `isFar`, none on the deployed verifier, no reference to acceptance: it is `Classical.em`
pointwise. Anything that consumed it would consume nothing. -/
theorem transcriptWordCommitmentTrivial_always {D Word : Type} (commit : D → Word)
    (isFar : Word → Prop) : TranscriptWordCommitmentTrivial commit isFar :=
  fun d => Classical.em (isFar (commit d))

/-! ### §6.2 — ⚑ THE OBLIGATION, WITH CONTENT: proof-indexed commitment made POINT-indexed.

What §3 actually needs is not "the committed word is far or it is not". It is a map
`commit : D → Word` that

  * is a function of the TRANSCRIPT POINT ALONE — so that `Bad := fun d => badOf (commit d)` is
    fixed BEFORE the answer at `d` is drawn, which is exactly what `hit_cond` demands of its `E`
    (`badSet_pointIndexed`); and
  * AGREES, on ACCEPTING proofs, with the proof-indexed commitment `WordProofBridge` already carries
    (`committed : Proof → Word`, `FriVerifierCompose:435`, instantiated over the deployed column
    encoding by `WordProofBridgeDeployed.wordProofBridge_decodedColumn`).

`pt : Proof → D` is the transcript point at which that layer's folding challenge is squeezed — in
the deployed FS transform, the post-commitment sponge state; the point whose ORACLE ANSWER the run
reads its challenge off (`hit_at_transcript_point_iff_of_log`, via `RomQueryLog`'s read-back
`mem_evalLog_answer`). -/

/-- **⚑⚑ THE RESIDUAL, WITH CONTENT.** A point-indexed extraction `commit` is CORRECT for the
deployed pair `(accepts, committed)` when every ACCEPTING proof's own committed word is what
`commit` reads off that proof's transcript point.

This is a real demand on `commit`: it is refutable (`trivial_holds_where_contentful_fails`), it is
satisfiable (`transcriptWordCommitment_satisfiable_when_bound`), and for some deployed pairs it is
UNSATISFIABLE by any `commit` whatsoever (`transcriptWordCommitment_unsatisfiable_when_equivocating`)
— none of which can be said of §6.1's shape. -/
def TranscriptWordCommitment {D Proof Word : Type} (accepts : Proof → Bool) (pt : Proof → D)
    (committed : Proof → Word) (commit : D → Word) : Prop :=
  ∀ p : Proof, accepts p = true → commit (pt p) = committed p

/-- **TRANSCRIPT-BINDING** — two ACCEPTING proofs that squeeze their folding challenge at the SAME
transcript point commit the SAME word. This is the property of the deployed `(accepts, pt,
committed)` triple; it mentions no extractor. -/
def TranscriptBinding {D Proof Word : Type} (accepts : Proof → Bool) (pt : Proof → D)
    (committed : Proof → Word) : Prop :=
  ∀ p p' : Proof, accepts p = true → accepts p' = true → pt p = pt p' → committed p = committed p'

open Classical in
/-- **⚑⚑ THE RESIDUAL IS *EXACTLY* TRANSCRIPT-BINDING — an IFF, not a hedge.**

A point-indexed extraction exists **iff** the deployed triple is transcript-binding. So the residual
§3 carries is not "some unspecified Merkle work": it is precisely the statement that an accepting
transcript point determines the committed word, no weaker and no stronger.

⚑ Both directions are content. `→` says any extractor forces binding — an equivocating pair refutes
every candidate at once (`no_commitment_of_equivocation`). `←` says binding is ENOUGH: the extractor
is then definable outright (choice over the accepting fibre of `pt`), so nothing beyond binding is
owed. That is what converts "supply an extractor" into "prove binding", which is the shape the
Merkle/sponge legs are already priced in. -/
theorem transcriptWordCommitment_exists_iff_binding {D Proof Word : Type} [Nonempty Word]
    (accepts : Proof → Bool) (pt : Proof → D) (committed : Proof → Word) :
    (∃ commit : D → Word, TranscriptWordCommitment accepts pt committed commit)
      ↔ TranscriptBinding accepts pt committed := by
  constructor
  · rintro ⟨commit, hc⟩ p p' hp hp' hpt
    rw [← hc p hp, ← hc p' hp', hpt]
  · intro hbind
    refine ⟨fun d => if h : ∃ q, accepts q = true ∧ pt q = d then committed h.choose
      else Classical.arbitrary Word, ?_⟩
    intro p hp
    have hex : ∃ q, accepts q = true ∧ pt q = pt p := ⟨p, hp, rfl⟩
    show (if h : ∃ q, accepts q = true ∧ pt q = pt p then committed h.choose
      else Classical.arbitrary Word) = committed p
    rw [dif_pos hex]
    exact hbind hex.choose p hex.choose_spec.1 hp hex.choose_spec.2

/-- **⚑ ONE EQUIVOCATING PAIR KILLS EVERY CANDIDATE EXTRACTOR.** If two accepting proofs share a
transcript point but commit DIFFERENT words, no `commit : D → Word` satisfies the obligation — the
residual is not merely undischarged there, it is UNSATISFIABLE. This is why the deployed instance is
an except-with-ε statement (see `transcriptBinding_of_absorbInjective_and_merkleBinding`): on the
oracles where a sponge collision or a Merkle equivocation occurs, there is no extractor at all. -/
theorem no_commitment_of_equivocation {D Proof Word : Type}
    (accepts : Proof → Bool) (pt : Proof → D) (committed : Proof → Word)
    {p p' : Proof} (hp : accepts p = true) (hp' : accepts p' = true)
    (hpt : pt p = pt p') (hne : committed p ≠ committed p') :
    ¬ ∃ commit : D → Word, TranscriptWordCommitment accepts pt committed commit := by
  rintro ⟨commit, hc⟩
  exact hne (by rw [← hc p hp, ← hc p' hp', hpt])

/-- **⚑ WHAT THE DEPLOYED INSTANCE OWES, FACTORED INTO ITS TWO PRICED LEGS.**

Transcript-binding follows from two facts about accepting runs, and from nothing else:

  * `habsorb` — the FS ABSORB leg: equal challenge-squeeze points force equal Merkle roots. In the
    deployed transform `pt` is the post-commitment sponge state, so this is injectivity of the
    absorb on accepting transcripts — a SPONGE-COLLISION statement, priced by
    `RomQueryFloor.birthday_cond` / `FriVerifierMerkle.merkle_path_collision_prob_le`, i.e. the
    `epsMerkle` leg;
  * `hmerkle` — the MERKLE BINDING leg: equal roots force equal committed words. This is
    `FriVerifierMerkle.findCollisionZ_none_binds` (binding from path-collision-freeness, with NO
    `Poseidon2SpongeCR` hypothesis), again on the no-collision event.

⚠ NEITHER LEG IS DISCHARGED HERE, and neither is unconditional: both hold only OFF the collision
event, so the extractor this yields is well-defined except-with-`εMerkle`. What this theorem
delivers is that the residual decomposes into exactly those two already-named, already-priced facts
— no third obligation, and in particular nothing about farness, radii, or the sampler. -/
theorem transcriptBinding_of_absorbInjective_and_merkleBinding
    {D Proof Word Digest : Type} (accepts : Proof → Bool) (pt : Proof → D)
    (root : Proof → Digest) (committed : Proof → Word)
    (habsorb : ∀ p p', accepts p = true → accepts p' = true → pt p = pt p' → root p = root p')
    (hmerkle : ∀ p p', accepts p = true → accepts p' = true → root p = root p' →
      committed p = committed p') :
    TranscriptBinding accepts pt committed :=
  fun p p' hp hp' hpt => hmerkle p p' hp hp' (habsorb p p' hp hp' hpt)

/-! ### §6.3 — TEETH: the contentful residual is neither excluded middle nor always-false.

Three witnesses over the SAME `accepts` and the SAME `pt`, differing only in `committed` / `commit`
— so the content is isolated exactly where it belongs. -/

/-- **THE OBLIGATION FIRES (satisfiable).** Two accepting proofs at ONE transcript point committing
the SAME word: the constant extractor is correct. So `TranscriptWordCommitment` is not the
always-false predicate. -/
theorem transcriptWordCommitment_satisfiable_when_bound :
    TranscriptWordCommitment (fun _ : Bool => true) (fun _ : Bool => ())
      (fun _ : Bool => true) (fun _ : Unit => true) :=
  fun _ _ => rfl

/-- **⚑ THE OBLIGATION IS UNSATISFIABLE ON AN EQUIVOCATING PAIR.** Same `accepts`, same `pt` as
above; only `committed` changes — the two accepting proofs now commit DIFFERENT words at the one
transcript point. NO extractor exists. This is the sharpest evidence that the predicate is not
excluded middle in disguise: excluded middle is never unsatisfiable. -/
theorem transcriptWordCommitment_unsatisfiable_when_equivocating :
    ¬ ∃ commit : Unit → Bool,
        TranscriptWordCommitment (fun _ : Bool => true) (fun _ : Bool => ())
          (fun b : Bool => b) commit :=
  no_commitment_of_equivocation _ _ _ (p := true) (p' := false) rfl rfl rfl (by decide)

/-- **⚑ THE RENAME IS NOT COSMETIC — the old shape cannot tell a CORRECT extractor from a WRONG
one.** For the extractor `fun _ => false` the retained content-free predicate HOLDS, while the
contentful obligation on the corresponding deployed data FAILS. The two predicates are therefore not
variants of one obligation; §6.1's carried no obligation at all. -/
theorem trivial_holds_where_contentful_fails :
    TranscriptWordCommitmentTrivial (fun _ : Unit => false) (fun b : Bool => b = true)
      ∧ ¬ TranscriptWordCommitment (fun _ : Bool => true) (fun _ : Bool => ())
            (fun b : Bool => b) (fun _ : Unit => false) := by
  refine ⟨transcriptWordCommitmentTrivial_always _ _, ?_⟩
  intro h
  exact Bool.noConfusion (h true rfl)

/-! ### §6.4 — what the commitment BUYS §3: `Bad` becomes point-indexed, read back off the LOG. -/

/-- **⚑ `Bad` BECOMES POINT-INDEXED.** With a correct extractor in hand, `fun d => badOf (commit d)`
is manifestly a function of the query point ALONE — the shape `hit_cond`/`epsQuery_adversary` take
for `E`/`Bad` — and at every accepting proof it computes that proof's OWN exceptional set. This is
the one line §3's `Bad` parameter was waiting for; all the content sits in the hypothesis, which is
the point (cf. `bundleFail_imp_far_of_bridge`). -/
theorem badSet_pointIndexed {D Proof Word Ω : Type}
    {accepts : Proof → Bool} {pt : Proof → D} {committed : Proof → Word} {commit : D → Word}
    (hcommit : TranscriptWordCommitment accepts pt committed commit) (badOf : Word → Finset Ω)
    (p : Proof) (hacc : accepts p = true) :
    (fun d => badOf (commit d)) (pt p) = badOf (committed p) := by
  show badOf (commit (pt p)) = badOf (committed p)
  rw [hcommit p hacc]

/-- **⚑ THE READ-BACK IS THE QUERY LOG'S.** On an accepting proof, the answer the run actually
received at that proof's transcript point is recovered from the ORACLE QUERY LOG
(`RomQueryLog.mem_evalLog_answer`: a logged pair `(d, r)` has `H d = r`), and §2's point-indexed
`badAnswers` at that point is EXACTLY the proof's own exceptional-challenge test. So the object
`hit_cond` prices on the adversary's run and the object `εQuery` bounds on the committed word are
the same object, once the extractor exists.

⚑ This is the wiring, not a discharge: it consumes `TranscriptWordCommitment` and gives back the
`E`-shaped set. The extractor's existence is still §6.2's obligation. -/
theorem hit_at_transcript_point_iff_of_log {D R Ω AnsT Proof Word : Type}
    [Fintype R] [DecidableEq R] [Fintype Ω] [DecidableEq Ω]
    {accepts : Proof → Bool} {pt : Proof → D} {committed : Proof → Word} {commit : D → Word}
    (hcommit : TranscriptWordCommitment accepts pt committed commit)
    (chal : D → R → Ω) (badOf : Word → Finset Ω)
    (A : OracleComp D R AnsT) (H : D → R) (p : Proof) (hacc : accepts p = true)
    {r : R} (hlog : (pt p, r) ∈ (A.evalLog H).2) :
    r ∈ badAnswers chal (fun d => badOf (commit d)) (pt p)
      ↔ chal (pt p) (H (pt p)) ∈ badOf (committed p) := by
  have hr : H (pt p) = r := A.mem_evalLog_answer H hlog
  rw [hr, ← hcommit p hacc]
  simp [badAnswers]

/-- **NAMED, NOT DISCHARGED — the `n % m` ↔ `Challenger.sampleBits` grounding.**

`FriQuerySamplingBias` models the deployed query index as `n % m` for a uniform squeeze `n`. No
in-tree lemma connects that to the Rust `Challenger.sampleBits`. The obligation is: the deployed
sampler's index at transcript point `d` under answer `r` EQUALS the modelled reduction. Stated as a
predicate so it can be discharged (or refuted) later against the emitted verifier, and so that its
absence is visible rather than implicit. -/
def SampleBitsGrounding {D R : Type} (deployedIdx : D → R → ℕ) (toNat : R → ℕ) (m : ℕ) : Prop :=
  ∀ d r, deployedIdx d r = toNat r % m

/-- The grounding predicate is not vacuous — it is satisfiable exactly by the modelled reduction,
and therefore says something falsifiable about a deployed sampler that differs from it. -/
theorem sampleBitsGrounding_of_eq (D : Type) {R : Type} (toNat : R → ℕ) (m : ℕ) :
    SampleBitsGrounding (D := D) (fun _ r => toNat r % m) toNat m := fun _ _ => rfl

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  hit_cond_density,
  badAnswers_card_le,
  badAnswers_density_le,
  epsQuery_adversary,
  epsQueryBias_adversary,
  epsFri_four_legs,
  epsQuery_nonneg,
  epsQueryAdv_mono,
  epsQueryAdv_deployed_vacuous_at_2_31,
  epsQueryAdv_deployed_lt_half_at_2_28,
  epsQueryAdv_deployed_vacuous_at_2_112,
  epsQueryAdv_ext_still_vacuous_at_2_32,
  epsQueryAdv_ext_not_vacuous_at_2_31,
  deployed_query_term_below_fold_term,
  epsQueryAdv_le_epsQueryBiasAdv,
  miss_density_of_far,
  transcriptWordCommitmentTrivial_always,
  transcriptWordCommitment_exists_iff_binding,
  no_commitment_of_equivocation,
  transcriptBinding_of_absorbInjective_and_merkleBinding,
  transcriptWordCommitment_satisfiable_when_bound,
  transcriptWordCommitment_unsatisfiable_when_equivocating,
  trivial_holds_where_contentful_fails,
  badSet_pointIndexed,
  hit_at_transcript_point_iff_of_log,
  sampleBitsGrounding_of_eq
]

end Dregg2.Circuit.FriQueryAdversary
