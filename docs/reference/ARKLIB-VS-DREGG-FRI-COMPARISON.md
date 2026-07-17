# ArkLib vs dregg — FRI/STARK soundness formalization, compared

**What this is.** A cited, side-by-side comparison of the Ethereum-Foundation
[ArkLib](https://github.com/Verified-zkEVM/ArkLib) Lean formalization (checkout `d72f8392`, with its
`VCVio` dependency at `.lake/packages/VCVio`, toolchain `v4.31.0`) against our FRI/STARK soundness
metatheory (`metatheory/Dregg2/`), and a ranked recommendation of what to **adopt**. File:line cites
on both sides; every characterization here was read against the actual code, not memory. Companion to
[`FRI-EXTRACTION-FLOOR-DESIGN.md`](./FRI-EXTRACTION-FLOOR-DESIGN.md) (the discharge plan for our one
assumed leg), [`STARK-SOUNDNESS-CENSUS.md`](./STARK-SOUNDNESS-CENSUS.md) (our floor), and
[`ARKLIB-KZG-VACUITY.md`](./ARKLIB-KZG-VACUITY.md) (the unbounded-adversary disease, found in ArkLib's KZG).

No Lean changes accompany this doc (soundness-adjacent work gets thought before edits).

---

## 0. The one-sentence contrast

**ArkLib has the *statement shape* our FRI soundness lacks — an adversary-as-a-game, a straight-line
extractor, round-by-round soundness, and (in VCVio) a real ROM query-cost model — but its FRI
soundness is `sorry` end to end. We have *proved FRI arithmetic* — per-fold proximity-gap density,
the Johnson list bound, correlated agreement, the query counting bound — instantiated at the deployed
BabyBear parameters and axiom-clean, but no adversary object at the FRI apex, which rests on the
deterministic, undischarged `FriLdtExtractV3` hypothesis.** The two are complementary. The adoption is
to give *our* proved arithmetic *their* statement shape — and we already have a home-grown VCVio-clone
(`Dregg2.Crypto.RomOracle`) to hang it on, so the high-value move is porting a **pattern**, not taking
a **dependency**.

A calibrating fact first: **ArkLib's FRI/proximity/IOP-soundness layer is definitional scaffolding.**
`admit` = 0 everywhere, but `sorry` is pervasive exactly where soundness lives —
`ProofSystem/Fri` 4, `ProofSystem/BatchedFri` 6, `ProofSystem/Stir` 5, `ProofSystem/Whir` 17,
`ProofSystem/Sumcheck` 19, `OracleReduction` 90, `ProofSystem` (all) 117,
`Data/CodingTheory/ProximityGap/BCIKS20` 22. Every headline protocol soundness theorem (FRI Claims
8.1–8.3, sumcheck round soundness, WHIR RBR soundness, Fiat–Shamir, BCS) is `:= by sorry`. What is
genuinely *proved* in ArkLib is the **coding theory** (RS codes, Johnson bound, the BCIKS20 Thm 1.2 /
DG25 correlated-agreement lemmas) and the two **commitment-binding reductions** (KZG→t-SDH,
Ajtai→Module-SIS) — and of those, the KZG one is [vacuous](./ARKLIB-KZG-VACUITY.md). So "adopt ArkLib's
FRI proof" is not on the table; there is no FRI proof to adopt. The valuable assets are (a) the
game/extractor *framework*, (b) VCVio's ROM cost model, (c) their proved RS/proximity *coding lemmas*.

---

## 1. Side-by-side, per concern

Cites: ArkLib paths are under `/private/tmp/arklib-review/ArkLib/`; VCVio under
`…/.lake/packages/VCVio/`; ours under `metatheory/Dregg2/`. "proved" = no `sorry` reachable;
"stated" = the statement exists but the body is `sorry`.

| Concern | ArkLib / VCVio | dregg (`Dregg2/`) |
|---|---|---|
| **Reed–Solomon codes** | **Proved, general, rich.** `code` = degree-`<d` polys evaluated on a domain (`Data/CodingTheory/ReedSolomon.lean:62`); MDS min-distance `minDist … = m-n+1` proved (`:416`); dimension `dim_eq_min_deg_card` (`:320`); unique-decoding radius `uniqueDecodingRadius_RS_eq` (`:543`); rate lemmas (`:335`). | **Proved, but deployment-instantiated**, not a general RS-code development. RS setup is a `FriSetup`/`Submodule F (ι→F)` with `farN`/`closeN`/`disagree` predicates (`metatheory/Dregg2/Circuit/FriSoundness.lean:80,96,104`); the code is the object the fold theorems quantify over. We have no standalone `minDist`/rate library — the distance facts we need are inlined at the BabyBear wrap parameters. |
| **Johnson / list-decoding bound** | **Proved.** `listDecodable` (`Data/CodingTheory/ListDecodability.lean:53`); `johnson_bound` proved (`Data/CodingTheory/JohnsonBound/Basic.lean:271`), alphabet-free variant `:288`; Johnson radius `J q δ` (`:52`). | **Proved at deployed params.** `RSListBound` at the Johnson radius: `rsListBound_johnson_112` with `L=15` (`metatheory/Dregg2/Circuit/FriLdtJohnsonList.lean`, axiom-clean per STARK census); `proximityGap_uniqueDecoding`, `MinDistGt` over `Submodule F (ι→F)` (`metatheory/Dregg2/Circuit/FriLdtJohnson.lean:130,152,189`); the deployed bound `friLdtDeployedBound_discharge` gives `(1/8)^19 = 2^-57` unconditionally. |
| **Proximity gaps / correlated agreement** | **Partly proved, general.** Core defs in `Data/CodingTheory/ProximityGap/Basic.lean` (`proximityGap :74`, the BCIKS20 dichotomy `δ_ε_proximityGap :95`, multilinear/affine CA `:107,125,146,162`). **Proved:** BCIKS20 Thm 1.2 `proximity_gap_RSCodes` (`ProximityGap/BCIKS20/ReedSolomonGap.lean:34`, ~230-line proof) and the whole DG25 RS correlated-agreement chain at the unique-decoding radius (`ProximityGap/DG25/ReedSolomon.lean:38,121,176`). **Stated only:** STIR `proximity_gap` (`ProofSystem/Stir/ProximityGap.lean:34`, `sorry`), WHIR `genRSC.proximity` (`ProofSystem/Whir/ProximityGen.lean:121`, `sorry`), and the deeper BCIKS20 affine-lines subtree (22 `sorry`). | **Proved at deployed params, reduced to one named residual.** Per-fold density `ledger_perFold_soundness` (`metatheory/Dregg2/Circuit/FriLedgerSound.lean:213`) — a Finset-cardinality/field-size ratio bound. Correlated agreement is *reduced* to `WrapCorrelatedAgreementSharp := BadChallengePoly friSetupWrapRate 112 56` via a `sorry`-free reduction (`metatheory/Dregg2/Circuit/FriCorrelatedAgreementSharp.lean`); the boundary-radius instance `wrap_correlatedAgreement_sharp_proved : WrapCorrelatedAgreementSharp 292` is proved axiom-clean (`:466`, `#assert_axioms` at `:1124`) by ordered-pair counting. The arity-8 far-fiber `arity8_phase_injective` is discharged for `dOut ≥ 496` (96.9%-far, `metatheory/Dregg2/Circuit/FriArityFiberDischarge.lean:509`); `good_card_le_of_phase_injective` is the count keystone (`metatheory/Dregg2/Circuit/FriArityTransfer.lean:207`). |
| **Schwartz–Zippel** | **Proved.** counting form `schwartz_zippel_counting` (`Data/MvPolynomial/SchwartzZippelCounting.lean:27`), probability form `prob_schwartz_zippel_mv_polynomial` (`Data/Probability/Instances.lean:457`), wrappers over Mathlib's SZ (`Data/MvPolynomial/Interpolation.lean:38`). Used as the per-round error `deg/|R|` in sumcheck. | **Proved / reduced to it.** The FS-SZ non-exceptionality residual is bounded `ε ≤ deg/|F|` as a **game in `winProb`** (`metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean:288`, `hnonexc_is_bounded_fs_form`; `metatheory/Dregg2/Circuit/OodSoundnessGame.lean:72`, `oodNonExc_winProb = #exceptionalSet/|F|`). The RLC de-batch and LogUp-bus membership reduce to SZ (STARK census). |
| **FRI protocol object** | **Exists, constructed (proved-as-`def`).** FRI is a full `OracleReduction` in the IOP framework: folding round `foldOracleReduction` (`ProofSystem/Fri/Spec/SingleRound.lean:416`), final fold (`:629`), query round `queryVerifier` (`:766`), assembled `reduction` (`ProofSystem/Fri/Spec/General.lean:98`); BatchedFri wraps an RLC batching round (`ProofSystem/BatchedFri/Spec/General.lean:121`). Round-consistency check + its **completeness proved** (`ProofSystem/Fri/RoundConsistency.lean:42`). The fold operator is `CPolynomial.FoldingPolynomial.cpolyFold`. | **No protocol object; a `Bool` verifier on a supplied proof.** `verifyAlgo perm RATE toNat params vk checks initState logN proof pub : Bool` (`metatheory/Dregg2/Circuit/FriVerifier.lean:695`) — six conjoined checks (`foldConsistent`, `merklePaths`, `batchTables`, `queryPow`, `segmentTooth`) over a *supplied* `BatchProofData`/`WrapPublics`; challenges derandomized by `deriveTranscript` (non-interactive FS). No prover, no rounds, no interaction. Our fold operator is `Fold`; fold soundness `fri_fold_soundness` (`metatheory/Dregg2/Circuit/FriSoundness.lean:381`), `friProximity_discharge` (`:409`) are proved over **words** `{f : ι→F} {f' : κ→F} {α : F}`. |
| **FRI soundness statement** | **Stated only (`sorry`).** BatchedFri Claim 8.1 completeness `fri_round_consistency_completeness` (`BatchedFri/Security.lean:256`, `sorry`), Claim 8.2 query soundness `fri_query_soundness` (`:625`, `sorry`), Claim 8.3 headline `fri_soundness` (`:749`, `sorry`): *"if some prover makes the batched-FRI verifier accept w.p. > εC + α^l, then the words have joint correlated agreement"* — an adversary-game ⇒ correlated-agreement extraction shape, reduced to the proved proximity gaps. **The shape is right; the proof is absent.** | **Proved at deployed params, quantified over words + one assumed apex leg.** The query bound `accept_prob_le : |{Q : Fin k→ι \| Accepts f g Q}| / N^k ≤ (1-δ)^k` (`metatheory/Dregg2/Circuit/FriQuerySoundness.lean:132`), `accept_prob_le_of_farN` (`:161`), deployed `deployed_accept_prob_lt < 2^-31` at `k=38` (`:240`). This IS a probability — a **counting measure over the uniform query sample space** — but the sampled object is a word, not an adversary's output. The apex extraction is `FriLdtExtractV3` (below), assumed. |
| **Adversary / cost model** | **The shape exists; VCVio has a real query-cost model.** ArkLib soundness = a game over an arbitrary `Prover`, `Pr[verifier accepts] ≤ ε` (`OracleReduction/Security/Basic.lean:242`), with a straight-line `Extractor.Straightline` reading both `QueryLog`s (`:218`), `knowledgeSoundness` (`:289`), round-by-round `rbrSoundness` + `StateFunction` (`Security/RoundByRound.lean:290,108`). **But ArkLib's adversary is unbounded** — no query/cost restriction on the mainline `Prover`, which is the [KZG-vacuity disease](./ARKLIB-KZG-VACUITY.md). **VCVio supplies the missing bound:** `IsQueryBound`/`IsQueryBoundP`/`IsTotalQueryBound` (`VCVio/OracleComp/QueryTracking/QueryBound.lean:54,227,656`), a semantic `CostModel.queryCost` over any `AddCommMonoid` (`…/CostModel.lean:65`, `unit :230`) with a **proved query-counted birthday bound** `romCRAdvantage_le_birthday` (`VCVio/CryptoFoundations/HardnessAssumptions/CollisionResistance.lean:275`), Markov for cost (`:214`), and structural↔semantic bridges. | **A real ROM query framework exists — but is NOT wired to the FRI apex.** `Dregg2.Crypto.RomOracle` is a *home-grown, self-contained, Mathlib-only* free monad: `inductive OracleComp D R A` (`Crypto/RomOracle.lean:47`), `QueryBounded` (`:68`), `eval_congr_of_agree_on_queried` (`:99`). On top of it: `birthday_cond` (`Crypto/RomQueryFloor.lean:231`), the query-bounded adversary class `RomEff` (`:442`), `choiceAdv_not_romEff` proving `Classical.choice` is excluded (`:548`), and the dichotomy `romCollision_top_false` (`:464`) vs the bounded hardness. Plus a counting-measure `winProb` (`Crypto/ProbCrypto.lean:71`), `Negl`, and a `CollisionFinder` adversary (`metatheory/Dregg2/Circuit/HashFloorHonesty.lean:181`). **None of this touches `verifyAlgo` or `FriLdtExtractV3`** — the FRI algebraic core has no `PMF`/`OracleComp`/`probEvent`/`queryCost` in `Circuit/` at all. |
| **Merkle / vector commitments** | **Binding is game-based; ArkLib has *no* Merkle module** — `find -iname '*merkle*'` in ArkLib → none; `BCS/Basic.lean` is a stub (the `BCSTransform` is commented out, `:56`). Functional-commitment binding = the two-openings game `binding : ∀ adversary, bindingExperiment ≤ ε` (`Commitments/Functional/Basic.lean:167`). **VCVio has the Merkle content:** a game-based `bindingExp` (`VCVio/CryptoFoundations/CommitmentScheme.lean:93`), a `TrapdoorExtractor` (`:114`), Σ-protocol two-transcript extraction `SpeciallySoundAt` (`VCVio/CryptoFoundations/SigmaProtocol.lean:81`), and (per the extraction-floor recon) a computable **collision-as-data** `findCollision` in `VCVio/CryptoFoundations/MerkleTree/Inductive/Binding.lean`. | **Merkle binding is an assumed CR predicate, used deterministically.** `Poseidon2SpongeCR sponge` (collision-resistance of the sponge) is the named floor; the OOD/table binding legs are two `merkleRecomputeZ` recomputes forced to a common root inside `FriLdtExtractV3`'s body. No collision-as-data object at the FRI apex; the CR floor is carried as a `Prop` hypothesis. (We *do* have the collision machinery — `birthday_cond` + `CollisionFinder` — but for the hash floor, not wired into the FRI binding legs.) |

---

## 2. The key contrast — statement shape

This is the gap, stated precisely.

**ArkLib / VCVio state security as a probabilistic game over an adversary.** The canonical form
(`OracleReduction/Security/Basic.lean:242`):

```lean
def soundness (langIn) (langOut) (verifier) (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut, ∀ witIn, ∀ prover : Prover oSpec …, ∀ stmtIn ∉ langIn,
    Pr[fun ⟨_, stmtOut⟩ => stmtOut ∈ langOut | … (reduction.run stmtIn witIn) …] ≤ soundnessError
```

— a *malicious prover* (an `OracleComp`-valued strategy), a *statement outside the language*, and a
*probability of the verifier accepting* bounded by ε. Knowledge soundness adds an existential
straight-line extractor and measures `Pr[verifier accepts ∧ extractor fails]` (`:289`). Round-by-round
adds a `StateFunction` doom predicate and bounds the per-round "doom-flip" probability (`RoundByRound.lean:290`).
VCVio then makes the adversary's *resource* first-class: `IsQueryBound` bounds queries along every
path, `CostModel.queryCost` costs per query with **no time model underneath**, and the payoff is a
theorem like `romCRAdvantage_le_birthday : romCRAdvantage A ≤ (t+2)(t+1) / (2|Y|)` for a `t`-query
adversary. That is the whole apparatus: *an adversary object, a query budget, and a probability of a
bad event bounded by a closed-form ε(Q)*.

**We state FRI soundness as combinatorial bounds over words + an assumed deterministic extraction.**
Two objects carry it:

1. **The ledger — a calculator.** `friLedger : FriParams → Ledger` (`metatheory/Dregg2/Circuit/FriLedger.lean:191`) is
   total `Nat` arithmetic: `goodCount = (m-1)·C(|κ|,2)` (a binomial count), `perFoldBits = Nat.log2((|F|-1)/goodCount)`
   (the exponent of the density `|Good|/|F|`). Its soundness theorem
   `ledger_perFold_soundness` (`metatheory/Dregg2/Circuit/FriLedgerSound.lean:213`) concludes
   `(Good.card : ℝ) / |F| < 1 / 2^perFoldBits` — a Finset-cardinality-to-field-size ratio. There is no
   adversary and no distribution; the "bits" are a density-ratio exponent. Even the query "probability"
   `accept_prob_le` (`metatheory/Dregg2/Circuit/FriQuerySoundness.lean:132`) is `|{Q | Accepts}| / N^k` — a counting
   measure over the *sample space of query tuples*, quantified over the words `f, g`, never over a
   strategy that chooses them.

2. **The apex — an assumed `Prop`.** `FriLdtExtractV3` (`metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean:131`) is
   `def … : Prop := ∀ pi π, verifyAlgo … = true → ∃ (t : VmTrace) …, <twelve conjuncts>` — a
   *deterministic, universally-quantified extraction over all accepting proofs at the fixed concrete
   permutation*. It is **always a hypothesis, never a conclusion**: a whole-directory grep for
   `: FriLdtExtractV3` / `→ FriLdtExtractV3` as a *conclusion* returns zero; every occurrence is the one
   `def` or an `(hfri : FriLdtExtractV3 …)` argument (`AlgoStarkSoundTransferV3.lean:262`,
   `StarkSoundReduce.lean:203,233,258,299`, `StarkSoundFriLdt.lean:20`, `AlgoStarkSoundGeneral.lean:472`).
   The apex `algoStarkSound_transferV3` (`:256`) *consumes* it to produce `AlgoStarkSound`.

**The disconnect, precisely.** The ledger's proven density columns speak *about words and challenge
densities*; the apex's assumed `FriLdtExtractV3` speaks *a deterministic ∀-over-accepting-proofs
extraction Prop*. **Nothing composes them.** The ledger is imported by no apex file; the apex chain runs
entirely through the assumed `FriLdtExtractV3`. There is a probability frame in the tree (`winProb`,
used for the FS/OOD residuals) and a real ROM adversary framework (`RomOracle`/`RomEff`) — but neither
is attached to `verifyAlgo`. So the deployed "57–61 bits" is a *calculator output*: a density ratio
that bounds the success probability of *no object*, because there is no adversary at the FRI apex whose
probability it could bound. This is [FRI-SOUNDNESS-REALITY]'s finding, confirmed against the code.

**And note the mirror-image failure modes.** ArkLib's *shape* is right but its adversary is *unbounded*,
so its stated soundness (were it proved) would be Lean-false the KZG way — `∀ prover, Pr[…] ≤ ε` with
no query bound is refutable by a `Classical.choice` prover (we proved this collapse for *any* game:
`FloorGames.hard_top_iff_solvableFrac_negl`, `Crypto/FloorGames.lean:241`). Our *arithmetic* is right
and *proved*, but has no adversary at all. The synthesis each needs is the same: **a query-bounded
adversary object with a proved ε(Q)** — which is exactly the extraction-floor design's `friLdtExtractV3_rom`.

---

## 3. Adoption recommendation (ranked, concrete)

Ranked by value/effort. Each maps to our specific gap: the assumed `FriLdtExtractV3`, the
ledger↔apex disconnect, the missing adversary.

### #1 (highest) — Adopt the *statement shape*: straight-line extraction over a query-bounded adversary, ported onto our `RomOracle`.

**What.** Re-state `FriLdtExtractV3` in the VCVio/ArkLib knowledge-soundness shape: an adversary
`A : OracleComp permSpec (BatchPublicInputs × BatchProof)` with `QueryBounded A Q`, and
`Pr[verifyAlgo accepts ∧ ¬ExtractBundle] ≤ εFri(Q, params)`, with a **straight-line** extractor reading
the committed word out of the adversary's Merkle-path query log — no rewinding (hash-based IOPs are the
good case). `ExtractBundle` is the twelve conjuncts of today's `FriLdtExtractV3` body verbatim; only the
quantifier changes from "∀ accepting proof, deterministically" to "∀ Q-query adversary, except w.p. ε".
This is exactly the `friLdtExtractV3_rom` target already specced in
[`FRI-EXTRACTION-FLOOR-DESIGN.md`](./FRI-EXTRACTION-FLOOR-DESIGN.md) §4.3; ArkLib's
`Extractor.Straightline` (`Security/Basic.lean:218`, transcript + two `QueryLog`s → witness) and its
`knowledgeSoundness` measured-event (`:289`, "verifier accepts ∧ extractor fails" *inside* the
probability) are the precise templates to imitate.

**What it buys.** The single most-fortunate fact: `verifyAlgo` is *already parametric in
`perm : List F → List F`*, so the re-basing is a re-interpretation, not a rewrite — every FS squeeze,
challenge, and PoW check threads through that one parameter. Once done: the adversary object exists; the
grinding term becomes `Pr[some query hits the mask] ≤ Q/2^powBits` (a birthday-genre theorem, not an
unmodeled Bool); the two FS non-exceptionality conjuncts become theorems (fresh oracle outputs, bounded
by `(Q+1)·deg/|F|`); and the ledger's density columns finally *purchase* something — they become the
`εQuery` addend of `εFri`. "b bits" acquires a defensible meaning: `εFri(2^b, params) ≤ 1/2`.

**What it costs.** A rewrite (additive files, no edits to deployed specs), staged over ~5 steps. **NOT a
dependency** — see #5. The one genuinely hard stage is the query-phase composition (per-fold density →
far-word-survives-all-checks), which is where our proved `ledger_perFold_soundness` meets a *named*
correlated-agreement carrier stated at the *proven radius* (unique-decoding / `M=1`-discharged), never
at Johnson 87.5% where `M=1` is provably false.

**Maps to.** Directly replaces the assumed `FriLdtExtractV3`; closes the ledger↔apex disconnect (the
`εQuery` addend is the ledger); supplies the missing adversary.

### #2 — Adopt VCVio's `IsQueryBoundP` (predicate-targeted) query-bound and the structural↔semantic cost bridge.

**What.** Our `QueryBounded` (`Crypto/RomOracle.lean:68`) is *total* only — at most `Q` queries along
every path. VCVio's `IsQueryBoundP oa p n` (`QueryBound.lean:227`) bounds queries *to the oracles
satisfying `p`*, and `CostModel.queryCost` (`CostModel.lean:65`) generalizes to any `AddCommMonoid`
cost, with proved bridges `WorstCaseCostBound.toIsPerIndexQueryBound_unit` (`:309`) and a cost-Markov
inequality (`:214`). Port the *predicate-targeted* variant and the Markov step.

**What it buys.** In `εFri` we want to count *permutation* queries separately from *grinding* queries;
predicate-targeting states that cleanly, and Markov-for-cost is the lever that turns a query-count bound
into a probability. Ours is ~2× looser (crude count vs `C(n,2)/|R|`) and total-only.

**What it costs.** A `def` + a lemma, ported into `RomOracle`/`RomQueryFloor`. Low. No dependency.

**Maps to.** Sharpens the `εGrind`/`εMerkle` addends of `εFri`.

### #3 — Adopt the binding-as-extraction (collision-as-data) pattern for the Merkle legs.

**What.** Two of `FriLdtExtractV3`'s twelve conjuncts are `merkleRecomputeZ` recomputes forced to a
common root. Replace the *assumed* use of `Poseidon2SpongeCR` in those legs with a computable
`findCollisionZ : … → Option (List ℤ × List ℤ)` in the shape of VCVio's `findCollision`
(`MerkleTree/Inductive/Binding.lean`, collision-as-data — no adversary, nothing to falsify), then bound
"the query log ever contains a collision" by our already-proved `birthday_cond`
(`Crypto/RomQueryFloor.lean:231`). VCVio's Σ-protocol `SpeciallySoundAt` (`SigmaProtocol.lean:81`,
two accepting transcripts → extracted witness) is the same pattern in its two-openings form.

**What it buys.** The two Merkle conjuncts move from assumed to theorem-except-ε; `Poseidon2SpongeCR`'s
*use* becomes derived (the class stays only for the concrete-Poseidon2 instantiation).

**What it costs.** A modest port — the computable collision-finder + a soundness/completeness pair. The
collision-as-data shape is the *good* kind of floor (an object the adversary must *produce*), and we
already have the birthday machinery; the work is wiring, not new mathematics.

**Maps to.** Two conjuncts of the `FriLdtExtractV3` body → `εMerkle`.

### #4 (conditional) — Port the *statements* of ArkLib's proved RS/proximity coding lemmas as our named-carrier targets.

**What.** ArkLib genuinely *proves* what we carry as the named residual `WrapCorrelatedAgreementSharp`:
BCIKS20 Thm 1.2 `proximity_gap_RSCodes` (`BCIKS20/ReedSolomonGap.lean:34`) and the DG25 multilinear
correlated-agreement chain (`DG25/ReedSolomon.lean:176`), plus a general `johnson_bound`
(`JohnsonBound/Basic.lean:271`). Where their radius *covers* ours, their statement is the target our
carrier should reduce to.

**What it buys / the catch.** Their proved CA is mostly at the **unique-decoding radius** (DG25's error
`ε = |ι|/|F|` holds for `δ ≤ relativeUniqueDecodingRadius`); FRI *operates* at the Johnson radius. So
their proved lemmas do **not** directly discharge our Johnson-radius carrier — they discharge the
*unique-decoding* column (which we already have via `friLdtDeployedBound_discharge`, `2^-57`
unconditional). The value is therefore (a) a cross-check that our unique-decoding arithmetic agrees with
a general proof, and (b) a *statement template* for the Johnson carrier — not a drop-in proof. **Effort
is high** because consuming their proof means importing ArkLib (heavy, and their BCIKS20 affine-lines
subtree still carries 22 `sorry`). **Recommendation: port the DG25 CA statement shape as the carrier's
target, do not import ArkLib to consume the proof.**

**Maps to.** The interior of `εQuery` (the correlated-agreement step).

### #5 (do not) — Vendor VCVio as a dependency. See the don't-adopt list.

---

## 4. Don't-adopt list (where we are better, or their approach doesn't fit)

- **Don't adopt ArkLib's FRI soundness proof — there is none.** Claims 8.1–8.3
  (`BatchedFri/Security.lean:256,625,749`) are all `sorry`; sumcheck soundness is `sorry`-backed at the
  single-round level (`Sumcheck/Spec/SingleRound.lean:975`); WHIR/STIR/Fiat–Shamir/BCS soundness is
  `sorry` or commented out. **Our per-fold density, Johnson list bound, query counting, and
  arity-8 fiber are all *proved* and axiom-clean at the deployed BabyBear parameters** — we are strictly
  ahead on *proved FRI arithmetic*. There is nothing to import here.

- **Don't inherit ArkLib's *unbounded-adversary* soundness shape.** `OracleReduction.soundness`
  (`Security/Basic.lean:242`) quantifies over an arbitrary `Prover` with **no query/cost bound** — the
  exact disease that makes ArkLib's own `KZG.binding` [vacuous](./ARKLIB-KZG-VACUITY.md) and that we
  proved collapses *any* game to a density fact (`FloorGames.hard_top_iff_solvableFrac_negl`). Adopt the
  **bounded** shape (VCVio's `IsQueryBound` + our `RomEff`, which already proves `Classical.choice` is
  excluded, `RomQueryFloor.lean:548`), never ArkLib's mainline unbounded `Prover`.

- **Don't vendor VCVio as a dependency.** It is heavy: 454 `.lean` files, a **pinned** `leanprover/lean4:v4.31.0`
  + full Mathlib + two unstable git deps (`loom2`, tracking an unmerged Lean PR; `PolyFun`, on which
  `OracleComp` and every query bound are *definitionally* built) + C/FFI in sibling libs. Our metatheory
  manifest carries none of ArkLib/VCVio, and — decisively — **we already have a self-contained,
  Mathlib-only, axiom-clean VCVio-clone** (`Dregg2.Crypto.RomOracle`: `OracleComp`, `QueryBounded`,
  `birthday_cond`, `RomEff`, the `Classical.choice`-exclusion, the top/bounded dichotomy). Adopting the
  *patterns* (#1–#3) onto `RomOracle` gets stages 1–3 with zero new dependency and a leaner TCB (a plain
  inductive vs `PolyFun.PFunctor.FreeM`). Re-examine vendoring only if the hard query-composition stage
  turns out to need VCVio's `PMF`/`ENNReal` semantics or `QueryLog` erasure that we cannot cheaply add —
  a decision to make *with evidence*, not in advance. (It is also an ember-call per the standing note.)

- **Don't adopt ArkLib's commitment binding for the FRI Merkle legs.** ArkLib has **no Merkle module** at
  all (`BCS` is a stub); its functional-commitment binding is a two-openings *game* that reduces to an
  *unbounded* hardness assumption (t-SDH — vacuous; Module-SIS — sound). For our hash-based FRI the right
  object is VCVio's *collision-as-data* `findCollision` (#3), not ArkLib's algebraic game.

- **Keep our `winProb` counting-measure frame where it already fits.** The FS/OOD non-exceptionality
  residuals are already stated as bounded-advantage events in `winProb` (`AlgoStarkSoundTransferV3.lean:288`,
  `OodSoundnessGame.lean:72`, `OodRomBound.lean`) — a finite counting measure, adequate for the SZ ε and
  lighter than pulling in `PMF`. The `RomOracle`/`winProb` split (adversary counting vs finite-event
  probability) is a reasonable division; don't collapse it onto VCVio's `SPMF` reflexively.

---

## 5. Bottom line

The valuable thing in ArkLib/VCVio for our FRI soundness is **the statement shape, not a proof and not a
dependency**. ArkLib demonstrates the target form (adversary-as-game, straight-line extractor, RBR
soundness) but leaves FRI soundness `sorry`; VCVio supplies the one ingredient that form needs to be
non-vacuous — a **query-bounded** adversary with a **proved ε(Q)** cost model — but as a heavy
dependency. We already own an axiom-clean re-implementation of that ingredient (`RomOracle`/`RomEff`) and
already *prove* the FRI arithmetic ArkLib only states. So the concrete decision this comparison settles:
**port the extraction-shaped, query-bounded statement pattern (#1–#3) onto our existing `RomOracle` to
re-base `FriLdtExtractV3` as `friLdtExtractV3_rom` — do not vendor VCVio, do not import ArkLib.** That is
exactly the plan in [`FRI-EXTRACTION-FLOOR-DESIGN.md`](./FRI-EXTRACTION-FLOOR-DESIGN.md); this comparison
confirms ArkLib/VCVio is the right *reference*, and that we have the substrate to do it in-tree.
</content>
</invoke>
