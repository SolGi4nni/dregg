# DESIGN — the FRI adversary object, and the `FriLdtExtractV3` discharge ladder

**Lane D1 of the release-arc design wave** (⚠ its sprint plan,
`SPRINT-poster-honesty-closure-2026-07-23`, was never committed under `docs/`).
Status: design + one additive Lean module. **Nothing deployed changes; no VK, no wire, no config.**
Every file:theorem reference below was verified at HEAD 2026-07-23 by reading the statements, not
grep. Predecessor: `docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` (2026-07-16) — its Stages 1–5
are **landed** (`FriVerifierO` / `FriVerifierFS` / `FriVerifierMerkle` / `FriVerifierQuery` /
`FriVerifierCompose`); this document is the successor design for what those stages exposed:
the adversary OBJECT the statements still lack, and the staged discharge of `FriLdtExtractV3`.

**Module landed with this design** (green, `#assert_all_clean`, 9 keystones):
`metatheory/Dregg2/Circuit/FriAdversaryObject.lean` — §2.1 below.

---

## 0. The posture being escaped (the honest baseline, all machine-checked)

- The deployed "security number" was retired as a **calculator output**: `verifyAlgo`
  (`FriVerifier.lean:695`) is a Bool on a *supplied* proof at a *fixed* permutation — no
  adversary, no interaction, no probability.
- The deployed low-degree carrier is **vacuous, as a theorem**:
  `FriCarrierVacuity.friLowDegreeSound_content_iff_true` (`FriCarrierVacuity.lean:123`) proves
  `FriLowDegreeSound` ⟺ `True`; `friLowDegreeSound_has_no_falsifier` proves it is not refutable
  in principle; §3.1 exhibits an accepted garbage twin carrying **no FRI data at all**.
- `StarkSound` rests on the assumed bundle `FriLdtExtractV3`
  (`AlgoStarkSoundTransferV3.lean:131`, consumed at `:262`): a **deterministic,
  ∀-accepting-proof extraction claim at the concrete Poseidon2** — unprovable in principle and
  plausibly false as stated (predecessor design §2). Twelve conjuncts; two (FS
  non-exceptionality) are probabilistic facts wearing deterministic costume.
- The three numbers in circulation, at their honest resolution: **130** = refuted-conjecture
  (capacity) accounting; **57** = Johnson accounting under a carrier the tree does **not** hold;
  **~31.5** = the unique-decoding radius, the only radius the tree proves
  (`FriCarrierVacuity` §5, `deployed_ud_survival_between`; `DeployedProximitySoundness`).
- The honest replacement shape exists and is proven: `FriCarrierEpsilon.FriQueryForgeryBound` —
  ε-bounded, Q-attempt-quantified, **refutable and refuted at a witness**
  (`friQueryForgeryBound_false_without_defect`), with the deployed-sampler bias term `m/N` paid
  (`deployed_forgery_bound`), vacuous by `Q ≈ 2^31` (`deployed_bound_useless_at_2pow32`).

The program (recorded in `project-fri-soundness-reality`): (1) an object for an adversary to BE;
(2) discharge `FriLdtExtractV3` from the real combinatorial bounds + a genuine FS/ROM argument;
(3) only then do bits mean something.

---

## 1. Ground truth at HEAD — the banked substrate this design composes

| substrate | where | what it proves | status |
|---|---|---|---|
| ROM adversary syntax | `Crypto/RomOracle.lean` | `OracleComp` query trees, `QueryBounded` (syntactic budget), determination theorem | green, verified |
| ROM counting core | `Crypto/RomCounting.lean` | `condProb`/`cyl`, `condProb_fresh_eq`, prefix splitting | green, verified |
| query-log substrate | `Crypto/RomQueryLog.lean` | `log`/`evalLog`/`mem_evalLog_answer` — the straight-line extractor's read-back | green |
| the escape dichotomy | `Crypto/RomQueryFloor.lean`, `RomQueryDial.lean`, `FloorGames.lean` | `hard_top_iff_solvableFrac_negl` (⊤ collapses) · `choiceAdv_not_romEff` · `romEff_not_iff_solvableFrac_negl` (the collapse FAILS for `RomEff`) · `binaryRom_budget_separates` (the budget dial is real) · `birthday_cond` | green |
| cost model | `Crypto/CostAdversary.lean` | deep-embedded `FreeOracle`, cost derived FROM SYNTAX, both poles (`bruteForce_not_polyTime`, `idAdv_polyTime`) | green; see §4 |
| poly-time floor falsity | `Exec/SystemRootsBindingReduction.lean:489–530` | `shortCollAdv` + `isPolyTime_of_polySize_answers` ⟹ the instantiated poly-time sponge floor is **FALSE at BabyBear** | theorem |
| keyed repair | `Crypto/KeyedRomFloor.lean` | `keyedRom_hard` + the counterexample dies two ways (`keyedChoiceAdv_excluded`, `fixedPairAdv_negl`) | green |
| oracle verifier (Stage 1) | `metatheory/Dregg2/Circuit/FriVerifierO.lean` | `verifyAlgoO` + faithfulness `verifyAlgoO_run_eq` + `permCallCount` budget | landed |
| FS ε (Stage 2→5) | `FriVerifierFS.lean`, `FriVerifierCompose.lean` §1 | freshness carrier **refuted** (`challenge_computing_adversary_is_not_log_fresh`) and replaced by `hit_cond` — per-query hit bound `Q·b/|R|`, no excluded adversary | landed |
| Merkle extraction (Stage 3) | `FriVerifierMerkle.lean` | `findCollisionZ` (collision **as data**, VCVio shape) + birthday ε + `queriedFinset` | landed |
| query leg (Stage 4) | `FriVerifierQuery.lean` | `epsilon_query_layer` — **fully proven at L=1 unique decoding**; Johnson kept as ONE named hypothesis, never assumed | landed |
| εFri composition (Stage 5) | `FriVerifierCompose.lean` | `epsFri` (`:340`) = εFS+εGrind+εMerkle+εQuery; `epsFri_compose` (`:368`) shared-oracle union bound; `epsFri_closed_legs` (`:392`) — **three of four legs discharged, no supplied ε**; `friLdtExtractV3_rom_of_legs` (`:501`) states the target with the two blockers explicit; apex tree side done (`nodes_union_bound`, `apex_probabilistic_nodeCarrier`) | landed |
| blocker (a), named | `FriVerifierCompose.WordProofBridge` (`:435`) = `DeployedTraceExtract.DeployedFriEmbedding` (`accept_folds` / `decode_trace`) | the word↔proof bridge; the UD-radius math BETWEEN the two maps is already proven (`friProximityK8_discharge0`) | hypothesis structure |
| blocker (b), named + repair banked | `FriVerifierCompose.babybear_sampleBits_not_balanced` (`:482`); repair: `FriQuerySamplingBias.biased_query_survival_pow_le`, composed in `FriCarrierEpsilon` | deployed `sampleBits` provably non-uniform; the `m/N` defect term exists but is **not yet composed into the shared-oracle `epsQuery`** | half-closed |
| per-fold column | `FriLedgerSound.ledger_perFold_soundness` (goodCount 14112 ⟹ perFoldBits 109 at the wrap) | **real, but proven at the wrong radius**: the `hΦ`/`M=1` discharge fires only at `dOut ≥ 496/512` (96.9%) — `FriArityFiberDischarge.arity8_phase_injective` | theorem, radius-gapped |
| Johnson `M=1` falsity | `FriJohnsonRadiusGap.deployed_M1_false_at_johnson` (`:318`); threshold **tight** (`495` vs `496`) | there is **no `M=1` theorem at Johnson**; the honest Johnson count is `M ≤ 7`, `|Good| ≤ 3528` ⟹ ~111 (`arity8_johnson_good_card_le`), even-`lb` only | theorem |
| commit column | `FriDeployedHeightPairing` | deployed pairing is `ir2_leaf_wrap_config @ |D⁰| = 2^22` ⟹ **commitBits 51** (refutes the 61 and the PROVEN-120 "57"); `min{51, 73} − 1 = 50` binds the Johnson path; **arithmetic only — no adversary anywhere**, stated in the file itself | theorem (arith.) |
| non-vacuous (q,pow) point | `FriQueryAdversaryLaunch.launch_100bits_vs_2_22_adv` | **100 bits vs `Q ≤ 2^22`** at `q = 150`, δ=7/16, ext field — a leg-level theorem, with the field-tradeoff law `λ + Qmax ≤ ~122` at ext-4 (`field_ceiling_vacuous_at_2_124`) | theorem (leg) |
| [Sta25]-free transfer | `FriWeightingTransfer.lean` + `FRI-SOUNDNESS-FRONTIER-RESEARCH.md` §8 | BCSS25's O(n) ε_C reachable from public BCIKS20 §7 + `CoCurvilinearity`; residual = the **BCI⁺20 §5 Hensel lift** (GS layer ≈ 3000–6000 lines, multi-month); the `+7` is **not banked** | partial |

**⚠ HEAD-red flag (report, not repair — outside this lane):** `FriVerifierCompose`'s import
closure is red at HEAD: `SpongeForgeReduction.lean:324,329` references
`effFloor_top_false_babyBear` / `effFloor_bot_vacuous`, which live in
`DomainSeparatedCREffRegrounded.lean:263` and are **not in its import list** — an unpropagated
regrounding rename (`SpongeForgeReduction.olean` is absent from the build cache; only
`.hash`/`.trace` remain). Independently found by the concurrent, uncommitted
`DeployedProximitySoundnessSampler.lean` lane (its header documents the same chain). Everything
in `FriAdversaryObject.lean` therefore imports only the verified-green `RomOracle` substrate.

**Concurrent-lane note:** `DeployedProximitySoundnessSampler.lean` (untracked at HEAD) is doing
part of ladder stage L1 at the leg level (link A over the biased sampler via
`FriQueryBiasSharp.biased_query_survival_sharp`). L1 below should land ON that work, not beside
it.

---

## 2. (a) THE OBJECT MODEL — what a FRI prover strategy IS

### 2.1 The typed object (landed: `Dregg2/Circuit/FriAdversaryObject.lean`)

```lean
/-- A FRI prover strategy: the next-round commitment as a function of the FS challenges
so far (round index = prefix length, newest-first). -/
def Strategy (R C : Type) : Type := List R → C

/-- The honest prover inhabits the type: commit the repeated fold of a fixed word. -/
def honestStrategy (fold : C → R → C) (w0 : C) : Strategy R C

/-- The FS transform: n rounds, each round QUERIES the ROM at the encoded
post-commitment transcript prefix and takes the answer as the challenge. -/
def fsRun (enc : C → List R → D) (S : Strategy R C) : ℕ → List R → OracleComp D R (List R)
```

Proven in the module (kernel-clean, no `sorry`, teeth included):

- `fsRun_queryBounded` — **FS challenges ARE ROM queries**, one per round: the transform is a
  syntactically `QueryBounded n` tree, so the whole banked per-query machinery (`hit_cond`,
  `birthday_cond`, `RomQueryLog`) applies to every strategy by construction.
- `fsRun_eval` — **faithfulness**: `eval` against a fixed oracle recovers the deterministic
  chain `fsChain` (the strategy-level `verifyAlgoO_run_eq`); the deployed derandomized FS is
  the `eval` image, so giving the prover an adversary type changes nothing deployed.
- `fsRun_queried` — **the query log IS the transcript**: the queried points are exactly the
  encoded prefixes in round order — what a straight-line extractor reads. No rewinding, no
  forking, matching the predecessor design's BCS16 posture.
- `ChainStep` (typed def — the per-round distance-preservation obligation), `AvoidsBad`, and
  `honest_chain_far` — **farness propagates through the whole fold chain**, proven, conditional
  on `ChainStep`; `chainStep_is_load_bearing` (mutation canary: drop the hypothesis, the
  conclusion is false at a witness) and `honest_chain_far_fires` (positive pole).

The key structural fact the object makes visible: **the ROM domain point carries the
commitment prefix** (`enc (S cs) cs`), so "bad for the commitment it must be good for" is
per-point pricing `E : D → Finset R` — exactly the shape `hit_cond` consumes. The predicate the
old Stage-2/3 freshness carrier wanted ("the challenge point was never queried") was refuted at
every challenge-computing adversary (`challenge_computing_adversary_is_not_log_fresh`); the
strategy object needs no such premise.

### 2.2 The two adversary layers, and how they relate

1. **The proof-finder** `A : OracleComp permSpec (BatchPublicInputs × BatchProof)` with
   `QueryBounded Q A` — the OUTER object `friLdtExtractV3_rom` quantifies over (predecessor
   §4.2). Smallest possible; already the tree's shape.
2. **The strategy** `S : Strategy R C` — the ROUND-STRUCTURED view. Every accepting proof a
   proof-finder outputs determines a transcript; the transcript's committed caps + derived
   challenges ARE a strategy run (the factoring is definitional once the committed word is
   extracted from the query log — stage L4). The strategy layer is where the **combinatorial
   per-fold bounds attach round-by-round** (`ChainStep`), which the flat proof-finder view
   cannot express — this is precisely why εQuery never attached in Stage 5.

### 2.3 Where extraction-shape suffices vs where probability is unavoidable

| leg | shape | why |
|---|---|---|
| Merkle binding | **extraction-as-data** (`findCollisionZ`: two openings ⟹ collision as a pair; no adversary, no probability, nothing to falsify) | DONE (Stage 3); the ε only enters when asking "does the adversary ever HOLD a collision" — `birthday_cond` |
| committed-word definition | **extraction-as-data** — the word read off the query log (`RomQueryLog.mem_evalLog_answer`), well-defined UNLESS a collision is in the log (already priced by εMerkle) | stage L4; no new probability |
| codeword → `VmTrace` decode | **deterministic data** (a decode function + a proof it satisfies `MainAirAcceptF`) | stage L5; zero probability, heavy engineering |
| FS challenges | **probabilistic, unavoidable** — `hit_cond`'s `Q·b/|R|`; a fixed-permutation version is unprovable in principle | DONE |
| grinding | **probabilistic** + accounting re-model (§3 L3) | open |
| query sampling | **probabilistic** + the proven non-uniformity defect (`m/N` term) | banked; compose (L1) |
| per-fold / fold-chain | **probabilistic over challenges**; at UD radius fully provable (L=1 unconditional); at Johnson provable-per-fold-count but extraction needs correlated agreement — the research line | L2 / L7 |

---

## 3. (b) THE DISCHARGE LADDER for `FriLdtExtractV3`

Target (unchanged from the predecessor §4.3): `friLdtExtractV3_rom` — for every `Q`-query
proof-finder, Pr[accepting proof ∧ extraction bundle fails] ≤ εFri(Q, params), the bundle's
twelve conjuncts verbatim. Stage 5 left the union bound proven, three legs discharged, and
`hQuery` blocked on (a) the word↔proof bridge and (b) the sampling defect. The ladder:

**L1 — compose the sampler defect into the shared-oracle query leg.** *Engineering, days;
partially in-flight in the concurrent sampler lane.* Replace `epsQuery cardF k δ = 1/|F| +
(1−δ)^k` with the defected `1/|F| + ((1−δ) + m/N)^k` (or the sharp `((1−δ) + δ/|F|)^k` form of
`FriQueryBiasSharp`), proven against the deployed `sampleBits` model — unifying
`FriCarrierEpsilon`'s independent-attempts shape with `FriVerifierCompose`'s `condProb` model.
**Acceptance bar:** `epsFri_compose` restated with the defected leg; the `N=3, m=2` witness
(`friQueryForgeryBound_false_without_defect`) re-lands as the falsifier in the condProb model.
**Blocked today** by the HEAD-red upstream (§1 flag) — the repair of `SpongeForgeReduction`'s
imports is a one-line C2-class fix that must land first (another lane's item; report, not fix).

**L2 — the round-chain: `ChainStep` instances + the `hit_cond` corollary.** *Engineering, 1–2
weeks. The module landed the skeleton.* Two halves:
  - *(i)* the probability corollary: `winProb (¬ far terminal) ≤ rounds·b/|R|` from
    `fsRun_queryBounded` + `hit_cond` + `honest_chain_far` (two lines once L1's upstream repair
    lands — the module header records why it is deferred).
  - *(ii)* the deployed `ChainStep` instance at the **UD radius**: "a `δ`-far word folded at a
    challenge outside its good set stays far", from `FriFoldArity` (contrapositive of
    `fold_close_of_arity_challenges`) with `goodSet` cardinality = the ledger's `goodCount`
    (this is where `perFoldBits` finally attaches to an adversary). Also *(iii)* the
    **dichotomy leg**: a cheating strategy whose round-`(i+1)` commitment is NOT the fold of
    round-`i` at the drawn challenge is caught by the fold-consistency spot checks except with
    the query-leg probability — the per-round disagreement-survival lemma (new; standard
    BCIKS20 round analysis, fully provable at UD).
  **Acceptance bar:** a composed `chain_far_survival` over ALL fold layers (not Stage 4's one
  layer), everything proven at L=1; mutation canary per instance. **Falsifier:** the wrong-ε
  witness must refute the un-defected form, as in `FriCarrierEpsilon`.

**L3 — the grinding re-accounting.** *Engineering with one real counting proof, ~1–2 weeks.*
The additive `epsGrind Q pow = Q/2^pow` leg is **self-vacuous at `Q = 2^16`**
(`grind_pow16_vacuous_at_2_16`) — as composed, εFri can never certify more than ~pow bits of
budget. Two honest options (ember decision E4):
  - *(A) drop the leg*: prove the extraction bundle does not need "PoW freebie" as a failure
    event (the PoW conjunct only throttles attempts); εFri = εFS + εMerkle + εQuery and `pow`
    is credited **zero** proven bits. Cheapest; matches what the launch file already proves
    (`pow` cannot carry union-bound security).
  - *(B) attempt-divider*: prove the ethSTARK accounting — each usable transcript attempt
    requires a mask hit, so attempts `A ≲ Q/2^pow` except-with-ε, and the FS/query legs' factor
    becomes `A` instead of `Q` — making `pow` worth `+pow` bits of budget as a THEOREM. A real
    ROM counting argument (birthday-genre induction); this is the only route by which `pow=16`
    ever means anything adversary-quantified.
  **Acceptance bar:** either the bundle-without-grind-event theorem, or the attempt-counting
  theorem with its own falsifier (an adversary that recycles one mask hit across attempts must
  be counted once).

**L4 — the word↔proof bridge, half (a): `accept_folds` (verifier-syntax decode).**
*Engineering, heavy, 2–4 weeks.* Define the committed word FROM the query log
(extraction-as-data over `RomQueryLog` + `findCollisionZ`; well-defined except-with-εMerkle),
then prove the deployed `fullChecks` fold-consistency recompute (`FriChecks.foldConsistent`,
the per-query Merkle recomputes) forces the opened positions to agree with `Fold` on that word
— lifting the deployed teeth (`verifyAlgoO_rejects_wrong_query_count` / `_tampered_quotient`)
from shape checks to the fold semantics. **Acceptance bar / falsifier:** `FriCarrierVacuity`'s
garbage twin must FAIL the decoded predicate (it passes only constant checks); an accepting run
under `fullChecks` must yield `Fold … ∈ friSetupK8.C'` — i.e. this stage DISCHARGES
`DeployedFriEmbedding.accept_folds` and the vacuity canary becomes the regression test.

**L5 — the bridge, half (b): `decode_trace` (codeword → `VmTrace`).** *Engineering, the
heaviest single block, 1–3 months.* Stage 5's own comment: "not lemma-sized: it IS the
FRI-proximity-to-VmTrace decode." The UD-radius math between the two maps is ALREADY proven
(`friProximityK8_discharge0`: 0-closeness ⟺ codeword), so this is purely the deterministic
decode: low-degree committed columns → interpolated trace rows → `MainAirAcceptF` + the aux
legs (`OodColumnLayout` supplies the column-layout side). No probability anywhere. **Acceptance
bar:** `DeployedFriEmbedding` becomes a `def` + theorem, not a hypothesis structure;
`embedding_rejects_far_oracle` upgraded from conditional to categorical.

**L6 — assembly at the UD radius, and the apex re-read.** *Engineering, days once L1–L5 land.*
`friLdtExtractV3_rom` proven (not `_of_legs`); instantiated at the recursion VK it discharges a
probabilistic `AggAirSound.FriExtract`; `nodes_union_bound` + `apex_probabilistic_nodeCarrier`
(both already proven) give `GroundedApex` "…except with probability ≤ #nodes·εFri(Q)". Retire
the two remaining costumes onto the one floor (`FriLowDegreeSound`, `FriExtract` — predecessor
§1.4's consolidation). **Acceptance bar:** `#assert_all_clean` on the end-to-end statement; the
two-column law survives (`query_ledger_does_not_determine_perFold` untouched); adversarial
audit reads the final statement against the twelve conjuncts token-for-token.

**L7 — the Johnson upgrade.** *Research.* Everything above prints UD-radius numbers. Moving the
query leg from ~0.83 bits/query (δ=7/16) to ~1.5 (Johnson at ρ=1/8) — the 31.5→57 move at
`q = 38` — requires list-size `L > 1` correlated agreement, where:
  - the per-fold **count** at Johnson is already a theorem (`arity8_johnson_good_card_le`,
    `|Good| ≤ 3528` ⟹ ~111, `M ≤ 7` — even-`lb` configs only), and `M = 1` is **refuted**
    (`deployed_M1_false_at_johnson`, threshold tight at 495/496);
  - the **extraction** at Johnson needs BCIKS20-style correlated agreement. Two sub-options
    (ember decision E5): *(i)* carry it as ONE named, citation-shaped, word-level carrier
    (`FriProximityGapChallenges … L` — the parametric `_carried` theorem in Stage 4 makes this
    a one-hypothesis discharge; auditable, falsifiable, but hypothesis-carrying — under the
    poster law its number is NOT printable as proven); *(ii)* mechanize it — the
    `[Sta25]`-free route is mapped (`FriWeightingTransfer` + `BCSS25-COMMIT-DERIVATION.md`) and
    the honest residual is the BCI⁺20 §5 **Hensel lift over an algebraic function field** on a
    ~3000–6000-line Guruswami–Sudan layer Mathlib lacks entirely: multi-month-to-paper.
  Note the ceiling: at the deployed pairing the **commit column binds the Johnson path at 51
  bits** (`FriDeployedHeightPairing`, `min{51, 73} − 1 = 50`), and BCSS25's unbanked `+7` is
  the only in-reach lift. Johnson-at-deployed-params buys ~50, not 57.

**Out of the ladder** (tracked in `FRI-SOUNDNESS-FRONTIER-RESEARCH.md`): the GG folded-RS
capacity question (§5.1 there), ext-degree changes (§5/E6 below), and the FRI floor's
literature frontier.

---

## 4. (c) THE COST-CLASS REPAIR PATH

The named open work from `CostAdversary`: the deep-embedded cost model prices syntax
(`tick`s + query calls + **answer size**), so a `Classical.choice` `.pure`-leaf that *writes a
short string which happens to be a collision* is `IsPolyTime` and wins with probability 1
against any FIXED compressing instance —
`SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` proves the instantiated
poly-time floor **false at BabyBear**. The model cannot separate "writes a short string" from
"finds a collision". Options for the FRI adversary class:

- **(Q) Query-bounded (`RomEff` / `QueryBounded`)** — the PROVEN escape, with the full
  dichotomy in-tree: `choiceAdv_not_romEff` (the collapse witness is excluded — it would have
  to know a collision it never asked for), `romEff_not_iff_solvableFrac_negl` (the
  `hard_top_iff_solvableFrac_negl` collapse FAILS here), `binaryRom_budget_separates` +
  `RomQueryDial.bruteAdv` (the budget is a real dial: the brute-forcer is IN the exhaustive
  class and OUT of the linear one — it pays a query per point, and may think as
  non-constructively as it likes between queries). **This is the right class for FRI**, and not
  as a compromise: hash-based IOP security in the ROM is *information-theoretic* against
  query-bounded adversaries (BCS16 / ethSTARK state exactly this class), so unbounded
  computation between queries costs the bound nothing. The `shortCollAdv` disease cannot recur:
  the game's instance is the SAMPLED oracle, and a hardwired answer wins only `1/|R|`
  (`KeyedRomFloor.fixedPairAdv_negl` is precisely this death, mechanized).
- **(P) Computability/poly-time (`CostAdversary.IsPolyTime`)** — the honest scope: this class
  matters exactly where the ROM idealization is *removed* — the concrete-Poseidon2
  instantiation, which is the ONE permanent named carrier (predecessor §4.2) and is never
  discharged by anyone. Adding `IsPolyTime` ON TOP of `QueryBounded` for the FRI statement adds
  nothing (the info-theoretic bound already holds without it) and would import the
  answer-size disease into statements that don't need it. Where (P) work continues —
  `reference-grounding-efficient-adversaries`' program, `Eff := PolyTime` over sampled-instance
  games — it repairs the LATTICE/hash-concrete floors, orthogonal to this ladder.

**Verdict (design, not decision):** the FRI adversary class is `QueryBounded Q` over the
Poseidon2-modeled ROM, full stop; the poly-time floor stops being provably false *for FRI* by
never being asserted there. The printable sentence names both: "Q-query ROM adversaries;
Poseidon2-as-random-function is the carried model assumption."

---

## 5. (d) THE FINAL PRINTABLE STATEMENT

**The sentence** (unchanged in shape from the predecessor §7, now with the object to back it):

> **"λ bits against 2^Qmax-query adversaries"** means: for every adversary making at most
> `2^Qmax` queries to the random oracle modeling Poseidon2, the probability of producing an
> accepting proof whose straight-line extraction fails is `εFri(2^Qmax, params) ≤ 2^−λ` — a
> theorem, with two named carriers: the ROM model (permanent), and (Johnson only) the
> correlated-agreement carrier.

It is a **(λ, Qmax) tradeoff line, not one number** — the field caps the sum
(`λ + Qmax ≤ ~122` at ext-4, `field_ceiling_vacuous_at_2_124`), the Merkle birthday leg caps
`λ + 2·Qmax` against the sponge space, and (unless L3-B lands) `pow` contributes nothing.

**The endpoints, honestly labeled:**

| endpoint | needs | what prints |
|---|---|---|
| today (legs only) | — | `epsClosedLegs` real for all Q (`epsFri_exceeds_closed_legs` forbids calling it the bits); query LEG: ~31.5 (outer, UD), **< 19** (wrap `lb=6`, UD — `inner_wrap_ud_survival_gt`); leg-level `launch_100bits_vs_2_22_adv` at `q=150` |
| **E1: engineering complete (L1–L6)** | no new mathematics | **system** εFri at UD radius, deployed params: **~18–31 bits** depending on config — small, TRUE, adversary-quantified; the first number this tree can defend end-to-end |
| E2: + parameter move `q → ~150` (ember E3) | deploy/wire change, prover+size cost | **100 bits vs 2^22-query** (or 60 vs 2^62) as a SYSTEM theorem at UD radius — the poster-grade proven line |
| R1: + Johnson (L7-ii mechanized) | multi-month research | ~50 at deployed heights (commit column 51 binds; BCSS25 `+7` unbanked) — or carrier-named at L7-i, which the poster law refuses to print as proven |
| R2: + ext-degree 8 (E6) | gnark wrap rewrite + VK re-key (`EXT-DEGREE-COST.md`: prover +25%, wrap ~7.5–12M R1CS) | the `PROVEN-120-CONFIG.md` ceiling: **122.60 on every shipped config** at `d=8, lb=6, q=36` — the only route past ~122 on the tradeoff line |

**Research vs engineering:** L1–L6 are engineering (composition of banked theorems + two heavy
decodes); L3-B is a contained counting proof; L7-ii and the GG question are research; E2/R2 are
parameter/deployment campaigns, not proofs.

---

## 6. (e) EMBER DECISIONS (surfaced, not made)

1. **VCVio as a dependency** (the previously-flagged ember-call, predecessor §4.5). Evidence
   now in: Stages 1–5 and this module needed nothing VCVio has that `RomOracle` lacks; the
   statements stayed VCVio-shaped so a later port is mechanical. *Non-binding lean:* stay on
   `RomOracle` through L6; revisit at L7-ii, where PMF/ENNReal and the Fischlin precedent
   actually earn their keep.
2. **Print posture:** print ONLY the UD-radius proven line until L7-ii lands (poster law:
   proven or absent). A Johnson number under the L7-i carrier is auditable but
   hypothesis-carrying — if quoted anywhere, the carrier must be in the same sentence.
3. **The `q` move** (`19/38 → ~150`): the one parameter change that makes the proven leg
   non-vacuous at real budgets (`launch_100bits_vs_2_22_adv`). Costs wire (~4× query openings)
   and prover time; interacts with the C2 VK epochs — should ride a planned VK rotation, and
   the `(λ, Qmax)` split printed (100/22 vs 60/62) is itself a choice.
4. **Grinding accounting** (L3): drop the leg (pow credited 0, cheapest, honest) vs prove the
   attempt-divider (pow worth +pow bits, a real proof). Affects the printed formula's shape.
5. **Johnson budget** (L7): fund the multi-month GS + Hensel-lift mechanization, or hold at
   UD + named carrier indefinitely. The commit column's 51 caps the payoff at deployed heights;
   BCSS25's banked-transfer route is the same decision's cheaper half.
6. **Ext-degree 8** (R2): the only lever past the ~122 tradeoff ceiling; already a standing
   campaign decision (`PROVEN-120-CONFIG.md` — "the answer is d=8 and it is the only answer").
   This ladder neither needs it nor blocks it; the εFri statement is parametric in the field.

---

## 7. Flags for the integrator

- **HEAD-red upstream** (§1): `SpongeForgeReduction.lean` missing-import breakage blocks the
  entire `FriVerifierCompose` closure (and with it L1/L2-i and the concurrent sampler lane).
  One-line import fix + possible type reconciliation (`DeployedSponge` vs
  `DomainSeparatedSponge`) — C2-class, NOT done by this lane (read-only discipline).
- **Cross-file drift:** `FriQueryAdversaryLaunch`'s header quotes the ε_C ceiling as "~61 at
  the deployed worst-case height"; `FriDeployedHeightPairing` (later) refutes 61 and reads
  **51** at the corrected `2^22` pairing. The launch file's *theorems* are unaffected (they are
  about the query leg); the header sentence should be re-pointed when next touched.
- **Two query-leg models in-tree** (`FriCarrierEpsilon`'s independent-attempts space with the
  defect vs `FriVerifierCompose`'s shared-oracle condProb without it) — L1 is the unification;
  until then neither alone is "the" query leg.
- The module `FriAdversaryObject.lean` is additive, imports only the green `RomOracle` closure,
  and is registered in `Dregg2.lean`.
