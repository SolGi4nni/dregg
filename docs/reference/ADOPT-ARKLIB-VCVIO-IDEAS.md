# ADOPT-ARKLIB-VCVIO-IDEAS — bringing the best of ArkLib/VCVio into our stack

**What this is.** A prioritized, whole-architecture adoption plan: which structural and
methodological ideas from the Ethereum-Foundation [ArkLib](https://github.com/Verified-zkEVM/ArkLib)
Lean formalization (checkout `d72f8392` at `/private/tmp/arklib-review`) and its `VCVio` dependency
(`.lake/packages/VCVio`, the Verified-zkEVM-orbit fork) are worth bringing into our metatheory
(`metatheory/Dregg2/`), and in what form — port-in-tree, depend-on, or be-inspired-by. This is
library-design and proof-infrastructure work: monadic abstractions, statement shapes, module
organization, dependency-graph methodology. Constructive infrastructure, not an attack study.

**Companions — read those for the slices they own; this doc does not re-derive them:**
- [`ARKLIB-VS-DREGG-FRI-COMPARISON.md`](./ARKLIB-VS-DREGG-FRI-COMPARISON.md) — the FRI/soundness
  slice, side-by-side with cites. Its verdicts stand and are inherited here: ArkLib's FRI soundness
  is `sorry` end-to-end; our FRI *arithmetic* is proved at deployed params; the adoption is a
  **statement shape**, not a proof or a dependency.
- [`FRI-EXTRACTION-FLOOR-DESIGN.md`](./FRI-EXTRACTION-FLOOR-DESIGN.md) — the staged plan for the
  single highest-value adoption (`friLdtExtractV3_rom`). Idea **B1** below is a pointer to it, not
  a restatement.
- [`ARKLIB-KZG-VACUITY.md`](./ARKLIB-KZG-VACUITY.md) — the unbounded-adversary disease; the
  standing reason we never adopt ArkLib's mainline soundness quantifier.

No Lean changes accompany this doc. Cites: ArkLib/VCVio paths are at checkout `d72f8392`
(toolchain `v4.31.0`); ours are `file:line` at HEAD 2026-07-16, under `metatheory/Dregg2/` unless
noted.

---

## 0. The three maturity profiles (why the adoption is asymmetric)

The three trees fail and succeed in *complementary* places, so "adopt their best ideas" means
different things per source:

- **ArkLib** (ArkLib/ = 274 files) is **architecture-rich, proof-porous**: a genuinely elegant
  four-layer stack — `To{Mathlib,VCVio,CompPoly}/` upstream staging (sorry-free by rule) →
  `Data/` (protocol-independent math, the proved crown jewel: RS codes, Johnson, Guruswami–Sudan,
  BCIKS20/DG25 proximity gaps) → `OracleReduction/` (the IOP framework: `ProtocolSpec`,
  `seqCompose`, a fully-proved `Lens` algebra) → `ProofSystem/` + `Commitments/`. Its sorry-debt
  (90 in OracleReduction, 117 in ProofSystem) is concentrated exactly at the **glue theorems** —
  binary `Append` security preservation (`OracleReduction/Composition/Sequential/Append.lean:450–526`),
  lens transport, Fiat–Shamir/BCS — while both the leaf math below and the composed statements
  above are in place. What's adoptable is the *organization* and the *statement shapes*, plus the
  proved coding theory as reference.
- **VCVio** (VCVio/ = 208 core files) is **genuinely proved**: 8 sorries, 0 axioms, all at the
  newest transform frontier (FO, GPV). Its reusable design is the *layering*: syntax
  (`OracleComp := PFunctor.FreeM`, `OracleComp/OracleComp.lean:21`) / handler (`QueryImpl` = just
  a function, `SimSemantics/QueryImpl/Basic.lean:30`) / handler *transformers*
  (`withLogging`/`withCaching`/`withCost` — the lazy random oracle is literally
  `uniformSampleImpl.withCaching`, `QueryTracking/RandomOracle/Basic.lean:20`) / semantics
  (typeclass lifts into `SPMF := OptionT PMF`). Cost and probability share one wp backbone
  (`expectedCost_eq_wp_costDist`, `QueryTracking/CostModel.lean:136`). Its center of gravity is
  concrete/exact security — query-counted ENNReal bounds — with asymptotics stated externally and
  `isPPT` deliberately abstract. What's adoptable is the framework *pattern* — but as a
  dependency it is disqualified for now (§4).
- **Ours** (Dregg2/ ≈ 1300 modules) is **proved-arithmetic-rich, framework-poor**: zero sorries
  corpus-wide, ~12.7k `#assert_axioms` pins, mutation-canary CI, keystone/load-bearing linters
  (`Verify/KeystoneLint.lean`) — hygiene tooling strictly ahead of both. Proved FRI arithmetic at
  deployed BabyBear params; a proved QROM/O2H layer (`Crypto/OneWayToHiding.lean:212`) that VCVio
  entirely lacks. But: **no protocol/IOP abstraction anywhere** (~230 bespoke Bool/Prop
  verifiers), **three parallel adversary notions** that never meet (`RomEff` on the `RomOracle`
  free monad; `FloorGames.Adversary`/`QBAdversary` on the `winProb` counting measure; the quantum
  unitary `Adversary`), **five disjoint Merkle formalizations**, coding math split three ways,
  and no dependency-graph/anti-drift tooling for the prose ledgers.

So: from VCVio we take *framework patterns onto our own substrate*; from ArkLib we take *module
organization, statement shapes, and methodology*; from neither do we take proofs we already have
or a dependency we can't cohabit with.

---

## 1. The ideas, per bucket

Each: (a) what it is + why it's good, (b) how it maps onto our stack, (c) port / depend /
be-inspired-by, (d) effort (S ≈ one session, M ≈ a few sessions, L ≈ a campaign), (e) priority.

### Bucket A — the oracle/computation framework

#### A1. One Eff: unify the three adversary worlds on an extended `RomOracle` (the FloorGames merge)

**(a)** VCVio's deepest design win is that *every* resource-tracked object — random oracles,
logging, counting, cost, caching, seeding — is one free monad (`OracleComp` over an
`OracleSpec ι := ι → Type` family, `OracleComp/OracleSpec.lean:25`) plus a lattice of handler
transformers (`so.withX : QueryImpl spec (T σ m)`, `QueryTracking/CountingOracle.lean:40` etc.).
One adversary type serves every game; one cost semantics serves every bound.

**(b)** We have three worlds that never meet (survey-confirmed: zero references to
`RomEff`/`OracleComp` in any Quant/QROM file): (i) `Crypto/RomOracle.lean:47`'s `OracleComp D R A`
+ `RomEff` (`Crypto/RomQueryFloor.lean:442`); (ii) `Crypto/FloorGames.lean:129`'s unrestricted
`Adversary` over `winProb`, with the missing Eff cost model *named as its own §8 residual*
(`FloorGames.lean:750`) and the collapse theorem `hard_top_iff_solvableFrac_negl` (`:241`)
proving why it's mandatory; (iii) the quantum `OneWayToHiding.Adversary`
(`Crypto/OneWayToHiding.lean:67`). Plus `ConcreteSecurity.StepBound.PPT` (`:221`) — a cost model
attached to nothing. The move: generalize `RomOracle.OracleComp` from single-oracle `D R` to a
small indexed spec (two or three oracles is all the FRI/hash work needs), adopt the
handler-transformer discipline, and make `FloorGames.Hard G Eff`'s `Eff` *be* "factors through a
query-bounded `OracleComp`" — so `RomEff`, `QBAdversary`, and (later, via the QROM query model)
the unitary adversary become instantiations of one parameter. FloorGames is a week old with
5 adopters; extending it now is cheap, building beside it later is a fourth world.

**(c)** Port the *pattern* onto our tree. Not a dependency (§4). **(d)** M–L, staged: spec
generalization first (S), handler transformers as needed by B1's stages, FloorGames `Eff`
instantiation last. **(e)** **P1, very high value** — this is the tree's own named residual, and
every subsequent crypto campaign stops choosing among three adversary notions.

#### A2. `QueryLog` + `withLogging` — the straight-line extractor's substrate

**(a)** VCVio's `QueryLog` (`QueryTracking/Structures.lean:293`, a list of dependent pairs) with
`withLogging` (a `WriterT` handler transformer, `QueryTracking/LoggingOracle.lean`) is what makes
straight-line extraction *mechanical*: the extractor reads the adversary's committed data out of
its own query log (VCVio's Fischlin `knowledgeSoundness`, ArkLib's `Extractor.Straightline` at
`OracleReduction/Security/Basic.lean:218`, both consume exactly this). Also the CMA pattern:
a signing oracle IS `QueryImpl.withLogging` and forgery-freshness is read off the log
(`CryptoFoundations/SignatureAlg.lean:58`).

**(b)** `Crypto/RomOracle.lean` has the counting core (`RomCounting.condProb_fresh_eq`,
`Crypto/RomCounting.lean:250`) but **no log/erasure interface** —
[`FRI-EXTRACTION-FLOOR-DESIGN.md`](./FRI-EXTRACTION-FLOOR-DESIGN.md) §4.5 names this as the one
modest addition its stages 3–5 need (the BCS-style extractor reads the committed word out of the
Merkle-path queries). Add `QueryLog` + a logging evaluator + agreement lemmas to `RomOracle`.

**(c)** Port (a `def` + an evaluator + ~3 lemmas, imitating VCVio's shapes). **(d)** S–M.
**(e)** **P0** — it is on the critical path of the flagship (B1) and is the seed of A1's
handler-transformer discipline.

#### A3. `IsQueryBoundP`-style targeted budgets + cost-Markov

**(a)** VCVio's `IsQueryBound oa budget canQuery cost` (`QueryTracking/QueryBound.lean:55`) is a
*generalized budget predicate* — budget type, per-index admissibility, budget-update function —
definitionally `PFunctor.FreeM.IsRollBound` (structural, per-path), with `IsPerIndexQueryBound`/
`IsTotalQueryBound` as specializations, proved bridges to the unit cost model
(`CostModel.lean:309–367`), and Markov (`probEvent_cost_gt_le_expectedCost_div`, `:214`).
Birthday bounds live on top (`QueryTracking/Birthday.lean:209`).

**(b)** Our `QueryBounded` (`Crypto/RomOracle.lean:68`) is total-only and ~2× looser. In `εFri`
we want permutation queries counted separately from grinding queries; per-index/predicate
targeting states that cleanly, and Markov is the lever from query-count to probability. Lands in
`RomOracle`/`RomQueryFloor` beside `birthday_cond` (`Crypto/RomQueryFloor.lean:231`).

**(c)** Port (this was the comparison doc's #2; the survey upgrades it: imitate the
*generalized-budget* formulation, not just the predicate variant, since it subsumes per-index and
total for free). **(d)** S. **(e)** **P1** — sharpens B1's `εGrind`/`εMerkle` addends; not
blocking stage 1.

### Bucket B — statement-shape patterns

#### B1. The flagship: `friLdtExtractV3_rom` — query-bounded straight-line extraction at the FRI apex

**(a)+(b)+(c)+(d)** Fully specced in [`FRI-EXTRACTION-FLOOR-DESIGN.md`](./FRI-EXTRACTION-FLOOR-DESIGN.md)
(stages 0–5, falsifiers included): re-state the assumed `FriLdtExtractV3`
(`metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean:131`) as `Pr[accepts ∧ ¬ExtractBundle] ≤ εFri(Q, params)`
over a `QueryBounded` adversary on `RomOracle`, with the twelve conjuncts preserved verbatim and
the ledger's proved density columns becoming the `εQuery` addend. ArkLib's
`knowledgeSoundness` measured-event (`Security/Basic.lean:289`) and VCVio's Fischlin
`knowledgeSoundness` (`Fischlin/KnowledgeSoundness.lean:2522`) are the templates. Port-pattern,
no dependency. This doc adds only the broad-survey confirmation: **nothing in either library
supersedes that design** — ArkLib's own FRI soundness (Claims 8.1–8.3,
`ProofSystem/BatchedFri/Security.lean:256,625,749`) is still `sorry`, and VCVio's proved
extraction precedents are exactly the shape the design already imitates.

**(e)** **P0 — do first.** Stage 1 (the `verifyAlgoO` faithfulness bridge) is the smallest
first theorem and needs only A2 alongside it.

#### B2. Collision-as-data (extraction-as-data) for the Merkle legs — and as the house pattern

**(a)** VCVio's `MerkleTree/Inductive/Binding.lean` proves binding with **no adversary, no
probability, nothing to falsify**: `findCollision` (`:73`) *computes* the colliding pair from two
openings; `getPutativeRootWithHash_binding_collision` (`:188`) is fully proved. The probability
enters only later, when a birthday bound prices "the log ever contains a collision". Same pattern
in Σ-form: `SigmaProtocol.SpeciallySoundAt` (`CryptoFoundations/SigmaProtocol.lean:81`).

**(b)** Two of `FriLdtExtractV3`'s conjuncts are `merkleRecomputeZ` recomputes under an *assumed*
`Poseidon2SpongeCR` (`metatheory/Dregg2/Circuit/Poseidon2Binding.lean:178`) — extraction-design stage 3 ports
`findCollisionZ` + `birthday_cond` there. The broad survey adds the *pattern* mandate: this is
the shape to prefer **house-wide** wherever a binding floor is currently a bare CR `Prop` —
the five Merkle formalizations (D1) all meet at that one hypothesis, so one ported
collision-finder shape serves all of them, and the `*Regrounded` sweep (11 pairs, e.g.
`Crypto/IdentityCommitmentRegrounded.lean:26`) already established the tree's re-basing idiom for
exactly this move.

**(c)** Port. **(d)** M (stage-3 scope; house-wide adoption is then per-consumer S each,
opportunistic). **(e)** **P1.**

#### B3. Which of our statements should NOT change shape (the honest counterpart)

**(a)+(b)** Adversary-game shapes are for statements whose truth *depends on a resource bound*.
Most of our proved corpus is not that: the ∀-over-words refinement idiom
(`metatheory/Dregg2/Circuit/RotatedKernelRefinement.lean:430`), the counting bounds
(`metatheory/Dregg2/Circuit/FriQuerySoundness.lean:132`), the Polis demonic-controller invariants
(`Polis…sandbox_governed_safe`), the noninterference results — these are *correctly*
deterministic/universal and should stay. The PQ hybrid keystone already has both registers
(Prop-floor `HybridCombiner.lean:232` + quantitative `HybridThresholdQuant.lean:140`). The
adopt-the-shape list is short and named: the FRI apex (B1), the Merkle binding legs (B2), and —
when A1 lands — restating the `FloorGames` instantiations' `Eff` uniformly. Nothing else
currently qualifies. **(c)** N/A — this is a scope fence. **(d)(e)** Free; it's what keeps
A/B-bucket work from metastasizing into a tree-wide rewrite.

### Bucket C — proof-system abstractions

#### C1. ArkLib's `OracleReduction` frame (ProtocolSpec / seqCompose / Lens / Component gadgets) — be-inspired-by, deferred with a named trigger

**(a)** The frame is genuinely good: round-indexed `ProtocolSpec` (`OracleReduction/ProtocolSpec/Basic.lean:28`)
makes message-vs-challenge a type distinction; `OracleVerifier` (`Basic.lean:271`) confines the
verifier to `OracleInterface` queries with an embedding constraint (can forward oracles, never
fabricate); the `Lens` algebra for running sub-protocols inside larger statements is **proved**
(`LiftContext/Lens.lean`, 686L, 0 sorries); `Component/` is a library of tiny 0/1-round gadgets
(SendClaim, CheckClaim, RandomQuery…) from which Spartan is assembled; sumcheck's headline
theorems are one-line applications of generic `seqCompose_*` lemmas
(`ProofSystem/Sumcheck/Spec/General.lean:208,218`).

**(b)** But the honest fit-check says: not now. (i) The security glue the frame's value rests on
— binary `Append` preservation, lens transport, FS — is where ArkLib's `sorry`s are
*concentrated*; "fill their frame" means proving their hardest open theorems on a substrate we
don't otherwise carry. (ii) Our deployed verifier is **non-interactive** — FS is already applied;
`verifyAlgo` has no rounds; the extraction design explicitly needs *no* interaction machinery
("the adversary is just a query-bounded proof-finder", FRI-EXTRACTION-FLOOR-DESIGN §4.2). (iii)
Our ~230 verifiers are refinement gates over one kernel, not composed IOPs — the emit→refine
backbone (`Circuit/Emit/`, 177 files) is a different (and working) composition story.
**Trigger to revisit:** the first time we build a genuinely *interactive multi-round* protocol
(a native sumcheck lane, an IVC folding argument stated as a reduction) — then adopt the
`ProtocolSpec`/lens *shape* for that lane only, with our proved arithmetic filling their
statement forms.

**(c)** Be-inspired-by; adopt nothing now except the vocabulary. **(d)** L if ever. **(e)** **P3 /
deferred.**

### Bucket D — reusable math

#### D1. One shared Merkle library (consolidate five formalizations, VCVio's indexed-tree shape)

**(a)** VCVio's preferred Merkle development (`MerkleTree/Inductive/` over skeleton-indexed
binary trees from `ToMathlib/Data/IndexedBinaryTree`) handles non-perfect trees, keeps
completeness/binding/extractability/uniqueness/query-bound as separate files, and proves the lot.

**(b)** We have **five** disjoint Merkle formalizations meeting only at `Poseidon2SpongeCR`:
`Crypto/Merkle.lean`, `metatheory/Dregg2/Circuit/IndexedMerkleTree.lean`, `metatheory/Dregg2/Circuit/CapMerkleGeneric.lean` (+ its
Emit family), `metatheory/Dregg2/Lightclient/MMR.lean`, `Crypto/HashSigMerkle.lean` — a real 3–5× duplication.
The consolidation: one shared module (natural home `Dregg2/Crypto/MerkleCore.lean` or a new
`Dregg2/Data/`, see D2) in the indexed-tree shape, carrying the B2 collision-finder once, with
**adapters** proved from each existing formalization — never a flag-day rewrite, because the
Emit-family files are byte-pinned by descriptor emission and must not churn.

**(c)** Port the shape; migrate opportunistically (new work uses the shared module; old modules
gain adapter lemmas and retire only when a campaign already touches them). **(d)** M for
core+first adapter; L to full convergence (unforced). **(e)** **P2** — real value, no deadline.

#### D2. A `Data/` layer: consolidate coding/polynomial math + adopt ArkLib's proved statements as carrier targets

**(a)** ArkLib's `Data/` vs `ProofSystem/` split — "anything a mathematician could state without
mentioning provers" lives in `Data/` — is the discipline that made their coding theory their
crown jewel (`Data/CodingTheory/`: ReedSolomon 769L, JohnsonBound 0-sorry, Guruswami–Sudan
2×~1000L 0-sorry, BCIKS20 `AffineSpaces.lean` 2326L 0-sorry, DG25 `MainResults.lean` 1446L).

**(b)** Ours is split three ways with a dangling asset: Circuit RS/low-degree (deployment-
instantiated), Crypto NTT/cyclotomic, and `ForMathlib/GuruswamiSudan.lean` — a list-decoding
bound **not wired into** the FRI Johnson files that want it. Two concrete moves: (i) wire
`ForMathlib/GuruswamiSudan` into `Circuit/FriLdtJohnson*` where it belongs (S, immediate); (ii)
grow a `Dregg2/Data/`-style shared layer for *new* general math, keeping the ArkLib rule that
deployment-instantiated facts stay with their deployment. Additionally, per the comparison doc's
#4 (unchanged by this survey): take ArkLib's proved **DG25 correlated-agreement statements**
(`Data/CodingTheory/ProximityGap/DG25/ReedSolomon.lean:38,121,176`) as the *statement templates*
our `WrapCorrelatedAgreementSharp` carrier reduces to at B1 stage 4 — reference their form, never
import their tree (their Johnson-radius/list-decoding corner still carries ~19 sorries; their
proved regime is unique-decoding, which we already have unconditionally).

**(c)** Be-inspired-by (the split + the statement templates); port nothing. **(d)** S for the
GuruswamiSudan wiring; M for the layer convention. **(e)** **P2** (the wiring piece is S and
worth doing early).

### Bucket E — methodology

#### E1. `checkdecls`-style decl-manifest CI: anti-drift teeth for our prose ledgers

**(a)** ArkLib's blueprint pipeline keeps prose and code from drifting *mechanically*: every
LaTeX node carries `\lean{Decl.Name}` macros; a generated `blueprint/lean_decls` manifest (200
names) is checked by the pinned `checkdecls` lake dependency in CI (`lakefile.toml`,
`.github/workflows/docs.yml`) — a renamed or deleted declaration fails the PR.

**(b)** This is the cheapest high-fit adoption in either library. Our prose layer is large and
load-bearing — `metatheory/docs/KEYSTONE-LEDGER.md` (110 apex pins), `metatheory/docs/NAVIGATION.md` (which
carries an honest line-drift warning *because* nothing checks it), `docs/reference/*.md` — and
the docs-excellence campaign just re-verified 455 files and found 166 stale. We already have the
harder half in-tree (`#assert_axioms` checks *axioms* of a decl; `Claims.lean` re-elaborates
keystones): what's missing is only "the decl names cited in prose still exist". Concretely: a
`decls.txt` manifest per ledger doc (or extracted from a `\lean{}`-like backtick convention) +
either the upstream `checkdecls` package or a ~40-line in-house `#check_ledger_decls` command in
`Verify/` (we already own richer meta-code in `KeystoneLint`), wired as a fast CI job.

**(c)** Port (in-house command preferred — zero new deps, and it can also check our `file:line`
cites' decl names). **(d)** S. **(e)** **P1 — best value/effort in the whole survey.** Full
leanblueprint (LaTeX graph, `\uses{}`, web output) is a separate call: see don't-bother.

#### E2. Light conventions bundle: `To*`-staging discipline, `Sorries.lean` quarantine, citation discipline, `docs/agents/` guides

**(a)+(b)** Four cheap conventions, each with an existing hook in our tree:
- **Upstream staging with a finished-only rule** (ArkLib `To{Mathlib,VCVio}/`, sorry-free by
  rule): we have `ForMathlib/` (5 genuinely general files) — adopt the *rule* (staged =
  upstream-ready, and actually file the PRs; we're contributing to ArkLib anyway per the standing
  note, so a `ForArkLib/` staging dir for e.g. our Johnson-radius arithmetic is the natural
  reciprocal move).
- **Named-debt quarantine** (`BerlekampWelch/Sorries.lean` — axiomatized steps quarantined in one
  named file): we have zero sorries, but our analogue is *named carrier Props*; the convention
  maps to keeping every carrier in a greppable, single-file-per-floor home rather than inline —
  largely already our practice (`FloorGames`, `Poseidon2Binding`); adopt as a stated rule.
- **Citation discipline** (every docstring paper-cite has a BibTeX entry + References section,
  CONTRIBUTING.md:212): our headline files cite BCIKS20/DG25/BCS16 in prose; one
  `metatheory/docs/references.bib` + the convention costs nearly nothing and pays at paper time.
- **`docs/agents/` topic guides** (VCVio ships 12 agent-oriented guides: notation, oracle-comp,
  query-tracking…): we are an agent-heavy shop; per-subsystem guides distilled from NAVIGATION.md
  (one for the RomOracle/FloorGames world, one for emit→refine, one for the apex chain) directly
  cut lane-orientation cost.

**(c)** Adopt as conventions (no code). **(d)** S each. **(e)** **P2.**

---

## 2. Do these first (ranked)

| # | Idea | What lands | Effort | Why first |
|---|------|-----------|--------|-----------|
| 1 | **B1** stage 1 (+A2 alongside) | `verifyAlgoO` + faithfulness lemma; `QueryLog`+logging on `RomOracle` | S–M | The flagship's smallest first theorem; proves the re-basing is conservative; A2 is its substrate and A1's seed |
| 2 | **E1** decl-manifest check | `#check_ledger_decls` + manifests for KEYSTONE-LEDGER/NAVIGATION | S | Best value/effort found; guards the docs campaign's 455-file re-verification from re-rotting |
| 3 | **A3** targeted query bounds + Markov | generalized-budget `QueryBounded` variants in `RomOracle` | S | Small, sharpens every ε downstream of B1 |
| 4 | **B2** `findCollisionZ` | collision-as-data for the `merkleRecomputeZ` legs + `birthday_cond` pricing | M | Two conjuncts of the apex bundle move to theorem-except-ε; establishes the house binding pattern |
| 5 | **A1** One-Eff merge (staged) | multi-oracle `RomOracle` spec; `FloorGames.Eff` = query-bounded oracle adversaries | M–L | The tree's own named residual (`FloorGames.lean:750`); do after A2/A3 so the handler discipline is already in place |
| 6 | **D2(i)** GuruswamiSudan wiring | `ForMathlib/GuruswamiSudan` consumed by `FriLdtJohnson*` | S | A finished asset lying unwired |
| 7 | **D1** shared Merkle core | indexed-tree module + first adapter | M | Starts the 5→1 consolidation without touching byte-pinned emit files |
| 8 | **E2** conventions bundle | staging rule, references.bib, agent guides | S | Cheap, compounding |

(B1 stages 2–5 then proceed per FRI-EXTRACTION-FLOOR-DESIGN's own ordering, consuming A3/B2/A1
as they land; D2's statement-template adoption binds at its stage 4.)

## 3. Don't bother / we're already ahead

- **ArkLib's protocol soundness proofs** — there are none to adopt (FRI Claims 8.1–8.3,
  sumcheck single-round, WHIR/STIR/FS/BCS: all `sorry`). Our per-fold density, Johnson list
  bound, query counting, arity-8 fiber are proved and axiom-clean at deployed params. Strictly
  ahead; nothing to import.
- **ArkLib's mainline (unbounded) soundness quantifier** — the KZG-vacuity disease
  (`OracleReduction/Security/Basic.lean:242` bounds no queries). Our own
  `hard_top_iff_solvableFrac_negl` proves the collapse; adopt only bounded shapes.
- **Vendoring VCVio** (or ArkLib) — dep-cohabitation fails concretely today: they pin
  `leanprover/lean4:v4.31.0` while we pin `v4.30.0` with mathlib by-rev; VCVio's ProgramLogic
  sits on **loom2**, which vendors an *unmerged Lean core PR* (leanprover/lean4#12965) under
  `Std.Do'`; `OracleComp` is definitionally built on **PolyFun**'s `FreeM` (which itself uses the
  new `module`/`public import` system). That is three unstable pins into our TCB for machinery we
  have a Mathlib-only clone of. Standing verdict unchanged (and it's an ember-call regardless);
  re-examine only if B1 stage 4 produces evidence of needing `SPMF`/wp semantics we can't cheaply
  add — the identified bridge points (`Proof/Synchronizer.lean:290`, `ModelBridge` §C) show PMF
  adoption would collide with nothing *if* that day comes.
- **`SPMF`/PMF probability semantics now** — our `winProb` counting measure is deliberate,
  adequate for every current statement, and lighter. Keep the `RomOracle`-counting vs
  finite-event split; revisit with stage-4 evidence only.
- **Full leanblueprint** (LaTeX dependency graph, `\uses{}`, web build) — the *teeth* (E1) are
  worth porting; the LaTeX apparatus is not: our proof corpus is not paper-driven, our de-facto
  blueprint (annotated `Dregg2.lean` + NAVIGATION.md + KEYSTONE-LEDGER) already carries more
  per-node information (axiom pins, teeth, tiers) than `leanok` flags do.
- **The full `ProtocolSpec` round-indexed machinery near-term** — C1's trigger hasn't fired; our
  deployed protocol is non-interactive and our composition story (emit→refine + fold) is a
  different, working architecture.
- **CompPoly's two-representation strategy** — solved differently and adequately here: the Lean
  kernel is the deployed executor via FFI (`Exec/FFI.lean`) and descriptors are emitted/pinned
  (`descriptor-drift` CI gate); we don't need a computable-polynomial mirror layer.
- **Axiom/sorry-hygiene tooling from either library** — ours (mutation canary, keystone lint with
  mandatory non-vacuity witnesses + hostile-instance refutations, `@[linter_calibration]`
  negative fixtures, 12.7k pins) is ahead of both; if anything this is our best candidate
  *export* to ArkLib alongside the coding-theory arithmetic (E2's staging dir).
- **Quantum/QROM machinery** — nothing to adopt: VCVio has no quantum layer; our proved
  `o2h_bound` (`Crypto/OneWayToHiding.lean:212`) has no counterpart in either library.

## 4. Bottom line

Everything worth taking fits one sentence: **VCVio's handler-transformer framework pattern and
query-log/budget/collision-as-data statement shapes, ported onto our existing `RomOracle`+
`FloorGames` substrate (A1–A3, B1–B2); ArkLib's module-hygiene and anti-drift methodology
(E1–E2, D2's Data-split); and neither library as a dependency.** The FRI apex re-basing
(B1, already fully specced) remains the flagship; the broad survey's genuinely new finds are the
One-Eff merge target (A1 — the tree already named it as a residual), the decl-manifest CI teeth
(E1 — smallest effort, largest hygiene payoff), and the Merkle/coding consolidations (D1/D2 —
real 3–5× duplication with safe, adapter-based paths). Where we are ahead — proved FRI
arithmetic, axiom-hygiene tooling, the QROM layer — the flow should eventually run the other
way, via an upstream staging directory in ArkLib's own `To*` idiom.
