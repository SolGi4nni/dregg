# PLAN — connecting the proven FRI proximity theorem to the deployed apex

**2026-07-27, rev. 2.** Attack on residual **(b)** of `docs/OPENING-SOUNDNESS-DECONFLATED.md`: turn
the deployed FRI verifier's *acceptance* into an implication of the **BCIKS20 proximity bound**, so
the ledger becomes a theorem with a real adversary object. Every file:line below was verified at HEAD
by reading the declaration, not by grep. **Read + plan; nothing deployed changes in this document.**

> **rev. 2 supersedes rev. 1 on its own headline.** Rev. 1 nominated "Slice 0 — the `FriLdtExtractV3`
> OOD cutover" as the recommended first commit. **That cutover already landed on 2026-07-25** and
> rev. 1 was reading a stale memory note. The corrected verdict is below; the residual it leaves is a
> *different and sharper* one, and it is one conjunct over.

---

## VERDICT (the four questions, answered)

1. **Is the proximity theorem connectable to the deployed verifier?**
   **The mathematics is done and the composition is done; the connector is not — and it cannot be
   connected in the shape it is currently written.** The keystone is a proved statistical theorem
   (`polishchuk_spielman`, `metatheory/Dregg2/ForMathlib/PolishchukSpielman.lean:739`), the L0–L6
   correlated-agreement ladder is landed, an adversary object exists
   (`metatheory/Dregg2/Circuit/FriAdversaryObject.lean`), and the four-leg union bound is proved
   (`FriVerifierCompose.friLdtExtractV3_rom_of_legs:378`). Three of its four legs are discharged.
   The fourth (`hQuery`) reduces — by a *proved* implication, `WordProofBridgeDeployed.
   wordProofBridge_of_embedding:89` — to the carrier `DeployedTraceExtract.DeployedFriEmbedding:238`.
   **That carrier is not merely unproven; as typed it is the full-cover idealization the tree itself
   refutes** (see §3). So the answer is **"retype, then connect"**, not "connect", and not "reprove
   the proximity math".

2. **Is the apex-vacuity a deeper break, or a missing connection?**
   **Neither, now: it is a *strict improvement that stopped one conjunct short*.** The OOD-singleton
   wound is **closed** — the vacuous assembler was deleted and relocated over a corrected bundle
   (§2). But the tree states the residual as a theorem, not a note:
   `ApexOodLaneRepair.friLdtExtractV3Cons_false_of_accepting_run_without_tableOpenings:801`, whose
   docstring is exact — *"The cutover therefore trades a premise empty EVERYWHERE for one whose
   emptiness is CONDITIONAL and UNDECIDED: a strict improvement, not a closure."* **No corrected
   bundle in this campaign has an exhibited model.** The apex is no longer provably vacuous; it is
   also not yet provably non-vacuous.

3. **What is the first provable slice?**
   **Force the deployed acceptance predicate to bind `proof.tableOpenings`** (§4, Slice A). It is
   small, it is the exact conjunct blocking every corrected bundle from having a model, and it is
   backed by a `decide` witness that the current predicate accepts a proof opening **no tables at
   all**. It also looks like a genuine verifier defect rather than a modeling artifact — flagged in
   §4 with the Rust check that decides which.

4. **Does ArkLib shortcut any of this?** **No.** See §6.

---

## 1. What is on disk and green — the substrate the connection composes

| piece | file:line | proves | status |
|---|---|---|---|
| proximity keystone | `ForMathlib/PolishchukSpielman.lean:739` `polishchuk_spielman` | bivariate BW → Polishchuk–Spielman divisibility (Kopparty 2025 §2.2 Cramér–Nardi-fixed form) | proved, `#assert_axioms` clean, `_fires` at `:931` |
| CA ladder L0–L6 | `Circuit/CorrelatedAgreement/{Scaffolding,BerlekampWelch,Interpolation,Collinearity,Theorems,Interface,RlcDischarge,DecimLiftDischarge}.lean` | UD-regime correlated agreement for RS codes (BCIKS20 Thm 4.1) | landed, sorry-free |
| adversary object | `metatheory/Dregg2/Circuit/FriAdversaryObject.lean:85,107,115,133,278` | `Strategy`, `fsRun` (FS as an `OracleComp`), `fsRun_queryBounded`, `fsRun_eval`, `chain_far_strategy_of_farCover` at an **arbitrary adaptive** strategy | landed |
| tower far-survival | `CorrelatedAgreement/Interface.lean:881` `ud_tower_far_survival` (`:837` `_strategy`) | `winProb bad ≤ rounds·(m−1)(r₁+1)/|F|`; `deployed_code_eq:516` pins the code to `friSetupDeployed.C` | landed — **but see the `hlift` hypothesis, §5** |
| four-leg union bound | `metatheory/Dregg2/Circuit/FriVerifierCompose.lean:378` `friLdtExtractV3_rom_of_legs` | `condProb C accepts_and_fails ≤ epsFri …` from the four leg bounds | landed |
| word↔proof bridge | `metatheory/Dregg2/Circuit/WordProofBridgeDeployed.lean:89` `wordProofBridge_of_embedding` | `DeployedFriEmbedding → WordProofBridge` over the **real** deployed `Int`-column encoding (`FriColumnDecode.decodeColumn`) | landed — closes the type-shape gap `FriVerifierCompose` §3 flagged |
| query leg over the real sampler | `metatheory/Dregg2/Circuit/FriVerifierComposeDefected.lean:169` `epsFri_compose_deployed_defected` | the query leg with the **sampling defect** composed in, deployed leg a theorem | landed |
| sampling defect itself | `FriVerifierCompose.lean:359` `babybear_sampleBits_not_balanced` | deployed `sampleBits` buckets **cannot** be balanced at any `logN ≥ 1` (BabyBear order is odd) | proved |
| L4 verifier-syntax half | `metatheory/Dregg2/Circuit/DeployedTraceExtract.lean:309` `verifyAlgo_concreteFri_opened_positions` | accepting run opens exactly `numQueries` positions, each index transcript-bound, each passing `friQueryCheck` | **proved** |
| L6 dichotomy | `metatheory/Dregg2/Circuit/DeployedTraceExtract.lean:551` `accept_close_or_paid` | per run: all folds `d`-close (⇒ oracle `n²d`-close by the keystone) **or** some fold is `d`-far and its sampled-agreement event has mass `≤ (1−δ)^k` | **proved, generic** |
| the refutation that disciplines all of it | `DeployedTraceExtract.lean:686` `sampled_pass_not_membership` | "sampled pass ⟹ membership" is **FALSE** at a witness | proved |
| V3 OOD cutover | `metatheory/Dregg2/Circuit/FriLdtExtractDeployed.lean:323,641`; `metatheory/Dregg2/Circuit/ApexOodLaneRepair.lean` | `FriLdtExtractV3Cons`, `algoStarkSound_transferV3_cons` — the transport `friLdtExtractV3_imp_cons` that used to sit at `:352` was **DELETED 2026-07-28** (that line is now its deletion notice): the corrected bundle carries the per-run `¬ OpeningColl` residual the landed bundle never had, so the implication is no longer provable | **landed 2026-07-25** |

---

## 2. The apex-vacuity: what is closed, and the theorem that says what is not

**Closed.** `AlgoStarkSoundTransferV3.algoStarkSound_transferV3` — the assembler whose premise
`FriLdtExtractV3` forced `CircuitSoundness.verifyBatch` to reject *every* triple — was **deleted**,
not corrected in place, and relocated to `FriLdtExtractDeployed.algoStarkSound_transferV3_cons:641`
over the corrected bundle `FriLdtExtractV3Cons:323`. The deletion is recorded at
`AlgoStarkSoundTransferV3.lean:256-276` and the receipt for what it removed is
`ApexOodLaneRepair.deleted_transferV3_assembler_premises_were_empty:779`. The old bundle is
deliberately **retained** as the *subject* of the vacuity theorems that prove it empty.

**Honest character of the repair.** The corrected bundle adds **exactly zero strength**:
`ApexOodLaneRepair.friLdtExtractV3Cons_iff_noOodShape:706` proves it equivalent to itself with the
OOD conjunct deleted, because acceptance already supplies the cons shape
(`acceptsFull_gives_cons_shape`; `batchTablesCheck` returns `false` on an empty `oodPoint`,
`FriVerifier.lean:805-808`). The sharper form
`algoStarkSound_transferV3_cons_noOodShape:738` mentions no OOD conjunct at all. So the repair
de-vacuified by **removing a false conjunct**, which is the correct move — the conjunct was the bug.

**NOT closed, and stated as a theorem.**
`ApexOodLaneRepair.friLdtExtractV3Cons_false_of_accepting_run_without_tableOpenings:801`:

> `FriLdtExtractV3Cons` retains the conjunct `topen ∈ (view pi π).1.tableOpenings`, and acceptance
> does **not** supply it. `FriLdtExtractDeployed.deployed_accepting_pole_has_no_tableOpenings:902`
> exhibits a `decide`-backed run that the **apex-facing deployed predicate**
> `verifyAlgoUnifiedFaithfulExt` ACCEPTS with `proof.tableOpenings = []`.

Every corrected bundle of the campaign retains that conjunct — `FriLdtExtractV3Cons`,
`FriLdtExtractV3Faithful`, `ApexOodLaneRepair.FriLdtExtractCons`, `FriFsDecodedOodRepair`'s and
`OodSingletonRepair`'s `…Cons` forms (`FriLdtExtractDeployed.lean:894-901`). **"The same disease, one
conjunct over."** The exhibited pole is `Nat`-typed at concrete arguments while the deployed
instantiation is at `opaque` `cfg*` arguments, so what is refuted is the *schema*; the deployed
instance is **undecided in both directions**.

This is the project's own `feedback-prove-the-floor-false` bar, unmet: a floor must be **satisfiable**
and **refutable** but not provable. The corrected bundle is now demonstrably **refutable**
(`:801`). It has never been shown **satisfiable**.

---

## 3. Why `DeployedFriEmbedding` cannot be "connected" as typed — retype first

`FriVerifierCompose` §3 names blocker (a) as the word↔proof bridge and says supplying it is supplying
`DeployedFriEmbedding`. `WordProofBridgeDeployed:89` has since made that sentence a theorem. So the
whole of residual (b) now sits in **one carrier**, which is real progress — but the carrier's
`accept_folds` field (`DeployedTraceExtract.lean:251-254`) concludes

```
∀ i, Fold friSetupK8.geom (chal pi π i) (oracle pi π) ∈ friSetupK8.C'
```

for **every** fold on **every** accepting run — deterministic, universal membership. The tree states
plainly what is wrong with that (`DeployedTraceExtract.lean:263-270`):

> *"The deployed verifier does not check that: `concreteFriChecks.foldConsistent` spot-checks fold
> consistency at the `params.numQueries` transcript-sampled positions ONLY … So the §2 bar is the
> FULL-COVER idealization, **unprovable-as-typed at deployed sampling**."*

and it is not a worry, it is **refuted**: `sampled_pass_not_membership:686` exhibits the failure of
"sampled pass ⟹ membership" without cover. `deployedFriEmbedding_of_sampled_cover` shows the §2 bar
is exactly recoverable *when the sample covers the folded domain* — which deployed sampling does not
do.

**Therefore the correct target is already in the tree**: `DeployedFriSampledEmbedding`
(`DeployedTraceExtract.lean:390+`), which replaces `accept_folds` with `accept_folds_sampled`
(per-column agreement between the true fold and the committed next-layer word **at the sampled
positions**) and retypes the decode input to a **batched multi-column** `MatrixOracle` — matching
what plonky3 actually commits (one LDE matrix per commitment; a query opens the whole row through
one Merkle path; `p3_commit::BatchOpening.opened_values`, `p3-commit/src/mmcs.rs:163-169` in Plonky3
at rev `82cfad7` — an upstream path, not this repo's `commit/` crate).

**This is the answer to "connectable or not".** Connectable — but only to the *sampled* bar. Anyone
who tries to discharge `DeployedFriEmbedding` as written is trying to prove something the tree has
already refuted, and any bundle that assumes it is assuming a statement false at deployed sampling.

---

## 4. The first provable slice — ordered by leverage, not by depth

### Slice A (recommended first commit) — **bind `tableOpenings` in the deployed acceptance predicate**

*Small. Not new mathematics. Unblocks the satisfiability of every corrected bundle at once.*

**The defect.** `FriVerifier.batchTablesCheck:803` is

```lean
match proof.oodPoint with
| ood :: _ => proof.tableOpenings.all (tableOk A ood)
            && decide (busSum A proof.tableOpenings = A.zero)
| []       => false
```

`List.all` on `[]` is `true` and `busSum A [] = A.zero`, so **`tableOpenings = []` passes
vacuously**. The predicate carefully rejects an empty `oodPoint` and does not reject an empty set of
opened tables. The apex-facing `verifyAlgoUnifiedFaithfulExt` does require
`decide (os ≠ [])` — but on `view.singleAirOpenings` (`ExtFieldChallenge.lean:736`), a **different
list**, with nothing in the predicate tying it to `proof.tableOpenings`. That unlinked seam is
precisely what `deployed_accepting_pole_has_no_tableOpenings:902` walks through.

**The slice.** Add the missing conjunct — `decide (proof.tableOpenings ≠ [])` in `batchTablesCheck`,
and/or a conjunct linking `view.singleAirOpenings` to `proof.tableOpenings` in
`verifyAlgoUnifiedFaithfulExt`. Then:

1. `deployed_accepting_pole_has_no_tableOpenings` must **flip** — the pole no longer accepts. It is a
   `decide` witness, so this is mechanical, and its flipping is the slice's own non-vacuity canary.
2. Re-establish `deployed_accepting_pole_nonempty:854` at a pole that **does** open a table (extend
   `poleProof` with one `TableOpening` satisfying `tableOk`; the quotient identity at a single table
   is `decide`-able at the existing concrete arguments).
3. That pole then discharges the standing obligation: exhibit a model of `FriLdtExtractV3Cons`, i.e.
   move `PremiseInhabitability` §7 row E1's successor from **UNDECIDED** to **INHABITED**, and
   `friLdtExtractV3Cons_false_of_accepting_run_without_tableOpenings` from "fires at the schema" to
   "cannot fire at deployed arguments".

**Acceptance bar (green-or-bust, per `feedback-a-documented-wound-is-not-a-detected-one`):** the slice
is only real if the *old* pole goes red. A verifier tightening that leaves every existing `decide`
witness green has not tightened anything.

**⚑ REQUIRED CHECK BEFORE LANDING — is this a live verifier hole or only a modeling one?**
`batchTablesCheck` is the Lean image of `verify_all_tables`, which is **not vendored in this repo**
(`grep -rn "fn verify_all_tables"` returns nothing; the callers are
`circuit-prove/src/plonky3_recursion_impl.rs:815`, `apex_shrink.rs:313`, `gpu_backend.rs:4650,5261`).
Read the upstream `p3_batch_stark` definition and determine whether a proof with **zero tables** is
accepted there too. If yes, this is a **deployed verifier defect**, not a modeling artifact, and it
is greenfield-fixable per `CLAUDE.md` — say what re-emits. If no, the Lean model is *weaker than the
Rust* and the fix is to make the model faithful. **Do not state which it is until that file is read.**
This document does not claim the Rust is broken; it claims the *model* accepts zero-table proofs, and
that the question is open and cheap to settle.

### Slice B (the first genuinely-open *proximity* brick) — **the L4 Merkle log-decode identification**

*Contained. The half that is hard is named; the half that is verifier-syntax is already proved.*

`DeployedTraceExtract.lean:272-277` names it exactly: the verifier-syntax half is
`verifyAlgo_concreteFri_opened_positions:309` (**proved**), and the residual is

> `friQueryCheck = true` at the sampled index ⟺ the opened leaves agree with `Fold` on the
> `RomQueryLog`-decoded word (extraction-as-data, except-with-`εMerkle`).

That single lemma is what upgrades `accept_folds_sampled` from a carrier field to a theorem. It is
the right second slice because **everything downstream of it is already proved**: `accept_close_or_paid:551`
turns per-position sampled agreement into the close-or-paid dichotomy, and
`friLdtExtractV3_rom_of_legs:378` composes the paid branch into `epsFri`. It needs the
`RomQueryLog` / `FriVerifierMerkle.findCollisionZ` machinery and is genuinely multi-file — this is
the "1–3 week" brick, not a PoC.

### Slice C — **`DecimLift` at the deployed arity `m = 8`**

`ud_tower_far_survival:881` carries `hlift : DecimLift nn V m dec` as a hypothesis
(`Interface.lean:885`), and `fireLift:916` discharges it only at the toy `nn = fun _ => 4`, `m = 1`.
Until `m = 8` is discharged, the deployed tower far-survival fires at the toy instance, not the
deployed one. Self-contained; named in the `Interface` and `FriChainStepIdx` headers as *the* tower
residual.

### Slice D — **the honest L5 instance** (heaviest; do not attempt before A–C)

`PositiveRadiusTraceDecode` (`DeployedTraceExtract.lean:350`) must be exhibited at a realistic
multi-layer instance with a `≥ 2^22`-class domain. **It cannot be stubbed**:
`FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8` *proves* the size-16 toy
domain cannot exhibit a positive radius, and `friProximityK8_discharge0` is only the `d = 0` toy.
This is the heavy engineering block.

---

## 5. Ordered plan (reconciled with `docs/DESIGN-fri-adversary-object.md`'s L1–L7)

| rung | status at HEAD |
|---|---|
| **L1** sampler-defect query leg | **LANDED** (`FriVerifierComposeDefected`) — retire from the ladder |
| **L1a** link over the non-uniform sampler | **LANDED** (`DeployedProximitySoundnessSampler`) |
| **L2** round-chain far-survival | **LANDED** at the adversary object (`FriChainStepIdx.chain_far_survival`) and at the tower (`Interface.ud_tower_far_survival`) — **residual: `hlift` at `m = 8` = Slice C** |
| **L2a** word↔proof bridge type-shape | **LANDED** (`WordProofBridgeDeployed:89`) — new since rev. 1 |
| **L3** grinding re-accounting | unchanged: drop the leg (credit `pow` 0) or prove the ethSTARK attempt-divider. Contained; ember decision |
| **L4** transcript wire / committed word | **= Slice B.** Verifier-syntax half proved; Merkle log-decode identification open |
| **L5** codeword → `VmTrace` decode | **= Slice D.** Deterministic, no probability, heaviest |
| **L6** assembly at UD radius + apex re-read | days once L4/L5 land; `friLdtExtractV3_rom` proved (not `_of_legs`) |
| **L7** Johnson upgrade | research. `M = 1` is **refuted** (`FriJohnsonRadiusGap.deployed_M1_false_at_johnson`, tight 495/496); honest count `M ≤ 7`. And the commit column caps the payoff — see `OPENING-SOUNDNESS-DECONFLATED.md` (a) |

**Insert Slice A ahead of all of them.** It is the only item that changes whether any of the rest
*means* anything at the deployed apex: an apex whose premise has no model is a theorem about nothing,
and the tree currently cannot say whether it has one.

---

## 6. ArkLib is not a shortcut (verified against upstream, not assumed)

Re-verified 2026-07-27 against upstream `main = fad5cbf80877` (both `/private/tmp/arklib-*`
checkouts had been emptied by macOS `/private/tmp` cleanup; content was read byte-exact via
`gh api`, not summarized — a `WebFetch` attempt **hallucinated** the file contents and was discarded).

- **The FRI security lemmas are `sorry`, at exactly the cited lines.** `ArkLib/ProofSystem/BatchedFri/
  Security.lean` — `fri_round_consistency_completeness:256` (`sorry` at `:268`),
  `fri_query_soundness:625` (`:682`, followed by ~60 lines of abandoned commented-out proof),
  `fri_soundness:749` (`:774`). Docstrings map them to BCIKS20 Claims 8.1/8.2/8.3.
- **The adversary is unbounded — and ArkLib has no query-counting primitive at all.**
  `Security/Basic.lean:242,289` quantify over *all* types `WitIn WitOut` and *all* inhabitants of
  `Prover`. ⚑ Sharper than previously stated: `fri_soundness` does not even use those definitions —
  it rolls its own inline existential over `OracleProver` (`Security.lean:759`). And
  `OracleReduction/Basic.lean:343` is `def numQueries ... := sorry` with the comment *"TODO: define
  once numQueries is defined in OracleComp"*. **The counting machinery dregg's `RomOracle` /
  `QueryBounded` floor is built on does not exist upstream.**
- **⚑ CORRECTION to this document's rev. 1 and to `ARKLIB-VS-DREGG-FRI-COMPARISON.md`:**
  `proximity_gap_RSCodes` (`Data/CodingTheory/ProximityGap/BCIKS20/ReedSolomonGap.lean:34`) is
  **stated at the JOHNSON bound**, not the unique-decoding radius — its hypothesis is
  `hδ : δ < 1 - ReedSolomon.sqrtRate deg domain` (`:39`). Its own file is `sorry`-free, but the
  import cone reaches a `sorry` by a **semantic**, not incidental, path:
  `ReedSolomonGap:240` → `correlatedAgreement_affine_spaces` (`AffineSpaces.lean:2096`) →
  `RS_correlatedAgreement_affineLines` (`AffineLines/Main.lean:29`), whose proof is a two-case
  split — the `δ ≤ relativeUniqueDecodingRadius` branch is discharged, and the `else` branch is
  literally `-- TODO: theorem 5.1 for list-decoding regime` / `sorry` (`:40`).
  **So it is honestly proved only at the unique-decoding radius, while advertising Johnson.**
  Everything strictly between UD and `1 − √ρ` rests on that one `sorry`. Cite it accordingly — this
  is the same "the statement is wider than the proof" pattern this campaign exists to catch.
- **Scale:** 235 live `sorry` across 70 files in ArkLib (after stripping comments); 22 in
  `ProximityGap/BCIKS20/`, 88 in `ProofSystem/`. `WeightedAgreement.lean` is a pure stub — all six
  declarations `sorry`. Even `Verifier.id_soundness` (*the identity verifier is perfectly sound*,
  `Basic.lean:555`) is `sorry`.
- **dregg is strictly ahead on proved FRI arithmetic.**
- **The one reusable asset** is the *statement shape* of `Extractor.Straightline:218` /
  `knowledgeSoundness:289` as a template for `friLdtExtractV3_rom`, paired with dregg's own ROM query
  bound — **ported as a pattern, not vendored.** VCVio is not optional: it supplies `OracleComp`,
  `QueryLog`, `simulateQ` and the `Pr[…]` notation, is 467 files / ~6.7 MB, moved as recently as
  today, and ArkLib's manifest pulls **19 packages**.
  ⚑ **Copy one detail deliberately**: `knowledgeSoundness` runs the extractor's `OptionT` *explicitly*
  (`.run`) so extractor failure counts as an adversary win. Its docstring (`:274-283`) records why —
  binding it inside the surrounding `OptionT` would let `fun _ _ _ _ _ => failure` drive the event
  probability to 0 and **vacuously** discharge knowledge soundness at error 0 for any verifier. That
  is a vacuity trap of exactly the class this repo keeps finding; if the template is copied, the
  `.run` placement must be copied with it.

See `docs/reference/ARKLIB-VS-DREGG-FRI-COMPARISON.md` — **its Johnson/UD line needs the correction
above.**

---

## 7. PoC status (honest)

**No speculative Lean is landed with this document, deliberately.** Slice A is the one candidate that
is small enough to be a real PoC, and it is a change to a *deployed acceptance predicate* — it must be
landed with its canary flipping and a full-tree build behind it, not as an unbuilt stub. Per
`feedback-every-instrument-is-blind-to-the-next-wound` and the shared-tree discipline, that is its own
committed lane on hbox `swarm-build`, starting with the `p3_batch_stark` read that decides whether
Slice A is a model fix or a verifier fix.

Slices B–D are multi-file and each lives inside a heavy import cone; none is a scratchpad PoC.

Cross-refs: `docs/OPENING-SOUNDNESS-DECONFLATED.md` (the 3-way split),
`docs/DESIGN-fri-adversary-object.md` (the original L1–L7 ladder),
`docs/WOUND-apex-premise-vacuity-2026-07-24.md` (the original wound; read §2 above for what has
changed since), `project-fri-correlated-agreement-formalization`, `project-fri-soundness-reality`.
