# Sound-Fix Verdict: which repair of ArkLib's vacuous t-SDH / KZG binding to ship

**Scope.** Five candidate sound fixes for ArkLib's `Classical.choice`-vacuous `tSdhAssumption`
(and the `binding` / `function_binding` it powers) were elaborated under
`candidates/`. This note is the integrator's verdict: each candidate re-verified against real
ArkLib @ `d72f8392` (Lean `v4.31.0`), the comparison, the per-goal winner, and the honest
recommendation. **Re-verification was done by rebuilding each artifact against the genuine tree
and reading the theorem *statements*, not trusting the lane's summary.**

Nothing here is filed, pushed, or PR'd.

**⚑ STATUS UPDATE — the end-to-end sound argument is COMPLETE, in BOTH standard GGM models.** The single
capstone `GgmEndToEnd.tSdh_ggm_sound` is a `sorry`-free upper bound on ArkLib's **real** `tSdhExperiment`,
`≤ (C(fuel+D+4,2)·D + (D+1))/(p−1)` (a genuine `< 1` in the standard regime,
`tSdh_ggm_sound_lt_one`), quantifying over the **image of the generic embedding** `embed` — the class
that escapes the vacuity. This wired capstone is the **Maurer explicit-equality** model (the adversary
tests handle pairs by explicit `Move.query` queries; the all-pairs count is a sound over-count here). The
**Shoup random-encoding** model — the adversary comparing all held encodings *freely* via the full
equality matrix `eqPattern`, no `query` move, where the same all-pairs count is *tight* — is now proved
**standalone** as `GgmShoup.shoup_ggm_sound` (commit `a97a7c7c1`) at the identical bound, with the
matrix-valued identical-until-bad hybrid `runShoup_congr_off_bad` PROVEN. Earlier drafts mislabelled the
wired capstone "Shoup random-encoding"; that label belongs to the standalone `GgmShoup` theorem, and the
capstone is corrected to Maurer. Wiring Shoup into ArkLib (a Tier-2 embed) is optional and redundant —
Maurer is the wired track; the injective encoding `σ` folds away in both models and is never mechanized. Independently rebuilt from the committed source against ArkLib `d72f8392`:
`#print axioms tSdh_ggm_sound` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; the full
spine (`embed`, `embed_run_correspondence`, `experiment_eq_count`, `rand_encoding_bound_D_of_run`,
`hdeg_out_of_run`, `hdeg_handles_of_run`, `groupWinSet_eq_realWinSet`, `card_realWinSet_le_encoding_D`)
is likewise axiom-clean. The two residuals the scope limits below used to track (degree discharge;
`ProbComp` threading) are DISCHARGED on the critical path; what remains is genuinely optional and
off-path (the conservative pairing-aware δ = 2D variant; re-typing the extraction reduction's adversary
as a `Strat`). Honest side-conditions, named: `1 ≤ D`, `2 ≤ p`, `orderOf g₁ = p` (`g₁, g₂ ≠ 1`), and
ArkLib's own `SampleableType` instance. The bracketed "scope limits" and "interlock verdict" below are
retained as the record of how the frontier closed; each is now annotated CLOSED.

---

## 0. Re-verification results (rebuilt by the integrator, not inherited)

Every artifact below was recompiled with `lake env lean` against the genuine ArkLib checkout
(`/private/tmp/arklib-review` or `/private/tmp/arklib-ggm`, both at `d72f8392`), and its axiom
closure printed. All are `sorry`-free with axioms exactly `[propext, Classical.choice, Quot.sound]`
— **no `sorryAx`**.

| Artifact | Headline theorem(s) | Build | Axioms |
|---|---|---|---|
| `GgmCandidate.lean` | `ggm_tSdh_sound`, `card_winningPoints_le`, `ggm_bound_lt_one` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmAdaptive.lean` (ADAPTIVE) | `adaptive_ggm_sound`, `runAux_congr_of_agree`, `realWinSet_subset`, `card_rootUnion_le`, `adaptive_generalizes_static` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmRandomEncoding.lean` (QUADRATIC) | `rand_encoding_bound`, `card_pairRootUnion_le_two_mul`, `card_handlePolys_le`, `badSet_subset_pairRootUnion`, `rand_encoding_bound_srs` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmDegreeInvariant.lean` (DEGREE, peer) | `degree_invariant_paired`, `degree_invariant_paired_uniform`, `flat_2D_bound_false`, `degree_invariant`, `degree_invariant_linComb` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmArkLibTransport.lean` (TRANSPORT) | `groupWinSet_eq_realWinSet`, `tSdhCondition_iff_field`, `gpow_val_injective`, `fraction_bound_transports_to_group` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmDegreeDischarge.lean` (DEGREE, real oracle) | `hdeg_out_of_run`, `hdeg_handles_of_run`, `rand_encoding_bound_D_of_run`, `runTable_natDegree_le` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmProbThreading.lean` (PROBCOMP) | `experiment_eq_count`, `game_collapse` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmEmbed.lean` (EMBEDDING) | `embed`, `embed_run_correspondence` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmEndToEnd.lean` (**⚑ CAPSTONE**, Maurer explicit-equality, wired) | `tSdh_ggm_sound`, `tSdh_ggm_sound_lt_one` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmShoup.lean` (**⚑ SHOUP random-encoding**, standalone) | `shoup_ggm_sound`, `shoup_ggm_sound_lt_one`, `runShoup_congr_off_bad`, `realWinSetShoup_subset`, `card_realWinSetShoup_le_allPairs` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `AlgebraicTSdh.lean` (novel) | `algExperiment_le`, `alg_survives_attack`, `algExperiment_zeroPoly` (canary) | exit 0 | clean |
| `RepairSurvives.lean` (extraction) | `binding_reduces_to_tSdh`, `repair_survives_attack`, `t_sdh_cond_of_two_valid_openings` | exit 0 | clean |
| `KzgQDlogVacuity.lean` (qdlog) | `not_qDlogAssumption`, `qDlogExperiment_trapdoorAdversary`, `experiment_discriminates` (canary) | exit 0 | clean |
| `AgmSound.lean` (agm) | `repr_valid_of_extraction`, `tau_mem_roots` | exit 0 | clean |

---

## 1. The comparison table

| Candidate | Survives-attack | Numeric bound (rests-on) | Mechanized today | Verdict |
|---|---|---|---|---|
| **extraction** | **PROVEN** (`repair_survives_attack`, sorry-free) | **NO** — reduction only, honestly | **sorry-free** (`+41/−14` patch to `Binding.lean`; whole tree 2994 jobs, exit 0) | **STRONG** (mergeable now) |
| **GGM (static → adaptive → end-to-end)** | **PROVEN** (`ggm_tSdh_sound` static, `adaptive_ggm_sound` adaptive, `tSdh_ggm_sound` end-to-end over the `embed` image on ArkLib's real `tSdhExperiment`) | **YES: `(D+1)/(p-1)` static; `(C(fuel+D+4,2)·D+(D+1))/(p−1)` end-to-end** — rests on the generic-restricted class (output is `g₁^{f(τ)}`, `deg f ≤ D`; `τ` never in the adversary's view) | **sorry-free, COMPLETE** (static + adaptive + capstone; axioms clean) | **STRONG — the mechanized numeric sound-fix, end-to-end** |
| **novel / AlgebraicTSdh** | **PROVEN** (`alg_survives_attack`, sorry-free) | **YES: `(D+1)/(p-1)`** — same static Schwartz–Zippel core, algebraic-model framing | **sorry-free** | **STRONG** — this *is* the GGM-static number in the AGM idiom; a sibling, not a rival |
| **AGM (FKL)** | bounded form **provably still BROKEN** (representation is free data); reduction transports t-SDH(alg) → q-DLOG | **NO** — relocates the number onto q-DLOG (FKL's own `O((t²q+q³)/p)` is *argued*, not mechanized) | reduction sorry-free; the bound is **not** mechanized | **VIABLE relocation / WEAK standalone** |
| **qdlog-direct** | naive form **mechanized BROKEN** (`not_qDlogAssumption`, sorry-free); sound form rests on GGM | **NO** — the number comes from GGM (now mechanized end-to-end, `tSdh_ggm_sound`) | vacuity mechanized; sound bound routes through the now-complete GGM | **DEAD as an escape** (collapses to "fix the base assumption first") — but a **valuable finding** (§4) |

Axes read as: **survives-attack** = does the exact `tauExtractingAdversary` trapdoor attack fail
to beat the bound? — `proven` (mechanized), `argued` (paper), `broken` (still refuted).
**numeric** = does it deliver a real `ε < 1`, and on what does that `ε` rest? **mechanized-today**
= sorry-free against the genuine tree now, partial, or frontier.

---

## 2. The crown jewel, re-checked by a skeptic — is GGM-static a real bound or a dodge?

`ggm_tSdh_sound` states: **for every** `A : GenericAdversary D p` (offset `c`, representation
polynomial `f` with `deg f ≤ D`), with `2 ≤ p`,

```
ggmExperiment A = (winningPoints A).card / (p - 1)  ≤  (D + 1) / (p - 1)
```

A survives-attack result is worthless if it survives by *excluding everything* — a bound that
holds because no adversary is expressible, or because it merely restates `≤ 1`. Applying that
sufficient test to **our own winner**:

1. **The adversary type is richly inhabited, not empty.** `GenericAdversary D p` ranges over
   *every* offset in `ZMod p` and *every* degree-≤D polynomial. The theorem quantifies over that
   whole type — including every `Classical.choice`-definable inhabitant. It does **not** survive
   by having no adversaries to bound. (Contrast a dodge that restricts the type to the empty set.)

2. **The bound is a genuine `< 1`, not a restated `≤ 1`.** `ggm_bound_lt_one` proves
   `(D+1)/(p-1) < 1` for `p > D+2`; at cryptographic parameters (`p ≈ 2²⁵⁴`, `D ≈ 2²⁰`) it is
   `≈ 2⁻²³⁴`. A real, tiny number.

3. **The measured quantity is genuinely nonzero and the cap is tight.** An adversary that
   interpolates `f` through `D+1` targets `1/(τᵢ+c)` wins on exactly `D+1` trapdoors — the
   Boneh–Boyen worst case — so `winningPoints` is not trivially empty and `(D+1)` is not slack.
   The sibling canaries confirm the experiment discriminates (`algExperiment_zeroPoly`,
   `experiment_discriminates`: distinct adversaries get distinct success values).

4. **The generic model is faithful for the static class.** In a prime-order group the reachable
   exponents from the SRS handles `g₁^{τ⁰}, …, g₁^{τ^D}` are exactly `span{1, τ, …, τ^D}` =
   degree-≤D polynomials, so "committed degree-≤D `f`, chosen with `τ` absent" is the *exact*
   static-generic output space, not a convenient sub-space. The exact `tauExtractingAdversary`
   that killed the original **cannot even be typed** here — `GenericAdversary` receives no group
   element, hence no `∃ a, · = g^a` for `Exists.choose` to invert.

**Semantic verdict: GGM-static is a REAL numeric survives-attack bound, not a definitional
dodge.** It survives by *removing the leak input* (`τ`/`g^τ`), not by emptying the adversary set,
and it delivers a real `ε`.

### Two honest scope limits (must travel with every citation)

- **(a) STATIC, now EXTENDED to ADAPTIVE (explicit-oracle model) — `GgmAdaptive.lean`.** The
  `GgmCandidate.lean` bound is the `q = 0` fragment: the adversary commits to one output and makes
  **zero** queries. This limit is now **closed for the explicit-equality-oracle (Maurer) GGM**:
  `adaptive_ggm_sound` admits an adversary making up to `fuel` adaptive queries — linear combinations,
  pairings, and equality tests — and bounds its success by `(fuel·Δ + (D+1))/(p−1)`, sorry-free,
  axioms `[propext, Classical.choice, Quot.sound]`. **The identical-until-bad hybrid is PROVEN by
  induction** (`runAux_congr_of_agree`), not assumed; `fuel = 0` recovers the static number exactly.
  Two residuals remain (see PAPER §9.2), named not faked, and **both narrowed** by the three new lemma
  files: (i) the *classical quadratic* `~(q_G+D)²(D+1)/(p−1)` — the all-table-pairs collision-counting
  shape — is MECHANIZED at the counting level as
  `GgmRandomEncoding.rand_encoding_bound : ε ≤ (C(n,2)·2D + (D+1))/(p−1)` with `n = fuel+D+4`, the
  all-table-pairs bad event and the table-size bound both THEOREMS (`badSet_subset_pairRootUnion`,
  `card_handlePolys_le`), **modulo** the whole-table degree hypothesis `hdeg_handles`; that all-pairs
  count is a sound *over-count* in the Maurer model (only queried pairs collide), and the genuine
  **Shoup random-encoding** model — free comparison, where the same count is *tight* — is now a proved
  standalone theorem `GgmShoup.shoup_ggm_sound` (the `eqPattern` free-comparison adversary, hybrid
  `runShoup_congr_off_bad` PROVEN); our tighter linear-in-queries number remains the honest Maurer bound
  for the model where equality costs a query; (ii)
  the degree facts still enter as hypotheses, but the SRS degree invariant is now proved
  **structurally** — `GgmDegreeInvariant.degree_invariant_paired : 2D` under the two-sorted pairing
  discipline, with the naive flat `2D` claim REFUTED (`flat_2D_bound_false`, `X⁴` at `D=1`). Crucially
  that proof is a **PEER model** (`PairedOp`/`buildPaired`) that `GgmAdaptive.runAux` does not import, so
  it does **not yet discharge** `hdeg_out`/`hdeg_pairs`/`hdeg_handles` — see the interlock verdict below.
  The generic-group oracle + simulation lemma that **neither Mathlib nor VCVio had** are built from
  scratch in `GgmAdaptive.lean`.

  **⚑ CLOSED (critical path).** The degree hypotheses are now DISCHARGED for the oracle the experiment
  actually runs. Because ArkLib's `tSdhAdversary D` is granted no pairing map, that oracle is purely
  **linear** (`Move.lin` only), and `GgmDegreeDischarge`'s `hdeg_out_of_run` / `hdeg_handles_of_run`
  prove `natDegree ≤ D` by induction on the real `runAux`/`runTable` (not the `buildPaired` peer). The
  capstone `GgmEndToEnd.tSdh_ggm_sound` consumes these `_of_run` theorems directly, so the δ = D
  random-encoding number is hypothesis-free. The peer δ = 2D model is retained as the off-path ceiling
  for a hypothetical pairing-endowed adversary.

- **(b) FIELD-LEVEL win predicate — condition-level transport MECHANIZED against real ArkLib;
  `ProbComp` plumbing now CLOSED (see annotation below).** The win condition is stated at the field level (`f.eval τ = 1/(τ+c)`).
  Its equivalence to ArkLib's group-level win is **no longer merely argued**:
  `GgmArkLibTransport.groupWinSet_eq_realWinSet` / `tSdhCondition_iff_field` import ArkLib's **real**
  `Groups.tSdhCondition` (restating nothing) and prove — via injectivity of `a ↦ g^{a.val}` in a
  prime-order group, from ArkLib's own `gpow_div_eq` / `exists_zmod_power_of_generator` — that the
  generic run's group-level winning-trapdoor set IS `GgmAdaptive.realWinSet`, so the bound transports
  verbatim to the group side. What remains is the `OptionT ProbComp` / `StateT QueryCache` monad
  threading (the `Strat → tSdhAdversary` embedding + `sampleNonzeroZMod` sampler `Pr = card/(p−1)`
  semantics) and the separate re-typing of `bindingReduction`'s adversary as a `Strat` — probability
  bookkeeping and reduction-plumbing, with the **condition provably identical**.

  **⚑ CLOSED (critical path).** The `ProbComp` threading is DONE:
  `GgmProbThreading.experiment_eq_count` collapses ArkLib's `OptionT ProbComp` / `StateT QueryCache`
  game to `(winSet.card)/(p−1)` for the deterministic-given-τ adversary `embed` produces. The
  `Strat → tSdhAdversary` embedding is DONE: `GgmEmbed.embed` / `embed_run_correspondence` construct
  the generic-restricted adversary and certify it realizes exactly `g₁^{f(τ)}`, `deg f ≤ D`. Composed
  in `GgmEndToEnd.tSdh_ggm_sound`, the counting bound now bounds ArkLib's literal `tSdhExperiment`.
  Remaining and **optional**: re-typing the extraction reduction's `bindingReduction` adversary as a
  `Strat` (a convenience to chain §8.1's binding statement to the number — the t-SDH soundness result
  already holds over the whole `embed` image).

**Interlock verdict (verified by reading, not taken on trust).** The three files are *designed* to
interlock — `GgmRandomEncoding`'s `hdeg_handles` ↔ `GgmDegreeInvariant`'s structural `2D` ↔ the pairing
discipline — but the interlock is **architectural, not mechanized**: `GgmDegreeInvariant` imports only
`Mathlib`, references no adaptive-experiment object, and nothing imports it; there is no bridge lemma
`runTable ↔ buildPaired`. So the degree bound is proved in a **peer model**, and the adaptive /
random-encoding theorems **still carry their degree facts as undischarged hypotheses**. Honest tag: the
degree invariant is proved *structurally as a peer* and refutes the naive flat claim — but it is **not**
a discharge of the hypothesis in the experiment. Wiring the discipline into `runAux` (two-sorted handle
table, or a `runTable ↔ buildPaired` bridge) is the one remaining item on that axis; and because
`runAux`'s flat `Move.pair` admits nesting, `flat_2D_bound_false` shows `2D` is a genuine restriction the
oracle must adopt, not a property it already has.

**⚑ CLOSED — resolved a different, simpler way.** The wiring turned out not to require the two-sorted
re-typing at all. The ArkLib t-SDH adversary has **no pairing map**, so the deployed oracle is purely
linear and δ = D holds *by construction*: `GgmDegreeDischarge` proves the degree facts by induction on
the real `runTable` (`runTable_natDegree_le`, `handlePolys_natDegree_le`, `badPolys_natDegree_le` via
`natDegree_sub_le`'s MAX bound), and the `_of_run` corollaries feed the capstone. So the degree
invariant is now a **theorem about the oracle the experiment runs**, not a peer-model result. The
`buildPaired` δ = 2D model remains a real, separate theorem — the honest ceiling for a *pairing-endowed*
oracle — but it is off the critical path and discharges nothing the deployed bound needs.

Neither limit makes the bound a dodge — they scope *what class* and *at what level* the real
number holds; both are now closed on the critical path, with the end-to-end capstone assembling them.

---

## 3. Winners, by goal

- **Mergeable now → `extraction`.** The only candidate that is both sorry-free against the genuine
  tree *and* a low-invasiveness (`+41/−14`) patch with the whole tree green. It removes the
  vacuous premise and provably survives the exact attack — but hands **no number** (its RHS is
  still `tSdhExperiment` of the constructed reduction adversary). This is the safe first commit.

- **Numeric survives-attack (static) → `GGM-static`** (equivalently `AlgebraicTSdh`). The only
  mechanized candidate that delivers a real `ε = (D+1)/(p-1) < 1` proven for the whole generic
  adversary type. Scope it as **static** every time.

- **End-to-end t-SDH soundness on ArkLib's real experiment → `GgmEndToEnd.lean` (MECHANIZED, COMPLETE) —
  the Maurer explicit-equality model.**
  The capstone `tSdh_ggm_sound` composes every leg into one `sorry`-free bound
  `tSdhExperiment D (embed strat) ≤ (C(fuel+D+4,2)·D + (D+1))/(p−1)` over the image of the generic
  embedding (`< 1` in the standard regime, `tSdh_ggm_sound_lt_one`), axioms exactly
  `[propext, Classical.choice, Quot.sound]`. This is the sound-fix goal fully met at the GGM level, in
  the Maurer model (explicit `Move.query` equality; all-pairs count a sound over-count).
- **Both standard GGM models covered → `GgmShoup.lean` (MECHANIZED, standalone) — the Shoup
  random-encoding model.** `shoup_ggm_sound` proves the *same* bound `≤ (C(fuel+D+4,2)·D + (D+1))/(p−1)`
  for the free-comparison `ShoupStrat` adversary (full equality matrix `eqPattern`, no `query` move,
  all-pairs count TIGHT), the matrix-valued identical-until-bad hybrid `runShoup_congr_off_bad` PROVEN,
  degree invariants discharged. Standalone (`1 ≤ D`, `2 ≤ p`, `Fact (Nat.Prime p)`; no group or
  `SampleableType` condition). This is the theorem the "random-encoding" claim now names; wiring it into
  ArkLib is optional and redundant, Maurer being the wired track.
- **Adaptive numeric bound (explicit-oracle GGM) → `GgmAdaptive.lean` (MECHANIZED).** The
  generic-group oracle that was absent from Mathlib/VCVio is now built, and the adaptive `q`-query
  bound `(fuel·Δ + (D+1))/(p−1)` is proven sorry-free with the identical-until-bad hybrid mechanized
  by induction. The follow-on files (PAPER §9.1) then complete the chain: `GgmRandomEncoding.lean`
  mechanizes the **quadratic** all-pairs collision-counting core `(C(n,2)·2D + (D+1))/(p−1)` at the
  counting level (all-table-pairs bad event + table size, both THEOREMS) — a sound over-count for the
  Maurer capstone, and the tight count for the standalone **Shoup random-encoding** theorem
  `GgmShoup.shoup_ggm_sound`; `GgmDegreeDischarge.lean`
  **discharges** the degree invariant on the real (linear, pairing-free) `runTable` via its `_of_run`
  theorems (`GgmDegreeInvariant.lean`'s `2D` structural bound is retained as the off-path pairing-aware
  ceiling); `GgmArkLibTransport.lean` mechanizes the **condition-level** field→group transport against
  ArkLib's real `tSdhCondition`; `GgmProbThreading.lean` threads the `ProbComp` monad
  (`experiment_eq_count`); and `GgmEmbed.lean` constructs the generic-restricted adversary. `AGM` and
  `qdlog-direct` correctly route their numbers back through exactly this generic-group hardness.

---

## 4. The finding that strengthens the whole result: the vacuity is the *pattern*, not the theorem

Re-verified, sorry-free, against real ArkLib:

- **`not_qDlogAssumption` (`KzgQDlogVacuity.lean`).** State the natural "reduce KZG binding to
  q-strong-DLOG" base assumption in ArkLib's *own* idiom — recover the trapdoor `τ` from the
  power-SRS, with the same unrestricted `… → StateT unifSpec.QueryCache ProbComp (Option _)`
  adversary type — and it is **equally vacuous**: false for every error `< 1`, by the *identical*
  `Classical.choice` trapdoor extraction. So switching the named assumption (t-SDH → q-DLOG) does
  **not** escape the hole.

- **ArkLib's own `AGM/Basic.lean` is unsound as written** (source-read, `d72f8392`):
  `Adversary.run` is literally `sorry` (`AGM/Basic.lean:164–165`), the type proves zero theorems
  and is orphaned, and — decisively — `Adversary` is a `ReaderT (GroupValTable ι G) …`
  (`AGM/Basic.lean:149–153`) that hands the adversary the **concrete** group table over the
  concrete group `G`, so its outputs can still depend on discrete logs. The author's own comments
  flag exactly this: *"TODO: need to be sure this definition is correct"* (line 147) and *"How to
  make the adversary truly independent of the group description? It could have had `G` hardwired"*
  (lines 169–173).

**Consequence:** the vacuity is not a t-SDH typo; it is the whole *unrestricted-adversary pattern*
in this idiom. Any concrete-group hardness assumption stated as `∀ (unrestricted adversary),
Pr[win] ≤ ε < 1` is `Classical.choice`-false, and the ecosystem lacks a sound generic/algebraic
adversary class to state it against. That is what makes the mechanized static-GGM bound above
worth having: it is the first sound, restricted-class numeric hardness statement in the tree.

---

## 5. Honest recommendation

1. **Ship `extraction` first** as the immediate, backward-compatible de-vacuation
   (`binding_reduces_to_tSdh` primary, `binding` a corollary). It is mergeable today and costs
   nothing in soundness.
2. **Adopt `GGM-static` as the mechanized numeric floor**, stated *precisely as the static
   fragment*, to discharge the single reduction obligation `extraction` isolates — for the static
   adversary class. Do not let it be read as the full adaptive number.
3. **The GGM soundness argument is COMPLETE — state it as done.** The generic-group oracle (once absent
   from Mathlib/VCVio), the adaptive linear bound, the quadratic random-encoding counting bound, the
   condition-level field→group transport, the degree discharge on the real oracle, the `ProbComp`
   threading, and the embedding are all MECHANIZED (PAPER §9.1), and compose into the `sorry`-free
   capstone `GgmEndToEnd.tSdh_ggm_sound` on ArkLib's real `tSdhExperiment`. Name the side-conditions
   (`1 ≤ D`, `2 ≤ p`, `orderOf g₁ = p`, ArkLib's `SampleableType` instance) with the claim. What remains
   is **optional, off the critical path**: (a) the conservative pairing-aware δ = 2D variant
   (`GgmDegreeInvariant`'s peer model) — a strictly weaker bound for a stronger, off-interface adversary,
   kept as a ceiling; (b) re-typing `bindingReduction`'s adversary as a `Strat` so the *extraction*
   reduction (not merely a generic `Strat`) inherits the number. Neither gates the soundness result.
4. **Present the q-DLOG-idiom vacuity and the AGM stub as evidence that the pattern is systemic** —
   the reason a sound restricted adversary class (not a renamed assumption) is the real fix.
