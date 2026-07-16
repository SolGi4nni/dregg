# KZG-GGM — the end-to-end coherent argument (wiring plan)

Status: DESIGN. No proofs written here. This document exists so the next swarm builds
toward **one named theorem** about ArkLib's real `tSdhExperiment`, not another pile of
green peer lemmas.

Verified by reading (2026-07-16, ArkLib @ `d72f8392`, real tree at
`/private/tmp/arklib-ember/ArkLib`, candidates at `candidates/`).

---

## 0. The honest current state (what actually exists)

Four sorry-free files, individually green, that **do not compose**:

| file | headline | model | status vs ArkLib |
|---|---|---|---|
| `candidates/GgmCandidate.lean` | `card_winningPoints_le : (winningPoints A).card ≤ D+1` | committed `GenericAdversary D p` (offset + degree-≤D repr poly) | static (q=0) field core; **reused as-is** |
| `candidates/GgmAdaptive.lean` | `adaptive_ggm_sound : adaptiveExperiment ≤ (fuel·Δ + (D+1))/(p−1)` | self-contained `Strat`/`runAux` | field-level ℚ; carries `hdeg_out`,`hdeg_pairs` as **hypotheses** |
| `candidates/GgmRandomEncoding.lean` | `rand_encoding_bound : adaptiveExperiment ≤ (C(n,2)·2D + (D+1))/(p−1)` | same `runAux` | field-level ℚ; carries `hdeg_handles` as **hypothesis** (table-size `card_handlePolys_le` IS a theorem) |
| `candidates/GgmDegreeInvariant.lean` | `degree_invariant_paired : G₁≤D ∧ Gₜ≤2D` | **peer** `buildPaired` (imports only Mathlib) | NOT wired into `runAux`; `flat_2D_bound_false` shows `runAux`'s `Move.pair` can violate ≤2D |
| `candidates/GgmArkLibTransport.lean` | `groupWinSet_eq_realWinSet`, `tSdhCondition_iff_field` | bridges field↔group **condition** | transports the CONDITION to `Groups.tSdhCondition`; **not** the experiment |

The disconnection is real and has three named seams: the degree hypotheses are unproven
about `runAux`; there is no adversary embedding `Strat → tSdhAdversary`; the field-level
ℚ-cardinality bound is never connected to `tSdhExperiment`'s `ℝ≥0∞` probability.

### ArkLib's real types (read, not inherited — `KZG/HardnessAssumptions.lean`)

```lean
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

abbrev tSdhCondition {g₁ : G₁} : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) => τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val

abbrev tSdhGame (D : ℕ) (adversary : tSdhAdversary D) : OptionT ProbComp (ZMod p × ZMod p × G₁) :=
  OptionT.mk (do
    let τ ← sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun (c, h) => (τ, c, h))))

noncomputable def tSdhExperiment (D : ℕ) (adversary : tSdhAdversary D) : ℝ≥0∞ :=
  Pr[tSdhCondition (g₁ := g₁) | tSdhGame (g₁ := g₁) (g₂ := g₂) D adversary]
```
with `sampleNonzeroZMod : ProbComp (ZMod p) = (fun i : Fin (p-1) => (i+1 : ZMod p)) <$> $ᵗ(Fin (p-1))`
and `PowerSrs.generate D τ = (tower g₁ τ D, tower g₂ τ 1)`, `tower g τ n = .ofFn (i ↦ g ^ (τ.val ^ i.val))`.

---

## 1. ⚑ THE SINGLE TARGET THEOREM

### 1a. Why it cannot quantify over all `tSdhAdversary`

`tSdhAdversary D` is an **arbitrary Lean function** `Vector G₁ (D+1) × Vector G₂ 2 → …`.
There is **no opacity invariant in the type**. A `Classical.choice`-definable adversary that
computes discrete logs (every element of a prime-order group *is* `g₁^(a.val)` for a unique
`a`, by ArkLib's own `exists_zmod_power_of_generator` + our `gpow_val_bijective`) wins t-SDH with
probability 1. So `∀ A : tSdhAdversary D, tSdhExperiment D A ≤ ε` is **FALSE** for any small ε.

The generic-group restriction is therefore **not a predicate on ArkLib adversaries** — it is a
**construction**. "Generic" = *in the image of the generic-oracle embedding*. The target quantifies
over generic **strategies** and applies the embedding:

### 1b. The socket (design sketch — the type everything fits)

```lean
-- the honest "generic-restricted adversary": the image of this embedding
def embed (strat : Strat p) : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)

theorem tSdh_ggm_sound
    {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁} (hg₁ : g₁ ≠ 1)
    {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂} (hg₂ : g₂ ≠ 1)
    (hp : 2 ≤ p) (D : ℕ) (strat : Strat p) (fuel : ℕ) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (embed (g₁ := g₁) (g₂ := g₂) D fuel strat)
      ≤ ENNReal.ofNNReal ⟨((fuel + D + 4).choose 2 * D + (D + 1) : ℚ) / (p - 1), _⟩
```

Read precisely:

- **What "generic-restricted" means as a type.** Not a subtype of `tSdhAdversary`; the *range* of
  `embed`. `embed strat` is an adversary that only ever touches group elements by (i) reading the
  SRS vectors, (ii) forming `ZMod p`-linear combinations of table elements, and (iii) testing
  `DecidableEq` equality of two table elements — never inverting the encoding. The **opacity
  invariant is discharged by construction**: `strat : List Bool → Move p ⊕ (ZMod p × ℕ)` receives
  only equality booleans, never a group element. There is no group element "in scope" for `strat`.

- **The concrete bound (random-encoding / Shoup shape, δ = D).** `n = fuel + D + 4` is the
  handle-table-size bound (`GgmRandomEncoding.card_handlePolys_le` at the SRS seeding: `D+3` seed
  handles — `1,X,…,X^D` in G₁ (D+1) plus `1,X` in G₂ (2) — one handle per fuel step, plus the
  zero/identity handle). Numerator `C(n,2)·D + (D+1)` is Shoup's global all-pairs collision event
  `C(n,2)·δ` plus the static Boneh–Boyen root event `D+1`, i.e. **`~(q+D)²·D/(2(p−1))`** with
  `q = fuel`. **δ = D, not 2D** — see §1c.

- **How it relates to ArkLib's experiment probability.** `tSdhExperiment D (embed strat)` is an
  `ℝ≥0∞` = `Pr[tSdhCondition | tSdhGame]`. Because `embed strat` is deterministic-given-τ and runs
  from an empty cache, the game collapses to `OptionT.mk (do τ ← sampleNonzeroZMod; pure (some (τ, c τ, h τ)))`,
  and the probability equals the **counting fraction** `(groupWinSet g₁ strat (srsSt D) fuel).card / (p−1)`
  cast `ℚ → ℝ≥0∞`. `groupWinSet_eq_realWinSet` (already proven) identifies that set with
  `realWinSet`, and `rand_encoding_bound` bounds its cardinality. So the counting bound is about
  **precisely the event `tSdhExperiment` scores**.

### 1c. ⚑ Architectural finding: δ = D, and the pairing machinery is off the critical path

ArkLib's `tSdhAdversary` receives `Vector G₁ (D+1) × Vector G₂ 2` and **must output a `G₁`
element**. Its interface grants **no pairing map** `e : G₁ × G₂ → Gₜ`. Every G₁ element it can
produce is a group-linear combination of the D+1 SRS G₁ elements `g₁^(τ^i)`, i ≤ D — i.e.
`g₁^(f τ)` with `deg f ≤ D`. It can *compare* any two handles it holds (G₁ handles deg ≤ D, G₂
handles deg ≤ 1), so every queried-handle **difference has degree ≤ D**. Therefore, **for the
theorem literally about ArkLib's `tSdhExperiment`, δ = D.**

Consequence for the swarm:

- `GgmDegreeInvariant.buildPaired` / the `≤ 2D` / the `flat_2D_bound_false` counterexample all
  model a **pairing the ArkLib adversary interface does not grant**. They are the *conservative*
  (stronger-adversary) claim and are **not required** to bound `tSdhExperiment`. Keep them as an
  optional separate track (§3, task E-opt); do **not** put them on the critical path.
- The critical path uses the **linear** handle model: drop `Move.pair` from the oracle (ArkLib's
  t-SDH adversary has no pairing), which *also* dissolves the `flat_2D_bound_false` obstruction
  (no products ⇒ no nesting ⇒ degree ≤ D by a one-line seed-max induction). The degree discharge
  becomes trivial (§2a).
- Use `GgmRandomEncoding` with **Δ instantiated at D**, not 2D. `card_pairRootUnion_le` already
  takes an arbitrary `Δ`; only the `_two_mul` specialization and `rand_encoding_bound`'s hardcoded
  `2*D` need a D-parametric sibling (mechanical).

---

## 2. GAP ANALYSIS — what each existing lemma must BECOME

### (a) DEGREE DISCHARGE — `hdeg_out` / `hdeg_handles` : hypothesis → theorem

**Current.** `GgmAdaptive.adaptive_ggm_sound` and `GgmRandomEncoding.rand_encoding_bound` take
`hdeg_out : (symOutput …).2.natDegree ≤ D` and `hdeg_handles : ∀ q ∈ handlePolys …, q.natDegree ≤ 2*D`
as hypotheses. `GgmDegreeInvariant` proves the analog for a **peer** model (`buildTable`/`buildPaired`),
never wired to `runAux`.

**Must become.** Two theorems about `runAux`'s *actual* table on the SRS seeding:
```lean
theorem symOutput_natDegree_le  (strat) (fuel) : (symOutput strat (srsSt D) fuel).2.natDegree ≤ D
theorem handlePolys_natDegree_le (strat) (fuel) : ∀ q ∈ handlePolys symAns strat fuel (srsSt D), q.natDegree ≤ D
```
**Route (critical path).** Drop `Move.pair` from `Move`/`runAux`/`runTable` (ArkLib t-SDH adversary
has no pairing). Then a single induction on fuel — mirroring `GgmDegreeInvariant.degree_invariant_linComb`
but on the real `runTable` recursion — gives every handle degree ≤ D: seeds `X^k` (k ≤ D) meet it
(`natDegree_srs_le`), `combine` degrades to the max (`natDegree_linEntry_le`), queries don't grow
the table. `hdeg_out` follows since the output handle is a table `getD`. The degree-invariant helper
lemmas in `GgmDegreeInvariant` (`natDegree_getD_le`, `natDegree_linEntry_le`, `natDegree_srs_le`) are
**reused verbatim**; only the induction target moves from `buildTable` to `runTable`.

*Note:* `combine` is a general `List (ZMod p × ℕ)` linear combination (n-ary), vs `GgmDegreeInvariant`'s
binary `linComb`. The max-bound generalizes to n-ary by `List.sum` + `natDegree_sum_le` — a small
extra lemma (`natDegree_combine_le`).

### (b) ADVERSARY EMBEDDING — `Strat → tSdhAdversary` (the load-bearing design)

**Current.** Nothing. `groupWinSet` (transport file) *names* the realized group element
`g ^ ((runOutput (realAns τ) …).2.eval τ).val` but there is no adversary that *produces* it inside
`tSdhAdversary`.

**Must become.** `embed : Strat p → tSdhAdversary D` plus one correspondence lemma:
```lean
def embed (D fuel : ℕ) (strat : Strat p) : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs => pure (runEmbed g₁ g₂ D fuel strat srs)   -- deterministic; empty-cache; no ProbComp coins

-- runEmbed maintains a G₁/G₂ handle table seeded from srs, interprets strat's Moves as real group
-- ops, answers Move.query by DecidableEq on real group elements, returns (offset, output G₁ elt).

theorem embed_run_correspondence (τ : ZMod p) (strat : Strat p) (fuel : ℕ) :
    (runEmbed g₁ g₂ D fuel strat (PowerSrs.generate D τ))
      = some ( (runOutput (realAns τ) strat fuel (srsSt D)).1,
               g₁ ^ ((runOutput (realAns τ) strat fuel (srsSt D)).2.eval τ).val )
```
**The mechanism (why it is design-hard, not open).** `runEmbed`'s equality branch compares real
group elements `g₁^(f τ) =? g₁^(h τ)`; by **injectivity** (`gpow_val_inj_iff`, already proven in the
transport file) this equals `f.eval τ =? h.eval τ` = `realAns τ f h`. So `runEmbed`'s history bits
coincide with `runAux (realAns τ)`'s bit-for-bit, and by induction the whole run corresponds and the
output element is the encoding of `(runOutput (realAns τ) …).2.eval τ`. The correspondence is the
**"which ArkLib adversaries are generic"** answer: exactly `range embed`. This is the one genuinely
subtle construction (table↔polynomial invariant `tableG[i] = g₁^(table[i].eval τ).val`, threaded
through the induction; G₂ handled symmetrically; the output G₁-element realized by the same invariant).

### (c) PROBABILITY THREADING — field ℚ-count → `tSdhExperiment` ℝ≥0∞

**Current.** `fraction_bound_transports_to_group` gives the ℚ bound on `groupWinSet.card/(p−1)`. The
transport header names this residual explicitly.

**Must become,** in two mechanical sub-steps (VCVio lemmas all exist; `Binding.lean` is the precedent
— it does an *identical-shape* `Pr[·|OptionT.mk (do τ ← sampleNonzeroZMod; …)]` reduction with
`probEvent_mono`, `probEvent_comp`, `OptionT.probEvent_eq_of_run_map_eq`, `support_bind_exists`):

- **(c1) collapse the game.** With `embed strat` deterministic and empty-cache,
  `(embed strat srs).run' ∅ = pure (some (c, h))`; so
  `tSdhGame D (embed strat) = OptionT.mk (do τ ← sampleNonzeroZMod; pure (some (τ, c τ, h τ)))`.
  Monad `simp` over `StateT.run'`/`OptionT.mk`; Binding shows the idiom.
- **(c2) count the sampler.**
  `Pr[tSdhCondition | OptionT.mk (do τ ← sampleNonzeroZMod; pure (some (τ, c τ, h τ)))]`
  → push `tSdhCondition` through the `i ↦ i+1` map with **`probEvent_map`**, then
  **`probEvent_uniformFin`** (`Pr[P | $ᵗ(Fin (n+1))] = (univ.filter P).card / (n+1)`) gives
  `(filter over Fin (p−1)).card / (p−1)`. Re-index `Fin (p−1) ≃ nonzeroPoints` (the `i ↦ i+1`
  bijection) to rewrite the count as `groupWinSet g₁ strat (srsSt D) fuel).card`, then
  `groupWinSet_eq_realWinSet`. Cast ℚ → ℝ≥0∞ (`ENNReal.ofNNReal`, matching Binding's cast idiom).

The one non-mechanical wrinkle is the `OptionT`/`StateT` unwrap around the deterministic adversary
(the `.run' ∅` and `OptionT.mk` layers) — fiddly but bounded, with a direct Binding precedent.

### (d) COMPOSITION — assemble (a)+(b)+(c) into §1b

```
tSdhExperiment D (embed strat)
  = Pr[tSdhCondition | tSdhGame D (embed strat)]           -- defn
  = Pr[… | OptionT.mk (do τ ← sampleNonzeroZMod; pure …)]  -- (b) embed_run_correspondence + (c1)
  = ((groupWinSet g₁ strat (srsSt D) fuel).card / (p−1) : ℚ)          -- (c2)
  = ((realWinSet strat (srsSt D) fuel).card / (p−1) : ℚ)             -- groupWinSet_eq_realWinSet [done]
  ≤ ((C(fuel+D+4,2)·D + (D+1)) / (p−1) : ℚ)                          -- rand_encoding_bound @ Δ=D + (a)
```
Trivial glue once (a),(b),(c) land. Produces `tSdh_ggm_sound`.

---

## 3. THE BUILD PLAN (dependency-ordered)

`Fable` = neutral mathematical framing suffices (pure poly / monad / cardinality manipulation).
`Opus` = subtle design (the embedding, the monad-semantics glue). Effort in focused-days.

| # | task | file / target lemma | kind | who | effort | depends on |
|---|---|---|---|---|---|---|
| **A** | drop `Move.pair`; D-parametric `rand_encoding_bound` (`Δ`, not `2D`) — add `card_pairRootUnion_le` @ Δ=D siblings | edit `GgmAdaptive.lean` + `rand_encoding_bound_D` in `GgmRandomEncoding.lean` | MECHANICAL | Fable | 0.5 | — |
| **B** | degree discharge on real `runTable`: `symOutput_natDegree_le`, `handlePolys_natDegree_le` (reuse `GgmDegreeInvariant` helpers; add `natDegree_combine_le`) | `GgmDegreeDischarge.lean` | MECHANICAL | Fable | 0.5–1 | A |
| **C** | probability plumbing: `game_collapse` (c1) + `experiment_eq_count` (c2) via `probEvent_map`,`probEvent_uniformFin`, Binding idioms | `GgmProbThreading.lean` | MECHANICAL core / Opus glue | Opus (Fable-assist) | 1–2 | — (parallel to A,B) |
| **D** | ⚑ the embedding: `runEmbed`, `embed`, `embed_run_correspondence` (injectivity aligns real-eq ↔ eval-eq) | `GgmEmbed.lean` | **HARD** (design) | **Opus** | 2–4 | — (parallel; gates E) |
| **E** | compose: `tSdh_ggm_sound` (§1b) — glue A+B+C+D + `groupWinSet_eq_realWinSet` | `GgmEndToEnd.lean` | MECHANICAL glue | Opus | 0.5 | A,B,C,D |
| E-opt | conservative pairing-aware δ=2D variant (two-sorted G₁/Gₜ `runAux` ↔ `buildPaired` bridge) — **off critical path** | `GgmPairingVariant.lean` | HARD | Opus | 2–3 | (independent) |

**Parallelism.** A, C, D are independent and start immediately. B gates on A. E gates on all of
A,B,C,D. E-opt is entirely independent and optional (only if ember wants the stronger-adversary
claim — but note it is then *not* literally about ArkLib's `tSdhExperiment`, whose adversary cannot
pair). Critical path length ≈ D (2–4 days) since A+B (≤1.5) and C (≤2) finish under D's cover.

**Do NOT** hand D to a Fable with "mechanical" framing — the table↔polynomial invariant and the
opacity-preserving argument are the design core; a Fable will reconstruct a plausible interpreter
that is green against its own fixture and wrong against the SRS. Paste `runAux`, `srsSt`, `tower`,
`gpow_val_inj_iff`, and the correspondence *statement* into D's prompt verbatim.

---

## 4. ⚑ HONEST REACHABILITY

**Verdict: the full end-to-end theorem is REACHABLE in bounded effort (≈ 1 focused week), with
task D the single genuine residual risk.**

Every semantic gap has a discharging tool already in hand:

- the encoding gap (group ↔ field) is closed by **injectivity** — `gpow_val_inj_iff` is proven;
- the counting gap (ℚ-cardinality ↔ probability) is closed by **`probEvent_uniformFin` + `probEvent_map`**,
  which exist in VCVio, and `Binding.lean` is a *complete worked reduction in the identical game monad*
  (`OptionT.mk (do τ ← sampleNonzeroZMod; …)`), so the plumbing is precedented, not invented;
- the degree gap collapses once `Move.pair` is dropped (matching ArkLib's pairing-free adversary type).

None of these is a research problem. The **one hard piece is D** — the embedding's
`embed_run_correspondence`. It is *design-hard* (define `runEmbed` so its `DecidableEq` equality
branches thread a table↔polynomial invariant that injectivity collapses onto `realAns τ`), not
*open-hard*. If D proves thornier than the 2–4 day estimate, the honest fallback is coherent and
already a large win over today's four disconnected peers:

> **Coherent-up-to-one-named-gap:** state `tSdh_ggm_sound` with `embed_run_correspondence` as a
> single hypothesis (a `def`-shaped, precisely-typed lemma — *not* a `FooHard` carrier laundering an
> assumption). The whole argument — degree discharge, the counting core, the transport, the final
> assembly — is then wired through ONE socket with ONE honest gap, and that gap is **days, not
> weeks** (it is a concrete induction with injectivity doing the semantic work, not a missing theory).

That is the design goal: **one target theorem with at most one honest, precisely-named hypothesis is
coherent; four disconnected peer lemmas are not.** The random-encoding bound at δ = D is the exact
`~(q+D)²·D/p` Shoup socket; the pairing-aware δ = 2D bound is a conservative *extra*, not a
prerequisite, because ArkLib's `tSdhAdversary` cannot pair.

*(Minor optional extension, not on the critical path: `embed` is taken deterministic, matching
`Strat`. A fully general generic adversary with internal `ProbComp` coins averages the bound over its
coins — the bound holds pointwise per coin, so it lifts by `probEvent` convexity. Note once; do not
gate composition on it.)*
