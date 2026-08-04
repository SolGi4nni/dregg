# SHOUP-PLAN — the random-encoding GGM as a second track

**Goal.** Add the **Shoup random-encoding** generic-group model as a second, first-class track
alongside the existing **Maurer explicit-equality** track (`GgmAdaptive` → `GgmEmbed` →
`GgmEndToEnd`), so the contribution covers *both* standard GGM formulations, and the
"random-encoding / Shoup" name becomes a **proved theorem** instead of a mislabel that commit
`e125c3308` (codex critical pass) correctly forced us to retract from the docstrings.

**Design only.** No proofs are written here beyond tiny type-sketches used to confirm a socket
compiles by eye. No deploys. Nothing filed externally.

---

## 0. The key insight, verified

> The existing all-pairs bound
> `GgmRandomEncoding.rand_encoding_bound_D = (C(n,2)·D + (D+1))/(p−1)` counts **all** handle pairs.
> That is exactly the Shoup bound: a random-encoding adversary compares every encoding it holds
> for free, so every pair is a live collision candidate. In Maurer the all-pairs count is a sound
> **over**-count of the true (queried-pairs) bad event; in Shoup it is **tight**.

Verified against the source:

* `GgmRandomEncoding.card_pairRootUnion_le` (lines 121–143) bounds the union, over **all
  unordered pairs** of a handle set `ps`, of `roots(q₁−q₂)` by `C(#ps,2)·Δ`. It quantifies over
  `ps.offDiag` re-indexed through `Sym2` — every pair, not a transcript. This is the crown-jewel
  reusable lemma.
* `GgmRandomEncoding.badSet_subset_pairRootUnion` (lines 339–353) proves Maurer's per-query
  `badSet` (built from `symPairs` = *actually `Move.query`-ed* pairs, of which there are ≤ `fuel`)
  is a **subset** of `pairRootUnion(handlePolys …)`. So in Maurer the all-pairs count is a strict
  over-count — the tighter true bound is `GgmAdaptive.card_realWinSet_le`'s `fuel·Δ + (D+1)`.
* In Shoup, free comparison makes the adversary's view depend on the equality pattern of **all**
  held handles, so the leak (view depends on τ) happens on **exactly** `pairRootUnion(handlePolys)`
  — no `⊆` slack to remove, because the adversary really can compare any pair. The all-pairs count
  is the *right* count, and the Shoup composition consumes `card_pairRootUnion_le_D` **directly**,
  with no `badSet` indirection.

Consequence for effort: the Shoup **bound** is the existing all-pairs number; the Shoup **numerator
is byte-identical** to `rand_encoding_bound_srs_D`. What is genuinely new is the **model** (the
free-comparison oracle + adversary type) and the **hybrid** (identical-until-collision over all
pairs). The Schwartz–Zippel machine is reused verbatim.

---

## 1. THE MODEL — precisely

### 1.1 The random encoding

Group elements are represented by encodings. Two equivalent formalizations; we adopt (B) because it
collapses onto the existing polynomial machinery with zero new algebra.

* **(A) Abstract-encoding form (narrative).** An encoding type `E` with `[DecidableEq E]` and an
  **injection** `σ : ZMod p ↪ E` (Shoup's lazily-sampled injective encoding; injectivity is the
  only load-bearing property). The adversary receives `List E` (encodings of its handles), a
  group-op oracle `add : E → E → E` with `σ a ⊕ σ b = σ (a+b)`, and — crucially — it may test
  equality of *any two* encodings it holds via `DecidableEq E`, for free. It cannot apply `σ⁻¹`
  (σ is not in its scope), so it never recovers a field value.

* **(B) Polynomial realization (what we mechanize).** Handles are formal polynomials in
  `(ZMod p)[X]` (as in `GgmAdaptive`). The encoding of handle `f` at trapdoor τ is `σ (f.eval τ)`.
  Because `σ` is **injective**, the equality pattern the adversary observes,
  `σ(fᵢ(τ)) = σ(fⱼ(τ)) ⟺ fᵢ(τ) = fⱼ(τ)`, is exactly the **eval-at-τ** pattern — i.e.
  `GgmAdaptive.realAns τ`. The symbolic (τ-independent) pattern is formal equality
  `GgmAdaptive.symAns`. So `σ` need never appear in the mechanization: injectivity folds it away,
  exactly as `GgmArkLibTransport.gpow_val_inj_iff` folds the concrete encoding `a ↦ g^a.val` away
  in the Maurer embed. `E` and `σ` live only in the docstring, where they name the model.

The two answer functions are **reused verbatim** from `GgmAdaptive`:

```lean
noncomputable def symAns   : AnswerFn p := fun f g => decide (f = g)            -- formal equality
noncomputable def realAns (τ : ZMod p) : AnswerFn p := fun f g => decide (f.eval τ = g.eval τ)
```

### 1.2 Free comparison — the crux distinction from Maurer

This is *the* difference between the two models, and it must be formalized exactly.

* **Maurer (existing).** `Strat p := List Bool → Move p ⊕ (ZMod p × ℕ)` and `Move` carries a
  `query : ℕ → ℕ → Move` constructor. The adversary must **spend a step** to test one pair; its
  input history is the list of single boolean answers to the pairs it chose to query. Only queried
  pairs enter `badPolys`/`badSet` (≤ `fuel` of them).

* **Shoup (new).** Comparison is **ambient and free**: at every step the adversary observes the
  **full equality pattern** (the partition induced by encoding-equality) of *all* the handles it
  currently holds, at no fuel and no handle cost. It branches on that entire pattern. Formally, the
  observation at a table is the pairwise-equality matrix under the oracle:

  ```lean
  /-- The free-comparison observation: the |tbl|×|tbl| equality matrix under the oracle `ans`.
      Packaged with its dimension so successive (growing) observations have a uniform type. -/
  def eqPattern (ans : AnswerFn p) (tbl : List ((ZMod p)[X])) : Σ n : ℕ, (Fin n → Fin n → Bool) :=
    ⟨tbl.length, fun i j => ans (tbl.get i) (tbl.get j)⟩

  /-- A Shoup (random-encoding) strategy: decides on the *history of full equality patterns*
      observed so far — never on a chosen single query. There is no `query` move: equality is
      ambient. `lin` is the only oracle-consuming move. -/
  abbrev ShoupStrat (p : ℕ) := List (Σ n : ℕ, (Fin n → Fin n → Bool)) → ShoupMove p ⊕ (ZMod p × ℕ)

  inductive ShoupMove (p : ℕ) where
    | lin : List (ZMod p × ℕ) → ShoupMove p          -- group-op: append Σ cᵢ · handleᵢ
  ```

  Equivalently one may keep `Move` and simply never expose `query`; the pattern-history typing is
  the honest, self-documenting form. The pairing-free discipline is inherited: `lin` is the only
  move, so — as in Maurer — every handle stays a `ZMod p`-linear combination of the seed, degree ≤ D
  (respecting ArkLib's G₁-only, pairing-free `tSdhAdversary`; the encoding oracle grants exactly the
  operations the real interface grants — `add` on G₁, no `e : G₁×G₂ → Gₜ`).

### 1.3 The run and the game

```lean
/-- The Shoup run. Each step: observe the current table's full equality pattern under `ans`,
    append it to the pattern-history, let `strat` decide. `lin` appends a `combine`; output
    reads out `(offset, table.getD k 0)`. Mirrors `runAux` but threads *patterns*, not booleans. -/
noncomputable def runShoup (ans : AnswerFn p) (strat : ShoupStrat p) :
    ℕ → ShSt p → (ZMod p × (ZMod p)[X])
  | 0, _ => (0, 0)
  | fuel + 1, st =>
    let obs := eqPattern ans st.table                     -- FREE full-table comparison
    match strat (st.phist ++ [obs]) with
    | Sum.inr (c, k) => (c, st.table.getD k 0)
    | Sum.inl (ShoupMove.lin spec) =>
        runShoup ans strat fuel ⟨st.table ++ [combine spec st.table], st.phist ++ [obs]⟩

/-- Trapdoors on which the free-comparison adversary wins t-SDH against the *real* encoding
    oracle. Same τ+c≠0-guarded win predicate reused verbatim from the static/Maurer files. -/
noncomputable def realWinSetShoup (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) :
    Finset (ZMod p) :=
  nonzeroPoints.filter (fun τ =>
    τ + (runShoup (realAns τ) strat fuel st₀).1 ≠ 0 ∧
      (runShoup (realAns τ) strat fuel st₀).2.eval τ
        = 1 / (τ + (runShoup (realAns τ) strat fuel st₀).1))

noncomputable def shoupExperiment (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) : ℚ :=
  (realWinSetShoup strat st₀ fuel).card / (p - 1)
```

**Win condition.** Identical to Maurer/static: produce a handle whose realized encoding is
`σ(1/(τ+c))` for the committed offset `c` — i.e. the committed output polynomial `f` satisfies
`f(τ) = 1/(τ+c)` with `τ+c ≠ 0`. Via `GgmArkLibTransport.tSdhCondition_iff_field` this is exactly
ArkLib's `tSdhCondition (τ, c, g₁^(f τ).val)`.

**Note on the `Σ`-typed history.** `eqPattern` returns a `Σ n, Fin n → Fin n → Bool` so growing
tables have a uniform observation type. The only fact the coupling proof needs is
`eqPattern (realAns τ) tbl = eqPattern symAns tbl` when `tbl` has no colliding pair — a single
`Sigma.ext` + funext. No decidable-equality-of-functions or heavy `Fin` bookkeeping is required for
the *coupling*; it is only needed if one later wants `DecidableEq` on the history (not needed for
the counting bound, which is classical throughout — same idiom as `GgmAdaptive`).

---

## 2. THE HYBRID — identical-until-collision, over all pairs

Shoup's identical-until-bad, stated for the free-comparison model.

**Lemma (pattern agreement off the all-pairs bad set).** For every table `tbl` all of whose
entries lie in a handle set `H` with `τ ∉ pairRootUnion H`,
`eqPattern (realAns τ) tbl = eqPattern symAns tbl`. Proof: entrywise,
`realAns τ fᵢ fⱼ = symAns fᵢ fⱼ` because distinct `fᵢ, fⱼ ∈ H` do not collide at τ
(τ not a root of `fᵢ−fⱼ`), and equal ones agree trivially. This is `realAns_agree_off_badSet`
(GgmAdaptive lines 253–276) **generalized from queried pairs to all pairs of `H`** — strictly
simpler, since it is a uniform statement about `H`, not tied to a transcript.

**Lemma (identical-until-bad, the crux).**
```lean
theorem runShoup_congr_off_bad (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) {τ : ZMod p}
    (hτ : τ ∉ pairRootUnion (handleSetShoup strat st₀ fuel)) :
    runShoup (realAns τ) strat fuel st₀ = runShoup symAns strat fuel st₀
```
Proof shape: induction on `fuel`, mirroring `runAux_congr_of_agree` (GgmAdaptive lines 142–192).
At each step both runs observe the same table (they are in lockstep so far); by the pattern-agreement
lemma the two observations are **equal** (every reachable table ⊆ the final handle set, so
non-collision on the final set covers it), hence `strat` makes the same decision, and the recursion
continues in lockstep. The single global hypothesis `τ ∉ pairRootUnion(handleSet)` discharges every
step's agreement — this is the free-comparison analogue of "agree on every queried pair", and it is
*why the bad event is all-pairs*.

**Corollary (set-level identical-until-bad).**
```lean
theorem realWinSetShoup_subset (strat : ShoupStrat p) (st₀ : ShSt p) (fuel D : ℕ)
    (hdeg_out : (runShoup symAns strat fuel st₀).2.natDegree ≤ D) :
    realWinSetShoup strat st₀ fuel ⊆
      pairRootUnion (handleSetShoup strat st₀ fuel)
        ∪ GgmCandidate.winningPoints ⟨(runShoup symAns …).1, (runShoup symAns …).2, hdeg_out⟩
```
This is `GgmAdaptive.realWinSet_subset` (lines 301–317) with the bad set already **equal to**
`pairRootUnion(handleSet)` — no `badSet_subset_pairRootUnion` step is needed, because there is no
`badSet` in this model; the all-pairs union is primitive.

---

## 3. THE BOUND — compose

`Pr[win] ≤ Pr[bad] + Pr[symbolic win]`:

* `Pr[bad] = pairRootUnion(handleSet).card / (p−1) ≤ C(n,2)·D / (p−1)` — **REUSE**
  `card_pairRootUnion_le_D` (GgmRandomEncoding lines 466–469) verbatim, with the degree hypothesis
  `∀ q ∈ handleSet, q.natDegree ≤ D` discharged by the degree-discharge machinery (§4).
* `Pr[symbolic win] ≤ (D+1)/(p−1)` — **REUSE** `GgmCandidate.card_winningPoints_le` (the static
  Boneh–Boyen root event) verbatim.
* Sum + `n = fuel + D + 4` at the SRS seeding (from `card_handlePolys_le` / `srsSt_table_length`,
  reused) ⇒ numerator `C(fuel+D+4,2)·D + (D+1)`, **byte-identical to `rand_encoding_bound_srs_D`**.

```lean
theorem card_realWinSetShoup_le (strat : ShoupStrat p) (st₀ : ShSt p) (fuel D n : ℕ)
    (hdeg_out : (runShoup symAns strat fuel st₀).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handleSetShoup strat st₀ fuel, q.natDegree ≤ D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    (realWinSetShoup strat st₀ fuel).card ≤ n.choose 2 * D + (D + 1)
-- proof = card_union_le ∘ [card_pairRootUnion_le_D ; card_winningPoints_le], Nat.choose monotone
```

Which existing lemmas plug in: `card_pairRootUnion_le_D`, `card_winningPoints_le`,
`card_handlePolys_le`, `srsSt_table_length`, `Nat.choose_le_choose`, and the ℚ-division wrapper
identical to `rand_encoding_bound_D`'s tail (lines 507–520). What the **new composition** needs:
only `realWinSetShoup_subset` (the corollary of the new hybrid) in place of `realWinSet_subset` —
one substitution — plus the trivial "bad set = pairRootUnion" equality (definitional here).

---

## 4. REUSE vs NEW — the honest ledger

**REUSED verbatim (no re-derivation):**

| item | file · lemma |
|---|---|
| all-pairs Schwartz–Zippel core | `GgmRandomEncoding.card_pairRootUnion_le` / `_le_D` |
| static Boneh–Boyen root event | `GgmCandidate.card_winningPoints_le` |
| handle-set size bound `n = fuel+D+4` | `GgmRandomEncoding.card_handlePolys_le`, `srsSt_table_length` |
| degree discharge δ=D (handles + output) | `GgmDegreeDischarge.runTable_natDegree_le`, `handlePolys_natDegree_le`, `runAux_output_natDegree_le`, `srsSt_table_natDegree_le` (see note) |
| injectivity transport → ArkLib condition | `GgmArkLibTransport.gpow_val_inj_iff`, `tSdhCondition_iff_field`, `groupWinSet_eq_realWinSet` |
| probability threading (game→count) | `Ggm.ProbThreading.game_collapse`, `experiment_eq_count`, `probEvent_optionT_mk`, `probEvent_sampleNonzeroZMod` — **fully adversary-agnostic** (generic over `resultOf`/`A`) |
| win predicate, `nonzeroPoints`, `GenericAdversary` | `GgmCandidate` / `GgmAdaptive` |
| ℚ/ℝ≥0∞ non-vacuity `< 1` wrappers | pattern of `rand_encoding_bound_lt_one`, `tSdh_ggm_sound_lt_one` |

**Genuinely NEW:**

1. **The free-comparison model** — `eqPattern`, `ShoupMove` (`lin`-only), `ShoupStrat`
   (pattern-history), `ShSt`, `runShoup`, `shoupExperiment`. *New but small; mechanical shape.*
2. **The identical-until-collision-over-all-pairs hybrid** — `runShoup_congr_off_bad` and its
   pattern-agreement lemma + `realWinSetShoup_subset`. *This is the intellectual content of the
   track; it is where "free comparison ⇒ all pairs live" is proved.*
3. **The Shoup handle-table siblings** — a `runTableShoup`/`handleSetShoup` and their size/degree
   lemmas. *Mechanical: same recursion as `runTable`, different strategy type. Two options:*
   (a) copy the four structural lemmas (`table_prefix`, `length_le`, `pairs_mem`, degree) with the
   `ShoupStrat` recursion; or (b) **refactor** the table recursion to be parametric in the decision
   source so Maurer and Shoup literally share `runTable` (the table only grows on `lin`, whose spec
   is answer-independent). (a) is faster to land; (b) is cleaner and the right long-term move.
4. **The game/experiment + target theorem** — `shoup_ggm_sound` and `shoup_ggm_sound_lt_one`.
5. **(Optional, Tier 2)** `embedShoup` into ArkLib's `tSdhAdversary` + its correspondence (see §5).

Effort verdict: (1),(3),(4) are mechanical (Fable-appropriate); (2) is the one Opus piece; (5) is
optional and the heaviest if pursued.

**Degree-discharge note.** `GgmDegreeDischarge`'s lemmas are stated over `runTable ans strat`
(Maurer strat type). Under refactor (3b) they apply to the shared table verbatim; under (3a) they
need `ShoupStrat` siblings — a copy-paste of ~4 inductions with the strategy branch swapped. Either
way the *mathematics* (linear combos stay ≤ D, `natDegree_sub_le` is a max) is untouched.

---

## 5. CONNECTION to ArkLib — the crux for scope

**Verdict: two-tier, ship Tier 1.**

* **Tier 1 (primary deliverable) — standalone random-encoding GGM theorem.** `shoup_ggm_sound` is a
  self-contained theorem about the abstract encoding game (`runShoup` against `realAns τ`, scored by
  the field-level win predicate). This is what makes "we proved the Shoup model" **true**, and it is
  the honest home for the all-pairs bound. It does not touch ArkLib's `tSdhExperiment`. Reachable in
  days.

* **Tier 2 (optional) — wire Shoup into ArkLib's `tSdhExperiment`, like the Maurer capstone.**
  **This is feasible.** The reason the Maurer `embed` works is that in a prime-order group the
  encoding `a ↦ g₁^a.val` is *injective* (`gpow_val_inj_iff`), so **real group equality on realized
  handles = eval-at-τ equality = `realAns τ`**. That injective encoding *is* a (deterministic)
  random-encoding, and in the concrete group **comparison genuinely is free** — the adversary holds
  the elements and `DecidableEq G₁` costs nothing. So a free-comparison Shoup adversary embeds as a
  bona-fide `tSdhAdversary` that group-multiplies handles and compares any pair via `DecidableEq`.
  Concretely: `embedShoup : ShoupStrat → tSdhAdversary D` whose `runEmbedShoup` computes, at each
  step, the full `groupEq`-pattern of its realized `List G₁` handle table and threads the same
  `Inv` (`tableGᵢ = g₁^(tableᵢ.eval τ).val`) as `GgmEmbed.runEmbedAux`. The correspondence
  `runEmbedShoup = runShoup (realAns τ)` uses `gpow_val_inj_iff` **entrywise on the pattern** — the
  identical mechanism as `GgmEmbed.runEmbedAux_correspondence`, one dimension richer (a matrix per
  step instead of one bool). Everything downstream is **reused verbatim and is adversary-agnostic**:
  `experiment_eq_count`, `game_collapse`, and `winIndex_card_le` depend only on
  "deterministic-given-τ from empty cache" + a `realWinSet`-shaped set, both of which
  `embedShoup`/`realWinSetShoup` supply. Only `stratResultShoup`, `embedShoup_det`, and the
  pattern-correspondence are new; each is a near-mechanical clone of its `GgmEmbed`/`GgmEndToEnd`
  counterpart.

**So: is the Shoup result *necessarily* about the abstract encoding game?** No — it embeds into
ArkLib's concrete experiment exactly as Maurer does, because the concrete group's injective encoding
realizes free comparison faithfully. **But it need not be wired**, and the honest recommendation is:

> **The Maurer track is the one wired to ArkLib's `tSdhExperiment` (via `embed`/`tSdh_ggm_sound`).
> The Shoup track ships as the standard random-encoding GGM theorem over the encoding model
> (`shoup_ggm_sound`), sharing the all-pairs Schwartz–Zippel core. It *can* be wired to ArkLib by
> the same injective-encoding correspondence (`embedShoup`), at the cost of equality-pattern
> bookkeeping — but doing so adds no new hardness guarantee about ArkLib's experiment beyond what
> Maurer already delivers (the two embedded classes realize the same `g₁^(f τ)` outputs and the same
> t-SDH win set; Shoup's all-pairs bad set is the over-count Maurer already pays as a bound).**

This keeps the contribution honest: two standard GGM models proved, one wiring to the real ArkLib
experiment (Maurer), with the Shoup→ArkLib wiring available but marked optional/redundant-for-value.

---

## 6. TARGET THEOREM + BUILD PLAN + TRACTABILITY

### 6.1 The single Shoup target theorem (Tier 1)

```lean
/-- **The random-encoding (Shoup) GGM t-SDH bound.** Every free-comparison generic strategy — one
    that observes, at each step and for free, the full equality pattern of all its held encodings —
    wins t-SDH against the real encoding oracle on at most a (C(fuel+D+4,2)·D + (D+1))/(p−1)
    fraction of trapdoors: the all-pairs collision event (now TIGHT, because comparison is free)
    plus the static Boneh–Boyen root event. Same numerator as `rand_encoding_bound_srs_D`; the
    difference is the model in which it is proved. -/
theorem shoup_ggm_sound (strat : ShoupStrat p) (fuel D : ℕ) (hD : 1 ≤ D) (hp : 2 ≤ p) :
    shoupExperiment strat (srsSt D) fuel
      ≤ (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1)

theorem shoup_ggm_sound_lt_one (strat : ShoupStrat p) (fuel D : ℕ) (hD : 1 ≤ D) (hp : 2 ≤ p)
    (hreg : (fuel + D + 4).choose 2 * D + (D + 1) < p - 1) :
    shoupExperiment strat (srsSt D) fuel < 1
```

(If Tier 2 is pursued, the capstone is `tSdhExperiment D (embedShoup …) ≤ …`, byte-identical RHS to
`tSdh_ggm_sound`.)

### 6.2 Dependency-ordered task plan

New file under `candidates/`: **`GgmRandomEncodingShoup`** (Tier 1), importing `GgmRandomEncoding`,
`GgmDegreeDischarge`, `GgmCandidate`. Optional **`GgmEmbedShoup`** +
`GgmShoupEndToEnd` (Tier 2), importing `GgmEmbed`, `GgmProbThreading`.

*(These name modules that do not exist yet — this section is the task plan, not a citation.
Written as bare module names, matching the convention the rest of this file already uses, so
the doc-reference gate is not asked to resolve a path nobody has written.)*

| # | task | new file · def/thm | worker | effort | depends on |
|---|---|---|---|---|---|
| S1 | model: `eqPattern`, `ShoupMove`, `ShoupStrat`, `ShSt`, `runShoup`, `shoupExperiment`, `realWinSetShoup` | GgmRandomEncodingShoup §1 | Fable | ~0.5 d | — |
| S2 | Shoup table siblings `runTableShoup`/`handleSetShoup` + size lemmas (or refactor 3b to share `runTable`) | §2 | Fable | ~0.5 d | S1 |
| S3 | degree discharge for `handleSetShoup`/output (siblings or shared) | §2 | Fable | ~0.5 d | S2, `GgmDegreeDischarge` |
| **S4** | **pattern-agreement lemma + `runShoup_congr_off_bad` (identical-until-collision, all pairs)** | §3 | **Opus** | **1–3 d** | S1, S2 |
| S5 | `realWinSetShoup_subset` (set-level hybrid) | §3 | Opus | ~0.5 d | S4 |
| S6 | `card_realWinSetShoup_le` + `shoup_ggm_sound` + `_lt_one` (compose reused lemmas) | §4 | Fable | ~0.5 d | S3, S5, `card_pairRootUnion_le_D`, `card_winningPoints_le` |
| S7 | docstrings: state the model precisely, cite the retraction in `e125c3308`, mark all-pairs TIGHT here | all | Fable | ~0.25 d | S6 |
| — | **Tier 2 (optional)** ↓ | | | | |
| T1 | `embedShoup`, `runEmbedShoup`, pattern `Inv`, `stratResultShoup` | GgmEmbedShoup | Opus | 1–2 d | S1, `GgmEmbed` |
| T2 | `runEmbedShoup_correspondence` (pattern lockstep via `gpow_val_inj_iff`) | GgmEmbedShoup | **Opus** | **2–4 d** | T1, S4 |
| T3 | `embedShoup_det` + capstone `tSdh_shoup_ggm_sound` (reuse `experiment_eq_count`, `winIndex_card_le`) | GgmShoupEndToEnd | Fable/Opus | ~1 d | T2, `GgmProbThreading` |

### 6.3 Honest reachability

* **Tier 1 alone: days.** ~2.5–4 focused days. The only non-mechanical piece is S4; everything else
  is either reused verbatim or a shape-copy of an existing induction. This is the deliverable that
  makes "both standard GGM models" true, and it is **bounded, not research-scale** — no new
  metatheory, no missing Mathlib/VCVio infrastructure (unlike the *original* full-adaptive-GGM
  estimate in `ggm.md §6`, which predated the all-pairs machinery now in hand).
* **Tier 1 + Tier 2: ~1.5–2.5 weeks.** T2 (the equality-pattern correspondence in the group) is the
  heaviest single item — one dimension richer than `GgmEmbed`'s bool correspondence.

### 6.4 The single hardest piece

**S4 — `runShoup_congr_off_bad`, the free-comparison identical-until-bad.** It is where the model's
defining feature (free, all-pairs comparison) meets the proof: discharging **step-wise full-pattern
agreement** from the **single global** hypothesis `τ ∉ pairRootUnion(handleSet)`, threaded through
the fuel induction. It is the Shoup analogue of `runAux_congr_of_agree`, but the branching input is a
whole equality matrix rather than one boolean — so the induction must carry "every reachable table's
pattern agrees" and reduce it to non-collision on the final handle set (via `table ⊆ runTable`). It
is HARD (Opus) but **bounded** — a known-shape induction over already-built lemmas, not new
mathematics. (If Tier 2 is pursued, T2 is comparably hard for the same reason, in the group.)

Nothing in the plan is research-scale. The all-pairs Schwartz–Zippel bound — the part that *would*
have been research-scale — already exists (`card_pairRootUnion_le`), which is exactly why the Shoup
track is now a days-scale add rather than the "months-away" item `ggm.md` once flagged.
