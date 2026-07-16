# Candidate: EXTRACTION-SHAPED (the VCVio pattern)

**Model:** extraction / reduction. **Rests on:** *nothing* — the statement is an unconditional
reduction, true with no cryptographic assumption. **Gives a numeric bound:** **NO** (reduction
only, honestly). **Survives the exact attack:** **PROVEN** — mechanized, `sorry`-free,
axiom-clean. **Mechanizability:** **MECHANIZED** today.

This is the safe baseline the other candidates must beat *on the "gives a number" axis*. It
concedes the number and buys, in exchange, a statement that has literally nothing for
`Classical.choice` to inhabit — because it drops the universally-quantified assumption `Prop`
entirely and states only what ArkLib's reduction already constructs.

- **Artifact dir (scratch ArkLib copy):** `/private/tmp/arklib-extraction`
  (fresh `cp -r` of `/private/tmp/arklib-review`, ArkLib @ `d72f8392`, Lean `v4.31.0`).
- **Patch:** `candidates/extraction.patch` (full diff against ArkLib `Binding.lean`).
- **Survives-attack proof:** `candidates/RepairSurvives.lean` (`sorry`-free; the exact
  trapdoor attack and the repaired bounds coexist in one axiom closure).
- **Companion (the minimal split alone):** `../binding-repair.patch`, `../REPAIR.md`.

---

## 1. The statement — three layers, strongest first

The extraction repair is not one theorem; it is a ladder from the purest "solution as data"
fact up to the assumption-form corollary. Every rung is `sorry`-free against the real tree.
All names are in `ArkLib/Commitments/Functional/KZG/Binding.lean` (patched).

### Layer 0 — the algebraic extractor (already in ArkLib, a *total function* of the break)

```lean
lemma t_sdh_cond_of_two_valid_openings
    (τ query resp₁ resp₂ : ZMod p) (cm proof₁ proof₂ : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hresp : resp₁ ≠ resp₂) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hverify₁ : KZG.verifyOpening … srs.2 cm proof₁ query resp₁)
    (hverify₂ : KZG.verifyOpening … srs.2 cm proof₂ query resp₂) :
    Groups.tSdhCondition (g₁ := g₁)
      (τ, -query, (proof₁ / proof₂) ^ (1 / (resp₂ - resp₁)).val)
```

Two valid KZG openings of the same commitment at the same point to *different* values yield
the explicit group element `(proof₁ / proof₂) ^ (1/(resp₂ − resp₁))` as a `t`-SDH solution at
challenge `c = −query`. The witness is a **closed-form function** of the break. There is no
adversary, no probability, no assumption. This is the purest possible "as data".

### Layer 1 — the run-level extractor (the strongest form this candidate adds)

This is the **KZG analog of VCVio's `binding_win_implies_collision`** — the pattern the task
names ("`findCollision` returns the collision as data"). VCVio states, pointwise over the
support of its Merkle binding game:

```lean
∀ z ∈ support ((simulateQ cachingOracle (bindingInner A)).run ∅),
  z.1 = true → CacheHasCollision z.2          -- VCVio Examples/CommitmentScheme/Binding.lean
```

The mechanized KZG mirror added by this candidate is:

```lean
lemma bindingCondExt_yields_tSdhCondition [SampleableType G₁]
    (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    ∀ y ∈ support (bindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary (kzg …)),
      bindingCondExt (p := p) (n := n) y →
        Groups.tSdhCondition (g₁ := g₁) (mapBindingToTsdh (p := p) (n := n) y)
```

Read it exactly as the VCVio line: **on every concrete run where the binding adversary wins
(`bindingCondExt y`), the transformed transcript `mapBindingToTsdh y` *is* a valid `t`-SDH
solution.** The solution is present as data on that run. No `∀ efficient adversary`, no
assumption `Prop`, no expectation — a universally-true implication about concrete transcripts.

### Layer 2 — the probability bound (the reduction, expectation form)

```lean
theorem binding_reduces_to_tSdh (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    [SampleableType G₁] (AuxState : Type) (adversary : KzgBindingAdversary …) :
    Commitment.bindingExperiment … (kzg …) AuxState adversary
    ≤ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n (bindingReduction … AuxState adversary)
```

Every binding adversary *yields, as explicit data* — the reduction `bindingReduction …
adversary` — a `t`-SDH adversary whose success probability upper-bounds the binding
advantage. `binding_cond_le_t_sdh_cond` now derives from Layer 1 in one line
(`probEvent_mono (bindingCondExt_yields_tSdhCondition …)`), so the whole ladder is one proof.

### Layer 3 — the assumption-form corollary (backward compatibility only)

```lean
theorem binding (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁]
    (tSdhError : ℝ≥0) (htSdh : Groups.tSdhAssumption … n tSdhError) :
    Commitment.binding … (kzg …) tSdhError
```

Kept with its original signature so no downstream breaks. Its docstring now states plainly
that `tSdhAssumption … error` is false below `1` for an unrestricted class, so this corollary
is informative only once the assumption is restricted (AGM / q-DLOG — the other candidates).
**All non-vacuous content lives in Layers 0–2, which never mention `tSdhAssumption`.**

---

## 2. Survives the exact attack — PROVEN (not argued)

The disease was structural: `tSdhAssumption D error := ∀ (A : tSdhAdversary D), tSdhExperiment
D A ≤ error` bounds an *unrestricted* adversary type (`tSdhAdversary` lands in
`StateT unifSpec.QueryCache ProbComp`, a free monad — pure computation is free), so
`Classical.choice` inhabits `tauExtractingAdversary`: it reads `g₂^τ` out of the verifier SRS
leg, recovers `τ` via `Exists.choose` on ArkLib's own `exists_zmod_power_of_generator`, and
wins with probability `1`. Hence `tSdhAssumption … error` is false for every `error < 1`, and
the old `binding` (which took it as a hypothesis) was vacuous.

The extraction candidate **does not weaken the assumption** — it *removes the assumption from
the load-bearing statements*. Why that survives the attack, made precise and mechanized:

- **There is no object to inhabit.** Layers 0–2 contain no `∀ adversary … ≤ error` and no
  assumption `Prop`. Layer 1 is `∀ y ∈ support …, win y → tSdhCondition (map y)` — an
  unconditional implication about concrete data. `Classical.choice` produces *inhabitants of
  propositions*; a universally-quantified true implication has no "winner slot" to fill. The
  attack that emptied the old premise has nothing to attach to. This is categorically
  different from AGM/q-DLOG candidates, which *keep* a `∀ restricted-adversary` shape and must
  therefore prove `Classical.choice` can no longer *build* a winner in the restricted class.

- **The exact attack still fires, and the bound still holds, together.** The mechanized
  `repair_survives_attack` (`RepairSurvives.lean`) proves, for any prime-order pair and any
  nondegenerate pairing — the precise setting where the trapdoor adversary wins:

  ```lean
  theorem repair_survives_attack … (herr : (tSdhError : ℝ≥0∞) < 1) … :
      (¬ Groups.tSdhAssumption (g₁ := g₁) (g₂ := g₂) n tSdhError)
      ∧ (Commitment.bindingExperiment … (kzg …) AuxState adversary
          ≤ Groups.tSdhExperiment n (bindingReduction … AuxState adversary))
  ```

  Leg (1) is the identical `not_tSdhAssumption` that killed the original (`hpair` even
  *forces* the `g₂ ≠ 1` the attack needs). Leg (2) is the repaired reduction bound, taking no
  `tSdhAssumption` hypothesis. They hold **simultaneously, in the same groups, one axiom
  closure** — the disease ("premise unsatisfiable") is cured by removing the premise while
  keeping every ounce of the reduction.

- **The bound is content, not a dressed-up `≤ 1`.** Its RHS is `tSdhExperiment` of a
  *specific constructed* adversary, and the vacuity artifact's canary
  (`tSdhExperiment_givingUpAdversary = 0`) shows the experiment discriminates.

**Axiom check (all six, from `RepairSurvives.lean`, `#print axioms`):**

```
ArkLibRepairCheck.not_tSdhAssumption                    [propext, Classical.choice, Quot.sound]
ArkLibRepairCheck.repair_survives_attack                [propext, Classical.choice, Quot.sound]
KZG.CommitmentScheme.bindingCondExt_yields_tSdhCondition [propext, Classical.choice, Quot.sound]
KZG.CommitmentScheme.t_sdh_cond_of_two_valid_openings    [propext, Classical.choice, Quot.sound]
KZG.CommitmentScheme.binding_reduces_to_tSdh             [propext, Classical.choice, Quot.sound]
KZG.CommitmentScheme.binding                             [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. (The one `sorry` in `ArkLib/OracleReduction/Security/Basic.lean:555` is
pre-existing ArkLib and is **not** in any of these closures.) Full tree builds:
`lake build ArkLib.Commitments.Functional.KZG.Binding` → 2994 jobs, exit 0.

---

## 3. Numeric vs reduction — and what it rests on (no free lunch)

**Gives a numeric bound: NO.** Honestly. This candidate proves
`bindingAdvantage(A) ≤ tSdhSuccess(reduction A)` and, at Layer 1, "a break *is* a `t`-SDH
solution." It does **not** upper-bound `tSdhSuccess` by any function of the parameters. To get
a number you must bound the *reduction adversary's* own `t`-SDH success — which requires a
model or assumption this candidate deliberately does not adopt.

**Rests on: nothing.** The statements are unconditionally true. That is exactly why there is
nothing to falsify and nothing for `Classical.choice` to inhabit — and exactly why there is no
number. The no-free-lunch ledger is explicit: a numeric `t`-SDH bound must rest on an
idealized model (GGM / AGM-with-a-real-boundary) or a primitive assumption (q-DLOG / DLOG)
stated over a sound adversary class. This candidate buys attack-immunity by paying the number.
It is the **floor** the AGM and q-DLOG candidates must clear: they keep a `∀ restricted-A`
shape *in order to* deliver a number, and in exchange they take on the obligation this
candidate is free of — proving the restricted class cannot be inhabited by a free-data winner.

---

## 4. Invasiveness

Two composable pieces, both in the single file `Binding.lean`:

1. **The minimal split** (`../binding-repair.patch`, +41 / −14): split `binding`'s five-step
   calc at the last `≤`; the unconditional prefix becomes `binding_reduces_to_tSdh`, and
   `binding` shrinks to a two-line corollary. The four transition lemmas and the whole
   reduction are untouched.

2. **The strongest-form factor** (this candidate's addition): expose the pointwise core of
   `binding_cond_le_t_sdh_cond` as the named lemma `bindingCondExt_yields_tSdhCondition`, then
   derive `binding_cond_le_t_sdh_cond` from it via `probEvent_mono`. This is a pure
   refactor — the extracted proof body is verbatim the old `hmono`'s `probEvent_mono`
   argument; no proof step is invented, and `binding_cond_le_t_sdh_cond`'s statement is
   unchanged. `git diff --stat` reports 172 / 137 because git sees the moved proof body as
   delete+insert; the *semantic* delta is "one new named lemma, one 2-line corollary."

Full combined diff: `candidates/extraction.patch`. Whole tree green, axiom-clean, no new
imports, no new infrastructure (contrast AGM: new algebraic-adversary type + game/experiment
rewrite + reduction rework to emit representations).

---

## 5. Mechanizability — MECHANIZED, `sorry`-free today

Everything above compiled against ArkLib @ `d72f8392` (Lean `v4.31.0`) in
`/private/tmp/arklib-extraction`. Nothing is named-but-unproven; nothing is `sorry`. The
strongest "solution as data" statement (`bindingCondExt_yields_tSdhCondition`) is a first-class
theorem, not a docstring. This candidate is done, not months away.

What it is *not*: it is not a number. If the launch needs a concrete `t`-SDH advantage bound,
this candidate is the sound scaffolding on which a model-bearing candidate (GGM / q-DLOG)
supplies the missing `tSdhSuccess(reduction) ≤ f(params)` factor — this candidate has already
isolated that as the single remaining obligation.
