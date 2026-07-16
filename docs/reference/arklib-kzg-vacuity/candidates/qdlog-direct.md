# Candidate: direct q-DLOG / DLOG reduction with a sound adversary class

**Candidate name:** `qdlog-direct`
**Status:** the *naive* form is **mechanized BROKEN** (`sorry`-free); the *sound* form is
**ARGUED-survives**, not mechanized, and rests on the Generic Group Model.
**Scratch tree:** `/private/tmp/arklib-ember` (ArkLib @ `d72f8392`, Lean `v4.31.0`, `.lake`
shared read-only with `/private/tmp/arklib-review`).
**Artifact:** `KzgQDlogVacuity.lean` (this directory; built copy in the scratch tree).

---

## 0. The candidate, and the one-line verdict

> *Instead of assuming t-SDH, reduce KZG binding directly to q-strong-DLOG (or DLOG),
> stated with a soundly-restricted adversary class, to get a number to falsify.*

**Verdict.** The reduction half is free — ArkLib already builds it (`bindingReduction`), and
the extraction-shaped split (candidate `(B)` in `../REPAIR.md`) already exposes it as
`binding_reduces_to_tSdh`. But the *assumption* half does **not** escape the vacuity by
switching t-SDH → q-DLOG. A q-DLOG assumption stated in ArkLib's own idiom — recover the SRS
trapdoor `τ` from the KZG power-SRS, with the **same unrestricted adversary type** — is **also
false for every error `< 1`**, by the **identical** `Classical.choice` trapdoor-extraction.
I **mechanized** this: `not_qDlogAssumption`, `sorry`-free. So the candidate, taken literally,
**collapses to "you must fix the base assumption first."**

The base assumption *can* be fixed — but only by an idealized model (GGM) or a genuinely
computational adversary class, and **that is where the number comes from.** There is no free
lunch: the number rests on the GGM ideal model, not on the word "q-DLOG".

---

## 1. What the tree actually contains (source-verified @ `d72f8392`)

- **ArkLib has no DLOG or q-DLOG assumption.** `HardnessAssumptions.lean` defines exactly two
  assumptions — `tSdhAssumption` and `arsdhAssumption` — both with the unrestricted adversary
  type `… → StateT unifSpec.QueryCache ProbComp (Option _)`. Both are the ones the vacuity
  work already refuted.
- **VCVio has a DLog *experiment* and reductions, but never a `∀ adversary ≤ error` DLog
  *assumption*.** `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean` defines
  `DLogAdversary F G := G → G → ProbComp F`, `dlogExp`, and the standard
  DLog→CDH→DDH reductions — all stated **per-adversary** (e.g.
  `dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction : Pr[dlogExp …]^2 ≤ Pr[cdhExp …]`). It never
  writes `∀ adversary, dlogExp g adversary ≤ error`. `HardRelation.lean` likewise defines only
  `hardRelationExp` (a per-adversary experiment), no universally-quantified hardness `Prop`.
  This is the same reduction-shaped dodge as candidate `(B)`: **nothing for `Classical.choice`
  to inhabit, but also no number.**
- **`ProbComp := OracleComp unifSpec`** — a free monad. Pure computation, including
  `Classical.choice`, is uncharged. This is the exact property that makes every
  unrestricted-adversary hardness `Prop` false.

**Finding (the task asked for it explicitly):** *if* one writes down the q-DLOG assumption the
candidate needs — the natural target of "reduce binding to q-DLOG" — in ArkLib's idiom, it has
**the same hole**. Mechanized below.

---

## 2. The statement, and the mechanized refutation of its naive form

The natural base assumption for "reduce KZG binding to q-DLOG" is **q-strong-DLOG**: given the
KZG power-SRS `(g₁, g₁^τ, …, g₁^(τ^D)), (g₂, g₂^τ)`, recover `τ`. In ArkLib's idiom
(`KzgQDlogVacuity.lean`):

```lean
abbrev qDlogAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 → StateT unifSpec.QueryCache ProbComp (Option (ZMod p))

abbrev qDlogCondition : (ZMod p × ZMod p) → Prop := fun (τ, τ') => τ' = τ

def qDlogAssumption {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : qDlogAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D),
    qDlogExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)
```

The winning adversary reads `g₂^τ` from the verifier leg of the SRS, recovers `τ` by
`Exists.choose` on ArkLib's own `exists_zmod_power_of_generator`, and **returns it** — even
simpler than the t-SDH attack (the win condition is literally `τ' = τ`; no `1/(τ+c)` needed):

```lean
noncomputable def trapdoorAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) : qDlogAdversary … D :=
  fun srs => pure (some (dlogOf (p := p) hg₂ srs.2[1]))   -- srs.2[1] = g₂^(τ.val)

theorem qDlogExperiment_trapdoorAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    qDlogExperiment … D (trapdoorAdversary … hg₂ D) = 1        -- wins w.p. 1

theorem not_qDlogAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ qDlogAssumption … D error                               -- FALSE below 1
```

Builds `sorry`-free against ArkLib @ `d72f8392`. Axiom audit:

```
not_qDlogAssumption                depends on axioms: [propext, Classical.choice, Quot.sound]
qDlogExperiment_trapdoorAdversary  depends on axioms: [propext, Classical.choice, Quot.sound]
qDlogExperiment_givingUpAdversary  depends on axioms: [propext, Classical.choice, Quot.sound]  (canary = 0)
qDlogAssumption_trivial_of_one_le  depends on axioms: [propext, Classical.choice, Quot.sound]
```

A canary (`qDlogExperiment_givingUpAdversary = 0` and `experiment_discriminates`) rules out a
degenerate "everything wins" experiment. So **the candidate's own base assumption fails the gate
the candidate was supposed to pass** — a judge (`Classical.choice`) still inhabits a winner.
This is not a defect of *q-DLOG*; it is the general fact (the project's "prove the floor false"
principle): a hardness `Prop` of the form `∀ (pure-function adversary), Pr[solve hard-instance]
≤ ε` is **false for any `ε < 1`**, because the mathematical solution *exists* (the discrete log
exists) and `Classical.choice` hands it over free. DLOG vs q-DLOG makes no difference.

---

## 3. The sound form, and whether it survives the exact attack

To make the base assumption non-vacuous you must remove the free-computation escape hatch. The
task's menu (query-bounding is **wrong** here — the winning adversary makes **zero** oracle
queries; all its work is under `pure`) leaves exactly two sound options, and both cost a real
model.

### 3a. ArkLib already has *partial* GGM/AGM scaffolding — and it is, as written, still unsound

`ArkLib/AGM/Basic.lean` (in the build, `import`ed by `ArkLib.lean`; **not** referenced by any
assumption) defines a would-be algebraic/generic adversary:

```lean
def Adversary (ι G : Type) (p bitLength : ℕ) (α : Type) : Type _ :=
  ReaderT (GroupValTable ι G)
    (OracleComp (GroupOpOracle ι + GroupExpOracle ι p + GroupEqOracle ι + GroupEncodeOracle ι bitLength))
    (List ι × α)
def Adversary.run (adversary …) (table : GroupValTable ι G) : List G × α := sorry
```

Two problems, both fatal to using it *today* as the sound base:

1. **`Adversary.run` is `sorry`.** No experiment/assumption can be evaluated over this adversary
   yet, so there is nothing to reduce KZG binding *to*.
2. **As written it does not block the exact attack.** The adversary receives the *real*
   `GroupValTable ι G` (the actual `G`-elements) through `ReaderT`, and `GroupExpOracle` lets it
   raise a stored element to **any** exponent `a : ZMod p`. So a `Classical.choice` adversary
   reads `g₂^τ` out of the table, computes `a = 1/τ` (or `τ` itself) by `Exists.choose`, and
   calls the exp oracle to place `g₁^(1/τ)` at a handle it then outputs. The extraction survives.
   The file's own author flags exactly this in a trailing comment:
   *"How to make the adversary truly independent of the group description? It could have had `G`
   hardwired."* — that is this hole, named.

So **ArkLib's current AGM scaffolding shares the disease** (a `Classical.choice` adversary that
sees the `G`-table can still inhabit a winner), on top of being unfinished (`run = sorry`).
Finding, recorded.

### 3b. What a *sound* GGM q-DLOG looks like, and why it survives (ARGUED)

The standard generic group model closes the hole structurally:

- The adversary is given **only handles** (indices `ι` into a hidden table) to the SRS elements,
  plus an **encoding oracle** returning **opaque labels** (`BitVec bitLength` / random
  encodings). It **never receives `GroupValTable ι G`** — the actual `G`-values live only inside
  the oracle's `StateT` and are invisible to the adversary. (Concretely: drop the
  `ReaderT (GroupValTable ι G)` environment; hand the adversary an initial `List ι` of handles.)
- **Why the exact attack can no longer inhabit a winner (the gate):** the refutation used
  `dlogOf := (exists_zmod_power_of_generator … x).choose`, which needs an actual group element
  `x : G`. In the sound GGM adversary there is **no `x : G` in scope** — the adversary holds
  `ι`-handles and `BitVec` labels, and there is **no lemma `∃ a, (handle) = g^a`** over the
  opaque handle/label type (an abstract encoding set with no exposed `PrimeOrderWith` structure).
  `Exists.choose` has nothing to chew on. To win, the adversary must produce a *handle* whose
  hidden table value equals the target `g₁^(1/(τ+c))`; it can only populate handles via
  op/exp/eq queries on the SRS handles, i.e. with values whose exponents lie in the *polynomial
  span of `1, τ, …, τ^D`* it can symbolically form. `1/(τ+c)` is a rational function outside that
  span. This is the point where the free-computation escape hatch is genuinely gone.
- **The number (Shoup / Boneh–Boyen):** by lazy-sampling the encoding and Schwartz–Zippel over
  the private `τ`, a GGM adversary making at most `q` oracle queries against a degree-`D` SRS
  wins q-DLOG / t-SDH with probability at most

  > `advantage ≤ (q + D + 2)² · D / (2·p)`   (standard SDH-in-GGM bound; Boneh–Boyen'04, Shoup'97)

  — a **real number to falsify**, monotone in `q, D`, negligible for `p ≈ 2²⁵⁶` and polynomial
  `q, D`. This bound is what "reduce to q-DLOG **soundly**" actually buys, and it **rests on the
  GGM ideal model**, not on the assumption's name.

Survives-attack status: **ARGUED**, not mechanized. The structural block (no `G` in scope ⇒
`dlogOf` un-constructible) is a genuine, checkable change of the adversary type; but "the attack
term no longer typechecks" is a meta-statement, not a Lean theorem. The mechanizable *positive*
content is **Shoup's lemma itself** (the numeric bound holds), which is months of new
infrastructure (see §5).

### 3c. Reduction-only, no model (for completeness)

If one refuses any ideal model, the honest statement is the **reduction bound** with the q-DLOG
*advantage of the specific reduction adversary* left symbolic:
`bindingExperiment(adv) ≤ qDlogExperiment(qdlogReduction adv)`. This is exactly candidate `(B)`
re-pointed from t-SDH to q-DLOG — **no number, nothing to falsify** — and adds nothing over the
`(B)` patch already written. It does *not* satisfy this candidate's "give a number" premise.

---

## 4. No free lunch — what each variant rests on

| Variant | Gives a number? | Rests on | Survives the exact attack |
|---|---|---|---|
| naive q-DLOG (unrestricted adversary) | yes, but **false** (`≤ ε<1` refuted) | nothing | **BROKEN** (mechanized: `not_qDlogAssumption`) |
| q-DLOG over ArkLib's current `AGM.Adversary` | no (`run = sorry`) | — | **BROKEN** (sees `G`-table; `run` unfinished) |
| q-DLOG in a **sound GGM** | **yes** — `(q+D+2)²·D/(2p)` | **GGM ideal model** | **ARGUED-survives** (structural, not mechanized) |
| reduction-only (no model) | **no** | DLOG assumption, symbolic | n/a — reduces to candidate `(B)` |

The number exists **only** in the GGM row, and it is a GGM number. This is the no-free-lunch
law made concrete: the moment you demand a falsifiable bound, you are inside an idealized model.

---

## 5. Invasiveness & mechanizability

- **Naive-refutation artifact (done):** `KzgQDlogVacuity.lean`, ~200 lines, `sorry`-free,
  builds against ArkLib @ `d72f8392`. Standalone scratch file (mirrors `../KzgVacuity.lean`);
  touches nothing in the ArkLib tree.
- **Sound GGM version (MONTHS-AWAY):** requires
  (1) finishing `AGM.Adversary.run` **soundly** — and first *redesigning* the adversary so it
  does **not** receive `GroupValTable ι G` (remove the `ReaderT` environment; hand it handles +
  encode-oracle only), fixing the hole the author flagged;
  (2) a lazily-sampled encoding oracle with the Schwartz–Zippel bookkeeping (VCVio has no
  generic-group master theorem; `HardRelation.lean` is per-adversary only);
  (3) stating q-DLOG (and t-SDH) over the sound GGM adversary and proving **Shoup's lemma**
  (the `(q+D+2)²·D/(2p)` bound);
  (4) re-pointing `bindingReduction` at the GGM q-DLOG adversary (mostly `(B)`'s split, but the
  reduction must now thread handles, not `G`-elements).
  None of (1)–(3) exists in ArkLib/VCVio today. This is a research-grade mechanization, not a
  drive-by patch.

## 6. Recommendation

Ship the `(B)` extraction-shaped patch now (it is the sound, mergeable, no-number step and it
already isolates the exact obligation). Record `qdlog-direct` as: **the number, if you want one,
must come from a *completed and hardened* GGM** — ArkLib's `AGM/Basic.lean` is the right seed but
is (a) `run = sorry` and (b) unsound as written (adversary sees the `G`-table). The mechanized
`not_qDlogAssumption` in this directory is the standing proof that **swapping t-SDH for q-DLOG
without a model changes nothing** — the base assumption is equally, provably vacuous.
