# ArkLib's `KZG.binding` is vacuous, via a false `tSdhAssumption`

> ## ⚖ ADVERSARIAL FACTCHECK — VERDICT: **CONFIRMED** (2026-07-16)
>
> An independent lane tried to **refute** this claim — the single biggest risk being that a
> prior factcheck attempt had been working against *placeholder* restatements of ArkLib's
> types, not the real library. **That risk is resolved: this builds against pristine upstream
> ArkLib.** Every axis checks out:
>
> - **(a) Real ArkLib, not a restatement.** `KzgVacuity.lean` `import`s
>   `ArkLib.Commitments.Functional.KZG.Binding` and uses `Groups.tSdhAssumption`,
>   `Groups.tSdhAdversary`, `Groups.exists_zmod_power_of_generator`, `Groups.sampleNonzeroZMod`
>   directly — no local `def` of any of them. Rebuilt from scratch by the factcheck lane against
>   a genuine checkout at **`d72f8392`** (`ArkLib.lean` root includes `KZG.Binding`; git working
>   tree of the checkout has **zero** modifications to tracked files — only the untracked
>   `Scratch/`), toolchain `v4.31.0`: `Built ArkLib.Scratch.KzgVacuity (23s)`,
>   `Build completed successfully (2995 jobs)`. The committed `KzgVacuity.lean` is **byte-identical**
>   to the one that built. `#print axioms` on every headline theorem **and on
>   `KZG.CommitmentScheme.binding` itself** → `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
> - **(b) `g₂ ≠ 1` is FORCED by `binding`'s own `hpair`, not assumed.** The real `pairing` is
>   `(Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ)` (genuinely `ZMod p`-bilinear);
>   `map_zero` gives `pairing g₁ 1 = 0`, so `hpair : pairing g₁ g₂ ≠ 0 ⇒ g₂ ≠ 1`. Mechanized in
>   `g₂_ne_one_of_pairing_ne_zero`, whose hypothesis is defeq to `binding`'s real `hpair`.
> - **(c) `tSdhAssumption` genuinely is `binding`'s assumption.** Exactly **one** `tSdhAssumption`
>   exists (`HardnessAssumptions.lean:88`, unrestricted); `binding` (`Binding.lean:745`) consumes it
>   directly. **No** query-bounded / AGM / restricted variant exists. `IsQueryBound` appears in
>   ArkLib only in **one commented-out line**.
> - **(d) Probability exactly 1 is genuine.** `not_tSdhAssumption` / `tSdhExperiment_..Adversary`
>   are sorry-free; the giving-up canary proves the experiment is not constantly 1. The extracting
>   adversary is a legal `noncomputable` inhabitant — the type carries **no** computability /
>   measurability / query side-condition.
> - **(e) `binding` is NOT WIP-labelled.** It is an exported theorem in the `ArkLib.lean` root, with
>   a finished module docstring and no TODO/experimental marker (the blueprint's `% TODO: add KZG`
>   is about *documentation*, not code status).
> - **(f) Codex, deputized independently** (its own separate ArkLib checkout, even building a
>   `binding_of_one_le` proof of the `error ≥ 1` triviality): **"NO FLAW — the claim holds."**
>
> **THE WEAKEST LINK** an ArkLib maintainer attacks first is **not** a correctness gap — it is
> *severity/novelty framing*: "this is the generic standard-model phenomenon — *any* computational
> assumption written `∀ A, adv A ≤ ε` with no resource bound on the adversary *type* is Lean-false
> via `Classical.choice`; `tSdhAssumption` is a stand-in for the informal assumption and the
> reduction in `Binding.lean` is the real content." That objection does not touch the mechanized
> fact (the exported theorem *is* sorry-free and *is* vacuous), and this writeup already concedes it
> squarely ("a formalization gap, not a break of KZG or t-SDH; nothing in `Binding.lean` needs
> discarding"). The framing below is fair. **Nothing filed; nothing published — ember's call.**

**Status:** mechanized, `sorry`-free, axiom-clean. **Not disclosed.** Publication is ember's call.

**Target:** [ArkLib](https://github.com/Verified-zkEVM/ArkLib) @ `d72f8392ff03047dc5386f4f4bb513743e7ada65`
(2026-07-15), `ArkLib/Commitments/Functional/KZG/`. Toolchain `leanprover/lean4:v4.31.0`.

**Artifact:** [`arklib-kzg-vacuity/KzgVacuity.lean`](arklib-kzg-vacuity/KzgVacuity.lean) —
reproduction instructions at the end. **Draft disclosure:**
[`arklib-kzg-vacuity/DISCLOSURE-DRAFT.md`](arklib-kzg-vacuity/DISCLOSURE-DRAFT.md), unfiled.

---

## The claim, precisely

ArkLib's `Groups.tSdhAssumption` is **false at every parameter where it says anything**, and
`KZG.CommitmentScheme.binding` — which assumes it — therefore has **no content at any parameter**.
Both are `sorry`-free. The whole KZG directory is `sorry`-free. It is green, careful, and empty.

This is a **formalization gap, not a break of KZG and not a break of t-SDH.** Deployed KZG is
fine. The t-SDH assumption, as cryptographers state it, is fine. What is broken is the Lean
*statement* of t-SDH: it quantifies over an adversary class so large that it contains an
adversary who already knows the trapdoor. Nothing about the real assumption is impugned. The
bug is in the quantifier, not the cryptography.

## The definitions (quoted, unedited)

`ArkLib/Commitments/Functional/KZG/HardnessAssumptions.lean:53`:

```lean
/-- A `t`-SDH adversary returns a challenge offset and a group element upon receiving the SRS. -/
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

/-- t-SDH condition for an adversary to win. -/
abbrev tSdhCondition {g₁ : G₁} : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) =>
    τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val
```

`:70` — the game samples the trapdoor as private setup randomness and hands the adversary only
the public SRS, from an empty query cache:

```lean
abbrev tSdhGame [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) :
    OptionT ProbComp (ZMod p × ZMod p × G₁) :=
  OptionT.mk (do
    let τ ← sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun ((c, h) : ZMod p × G₁) => (τ, c, h))))
```

`:88` — the assumption:

```lean
/-- The `t`-SDH assumption bounds every adversary's success probability by `error`. -/
def tSdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)),
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)
```

`Binding.lean:743` — the consumer:

```lean
theorem binding {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (tSdhError : ℝ≥0)
    (htSdh : Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁)
      (g₂ := g₂) n tSdhError) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) tSdhError
```

## The argument

**1. The adversary type is unconstrained where it counts.** `tSdhAdversary` is *not* a bare Lean
function — it lands in `StateT unifSpec.QueryCache ProbComp`, a monadic computation. But
`ProbComp` is a **free monad over queries**: `pure` is a constructor, and nothing charges for
what happens underneath it. `tSdhAssumption` imposes **no query bound and no cost model** on the
adversary — `IsQueryBoundP` appears nowhere in ArkLib except one commented-out line in an
unrelated file. So `pure (some (0, <anything whatsoever>))` is a legal adversary at zero cost.

> This is the one place the informal version of this diagnosis gets it wrong, and it matters for
> a fair writeup: the type is *not* "a bare function with no oracle". It is a real monadic
> computation. The defect is subtler — the monad tracks queries, and the adversary makes none.

**2. The SRS determines τ, and the discrete log is choice-definable.** This is the crux, and
ArkLib **proves the necessary lemma itself**, in `Algebra.lean:105`:

```lean
/-- Every element of a prime-order group is a `ZMod p` power of a nontrivial generator. -/
lemma exists_zmod_power_of_generator {g : G} (hpG : Nat.card G = p) (hg : g ≠ 1)
    (hord : orderOf g = p) (x : G) : ∃ a : ZMod p, x = g ^ a.val
```

`Exists.choose` applied to this **is** the discrete logarithm. It is noncomputable; it is not an
algorithm; it is a perfectly legal inhabitant of `ZMod p`. `PrimeOrderWith G p` carries
`hCard : Nat.card G = p`, and `orderOf_eq_prime_of_ne_one` (`Algebra.lean:61`) supplies `hord`
from `g ≠ 1`. **The crux is verified, and it discharges out of the target library's own API.**

**3. Which generator?** The SRS is `(g₁, g₁^τ, …, g₁^(τ^D)), (g₂, g₂^τ)`. The G₂ leg carries
`g₂^τ` at **every** degree `D` (`Vector G₂ 2`), so it is the robust extraction site — the G₁ leg
would need `D ≥ 1`. This needs `g₂ ≠ 1`.

**4. `binding`'s own hypothesis supplies it.** The pairing is `ZMod p`-**bilinear**:

```lean
(pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
```

so `pairing g₁ 1 = 0` by `map_zero`. Hence `hpair : pairing g₁ g₂ ≠ 0` **forces `g₂ ≠ 1`**
(and `g₁ ≠ 1`, making `hg₁` redundant). This is the sharp form of the result:

> **The very pairing nondegeneracy `binding` needs to run its reduction is what makes its t-SDH
> premise false.** `binding`'s two hypotheses are *jointly unsatisfiable* for any `tSdhError < 1`.

**5. Probability 1.** The adversary returns `(c, h) = (0, g₁^(1/τ).val)`. The win condition needs
`τ + 0 ≠ 0` — and `sampleNonzeroZMod` samples from `1, …, p-1`, so `τ ≠ 0` on the whole support —
and `h = g₁^(1/(τ+0)).val`, which is `rfl` after `add_zero`. The game never fails. So
`tSdhExperiment = 1`.

**6. No content at any parameter.** For `error < 1`: `tSdhAssumption` is **false**, so `binding`
proves nothing. For `error ≥ 1`: `tSdhAssumption` is **trivially true** (a probability is `≤ 1`),
but then `binding`'s conclusion `Commitment.binding … tSdhError` is *also* trivially true for the
same reason. Either the premise is false or the conclusion is free. **There is no parameter at
which `binding` transports information.**

## The mechanization

`sorry`-free, and axiom-clean modulo the three Lean standard axioms — `Classical.choice` is not
a leak here, it is the *content*:

```
'ArkLibVacuity.not_tSdhAssumption'             depends on axioms: [propext, Classical.choice, Quot.sound]
'ArkLibVacuity.binding_hypotheses_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArkLibVacuity.experiment_discriminates'       depends on axioms: [propext, Classical.choice, Quot.sound]
'KZG.CommitmentScheme.binding'                 depends on axioms: [propext, Classical.choice, Quot.sound]
```

ArkLib and VCVio *do* carry `sorry`s elsewhere (`ArkLib/Data/Fin/Basic.lean:307`,
`VCVio/CryptoFoundations/…`); the axiom check confirms **none of them are under this refutation**,
and none are under `binding` either. The target is genuinely green.

The headline theorems:

```lean
/-- The winning adversary. Reads `g₂ ^ τ` out of the *verifier* leg of the SRS, recovers `τ`
by `Classical.choice`, returns the t-SDH solution at offset `c = 0`. ZERO oracle queries. -/
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf (p := p) hg₂ srs.2[1]).val))

theorem tSdhExperiment_tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (tauExtractingAdversary … hg₂ D) = 1

/-- ArkLib's `tSdhAssumption` is FALSE for every error bound `< 1`, at every degree `D`,
in every prime-order group pair with a nontrivial `g₂`. Not asymptotic: no hypothesis on `p`. -/
theorem not_tSdhAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error

/-- `binding`'s hypotheses are jointly unsatisfiable at every meaningful error. -/
theorem binding_hypotheses_unsatisfiable
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0)
    (n : ℕ) (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n tSdhError
```

**Canary** (a gate that accepts everything is a broken gate). `tSdhExperiment` is not *constantly*
`1` — an adversary that gives up loses with probability 1, so the probability-1 theorem is a
statement about the exhibited adversary and not an artifact of the probability machinery:

```lean
theorem tSdhExperiment_givingUpAdversary (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (givingUpAdversary … D) = 0

theorem experiment_discriminates (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment … (givingUpAdversary … D)
    ≠ Groups.tSdhExperiment … (tauExtractingAdversary … hg₂ D)
```

`arsdhAssumption` (`HardnessAssumptions.lean:125`) has the identical shape and is almost
certainly refutable the same way; **we have not mechanized that** and do not claim it.

## What this does and does not mean

**Does not mean:**
- KZG is broken. It is not. This says nothing about the scheme.
- t-SDH is broken. It is not. This says nothing about the assumption as cryptographers state it.
- ArkLib is sloppy work. It is careful work — the proofs are real, the reduction in `Binding.lean`
  is a genuine reduction, the algebra is correct, and the file that kills the assumption is
  ArkLib's own. The reduction would be *sound and valuable* the moment the assumption is stated
  with a query bound. Nothing in `Binding.lean` needs to be thrown away.
- Anything is exploitable. There is no attack here. There is a quantifier.

**Does mean:**
- `KZG.binding` currently transports no information, at any parameter.
- Any downstream consumer of `tSdhAssumption` inherits this.
- A `#print axioms`-clean, `sorry`-free theorem can still be empty. **`#print axioms` is blind to
  hypotheses.** `binding` is axiom-clean *and* vacuous, simultaneously, and neither check catches
  the other.

## The fix

**Query-bound the adversary.** The escape is real and it is narrow: `OracleComp` is a free monad,
so pure computation is free, and the *only* resource it tracks is queries. Bound that resource and
`Classical.choice` is excluded — not by fiat, but because a choice-defined adversary would have to
know a value it never asked for.

**ArkLib already depends on the machinery.** `VCVio/OracleComp/QueryTracking/QueryBound.lean:227`
defines `IsQueryBoundP`, and `VCVio/OracleComp/QueryTracking/CostModel.lean:66` defines
`CostModel.queryCost` — costing **per oracle query only, with no time model underneath**. VCVio's
own `IdenticalUntilBad` results consume `IsQueryBoundP` for real. The fix is an import away.

The shape:

```lean
def tSdhAssumption … (D : ℕ) (Q : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D …),
    IsQueryBoundP (adversary srs) … Q →        -- ← the missing quantifier restriction
      tSdhExperiment … D adversary ≤ (error : ℝ≥0∞)
```

A caveat we owe the reader, and it is not small: **query-bounding is sound for random-oracle and
hash-based statements, and does essentially nothing for an algebraic assumption like t-SDH**,
whose adversaries make no oracle calls at all. For t-SDH the honest options are the generic/
algebraic group model (where the adversary is a *tracked* linear combination, not a function), or
an extraction-shaped statement where the floor becomes **data** — an object the adversary must
*produce*, with nothing left to falsify. The general PPT formalization is a known-hard open
problem, not an oversight: EasyCrypt built the only real adversarial-cost judgement
(eprint 2021/156) and **deleted it** in 2024 (`41c2667f`, −10,091 lines, "barely used"). Mathlib's
`TM2ComputableInPolyTime` is deterministic and its only witness is the identity function.

We are not handing ArkLib a cheap fix. We are handing them a correct diagnosis and the honest
menu.

## The general lesson — and our own identical hole

**This is the same hole we found in our own floors, which is the only framing that makes this a
field lesson rather than a dunk.** In `metatheory/Dregg2/Crypto/`:

- `FloorGames.lean` — `hard_top_iff_solvableFrac_negl`: for **any** game,
  `Hard G ⊤ ↔ Negl (solvableFrac G)`. At the unrestricted adversary class **a game floor *is* the
  existence floor — `Classical.choice` is the adversary.** No restatement of the win relation
  escapes, because the ↔ is an ↔. This refuted *our own* prescribed repair:
  `collisionResistant_false_of_compressing` proves the pattern we had called "the correct pattern
  already in the tree" is FALSE at deployed parameters, by pigeonhole, one `Classical.choice`
  later.
- `FriWeightingTransfer.lean` — `coCurvilinearity_unconstrained_is_vacuous`: a hypothesis
  quantified `∃v` over arbitrary words with the real constraint only in a docstring aside, so
  `v := u` proved it outright.
- `FriArityTransfer.lean` — `arity8FiberBoundNaive_false`: a named "open obligation" that was not
  open but *false*, refuted by the constant map.
- `RomQueryFloor.lean` — **the repair, and it is the same repair we are recommending here.**
  `RomEff` restricts to adversaries factoring through a query-bounded tree;
  `choiceAdv_not_romEff` **proves** `Classical.choice`'s adversary is excluded;
  `birthday_bound` then proves the floor unconditionally. `binaryRom_top_false` vs
  `binaryRom_hard_linear_budget`: **same game, same win relation, two adversary classes, opposite
  verdicts.** That is what it means for the adversary class to do real work.

The lesson, stated once: **a hardness assumption written as `∀ (A : <type>), advantage A ≤ ε` is
an assumption about `<type>`, and if `<type>` is not restricted, the assumption is a statement
about `Classical.choice` and is false.** `#assert_axioms` / `#print axioms` will never tell you.
The only test that finds it is: **try to prove your own floor false at deployed parameters.**
Hardness quantifies over *efficient adversaries*; a floor that quantifies over *solutions* is
empty, because the solutions exist.

The premier Lean ZK-crypto library has the identical hole. We are not uniquely sloppy. **We just
went looking.**

## Reproduction

```bash
git clone https://github.com/Verified-zkEVM/ArkLib.git && cd ArkLib
git checkout d72f8392ff03047dc5386f4f4bb513743e7ada65
lake exe cache get
mkdir -p ArkLib/Scratch
cp <this-repo>/docs/reference/arklib-kzg-vacuity/KzgVacuity.lean ArkLib/Scratch/
lake build ArkLib.Scratch.KzgVacuity          # green, no sorry
echo 'import ArkLib.Scratch.KzgVacuity
#print axioms ArkLibVacuity.not_tSdhAssumption' > /tmp/ax.lean
lake env lean /tmp/ax.lean                    # [propext, Classical.choice, Quot.sound]
```

The file is **not** part of our lake build and ArkLib is **not** a dregg dependency; it is a
disclosure artifact, reproducible against ArkLib read-only.

## Disclosure

**Nothing has been filed.** ArkLib is Ethereum-Foundation-adjacent (verified-zkevm.org); the
courteous route is an issue or PR on their repo, not a paper drop. A draft issue is at
[`arklib-kzg-vacuity/DISCLOSURE-DRAFT.md`](arklib-kzg-vacuity/DISCLOSURE-DRAFT.md).
It is ember's call whether, when, and in what form any of this goes out.
