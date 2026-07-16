# DRAFT — not filed. Publication is ember's call.

Intended venue: an issue on https://github.com/Verified-zkEVM/ArkLib.
Not a security advisory: there is no vulnerability, no embargo, and nothing exploitable.
This is a formalization-soundness report about a Lean statement.

Suggested title: **`tSdhAssumption` is false for `error < 1`, making `KZG.binding` vacuous**

Suggested labels: `bug`, `security-definitions`

---

## Body

Hi — we've been running an adversarial audit on the hardness floors in our own Lean
tree, and applied the same tooth to ArkLib. The result reproduces against
`d72f8392ff03047dc5386f4f4bb513743e7ada65`, so we wanted to bring it to you directly
rather than write it up anywhere else first.

**Summary:** `Groups.tSdhAssumption` is false for every `error < 1`, and trivially true
for `error ≥ 1`. Since `KZG.CommitmentScheme.binding` takes it as a hypothesis and
concludes a bound at the same `error`, `binding` carries no information at any parameter.
Everything below is `sorry`-free and depends only on `propext, Classical.choice, Quot.sound`.

To be clear up front about what this is not: **this is not a break of KZG or of t-SDH.**
The scheme is fine, the assumption as normally stated is fine, and the reduction in
`Binding.lean` is a real reduction that we think becomes sound and valuable as soon as the
assumption is stated with a restricted adversary class. Nothing in `Binding.lean` needs to
be discarded. The issue is the quantifier in `tSdhAssumption`, not the cryptography.

We should also say plainly: **we found the identical hole in our own floors first**, in
several places, and one of the things that makes it hard to see is that
`#print axioms` is completely blind to it. `binding` is axiom-clean *and* vacuous at the
same time.

### The problem

`tSdhAssumption` quantifies over `tSdhAdversary` with no restriction:

```lean
def tSdhAssumption … (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D …),
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)
```

`tSdhAdversary` lands in `StateT unifSpec.QueryCache ProbComp`, which is a real monadic
computation — but `ProbComp` is a free monad over queries, so **pure computation is free**,
and no query bound is imposed. An adversary may therefore `pure` an arbitrary noncomputable
function of the SRS at zero cost.

The SRS `(g₁, g₁^τ, …), (g₂, g₂^τ)` determines `τ` whenever `g₂ ≠ 1`, and — this is the
part we want to flag as a compliment rather than a criticism — **the lemma that makes the
discrete log choice-definable is already in ArkLib**, `Algebra.lean:105`:

```lean
lemma exists_zmod_power_of_generator {g : G} (hpG : Nat.card G = p) (hg : g ≠ 1)
    (hord : orderOf g = p) (x : G) : ∃ a : ZMod p, x = g ^ a.val
```

`Exists.choose` on that is the trapdoor. So:

```lean
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf (p := p) hg₂ srs.2[1]).val))

theorem tSdhExperiment_tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary … hg₂ D) = 1

theorem not_tSdhAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0)
    (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption … D error
```

It wins with probability exactly 1: `sampleNonzeroZMod` guarantees `τ ≠ 0` on the whole
support, so the offset `c = 0` satisfies `τ + c ≠ 0`, and `h = g₁^(1/(τ+0)).val` holds by
`add_zero`. It makes zero oracle queries.

### Why `binding` cannot dodge it

`binding` carries `hpair : pairing g₁ g₂ ≠ 0`. Since `pairing` is `ZMod p`-bilinear,
`pairing g₁ 1 = 0` by `map_zero`, so `hpair` **forces `g₂ ≠ 1`** — exactly the hypothesis
the adversary above needs. (It also forces `g₁ ≠ 1`, so `hg₁` looks redundant.)

```lean
theorem binding_hypotheses_unsatisfiable
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0)
    (n : ℕ) (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption … n tSdhError
```

So `binding`'s hypotheses are jointly unsatisfiable for `tSdhError < 1`; and for
`tSdhError ≥ 1` its conclusion is already trivial, because a probability is `≤ 1`. Either
the premise is false or the conclusion is free.

We also included a canary, since a probability-1 theorem is worth distrusting:
`tSdhExperiment_givingUpAdversary` proves an adversary that returns `none` has experiment
`0`, so the experiment does discriminate and the result above isn't an artifact of the
`probEvent` machinery.

`arsdhAssumption` has the same shape and we'd expect it to be refutable identically, but we
have not mechanized that and aren't claiming it.

### Suggested fix

Restrict the adversary class. The good news is that the machinery is already in your
dependency tree — `VCVio/OracleComp/QueryTracking/QueryBound.lean:227` has `IsQueryBoundP`,
`CostModel.lean:66` has `queryCost` (per-query, no time model underneath), and VCVio's own
`IdenticalUntilBad` lemmas consume `IsQueryBoundP` for real:

```lean
def tSdhAssumption … (D : ℕ) (Q : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D …),
    IsQueryBoundP (adversary srs) … Q →
      tSdhExperiment … D adversary ≤ (error : ℝ≥0∞)
```

But we don't want to oversell that, because **query-bounding is the right tool for
random-oracle/hash-based statements and does almost nothing for an algebraic assumption
like t-SDH**, whose adversaries make no oracle queries at all. For t-SDH specifically the
honest options look like: the generic/algebraic group model (the adversary becomes a
tracked linear combination rather than an arbitrary function), or an extraction-shaped
statement where the assumption becomes *data* the adversary must produce, leaving nothing
to falsify. A general PPT restriction seems genuinely hard rather than merely undone —
EasyCrypt built the only real adversarial-cost judgement we know of (eprint 2021/156) and
deleted it in 2024 as "barely used".

We'd be glad to send a PR for whichever direction you prefer, or to just leave this here if
you'd rather take it yourselves.

### Reproduction

Attached: `KzgVacuity.lean`. Drop into `ArkLib/Scratch/`, then:

```bash
lake build ArkLib.Scratch.KzgVacuity
# green, no sorry
# #print axioms ArkLibVacuity.not_tSdhAssumption
#   → [propext, Classical.choice, Quot.sound]
```

Thanks for ArkLib — the reduction in `Binding.lean` is careful work and the algebra is
right, which is precisely why we think the fix is worth making rather than working around.
