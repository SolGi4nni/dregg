# Vacuity and Repair: the Generic-Group Security of KZG Evaluation Binding, from a Mechanized Formalization-Soundness Finding

**Draft — not filed, not submitted, not a security advisory.** This is an internal working paper. It
concerns a *formalization-soundness* issue in a public, in-development library, not a vulnerability in
any deployed system. KZG, the t-SDH assumption, and the reduction in question are all sound as normally
stated; the issue is a Lean quantifier. Nothing here is embargoed and nothing is exploitable.

**Scope.** All Lean claims are mechanized against the Ethereum Foundation's ArkLib at revision
`d72f8392ff03047dc5386f4f4bb513743e7ada65` (Lean `v4.31.0`), verified by two independent checkers. All
cryptographic bounds are stated with, and checked against, their primary sources; where a statement is
argued on paper but not yet mechanized, it is labelled a *formalization frontier* and the missing
primitives are named. `#assert_axioms`-clean is not hypothesis-free, and we say so wherever it matters.

---

## Abstract

We report a mechanized formalization-soundness finding in the Ethereum Foundation's ArkLib and deliver
the honest fix its statement lacks. ArkLib's `KZG.CommitmentScheme.binding` — evaluation binding for the
KZG polynomial commitment — is stated as a conditional on the `t`-SDH assumption
`Groups.tSdhAssumption`, but that assumption quantifies over an *unrestricted* adversary type. Because
the underlying probabilistic-computation monad charges nothing for pure computation, a `Classical.choice`
adversary reads the trapdoor `τ` out of the verifier leg of the structured reference string, recovers it,
and wins with probability exactly `1`. Hence `tSdhAssumption D error` is **false for every `error < 1`**
and trivially true for `error ≥ 1`, so `binding` — and, identically, `function_binding` via the sibling
ARSDH assumption — carries no information at any parameter. This is `sorry`-free in Lean and depends only
on `[propext, Classical.choice, Quot.sound]`; `#print axioms` is blind to the vacuity, which coexists
with a perfectly clean axiom closure. We found the identical pattern in our own hardness floors first;
we present it as a field lesson, not a dunk.

We then give the honest repair in two layers. The immediate, mergeable de-vacuation is an
*extraction-shaped* restatement, `binding_reduces_to_tSdh`, that removes the vacuous premise while keeping
every step of ArkLib's real reduction; it is mechanized, `sorry`-free, and provably survives the exact
attack that empties the original (`repair_survives_attack`). The sound numeric grounding is the
classical generic-bilinear-group-model (GGM) bound: modelling group elements as opaque handles carrying
*ordinary* polynomials in the trapdoor indeterminate `X` (**not Laurent** — group inversion negates the
exponent, it does not introduce `X⁻¹`, and this is exactly why a winning `1/(X+c)` output is
unrepresentable and forces a bounded-degree root event), a simulation theorem plus Schwartz–Zippel yield
Boneh–Boyen's bound `ε ≤ (q_G + D + 3)²(D + 1)/(p − 1) = O((q_G + D)²·D / p)` — a `q`-type,
degree-dependent bound, **not** a clean `q²/p`. We give the full argument, verified line by line against
Boneh–Boyen's own Theorem 12. Finally, we are scrupulous about the mechanization boundary. Three things
are `sorry`-free in Lean today: the vacuity refutation, the reduction repair, and — new in this
revision — the *static* generic-group numeric survives-attack bound, `ε ≤ (D + 1)/(p − 1) < 1`, proved
by Schwartz–Zippel over the entire committed-generic (zero-group-operation-query) adversary class. What
remains a named formalization frontier is the **full adaptive** model: the opaque symbolic simulation
under `q` adaptive equality queries, whose collision term lifts the static number to the
`(q_G + D + 3)²(D + 1)/(p − 1)` shape. As far as our census of ArkLib and its dependencies could
determine, no generic-group-model security *theorem* previously existed in Lean — ArkLib's own
`AGM/Basic.lean` is a `sorry` stub with zero theorems, and is moreover *unsound as written* (its
adversary is a `ReaderT` over the concrete group table, so it can read discrete logs) — so the static
bound here is, to our knowledge, the first mechanized generic-group security statement of its kind, and
the adaptive development this paper specifies would complete it.

---

## 1. Introduction

The KZG polynomial commitment [KZG10] is one of the load-bearing primitives of modern succinct-argument
systems. Its evaluation-binding property — an adversary cannot open one commitment at one point to two
different values — is what a verifier relies on, and it is proved by reduction to the `t`-Strong
Diffie–Hellman (`t`-SDH) assumption in a bilinear group [BB04, BB08, KZG10]. The Ethereum Foundation's
ArkLib is a Lean 4 library formalizing the building blocks of such arguments; it contains a careful,
correct mechanization of exactly this reduction, in
`ArkLib/Commitments/Functional/KZG/Binding.lean`.

While running an adversarial audit of the hardness *floors* in our own Lean tree — the practice of trying
to *prove each cryptographic floor false at its deployed parameters*, rather than merely checking it is
axiom-clean — we applied the same tooth to ArkLib and found that its `t`-SDH assumption, as stated, is
vacuously false. This paper is the honest, finished treatment of that finding: the mechanized refutation,
the general methodological lesson, the mergeable repair, and the sound numeric grounding the repair
points at, presented as the completed generic-group theorem rather than a menu of options.

### 1.1 The finding, in one paragraph

`Groups.tSdhAssumption D error` is `∀ (adversary : tSdhAdversary D), tSdhExperiment … adversary ≤ error`.
The adversary type is a plain function into `StateT unifSpec.QueryCache ProbComp`. `ProbComp` is a *free
monad* over oracle queries, so pure computation is free and no resource bound is imposed anywhere. An
adversary may therefore `pure` an arbitrary noncomputable function of the SRS at zero cost. ArkLib's SRS
includes the verifier leg `(g₂, g₂^τ)`, which determines `τ` whenever `g₂ ≠ 1`; and ArkLib's own
`Algebra.lean:105 exists_zmod_power_of_generator` makes the discrete logarithm `Classical.choice`-definable.
So the adversary recovers `τ`, returns the `t`-SDH solution `(c = 0, g₁^{1/τ})`, and wins with
probability exactly `1`. Consequently `tSdhAssumption … error` is false for every `error < 1`; and for
`error ≥ 1` its conclusion is the triviality "a probability is `≤ 1`." `binding` takes `tSdhAssumption`
as a hypothesis and concludes a bound at the same `error`, so it says nothing at any parameter. The
sibling ARSDH assumption (`Groups.arsdhAssumption`), which powers `KZG.function_binding`, has the
identical unrestricted quantifier and falls the identical way.

### 1.2 Why this is worth a paper, and what is novel

The finding is small to state and (once seen) elementary; its value is threefold.

1. **The vacuity result and its methodological lesson (ours, mechanized).** The precise reason
   `∀ (unrestricted adversary), adv ≤ ε` is inhabited-false for an *algebraic* assumption, and — the part
   that makes it a genuine trap rather than a typo — the fact that `#print axioms` is **completely blind**
   to it: `binding` is axiom-clean *and* vacuous simultaneously. We found the same pattern in our own
   floors first; the lesson is general and it is the reason we treat this as a shared discipline problem.

2. **The honest fix, finished.** Not a menu. An immediate, mechanized, mergeable de-vacuation (the
   extraction-shaped `binding_reduces_to_tSdh`, which provably survives the exact attack), plus the sound
   numeric grounding — the generic-group bound — written out as a complete theorem with its argument
   verified against Boneh–Boyen. Handing a finished cryptosystem treatment is better than handing a list
   of options: KZG's generic-group security is public, classical mathematics, and the honest form of the
   fix is to state it correctly and completely.

3. **A mechanized static generic-group security bound — the first in Lean (as far as our census found).**
   ArkLib's own `AGM/Basic.lean` is a work-in-progress stub — its adversary's `run` function is literally
   `sorry`, it proves *zero* theorems, it is orphaned from the rest of the tree, and (as we detail in
   §3.6) it is unsound as written. Nowhere in ArkLib or its dependencies (VCVio, Mathlib) is there a
   generic- or algebraic-group-model *security theorem*. This revision supplies one for the **static**
   (committed, zero-query) generic class: a `sorry`-free, axiom-clean Schwartz–Zippel bound
   `ε ≤ (D+1)/(p−1)` proved for the whole committed-generic adversary type (§8.2, §9.1). We are careful
   that this is the *static* fragment: it kills the exact attack and exhibits the correct number, but the
   **full adaptive** Shoup/Boneh–Boyen bound — same shape, strictly larger, over `q`-query adversaries —
   remains the frontier, and we give its precise shape and its missing primitives.

### 1.3 Reproducibility and honesty commitments

Everything asserted as "mechanized" imports the genuine upstream ArkLib module at the pinned commit,
redefines nothing, builds green, and has a clean axiom closure that we print. Everything asserted as a
*bound* is quoted from and checked against its primary source. Everything not yet in Lean is labelled a
frontier. The one discipline this whole line of work exists to enforce — never assert a theorem at a
resolution higher than it has actually reached — is applied to this paper itself.

---

## 2. Preliminaries

### 2.1 Bilinear groups and KZG

Fix a prime `p` and three groups `G₁, G₂, G_T` of order `p` with a non-degenerate bilinear pairing
`e : G₁ × G₂ → G_T`. Fix generators `g₁ ∈ G₁`, `g₂ ∈ G₂`. The KZG structured reference string (SRS) for
degree `D` is generated from a secret trapdoor `τ`:

```
srs = ( (g₁, g₁^τ, g₁^{τ²}, …, g₁^{τ^D}),  (g₂, g₂^τ) ).
```

A commitment to a polynomial `f` of degree `≤ D` is `C = g₁^{f(τ)}`, computed from the `G₁` leg without
knowing `τ`. An opening of `C` at a point `z` to a value `v` is a witness `w = g₁^{q(τ)}` where
`q(X) = (f(X) − v)/(X − z)`; the verifier accepts iff `e(C · g₁^{−v}, g₂) = e(w, g₂^τ · g₂^{−z})`.
*Evaluation binding* is the property that no efficient adversary produces one commitment `C`, one point
`z`, and two valid openings `(v₁, w₁), (v₂, w₂)` with `v₁ ≠ v₂`.

### 2.2 The `t`-SDH assumption (`= q`-SDH, verbatim from ArkLib)

The `t`-Strong Diffie–Hellman problem, in a group of prime order `p`: given `(g, g^x, g^{x²}, …, g^{x^q})`,
output a pair `(c, g^{1/(x+c)})` with `c ∈ Z_p`, `x + c ≠ 0` [BB04, BB08]. ArkLib states it in
`HardnessAssumptions.lean` as (paraphrasing the Lean, which we read directly):

```lean
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 → StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

abbrev tSdhCondition {g₁ : G₁} : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) => τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val

def tSdhExperiment (D : ℕ) (adversary : tSdhAdversary D) : ℝ≥0∞ :=
  Pr[tSdhCondition | tSdhGame D adversary]          -- τ sampled nonzero; SRS from τ; run adversary

def tSdhAssumption (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D), tSdhExperiment D adversary ≤ (error : ℝ≥0∞)
```

The SRS the adversary receives is exactly the KZG SRS above: `PowerSrs.generate D τ` yields
`((g₁, g₁^τ, …, g₁^{τ^D}), (g₂, g₂^τ))`, and in particular `srs.2[1] = g₂^τ`. In KZG the SRS degree `D`
is Boneh–Boyen's `q`; we use `D` for the KZG degree throughout and `q_G` for the adversary's group-operation
count.

The sibling assumption `arsdhAssumption` (adaptive rational SDH, Definition 9.6 in [CGKY25]) asks the
adversary for a size-`(D+1)` set `S ⊆ Z_p` with `Z_S(τ) ≠ 0` (where `Z_S = ∏_{s∈S}(X − s)`), a nontrivial
`h₁`, and `h₂ = h₁^{1/Z_S(τ)}`; it has the identical unrestricted-quantifier shape and powers
`function_binding`.

### 2.3 The reduction in ArkLib

`Binding.lean` proves `binding` by a five-step `calc`: four unconditional transition lemmas rewrite the
binding-game success probability into `tSdhExperiment D (bindingReduction … adversary)` — the success
probability of an *explicitly constructed* `t`-SDH adversary — and the fifth step applies
`tSdhAssumption` to that one reduction adversary. The reduction is fully constructive and, we confirm,
algebraically correct (Section 7). The vacuity is entirely in the *quantifier* of the assumption the
fifth step consumes, not in the reduction.

---

## 3. The vacuity result

### 3.1 Why `∀ (unrestricted adversary), adv ≤ ε` is `Classical.choice`-false

For an *algebraic* hardness assumption, "bounding every adversary of a type" is only meaningful if the
type is restricted — by running time, by oracle-query count, or by an algebraic/generic structural
constraint. ArkLib's `tSdhAdversary` carries none of these. It is a total function whose body may be any
term of the right type, including a noncomputable one built with `Classical.choice`. The success
*experiment* is a probability, so the assumption is a universally quantified inequality over a type that
contains a probability-`1` winner. A universally quantified statement with a counterexample in scope is
simply false, and `Classical.choice` supplies the counterexample constructively-in-the-logic (though of
course not computationally).

The monad matters. `tSdhExperiment` is defined over `ProbComp`, a free monad on oracle queries; only
`query` nodes cost anything, and a "resource bound" like `IsQueryBoundP` counts exactly those nodes. The
winning adversary makes **zero** queries — all of its work is under `pure` — so *any* query-based bound
constrains something this adversary never does and leaves the vacuity untouched. This is the crux of why
query-bounding, the correct tool for random-oracle/hash floors, is the *wrong* tool here.

### 3.2 The trapdoor-extracting adversary (mechanized, `sorry`-free)

The discrete logarithm base a nontrivial element of a prime-order group is choice-definable via ArkLib's
own lemma:

```lean
lemma exists_zmod_power_of_generator {g : G} (hpG : Nat.card G = p) (hg : g ≠ 1)
    (hord : orderOf g = p) (x : G) : ∃ a : ZMod p, x = g ^ a.val         -- Algebra.lean:105
```

`Exists.choose` on this is the trapdoor. The adversary reads `g₂^τ` from the verifier SRS leg and returns
the solution at offset `c = 0`:

```lean
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) : Groups.tSdhAdversary D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf hg₂ srs.2[1]).val))

theorem tSdhExperiment_tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment g₁ g₂ D (tauExtractingAdversary hg₂ D) = 1
```

It wins with probability *exactly* `1`: ArkLib's trapdoor sampler `sampleNonzeroZMod` has support
`{1, …, p−1}`, so `τ ≠ 0` on the whole support, so `c = 0` satisfies `τ + c ≠ 0`, and
`h = g₁^{1/(τ+0)}` holds by `add_zero`. A canary (`tSdhExperiment_givingUpAdversary = 0`, an adversary
returning `none`) confirms the experiment discriminates, so the probability-`1` result is a fact about
this adversary and not an artifact of the probability machinery.

### 3.3 Both regimes: no content at any parameter

```lean
theorem not_tSdhAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption D error                          -- FALSE below 1

theorem tSdhAssumption_trivial_of_one_le (D : ℕ) (error : ℝ≥0) (herr : (1 : ℝ≥0∞) ≤ error) :
    Groups.tSdhAssumption D error                            -- TRIVIAL at ≥ 1
```

Below `1` the assumption is refuted by the adversary above; at `≥ 1` it holds by `probEvent_le_one`. There
is no parameter left at which it constrains anything.

### 3.4 `binding` and `function_binding` are vacuous

`binding` carries `hpair : pairing g₁ g₂ ≠ 0`. Since `pairing` is `Z_p`-bilinear, `pairing g₁ 1 = 0` (a
bilinear map kills the identity), so `hpair` *forces* `g₂ ≠ 1` — exactly the hypothesis the adversary
needs. Hence `binding`'s hypotheses are jointly unsatisfiable for `tSdhError < 1`, and its conclusion is
free for `tSdhError ≥ 1`:

```lean
theorem binding_hypotheses_unsatisfiable
    (pairing …) (hpair : pairing (.ofMul g₁) (.ofMul g₂) ≠ 0)
    (n : ℕ) (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption n tSdhError
```

The ARSDH refutation is the same, with one extra step: for each `τ` the adversary must exhibit a
size-`(D+1)` set `S` avoiding `τ` (so `Z_S(τ) ≠ 0`), which exists precisely when `p ≥ D + 2` — exactly
the `hp : p ≥ n + 2` hypothesis `function_binding` already carries. So `function_binding` is vacuous for
the identical reason (`not_arsdhAssumption`, `arsdh_binding_hypotheses_unsatisfiable`, both `sorry`-free
with a discriminating canary).

### 3.5 The methodological lesson: `#print axioms` is blind to vacuity

The reason this pattern is a trap and not a typo is that the standard soundness check does not catch it.
`binding`, `binding_hypotheses_unsatisfiable`, and the refutation all print the *same* clean axiom
closure `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, no custom axiom, nothing a
`#print axioms` or `#assert_axioms` gate would flag. **Axiom-clean and vacuous coexist.** The blindness is
structural: `#print axioms` reports the axioms in a proof term's *closure*; it says nothing about whether
the *hypotheses* of the theorem are jointly satisfiable, and a theorem with unsatisfiable hypotheses is
axiom-clean and content-free at once. This generalizes past this instance: any `def FooHard : Prop`
used as a *hypothesis* is an assumption, and no axiom check ever inspects hypotheses. The only reliable
test is adversarial — try to *inhabit* the assumption's negation (or, dually, to prove the floor false at
its real parameters) — which is precisely what `tauExtractingAdversary` does.

We record plainly that **we found the identical hole in our own hardness floors first**, in several
places, before we ever looked at ArkLib. The discipline that surfaced it — "try to prove each floor false
at deployed parameters" — is the transferable content here; the ArkLib instance is a clean, public,
mechanized exemplar of a mistake that is easy to make and invisible to the usual gate.

### 3.6 The vacuity is the *pattern*, not the theorem: q-DLOG and the AGM stub

The natural first instinct on seeing the t-SDH refutation is "then reduce KZG binding to a *different*
base assumption." That does not escape the hole, and we mechanized why. State the natural q-strong-DLOG
assumption — recover the trapdoor `τ` from the KZG power-SRS — in ArkLib's **own** idiom, i.e. with the
identical unrestricted adversary type `… → StateT unifSpec.QueryCache ProbComp (Option _)`:

```lean
theorem not_qDlogAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ qDlogAssumption D error                              -- FALSE below 1, same Classical.choice attack
```

`qDlogExperiment_trapdoorAdversary` shows the same trapdoor adversary — reading `g₂^τ`, recovering `τ`,
returning it, zero oracle queries — wins with probability exactly `1`; a canary
(`experiment_discriminates`: the giving-up adversary scores `0`) confirms the experiment is not
constantly `1`. Both `sorry`-free against genuine ArkLib at `d72f8392`, axioms
`[propext, Classical.choice, Quot.sound]`. So **renaming the assumption (t-SDH → q-DLOG) does not close
the vacuity**; the base assumption must be restated over a *sound adversary class*, which is where any
number comes from (§4–§8).

The disease is confirmed a second way by ArkLib's *own* algebraic-group-model scaffolding.
`AGM/Basic.lean` is not merely incomplete — it is **unsound as written**, and its author flags it:

- Its adversary's runner is a placeholder: `def run … : List G × α := sorry` (`AGM/Basic.lean:164–165`).
- Decisively, the adversary type is `Adversary := ReaderT (GroupValTable ι G) (OracleComp …) (List ι × α)`
  (`AGM/Basic.lean:149–153`) — a reader over the **concrete** group table `GroupValTable ι G = Π₀ _ : ι,
  Option G`, over the concrete group `G`. Handed the actual group elements, the adversary's
  scalar/control-flow outputs can still depend on discrete logs, i.e. it is *not* opaque. This is the
  exact leak that makes the unrestricted t-SDH adversary vacuous, reappearing inside the model that was
  meant to remove it.
- The source comments name the open problem verbatim: *"TODO: need to be sure this definition is
  correct"* (line 147); *"How to make the adversary truly independent of the group description? It could
  have had `G` hardwired."* (lines 169–173).

Taken together: the vacuity is **not** a t-SDH typo but the whole **unrestricted-adversary pattern** in
this idiom. Any concrete-group assumption of the shape `∀ (unrestricted adversary), Pr[win] ≤ ε < 1` is
`Classical.choice`-false, and the ecosystem has no sound generic/algebraic adversary class to state it
against. That absence is precisely what the mechanized static bound of §8.2 begins to fill.

---

## 4. The generic bilinear group model

The vacuity has two honest cures (Section 8). The one that supplies an actual *number* — a concrete
`ε` for which `binding … ε` is true and non-trivial — is the generic-group model. This section defines
it precisely; Sections 5–7 prove the bound. The development is the classical Boneh–Boyen argument
[BB08, §6], which we reproduce faithfully because it is the mathematics the fix must contain. Its
**static** (zero-query) fragment — the Schwartz–Zippel survives-attack number `(D+1)/(p−1)` — is
mechanized (§8.2, §9.1); mechanizing the **full adaptive** argument (equality queries, collision
branching) is the named frontier of Section 9.

### 4.1 Opaque handles and symbolic polynomials

In the generic bilinear group model [Sho97, Mau05, BB08], the adversary never sees a group element. It
sees an opaque *handle* — an arbitrary unique string — and can only combine handles by calling oracles:
a group-operation oracle in each of `G₁, G₂, G_T`, and the pairing oracle `e : G₁ × G₂ → G_T`. (Boneh
and Boyen additionally give the adversary the homomorphism `ψ : G₂ → G₁` and its inverse; they note this
"gives too much power" in groups where `ψ` is not efficiently computable. For the asymmetric, Type-3
pairing setting KZG is typically instantiated in, one omits `ψ`, which only weakens the adversary and
strengthens the bound. We keep BB's model as the conservative one.)

The simulator maintains, internally, a *symbolic* representation. Each handle in `G₁` and `G₂` is
associated with a **univariate polynomial in `Z_p[X]`**, where `X` is the formal trapdoor indeterminate;
handles in `G_T` carry polynomials of degree up to twice that. The tables are initialized with the SRS as
formal polynomials:

```
G₁ handles:  1, X, X², …, X^D          (the D+1 SRS elements g₁, g₁^τ, …, g₁^{τ^D})
G₂ handles:  1, X                       (the 2 SRS elements g₂, g₂^τ)
G_T handles: (empty initially)
```

The oracles act on the *polynomials*:

- **Group operation** in `G₁` (resp. `G₂`, `G_T`): given handles for `F` and `F'`, multiplication returns
  a handle for `F + F'` and division returns a handle for `F − F'`.
- **Pairing**: given a `G₁` handle for `F` and a `G₂` handle for `F'`, returns a `G_T` handle for the
  **product** `F · F'`. Since `G₁, G₂` polynomials have degree `≤ D`, `G_T` polynomials have degree
  `≤ 2D`.

The trapdoor `τ` is chosen at random and is *never* substituted while the adversary runs: the adversary's
entire interaction is with handles and the symbolic polynomials behind them. This is the precise sense in
which `τ` is information-theoretically unavailable — there is no oracle that reveals a discrete log, and
`X` is a free formal variable, not a number, during the game.

### 4.2 The crux: ordinary polynomials, not Laurent

**This is the load-bearing point of the whole model, and it is easy to get wrong.** The exponents are
*ordinary* polynomials in `Z_p[X]`. Group inversion (the division operation) **negates** the exponent
polynomial — `F ↦ −F`, which is degree-preserving — it does **not** introduce `X⁻¹`. There is no oracle
whose action on a symbolic exponent produces a negative power of `X`. Consequently the set of exponent
polynomials the adversary can ever hold is contained in `Z_p[X]` of bounded degree; it is **not** the
Laurent ring `Z_p[X, X⁻¹]`.

Why this is the crux: a `t`-SDH winner must output a `G₁` handle whose exponent equals the *rational
function* `1/(X + c)`. But `1/(X + c)` is **not a polynomial** — `(X + c)` does not divide `1` in `Z_p[X]`
(a unit has degree `0`, `X + c` has degree `1`). So the adversary cannot hold a handle whose symbolic
exponent *is* `1/(X + c)`. The best it can do is output a handle carrying some genuine polynomial
`P(X)` of degree `≤ D`, and this "wins" only if `P(X)` happens to equal `1/(X + c)` *at the specific
random value* `τ` — that is, only if

```
(X + c)·P(X) − 1   vanishes at X = τ.
```

The polynomial `(X + c)·P(X) − 1` has degree `≤ D + 1`, and it is **nonzero** (it cannot be identically
zero: `(X + c)·P(X)` has degree `≥ 1` wherever `P ≠ 0`, and if `P = 0` the expression is `−1`; either way
it is not the zero polynomial). A nonzero polynomial of degree `≤ D + 1` vanishes at a uniformly random
`τ ∈ Z_p^×` with probability `≤ (D + 1)/(p − 1)`. This is the terminal "win is itself a bad event" bound,
and it is exactly why the model produces a *finite, degree-dependent* `ε` rather than `0` or `1`.

Had the exponents been Laurent polynomials, `1/(X + c)` would be a legitimate element and the argument
would collapse; the whole quantitative content of the generic-group bound depends on the exponent ring
being `Z_p[X]`. We flag this because the natural intuition "inversion in the group is inversion in the
exponent, so `1/(τ+c)` is `(X+c)⁻¹`" is *wrong at the level of the symbolic model* — inversion in the
group negates the exponent; it is the *value* `1/(τ+c) ∈ Z_p` the honest prover computes, not a symbolic
`(X+c)⁻¹`.

### 4.3 The symbolic game, precisely

We restate Boneh–Boyen's simulator `B`, which *is* the symbolic game, in the form we will mechanize.
`B` maintains three lists `L₁, L₂, L_T` of pairs `(F, ξ)` where `F ∈ Z_p[X]` and `ξ` is the opaque handle
string. Write `τ₁, τ₂, τ_T` for the lengths of the three lists and `τ` for the number of oracle queries
answered so far. Initialization: `τ₁ = D + 1`, `τ₂ = 2`, `τ_T = 0`, with `F₁,ᵢ = X^{i−1}` (`i = 1..D+1`)
and `F₂,ᵢ = X^{i−1}` (`i = 1, 2`); handles are distinct random strings. The invariant

```
τ₁ + τ₂ + τ_T = τ + D + 3                                     (BB Eq. 4, with q = D)
```

is preserved. On each oracle call `B` forms the new polynomial (`±` for group op, `·` for pairing); if it
equals an existing polynomial in the relevant list it *reuses* that handle, otherwise it issues a fresh
random handle. When `A` halts it returns `(c, ξ_ℓ)` for some `G₁` handle `ξ_ℓ` with polynomial `F_ℓ`; `B`
forms the check polynomial `F_⋆ = F_ℓ·(X + c)` and the win condition is `F_⋆(τ) = 1`.

Only at the *end* does `B` sample `τ ∈ Z_p^×` and evaluate all polynomials at `X = τ`. The simulation is
faithful unless this evaluation makes two *distinct* polynomials collide (Section 5), or makes the
nonzero degree-`≤ D+1` polynomial `F_⋆ − 1` vanish (Section 4.2). Bounding the union of these events is
the whole proof.

---

## 5. The simulation theorem

**Theorem (Simulation / identical-until-bad, [BB08 §6], [Sho97], [Mau05]).** Fix the generic-bilinear-group
adversary `A` making at most `q_G` oracle queries. Let `Real` be `A`'s interaction with a genuine
prime-order bilinear group whose trapdoor `τ` is sampled uniformly from `Z_p^×`, and let `Sym` be `A`'s
interaction with the symbolic simulator `B` of Section 4.3 (handles issued from the polynomial lists,
`τ` sampled only at the end). Then the distributions of `A`'s *view* — the entire transcript of handle
strings returned and equality outcomes observed — are **identical** in `Real` and `Sym`, *unless* the
final evaluation at `τ` triggers the bad event

```
Bad :  ∃ two distinct polynomials F ≠ F' in the same list with F(τ) = F'(τ).
```

Precisely: there is a coupling of `Real` and `Sym` under which the two views agree pointwise on the
complement of `Bad`, so for every event `E` on views, `|Pr_Real[E] − Pr_Sym[E]| ≤ Pr[Bad]`.

**Why it holds.** In `Sym`, two handles are given the *same* string exactly when their polynomials are
*equal as elements of `Z_p[X]`*; two handles get *distinct* strings when their polynomials differ. In
`Real`, two handles are equal exactly when their *exponents at `τ`* coincide. These two notions of
equality agree unless some pair of distinct polynomials happens to evaluate equal at `τ` — that is exactly
`Bad`. Off `Bad`, every equality query is answered identically in both worlds and every fresh handle is a
fresh uniform string in both, so the transcripts are identically distributed. The only information `A`
ever extracts about `τ` is through equality outcomes; off `Bad` those are determined by the *symbolic*
(polynomial) identities, which are independent of `τ`. Hence, conditioned on `¬Bad`, `A`'s view is
independent of `τ`, and in particular `A`'s output polynomial `F_ℓ` and offset `c` are chosen without any
information about `τ` — which is what makes the terminal win itself a fresh degree-`≤ D+1` root event
(Section 4.2). ∎ (paper argument; see Section 9 for mechanization status)

The content of the theorem is entirely in the phrase "two distinct polynomials collide at `τ`." Bounding
`Pr[Bad]` is Schwartz–Zippel plus a union bound.

---

## 6. The Schwartz–Zippel bound on the bad event

**Lemma (Schwartz–Zippel, univariate; Mathlib `MvPolynomial.schwartz_zippel_…`, ArkLib
`SchwartzZippelCounting`).** A nonzero polynomial `F ∈ Z_p[X]` of degree `d` has at most `d` roots, so for
`τ` uniform on `Z_p^×` (a set of size `p − 1`), `Pr_τ[F(τ) = 0] ≤ d/(p − 1)`.

Apply it to each pair of distinct polynomials in each list, and to the terminal win polynomial:

- **`L₁` pairs.** `F₁,ᵢ − F₁,ⱼ` is nonzero of degree `≤ D`, so vanishes with probability `≤ D/(p − 1)`.
- **`L₂` pairs.** degree `≤ D` (in fact `≤ 1` from the initial SRS, but `≤ D` after operations), probability
  `≤ D/(p − 1)`.
- **`L_T` pairs.** degree `≤ 2D` (pairing doubles degree), probability `≤ 2D/(p − 1)`.
- **Terminal win.** `F_⋆ − 1 = F_ℓ·(X + c) − 1` is nonzero of degree `≤ D + 1`, probability
  `≤ (D + 1)/(p − 1)` (Section 4.2).

**Union bound.** Let `τ₁, τ₂, τ_T` be the final list lengths. The number of distinct pairs is
`\binom{τ₁}{2} + \binom{τ₂}{2} + \binom{τ_T}{2}`, plus the single terminal event. By BB Eq. 4,
`τ₁ + τ₂ + τ_T ≤ q_G + D + 3`. Summing,

```
Pr[A wins]  ≤  \binom{τ₁}{2}·D/(p−1) + \binom{τ₂}{2}·D/(p−1) + \binom{τ_T}{2}·2D/(p−1) + (D+1)/(p−1)
            ≤  (q_G + D + 3)²·(D + 1)/(p − 1).
```

The last inequality bounds every pairwise degree factor by `(D + 1)` uniformly and
`\binom{τ₁}{2}+\binom{τ₂}{2}+\binom{τ_T}{2} ≤ (τ₁+τ₂+τ_T)² ≤ (q_G + D + 3)²`. This is **exactly**
Boneh–Boyen's Theorem 12 bound (Section 7.2), with their `q` specialized to the KZG SRS degree `D`.

---

## 7. The KZG binding reduction and the concrete bound

### 7.1 A binding break yields a `t`-SDH solution

Suppose an adversary produces one commitment `C`, one point `z`, and two valid openings `(v₁, w₁)` and
`(v₂, w₂)` with `v₁ ≠ v₂`. Both pass the verifier:

```
e(C · g₁^{−v₁}, g₂) = e(w₁, g₂^{τ − z}),     e(C · g₁^{−v₂}, g₂) = e(w₂, g₂^{τ − z}).
```

Dividing the two equations cancels `C`:

```
e(g₁^{v₂ − v₁}, g₂) = e(w₁ · w₂^{−1}, g₂^{τ − z}),
```

i.e. in the exponent `(v₂ − v₁) = dlog(w₁/w₂)·(τ − z)`. Since `v₂ − v₁ ≠ 0` is invertible mod `p`,

```
g₁^{1/(τ − z)} = (w₁ · w₂^{−1})^{1/(v₂ − v₁)}.
```

That is a `t`-SDH solution with offset `c = −z`: `τ + c = τ − z`, and the extracted element is
`g₁^{1/(τ + c)}`. This is the algebra ArkLib's `bindingReduction` performs, and we have checked it is the
standard KZG10 computation. The reduction is *unconditional and constructive* — it builds the `t`-SDH
adversary explicitly from the binding adversary — so as a mechanized statement it needs no assumption at
all (Section 8.1).

### 7.2 Boneh–Boyen's Theorem 12, verbatim, and the composed bound

We verified the following against the full journal version of Boneh–Boyen (dated 2014; *J. Cryptology*
21(2):149–177, 2008; conference version EUROCRYPT 2004 [BB04]). **This is quoted, not paraphrased, from
the source.**

> **Theorem 12 (Boneh–Boyen).** Suppose `A` is an algorithm that solves the `q`-SDH problem in generic
> bilinear groups of order `p`, making at most `q_G` oracle queries for the group operations in
> `G₁, G₂, G_T`, the homomorphisms `ψ, ψ⁻¹`, and the pairing `e`, all counted together. Suppose the
> integer `x ∈ Z_p^×` and the encoding functions `ξ₁, ξ₂, ξ_T` are chosen at random. Then the probability
> `ε` that `A`, on input `(p, ξ₁(1), ξ₁(x), …, ξ₁(x^q), ξ₂(1), ξ₂(x))`, outputs `(c, ξ₁(1/(x+c)))` with
> `c ∈ Z_p \ {−x}` is bounded by
> ```
> ε ≤ (q_G + q + 3)²·(q + 1)/(p − 1).
> ```
> Asymptotically, `ε ≤ O((q_G²·q + q³)/p)`.

And its restatement:

> **Corollary 13 (Boneh–Boyen).** Any adversary that solves the `q`-SDH problem with constant probability
> `ε > 0` in generic bilinear groups of order `p` such that `q < O(p^{1/3})` requires `Ω(√(p/q))` generic
> operations.

Specializing `q := D` (the KZG SRS degree) and composing with the reduction of Section 7.1 (mechanized in
ArkLib as `binding_reduces_to_tSdh`, Section 8.1) gives the concrete KZG evaluation-binding bound in the
generic bilinear group model:

```
Adv^{eval-binding}_{KZG}(A)  ≤  (q_G + D + 3)²·(D + 1)/(p − 1)  =  O((q_G + D)²·D / p).
```

**This is not a clean `q²/p`.** It carries a factor of the SRS degree `D`: the `G_T` polynomials reach
degree `2D`, the terminal win polynomial degree `D + 1`, and the asymptotic form `O((q_G²·D + D³)/p)` is
quadratic in `q_G` but *cubic* in `D`. For KZG at production parameters (`D` in the thousands to millions,
`p ≈ 2^{255}`), the `D³/p` term is the one to watch, and Corollary 13's `q < O(p^{1/3})` side condition is
exactly the constraint that keeps the bound meaningful (and the reason implementations choose `p` to dodge
the matching Brown–Gallant/Cheon generic *upper* bounds [BB08 §3]). Reporting the bound as `q²/p` would
understate the degree dependence; the honest statement is Boneh–Boyen's.

---

## 8. The fix for ArkLib

### 8.1 The immediate, mechanized de-vacuation: `binding_reduces_to_tSdh`

The decisive structural fact is that ArkLib's reduction is *already constructive*, and `tSdhAssumption` is
consumed in exactly one place — the last `calc` step. **Split the `calc` at the final `≤`.** The
unconditional prefix (the four transition lemmas, verbatim) becomes a new primary theorem; the original
`binding` becomes a one-line corollary.

```lean
/-- Extraction-shaped evaluation binding: every binding adversary yields — as the explicit data
    `bindingReduction … adversary` — a t-SDH adversary whose success upper-bounds its advantage. -/
theorem binding_reduces_to_tSdh (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    [SampleableType G₁] (AuxState : Type) (adversary : KzgBindingAdversary … AuxState) :
    Commitment.bindingExperiment … (kzg …) AuxState adversary
      ≤ Groups.tSdhExperiment g₁ g₂ n (bindingReduction … AuxState adversary) := …

/-- Original assumption-form binding, now a corollary. -/
theorem binding (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁]
    (tSdhError : ℝ≥0) (htSdh : Groups.tSdhAssumption n tSdhError) :
    Commitment.binding … (kzg …) tSdhError := by
  simp only [Commitment.binding]; intro AuxState adversary
  exact (binding_reduces_to_tSdh hg₁ hpair AuxState adversary).trans
    (t_sdh_error_bound … tSdhError htSdh adversary)
```

`binding_reduces_to_tSdh` takes **no assumption `Prop`** — its right-hand side is `tSdhExperiment` of a
*specific constructed* adversary, and it relates two concrete probabilities that hold at every parameter.
There is nothing for `Classical.choice` to inhabit. The full diff is **+41 / −14** in one file; the four
transition lemmas and the entire reduction are untouched; the whole tree still builds
(`lake build …KZG.Binding` → 2994 jobs, exit 0) and both theorems are axiom-clean
`[propext, Classical.choice, Quot.sound]`.

**It survives the exact attack** (`RepairSurvives.lean`, `sorry`-free):

```lean
theorem repair_survives_attack (pairing …) (hg₁ : g₁ ≠ 1) (hpair : pairing (.ofMul g₁) (.ofMul g₂) ≠ 0)
    [SampleableType G₁] (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1)
    (AuxState : Type) (adversary : KzgBindingAdversary … AuxState) :
    (¬ Groups.tSdhAssumption n tSdhError)                       -- (1) the exact attack still refutes it
    ∧ (Commitment.bindingExperiment … AuxState adversary        -- (2) yet the repaired bound holds
        ≤ Groups.tSdhExperiment n (bindingReduction … AuxState adversary)) := …
```

Both conjuncts hold *simultaneously, in the same groups, in one `sorry`-free axiom closure.* Leg (1) is
the identical trapdoor-extracting adversary that killed the original — we did not weaken the assumption.
Leg (2) is the repaired bound, which takes no `tSdhAssumption` hypothesis, so leg (1) cannot empty it.
That is the precise sense in which the vacuity is closed: the disease was "the premise is unsatisfiable";
the cure removes the premise while keeping every ounce of the reduction's content.

This is the mergeable step. It does not by itself supply the *number* `ε` (the RHS is still a
`tSdhExperiment`, whose value needs a model in which `τ` is unreadable); it isolates the exact obligation
— bound the success of the *one* reduction adversary — that any sound assumption must discharge.

### 8.2 The sound numeric grounding: the generic-group bound

The obligation `binding_reduces_to_tSdh` isolates is discharged by Sections 4–7: over the generic-bilinear-group
adversary class, `tSdhExperiment` of any adversary — in particular the reduction adversary — is bounded by
`(q_G + D + 3)²(D + 1)/(p − 1)`. Concretely, the fix is to state `tSdhAssumption` over the *generic*
(equivalently, restricted straight-line/symbolic) adversary class and instantiate `error` at Boneh–Boyen's
bound; then `binding` becomes true and non-trivial, with `Adv^{eval-binding}_{KZG} ≤ (q_G + D + 3)²(D+1)/(p−1)`.
This is the finished theorem: the extraction-shaped bound as the unconditional content, the generic-group
bound as its quantitative closure.

**The static fragment of this bound is mechanized** (`GgmCandidate.lean`, `sorry`-free, axioms
`[propext, Classical.choice, Quot.sound]`). Model the committed-generic adversary as a bare
`(offset c, representation polynomial f)` with `deg f ≤ D` and **no group-element input** — faithful,
because from the SRS handles `g₁^{τ⁰}, …, g₁^{τ^D}` the reachable exponents are exactly
`span{1, τ, …, τ^D}`, the degree-≤D polynomials. Winning requires `f(τ)·(τ+c) = 1`, so every winning `τ`
is a root of the nonzero degree-≤(D+1) polynomial `f·(X+c) − 1`; Schwartz–Zippel caps the winning set at
`D+1`, giving

```lean
theorem ggm_tSdh_sound (A : GenericAdversary D p) (hp : 2 ≤ p) :
    ggmExperiment A ≤ (D + 1 : ℚ) / (p - 1)                   -- over the FULL generic adversary type
theorem ggm_bound_lt_one (hp : D + 2 < p) : ((D : ℚ) + 1) / (p - 1) < 1
```

The theorem quantifies over the *entire* `GenericAdversary` type, so every `Classical.choice`-definable
inhabitant provably obeys the bound; the exact `tauExtractingAdversary` cannot even be typed here (no
group element in, so no `∃ a, · = g^a` to invert). This is a real number, not a definitional dodge: the
type is richly inhabited (every offset, every degree-≤D `f`), the bound is a genuine `< 1` (≈ `2⁻²³⁴` at
`p ≈ 2²⁵⁴`, `D ≈ 2²⁰`), and it is *tight* — interpolating `f` through `D+1` targets `1/(τᵢ+c)` wins on
exactly `D+1` trapdoors.

**Two scope limits, stated precisely.** (i) This is the **static** (`q = 0`, zero group-operation/equality
queries) fragment; the number `(D+1)/(p-1)` is the static-class number and does **not** upper-bound the
adaptive adversary, whose bound is the larger, same-shape `(q_G+D+3)²(D+1)/(p-1)` — that requires the
adaptive analysis of §4–§7 (the collision term). (ii) The win predicate is stated at the **field** level
(`f(τ) = 1/(τ+c)`); its equivalence to the group-level t-SDH win rests on injectivity of `a ↦ g₁^{a.val}`
in a prime-order group (ArkLib's `Algebra.lean`), which is standard but **argued**, so `GgmCandidate.lean`
is a self-contained model not yet wired to ArkLib's `tSdhExperiment` — the reduction transport of §7
(and §9.2) is what connects them. What is mechanized is genuinely the static-generic *survives-attack
number*; what is not is the adaptive term and the field→group reduction.

### 8.3 The algebraic-group-model alternative

The other honest cure is the *algebraic* group model (AGM) [FKL18]. There an adversary that outputs a
group element must also output a representation of it as a known linear combination of its inputs
(FKL18 Definition 1); under this restriction, Fuchsbauer–Kiltz–Loss show SDH (and CDH, and LRSW) are
equivalent to the discrete logarithm assumption. For the degree-`D` polynomial setting KZG lives in, the
relevant reduction target is the parametrized `q`-DLog assumption (FKL18 Fig. 13); FKL18's own generic
hardness bound for `q`-DLog is `O((t²·q + q³)/p)`, which they state is "derived analogously to the bound
for Boneh and Boyen's SDH assumption [BB08]." With `t` the generic-operation count (our `q_G`) and `q` the
degree (our `D`), this is the *identical* `O((q_G² + …)·D + D³)/p` shape as our Section 7.2 bound — an
independent corroboration that the degree-cubic dependence is real and not an artifact of one derivation.

A subtlety worth stating, because it bit our first attempt: **naive AGM does not close our vacuity.** If
the adversary stays an arbitrary function that *additionally* returns a representation, `Classical.choice`
still wins — it extracts `τ`, returns `h = g₁^{1/τ}`, *and* returns the genuinely valid representation
(coefficient `1/τ` on the `g₁` SRS basis element). A dependent pair `(element, valid-representation)` is
extra data choice supplies for free, not a restriction; *validity is not independence.* A sound AGM repair
therefore still needs a real computational boundary — the representation must be *extracted by the
reduction to solve a separate hard problem* (`q`-DLog), whose own generic-group hardness again routes
through Sections 4–7. So the AGM is the more standard textbook framing but is *not* a shortcut around the
model; it relocates the same metatheoretic content onto `q`-DLog.

### 8.4 Recommendation

Ship §8.1 (the extraction-shaped `binding_reduces_to_tSdh`) as the immediate, backward-compatible primary
statement, keeping `binding` as a corollary and documenting that the assumption-form corollary is
informative only once `tSdhAssumption` is restricted. Then close the number via §8.2 (generic group) or
§8.3 (AGM). The generic-group development (Sections 4–7) is the direction that yields a self-contained
numeric theorem with no residual assumption.

---

## 9. Mechanization status (scrupulously honest)

**`#assert_axioms`-clean is not hypothesis-free.** We repeat this here because it governs how to read the
list below: a theorem can have a clean axiom closure and still assume something (in a hypothesis) or, as
in Section 3, prove nothing (unsatisfiable hypotheses). The list distinguishes *mechanized and
non-vacuous* from *paper argument, frontier*.

### 9.1 Sorry-free in Lean today (verified, clean axiom closure)

- **The vacuity refutation.** `not_tSdhAssumption`, `tSdhExperiment_tauExtractingAdversary`,
  `tSdhAssumption_trivial_of_one_le`, the discriminating canaries; the ARSDH analogues
  `not_arsdhAssumption`, `arsdhAssumption_trivial_of_one_le`; and the consumer lemmas
  `binding_hypotheses_unsatisfiable`, `arsdh_binding_hypotheses_unsatisfiable`. All import genuine ArkLib
  at `d72f8392`, redefine nothing, build green, axioms `[propext, Classical.choice, Quot.sound]`.
  (`KzgVacuity.lean`.)
- **The extraction-shaped repair.** `binding_reduces_to_tSdh` and the shrunk `binding` corollary, as the
  real `+41/−14` diff against `Binding.lean`; whole tree builds (2994 jobs, exit 0); axiom-clean.
  (`binding-repair.patch`.)
- **The repair survives the attack.** `repair_survives_attack`: the exact trapdoor adversary still refutes
  the assumption below error `1`, while the repaired bound holds unconditionally — both in one `sorry`-free
  closure. (`RepairSurvives.lean`.)
- **The static generic-group numeric survives-attack bound.** `ggm_tSdh_sound` (with
  `card_winningPoints_le`, `winPoly_ne_zero`, `winPoly_natDegree_le`, `ggm_bound_lt_one`): over the
  **entire** committed-generic adversary type `GenericAdversary D p` (offset, degree-≤D representation
  polynomial, no group-element input), the success experiment is `≤ (D+1)/(p−1)`, a genuine rational
  `< 1` for `p > D+2`. Proved by the Schwartz–Zippel root count on `f·(X+c) − 1`; the exact trapdoor
  adversary is untypable in this class. This is the **static** (`q = 0`) fragment of §4–§7's bound and its
  win predicate is field-level (group-faithfulness argued, §8.2); it is a self-contained model, not yet
  wired to ArkLib's `tSdhExperiment`. Axioms `[propext, Classical.choice, Quot.sound]`. (`GgmCandidate.lean`;
  the equivalent algebraic-model framing is `AlgebraicTSdh.lean`.)
- **The ADAPTIVE generic-group numeric bound — `q`-query, identical-until-bad proven.**
  `adaptive_ggm_sound` (with `card_realWinSet_le`, `realWinSet_subset`, `runAux_congr_of_agree`,
  `card_rootUnion_le`, `adaptive_bound_lt_one`, `adaptive_generalizes_static`): the `q = 0` static bound
  above pushed to an adversary that makes up to `fuel` **adaptive oracle queries** — group operations
  (`ZMod p`-linear combinations), pairings (`G₁×G₂→Gₜ` polynomial products), and **equality tests** — before
  committing its output. The generic-group oracle (`runAux`) carries handles as `ℕ` indices into a table of
  formal `Z_p[X]` polynomials seeded with the SRS, and answers equality *symbolically* (τ never enters the
  adversary's view). The crux, **Shoup's identical-until-bad, is PROVEN by induction not assumed**
  (`runAux_congr_of_agree`: two oracles agreeing on every queried pair produce identical runs), yielding the
  set-level `W₀ ⊆ W₁ ∪ F` (`realWinSet_subset`) — the real winning trapdoors are contained in the bad-event
  set plus the static win set of the τ-independent symbolic output. Composed with the union Schwartz–Zippel
  bad-event bound and the reused static core, the success experiment is
  `≤ (fuel·Δ + (D+1))/(p−1)` — Boneh–Boyen's static root event `(D+1)` plus Shoup's collision event
  `(#queries)·Δ` — a genuine rational `< 1` whenever `fuel·Δ + (D+1) < p−1`. At faithful SRS degrees
  `Δ = D+1`; `fuel = 0` recovers exactly the static `(D+1)/(p−1)` (`adaptive_generalizes_static`). Axioms
  `[propext, Classical.choice, Quot.sound]`. **Scope (honest):** this is the *explicit-equality-oracle*
  (Maurer abstract-handle) GGM, in which learning equality costs a query — hence the bound is **linear in
  the number of equality queries**, strictly tighter than the classical `~(q_G+D)²(D+1)/(p−1)` of Shoup's
  *random-encoding* model, where equality of visible encodings is free and the bad event ranges over all
  table pairs (§9.2). The two degree facts (output handle degree ≤ D; queried-handle differences degree
  ≤ Δ) enter as explicit hypotheses — the SRS degree invariant, the same idiom as the static adversary's
  `degree_le` field — satisfied structurally by the faithful group-op discipline and discharged
  automatically at `fuel = 0`. Not yet wired to ArkLib's `tSdhExperiment` (§9.2). (`GgmAdaptive.lean`.)
- **The vacuity is systemic, not t-SDH-specific.** `not_qDlogAssumption` (`KzgQDlogVacuity.lean`): the
  natural q-DLOG base assumption in ArkLib's own unrestricted-adversary idiom is *equally* false below
  error `1`, by the identical `Classical.choice` extraction (with a discriminating canary,
  `experiment_discriminates`). Confirms §3.6: renaming the assumption does not escape the pattern. Imports
  genuine ArkLib at `d72f8392`; axiom-clean.

### 9.2 What remains: from the mechanized adaptive core to the classical Shoup number

The **static** bound is mechanized (§9.1), and the **adaptive** identical-until-bad development of
Sections 4–7 is now mechanized *for the explicit-equality-oracle (Maurer) model* (`GgmAdaptive.lean`,
§9.1): the opaque symbolic oracle, the simulation/coupling lemma, and the composed `q`-query bound all
build sorry-free with a clean axiom closure. What was, in the prior draft of this section, the full
frontier is now three *named, scoped* residuals — smaller and sharper than "a from-scratch paper-sized
development":

- **The classical quadratic (Shoup random-encoding) bound.** Our mechanized adaptive bound is
  `(fuel·Δ + (D+1))/(p−1)`, **linear** in the number of equality queries, because our oracle *charges a
  query for each equality test* (Maurer abstract-handle model) and the bad event `F` ranges over the
  ≤ `fuel` *queried* pairs (`runAux_congr_of_agree` is exactly agreement on the queried pairs). Shoup's
  original **random-encoding** model gives equality *for free* — the adversary compares any two visible
  encoding strings — so there `F` ranges over all `\binom{N}{2}` same-group table pairs with
  `N ≤ q_G + D + 4`, yielding the classical `~(q_G+D)²(D+1)/(p−1)`. Reaching that number means: (i) an
  all-table-pairs bad event (not just queried pairs), and (ii) a whole-table degree invariant to bound
  every pair's difference degree by `Δ`. Both are additions to the present development, not corrections
  of it; our tighter linear bound is *sound for the model we state*, and is the honest number for an
  explicit-equality-oracle GGM.
- **Structural discharge of the degree invariant.** The two degree facts (`hdeg_out`, `hdeg_pairs`) are
  supplied as hypotheses — the SRS/group-op degree bounds, the same idiom as the static adversary's
  `degree_le` field, and discharged automatically at `fuel = 0` (`adaptive_generalizes_static`). Proving
  them *structurally* for every faithful run (a degree-tracking oracle that tags handles by group `G₁/G₂/Gₜ`
  and proves `lin` preserves the per-group degree bound and `pair : G₁×G₂→Gₜ` reaches only `D+1`) would
  remove the hypotheses. This is bookkeeping over the same `runAux`, not new mathematics; it is named, not
  faked.
- **The reduction transport (Section 7, unchanged).** `binding_reduces_to_tSdh` *builds* a `tSdhAdversary`
  from a binding adversary; to inherit the generic-group bound, that construction must be re-typed as a
  straight-line/symbolic program in the `Strat` class and its field-level win predicate connected to
  ArkLib's group-level `tSdhExperiment` via prime-order injectivity (`Limit (b)` of `SOUND-FIX-VERDICT`).
  This is the field→group wiring that both the static and adaptive self-contained models still await.

**On ArkLib's own `AGM/Basic.lean`.** It remains a WIP stub, not a foundation: `Adversary.run` is literally
`sorry` (line 165), it proves *zero* theorems, it is orphaned, and — decisively — it is **not opaque**: the
`Adversary` is a `ReaderT (GroupValTable ι G) …` handed the *actual* group table over the *concrete* group
`G`, so its outputs can still depend on discrete logs. `GgmAdaptive.lean`'s oracle takes the opposite,
sound stance: the adversary is a `Strat := List Bool → Move ⊕ Output` that receives **only** equality-query
booleans, never `G`, never τ — the opacity invariant is *structural in the type*, which is exactly why the
identical-until-bad induction goes through and the trapdoor-extraction attack is untypable.

**Missing primitives, concretely.** The **static** bound of §8.2 needs only Mathlib's single-variable
`Polynomial.card_roots'` and `Field (ZMod p)`. The **adaptive** core (`GgmAdaptive.lean`) needed, and now
supplies from scratch, what was absent from ArkLib/VCVio/Mathlib: an opaque-handle bilinear-group oracle
(`runAux`), a generic-group identical-until-bad simulation lemma (`runAux_congr_of_agree` — VCVio's
`IdenticalUntilBad`/`IsQueryBoundP` are ROM-shaped and were not reused), and a union Schwartz–Zippel
bad-event bound (`card_rootUnion_le`) over Mathlib's `card_roots'`. As far as our census found, this is the
first **adaptive** generic-group-model security theorem in Lean; the static bound was the first
generic-group security theorem of any kind, and the residuals above sharpen — they do not gate — the claim.

### 9.3 What is verified vs. asserted, for the bounds

The concrete bound `(q_G + D + 3)²(D + 1)/(p − 1)` is **quoted from and checked against** Boneh–Boyen's
Theorem 12 (§7.2), not asserted: we read the theorem statement and its proof (the polynomial-list
simulator, the per-list degree bounds `D, D, 2D`, the terminal `(D+1)` factor, and the union bound under
`τ₁+τ₂+τ_T ≤ q_G+D+3`) directly from the full-version source and reproduced them in Sections 4–6. The
"ordinary polynomials, not Laurent" point (§4.2) is corroborated by Boneh–Boyen's own construction, in
which group division sets `F ← F_i − F_j` (negation), never a negative power of `X`.

---

## 10. Related work

**KZG commitments.** Kate, Zaverucha, and Goldberg [KZG10] introduced the polynomial commitment and its
evaluation-binding proof by reduction to `t`-SDH. ArkLib mechanizes this reduction; the sibling ARSDH
route follows Chiesa–Guan–Knabenhans–Yu [CGKY25, Def. 9.6].

**The `t`-SDH / `q`-SDH assumption and its generic hardness.** Boneh and Boyen [BB04] introduced SDH for
short signatures; the full version [BB08] proves the generic-bilinear-group lower bound (Theorem 12,
Corollary 13) we use. Shoup [Sho97] introduced the generic group model; Maurer [Mau05] gave an alternative
formulation. Brown–Gallant and Cheon [BB08 §3, refs therein] give the matching generic *upper* bound,
which is why parameter choice matters.

**The algebraic group model.** Fuchsbauer, Kiltz, and Loss [FKL18] introduced the AGM and showed SDH is
equivalent to discrete log within it; this is the §8.3 alternative. Jaeger–Mohan [JM24] and
Lipmaa–Parisella–Siim [LPS24] — the references ArkLib's `AGM/Basic.lean` cites — study when AGM proofs
transfer to the GGM and knowledge-soundness from falsifiable assumptions.

**Formal cryptography and adversary cost.** VCVio (ArkLib's dependency) models random-oracle reductions
(e.g. DLog for Schnorr, Pointcheval–Stern) via query bounds `IsQueryBoundP` and `IdenticalUntilBad`
lemmas — the right tools for hash/ROM floors, and (as we note) exactly the wrong ones for an algebraic
assumption. EasyCrypt built the only mechanized adversarial *cost* judgement we know of (eprint 2021/156)
and removed it in 2024 as "barely used," which is part of why a general PPT restriction is hard rather than
merely undone; extraction-shaped statements (VCVio's Merkle `Binding`) and generic/algebraic-group models
are the tractable routes. Schwartz–Zippel is in Mathlib (`MvPolynomial.SchwartzZippel`) and ArkLib
(`SchwartzZippelCounting`).

**The vacuity pattern.** That a universally-quantified security bound over an unrestricted adversary type
is inhabited-false, and that axiom checks are blind to it, is — to our knowledge — not previously written
up as a mechanization hazard with a clean public exemplar. The transferable lesson (prove the floor false
at deployed parameters; a named hard-problem `def` used as a hypothesis is an assumption no axiom check
inspects) is the methodological contribution.

---

## References

- **[BB04]** D. Boneh and X. Boyen. *Short Signatures Without Random Oracles.* EUROCRYPT 2004, LNCS 3027,
  pp. 56–73.
- **[BB08]** D. Boneh and X. Boyen. *Short Signatures Without Random Oracles and the SDH Assumption in
  Bilinear Groups.* Journal of Cryptology 21(2):149–177, 2008. (Full version; **Theorem 12** and
  **Corollary 13**, §6, are the generic-bilinear-group bounds used here. Verified against the
  August 2014 revision of the full text.)
- **[CGKY25]** A. Chiesa, Z. Guan, C. Knabenhans, and Z. Yu. *On the Fiat–Shamir Security of Succinct
  Arguments from Functional Commitments.* (Source of ArkLib's ARSDH, Definition 9.6.)
- **[FKL18]** G. Fuchsbauer, E. Kiltz, and J. Loss. *The Algebraic Group Model and its Applications.*
  CRYPTO 2018, Part II, LNCS 10992, pp. 33–62.
- **[JM24]** J. Jaeger and D. I. Mohan. *Generic and Algebraic Computation Models: When AGM Proofs
  Transfer to the GGM.* (Cited by ArkLib `AGM/Basic.lean`.)
- **[KZG10]** A. Kate, G. M. Zaverucha, and I. Goldberg. *Constant-Size Commitments to Polynomials and
  Their Applications.* ASIACRYPT 2010, LNCS 6477, pp. 177–194.
- **[LPS24]** H. Lipmaa, R. Parisella, and J. Siim. *On Knowledge-Soundness of Plonk in ROM from
  Falsifiable Assumptions.* (Cited by ArkLib `AGM/Basic.lean`.)
- **[Mau05]** U. Maurer. *Abstract Models of Computation in Cryptography.* IMA Cryptography and Coding
  2005, LNCS 3796, pp. 1–12.
- **[Sho97]** V. Shoup. *Lower Bounds for Discrete Logarithms and Related Problems.* EUROCRYPT 1997,
  LNCS 1233, pp. 256–266.
- **ArkLib** (Ethereum Foundation / Verified-zkEVM), revision
  `d72f8392ff03047dc5386f4f4bb513743e7ada65`, Lean `v4.31.0`.
  `ArkLib/Commitments/Functional/KZG/{Binding,HardnessAssumptions,Algebra,Sampling}.lean`,
  `ArkLib/AGM/Basic.lean`.

---

## Appendix A. Artifacts

Mechanized files (this directory), all against ArkLib `d72f8392`:

- `KzgVacuity.lean` — the vacuity refutation (`t`-SDH and ARSDH), `sorry`-free, with canaries.
- `binding-repair.patch` — the `+41/−14` extraction-shaped repair of `Binding.lean`.
- `RepairSurvives.lean` — `repair_survives_attack`: repair coexists with the exact attack, `sorry`-free.
- `candidates/GgmCandidate.lean` — the **static** generic-group numeric survives-attack bound
  `ggm_tSdh_sound : ε ≤ (D+1)/(p−1)` over the whole `GenericAdversary` type, `sorry`-free, axiom-clean.
  (`candidates/AlgebraicTSdh.lean` is the equivalent algebraic-model framing.)
- `candidates/KzgQDlogVacuity.lean` — `not_qDlogAssumption`: the q-DLOG idiom is equally vacuous
  (§3.6), `sorry`-free against genuine ArkLib, with a discriminating canary.
- `candidates/` (`agm-sound`, `extraction`, `ggm`, `qdlog-direct`, `novel`) — the five elaborated
  candidate fixes and their writeups.
- `SOUND-FIX-VERDICT.md` — the integrator's re-verified comparison, per-goal winner, and recommendation.
- `DISCLOSURE-DRAFT.md` — the maintainer-facing writeup of the finding.
- `REPAIR.md`, `WHY-FINDING-ONLY.md` — the repair rationale and the tractability map for the numeric fix.
- `FACTCHECK-FABLE.md` — an independent second checker's from-scratch confirmation (real upstream, green
  build, clean axioms).

Reproduce the vacuity: drop `KzgVacuity.lean` into `ArkLib/Scratch/`, then
`lake build ArkLib.Scratch.KzgVacuity` (green, no `sorry`); `#print axioms not_tSdhAssumption` →
`[propext, Classical.choice, Quot.sound]`.
