# Candidate: Generic Group Model (GGM) — the Boneh–Boyen boundary, with a number

**Candidate name:** `ggm`
**Status:** the **static / committed-generic** fragment is **MECHANIZED, `sorry`-free**
(`GgmCandidate.lean`, axioms `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`),
yielding the numeric bound **`(D+1)/(p-1)`** and a **PROVEN survives-attack**. The **full
adaptive Shoup GGM** (equality/group-op queries, branching on collisions) is **MONTHS-AWAY** —
no generic-group scaffolding exists in Mathlib or VCVio.
**Scratch tree:** `/private/tmp/arklib-ggm` (ArkLib @ `d72f8392`, Lean `v4.31.0`; `.lake`
symlinked read-only to `/private/tmp/arklib-review`, so no clobber of sibling lanes).
**Artifact:** `GgmCandidate.lean` (this directory; built copy in the scratch tree).

---

## 0. The candidate, and the one-line verdict

> *Restrict the t-SDH adversary to generic group operations — a strategy that manipulates
> opaque handles, never field elements — and derive the numeric bound the way Boneh–Boyen
> (EUROCRYPT 2004) and Shoup do.*

**Verdict.** This is the *only* candidate that both **survives the exact attack with a
mechanized proof** and **delivers a real number** — because it is the one that identifies and
removes the true source of the leak: the adversary's access to the SRS as *field data*. The
naïve AGM fix (candidate `agm-sound`) fails precisely because a representation is *extra data
`Classical.choice` supplies for free*; the GGM boundary is stronger — it denies the adversary
`τ` (and `g^τ`) as an input *at all*, so the winning output must be committed as a polynomial
`f` chosen **without** `τ` in scope. Schwartz–Zippel then caps every such adversary — including
every choice-definable one — at `(D+1)/(p-1)`.

**The honest scope line.** What is *mechanized* is the **static** generic adversary (commits to
one output; makes no adaptive queries). That is the Boneh–Boyen boundary specialized to zero
group-operation queries, and it already (a) kills the exact attack and (b) exhibits the correct
Schwartz–Zippel number. The **full** GGM guarantee — the same *shape* of bound `~(q+D)²/p` over
adaptive `q`-query adversaries — needs a formalized generic-group oracle, which neither Mathlib
nor VCVio has. The number `(D+1)/(p-1)` is the *static-class* number; do not read it as the
all-generic-adversaries number (that one is strictly larger, same shape).

---

## 1. Why the naïve AGM fails and GGM does not (the load-bearing difference)

The refutation (`../KzgVacuity.lean`, `not_tSdhAssumption`) wins because `tSdhAdversary` takes
the SRS as **concrete group elements** `Vector G₁ (D+1) × Vector G₂ 2`. From the verifier leg
`g₂^τ`, ArkLib's own `exists_zmod_power_of_generator : ∃ a, x = g^a` hands `Exists.choose` the
trapdoor `τ : ZMod p`.

- **Naïve AGM** additionally demands the adversary output a *representation* `(element, f)` with
  `element = ∏ srs_i^{f_i}`. This does **not** restrict `Classical.choice`: knowing `τ`, it
  returns `h = g₁^{1/τ}` **and** the genuinely valid one-coefficient representation
  `f = (1/τ)·e₀`. The representation predicate is *satisfiable for any output once you know `τ`*
  — it is more data the choice-adversary supplies, never a hardness.

- **GGM** removes the input that leaks `τ`. A generic algorithm sees the group only through
  opaque handles and a group-operation oracle; it never receives `g₂^τ` as a decodable field
  element. Formalized minimally: the adversary receives **no group elements and no `τ`**, and
  its output is a **committed polynomial** `f` (the exponent of its output handle as a linear
  combination of the SRS tower exponents `1, τ, …, τ^D`), chosen with **`τ` absent from scope**.
  The environment then *defines* the output element as `g₁^{f(τ)}`. There is no
  `∃ a, · = g^a` term anywhere in the adversary's inputs, so **`Exists.choose` has nothing to
  invoke.** This is the real boundary the naïve AGM lacked.

**The output space is faithfully captured, not weakened.** In a prime-order group the group
operation *adds exponents*; starting from the handles `g₁^{τ^0}, …, g₁^{τ^D}` the reachable
exponents are exactly `span{1, τ, …, τ^D}` = polynomials of degree ≤ D. So "committed
degree-≤D polynomial `f`" is the exact reachable-output space of a generic adversary, not a
convenient sub-space. What the *static* model omits is only the adversary's ability to make
adaptive **equality-test** queries and branch on observed collisions (§4).

---

## 2. The statement (mechanized)

```lean
/-- A committed (static) generic t-SDH adversary: an offset and a degree-≤D representation
    polynomial, chosen independently of the trapdoor. NO group-element input ⇒ no τ to extract. -/
structure GenericAdversary (D : ℕ) (p : ℕ) where
  offset    : ZMod p
  repr      : (ZMod p)[X]
  degree_le : repr.natDegree ≤ D

/-- Winning trapdoors: nonzero τ with τ+c ≠ 0 and f(τ) = 1/(τ+c). In a prime-order group,
    g₁^{f(τ).val} = g₁^{(1/(τ+c)).val} ⟺ f(τ) = 1/(τ+c), so this is the faithful t-SDH win. -/
noncomputable def winningPoints (A : GenericAdversary D p) : Finset (ZMod p) :=
  nonzeroPoints.filter (fun τ => τ + A.offset ≠ 0 ∧ A.repr.eval τ = 1 / (τ + A.offset))

/-- The experiment: fraction of the p-1 nonzero trapdoors on which the committed adversary wins. -/
noncomputable def ggmExperiment (A : GenericAdversary D p) : ℚ :=
  (winningPoints A).card / (p - 1)
```

The win-condition reduction is faithful: `g₁` has order `p`, so `a ↦ g₁^{a.val}` is injective
on `ZMod p` and `g₁^{f(τ)} = g₁^{1/(τ+c)} ⟺ f(τ) = 1/(τ+c)` (ArkLib's `Algebra.lean` supplies
exactly this injectivity via `zmod_eq_zero_of_gpow_eq_one`). Working at the field level is a
faithful reduction, not a simplification.

---

## 3. Survives-attack — PROVEN, `sorry`-free

The heart is one Schwartz–Zippel bound. For a committed `(c, f)` define
`winPoly = f·(X + c) - 1`. It is **nonzero** (else `X + c` is a unit of `(ZMod p)[X]`,
impossible over a field — degree 1 ≠ 0) and has **degree ≤ D+1**, hence **≤ D+1 roots**
(`Polynomial.card_roots'`). Every winning `τ` is a root (`f(τ)(τ+c) = 1 ⇒ winPoly(τ) = 0`), so:

```lean
theorem card_winningPoints_le (A : GenericAdversary D p) : (winningPoints A).card ≤ D + 1
theorem ggm_tSdh_sound (A : GenericAdversary D p) (hp : 2 ≤ p) :
    ggmExperiment A ≤ (D + 1 : ℚ) / (p - 1)
theorem ggm_bound_lt_one (hp : D + 2 < p) : ((D : ℚ) + 1) / (p - 1) < 1
```

All `sorry`-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]` — **no
`sorryAx`**.

**Why this is the strongest possible form of survives-attack.** `ggm_tSdh_sound` quantifies
over the **full** structure type `GenericAdversary D p`. `Classical.choice` *can* inhabit that
type (pick any `offset`, any `repr`) — and **every** inhabitant provably obeys the bound. So the
theorem is not "the attack cannot be expressed"; it is "even the choice-definable adversaries
provably cannot exceed `(D+1)/(p-1) < 1`." This mirrors `not_tSdhAssumption` in the mirror
image: there, choice *inhabited a probability-1 winner*; here, choice inhabits only sub-1
losers. The `Classical.choice` axiom is *present in the axiom list of the bound itself* — the
guarantee holds in the same logic that broke the original.

The one load-bearing design invariant: **`GenericAdversary` must not take `τ` (or `g^τ`) as an
input.** If the type were re-parameterized as a *function of `τ`*, the leak returns — but that
is by definition not the generic model. The type forbids it; that forbiddance is the whole fix.

**Randomized generic adversaries** (a distribution over `(c, f)`) are covered by convex
averaging: success is the mean of point-mass successes, each ≤ `(D+1)/(p-1)`, so the mean is too
(ARGUED — a one-line `PMF`/`tsum` monotonicity extension, not mechanized; not needed for
survives-attack, since a distribution cannot beat its best point mass).

---

## 4. What the number rests on, and what is dropped (no free lunch)

**Rests on:** the **GGM ideal model** — specifically the restriction that the adversary's output
representation `f` is chosen with `τ` absent, `deg f ≤ D`. That restriction is *the* assumption;
it is not derived from DLOG. This is the honest "no free lunch" answer: the number
`(D+1)/(p-1)` is bought with the generic-group idealization, exactly as Boneh–Boyen's t-SDH
bound is.

**Relation to Boneh–Boyen '04 / Shoup.** The full GGM bound for an adversary making `q`
group-operation queries is `~ (q + D + 1)²·(D+1) / p` (the `q²` term counts collision events
among adaptively-built handles). Mine is the **`q = 0` specialization**: the adversary commits
to one output and makes no equality queries. So:

- ✅ mechanized: `static-generic advantage ≤ (D+1)/(p-1)`.
- ❌ **not** mechanized, and **not implied** by the above: `all-generic advantage ≤ …`. The
  static bound is *smaller*, so it does **not** upper-bound the adaptive adversary. Proving the
  full guarantee needs the adaptive analysis (the `q²` collision term).

Stated plainly: **the survives-attack property is robust across both models** (choice cannot
win in either), but the **specific number** `(D+1)/(p-1)` is the static-class number, and the
all-generic number of the same shape is what a complete GGM proof delivers.

---

## 5. Does ArkLib's binding reduction survive?

Structurally yes; mechanically it needs a rewrite (the same invasiveness `../REPAIR.md` flags
for its option `(A)`). `bindingReduction` forms the t-SDH solution as a fixed **group
combination** of the binding adversary's two openings — a generic operation. Lifted into the
representation world, a *generic* binding adversary carries representation polynomials for its
openings, and the reduction's output representation is the corresponding combination of them; so
the reduction is generic-compatible. But ArkLib's `bindingReduction` currently threads *group
elements*, not representations, so making it a `GenericAdversary(binding) → GenericAdversary(tSdh)`
map is a real rework of the reduction, not a `+41/-14` split. The extraction-shaped split
(`../REPAIR.md` option `(B)`, `binding_reduces_to_tSdh`) is the right *first* step regardless:
it isolates exactly the obligation — bound the one reduction adversary's success — that this GGM
statement discharges.

---

## 6. Invasiveness & mechanizability

**Invasiveness (of adopting GGM in ArkLib): heavy.** New `GenericAdversary` type; rewrite
`tSdhGame`/`tSdhExperiment` to define the output element as `g₁^{f(τ)}` from a committed `f`;
rework `bindingReduction` to emit representations. This is ArkLib's option `(A)`, made concrete
and given its number. It is a maintainer-owned redesign, not a drive-by patch.

**Mechanizability: PARTIAL.**
- **MECHANIZED (`sorry`-free, this candidate):** the static Schwartz–Zippel core and the
  survives-attack bound — `winPoly_ne_zero`, `winPoly_natDegree_le`, `card_roots_winPoly_le`,
  `card_winningPoints_le`, `ggm_tSdh_sound`, `ggm_bound_lt_one`. Built against Mathlib's
  `Polynomial.card_roots'`; `Fact (Nat.Prime p) ⇒ Field (ZMod p)` gives the domain structure.
- **MONTHS-AWAY:** full adaptive Shoup GGM. **Grepped:** neither Mathlib nor VCVio has any
  generic-group / symbolic-handle / straight-line-program infrastructure (VCVio's
  `CryptoFoundations/HardnessAssumptions/` has DLog/CDH/DDH *experiments* but no generic-group
  oracle; the only "generic group" string hits in Mathlib are unrelated substrings). Building a
  faithful generic-group oracle with an equality-query transcript and the
  distinct-polynomials-collide-at-`τ` hybrid is a multi-week formalization on its own.

---

## 7. Comparison to the sibling candidates

- vs **`../REPAIR.md` (B) / `extraction`**: those give a *reduction* (no number, nothing to
  falsify) and are nearly free (`+41/-14`). GGM gives the *number* but is heavy. They compose:
  ship (B) now to expose `binding_reduces_to_tSdh`; GGM (or AGM-sound) is what eventually bounds
  the single reduction adversary (B) isolates.
- vs **`agm-sound`**: same goal (a numeric algebraic-model bound); GGM's boundary is what makes
  AGM sound — the representation must be committed *without `τ`*. GGM is the honest floor under
  the AGM fix.
- vs **`qdlog-direct`**: that candidate correctly concludes "you must fix the base assumption
  first, and the number comes from GGM." **This candidate is that GGM number, mechanized for the
  static class.**

---

## Artifact

- `GgmCandidate.lean` (this directory) — the `sorry`-free static-GGM core. Built in
  `/private/tmp/arklib-ggm` via `lake env lean GgmCandidate.lean` (exit 0; axioms
  `[propext, Classical.choice, Quot.sound]`).
