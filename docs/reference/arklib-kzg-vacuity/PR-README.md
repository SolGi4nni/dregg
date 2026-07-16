# KZG evaluation binding: a vacuity finding, an honest de-vacuation, and the sound GGM bound

This directory contains a mechanized formalization-soundness finding about
`ArkLib/Commitments/Functional/KZG/Binding.lean`, a minimal fix, and (optionally) the
generic-group soundness bound the fix points at. Everything is checked against ArkLib at
`d72f8392ff03047dc5386f4f4bb513743e7ada65` (Lean `v4.31.0`), imports the genuine upstream
modules, redefines nothing, builds `sorry`-free, and has axiom closure exactly
`[propext, Classical.choice, Quot.sound]`.

**This is not a security advisory.** There is no vulnerability, nothing exploitable, and no
embargo. KZG, the `t`-SDH assumption as normally stated, and the reduction in `Binding.lean`
are all sound. The issue is the *quantifier* in one Lean assumption. We found the identical
pattern in our own Lean tree first; we bring it here as a shared field lesson, not a dunk.

---

## 1. The finding: `tSdhAssumption` is vacuous, and so is `binding`

`Groups.tSdhAssumption` quantifies over an *unrestricted* adversary type:

```lean
def tSdhAssumption … (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D …),
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)
```

`tSdhAdversary` lands in `StateT unifSpec.QueryCache ProbComp`. Because `ProbComp` is a free
monad over oracle queries, **pure computation is free** and no resource bound is imposed. An
adversary may therefore `pure` an arbitrary noncomputable function of the SRS at zero cost.

The SRS includes the verifier leg `(g₂, g₂^τ)`, which determines `τ` whenever `g₂ ≠ 1`, and
ArkLib's own `Algebra.lean:105 exists_zmod_power_of_generator` makes that discrete log
`Classical.choice`-definable. So a one-line adversary recovers `τ`, returns the `t`-SDH
solution `(c = 0, g₁^{1/τ})`, and wins with probability *exactly* `1` (it makes zero oracle
queries). Consequently:

- `tSdhAssumption D error` is **false for every `error < 1`** (`not_tSdhAssumption`), and
- trivially true for `error ≥ 1`, since a probability is `≤ 1` (`tSdhAssumption_trivial_of_one_le`).

`KZG.CommitmentScheme.binding` takes `tSdhAssumption` as a hypothesis and concludes a bound
at the *same* `error`, so it carries no information at any parameter: below `1` its premise is
unsatisfiable, at or above `1` its conclusion is free. `binding`'s own `hpair : pairing g₁ g₂ ≠ 0`
even *forces* `g₂ ≠ 1` (via bilinearity and `map_zero`), so the killing adversary's one
hypothesis is discharged from `binding`'s own premises (`binding_hypotheses_unsatisfiable`).

The sibling `Groups.arsdhAssumption` — the hypothesis of `KZG.function_binding` — has the
identical unrestricted quantifier and falls the identical way (`not_arsdhAssumption` /
`arsdhAssumption_trivial_of_one_le`); the ARSDH branch's `D + 2 ≤ p` is exactly the
`p ≥ n + 2` that `function_binding` already carries.

The mechanized witness is `ArkLib/Scratch/KzgVacuity/KzgVacuity.lean` (namespace
`ArkLibVacuity`). It ships with canaries — `tSdhExperiment_givingUpAdversary = 0`,
`arsdhExperiment_givingUpAdversary = 0` — proving the `= 1` is a fact about *this* adversary,
not an artifact of the probability machinery: the experiment genuinely discriminates.

**Why `#print axioms` does not catch this.** `binding` is axiom-clean *and* vacuous at the
same time. A clean axiom closure certifies "no `sorry`, no `native_decide`"; it says nothing
about whether a hypothesis is satisfiable. That blindness is the whole reason the pattern is
easy to miss, and it is why we treat it as a discipline problem rather than a typo.

---

## 2. The fix: an extraction-shaped restatement (`+41 / −14`, one file)

The right tool here is **not** query-bounding. `t`-SDH is an *algebraic* assumption whose
killing adversary makes zero queries, so an `IsQueryBoundP`-style restriction (the correct
fix for random-oracle/hash floors) constrains something this adversary never does. The honest
menu is the generic/algebraic group model, or an extraction-shaped restatement that turns the
assumption into *data the adversary must produce*. We ship the latter as the minimal step —
it is the pattern VCVio already uses for its Merkle `Binding`.

The key observation is structural: **ArkLib's reduction is already fully constructive.**
`binding`'s proof is a five-step `calc`; the first four steps are unconditional transition
lemmas, and `tSdhAssumption` is consumed in exactly one place — the last `≤`. So the fix is to
*split the calc at that last step*:

```lean
/-- Extraction-shaped evaluation binding: every binding adversary yields — as the explicit
    reduction `bindingReduction … adversary` — a t-SDH adversary whose success probability
    upper-bounds its binding advantage. No assumption `Prop`, hence nothing for a
    `Classical.choice` adversary to inhabit. -/
theorem binding_reduces_to_tSdh {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (AuxState : Type)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Commitment.bindingExperiment … (kzg …) AuxState adversary
      ≤ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
          (bindingReduction … AuxState adversary) := by
  … -- the existing calc prefix, verbatim; the four transition lemmas are untouched

/-- The original assumption-form binding, now a one-line corollary. -/
theorem binding … (htSdh : Groups.tSdhAssumption … n tSdhError) :
    Commitment.binding … (kzg …) tSdhError := by
  simp only [Commitment.binding]; intro AuxState adversary
  exact (binding_reduces_to_tSdh (pairing := pairing) hg₁ hpair AuxState adversary).trans
    (t_sdh_error_bound … tSdhError htSdh adversary)
```

`binding_reduces_to_tSdh` carries the full constructive content *without* the
universally-quantified assumption, so it is immune to the vacuity: the bound relates two
concrete probabilities — *this* adversary's advantage and *its* reduction's success — and
carries content at every parameter. `binding` keeps its exact signature (backward
compatible) as an immediate corollary; its docstring notes that the corollary only becomes
informative once `tSdhAssumption` is stated over a restricted adversary class.

The full diff is `+41 / −14` in `Binding.lean` (see `binding-repair.patch`). The whole tree
still builds; both theorems are `[propext, Classical.choice, Quot.sound]`.

### The fix survives the exact attack (mechanized)

A de-vacuation is only honest if it survives the attack rather than merely avoiding it.
`ArkLib/Scratch/KzgVacuity/RepairSurvives.lean` (namespace `ArkLibRepairCheck`) proves both
facts as one conjunction, `repair_survives_attack`:

1. the identical trapdoor-extracting adversary *still* refutes `tSdhAssumption` below `1`
   (we did not weaken the assumption), **and**
2. `binding_reduces_to_tSdh` holds *unconditionally* — it takes no `tSdhAssumption`
   hypothesis, so leg (1) has nothing to empty.

Both hold at once, in the same groups, `sorry`-free. That is the precise sense in which the
vacuity is closed: the disease was an unsatisfiable premise; the cure removes the premise
while keeping every step of the reduction.

---

## 3. (Optional / follow-up) The sound numeric bound: KZG binding in the generic bilinear group model

The extraction-shaped fix removes the vacuity but hands *no number*: its right-hand side is
still `tSdhExperiment` of the constructed reduction adversary. The number a KZG binding bound
ultimately rests on is the generic-group hardness of `t`-SDH. This directory mechanizes it,
end to end, on ArkLib's **real** `tSdhExperiment`.

Group elements are modelled as opaque handles carrying *ordinary* polynomials in the trapdoor
indeterminate `X` (**not Laurent** — group inversion negates the exponent, it does not
introduce `X⁻¹`; that is exactly why a winning `1/(X+c)` output is unrepresentable and forces
a bounded-degree root event). A simulation theorem plus Schwartz–Zippel then yield the bound.
The capstone is `ArkLib/Scratch/KzgVacuity/GgmEndToEnd.lean`:

```lean
theorem tSdh_ggm_sound … (strat : Strat p) (fuel : ℕ) :
    tSdhExperiment D (embed strat) ≤ (C(fuel+D+4,2)·D + (D+1)) / (p − 1)
```

with a companion `tSdh_ggm_sound_lt_one` giving a genuine `< 1` in the standard regime
`C(fuel+D+4,2)·D + (D+1) < p − 1` (at cryptographic parameters, `≈ 2⁻²³⁴`). It quantifies over
the **image of the generic embedding** `embed` — the generic-restricted class that escapes the
vacuity: `embed strat` receives only equality booleans, never a group element, so it can only
realize `g₁^{f(τ)}` with `deg f ≤ D`, which is exactly what the counting bound bounds. The full
`tSdhAdversary` type does *not* escape (§1 proves the statement over it false); the embedding is
what makes the number meaningful.

The dependency spine — all `sorry`-free, axioms exactly `[propext, Classical.choice, Quot.sound]`:

| Module | Role |
|---|---|
| `GgmCandidate` | static (zero-query) Schwartz–Zippel core, `(D+1)/(p−1)`; reused below |
| `GgmAdaptive` | the adaptive `q`-query bound; identical-until-bad hybrid proved by induction on fuel |
| `GgmRandomEncoding` | the Shoup all-pairs (quadratic) random-encoding count; table size is a theorem |
| `GgmDegreeDischarge` | discharges the SRS degree invariant on the *actual* (linear, pairing-free) oracle |
| `GgmArkLibTransport` | field→group transport against ArkLib's real `Groups.tSdhCondition` |
| `GgmProbThreading` | collapses ArkLib's `OptionT ProbComp` / `StateT QueryCache` game to `card/(p−1)` |
| `GgmEmbed` | constructs the generic-restricted adversary and certifies what it realizes |
| `GgmEndToEnd` | the capstone `tSdh_ggm_sound` (+ `tSdh_ggm_sound_lt_one`) |

To our knowledge — a census of ArkLib, VCVio, and Mathlib — no generic-group-model security
*theorem* previously existed in Lean, so this is a candidate first of its kind. ArkLib's own
`AGM/Basic.lean` is a WIP stub (`Adversary.run` is `sorry`, zero theorems, orphaned) and is
moreover unsound as written: its adversary is a `ReaderT` over the concrete group table, so its
outputs can still depend on discrete logs. If you would prefer to complete that module to
opacity instead, the extraction-shaped fix in §2 is the right first step regardless: it isolates
the *single* obligation (bound the success of the one reduction adversary) that any restricted
assumption — generic, algebraic, or otherwise — must discharge.

### Honest side-conditions on `tSdh_ggm_sound`

These travel with every citation of the bound:

- `1 ≤ D` — the meaningful KZG regime; at `D = 0` a pairing-free `G₁` adversary genuinely
  cannot form `g₁^τ`.
- `2 ≤ p` (so `p − 1 ≥ 1`) and `orderOf g₁ = p` (the base is a generator, used for encoding
  injectivity).
- `[∀ i, SampleableType (unifSpec.Range i)]` — ArkLib's own instance on `tSdhExperiment`,
  carried verbatim.

The bound is the classical Boneh–Boyen shape — `O((q_G + D)²·D / p)`, degree-dependent, **not**
a clean `q²/p`. Off the critical path (and *not* required by `tSdh_ggm_sound`): a conservative
pairing-aware `δ = 2D` variant for a stronger, off-interface adversary, and re-typing the
extraction reduction's adversary as a generic strategy so §2's binding statement inherits the
number directly. Neither gates the soundness result.

---

## 4. Build and check

Against ArkLib at `d72f8392` with Lean `v4.31.0` (VCVio/CompPoly `v4.31.0`), the scratch
modules under `ArkLib/Scratch/KzgVacuity/`:

```bash
# The finding
lake build ArkLib.Scratch.KzgVacuity.KzgVacuity
#   #print axioms ArkLibVacuity.not_tSdhAssumption               → [propext, Classical.choice, Quot.sound]
#   #print axioms ArkLibVacuity.not_arsdhAssumption              → [propext, Classical.choice, Quot.sound]
#   #print axioms ArkLibVacuity.tSdhAssumption_trivial_of_one_le → [propext, Classical.choice, Quot.sound]

# The fix (applied to ArkLib/Commitments/Functional/KZG/Binding.lean) and its survival proof
lake build ArkLib.Scratch.KzgVacuity.RepairSurvives
#   #print axioms KZG.CommitmentScheme.binding_reduces_to_tSdh   → [propext, Classical.choice, Quot.sound]
#   #print axioms ArkLibRepairCheck.repair_survives_attack       → [propext, Classical.choice, Quot.sound]

# The GGM bound (only if this PR includes §3)
lake build ArkLib.Scratch.KzgVacuity.GgmEndToEnd
#   #print axioms GgmEndToEnd.tSdh_ggm_sound                      → [propext, Classical.choice, Quot.sound]
#   #print axioms GgmEndToEnd.tSdh_ggm_sound_lt_one              → [propext, Classical.choice, Quot.sound]
```

Every headline theorem is `sorry`-free with axiom closure exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`, no
`ofReduceBool`. The `Classical.choice` in the vacuity theorems is the *content*, not a smell:
it is the unbounded extractor being exhibited as a legal inhabitant of the unrestricted
adversary type.

---

## 5. A note on framing

We ran this same "try to prove each hardness floor false at its deployed parameters" tooth on
our own Lean tree before pointing it here, and found the identical unrestricted-quantifier hole
in several of our own floors first. `#print axioms` was blind to all of them. The reduction in
`Binding.lean` is careful, correct work — which is exactly why the honest thing is to state it
soundly rather than route around it. We would be glad to open the fix as a PR, split it however
you prefer (finding + de-vacuation first, GGM bound as a follow-up), or leave it here for you to
take up directly.
