/-
# Market.AggregateBinding — aggregate binding as a proof-carrying MSIS obligation

**codex fhEgg Round-3 Q1, the linked `(ct, C, Π)` carrier.** Each order carries a BDLOP-family
*additive* lattice commitment `C_i = Com(m_i; r_i)` whose BINDING is Module-SIS. The batch
AGGREGATES commitments by native ring addition: `C_agg = Σ C_i`. codex's sharp point, honored
exactly here: the SIS witness extracted from a binding break is

        A·(r − r') + G·(m − m') = 0

— it **includes the message difference `m − m'`** — so the Module-SIS instance must be sized to the
**accepted-aggregate opening radius**, not to a single order. A forgotten radius bound is a break.

## What this file is (honest scope)

This is the **reduction STRUCTURE**, not a security proof:

  * `Com` is the abstract *additive/linear* commitment shape `A·r + G·m` over a commutative ring
    `R`. The concrete BDLOP matrix distribution (`A, G` sampled, `‖·‖`-norms) is the crypto build,
    NOT this Lean. Linearity is the only load-bearing property, and it is exactly what turns a
    collision into a linear kernel witness.
  * `IsShort : R → R → Prop` is the abstract SIS norm bound on the *witness pair* `(dr, dm)` — it
    carries codex's radius, and it is a **REQUIRED field** of an `AggregateOpening`: an opening
    that forgot to establish its radius bound cannot be constructed (a forgotten radius = a type
    error).
  * `MSISHard A G IsShort` is a **NAMED hardness HYPOTHESIS** — "no short nonzero `(dr, dm)` lies in
    the kernel of `[A | G]`". It is **NEVER proven and NEVER laundered as an axiom** (`#assert_axioms`
    only inspects `axiom`-keyword decls; hardness enters solely as an explicit `Prop` hypothesis).

## Proven vs assumed

  * PROVEN (pure algebra): `collision_yields_msis_witness` — two distinct openings of one commitment
    yield the message-difference-carrying kernel witness, nonzero.
  * PROVEN (reduction): `aggregate_binding_of_msis` — GIVEN `MSISHard`, a radius-bounded collision of
    the aggregate commitment forces equality (binding). The security content is discharged onto the
    hypothesis; the theorem is the reduction, not the hardness.
  * ASSUMED: `MSISHard A G IsShort` (Module-SIS). Shown SATISFIABLE-in-principle by a concrete model
    (`msisHard_trivial_model`) so the reduction is not vacuous over a `False` hypothesis.
-/
import Market.MintSafeQuantization
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

namespace Market

universe u

variable {R : Type u} [CommRing R]

/-- The abstract additive/linear commitment shape: `Com A G r m = A·r + G·m`.

`A, G` are the (here scalar-modelled) BDLOP matrices, `r` the randomness, `m` the message. The
only property used downstream is LINEARITY in `(r, m)`, which is exactly what makes a collision a
linear kernel witness. The concrete matrix distribution is the crypto build, not this model. -/
def Com (A G r m : R) : R := A * r + G * m

@[simp] theorem Com_def (A G r m : R) : Com A G r m = A * r + G * m := rfl

/-- Native ring addition of two commitments is the commitment of the summed openings — the batch
`C_agg = Σ C_i` is honest precisely because `Com` is linear. -/
theorem Com_add (A G r₁ m₁ r₂ m₂ : R) :
    Com A G r₁ m₁ + Com A G r₂ m₂ = Com A G (r₁ + r₂) (m₁ + m₂) := by
  simp only [Com]; ring

/-- **The named Module-SIS hardness hypothesis** (assumption, never proven).

`MSISHard A G IsShort` asserts: there is NO short, nonzero pair `(dr, dm)` in the kernel of the
concatenated matrix `[A | G]`, i.e. with `A·dr + G·dm = 0`. `IsShort` carries codex's radius bound
on the *whole* witness pair — crucially INCLUDING the message component `dm`. This is carried as an
ordinary `Prop`; it is never an `axiom` and never discharged. -/
def MSISHard (A G : R) (IsShort : R → R → Prop) : Prop :=
  ¬ ∃ dr dm : R, (dr ≠ 0 ∨ dm ≠ 0) ∧ IsShort dr dm ∧ A * dr + G * dm = 0

/-- **The crux (PROVEN, pure algebra).** Two DISTINCT openings `(r, m) ≠ (r', m')` of the SAME
commitment `Com A G r m = Com A G r' m'` yield the Module-SIS witness

        A·(r − r') + G·(m − m') = 0

with `(r − r', m − m')` nonzero. The witness **carries the message difference `m − m'`** — codex's
sharp point: the radius that sizes MSIS must bound this whole pair, not just `r − r'`. -/
theorem collision_yields_msis_witness (A G r m r' m' : R)
    (hne : (r, m) ≠ (r', m'))
    (hcol : Com A G r m = Com A G r' m') :
    A * (r - r') + G * (m - m') = 0 ∧ (r - r' ≠ 0 ∨ m - m' ≠ 0) := by
  refine ⟨?_, ?_⟩
  · -- the kernel equation, by linearity of `Com`
    simp only [Com] at hcol
    linear_combination hcol
  · -- nonzero: else both differences vanish and the openings coincide, contradicting `hne`
    by_contra h
    simp only [not_or, not_not] at h
    obtain ⟨h1, h2⟩ := h
    exact hne (Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2))

/-- **Aggregate binding, the REDUCTION (PROVEN modulo the named hypothesis).**

GIVEN `MSISHard A G IsShort`, any two openings of the aggregate commitment whose difference is
short (radius-bounded, `IsShort (r − r') (m − m')`) and which open the SAME commitment must be
EQUAL. A binding break would be exactly the short nonzero kernel witness forbidden by `MSISHard`.

The security content lives entirely in the hypothesis `hard`; this theorem is the reduction. -/
theorem aggregate_binding_of_msis (A G : R) (IsShort : R → R → Prop)
    (hard : MSISHard A G IsShort)
    (r m r' m' : R)
    (hshort : IsShort (r - r') (m - m'))
    (hcol : Com A G r m = Com A G r' m') :
    (r, m) = (r', m') := by
  by_contra hne
  obtain ⟨hker, hnz⟩ := collision_yields_msis_witness A G r m r' m' hne hcol
  exact hard ⟨r - r', m - m', hnz, hshort, hker⟩

/-- **A proof-carrying aggregate opening.** The radius bound `radius : IsShort r m` is a REQUIRED
field: an `AggregateOpening` that never established its shortness/radius bound cannot be formed — a
forgotten radius is a *type error*, exactly codex's discipline. `opens` ties `(r, m)` to `C`. -/
structure AggregateOpening (A G : R) (IsShort : R → R → Prop) where
  /-- aggregate randomness `Σ rᵢ`. -/
  r : R
  /-- aggregate message `Σ mᵢ`. -/
  m : R
  /-- aggregate commitment `C_agg = Σ Cᵢ`. -/
  C : R
  /-- the opening relation `Com A G r m = C`. -/
  opens : Com A G r m = C
  /-- **REQUIRED radius field** — the aggregate opening's shortness bound, sized (per codex) to the
  whole `(r, m)` pair including the message. Omitting it makes the structure unconstructable. -/
  radius : IsShort r m

/-- **Aggregation by native ring addition.** Two aggregate openings combine into one whose randomness,
message, and commitment are the componentwise sums (`C_agg = Σ Cᵢ`). The combined radius bound
`hradius` must be SUPPLIED — you cannot mint the aggregate opening without proving its aggregate
radius. This is where a forgotten radius bound would be caught. -/
def AggregateOpening.combine (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort)
    (hradius : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    AggregateOpening A G IsShort where
  r := o₁.r + o₂.r
  m := o₁.m + o₂.m
  C := o₁.C + o₂.C
  opens := by
    have e := Com_add A G o₁.r o₁.m o₂.r o₂.m
    rw [o₁.opens, o₂.opens] at e
    exact e.symm
  radius := hradius

@[simp] theorem combine_r (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    (AggregateOpening.combine A G IsShort o₁ o₂ h).r = o₁.r + o₂.r := rfl

@[simp] theorem combine_m (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    (AggregateOpening.combine A G IsShort o₁ o₂ h).m = o₁.m + o₂.m := rfl

@[simp] theorem combine_C (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    (AggregateOpening.combine A G IsShort o₁ o₂ h).C = o₁.C + o₂.C := rfl

/-- The combined opening's radius field IS the aggregate radius that was supplied — the required
field is genuinely the aggregate bound, not a per-order one. -/
theorem combine_radius_is_aggregate (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    IsShort (AggregateOpening.combine A G IsShort o₁ o₂ h).r
            (AggregateOpening.combine A G IsShort o₁ o₂ h).m := by
  simpa using h

/-! ## Non-vacuity — concrete witnesses over `ℤ` -/

/-- A concrete valid aggregate opening over `ℤ`: `Com 1 1 2 3 = 5`, trivial radius. Exists ⇒ the
proof-carrying structure is inhabited. -/
def exampleOpening : AggregateOpening (1 : ℤ) 1 (fun _ _ => True) where
  r := 2
  m := 3
  C := 5
  opens := by simp only [Com]; norm_num
  radius := trivial

/-- The aggregate of a concrete opening with itself, formed by native addition — its radius field is
the aggregate `(4, 6)` bound (here trivially discharged). Non-vacuous use of `combine`. -/
def exampleAggregate : AggregateOpening (1 : ℤ) 1 (fun _ _ => True) :=
  AggregateOpening.combine (1 : ℤ) 1 (fun _ _ => True) exampleOpening exampleOpening trivial

example : exampleAggregate.r = 4 := rfl
example : exampleAggregate.m = 6 := rfl
example : exampleAggregate.C = 10 := rfl

/-- **`collision_yields_msis_witness` FIRES on a concrete collision.** Over `ℤ` with `A = G = 1`,
`Com 1 1 2 3 = 5 = Com 1 1 1 4` while `(2,3) ≠ (1,4)`; the extracted witness `(2−1, 3−4) = (1, −1)`
is a nonzero kernel element `1·1 + 1·(−1) = 0`. The message component `3 − 4 = −1` is genuinely
present in the witness. -/
example :
    (1 : ℤ) * (2 - 1) + 1 * (3 - 4) = 0 ∧ ((2 : ℤ) - 1 ≠ 0 ∨ (3 : ℤ) - 4 ≠ 0) :=
  collision_yields_msis_witness (1 : ℤ) 1 2 3 1 4
    (by decide)
    (by simp only [Com]; norm_num)

/-- **`MSISHard` is SATISFIABLE-in-principle** (not definitionally `False`): the model where the ONLY
short pair is `(0, 0)` admits no short *nonzero* kernel element, so hardness holds for ANY `A, G`.
This shows the reduction is not vacuous over a `False` hypothesis. The real crypto model has a
richly-populated short set and its hardness is the genuine Module-SIS ASSUMPTION. -/
theorem msisHard_trivial_model (A G : R) :
    MSISHard A G (fun dr dm => dr = 0 ∧ dm = 0) := by
  rintro ⟨dr, dm, hnz, ⟨h0r, h0m⟩, _⟩
  rcases hnz with h | h
  · exact h h0r
  · exact h h0m

/-- **The reduction genuinely consumes `MSISHard`.** Instantiated at the trivial hardness model,
aggregate binding holds — and the ONLY way two openings can be short here is if their difference is
`(0,0)`, i.e. they were already equal; the reduction then returns equality. This exercises
`aggregate_binding_of_msis` against a live (non-`False`) hypothesis. -/
example (A G r m r' m' : R)
    (hshort : (r - r' = 0 ∧ m - m' = 0))
    (hcol : Com A G r m = Com A G r' m') :
    (r, m) = (r', m') :=
  aggregate_binding_of_msis A G (fun dr dm => dr = 0 ∧ dm = 0)
    (msisHard_trivial_model A G) r m r' m' hshort hcol

#assert_all_clean [Market.collision_yields_msis_witness, Market.aggregate_binding_of_msis,
  Market.Com_add, Market.combine_radius_is_aggregate, Market.msisHard_trivial_model]

end Market
