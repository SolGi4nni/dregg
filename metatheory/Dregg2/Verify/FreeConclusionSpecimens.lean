/-
# Dregg2.Verify.FreeConclusionSpecimens — the free-conclusion gate's own SELF-TEST fixtures.

`#free_conclusion_ratchet`'s classifier (`FreeConclusionRatchet.scanType`) decides whether a
declaration's CONCLUSION contains a disjunct this tree already PROVES free. A classifier that
degenerates in either direction is invisible from a green build, and both degenerations have a
concrete cost here:

  * degenerate toward CLEAN — every free disjunct passes and the gate is a green light with no
    bulb. That is the state the tree was in on 2026-08-01: three keystones registered on
    `OrBreak (SpongeCollision …) _` / `OrBreak (StateBreakP …) _` statements passed
    `#keystone_audit` with genuine satisfiability and genuine teeth, one of them labelled "the
    CRITICAL-3 closure", while `SpongeCollisionShirk.orBreak_spongeCollision_iff_True` proves the
    disjunction is literally `True`.
  * degenerate toward FLAGGED — the campaign's own REPAIR starts tripping the gate. The sound
    shape (`AggregationAirSound`, `MapPathCutoverCheck`, `StateCommitLeafRegrounded`) is a
    disjunction too: `xs = ys ∨ SpongeColl hash xs ys`, a per-instance residual at the NAMED pair.
    A gate that cannot tell it from `xs = ys ∨ SpongeCollision hash` makes porting a build error,
    and then there is no gate. `specPerInstanceResidual` is that control and it is the single most
    important line in this file.

So the classifier is not trusted on the strength of the build being green. This module holds
`Prop`-valued defs whose VALUES are declaration TYPES with a known-correct verdict, and
`FreeConclusionRatchet.check` re-classifies every one of them on EVERY run and hard-errors if a
verdict moved.

⚑ They live in their own module because the machinery resolves them by raw `Name` out of the
environment, exactly the way `FloorRatchet` resolves `FloorRatchetSpecimens`.

## THE RULE the specimens pin

A declaration's conclusion is FREE exactly when it contains, in POSITIVE position, a subterm that
some in-tree theorem PROVES equivalent to `True` (an `_iff_True` witness) or PROVES for an
arbitrary good branch (a `_trivial` witness). Position matters in both directions:

  * a break event in HYPOTHESIS position is a floor question, not a freeness question — that is
    `#floor_ratchet`'s surface, and this gate must not double-bill it;
  * a break event CLAIMED (`FieldBounded hash → SpongeCollision hash`) is the pigeonhole fact
    itself, which is TRUE and load-bearing — flagging it would gate the refutation that arms this
    very gate;
  * a break event under `¬` is a tombstone, and the campaign wants more of them.
-/
import Dregg2.Circuit.SpongeCollisionShirk
import Dregg2.Circuit.StateCommitReduceRaw

set_option autoImplicit false

namespace Dregg2.Verify.FreeConclusionSpecimens

open Dregg2.Circuit
open Dregg2.Exec
open Dregg2.Circuit.CollisionReduce (SpongeCollision OrBreak)
open Dregg2.Circuit.SpongeCollisionShirk (SpongeColl FieldBounded)

/-! ### FLAGGED — the free-conclusion class, in the four spellings it has actually appeared in. -/

/-- FLAGGED. The headline shape: `HistoryAggregation.verified_history_conserves_orBreak` and
`root_tooth_pins_kernel_orBreak` had exactly this form, and both were REGISTERED KEYSTONES that
passed `#keystone_audit`. `orBreak_spongeCollision_iff_True` proves the conclusion is `True` at
every field-bounded sponge, so the good branch is unreachable from the statement. -/
def specFreeOrBreak : Prop :=
  ∀ (hash : List ℤ → ℤ) (xs ys : List ℤ), hash xs = hash ys →
    OrBreak (SpongeCollision hash) (xs = ys)

/-- FLAGGED. ⚑ THE SPELLING HOLE, pinned before it can open. `OrBreak B P` is an `abbrev` for
`P ∨ B`, so the identical statement can be written with a bare `∨` and no `OrBreak` token anywhere.
A gate keyed on the `OrBreak` NAME would cost a build error under one spelling and nothing under
the other — which is precisely the residual `FloorRatchet`'s `inj-spelled` class had to close for
`Function.Injective` vs `Poseidon2SpongeCR`. The matcher is `isDefEq`, not a name test, so both
spellings land on the same witness. -/
def specFreeSpelledViaOr : Prop :=
  ∀ (hash : List ℤ → ℤ) (xs ys : List ℤ), hash xs = hash ys →
    (xs = ys ∨ SpongeCollision hash)

/-- FLAGGED. The free disjunct as ONE CONJUNCT of a larger conclusion. The rest of the conclusion
may well be load-bearing; this conjunct is not, and a keystone is not entitled to launder a free
half behind a true half. -/
def specFreeUnderConjunct : Prop :=
  ∀ (hash : List ℤ → ℤ) (xs ys : List ℤ),
    xs.length = ys.length ∧ OrBreak (SpongeCollision hash) (xs = ys)

/-- FLAGGED. Buried under an `∃` — the shape a "there is an extraction such that …" statement
takes. The scan descends binders, so depth is not a hiding place. -/
def specFreeUnderExists : Prop :=
  ∀ (hash : List ℤ → ℤ), ∃ xs : List ℤ, OrBreak (SpongeCollision hash) (xs = [])

/-- FLAGGED. The SECOND break family, `StateCommitReduce.StateBreakP` — a four-way apex break whose
first disjunct is the sponge collision. It has its own `_iff_True` witness
(`orBreak_stateBreakP_iff_True`) and is NOT definitionally the sponge one, so a gate that derived
only one pattern would pass this. This is the specimen that keeps the witness derivation plural. -/
def specFreeStateBreak : Prop :=
  ∀ (CH : CellId → Value → ℤ) (cmb compress : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ) (n : Nat),
    OrBreak (Dregg2.Circuit.StateCommitReduce.StateBreakP CH cmb compress compressN) (n = n)

/-! ### CLEAN — and each one is a REPAIR, a REFUTATION, or ordinary content. -/

/-- CLEAN. ⚑⚑ **THE CONTROL THAT MATTERS MOST — the SOUND SHAPE must never be a build error.**
This is the landed port (`SpongeCollisionShirk` §3, `AggregationAirSound`, `MapPathCutoverCheck`):
the residual is `SpongeColl hash xs ys` — a collision AT THE NAMED PAIR, `xs ≠ ys ∧ hash xs = hash
ys` — not the global existential. Pigeonhole does not supply it (`noSpongeColl_satisfiable` proves
it fails at a real pair of a real field-bounded sponge), so no `_iff_True` witness exists for it and
none can. Same symbols, same `∨`, opposite content — if the gate cannot separate these two lines it
is worthless in both directions. -/
def specPerInstanceResidual : Prop :=
  ∀ (hash : List ℤ → ℤ) (xs ys : List ℤ), hash xs = hash ys →
    (xs = ys ∨ SpongeColl hash xs ys)

/-- CLEAN. The break event in HYPOTHESIS position. Whether assuming `¬ SpongeColl` is legitimate is
a FLOOR question and `#floor_ratchet` owns it; this gate asks only whether the CONCLUSION is free,
and must not double-bill the other instrument's surface. -/
def specBreakInHypothesis : Prop :=
  ∀ (hash : List ℤ → ℤ) (xs ys : List ℤ), ¬ SpongeColl hash xs ys → hash xs = hash ys → xs = ys

/-- CLEAN. A POSITIVE claim that the collision exists — this is
`spongeCollision_of_fieldBounded` itself, the pigeonhole fact that ARMS this gate. Flagging it
would make writing the freeness witness a build error, which is the exact failure
`FloorRatchet`'s POSITION rule was introduced to stop (`34854bf62` deleted a satisfiability
witness because naming a floor in a conclusion tripped an instrument). -/
def specBreakClaimed : Prop :=
  ∀ (hash : List ℤ → ℤ), FieldBounded hash → SpongeCollision hash

/-- CLEAN. An ordinary disjunction with no break event in it. Pins that the gate is keyed on
DERIVED freeness witnesses and not on the `∨` connective — a rule that flagged every disjunction in
the tree would be turned off within a week. -/
def specOrdinaryDisjunction : Prop :=
  ∀ n : Nat, n = 0 ∨ 0 < n

/-- CLEAN. The free shape REFUTED rather than assumed — a tombstone with teeth, which the campaign
wants more of, not less. Under `¬` the free disjunct makes the statement UNPROVABLE, not vacuous,
so this is the anti-vacuity pole and it is exempt for the same reason `FloorRatchet.antiFloor`
exempts a refutation. -/
def specFreeUnderNot : Prop :=
  ∀ (hash : List ℤ → ℤ), ¬ OrBreak (SpongeCollision hash) False

end Dregg2.Verify.FreeConclusionSpecimens
