/-
# Dregg2.Verify.FloorRatchetSpecimens — the ratchet's own SELF-TEST fixtures.

`#floor_ratchet`'s exemption predicate (`FloorRatchet.antiFloor`) decides which declarations are
ANTI-floor content and therefore never gated. A predicate that degenerates in EITHER direction is
invisible from a green build:

  * degenerate to `true` — every declaration is "a refutation", the gate exempts the whole tree and
    passes forever. This is not hypothetical: the shipped rule exempted any declaration whose
    conclusion was `False`, and 113 of them were contrapositive SOUNDNESS claims
    (`consensus_safe_under_floor`, `closure_rejects_overdebit_avail`, `lightclient_no_fork`, …),
    laundered out of the census by a spelling accident.
  * degenerate to `false` — refutations start tripping the gate, so the campaign's own anti-floor
    work becomes a build error and the only way forward is to grandfather it. Also invisible: the
    gate still passes on a tree where nobody has written a new refutation this week.

So the predicate is not trusted on the strength of the build being green. This module holds five
`Prop`-valued defs whose VALUES are declaration TYPES with a known-correct verdict, and `surface`
elaborates each one on EVERY root build and hard-errors if the verdict moved. The specimens are
the classification's fixed points, on the record and in the diff.

⚑ They are EXCLUDED from the carrier surface by name (`FloorRatchet.specimens`) — they are the
instrument's test fixtures, not tree content, and counting them would put five permanent entries in
a baseline whose only healthy direction is shorter.

⚑ They live in their own module, not in `Verify/FloorRatchet.lean`, because the gate's machinery is
imported BY the root and therefore cannot import the tree it measures. `surface` resolves these by
raw `Name` out of the environment exactly the way it resolves `sentinelFloors`, and fails closed if
one is missing.

## THE RULE the specimens pin

A declaration is ANTI-FLOOR — exempt — exactly when it REFUTES floor content and ASSUMES none:

  **NO binder carries floor content, AND the conclusion is `¬ F …` for floor content `F`.**

Everything else assumes a refuted floor on the way to its conclusion, and is vacuous at deployed
BabyBear parameters no matter how the conclusion is spelled.

⚑ BINDER POSITION IS NOT CONSULTED. The rule this replaced also exempted a `False` conclusion whose
INNERMOST binder was the floor, on the (correct) reasoning that `Γ → F → False` IS `Γ → ¬ F`. It
was still a hole, because ORDER IS A SPELLING THE AUTHOR CONTROLS: the identical soundness claim
was gated with its floor hypothesis first and EXEMPT with it last, and the gate's error text
coached the swap. `specB4BinderOrderLaundry` and `specB4UncurriedShape` are that hole, pinned
GATED. What was actually sitting on it were `HermineMSIS.no_forgery_under_msis` and
`HermineSelfTargetMSIS.no_forgery_under_msis_selftarget` — "the deployed threshold signature cannot
be forged", on `Lattice.MSISHard`, a floor `CryptoFloorTeeth` refutes.

The price is one spelling: a genuine refutation written uncurried now trips the gate and must be
restated as `¬ F …` (definitionally equal, zero proof work). That is the FAIL-CLOSED direction —
the old rule's spelling-dependence let a vacuous security claim out; this one's can only cost an
author a one-line restatement. `specRefutationManyHyp` pins that the tightening did NOT degenerate
into "only single-binder refutations are exempt".
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.CircuitSoundness

set_option autoImplicit false

namespace Dregg2.Verify.FloorRatchetSpecimens

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.CircuitSoundness (CommitSurface)

/-- EXEMPT. The canonical refutation spelling: refutes a floor, assumes none. This is the shape of
`poseidon2SpongeCR_false_babyBear`, and the campaign wants more of it — writing one must never be a
build error. -/
def specRefutation : Prop :=
  ∀ f : List ℤ → ℤ, (∀ xs, 0 ≤ f xs) → ¬ Poseidon2SpongeCR f

/-- EXEMPT, and the control against OVER-tightening. A refutation may carry any number of
NON-floor hypotheses — this is the shape of `collisionResistant_false_of_compressing` and of every
`*_false_of_finite_range` in the tree. A rule that only exempted single-binder refutations would
make the campaign's own anti-floor work a build error, so that degeneration is pinned out here. -/
def specRefutationManyHyp : Prop :=
  ∀ f : List ℤ → ℤ, (∀ xs, 0 ≤ f xs) → (∀ xs, f xs < 2013265921) → f [] = f [0] →
    ¬ Poseidon2SpongeCR f

/-- GATED. **B4** — the same statement UNCURRIED. `Γ → Poseidon2SpongeCR f → False` IS `Γ → ¬ …`
by definition, and the old rule exempted it for exactly that reason. The trouble is that this
`Expr` is INDISTINGUISHABLE from `specB4BinderOrderLaundry` below — a soundness claim with its
floor hypothesis moved last — so exempting the spelling exempts the laundry too. The honest
refutation is `specRefutation`, one `¬` away, with the same proof term. -/
def specB4UncurriedShape : Prop :=
  ∀ f : List ℤ → ℤ, (∀ xs, 0 ≤ f xs) → Poseidon2SpongeCR f → False

/-- GATED. **B4, the live shape.** The adversarial probe that walked through the old rule: a
contrapositive SOUNDNESS claim whose refuted floor happens to be the LAST binder. Nothing
distinguishes it from an uncurried refutation, which is why the rule stopped keying on position.
`HermineMSIS.no_forgery_under_msis` is this, with nine hypotheses instead of one. -/
def specB4BinderOrderLaundry : Prop :=
  ∀ f : List ℤ → ℤ, f [1] = f [2] → Poseidon2SpongeCR f → False

/-- GATED. **B4 × B1** — floor innermost, conclusion a negation of a DIFFERENT floor. Both the
`False` route and the `¬ …` route reordered at once; neither position saves it. -/
def specB4NegOtherFloorReordered : Prop :=
  ∀ f g : List ℤ → ℤ, f [1] = f [2] → Poseidon2SpongeCR f →
    ¬ Dregg2.Circuit.StateCommit.compressNInjective g

/-- GATED. **B1** — the negation exemption used as a laundry: a refuted floor in HYPOTHESIS
position, on a declaration that merely happens to CONCLUDE a negation. Nothing about the deployed
system follows from it. -/
def specB1NegationLaundry : Prop :=
  ∀ f g : List ℤ → ℤ, Poseidon2SpongeCR f → ¬ Poseidon2SpongeCR g

/-- GATED. **B2** — the `False` exemption used as a laundry. Reads as a real claim (`¬ (0 = 1)`
about whatever the middle hypothesis says), proved under a hypothesis this tree refutes. `False` is
the most permissive conclusion in the language; exempting on it is exempting on nothing. -/
def specB2FalseLaundry : Prop :=
  ∀ f : List ℤ → ℤ, Poseidon2SpongeCR f → (0 : ℤ) = 1 → False

/-- GATED, and a CARRIER. **B3** — the floor arrives through a grandfathered STRUCTURE instead of a
binder. `CommitSurface` carries four refuted floors as FIELDS, so no inhabitant exists at deployed
parameters and this says exactly as little as a floor binder does. -/
def specB3BundleLaundry : Prop :=
  ∀ _S : CommitSurface, ∀ xs ys : List ℤ, xs = ys

end Dregg2.Verify.FloorRatchetSpecimens
