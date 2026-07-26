/-
# `Dregg2.Circuit.CapHashBundleCutoverCheck` — the SEMANTIC TEETH of the 1-felt cap-hash bundle cutover.

`DeployedCapTree.CapHashScheme` carried a REFUTED FLOOR as a FIELD — `chipCR : Compress1CR chipAbsorb`
— which made it UNINHABITABLE at deployed BabyBear parameters (`FactoryBindingFloorRegrounded.
compress1CR_false_babyBear` refutes injectivity for every chip absorb landing in one bounded felt, and
`cap_root.rs::cap_chip_absorb` does) and every `∀ S : CapHashScheme State, …` theorem VACUOUS. It was
the LAST `Compress1CR` field in the tree: its 8-felt sibling `Cap8Scheme` shed `chip8CR` on 07-20 and
`Crypto.CommitmentBinding.Compress2` shed `compress1CR` earlier on 07-25. This module is the shape the
last two cutovers used, applied to the one that was missed.

* **§1 THE FIELD IS GONE, STRUCTURALLY** — the bundle is built from its DATA field alone by an
  anonymous constructor. Any resurrected Prop field (the floor, OR a `noColl` field standing in for
  it — the laundering the bundle-family decision at `Shielded.RealCrypto` §2.0 forbids) fails to
  elaborate here.
* **§2 THE CUTOVER TYPE PINS** — each cured theorem's type is pinned by KERNEL DEFEQ
  (`example : ⟨independently written type⟩ := @original`). A silent weakening, a dropped hypothesis, a
  binder reorder, or a floor resurrection goes RED.
* **§3 NOTHING WAS WEAKENED** — carried by the ONE pre-existing bridge
  `compress1Coll_refutable_of_injective` (old field's type ⟹ new side condition at EVERY pair), so the
  ports are strictly stronger. Deliberately mints NO new `…_of_injective` restatements: each would be
  a fresh declaration on a refuted floor, which is the accrual this campaign exists to stop.
* **§4 THE SIDE CONDITION IS LOAD-BEARING** — dropping it is FALSE, not merely unproved: a degenerate
  chip refutes each unconditional form, and the collision branch is REACHABLE there.
* **§5 THE ACCEPTANCE TEST** — the constructed `deployedCapHashScheme`'s OWN chip REFUTES the deleted
  field. A green build proves nothing here; the inhabitant does.
* **§6 THE FLOOR IS UNREACHABLE** — `#assert_not_depends_on` on the unconditional forms, with an
  `#assert_depends_on` POSITIVE CONTROL on §3's bridge so the rejectors are not vacuous.
-/
import Dregg2.Circuit.DeployedCapTree
import Dregg2.Crypto.FactoryBindingFloorRegrounded
import Dregg2.Tactics

namespace Dregg2.Circuit.CapHashBundleCutoverCheck

open Dregg2.Crypto.CommitmentBinding (Compress1CR Compress1Coll)
open Dregg2.Circuit.DeployedCapTree
  (CapHashScheme CapLeaf leafFields packNode deployedCapHashScheme deployedShapedChip1)

set_option autoImplicit false

/-! ## §1 — THE FIELD IS GONE, STRUCTURALLY.

The bundle is constructed from its DATA field alone. If any Prop field came back — the refuted floor,
or a `noColl` field standing in for it — this anonymous constructor would no longer elaborate. -/

/-- A `CapHashScheme` is EXACTLY a chip absorb: no crypto field to discharge. -/
def dataOnlyCapHashScheme : CapHashScheme Unit := ⟨fun _ => 0⟩

/-! ## §2 — THE CUTOVER TYPE PINS (kernel defeq, re-proved every build). -/

/-- ⚙ CUTOVER CHECK — `capLeafDigest_injective`: same conclusion `l₁ = l₂`, the `chipCR` field replaced
by a PER-INSTANCE `¬ Compress1Coll` at the exact pair `leafCollFind` returns. -/
example :
    ∀ {State : Type} (S : CapHashScheme State) {l₁ l₂ : CapLeaf},
      CapHashScheme.capLeafDigest S l₁ = CapHashScheme.capLeafDigest S l₂ →
      ¬ Compress1Coll S.chipAbsorb (CapHashScheme.leafCollFind l₁ l₂) →
      l₁ = l₂ :=
  @CapHashScheme.capLeafDigest_injective

/-- ⚙ CUTOVER CHECK — `nodeOf_injective`: same conclusion `l₁ = l₂ ∧ r₁ = r₂`, per-instance
non-collision at the two arity-3 blocks the node absorb ran on. -/
example :
    ∀ {State : Type} (S : CapHashScheme State) {l₁ r₁ l₂ r₂ : ℤ},
      CapHashScheme.nodeOf S l₁ r₁ = CapHashScheme.nodeOf S l₂ r₂ →
      ¬ Compress1Coll S.chipAbsorb (CapHashScheme.nodeCollFind l₁ r₁ l₂ r₂) →
      l₁ = l₂ ∧ r₁ = r₂ :=
  @CapHashScheme.nodeOf_injective

/-- ⚙ CUTOVER CHECK — `recomposeUp_inj_of_path`: same conclusion `a = b` (the anti-ghost spine), the
`chipCR`-through-`nodeOf_injective` route replaced by the per-instance non-collision at the ONE level
pair the generic walk lands on. -/
example :
    ∀ {State : Type} (S : CapHashScheme State) (path : List CapHashScheme.Step) {a b : ℤ},
      CapHashScheme.recomposeUp S a path = CapHashScheme.recomposeUp S b path →
      ¬ Compress1Coll S.chipAbsorb (CapHashScheme.recomposeUpFind S a b path) →
      a = b :=
  @CapHashScheme.recomposeUp_inj_of_path

/-! ## §3 — NOTHING WAS WEAKENED — and the proof of that costs ZERO new floor carriers.

The old bundle carried the floor as a field, so the old theorems' content is exactly "…given that
field". The machine-checked statement that nothing was lost is therefore
`CommitmentBinding.compress1Coll_refutable_of_injective`:

    Compress1CR c1 → ∀ p, ¬ Compress1Coll c1 p

— the deleted field's own type IMPLIES the new per-instance side condition AT EVERY PAIR. Drop it into
the `hnc` slot of `capLeafDigest_injective` / `nodeOf_injective` / `recomposeUp_inj_of_path` and each
recovers its verbatim pre-cutover statement. That theorem ALREADY EXISTS in the tree (it was minted for
the `Compress2` cutover), it is grandfathered in `FloorRatchetBaseline`, and it covers every consumer
uniformly — there is no per-theorem work for it to do differently.

⚑ WHY THIS SECTION MINTS NOTHING. The three sibling cutovers each added per-theorem
`…_of_injective` restatements. Every one of those is a declaration whose type takes a hypothesis this
tree PROVES FALSE at deployed BabyBear parameters — a new VACUOUS declaration. Adding three more here
would have grown the carrier count by three to re-say, a fourth time, what one grandfathered theorem
already says. That is precisely the accrual `#floor_ratchet` was built to stop, and a vacuity-removal
lane does not get to be the thing it is removing. HONEST COST, stated rather than hidden: the three
one-step compositions are not themselves elaborated anywhere, so this section is a pointer plus an
argument, not three more machine-checked terms. The §6 positive control below pins that the bridge it
points at genuinely reaches the floor. -/

/-! ## §4 — THE SIDE CONDITION IS LOAD-BEARING (dropping it is FALSE, not merely unproved).

If a "port" quietly dropped the per-instance non-collision hypothesis it would be claiming something
these theorems REFUTE. Both branches of each cured disjunction are therefore live. -/

/-- A degenerate scheme: every absorbed block squeezes to `0`. -/
def constCapHashScheme : CapHashScheme Unit := ⟨fun _ => 0⟩

/-- Two DISTINCT deployed cap leaves (they differ in `target`), used as the concrete counterexample. -/
def leafA : CapLeaf :=
  { slot_hash := 0, target := 0, auth_tag := 0, mask_lo := 0, mask_hi := 0, expiry := 0,
    breadstuff := 0 }

/-- The sibling leaf, differing only in `target`. -/
def leafB : CapLeaf := { leafA with target := 1 }

/-- ⚑ Dropping the side condition would be FALSE: at `constCapHashScheme` the DISTINCT leaves `leafA`
and `leafB` share a digest. So the cured `capLeafDigest_injective` cannot be strengthened back to an
unconditional binding, and a port that dropped the hypothesis would be refuted here. -/
theorem capLeafDigest_unconditional_false :
    ¬ (∀ {State : Type} (S : CapHashScheme State) (l₁ l₂ : CapLeaf),
        CapHashScheme.capLeafDigest S l₁ = CapHashScheme.capLeafDigest S l₂ → l₁ = l₂) := by
  intro h
  exact absurd (h constCapHashScheme leafA leafB rfl) (by decide)

/-- ⚑ The same for the node fold: at the degenerate chip every child pair shares an image, so an
unconditional `nodeOf_injective` would be false. -/
theorem nodeOf_unconditional_false :
    ¬ (∀ {State : Type} (S : CapHashScheme State) (l₁ r₁ l₂ r₂ : ℤ),
        CapHashScheme.nodeOf S l₁ r₁ = CapHashScheme.nodeOf S l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂) := by
  intro h
  exact absurd (h constCapHashScheme 0 0 1 1 rfl).1 (by decide)

/-- And the collision branch is REACHABLE at the degenerate carrier, so neither cured disjunction is a
disguised equality. -/
theorem constCapHashScheme_has_leafColl :
    Compress1Coll constCapHashScheme.chipAbsorb (CapHashScheme.leafCollFind leafA leafB) :=
  ⟨by decide, rfl⟩

/-- The node blocks likewise genuinely collide at the degenerate chip. -/
theorem constCapHashScheme_has_nodeColl :
    Compress1Coll constCapHashScheme.chipAbsorb (CapHashScheme.nodeCollFind 0 0 1 1) :=
  ⟨by decide, rfl⟩

/-! ## §5 — ⚑ THE ACCEPTANCE TEST: the constructed inhabitant REFUTES the deleted field.

This is the whole point. Before the cutover no `CapHashScheme` value existed anywhere in the tree, so
every `∀ S : CapHashScheme State, …` theorem was vacuously true. -/

/-- ⚑ **THE REFUTATION TOOTH — the deployed inhabitant's own chip REFUTES the deleted field.** Had
`chipCR : Compress1CR chipAbsorb` survived, THIS value could not have been built: the structure was
uninhabitable at deployed parameters and its whole `∀ S`-surface was vacuous. The very function the
teeth refute now INHABITS the structure. -/
theorem deployedCapHashScheme_chip_not_Compress1CR :
    ¬ Compress1CR deployedCapHashScheme.chipAbsorb :=
  Dregg2.Crypto.FactoryBindingFloorRegrounded.compress1CR_false_babyBear _
    Dregg2.Circuit.DeployedCapTree.deployedShapedChip1_bounded

/-- ⚑ AND THE GENERAL FALSIFIER STILL BITES: a bundle that RE-ADDED a BabyBear-range-bounded
`Compress1CR` field would be uninhabitable again — stated over the field's TYPE at the deployed chip,
so this is the check the next bundle in this shape has to pass.

Spelled `¬ Compress1CR …` rather than `Compress1CR … → False`: definitionally the same statement and
the same proof term, but the negation is what `Verify.FloorRatchet.antiFloor` recognises as
anti-floor content now that it no longer keys on binder POSITION (the B4 hole). -/
theorem deployedCapHashScheme_field_would_be_uninhabitable :
    ¬ Compress1CR deployedCapHashScheme.chipAbsorb :=
  Dregg2.Crypto.FactoryBindingFloorRegrounded.compress1CR_field_uninhabitable_babyBear _
    Dregg2.Circuit.DeployedCapTree.deployedShapedChip1_bounded

/-- ⚑ THE TOOTH FIRES AT THE INHABITANT — the spine anti-ghost, INSTANTIATED at a real deployed value,
which is the operation the `∀ S : CapHashScheme State` form could never actually be performed for. -/
example (path : List CapHashScheme.Step) {a b : ℤ}
    (h : CapHashScheme.recomposeUp deployedCapHashScheme a path
       = CapHashScheme.recomposeUp deployedCapHashScheme b path) :
    a = b ∨ Compress1Coll deployedCapHashScheme.chipAbsorb
      (CapHashScheme.recomposeUpFind deployedCapHashScheme a b path) :=
  Dregg2.Circuit.DeployedCapTree.deployed_recomposeUp_binds_or_collides path h

/-- NON-VACUITY at the inhabitant, computably: distinct leaves MOVE the deployed 1-felt digest, so the
binding is not carried by a collapsing chip. -/
theorem deployedCapHashScheme_separates_leaves :
    CapHashScheme.capLeafDigest deployedCapHashScheme leafA
      ≠ CapHashScheme.capLeafDigest deployedCapHashScheme leafB := by decide

/-! ## §6 — THE FLOOR IS UNREACHABLE from the cured theorems.

The unconditional (`…_or_collides`) forms are the ones that must be clear of the floor outright; the
side-condition forms mention the floor's REFUTATION vocabulary only. A resurrection of the floor
inside any of these proofs is a build ERROR here. -/

#assert_axioms Dregg2.Circuit.DeployedCapTree.CapHashScheme.capLeafDigest_binds_or_collides
#assert_not_depends_on Dregg2.Circuit.DeployedCapTree.CapHashScheme.capLeafDigest_binds_or_collides
  [Dregg2.Crypto.CommitmentBinding.Compress1CR,
   Dregg2.Crypto.CommitmentBinding.Reference.refCompress1]

#assert_axioms Dregg2.Circuit.DeployedCapTree.CapHashScheme.nodeOf_binds_or_collides
#assert_not_depends_on Dregg2.Circuit.DeployedCapTree.CapHashScheme.nodeOf_binds_or_collides
  [Dregg2.Crypto.CommitmentBinding.Compress1CR,
   Dregg2.Crypto.CommitmentBinding.Reference.refCompress1]

#assert_axioms Dregg2.Circuit.DeployedCapTree.CapHashScheme.recomposeUp_binds_or_collides
#assert_not_depends_on Dregg2.Circuit.DeployedCapTree.CapHashScheme.recomposeUp_binds_or_collides
  [Dregg2.Crypto.CommitmentBinding.Compress1CR,
   Dregg2.Crypto.CommitmentBinding.Reference.refCompress1]

#assert_axioms deployedCapHashScheme_chip_not_Compress1CR

/-! ### §6-controls — the rejectors above are NOT vacuous.

A `#assert_not_depends_on` that walks a closure the floor was never in reports CLEAN for free. These
POSITIVE control proves the walk genuinely reaches the floor when the floor IS there: §3's bridge
`compress1Coll_refutable_of_injective` takes the deleted field's type as a hypothesis, so the floor
constant MUST appear in its closure. Clean-above + reached-here is the pair that makes the guard mean
something — and the control costs no new carrier, because that bridge already existed. -/

#assert_depends_on Dregg2.Crypto.CommitmentBinding.compress1Coll_refutable_of_injective
  [Dregg2.Crypto.CommitmentBinding.Compress1CR]

#assert_all_clean [
  capLeafDigest_unconditional_false,
  nodeOf_unconditional_false,
  constCapHashScheme_has_leafColl,
  constCapHashScheme_has_nodeColl,
  deployedCapHashScheme_chip_not_Compress1CR,
  deployedCapHashScheme_field_would_be_uninhabitable,
  deployedCapHashScheme_separates_leaves
]

end Dregg2.Circuit.CapHashBundleCutoverCheck
