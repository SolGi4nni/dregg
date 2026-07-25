/-
# Dregg2.Circuit.BundleCutoverCheck — the SEMANTIC teeth of the 2026-07-25 BUNDLE cutover.

Three structures carried a REFUTED FLOOR as a FIELD, which made them UNINHABITABLE at deployed
BabyBear parameters and every theorem quantifying over them VACUOUS:

  * `Shielded.RealCrypto.Poseidon2Tree`   — `spongeCR   : Poseidon2SpongeCR sponge`
  * `Crypto.CommitmentBinding.Compress2`  — `compress1CR : Compress1CR compress1`
  * `Circuit.DigestPortal.PortalBundle`   — `cellLeafInj : cellLeafInjective CH`  (whole bundle DELETED)

The design decision that governs the family — DELETE THE FIELD, never swap in a `noColl` field — and
the reason the answer differs from the one threaders get, is recorded at `Shielded.RealCrypto` §2.0.

## What is pinned here, and what turns the build red

  **§1 THE FIELD IS GONE, STRUCTURALLY.** Each bundle is built by anonymous constructor from its DATA
  ALONE. Resurrecting a Prop field — of any type, floor or `noColl` — makes these fail to elaborate.

  **§2 THE CUTOVER TYPE PINS.** `example : ⟨new type⟩ := @original` re-proves BY KERNEL DEFEQ, on every
  build, that each in-place original has exactly the cured type: SAME conclusion, floor gone, the
  per-instance side condition and nothing else. A silent weakening or a binder reorder reddens HERE.

  **§3 NOTHING WAS WEAKENED.** For each cured theorem, its ORIGINAL statement is RE-DERIVED from the
  deleted field's own type. So the old hypothesis IMPLIES the new one and the ported theorems are
  strictly stronger — a `PORT MAY NOT WEAKEN A THEOREM` check, discharged as a proof rather than
  asserted in a comment.

  **§4 THE SIDE CONDITION IS LOAD-BEARING.** Dropping it is not merely unproved, it is FALSE: a
  degenerate carrier collides, so a "port" that dropped the condition would be refutable here.

  **§5 THE ACCEPTANCE TEST.** Each cured bundle has a CONSTRUCTED DEPLOYED INHABITANT whose own carrier
  REFUTES the deleted field. This — not a green build — is what measures that the deletion bought
  something: the very function the teeth refute now inhabits the structure.

  **§6 THE FLOOR IS UNREACHABLE.** `#assert_not_depends_on` pins each cured theorem's proof-term
  closure clear of the refuted floor, so a floor-binder resurrection is a build error, not a review
  miss.
-/
import Dregg2.Shielded.RealCrypto
import Dregg2.Circuit.DigestPortal
import Dregg2.Crypto.FactoryBindingFloorRegrounded
import Dregg2.Tactics

namespace Dregg2.Circuit.BundleCutoverCheck

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR SpongeColl)
open Dregg2.Shielded.RealCrypto (Poseidon2Tree MemberAtRoot)
open Dregg2.Crypto.CommitmentBinding (Compress1CR Compress1Coll Compress2)

set_option autoImplicit false

/-! ## §1 — THE FIELD IS GONE, STRUCTURALLY.

Each bundle is constructed from its DATA fields alone. If any Prop field came back — the refuted floor,
or a `noColl` field standing in for it — these anonymous constructors would no longer elaborate. -/

/-- A `Poseidon2Tree` is EXACTLY a sponge: no crypto field to discharge. -/
def dataOnlyTree : Poseidon2Tree := ⟨fun _ => 0⟩

/-- A `Compress2` is EXACTLY (compression, packing, packing-injectivity, factorization): the
`compress1CR` field is gone, and the three survivors are all STRUCTURAL, not crypto. -/
def dataOnlyCompress2 : Compress2 (fun _ _ => 0) where
  compress1 := fun _ => 0
  pack₂ := fun a b => [a, b]
  pack₂_inj := by
    intro a b c d h
    exact ⟨(List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩
  factor := fun _ _ => rfl

/-! ## §2 — THE CUTOVER TYPE PINS (kernel defeq, re-proved every build). -/

/-- ⚙ CUTOVER CHECK — `Poseidon2Tree.root_binds`: same conclusion `l₁ = l₂`, the `spongeCR` field
replaced by a PER-INSTANCE `¬ SpongeColl` at the exact pair `rootCollFind` returns. -/
example :
    ∀ (T : Poseidon2Tree) {l₁ l₂ : List ℤ},
      T.root l₁ = T.root l₂ →
      ¬ SpongeColl T.sponge (Poseidon2Tree.rootCollFind l₁ l₂) →
      l₁ = l₂ :=
  @Dregg2.Shielded.RealCrypto.Poseidon2Tree.root_binds

/-- ⚙ CUTOVER CHECK — `forged_set_forces_collision`: same conclusion `forged = leaves`. -/
example :
    ∀ (T : Poseidon2Tree) {leaves forged : List ℤ},
      T.root forged = T.root leaves →
      ¬ SpongeColl T.sponge (Poseidon2Tree.rootCollFind forged leaves) →
      forged = leaves :=
  @Dregg2.Shielded.RealCrypto.forged_set_forces_collision

/-- ⚙ CUTOVER CHECK — `nonmember_refused`: same conclusion `False` (a non-member IS refused). -/
example :
    ∀ (T : Poseidon2Tree) {root leaf : ℤ} {leaves leaves' : List ℤ},
      root = T.root leaves →
      MemberAtRoot T root leaf leaves' →
      leaf ∉ leaves →
      ¬ SpongeColl T.sponge (Poseidon2Tree.rootCollFind leaves' leaves) →
      False :=
  @Dregg2.Shielded.RealCrypto.nonmember_refused

/-- ⚙ CUTOVER CHECK — `compressInjective_of_compress2`: same conclusion `compressInjective h`, the
`compress1CR` field replaced by a per-instance `¬ Compress1Coll` at the packed blocks. -/
example :
    ∀ {h : ℤ → ℤ → ℤ} (R : Compress2 h),
      (∀ a b c d : ℤ, ¬ Compress1Coll R.compress1 (R.nodeCollFind a b c d)) →
      Dregg2.Circuit.StateCommit.compressInjective h :=
  @Dregg2.Crypto.CommitmentBinding.compressInjective_of_compress2

/-! ## §3 — NOTHING WAS WEAKENED: each ORIGINAL statement is RE-DERIVED from the deleted field.

The old bundles carried the floor as a field, so the old theorems' content is exactly "…given that
field". These re-derivations take the field's TYPE as a hypothesis and recover the original conclusion
with NO side condition — which is the machine-checked form of "the old hypothesis implies the new one,
so the ported theorem is strictly stronger". -/

/-- The ORIGINAL `Poseidon2Tree.root_binds` (no side condition), recovered from the deleted field's
own type. Whatever the pre-cutover theorem proved, the cured one still proves. -/
theorem root_binds_of_injective (T : Poseidon2Tree) (hCR : Poseidon2SpongeCR T.sponge)
    {l₁ l₂ : List ℤ} (h : T.root l₁ = T.root l₂) : l₁ = l₂ :=
  T.root_binds h (Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _)

/-- The ORIGINAL `forged_set_forces_collision`, recovered the same way. -/
theorem forged_set_forces_collision_of_injective (T : Poseidon2Tree) (hCR : Poseidon2SpongeCR T.sponge)
    {leaves forged : List ℤ} (hforge : T.root forged = T.root leaves) : forged = leaves :=
  Dregg2.Shielded.RealCrypto.forged_set_forces_collision T hforge
    (Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _)

/-- The ORIGINAL `nonmember_refused`, recovered the same way. -/
theorem nonmember_refused_of_injective (T : Poseidon2Tree)
    (hCR : Poseidon2SpongeCR T.sponge) {root leaf : ℤ} {leaves leaves' : List ℤ}
    (hcommit : root = T.root leaves) (hclaim : MemberAtRoot T root leaf leaves')
    (hnon : leaf ∉ leaves) : False :=
  Dregg2.Shielded.RealCrypto.nonmember_refused T hcommit hclaim hnon
    (Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _)

/-- The ORIGINAL `compressInjective_of_compress2` (no side condition), recovered from the deleted
`compress1CR` field's own type. -/
theorem compress2_binds_of_injective {h : ℤ → ℤ → ℤ} (R : Compress2 h)
    (hCR : Compress1CR R.compress1) : Dregg2.Circuit.StateCommit.compressInjective h :=
  Dregg2.Crypto.CommitmentBinding.compressInjective_of_compress2 R
    (fun _ _ _ _ => Dregg2.Crypto.CommitmentBinding.compress1Coll_refutable_of_injective hCR _)

/-! ## §4 — THE SIDE CONDITION IS LOAD-BEARING (dropping it is FALSE, not merely unproved).

If a "port" quietly dropped the per-instance non-collision hypothesis, it would be claiming something
these two theorems REFUTE. Both branches of each cured disjunction are therefore live: the side
condition is satisfiable at an injective carrier (`RealCrypto.refTree_no_spongeColl`,
`CommitmentBinding.Reference.refCompress2_no_coll`) and refutable at a colliding one. -/

/-- A degenerate tree: every leaf set squeezes to `0`. -/
def constTree : Poseidon2Tree := ⟨fun _ => 0⟩

/-- ⚑ Dropping the side condition would be FALSE: at `constTree` the distinct leaf sets `[0]` and `[1]`
share a root. So the cured `root_binds` cannot be strengthened back to an unconditional binding, and a
port that dropped the hypothesis would be refuted here. -/
theorem root_binds_unconditional_false :
    ¬ (∀ (T : Poseidon2Tree) (l₁ l₂ : List ℤ), T.root l₁ = T.root l₂ → l₁ = l₂) := by
  intro h
  exact absurd (h constTree [0] [1] rfl) (by decide)

/-- ⚑ The same for the node compression: at `dataOnlyCompress2` every input pair shares an image, so an
unconditional `compressInjective` would be false. -/
theorem compressInjective_of_compress2_unconditional_false :
    ¬ (∀ {h : ℤ → ℤ → ℤ}, Compress2 h → Dregg2.Circuit.StateCommit.compressInjective h) := by
  intro h
  exact absurd ((h dataOnlyCompress2 0 0 1 1 rfl).1) (by decide)

/-- And the collision branch is REACHABLE at the degenerate carriers, so neither cured disjunction is a
disguised equality. -/
theorem constTree_has_spongeColl :
    SpongeColl constTree.sponge ([0], [1]) := ⟨by decide, rfl⟩

/-! ## §5 — THE ACCEPTANCE TEST: constructed deployed inhabitants that REFUTE the deleted fields.

These are the whole point. Before the cutover no such value existed, so every `∀ T : Poseidon2Tree, …`
and `∀ R : Compress2 h, …` theorem was vacuously true. -/

/-- The deployed `Poseidon2Tree` inhabitant's own sponge refutes the deleted `spongeCR` field. -/
example : ¬ Poseidon2SpongeCR Dregg2.Shielded.RealCrypto.deployedPoseidon2Tree.sponge :=
  Dregg2.Shielded.RealCrypto.deployedPoseidon2Tree_sponge_not_Poseidon2SpongeCR

/-- The deployed `Compress2` inhabitant's own compression refutes the deleted `compress1CR` field. -/
example : ¬ Compress1CR Dregg2.Crypto.CommitmentBinding.deployedCompress2.compress1 :=
  Dregg2.Crypto.FactoryBindingFloorRegrounded.deployedCompress2_compress1_not_Compress1CR

/-- ⚑ AND THE TOOTH FIRES AT THE INHABITANT — the anti-forgery statement, INSTANTIATED at a real
deployed value, which is the operation the `∀ T` form could never actually be performed for. -/
example {leaves forged : List ℤ}
    (hforge : Dregg2.Shielded.RealCrypto.deployedPoseidon2Tree.root forged
            = Dregg2.Shielded.RealCrypto.deployedPoseidon2Tree.root leaves) :
    forged = leaves
    ∨ SpongeColl Dregg2.Shielded.RealCrypto.deployedPoseidon2Tree.sponge
        (Poseidon2Tree.rootCollFind forged leaves) :=
  Dregg2.Shielded.RealCrypto.deployed_forged_set_is_honest_or_collides hforge

/-! ## §6 — THE FLOOR IS UNREACHABLE from the cured theorems.

The unconditional (`…_or_collides`) forms are the ones that must be clear of the floor outright; the
side-condition forms mention the floor's REFUTATION vocabulary only. A resurrection of the floor binder
inside any of these proofs is a build ERROR here. -/

#assert_axioms Dregg2.Shielded.RealCrypto.Poseidon2Tree.root_binds_or_collides
#assert_not_depends_on Dregg2.Shielded.RealCrypto.Poseidon2Tree.root_binds_or_collides
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR,
   Dregg2.Circuit.Poseidon2Binding.Reference.refSponge]

#assert_axioms Dregg2.Shielded.RealCrypto.forged_set_is_honest_or_collides
#assert_not_depends_on Dregg2.Shielded.RealCrypto.forged_set_is_honest_or_collides
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR,
   Dregg2.Circuit.Poseidon2Binding.Reference.refSponge]

#assert_axioms Dregg2.Crypto.CommitmentBinding.compressInjective_of_compress2_or_collides
#assert_not_depends_on Dregg2.Crypto.CommitmentBinding.compressInjective_of_compress2_or_collides
  [Dregg2.Crypto.CommitmentBinding.Compress1CR,
   Dregg2.Crypto.CommitmentBinding.Reference.refCompress1]

#assert_axioms Dregg2.Shielded.RealCrypto.deployedPoseidon2Tree_sponge_not_Poseidon2SpongeCR
#assert_axioms Dregg2.Crypto.FactoryBindingFloorRegrounded.deployedCompress2_compress1_not_Compress1CR

/-! ### §6-controls — the rejectors above are NOT vacuous.

A `#assert_not_depends_on` that walks a closure the floor was never in reports CLEAN for free. These
POSITIVE controls prove the walk genuinely reaches the floor when the floor IS there: the §3
re-derivations take the deleted field's type as a hypothesis, so the floor constant MUST appear in
their closures. Clean-above + reached-here is the pair that makes the guard mean something. -/

#assert_depends_on root_binds_of_injective
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_depends_on compress2_binds_of_injective
  [Dregg2.Crypto.CommitmentBinding.Compress1CR]

#assert_all_clean [
  root_binds_of_injective,
  forged_set_forces_collision_of_injective,
  nonmember_refused_of_injective,
  compress2_binds_of_injective,
  root_binds_unconditional_false,
  compressInjective_of_compress2_unconditional_false,
  constTree_has_spongeColl
]

end Dregg2.Circuit.BundleCutoverCheck
