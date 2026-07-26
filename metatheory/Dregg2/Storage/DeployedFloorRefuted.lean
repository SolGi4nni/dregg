/-
# The deployed storage hash REFUTES the floor its own theorem assumes

`Dregg2.Storage.contentRootDeployed_injective` is gated on
`Poseidon2Binding.Poseidon2SpongeCR poseidon2Hash`. That floor is **literal injectivity**

    Poseidon2SpongeCR (sponge : List ℤ → ℤ) : Prop := ∀ xs ys, sponge xs = sponge ys → xs = ys

and the deployed `poseidon2Hash` **provably violates it**. So the one theorem in the tree that
instantiates this floor at a concrete hash is **vacuously true at deployment**.

## Why it fails, and why no encoder fix repairs it

`poseidon2Hash : List ℤ → ℤ` factors through `UInt64`, so its image is *finite* while its domain is
*infinite*. Exact injectivity is therefore unsatisfiable at **any** encoding. The floor is
mis-specified, not mis-implemented — which is why the repair was a CUTOVER onto the collision game
(`Storage.DeployedFloorRegrounded`) and not a better encoder.

⛑ **THE WITNESS MOVED, THE REFUTATION DID NOT (2026-07-26).** Until the encoder repair, the free
collision was `poseidon2Hash [-1] = poseidon2Hash [0]`: the limb map clamped through `Int.toNat`, so
`-1` and `0` — two DIFFERENT BabyBear elements — became one limb. That was a plain bug and it is
FIXED (`Storage.Deployed.canonLimb`, and `Storage.Deployed.clampLimb_merges_negative` keeps the
defect nameable). The floor is still refuted, now at a witness that is not a bug at all:
`canonLimb` is a REDUCTION mod `p`, so `poseidon2Hash [0] = poseidon2Hash [p]` by `rfl`. Two integers
congruent mod `p` denote one field element; the encoder is right and the FLOOR is still wrong. That
is the sharpest possible statement of "mis-specified, not mis-implemented" — the refutation survived
its own bug being fixed.

## Why our gates did not see it

`#assert_axioms contentRootDeployed_injective` **passes**. Axiom hygiene checks what a proof *rests
on*; it cannot see that a hypothesis is false. This is the same structural blindness that let the
apex premise sit empty (`docs/WOUND-apex-premise-vacuity-2026-07-24.md`), one level lower down: there
the premise was uninhabitable, here the *floor* is refutable.

The standing rule this violates: **a floor must be SATISFIABLE and REFUTABLE but NOT PROVABLE.**
`Poseidon2SpongeCR` is satisfiable *abstractly* — an injection `List ℤ → ℤ` exists, both being
countably infinite — which is why the ~30 modules carrying it as an abstract hypothesis are NOT
vacuous. It is refutable *at any concrete hash with finite image*, which is why instantiating it is.

## Scope, stated exactly

* **Abstract carriers are FINE.** Every `(hCR : Poseidon2SpongeCR sponge)` over an abstract `sponge`
  — including the STARK apex — remains a meaningful conditional. Nothing here empties them.
* **Exactly ONE concrete instantiation exists** (`Dregg2/Storage/Deployed.lean:45`), and it is the
  one this module refutes.
* What this does **not** do: repair the floor. The right shape is a *computational* collision
  resistance — the tree already has that machinery (`HashFloorHonesty.CollisionResistant`, the ROM
  query floors, `birthday_cond`), and `Dregg2/Crypto/CommitmentBinding.lean:75` already records that
  the `⊤` form of that floor "is itself false". Routing the deployed storage claim onto a
  computational floor is a separate change and is NOT made here.
-/
import Dregg2.Storage.Deployed
import Dregg2.Tactics

namespace Dregg2.Storage.DeployedFloorRefuted

open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Storage

/-- The collision, by `rfl`: `canonLimb` reduces mod `p`, so `0` and `p` are the SAME field element
and the deployed hash cannot distinguish the two integer spellings. No property of `p2compress` is
used. Unlike the pre-2026-07-26 witness (`[-1]` vs `[0]`, an `Int.toNat` clamp bug — see
`Storage.Deployed.clampLimb_merges_negative`) this one is not a defect: it is what reducing into a
field MEANS, and it refutes the floor anyway. -/
theorem deployed_collides : poseidon2Hash [(0 : Int)] = poseidon2Hash [(2013265921 : Int)] := rfl

/-- **THE REPAIR IS LOAD-BEARING, NOT COSMETIC.** The pre-fix witness is DEAD: `-1` and `0` now
encode to different limbs, so the old collision is no longer available for free. Stated as a
`decide` over the encoder rather than as prose, so re-clamping goes red here too. -/
theorem clamp_witness_is_dead :
    Storage.canonLimb (-1) ≠ Storage.canonLimb 0 := Storage.canonLimb_separates_negative

/-- **THE TOOTH.** The deployed hash refutes the injectivity floor its own theorem assumes. -/
theorem deployed_floor_false : ¬ Poseidon2SpongeCR poseidon2Hash := by
  intro h
  have := h [(0 : Int)] [(2013265921 : Int)] deployed_collides
  simp at this

/-- The consequence, stated so it cannot be read up: anything proved from the floor at the DEPLOYED
hash is vacuous — the hypothesis can never be supplied. -/
theorem deployed_instantiation_is_vacuous (P : Prop) :
    Poseidon2SpongeCR poseidon2Hash → P :=
  fun h => absurd h deployed_floor_false

/-- The floor is NOT unsatisfiable in general — so the ~30 modules carrying it over an ABSTRACT
sponge are not vacuous. Witness: the identity on a domain where the sponge is injective. This is
what makes `deployed_floor_false` a statement about the DEPLOYED encoder rather than about the
predicate. -/
theorem floor_is_satisfiable_abstractly :
    ∃ sponge : List ℤ → ℤ, Poseidon2SpongeCR sponge := by
  classical
  obtain ⟨f, hf⟩ := (inferInstance : Countable (List ℤ)).exists_injective_nat
  refine ⟨fun xs => (f xs : ℤ), fun xs ys h => hf ?_⟩
  exact Nat.cast_inj.mp h

#assert_axioms deployed_collides
#assert_axioms clamp_witness_is_dead
#assert_axioms deployed_floor_false
#assert_axioms deployed_instantiation_is_vacuous
#assert_axioms floor_is_satisfiable_abstractly

end Dregg2.Storage.DeployedFloorRefuted
