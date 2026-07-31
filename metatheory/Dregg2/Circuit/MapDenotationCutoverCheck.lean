/-
# `Dregg2.Circuit.MapDenotationCutoverCheck` — the TEETH of the map-op DENOTATION cutover.

On 2026-07-30 `DescriptorIR2.opensTo` / `writesTo` — hence `MapOp.holdsAt`, hence the `.mapOp` arm of
`Satisfied2`, hence every `AlgoStarkSound*` conclusion — were repointed from the RETIRED arity-2 dense
binary-Merkle fold onto the DEPLOYED arity-3 indexed-Merkle commitment
(`circuit/src/heap_root.rs`: `HEAP_LEAF_ARITY = 3`, `relink_next_addrs`, sparse zero padding).

This file is the instrument that makes that claim FALSIFIABLE on every build. It is not prose about
the cutover; each item below goes RED if the cutover is reverted, weakened, or quietly re-pointed.

## Substrate
**Model/denotation only.** Nothing here authors an AIR, a gate or a gadget.

## The four teeth

  * **§1 THE PREMISE IS INHABITED AT DEPLOYED PARAMETERS.** The headline question. A witness of
    `DescriptorIR2.opensTo` at the DEPLOYED depth (`MAP_TREE_DEPTH = 16`) over the DEPLOYED sparse
    occupancy (ONE live leaf in a `2^16` tree, which is what `CanonicalHeapTree::new` builds) at the
    DEPLOYED terminal sentinel (`SENTINEL_MAX = 2013265920`). Before the cutover no such witness
    existed and none could: the denotation demanded a DENSE vector of `2^16` strictly increasing keys
    committed by an arity-2 fold, which the deployed prover never computes.
  * **§2 THE SEPARATIONS SURVIVE.** The arity-3 leaf and the arity-2 leaf are still different objects,
    and their roots still separate. These are PERMANENT facts; if any of them went green-by-collapse
    the cutover would have unified two commitments that are not the same, which is the failure mode
    the whole campaign exists to detect.
  * **§3 THE DRIFT GUARD.** `MapOp.holdsAt`'s proof-term closure no longer reaches `Heap.leafOf` or
    `MapMerkleRoot.mapRoot`, and DOES reach `imtLeafHash` and `padImtRoot`. Positive controls
    included, per `Dregg2.Tactics`' own warning that a walk over a closure the constant was never in
    reports clean for free.
  * **§4 THE ANTI-GHOST IS FLOOR-FREE.** `opensTo_functional` / `writesTo_functional` do not reach
    `Poseidon2SpongeCR` — which is PROVED FALSE at deployed BabyBear
    (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so a route through it would make the
    deployed anti-ghost vacuous at the prover's own parameters. This is the ∃-hoist half of the
    change, and it is the half that de-vacuums: moving the arity alone would have re-based the same
    vacuous theorems onto a new commitment.

## ⚠ What this file does NOT check, stated so nobody reads it as more than it is
It does not check that the deployed AIR FORCES the denotation for every kind. Two kinds provably
cannot be forced, for Rust-side reasons: `.insert` (op=3) constrains only the post-root, and
`.aafiInsert`'s post side folds the physical append-order layout. Both are proved in
`MapKindImtGates`; neither is a Lean defect and neither is repaired here.
-/
import Dregg2.Circuit.MapInsertImtRepoint
import Dregg2.Circuit.MapKindImtGates
import Dregg2.Tactics

namespace Dregg2.Circuit.MapDenotationCutoverCheck

open Dregg2.Substrate
open Dregg2.Circuit.DescriptorIR2 (opensTo writesTo MAP_TREE_DEPTH MAP_SENTINEL mapSchema mapTeeth)
open Dregg2.Circuit.DeployedMapDenotation

set_option autoImplicit false

/-! ## §1 — ★★ THE PREMISE IS INHABITED AT DEPLOYED PARAMETERS.

⚠ Every root below is NAMED (`padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH biteHeap`) and never
EVALUATED. Evaluating it would fold a `2^16` spine and die at the heartbeat limit; naming it is what
makes the witness a statement about the deployed tree rather than about a toy depth. -/

/-- The deployed sparse occupancy: ONE live leaf in a `2^16`-leaf commitment — what
`circuit/src/heap_root.rs::CanonicalHeapTree::new` actually builds. -/
def biteHeap : Heap.FeltHeap := [(1, 7)]

theorem bite_sorted : Heap.SortedKeys biteHeap := by
  simp [biteHeap, Heap.SortedKeys, Heap.keys]

/-- Every committed key is strictly below the deployed terminal sentinel — the bound
`relink_next_addrs` refuses to violate (`heap_root.rs`'s `addr < next_addr` release-active guard). -/
theorem bite_below_sentinel : ∀ x ∈ Heap.keys biteHeap, x < MAP_SENTINEL := by
  intro x hx
  simp only [biteHeap, Heap.keys, List.map_cons, List.map_nil, List.mem_singleton] at hx
  subst hx
  norm_num [MAP_SENTINEL, DEPLOYED_SENTINEL]

/-- The deployed occupancy discipline is SPARSE (`≤`), not dense. One leaf, `2^16` slots. -/
theorem bite_sizeOk : biteHeap.length ≤ 2 ^ MAP_TREE_DEPTH := by
  simp only [biteHeap, List.length_cons, List.length_nil]
  norm_num [MAP_TREE_DEPTH, Dregg2.Circuit.MapMerkleRoot.HEAP_TREE_DEPTH]

/-- The POST heap of a fresh-key write: one MORE live leaf, still inside `2^16`. -/
theorem bite_grown_sizeOk : (Heap.set biteHeap 2 9).length ≤ 2 ^ MAP_TREE_DEPTH := by
  have hset : Heap.set biteHeap 2 9 = [(1, 7), (2, 9)] := by decide
  rw [hset]
  simp only [List.length_cons, List.length_nil]
  norm_num [MAP_TREE_DEPTH, Dregg2.Circuit.MapMerkleRoot.HEAP_TREE_DEPTH]

/-- **★★ THE DEPLOYED MAP-OP DENOTATION IS INHABITED, AT DEPLOYED PARAMETERS.**

The apex's `.mapOp` arm has a witness at the depth the prover runs, over the occupancy the prover
builds, at the sentinel the prover pins. **This is what was not true before the cutover** — and it was
not merely unproved there, it was REFUTED: `MapReconcileImtRepoint.retiredMapOpHoldsAt_unsat_at_imtRoot`
shows the arity-2 denotation is FALSE at a deployed root, so the apex's conclusion (not its premise)
was false on the ordinary path.

Holds for an ARBITRARY `hash` — no floor, no idealisation, no `Good`. -/
theorem deployed_opensTo_inhabited (hash : List ℤ → ℤ) :
    opensTo hash (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH biteHeap) 1 (some 7) :=
  padImt_opens_of_get MAP_SENTINEL hash MAP_TREE_DEPTH
    ⟨bite_sorted, bite_below_sentinel⟩ bite_sizeOk rfl

/-- **★ AND THE TREE REFUSES TO CALL A PRESENT KEY ABSENT** — the same committed root cannot also
open key `1` to `none`, up to the named per-instance residual. This is `opensTo_some_excludes_none`
biting at deployed parameters, i.e. the nullifier / cap non-membership tooth. -/
theorem deployed_absence_is_refused (hash : List ℤ → ℤ)
    (habs : opensTo hash (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH biteHeap) 1 none)
    (hno : ¬ DescriptorIR2.OpenColl hash (deployed_opensTo_inhabited hash) habs) : False :=
  DescriptorIR2.opensTo_some_excludes_none hash (deployed_opensTo_inhabited hash) habs hno

/-- **★ THE WRITE DENOTATION IS INHABITED TOO, AND IT ADMITS GENUINE GROWTH.** The deployed sparse
occupancy makes a FRESH key representable: the post-heap has one more entry and still fits. At the
retired DENSE schema this witness did not exist at all — `length = 2^d` forces every write to be an
in-place update, which is why every `.write`/`.insert` law could only ever speak about a key already
committed. -/
theorem deployed_writesTo_inhabited_with_growth (hash : List ℤ → ℤ) :
    writesTo hash (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH biteHeap) 2 9
      (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set biteHeap 2 9)) :=
  padImt_writes_of_set MAP_SENTINEL hash MAP_TREE_DEPTH
    ⟨bite_sorted, bite_below_sentinel⟩ bite_sizeOk bite_grown_sizeOk

/-! ## §2 — ★ THE SEPARATIONS, which must SURVIVE the cutover permanently.

The arity-3 leaf is not the arity-2 leaf, and the arity-3 root is not the arity-2 root. If the
cutover had unified them, every one of these would collapse and the "move" would have been a
renaming. They are re-checked here by KERNEL DEFEQ against their originals, so a silent weakening,
a binder reorder, or a floor-binder resurrection turns the build RED at this line. -/

/-! ⚙ SURVIVES — re-checked by kernel axiom hygiene on every build. If the cutover had unified the
arity-3 and arity-2 commitments these three would collapse and the "move" would have been a
renaming. -/
#assert_axioms Dregg2.Circuit.MapAbsentImtGate.imtLeafHash_ne_heapLeafOf
#assert_axioms Dregg2.Circuit.MapReconcileImtRepoint.imtRoot_ne_mapRoot
#assert_axioms Dregg2.Circuit.MapInsertImtRepoint.padImtRoot_ne_mapRoot_of_good

/-! ## §3 — ★★ THE DRIFT GUARD. The chain this cutover exists to cut.

Before the cutover the first line below printed:
  "semantics-freedom FAIL: … MapOp.holdsAt DEPENDS on … Heap.leafOf via
   [MapOp.holdsAt, opensTo, MapMerkleRoot.opensToMerkle, MapMerkleRoot.mapRoot, …]" -/

#assert_not_depends_on Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt [Dregg2.Substrate.Heap.leafOf]
#assert_not_depends_on Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt
  [Dregg2.Circuit.MapMerkleRoot.mapRoot]
#assert_not_depends_on Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt
  [Dregg2.Circuit.MapMerkleRoot.opensToMerkle]

/-! POSITIVE CONTROLS — the walk is not blind. Without these the three pins above would pass
vacuously for any future refactor that simply renamed the constants. -/
#assert_depends_on Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt
  [Dregg2.Circuit.DeployedMapDenotation.imtLeafHash]
#assert_depends_on Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt
  [Dregg2.Circuit.DeployedMapDenotation.padImtRoot]
#assert_depends_on Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt
  [Dregg2.Circuit.DeployedMapDenotation.imtChainOf]

/-! ## §4 — ★★ THE ANTI-GHOST IS FLOOR-FREE (the ∃-hoist half).

`Poseidon2SpongeCR` is PROVED FALSE at deployed BabyBear parameters, so any route to it makes the
deployed anti-ghost vacuous AT THE PROVER'S OWN PARAMETERS. These pins are what stops the arity move
from re-basing the same vacuous theorems onto a new commitment. -/

#assert_not_depends_on Dregg2.Circuit.DescriptorIR2.opensTo_functional
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.DescriptorIR2.writesTo_functional
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.DescriptorIR2.opensTo_some_excludes_none
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-! ## §5 — ★★ THE TWIN CHECK. The one failure mode that would look like success.

The schema core (`MapLeafSchema`, `imtChainOf`, `padImtRoot`, `padImtSchema`, `padImtTeeth`, the IMT
leaf) had to move UPSTREAM of `DescriptorIR2` for the denotation to be rebindable onto it. The cheap
way to do that is to COPY it and leave the originals in place. That would build green everywhere and
be worth nothing: `MapKindImtGates`' four arm laws, `MapPaddedDenotation`'s teeth and every
`Map*ImtRepoint` theorem are stated over `MapPaddedDenotation.padImtSchema`, so if that were a
SECOND structure they would all be theorems about a schema the deployed denotation does not use.

Nothing was copied. Each equation below is by KERNEL DEFEQ, and a resurrected local definition
anywhere in the family turns the build RED here.

⚑ This is not hypothetical: a local `imtChainOf` DID survive the first deletion pass in
`MapDenotationSchema`, and the only thing that caught it was a `rfl` failing three modules
downstream. -/

example : Dregg2.Circuit.MapPaddedDenotation.padImtSchema
        = Dregg2.Circuit.DeployedMapDenotation.padImtSchema := rfl
example : Dregg2.Circuit.MapPaddedDenotation.padImtTeeth
        = Dregg2.Circuit.DeployedMapDenotation.padImtTeeth := rfl
example : Dregg2.Circuit.MapPaddedDenotation.padImtRoot
        = Dregg2.Circuit.DeployedMapDenotation.padImtRoot := rfl
example : Dregg2.Circuit.MapDenotationSchema.imtChainOf
        = Dregg2.Circuit.DeployedMapDenotation.imtChainOf := rfl
example : Dregg2.Circuit.IndexedMerkleTree.imtLeafHash
        = Dregg2.Circuit.DeployedMapDenotation.imtLeafHash := rfl
example : Dregg2.Circuit.IndexedMerkleTree.ImtLeaf
        = Dregg2.Circuit.DeployedMapDenotation.ImtLeaf := rfl

/-- ★★ AND THE DEPLOYED DENOTATION IS THAT SCHEMA'S OPENING, definitionally — the single equation
that ties `MapKindImtGates`' arm laws to `Satisfied2`'s `.mapOp` arm. -/
example (hash : List ℤ → ℤ) (r k : ℤ) (o : Option ℤ) :
    DescriptorIR2.opensTo hash r k o
      = DeployedMapDenotation.opensToMerkleS
          (MapPaddedDenotation.padImtSchema DescriptorIR2.MAP_SENTINEL) hash
          DescriptorIR2.MAP_TREE_DEPTH r k o := rfl

#assert_axioms deployed_opensTo_inhabited
#assert_axioms deployed_writesTo_inhabited_with_growth
#assert_axioms deployed_absence_is_refused

end Dregg2.Circuit.MapDenotationCutoverCheck
