/-
# `Dregg2.Crypto.XmVrfRefinementRegrounded` — the DEPLOYED XM-VRF UNIQUENESS
RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the PROPER keyed `CollisionResistant` floor.

## The gap this closes (the PQ sortition-VRF leg of the forward-scaffolding floor sweep)

`XmVrfRefinement.xm_unique` / `merkle_leaf_binding` / `leaf_unique` are the UNIQUENESS floor of the deployed
`crypto-xmvrf` leader-sortition VRF: at most one output `y` verifies per `(pk, epoch)`, so a validator cannot
double-claim a committee seat. The whole reduction bottoms out at `HermineHintMLWE.HashCR X.cr` — injectivity
of the role-indexed leaf hash `H(Role.leaf, ·)` and node hash `H(Role.node, ·)`. But
`HashFloorHonesty.hashCR_false_of_compressing` PROVES `HashCR` FALSE for a compressing hash (the deployed
BLAKE3 leaf/node hashes map long framed pre-images to fixed-width digests, so they ARE compressing) — the
deployed uniqueness guarantee is VACUOUSLY TRUE at real parameters.

This file instantiates the generic commit-reveal regrounding (`HermineHashCRRegrounded`) for the XM-VRF's own
leaf/node hashes, so `SortitionGame.sortition_unique` on the deployed VRF no longer rides an empty
hypothesis. Mirror of `IdentityCommitmentRegrounded`.

## The re-grounding

* **`xmVrfLeafFamily X` / `xmVrfNodeFamily X`** — the deployed leaf hash `H(Role.leaf, frameLeaf …)` and
  node hash `H(Role.node, frameNode …)` as keyed families (`commitRevealFamily X.cr Role.leaf/node`).
* **`xm_leaf_uniqueness_advantage_bound` / `xm_node_binding_advantage_bound`** — the advantage-bounded siblings
  of `leaf_unique` / `merkle_leaf_binding`: a uniqueness-breaking adversary (per key, two distinct verifying
  outputs colliding at one leaf, or two distinct child pairs colliding at one node — a hash collision, exactly
  `distinct_outputs_break_hashcr` witnesses) IS a `CollisionFinder`, so under the proper floor its advantage is
  `Negl`. "two verifying outputs ⟹ equal" becomes "⟹ equal EXCEPT with negligible probability": a validator
  double-claims a seat only with negligible advantage. Discharged by `thread_advantage_bound`.

## Non-fake

Each floor is SATISFIABLE (`xmVrf_goodCR_leaf_CR` / `_node_CR` on the injective deployed `goodX.cr`) and
LOAD-BEARING (`xmVrf_badCR_node_not_CR` on a colliding node hash). Old injective-floor consumers KEPT
untouched; siblings ADDED. `#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no
fresh `axiom`, no `native_decide`.

## Coordination

PQ sortition-VRF commit-reveal leg. Generic template = `HermineHashCRRegrounded`; the beacon (also `HashCR`)
= `RandomnessBeaconRegrounded`; the wire channel binding = `WireAkeRegrounded`. The `Pseudorandom` sortition
fairness leg is NOT touched — its floor is the PRG, not the vacuous injective `HashCR`. The lattice LB-VRF
uniqueness (`MSISHard`) is the sibling `VrfRegrounded`. Stays in the XM-VRF subtree.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.XmVrfRefinement

namespace Dregg2.Crypto.XmVrfRefinementRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv idFamily idFamily_CR)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineHashCRRegrounded
  (commitRevealFamily commitRevealFamily_CR_of_hashcr hermine_commitment_binding_advantage_bound
   crEquivocator)
open Dregg2.Crypto.XmVrfRefinement (XmVrf Role)

set_option autoImplicit false

/-! ## §1 — the deployed XM-VRF leaf/node hashes as keyed families. -/

/-- **THE XM-VRF LEAF FAMILY.** The deployed leaf commitment `H(Role.leaf, frameLeaf epoch y r)` as a keyed
family (`commitRevealFamily X.cr Role.leaf`) — the keyed hash the uniqueness collision game runs over. -/
def xmVrfLeafFamily {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest) : KeyedHashFamily :=
  commitRevealFamily X.cr Role.leaf

/-- **THE XM-VRF NODE FAMILY.** The deployed internal node hash `H(Role.node, frameNode l r)` as a keyed
family (`commitRevealFamily X.cr Role.node`) — the Merkle-binding collision game object. -/
def xmVrfNodeFamily {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest) : KeyedHashFamily :=
  commitRevealFamily X.cr Role.node

/-! ## §2 — the advantage-bounded uniqueness keystones (`leaf_unique` / `merkle_leaf_binding`, re-grounded). -/

/-- **RE-GROUNDED `XmVrfRefinement.leaf_unique`.** Under the proper keyed floor, the leaf-equivocation
adversary (per key, two distinct verifying outputs committed at one leaf — a collision by
`distinct_outputs_break_hashcr`) has negligible advantage. "two verifying outputs ⟹ equal" becomes "⟹ equal
EXCEPT with negligible probability": a validator double-claims a committee seat only with negligible
advantage. Proof: `thread_advantage_bound`. -/
theorem xm_leaf_uniqueness_advantage_bound {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (hCR : CollisionResistant (xmVrfLeafFamily X))
    (leafEquivocator : CollisionFinder (xmVrfLeafFamily X)) :
    Negl (collisionAdv (xmVrfLeafFamily X) leafEquivocator) :=
  hermine_commitment_binding_advantage_bound hCR leafEquivocator

/-- **RE-GROUNDED `XmVrfRefinement.merkle_leaf_binding` (the node leg).** Under the proper keyed floor, the
node-equivocation adversary (per key, two distinct child pairs hashing to one internal node) has negligible
advantage — the Merkle path binds each node except with negligible probability. Proof:
`thread_advantage_bound`. -/
theorem xm_node_binding_advantage_bound {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (hCR : CollisionResistant (xmVrfNodeFamily X))
    (nodeEquivocator : CollisionFinder (xmVrfNodeFamily X)) :
    Negl (collisionAdv (xmVrfNodeFamily X) nodeEquivocator) :=
  hermine_commitment_binding_advantage_bound hCR nodeEquivocator

/-! ## §3 — non-vacuity: satisfiable AND load-bearing, on the deployed XM-VRF hashes. -/

/-- **(TOOTH — the leaf floor is SATISFIABLE.)** The injective deployed hash `goodX.cr` satisfies the proper
keyed floor at `Role.leaf`. -/
theorem xmVrf_goodCR_leaf_CR :
    CollisionResistant (xmVrfLeafFamily Dregg2.Crypto.XmVrfRefinement.goodX) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.XmVrfRefinement.goodX.cr Role.leaf
    Dregg2.Crypto.XmVrfRefinement.goodX_hashcr

/-- **(TOOTH — the node floor is SATISFIABLE.)** The injective deployed hash `goodX.cr` satisfies the proper
keyed floor at `Role.node`. -/
theorem xmVrf_goodCR_node_CR :
    CollisionResistant (xmVrfNodeFamily Dregg2.Crypto.XmVrfRefinement.goodX) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.XmVrfRefinement.goodX.cr Role.node
    Dregg2.Crypto.XmVrfRefinement.goodX_hashcr

/-- A COLLIDING XM-VRF hash `H(role, _) = 0` — every framed pre-image maps to one digest, so any two child
pairs collide at a node (the structural failure the Merkle CR commitment forbids, as a hash). -/
def badXmVrf : XmVrf Unit ℕ ℕ (List ℕ) ℕ where
  cr := ⟨fun _ _ => 0⟩
  frameLeaf := fun _ y r => [y, r]
  frameNode := fun a b => a :: [b]

/-- **(TOOTH — the node floor is LOAD-BEARING.)** The colliding node hash has the node-equivocator
`crEquivocator badXmVrf.cr Role.node [1] [2]` winning on every key (`[1] ≠ [2]` yet both hash to `0`),
advantage `1`, so its family is NOT CR — the deployed uniqueness's floor is a genuine constraint, exactly as
`XmVrfRefinement.naive_not_merkle_backed` shows the Merkle CR commitment is what buys uniqueness. -/
theorem xmVrf_badCR_node_not_CR : ¬ CollisionResistant (xmVrfNodeFamily badXmVrf) := by
  intro hCR
  have hadv : collisionAdv (xmVrfNodeFamily badXmVrf)
      (crEquivocator badXmVrf.cr Role.node ([1] : List ℕ) [2]) = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (xmVrfNodeFamily badXmVrf).Key n =>
        (crEquivocator badXmVrf.cr Role.node ([1] : List ℕ) [2]).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, badXmVrf]
    show @winProb ((xmVrfNodeFamily badXmVrf).Key n) ((xmVrfNodeFamily badXmVrf).keyFintype n)
        (fun k => (crEquivocator badXmVrf.cr Role.node ([1] : List ℕ) [2]).wins n k) = 1
    rw [hall]
    exact @winProb_top ((xmVrfNodeFamily badXmVrf).Key n) ((xmVrfNodeFamily badXmVrf).keyFintype n)
      ((xmVrfNodeFamily badXmVrf).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator badXmVrf.cr Role.node [1] [2]))

/-- **THE RE-GROUNDED UNIQUENESS FIRES AT A REAL FLOOR WITNESS.** On the injective identity family, the
leaf-equivocation advantage is negligible — the deployed sortition uniqueness runs end-to-end to a genuine
`Negl`. -/
theorem xm_uniqueness_fires (leafEquivocator : CollisionFinder idFamily) :
    Negl (collisionAdv idFamily leafEquivocator) :=
  hermine_commitment_binding_advantage_bound idFamily_CR leafEquivocator

#assert_all_clean [
  xm_leaf_uniqueness_advantage_bound,
  xm_node_binding_advantage_bound,
  xmVrf_goodCR_leaf_CR,
  xmVrf_goodCR_node_CR,
  xmVrf_badCR_node_not_CR,
  xm_uniqueness_fires
]

end Dregg2.Crypto.XmVrfRefinementRegrounded
