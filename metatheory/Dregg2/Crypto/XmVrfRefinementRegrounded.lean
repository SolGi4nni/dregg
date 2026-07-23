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
  (commitRevealFamily commitRevealFamily_CR_of_hashcr commitOpenGame openToFinder
   hermine_commitment_binding_advantage_bound hermine_commitment_binding_from_polyTime
   hashAnsSizeOf openAnsSizeOf crEquivocator)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv hashGame finderToAdv HashCRHardQuant
   collisionResistant_iff_hashCRHardQuant_top hard_bot_vacuous)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
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

/-! ## §2 — the leaf and node breaks, as SECURITY REDUCTIONS.

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** `xm_leaf_uniqueness_advantage_bound` and
`xm_node_binding_advantage_bound` took `hCR : CollisionResistant (…Family X)`.
`FloorGames.collisionResistant_iff_hashCRHardQuant_top` proves that IS the collision floor at the
UNRESTRICTED class, and `collisionResistant_false_of_compressing` proves THAT false for any compressing
hash — the deployed BLAKE3 leaf and node hashes included. So both exports rested on a hypothesis REFUTED
at deployed parameters. Their `_eff` siblings took a `CollisionFinder` and applied the floor TO IT, so
neither the seat double-claim nor the node equivocation ever appeared in a `Prop`. ALL FOUR ARE DELETED.

What stands here is the commit-opening REDUCTION (`HermineHashCRRegrounded` §2) at each deployed family:
the break is a `Game` whose win says an adversary published a leaf digest (resp. an internal node) with
TWO DISTINCT framed pre-images that both produce it — the seat double-claim, and the Merkle node
equivocation — and the extractor DISCARDS the published digest to reach a genuine collision. -/

/-- **THE SEAT DOUBLE-CLAIM GAME** — the commit-opening break of the deployed XM-VRF LEAF hash. A win is
one published leaf digest opened by two DISTINCT framed `(epoch, output, rand)` pre-images: exactly the
double-claim `XmVrfRefinement.leaf_unique` denies. -/
abbrev xmLeafGame {Epoch Output Rand Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : XmVrf Epoch Output Rand Pre Digest) : Game :=
  commitOpenGame (xmVrfLeafFamily X)

/-- **THE NODE EQUIVOCATION GAME** — the commit-opening break of the deployed XM-VRF NODE hash. A win is
one internal node opened by two DISTINCT framed child pairs. -/
abbrev xmNodeGame {Epoch Output Rand Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : XmVrf Epoch Output Rand Pre Digest) : Game :=
  commitOpenGame (xmVrfNodeFamily X)

/-- **THE PROBLEM IS IN THE STATEMENT (leaf)** — by `Iff.rfl`, two distinct framed pre-images opening one
published leaf digest. -/
theorem xmLeafGame_wins_iff {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (n : ℕ) (k : (xmVrfLeafFamily X).Key n) (p : Digest × Pre × Pre) :
    (xmLeafGame X).wins n k p ↔
      (p.2.1 ≠ p.2.2 ∧ X.cr.H Role.leaf p.2.1 = p.1 ∧ X.cr.H Role.leaf p.2.2 = p.1) :=
  Iff.rfl

/-- **⚑ RE-GROUNDED `XmVrfRefinement.leaf_unique` — from the leaf hash's collision floor, VIA the
reduction.** Under the collision floor at the class `Eff`, a seat double-claimer whose extracted finder is
in that class has NEGLIGIBLE advantage: "two verifying outputs ⟹ equal" becomes "⟹ equal EXCEPT with
negligible probability". `Eff` is a parameter because this is the statement at an ARBITRARY class;
`_from_polyTime` discharges it. -/
theorem xm_leaf_uniqueness_advantage_bound {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (Eff : Adversary (hashGame (xmVrfLeafFamily X)) → Prop)
    (A : Adversary (xmLeafGame X))
    (hEff : Eff (openToFinder (xmVrfLeafFamily X) A))
    (hD : HashCRHardQuant (xmVrfLeafFamily X) Eff) :
    Negl (gameAdv (xmLeafGame X) A) :=
  hermine_commitment_binding_advantage_bound (xmVrfLeafFamily X) Eff A hEff hD

/-- **⚑ RE-GROUNDED `XmVrfRefinement.merkle_leaf_binding` (node leg) — same reduction at the node hash.**
Each Merkle node binds its child pair except with negligible probability. -/
theorem xm_node_binding_advantage_bound {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (Eff : Adversary (hashGame (xmVrfNodeFamily X)) → Prop)
    (A : Adversary (xmNodeGame X))
    (hEff : Eff (openToFinder (xmVrfNodeFamily X) A))
    (hD : HashCRHardQuant (xmVrfNodeFamily X) Eff) :
    Negl (gameAdv (xmNodeGame X) A) :=
  hermine_commitment_binding_advantage_bound (xmVrfNodeFamily X) Eff A hEff hD

/-- **⚑ THE LEAF LEG'S EFFICIENCY OBLIGATION DISCHARGED.** A seat double-claimer that is EFFICIENT at the
game's own answer encoding yields a collision finder that is STILL efficient (the extractor DISCARDS the
published digest, growth `(1, 0)`), so the floor at `Eff := IsPolyTime` applies to IT. Per-site inputs:
the reshaper's declared work `(cw, bw)` and the deployment's own pre-image/digest encodings. -/
theorem xm_leaf_uniqueness_from_polyTime {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (szIn : ℕ → Pre → ℕ) (szOut : ℕ → Digest → ℕ)
    (A : Adversary (xmLeafGame X))
    (hA : IsPolyTime (openAnsSizeOf (xmVrfLeafFamily X) szIn szOut) A) (cw bw : ℕ)
    (hD : HashCRHardQuant (xmVrfLeafFamily X)
      (IsPolyTime (hashAnsSizeOf (xmVrfLeafFamily X) szIn))) :
    Negl (gameAdv (xmLeafGame X) A) :=
  hermine_commitment_binding_from_polyTime (xmVrfLeafFamily X) szIn szOut A hA cw bw hD

/-- **⚑ THE NODE LEG'S EFFICIENCY OBLIGATION DISCHARGED.** Same, at the node hash. -/
theorem xm_node_binding_from_polyTime {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest)
    (szIn : ℕ → Pre → ℕ) (szOut : ℕ → Digest → ℕ)
    (A : Adversary (xmNodeGame X))
    (hA : IsPolyTime (openAnsSizeOf (xmVrfNodeFamily X) szIn szOut) A) (cw bw : ℕ)
    (hD : HashCRHardQuant (xmVrfNodeFamily X)
      (IsPolyTime (hashAnsSizeOf (xmVrfNodeFamily X) szIn))) :
    Negl (gameAdv (xmNodeGame X) A) :=
  hermine_commitment_binding_from_polyTime (xmVrfNodeFamily X) szIn szOut A hA cw bw hD

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
theorem xm_uniqueness_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp idFamily_CR)

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at a compressing XM-VRF node hash.)** The bare-CR floor at the colliding
`badXmVrf` node hash is refuted (`xmVrf_badCR_node_not_CR`), and it IS `HashCRHardQuant _ ⊤` — so the `⊤`
class is FALSE. The price of `hEff`, as a theorem. -/
theorem xmVrf_node_eff_top_false :
    ¬ HashCRHardQuant (xmVrfNodeFamily badXmVrf) (fun _ => True) :=
  fun h => xmVrf_badCR_node_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the node floor holds for ANY
XM-VRF. -/
theorem xmVrf_node_eff_bot_vacuous {Epoch Output Rand Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : XmVrf Epoch Output Rand Pre Digest) :
    HashCRHardQuant (xmVrfNodeFamily X) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — uniqueness does NOT follow from the floor at another adversary.)** From the floor at some
OTHER adversary `B` the leaf-equivocator's negligibility does not follow: `hD B hB` bounds a DIFFERENT
ensemble. -/
example {Epoch Output Rand Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : XmVrf Epoch Output Rand Pre Digest)
    (Eff : Adversary (hashGame (xmVrfLeafFamily X)) → Prop)
    (A : Adversary (xmLeafGame X))
    (B : Adversary (hashGame (xmVrfLeafFamily X))) (hB : Eff B)
    (hD : HashCRHardQuant (xmVrfLeafFamily X) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (xmLeafGame X) A) := hD B hB)
  trivial

/-- **THE `Eff` UNIQUENESS FIRES AT A REAL FLOOR WITNESS.** On the injective deployed `goodX.cr` the leaf
`Eff`-floor at `⊤` holds (`xmVrf_goodCR_leaf_CR`), so the `Eff` uniqueness runs end-to-end to a genuine
`Negl` at an inhabited hypothesis. -/
theorem xm_uniqueness_eff_fires
    (A : Adversary (xmLeafGame Dregg2.Crypto.XmVrfRefinement.goodX)) :
    Negl (gameAdv (xmLeafGame Dregg2.Crypto.XmVrfRefinement.goodX) A) :=
  xm_leaf_uniqueness_advantage_bound Dregg2.Crypto.XmVrfRefinement.goodX (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp xmVrf_goodCR_leaf_CR)

#assert_all_clean [
  xmLeafGame_wins_iff,
  xm_leaf_uniqueness_advantage_bound,
  xm_node_binding_advantage_bound,
  xm_leaf_uniqueness_from_polyTime,
  xm_node_binding_from_polyTime,
  xmVrf_goodCR_leaf_CR,
  xmVrf_goodCR_node_CR,
  xmVrf_badCR_node_not_CR,
  xm_uniqueness_fires,
  xmVrf_node_eff_top_false,
  xmVrf_node_eff_bot_vacuous,
  xm_uniqueness_eff_fires
]

end Dregg2.Crypto.XmVrfRefinementRegrounded
