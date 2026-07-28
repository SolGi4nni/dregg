/-
# `Dregg2.Crypto.XmVrfRefinementRegrounded` — the DEPLOYED XM-VRF UNIQUENESS
RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the KEYED COLLISION GAME
(`FloorGames.HashCRHardQuant F Eff`, adversary class IN THE STATEMENT).

⚑ The intermediate spelling `HashFloorHonesty.CollisionResistant` is DELETED (2026-07-28): it WAS
`HashCRHardQuant F (fun _ => True)` with the `⊤` folded into a name, and that `⊤` floor is itself FALSE
for every compressing hash (`FloorGames.hashCRHardQuant_top_false_of_compressing`) — the deployed BLAKE3
leaf/node hashes included. The `⊤`-class results below are stated with the `⊤` written out; the
DISCHARGED bindings are §2R's keyed-ROM successors.

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
  `distinct_outputs_break_hashcr` witnesses) IS a `CollisionFinder`, so under the collision floor
  `HashCRHardQuant (…Family X) Eff` its advantage is `Negl`. "two verifying outputs ⟹ equal" becomes "⟹
  equal EXCEPT with negligible probability": a validator double-claims a seat only with negligible
  advantage. `Eff` stays a PARAMETER; the discharge is §2R's keyed-ROM floor.

## Non-fake

Each `⊤`-class floor is SATISFIABLE (`xmVrf_goodCR_leaf_CR` / `_node_CR` on the injective `goodX.cr`) and
REFUTABLE (`xmVrf_badCR_node_not_CR` on a colliding node hash, via
`hashCRHardQuant_top_false_of_compressing`).

⚑ Those two poles are the whole shape of the `⊤` class: it holds exactly for the injective families and
fails exactly for the compressing ones. So the satisfiability witnesses say `goodX.cr` is NOT compressing,
and the deployed BLAKE3 leaf/node hashes sit with `badXmVrf` on the refuted side. §2R's keyed-ROM
successors are what carry the deployed uniqueness claim.

Old injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean` (⊆ {propext,
Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`, no `native_decide`.

## Coordination

PQ sortition-VRF commit-reveal leg. Generic template = `HermineHashCRRegrounded`; the beacon (also `HashCR`)
= `RandomnessBeaconRegrounded`; the wire channel binding = `WireAkeRegrounded`. The `Pseudorandom` sortition
fairness leg is NOT touched — its floor is the PRG, not the vacuous injective `HashCR`. The lattice LB-VRF
uniqueness (`MSISHard`) is the sibling `VrfRegrounded`. Stays in the XM-VRF subtree.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Crypto.XmVrfRefinement

namespace Dregg2.Crypto.XmVrfRefinementRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv idFamily)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineHashCRRegrounded
  (commitRevealFamily commitRevealFamily_CR_of_hashcr commitOpenGame openToFinder
   hermine_commitment_binding_advantage_bound crEquivocator)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily fixedTagCarrier romOpenGame RomOpenEff rom_open_binds romOpen_forger_excluded
   romOpenAdv constOpenComp constOpen_in_eff constOpen_gameAdv_pos constOpen_binds)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv hashGame finderToAdv HashCRHardQuant
   hashCRHardQuant_top_false_of_compressing idFamily_hashCRHardQuant_top hard_bot_vacuous)
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
`xm_node_binding_advantage_bound` took the collision floor at the UNRESTRICTED class —
`HashCRHardQuant (…Family X) (fun _ => True)`, then written `CollisionResistant (…Family X)`, a spelling
since DELETED — and `FloorGames.hashCRHardQuant_top_false_of_compressing` proves THAT false for any
compressing hash — the deployed BLAKE3 leaf and node hashes included. So both exports rested on a
hypothesis REFUTED at deployed parameters. Their `_eff` siblings took a `CollisionFinder` and applied the
floor TO IT, so neither the seat double-claim nor the node equivocation ever appeared in a `Prop`.
ALL FOUR ARE DELETED.

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

/-! ## §2R — ⚑⚑ THE DISCHARGED SUCCESSOR: both legs on the PROVED keyed-ROM floor, ONE oracle.

⚑ **WHAT WAS DELETED HERE, AND WHY.** `xm_leaf_uniqueness_from_polyTime` and
`xm_node_binding_from_polyTime` discharged `Eff` at `CostAdversary.IsPolyTime`, whose floor
`HashCRHardQuant … (IsPolyTime …)` is REFUTED at deployed parameters
(`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`: `IsPolyTime` prices answer
SIZE, so a `.pure` answerer with a hardcoded short collision is in the class and wins with probability
`1`). BOTH ARE DELETED, and replaced by the keyed-ROM successors below.

⚑ **THE MODELLING STEP, STATED (not smuggled).** The deployed role-separated BLAKE3 is idealised as
ONE SAMPLED oracle `H : Role × Pre → Fin (2 ^ l)` over the (finite, truncated-deployed-shape) framed
pre-image space — the standard ROM idealisation at an ASYMPTOTIC digest width, a deliberate labelled
modelling step, NOT a derivation about the fixed public function. Both legs run over the SAME sampled
oracle, domain-separated by the deployed `Role` tag — the leaf carrier pins `Role.leaf`, the node
carrier pins `Role.node` (`fixedTagCarrier`: the deployed prover never lets the adversary move the
role). What the move buys: the floor under both bindings is `KeyedRomFloor.keyedRom_hard` (the
birthday bound, PROVED) where the deleted forms carried a refuted hypothesis. -/

section RomSuccessor

open Dregg2.Crypto.XmVrfRefinement (Role)

/-- `Role` is finite (two roles) — the flat family's key-space obligation, discharged once. -/
def roleFin : Fintype Role :=
  Fintype.ofList [Role.leaf, Role.node] (fun r => by cases r <;> simp)

variable (Pre : Type) [Fintype Pre] [DecidableEq Pre] [Nonempty Pre]

/-- **THE XM-VRF KEYED-ROM FAMILY** — ONE oracle for both legs, keyed by the DEPLOYED role tag
(`Role.leaf` / `Role.node`, the same domain separation the prover absorbs), ideal `λ`-bit digests. -/
def xmRomFamily : KeyedRomFamily :=
  flatFamily Role roleFin inferInstance ⟨Role.leaf⟩ (fun _ => Pre)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The family's width obligation, closed by construction. -/
theorem xmRomFamily_card_R (l : ℕ) :
    letI := (xmRomFamily Pre).rFin l
    Fintype.card ((xmRomFamily Pre).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE LEAF CARRIER** — commitment `H (Role.leaf, p)`: the role is PINNED in the encoding (the
deployed leaf layer never absorbs under another role), the payload is the framed
`(epoch, output, rand)` pre-image itself, injective on the nose. -/
def xmLeafRomCarrier : RomCarrier (xmRomFamily Pre) :=
  fixedTagCarrier _ (fun _ => Role.leaf) (fun _ => Unit) (fun _ => Pre) (fun _ => inferInstance)
    (fun _ _ p => p) (fun _ _ _ _ h => h)

/-- **THE NODE CARRIER** — commitment `H (Role.node, p)`: same oracle, the OTHER pinned role. -/
def xmNodeRomCarrier : RomCarrier (xmRomFamily Pre) :=
  fixedTagCarrier _ (fun _ => Role.node) (fun _ => Unit) (fun _ => Pre) (fun _ => inferInstance)
    (fun _ _ p => p) (fun _ _ _ _ h => h)

/-- The seat double-claim at the sampled oracle: a PUBLISHED leaf digest opened by two DISTINCT framed
pre-images. -/
abbrev xmLeafRomGame : Game := romOpenGame (xmRomFamily Pre) (xmLeafRomCarrier Pre)

/-- The Merkle-node equivocation at the sampled oracle: a PUBLISHED node opened by two DISTINCT framed
child pairs. -/
abbrev xmNodeRomGame : Game := romOpenGame (xmRomFamily Pre) (xmNodeRomCarrier Pre)

/-- **THE DEPLOYED DOUBLE-CLAIM IS A WIN** — two distinct framed pre-images whose `Role.leaf`-tagged
oracle digests both equal the published leaf digest are a win of the leaf game. -/
theorem xmLeafRom_forgery_is_break (l : ℕ) (H : (xmLeafRomGame Pre).Inst l) (d : Fin (2 ^ l))
    {p p' : Pre} (hne : p ≠ p') (h1 : H (Role.leaf, p) = d) (h2 : H (Role.leaf, p') = d) :
    (xmLeafRomGame Pre).wins l H (d, (), p, p') :=
  ⟨hne, h1, h2⟩

/-- **THE DEPLOYED NODE EQUIVOCATION IS A WIN** — same, at the pinned `Role.node`. -/
theorem xmNodeRom_forgery_is_break (l : ℕ) (H : (xmNodeRomGame Pre).Inst l) (d : Fin (2 ^ l))
    {p p' : Pre} (hne : p ≠ p') (h1 : H (Role.node, p) = d) (h2 : H (Role.node, p') = d) :
    (xmNodeRomGame Pre).wins l H (d, (), p, p') :=
  ⟨hne, h1, h2⟩

/-- **⚑⚑ THE RE-GROUNDED LEAF UNIQUENESS — floor PROVED, nothing refutable carried.** Every
query-bounded seat double-claimer has NEGLIGIBLE advantage: at most one framed `(epoch, output, rand)`
opens a published leaf digest except with negligible probability, in the keyed ROM model of the
header. This is what `xm_leaf_uniqueness_from_polyTime` (DELETED — floor refuted) claimed and could
not have. -/
theorem xm_leaf_uniqueness_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (xmLeafRomGame Pre))
    (hA : RomOpenEff (xmRomFamily Pre) (xmLeafRomCarrier Pre) Q A) :
    Negl (gameAdv (xmLeafRomGame Pre) A) :=
  rom_open_binds _ _ Q hQ (xmRomFamily_card_R Pre) A hA

/-- **⚑ THE RE-GROUNDED NODE BINDING** — same floor, same oracle, the node leg. -/
theorem xm_node_binding_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (xmNodeRomGame Pre))
    (hA : RomOpenEff (xmRomFamily Pre) (xmNodeRomCarrier Pre) Q A) :
    Negl (gameAdv (xmNodeRomGame Pre) A) :=
  rom_open_binds _ _ Q hQ (xmRomFamily_card_R Pre) A hA

/-- **(TOOTH — the counterexample DIES.)** A double-claimer with non-negligible advantage is OUTSIDE
the query class. -/
theorem xmLeafRom_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (xmLeafRomGame Pre)) (hnn : ¬ Negl (gameAdv (xmLeafRomGame Pre) A)) :
    ¬ RomOpenEff (xmRomFamily Pre) (xmLeafRomCarrier Pre) Q A :=
  romOpen_forger_excluded _ _ Q hQ (xmRomFamily_card_R Pre) A hnn

/-- **(TOOTH — admitted, winnable, DEFANGED, at a CLOSED instance.)** At `Pre = Fin 4`, `Q = 2`: the
`0`-query hardcoded opener is IN the class, wins with POSITIVE probability, and its advantage is
NEGLIGIBLE — the successor spine elaborates end-to-end at a closed instance. -/
theorem xmLeafRom_fires :
    (RomOpenEff (xmRomFamily (Fin 4)) (xmLeafRomCarrier (Fin 4)) (fun _ => 2)
        (romOpenAdv _ _ (constOpenComp _ (xmLeafRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ()) (fun _ => (0 : Fin 4)) (fun _ => (1 : Fin 4)))))
    ∧ (∀ l, 0 < gameAdv (xmLeafRomGame (Fin 4))
        (romOpenAdv _ _ (constOpenComp _ (xmLeafRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ()) (fun _ => (0 : Fin 4)) (fun _ => (1 : Fin 4)))) l)
    ∧ Negl (gameAdv (xmLeafRomGame (Fin 4))
        (romOpenAdv _ _ (constOpenComp _ (xmLeafRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ()) (fun _ => (0 : Fin 4)) (fun _ => (1 : Fin 4))))) := by
  refine ⟨constOpen_in_eff _ _ _ _ _ _ _,
    fun l => constOpen_gameAdv_pos _ _ _ _ _ _ l (by show (0 : Fin 4) ≠ 1; decide),
    constOpen_binds _ _ _ _ _ _ (fun _ => 2) ⟨1, 5, ?_⟩ (xmRomFamily_card_R (Fin 4))⟩
  filter_upwards [Filter.eventually_ge_atTop 5] with n hn
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

end RomSuccessor

/-! ## §3 — non-vacuity: satisfiable AND load-bearing, on the deployed XM-VRF hashes. -/

/-- **(TOOTH — the leaf `⊤`-class floor is SATISFIABLE.)** The injective `goodX.cr`
(`H role p = roleTag role :: p`) satisfies the keyed collision floor at the UNRESTRICTED class, at
`Role.leaf`. ⚑ Injectivity is the only way to satisfy it (see `xmVrf_badCR_node_not_CR`), so this witness
says `goodX.cr` is not compressing; the deployed BLAKE3 leaf hash is, and cannot be on this side. -/
theorem xmVrf_goodCR_leaf_CR :
    HashCRHardQuant (xmVrfLeafFamily Dregg2.Crypto.XmVrfRefinement.goodX) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.XmVrfRefinement.goodX.cr Role.leaf
    Dregg2.Crypto.XmVrfRefinement.goodX_hashcr

/-- **(TOOTH — the node `⊤`-class floor is SATISFIABLE.)** The injective `goodX.cr` satisfies the keyed
collision floor at the UNRESTRICTED class, at `Role.node`. Same caveat as the leaf tooth above. -/
theorem xmVrf_goodCR_node_CR :
    HashCRHardQuant (xmVrfNodeFamily Dregg2.Crypto.XmVrfRefinement.goodX) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.XmVrfRefinement.goodX.cr Role.node
    Dregg2.Crypto.XmVrfRefinement.goodX_hashcr

/-- A COLLIDING XM-VRF hash `H(role, _) = 0` — every framed pre-image maps to one digest, so any two child
pairs collide at a node (the structural failure the Merkle CR commitment forbids, as a hash). -/
def badXmVrf : XmVrf Unit ℕ ℕ (List ℕ) ℕ where
  cr := ⟨fun _ _ => 0⟩
  frameLeaf := fun _ y r => [y, r]
  frameNode := fun a b => a :: [b]

/-- **(TOOTH — the node `⊤`-class floor is REFUTABLE.)** The colliding node hash has a collision at EVERY
key (`[1] ≠ [2]` yet both hash to `0`), so `hashCRHardQuant_top_false_of_compressing` refutes the floor at
the UNRESTRICTED class — exactly as `XmVrfRefinement.naive_not_merkle_backed` shows the Merkle CR
commitment is what buys uniqueness. The argument needs only compression, so it runs at the deployed BLAKE3
node hash too. -/
theorem xmVrf_badCR_node_not_CR :
    ¬ HashCRHardQuant (xmVrfNodeFamily badXmVrf) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨([] : List ℕ)⟩
    (fun _ _ => ⟨([1] : List ℕ), ([2] : List ℕ), ?_, rfl⟩)
  show ([1] : List ℕ) ≠ [2]
  decide

/-- **THE RE-GROUNDED UNIQUENESS FIRES AT A REAL FLOOR WITNESS.** On the injective identity family, the
leaf-equivocation advantage is negligible — the deployed sortition uniqueness runs end-to-end to a genuine
`Negl`. -/
theorem xm_uniqueness_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    idFamily_hashCRHardQuant_top

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at a compressing XM-VRF node hash.)** The price of `hEff`, as a
theorem: the `⊤` class is refuted at the colliding `badXmVrf` node hash.

⚑ This IS `xmVrf_badCR_node_not_CR` — nothing is added. It used to bridge a `CollisionResistant`
refutation across `collisionResistant_iff_hashCRHardQuant_top`; with the `⊤` now written into the tooth's
own statement, the bridge is the identity. Both names are kept because `Verify/FloorRatchetBaseline`
grandfathers refuted-floor carriers BY NAME. -/
theorem xmVrf_node_eff_top_false :
    ¬ HashCRHardQuant (xmVrfNodeFamily badXmVrf) (fun _ => True) :=
  xmVrf_badCR_node_not_CR

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

/-- **THE `Eff` UNIQUENESS FIRES AT A REAL FLOOR WITNESS.** On the injective `goodX.cr` the leaf
`Eff`-floor at `⊤` holds (`xmVrf_goodCR_leaf_CR`), so the `Eff` uniqueness runs end-to-end to a genuine
`Negl` at an inhabited hypothesis. Read with `xmVrf_node_eff_top_false`: it fires HERE and cannot fire at
a compressing leaf hash, which is why the deployed discharge is §2R. -/
theorem xm_uniqueness_eff_fires
    (A : Adversary (xmLeafGame Dregg2.Crypto.XmVrfRefinement.goodX)) :
    Negl (gameAdv (xmLeafGame Dregg2.Crypto.XmVrfRefinement.goodX) A) :=
  xm_leaf_uniqueness_advantage_bound Dregg2.Crypto.XmVrfRefinement.goodX (fun _ => True) A trivial
    xmVrf_goodCR_leaf_CR

#assert_all_clean [
  xmLeafGame_wins_iff,
  xm_leaf_uniqueness_advantage_bound,
  xm_node_binding_advantage_bound,
  xmRomFamily_card_R,
  xmLeafRom_forgery_is_break,
  xmNodeRom_forgery_is_break,
  xm_leaf_uniqueness_rom,
  xm_node_binding_rom,
  xmLeafRom_nonNegl_forger_excluded,
  xmLeafRom_fires,
  xmVrf_goodCR_leaf_CR,
  xmVrf_goodCR_node_CR,
  xmVrf_badCR_node_not_CR,
  xm_uniqueness_fires,
  xmVrf_node_eff_top_false,
  xmVrf_node_eff_bot_vacuous,
  xm_uniqueness_eff_fires
]

end Dregg2.Crypto.XmVrfRefinementRegrounded
