/-
# `Dregg2.Crypto.RandomnessBeaconRegrounded` — the POST-QUANTUM randomness beacon (abstract model AND the
deployed `crypto-hashrand` refinement) RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the
PROPER keyed `CollisionResistant` floor.

## The gap this closes (the beacon leg of the forward-scaffolding floor sweep)

`RandomnessBeacon.unbiasable_of_hashcr` / `prediction_matching_two_reveals_breaks_hashcr` /
`commit_binds_contribution`, and their deployed refinements `HashRandRefinement.hashrand_unbiasable` /
`hashrand_commit_binds`, are the UNBIASABILITY + UNPREDICTABILITY floors of the hash-based beacon. Each is
conditioned on `HermineHintMLWE.HashCR cr` — the injective floor `HashFloorHonesty.hashCR_false_of_compressing`
PROVES FALSE for any compressing commit (`beaconViaHash cr i adv c = cr.H i (c, adv)` and the deployed
`combine = H("output", sorted[(i,cᵢ)])` both map a long framed pre-image to a fixed-width digest, so they
ARE compressing). So the beacon's safety lemmas are VACUOUSLY TRUE at real parameters.

This file instantiates the generic commit-reveal regrounding (`HermineHashCRRegrounded`) for the beacon's own
combine/commit hashes — the abstract model AND the deployed `crypto-hashrand` surface — so unbiasability and
unpredictability no longer ride an empty hypothesis. Mirror of `IdentityCommitmentRegrounded`.

## The re-grounding

* **`beaconHashFamily cr i`** — the beacon's combine/commit hash `cr.H i` as the keyed hash family
  `commitRevealFamily cr i`. **`hashRandCommitFamily X` / `hashRandOutputFamily X`** — the deployed
  `crypto-hashrand` commit hash `H(Role.commit, ·)` and combine hash `H(Role.output, ·)` as families.
* **`beacon_binding_advantage_bound`** — the advantage-bounded sibling of `unbiasable_of_hashcr` /
  `prediction_matching_two_reveals_breaks_hashcr`: a BIAS / early-prediction adversary (per key, two distinct
  reveals colliding to one beacon output — a hash collision, by `bias_breaks_honest_slot_cr`) IS a
  `CollisionFinder`, so under the proper floor its advantage is `Negl`. "distinct honest reveal ⟹ distinct
  output" becomes "⟹ distinct output EXCEPT with negligible probability".
* **`hashrand_commit_binding_advantage_bound` / `hashrand_output_binding_advantage_bound`** — the same, on the
  DEPLOYED `crypto-hashrand` commit/combine hashes: an equivocating committer / a bias adversary has
  negligible advantage under the proper floor. Both discharged by `thread_advantage_bound`.

## Non-fake

Each floor is SATISFIABLE (`beacon_exBeaconHash_CR` on the injective `exBeaconHash`;
`hashRand_goodCR_commit_CR` / `_output_CR` on the injective deployed `goodCR`) and LOAD-BEARING
(`beacon_badBeaconOut_not_CR` on the colliding `badBeaconOut`; `hashRand_badCR_output_not_CR` on the deployed
colliding `badCR`). Old injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`, no `native_decide`.

## Coordination

Beacon commit-reveal leg. Generic template = `HermineHashCRRegrounded`; the PQ sortition VRF (also `HashCR`)
= `XmVrfRefinementRegrounded`; the wire channel binding = `WireAkeRegrounded`. Stays in the beacon subtree.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.HashRandRefinement

namespace Dregg2.Crypto.RandomnessBeaconRegrounded

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
open Dregg2.Crypto.HashRandRefinement (HashRand Role)

set_option autoImplicit false

/-! ## §1 — the beacon combine/commit hashes as keyed families. -/

/-- **THE BEACON KEYED FAMILY.** The abstract beacon's combine/commit hash `cr.H i` over the framed
`(contribution, adversary aggregate)` pre-images, as `commitRevealFamily cr i` — the keyed hash the honest
collision game runs over. -/
def beaconHashFamily {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) : KeyedHashFamily :=
  commitRevealFamily cr i

/-- **THE DEPLOYED `crypto-hashrand` COMMIT FAMILY.** `H(Role.commit, frameCommit i c)` as a keyed family. -/
def hashRandCommitFamily {Party Ct Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : HashRand Party Ct Pre Digest) : KeyedHashFamily :=
  commitRevealFamily X.cr Role.commit

/-- **THE DEPLOYED `crypto-hashrand` OUTPUT FAMILY.** `H(Role.output, frameOutput cs)` as a keyed family. -/
def hashRandOutputFamily {Party Ct Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : HashRand Party Ct Pre Digest) : KeyedHashFamily :=
  commitRevealFamily X.cr Role.output

/-! ## §2 — the three beacon breaks, as SECURITY REDUCTIONS.

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** The three keystones took
`hCR : CollisionResistant (…Family …)`. `FloorGames.collisionResistant_iff_hashCRHardQuant_top` proves
that IS the collision floor at the UNRESTRICTED class, and `collisionResistant_false_of_compressing`
proves THAT false for any compressing hash — the deployed `crypto-hashrand` commit and combine hashes
included. So all three exported bounds rested on a hypothesis REFUTED at deployed parameters: leader
election was resting on nothing. Their three `_eff` siblings took a `CollisionFinder` and applied the
floor TO IT, so the BIAS and the COMMIT EQUIVOCATION never appeared in a `Prop`. ALL SIX ARE DELETED.

What stands here is the commit-opening REDUCTION (`HermineHashCRRegrounded` §2) at each of the three
deployed families: the break is a `Game` whose win says an adversary published a beacon output (resp. a
commitment) together with TWO DISTINCT framed pre-images that BOTH produce it — steering the beacon, or
opening one commitment to two contributions — and the extractor DISCARDS the published value to reach a
genuine collision. The advantage inequality is unconditional; the class is discharged at `IsPolyTime`. -/

/-- **THE BEACON-STEERING GAME** — the commit-opening break of the abstract beacon combine hash. A win is
one published beacon output produced by two DISTINCT reveals: a coalition steering the beacon. -/
abbrev beaconGame {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) : Game :=
  commitOpenGame (beaconHashFamily cr i)

/-- **THE `crypto-hashrand` COMMIT-EQUIVOCATION GAME** — one published commitment opened by two DISTINCT
contributions: the honest party escaping its own commitment (UNPREDICTABILITY's break). -/
abbrev hashRandCommitGame {Party Ct Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : HashRand Party Ct Pre Digest) : Game :=
  commitOpenGame (hashRandCommitFamily X)

/-- **THE `crypto-hashrand` BIAS GAME** — one published beacon output produced by two DISTINCT
contribution multisets: the coalition steering the deployed beacon (UNBIASABILITY's break). -/
abbrev hashRandOutputGame {Party Ct Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : HashRand Party Ct Pre Digest) : Game :=
  commitOpenGame (hashRandOutputFamily X)

/-- **THE PROBLEM IS IN THE STATEMENT** — by `Iff.rfl`, two distinct reveals producing one published
beacon output. -/
theorem beaconGame_wins_iff {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (n : ℕ) (k : (beaconHashFamily cr i).Key n)
    (p : C × W × W) :
    (beaconGame cr i).wins n k p ↔
      (p.2.1 ≠ p.2.2 ∧ cr.H i p.2.1 = p.1 ∧ cr.H i p.2.2 = p.1) :=
  Iff.rfl

/-- **⚑ RE-GROUNDED `RandomnessBeacon.unbiasable_of_hashcr` /
`prediction_matching_two_reveals_breaks_hashcr` — from the combine hash's collision floor, VIA the
reduction.** Under the collision floor at the class `Eff`, a beacon-steering adversary whose extracted
finder is in that class has NEGLIGIBLE advantage: no coalition steers or predicts the beacon except with
negligible probability. `Eff` is a parameter because this is the statement at an ARBITRARY class;
`_from_polyTime` discharges it. -/
theorem beacon_binding_advantage_bound {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx)
    (Eff : Adversary (hashGame (beaconHashFamily cr i)) → Prop)
    (A : Adversary (beaconGame cr i))
    (hEff : Eff (openToFinder (beaconHashFamily cr i) A))
    (hD : HashCRHardQuant (beaconHashFamily cr i) Eff) :
    Negl (gameAdv (beaconGame cr i) A) :=
  hermine_commitment_binding_advantage_bound (beaconHashFamily cr i) Eff A hEff hD

/-- **⚑ RE-GROUNDED `HashRandRefinement.hashrand_commit_binds` — the deployed commit leg.** A commit
equivocator has negligible advantage: an honest party is pinned to ONE contribution except with
negligible probability, which is what grounds UNPREDICTABILITY. -/
theorem hashrand_commit_binding_advantage_bound {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (Eff : Adversary (hashGame (hashRandCommitFamily X)) → Prop)
    (A : Adversary (hashRandCommitGame X))
    (hEff : Eff (openToFinder (hashRandCommitFamily X) A))
    (hD : HashCRHardQuant (hashRandCommitFamily X) Eff) :
    Negl (gameAdv (hashRandCommitGame X) A) :=
  hermine_commitment_binding_advantage_bound (hashRandCommitFamily X) Eff A hEff hD

/-- **⚑ RE-GROUNDED `HashRandRefinement.hashrand_unbiasable` — the deployed combine leg.** A bias
adversary has negligible advantage: the honest contribution MOVES the beacon except with negligible
probability, which is what grounds UNBIASABILITY. -/
theorem hashrand_output_binding_advantage_bound {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (Eff : Adversary (hashGame (hashRandOutputFamily X)) → Prop)
    (A : Adversary (hashRandOutputGame X))
    (hEff : Eff (openToFinder (hashRandOutputFamily X) A))
    (hD : HashCRHardQuant (hashRandOutputFamily X) Eff) :
    Negl (gameAdv (hashRandOutputGame X) A) :=
  hermine_commitment_binding_advantage_bound (hashRandOutputFamily X) Eff A hEff hD

/-! ### §2b — all three efficiency obligations DISCHARGED at `Eff := IsPolyTime`.

Each extractor DISCARDS the published value and keeps the two pre-images, so its growth constants are
`(1, 0)` and no output-size hypothesis is needed. The per-site inputs are the reshaper's declared work
`(cw, bw)` — a Lean `fun` has no runtime — and the deployment's own pre-image/digest encodings, which a
`KeyedHashFamily` over abstract carriers cannot supply itself. -/

/-- **⚑ LEADER ELECTION'S EFFICIENCY OBLIGATION DISCHARGED.** A beacon-steering adversary that is
EFFICIENT yields a collision finder that is STILL efficient, so the floor at `Eff := IsPolyTime` applies
to IT: the beacon resists steering with NO floating efficiency parameter. -/
theorem beacon_binding_from_polyTime {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (szIn : ℕ → W → ℕ) (szOut : ℕ → C → ℕ)
    (A : Adversary (beaconGame cr i))
    (hA : IsPolyTime (openAnsSizeOf (beaconHashFamily cr i) szIn szOut) A) (cw bw : ℕ)
    (hD : HashCRHardQuant (beaconHashFamily cr i)
      (IsPolyTime (hashAnsSizeOf (beaconHashFamily cr i) szIn))) :
    Negl (gameAdv (beaconGame cr i) A) :=
  hermine_commitment_binding_from_polyTime (beaconHashFamily cr i) szIn szOut A hA cw bw hD

/-- **⚑ THE DEPLOYED COMMIT LEG'S EFFICIENCY OBLIGATION DISCHARGED.** -/
theorem hashrand_commit_binding_from_polyTime {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (szIn : ℕ → Pre → ℕ) (szOut : ℕ → Digest → ℕ)
    (A : Adversary (hashRandCommitGame X))
    (hA : IsPolyTime (openAnsSizeOf (hashRandCommitFamily X) szIn szOut) A) (cw bw : ℕ)
    (hD : HashCRHardQuant (hashRandCommitFamily X)
      (IsPolyTime (hashAnsSizeOf (hashRandCommitFamily X) szIn))) :
    Negl (gameAdv (hashRandCommitGame X) A) :=
  hermine_commitment_binding_from_polyTime (hashRandCommitFamily X) szIn szOut A hA cw bw hD

/-- **⚑ THE DEPLOYED COMBINE LEG'S EFFICIENCY OBLIGATION DISCHARGED.** -/
theorem hashrand_output_binding_from_polyTime {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (szIn : ℕ → Pre → ℕ) (szOut : ℕ → Digest → ℕ)
    (A : Adversary (hashRandOutputGame X))
    (hA : IsPolyTime (openAnsSizeOf (hashRandOutputFamily X) szIn szOut) A) (cw bw : ℕ)
    (hD : HashCRHardQuant (hashRandOutputFamily X)
      (IsPolyTime (hashAnsSizeOf (hashRandOutputFamily X) szIn))) :
    Negl (gameAdv (hashRandOutputGame X) A) :=
  hermine_commitment_binding_from_polyTime (hashRandOutputFamily X) szIn szOut A hA cw bw hD

/-! ## §3 — non-vacuity: satisfiable AND load-bearing, on the abstract beacon and the deployed surface. -/

/-- **(TOOTH — the beacon floor is SATISFIABLE.)** The injective combine hash `exBeaconHash` satisfies the
proper keyed floor. -/
theorem beacon_exBeaconHash_CR :
    CollisionResistant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.exBeaconHash 0) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.RandomnessBeacon.exBeaconHash 0
    Dregg2.Crypto.RandomnessBeacon.exBeaconHash_hashcr

/-- **(TOOTH — the beacon floor is LOAD-BEARING.)** The colliding combine hash `badBeaconOut` (`H _ _ = 0`,
every reveal absorbed to one output) has the bias equivocator `crEquivocator badBeaconOut 0 (5,1) (6,1)`
winning on every key (advantage `1`), so its family is NOT CR — the proper floor is a genuine constraint. -/
theorem beacon_badBeaconOut_not_CR :
    ¬ CollisionResistant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.badBeaconOut 0) := by
  intro hCR
  set bad := Dregg2.Crypto.RandomnessBeacon.badBeaconOut with hbad
  have hadv : collisionAdv (beaconHashFamily bad 0)
      (crEquivocator bad 0 ((5, 1) : ℤ × ℤ) (6, 1)) = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (beaconHashFamily bad 0).Key n =>
        (crEquivocator bad 0 ((5, 1) : ℤ × ℤ) (6, 1)).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, hbad,
        Dregg2.Crypto.RandomnessBeacon.badBeaconOut]
    show @winProb ((beaconHashFamily bad 0).Key n) ((beaconHashFamily bad 0).keyFintype n)
        (fun k => (crEquivocator bad 0 ((5, 1) : ℤ × ℤ) (6, 1)).wins n k) = 1
    rw [hall]
    exact @winProb_top ((beaconHashFamily bad 0).Key n) ((beaconHashFamily bad 0).keyFintype n)
      ((beaconHashFamily bad 0).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator bad 0 (5, 1) (6, 1)))

/-- **(TOOTH — the deployed commit floor is SATISFIABLE.)** The injective deployed hash `goodCR` satisfies
the proper keyed floor at `Role.commit`. -/
theorem hashRand_goodCR_commit_CR :
    CollisionResistant (hashRandCommitFamily Dregg2.Crypto.HashRandRefinement.goodX) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.HashRandRefinement.goodX.cr Role.commit
    Dregg2.Crypto.HashRandRefinement.goodCR_hashcr

/-- **(TOOTH — the deployed output floor is SATISFIABLE.)** The injective deployed hash `goodCR` satisfies
the proper keyed floor at `Role.output`. -/
theorem hashRand_goodCR_output_CR :
    CollisionResistant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.goodX) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.HashRandRefinement.goodX.cr Role.output
    Dregg2.Crypto.HashRandRefinement.goodCR_hashcr

/-- **(TOOTH — the deployed output floor is LOAD-BEARING.)** The deployed colliding combine `badCR`
(`H _ _ = 0`) has a bias equivocator winning on every key (advantage `1`), so its output family is NOT CR —
the deployed unbiasability's floor is a genuine constraint. -/
theorem hashRand_badCR_output_not_CR :
    ¬ CollisionResistant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX) := by
  intro hCR
  set bad := Dregg2.Crypto.HashRandRefinement.badX.cr with hbad
  have hadv : collisionAdv (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX)
      (crEquivocator bad Role.output (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) (Sum.inl (2, 2)))
      = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).Key n =>
        (crEquivocator bad Role.output (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ))
          (Sum.inl (2, 2))).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, hbad,
        Dregg2.Crypto.HashRandRefinement.badX, Dregg2.Crypto.HashRandRefinement.badCR]
    show @winProb ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).Key n)
        ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).keyFintype n)
        (fun k => (crEquivocator bad Role.output (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ))
          (Sum.inl (2, 2))).wins n k) = 1
    rw [hall]
    exact @winProb_top ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).Key n)
      ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).keyFintype n)
      ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR
    (crEquivocator bad Role.output (Sum.inl (1, 1)) (Sum.inl (2, 2))))

/-- **THE RE-GROUNDED BEACON BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective identity family, the
bias-equivocation advantage is negligible — the beacon safety runs end-to-end to a genuine `Negl`. -/
theorem beacon_binding_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp idFamily_CR)

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing beacon combine hash.)** The bare-CR floor at the
colliding `badBeaconOut` is refuted (`beacon_badBeaconOut_not_CR`), and it IS `HashCRHardQuant _ ⊤` — so
the `⊤` class is FALSE. The price of `hEff`, as a theorem. -/
theorem beacon_eff_top_false :
    ¬ HashCRHardQuant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.badBeaconOut 0) (fun _ => True) :=
  fun h => beacon_badBeaconOut_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing deployed combine hash.)** Same, on the deployed
`crypto-hashrand` colliding `badX` output hash (`hashRand_badCR_output_not_CR`). -/
theorem hashRand_output_eff_top_false :
    ¬ HashCRHardQuant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX) (fun _ => True) :=
  fun h => hashRand_badCR_output_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the beacon floor holds for ANY
combine/commit hash. -/
theorem beacon_eff_bot_vacuous {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) :
    HashCRHardQuant (beaconHashFamily cr i) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — beacon safety does NOT follow from the floor at another adversary.)** From the floor at some
OTHER adversary `B` the bias-equivocator's negligibility does not follow: `hD B hB` bounds a DIFFERENT
ensemble. -/
example {Idx W C : Type} [DecidableEq W] [DecidableEq C] (cr : CommitReveal Idx W C) (i : Idx)
    (Eff : Adversary (hashGame (beaconHashFamily cr i)) → Prop)
    (A : Adversary (beaconGame cr i))
    (B : Adversary (hashGame (beaconHashFamily cr i))) (hB : Eff B)
    (hD : HashCRHardQuant (beaconHashFamily cr i) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (beaconGame cr i) A) := hD B hB)
  trivial

/-- **THE `Eff` BEACON BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective deployed `goodX.cr` the
output `Eff`-floor at `⊤` holds (`hashRand_goodCR_output_CR`), so the deployed unbiasability runs
end-to-end to a genuine `Negl` at an inhabited hypothesis. -/
theorem hashrand_output_eff_fires
    (A : Adversary (hashRandOutputGame Dregg2.Crypto.HashRandRefinement.goodX)) :
    Negl (gameAdv (hashRandOutputGame Dregg2.Crypto.HashRandRefinement.goodX) A) :=
  hashrand_output_binding_advantage_bound Dregg2.Crypto.HashRandRefinement.goodX (fun _ => True) A
    trivial ((collisionResistant_iff_hashCRHardQuant_top _).mp hashRand_goodCR_output_CR)

#assert_all_clean [
  beacon_binding_advantage_bound,
  hashrand_commit_binding_advantage_bound,
  hashrand_output_binding_advantage_bound,
  beaconGame_wins_iff,
  beacon_binding_from_polyTime,
  hashrand_commit_binding_from_polyTime,
  hashrand_output_binding_from_polyTime,
  beacon_exBeaconHash_CR,
  beacon_badBeaconOut_not_CR,
  hashRand_goodCR_commit_CR,
  hashRand_goodCR_output_CR,
  hashRand_badCR_output_not_CR,
  beacon_binding_fires,
  beacon_eff_top_false,
  hashRand_output_eff_top_false,
  beacon_eff_bot_vacuous,
  hashrand_output_eff_fires
]

end Dregg2.Crypto.RandomnessBeaconRegrounded
