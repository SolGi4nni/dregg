/-
# `Dregg2.Crypto.RandomnessBeaconRegrounded` — the POST-QUANTUM randomness beacon (abstract model AND the
deployed `crypto-hashrand` refinement) RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the
KEYED COLLISION GAME (`FloorGames.HashCRHardQuant F Eff`, adversary class IN THE STATEMENT).

⚑ The intermediate spelling `HashFloorHonesty.CollisionResistant` is DELETED (2026-07-28): it WAS
`HashCRHardQuant F (fun _ => True)` with the `⊤` folded into a name, and that `⊤` floor is itself FALSE
for every compressing hash (`FloorGames.hashCRHardQuant_top_false_of_compressing`). The `⊤`-class results
below are stated with the `⊤` written out; the DISCHARGED bindings are §2R's keyed-ROM successors.

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

Each `⊤`-class floor is SATISFIABLE (`beacon_exBeaconHash_CR` on the injective `exBeaconHash`;
`hashRand_goodCR_commit_CR` / `_output_CR` on the injective deployed `goodCR`) and REFUTABLE
(`beacon_badBeaconOut_not_CR` on the colliding `badBeaconOut`; `hashRand_badCR_output_not_CR` on the
deployed colliding `badCR`, both via `hashCRHardQuant_top_false_of_compressing`).

⚑ Those two poles are the WHOLE shape of the `⊤` class: it holds exactly for the injective families and
fails exactly for the compressing ones. So a satisfiability witness here says the hash is NOT compressing,
and the deployed `crypto-hashrand` combine/commit hashes — which ARE compressing — sit with `badCR` on the
refuted side. The keyed-ROM successors in §2R are what carry the deployed claim.

Old injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`, no `native_decide`.

## Coordination

Beacon commit-reveal leg. Generic template = `HermineHashCRRegrounded`; the PQ sortition VRF (also `HashCR`)
= `XmVrfRefinementRegrounded`; the wire channel binding = `WireAkeRegrounded`. Stays in the beacon subtree.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Crypto.HashRandRefinement

namespace Dregg2.Crypto.RandomnessBeaconRegrounded

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

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** The three keystones took the collision
floor at the UNRESTRICTED class — `HashCRHardQuant (…Family …) (fun _ => True)`, then written
`CollisionResistant (…Family …)`, a spelling since DELETED — and
`FloorGames.hashCRHardQuant_top_false_of_compressing` proves THAT false for any compressing hash — the
deployed `crypto-hashrand` commit and combine hashes included. So all three exported bounds rested on a
hypothesis REFUTED at deployed parameters: leader
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

/-! ### §2R — ⚑⚑ THE DISCHARGED SUCCESSORS: all three legs on the PROVED keyed-ROM floor.

⚑ **WHAT WAS DELETED HERE, AND WHY.** `beacon_binding_from_polyTime`,
`hashrand_commit_binding_from_polyTime` and `hashrand_output_binding_from_polyTime` discharged `Eff`
at `CostAdversary.IsPolyTime`, whose floor `HashCRHardQuant … (IsPolyTime …)` is REFUTED at deployed
parameters (`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`: `IsPolyTime`
prices answer SIZE, so a `.pure` answerer with a hardcoded short collision is in the class and wins
with probability `1`). ALL THREE ARE DELETED, and replaced by the keyed-ROM successors below.

⚑ **THE MODELLING STEP, STATED (not smuggled).** The abstract beacon combine hash is idealised as ONE
SAMPLED oracle `H : Idx × W → Fin (2 ^ l)` keyed by the beacon's own domain-separation index space;
the deployed `crypto-hashrand` surface as ONE oracle `H : Role × Pre → Fin (2 ^ l)` keyed by the
DEPLOYED `Role` tag, with the commit leg pinned at `Role.commit` and the combine leg at `Role.output`
(`fixedTagCarrier` — both legs share one oracle, exactly the deployed domain separation). The standard
ROM idealisation at an ASYMPTOTIC digest width — a deliberate labelled modelling step, NOT a
derivation about the fixed public function. The floor under all three is
`KeyedRomFloor.keyedRom_hard` (the birthday bound, PROVED); the breaks keep §2's commitOpenGame shape
(`romOpenGame`: the PUBLISHED beacon output / commitment is in the win relation). -/

section RomSuccessor

open Dregg2.Crypto.HashRandRefinement (Role) in
/-- The deployed `crypto-hashrand` role tag is finite — the flat family's key obligation, once. -/
def hrRoleFin : Fintype Role :=
  Fintype.ofList [Role.commit, Role.output] (fun r => by cases r <;> simp)

variable (Idx : Type) [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
variable (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]

/-- **THE ABSTRACT-BEACON KEYED-ROM FAMILY** — the combine/commit hash as ONE sampled oracle over the
index-separated domain `Idx × W`, ideal `λ`-bit outputs. -/
def beaconRomFamily : KeyedRomFamily :=
  flatFamily Idx inferInstance inferInstance inferInstance (fun _ => W)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The beacon family's width obligation, closed by construction. -/
theorem beaconRomFamily_card_R (l : ℕ) :
    letI := (beaconRomFamily Idx W).rFin l
    Fintype.card ((beaconRomFamily Idx W).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE BEACON CARRIER AT A PINNED INDEX `i`** — the deployed slot never lets the adversary move its
domain-separation index; the payload is the framed reveal itself, injective on the nose. -/
def beaconRomCarrier (i : Idx) : RomCarrier (beaconRomFamily Idx W) :=
  fixedTagCarrier _ (fun _ => i) (fun _ => Unit) (fun _ => W) (fun _ => inferInstance)
    (fun _ _ w => w) (fun _ _ _ _ h => h)

/-- The beacon-steering break at the sampled oracle: one PUBLISHED beacon output produced by two
DISTINCT reveals — §2's `beaconGame`, at the sampled oracle. -/
abbrev beaconRomGame (i : Idx) : Game := romOpenGame (beaconRomFamily Idx W) (beaconRomCarrier Idx W i)

/-- **THE DEPLOYED STEERING IS A WIN** — two distinct reveals whose `i`-tagged oracle outputs both
equal the published beacon output are a win. -/
theorem beaconRom_forgery_is_break (i : Idx) (l : ℕ) (H : (beaconRomGame Idx W i).Inst l)
    (out : Fin (2 ^ l)) {w w' : W} (hne : w ≠ w')
    (h1 : H (i, w) = out) (h2 : H (i, w') = out) :
    (beaconRomGame Idx W i).wins l H (out, (), w, w') :=
  ⟨hne, h1, h2⟩

/-- **⚑⚑ THE RE-GROUNDED BEACON BINDING — floor PROVED, nothing refutable carried.** Every
query-bounded beacon-steering adversary has NEGLIGIBLE advantage: no coalition steers or predicts the
beacon except with negligible probability, in the keyed ROM model of the header. This is what
`beacon_binding_from_polyTime` (DELETED — floor refuted) claimed and could not have. -/
theorem beacon_binding_rom (i : Idx) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (beaconRomGame Idx W i))
    (hA : RomOpenEff (beaconRomFamily Idx W) (beaconRomCarrier Idx W i) Q A) :
    Negl (gameAdv (beaconRomGame Idx W i) A) :=
  rom_open_binds _ _ Q hQ (beaconRomFamily_card_R Idx W) A hA

/-- **(TOOTH — the counterexample DIES.)** A steering adversary with non-negligible advantage is
OUTSIDE the query class. -/
theorem beaconRom_nonNegl_forger_excluded (i : Idx) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (beaconRomGame Idx W i)) (hnn : ¬ Negl (gameAdv (beaconRomGame Idx W i) A)) :
    ¬ RomOpenEff (beaconRomFamily Idx W) (beaconRomCarrier Idx W i) Q A :=
  romOpen_forger_excluded _ _ Q hQ (beaconRomFamily_card_R Idx W) A hnn

/-! ### The DEPLOYED `crypto-hashrand` surface: one oracle, two pinned roles. -/

open Dregg2.Crypto.HashRandRefinement (Role)

variable (Pre : Type) [Fintype Pre] [DecidableEq Pre] [Nonempty Pre]

/-- **THE `crypto-hashrand` KEYED-ROM FAMILY** — ONE oracle for both deployed legs, keyed by the
DEPLOYED `Role` tag (`Role.commit` / `Role.output`), over the framed pre-image space. -/
def hashRandRomFamily : KeyedRomFamily :=
  flatFamily Role hrRoleFin inferInstance ⟨Role.commit⟩ (fun _ => Pre)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The deployed family's width obligation, closed by construction. -/
theorem hashRandRomFamily_card_R (l : ℕ) :
    letI := (hashRandRomFamily Pre).rFin l
    Fintype.card ((hashRandRomFamily Pre).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE COMMIT-LEG CARRIER** — `H (Role.commit, ·)`, role pinned in the encoding. -/
def hashRandCommitRomCarrier : RomCarrier (hashRandRomFamily Pre) :=
  fixedTagCarrier _ (fun _ => Role.commit) (fun _ => Unit) (fun _ => Pre) (fun _ => inferInstance)
    (fun _ _ p => p) (fun _ _ _ _ h => h)

/-- **THE COMBINE-LEG CARRIER** — `H (Role.output, ·)`, same oracle, the other pinned role. -/
def hashRandOutputRomCarrier : RomCarrier (hashRandRomFamily Pre) :=
  fixedTagCarrier _ (fun _ => Role.output) (fun _ => Unit) (fun _ => Pre) (fun _ => inferInstance)
    (fun _ _ p => p) (fun _ _ _ _ h => h)

/-- The commit-equivocation break at the sampled oracle (UNPREDICTABILITY's break). -/
abbrev hashRandCommitRomGame : Game :=
  romOpenGame (hashRandRomFamily Pre) (hashRandCommitRomCarrier Pre)

/-- The bias break at the sampled oracle (UNBIASABILITY's break). -/
abbrev hashRandOutputRomGame : Game :=
  romOpenGame (hashRandRomFamily Pre) (hashRandOutputRomCarrier Pre)

/-- **⚑ THE RE-GROUNDED DEPLOYED COMMIT BINDING** — an honest party is pinned to ONE contribution
except with negligible probability (UNPREDICTABILITY's ground), floor PROVED. Successor of the
deleted `hashrand_commit_binding_from_polyTime`. -/
theorem hashrand_commit_binding_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (hashRandCommitRomGame Pre))
    (hA : RomOpenEff (hashRandRomFamily Pre) (hashRandCommitRomCarrier Pre) Q A) :
    Negl (gameAdv (hashRandCommitRomGame Pre) A) :=
  rom_open_binds _ _ Q hQ (hashRandRomFamily_card_R Pre) A hA

/-- **⚑ THE RE-GROUNDED DEPLOYED COMBINE BINDING** — the honest contribution MOVES the beacon except
with negligible probability (UNBIASABILITY's ground), floor PROVED. Successor of the deleted
`hashrand_output_binding_from_polyTime`. -/
theorem hashrand_output_binding_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (hashRandOutputRomGame Pre))
    (hA : RomOpenEff (hashRandRomFamily Pre) (hashRandOutputRomCarrier Pre) Q A) :
    Negl (gameAdv (hashRandOutputRomGame Pre) A) :=
  rom_open_binds _ _ Q hQ (hashRandRomFamily_card_R Pre) A hA

/-- **(TOOTH — admitted, winnable, DEFANGED, at a CLOSED instance.)** At `Pre = Fin 4`, `Q = 2`: the
`0`-query hardcoded opener — the exact `IsPolyTime`-refuting shape — is IN the class, wins with
POSITIVE probability, and its advantage is NEGLIGIBLE, on the DEPLOYED role-separated surface. -/
theorem hashRandRom_fires :
    (RomOpenEff (hashRandRomFamily (Fin 4)) (hashRandOutputRomCarrier (Fin 4)) (fun _ => 2)
        (romOpenAdv _ _ (constOpenComp _ (hashRandOutputRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ()) (fun _ => (0 : Fin 4)) (fun _ => (1 : Fin 4)))))
    ∧ (∀ l, 0 < gameAdv (hashRandOutputRomGame (Fin 4))
        (romOpenAdv _ _ (constOpenComp _ (hashRandOutputRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ()) (fun _ => (0 : Fin 4)) (fun _ => (1 : Fin 4)))) l)
    ∧ Negl (gameAdv (hashRandOutputRomGame (Fin 4))
        (romOpenAdv _ _ (constOpenComp _ (hashRandOutputRomCarrier (Fin 4))
          (fun l => (0 : Fin (2 ^ l))) (fun _ => ()) (fun _ => (0 : Fin 4)) (fun _ => (1 : Fin 4))))) := by
  refine ⟨constOpen_in_eff _ _ _ _ _ _ _,
    fun l => constOpen_gameAdv_pos _ _ _ _ _ _ l (by show (0 : Fin 4) ≠ 1; decide),
    constOpen_binds _ _ _ _ _ _ (fun _ => 2) ⟨1, 5, ?_⟩ (hashRandRomFamily_card_R (Fin 4))⟩
  filter_upwards [Filter.eventually_ge_atTop 5] with n hn
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

end RomSuccessor

/-! ## §3 — non-vacuity: satisfiable AND load-bearing, on the abstract beacon and the deployed surface. -/

/-- **(TOOTH — the beacon `⊤`-class floor is SATISFIABLE.)** The injective combine hash `exBeaconHash`
satisfies the keyed collision floor at the UNRESTRICTED class. ⚑ Injectivity is the only way to satisfy
it (see `beacon_badBeaconOut_not_CR`), so this witness says `exBeaconHash` is not compressing. -/
theorem beacon_exBeaconHash_CR :
    HashCRHardQuant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.exBeaconHash 0) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.RandomnessBeacon.exBeaconHash 0
    Dregg2.Crypto.RandomnessBeacon.exBeaconHash_hashcr

/-- **(TOOTH — the beacon `⊤`-class floor is REFUTABLE.)** The colliding combine hash `badBeaconOut`
(`H _ _ = 0`, every reveal absorbed to one output) has a collision at EVERY key (`(5,1) ≠ (6,1)` yet both
hash to `0`), so `hashCRHardQuant_top_false_of_compressing` refutes the floor at the UNRESTRICTED class —
and the same argument runs at any compressing combine hash, the deployed one included. -/
theorem beacon_badBeaconOut_not_CR :
    ¬ HashCRHardQuant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.badBeaconOut 0)
      (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨((0, 0) : ℤ × ℤ)⟩
    (fun _ _ => ⟨((5, 1) : ℤ × ℤ), ((6, 1) : ℤ × ℤ), ?_, rfl⟩)
  show ((5, 1) : ℤ × ℤ) ≠ (6, 1)
  norm_num

/-- **(TOOTH — the deployed commit `⊤`-class floor is SATISFIABLE.)** The injective deployed hash `goodCR`
satisfies the keyed collision floor at the UNRESTRICTED class, at `Role.commit`. -/
theorem hashRand_goodCR_commit_CR :
    HashCRHardQuant (hashRandCommitFamily Dregg2.Crypto.HashRandRefinement.goodX) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.HashRandRefinement.goodX.cr Role.commit
    Dregg2.Crypto.HashRandRefinement.goodCR_hashcr

/-- **(TOOTH — the deployed output `⊤`-class floor is SATISFIABLE.)** The injective deployed hash `goodCR`
satisfies the keyed collision floor at the UNRESTRICTED class, at `Role.output`. ⚑ `goodCR` is the
INJECTIVE toy (`H role p = p`); the deployed compressing combine hash is refuted by
`hashRand_badCR_output_not_CR`'s argument, not covered by this. -/
theorem hashRand_goodCR_output_CR :
    HashCRHardQuant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.goodX) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.HashRandRefinement.goodX.cr Role.output
    Dregg2.Crypto.HashRandRefinement.goodCR_hashcr

/-- **(TOOTH — the deployed output `⊤`-class floor is REFUTABLE.)** The deployed colliding combine `badCR`
(`H _ _ = 0`) has a collision at EVERY key (`inl (1,1) ≠ inl (2,2)`, both absorbed to `0`), so
`hashCRHardQuant_top_false_of_compressing` refutes the floor at the UNRESTRICTED class. ⚑ The argument
needs only compression, so it applies verbatim to the DEPLOYED `H("output", sorted[(i,cᵢ)])`. -/
theorem hashRand_badCR_output_not_CR :
    ¬ HashCRHardQuant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX)
      (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _
    ⟨(Sum.inl (0, 0) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ))⟩
    (fun _ _ => ⟨(Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)),
      (Sum.inl (2, 2) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)), ?_, rfl⟩)
  show (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) ≠ Sum.inl (2, 2)
  simp

/-- **THE RE-GROUNDED BEACON BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective identity family, the
bias-equivocation advantage is negligible — the beacon safety runs end-to-end to a genuine `Negl`. -/
theorem beacon_binding_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    idFamily_hashCRHardQuant_top

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing beacon combine hash.)** The price of `hEff`, as a
theorem: the `⊤` class is refuted at the colliding `badBeaconOut`.

⚑ This IS `beacon_badBeaconOut_not_CR` — nothing is added. It used to bridge a `CollisionResistant`
refutation across `collisionResistant_iff_hashCRHardQuant_top`; with the `⊤` now written into the tooth's
own statement, the bridge is the identity. Both names are kept because `Verify/FloorRatchetBaseline`
grandfathers refuted-floor carriers BY NAME. -/
theorem beacon_eff_top_false :
    ¬ HashCRHardQuant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.badBeaconOut 0) (fun _ => True) :=
  beacon_badBeaconOut_not_CR

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing deployed combine hash.)** Same, on the deployed
`crypto-hashrand` colliding `badX` output hash — and, like its beacon sibling above, this now IS
`hashRand_badCR_output_not_CR`, the `⊤` having moved into that tooth's own statement. -/
theorem hashRand_output_eff_top_false :
    ¬ HashCRHardQuant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX) (fun _ => True) :=
  hashRand_badCR_output_not_CR

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

/-- **THE `Eff` BEACON BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective `goodX.cr` the output
`Eff`-floor at `⊤` holds (`hashRand_goodCR_output_CR`), so the unbiasability reduction runs end-to-end to
a genuine `Negl` at an inhabited hypothesis. Read with `hashRand_output_eff_top_false`: it fires HERE and
cannot fire at a compressing combine hash, which is why the deployed discharge is §2R's keyed ROM. -/
theorem hashrand_output_eff_fires
    (A : Adversary (hashRandOutputGame Dregg2.Crypto.HashRandRefinement.goodX)) :
    Negl (gameAdv (hashRandOutputGame Dregg2.Crypto.HashRandRefinement.goodX) A) :=
  hashrand_output_binding_advantage_bound Dregg2.Crypto.HashRandRefinement.goodX (fun _ => True) A
    trivial hashRand_goodCR_output_CR

#assert_all_clean [
  beacon_binding_advantage_bound,
  hashrand_commit_binding_advantage_bound,
  hashrand_output_binding_advantage_bound,
  beaconGame_wins_iff,
  beaconRomFamily_card_R,
  beaconRom_forgery_is_break,
  beacon_binding_rom,
  beaconRom_nonNegl_forger_excluded,
  hashRandRomFamily_card_R,
  hashrand_commit_binding_rom,
  hashrand_output_binding_rom,
  hashRandRom_fires,
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
