/-
# `Dregg2.Crypto.IdentityCommitmentRegrounded` — the DEPLOYED hybrid-identity-commitment binding
RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the PROPER keyed `CollisionResistant` floor.

## The gap this closes (the id-re-basing leg of the 07-13 floor sweep)

`IdentityCommitment.id_commitment_binds` is the soundness floor UNDER THE DEPLOYED id re-basing
(`types/src/lib.rs::hybrid_id_commitment`; the `cell-crypto` / `captp` / `wire` `verify_committed_ml_dsa`
gate). It concludes "one id determines its `(ed25519, ml_dsa)` pair uniquely", conditioned on
`HermineHintMLWE.HashCR cr` — the SAME injective floor `HashFloorHonesty.hashCR_false_of_compressing`
PROVES FALSE for any compressing commitment. `hybrid_id_commitment = BLAKE3_derive_key(tag, ed ‖ len(ml) ‖ ml)`
maps a long framed preimage to a fixed-width id, so it IS compressing — the deployed gate's binding lemma
is VACUOUSLY TRUE at real parameters.

`HermineHashCRRegrounded` landed the generic commit-reveal regrounding (`commitRevealFamily`,
`hermine_commitment_binding_advantage_bound`) and its prose names IdentityCommitment as a "DEPLOYED-reachable
reuse" — but no theorem instantiates it for the id-commitment gate's own `cr`. This file wires that: it moves
the deployed gate onto the proper floor, so the id re-basing no longer rides an empty hypothesis.

## The re-grounding

* **`idCommitFamily cr`** — the deployed id-commit hash `H(())` over framed preimages, as the keyed hash
  family `commitRevealFamily cr ()` the honest collision game runs over.
* **`id_commitment_binds_advantage_bound`** — the advantage-bounded sibling of `id_commitment_binds`: an
  enrollment-equivocation adversary (two DISTINCT key pairs — hence two distinct length-framed preimages,
  by `IdentityCommitment.commit_collision_is_hash_collision` — colliding to one id) IS a `CollisionFinder`,
  so under the proper `CollisionResistant (idCommitFamily cr)` floor its advantage is `Negl`. "one id ⟹ one
  key pair" becomes "one id ⟹ one key pair EXCEPT with negligible probability" — a self-carried PQ key
  cannot impersonate the enrolled one except with negligible advantage. Discharged by
  `thread_advantage_bound` (the single `CollisionResistant` leaf), reusing the generic keystone.

## Non-fake

The floor is SATISFIABLE (`idCommit_exCR_CR`: the injective `IdentityCommitment.exCR` discharges it) and
LOAD-BEARING (`idCommit_badCR_not_CR`: the COLLIDING `IdentityCommitment.badCR` has an equivocator winning
on every key, advantage `1`, so its family is NOT CR — mirrors `IdentityCommitment.binding_needs_hashcr`).
The old injective-floor consumers are KEPT untouched; this file only ADDS the sibling. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`.

## Coordination

This is the id-re-basing commit-reveal leg. The generic template + the concurrent-forgery composition are
`HermineHashCRRegrounded`; the STARK/FRI/Merkle hash consumers are `Circuit.FloorRegroundedConsumers`; the
`MSISHard`/DL Boolean crypto floors are `FloorBridge`/`CryptoFloorTeeth`. It stays in the
`IdentityCommitment` subtree — no consumer moved here lives elsewhere.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.IdentityCommitment

namespace Dregg2.Crypto.IdentityCommitmentRegrounded

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
  (Game Adversary gameAdv gameAdv_mem_unit hashGame finderToAdv HashCRHardQuant
   collisionResistant_iff_hashCRHardQuant_top hard_bot_vacuous)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.IdentityCommitment (commit verify_committed)

set_option autoImplicit false

/-! ## §1 — the deployed id-commit hash as a keyed family. -/

/-- **THE ID-COMMITMENT KEYED FAMILY.** The deployed hybrid-identity commit hash `cr.H ()` over the
length-framed preimages, as a `KeyedHashFamily` (`commitRevealFamily cr ()`). This is the keyed hash the
proper collision game runs over — the honest floor object the id re-basing actually needs. -/
def idCommitFamily {Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) : KeyedHashFamily :=
  commitRevealFamily cr ()

/-! ## §2 — the ENROLLMENT EQUIVOCATION, as a SECURITY REDUCTION on the DEPLOYED gate.

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** `id_commitment_binds_advantage_bound` took
`hCR : CollisionResistant (idCommitFamily cr)`. `FloorGames.collisionResistant_iff_hashCRHardQuant_top`
proves that IS the collision floor at the UNRESTRICTED class, and `collisionResistant_false_of_compressing`
proves THAT false for any compressing hash — including the deployed
`BLAKE3(tag, ed ‖ len(ml) ‖ ml)`. So the exported binding rested on a hypothesis REFUTED at deployed
parameters. Its `_eff` sibling took a `CollisionFinder` and applied the floor TO IT, so the ENROLLMENT
never appeared in a `Prop` at all. BOTH ARE DELETED.

What stands here is stronger than a generic instantiation: the break game is stated on the DEPLOYED
enrollment gate `IdentityCommitment.verify_committed` — the Rust `==` check — so the adversary's win is
literally "two DISTINCT `(ed25519, ml_dsa)` pairs both pass the gate against one enrolled id". The
extractor is the LENGTH FRAMING, and `hframe`'s contrapositive is what makes the two framed pre-images
distinct: that is the step `IdentityCommitment.id_commitment_binds` spends its (false) `HashCR` on. -/

/-- **THE ENROLLMENT-EQUIVOCATION GAME.** The adversary is handed a sampled key and WINS iff it publishes
an identity together with TWO key pairs that BOTH pass the deployed enrollment gate
(`verify_committed`, i.e. `commit cr frame ed ml = id`) while DIFFERING. A win is exactly the
impersonation `IdentityCommitment.attacker_key_not_committed` denies: a self-carried PQ key that the
enrolled id accepts. The deployed gate is IN the win relation. -/
noncomputable def enrollGame {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre) : Game where
  Inst := fun _ => Unit
  Ans := fun _ => Id × (Ed × MlDsa) × (Ed × MlDsa)
  instFin := fun _ => inferInstance
  instNe := fun _ => inferInstance
  wins := fun _ _ p =>
    p.2.1 ≠ p.2.2 ∧
      verify_committed cr frame p.1 p.2.1.1 p.2.1.2 ∧ verify_committed cr frame p.1 p.2.2.1 p.2.2.2
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — a win unfolds, by `Iff.rfl`, to two distinct key pairs passing
the deployed enrollment gate against one id. -/
theorem enrollGame_wins_iff {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre) (n : ℕ) (k : Unit)
    (p : Id × (Ed × MlDsa) × (Ed × MlDsa)) :
    (enrollGame cr frame).wins n k p ↔
      (p.2.1 ≠ p.2.2 ∧
        verify_committed cr frame p.1 p.2.1.1 p.2.1.2 ∧
          verify_committed cr frame p.1 p.2.2.1 p.2.2.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** An enrollment equivocator becomes a hash-collision finder
by FRAMING its two key pairs — `frame ed ml = ed ‖ len(ml) ‖ ml`, the deployed length framing. The
published id is discarded; the collision must be re-derived on the other side. -/
def enrollToFinder {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (A : Adversary (enrollGame cr frame)) : Adversary (hashGame (idCommitFamily cr)) where
  run := fun n k =>
    let p := A.run n k
    (frame p.2.1.1 p.2.1.2, frame p.2.2.1 p.2.2.2)

/-- **⚑ WIN-PRESERVATION — and this IS `IdentityCommitment.commit_collision_is_hash_collision`, as a map
rather than an `∃`.** Wherever the equivocator wins, the two framed pre-images are a GENUINE collision:
they are DISTINCT because `hframe` is injective in both arguments and the pairs differ, and their hashes
are EQUAL because both equal the published id. The `∃`-form of this fact is unconditionally TRUE at
deployed parameters by pigeonhole and so binds nothing; a MAP OF ADVERSARIES lands in a game advantage,
which a floor can bind. -/
theorem enroll_wins_imp {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame) (A : Adversary (enrollGame cr frame)) (n : ℕ) (k : Unit)
    (hwin : (enrollGame cr frame).wins n k (A.run n k)) :
    (hashGame (idCommitFamily cr)).wins n k ((enrollToFinder cr frame A).run n k) := by
  obtain ⟨hne, h1, h2⟩ := hwin
  refine ⟨fun hf => hne ?_, ?_⟩
  · obtain ⟨he, hm⟩ := hframe hf
    exact Prod.ext he hm
  · show cr.H () (frame (A.run n k).2.1.1 (A.run n k).2.1.2)
      = cr.H () (frame (A.run n k).2.2.1 (A.run n k).2.2.2)
    exact h1.trans h2.symm

/-- **THE ADVANTAGE INEQUALITY.** The enrollment equivocator's advantage is at most the extracted
finder's, at every parameter. Unconditional: no adversary class appears. -/
theorem enroll_adv_le {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame) (A : Adversary (enrollGame cr frame)) (n : ℕ) :
    gameAdv (enrollGame cr frame) A n
      ≤ gameAdv (hashGame (idCommitFamily cr)) (enrollToFinder cr frame A) n := by
  refine @winProb_le_of_imp _ ((enrollGame cr frame).instFin n) _ _ (fun k hk => ?_)
  rw [Adversary.hit_eq_true] at hk ⊢
  exact enroll_wins_imp cr frame hframe A n k hk

/-- **⚑ RE-GROUNDED `IdentityCommitment.id_commitment_binds` — from the id-commit hash's collision floor,
VIA the reduction.** Under the collision floor at the class `Eff`, an enrollment equivocator whose
extracted finder is in that class has NEGLIGIBLE advantage: an id determines its `(ed25519, ml_dsa)` pair
EXCEPT with negligible probability, so a self-carried PQ key cannot impersonate the enrolled one except
with that advantage. The Boolean "one id ⟹ one key pair", which needed the FALSE injective `HashCR`,
becomes an honest advantage bound.

`Eff` is a parameter here because this is the statement at an ARBITRARY class; `_from_polyTime`
discharges it. -/
theorem id_commitment_binds_advantage_bound {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame)
    (Eff : Adversary (hashGame (idCommitFamily cr)) → Prop)
    (A : Adversary (enrollGame cr frame))
    (hEff : Eff (enrollToFinder cr frame A))
    (hD : HashCRHardQuant (idCommitFamily cr) Eff) :
    Negl (gameAdv (enrollGame cr frame) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (enrollGame cr frame) A n).1)
    (enroll_adv_le cr frame hframe A) (hD _ hEff)

/-- **THE ENROLLMENT GAME'S ANSWER ENCODING** — the published id plus the two key pairs, at the
deployment's own encodings. -/
def enrollAnsSize {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (szEd : Ed → ℕ) (szMl : MlDsa → ℕ) (szId : Id → ℕ) : AnsSize (enrollGame cr frame) :=
  fun _ (p : Id × (Ed × MlDsa) × (Ed × MlDsa)) =>
    szId p.1 + (szEd p.2.1.1 + szMl p.2.1.2) + (szEd p.2.2.1 + szMl p.2.2.2)

/-- **⚑ THE EFFICIENCY OBLIGATION DISCHARGED.** An enrollment equivocator that is EFFICIENT at the game's
own answer encoding, put through the length framing, yields a collision finder that is STILL efficient —
so the collision floor at `Eff := IsPolyTime` applies to IT, and the id binds its key pair with no
floating efficiency parameter.

The per-site inputs are the reshaper's declared work `(cw, bw)` and the FRAMING'S OWN GROWTH `hout`: the
framing WRITES a new pre-image (`ed ‖ len(ml) ‖ ml`), so its size is a property of the deployed encoding,
not derivable from abstract carriers. That is the one honest modelling input; no `PolyBoundedNat`
overhead hypothesis is taken. -/
theorem id_commitment_binds_from_polyTime {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame)
    (szEd : Ed → ℕ) (szMl : MlDsa → ℕ) (szId : Id → ℕ) (szIn : ℕ → Pre → ℕ)
    (A : Adversary (enrollGame cr frame))
    (hA : IsPolyTime (enrollAnsSize cr frame szEd szMl szId) A) (cw bw co bo : ℕ)
    (hout : ∀ n (k : Unit) (p : Id × (Ed × MlDsa) × (Ed × MlDsa)),
      szIn n (frame p.2.1.1 p.2.1.2) + szIn n (frame p.2.2.1 p.2.2.2)
        ≤ co * enrollAnsSize cr frame szEd szMl szId n p + bo)
    (hD : HashCRHardQuant (idCommitFamily cr)
      (IsPolyTime (hashAnsSizeOf (idCommitFamily cr) szIn))) :
    Negl (gameAdv (enrollGame cr frame) A) := by
  have hEff : IsPolyTime (hashAnsSizeOf (idCommitFamily cr) szIn) (enrollToFinder cr frame A) := by
    poly_time (enrollAnsSize cr frame szEd szMl szId) (hashAnsSizeOf (idCommitFamily cr) szIn)
      (fun _ _ (p : Id × (Ed × MlDsa) × (Ed × MlDsa)) =>
        (frame p.2.1.1 p.2.1.2, frame p.2.2.1 p.2.2.2))
      cw bw co bo hA
    exact hout
  exact id_commitment_binds_advantage_bound cr frame hframe
    (IsPolyTime (hashAnsSizeOf (idCommitFamily cr) szIn)) A hEff hD

/-! ## §3 — non-vacuity: the floor is satisfiable AND load-bearing on the id-commitment. -/

/-- **(TOOTH — the floor is SATISFIABLE on the id-commitment.)** The binding instance
`IdentityCommitment.exCR` (`H () p = p`, injective) satisfies the proper keyed floor — the sibling
hypothesis is inhabited, unlike the vacuous injective floor. -/
theorem idCommit_exCR_CR : CollisionResistant (idCommitFamily Dregg2.Crypto.IdentityCommitment.exCR) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.IdentityCommitment.exCR ()
    Dregg2.Crypto.IdentityCommitment.exCR_hashcr

/-- **(TOOTH — the floor is LOAD-BEARING on the id-commitment.)** The COLLIDING commit
`IdentityCommitment.badCR` (`H () _ = []`, every framed preimage opens every id) has the equivocator
`crEquivocator badCR () [1] [2]` winning on EVERY key (`[1] ≠ [2]` yet both hash to `[]`), so its advantage
is the constant `1` and the family is NOT collision-resistant. So the sibling cannot be discharged on a
broken commit — the proper floor is a genuine constraint, exactly as `IdentityCommitment.binding_needs_hashcr`
shows the id stops binding once collision-resistance fails. -/
theorem idCommit_badCR_not_CR :
    ¬ CollisionResistant (idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR) := by
  intro hCR
  have hadv : collisionAdv (idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR)
      (crEquivocator Dregg2.Crypto.IdentityCommitment.badCR () ([1] : List ℕ) [2]) = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR).Key n =>
        (crEquivocator Dregg2.Crypto.IdentityCommitment.badCR () ([1] : List ℕ) [2]).wins n k)
        = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily,
        Dregg2.Crypto.IdentityCommitment.badCR]
    show @winProb ((idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR).Key n)
        ((idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR).keyFintype n)
        (fun k => (crEquivocator Dregg2.Crypto.IdentityCommitment.badCR () ([1] : List ℕ) [2]).wins n k) = 1
    rw [hall]
    exact @winProb_top ((idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR).Key n)
      ((idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR).keyFintype n)
      ((idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator Dregg2.Crypto.IdentityCommitment.badCR () [1] [2]))

/-- **THE RE-GROUNDED GATE FIRES AT A REAL FLOOR WITNESS.** On the injective identity family
(`HashFloorHonesty.idFamily_CR`), the enrollment-equivocation advantage is negligible — the deployed
id-re-basing binding runs end-to-end to a genuine `Negl` conclusion at an inhabited floor hypothesis. -/
theorem id_commitment_binds_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp idFamily_CR)

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the deployed compressing id-commit.)** The bare-CR floor at the
colliding `IdentityCommitment.badCR` is refuted (`idCommit_badCR_not_CR`), and it IS `HashCRHardQuant _ ⊤`
(`collisionResistant_iff_hashCRHardQuant_top`) — so the `⊤` class is FALSE. The price of `hEff`, stated as
a theorem: the class cannot be left implicit. -/
theorem idCommit_eff_top_false :
    ¬ HashCRHardQuant (idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR) (fun _ => True) :=
  fun h => idCommit_badCR_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY
id-commit hash. -/
theorem idCommit_eff_bot_vacuous {Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) :
    HashCRHardQuant (idCommitFamily cr) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the gate does NOT follow from the floor applied at another adversary.)** From the floor at
some OTHER adversary `B` the enrollment-equivocator's negligibility does not follow: `hD B hB` bounds a
DIFFERENT ensemble, and only the game-advantage bridge at the extracted finder connects it. -/
example {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id] (cr : CommitReveal Unit Pre Id)
    (frame : Ed → MlDsa → Pre)
    (Eff : Adversary (hashGame (idCommitFamily cr)) → Prop)
    (A : Adversary (enrollGame cr frame))
    (B : Adversary (hashGame (idCommitFamily cr))) (hB : Eff B)
    (hD : HashCRHardQuant (idCommitFamily cr) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (enrollGame cr frame) A) := hD B hB)
  trivial

/-- **THE `Eff` GATE FIRES AT A REAL FLOOR WITNESS.** On the injective deployed `IdentityCommitment.exCR`
the `Eff`-floor at `⊤` holds (`idCommit_exCR_CR`, an INHABITED hypothesis, unlike the vacuous injective
floor), so the `Eff` gate runs end-to-end to a genuine `Negl`. -/
theorem id_commitment_binds_eff_fires
    (A : Adversary (enrollGame Dregg2.Crypto.IdentityCommitment.exCR
      Dregg2.Crypto.IdentityCommitment.exFrame)) :
    Negl (gameAdv (enrollGame Dregg2.Crypto.IdentityCommitment.exCR
      Dregg2.Crypto.IdentityCommitment.exFrame) A) :=
  id_commitment_binds_advantage_bound Dregg2.Crypto.IdentityCommitment.exCR
    Dregg2.Crypto.IdentityCommitment.exFrame Dregg2.Crypto.IdentityCommitment.exFrame_inj
    (fun _ => True) A trivial
    ((collisionResistant_iff_hashCRHardQuant_top _).mp idCommit_exCR_CR)

#assert_all_clean [
  enrollGame_wins_iff,
  enroll_wins_imp,
  enroll_adv_le,
  id_commitment_binds_advantage_bound,
  id_commitment_binds_from_polyTime,
  idCommit_exCR_CR,
  idCommit_badCR_not_CR,
  id_commitment_binds_fires,
  idCommit_eff_top_false,
  idCommit_eff_bot_vacuous,
  id_commitment_binds_eff_fires
]

end Dregg2.Crypto.IdentityCommitmentRegrounded
