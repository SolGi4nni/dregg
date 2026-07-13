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
  (commitRevealFamily commitRevealFamily_CR_of_hashcr hermine_commitment_binding_advantage_bound
   crEquivocator)

set_option autoImplicit false

/-! ## §1 — the deployed id-commit hash as a keyed family. -/

/-- **THE ID-COMMITMENT KEYED FAMILY.** The deployed hybrid-identity commit hash `cr.H ()` over the
length-framed preimages, as a `KeyedHashFamily` (`commitRevealFamily cr ()`). This is the keyed hash the
proper collision game runs over — the honest floor object the id re-basing actually needs. -/
def idCommitFamily {Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) : KeyedHashFamily :=
  commitRevealFamily cr ()

/-! ## §2 — the advantage-bounded binding keystone (`id_commitment_binds`, re-grounded). -/

/-- **RE-GROUNDED `IdentityCommitment.id_commitment_binds`.** Under the proper keyed floor, the
enrollment-equivocation adversary (per key, two DISTINCT key pairs — hence two distinct length-framed
preimages, `IdentityCommitment.commit_collision_is_hash_collision` — colliding to one id, a hash collision)
has negligible advantage. The Boolean "one id ⟹ one key pair" becomes "⟹ one key pair EXCEPT with negligible
probability": a self-carried PQ key cannot impersonate the enrolled one except with negligible advantage.
Proof: `thread_advantage_bound` (the single `CollisionResistant` leaf), via the generic commit-reveal
keystone. -/
theorem id_commitment_binds_advantage_bound {Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id)
    (hCR : CollisionResistant (idCommitFamily cr))
    (equivocator : CollisionFinder (idCommitFamily cr)) :
    Negl (collisionAdv (idCommitFamily cr) equivocator) :=
  hermine_commitment_binding_advantage_bound hCR equivocator

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
theorem id_commitment_binds_fires (equivocator : CollisionFinder idFamily) :
    Negl (collisionAdv idFamily equivocator) :=
  hermine_commitment_binding_advantage_bound idFamily_CR equivocator

#assert_all_clean [
  id_commitment_binds_advantage_bound,
  idCommit_exCR_CR,
  idCommit_badCR_not_CR,
  id_commitment_binds_fires
]

end Dregg2.Crypto.IdentityCommitmentRegrounded
