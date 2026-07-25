/-
# Dregg2.Circuit.Emit.LightClientEthFinFold — wiring the SHA-256 fold into ETH finality:
`FIN_OK` becomes DERIVED, not a trusted witnessed boolean carrier.

## The carrier being folded out

`LightClientEthAir.FIN_OK` is a witnessed boolean column standing for
`beq (reconstruct L (htrHeader L finalizedBeacon) finalityBranch finalizedRootSubtreeIndex)
attestedStateRoot` — the finality Merkle-branch fold of `Dregg2.Bridge.LightClientEth.reconstruct`.
In the carrier slice the AIR forces `FIN_OK = 1` and the refinement `ethLcAir_no_forgery` takes the
HONEST-WITNESS relation `hfin : a FIN_OK = if beq(reconstruct …) then 1 else 0` as a hypothesis — i.e.
it TRUSTS the prover set the bit to the true SHA result. The verifier re-runs no hash; it believes a
bit.

This file replaces that trust with the branch itself. `Sha256MerkleFold.merkleBranchFold` GENERATES
the constraints that recompute `reconstruct` in-circuit via `Sha256MerkleFold.sha256PairHash` (the SSZ
two-block SHA-256, FIPS-anchored). The tie proved here:

  * `reconstruct_shaWordLeaf_eq_foldReconstruct` — for the SHA leaf (`shaWordLeaf`: `Digest = List Nat`,
    `hashPair = pairHash`), the bridge's `reconstruct` IS the generator's `foldReconstruct`. So the AIR
    fold recomputes EXACTLY the object `FIN_OK` stood for — via the SHA arithmetic, not a bit.
  * `verifyFinalityBranch_from_fold` — the finality gate's boolean is DISCHARGED by the (derived)
    branch fold: no `FIN_OK` column is read. A satisfying prover must EXHIBIT a branch whose SHA fold
    hits the attested state root.
  * `eth_finality_from_fold_slots_into_no_forgery` — the fold-derived finality slots into
    `eth_no_forgery` IN PLACE of the trusted bit: the no-forgery guarantee holds with one fewer
    trusted carrier. Trust moves from "an opaque prover-set bit" to "the SHA gadget's gates over an
    exhibited branch" — the latter is atomic-KAT'd (`Sha256Gadget`/`Sha256MerkleFold` §0/§2) and
    provable in principle (residual #1), not an opaque node computation.

## What remains (the honest, PRICED residuals — this is proof-mode step 1)

  * RESIDUAL #1 (proof-composition wall): the hypothesis `hfold : foldReconstruct … = attested` is,
    in the deployed circuit, the CONCLUSION of the fold gates forcing their SHA outputs up ~30k
    gates/block × 2 blocks × depth. The atomic gates are forced + both-polarity KAT'd
    (`xor3_forces`/`chHead_forces`/`majHead_forces`/`addMod32_forces`); the full composition is the
    next slice. Here `hfold` is an explicit hypothesis, so what is DERIVED vs ASSUMED is visible.
  * RESIDUAL #2 (deploy/emit wall): the depth-6 two-block-SHA fold is ~4.9·10^5 flat gates, so it
    cannot be merged into `ethLcVerifyDesc`'s byte-golden `#guard emitVmJson2` and the `FIN_OK` column
    cannot be flat-removed from the DEPLOYED descriptor in this slice (a kernel `#guard` does not
    reduce over that many gates). The deployed removal routes through the IR-v2 `proofBind` recursion
    seam (the fold as a bound sub-proof). `ethLcVerifyDesc` and its golden are UNTOUCHED here.
  * RESIDUAL #3 (felt-width): `bindRootWords` binds the fold's 8 output words to a witnessed target
    root word-for-word; the 256-bit ↔ nine-radix-2^31-limb repack to `FIN_STATE_ROOT` is the same
    field-soundness residual `LightClientEthAir` §6 carries.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `shaWordLeaf` is a lawful `EthLeaf`
DEMONSTRATION instance (`Digest = List Nat`, `hashPair = pairHash`); its `hashPairCR`/`uChunkInj` are
the GENUINE named SHA/encoding assumptions (Props over its own primitives — the production floor,
exactly as `LightClientEth`'s production instance), taken as explicit hypotheses where consumed. NEW
file; imports read-only (`Sha256MerkleFold`, `Bridge.LightClientEth`).
-/
import Dregg2.Circuit.Emit.Sha256MerkleFold
import Dregg2.Bridge.LightClientEth

namespace Dregg2.Circuit.Emit.LightClientEthFinFold

open Dregg2.Circuit.Emit.Sha256MerkleFold
open Dregg2.Bridge.LightClientEth

set_option autoImplicit false

/-! ## §1 — The abstract fold: `reconstruct` and `foldReconstruct` are ONE fold, differing only in
the leaf-hash instantiation. -/

/-- The Merkle-branch fold parameterized by the pair-hash — the shared shape of the bridge's
`reconstruct` (at `L.hashPair`) and the generator's `foldReconstruct` (at `pairHash`). -/
def absFold {D : Type} (hp : D → D → D) : D → List D → Nat → D
  | leaf, [], _ => leaf
  | leaf, sib :: rest, idx =>
      absFold hp (if idx % 2 = 1 then hp sib leaf else hp leaf sib) rest (idx / 2)

/-- The bridge's `reconstruct` IS `absFold` at the leaf's pair-hash (definitional shape match). -/
theorem reconstruct_eq_absFold (L : EthLeaf) (leaf : L.Digest) (branch : List L.Digest) (idx : Nat) :
    reconstruct L leaf branch idx = absFold L.hashPair leaf branch idx := by
  induction branch generalizing leaf idx with
  | nil => rfl
  | cons sib rest ih =>
    -- both sides step to the recursive call with the SAME `if idx%2=1 …` new leaf (`hp = L.hashPair`)
    simp only [reconstruct, absFold]; exact ih _ _

/-- The generator's `foldReconstruct` IS `absFold` at the SSZ pair-hash. -/
theorem foldReconstruct_eq_absFold (leaf : List Nat) (branch : List (List Nat)) (idx : Nat) :
    foldReconstruct leaf branch idx = absFold pairHash leaf branch idx := by
  induction branch generalizing leaf idx with
  | nil => rfl
  | cons sib rest ih =>
    simp only [foldReconstruct, absFold]; exact ih _ _

/-! ## §2 — The SHA leaf: `Digest = List Nat`, `hashPair = pairHash` (the two-block SSZ SHA-256).

A lawful `EthLeaf` whose pair-hash is the FIPS-anchored `Sha256MerkleFold.pairHash`. The BLS fields
are inert (never accept — sound and unused here); the hash carriers are the GENUINE SHA/encoding
Props over its own primitives — the production floor. This makes the AIR fold's reconstruction
CONCRETELY the bridge's `reconstruct`. -/
@[reducible] def shaWordLeaf : EthLeaf where
  PubKey := Nat
  Sig := Nat
  Digest := List Nat
  deq := inferInstance
  blsAggVerify := fun _ _ _ => false
  SignedAll := fun _ _ => True
  blsSound := fun _ _ _ _ => trivial
  hashPair := pairHash
  hashPairCR := ∀ a b c d : List Nat, pairHash a b = pairHash c d → a = c ∧ b = d
  noPairCollision := fun h => h
  uChunk := fun n => [n]
  uChunkInj := ∀ a b : Nat, ([a] : List Nat) = [b] → a = b
  noChunkCollision := fun h => h
  zeroChunk := List.replicate 8 0
  zeroSig := 0

/-- **The AIR fold recomputes EXACTLY the bridge's `reconstruct`.** For the SHA leaf, the generator's
`foldReconstruct` (which the emitted `merkleBranchFold` gates compute, via `sha256PairHash`) equals
the object `FIN_OK` stood for. -/
theorem reconstruct_shaWordLeaf_eq_foldReconstruct
    (leaf : List Nat) (branch : List (List Nat)) (idx : Nat) :
    reconstruct shaWordLeaf leaf branch idx = foldReconstruct leaf branch idx := by
  rw [reconstruct_eq_absFold, foldReconstruct_eq_absFold]

/-! ## §3 — `FIN_OK` DERIVED: the finality gate is discharged by the exhibited branch fold. -/

/-- **The finality-binding content, DERIVED from the branch fold.** The explicit chain the emitted
constraints realize: the fold gates force the reconstructed root `= foldReconstruct leaf branch`
(RESIDUAL #1, an explicit hypothesis here), and `bindRootWords` forces that root `= attested`;
therefore the branch reconstructs the leaf into the attested root — the `FIN_OK` content, obtained
from the branch, not a trusted bit. -/
theorem finFold_derives_finalityCommits
    (leafDigest : List Nat) (branch : List (List Nat)) (rootDigest attested : List Nat)
    (hforce : rootDigest = foldReconstruct leafDigest branch finalizedRootSubtreeIndex)
    (hbind : rootDigest = attested) :
    foldReconstruct leafDigest branch finalizedRootSubtreeIndex = attested := by
  rw [← hforce, hbind]

/-- **The finality gate's boolean is DISCHARGED by the (derived) branch fold — no `FIN_OK` bit read.**
Given a legal depth and the fold-derived reconstruction equality, the bridge's `verifyFinalityBranch`
verdict is `true`. A satisfying prover must EXHIBIT a branch whose SHA fold hits the attested state
root; there is no witnessed carrier to set. -/
theorem verifyFinalityBranch_from_fold (finalizedBeacon : BeaconBlockHeader shaWordLeaf)
    (branch : List (List Nat)) (attested : List Nat)
    (hdepth : branch.length = finalizedRootDepth ∨ branch.length = finalizedRootDepthElectra)
    (hfold : foldReconstruct (htrHeader shaWordLeaf finalizedBeacon) branch
              finalizedRootSubtreeIndex = attested) :
    verifyFinalityBranch shaWordLeaf finalizedBeacon branch attested = true := by
  unfold verifyFinalityBranch
  rw [reconstruct_shaWordLeaf_eq_foldReconstruct, hfold]
  have hbeq : shaWordLeaf.beq attested attested = true := (shaWordLeaf.beq_iff).mpr rfl
  rw [hbeq, Bool.and_true]
  rcases hdepth with h | h <;> rw [h] <;> decide

/-- **The fold-derived finality slots into `eth_no_forgery` in place of the trusted `FIN_OK` bit.**
GIVEN the SHA carriers (`hcr`/`hinj` — the named floor, exactly as the carrier version) and the sync
and execution legs, if the finality branch fold reconstructs the finalized header into the attested
state root (`hfold` — DERIVED from the exhibited branch, not a witnessed bit), the update is
Ethereum-VALID. The `FIN_OK` carrier is folded out: its content is now the conclusion of the branch
fold. -/
theorem eth_finality_from_fold_slots_into_no_forgery
    (hcr : shaWordLeaf.hashPairCR) (hinj : shaWordLeaf.uChunkInj)
    (ts : EthState shaWordLeaf) (u : LightClientUpdate shaWordLeaf)
    (hsync : verifySyncAggregate shaWordLeaf ts u.attestedHeader u.syncAggregate = true)
    (hexec : verifyExecutionPayload shaWordLeaf u.finalizedHeader.execution
              u.finalizedHeader.executionBranch u.finalizedHeader.beacon.bodyRoot = true)
    (hdepth : u.finalityBranch.length = finalizedRootDepth
              ∨ u.finalityBranch.length = finalizedRootDepthElectra)
    (hfold : foldReconstruct (htrHeader shaWordLeaf u.finalizedHeader.beacon) u.finalityBranch
              finalizedRootSubtreeIndex = u.attestedHeader.stateRoot) :
    EthValidAt shaWordLeaf ts u := by
  refine eth_no_forgery shaWordLeaf hcr hinj ts u ?_
  unfold verifyFinalizedUpdate
  rw [hsync, verifyFinalityBranch_from_fold u.finalizedHeader.beacon u.finalityBranch
    u.attestedHeader.stateRoot hdepth hfold, hexec]
  decide

/-! ## §4 — axiom hygiene. -/

#assert_axioms reconstruct_eq_absFold
#assert_axioms foldReconstruct_eq_absFold
#assert_axioms reconstruct_shaWordLeaf_eq_foldReconstruct
#assert_axioms finFold_derives_finalityCommits
#assert_axioms verifyFinalityBranch_from_fold
#assert_axioms eth_finality_from_fold_slots_into_no_forgery

#print axioms eth_finality_from_fold_slots_into_no_forgery

end Dregg2.Circuit.Emit.LightClientEthFinFold
