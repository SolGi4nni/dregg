/-
# Dregg2.Circuit.Emit.LightClientEthExecFold — wiring the SHA-256 fold into ETH EXECUTION:
`EXEC_OK` becomes DERIVED, not a trusted witnessed boolean carrier — and it is the carrier that
binds the ROOT the on-chain `DreggPeerRegistry` actually records.

## The carrier being folded out (the SECOND fold — the on-chain-relevant one)

`LightClientEthAir.EXEC_OK` is a witnessed boolean column standing for
`beq (reconstruct L (htrExec L finalizedExecution) executionBranch executionPayloadSubtreeIndex)
finalizedBodyRoot` — the depth-4 execution-payload Merkle-branch fold of
`Dregg2.Bridge.LightClientEth.reconstruct` at subtree index 9 (`EXECUTION_PAYLOAD_GINDEX = 25`). In
the carrier slice the AIR forces `EXEC_OK = 1` and `ethLcAir_no_forgery` takes the HONEST-WITNESS
relation `hexec : a EXEC_OK = if beq(reconstruct …) then 1 else 0` as a hypothesis — it TRUSTS the
prover set the bit to the true SHA result. The verifier re-runs no hash; it believes a bit.

This file replaces that trust with the branch itself, MIRRORING `LightClientEthFinFold` exactly and
REUSING its machinery (`Sha256MerkleFold.merkleBranchFold` / `sha256PairHash`, and `absFold` /
`shaWordLeaf` / `reconstruct_shaWordLeaf_eq_foldReconstruct` from the finality fold). The ties proved
here:

  * `reconstruct_exec_eq_foldReconstruct` — for the SHA leaf, the bridge's `reconstruct` at the
    execution-payload commitment `htrExec` IS the generator's `foldReconstruct`. So the AIR fold
    recomputes EXACTLY the object `EXEC_OK` stood for — via the SHA arithmetic, not a bit.
  * `verifyExecutionPayload_from_fold` — the execution gate's boolean is DISCHARGED by the (derived)
    depth-4 branch fold: no `EXEC_OK` column is read. A satisfying prover must EXHIBIT a branch whose
    SHA fold hits the finalized body root.
  * `eth_exec_from_fold_gate_accepts` (carrier-free) + `exec_fold_binds_finStateRoot_on` (the HONEST
    floor) — the fold-derived execution slots into
    the composed gate IN PLACE of the trusted bit, and the binding rides a floor a model satisfies.

## The on-chain root: how EXEC_OK binds FIN_STATE_ROOT (the honest chain — read this)

`FIN_STATE_ROOT` (PI[1..9], the full 256-bit EVM `state_root` the on-chain `DreggPeerRegistry`
records — `eth-lightclient`'s `FinalizedExecution.execution_state_root`, and the `modelIncl` event of
`LightClientEth` §11) is `finalizedExecution.stateRoot`. GET THE SHAPE RIGHT (correcting the FIN_OK
lane's fidelity flag, which noted FIN_OK bound the BEACON `attestedStateRoot`, a root that is NOT
FIN_STATE_ROOT at all):

  * The execution branch fold's TARGET is the finalized `bodyRoot` (depth 4, index 9) — NOT
    FIN_STATE_ROOT. FIN_STATE_ROOT is not the reconstruction target of any branch.
  * FIN_STATE_ROOT = `execution.stateRoot` is a COMMITTED FIELD of the fold's LEAF `htrExec` (field #3
    of the 17-field SSZ `ExecutionPayloadHeader`). `htrExec_commits_stateRoot` proves the leaf BINDS
    that field (the SSZ merkleization pins it, GIVEN separation on the spine's own pairs).
  * `exec_fold_binds_finStateRoot_on` composes the two: the DERIVED fold binds FIN_STATE_ROOT — no two
    execution headers with DIFFERENT EVM state roots open the same finalized body root through
    same-depth branches. This is why this is the carrier that binds the on-chain-recorded root:
    FIN_OK's finality branch never touches FIN_STATE_ROOT; EXEC_OK's leaf commits it.

So the on-chain binding is LEAF-COMMITMENT (`htrExec` pins `stateRoot`) ∘ BRANCH-BINDING (the fold's
reconstruct pins the leaf under `bodyRoot`), NOT "the fold reconstructs into FIN_STATE_ROOT" (which
would be the wrong SSZ shape). `bindRootWords` in the generator binds the fold OUTPUT to the body
root word-for-word; FIN_STATE_ROOT rides the leaf, and its 256-bit ↔ nine-radix-`2^31`-limb repack to
PI[1..9] is the SAME field-soundness residual `LightClientEthAir` §6 / `Sha256MerkleFold` #3 carries.

## What remains (the honest, PRICED residuals — same three as the FIN_OK fold, proof-mode step 1)

  * RESIDUAL #1 (proof-composition wall): the hypothesis `hfold : foldReconstruct … = bodyRoot` is,
    in the deployed circuit, the CONCLUSION of the fold gates forcing their SHA outputs up ~30k
    gates/block × 2 blocks × depth 4. The atomic gates are forced + both-polarity KAT'd
    (`xor3_forces`/`chHead_forces`/`majHead_forces`/`addMod32_forces`); the full composition is the
    next slice. Here `hfold` is an explicit hypothesis, so DERIVED vs ASSUMED is visible.
  * RESIDUAL #2 (deploy/emit wall): a depth-4 two-block-SHA fold is ~3.3·10^5 flat gates, so it
    cannot be merged into `ethLcVerifyDesc`'s byte-golden `#guard emitVmJson2`, and the `EXEC_OK`
    column cannot be flat-removed from the DEPLOYED descriptor in this slice. The deployed removal
    routes through the IR-v2 `proofBind` recursion seam. `ethLcVerifyDesc` and its JSON golden are
    UNTOUCHED here — NO VK regen.
  * RESIDUAL #3 (felt-width): the fold binds word-for-word to the body root; the 256-bit ↔
    nine-radix-`2^31`-limb repack of FIN_STATE_ROOT to PI[1..9] is the shared field-soundness residual.

`BLS_OK` remains a hypothesis (the only ETH carrier not yet folded). Two of three ETH carriers folded.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `shaWordLeaf` (from `LightClientEthFinFold`)
is the lawful SHA `EthLeaf` instance over the real SSZ pair hash; its `hashPairCR` slot is `False`
(the interface demands global injectivity of a compressing hash) and its `uChunkInj` is PROVED. The
`#guard` KATs anchor the depth-4 execution reconstruction against an independently-computed SHA-256
vector (`hashlib`), both polarities (a real fold value + a tampered sibling that DIFFERS). NEW file;
imports read-only (`LightClientEthFinFold`, transitively `Sha256MerkleFold` + `Bridge.LightClientEth`).
-/
import Dregg2.Circuit.Emit.LightClientEthFinFold

namespace Dregg2.Circuit.Emit.LightClientEthExecFold

open Dregg2.Circuit.Emit.Sha256MerkleFold
open Dregg2.Circuit.Emit.LightClientEthFinFold
open Dregg2.Bridge.LightClientEth

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §1 — The AIR fold recomputes EXACTLY the bridge's `reconstruct` (the execution leaf).

Reuses `reconstruct_shaWordLeaf_eq_foldReconstruct` (the SHA leaf's `reconstruct` IS `foldReconstruct`,
proved generically in the finality fold) at the execution-payload commitment `htrExec`. The emitted
`merkleBranchFold` gates (via `sha256PairHash`) compute this `foldReconstruct`. -/

/-- **The AIR fold recomputes EXACTLY the bridge's execution `reconstruct`.** For the SHA leaf, the
generator's `foldReconstruct` on the execution-payload commitment equals the object `EXEC_OK` stood
for — via the SHA arithmetic, not a trusted bit. -/
theorem reconstruct_exec_eq_foldReconstruct
    (execution : ExecutionPayloadHeader shaWordLeaf) (branch : List (List Nat)) (idx : Nat) :
    reconstruct shaWordLeaf (htrExec shaWordLeaf execution) branch idx
      = foldReconstruct (htrExec shaWordLeaf execution) branch idx :=
  reconstruct_shaWordLeaf_eq_foldReconstruct (htrExec shaWordLeaf execution) branch idx

/-! ## §2 — The LEAF commits FIN_STATE_ROOT: the execution-payload root pins the EVM `state_root`.

`FIN_STATE_ROOT = execution.stateRoot` is field #3 of the 17-field SSZ `ExecutionPayloadHeader`; the
merkleization `htrExec` COMMITS it. Five `pair_inj` peels down the SSZ tree (`hashPair (merk8 …) …`
→ `merk4` → `hashPair stateRoot receiptsRoot`), GIVEN the SHA-256 CR carrier. This is the sense in
which the execution branch binds the on-chain-recorded root — through the LEAF, not the fold target. -/

/-- **The execution-payload root COMMITS the EVM `state_root` (= FIN_STATE_ROOT), GIVEN the CR
carrier.** Equal `htrExec` roots pin equal `stateRoot` fields. Mirrors `htrHeader_inj`'s peel, but
projects only the on-chain root field. -/
theorem htrExec_commits_stateRoot (L : EthLeaf) (hcr : L.hashPairCR)
    (e₁ e₂ : ExecutionPayloadHeader L)
    (h : htrExec L e₁ = htrExec L e₂) : e₁.stateRoot = e₂.stateRoot := by
  unfold htrExec merk16 merk8 merk4 at h
  obtain ⟨hL, _⟩ := L.pair_inj hcr h        -- left 16-chunk subtree (fields 0..15)
  obtain ⟨hL8, _⟩ := L.pair_inj hcr hL      -- left 8-chunk subtree (fields 0..7)
  obtain ⟨hL4, _⟩ := L.pair_inj hcr hL8     -- left 4-chunk subtree (fields 0..3)
  obtain ⟨_, hR2⟩ := L.pair_inj hcr hL4     -- right pair of that subtree: (stateRoot, receiptsRoot)
  obtain ⟨hstate, _⟩ := L.pair_inj hcr hR2  -- the stateRoot field
  exact hstate

/-! ## §3 — `EXEC_OK` DERIVED: the execution gate is discharged by the exhibited branch fold. -/

/-- **The execution-binding content, DERIVED from the depth-4 branch fold.** The fold gates force the
reconstructed root `= foldReconstruct leaf branch` (RESIDUAL #1, an explicit hypothesis here), and
`bindRootWords` forces that root `= bodyRoot`; therefore the branch reconstructs the leaf into the
finalized body root — the `EXEC_OK` content, obtained from the branch, not a trusted bit. -/
theorem exec_fold_derives_executionCommits
    (leafDigest : List Nat) (branch : List (List Nat)) (rootDigest bodyRoot : List Nat)
    (hforce : rootDigest = foldReconstruct leafDigest branch executionPayloadSubtreeIndex)
    (hbind : rootDigest = bodyRoot) :
    foldReconstruct leafDigest branch executionPayloadSubtreeIndex = bodyRoot := by
  rw [← hforce, hbind]

/-! ## §4 — the execution gate's boolean is DISCHARGED by the (derived) branch fold. -/

/-- **`verifyExecutionPayload` is discharged by the fold — no `EXEC_OK` bit read.** Given the depth-4
admissibility and the fold-derived reconstruction equality into the finalized body root, the bridge's
`verifyExecutionPayload` verdict is `true`. A satisfying prover must EXHIBIT a branch whose SHA fold
hits the body root; there is no witnessed carrier to set. -/
theorem verifyExecutionPayload_from_fold (execution : ExecutionPayloadHeader shaWordLeaf)
    (branch : List (List Nat)) (bodyRoot : List Nat)
    (hdepth : branch.length = executionPayloadDepth)
    (hfold : foldReconstruct (htrExec shaWordLeaf execution) branch executionPayloadSubtreeIndex
              = bodyRoot) :
    verifyExecutionPayload shaWordLeaf execution branch bodyRoot = true := by
  unfold verifyExecutionPayload
  rw [reconstruct_exec_eq_foldReconstruct, hfold]
  have hbeq : shaWordLeaf.beq bodyRoot bodyRoot = true := (shaWordLeaf.beq_iff).mpr rfl
  rw [hbeq, Bool.and_true, hdepth]
  decide

/-! ## §5 — the DERIVED fold BINDS FIN_STATE_ROOT, at the HONEST floor.

⚑ 2026-07-27 — the old `exec_fold_binds_finStateRoot` took `hcr : shaWordLeaf.hashPairCR`, which at
the real compressing `pairHash` is FALSE (`Sha256MerkleFold.pairHashInjective_false`), so the
"on-chain payoff" proved nothing. The conclusion is unchanged here; the premise is replaced by
`Sha256MerkleFold.pairSepOn P` — separation on the FINITE class of pairs these two openings actually
hash — which is satisfiable (`pairSepOn_modelSep`), refutable (`pairSepOn_truncSep_false`) and not
provable. Every `pair_inj` in the old proof is applied at ONE explicit pair, so nothing is lost by
the restriction: the old hypothesis was simply far stronger than the proof used, and false. -/

/-- **`execSpineCovered P e`** — `P` holds of the FIVE pairs the `htrExec` peel walks down the left
spine to the `state_root` field (field #3 of the 17-field SSZ container). Not the whole 31-pair
merkleization: only the pairs the floor is actually applied at. -/
def execSpineCovered (P : List Nat → List Nat → Prop)
    (e : ExecutionPayloadHeader shaWordLeaf) : Prop :=
  P e.stateRoot e.receiptsRoot
  ∧ P (pairHash e.parentHash e.feeRecipient) (pairHash e.stateRoot e.receiptsRoot)
  ∧ P (merk4 shaWordLeaf e.parentHash e.feeRecipient e.stateRoot e.receiptsRoot)
      (merk4 shaWordLeaf e.logsBloomRoot e.prevRandao [e.blockNumber] [e.gasLimit])
  ∧ P (merk8 shaWordLeaf e.parentHash e.feeRecipient e.stateRoot e.receiptsRoot
        e.logsBloomRoot e.prevRandao [e.blockNumber] [e.gasLimit])
      (merk8 shaWordLeaf [e.gasUsed] [e.timestamp] e.extraDataRoot e.baseFeePerGas
        e.blockHash e.transactionsRoot e.withdrawalsRoot [e.blobGasUsed])
  ∧ P (merk16 shaWordLeaf e.parentHash e.feeRecipient e.stateRoot e.receiptsRoot
        e.logsBloomRoot e.prevRandao [e.blockNumber] [e.gasLimit]
        [e.gasUsed] [e.timestamp] e.extraDataRoot e.baseFeePerGas
        e.blockHash e.transactionsRoot e.withdrawalsRoot [e.blobGasUsed])
      (merk16 shaWordLeaf [e.excessBlobGas] (List.replicate 8 0) (List.replicate 8 0)
        (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
        (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
        (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
        (List.replicate 8 0))

/-- **The execution-payload root COMMITS the EVM `state_root` (= FIN_STATE_ROOT), at the HONEST
floor.** `htrExec_commits_stateRoot`'s conclusion with its refuted premise replaced by separation
on the two headers' own left-spine pairs. -/
theorem htrExec_commits_stateRoot_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (e₁ e₂ : ExecutionPayloadHeader shaWordLeaf)
    (hc₁ : execSpineCovered P e₁) (hc₂ : execSpineCovered P e₂)
    (h : htrExec shaWordLeaf e₁ = htrExec shaWordLeaf e₂) : e₁.stateRoot = e₂.stateRoot := by
  obtain ⟨q0₁, q1₁, q2₁, q3₁, q4₁⟩ := hc₁
  obtain ⟨q0₂, q1₂, q2₂, q3₂, q4₂⟩ := hc₂
  simp only [htrExec, merk16, merk8, merk4, shaWordLeaf_hashPair, shaWordLeaf_uChunk,
    shaWordLeaf_zeroChunk] at h q2₁ q3₁ q4₁ q2₂ q3₂ q4₂
  obtain ⟨hL, _⟩ := hsep _ _ _ _ q4₁ q4₂ h
  obtain ⟨hL8, _⟩ := hsep _ _ _ _ q3₁ q3₂ hL
  obtain ⟨hL4, _⟩ := hsep _ _ _ _ q2₁ q2₂ hL8
  obtain ⟨_, hR2⟩ := hsep _ _ _ _ q1₁ q1₂ hL4
  exact (hsep _ _ _ _ q0₁ q0₂ hR2).1

/-- **THE REPAIRED ON-CHAIN PAYOFF — the derived execution fold BINDS FIN_STATE_ROOT.** Two
execution headers whose depth-matched branches both fold to the SAME finalized `bodyRoot` carry the
SAME EVM `state_root`, GIVEN separation on the class those two openings' pairs live in. This is
what the `EXEC_OK` carrier was supposed to buy — a forger cannot open the finalized body root to a
different EVM state root — now resting on a hypothesis a model satisfies. -/
theorem exec_fold_binds_finStateRoot_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (e₁ e₂ : ExecutionPayloadHeader shaWordLeaf) (b₁ b₂ : List (List Nat)) (bodyRoot : List Nat)
    (hlen : b₁.length = b₂.length)
    (hcf₁ : FoldCovered P (htrExec shaWordLeaf e₁) b₁ executionPayloadSubtreeIndex)
    (hcf₂ : FoldCovered P (htrExec shaWordLeaf e₂) b₂ executionPayloadSubtreeIndex)
    (hs₁ : execSpineCovered P e₁) (hs₂ : execSpineCovered P e₂)
    (hf₁ : foldReconstruct (htrExec shaWordLeaf e₁) b₁ executionPayloadSubtreeIndex = bodyRoot)
    (hf₂ : foldReconstruct (htrExec shaWordLeaf e₂) b₂ executionPayloadSubtreeIndex = bodyRoot) :
    e₁.stateRoot = e₂.stateRoot :=
  htrExec_commits_stateRoot_on P hsep e₁ e₂ hs₁ hs₂
    (foldReconstruct_binding_on P hsep b₁ b₂ executionPayloadSubtreeIndex _ _ hlen hcf₁ hcf₂
      (hf₁.trans hf₂.symm))

/-! ## §6 — the fold-derived execution discharges the composed gate, CARRIER-FREE.

⚑ 2026-07-27 — `eth_exec_from_fold_slots_into_no_forgery` is GONE. It concluded
`EthValidAt shaWordLeaf ts u` from `hcr : shaWordLeaf.hashPairCR` (refuted) and `hsync`
(unsatisfiable while the leaf's `blsAggVerify` was `fun _ _ _ => false`), so it proved nothing.
Its honest half is below; the binding half is §5. **CAPABILITY LOST, NAMED:** the ∀-quantified
`EthValidAt.finalityBinds` conjunct is not derivable at a compressing hash by any premise — see
`LightClientEthFinFold`'s header for the full statement of what that costs and what replaces it. -/

/-- **The fold-derived execution DISCHARGES THE COMPOSED GATE — no `EXEC_OK` bit, no crypto
carrier.** Given the sync + finality legs and the depth-4 admissibility, a branch whose SHA fold
reaches the finalized body root makes the whole rule accept. -/
theorem eth_exec_from_fold_gate_accepts
    (ts : EthState shaWordLeaf) (u : LightClientUpdate shaWordLeaf)
    (hsync : verifySyncAggregate shaWordLeaf ts u.attestedHeader u.syncAggregate = true)
    (hfin : verifyFinalityBranch shaWordLeaf u.finalizedHeader.beacon u.finalityBranch
              u.attestedHeader.stateRoot = true)
    (hdepth : u.finalizedHeader.executionBranch.length = executionPayloadDepth)
    (hfold : foldReconstruct (htrExec shaWordLeaf u.finalizedHeader.execution)
              u.finalizedHeader.executionBranch executionPayloadSubtreeIndex
              = u.finalizedHeader.beacon.bodyRoot) :
    verifyFinalizedUpdate shaWordLeaf ts u = true := by
  unfold verifyFinalizedUpdate
  rw [hsync, hfin, verifyExecutionPayload_from_fold u.finalizedHeader.execution
    u.finalizedHeader.executionBranch u.finalizedHeader.beacon.bodyRoot hdepth hfold]
  rfl

/-! ## §7 — KATs: the depth-4 execution reconstruction, anchored to an independent SHA-256 vector.

Both-polarity, at the real `executionPayloadSubtreeIndex = 9`: a genuine depth-4 fold value computed
independently (`hashlib`, matching `Sha256MerkleFold` §0's FIPS anchoring exactly — encoding verified
against the published `SHA256(64·0x00)` / `SHA256(0x00..0x3f)` vectors), and a tampered sibling whose
fold DIFFERS (the execution binding is not vacuous). These reduce in the kernel (Nat SHA reference). -/

-- Positive: the real depth-4 execution-branch fold at subtree index 9.
#guard foldReconstruct [0, 1, 2, 3, 4, 5, 6, 7]
    [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23],
     [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39]]
    executionPayloadSubtreeIndex
  == [0xf3067d97, 0xfcd814e6, 0x7bf75933, 0xf873e406, 0x31da31ee, 0x94a37f87, 0x92b917b9, 0x2a78a1d5]

-- Negative (discrimination): a tampered sibling (24…31 → 24…30,99) changes the reconstructed root.
#guard foldReconstruct [0, 1, 2, 3, 4, 5, 6, 7]
    [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23],
     [24, 25, 26, 27, 28, 29, 30, 99], [32, 33, 34, 35, 36, 37, 38, 39]]
    executionPayloadSubtreeIndex
  != [0xf3067d97, 0xfcd814e6, 0x7bf75933, 0xf873e406, 0x31da31ee, 0x94a37f87, 0x92b917b9, 0x2a78a1d5]

-- Depth/index pins (the execution leg is depth 4 at subtree index 9 = 25 mod 2^4).
#guard executionPayloadDepth == 4
#guard executionPayloadSubtreeIndex == 9

/-! ## §8 — axiom hygiene. -/

#assert_axioms reconstruct_exec_eq_foldReconstruct
#assert_axioms htrExec_commits_stateRoot
#assert_axioms exec_fold_derives_executionCommits
#assert_axioms verifyExecutionPayload_from_fold
#assert_axioms htrExec_commits_stateRoot_on
#assert_axioms exec_fold_binds_finStateRoot_on
#assert_axioms eth_exec_from_fold_gate_accepts

#print axioms eth_exec_from_fold_gate_accepts
#print axioms exec_fold_binds_finStateRoot_on

end Dregg2.Circuit.Emit.LightClientEthExecFold
