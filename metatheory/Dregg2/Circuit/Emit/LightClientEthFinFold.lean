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
  * `eth_finality_from_fold_gate_accepts` — the fold-derived finality discharges the COMPOSED gate,
    with NO crypto carrier at all. Trust moves from "an opaque prover-set bit" to "the SHA gadget's
    gates over an exhibited branch" — the latter is atomic-KAT'd (`Sha256Gadget`/`Sha256MerkleFold`
    §0/§2) and provable in principle (residual #1), not an opaque node computation.
  * `eth_finality_fold_binds_header` — the NON-EQUIVOCATION payoff, on the HONEST floor
    (`Sha256MerkleFold.pairSepOn`).

## ⚑ 2026-07-27 — WHAT WAS DELETED AND WHY (the vacuity repair)

`eth_finality_from_fold_slots_into_no_forgery` is GONE. It concluded `EthValidAt shaWordLeaf ts u`
from `hcr : shaWordLeaf.hashPairCR`, and BOTH of its crypto premises were unsatisfiable:

  * `hashPairCR` was idealized injectivity of the real compressing `pairHash` — REFUTED by an
    executable collision (`Sha256MerkleFold.pairHashInjective_false`); and
  * `hsync` could never hold, because the leaf's `blsAggVerify` was `fun _ _ _ => false`.

So it proved nothing. Its honest content is now two theorems that rest on nothing false:
`eth_finality_from_fold_gate_accepts` (carrier-free gate acceptance) and `eth_fold_quorumSigned`
(the signature denotation), plus `eth_finality_fold_binds_header` for the binding.

**CAPABILITY LOST, NAMED:** the ∀-quantified `EthValidAt.finalityBinds` conjunct — "NO OTHER
finalized header opens this attested state root", over the infinite space of alternatives — is not
derivable at a compressing hash, by ANY premise, because `EthLeaf.noPairCollision` demands global
injectivity and that is false. What replaces it is the PAIRWISE form (`eth_finality_fold_binds_header`):
two EXHIBITED openings cannot both stand unless separation fails on the pairs they hash. That is
also the form a query-counted collision bound can price, so it is where the ladder continues.

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
instance over the REAL SSZ pair hash (`Digest = List Nat`, `hashPair = pairHash`). Its `uChunkInj`
is PROVED (`shaWordLeaf_uChunkInj`); its `hashPairCR` is `False`, because the interface's unpacker
demands global injectivity of a compressing hash (`shaWordLeaf_no_CR_carrier`). `NonVacuous` is
DISCHARGED on concrete data over the real SHA-256 (`shaWordLeaf_non_vacuous`). Imports read-only
(`Sha256MerkleFold`, `Bridge.LightClientEth`).
-/
import Dregg2.Circuit.Emit.Sha256MerkleFold
import Dregg2.Bridge.LightClientEth

namespace Dregg2.Circuit.Emit.LightClientEthFinFold

open Dregg2.Circuit.Emit.Sha256MerkleFold
open Dregg2.Bridge.LightClientEth
open Dregg2.Bridge.VerifiedLightClient

set_option autoImplicit false
set_option maxRecDepth 8192

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

A lawful `EthLeaf` whose pair-hash is the FIPS-anchored `Sha256MerkleFold.pairHash`. This makes the
AIR fold's reconstruction CONCRETELY the bridge's `reconstruct`.

⚑ TWO THINGS CHANGED HERE ON 2026-07-27, both of them vacuities measured by the crypto-gadget audit
(`docs/AUDIT-CRYPTO-GADGETS.md` F1/F2):

  * **The BLS slot no longer refuses everything.** It used to be `blsAggVerify := fun _ _ _ => false`
    with `SignedAll := fun _ _ => True`, doc'd "inert … sound and unused here". It was NOT unused:
    `verifySyncAggregate` ends with `L.blsAggVerify …`, so `hsync = true` reduced to `false = true`
    and EVERY theorem taking it was vacuous on that hypothesis alone, independently of the hash.
    It is now the same registered-key demo shape the Tendermint/Solana leaves use — an aggregate
    that CAN verify, with a `SignedAll` denotation that DISCRIMINATES (a non-`7` key is not
    all-signed). `shaWordLeaf_non_vacuous` (§2b) discharges the foundation's `NonVacuous`
    obligation, which `LightClientEth` §9 declares an INSTANCE obligation and which this leaf had
    simply never paid.

  * **The CR slot is `False`, and that is a THEOREM about the interface, not a shrug.**
    `EthLeaf.noPairCollision` demands the carrier ENTAIL GLOBAL injectivity of `hashPair`
    (`hashPairCR → ∀ a b c d, hashPair a b = hashPair c d → a = c ∧ b = d`). At the real
    compressing `pairHash` that consequent is REFUTED with an executable witness
    (`Sha256MerkleFold.pairHashInjective_false`), so ANY `Prop` in this slot is false and any
    theorem taking it proves nothing. It previously held exactly that refuted injectivity `Prop`,
    dressed as "the GENUINE named SHA assumption". Writing `False` says out loud what the slot can
    hold at a real hash, and makes it impossible to route a proof through it by accident.
    The binding content this leaf really carries now rides the HONEST floor —
    `Sha256MerkleFold.pairSepOn`, satisfiable / refutable / not provable — in §4 below.

  * `uChunkInj` is NOT in that situation: `uChunk n = [n]` is genuinely injective, and
    `shaWordLeaf_uChunkInj` PROVES it. A provable fact is strictly better than a floor; it is
    stated as a theorem rather than assumed. -/
@[reducible] def shaWordLeaf : EthLeaf where
  PubKey := Nat
  Sig := List Nat
  Digest := List Nat
  deq := inferInstance
  blsAggVerify := fun pks m s => pks.all (fun k => decide (k = 7)) && decide (s = m)
  SignedAll := fun pks _ => ∀ pk ∈ pks, pk = 7
  blsSound := fun _ _ _ h pk hpk => by
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1 pk hpk
  hashPair := pairHash
  hashPairCR := False
  noPairCollision := fun h => h.elim
  uChunk := fun n => [n]
  uChunkInj := ∀ a b : Nat, ([a] : List Nat) = [b] → a = b
  noChunkCollision := fun h => h
  zeroChunk := List.replicate 8 0
  zeroSig := []

/-- The leaf's primitives, as rewrite rules (the projections of a `@[reducible]` instance, named so
proofs can `simp only` them instead of relying on unfolding a structure literal). -/
@[simp] theorem shaWordLeaf_hashPair : shaWordLeaf.hashPair = pairHash := rfl
@[simp] theorem shaWordLeaf_uChunk : shaWordLeaf.uChunk = fun n => [n] := rfl
@[simp] theorem shaWordLeaf_zeroChunk : shaWordLeaf.zeroChunk = List.replicate 8 0 := rfl

/-- **The chunk-encoding carrier is PROVED, not assumed** — `uChunk n = [n]` is injective. -/
theorem shaWordLeaf_uChunkInj : shaWordLeaf.uChunkInj := fun _ _ h => by
  simpa using h

/-- **The CR slot is uninhabitable at this leaf — with the refutation on the record.** Anything
in `hashPairCR` would, through `noPairCollision`, yield `pairHashInjective`, which is FALSE by an
executable collision. `hashPairCR := False` is therefore the only honest content, and this theorem
is the reason. -/
theorem shaWordLeaf_no_CR_carrier :
    ¬ (∀ a b c d : List Nat, shaWordLeaf.hashPair a b = shaWordLeaf.hashPair c d → a = c ∧ b = d) :=
  pairHashInjective_false

/-! ## §2b — NON-VACUITY: the gate ACCEPTS a genuine update over the REAL SHA-256.

The foundation makes `NonVacuous` an INSTANCE obligation precisely because a degenerate leaf
(`blsAggVerify ≡ false`) is perfectly SOUND and never accepts (`Bridge/LightClientEth.lean` §9).
This leaf never paid it. It does now, on concrete data: a 512-key committee, a self-consistent
depth-6 finality branch and depth-4 execution branch over the FIPS-anchored `pairHash`, and an
aggregate that verifies against the real signing root. -/

/-- Full participation selects the whole committee (the bit filter only selects). -/
theorem participants_replicate {α : Type} (n : Nat) (x : α) :
    participants (List.replicate n x) (List.replicate n true) = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, participants, ih]

/-- A constant list all satisfies a predicate its element satisfies. -/
theorem all_replicate_eq {α : Type} (n : Nat) (x : α) (p : α → Bool) (h : p x = true) :
    (List.replicate n x).all p = true := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, h, ih]

/-- The genuine trusted state: 512 copies of the registered key `7` (the REAL
`SYNC_COMMITTEE_SIZE`) and a config domain. -/
def shaState : EthState shaWordLeaf :=
  ⟨List.replicate syncCommitteeSize 7, List.replicate 8 9⟩

def shaExec : ExecutionPayloadHeader shaWordLeaf where
  parentHash := List.replicate 8 11
  feeRecipient := List.replicate 8 12
  stateRoot := List.replicate 8 13
  receiptsRoot := List.replicate 8 14
  logsBloomRoot := List.replicate 8 15
  prevRandao := List.replicate 8 16
  blockNumber := 999
  gasLimit := 30000000
  gasUsed := 21000
  timestamp := 1720000000
  extraDataRoot := List.replicate 8 17
  baseFeePerGas := List.replicate 8 18
  blockHash := List.replicate 8 19
  transactionsRoot := List.replicate 8 20
  withdrawalsRoot := List.replicate 8 21
  blobGasUsed := 0
  excessBlobGas := 0

def shaExecBranch : List (List Nat) := List.replicate 4 (List.replicate 8 0)

/-- The finalized `body_root` COMMITS the execution payload (the constructive inverse of the
depth-4 branch at subtree index 9 — real SHA-256, not a free constructor). -/
def shaBodyRoot : List Nat :=
  reconstruct shaWordLeaf (htrExec shaWordLeaf shaExec) shaExecBranch executionPayloadSubtreeIndex

def shaFinalized : BeaconBlockHeader shaWordLeaf :=
  ⟨6400, 42, List.replicate 8 1, List.replicate 8 2, shaBodyRoot⟩

def shaFinalityBranch : List (List Nat) := List.replicate 6 (List.replicate 8 3)

/-- The attested header: its `state_root` COMMITS the finalized header at subtree index 41. -/
def shaAttested : BeaconBlockHeader shaWordLeaf :=
  ⟨6464, 77, List.replicate 8 4,
    reconstruct shaWordLeaf (htrHeader shaWordLeaf shaFinalized) shaFinalityBranch
      finalizedRootSubtreeIndex,
    List.replicate 8 5⟩

/-- The GENUINE update: full participation, an aggregate over the real signing root, and
self-consistent finality + execution branches. -/
def shaGoodUpdate : LightClientUpdate shaWordLeaf :=
  ⟨shaAttested, ⟨shaFinalized, shaExec, shaExecBranch⟩, shaFinalityBranch,
    ⟨List.replicate syncCommitteeSize true, signingRoot shaWordLeaf shaState shaAttested⟩⟩

/-- **THE GATE ACCEPTS** — over the real two-block SSZ SHA-256, the whole composed rule is `true`
on the genuine update. (Every branch equality is `beq x x`, so no digest has to be predicted; the
SHA arithmetic is still the thing being compared.) -/
theorem shaWordLeaf_gate_accepts :
    verifyFinalizedUpdate shaWordLeaf shaState shaGoodUpdate = true := by
  have hpart : participants shaState.committee shaGoodUpdate.syncAggregate.bits
      = List.replicate syncCommitteeSize (7 : Nat) := participants_replicate _ _
  have hall : (List.replicate syncCommitteeSize (7 : Nat)).all (fun k => decide (k = 7)) = true :=
    all_replicate_eq _ _ _ (by decide)
  have hsync : verifySyncAggregate shaWordLeaf shaState shaGoodUpdate.attestedHeader
      shaGoodUpdate.syncAggregate = true := by
    unfold verifySyncAggregate
    rw [hpart]
    simp only [shaState, shaGoodUpdate, List.length_replicate, hall, Bool.and_eq_true,
      decide_eq_true_eq, Bool.true_and, and_true, true_and]
    exact ⟨by decide, by decide⟩
  have hfin : verifyFinalityBranch shaWordLeaf shaGoodUpdate.finalizedHeader.beacon
      shaGoodUpdate.finalityBranch shaGoodUpdate.attestedHeader.stateRoot = true := by
    unfold verifyFinalityBranch
    have hb : shaWordLeaf.beq
        (reconstruct shaWordLeaf (htrHeader shaWordLeaf shaGoodUpdate.finalizedHeader.beacon)
          shaGoodUpdate.finalityBranch finalizedRootSubtreeIndex)
        shaGoodUpdate.attestedHeader.stateRoot = true := by
      apply (shaWordLeaf.beq_iff).mpr; rfl
    rw [hb]
    decide
  have hexec : verifyExecutionPayload shaWordLeaf shaGoodUpdate.finalizedHeader.execution
      shaGoodUpdate.finalizedHeader.executionBranch
      shaGoodUpdate.finalizedHeader.beacon.bodyRoot = true := by
    unfold verifyExecutionPayload
    have hb : shaWordLeaf.beq
        (reconstruct shaWordLeaf (htrExec shaWordLeaf shaGoodUpdate.finalizedHeader.execution)
          shaGoodUpdate.finalizedHeader.executionBranch executionPayloadSubtreeIndex)
        shaGoodUpdate.finalizedHeader.beacon.bodyRoot = true := by
      apply (shaWordLeaf.beq_iff).mpr; rfl
    rw [hb]
    decide
  unfold verifyFinalizedUpdate
  rw [hsync, hfin, hexec]
  rfl

/-- **`NonVacuous` DISCHARGED** — the obligation the foundation deliberately made explicit, and
that this leaf had never paid. The gate accepts the genuine update and refuses the empty one. -/
theorem shaWordLeaf_non_vacuous : NonVacuous (verifyFinalizedUpdate shaWordLeaf) :=
  ⟨shaState, shaGoodUpdate, emptyUpdate shaWordLeaf, shaWordLeaf_gate_accepts,
    eth_fail_closed shaWordLeaf shaState⟩

/-- **The BLS denotation DISCRIMINATES** (it used to be `True`, which denotes nothing): a committee
of untrusted key-`3`s cannot produce a verifying aggregate for the genuine update. -/
theorem shaWordLeaf_forged_committee_rejected :
    verifySyncAggregate shaWordLeaf ⟨List.replicate syncCommitteeSize 3, List.replicate 8 9⟩
      shaGoodUpdate.attestedHeader shaGoodUpdate.syncAggregate = false := by
  unfold verifySyncAggregate
  have hpart : participants (List.replicate syncCommitteeSize (3 : Nat))
      shaGoodUpdate.syncAggregate.bits = List.replicate syncCommitteeSize 3 := by
    simpa [shaGoodUpdate] using participants_replicate (α := Nat) syncCommitteeSize 3
  rw [hpart]
  have hall : (List.replicate syncCommitteeSize (3 : Nat)).all (fun k => decide (k = 7)) = false := by
    simp [syncCommitteeSize]
  simp only [hall, Bool.false_and, Bool.and_false]

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

/-- **THE FOLD-DERIVED FINALITY DISCHARGES THE WHOLE GATE — carrier-free.** Given the sync and
execution legs and a legal depth, a branch whose SHA fold reaches the attested state root makes the
composed rule accept: no `FIN_OK` bit is read and NO hash floor is used. This half of the old
`eth_finality_from_fold_slots_into_no_forgery` was always honest; it is now stated on its own so
that it does not travel inside a theorem whose other half rested on a refuted premise. -/
theorem eth_finality_from_fold_gate_accepts
    (ts : EthState shaWordLeaf) (u : LightClientUpdate shaWordLeaf)
    (hsync : verifySyncAggregate shaWordLeaf ts u.attestedHeader u.syncAggregate = true)
    (hexec : verifyExecutionPayload shaWordLeaf u.finalizedHeader.execution
              u.finalizedHeader.executionBranch u.finalizedHeader.beacon.bodyRoot = true)
    (hdepth : u.finalityBranch.length = finalizedRootDepth
              ∨ u.finalityBranch.length = finalizedRootDepthElectra)
    (hfold : foldReconstruct (htrHeader shaWordLeaf u.finalizedHeader.beacon) u.finalityBranch
              finalizedRootSubtreeIndex = u.attestedHeader.stateRoot) :
    verifyFinalizedUpdate shaWordLeaf ts u = true := by
  unfold verifyFinalizedUpdate
  rw [hsync, verifyFinalityBranch_from_fold u.finalizedHeader.beacon u.finalityBranch
    u.attestedHeader.stateRoot hdepth hfold, hexec]
  rfl

/-- Project the left conjunct of a satisfied Boolean `&&` (used instead of `simp`, which sees
through the reducible leaf and normalises `blsAggVerify` into its own `&&`). -/
theorem band_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

/-- Project the right conjunct of a satisfied Boolean `&&`. -/
theorem band_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> simp_all

/-- **THE SIGNATURE LEG, still DERIVED and now non-trivial.** Gate acceptance entails that a subset
of the TRUSTED committee meeting the multiply-form 2/3 threshold GENUINELY signed the attested
header's signing root — `EthValidAt.quorumSigned`, the conjunct that needs no hash floor at all.
Kept as a first-class theorem so that removing the refuted CR premise does not silently drop the
part of `eth_no_forgery` this leaf can actually deliver. The proof CONSUMES `blsSound`, whose
`SignedAll` denotation is now discriminating rather than `True`. -/
theorem eth_fold_quorumSigned (ts : EthState shaWordLeaf) (u : LightClientUpdate shaWordLeaf)
    (hacc : verifyFinalizedUpdate shaWordLeaf ts u = true) :
    ∃ ps : List Nat,
      (∀ pk ∈ ps, pk ∈ ts.committee)
      ∧ 2 * syncCommitteeSize ≤ 3 * ps.length
      ∧ shaWordLeaf.SignedAll ps (signingRoot shaWordLeaf ts u.attestedHeader) := by
  unfold verifyFinalizedUpdate at hacc
  have hsync : verifySyncAggregate shaWordLeaf ts u.attestedHeader u.syncAggregate = true :=
    band_left (band_left hacc)
  unfold verifySyncAggregate at hsync
  have hq : decide (2 * syncCommitteeSize
      ≤ 3 * (participants ts.committee u.syncAggregate.bits).length) = true :=
    band_right (band_left hsync)
  have hbls : shaWordLeaf.blsAggVerify (participants ts.committee u.syncAggregate.bits)
      (signingRoot shaWordLeaf ts u.attestedHeader) u.syncAggregate.sig = true :=
    band_right hsync
  exact ⟨participants ts.committee u.syncAggregate.bits, fun _ hpk => mem_participants hpk,
    of_decide_eq_true hq, shaWordLeaf.blsSound _ _ _ hbls⟩

/-! ## §4 — NON-EQUIVOCATION at the HONEST floor (the repair of the vacuous payoff).

The old `eth_finality_from_fold_slots_into_no_forgery` concluded `EthValidAt shaWordLeaf ts u` from
`hcr : shaWordLeaf.hashPairCR`. `EthValidAt.finalityBinds` is a ∀ over ALL alternative headers and
branches, so deriving it needs GLOBAL injectivity of `pairHash` — refuted. That conclusion is
therefore not available at a real hash, and no restatement of the premise recovers it: the
capability genuinely lost is the ∀-quantified "NO other finalized header opens this root", over the
infinite space of alternatives.

What IS available, and is what a collision bound actually prices, is the PAIRWISE form: two
EXHIBITED openings cannot both stand unless the adversary broke separation on the pairs those two
openings hash. That is the shape below, on `Sha256MerkleFold.pairSepOn` — satisfiable
(`pairSepOn_modelSep`), refutable (`pairSepOn_truncSep_false`), not provable. -/

/-- **`htrHeaderCovered P h`** — `P` holds of every pair the 5-field-into-8-chunk header
merkleization feeds to `pairHash`. The six pairs `htrHeader_inj_on` peels, and no more. -/
def htrHeaderCovered (P : List Nat → List Nat → Prop) (h : BeaconBlockHeader shaWordLeaf) : Prop :=
  P [h.slot] [h.proposerIndex]
  ∧ P h.parentRoot h.stateRoot
  ∧ P h.bodyRoot (List.replicate 8 0)
  ∧ P (pairHash [h.slot] [h.proposerIndex]) (pairHash h.parentRoot h.stateRoot)
  ∧ P (pairHash h.bodyRoot (List.replicate 8 0))
      (pairHash (List.replicate 8 0) (List.replicate 8 0))
  ∧ P (pairHash (pairHash [h.slot] [h.proposerIndex]) (pairHash h.parentRoot h.stateRoot))
      (pairHash (pairHash h.bodyRoot (List.replicate 8 0))
        (pairHash (List.replicate 8 0) (List.replicate 8 0)))

/-- **HEADER ROOTS PIN HEADERS, at the HONEST floor.** `htrHeader_inj`'s conclusion — including
`slot` and `proposer_index` through the (PROVED, not assumed) chunk encoding — from separation on
the two headers' OWN merkleization pairs instead of injectivity of `pairHash`. -/
theorem htrHeader_inj_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (h₁ h₂ : BeaconBlockHeader shaWordLeaf)
    (hc₁ : htrHeaderCovered P h₁) (hc₂ : htrHeaderCovered P h₂)
    (h : htrHeader shaWordLeaf h₁ = htrHeader shaWordLeaf h₂) : h₁ = h₂ := by
  unfold htrHeader merk8 merk4 at h
  simp only [shaWordLeaf_hashPair, shaWordLeaf_uChunk, shaWordLeaf_zeroChunk] at h
  obtain ⟨q0₁, q1₁, q2₁, q3₁, q4₁, q5₁⟩ := hc₁
  obtain ⟨q0₂, q1₂, q2₂, q3₂, q4₂, q5₂⟩ := hc₂
  obtain ⟨hl, hr⟩ := hsep _ _ _ _ q5₁ q5₂ h
  obtain ⟨hll, hlr⟩ := hsep _ _ _ _ q3₁ q3₂ hl
  obtain ⟨hslot, hpi⟩ := hsep _ _ _ _ q0₁ q0₂ hll
  obtain ⟨hparent, hstate⟩ := hsep _ _ _ _ q1₁ q1₂ hlr
  obtain ⟨hrl, _⟩ := hsep _ _ _ _ q4₁ q4₂ hr
  obtain ⟨hbody, _⟩ := hsep _ _ _ _ q2₁ q2₂ hrl
  cases h₁; cases h₂
  simp only [BeaconBlockHeader.mk.injEq]
  exact ⟨by simpa using hslot, by simpa using hpi, hparent, hstate, hbody⟩

/-- **THE REPAIRED PAYOFF — NON-EQUIVOCATION OF THE FINALIZED HEADER.** Two finality branches of the
same depth whose SHA folds both reach the SAME attested state root carry the SAME finalized header,
GIVEN that `pairHash` separates on the class the two folds' and two headers' own pairs live in. This
is the crypto content the `FIN_OK` carrier was supposed to buy — a forger cannot open one attested
state root to two different finalized headers — now resting on a hypothesis a model satisfies
instead of on `∀ a b c d, pairHash a b = pairHash c d → …`, which is FALSE. -/
theorem eth_finality_fold_binds_header (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (f₁ f₂ : BeaconBlockHeader shaWordLeaf) (b₁ b₂ : List (List Nat)) (attested : List Nat)
    (hlen : b₁.length = b₂.length)
    (hcf₁ : FoldCovered P (htrHeader shaWordLeaf f₁) b₁ finalizedRootSubtreeIndex)
    (hcf₂ : FoldCovered P (htrHeader shaWordLeaf f₂) b₂ finalizedRootSubtreeIndex)
    (hh₁ : htrHeaderCovered P f₁) (hh₂ : htrHeaderCovered P f₂)
    (hfold₁ : foldReconstruct (htrHeader shaWordLeaf f₁) b₁ finalizedRootSubtreeIndex = attested)
    (hfold₂ : foldReconstruct (htrHeader shaWordLeaf f₂) b₂ finalizedRootSubtreeIndex = attested) :
    f₁ = f₂ :=
  htrHeader_inj_on P hsep f₁ f₂ hh₁ hh₂
    (foldReconstruct_binding_on P hsep b₁ b₂ finalizedRootSubtreeIndex _ _ hlen hcf₁ hcf₂
      (hfold₁.trans hfold₂.symm))

/-! ## §5 — axiom hygiene. -/

#assert_axioms reconstruct_eq_absFold
#assert_axioms foldReconstruct_eq_absFold
#assert_axioms reconstruct_shaWordLeaf_eq_foldReconstruct
#assert_axioms finFold_derives_finalityCommits
#assert_axioms verifyFinalityBranch_from_fold
#assert_axioms shaWordLeaf_uChunkInj
#assert_axioms shaWordLeaf_no_CR_carrier
#assert_axioms participants_replicate
#assert_axioms all_replicate_eq
#assert_axioms shaWordLeaf_gate_accepts
#assert_axioms shaWordLeaf_non_vacuous
#assert_axioms shaWordLeaf_forged_committee_rejected
#assert_axioms eth_finality_from_fold_gate_accepts
#assert_axioms eth_fold_quorumSigned
#assert_axioms htrHeader_inj_on
#assert_axioms eth_finality_fold_binds_header

#print axioms eth_finality_fold_binds_header
#print axioms shaWordLeaf_non_vacuous

end Dregg2.Circuit.Emit.LightClientEthFinFold
