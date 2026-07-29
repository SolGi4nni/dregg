/-
# Dregg2.Bridge.LightClientEth — the VERIFIED Ethereum (Altair sync-committee) light client
RULES, over the shared `Dregg2.Bridge.VerifiedLightClient` foundation.

This formalizes the verification RULES of `eth-lightclient/src/{lib,finality,execution}.rs`
— the Rust verifier whose logic is the spec — and proves the three foundation obligations
(`NoForgery` / `FailClosed` / `NonVacuous`) plus the load-bearing teeth the mandate names:
the ≥ 2/3 participation threshold (`participants * 3 ≥ 512 * 2`, no rounding trap: 342
accepted, 341 rejected) and the finality-branch reconstruction (a bad or wrong-depth branch
is REJECTED).

TWO LAYERS, kept distinct + honest:

  * RULES (formalized + proven here):
      - the trusted committee is exactly `SYNC_COMMITTEE_SIZE = 512` pubkeys
        (`lib.rs:283-287`), and the participation bitfield is 512 bits;
      - the participating subset is the bit-selected committee (`lib.rs:290-295`);
      - the ≥ 2/3 safe-update threshold in multiply form `count * 3 ≥ 512 * 2`
        (`lib.rs:301-309` — "the multiply form avoids the rounding trap"), with the
        zero-participants Nomad floor (`lib.rs:298-300`);
      - the BLS aggregate is verified over the SIGNING ROOT
        `hash_pair(hash_tree_root(header), domain)` (`lib.rs:192-201` — the SSZ
        `SigningData` 2-field container), never over raw header bytes;
      - the finality branch reconstructs `hash_tree_root(finalized_header.beacon)` into
        `attested_header.state_root` at subtree index 41 with depth 6 (Altair..Deneb,
        `FINALIZED_ROOT_GINDEX = 105`) OR depth 7 (Electra+, gindex 169) — any other
        depth is fail-closed (`finality.rs:92-124`);
      - the execution branch reconstructs `hash_tree_root(finalized_header.execution)`
        into `finalized_header.beacon.body_root` at subtree index 9, depth 4
        (`EXECUTION_PAYLOAD_GINDEX = 25`, `execution.rs:104-126`) — recovering the EVM
        `state_root` the proof-of-holdings opens against;
      - `is_valid_merkle_branch` per `ssz.rs:130-145` (bit-indexed left/right fold), and
        the SSZ `hash_tree_root` shapes: the 5-field `BeaconBlockHeader` merkleized to 8
        chunks (`lib.rs:114-123`), the 17-field Deneb/Electra `ExecutionPayloadHeader`
        merkleized to 32 chunks (`execution.rs:74-96`, field ORDER load-bearing).

  * CRYPTO (honest, NAMED, MINIMAL leaves — the `EthLeaf` structure fields):
      - `blsSound` : BLS12-381 `fast_aggregate_verify` soundness — a verifying aggregate
        over pubkeys `pks` and message `m` entails every listed key's holder genuinely
        signed `m` (`SignedAll pks m`). This is the ONLY signature assumption; it does
        NOT say "the update is valid". Discharged in production by `blst` (the audited
        library every ETH consensus client uses — `lib.rs:210-260`) / an EverCrypt-style
        verified realization.
      - `hashPairCR` : the SHA-256 collision-resistance CARRIER (a `Prop`, mirroring
        `Dregg2.Crypto.PortalFloor.Blake3Kernel.collisionHard`, `Crypto/PortalFloor.lean:178-185`)
        on the SSZ pair-hash `hash(a ‖ b)` (`ssz.rs:16-26`), unpacked by `noPairCollision`:
        GIVEN the CR floor, equal digests pin equal children — which is what makes a
        reconstructed Merkle branch BINDING (`finalized_header_binding` below). NOT stated
        as unconditional injectivity: that is pigeonhole-UNSATISFIABLE for the real
        compressing `SHA-256 : 64 bytes → 32 bytes` (collisions EXIST; only a toy
        injective hash could discharge it). Injectivity holds RELATIVE to the carrier.
      - `uChunkInj` : the SSZ little-endian `uint64`-chunk-encoding injectivity CARRIER
        (`ssz.rs:54-60`), unpacked by `noChunkCollision` — spec-level (true of the real
        encoding on the `u64` domain), given the SAME carrier treatment so no
        unconditional injectivity law over all of `Nat` is smuggled in; needed so a
        header's root pins its `slot`/`proposer_index` too.
    All three are EXPLICIT VISIBLE STRUCTURE FIELDS supplied at the instance site — never
    a global `axiom`, never a laundered `def FooValid` hidden hypothesis. The `modelLeaf`
    instance below PROVES all three (a perfectly-binding model realization —
    `modelLeaf_hashPairCR` / `modelLeaf_uChunkInj` discharge the carriers standalone), so
    this file is genuinely axiom-clean end-to-end and the leaves demonstrably do not
    trivialize the theorems (`eth_forged_committee_invalid` shows `SignedAll`
    discriminates; `collapseEthLeaf_not_hashPairCR` / `collapseEthLeaf_not_uChunkInj` show
    a collapsing hash/encoding REFUTES the carriers — both polarities witnessed).

The DOMAIN (`compute_domain`, `lib.rs:182-188`: fork version + genesis validators root →
a 32-byte domain) is trusted-CONFIG data, not adversary-controlled per-update input, so it
lives in `EthState` as an opaque digest — exactly the posture of the Rust API, which takes
`fork_version`/`genesis_validators_root` as caller-trusted parameters.

NON-VACUITY (the Nomad-law teeth, all under the SAME trusted state): the gate accepts a
genuine full-participation update AND the exact-quorum 342-participant update AND the
Electra depth-7 update, and REJECTS the 341-participant (sub-2/3) update, the tampered
finality branch, the wrong-depth branch, the tampered execution branch, the forged
signature, and the empty update (`eth_gate_discriminates`).
-/
import Dregg2.Bridge.VerifiedLightClient
import Dregg2.Tactics

/- The concrete witnesses walk 512-element committees (the REAL `SYNC_COMMITTEE_SIZE`),
which exceeds the default elaborator recursion depth. -/
set_option maxRecDepth 8192

namespace Dregg2.Bridge.LightClientEth

open Dregg2.Bridge.VerifiedLightClient

/-! ## §1 — The HONEST crypto leaves: BLS aggregate soundness + SHA-256 CR, as VISIBLE fields.

`EthLeaf` refines the foundation's `CryptoLeaf` shape to the sync-committee reality: the
signature primitive is an AGGREGATE verify over a LIST of pubkeys and one shared message
(`fast_aggregate_verify`, `lib.rs:225-241`), and the hash primitive is the 2-ary SSZ pair
hash `SHA-256(a ‖ b)` (`ssz.rs:16-26`) from which every `hash_tree_root` and Merkle branch
in the client is built. `toCryptoLeaf` below packages it back into the foundation's
`CryptoLeaf` (the signed `Msg` is the `SigningData` pair, its `hash` IS the signing root). -/

/-- **`EthLeaf`** — the named, minimal verified-primitive bundle for Ethereum.
`blsSound` and `hashPairCR` are THE two crypto leaves; `uChunkInj` is the (spec-level) SSZ
`uint64`-chunk injectivity. All are visible structure fields an instance must supply. -/
structure EthLeaf where
  /-- BLS12-381 G1 public key (48 compressed bytes in production). -/
  PubKey : Type
  /-- BLS12-381 G2 (aggregate) signature (96 compressed bytes in production). -/
  Sig : Type
  /-- 32-byte digest / root (SHA-256 output in production). -/
  Digest : Type
  /-- Digest equality is decidable (the Rust `==` on `[u8; 32]`). Computability
  structure, not a crypto assumption. -/
  deq : DecidableEq Digest
  /-- `fast_aggregate_verify`: one aggregate signature, a list of pubkeys, one shared
  message (the sync-committee case, `lib.rs:246-261`). Opaque; `blst`/EverCrypt realizes it. -/
  blsAggVerify : List PubKey → Digest → Sig → Bool
  /-- The DENOTATION: every key holder in the list genuinely authorized the message. -/
  SignedAll : List PubKey → Digest → Prop
  /-- **THE BLS LEAF (named, minimal).** A verifying aggregate entails all listed key
  holders signed the message — aggregate unforgeability, nothing more. -/
  blsSound : ∀ pks m s, blsAggVerify pks m s = true → SignedAll pks m
  /-- The SSZ pair hash `SHA-256(a ‖ b)` (`ssz.rs:16-26`). Opaque. -/
  hashPair : Digest → Digest → Digest
  /-- **CARRIER — THE SHA-256 CR LEAF (named, minimal).** A `Prop`, NOT idealized
  injectivity (which is pigeonhole-false for the compressing SHA-256). Mirrors
  `PortalFloor.Blake3Kernel.collisionHard` (`Crypto/PortalFloor.lean:181-182`): a
  production instance supplies the named SHA-256 CR assumption here; the model PROVES it
  (`modelLeaf_hashPairCR`); a collapsing hash REFUTES it (`collapseEthLeaf_not_hashPairCR`). -/
  hashPairCR : Prop
  /-- The CR carrier unpacked (mirrors `Blake3Kernel.noCollision`): GIVEN the CR floor,
  equal pair-hashes pin equal children — which makes Merkle reconstruction BINDING. -/
  noPairCollision : hashPairCR → ∀ a b c d : Digest, hashPair a b = hashPair c d → a = c ∧ b = d
  /-- The SSZ `uint64` chunk encoding (little-endian right-padded, `ssz.rs:54-60`). -/
  uChunk : Nat → Digest
  /-- **CARRIER — SSZ `uint64`-chunk injectivity** (spec-level: true of the real encoding
  on the `u64` domain — but a CARRIER all the same, so no unconditional injectivity law
  over all of `Nat` is smuggled in; refutable by a collapsing encoding,
  `collapseEthLeaf_not_uChunkInj`). -/
  uChunkInj : Prop
  /-- The chunk carrier unpacked: GIVEN the encoding floor, equal chunks pin equal values. -/
  noChunkCollision : uChunkInj → ∀ a b : Nat, uChunk a = uChunk b → a = b
  /-- The all-zero 32-byte chunk (SSZ merkleize padding, `ssz.rs:33-52`). -/
  zeroChunk : Digest
  /-- The all-zero (uninitialized) signature — the fail-closed probe's signature slot. -/
  zeroSig : Sig

/-- Decidable digest equality as a `Bool` (the Rust `value == root` in
`is_valid_merkle_branch`, `ssz.rs:144`). -/
def EthLeaf.beq (L : EthLeaf) (a b : L.Digest) : Bool := @decide (a = b) (L.deq a b)

theorem EthLeaf.beq_iff (L : EthLeaf) {a b : L.Digest} : L.beq a b = true ↔ a = b := by
  letI := L.deq
  unfold EthLeaf.beq
  exact decide_eq_true_iff

/-- **`EthLeaf.pair_inj` (the floor theorem shape; mirrors `CryptoLeaf.hash_inj` /
`blake3_floor_cr`).** GIVEN the SHA-256 CR carrier, a pair-hash equality pins both
children. The carrier is an explicit hypothesis — visible at every use site, never
smuggled. -/
theorem EthLeaf.pair_inj (L : EthLeaf) (hcr : L.hashPairCR) {a b c d : L.Digest}
    (h : L.hashPair a b = L.hashPair c d) : a = c ∧ b = d :=
  L.noPairCollision hcr a b c d h

/-- **`EthLeaf.chunk_inj`.** GIVEN the chunk-encoding carrier, equal `uint64` chunks pin
equal values. -/
theorem EthLeaf.chunk_inj (L : EthLeaf) (hinj : L.uChunkInj) {a b : Nat}
    (h : L.uChunk a = L.uChunk b) : a = b :=
  L.noChunkCollision hinj a b h

/-- Package an `EthLeaf` as the foundation's `CryptoLeaf`: the signer set is the pubkey
LIST, the signed `Msg` is the SSZ `SigningData` pair `(object_root, domain)`, and the
leaf's `hash` of that pair IS the signing root (`lib.rs:192-201`) — so `sigVerify` is
exactly "BLS-aggregate-verify over the signing root". `sigSound` comes straight from
`blsSound`, and the foundation's `hashCR` CARRIER is the conjunction of THIS chain's two
hash-fact carriers (`hashPairCR ∧ uChunkInj` — the Ethereum hash floor as ONE named
hypothesis, which is exactly what the foundation's `noForgery : leaf.hashCR → …`
threads); `noCollision` consumes only the pair-CR half. The foundation leaf is the SAME
assumption, repackaged. -/
def EthLeaf.toCryptoLeaf (L : EthLeaf) : CryptoLeaf where
  PubKey := List L.PubKey
  Msg := L.Digest × L.Digest
  Sig := L.Sig
  Digest := L.Digest
  sigVerify := fun pks m s => L.blsAggVerify pks (L.hashPair m.1 m.2) s
  hash := fun m => L.hashPair m.1 m.2
  Signed := fun pks m => L.SignedAll pks (L.hashPair m.1 m.2)
  sigSound := fun pks m s h => L.blsSound pks (L.hashPair m.1 m.2) s h
  hashCR := L.hashPairCR ∧ L.uChunkInj
  noCollision := fun hcr m₁ m₂ h => by
    obtain ⟨h1, h2⟩ := L.pair_inj hcr.1 h
    cases m₁; cases m₂; cases h1; cases h2; rfl

/-! ## §2 — Spec constants (`lib.rs:43-60`, `finality.rs:36-45`, `execution.rs:26-31`). -/

/-- `SYNC_COMMITTEE_SIZE = 512` (`lib.rs:43`). -/
def syncCommitteeSize : Nat := 512

/-- `FINALIZED_ROOT_GINDEX = 105` (Altair..Deneb, `finality.rs:36`). -/
def finalizedRootGindex : Nat := 105
/-- Altair..Deneb finality-branch depth `floor(log2 105) = 6` (`finality.rs:38`). -/
def finalizedRootDepth : Nat := 6
/-- `FINALIZED_ROOT_GINDEX_ELECTRA = 169` (`finality.rs:40`). -/
def finalizedRootGindexElectra : Nat := 169
/-- Electra+ finality-branch depth `floor(log2 169) = 7` (`finality.rs:42`). -/
def finalizedRootDepthElectra : Nat := 7
/-- Finalized-root SUBTREE index — 41 in BOTH fork families (`finality.rs:43-45`). -/
def finalizedRootSubtreeIndex : Nat := 41

/-- The subtree index really is `gindex mod 2^depth` in both fork families (the
`debug_assert_eq!` at `finality.rs:109-112`, proven). -/
theorem finalizedRootSubtreeIndex_correct :
    finalizedRootSubtreeIndex = finalizedRootGindex % 2 ^ finalizedRootDepth
    ∧ finalizedRootSubtreeIndex = finalizedRootGindexElectra % 2 ^ finalizedRootDepthElectra := by
  decide

/-- `EXECUTION_PAYLOAD_GINDEX = 25` (`execution.rs:26`). -/
def executionPayloadGindex : Nat := 25
/-- Execution-branch depth `floor(log2 25) = 4` (`execution.rs:28`). -/
def executionPayloadDepth : Nat := 4
/-- Execution-payload subtree index `25 % 2^4 = 9` (`execution.rs:30-31`). -/
def executionPayloadSubtreeIndex : Nat := 9

theorem executionPayloadSubtreeIndex_correct :
    executionPayloadSubtreeIndex = executionPayloadGindex % 2 ^ executionPayloadDepth := by
  decide

/-- `NEXT_SYNC_COMMITTEE_GINDEX = 55` (Altair..Deneb, `lib.rs:66-68`). -/
def nextSyncCommitteeGindex : Nat := 55
/-- Altair..Deneb committee-rotation branch depth `floor(log2 55) = 5` (`lib.rs:69-70`). -/
def nextSyncCommitteeDepth : Nat := 5
/-- `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA = 87` (`lib.rs:71-73`). -/
def nextSyncCommitteeGindexElectra : Nat := 87
/-- Electra+ committee-rotation branch depth `floor(log2 87) = 6` (`lib.rs:74-75`). -/
def nextSyncCommitteeDepthElectra : Nat := 6
/-- Committee-rotation SUBTREE index — 23 in BOTH fork families (`lib.rs:76-81`). -/
def nextSyncCommitteeSubtreeIndex : Nat := 23

/-- The committee-rotation subtree index really is `gindex mod 2^depth` in both fork
families. ⚠ The Rust states this as a `debug_assert_eq!` (`lib.rs:548-551`) — which is
COMPILED OUT of every release build, so in the shipped binary it asserts nothing. Here it
is a kernel-checked theorem. -/
theorem nextSyncCommitteeSubtreeIndex_correct :
    nextSyncCommitteeSubtreeIndex = nextSyncCommitteeGindex % 2 ^ nextSyncCommitteeDepth
    ∧ nextSyncCommitteeSubtreeIndex
        = nextSyncCommitteeGindexElectra % 2 ^ nextSyncCommitteeDepthElectra := by
  decide

/-- **The no-rounding-trap boundary** (`lib.rs:301-303`): 342 participants meet the
multiply-form 2/3 threshold, 341 do not. `342 = ⌈2·512/3⌉` exactly. -/
theorem quorum_boundary :
    (2 * syncCommitteeSize ≤ 3 * 342) ∧ ¬ (2 * syncCommitteeSize ≤ 3 * 341) := by
  decide

/-! ## §3 — The data types (`lib.rs:99-164`, `finality.rs:47-71`, `execution.rs:44-70`). -/

/-- Altair `BeaconBlockHeader` (`lib.rs:102-109`) — 5-field SSZ container, field order
load-bearing for the root. -/
structure BeaconBlockHeader (L : EthLeaf) where
  slot : Nat
  proposerIndex : Nat
  parentRoot : L.Digest
  stateRoot : L.Digest
  bodyRoot : L.Digest

/-- Deneb/Electra 17-field `ExecutionPayloadHeader` (`execution.rs:44-70`). The
byte-blob fields (`logs_bloom`, `extra_data`) enter the container root through their own
sub-roots (`htr_logs_bloom` / `htr_bytelist_le32`, `execution.rs:81,87`), so they are
modeled at that seam as digest fields; `fee_recipient` (bytes20) and `base_fee_per_gas`
(LE uint256) are single right-padded chunks, likewise modeled as digests. -/
structure ExecutionPayloadHeader (L : EthLeaf) where
  parentHash : L.Digest
  feeRecipient : L.Digest
  stateRoot : L.Digest
  receiptsRoot : L.Digest
  logsBloomRoot : L.Digest
  prevRandao : L.Digest
  blockNumber : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraDataRoot : L.Digest
  baseFeePerGas : L.Digest
  blockHash : L.Digest
  transactionsRoot : L.Digest
  withdrawalsRoot : L.Digest
  blobGasUsed : Nat
  excessBlobGas : Nat

/-- The `SyncAggregate` (`lib.rs:145-149`): the 512-bit participation bitfield (as a
`List Bool`, length CHECKED = 512 by the rules) + one aggregate signature. -/
structure SyncAggregate (L : EthLeaf) where
  bits : List Bool
  sig : L.Sig

/-- Capella+ `LightClientHeader` (`finality.rs:49-55`): beacon header + execution payload
header + the depth-4 branch proving the latter into `beacon.body_root`. -/
structure LightClientHeader (L : EthLeaf) where
  beacon : BeaconBlockHeader L
  execution : ExecutionPayloadHeader L
  executionBranch : List L.Digest

/-- The `LightClientUpdate` subset this client verifies (`finality.rs:60-71`). -/
structure LightClientUpdate (L : EthLeaf) where
  attestedHeader : BeaconBlockHeader L
  finalizedHeader : LightClientHeader L
  finalityBranch : List L.Digest
  syncAggregate : SyncAggregate L

/-- The TRUSTED STATE: the current sync-committee pubkeys plus the (config-derived)
sync-committee DOMAIN (`compute_domain`, `lib.rs:182-188` — fork version + genesis
validators root; caller-trusted parameters in the Rust API, so opaque config here). -/
structure EthState (L : EthLeaf) where
  committee : List L.PubKey
  domain : L.Digest

/-! ## §4 — SSZ hash-tree-roots and Merkle reconstruction (`ssz.rs`, `lib.rs:114-123`,
`execution.rs:74-96`). -/

/-- Merkleize 4 chunks. -/
def merk4 (L : EthLeaf) (a b c d : L.Digest) : L.Digest :=
  L.hashPair (L.hashPair a b) (L.hashPair c d)

/-- Merkleize 8 chunks. -/
def merk8 (L : EthLeaf) (a b c d e f g h : L.Digest) : L.Digest :=
  L.hashPair (merk4 L a b c d) (merk4 L e f g h)

/-- Merkleize 16 chunks. -/
def merk16 (L : EthLeaf) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : L.Digest) :
    L.Digest :=
  L.hashPair (merk8 L c0 c1 c2 c3 c4 c5 c6 c7) (merk8 L c8 c9 c10 c11 c12 c13 c14 c15)

/-- `hash_tree_root` of a `BeaconBlockHeader` (`lib.rs:114-123`): the five field chunks
padded to 8 and merkleized. Field ORDER is load-bearing. -/
def htrHeader (L : EthLeaf) (h : BeaconBlockHeader L) : L.Digest :=
  merk8 L (L.uChunk h.slot) (L.uChunk h.proposerIndex)
    h.parentRoot h.stateRoot h.bodyRoot
    L.zeroChunk L.zeroChunk L.zeroChunk

/-- `hash_tree_root` of the 17-field `ExecutionPayloadHeader` (`execution.rs:74-96`):
17 chunks padded to 32 and merkleized — left subtree = fields 0..15, right subtree =
`excess_blob_gas` + 15 zero chunks. Field ORDER matches `execution.rs:76-94` exactly. -/
def htrExec (L : EthLeaf) (e : ExecutionPayloadHeader L) : L.Digest :=
  L.hashPair
    (merk16 L e.parentHash e.feeRecipient e.stateRoot e.receiptsRoot
      e.logsBloomRoot e.prevRandao (L.uChunk e.blockNumber) (L.uChunk e.gasLimit)
      (L.uChunk e.gasUsed) (L.uChunk e.timestamp) e.extraDataRoot e.baseFeePerGas
      e.blockHash e.transactionsRoot e.withdrawalsRoot (L.uChunk e.blobGasUsed))
    (merk16 L (L.uChunk e.excessBlobGas) L.zeroChunk L.zeroChunk L.zeroChunk
      L.zeroChunk L.zeroChunk L.zeroChunk L.zeroChunk L.zeroChunk L.zeroChunk
      L.zeroChunk L.zeroChunk L.zeroChunk L.zeroChunk L.zeroChunk L.zeroChunk)

/-- `compute_signing_root` (`lib.rs:192-201`): the SSZ `SigningData` 2-field container
root `hash_pair(hash_tree_root(header), domain)` — the 32 bytes the committee SIGNS.
The committee never signs raw header bytes; the domain separates forks/chains. -/
def signingRoot (L : EthLeaf) (ts : EthState L) (h : BeaconBlockHeader L) : L.Digest :=
  L.hashPair (htrHeader L h) ts.domain

/-- The Merkle-branch FOLD of `is_valid_merkle_branch` (`ssz.rs:130-145`): walk the branch
bottom-up, hashing left/right by the index bit (`compute_branch_root`,
`execution.rs:130-140` is the same fold). `reconstruct leaf branch index` is the root the
branch CLAIMS; the rules compare it to the trusted root. -/
def reconstruct (L : EthLeaf) : L.Digest → List L.Digest → Nat → L.Digest
  | leaf, [], _ => leaf
  | leaf, n :: rest, idx =>
      reconstruct L (if idx % 2 = 1 then L.hashPair n leaf else L.hashPair leaf n) rest (idx / 2)

/-! ## §5 — THE RULES (`verify_sync_aggregate` `lib.rs:276-324`,
`verify_finality_branch` `finality.rs:92-124`, `verify_execution_payload`
`execution.rs:104-126`, composed by `verify_finalized_update` `finality.rs:139-176`). -/

/-- The bit-selected participating subset (`lib.rs:290-295`): committee member `i`
participates iff bit `i` is set. Truncating zip, exactly like `iter().zip`-style selection;
both lengths are separately checked = 512 by the rules. -/
def participants {α : Type} : List α → List Bool → List α
  | [], _ => []
  | _ :: _, [] => []
  | pk :: c, b :: bs => if b then pk :: participants c bs else participants c bs

/-- **RULE 1 — the sync-aggregate gate** (`verify_sync_aggregate`, `lib.rs:276-324`):
committee is exactly 512 keys; the bitfield is 512 bits; the participating subset is
nonempty (the Nomad floor, `lib.rs:298-300`); participation meets the multiply-form 2/3
threshold `count * 3 ≥ 512 * 2` (`lib.rs:301-309`); and the BLS aggregate over the
participating pubkeys verifies against the SIGNING ROOT (`lib.rs:319-323`). -/
def verifySyncAggregate (L : EthLeaf) (ts : EthState L)
    (hdr : BeaconBlockHeader L) (agg : SyncAggregate L) : Bool :=
  decide (ts.committee.length = syncCommitteeSize)
  && decide (agg.bits.length = syncCommitteeSize)
  && decide (0 < (participants ts.committee agg.bits).length)
  && decide (2 * syncCommitteeSize ≤ 3 * (participants ts.committee agg.bits).length)
  && L.blsAggVerify (participants ts.committee agg.bits) (signingRoot L ts hdr) agg.sig

/-- **RULE 2 — the finality branch** (`verify_finality_branch`, `finality.rs:92-124`):
branch depth is 6 (Altair..Deneb) or 7 (Electra+) — any other length fail-closed — and the
branch reconstructs `hash_tree_root(finalized_beacon)` into the attested `state_root` at
subtree index 41. -/
def verifyFinalityBranch (L : EthLeaf) (finalizedBeacon : BeaconBlockHeader L)
    (branch : List L.Digest) (attestedStateRoot : L.Digest) : Bool :=
  (decide (branch.length = finalizedRootDepth)
    || decide (branch.length = finalizedRootDepthElectra))
  && L.beq (reconstruct L (htrHeader L finalizedBeacon) branch finalizedRootSubtreeIndex)
      attestedStateRoot

/-- **RULE 3 — the execution branch** (`verify_execution_payload`,
`execution.rs:104-126`): depth exactly 4, reconstructing
`hash_tree_root(execution_payload_header)` into the finalized `body_root` at subtree
index 9 — this is what pins the EVM `state_root` the proof-of-holdings opens against. -/
def verifyExecutionPayload (L : EthLeaf) (e : ExecutionPayloadHeader L)
    (branch : List L.Digest) (bodyRoot : L.Digest) : Bool :=
  decide (branch.length = executionPayloadDepth)
  && L.beq (reconstruct L (htrExec L e) branch executionPayloadSubtreeIndex) bodyRoot

/-- **THE COMPOSED GATE** (`verify_finalized_update`, `finality.rs:139-176`): sync
aggregate over the ATTESTED header, finality branch binding the FINALIZED header under the
attested state root, execution branch binding the payload under the finalized body root.
Any failed leg makes the whole verdict `false` — never a partial advance. -/
def verifyFinalizedUpdate (L : EthLeaf) (ts : EthState L) (u : LightClientUpdate L) : Bool :=
  verifySyncAggregate L ts u.attestedHeader u.syncAggregate
  && verifyFinalityBranch L u.finalizedHeader.beacon u.finalityBranch
      u.attestedHeader.stateRoot
  && verifyExecutionPayload L u.finalizedHeader.execution
      u.finalizedHeader.executionBranch u.finalizedHeader.beacon.bodyRoot

/-- **RULE 4 — the COMMITTEE-ROTATION branch** (`verify_committee_update`,
`lib.rs:534-563`): the branch depth is 5 (Altair..Deneb, `NEXT_SYNC_COMMITTEE_GINDEX = 55`)
or 6 (Electra+, gindex 87) — any other length fail-closed — and the branch reconstructs the
offered committee's SSZ `hash_tree_root` into the trusted/attested `state_root` at subtree
index 23.

**This is a SEPARATE decision from `verifyFinalizedUpdate`, deliberately.** A finalized
update advances the client's view of the CHAIN; a committee rotation advances the client's
TRUST ROOT — the set of keys every future update is checked against. `WeakSubjectivityStore`
reaches it on two paths: `bootstrap_committee` (under the governance-pinned checkpoint state
root, with no prior committee to sign anything) and `advance` step 3 (under the state root a
`verifyFinalizedUpdate` just accepted). Folding it into `verifyFinalizedUpdate` would make
the bootstrap path unreachable and would break `ethVerifyDecision_refines`; it gets its own
export instead.

⚠ **NAMED RESIDUAL — the committee root is a PROJECTION, not a modelled term.**
`committeeRoot` is taken as an opaque `L.Digest`: the SSZ `hash_tree_root` of the 512-key
`SyncCommittee` container (`merkleize([merkleize(map htr_bytes48 pubkeys), htr_bytes48 agg)])`,
`lib.rs:170-175`) is computed in Rust and supplied. This is ONE level weaker than
`verifyFinalityBranch` / `verifyExecutionPayload`, whose leaves are modelled here
(`htrHeader` / `htrExec`) — so the "the offered committee really is the one those bytes
hash to" step is a Rust projection on this path, exactly as the participant popcount is on
the sync path. What IS decided here, and what the Rust no longer decides, is the branch-DEPTH
admissibility and the reconstruction compare. -/
def verifyCommitteeRotation (L : EthLeaf) (committeeRoot : L.Digest)
    (branch : List L.Digest) (attestedStateRoot : L.Digest) : Bool :=
  (decide (branch.length = nextSyncCommitteeDepth)
    || decide (branch.length = nextSyncCommitteeDepthElectra))
  && L.beq (reconstruct L committeeRoot branch nextSyncCommitteeSubtreeIndex) attestedStateRoot

/-- The empty / default / uninitialized update — the Nomad-law fail-closed probe: zeroed
headers, NO participation bits, NO branches, the zero signature. -/
def emptyHeader (L : EthLeaf) : BeaconBlockHeader L :=
  ⟨0, 0, L.zeroChunk, L.zeroChunk, L.zeroChunk⟩

def emptyExec (L : EthLeaf) : ExecutionPayloadHeader L :=
  ⟨L.zeroChunk, L.zeroChunk, L.zeroChunk, L.zeroChunk, L.zeroChunk, L.zeroChunk,
    0, 0, 0, 0, L.zeroChunk, L.zeroChunk, L.zeroChunk, L.zeroChunk, L.zeroChunk, 0, 0⟩

def emptyUpdate (L : EthLeaf) : LightClientUpdate L :=
  ⟨emptyHeader L, ⟨emptyHeader L, emptyExec L, []⟩, [], ⟨[], L.zeroSig⟩⟩

/-! ## §6 — The FOREIGN-VALIDITY denotation: what a verify-accepted update genuinely IS. -/

/-- **`EthValidAt L ts u`** — Ethereum's OWN validity of the update, relative to the
trusted committee/domain `ts`:

  * `quorumSigned` — SOME subset of the TRUSTED committee, meeting the 2/3 multiply-form
    threshold, GENUINELY signed (the `SignedAll` denotation, via the BLS leaf) the
    attested header's signing root;
  * `finalityDepth`/`finalityCommits` — the finality branch has a legal depth (6 | 7) and
    reconstructs the finalized beacon header's root into the attested `state_root` at
    subtree index 41 (the attested state COMMITS the finalized header);
  * `finalityBinds` — the commitment is BINDING: NO other finalized header opens the
    attested state root through a same-depth branch. This conjunct is exactly what the
    SHA-256 CR carrier buys (`noPairCollision`/`noChunkCollision` consumed, via
    `reconstruct_binding` + `htrHeader_inj`, in `eth_no_forgery`) — and exactly what a
    collapsing hash LOSES (`collapse_finality_not_binding`);
  * `executionDepth`/`executionCommits` — the depth-4 execution branch reconstructs the
    execution payload root into the finalized `body_root` (the finalized header COMMITS
    the EVM `state_root`). -/
structure EthValidAt (L : EthLeaf) (ts : EthState L) (u : LightClientUpdate L) : Prop where
  quorumSigned :
    ∃ ps : List L.PubKey,
      (∀ pk ∈ ps, pk ∈ ts.committee)
      ∧ 2 * syncCommitteeSize ≤ 3 * ps.length
      ∧ L.SignedAll ps (signingRoot L ts u.attestedHeader)
  finalityDepth :
    u.finalityBranch.length = finalizedRootDepth
    ∨ u.finalityBranch.length = finalizedRootDepthElectra
  finalityCommits :
    reconstruct L (htrHeader L u.finalizedHeader.beacon) u.finalityBranch
      finalizedRootSubtreeIndex = u.attestedHeader.stateRoot
  finalityBinds :
    ∀ (f : BeaconBlockHeader L) (b : List L.Digest),
      b.length = u.finalityBranch.length →
      reconstruct L (htrHeader L f) b finalizedRootSubtreeIndex = u.attestedHeader.stateRoot →
      f = u.finalizedHeader.beacon
  executionDepth :
    u.finalizedHeader.executionBranch.length = executionPayloadDepth
  executionCommits :
    reconstruct L (htrExec L u.finalizedHeader.execution) u.finalizedHeader.executionBranch
      executionPayloadSubtreeIndex = u.finalizedHeader.beacon.bodyRoot

/-! ## §7 — Supporting lemmas: participation subset, Merkle BINDING, header-root injectivity. -/

/-- A participating key is a TRUSTED-committee key (the bit filter only selects,
never invents — `lib.rs:290-295`). -/
theorem mem_participants {α : Type} {x : α} :
    ∀ {c : List α} {bs : List Bool}, x ∈ participants c bs → x ∈ c := by
  intro c
  induction c with
  | nil => intro bs h; cases bs <;> simp [participants] at h
  | cons pk c ih =>
    intro bs h
    cases bs with
    | nil => simp [participants] at h
    | cons b bs =>
      simp only [participants] at h
      split at h
      · rcases List.mem_cons.mp h with h1 | h2
        · exact h1 ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h2)
      · exact List.mem_cons_of_mem _ (ih h)

/-- **Merkle reconstruction is BINDING, GIVEN the SHA-256 CR carrier**: two same-depth
branches at the same index reconstructing the SAME root carry the SAME leaf. This is what
turns "the branch reconstructs" into "the root COMMITS the leaf" — a forger cannot open
the attested state root to a different finalized header. `hcr` is the explicit CR
hypothesis; `noPairCollision hcr` (via `pair_inj`) is consumed at every fold step — a
collapsing hash gets NO binding (`collapse_finality_not_binding`). -/
theorem reconstruct_binding (L : EthLeaf) (hcr : L.hashPairCR) :
    ∀ (b₁ b₂ : List L.Digest) (idx : Nat) (l₁ l₂ : L.Digest),
      b₁.length = b₂.length →
      reconstruct L l₁ b₁ idx = reconstruct L l₂ b₂ idx → l₁ = l₂ := by
  intro b₁
  induction b₁ with
  | nil =>
    intro b₂ idx l₁ l₂ hlen h
    cases b₂ with
    | nil => simpa [reconstruct] using h
    | cons _ _ => simp at hlen
  | cons n₁ rest₁ ih =>
    intro b₂ idx l₁ l₂ hlen h
    cases b₂ with
    | nil => simp at hlen
    | cons n₂ rest₂ =>
      simp only [reconstruct] at h
      have hlen' : rest₁.length = rest₂.length := by simpa using hlen
      have hstep := ih rest₂ (idx / 2) _ _ hlen' h
      by_cases hp : idx % 2 = 1
      · rw [if_pos hp, if_pos hp] at hstep
        exact (L.pair_inj hcr hstep).2
      · rw [if_neg hp, if_neg hp] at hstep
        exact (L.pair_inj hcr hstep).1

/-- **Header roots pin headers, GIVEN the carriers** (SHA-256 CR + `uint64`-chunk
injectivity, both explicit hypotheses): equal `hash_tree_root`s entail equal
`BeaconBlockHeader`s — including `slot` and `proposer_index` through the chunk
encoding (`noChunkCollision hinj` consumed there). -/
theorem htrHeader_inj (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj)
    (h₁ h₂ : BeaconBlockHeader L)
    (h : htrHeader L h₁ = htrHeader L h₂) : h₁ = h₂ := by
  unfold htrHeader merk8 merk4 at h
  obtain ⟨hl, hr⟩ := L.pair_inj hcr h
  obtain ⟨hll, hlr⟩ := L.pair_inj hcr hl
  obtain ⟨hslot, hpi⟩ := L.pair_inj hcr hll
  obtain ⟨hparent, hstate⟩ := L.pair_inj hcr hlr
  obtain ⟨hrl, _⟩ := L.pair_inj hcr hr
  obtain ⟨hbody, _⟩ := L.pair_inj hcr hrl
  cases h₁; cases h₂
  simp only [BeaconBlockHeader.mk.injEq]
  exact ⟨L.chunk_inj hinj hslot, L.chunk_inj hinj hpi, hparent, hstate, hbody⟩

/-- **NON-EQUIVOCATION, GIVEN the carriers.** Two finality branches of the same depth
accepted against the SAME attested state root carry the SAME finalized header: the
attested root COMMITS one finalized header. (The crypto content of `BadFinalityBranch`
fail-closure: a forger cannot substitute a different finalized header under an honest
attested root.) The CR carrier is the explicit hypothesis making this true — for the
collapsing hash the conclusion is FALSE (`collapse_finality_not_binding`). -/
theorem finalized_header_binding (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj)
    (f₁ f₂ : BeaconBlockHeader L) (b₁ b₂ : List L.Digest) (root : L.Digest)
    (h₁ : verifyFinalityBranch L f₁ b₁ root = true)
    (h₂ : verifyFinalityBranch L f₂ b₂ root = true)
    (hlen : b₁.length = b₂.length) : f₁ = f₂ := by
  unfold verifyFinalityBranch at h₁ h₂
  simp only [Bool.and_eq_true] at h₁ h₂
  have e₁ := L.beq_iff.mp h₁.2
  have e₂ := L.beq_iff.mp h₂.2
  exact htrHeader_inj L hcr hinj f₁ f₂
    (reconstruct_binding L hcr b₁ b₂ finalizedRootSubtreeIndex _ _ hlen (e₁.trans e₂.symm))

/-- **THE TRUST ROOT DOES NOT FORK, GIVEN the CR carrier.** Two committee-rotation branches
of the same depth accepted against the SAME trusted/attested state root carry the SAME
committee root: one state commits ONE `next_sync_committee`. This is the crypto content of
`UnchainedCommittee` fail-closure and the reason a rotation may advance the trust anchor at
all — an attacker holding a genuine state root cannot open it to a second, forged committee.
(For the collapsing hash the conclusion is FALSE — `collapse_committee_rotation_not_binding`
— so `hcr` is exactly the hypothesis separating commitment from equivocation here too.) -/
theorem committee_rotation_binding (L : EthLeaf) (hcr : L.hashPairCR)
    (cr₁ cr₂ : L.Digest) (b₁ b₂ : List L.Digest) (root : L.Digest)
    (h₁ : verifyCommitteeRotation L cr₁ b₁ root = true)
    (h₂ : verifyCommitteeRotation L cr₂ b₂ root = true)
    (hlen : b₁.length = b₂.length) : cr₁ = cr₂ := by
  unfold verifyCommitteeRotation at h₁ h₂
  simp only [Bool.and_eq_true] at h₁ h₂
  have e₁ := L.beq_iff.mp h₁.2
  have e₂ := L.beq_iff.mp h₂.2
  exact reconstruct_binding L hcr b₁ b₂ nextSyncCommitteeSubtreeIndex _ _ hlen
    (e₁.trans e₂.symm)

/-- **COMMITTEE ROTATION FAILS CLOSED — UNCONDITIONAL.** A missing / empty rotation branch
is refused under EVERY leaf, EVERY committee root and EVERY state root, with NO crypto
hypothesis: depth 0 is neither 5 nor 6. The bootstrap path (no prior committee has signed
anything) is exactly where a permissive default would install an attacker's committee as the
trust anchor, so this leg must hold even for a broken hash. -/
theorem committee_rotation_fail_closed (L : EthLeaf) (cr root : L.Digest) :
    verifyCommitteeRotation L cr [] root = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  unfold verifyCommitteeRotation at htrue
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at htrue
  obtain ⟨hdepth, _⟩ := htrue
  simp [nextSyncCommitteeDepth, nextSyncCommitteeDepthElectra] at hdepth

/-! ## §8 — THE THREE OBLIGATIONS: NoForgery, FailClosed (both generic over ANY leaf),
NonVacuous (per-instance; discharged on `modelLeaf` in §9). -/

/-- **NO FORGERY (the strong, ts-relative statement), GIVEN the hash carriers.** For
EVERY leaf, trusted state and update: IF the SHA-256 CR carrier and the chunk-encoding
carrier hold (`hcr`/`hinj` — the named crypto floor, an explicit hypothesis, NOT
injectivity), then gate-acceptance entails the update is Ethereum-VALID relative to that
trusted state — a ≥ 2/3 subset of the TRUSTED committee genuinely signed the attested
header's signing root (via the BLS leaf), the attested state commits AND BINDS the
finalized header, and the finalized body commits the execution payload. The proof
CONSUMES `L.blsSound` on the signature leg and `noPairCollision hcr` /
`noChunkCollision hinj` (via `reconstruct_binding` + `htrHeader_inj`) on the
`finalityBinds` leg: remove the BLS check from the rules, or drop a carrier, and this
theorem is unprovable. -/
theorem eth_no_forgery (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj) :
    ∀ (ts : EthState L) (u : LightClientUpdate L),
      verifyFinalizedUpdate L ts u = true → EthValidAt L ts u := by
  intro ts u h
  unfold verifyFinalizedUpdate verifySyncAggregate verifyFinalityBranch
    verifyExecutionPayload at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, EthLeaf.beq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hquorum⟩, hbls⟩, hfdepth, hfrec⟩, hedepth, herec⟩ := h
  exact {
    quorumSigned :=
      ⟨participants ts.committee u.syncAggregate.bits,
        fun _ hpk => mem_participants hpk, hquorum,
        L.blsSound _ _ _ hbls⟩
    finalityDepth := hfdepth
    finalityCommits := hfrec
    finalityBinds := fun f b hlen hb =>
      htrHeader_inj L hcr hinj f u.finalizedHeader.beacon
        (reconstruct_binding L hcr b u.finalityBranch finalizedRootSubtreeIndex _ _ hlen
          (hb.trans hfrec.symm))
    executionDepth := hedepth
    executionCommits := herec }

/-- **FAIL CLOSED (the Nomad-law tooth) — UNCONDITIONAL.** The empty/uninitialized update
is rejected under EVERY trusted state and EVERY leaf, with NO crypto hypothesis: rejection
never leans on the hash floor (fail-closed must hold even for a broken hash). Proof:
directly from the gate booleans — the empty finality branch has depth 0, neither 6 nor 7.
(Independently, its empty bitfield already fails the 512-bit and quorum checks.) -/
theorem eth_fail_closed (L : EthLeaf) :
    ∀ ts : EthState L, verifyFinalizedUpdate L ts (emptyUpdate L) = false := by
  intro ts
  rw [Bool.eq_false_iff]
  intro htrue
  unfold verifyFinalizedUpdate verifyFinalityBranch emptyUpdate at htrue
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at htrue
  obtain ⟨⟨_, hdepth, _⟩, _⟩ := htrue
  simp [finalizedRootDepth, finalizedRootDepthElectra] at hdepth

/-! ## §9 — The `ForeignLightClient` bundle + the PROVED model leaf (axiom-clean instance).

`NonVacuous` cannot hold for a degenerate leaf (e.g. `blsAggVerify ≡ false` is perfectly
SOUND but never accepts), so it is an INSTANCE obligation, taken as an argument and
discharged concretely below. -/

/-- **The Ethereum `ForeignLightClient`** over any leaf: the foundation bundle, with
`ForeignValid u := ∃ ts, EthValidAt L ts u` (the ts-free packaging the shared shape
requires; the STRONG per-ts statement is `eth_no_forgery` / `toAdapter_foreignFinal_eth`,
which the adapter composition uses at its fixed trusted state). -/
def ethClient (L : EthLeaf)
    (hnv : NonVacuous (verifyFinalizedUpdate L)) : ForeignLightClient where
  leaf := L.toCryptoLeaf
  Update := LightClientUpdate L
  TrustedState := EthState L
  ForeignValid := fun u => ∃ ts, EthValidAt L ts u
  verify := verifyFinalizedUpdate L
  emptyUpdate := emptyUpdate L
  noForgery := fun hcr ts u h => ⟨ts, eth_no_forgery L hcr.1 hcr.2 ts u h⟩
  failClosed := eth_fail_closed L
  nonVacuous := hnv

/-- **The adapter discharge, STRONG form, GIVEN the carriers**: the `InterchainAdapter` a
produced Ethereum client exposes at trusted state `ts` has its `foreignFinal` entail
`EthValidAt L ts` — the finality hypothesis is discharged to the ts-RELATIVE validity,
not just the ∃-form. The hash carriers are the explicit crypto hypotheses, exactly as in
the foundation's `toAdapter_foreignFinal_discharged`. -/
theorem toAdapter_foreignFinal_eth (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj)
    (hnv : NonVacuous (verifyFinalizedUpdate L)) (ts : EthState L)
    {Event : Type} (incl : Event → LightClientUpdate L → Prop)
    (u : LightClientUpdate L)
    (h : (toAdapter (ethClient L hnv) ts incl).foreignFinal u) : EthValidAt L ts u :=
  eth_no_forgery L hcr hinj ts u h

/-! ### The PROVED model leaf — a perfectly-binding realization, so the file is genuinely
axiom-clean and the leaves are demonstrably non-laundering. A PRODUCTION instance replaces
`modelLeaf` with the `blst`/EverCrypt realization, whose `blsSound`/`hashPairCR` are the
named library assumptions (documented at the instance site — `#assert_axioms` cannot see
hypothesis-carried assumptions, so the leaf fields ARE the audit surface). -/

/-- The model digest: a perfectly-binding "hash" — pairing is a free constructor, so CR
is constructor injectivity. (Production: 32-byte SHA-256 digests.) -/
inductive ModelDigest
  | chunk : Nat → ModelDigest
  | pair : ModelDigest → ModelDigest → ModelDigest
deriving DecidableEq, Repr

/-- The model `SignedAll` denotation: every listed signer is the genuine committee key
`7`. Discriminates — a list containing a forged key `3` is NOT all-signed. -/
def ModelSignedAll (pks : List Nat) (_m : ModelDigest) : Prop := ∀ pk ∈ pks, pk = 7

/-- The model aggregate verifier: all listed keys are the genuine key `7`, the signature
carries the exact signed message (message binding), and the aggregate count matches. -/
def modelAggVerify (pks : List Nat) (m : ModelDigest) (s : ModelDigest × Nat) : Bool :=
  pks.all (fun k => decide (k = 7)) && decide (s.1 = m) && decide (s.2 = 7 * pks.length)

/-- **The BLS leaf, PROVED for the model**: a verifying model aggregate entails every
listed key is the genuine key. -/
theorem modelBlsSound : ∀ pks m s, modelAggVerify pks m s = true → ModelSignedAll pks m := by
  intro pks m s h pk hpk
  simp only [modelAggVerify, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1 pk hpk

/-- The model leaf: the BLS soundness field PROVED, and the two hash-fact CARRIERS
supplied as the GENUINE CR/injectivity `Prop`s over this leaf's own primitives (the
`PortalFloor.Reference` pattern, `Crypto/PortalFloor.lean:362`) — NOT `True`. Both are
inhabitable here (`modelLeaf_hashPairCR` / `modelLeaf_uChunkInj` below: pairing is a free
constructor, so CR is constructor injectivity) and the SAME shapes are FALSE for the
collapsing leaf (`collapseEthLeaf_not_hashPairCR` / `collapseEthLeaf_not_uChunkInj`), so
every theorem below is kernel-axiom-clean AND the carriers demonstrably discriminate.
(`@[reducible]` so numerals/decidability see through the projections.) -/
@[reducible] def modelLeaf : EthLeaf where
  PubKey := Nat
  Sig := ModelDigest × Nat
  Digest := ModelDigest
  deq := inferInstance
  blsAggVerify := modelAggVerify
  SignedAll := ModelSignedAll
  blsSound := modelBlsSound
  hashPair := ModelDigest.pair
  hashPairCR := ∀ a b c d : ModelDigest,
    ModelDigest.pair a b = ModelDigest.pair c d → a = c ∧ b = d
  noPairCollision := fun h => h
  uChunk := ModelDigest.chunk
  uChunkInj := ∀ a b : Nat, ModelDigest.chunk a = ModelDigest.chunk b → a = b
  noChunkCollision := fun h => h
  zeroChunk := ModelDigest.chunk 0
  zeroSig := (ModelDigest.chunk 0, 0)

/-- **The model CR carrier HOLDS (positive polarity).** Pairing is a free constructor, so
collision resistance is constructor injectivity — the carrier is dischargeable, exactly
as a production instance discharges it with the named SHA-256 CR floor. -/
theorem modelLeaf_hashPairCR : modelLeaf.hashPairCR :=
  fun _ _ _ _ h => by injection h with h1 h2; exact ⟨h1, h2⟩

/-- **The model chunk carrier HOLDS (positive polarity).** -/
theorem modelLeaf_uChunkInj : modelLeaf.uChunkInj :=
  fun _ _ h => by injection h

/-- The BUNDLED foundation carrier (`toCryptoLeaf.hashCR = hashPairCR ∧ uChunkInj`)
discharged for the model — the argument the foundation's `noForgery`/adapter theorems
consume. -/
theorem modelCryptoLeaf_hashCR : modelLeaf.toCryptoLeaf.hashCR :=
  ⟨modelLeaf_hashPairCR, modelLeaf_uChunkInj⟩

/-! ### The badCompress-style FALSIFIER — the carriers are load-bearing, not `True` in
disguise (the `PortalFloor` §9b / `VerifiedLightClient.collapseLeaf` pattern): a
COLLAPSING pair hash / chunk encoding yields a lawful `EthLeaf` — the interface admits it
— but its carriers are provably FALSE, so `eth_no_forgery` has no conclusion for it, and
finality binding demonstrably FAILS (`collapse_finality_not_binding`): both polarities
witnessed. -/

/-- The collapsing pair hash: every pair digests to `chunk 0` (the badCompress). -/
def collapseHashPair (_ _ : ModelDigest) : ModelDigest := ModelDigest.chunk 0

/-- The collapsing chunk encoding: every value encodes to `chunk 0`. -/
def collapseUChunk (_ : Nat) : ModelDigest := ModelDigest.chunk 0

/-- A lawful `EthLeaf` over the COLLAPSING hash/encoding — same BLS primitives, same
genuine-CR-Prop carrier SHAPES, stated over the collapsed functions. The interface admits
it; only the carriers (below) separate it from the sound leaf. -/
@[reducible] def collapseEthLeaf : EthLeaf :=
  { modelLeaf with
    hashPair := collapseHashPair
    hashPairCR := ∀ a b c d : ModelDigest,
      collapseHashPair a b = collapseHashPair c d → a = c ∧ b = d
    noPairCollision := fun h => h
    uChunk := collapseUChunk
    uChunkInj := ∀ a b : Nat, collapseUChunk a = collapseUChunk b → a = b
    noChunkCollision := fun h => h }

/-- **The collapsing CR carrier is FALSE (negative polarity).** Distinct children collide
— the carrier REFUTES a broken hash, so it is a real discriminating hypothesis:
`modelLeaf.hashPairCR` holds, `collapseEthLeaf.hashPairCR` fails. -/
theorem collapseEthLeaf_not_hashPairCR : ¬ collapseEthLeaf.hashPairCR := by
  intro h
  exact absurd (h (.chunk 0) (.chunk 0) (.chunk 1) (.chunk 0) rfl).1 (by decide)

/-- **The collapsing chunk carrier is FALSE (negative polarity).** `0 ≠ 1` yet their
chunks collide. -/
theorem collapseEthLeaf_not_uChunkInj : ¬ collapseEthLeaf.uChunkInj := by
  intro h
  exact absurd (h 0 1 rfl) (by decide)

/-- **Binding is LOST under the collapse (what the carrier buys, shown by its absence).**
Two DIFFERENT finalized headers reconstruct the SAME root through same-depth branches —
the `finalized_header_binding` / `finalityBinds` conclusion is FALSE for the collapsing
leaf, so the CR carrier is exactly the hypothesis that separates commitment from
equivocation. -/
theorem collapse_finality_not_binding :
    ∃ (f₁ f₂ : BeaconBlockHeader collapseEthLeaf) (b : List ModelDigest),
      f₁ ≠ f₂
      ∧ b.length = finalizedRootDepth
      ∧ reconstruct collapseEthLeaf (htrHeader collapseEthLeaf f₁) b finalizedRootSubtreeIndex
        = reconstruct collapseEthLeaf (htrHeader collapseEthLeaf f₂) b
            finalizedRootSubtreeIndex := by
  refine ⟨⟨0, 0, .chunk 0, .chunk 0, .chunk 0⟩, ⟨1, 0, .chunk 0, .chunk 0, .chunk 0⟩,
    List.replicate finalizedRootDepth (.chunk 0), ?_, by decide, by decide⟩
  intro h
  exact absurd (congrArg BeaconBlockHeader.slot h) (by decide)

/-- **The TRUST ROOT forks under the collapse (what the carrier buys on the rotation path).**
Two DIFFERENT committee roots reconstruct the SAME state root through a same-depth rotation
branch, so `committee_rotation_binding`'s conclusion is FALSE for the collapsing leaf: with
a broken SHA-256 an attacker opens one honest attested state root to a second committee and
takes the trust anchor. The CR carrier is precisely what forbids that. -/
theorem collapse_committee_rotation_not_binding :
    ∃ (cr₁ cr₂ : ModelDigest) (b : List ModelDigest),
      cr₁ ≠ cr₂
      ∧ b.length = nextSyncCommitteeDepth
      ∧ reconstruct collapseEthLeaf cr₁ b nextSyncCommitteeSubtreeIndex
        = reconstruct collapseEthLeaf cr₂ b nextSyncCommitteeSubtreeIndex :=
  ⟨.chunk 0, .chunk 1, List.replicate nextSyncCommitteeDepth (.chunk 0), by decide, by decide,
    by decide⟩

/-! ### Concrete witnesses: a genuine 512-committee state and a self-consistent update
(branches built with the constructive inverse of `is_valid_merkle_branch`, exactly like
the Rust KATs use `compute_branch_root`, `execution.rs:128-140`). -/

/-- The genuine trusted state: 512 copies of the genuine key `7` (`SYNC_COMMITTEE_SIZE`
for real), sync-committee domain `chunk 99`. -/
def modelState : EthState modelLeaf :=
  ⟨List.replicate syncCommitteeSize 7, ModelDigest.chunk 99⟩

/-- A FORGED trusted state: a committee of 512 untrusted keys `3`. -/
def forgedState : EthState modelLeaf :=
  ⟨List.replicate syncCommitteeSize 3, ModelDigest.chunk 99⟩

def modelExec : ExecutionPayloadHeader modelLeaf where
  parentHash := ModelDigest.chunk 11
  feeRecipient := ModelDigest.chunk 12
  stateRoot := ModelDigest.chunk 13
  receiptsRoot := ModelDigest.chunk 14
  logsBloomRoot := ModelDigest.chunk 15
  prevRandao := ModelDigest.chunk 16
  blockNumber := 999
  gasLimit := 30000000
  gasUsed := 21000
  timestamp := 1720000000
  extraDataRoot := ModelDigest.chunk 17
  baseFeePerGas := ModelDigest.chunk 18
  blockHash := ModelDigest.chunk 19
  transactionsRoot := ModelDigest.chunk 20
  withdrawalsRoot := ModelDigest.chunk 21
  blobGasUsed := 0
  excessBlobGas := 0

def modelExecBranch : List ModelDigest := List.replicate 4 (ModelDigest.chunk 0)

/-- The finalized header's `body_root` COMMITS the execution payload (constructive
inverse of the depth-4 branch at subtree index 9). -/
def modelBodyRoot : ModelDigest :=
  reconstruct modelLeaf (htrExec modelLeaf modelExec) modelExecBranch
    executionPayloadSubtreeIndex

def modelFinalized : BeaconBlockHeader modelLeaf :=
  ⟨6400, 42, ModelDigest.chunk 1, ModelDigest.chunk 2, modelBodyRoot⟩

def modelFinalityBranch : List ModelDigest := List.replicate 6 (ModelDigest.chunk 3)
def modelFinalityBranch7 : List ModelDigest := List.replicate 7 (ModelDigest.chunk 3)

/-- The attested header (Altair..Deneb, depth-6 finality branch): its `state_root`
COMMITS the finalized header at subtree index 41. -/
def modelAttested : BeaconBlockHeader modelLeaf :=
  ⟨6464, 77, ModelDigest.chunk 4,
    reconstruct modelLeaf (htrHeader modelLeaf modelFinalized) modelFinalityBranch
      finalizedRootSubtreeIndex,
    ModelDigest.chunk 5⟩

/-- The attested header for the Electra+ depth-7 finality branch. -/
def modelAttested7 : BeaconBlockHeader modelLeaf :=
  ⟨6464, 77, ModelDigest.chunk 4,
    reconstruct modelLeaf (htrHeader modelLeaf modelFinalized) modelFinalityBranch7
      finalizedRootSubtreeIndex,
    ModelDigest.chunk 5⟩

/-- The GENUINE update: full participation, correct aggregate over the signing root,
self-consistent finality + execution branches. -/
def goodUpdate : LightClientUpdate modelLeaf :=
  ⟨modelAttested, ⟨modelFinalized, modelExec, modelExecBranch⟩, modelFinalityBranch,
    ⟨List.replicate 512 true, (signingRoot modelLeaf modelState modelAttested, 7 * 512)⟩⟩

/-- The Electra+ depth-7 genuine update (both legal depths must be ACCEPTED,
`finality.rs:97-107`). -/
def goodUpdate7 : LightClientUpdate modelLeaf :=
  ⟨modelAttested7, ⟨modelFinalized, modelExec, modelExecBranch⟩, modelFinalityBranch7,
    ⟨List.replicate 512 true, (signingRoot modelLeaf modelState modelAttested7, 7 * 512)⟩⟩

/-- EXACTLY 342 participants = ⌈2·512/3⌉ — the boundary ACCEPT (no rounding trap). -/
def quorum342Update : LightClientUpdate modelLeaf :=
  { goodUpdate with
    syncAggregate :=
      ⟨List.replicate 342 true ++ List.replicate 170 false,
        (signingRoot modelLeaf modelState modelAttested, 7 * 342)⟩ }

/-- 341 participants — ONE below the 2/3 threshold: must be REJECTED. -/
def subQuorum341Update : LightClientUpdate modelLeaf :=
  { goodUpdate with
    syncAggregate :=
      ⟨List.replicate 341 true ++ List.replicate 171 false,
        (signingRoot modelLeaf modelState modelAttested, 7 * 341)⟩ }

/-- A TAMPERED finality branch (right depth, wrong nodes): the reconstruction misses the
attested state root — must be REJECTED. -/
def badFinalityUpdate : LightClientUpdate modelLeaf :=
  { goodUpdate with finalityBranch := List.replicate 6 (ModelDigest.chunk 4) }

/-- A WRONG-DEPTH finality branch (depth 5 — neither 6 nor 7): fail-closed. -/
def wrongDepthUpdate : LightClientUpdate modelLeaf :=
  { goodUpdate with finalityBranch := List.replicate 5 (ModelDigest.chunk 3) }

/-- A TAMPERED execution branch: the payload no longer proves into `body_root`. -/
def badExecUpdate : LightClientUpdate modelLeaf :=
  { goodUpdate with
    finalizedHeader :=
      ⟨modelFinalized, modelExec, List.replicate 4 (ModelDigest.chunk 9)⟩ }

/-- A FORGED signature: the aggregate does not bind the signing root. -/
def forgedSigUpdate : LightClientUpdate modelLeaf :=
  { goodUpdate with
    syncAggregate := ⟨List.replicate 512 true, (ModelDigest.chunk 123, 7 * 512)⟩ }

/-- **NON-VACUOUS**: under the genuine state the gate accepts the genuine update and
rejects the empty update — `verifyFinalizedUpdate modelLeaf` discriminates. -/
theorem model_non_vacuous : NonVacuous (verifyFinalizedUpdate modelLeaf) :=
  ⟨modelState, goodUpdate, emptyUpdate modelLeaf, by decide, by decide⟩

/-- **The Ethereum client instance** — all three foundation obligations discharged
(so the bundle EXISTS; the shape is inhabited by the real rules). -/
def modelEthClient : ForeignLightClient := ethClient modelLeaf model_non_vacuous

/-! ## §10 — THE DISCRIMINATORS BITE (all under the SAME genuine trusted state). -/

/-- **THE GATE DISCRIMINATES** — the assembled Nomad-law tooth, on concrete data:
accepts the genuine update, the exact-quorum-342 update, and the Electra depth-7 update;
REJECTS sub-quorum-341, the tampered finality branch, the wrong-depth branch, the
tampered execution branch, the forged signature, and the empty update. -/
theorem eth_gate_discriminates :
    verifyFinalizedUpdate modelLeaf modelState goodUpdate = true
    ∧ verifyFinalizedUpdate modelLeaf modelState goodUpdate7 = true
    ∧ verifyFinalizedUpdate modelLeaf modelState quorum342Update = true
    ∧ verifyFinalizedUpdate modelLeaf modelState subQuorum341Update = false
    ∧ verifyFinalizedUpdate modelLeaf modelState badFinalityUpdate = false
    ∧ verifyFinalizedUpdate modelLeaf modelState wrongDepthUpdate = false
    ∧ verifyFinalizedUpdate modelLeaf modelState badExecUpdate = false
    ∧ verifyFinalizedUpdate modelLeaf modelState forgedSigUpdate = false
    ∧ verifyFinalizedUpdate modelLeaf modelState (emptyUpdate modelLeaf) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A forged-committee state never accepts the genuine update (its keys cannot produce a
verifying aggregate). -/
theorem eth_forged_committee_rejected :
    verifyFinalizedUpdate modelLeaf forgedState goodUpdate = false := by decide

/-- The TRUE side of the denotation: the genuine update IS Ethereum-valid at the genuine
state (obtained THROUGH `eth_no_forgery` — the model carriers `modelLeaf_hashPairCR` /
`modelLeaf_uChunkInj` passed explicitly, so the pipeline is exercised end-to-end,
carrier discharge included). -/
theorem eth_valid_good : EthValidAt modelLeaf modelState goodUpdate :=
  eth_no_forgery modelLeaf modelLeaf_hashPairCR modelLeaf_uChunkInj
    modelState goodUpdate (by decide)

/-- The FALSE side: the tampered-finality-branch update is NOT Ethereum-valid — its
branch does not commit the finalized header under the attested state root. -/
theorem eth_invalid_bad_finality : ¬ EthValidAt modelLeaf modelState badFinalityUpdate := by
  rintro ⟨_, _, hrec, _, _, _⟩
  exact absurd hrec (by decide)

/-- **The BLS leaf discriminates (non-laundering witness).** At the FORGED state (an
untrusted committee of key-3s) NO update is Ethereum-valid: any qualifying signer subset
is nonempty (2/3 of 512 > 0), its members must be committee keys (= 3) AND genuinely
signed (= 7) — absurd. The `SignedAll` denotation is doing real work. -/
theorem eth_forged_committee_invalid (u : LightClientUpdate modelLeaf) :
    ¬ EthValidAt modelLeaf forgedState u := by
  rintro ⟨⟨ps, hsub, hlen, hsigned⟩, _, _, _, _, _⟩
  cases ps with
  | nil => exact absurd hlen (by decide)
  | cons pk rest =>
    have h7 : pk = 7 := hsigned pk List.mem_cons_self
    have h3 : pk = 3 :=
      List.eq_of_mem_replicate (hsub pk List.mem_cons_self)
    exact absurd (h7 ▸ h3) (by decide)

/-! ## §11 — COMPOSITION: the verified Ethereum client PRODUCES the `InterchainAdapter`
finality hypothesis (the `foreignFinal` oracle is discharged, not assumed). The inclusion
relation is the finality-following PAYOFF (`FinalizedExecution`, `finality.rs:169-175`):
the event is the claim "this is the finalized EVM execution state root". -/

/-- The claimed finalized EVM state root matches the one the update commits. -/
def modelIncl : ModelDigest → LightClientUpdate modelLeaf → Prop :=
  fun ev u => ev = u.finalizedHeader.execution.stateRoot

/-- The adapter the Ethereum client produces at the genuine trusted state. -/
def modelAdapter : Metatheory.Bridge.InterchainAdapter (LightClientUpdate modelLeaf) ModelDigest :=
  toAdapter modelEthClient modelState modelIncl

/-- **END-TO-END DISCHARGE.** The adapter ACCEPTS the genuine finalized EVM state root,
and by `NoForgery` that acceptance yields an Ethereum-VALID update committing it — the
`foreignFinal` hypothesis is BACKED by the verified sync-committee rules, not assumed. -/
theorem eth_adapter_accepts_and_discharges :
    modelAdapter.accepts modelExec.stateRoot
    ∧ ∃ u, (∃ ts, EthValidAt modelLeaf ts u) ∧ modelIncl modelExec.stateRoot u := by
  have hacc : modelAdapter.accepts modelExec.stateRoot :=
    ⟨goodUpdate,
      (by decide : verifyFinalizedUpdate modelLeaf modelState goodUpdate = true), rfl⟩
  exact ⟨hacc, toAdapter_accepts_entails_valid modelEthClient modelCryptoLeaf_hashCR
    modelState modelIncl _ hacc⟩

/-- **The empty update is rejected at the adapter boundary** — `FailClosed` lifted. -/
theorem eth_adapter_rejects_empty :
    ¬ modelAdapter.foreignFinal (emptyUpdate modelLeaf) :=
  toAdapter_rejects_empty modelEthClient modelState modelIncl

/-! ### The COMMITTEE-ROTATION witnesses (RULE 4) — the TRUST-ROOT advance, both polarities. -/

/-- A concrete `next_sync_committee` SSZ root. (Modelled as the opaque digest it is — see
the named residual on `verifyCommitteeRotation`.) -/
def modelCommitteeRoot : ModelDigest := ModelDigest.chunk 55
/-- A depth-5 (Altair..Deneb) committee-rotation branch. -/
def modelRotationBranch : List ModelDigest :=
  List.replicate nextSyncCommitteeDepth (ModelDigest.chunk 4)
/-- The trusted/attested beacon state root that branch reconstructs into — built with the
constructive inverse of `is_valid_merkle_branch`, exactly like the Rust KATs. -/
def modelRotationStateRoot : ModelDigest :=
  reconstruct modelLeaf modelCommitteeRoot modelRotationBranch nextSyncCommitteeSubtreeIndex

/-- **RULE 4 DISCRIMINATES**, kernel-checked, in all four directions: the genuine rotation
is ACCEPTED; a DIFFERENT committee root under the same branch and state root is REFUSED
(the trust-root forgery); a MISSING branch is REFUSED (the bootstrap permissive-default
trap); and an inadmissible depth is REFUSED. A constant rotation gate fails this. -/
theorem committee_rotation_discriminates :
    verifyCommitteeRotation modelLeaf modelCommitteeRoot modelRotationBranch
        modelRotationStateRoot = true
    ∧ verifyCommitteeRotation modelLeaf (ModelDigest.chunk 56) modelRotationBranch
        modelRotationStateRoot = false
    ∧ verifyCommitteeRotation modelLeaf modelCommitteeRoot [] modelRotationStateRoot = false
    ∧ verifyCommitteeRotation modelLeaf modelCommitteeRoot
        (List.replicate 7 (ModelDigest.chunk 4)) modelRotationStateRoot = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### It runs (`#guard`): the gate discriminates on concrete data. -/

#guard verifyCommitteeRotation modelLeaf modelCommitteeRoot modelRotationBranch
  modelRotationStateRoot == true
#guard verifyCommitteeRotation modelLeaf (ModelDigest.chunk 56) modelRotationBranch
  modelRotationStateRoot == false
#guard verifyCommitteeRotation modelLeaf modelCommitteeRoot [] modelRotationStateRoot == false

#guard verifyFinalizedUpdate modelLeaf modelState goodUpdate == true
#guard verifyFinalizedUpdate modelLeaf modelState quorum342Update == true
#guard verifyFinalizedUpdate modelLeaf modelState subQuorum341Update == false
#guard verifyFinalizedUpdate modelLeaf modelState badFinalityUpdate == false
#guard verifyFinalizedUpdate modelLeaf modelState (emptyUpdate modelLeaf) == false
#guard verifyFinalizedUpdate modelLeaf forgedState goodUpdate == false

/-! ## §12 — Axiom hygiene: every theorem kernel-clean. The model leaf is PROVED (BLS
soundness AND both hash-fact carriers — `modelLeaf_hashPairCR` / `modelLeaf_uChunkInj`),
so nothing here rests on an unproven crypto assumption; a PRODUCTION instance's
`eth_no_forgery` rests on its visible, named `blsSound` leaf field and takes
`hashPairCR`/`uChunkInj` as its explicit CR hypotheses — structure fields and hypotheses
are invisible to `#assert_axioms` (which sees only `axiom`-keyword decls), which is
exactly why they are VISIBLE fields/arguments an auditor reads at the instance/use site.
The both-polarity pins (`modelLeaf_hashPairCR`/`modelLeaf_uChunkInj` vs
`collapseEthLeaf_not_hashPairCR`/`collapseEthLeaf_not_uChunkInj`, plus
`collapse_finality_not_binding`) prove the carriers are real discriminating hypotheses,
not `True` in disguise. -/

#assert_axioms finalizedRootSubtreeIndex_correct
#assert_axioms executionPayloadSubtreeIndex_correct
#assert_axioms nextSyncCommitteeSubtreeIndex_correct
#assert_axioms quorum_boundary
#assert_axioms mem_participants
#assert_axioms EthLeaf.pair_inj
#assert_axioms EthLeaf.chunk_inj
#assert_axioms reconstruct_binding
#assert_axioms htrHeader_inj
#assert_axioms finalized_header_binding
#assert_axioms committee_rotation_binding
#assert_axioms committee_rotation_fail_closed
#assert_axioms committee_rotation_discriminates
#assert_axioms collapse_committee_rotation_not_binding
#assert_axioms eth_no_forgery
#assert_axioms eth_fail_closed
#assert_axioms toAdapter_foreignFinal_eth
#assert_axioms modelBlsSound
#assert_axioms modelLeaf_hashPairCR
#assert_axioms modelLeaf_uChunkInj
#assert_axioms modelCryptoLeaf_hashCR
#assert_axioms collapseEthLeaf_not_hashPairCR
#assert_axioms collapseEthLeaf_not_uChunkInj
#assert_axioms collapse_finality_not_binding
#assert_axioms model_non_vacuous
#assert_axioms eth_gate_discriminates
#assert_axioms eth_forged_committee_rejected
#assert_axioms eth_valid_good
#assert_axioms eth_invalid_bad_finality
#assert_axioms eth_forged_committee_invalid
#assert_axioms eth_adapter_accepts_and_discharges
#assert_axioms eth_adapter_rejects_empty

#print axioms eth_no_forgery
#print axioms eth_gate_discriminates

end Dregg2.Bridge.LightClientEth
