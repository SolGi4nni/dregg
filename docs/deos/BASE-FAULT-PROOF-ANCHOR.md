# Base Fault-Proof Anchor — the plan to verify the LIVE Base L2 anchor

**Status:** design scout (no implementation). Closes the named residual in
`eth-lightclient/src/base.rs:45-54`: that module verifies the legacy
`L2OutputOracle` honest-oracle model; the live Base anchor is a resolved dispute
game tracked by an `AnchorStateRegistry`. This doc is the concrete, slot-level
plan to verify THAT — grounded against the Optimism specs, the contracts-bedrock
storage-layout snapshots, and (decisively) **live reads of Base's L1 contracts on
2026-07-12** via `eth_getStorageAt`/`eth_call` against Ethereum mainnet. Every
"validated live" claim below was reproduced against the chain during this scout.

---

## 0. The headline discovery: live Base is NOT classic CANNON anymore

The scout brief (and the residual note in `base.rs:45-54`) assumed the live
anchor is a classic `FaultDisputeGame` (CANNON, game type 0) with the
portal-era airgap. **Live Base in 2026-07 is two upgrades past that:**

| Fact (validated live 2026-07-12) | Value |
|---|---|
| `OptimismPortal` 0x49048044D57e1C92A77f79988d21Fa8fAF74E97e `version()` | `5.2.0` (post-Upgrade-14 layout: `anchorStateRegistry` at slot 62, old portal `respectedGameType` slot 59 is now a spacer still holding the Oct-2024 launch residue `0x672253a3‖00000000`) |
| `AnchorStateRegistry` (ASR) proxy | `0x909f6CF47ED12f010A796527F562BFc26c7F4e72`, `version()` = `3.7.0`, impl `0x4483f964f6711cB55F633820eD174e780369B99d` (verified source: **Base's fork**, `lib/contracts/src/dispute/AnchorStateRegistry.sol`, not upstream contracts-bedrock) |
| `DisputeGameFactory` (DGF) | `0x43edB88C4B80fDD2AdFF2412A7BebF9dF42cB40e` (same address as `base.rs:47` names) — ASR slot 1 points at it (validated live) |
| **respectedGameType** | **621** (`0x26d`) — ASR slot 6, offset 0 |
| retirementTimestamp | `0x6a15fbbf` = 1779825599 = 2026-05-26T19:59:59Z — ASR slot 6, offset 4 |
| Game type 621 implementation | `0x1bd8db5139Ba7aC9277684650c15e6E341761919` = **`AggregateVerifier` v0.1.0** (Blockscout-verified source, `lib/contracts/src/L1/proofs/AggregateVerifier.sol`, solc 0.8.15) — a **dual-attestation validity game**: every proposal is created WITH a TEE attestation or a ZK proof; a challenge is the counter-proof of the other type |
| Registered game impls | type 0 (permissionless CANNON) = **address(0) — deregistered**; type 1 (PERMISSIONED_CANNON) = `0x58bf355C5d4EdFc723eF89d99582ECCfd143266A` (fallback); type 621 = AggregateVerifier |
| `ASR.disputeGameFinalityDelaySeconds()` | **0** (raw 32-byte zero word — the registry-level airgap is literally zero; the finality windows live INSIDE the game: `FAST_FINALIZATION_DELAY = 1 days` with both proof types, `SLOW_FINALIZATION_DELAY = 5 days` with one, gating `resolve()` itself) |
| AggregateVerifier immutables | `TEE_VERIFIER = 0x1FbA0C57b07Af804A9717e51dec9CC27FBC12228`, `TEE_IMAGE_HASH = 0x58557c70…4d212a`, `ZK_VERIFIER = 0xB88D95bDf6972508942d184866890c1834219B75`, `ZK_RANGE_HASH = 0x505c97f1…88d677`, `ZK_AGGREGATE_HASH = 0x001df6df…243a3b`, `CONFIG_HASH = 0x1607709d…5f3c57`, `L2_CHAIN_ID = 8453`, `BLOCK_INTERVAL = 600`, `INTERMEDIATE_BLOCK_INTERVAL = 30`, bond (`DGF.initBonds(621)`) = 0.05 ETH |

**The good news for the plan:** the *storage-proof trust chain* is essentially
the same for the generic OP-stack `FaultDisputeGame` model and Base's live
AggregateVerifier model — same factory slots, same GameId packing, same
game slot-0 packing (`createdAt ‖ resolvedAt ‖ status`), same ASR predicate.
The plan below is written against the ASR's validity predicate
(`isGameClaimValid`, which we reproduced from the live verified source and
whose getters we confirmed return `true` on the live anchor game), so it covers
Base-today AND any OP-stack fault-proof chain, parameterized by game type.

**And the decisive reuse fact, validated live:** the type-621 game's
`rootClaim` is STILL a v0 OP output root. We recomputed
`keccak256(0³² ‖ stateRoot ‖ messagePasserStorageRoot ‖ blockHash)` for Base
block 48306960 (state root `0x0ae03ce0…f35f142`, message-passer storage root
`0xba3203fb…1ebe0e` from `eth_getProof` on `0x4200…0016`, block hash
`0xcd905ee2…650ae7`) and got exactly the live game's `rootClaim`
`0x24da26cd52eef56f2433564bac025733b4c24e4ef65b4e8b33ee80369bafdf10`.
So `verify_op_output_root` (`base.rs:200-222`) and everything downstream of it
carry over **unchanged**.

---

## 1. THE TRUST CHAIN

The fault-proof analog of `verify_l1_committed_output_root`
(`base.rs:317-381`). Input: a light-client-verified `FinalizedExecution`
(`finality.rs:85-135`) giving the finalized L1 `state_root`. Output: a trusted
`(output_root, l2_block_number)` — the same `L1CommittedOutput`
(`base.rs:261-268`) the existing composition consumes.

All storage proofs are EIP-1186 opens via the existing
`verify_evm_account_proof` (`evm.rs:165`) / `verify_evm_storage_slot`
(`evm.rs:200-219`) machinery. Ordered checks:

### Link 1 — ASR account proof
`l1.execution_state_root() --MPT--> ASR account (0x909f6CF4…7F4e72)`, binding
`asr_account.storage_hash`. (Note the slots below live in the PROXY's storage —
an account proof of the proxy address is exactly right. The impl address at the
EIP-1967 slot `0x360894a1…382bbc` should also be proven and pinned; see Link 7
and Residual R3.)

### Link 2 — respected game type + retirement (ASR slot 6)
One storage proof of ASR **slot 6** =
`uint64 retirementTimestamp (offset 4) ‖ GameType respectedGameType (uint32, offset 0)`,
i.e. word = `(retirementTimestamp << 32) | gameType`.
*Layout source:* upstream develop snapshot
`snapshots/storageLayout/AnchorStateRegistry.json` (respectedGameType slot 6
offset 0, retirementTimestamp slot 6 offset 4) — **validated live**: slot 6 reads
`0x…6a15fbbf0000026d` and `eth_call respectedGameType()/retirementTimestamp()`
decode to 621 / 1779825599. Checks:
- `game_type == respected_game_type` (respected-NOW; the respected-at-creation
  check is Link 6's `wasRespectedGameTypeWhenCreated` byte, mirroring
  `ASR.isGameRespected` which reads only that flag).
- retirement (used in Link 6): `game.createdAt > retirementTimestamp`
  (the live ASR source: `isGameRetired ⇔ createdAt <= retirementTimestamp`;
  specs "anchor-state-registry" agrees: created *at or before* the boundary is
  retired).

### Link 3 — DGF account proof
`l1.execution_state_root() --MPT--> DGF account (0x43edB88C…cB40e)`, binding
`dgf_account.storage_hash`. Also: the ASR's `disputeGameFactory` (slot 1) should
be proven equal to this DGF address (one more storage proof; validated live —
slot 1 holds `0x43edb88c…`) so the factory identity is L1-anchored, not config.

### Link 4 — THE BINDING: `_disputeGames[UUID]` (DGF slot 103 mapping)
This is the keystone that replaces the `l2Outputs` array math, and it is
*better* than reading the game's own state, because the mapping KEY commits the
entire claim content:

```
UUID     = keccak256(abi.encode(uint32 gameType, bytes32 rootClaim, bytes extraData))
         = keccak256( pad32(gameType) ‖ rootClaim ‖ 0x…60 ‖ pad32(len) ‖ extraData ‖ zero-pad to 32 )
slot     = keccak256(UUID ‖ pad32(103))          // mapping value slot
value    = GameId = pad-to-32( gameType(4 bytes) ‖ createdAt-timestamp(8 bytes) ‖ gameProxy(20 bytes) )
                    // uint256(gameType) << 224 | uint256(timestamp) << 160 | uint160(proxy)
```

*Layout source:* contracts-bedrock `DisputeGameFactory` snapshot —
`_disputeGames` mapping(Hash ⇒ GameId) at **slot 103**, `_disputeGameList`
GameId[] at **slot 104** (`gameImpls` 101, `initBonds` 102; stable from
op-contracts v1.x through develop). `getGameUUID` and `LibGameId.pack` per
`DisputeGameFactory.sol` / `lib/LibUDT.sol`. **Validated live end-to-end**: for
the anchor game, `getGameUUID(621, rootClaim, extraData)` =
`0x72ec4e4c…8eb105`, and raw `eth_getStorageAt(DGF, keccak256(uuid‖103))` =
`0x0000026d ‖ 000000006a4c9603 ‖ 15f3835a66b1c0a9c4327fd2894d768142c73626` =
GameId(621, createdAt=1783404035, game address). Also validated the list form:
`_disputeGameList[17407]` at `keccak256(pad32(104)) + 17407` unpacks identically.

One storage proof of this slot therefore binds, under the finalized L1 root:
**gameType + rootClaim + extraData → the unique game proxy address** the factory
created for exactly that claim (`ASR.isGameRegistered` does the same check via
`disputeGameFactory.games(...)`). The claimed L2 block number rides IN
`extraData`: for AggregateVerifier,
`extraData = pad32(l2BlockNumber) ‖ parentGame(20 bytes) ‖ intermediateOutputRoots(20 × 32 bytes)`
(per `initializeWithInitData`'s CWIA layout comment; live anchor game:
first word `0x2e11b10` = 48306960, last 32 bytes == rootClaim); for classic
`FaultDisputeGame`, `extraData = abi.encode(uint256 l2BlockNumber)` (32 bytes).
The verifier parses the block number out of the proven `extraData` — the exact
analog of the `l2Outputs` metadata slot in `base.rs:365-374`, and like it, the
snapshot height is L1-anchored, never caller-claimed.

Fail-closed notes: a GameId of 0 (absent key) means "no such game" — that is a
*zero/absence* read, see the new exclusion-proof helper in §2. The unpacked
proxy address and createdAt from the GameId are the authoritative ones.

### Link 5 — game account proof
`l1.execution_state_root() --MPT--> game proxy account` (address from Link 4's
GameId), binding `game_account.storage_hash` **and `code_hash`**. The code hash
matters: the game is a Solady/CWIA clone whose immutable args (creator,
rootClaim, l1Head, extraData) are baked into the proxy bytecode, and whose
delegate target (the AggregateVerifier impl, carrying `TEE_IMAGE_HASH`,
`ZK_*`, `CONFIG_HASH`, `ANCHOR_STATE_REGISTRY`, the finalization delays) defines
the game's semantics. Pinning `code_hash` against a recomputed CWIA proxy
bytecode (impl address + args) gives a second, independent binding of
rootClaim/extraData AND pins the semantics version.

**Residual R3: CLOSED (2026-07-12).** `cwia_proxy_code_hash(BASE_AGGREGATE_VERIFIER_IMPL,
creator ‖ rootClaim ‖ l1Head ‖ extraData)` reconstructs the Solady LibClone CWIA runtime
bytecode and reproduces the live game's real code hash **byte-exactly** (KAT
`kat_cwia_code_hash_reconstructs` against the L1-account-proof-bound value); Link 5 now
refuses unless the proven `code_hash` recomputes from the pinned impl + this game's args, so
a look-alike contract with the same slot-0/DEFENDER_WINS layout but non-CWIA bytecode is
REFUSED (`synthetic::look_alike_game_code_rejects`). Remaining (lower): the impl address +
CWIA template bytes are documented constants — they change only on an OP-stack upgrade
(fail-closed → explicit re-pin); the impl's own bytecode is not separately account-proven
(immutable post-Cancun, so the address IS the semantics pin — same class as the oracle-address
trust). See `eth-lightclient/src/base_fault_proof.rs`.

### Link 6 — game resolution state (game slot 0)
One storage proof of game **slot 0** =
`createdAt(u64 @0) ‖ resolvedAt(u64 @8) ‖ status(u8 @16) ‖ initialized(bool @17) ‖ wasRespectedGameTypeWhenCreated(bool @18)`.
*Layout source:* AggregateVerifier verified source (state-var order,
`AggregateVerifier.sol` lines ~118-135); **validated live**: slot 0 of the
anchor game reads `0x…010102_000000006a532d8f_000000006a4c9603` — createdAt
1783404035 (2026-07-07T06:00:35Z), resolvedAt 1783836047 (2026-07-12T06:00:47Z),
status 2, initialized 1, wasRespectedGameTypeWhenCreated 1, byte-exact match
with the `eth_call` getters. For classic `FaultDisputeGame` the same slot-0
packing holds for createdAt/resolvedAt/status/initialized (snapshot, v1.8.0 and
develop), but `wasRespectedGameTypeWhenCreated` is **elsewhere and
version-dependent** (absent in v1.8.0; slot 10 offset 0 in develop) — see
Unpinned U2. Checks (mirroring `ASR.isGameResolved/isGameRespected/isGameRetired`
+ the `DEFENDER_WINS` arm of `isGameClaimValid`, all quoted from the live
verified source):
- `status == 2` (**DEFENDER_WINS**; GameStatus enum: 0 IN_PROGRESS,
  1 CHALLENGER_WINS, 2 DEFENDER_WINS)
- `resolvedAt != 0`
- `wasRespectedGameTypeWhenCreated == 1`
- `createdAt > retirement_timestamp` (Link 2)
- `createdAt` consistency: equals the timestamp packed in Link 4's GameId
  (both proven; cheap cross-tooth).

### Link 7 — not blacklisted (ASR slot 5 mapping, EXCLUSION proof)
`disputeGameBlacklist` is `mapping(IDisputeGame ⇒ bool)` at ASR **slot 5**
(develop snapshot; Base's live ASR source has the same var order — systemConfig
slot 0 offset 2, disputeGameFactory 1, anchorGame 2, startingAnchorRoot 3-4,
blacklist 5, respectedGameType/retirementTimestamp 6 — slots 0,1,2,6 validated
live by raw reads). Check: slot `keccak256(pad32(game) ‖ pad32(5))` is **zero** —
which in the EVM storage MPT means the key is ABSENT, so this is an
**exclusion proof**, not a value proof (live read confirms the zero word). This
needs a new helper (§2): `verify_evm_storage_slot` as written
(`evm.rs:200-219`) proves `Some(rlp(value))` and cannot express absence.

### Link 8 — the airgap / finality-window predicate
`l1_finalized_timestamp - resolvedAt > DISPUTE_GAME_FINALITY_DELAY_SECONDS`
(strict `>`, mirroring `isGameFinalized`'s `<=`-reject in the live source).
Two grounding facts:
- The delay is an **immutable in the ASR impl** (constructor-set,
  `AnchorStateRegistry.sol:80-81` in the live source), NOT a storage slot — so
  it is *configuration pinned by the ASR impl code hash*, and **on live Base it
  is 0**.
- On live Base the real anti-fraud windows are enforced INSIDE the game before
  `resolve()` can run (`gameOver()` gates on `expectedResolution` =
  createdAt/proof-time + 1 day if both TEE+ZK proofs agree, 5 days if only one;
  a nullified proof pushes it out by another 5 days) — so `resolvedAt != 0 ∧
  status == DEFENDER_WINS` already implies the in-game window elapsed on L1.
- `l1_finalized_timestamp` must come from the light client. `FinalizedExecution`
  (`finality.rs:85-91`) does not carry the execution timestamp today, but
  `ExecutionPayloadHeader` already parses it (`execution.rs:58`) — an additive
  field + accessor (every `new_unchecked` call site updates; it's greppable by
  design, `finality.rs:94-113`).
- **Policy delay (recommended):** because the on-chain registry delay is 0, the
  verifier should additionally enforce a caller-supplied
  `policy_finality_delay` (e.g. ≥ the guardian's realistic blacklist-response
  window) — encoded as `l1_time > resolvedAt + max(asr_delay, policy_delay)`.
  This is OUR conservatism knob, not a protocol parameter; see Trust Delta.

### Link 9 — output-root opening + L2 holding (existing, unchanged)
`verify_op_output_root(version=v0, l2_state_root, l2_withdrawal_storage_root,
l2_block_hash, root_claim)` (`base.rs:200-222`) — **validated live** against the
type-621 anchor game's rootClaim (§0). Then `verify_erc20_holding`
(`evm.rs:237`) against the bound L2 state root at the L1-proven L2 block number
from Link 4's `extraData`, exactly as `verify_base_erc20_holding` does at
`base.rs:443-459`.

Trust-chain summary (each arrow = a fail-closed check):

```
FinalizedExecution (finality.rs, unforgeable)
  ├─(L1 acct proof)→ ASR.storage_hash ─→ slot 6: respectedGameType=621, retirementTs   [Link 1,2]
  │                                  └→ slot 5 mapping: blacklist[game] ABSENT          [Link 7]
  │                                  └→ slot 1: disputeGameFactory == DGF               [Link 3]
  ├─(L1 acct proof)→ DGF.storage_hash ─→ slot keccak(UUID‖103): GameId(type,ts,game)    [Link 4]
  │                     where UUID = keccak(abi.encode(type, rootClaim, extraData))
  ├─(L1 acct proof)→ game.storage_hash (+code_hash pin) ─→ slot 0:                      [Link 5,6]
  │                     status==DEFENDER_WINS ∧ resolvedAt≠0 ∧ respected@creation
  │                     ∧ createdAt > retirementTs
  ├─ l1_time > resolvedAt + max(asr_delay=0, policy_delay)                              [Link 8]
  └─→ (rootClaim, l2BlockNumber from extraData) = L1CommittedOutput
        └→ verify_op_output_root → l2_state_root → verify_erc20_holding                 [Link 9]
```

---

## 2. WHAT REUSES vs WHAT IS NEW

**Reuses unchanged:**
- `FinalizedExecution` / `verify_finalized_update` (`finality.rs:187-224`) — the
  L1 finality authority, as-is (plus one additive timestamp field, below).
- `verify_evm_account_proof` (`evm.rs:165`) — Links 1, 3, 5.
- `verify_evm_storage_slot` (`evm.rs:200-219`) — Links 2, 3(slot 1), 4, 6.
- `verify_op_output_root` / `compute_op_output_root_v0` (`base.rs:179-222`) —
  Link 9, live-validated against the type-621 rootClaim.
- `verify_erc20_holding` (`evm.rs:237`) and the `L1CommittedOutput` /
  `L2StateCommitment` shapes (`base.rs:261,387`) — the composition tail of
  `verify_base_erc20_holding` (`base.rs:418-460`) is reused verbatim; only the
  anchor-opening head is swapped.

**New pieces (all in a new `eth-lightclient/src/base_fault_proof.rs`, or a
`fault_proof` section of `base.rs`):**
1. `verify_evm_storage_slot_absent(storage_hash, slot_key, proof)` in `evm.rs` —
   the exclusion-proof twin of `verify_evm_storage_slot` (alloy-trie
   `verify_proof` with expected `None`; a zero-valued slot is an absent MPT
   key). Needed for Link 7. Adversarial tests: an absence proof for a PRESENT
   key must refuse; a truncated proof must refuse.
2. `game_uuid(game_type, root_claim, extra_data)` — the
   `keccak256(abi.encode(uint32, bytes32, bytes))` head/tail encoding (offset
   word `0x60`, length word, zero-padded tail), plus
   `dispute_games_mapping_slot(uuid) = keccak256(uuid ‖ pad32(103))` and
   `GameId::unpack(word) -> (game_type: u32, timestamp: u64, address: [u8;20])`.
   KATs from the live fixture in §4.
3. `parse_extra_data_l2_block_number(game_type_profile, extra_data)` — first
   32-byte word as `uint256` (both the FDG and AggregateVerifier layouts put
   `l2BlockNumber` first; AggregateVerifier additionally carries parent +
   intermediate roots, which we do not interpret beyond UUID binding).
4. Game slot-0 unpacking + the resolution predicate (Link 6), with the packed
   word recomputed from claimed fields exactly like `pack_output_meta`
   (`base.rs:253-255`) does — prove the WHOLE word, parse nothing off-proof.
5. The airgap predicate (Link 8) + an additive
   `FinalizedExecution::execution_timestamp()` (plumb
   `ExecutionPayloadHeader.timestamp`, `execution.rs:58`, through
   `verify_finalized_update` and `new_unchecked`).
6. A `FaultProofAnchorParams` config carrying: expected ASR address, expected
   respected game type, the pinned game-impl/proxy `code_hash`s, the ASR-impl
   pinned `dispute_game_finality_delay` (0 on Base), and `policy_finality_delay`.
   New error enum `FaultProofAnchorError` in the `BaseProofError` style
   (`base.rs:91-129`) — one variant per link, fail-closed.

Illustrative sketch (shape only — NOT implementation):

```rust
pub struct FaultProofAnchor {
    // Link 1-2, 7: ASR
    pub asr_account: AccountClaim, pub asr_account_proof: Vec<Vec<u8>>,
    pub respected_slot6_proof: Vec<Vec<u8>>,   // retirementTs ‖ respectedGameType
    pub dgf_binding_slot1_proof: Vec<Vec<u8>>, // ASR.disputeGameFactory
    pub blacklist_absence_proof: Vec<Vec<u8>>,
    // Link 3-4: DGF
    pub dgf_account: AccountClaim, pub dgf_account_proof: Vec<Vec<u8>>,
    pub game_id_slot_proof: Vec<Vec<u8>>,      // _disputeGames[uuid] -> GameId
    // Link 5-6: the game
    pub game_account: AccountClaim, pub game_account_proof: Vec<Vec<u8>>,
    pub game_slot0_proof: Vec<Vec<u8>>,
    pub created_at: u64, pub resolved_at: u64, // status/flags recomputed+proven
    // The claim being opened (the UUID preimage):
    pub game_type: u32, pub root_claim: [u8; 32], pub extra_data: Vec<u8>,
}

pub fn verify_l1_fault_proof_output_root(
    l1_finalized: &FinalizedExecution,
    params: &FaultProofAnchorParams,
    anchor: &FaultProofAnchor,
) -> Result<L1CommittedOutput, FaultProofAnchorError>;
// then: verify_op_output_root + verify_erc20_holding, exactly as base.rs:432-459
```

---

## 3. THE HONEST TRUST DELTA

What each anchor model asks you to believe, beyond L1 finality + keccak/MPT:

- **Honest-oracle (`base.rs`, committed):** the `PROPOSER` role posts only true
  roots and the `CHALLENGER` role deletes bad ones. A trusted committee, full
  stop. The light client verifies *bookkeeping*, not correctness.
- **Generic OP fault proofs (classic FDG/CANNON):** permissionless proposals;
  correctness is enforced by the bisection game ⇒ the assumption becomes
  **challenger liveness inside the window**: at least one honest, funded,
  censorship-resistant challenger acts within the game's chess-clock (3.5 days)
  + the registry airgap. A `DEFENDER_WINS` + airgap-elapsed game is final
  *given* that liveness. Plus the guardian's blacklist/retirement/pause powers
  (safety valve AND a trusted key).
- **Live Base (AggregateVerifier, type 621):** the model shifted from
  fraud-window-only toward **validity-at-creation**: a game cannot even
  initialize without a TEE attestation or ZK proof of the state transition from
  the parent game's root (`initializeWithInitData` → `_verifyProof`), and
  cannot resolve DEFENDER_WINS before its in-game window (1d both-proofs / 5d
  single-proof) with `PROOF_THRESHOLD = 1` met and an unbroken DEFENDER_WINS
  parent chain (`resolve()` propagates parent CHALLENGER_WINS). The assumption
  set becomes: **soundness of (AWS Nitro TEE attestation for `TEE_IMAGE_HASH`)
  OR-challenged-by (the ZK verifier for `ZK_RANGE/AGGREGATE_HASH`)**, plus the
  same governance keys. The challenger-liveness assumption is not gone — a
  wrong TEE proposal still needs a ZK challenge inside the 5-day window — but
  the challenge is now *one proof transaction*, not a bisection marathon, and a
  both-proofs proposal finalizes in 1 day.
- **Registry airgap = 0 (live-read fact):** the classic "guardian has N seconds
  after resolution to blacklist" window is currently ZERO at the registry
  level on Base. Encode "sufficiently final" as the verifiable predicate
  `l1_finalized_time > resolvedAt + max(asr_delay, policy_delay)` — the
  `asr_delay` proves what the CHAIN enforces (0), the `policy_delay` is our own
  extra conservatism, and the doc/API must not launder one as the other.
- **What the light client checks vs. inherits:** every predicate in §1 is a
  faithful storage-level mirror of the live `ASR.isGameClaimValid` (we
  confirmed all five getters — registered/respected/not-blacklisted/not-retired/
  finalized — return `true` for the live anchor game). What we *inherit without
  re-verifying* is the game/ASR **code semantics** (that `resolve()` really
  gates on proofs and parent status) — pinned by code-hash (Link 5, Residual
  R3), the same way `base.rs` inherits `L2OutputOracle` semantics from its
  address. One check we deliberately do NOT mirror: `isGameProper`'s `paused()`
  (it reads `SystemConfig.paused()`, a Base-fork slot we have not pinned —
  Unpinned U4; pause is a temporary guardian veto, and a paused-at-T chain
  would only make on-chain acceptance MORE conservative than ours at T — named
  honestly as a divergence, mitigable later by one more storage proof).

---

## 4. THE SMALLEST FIRST BUILD INCREMENT

**Goal:** `verify_l1_fault_proof_output_root` green end-to-end against ONE real
resolved Base game, fixtures captured from mainnet.

**The fixture game (all values validated live 2026-07-12):**
- Game **index 17049** in `_disputeGameList` (found by binary search on
  creation timestamps; `gameCount()` = 17408 at scout time)
- Game proxy: `0x15F3835a66b1C0A9C4327Fd2894d768142C73626` — the CURRENT
  `ASR.anchorGame` (ASR slot 2), so it is by construction a claim-valid game
- gameType 621, createdAt 1783404035 (2026-07-07), resolvedAt 1783836047
  (2026-07-12), status DEFENDER_WINS(2), wasRespectedGameTypeWhenCreated true
- rootClaim `0x24da26cd52eef56f2433564bac025733b4c24e4ef65b4e8b33ee80369bafdf10`
  = v0 output root of **Base block 48306960**; parent game
  `0xa56c6a0cb4b535071cc0f7858f7549174cc04bd7` (rootClaim = this game's
  `startingOutputRoot.root`, slot 1; slot 2 = 48306360 = 48306960 − 600 ✓)
- UUID `0x72ec4e4cfe114031a467583b88f453785a4c6aa95de48fadcd6ddefbda8eb105`;
  extraData = 692 bytes (`pad32(48306960) ‖ parent ‖ 20 intermediate roots`,
  last = rootClaim)

**Steps:**
1. **Fixture capture** (script, one shot, pin the L1 block number): choose a
   finalized L1 block T with timestamp > resolvedAt; `eth_getProof` at T for
   (a) ASR `0x909f…4e72` with slots `[5-mapping key for the game, 1, 6]`,
   (b) DGF `0x43ed…B40e` with slot `[keccak256(uuid‖103)]`,
   (c) game `0x15F3…3626` with slot `[0]`;
   plus Base-side `eth_getProof` at block 48306960 for the ERC-20 holding and
   `0x4200…0016` (the withdrawal root is already in hand above). Serialize as
   JSON fixtures like the existing base.rs test corpus.
2. **KAT tests first** (pure, no proofs): `game_uuid` and
   `dispute_games_mapping_slot` against the §4 constants; `GameId::unpack`
   against `0x0000026d‖000000006a4c9603‖15f3…3626`; slot-0 unpack against
   `0x…010102‖000000006a532d8f‖000000006a4c9603`; slot-6 unpack against
   `0x…6a15fbbf0000026d`.
3. `verify_evm_storage_slot_absent` in `evm.rs` + its adversarial tests
   (absence-of-present-key refused).
4. `verify_l1_fault_proof_output_root` (Links 1-8) + polarity tests per link:
   flipped status byte (1 = CHALLENGER_WINS) refused; resolvedAt = 0 refused;
   createdAt ≤ retirementTimestamp refused; wrong game type refused; a
   blacklist-PRESENT fixture (synthesized trie) refused; tampered UUID
   preimage (any byte of extraData) refused — the UUID changes, the mapping
   slot proof fails; `l1_time ≤ resolvedAt + policy_delay` refused.
5. Compose `verify_base_erc20_holding_fault_proof` = Links 1-8 +
   `verify_op_output_root` + `verify_erc20_holding`, minting
   `HoldingTrust::ConsensusProven` exactly like `base.rs:458`. The L1-finality
   fixture can enter via `FinalizedExecution::new_unchecked` initially (as the
   existing tests do), with the timestamp field added in the same lane.

**Not in increment 1:** CWIA code-hash *recomputation* (pin the literal
`code_hash` from the fixture instead), the pause-slot proof, classic-FDG
game-type profile (add as a parameterized second profile when an OP-mainnet
anchor is wanted), multi-game parent-chain walking (the ASR predicate
deliberately doesn't require it; see R5).

---

## 5. NAMED RESIDUALS

- **R1 — Game-type spoofing / permissionless creation:** anyone can call
  `DGF.create` for any REGISTERED type with the 0.05 ETH bond. Defenses in the
  plan: the UUID mapping binds the game to its claimed `gameType`; Link 2+6
  require respected-now AND respected-at-creation; Link 5's code-hash pin binds
  the proxy to the audited impl (`gameImpls[621]`). Residual: if governance
  registers a NEW type or rotates `respectedGameType`, the light client's
  pinned expectations go stale — fail-closed by construction (checks refuse),
  needs an explicit re-pin, which is the correct failure mode.
- **R2 — Bond/incentive assumptions:** the 0.05 ETH bond + DelayedWETH refunds
  incentivize challenges but prove nothing cryptographic. The light client
  should treat bonds as liveness lubricant, not a verified property (we do not
  prove `initBonds`).
- **R3 — Code-hash pinning depth:** increment 1 pins literal code hashes
  (fixture constants). Full defense = recompute the Solady CWIA proxy bytecode
  from (impl, creator, rootClaim, l1Head, extraData) so the account-proof
  `code_hash` independently re-binds the claim, and pin the ASR/impl hashes
  behind the EIP-1967 slots. Until then, a contracts upgrade (ProxyAdmin) both
  changes semantics AND breaks our pins — again fail-closed, but noisy.
- **R4 — Upgrade/governance keys:** `setRespectedGameType`,
  `updateRetirementTimestamp`, `blacklistDisputeGame` are
  guardian-only (`_assertOnlyGuardian` → `systemConfig.guardian()`); ProxyAdmin
  can swap every implementation. With the registry airgap at 0, guardian
  protection after resolution is best-effort. This is the irreducible
  governance trust of ANY L2 anchor; the light client's job is to make it
  VISIBLE (pinned hashes + the policy delay), not to remove it.
- **R5 — Parent-chain validity:** `isGameClaimValid` (and we) check ONE game;
  the parent chain's correctness is enforced by game code (`resolve()`
  propagates parent CHALLENGER_WINS; init proves the transition from the
  parent's root) — inherited via R3's semantics pin, not re-verified per-link.
- **R6 — TEE/ZK verifier soundness:** `TEE_VERIFIER` (Nitro attestation
  verification) and `ZK_VERIFIER` + program hashes are the new cryptographic
  floor. Named primitive trust — terminal for this lane, in the same class as
  BLS/keccak trust elsewhere in the crate.

## 6. Pinned vs UNPINNED (honesty ledger)

**Pinned (live-validated raw storage, 2026-07-12):** DGF slots 103/104 math +
GameId packing + UUID formula; ASR slots 0/1/2/5/6 layout + values; game slot 0
packing (type 621); rootClaim = v0 output root (recomputed); airgap = 0;
`isGameClaimValid` semantics (verified source + live getters).

**Pinned from snapshots only (not live-validated):** classic FDG slot-0 packing
(identical in v1.8.0 + develop snapshots); portal-era v1.8.0 layout
(respectedGameType/blacklist at portal slots 59/58) for chains still there.

**Unpinned / version-dependent (named):**
- **U1:** Base's contracts are Base's FORK (`base-org` `lib/contracts` tree,
  AggregateVerifier 0.1.0, ASR "3.7.0") — upstream OP snapshots matched
  everywhere we checked, but future Base releases can diverge from upstream;
  re-validate slots per release (the fixture harness makes this cheap).
- **U2:** classic FDG `wasRespectedGameTypeWhenCreated` location: absent in
  op-contracts v1.8.0, slot 10 offset 0 in develop — MUST be re-pinned per
  deployment when the FDG profile is built.
- **U3:** AggregateVerifier slots ≥ 1 (startingOutputRoot, bond fields,
  `expectedResolution` at ~slot 7) — read from source, only slots 1-2
  spot-checked live; not needed for the trust chain.
- **U4:** `SystemConfig.paused()` slot on Base's fork — not pinned; the pause
  check is consciously omitted (see §3) until pinned.
- **U5:** whether `respectedGameType = 621` / the AggregateVerifier system has
  a published spec (the Optimism specs cover CANNON-family fault proofs and the
  ASR; type 621's semantics were grounded from verified on-chain source only).
