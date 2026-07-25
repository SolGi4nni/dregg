# Interchain / Cross-Chain Surface Audit — 2026-07-25

REALITY GATE: **nothing is on mainnet.** Only DreggSettlement + its Groth16 verifier are deployed — to Base
Sepolia TESTNET (84532), verifying a FIXTURE proof under a single-party dev-ceremony trusted setup. Every
custody contract + bridge mint path is test/local only. So CRITICAL/HIGH below are PRE-LAUNCH LATENT holes, not
live-drain — but several go live the moment the corresponding daemon/contract deploys. Excluded: market/dark-amm/fhegg.

VERDICT: MIXED, clean split. The NON-CUSTODIAL proof-of-holdings half is SOUND (genuine LC verification on
ETH/Base, Cosmos, Solana-anchored — real sigs/thresholds/inclusion proofs, adversarially tested, fail-closed;
caveats = honestly-surfaced composition duties + the universal STARK/FRI + dev-ceremony floor). The interop-
messaging half (Hyperlane/LayerZero) is correctly MOSTLY-STUB — real standard-conforming adapters deliberately
fail-closed/inert (isProvenMessageRoot hard-coded false; the one operator-trust forgery hole there was already
FOUND+REMOVED). The CUSTODY/MINT half is where the exposure is — TRUSTED (bridge-hack-shaped) in the classic places.

## Discovery map (5 trust models)
A. NON-CUSTODIAL proof-of-holdings (read-only, SOUND): eth-lightclient (real BLS 2/3-of-512, SSZ finality+exec,
   EIP-1186 incl+strict exclusion), cosmos-lightclient (audited tendermint verifier), bridge solana_trustless
   (stake-weighted rooted Ed25519, WS-anchored, 3 value holes closed+red-teamed), dregg-interchain-gov (the
   compiled join), dregg-pay/multichain (non-custodial treasury view).
B. CUSTODY (funds move): DreggVault.sol (no admin/upgrade/drain; SP1-STARK-proof + isProvenRoot gated),
   cosmos-lock (isProvenRoot AND M-of-N ed25519 oracle multisig), dregg-pay/hd+sweeper (FULLY CUSTODIAL HD model),
   turn/executor/bridge_ledger.rs (the dregg-side mint; double-mint+conservation sound but trusts a caller bool).
C. INTEROP (Hyperlane/LayerZero): DreggProofISM.sol + DreggDVN.sol (standard-conforming, Nomad-hardened, but
   attest NOTHING today — isProvenMessageRoot=false, fail-closed); dregg-deploy/gate.rs = a doc-comment only.
D. STATE ORACLE: DreggSettlement.sol (real gnark Groth16, DEPLOYED Sepolia fixture), DreggStateOracle.sol
   (inclusion sound but sub-roots operator-attested), the socket contracts (demo), cosmos-settlement (hand-written
   2nd Groth16 verifier — divergence risk).
E. NOT cross-chain (disambiguated): dregg-oracle=zkTLS web-fact; lightclient/=dregg self-verifier; sandstorm-bridge
   =app sandbox; starbridge*=deos UI; dregg-sdk-net=node p2p.

## Findings (severity)
- **#1 CRITICAL-latent — bridge/src/ethereum_relayer.rs:606,619 hard-codes consensus_verified:true** over
  RPC-supplied logs/receipts (no LC, no MPT-vs-state-root, no beacon sig). A lying/MITM/compromised ETH RPC
  fabricates a Deposit log + receipt + finalized head → mints attacker $DREGG; the escrow leg hard-codes true too
  → conservation draws against fabricated backing; each forged lock_id is a fresh nullifier so replay-defense
  doesn't help. THE textbook bridge-oracle drain. Latent (unwired to a live daemon; test drives the mint). FIX:
  route through the same fail-closed dial the Solana path uses (ConditionalInterchainAdapter/reached_consensus) so
  consensus_verified is DERIVED from a real verdict (Rpc→false), backed by the already-sound eth-lightclient. The
  ETH leg asserts trust where Solana fail-closes — an inconsistency. Do before the relayer deploys.
- #2 HIGH — ethereum_relayer.rs:840 storage_binds_deposit reads eth_getProof but does NOT verify the MPT proof
  (RPC-value vs RPC-amount, zero assurance). Contributory to #1.
- #3 HIGH — dregg-pay/hd.rs+sweeper.rs: single HD seed derives all user keys, operator sweeps unilaterally (fully
  custodial by design, documented interim). Seed leak/rogue op drains everyone.
- #4 HIGH — cosmos-lock/src/lib.rs:207: escrow release binds via M-of-N ed25519 ORACLE multisig (+ isProvenRoot),
  NO Merkle inclusion of the leg into the proven root. Trust asymmetry vs the EVM twin (which uses an SP1 fill
  proof). Oracle-key compromise → release any escrow to any recipient. FIX: move to the EVM's fill-proof model.
- #5 HIGH — bridge/midnight_observer.rs:342: re-executing observer trusts RPC GRANDPA finalized-head; mint via
  federation quorum, no LC/threshold/ZK. TRUSTED-MIRROR.
- #6 MED-HIGH — DreggStateOracle.sol:152: sub-roots (balance/nullifier/commitments/heap) OPERATOR-ATTESTED, only
  top root proof-bound. Keep out of any value-bearing consumer until the apex exposes sub-root lanes.
- #7 MED — bridge/midnight_inclusion.rs:31: Merkle over a BLAKE3 PLACEHOLDER (TODO(mirror-hash)), not real
  Poseidon2 — tautology, binds nothing (STUB, not a live gate).
- #8 LOW — bridge/mina.rs:214: Kimchi verify removed as vacuous; now a BLAKE3 tag over the proof's own bytes
  (self-referential STUB, no live mint path).
- #9 MED — chain/src/bridge.rs:221+listener.rs:216: EVM Base deposit-mirror watches eth_getLogs (no inclusion
  proof) at 2 confirmations (reorg); note-creation a TODO stub (mints nothing yet).
- #10 MED — bridge/solana_mirror.rs:21: legacy threshold-ed25519 federation-oracle mint (superseded by solana_trustless).
- #11 MED — cosmos-settlement/verifier.rs: hand-written 2nd Groth16 verifier vs canonical gnark/Solidity —
  divergence risk (generate-from-source or differentially fuzz).
- #12 MED — DreggVault.sol:63: on-chain note tree keccak256 PLACEHOLDER; circuit proves Poseidon2 (agree only
  because the federation mirrors deposits). Documented pending Poseidon2 tree.
- **#13 HIGH — eth-lightclient composition boundary**: verify-core SOUND but committee pubkeys / attested root are
  BARE CALLER ARGS; no in-crate weak-subjectivity store. The dregg integration MUST pin a genesis committee +
  genesis_validators_root WS checkpoint and only advance via verify_committee_update over a verify_finalized_update
  state root — else an RPC-supplied 512-key committee mints ConsensusProven (BLS floor goes vacuous). Audit the store code.
- #14 LOW — bridge/solana_feed.rs:209: mainnet evidence feed "DESIGNED not built" → every Solana lock stays
  consensus_verified=false (safely inert).
- #15 INFO — turn/executor/bridge_ledger.rs:270: consensus_verified is a caller bool re-verified nowhere here (the
  seam #1 exploits; double-mint + conservation are genuinely sound).

## Top 5 (dispatch order)
1. Fix the ETH relayer (#1) — route through the fail-closed dial + eth-lightclient. THE one sharp defect.
2. Pin+chain the eth-lightclient trust root at the integration (#13).
3. Close the Cosmos custody trust asymmetry (#4) — SP1 fill-proof like the EVM twin.
4. Label Midnight/Mina honestly + gate them (#5,#7,#8) — no mint path wired; don't call stubs "verified".
5. Tidy debt: #12 keccak/Poseidon2 vault, #11 hand-written Cosmos verifier, #10 legacy solana_mirror, #9 chain/bridge stub.

SOUND (stated explicitly): cosmos-lightclient (KATs both polarities), eth-lightclient every gate incl strict
exclusion, the Solana anchored path, DreggVault accounting, DreggSettlement.settle, dregg-pay/watcher (governance-
pinned anchor), the committed double-mint/replay defense. The verify-cores are REAL; the WIRING is where the
bridge-hack risk lives; #1 dispatches first.
