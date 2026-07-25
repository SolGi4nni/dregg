# On-Chain Contract Security Audit (EVM + CosmWasm) — 2026-07-25

VERDICT: **the cryptographic core is SOUND; the exploitable holes are in TRUST ANCHORS, TOKEN ACCOUNTING, and
PROOF-BINDING — not the pairing math.** REALITY: only DreggSettlement is on Base Sepolia testnet (fixture); the
rest are pre-launch. The campaign's contract work should center on trust anchors (VK owner, oracle/recorder,
deployer roles) + statement-binding (fold chain/contract/recipient/action into every proof + signature).

## SOUND (verified — do not re-audit)
- DreggVault custody: NO owner/admin/pause/upgrade exists; withdraw/escrowRelease/escrowRefund all nonReentrant +
  checks-effects-interactions (nullifier/status/balance set before every transfer); escrowedBalances and
  tokenBalances DISJOINTLY accounted (neither pool can drain the other). Confirms the interchain audit.
- DreggSettlement: verifier + VK IMMUTABLE (no settable VK here), genesis pinned at construction, continuity +
  monotone-height + BabyBear-canonical + numTurns>0, replay-proof (continuity advances the proven root),
  outbound-message-root path fail-closed.
- DreggMerkle: correct 0x00 leaf/node domain separation + positional binding.
- The Groth16 stack (DreggGroth16Verifier25 standard gnark template; adapter maps revert→false; upgradeable same
  math over storage VK): public inputs < R, precompiles enforce on-curve/subgroup on ALL proof points, Pedersen
  PoK gate + final pairing equation faithful.
- cosmos-settlement/verifier.rs: full on-curve AND subgroup checks; VK matches the EVM VK BYTE-FOR-BYTE (all
  G1/G2 constants + 26 IC points cross-checked); the only divergences (#9) are strictly STRICTER on the Cosmos
  side (Cosmos ≤ EVM acceptance — can't settle anything false). No admin, no migrate entry point.

## EXPLOITABLE HOLES (pre-mainnet)
- **#1 CRITICAL — settable-VK trust root.** DreggGroth16VerifierUpgradeable.sol:139-178: advanceEpoch/
  setVerifyingKey/transferOwnership are onlyOwner, owner=msg.sender (EOA), no on-chain timelock/delay/two-step.
  A compromised owner installs an accept-anything VK → the socket, TrustsADreggClearing, DreggProofAttestor +
  every registry consumer accept forged proofs over ANY statement. The code NAMES "must be governance+timelock"
  but nothing enforces it. Fix: enforce timelock/governance owner on-chain + epoch-advance delay + two-step.
- **#4 Medium/High — fee-on-transfer over-crediting.** DreggVault.sol:236,262,391: tokenBalances[token] += amount
  (not the received delta). A fee-on-transfer/rebasing token over-credits → withdrawals draw down OTHER
  depositors' balances of the same token (cross-user theft). The only unauthenticated cross-user theft vector in
  core custody. Fix: credit measured balanceOf delta, or allowlist standard tokens.
- **#10 High — unlocked conduct bond.** launchpad/DreggDeployerGate.sol:146-170: authorizeDeploy checks
  bondOf>=minBond at deploy; withdrawBond is UNCONDITIONAL → postBond→registerLaunch→withdrawBond next block =
  rug with ZERO bond at stake. The anti-scam economic layer is toothless. Fix: escrow the bond over the launch +
  challenge window; block withdraw while a backed launch is live.
- #2 High-if-consumed — DreggStateOracle.sol:152: recorder attaches ARBITRARY balance/nullifier/commitments/heap
  sub-roots to any proven state root (only binding isProvenRoot). Any RWA/DeFi consumer gating on proveHolding/
  proveNullifierSpent trusts the recorder. Fix: the sub-root-exposure weld (apex exposes sub-roots as PIs); until
  then no consumer may treat these as trustless.
- #5 Medium — DreggVault.sol:576 _computeRoot rebuilds the WHOLE tree from storage per deposit (O(n) SLOADs+hash),
  depositCount unbounded → deposits eventually exceed block gas (permanent griefing ceiling). Plus keccak,
  non-domain-separated ≠ circuit Poseidon2. PRE-LAUNCH LIVENESS BLOCKER. Fix: incremental fixed-depth Merkle; align Poseidon2.
- #3 Medium — DreggVault withdraw SP1 public values carry NO address(this)/chainid binding → replay on any vault
  sharing programVkey. Fix: fold address+chainid into the guest statement.
- #8 Medium/High — cosmos-lock/src/lib.rs: release_digest omits contract addr + chain-id (replayable across
  instances sharing the oracle set); RELEASE is an M-of-N ed25519 MULTISIG (trusted), not a validity proof
  (weaker than the EVM twin's SP1 fill proof). Fix: bind env.contract.address+chain-id; move to a real fill proof.
- #11 Medium — DreggDeployerGate.sol:152 slash = bare msg.sender==slasher (EOA), any amount, arbitrary recipient,
  NO on-chain fraud proof → compromised slasher drains all bonds. Gate behind a fraud proof/timelock.
- #13 Medium — DreggCredentialGate.sol:197: SP1 credential proof binds only (valid,fedRoot,predHash,nullifier),
  NOT msg.sender/tokenId/proposalId/support → snipe the proof: steal the mint, vote OPPOSITE, vote EVERY proposal.
  Fix: fold recipient/action into the presentation nullifier + check as a public value.
- #12 Medium — DreggDeployerGate authorizeDeploy is external (no onlyLaunchpad) and the private arm burns a
  nullifier → snipe a pending registerLaunch's sp1Proof from the mempool → burn the nullifier → victim reverts.
- #14 Medium — DreggCredentialGate admin can trust ANY federation root (two-step rotation present, good). Timelock.
- #15 Medium — launchpad/CommitteeAttestor.sol:218 challenge arm computes marginal from CALLER-SUPPLIED
  reservePrice (not in the signed tuple) → slash an HONEST committee (disables all future attests). Read
  reservePrice/saleSupply from the on-chain scheduleCommit.
- #6/#16/#17/#18 Low/Info — DreggVault deposit CEI (no concrete theft), launchpad marginal-fill fairness,
  SolventPool init front-run (mitigated by atomic graduate), undersubscribed token stranding.

## Top 5 (dispatch order — these are SOLIDITY/CosmWasm fixes, verify via the contract toolchain not persvati)
1. Settable-VK trust root (#1) — the single Critical; timelock/governance owner + epoch delay.
2. Fee-on-transfer over-crediting (#4) — the core-custody cross-user theft vector.
3. Unlocked conduct bond (#10) — escrow over launch + challenge window.
4. Operator-attested sub-roots (#2) — land the weld or fence consumers.
5. Statement-binding cluster (#3,#8,#13) — fold chain/contract/recipient/action into every proof + signature.
Plus the pre-launch liveness blocker: #5 DreggVault gas-DoS incremental Merkle.

NEW SURFACE found: the launchpad stack (DreggDeployerGate/Launchpad/SolventPool/CredentialGate/CommitteeAttestor)
is value-bearing with its own cluster (#10-18) — the economic/griefing layer needs the most work.
