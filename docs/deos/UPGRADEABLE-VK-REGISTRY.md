# The Upgradeable-VK Registry — a VK-epoch flip is a transaction, not a redeploy

## What is

dregg's on-chain settlement verifies a Groth16(BN254) proof over the pinned
25-lane statement (`genesis_root ++ final_root ++ num_turns ++ chain_digest`).
The gnark-generated verifier `chain/contracts/DreggGroth16Verifier25.sol` bakes
the verifying key into contract CODE as Solidity constants: α in G1; β, γ, δ in
G2 (stored negated); the Pedersen commitment key G, Gσ in G2; and the 27 IC
points (the constant term + 26 public-input bases = 25 statement lanes + 1
Pedersen-commitment public input).

Because the VK is code, every VK epoch — a GAP-flip, the nullifier flip, a
re-genesis — forces a full redeploy of the verifier AND, since
`DreggSettlement` pins its verifier at construction, the settlement contract
too. During the evolving phase where the VK changes often, that redeploy cost
recurs each time.

`chain/contracts/DreggGroth16VerifierUpgradeable.sol` moves the VK into
STORAGE, keyed by a VK EPOCH:

- `mapping(uint256 epoch => VerifyingKey) _vks` — the VK per epoch;
- `currentEpoch` — the pointer a fresh proof (and a fresh settlement) targets;
- `advanceEpoch(VerifyingKey newVk)` — write the NEXT epoch's VK and bump the
  pointer, in ONE transaction;
- `setVerifyingKey(epoch, vk)` — seed/correct a not-yet-live epoch (refuses to
  overwrite a set epoch);
- `verifyProofAtEpoch(epoch, …)` — verify against a TARGETED epoch's VK;
- `verifyProof(…)` — the `IGroth16Verifier25` drop-in, targeting the current
  epoch, so the registry is a drop-in for the generated-verifier + adapter pair
  in `DreggSettlement`'s consumer slot.

The pairing MATH is byte-identical to the generated verifier — the same
commitment proof-of-knowledge gate `e(commitment, Gσ)·e(pok, G) == 1`, the same
public-input MSM `L = IC[0] + commitment + Σ inputᵢ·IC[i+1] + pubCommit·IC[26]`,
and the same final equation

    e(A, B) · e(C, −δ) · e(α, −β) · e(L, −γ) == 1

— reproduced reading the VK from STORAGE instead of from code constants. Epoch
0 is seeded in the constructor with the LIVE deployed VK, copied byte-for-byte
from `DreggGroth16Verifier25.sol`, so the current live proof still verifies
unchanged. This is proven in
`chain/test/DreggVerifierEpochRegistry.t.sol`: the REAL settlement fixture proof
(`chain/test/fixtures/settlement_groth16.json`, the real 2-turn apex) verifies
against the storage-seeded epoch-0 VK, and an epoch FLIP changes settlement
behavior at the SAME verifier and settlement addresses — a transaction, no
redeploy.

## Old epochs stay verifiable

A proof targets an epoch and is checked against THAT epoch's VK, so proofs
minted under an old VK stay verifiable at their epoch after the pointer
advances (`verifyProofAtEpoch(oldEpoch, …)` still returns true). Already-settled
roots are recorded permanently by `DreggSettlement._provenRoots`, so a flip
never un-proves history regardless.

## The gate is THE security control (honest framing)

A mutable VK is a security control, not a convenience: a malicious setter can
install a VK that accepts ANY proof — a forged one over any statement. So
`advanceEpoch` / `setVerifyingKey` are `onlyOwner`, a real modifier, tested in
both polarities (an ungated advance REVERTS `NotOwner`).

This adds NO new trust over the status quo. Today the deployer already chooses
the baked-in VK by deploying the generated verifier; the registry simply names
the setter and makes the VK swappable without a redeploy. The trust root is the
same party. What changes is only WHERE the VK lives and HOW it is replaced.

- **Private / testnet:** `onlyOwner` on this contract is sufficient — the owner
  is the operator who would otherwise have redeployed. This is the current dev
  posture (single-party dev-ceremony VK, `keccak256("dregg-settlement-vk-dev-setup")`).
- **Public / mainnet:** the owner MUST be a GOVERNANCE contract behind a
  TIMELOCK (e.g. an OpenZeppelin `TimelockController` owned by a multisig or
  token governor). A mutable VK with an EOA owner is an accept-anything
  backdoor; the timelock is what makes a flip OBSERVABLE and VETOABLE before it
  takes effect. Ship `transferOwnership(timelock)` as part of the public deploy;
  never leave an EOA owner on a public instance.

The VK is also validated at set time (`_validate`): every coordinate must be a
reduced Fp residue (< P) and every G1 point (α and the 27 IC bases) must satisfy
`y² = x³ + 3`, so a malformed VK REVERTS rather than shipping a silently-wrong
key. (G2 on-curve is left to the pairing precompile, which fail-closes on a bad
β/γ/δ/G/Gσ at verify time.) This is a well-formedness gate, not a
proof-of-honest-setup — a well-formed but adversarially-chosen VK is exactly
what the owner gate + timelock defend against.

## Gas note — storage-VK vs embedded

Reading the VK from storage costs the cold SLOADs of ~76 words (27 IC × 2 + α +
five G2 points × 4) that the generated verifier reads for free from code:

| path | embedded (code-constant VK) | storage-VK registry | delta |
|---|---|---|---|
| `verifyProof` | 466,163 gas | 650,244 gas | +184k (~+39%) |
| `DreggSettlement.settle` | 604,789 gas | 780,901 gas | +176k (~+29%) |

(The embedded `settle` figure 604,789 matches the live Base-Sepolia settlement
tx in `chain/DEPLOYMENTS.md` exactly.) The ~180k-gas premium per settlement is
the price of never paying the redeploy cost of a verifier + settlement stack per
VK epoch — a favorable trade during the evolving phase, where flips are frequent
and each redeploy is far more than 180k gas plus the re-wiring/re-anchoring
ceremony. If a future epoch schedule stabilizes, the registry can be frozen
(hand ownership to `address(0)` via a burn, or a dedicated freeze) to lock the
VK, or a fresh embedded verifier deployed for the final VK.

## Non-EVM analogues (NAMED follow-ups)

The same VK-in-storage move applies to dregg's other chain targets:

- **Solana:** today the settlement verifier's VK is a compiled-in `vk.rs`
  (constant `Groth16Verifyingkey`), so a flip needs a program redeploy. The
  analogue is VK-IN-ACCOUNT: store the VK (α, β, γ, δ, IC[]) in a
  program-owned PDA account keyed by epoch, with an `advance_epoch` instruction
  gated by an upgrade-authority / governance PDA (the Solana counterpart of
  `onlyOwner` + timelock). Verification reads the epoch's account. Follow-up.
- **Cosmos (CosmWasm / a light-client module):** the VK becomes VK-IN-STATE — a
  `Map<u64 /*epoch*/, VerifyingKey>` in the contract's `Item`/`Map` store (or an
  `x/` module `KVStore` entry), with an `AdvanceEpoch` execute message gated by
  the contract admin / a `x/gov` proposal + voting period (the Cosmos analogue
  of the timelock). Verification loads the epoch's VK from state. Follow-up.

Both keep the identical shape: VK moves from code/binary into per-epoch state, a
flip is a gated message, old epochs stay verifiable, and the gate (upgrade
authority / governance + voting delay) is the load-bearing control — private
single-authority, public governance.

## Files

- `chain/contracts/DreggGroth16VerifierUpgradeable.sol` — the storage-VK
  registry verifier (epoch registry + owner gate + the real pairing).
- `chain/contracts/IGroth16VerifierRegistry.sol` — the registry interface
  (extends `IGroth16Verifier25`).
- `chain/test/DreggVerifierEpochRegistry.t.sol` — both-polarity suite over the
  real fixture proof.
- `chain/script/DeployUpgradeableSettlement.s.sol` — deploys the registry
  (epoch-0 seeded) + `DreggSettlement` wired to it.
