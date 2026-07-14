# Regenerating the cross-chain settlement verifiers

dregg settles the same BN254 Groth16 proof on three chains: EVM (Solidity), Solana
(`alt_bn128` syscalls), and Cosmos (CosmWasm/arkworks). All three verify the *same*
verifying key (VK) and the *same* proof format. Those constants used to be
hand-maintained per chain, so they could drift. They are now generated from ONE
canonical spec, so a VK/format change is a regen + a set-VK transaction — not a
three-chain hand-port.

## The one source

`chain/codegen/dregg_vk.json` — the canonical, chain-agnostic VK + proof-format
spec. It holds the gnark VK (α in G1; β/γ/δ pre-negated in G2; the Pedersen G/Gσ
keys; IC[0] and the 26 IC bases IC[0..25]) as decimal field elements, plus the
format params (25 public inputs, the scalar field R, the commitment fold
`h = keccak256(be32(C.x)‖be32(C.y)) mod r`, the MSM
`L = IC0 + C + Σ input_i·IC[i] + h·IC[25]`, and the pairing
`e(A,B)·e(C,-δ)·e(α,-β)·e(L,-γ) == 1`).

The spec is extracted once from the gnark output (the VK gnark bakes into
`chain/contracts/DreggGroth16Verifier25.sol` via `ExportSolidity`). Day-to-day the
committed `dregg_vk.json` is the source of truth.

## What is generated vs hand-written

Generated from the spec by `chain/codegen/gen_verifiers.py`:

| Output | Chain | Encoding |
| --- | --- | --- |
| `solana-settlement/src/vk.rs` | Solana | bytes: G1 = X‖Y (64 be), G2 = X_c1‖X_c0‖Y_c1‖Y_c0 (EIP-197); β/γ/δ pre-negated |
| `cosmos-settlement/src/vk.rs` | Cosmos | arkworks decimal strings: G1 = (x,y), G2 = ((x.c0,x.c1),(y.c0,y.c1)) |
| `chain/codegen/out/DreggGroth16Verifier25.vk.sol` | EVM | the Solidity VK constant block (diff vs the live `.sol`; injection body for the upgradeable path) |
| `chain/codegen/out/dregg_vk.evm.json` | EVM | the VK as the uint256 injection vector for an upgradeable `setVerifyingKey(...)` tx |

**Unified:** the VK constants + the format params — the drift-prone part — for all
three chains, from the one spec.

**Not unified (named residual):** the per-chain *pairing body* stays hand-written in
each chain's crypto library (EIP-197 precompiles / `solana_bn254` syscalls /
arkworks). That logic is small and stable; unifying the VK + format constants kills
the actual drift source. The gnark `.sol` pairing body remains gnark's own output.

## Regenerating on a VK / format change

1. Re-run the gnark setup if the circuit/VK changed (mints a new
   `chain/contracts/DreggGroth16Verifier25.sol`):
   ```
   cd chain/gnark && DREGG_SNARK=1 go test -run TestSettlementGroth16EndToEnd -v
   ```
2. Re-extract the canonical spec from the fresh gnark output:
   ```
   python3 chain/codegen/extract_vk_spec.py \
       chain/contracts/DreggGroth16Verifier25.sol \
       chain/codegen/dregg_vk.json
   ```
   (Skip step 1–2 if only re-emitting encodings from an unchanged spec.)
3. Regenerate all three chains' VK from the one spec:
   ```
   python3 chain/codegen/gen_verifiers.py
   ```
4. Prove consistency — the same real proof verifies on EVM + Solana + Cosmos, and a
   tampered proof is rejected by all three:
   ```
   chain/codegen/check_consistency.sh
   ```
5. Point each chain at the new VK:
   - **EVM (upgradeable path):** send `setVerifyingKey(...)` using the words in
     `chain/codegen/out/dregg_vk.evm.json`. Where the verifier is still the
     immutable gnark contract, deploy the regenerated `.sol` and repoint
     `DreggSettlement.verifier`.
   - **Solana:** ship `solana-settlement` (`cargo build-sbf`) and upgrade the
     program (the VK is compiled in).
   - **Cosmos:** store + migrate the `cosmos-settlement` code id (the VK is compiled
     in).

So the on-chain side evolves with dregg at low pain: one spec, one codegen run, one
consistency gate, then a set-VK / program-upgrade per chain — not a three-chain
hand-maintenance flag day.

## Consistency gate

`chain/codegen/check_consistency.sh` is the payoff. It checks, structurally, that
the codegen output equals the committed verifiers, that the generated Solidity VK
block equals the live gnark `.sol`, and that the Cosmos fixture equals the chain
source fixture; then, at runtime, that the SAME real proof
(`chain/test/fixtures/settlement_groth16.json`) verifies under all three verifiers
and that tampered proofs are rejected by all three. Rust builds route through warm
`pbuild` lanes; forge runs locally.
