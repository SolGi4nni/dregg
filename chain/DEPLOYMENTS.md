# dregg on-chain deployments

## Base-Sepolia (chainId 84532) — first live dregg settlement — 2026-07-13
A **real dregg state-transition proof** (STARK apex → BN254-native shrink → gnark verify → Groth16)
settled and **verified on-chain via the Solidity pairing**. Fixture turn; dev-ceremony trusted setup.

| contract | address |
|---|---|
| DreggGroth16Verifier25 | `0x7FBe1D2505644e1e4D50a1B5Cf08d0AcbF60C7cD` |
| Groth16Verifier25Adapter | `0x6C353666B3516f7d04cd68437c22D056446e455F` |
| **DreggSettlement** | `0x6c87b53530c8392F22bab3B004919EBC4E86Bd87` |

- **Settle tx (a real proof verified on Base-Sepolia):** `0xbd2cac6a54d27ff818c46ad67667412a489001cc4c382193cf7ac757229e963b`
  https://sepolia.basescan.org/tx/0xbd2cac6a54d27ff818c46ad67667412a489001cc4c382193cf7ac757229e963b
- On-chain state (read back): `provenHeight() = 2`, `provenRoot() = 0x6ca8f74f…364b868`. Block 44,100,644, 604,789 gas.
- Deployer (throwaway): `0x8b251ADF19a78C6f9e9217E07CD3468C40F00343`.
- Redeploy: `forge script chain/script/DeploySettlement.s.sol:DeploySettlement --rpc-url base_sepolia --broadcast`.

**Honest:** fixture proof (real 2-turn apex, pre-generated — not yet a live user turn); dev single-party
Groth16 ceremony (toxic-waste-known), not production MPC. Proof-gen ≈ 5-7 min/proof on M2 Max (fold ~288s +
shrink ~95s CPU/14.5s GPU + Groth16 prove ~18s).
