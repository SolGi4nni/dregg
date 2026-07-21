# dregg chain / interchain / settlement — grounded inventory (2026-07-18)

Ground-truth read (4 read-only lanes, cited to code). The through-line: **the crypto/verification
machinery is real, sophisticated, and rare — no toy-roots anywhere — but nothing is
production-deployed, and the trust ceiling is three named, actively-worked things.** Distance to
production is *specific*, not "the crypto is fake."

## What is REAL (verification logic — the moat)
- **Proof-gated EVM settlement, LIVE on testnet.** `DreggSettlement` (Base-Sepolia, chainId 84532):
  real BN254 Groth16 pairing before moving the proven root; enforces continuity + monotonicity;
  genesis pinned at construction. **One real settle tx** verified a real dregg state-transition proof
  (STARK apex → BN254 shrink → gnark → on-chain pairing, 604k gas, `provenHeight()=2`).
- **Real Groth16 verifiers on EVM + Solana + Cosmos** (same VK): real pairing math (EVM precompiles;
  Solana `alt_bn128` syscalls; Cosmos arkworks), fail-closed. `solana-settlement` settles dregg's own
  25-lane turn statement onto Solana.
- **⚑ Real light-clients — the genuine kind — for all three foreign chains, exercised on real chain data:**
  - **ETH:** Altair sync-committee, BLS12-381 (`blst`), ≥2/3 participation, full finality → EVM
    `state_root` → EIP-1186 MPT proofs. e2e test on **live-captured mainnet, 2026-07-12, post-Electra**.
  - **Cosmos:** Tendermint (`ProdVerifier`) — real Ed25519 ≥2/3, validator-set binding, ICS-23.
  - **Solana:** Tower-BFT — Ed25519 vote verify, ≥2/3 stake, bank-hash recompute, accounts inclusion.
- **Real on-chain STARK verifier** (`chain/gnark/settlement_circuit.go`): ~12M-R1CS assembled
  in-circuit FRI/STARK verifier (transcript + batch-STARK algebra + FRI + Merkle-open + 25-lane bind),
  verifies a **real prover proof** (self-checked vs p3 `pcs.verify`) of a 2-turn chain.
- **Real verified executor** embedded in starbridge-v2 (the Lean-authored `TurnExecutor`); real DrEX
  engine (matcher/prover/settle bins); ~30 dregg-native apps (300+ tests).

## The TRUST CEILING (three named seams, all worked)
1. **FRI extraction floor — undischarged (no adversary model; the bit-count is a density reading, NOT a soundness bound).** The theorem-backed ledger columns are the deployed commit `FriDeployedHeightPairing.deployed_wrap_commitBits` and query `DeployedProximitySoundness` (`(9/16)³⁸ < 2⁻³¹`; digits in `docs/reference/PROVEN-120-CONFIG.md`). Everything
   wrapping a STARK inherits it. Worked by the FRI stages (FriVerifier* 5-stage re-basing) + codex.
2. **Hand-authored circuits (the gnark Go STARK verifier — 12M R1CS, no Lean refinement; faithfulness
   is differential-test-validated, not proven).** The AIR-in-Lean debt at scale. Closure = stark-kill
   (Lean-authored verifier circuit + refinement proof).
3. **Dev VK ceremony — single-party, toxic-waste-known → FORGEABLE.** The #1 deployment seam
   (EVM/Solana/Cosmos/gnark all share it). Fix = a real MPC ceremony (ember-gated).

## The DEPLOYMENT gap ("green on ember's laptop")
- **EVM:** testnet only (Base-Sepolia), a *fixture* turn (not a live user), dev VK, single chain.
  DVN/ISM/oracle/vault/socket/launchpad = code-only, not deployed; interchain modules correctly
  fail-closed but **inert** (outbound-message commitment not yet proof-bound).
- **Cross-chain:** the trustless consensus verification EXISTS + is unit-real, but the **deployed
  devnet path runs a TRUSTED-ORACLE mirror** (M-of-N ed25519) — devnet RPC can't feed the trustless
  path (accounts-hash proofs + signed bank hash unavailable off-chain). Remaining = wire-format
  ingestion + stake-table provenance, **not verification logic**. Cosmos settle/lock = local-test only.
  Weak-subjectivity anchors are the standard/correct posture (Helios/Hermes/ibc-rs), not per-query trust.
- **DrEX / starbridge / apps:** real engines, **deployed nowhere** — no listener on :8420/:8781/:8782;
  `drex_clear`/`cert_f_prove` not built locally (ssh persvati); durable node unit targets hbox, not
  installed; public gateway fronts the GAMES funnel, not DrEX. starbridge ships a real DMG but boots
  hardcoded demo-genesis. A stranger cannot complete a DrEX trade out of the box.
- **Bridges:** no deployed contracts, no live chains — loopback/testnet, `Mock*Rpc` test doubles, no
  committed addresses. Mina = observation-only (recursion removed as vacuous — honest). `sandstorm-bridge`
  is app-hosting, misfiled under "bridge".

## Honest one-liner
**Real, rare verified-settlement + cross-chain infrastructure (real light-clients, real on-chain STARK
verifier, real proof-gated settlement — most projects fake all three) at the "verification-logic real,
deployment + hardening pending" stage.** The path to production is specific: MPC ceremony · discharge/
bound the FRI floor · Lean-author the circuits · wire the trustless cross-chain to mainnet · deploy +
host durably. Not vaporware; not done.
