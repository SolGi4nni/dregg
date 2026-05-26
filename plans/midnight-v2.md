# Midnight Integration v2: From Attestation Bridge to Proof-Carrying Interop

## Current State

### What We Have
- `gen_midnight.rs` — DSL backend emitting ZKIR v3 JSON from CircuitDescriptors
- `bridge/src/midnight.rs` — Level 1 attestation bridge (25 tests)
  - FederationAttestation (Ed25519 aggregate sig + BLAKE3 domain separation)
  - DreggToMidnight / MidnightToDregg message types
  - NonceTracker (replay prevention)
  - MidnightBridgeConfig (epoch-based key rotation)
- `bridge/src/midnight_observer.rs` — Substrate RPC observer (mock infrastructure, 7 tests)
- `bridge/src/midnight_contract.compact` — Compact pseudo-code for Midnight-side contract
- `cell/src/note_bridge.rs` — `BridgeDestination::Midnight` routing enum
- `dregg-dsl-tests/src/fri_verifier_dsl.rs` — FRI verifier prototype (29 cols, 7 tests)
- `plans/midnight-insight.md` — Gap analysis + integration priorities
- `plans/midnight-bridge-level2.md` — Path analysis (A/B/C/D feasibility)
- ~/midnight/ — 12 cloned repos (midnight-zk, midnight-ledger, midnight-node, etc.)

### Midnight's Architecture (confirmed from code)
- Proof system: PLONK over BLS12-381 with KZG commitments (Halo2 v0.3 fork)
- Smart contracts: Compact (TypeScript-like) → ZKIR v3 → Plonk circuit
- State: ZSwap (shielded pool) + Night (unshielded UTXO) + Contract state
- Settlement: Substrate node, bridges to Cardano via Partner Chains
- Circuit limits: k=20 (up to ~1M rows)
- ZK stdlib: Poseidon, SHA-256, Keccak, ECDSA, Ed25519, BLS12-381 in-circuit

## The Four Levels of Integration

### Level 1: Attestation Bridge ✅ DONE
**Trust model:** Federation signs "this happened." Midnight trusts signatures.
**Security:** 2/3 federation honest assumption.
**What it gives us:** Token bridging (lock on dregg → attest → mint on Midnight, and reverse).

### Level 2: Proof-Carrying Bridge (DESIGNED, PROTOTYPE EXISTS)
**Trust model:** `dregg` sends a PROOF that Midnight verifies in-circuit.
**Security:** Computational soundness of the STARK (no federation trust for safety).

**Feasible path:** Wrap dregg STARK into BLS12-381 PLONK externally, then Midnight's
`VerifierGadget<BlstrsEmulation>` verifies it natively. Requires an external compression
service (STARK → BLS12-381 PLONK proof).

**Gate count estimate:** ~920K gates for FRI verification in BLS12-381 arithmetic.
Fits in Midnight's k=20 circuit (1M rows). BabyBear (31 bits) embeds trivially
into BLS12-381 Fq (255 bits) — zero limb overhead.

**Blocker:** No production BLS12-381 PLONK wrapper for our STARKs yet.
SP1 wraps to BN254/Groth16, not BLS12-381.

### Level 3: Shared Programs (DESIGNED, gen_midnight.rs EXISTS)
**Trust model:** Same program runs on BOTH chains. Verification is native on each.
**What it gives us:** A dregg capability proof IS a valid Midnight contract call.

A `CircuitDescriptor` compiles to:
- BabyBear STARK (dregg-native, fast proving)
- ZKIR v3 (Midnight-native, verified by their proof server)

Same semantics, different proof systems. The program's MEANING is the interop atom.

**Current gap:** `gen_midnight.rs` emits ZKIR but we haven't deployed anything to Midnight's
testnet. Need: Compact contract wrapper that loads ZKIR, Midnight SDK tooling.

### Level 4: Composable Cross-Chain Proofs (FUTURE)
**Trust model:** A proof on dregg is a VALID INPUT to a Midnight computation.
**What it gives us:** "I proved on dregg I'm authorized" → feeds into a Midnight
contract that moves shielded tokens based on that authorization.

Requires Level 2 or Level 3 as foundation. Application-level composition where
both proof systems share a public commitment (e.g., a Poseidon hash) as the
binding point.

## Implementation Phases

### Phase 1: Ship Level 1 (NOW — 1-2 weeks)
- [ ] Deploy observer node connecting to Midnight testnet (when available)
- [ ] Write actual Compact contract (not just pseudo-code)
- [ ] End-to-end test: lock on dregg → attest → unlock on Midnight mock
- [ ] Rate limiting + amount caps for safety
- [ ] Monitor for Midnight testnet availability

### Phase 2: External Compression Service (4-6 weeks)
- [ ] Build a service that takes our Poseidon-committed STARK proof and produces a BLS12-381 PLONK proof
- [ ] Options:
  - Use Halo2 (BLS12-381) to verify our STARK in-circuit
  - Use gnark (Go, BLS12-381 PLONK) as the compression backend
  - Wait for SP1 to ship BLS12-381 support
- [ ] Once we have BLS12-381 PLONK output: Midnight's VerifierGadget can verify it natively
- [ ] This gives us Level 2: proof-carrying bridge without Midnight protocol changes

### Phase 3: ZKIR Program Deployment (6-8 weeks)
- [ ] Compile a simple dregg predicate (e.g., "balance >= threshold") via gen_midnight.rs → ZKIR
- [ ] Deploy to Midnight testnet as a contract
- [ ] Call the contract with a valid witness → proof verifies on Midnight
- [ ] This gives us Level 3: same program, two chains

### Phase 4: Cross-Chain Capability Exercise (10-12 weeks)
- [ ] `dregg` capability proof → shared Poseidon commitment → Midnight contract input
- [ ] "Prove on dregg you're authorized to spend" → "Midnight moves shielded tokens"
- [ ] Compose: dregg Effect VM proof + Midnight ZSwap proof + shared commitment binding
- [ ] Full privacy: dregg hides WHO is authorized, Midnight hides HOW MUCH moves

## What `dregg` Adds to Midnight's Ecosystem

Midnight has shielded VALUE transfer. `dregg` has private AUTHORIZATION.

| Midnight alone | `dregg` + Midnight |
|----------------|-----------------|
| "Move 100 tokens privately" | "Move 100 tokens privately IF authorized by a capability chain" |
| Contract state is private | Authorization to CALL the contract is also private |
| KYC gate (reveal identity to verifier) | ZK-KYC (prove property without revealing identity) |
| Simple token types | Attenuated, delegatable, revocable capability tokens |

The deepest integration: Midnight's DeFi contracts gain dregg's authorization model.
A Midnight DEX could require a dregg capability proof to trade — proving you're an
authorized participant without revealing who you are or how you got the authorization.

## What Midnight Adds to `dregg`'s Ecosystem

- Shielded value layer (production-grade Zerocash, battle-tested)
- Cardano settlement (via Partner Chains — access to Cardano liquidity)
- Stablecoin infrastructure (if USDC/USDT deploy on Midnight)
- Regulatory compliance (Midnight's "rational privacy" model for institutions)
- Larger anonymity set (more users = better privacy for everyone)

## Key Technical Decisions

### Why not just use Midnight for everything?
Midnight is a BLOCKCHAIN. Fixed global state, consensus on all operations.
`dregg` is a COORDINATION LAYER. Sovereign state, consensus only when needed.
For 90%+ of dregg operations (single-owner, bilateral), a blockchain is overkill.
Use Midnight for SETTLEMENT and VALUE. Use dregg for AUTHORIZATION and EXECUTION.

### Why Midnight over Ethereum?
- Same proof system family (Plonk) — easier to bridge
- Native privacy (ZSwap) — don't need to add privacy on top
- Cardano ecosystem — access to different liquidity pool
- Architecturally aligned — both believe in "not everything needs to be on-chain"
- Can do BOTH: EVM bridge (SP1→Groth16) for DeFi liquidity, Midnight bridge for privacy

### The Poseidon2 advantage
Our `poseidon_stark.rs` uses Poseidon commitments SPECIFICALLY to be verifiable
in other proof systems that have Poseidon gates. Midnight has Poseidon in zk_stdlib.
If parameters match: FRI verification becomes native. This was a deliberate design choice.

## Dependencies + Risks

| Dependency | Status | Risk |
|-----------|--------|------|
| Midnight testnet access | Not yet available to us | Medium — may need partnership |
| Compact compiler (closed source) | Available as binary releases | Low — we have it at ~/midnight/compact |
| BLS12-381 PLONK wrapper | Doesn't exist yet | High — need to build or wait for SP1 |
| ZKIR v3 stability | Under active development | Medium — our gen_midnight.rs may need updates |
| Midnight's VerifierGadget | Exists, BLS12-381 native | Low — confirmed from code |

## Metric: When Is the Bridge "Deep Enough"?

- Level 1: "I trust the federation" → Ship now, iterate later
- Level 2: "I trust math" → The target for production
- Level 3: "Same program, two chains" → The dream (programs are portable)
- Level 4: "Proofs compose across chains" → The endgame (authorization + value as one)

We're at Level 1 today. Level 2 is 4-6 weeks of focused work (the compression service).
Level 3 follows naturally from gen_midnight.rs. Level 4 is the research frontier.
