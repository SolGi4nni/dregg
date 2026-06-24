# Proof Composition Coherence for Cross-Chain Sovereign Cell Verification

## The Incoherence Today

`dregg` has seven proof backends producing five incompatible formats. A sovereign cell state transition currently requires picking one, but no single backend satisfies all destinations. The `SovereignTransitionAir` (6 columns, balance transfer only) is the closest thing to a canonical statement, but it only covers one effect type and only lives in BabyBear-land.

The real question is not "which proof system" but "what is the canonical statement, and how does it reach each destination?"

## 1. The Canonical Statement

The canonical "valid state transition" proof must attest:

- **Old state commitment** (Poseidon2 hash of cell state)
- **New state commitment** (after effects applied)
- **Effects hash** (what was done)
- **Cell ID** (which cell)
- **Conservation** (no value created from nothing)
- **Permission** (caller was authorized)

**Answer: SP1 proving the TurnExecutor (Option B).**

The TurnExecutor already enforces all dregg rules (conservation, capability checks, effect application). Proving it inside SP1 means one circuit handles arbitrary effects -- SetField, GrantCapability, Transfer, Revoke, anything future. Specialized AIRs (Option A) require a new circuit per effect type and a composition layer. Kimchi native (Option C) gives small proofs but requires reimplementing every rule as gates, doubling the audit surface.

SP1 proving the executor is the canonical inner proof. It says: "I ran the real dregg state machine on these inputs and got these outputs." General-purpose, auditable, one implementation.

## 2. The VK Bridging Problem

A destination chain verifying an SP1 Groth16 proof needs to know the verification key corresponds to "the dregg executor program." This is solved by:

1. **Program commitment**: SP1 produces a program VK (hash of the ELF). This is a fixed constant for a given dregg release.
2. **Registry contract**: An on-chain registry maps `program_vk_hash -> "dregg-executor-v{N}"`. Governed by dregg's multisig or DAO. Updated on protocol upgrades.
3. **The verifier checks**: `proof.vk_hash == registry.current_dregg_vk()`.

The destination doesn't need to understand dregg's rules. It trusts that SP1 soundly executed a program whose VK is registered. The VK commitment IS the trust anchor. This is the same model as Succinct's SP1 verifier gateway.

For Mina: the Pickles proof carries the verification key in the proof structure itself. A Mina zkApp stores the expected VK and rejects proofs from unknown programs.

## 3. The Wrapping Architecture

```
                    Canonical Inner Proof
                           |
            SP1 STARK (proves TurnExecutor ran correctly)
                           |
              +------------+------------+
              |            |            |
         SP1->Groth16   Pickles     Halo2/KZG
              |            |            |
            EVM          Mina        Midnight
```

**Inner proof**: SP1 STARK. Always produced. ~48 KiB, proves arbitrary executor logic.

**Outer wrappers** (one per destination family):
- **EVM**: SP1's built-in STARK-to-Groth16 compression. Exists, works, ~200K gas. This is `./chain`.
- **Mina**: STARK-in-Pickles wrapping (already scaffolded in `stark_in_pickles.rs`). Compress the SP1 STARK into a Pickles proof. Mina zkApps verify natively. ~272K gates, ~5s wrap time.
- **Midnight**: Observation bridge (attested state relay), not proof translation. Midnight uses KZG-based Plonk; translating IPA proofs to KZG requires a trusted setup bridge or just relaying attested roots signed by a quorum. Given Midnight's own Cardano bridge uses attestation, this is the pragmatic path.

Key insight: the wrapping is done ONCE per destination family, not per effect type. Adding a new effect to dregg requires zero circuit changes to the bridge -- only the SP1 guest program (which is just Rust) gets updated.

## 4. SP1 vs Kimchi: Complementary, Not Competing

**SP1** is the canonical path for cross-chain settlement. It proves "the executor ran correctly" for any effect type. Slow to prove (~minutes for complex turns), but the output reaches EVM cheaply.

**Kimchi/Pickles** is the native path for Mina and for recursive credential composition. It proves specific sub-statements (membership, derivation, fold chains) with constant-size recursive proofs. It is operationally better for: agent-to-agent presentations within the dregg network, Mina L1 anchoring, and unbounded delegation chains.

The answer is: **SP1 for outbound bridges, Kimchi/Pickles for internal recursion and Mina.**

They compose: a Pickles proof of a 50-step delegation chain can be included as a public input to the SP1 executor proof ("the credential presented to authorize this turn was valid"). The SP1 guest program verifies the Pickles proof's accumulated hash against the expected value.

## 5. The "Someday Trustless Bridge" Architecture

**dregg -> EVM**: SP1 -> Groth16. Trustless. Path exists in `./chain`. Complete the integration.

**dregg -> Mina**: Pickles natively. Trustless. Path exists in `backends/mina/`. The STARK-in-Pickles wrapper (when completed) allows any STARK proof to become Mina-verifiable.

**dregg -> Midnight**: Attestation bridge. NOT trustless in the ZK sense. Midnight's architecture (KZG + Plonk) is algebraically incompatible with our IPA/FRI proofs without a translation circuit that doesn't yet exist in any production system. The pragmatic path is a threshold-signed state attestation, same as Cardano->Midnight uses today. If Midnight exposes a STARK verifier precompile in the future, we can switch to proof-based.

## 6. Recommendation: The Coherent Architecture

**One canonical inner proof**: SP1 proving the TurnExecutor. Every sovereign cell state transition produces this proof. It covers all effect types, all permission models, all conservation checks.

**Recursive history**: Pickles-assisted recursion compresses unbounded turn histories into constant-size proofs. The SP1 proof for turn N includes the accumulated hash from turns 1..N-1 as a public input. The Pickles recursive chain provides the 124-bit binding.

**Three outer wrappers**:
1. SP1 -> Groth16 (EVM). Trustless, ~200K gas.
2. STARK-in-Pickles (Mina). Trustless, native verification.
3. Attestation relay (Midnight, other). Practical, upgradeable to trustless when destination chains support STARK verification.

**What to build next** (in priority order):
1. Complete the SP1 guest program for TurnExecutor (currently scaffold).
2. Deploy the Groth16 verifier to Base Sepolia with the VK registry.
3. Finish the STARK-in-Pickles BabyBear Poseidon2 emulation (~2000 lines of gate code).
4. Deprecate specialized AIRs for cross-chain use (keep them for fast-path intra-network presentations where latency matters more than universality).

The architecture is: **one program, one proof, many wrappers.** The program is the TurnExecutor. The proof is SP1's STARK. The wrappers are mechanical translations to destination-specific formats. Adding a new destination chain means writing one new wrapper, not reimplementing dregg's logic.
