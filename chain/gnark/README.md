# chain/gnark — dregg's native Ethereum wrap circuit

The modern replacement for the SP1 RISC-V-zkVM bridge (`chain/program/`,
`chain/src/prove.rs`). A **native gnark circuit over BN254** that verifies the
dregg whole-history FRI proof directly — no RISC-V emulation — and emits a
Groth16/BN254 proof checked by `IDreggSettlement.settle` for ~250–300k gas.

Design + rationale + plan + the load-bearing unknown:
**`docs/deos/ETH-NATIVE-WRAP.md`**.

## Status

Interface spec / skeleton. `fri_verifier.go` defines the witness shape and the
three teeth of `verify_turn_chain_recursive_from_parts`
(`circuit-prove/src/ivc_turn_chain.rs:2845`); the gadget bodies (BabyBear/ext/
Poseidon2, the FRI low-degree test, the Fiat-Shamir transcript, the four NPO
tables) are the multi-week build (ETH-NATIVE-WRAP.md §3–4).

## Why native, not zkVM

SP1 proves *RISC-V execution of* the verifier — every BabyBear op becomes ~10–40
constrained zkVM cycles (the emulation tax), ballooning millions of native ops
into tens-to-hundreds of millions of cycles. The native circuit makes one
BabyBear op ≈ one constraint, dropping wrap proving from minutes-to-tens-of-minutes
(GPU, SP1) to seconds-to-low-minutes. It also verifies the **current** fork proof
(`BatchStarkProof<DreggRecursionConfig>` at `ir2_leaf_wrap_config`), not the
legacy `GuestStarkProof` the SP1 guest still encodes.

## What's reused

The entire non-cryptographic seam is already built and unchanged:
`bridge/src/ethereum.rs` (calldata, public-input binding, settlement state
machine) and `chain/contracts/IDreggSettlement.sol`. This module only replaces
the *wrap prover*.
</content>
