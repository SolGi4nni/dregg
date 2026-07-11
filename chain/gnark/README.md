# chain/gnark — dregg's native Ethereum wrap circuit

The modern replacement for the SP1 RISC-V-zkVM bridge (`chain/program/`,
`chain/src/prove.rs`). A **native gnark circuit over BN254** that verifies the
dregg whole-history FRI proof directly — no RISC-V emulation — and emits a
Groth16/BN254 proof checked by `IDreggSettlement.settle` for ~250–300k gas.

Design + rationale + plan + the load-bearing unknown:
**`docs/deos/ETH-NATIVE-WRAP.md`**.

## Status

Gadget layer landed; verifier assembly pending. `fri_verifier.go` defines the
witness shape, the pinned 25-lane public-input contract
(`genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8]`, every lane
a canonical BabyBear residue, enforced fail-closed in `Define`), and the three
teeth of `verify_turn_chain_recursive_from_parts`
(`circuit-prove/src/ivc_turn_chain.rs:2845`) with tooth 3 (the segment tooth)
wired. The field gadgets exist and are differentially tested against plain-Go
references (and those against `math/big` / the fork's known-answer vector):

- `babybear.go` — BabyBear ops over BN254 (canonical residues; hinted
  `x = q·p + r` reduction, range-checked fail-closed).
- `babybear_ext.go` — the degree-4 extension `BabyBear[X]/(X^4 − 11)`
  (W = 11 per plonky3 `baby-bear/src/baby_bear.rs:65`).
- `poseidon2_w16.go` — the width-16 Poseidon2 permutation with the exact
  `BABYBEAR_POSEIDON2_RC_16_*` constants of the fork's
  `default_babybear_poseidon2_16()`; width-generic engine so w24 follows as
  data. ~17k R1CS constraints per permutation.

Remaining milestone-2 work: the w24 instance, the DuplexChallenger transcript
(fixture-validated), Merkle paths, and the batch-STARK/FRI verification body
(teeth 1–2) — see ETH-NATIVE-WRAP.md §3–4.

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
