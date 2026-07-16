# Native Proof Bridges: Ethereum (wrap) and Midnight (foreclosed)

> ⚑ **STATUS (2026-07-12):** this survey's ETH milestone 2 (an SP1/RISC0 zkVM
> guest) was superseded by the **native gnark circuit** path
> (`ETH-NATIVE-WRAP.md` → `WRAP-NATIVE-HASH-DECISION.md`), which is now built:
> a real Groth16 wrap (12.2M R1CS, dev trusted setup) settles a real proof in
> Foundry against the gnark-generated Solidity verifier, 25-lane statement
> bound, shrink + apex VKs pinned. Residuals (dev ceremony, fixture-lifted apex
> constant, 384-byte submitter blob, operator-attested `outboundMessageRoot`,
> assumed FRI low-degree) are listed in `WRAP-NATIVE-HASH-DECISION.md`
> §CURRENT STATE. The survey below stands as the feasibility record.

What it would take to settle a dregg whole-history proof *natively* — by proof,
not by federation attestation — onto an external chain. Grounded in the actual
proving stack at HEAD, not general ZK lore.

## 0. What our proof actually is

The finality artifact a light client keeps is `WholeChainProof`
(`circuit-prove/src/ivc_turn_chain.rs:1286`): a single recursive **batch-STARK**
over **BabyBear** (`p = 2^31 - 2^27 + 1`), degree-4 extension, **Poseidon2**
width-16 hash/compress/challenger, **FRI** with `log_blowup=3`, `38` queries,
`14` query-PoW bits → conjectured ~128-bit soundness
(`circuit-prove/src/plonky3_recursion_impl.rs:24-29`, `:248-310`). The whole
recursion tower is **BabyBear → BabyBear, FRI all the way** — STARK-into-STARK
in-circuit verification (`prove_recursive_layer_for_air`,
`plonky3_recursion_impl.rs:560`). There is **no pairing-friendly curve anywhere
in the stack**: the recursion fork (`github.com/emberian/plonky3-recursion`, pinned
at `Cargo.toml:208`; local `~/dev/plonky3-recursion`) has **zero** references to
`bn254`/`groth16`/`gnark`/`bls12`/`halo2`/`pairing`. It cannot emit a
curve-verifiable proof. (verified: grep over the fork tree, 0 hits.)

What a verifier checks for ONE whole-history proof —
`verify_turn_chain_recursive_from_parts` (`ivc_turn_chain.rs:2845`), three teeth:

1. **VK pin** — recompute `recursion_vk_fingerprint(root_proof)` (a blake3 over the
   root circuit's table shape + preprocessed Merkle commitment,
   `plonky3_recursion_impl.rs:646`) and compare to a trusted anchor `RecursionVk`.
2. **The root** — `verify_recursive_batch_proof` →
   `BatchStarkProver::verify_all_tables` (`plonky3_recursion_impl.rs:722`): the
   fork's batch-STARK FRI verifier, with the Poseidon2-w16, Poseidon2-w24,
   recompose, and expose_claim non-primitive tables registered.
3. **The segment tooth** — the root's exposed ordered segment `[first_old,
   last_new, count, acc]` must equal the carried public inputs
   `[genesis_root, final_root, num_turns, chain_digest]`.

Public inputs (`WholeChainProof`, `ivc_turn_chain.rs`): `genesis_root: [BabyBear;
SEG_ANCHOR_WIDTH]`, `final_root: [BabyBear; SEG_ANCHOR_WIDTH]`, `chain_digest:
[BabyBear; SEG_DIGEST_WIDTH]`, `num_turns: usize` — the roots and digest are now
each **8 BabyBear lanes** (`SEG_DIGEST_WIDTH = 8`, `SEG_ANCHOR_WIDTH = 8`; the
v11 8-felt ~124-bit faithful-commitment migration reaching the whole-chain
public-input shape — the host verifier's segment tooth reads them as
`genesis_root8`/`final_root8`/`chain_digest_0..`). Still all BabyBear limbs
(31-bit each) — they embed losslessly into any larger field (BN254/BLS12-381
scalars). The wire
envelope is `WholeChainProofBytes` (`:1357`), which carries the same publics
plus the `vk_fingerprint_hex` anchor. The Rust light client that runs teeth 1–3 is
`lightclient/src/lib.rs` (`verify_history`, `:183`; `AttestedHistory`, `:130`).

The verifier's *cost* is the obstruction: tooth 2 is hundreds of thousands of
BabyBear field ops + Poseidon2 Merkle-path hashing. Running it directly on the EVM
is tens of millions of gas — not viable (`bridge/src/ethereum.rs:7-11`).

## 1. Ethereum — the STARK→SNARK wrap (feasible)

The production pattern (SP1, RISC Zero, Polygon zkEVM): wrap the BabyBear STARK in
a SNARK over **BN254** (the curve with EVM pairing precompiles EIP-196/197), whose
circuit **is the STARK verifier**; the resulting Groth16 proof is ~256 bytes and a
Solidity verifier checks it in one pairing check for ~250–300k gas.

```
WholeChainProof (BabyBear recursive batch-STARK)
   │  wrap: a SNARK circuit that RUNS verify_turn_chain_recursive_from_parts
   ▼
Groth16/BN254 proof (≈256 B, 8 field elements)
   │  submit calldata
   ▼
Solidity IDreggSettlement.settle(...) — one EIP-197 pairing check, ~250–300k gas
```

### What already exists in-tree

- **`bridge/src/ethereum.rs`** — the full settlement scaffold: `EthSettlementProof`
  (`SnarkSystem::{Groth16Bn254, PlonkBn254, BindingOnly}`), `wrap_for_ethereum`,
  the 256-byte Groth16 `(A,B,C)` calldata slicer (`Groth16Calldata`,
  `:217`), the four-public-input EVM-word encoding (`EthPublicInputs`, `:260`,
  matching `WholeChainProof`'s publics), the `EthBridgeState` settlement state
  machine (continuity + monotone-height gated, mirroring `mina.rs`), and the
  `IDreggSettlement` Solidity ABI (`solidity_verifier_interface`, `:473`).
  Everything around the SNARK is built; dropping in a real prover is a localized
  change to `wrap_for_ethereum`.
- **`chain/`** (standalone workspace) — an SP1-based STARK→Groth16 path:
  `chain/program/src/main.rs` is an SP1 RISC-V guest that runs a STARK verifier and
  whose execution SP1 wraps to Groth16/BN254; `chain/src/{prove,verify,bridge}.rs`
  drive it; `chain/contracts/{DreggVault,DreggCredentialGate}.sol` are the deployed
  withdraw/credential verifiers. `plans/evm-bridge-rich.md` generalizes this to
  arbitrary Effect-VM turns.

### The honest gap (bigger than "drop in a prover")

The SP1 guest in `chain/program/src/main.rs` verifies a **legacy hand-rolled STARK
format** — `GuestStarkProof { trace_commitment, constraint_commitment,
fri_commitments, fri_final_poly, query_proofs, … }` (`chain/src/prove.rs:18`).
That is the **pre-Plonky3 bespoke verifier**, NOT the current `WholeChainProof`
(`BatchStarkProof<DreggRecursionConfig>` from the plonky3-recursion fork). The
current proof's verifier is the fork's `BatchStarkProver::verify_all_tables` plus
the VK-fingerprint pin and the segment tooth — a substantially larger verifier
than what the existing guest encodes.

So the missing wrapper is: **a SNARK circuit (SP1/RISC0 zkVM guest, OR a bespoke
gnark/halo2 circuit) that runs `verify_turn_chain_recursive_from_parts` over the
CURRENT fork proof format.** Two routes:

- **(a) zkVM route (recommended first):** compile the *current* fork batch-STARK
  verifier (`p3-circuit-prover`'s `verify_all_tables` over BabyBear + Poseidon2,
  the `recursion_vk_fingerprint` pin, the segment tooth) as a `no_std` RISC-V guest
  for SP1 (or RISC0), feed it `WholeChainProofBytes` + the four publics + the trust
  anchor, and let SP1's existing Groth16/BN254 wrapper produce the EVM proof. Reuses
  vetted, audited STARK→Groth16 tooling — no bespoke pairing crypto. Cost: the fork
  verifier must build under the zkVM target (`no_std`, the p3 crates are mostly
  `no_std`-friendly; the prover-only halves are not needed by the verifier), and the
  proving is a large zkVM run (minutes, GPU-class). This is the route
  `bridge/src/ethereum.rs:55-60` names as option (a).
- **(b) bespoke gnark/halo2 STARK-verifier circuit:** hand-write the BabyBear-FRI
  verifier as a BN254 circuit. Smaller proving cost, but a large security-critical
  artifact with a trusted setup — ill-advised to build bespoke (the memory note on
  vetted-component-vs-bespoke-crypto; `ethereum.rs:50-54`).

**Direct FRI-verifier-in-Solidity** (no wrap): not viable for our params. Tooth 2
re-checks 38 FRI queries each with a Poseidon2-w16 Merkle path of depth ~log(trace)
over BabyBear — each Poseidon2 permutation is dozens of BN254-field-foreign
BabyBear mults, ×38 queries ×~20 layers, plus the batch-STARK constraint
evaluation. That is the tens-of-millions-of-gas figure the module rejects up front.
The wrap exists precisely to move that work off-chain into the SNARK.

### Gas ballpark

The on-chain cost is independent of dregg's verifier size once wrapped: a Groth16
verifier on BN254 is **~250–300k gas** (one EIP-197 pairing of fixed size + a
handful of EIP-196 scalar-mults for the public inputs). PLONK/BN254 is somewhat
higher (~300–500k) but needs no per-circuit ceremony. The BabyBear publics (the
two 8-lane roots + 8-lane digest + `num_turns`) cost a few k gas to fold into the
pairing input. This is the SP1/RISC0 EVM-settlement
envelope, unchanged by what the SNARK wraps.

## 2. Midnight — native proof-carrying is foreclosed (by Midnight's architecture)

Not by SP1's output curve, but by Midnight itself
(`plans/midnight-bridge-production.md`, "Reassessment 2026-06-26";
`docs/deos/ZKIR-V3.md:30-38`):

- Midnight's contract proof system is **Halo2 + KZG over BLS12-381** (Jubjub as the
  in-circuit curve). There is **no STARK / FRI backend** — nothing on the chain
  speaks BabyBear/Poseidon2-FRI.
- A `ContractCall` carries a proof whose **verifier key is fixed per entry point at
  deployment**. There is **no generic in-circuit proof-verification / recursion
  primitive exposed to Compact authors** — a contract **cannot verify an arbitrary
  foreign proof**. (`ZKIR-V3.md:34-38`.)
- Therefore even a BLS12-381-*wrapped* dregg proof has nowhere to land: you would
  have to compile a **dregg-STARK verifier as a Compact circuit** (emulate
  BabyBear/FRI inside BLS12-381/Jubjub constraints — massive, no tooling), and the
  result is a Halo2 proof *of the verifier*, not a STARK verified natively. The
  ZKVM / field-independent-IR fallback (`proposals/0014`, `0021`) is an in-progress
  draft, explicitly not mainnet-targeted.

**Why ETH differs:** the EVM exposes a *general* BN254 pairing precompile
(EIP-197), so any contract can verify any Groth16/PLONK-BN254 proof against a VK it
chooses — the wrap lands. Midnight exposes only a *per-entry-point, fixed-VK*
verifier with no general verification primitive — the wrap has nowhere to land.

What the verified circuit *does* enable on Midnight is the **dregg-side fraud
proof**: an optimistic Level-1.5 bridge where the circuit proof is the objective
evidence a permissionless watchtower uses to challenge a false federation
attestation, turning 2/3-threshold trust into 1-of-N. That is already wired
(`bridge/src/midnight_verified.rs`, `midnight_gateway.rs`) and is the recommended
Midnight path — not a proof-carrying-onto-Midnight chase.

## 3. Verdict + first milestone

**Ethereum native proof-bridge: feasible.** The whole non-cryptographic half is
already built (`bridge/src/ethereum.rs`: calldata, public-input binding, settlement
state machine, Solidity ABI). The single missing piece is the **wrap prover that
verifies the CURRENT fork proof** — and the cleanest route reuses SP1/RISC0's
audited STARK→Groth16 wrapper rather than bespoke pairing crypto. The realistic
missing-wrapper size: a `no_std` port of `verify_turn_chain_recursive_from_parts`
(the fork `verify_all_tables` + VK pin + segment tooth) into a zkVM guest, then
threading SP1's Groth16 bytes into `wrap_for_ethereum(SnarkSystem::Groth16Bn254,
…)`. Weeks of integration (guest build under the zkVM target is the real work),
not a new proof system.

**Midnight native proof-bridge: foreclosed** (architectural, target-chain side).
Ship the optimistic + watchtower bridge that already exists.

### Scoped first milestone (ETH)

1. **Lock the settlement interface** — materialize the `IDreggSettlement` ABI from
   `ethereum.rs:473` as a real `chain/contracts/IDreggSettlement.sol` (done
   alongside this doc), and confirm `EthPublicInputs` ↔ `WholeChainProof` publics
   stay in lockstep. (Cheap, done.)
2. **Wrap-target spike** — stand up an SP1 (or RISC0) guest crate that builds the
   *current* fork batch-STARK verifier `no_std` and runs teeth 1–3 over a
   `WholeChainProofBytes` fixture from `lightclient`'s test history. Success
   criterion: the guest *accepts* a genuine whole-history proof and *rejects* a
   tampered one, inside the zkVM, with no `chain/`-legacy `GuestStarkProof` types.
   This is the load-bearing unknown (does the fork verifier compile + run under the
   zkVM target). Everything downstream (SP1 Groth16 wrap → `wrap_for_ethereum` →
   `settle`) is integration over vetted tooling.
3. **End-to-end on a testnet** — SP1 Groth16 bytes → `wrap_for_ethereum` →
   `submit_eth_settlement` → deployed `IDreggSettlement` on an EVM testnet; one real
   `Settled(oldRoot, newRoot, height)` event.

The wrap-circuit spec is exactly §0's three teeth over the §0 public inputs — the
guest's job is to be a faithful, `no_std`, in-zkVM transcription of
`verify_turn_chain_recursive_from_parts` (`ivc_turn_chain.rs:2845`).
