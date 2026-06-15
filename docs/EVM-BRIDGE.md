# The EVM Bridge

How dregg connects to EVM chains: an EVM contract that **trusts dregg's whole
finalized history** through one cheap pairing check, and a **lock-mint value
bridge** that moves assets across the seam with no trusted relayer — both sides
verifying the other's proof.

dregg proves with Plonky3: a recursive STARK over the BabyBear field
(`p = 2³¹ − 2²⁷ + 1`), Poseidon2 hashing, FRI low-degree testing. That is
post-quantum and fast to verify *off*-chain (16 ms for the whole-chain root),
but FRI verification on the EVM is hundreds of thousands of field operations and
Merkle-path checks — tens of millions of gas, not viable. The bridge exists to
close that gap. Its keystone is a **wrap**: recompress the dregg aggregate into a
constant-size SNARK a ~270k-gas Solidity verifier checks.

This document is first-principles and present tense. The two halves are
independent and compose; the wrap (§2) is the trust foundation the value bridge
(§3) settles against.

---

## 1. What exists today

Two EVM-facing artifacts are already in the tree. They are complementary, not
redundant, and neither is finished — but together they pin almost the entire
surface around one named cryptographic gap.

### 1.1 `bridge/src/ethereum.rs` — the settlement scaffold (backend-agnostic)

The clean, dependency-light half: a settlement state machine plus the EVM
calldata format, with the SNARK wrap named as the gap rather than faked.

- **`EthSettlementProof`** — the artifact: SNARK proof bytes + the four public
  inputs the EVM verifier binds + the verifying-key hash + a commitment to the
  wrapped recursive root.
- **`EthPublicInputs`** — exactly the four values the whole-chain STARK exposes:
  `genesis_root`, `final_root`, `num_turns`, `chain_digest`, re-encoded as EVM
  words. (These are identical to `WholeChainProof`'s public values — §2.1.)
- **`SnarkSystem`** — `Groth16Bn254` | `PlonkBn254` | `BindingOnly`. The
  `BindingOnly` variant is a BLAKE3 binding (NOT a SNARK) that lets the whole
  settlement state machine run and be tested end-to-end while the real wrapper is
  integrated. `is_snark_backed()` gates production on a real system.
- **`EthBridgeState` / `submit_eth_settlement` / `confirm_eth_settlement`** — a
  monotone chain of `(old_root → new_root)` advances, each gated on continuity
  (the temporal binding: an advance's `old_root` must equal the current proven
  root) and monotone height, awaiting EVM confirmation. This mirrors
  `bridge::mina::MinaBridgeState` exactly.
- **`solidity_verifier_interface()`** — the `IDreggSettlement` ABI the on-chain
  verifier must expose, pinned as a reference string so the contract and the
  bridge stay in lockstep. `settle(uint256[2] a, uint256[2][2] b, uint256[2] c,
  bytes32 genesisRoot, bytes32 finalRoot, uint64 numTurns, bytes32 chainDigest)`.
- **The calldata codec** (`to_calldata` + `public_input_tail` / `from_tail` +
  `Groth16Calldata::from_proof_bytes`) — encodes the proof+publics into the
  `settle` calldata and slices the 256-byte Groth16 proof into its `(A, B, C)`
  points in the exact word order the EIP-197 pairing precompile consumes. Tested
  round-trip (`public_inputs_tail_round_trips`, `groth16_calldata_slices_abc`).

**Honest gap, as the module states:** the cryptographic core NOT in this module
is the SNARK circuit that encodes the Plonky3/BabyBear STARK verifier (and its
proving/verifying keys). Everything *around* it — calldata shape, public-input
binding, settlement state machine, Solidity ABI — is built, so dropping in a real
prover is a localized change to `wrap_for_ethereum`.

### 1.2 `chain/` — the SP1 integration (concrete, but stale)

The concrete half: a real SP1 zkVM integration with deployable contracts, in its
own Cargo workspace (SP1's dep tree pins `generic-array = 1.1.0`, which conflicts
with the main workspace's `nova-snark`).

- **`chain/program/src/main.rs`** — an SP1 guest program: a STARK verifier
  compiled to `riscv32im-succinct-zkvm-elf` that SP1 then wraps in Groth16.
- **`chain/contracts/DreggVault.sol`** — a real lock-mint vault: `deposit`
  creates a note commitment; `withdraw` requires an SP1-wrapped proof, delegated
  to the **SP1 Verifier Gateway** (a deterministic CREATE2 deployment, same
  address on every EVM chain) checked against a `programVkey`. Tracks a
  note-commitment tree and a spent-nullifier set (Tornado-Cash-shaped).
- **`chain/contracts/DreggCredentialGate.sol`**, `chain/src/{prove,verify,
  bridge,withdraw,listener}.rs` — the host-side prove/verify/submit flow and an
  event listener, behind `mock` (default) / `prove` / `on-chain` features.

**The stale part (the crate says so):** the guest's STARK verifier predates the
Plonky3 cutover. `chain/src/lib.rs`: *"The guest program's STARK verifier is
incompatible with the current circuit crate (which uses Plonky3). Do not use for
real proofs until the guest is regenerated against the Plonky3 backend."* Mock
mode passes; real proving needs the `sp1up` toolchain and is not in CI.

### 1.3 The assessment

| piece | state | verdict |
|---|---|---|
| `ethereum.rs` settlement state machine + continuity | real, green | keep — it is the settlement spine |
| `ethereum.rs` calldata codec + Solidity ABI | real, green | keep — matches the PoC's 256-byte proof exactly |
| `ethereum.rs` `BindingOnly` scaffold | real, green | keep as the dev/test harness; never production |
| `ethereum.rs` SNARK wrap | **named gap** | the keystone — §2 |
| `chain/` Solidity (`DreggVault`, gateway delegation) | real | keep — the value-bridge EVM side |
| `chain/` SP1 guest STARK verifier | **stale (pre-Plonky3)** | regenerate or replace — §2.4 |

The bridge is not a green field. It is **~80% scaffolded around one gap**: a
Plonky3/BabyBear STARK verifier expressed as a BN254 SNARK. Everything in this
document orbits that gap.

---

## 2. The keystone: the trust bridge (wrap)

**The goal:** an EVM contract trusts dregg state — "the dregg chain advanced from
`genesis_root` to `final_root` over `num_turns` correctly-executed, correctly-
ordered finalized turns" — by checking ONE cheap proof, with no relayer it must
trust. A light client on the EVM, in ~270k gas.

### 2.1 What dregg already produces (the input to the wrap)

`circuit/src/ivc_turn_chain.rs::WholeChainProof` is dregg's whole-history
aggregate: one recursive batch-STARK that attests every one of `num_turns`
finalized turns executed correctly, in order, folding `genesis_root → final_root`,
with `chain_digest` committing to the exact ordered `(old_root, new_root)`
sequence. Its public values are exactly four BabyBear field elements:

```
[genesis_root, final_root, num_turns, chain_digest]
```

`lightclient/src/lib.rs::verify_history` checks it (re-witnessing nothing: VK-
fingerprint pin + claimed-publics attestation + one recursive STARK verify, cost
independent of history length), and `verify_finalized_history` adds the BFT
finality leg (a super-ratification quorum `≥ 2n/3 + 1` over `final_root`). Off-
chain this is **502 KiB / 16 ms verify** (measured, `docs/PROOF-ECONOMICS.md`).

The wrap's job: turn that 502 KiB / FRI-heavy artifact into a ~260-byte SNARK
whose **public inputs are those same four values**, so an EVM verifier binds the
identical claim.

### 2.2 Why a direct FRI verifier on the EVM is out

A Solidity contract verifying the BabyBear FRI proof directly would run, per the
proof economics: the recursion root opens ~38 FRI queries, each a Merkle path of
Poseidon2 compressions over a wide committed row, plus out-of-domain evaluations
and the Fiat-Shamir transcript. That is hundreds of thousands of field ops and
Keccak/Poseidon hashes — **tens of millions of gas**. Even if affordable it would
be fragile (every FRI-param or VK bump re-touches the contract). Direct FRI is a
non-starter; the wrap is not an optimization, it is the only viable shape.

### 2.3 The wrap: BabyBear-STARK-verifier-in-a-BN254-SNARK

The production-proven pattern (SP1, RISC Zero, Polygon zkEVM, Herodotus/STWO):

```
recursive STARK (BabyBear)          ← dregg WholeChainProof.root (502 KiB)
      │  recompress STARK→STARK (Plonky3 recursion; already dregg's fold)
      │  then WRAP: a SNARK circuit that IS the STARK verifier
Groth16 / PLONK proof over BN254    ← ~260 B, constant-size, pairing-checkable
      │  submit (A,B,C) + 4 publics as calldata
EVM verification (~270k gas)        ← ONE pairing check via the EIP-197 precompile
```

The wrap circuit's statement is: *"I verified a `WholeChainProof.root` against the
honest root VK, and these four field elements are its genuine public values."*
Compiled to a Groth16/PLONK circuit over BN254 and proven once, the result is a
constant-size proof a standard Solidity `Pairing.verify` checks natively (BN254
has the EIP-196/197 precompiles).

**Who does this, concretely:**

- **SP1 (Succinct)** is built on Plonky3 and ships a gnark Groth16/PLONK BN254
  wrapper as its final EVM-settlement step. Measured, production: **Groth16 ~260
  bytes / ~270k gas; PLONK ~868 bytes / ~300k gas** (PLONK adds ~1m30s prover,
  needs no per-circuit ceremony). This is dregg's gas/size target, and it matches
  the 256-byte shape `ethereum.rs` already pins. Trusted setup reuses the Aztec
  Ignition ceremony.
- **RISC Zero** ships the same STARK→Groth16 BN254 wrap (its "Groth16 receipt").
- **Herodotus `stwo-gnark-verifier`** wraps a *non-zkVM* STARK (StarkWare's
  Circle-STARK over M31) into Groth16 with gnark — implementing M31/QM31 field
  arithmetic, Circle-FRI, and Blake2s-Merkle verification *inside* the gnark
  circuit. This is the closest precedent for what dregg needs: a STARK-verifier
  gnark circuit that is **statement-specific** (tailored to one AIR + one FRI
  config), not a generic zkVM.

**The crate/path reality (the honest nuance that picks the rung):** dregg does
NOT prove with a zkVM. It uses raw Plonky3 `uni-stark`/`batch-stark`
(`Plonky3/Plonky3@82cfad73`) plus a custom recursion fork
(`emberian/plonky3-recursion`). Two consequences:

1. **dregg cannot just "use SP1's Groth16 wrapper."** SP1's wrapper verifies
   SP1's *own* recursion VK — its fixed RISC-V zkVM STARK shape — not dregg's
   `WholeChainProof.root`. The Groth16 *math* and the ~270k-gas verifier are
   reusable; the *circuit inside* is not.
2. **Plonky3-recursion compresses STARK→STARK only.** It has no BN254 terminal
   wrap ("built entirely on Plonky3's own STARK primitives — no separate
   plonkish SNARK wrapper"). The final BN254 SNARK is a *separate* gnark step,
   outside Plonky3, exactly as in SP1/STWO.

So the keystone gap is precise: **a gnark (or arkworks) circuit that verifies
dregg's BabyBear FRI recursion root, terminating in a BN254 Groth16/PLONK proof
over the four dregg public inputs.** Three ways to fill it (§2.4).

### 2.4 Three rungs to fill the wrap gap

Ordered by build cost; (B) is the recommended near-term path.

- **(A) Bespoke gnark STARK-verifier circuit (the STWO pattern, retargeted).**
  Implement BabyBear field arithmetic, Poseidon2, and FRI verification for
  dregg's recursion-root AIR *inside* a gnark circuit; terminate in Groth16
  BN254. Highest fidelity (no extra trust, no zkVM overhead), highest effort
  (large, security-critical, must track the dregg AIR + FRI params), and the
  trickiest to keep in lockstep with circuit changes — the same drift that
  stranded `chain/`'s guest. This is the long-run "pure" answer.

- **(B) Re-host the dregg verifier in a zkVM, reuse its audited wrapper
  (RECOMMENDED near-term).** Run dregg's *native Plonky3 verifier* (the real
  `verify_turn_chain_recursive`, compiled to the zkVM target) as the guest of
  SP1 or RISC Zero, and settle *their* battle-tested Groth16 BN254 proof. The
  guest's public outputs are the four dregg roots; the zkVM's existing wrapper +
  deployed Verifier Gateway do the rest at the measured ~270k gas. This is
  precisely what `chain/` set out to do — the only fix it needs is **regenerating
  the guest against the current Plonky3 backend** (today's guest hand-rolls a
  pre-Plonky3 verifier). Trade-off: a zkVM-execution trust layer + heavier proving
  than (A), bought back by a vetted, deployed wrapper and Gateway and far less
  bespoke crypto. The memory note holds: *pull in a vetted component, don't ship
  bespoke crypto.*

- **(C) Wait on / contribute a Plonky3-native BN254 terminal.** If the Plonky3-
  recursion roadmap (or the `emberian/plonky3-recursion` fork) adds a gnark/Halo2
  BN254 wrap, (A)'s effort drops to wiring. Track, don't block on it.

**Recommendation: (B) now, (A) later.** (B) reuses the `chain/` contracts and a
deployed verifier and reaches a live EVM testnet settlement fastest; (A) is the
eventual trust-minimizing endpoint when the bespoke circuit is worth its audit.
Either way the EVM-facing half — calldata, publics, pairing — is identical and is
what the PoC measures (§4).

---

## 3. The value bridge: lock-mint

The trust bridge (§2) lets each side verify the other's state. The value bridge
moves assets across that seam: **lock value in an EVM contract ↔ mint the
mirrored asset on dregg**, and **burn-to-unlock** back — each direction gated by a
verified proof of the other side's state. No trusted relayer: the relayer is a
liveness convenience, never a trust root.

### 3.1 EVM → dregg (lock on EVM, mint on dregg)

1. A user calls `DreggVault.deposit(token, amount, noteCommitment)` on the EVM
   chain. The vault escrows the ERC-20/ETH and records the note commitment in its
   on-chain note tree (`chain/contracts/DreggVault.sol`, already written).
2. dregg must learn the lock happened, *trustlessly*. The dregg side verifies the
   EVM lock by checking Ethereum's own consensus + an inclusion/event proof —
   which requires, in the dregg circuit: **keccak256** (block-header and log
   hashing), **secp256k1** (if validating signatures), **RLP** decoding, and
   **Merkle-Patricia-Trie** proof verification (the receipt/storage proof that the
   `Deposit` event is in a finalized block). This is an *Ethereum light client in
   a Plonky3 circuit*.
3. On a verified lock, dregg mints the mirrored note. The mint's cryptographic
   core already exists: `bridge/src/action_binding.rs` +
   `circuit/src/bridge_action_air.rs` pin `(nullifier, recipient,
   destination_federation, amount)` at **full byte/bit fidelity** (the full 32
   bytes of each hash, the full 64-bit amount — no Poseidon2 felt-compression, no
   30-bit amount truncation). The executor mints to `recipient` for `amount`.

**Cost of the in-circuit Ethereum light client (the EVM→dregg hard part):**
keccak and MPT/RLP in a STARK trace are heavy — a keccak permutation is ~150k+
constraints in typical AIRs, an MPT proof is a logarithmic chain of them. Two
mitigations: (i) verify against **finalized** headers only (post-Merge: a synced
beacon-committee signature, or a checkpoint header the federation co-signs), so
the in-circuit work is one header + one receipt proof, not a re-execution; (ii)
**trust-in-observation as the v1 fallback** — the federation runs an EVM observer
(exactly the `bridge::midnight_observer` pattern, which already watches a foreign
chain's finalized blocks and mirrors `Lock`/`Unlock` events into dregg consensus
with crash-recovery + idempotent dedup). v1 is observer-attested (relayer
liveness, federation-quorum safety); v2 hardens to the in-circuit light client.

### 3.2 dregg → EVM (burn on dregg, unlock on EVM)

1. A user burns the dregg note (spends it to the bridge cell), producing the
   `note_spending` proof (spend authority + Merkle membership in the source
   federation note tree) plus the `bridge_action` proof (the full-fidelity
   `(nullifier, recipient, amount)` binding). Both already exist
   (`cell::note_bridge::PortableNoteProof` + `bridge::action_binding`).
2. The EVM side must verify dregg's state to honor the unlock. It does so via the
   **trust bridge (§2)**: the dregg whole-chain root that includes the burn is
   wrapped to a SNARK and settled to the EVM verifier (~270k gas). The unlock is
   authorized against the settled `final_root` + a Merkle/nullifier proof that the
   burn note is spent in that proven state.
3. `DreggVault.withdraw` releases the escrowed value to `recipient` for `amount`,
   marking the `nullifier` spent (its double-spend guard already in the contract).

This direction is **fully trustless** the moment §2 lands: the EVM checks dregg's
proof; no observer, no relayer trust. The `nullifier` set on each side prevents
double-mint/double-unlock; the §2 continuity chain prevents settling a forked
history.

### 3.3 The security model in one line

Both sides verify the other's consensus/proof: the **EVM side checks dregg's proof
via §2's wrap**; the **dregg side checks the EVM lock via an Ethereum light-client
/ event proof in-circuit** (v2) or via a federation-quorum observer (v1). The
relayer carries bytes, never trust. Conservation is enforced per direction by the
escrow + the full-fidelity `(amount, recipient, nullifier)` binding AIR, with the
nullifier sets closing replay.

---

## 4. The feasibility PoC (with a number)

The decisive question for the keystone is: *does the EVM-facing half actually
work, end to end, with a real proof, at the claimed size and gas?* The PoC at
**`/tmp/dregg-evm-wrap-poc/`** (standalone crate, the stable arkworks-0.4 BN254
set, isolated from the workspace's ark-0.5 pins) answers it.

It builds the exact EVM-facing Groth16 instance — a BN254 circuit whose **four
public inputs ARE the dregg whole-chain commitments** `[genesis_root, final_root,
num_turns, chain_digest]` — runs the **real BN254 pairing verify** (the operation
the EVM precompile performs), and emits the proof in the precise 256-byte
`(A,B,C)` calldata layout `bridge/ethereum.rs` pins. Measured:

```
Groth16/BN254 (the EVM-facing wrap half), arkworks, real pairing check:
  honest proof verifies : true
  tampered final_root   : REJECTED   ← the four dregg roots are load-bearing
  proof, compressed     : 128 bytes
  proof, EVM calldata   : 256 bytes  (A: G1 64 + B: G2 128 + C: G1 64)
  + 4 public-input words : 384 bytes total settle() calldata
  verifying key         : 392 bytes  (deployed once)
  verify (off-chain)    : ~1.1 ms
EVM gas envelope (SP1 production verifier, this exact pairing):
  Groth16 : ~270,000 gas   (constant, K-independent)
  PLONK   : ~300,000 gas   (no per-circuit ceremony)
```

The 256-byte proof shape matches `EthSettlementProof`'s pinned layout exactly,
and the `Groth16Calldata::from_proof_bytes` codec in `ethereum.rs` slices it into
the `(A,B,C)` words the Solidity `settle` ABI + EIP-197 precompile consume (green
test). **The EVM-facing seam is real and measured.**

**What the PoC deliberately stubs (and the doc is honest about):** the *inside* of
the wrap circuit — the in-circuit BabyBear-FRI verifier that proves the four
public inputs are a genuine `WholeChainProof.root`'s values. In the PoC those four
are bound as public inputs with a placeholder witness so the SNARK runs on the
real shape; swapping the placeholder for the FRI-verifier constraints is the
§2.4-(A) circuit or the §2.4-(B) zkVM guest. The PoC proves the half that was
hand-waved ("the EVM verifier's job") and leaves the half that is genuinely large.

**Also landed, in-workspace and green (`cargo test -p dregg-bridge`, 7/7
ethereum tests):** the bridge-side calldata codec that was missing — the inverse
of `to_calldata` (`EthPublicInputs::from_tail`) and the Groth16 point slicer
(`Groth16Calldata::from_proof_bytes`), both round-trip tested. This is the
permanent bridge seam the relayer uses to read a `settle` calldata back into typed
dregg commitments and to hand `(A,B,C)` to the verifier.

### 4.1 The running end-to-end PoC (§2.4-(B), the zkVM wrap, built)

The §4 PoC stubbed the *inside* of the wrap. **`/tmp/dregg-evm-e2e/`** fills it
via rung (B): dregg's OWN verifier runs inside a RISC Zero zkVM, is wrapped to a
Groth16/BN254 receipt, and is verified **on-chain** by the REAL
`RiscZeroGroth16Verifier` in a real EVM (anvil/foundry) — which then drives the
bridge (`DreggBridgeVault.sol`: `attestTurn`, `lockForDregg`, `unlockFromDregg`,
and `driveTurn` — an EVM contract issuing a dregg-turn intent gated on a verified
dregg-state proof). Every interface is the real one.

What this validated, and the findings that matter:

- **The whole production verifier cross-compiles into the zkVM guest.** The full
  `dregg-circuit --features verifier` tree — `verify_vm_descriptor2` plus all of
  Plonky3 (`p3-batch-stark`, `p3-fri`, `p3-poseidon2`, …) — compiles to
  `riscv32im-risc0-zkvm-elf`. The two classic guest-build blockers (getrandom has
  no zkVM backend; `__atomic_*` intrinsics) are set automatically by
  `risc0_build::embed_methods` (`getrandom_backend="custom"` + `passes=lower-atomic`).
  No bespoke crypto, no FRI-verifier-circuit to write or audit — this is why (B)
  is the **easiest path to a first ship**, the inverse of (A)'s cost profile.

- **Use the PRODUCTION Poseidon2 verifier, NOT the experimental BLAKE3 one.** The
  first guest mistakenly verified `bridge_action_air` via the from-scratch
  `circuit/src/stark.rs` — which is explicitly `ProofTier::Experimental` and uses
  **BLAKE3** Merkle. RISC Zero has no BLAKE3 accelerator, so the guest paid full
  unaccelerated cost for thousands of Merkle-path hashes (the base zkVM proof ran
  >200 CPU-minutes and did not finish on a laptop). The fix is the production path:
  `verify_vm_descriptor2` (the IR-v2 multi-table batch STARK, the actual
  turn-proof verifier) uses **Poseidon2** over BabyBear — field arithmetic the
  zkVM does natively — which is both *more real* (the production prover) and an
  order of magnitude cheaper to prove in-circuit. The guest at
  `methods/guest/src/main.rs` runs `verify_vm_descriptor2` over a real transfer
  turn-descriptor proof.

- **The EVM half is fully de-risked.** Real `RiscZeroGroth16Verifier` +
  `DreggBridgeVault` compile under foundry; control IDs are version-matched to
  risc0-zkvm 3.0.5 (`CONTROL_ROOT` identical, `BN254_CONTROL_ID` byte-reversed
  exactly as the verifier constructor expects); the `verify(seal, imageId,
  journalDigest)` calldata is produced by `encode_seal`; the journal slicing
  decodes the verified turn's public inputs correctly in-contract.

- **Run the wrap on real hardware.** The STARK→Groth16 wrap is CPU/RAM-heavy; do
  it on a 24-core box (persvati), not a laptop. With Poseidon2 the guest is far
  lighter than the BLAKE3 attempt.

The honest residual (same boundary, now inside a running loop): the guest verifies
a single turn-descriptor proof, not yet the full `WholeChainProof` recursion root
(`verify_history`) — a one-line guest swap to the heavier root verifier, same
shape. And the zkVM is the *easiest* wrap to ship, not the *cheapest to prove*; §2.4
keeps (A)/(C) as the cost-optimization rungs.

### 4.2 The cost-optimization endgame: a Plonky3-native BN254 terminal (§2.4-(C))

RISC-V'ing the verifier (B) is the easiest build but the most expensive to *prove*
— you pay to prove a whole RISC-V execution of the verifier, not just its math. The
cheaper-to-prove answers, in increasing elegance:

- **(A) a bespoke gnark Poseidon2-FRI verifier circuit** — encode only the
  verifier's arithmetic (the SP1 / `stwo-gnark-verifier` pattern), ~10-100× fewer
  constraints than the zkVM, at the cost of a new security-critical circuit to
  audit.
- **(C) make dregg's own recursion terminate in a BN254 SNARK.** dregg already
  does STARK→STARK recursion (`emberian/plonky3-recursion`, the `WholeChainProof`
  fold). The missing piece is a *terminal* layer whose output is a BN254
  Groth16/Halo2 proof instead of another BabyBear STARK — the exact gap the doc
  found ("no separate plonkish SNARK wrapper" in Plonky3-recursion). Building it
  (e.g. a new `emberian/plonky3-bn254-wrap`) is the elegant endgame: no RISC-V
  overhead, no separate FRI-verifier circuit. It is genuine research-grade work
  (a BN254-field recursion layer + the Groth16/Halo2 terminal — what SP1 built
  internally), so it is a tracked *next project*, NOT a prerequisite for the first
  ship. **Ship (B), build (C).**

---

## 5. The buildable plan, rung by rung

Each rung is independently shippable and leaves a testable artifact.

1. **[done] Settlement spine + calldata codec.** `ethereum.rs`: state machine,
   continuity, Solidity ABI, the proof↔calldata codec (this lane added the
   decoder + Groth16 slicer). Green.
2. **[done] EVM-facing wrap feasibility.** `/tmp/dregg-evm-wrap-poc`: real BN254
   Groth16 proof over the four dregg roots, real pairing verify, 256-byte
   calldata, ~270k-gas envelope. Green.
3. **Pick the wrap rung (§2.4).** Decision: **(B)** re-host dregg's native
   Plonky3 `verify_turn_chain_recursive` as an SP1/RISC0 guest. Concretely:
   regenerate `chain/program` against the current Plonky3 backend (the guest's
   public outputs = the four dregg roots), drop the stale hand-rolled verifier.
   *Decisive artifact:* one real SP1 Groth16 proof of one real `WholeChainProof`,
   verified by `cargo test --features prove` (needs `sp1up`).
4. **Wire the real proof into the settlement machine.** Replace `BindingOnly`
   with `Groth16Bn254` in `submit_eth_settlement`: the 256-byte SP1 proof flows
   through the codec (rung 1) into `EthSettlementProof`. Local `ark-groth16`
   verify (the PoC's pairing check) as a pre-submit guard. *Artifact:* a green
   end-to-end test from `WholeChainProof` → `EthSettlementProof` → local pairing
   verify, no chain.
5. **Deploy + settle on an EVM testnet.** Deploy the SP1 Verifier Gateway binding
   + `DreggVault` (Base Sepolia). Submit a real settlement; confirm `provenRoot`
   advances. *Artifact:* an on-chain `Settled(oldRoot, newRoot, height)` event for
   a real dregg history. This is the headline ("a number attached" → "a tx hash
   attached").
6. **Value bridge v1 (observer-attested).** Stand up the EVM observer
   (`midnight_observer` pattern, retargeted to EVM logs via alloy): watch
   `DreggVault.Deposit`, mirror to dregg consensus, mint via `bridge_action`.
   dregg→EVM unlock rides rung 5's settled root. *Artifact:* a round-trip lock→
   mint→burn→unlock on testnet.
7. **Value bridge v2 (trustless EVM→dregg).** Replace the observer with the
   in-circuit Ethereum light client (§3.1): keccak + RLP + MPT verification of a
   finalized `Deposit` receipt proof in a Plonky3 circuit. Removes the last
   relayer-trust assumption. The hard rung — gated behind a keccak/MPT AIR; until
   then v1's federation-quorum observer is the honest floor.
8. **[later] Bespoke gnark wrap (§2.4-A).** When the bespoke BabyBear-FRI gnark
   circuit is worth its audit, swap the zkVM guest for it — same EVM seam, zero
   zkVM trust layer, smaller prover.

The through-line: the bridge is already scaffolded around one gap — a
Plonky3/BabyBear STARK verifier as a BN254 SNARK. Rung 3 fills it by reusing a
vetted wrapper; rungs 4-5 carry a real dregg history onto a live EVM chain; rungs
6-7 move value across with the trust assumption shrinking each rung. The number is
attached (§4: ~270k gas, 256-byte proof, real pairing verify); the path is
buildable.
