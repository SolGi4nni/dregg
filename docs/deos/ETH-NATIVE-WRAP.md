# ETH Native Wrap: a fast native-circuit proof bridge (retiring the SP1 path)

> ⚠ **CORRECTION (2026-07-11) — see `WRAP-NATIVE-HASH-DECISION.md`.** This doc's
> efficiency premise (proving cost ∝ constraint count ≈ the verifier's field ops,
> implying seconds) is INCOMPLETE: it planned the gnark circuit around **BabyBear**
> Poseidon2 gadgets, which are EMULATED in BN254 at a **measured 16,837 R1CS per
> Merkle compress** — so a FRI verifier's ~1,000+ hashes would be ~20–70M
> constraints (GPU-class minutes, no better than SP1). The fix is the RISC0/SP1
> standard: a **BN254-native-hash outer "shrink" layer** so the gnark verifier
> hashes natively (**187 R1CS/compress, a 90–145× cut** → ~1–6M total). The IVC,
> the Groth16 EVM verifier, and the FRI-verify *structure* below all stay; the
> **hash + challenger** gadgets switch to native BN254. Read the decision doc first.

A modern replacement for dregg's legacy SP1 RISC-V-zkVM Ethereum bridge. The goal
is unchanged — settle a dregg whole-history proof on Ethereum by **proof**, one
~250–300k-gas Groth16 check — but the *wrap prover* is rebuilt as a **native
arithmetic circuit** that verifies the dregg Plonky3 FRI proof directly, with no
RISC-V emulation layer. Grounded in the proving stack at HEAD.

> Companion to `docs/deos/NATIVE-PROOF-BRIDGES.md` (the feasibility survey). This
> doc is the *replacement design + plan*. Where the two disagree on FRI knobs,
> this one is correct: the root proof is verified at `ir2_leaf_wrap_config`
> (log_blowup 6 / 19 queries / 16 PoW), not the default `create_recursion_config`.

## 0. The artifact and the verifier we must wrap

> **CORRECTION (2026-07-11, census `docs/FINDING-chain-participation-census.md`):** the
> public-input shape below is stale. Post-v11 the claim is **25 BabyBear lanes**:
> `genesis_root: [BabyBear; 8]`, `final_root: [BabyBear; 8]`, `num_turns` (1),
> `chain_digest: [BabyBear; 8]` (`SEG_ANCHOR_WIDTH = 8` at `ivc_turn_chain.rs:267`,
> `SEG_DIGEST_WIDTH = 8` at `:254`, host tooth `:2807-2811`, wire envelope v3).
> The gnark circuit's public-input vector, `EthPublicInputs`, and the
> `IDreggSettlement.settle` ABI must all target the 25-lane statement — the
> single-`bytes32`-per-root shapes in `bridge/src/ethereum.rs` and
> `chain/contracts/IDreggSettlement.sol` are pre-widening and must be regenerated
> with the wrap (milestone 1/4).

The finality artifact is `WholeChainProof` (`circuit-prove/src/ivc_turn_chain.rs:1286`):
a single recursive **batch-STARK** over **BabyBear** (`p = 2^31 − 2^27 + 1`),
degree-4 extension, **Poseidon2** (width-16 challenger/hash + width-24 for the
isolated segment-digest sponge), **FRI**. Its four public inputs
(`:1296–1304`) are `genesis_root: BabyBear`, `final_root: BabyBear`,
`chain_digest: [BabyBear; 4]` (`SEG_DIGEST_WIDTH = 4`, `:249`), `num_turns: usize`
— all BabyBear (31-bit), which embed losslessly into any larger scalar field.
*(Stale — see the correction banner above.)*

The verifier the wrap circuit must reproduce is
`verify_turn_chain_recursive_from_parts` (`ivc_turn_chain.rs:2845`), three teeth:

1. **VK pin** — `recursion_vk_fingerprint(root_proof)`
   (`plonky3_recursion_impl.rs:646`): a blake3 over the root circuit's table
   shape (`table_packing`, `rows`, `degree_bits`, the non-primitive op manifest,
   and the preprocessed Merkle commitment) compared against a trusted
   `RecursionVk` anchor.
2. **The root** — `verify_recursive_batch_proof_with_config(root_proof,
   ir2_leaf_wrap_config())` (`ivc_turn_chain.rs:2873` → `plonky3_recursion_impl.rs:732`)
   → `BatchStarkProver::verify_all_tables` with the **Poseidon2-w16**,
   **Poseidon2-w24**, **recompose**, and **expose_claim** non-primitive tables
   registered (`:739–748`). This is the fork's batch-STARK FRI verifier.
   **FRI knobs (load-bearing): `ir2_leaf_wrap_config` — log_blowup 6, 19 queries,
   16 query-PoW bits, max_log_arity 3** (`ivc_turn_chain.rs:1055–1137`,
   `1137 fn ir2_leaf_wrap_config`). Conjectured soundness ≈ `6·19 + 16 = 130`
   bits.
3. **The segment tooth** — the root's `expose_claim` table exposes the ordered
   segment `[first_old, last_new, count, acc_0..acc_3]`; it must equal the
   carried `[genesis_root, final_root, num_turns, chain_digest]` (`:2887–2905`).

The Rust light client that runs teeth 1–3 today is `lightclient/src/lib.rs`
(`verify_history`).

## 1. Why the SP1 path is slow (the emulation tax)

The legacy bridge is `chain/` (standalone workspace). `chain/program/src/main.rs`
is an **SP1 RISC-V guest** that runs a STARK verifier; `chain/src/prove.rs`
(`real_wrap`, `:314`) drives `cargo prove` → SP1 → Groth16/BN254. It is slow —
and stale — for two compounding reasons.

### 1a. It proves the wrong thing (legacy format)

The guest verifies `GuestStarkProof { trace_commitment, constraint_commitment,
fri_commitments, fri_final_poly, query_proofs, … }` (`chain/src/prove.rs:18`,
mirrored in `chain/program/src/main.rs:86`) — a **pre-Plonky3, hand-rolled**
verifier: blake3 Merkle trees (`hash_node`, `main.rs:191`), a bespoke
`MerkleStarkAir` 6-column constraint (`main.rs:305–318`), `BLOWUP = 4`. That is
*not* `WholeChainProof` (`BatchStarkProof<DreggRecursionConfig>`). So even before
performance, the SP1 path verifies an artifact dregg no longer produces. It is
legacy twice over.

### 1b. The emulation tax (the actual slowness)

SP1 proves **RISC-V execution of the verifier**, not the verifier's arithmetic.
The cost model:

- Every BabyBear field op the verifier performs is compiled to a *sequence* of
  RISC-V instructions — a `mul` plus a modular reduction (Montgomery/Barrett) is
  on the order of **~10–40 RISC-V cycles**, and **each cycle is a constrained row**
  in the zkVM execution trace (plus the memory-argument and instruction-decode
  rows the zkVM pays on every cycle regardless of the op).
- A Poseidon2-w16 permutation is hundreds of BabyBear mults; the FRI verifier
  does **19 queries × ~20 Merkle layers × a Poseidon2 compress each**, plus the
  per-table constraint/quotient evaluation and the logup bus checks. That is on
  the order of **millions of BabyBear ops** in the *native* verifier.
- Run through the RISC-V interpreter, those millions of native ops balloon to
  **tens-to-hundreds of millions of zkVM cycles** — a roughly **1–2
  orders-of-magnitude** blowup purely from emulating an interpreter (decode →
  execute → memory) on top of the arithmetic that matters.
- Then SP1's own STARK→Groth16 *wrap* of that giant trace is itself a multi-stage
  recursive proving step.

Net: the SP1 wrap is a large GPU-class proving job (minutes to tens of minutes),
dominated by the interpreter overhead — paying to prove "a RISC-V CPU correctly
ran a verifier" instead of proving "the verifier accepts."

## 2. The modern wrap: a native FRI-verifier circuit over BN254

Replace the zkVM with a **native arithmetic circuit whose constraints *are* the
verifier** — one BabyBear mul ≈ one circuit mul (plus a small reduction), not ~30
RISC-V rows. The circuit verifies the dregg batch-STARK FRI proof directly and
emits a Groth16/BN254 proof the existing Solidity verifier checks.

```
WholeChainProof root (BabyBear batch-STARK, ir2 knobs: blowup 6 / 19 queries)
   │  NATIVE circuit C(witness = root proof) ⇔ verify_turn_chain_recursive_from_parts
   │     · tooth 1: recompute recursion_vk_fingerprint, == trusted anchor
   │     · tooth 2: verify_all_tables (FRI low-degree test + Merkle paths +
   │                per-table quotient + logup bus + NPO Poseidon2/expose_claim)
   │     · tooth 3: exposed segment == [genesis, final, num_turns, chain_digest]
   ▼
Groth16/BN254 proof (≈256 B, 8 field elements)   ← public inputs = the 4 dregg roots
   │  to_calldata()  (bridge/src/ethereum.rs:159 — REUSED)
   ▼
IDreggSettlement.settle(a,b,c, genesisRoot, finalRoot, numTurns, chainDigest)
   one EIP-197 pairing check, ~250–300k gas      ← chain/contracts/IDreggSettlement.sol (REUSED)
```

### 2a. gnark vs Halo2

**Recommend gnark (Go, Groth16 over BN254).**

| | gnark | Halo2 (PSE/BN254) |
|---|---|---|
| EVM verifier | `gnark-solidity-verifier` emits the Solidity Groth16 verifier directly | `snark-verifier` emits a Yul verifier (KZG) |
| Final proof | Groth16: ~256 B, **~250–300k gas**, smallest | KZG/PLONK: larger, ~300–500k gas |
| Trusted setup | per-circuit Groth16 ceremony **or** gnark PLONK (universal SRS, no per-circuit ceremony, slightly more gas) | universal KZG SRS |
| Non-native field | `std/math/emulated` + hand-rolled small-modulus reduction; mature | possible, heavier ergonomics |
| Provenance | exactly what SP1/Succinct/RISC0 use for their *own* final wrap — battle-tested for "STARK-verifier-in-SNARK" | used by zkEVMs, heavier to drive for a FRI verifier |

gnark wins on three axes that matter here: it produces the **cheapest on-chain
proof** (Groth16, 256 B, ~250–300k gas — the envelope `bridge/src/ethereum.rs`
already encodes), it has the **directest Solidity export**, and it is the
**same tool the production STARK-wrap ecosystems already use** for this exact
job, so we inherit vetted Groth16/pairing crypto rather than building bespoke.
Pick gnark **PLONK** if avoiding a per-circuit Groth16 ceremony is worth ~1.5×
gas; pick gnark **Groth16** for the cheapest settlement. Both reuse the same
verifier circuit.

### 2b. The field embedding (BabyBear → BN254, lossless and cheap)

BabyBear is 31-bit; the BN254 scalar field is ~254-bit. Each BabyBear element is
**one BN254 witness variable** — the embedding is lossless (31 ≪ 254) and the four
public inputs drop straight into the Groth16 public-input vector.

The only in-circuit cost is keeping BabyBear values *canonical*: after a BN254
mul of two <2³¹ operands the product is <2⁶², well inside BN254, and reduction is
`x mod (2³¹ − 2⁷ + 1)` — a small, cheap gadget (a few range-checks + a
conditional subtract), **far cheaper than generic non-native field emulation**
because the modulus is tiny relative to the host field (no limb decomposition of
the host field is needed; this is the favorable "small modulus inside a big
field" regime, unlike Goldilocks-in-BN254 or BN254-in-BN254). Degree-4 extension
arithmetic is the standard 4-limb BabyBear schoolbook. Poseidon2-w16/w24 over
BabyBear becomes a fixed sequence of these BabyBear muls/adds with the fork's
round constants and MDS re-expressed as BN254 constants.

### 2c. Prover-time win

The native circuit's proving cost is ∝ its **constraint count ≈ the number of
BabyBear ops in the verifier** (order millions), *not* the number of RISC-V
cycles SP1 pays (order tens-to-hundreds of millions). Removing the interpreter
layer removes the ~1–2 orders-of-magnitude blowup, plus there is no RISC-V→Groth16
recursion stack — the circuit *is* the Groth16 statement. Expect wrap proving to
drop from **minutes-to-tens-of-minutes (GPU-class, SP1)** to **seconds-to-low-minutes
(CPU or a modest GPU)** for the single-root verifier at 19 queries. (Ballpark, to
be confirmed by the §4 spike; the constant factor depends on Poseidon2 round
count and the table set verify_all_tables walks.)

### 2d. What is reused as-is

Everything *around* the SNARK is already built and untouched by this change:

- `bridge/src/ethereum.rs` — `EthSettlementProof`, `wrap_for_ethereum`
  (`:287`), the 256-byte Groth16 `(A,B,C)` slicer (`Groth16Calldata`, `:217`),
  the four-public-input EVM-word encoding (`EthPublicInputs`, `:260`,
  `to_calldata`/`from_tail`), the `EthBridgeState` continuity+monotone-height
  settlement state machine (`:373`), and the `IDreggSettlement` ABI string
  (`solidity_verifier_interface`, `:473`).
- `chain/contracts/IDreggSettlement.sol` — the deployed `settle(a,b,c, …)`
  interface and `Settled` event.

The replacement is localized: a real gnark prover feeds 256-byte Groth16 bytes
into `wrap_for_ethereum(SnarkSystem::Groth16Bn254, Some(bytes), …)`; the calldata,
binding, state machine, and contract are unchanged.

## 3. The plan

**Keep** the Solidity settlement ABI + the whole `bridge/src/ethereum.rs` seam.
**Replace** the SP1 guest (`chain/program/`) with a native gnark wrap circuit that
verifies the *current* fork proof at `ir2_leaf_wrap_config`. **Retire** the
`GuestStarkProof` legacy format and the `chain/src/{prove,verify}.rs` SP1 driver
once the gnark path settles a real root.

Milestones:

1. **Witness export (Rust → gnark JSON).** A `circuit-prove` exporter that
   serializes a `BatchStarkProof<DreggRecursionConfig>` root + the trusted
   `RecursionVk` + the four publics into the flat field-element witness the gnark
   circuit consumes. (Pure serialization; the proof already exists.)
2. **gnark circuit, tooth by tooth.** `chain/gnark/` (new Go module, disjoint):
   - `fri_verifier.go` — the BabyBear/extension/Poseidon2 gadgets + the three
     teeth as a `frontend.Circuit`. Skeleton shipped alongside this doc.
   - Validate the **Fiat-Shamir transcript** byte-for-byte against the Rust
     challenger first (a single Poseidon2 sponge fixture) — a transcript mismatch
     is a silent soundness break.
3. **Spike: accept genuine / reject tampered.** Prove the circuit over a real
   `WholeChainProofBytes` fixture from `lightclient`'s test history; confirm it
   *accepts* a genuine root and *rejects* a tampered one (flip a query value, a
   Merkle sibling, the exposed segment). This is the load-bearing unknown (§5).
4. **Groth16 export + Solidity.** `gnark-solidity-verifier` → a concrete
   `DreggSettlementVerifier.sol` implementing `IDreggSettlement`; confirm its VK
   hash matches `EthSettlementProof::verifying_key_hash`.
5. **End-to-end on a testnet.** gnark Groth16 bytes → `wrap_for_ethereum` →
   `submit_eth_settlement` → deployed verifier on an EVM testnet → one real
   `Settled(oldRoot, newRoot, height)` event.

### Honest size estimate

The wrap-around (milestones 1, 4, 5) is days — serialization + a tool-generated
Solidity verifier + an integration over the existing bridge seam. The **circuit
itself (milestone 2–3) is the bulk: a multi-week reimplementation** of the fork
batch-STARK verifier as BN254 constraints — BabyBear/ext/Poseidon2 gadgets, the
FRI low-degree test, per-table quotient + logup, the four NPO tables
(Poseidon2-w16, Poseidon2-w24, recompose, expose_claim), and a bit-exact
Fiat-Shamir transcript. Call it **~4–8 weeks** for a correct, tested
single-root verifier, dominated by the FRI/transcript fidelity work — not a new
proof system, but a large, soundness-critical circuit.

## 4. The load-bearing unknown

> **Update — this unknown is now partly discharged in Lean, not just diff-tested.**
> The companion `docs/deos/FRI-VERIFIER-PROOF-ENGINEERING.md` has since landed a
> SPECIFIED Lean verifier `verifyAlgo` (`metatheory/Dregg2/Circuit/FriVerifier.lean`,
> `def verifyAlgo`) whose soundness-relevant teeth are proven, plus the bridge
> `starkSound_of_verifyAlgo` (`FriVerifierBridge.lean`) that makes `StarkSound` a
> theorem resting on two named residuals. The transcript/table-fidelity trust below
> is now captured as the `GnarkRefines` / `TranscriptRefines` code-refines-spec
> obligation (`FriVerifier.lean:849 def GnarkRefines`): the gnark circuit's job is
> to *refine* the proven `verifyAlgo`, so "bit-exact with the Rust verifier" becomes
> a refinement statement rather than a purely empirical differential-testing hope.
> The residual below is still real (the refinement obligation must be discharged),
> but it is no longer an unstructured unknown.

**Writing a correct BabyBear batch-STARK FRI verifier in gnark.** Everything else
is integration over vetted tooling (gnark's Groth16/pairing, the existing Rust
bridge, a tool-generated Solidity verifier). The circuit is the risk because it is
**security-critical and must be bit-exact** with the Rust fork verifier:

- **Transcript / Fiat-Shamir fidelity.** The in-circuit challenger must squeeze
  the *identical* challenges (FRI betas, query indices, the constraint-combination
  α) as `DuplexChallenger<Poseidon2-w16>`. Any divergence in absorb order,
  domain separation, or squeeze layout makes the circuit accept proofs the Rust
  verifier rejects (a soundness hole) or vice-versa. Validate with fixtures first.
- **verify_all_tables surface area.** It is not one STARK — it is a *batch* with
  per-table degree_bits, a logup interaction bus across tables, and four
  non-primitive op tables (`plonky3_recursion_impl.rs:739–748`). The circuit must
  reproduce the full table set, not a single-AIR FRI check.
- **VK fingerprint inside the circuit (tooth 1).** `recursion_vk_fingerprint`
  hashes the *proof's structural fields* with blake3 (`:646`). Either reproduce
  blake3 in-circuit (costly) or — better — bind the VK as a circuit *constant*
  baked at setup so the per-instance check is "this proof's shape == the shape
  this circuit was built for," moving the blake3 out of band. A design decision
  to settle in milestone 2.
- **No oracle to diff against on-chain.** The only ground truth is the Rust
  verifier; the circuit must be differentially tested against it
  (`verify_turn_chain_recursive_from_parts`) over genuine and adversarial
  fixtures until they agree on every accept/reject.

If the transcript and table surface are reproduced faithfully, the rest (BabyBear
reduction, Merkle paths, the segment tooth as a public-input equality) is
mechanical.

## 5. Midnight (unchanged)

Native proof-carrying onto Midnight remains **foreclosed by Midnight's
architecture** (no general in-circuit proof-verification primitive; fixed-VK
per-entry-point Halo2/KZG-BLS12-381). Ship the optimistic + watchtower bridge that
already exists (`bridge/src/midnight_verified.rs`). See
`docs/deos/NATIVE-PROOF-BRIDGES.md §2`. This doc changes only the *Ethereum* wrap
prover.
</content>
</invoke>
