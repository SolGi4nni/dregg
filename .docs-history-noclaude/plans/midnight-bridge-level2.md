# Level 2 Bridge: Proof-Carrying `dregg`-to-Midnight

## Status: Design / Prototype

## Problem Statement

Level 1 bridge (current): Federation members sign attestations ("this state
transition happened on dregg"). Midnight trusts N-of-M signatures. Safety
depends entirely on federation honesty.

Level 2 goal: `dregg` submits a cryptographic PROOF of the state transition.
Midnight VERIFIES the proof in-circuit. Safety depends only on the math.

## Proof System Mismatch

| Property | `dregg` | Midnight |
|----------|-------|----------|
| Field | BabyBear (p = 2^31 - 2^27 + 1) | BLS12-381 scalar (Fq, 255-bit) |
| Proof system | STARK (FRI-based) | PLONK + KZG |
| Hash function | Poseidon2 (width 16, BabyBear) | Poseidon (width 3, rate 2, BLS12-381 Fq) |
| Commitment | FRI (Poseidon2 Merkle) | KZG (polynomial commitment) |
| Proof size | ~24-48 KB | ~1-2 KB |

These are fundamentally incompatible. There is no direct path where Midnight's
native verifier accepts a dregg STARK proof.

## Path Analysis

### Path A: FRI Verifier in ZkStdLib Circuit (FEASIBLE but EXPENSIVE)

**Idea:** Write a Midnight `Relation` (ZkStdLib circuit) that implements the
entire FRI verification protocol. Deploy it as a Midnight contract. `dregg`
submits STARK proofs; the contract verifies them.

**What FRI verification requires:**
1. Merkle path verification (depth ~20, using Poseidon2 hashes)
2. Polynomial evaluation checks at queried points
3. Folding consistency checks between FRI layers

**Critical blocker: Hash mismatch.**
- `dregg`'s FRI Merkle trees use Poseidon2 over BabyBear
- Midnight's available hash is Poseidon over BLS12-381 Fq (width=3, rate=2)
- To verify dregg's Merkle paths in Midnight, we'd need Poseidon2-over-BabyBear
  computed inside BLS12-381 arithmetic
- BabyBear arithmetic in BLS12-381: trivial (BabyBear fits in a single Fq element)
- Poseidon2-over-BabyBear in Plonk: doable but the round constants and MDS matrix
  are different from Midnight's native Poseidon

**Gate count estimate:**
- Poseidon2 hash (width 16, BabyBear): ~200 gates per invocation in native field
  BUT in non-native (BabyBear simulated in Fq): ~50 gates (BabyBear is SMALL, so
  no limb decomposition needed; mod reduction is a single constrain_bits(31))
- One Merkle path (depth 20): 20 hashes = ~1000 native-equivalent gates
- One FRI query: 1 Merkle path + evaluation check = ~1200 gates
- 50 FRI queries: ~60,000 gates
- FRI folding (log_2(trace_len) layers): another ~30,000 gates
- Total: ~100K-200K gates

**Midnight capacity:** SRS supports k up to at least 19 (2^19 = 524K rows).
The ZkStdLib `optimal_k` searches up to k=25. A 200K-gate FRI verifier fits
comfortably.

**Engineering cost:** 6-10 weeks. Requires:
- Implement Poseidon2-over-BabyBear as a custom chip or via native arithmetic
- Implement FRI query verification logic in ZkStdLib
- Implement polynomial evaluation check
- Serialize/deserialize dregg STARK proofs into Midnight witness format
- Deploy as a Midnight contract via ZKIR or direct Relation

**Verdict: Feasible but high effort. Highest security guarantee.**

### Path B: SP1 -> Groth16 -> BN254 Verifier on Midnight (MOST PROMISING)

**Idea:** Use SP1 to wrap our BabyBear STARK into a Groth16 proof over BN254.
Then verify that Groth16 proof on Midnight.

**Evidence in our codebase:** `circuit/src/backends/sp1.rs` already supports
Groth16-wrapped mode (the `Sp1ProofMode::Groth16` variant). SP1 compresses
STARK -> STARK -> Groth16/BN254.

**Midnight's BN254 support:**
- `midnight-zk/curves/src/bn256/` has full BN256 (= BN254) curve implementation
- The verifier types module (`circuits/src/verifier/types.rs`) has `BnEmulation`
  implementing `SelfEmulation` for BN256, gated behind `feature = "dev-curves"`
- This means Midnight CAN do in-circuit BN254 Plonk verification

**But wait:** Midnight's in-circuit verifier (`VerifierGadget`) verifies PLONK
proofs, not Groth16 proofs. Groth16 verification requires:
1. 3 pairings (or 1 multi-pairing with 3 pairs)
2. G1/G2 arithmetic on BN254

Midnight has BN254 G1 arithmetic (ForeignWeierstrassEccChip) but NOT pairing
gadgets for BN254. The native pairing is BLS12-381.

**Revised approach: SP1 -> PLONK/BN254 -> Midnight VerifierGadget<BnEmulation>**

SP1 also supports "PLONK-wrapped" mode (not just Groth16). If we can get SP1 to
produce a BN254 PLONK proof, Midnight's `VerifierGadget<BnEmulation>` can verify
it directly in-circuit. This is the `dev-curves` path.

**Alternatively: SP1 -> Groth16/BN254 -> custom Groth16 verifier**

A Groth16 verifier is much simpler than PLONK:
- 1 pairing equation: e(A, B) == e(alpha, beta) * e(sum_IC, gamma) * e(C, delta)
- Requires BN254 pairing in-circuit on BLS12-381
- BN254 pairing in BLS12-381 Plonk: ~millions of gates (tower field arithmetic)
- NOT practical without a precompile

**Status of BN254 on Midnight (production):**
- `dev-curves` feature exists but is gated
- No production BN254 pairing precompile found
- The `BnEmulation` is for circuits operating OVER Bn254 scalar field (not for
  verifying BN254-based proofs inside BLS12-381 circuits)

**Corrected understanding:** `BnEmulation` lets you build a verifier circuit
whose NATIVE field is BN254. It does NOT give you BN254 pairing verification
inside a BLS12-381 circuit.

**True Path B verdict:**
- We'd need Midnight to add a Groth16/BN254 precompile, OR
- We'd need SP1 to produce a BLS12-381 PLONK proof (which it doesn't; SP1 only
  wraps to BN254)
- **Not currently feasible without Midnight protocol changes.**

### Path C: Shared Commitment Interop (PRAGMATIC, IMMEDIATE)

**Idea:** Both chains commit to the same state root. The dregg proof proves
"old_root -> new_root is valid." A relay verifies the dregg proof off-chain,
then submits new_root to Midnight with an attestation.

**Trust model:** Weaker than full verification. Safety = "at least one honest
relay verified the proof." This is still better than Level 1 (pure federation
trust) if the relay set is permissionless.

**Variant C+: Optimistic bridge with fraud proofs**
- Relay posts new_root with a bond
- Challenge period (e.g., 24h)
- Anyone can challenge by submitting the FULL dregg STARK proof to an off-chain
  arbitration committee (or by re-running verification)
- If fraud proven: relay loses bond
- This gives economic security without in-circuit verification

**Engineering cost:** 2-3 weeks
- Shared hash commitment format (Poseidon2 state root -> field element)
- Relay submission logic on Midnight
- Challenge/bond contract (if optimistic variant)

**Verdict: Immediately buildable. Weaker security but practical.**

### Path D: STARK -> Pickles -> ??? -> Midnight (NOT FEASIBLE)

Pickles uses Pasta curves (Pallas/Vesta). Midnight uses BLS12-381. There is no
efficient path from Pasta to BLS12-381 without yet another wrapping step.

**Verdict: Dead end. Too many hops, each adding overhead and complexity.**

## Recommended Strategy: Hybrid B+ / C

### Phase 1 (Now, 2-3 weeks): Path C - Shared Commitment Bridge

Deploy immediately using shared Poseidon2 state commitments. This gives:
- Functional bridge with relay-based security
- No protocol changes needed on Midnight
- Foundation for upgrade to Phase 2

### Phase 2 (When available, ~Q4 2026): Path B via BLS12-381 wrapping

**Key insight:** The missing piece is a proof compression that outputs a
BLS12-381 PLONK proof. Two emerging options:

1. **Aligned Layer / proof aggregation services** that accept STARK proofs and
   produce BLS12-381 proofs for L1s
2. **SP1 BLS12-381 backend** (on the SP1 roadmap but not yet shipped)
3. **Custom recursive STARK-to-PLONK compiler** targeting BLS12-381 KZG

When any of these become available, the flow becomes:
```
Dregg STARK (BabyBear/FRI) -> Compression Service -> BLS12-381 PLONK proof
-> Midnight VerifierGadget<BlstrsEmulation> verifies in-circuit
```

This uses Midnight's EXISTING in-circuit verifier (`VerifierGadget<BlstrsEmulation>`).
No new Midnight features needed. The contract simply calls `std_lib.verifier().prepare()`
on the incoming proof.

### Phase 3 (Longer term): Path A - Native FRI Verifier

If neither compression service nor BLS12-381 SNARK wrapping materializes, build
the full FRI verifier as a Midnight ZkStdLib Relation. This is the ultimate
trust-minimized path but requires significant engineering.

## Prototype: FRI Verifier DSL Circuit

File: `dregg-dsl-tests/src/fri_verifier_dsl.rs`

This prototype expresses the core FRI query verification logic as a
`CircuitDescriptor` targeting our DSL format. While not directly compilable to
ZKIR v3 (which lacks the hash primitives needed), it demonstrates:
1. The algorithmic structure of FRI verification
2. Column layout for Merkle path verification
3. Polynomial evaluation check constraints
4. How it maps to a Midnight `Relation` (design sketch in comments)

## Gate Count Summary

| Component | Gates (estimated) | Notes |
|-----------|-------------------|-------|
| Poseidon2-in-Fq (1 hash) | 50 | BabyBear fits in Fq natively |
| Merkle path (depth 20) | 1,000 | 20 hashes |
| 1 FRI query | 1,200 | path + eval check |
| 50 FRI queries | 60,000 | Standard security |
| FRI folding layers | 30,000 | log2(trace) layers |
| **Total FRI verifier** | **~100K-200K** | Fits in k=18 (262K rows) |
| Midnight max circuit | ~33M rows (k=25) | SRS supports up to k=25 |

## What We Need to Build (Phase 1)

1. **State commitment format**: Define how dregg's Poseidon2 state root maps to
   a Midnight-compatible field element (BLS12-381 Fq). Since BabyBear elements
   fit in Fq, the commitment can be a direct embedding.

2. **Relay contract on Midnight**: A Compact program that:
   - Accepts `(old_root: Fq, new_root: Fq, relay_signature: Signature)` as inputs
   - Verifies relay is in the authorized set (or anyone, for optimistic mode)
   - Updates the canonical state root
   - Emits a "bridge update" event

3. **Relay service**: An off-chain process that:
   - Monitors dregg for finalized state transitions
   - Verifies the STARK proof locally
   - Submits the new root to the Midnight contract
   - Posts bond (optimistic variant)

4. **Client integration**: Update `bridge/src/present.rs` to support Level 2
   attestation format alongside Level 1 signatures.

## Open Questions

1. Will Midnight's `dev-curves` BN254 feature reach production? If so, Path B
   becomes immediately viable via SP1 Groth16.
2. Is there a BLS12-381 PLONK wrapping service we can use externally?
3. What's the maximum circuit size the Midnight mainnet SRS actually supports?
   (The code searches k=9..25, but production deployment may be limited by the
   ceremony parameters.)
4. Could we contribute a Poseidon2-over-BabyBear chip to midnight-zk? This
   would make Path A significantly easier.
