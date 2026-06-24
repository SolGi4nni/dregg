# Recursive Proof Architecture

## Recursion Model: Three Levels

Ordered by how much the external verifier must do:

1. **Mina-equivalent (target for standalone.rs):** Everything verified in-circuit EXCEPT
   the `sg` MSM (`<b_poly_coefficients(challenges), G>`). External verifier does only
   `batch_dlog_accumulator_check` — one batch MSM over SRS generators. This is what
   Mina's Pickles provides. The proof is constant-size with minimal external verification.

2. **Assisted recursion (our pickles.rs):** All IPA operations deferred. External verifier
   runs full `kimchi::verifier::verify` which includes the complete IPA batch check.
   More work for verifier but simpler circuit.

3. **Pure computation (BabyBear STARK):** No recursion. External verifier does full
   FRI + Merkle + constraint checking. Bounded depth.

IPA fundamentally requires external MSM — there is no "self-verifying" or
"standalone-transitive" IPA proof. The correct claim for Level 1 is "constant-size
proof with minimal external verification (one batch MSM)."

## Available Proof Paths

### 1. BabyBear STARK (custom + Plonky3) — Level 3: Pure Computation
- Proves: Merkle membership, fold steps, derivation, predicates, IVC chains, full presentations
- Size: ~24-48 KiB
- External verifier work: Full FRI + Merkle + constraint checking
- Composition: Hash-chain IVC (not recursive). MAX_FOLD_DEPTH=16
- Latency: ~64-200us prove, ~1ms verify
- PQ-secure: Yes

### 2. Kimchi Single Proof (mina backend)
- Proves: Merkle membership, fold steps
- Size: ~5-10 KiB
- External verifier work: Full Kimchi verification (IPA batch check)
- Composition: None (single statement per proof)
- Latency: ~1-2s prove

### 3. Pickles Assisted Recursion (mina/pickles.rs) — Level 2: Assisted Recursion
- Proves: Unbounded state transition chains via IPA accumulator forwarding
- Size: ~5-10 KiB (constant regardless of chain length)
- External verifier work: Full `kimchi::verifier::verify` including complete IPA batch check
- Composition: Each step carries forward previous IPA accumulator via create_recursive. Unbounded depth.
- Status: OPERATIONAL (prove_recursive_step, verify_recursive_proof both work with full Kimchi verification)

### 4. Dual-Curve Step/Wrap (mina/step_verifier.rs + wrap_verifier.rs)
- Proves: State transitions with deferred EC verification
- Step (Vesta): Poseidon transcript + b(zeta) computation. No EC gates. ~200 gates.
- Wrap (Pallas): EndoMul + CompleteAdd for IPA bullet_reduce. ~4700 gates.
- Size: ~5-15 KiB per wrap proof
- External verifier work: Batch MSM for accumulated sg commitments (same as Mina)
- Composition: Step -> Wrap -> Step -> Wrap alternation. prove_full_recursive_chain produces final wrap.
- Status: OPERATIONAL (prove_full_recursive_chain, verify_full_recursive_proof)

### 5. Mina-Equivalent In-Circuit IPA Verification (mina/standalone.rs) — Level 1 Target
- Proves: In-circuit Fiat-Shamir replay, bullet_reduce, b(zeta) computation, final equation assertion
- Defers to external verifier: sg accumulator MSM only (batch_dlog_accumulator_check)
- Size: ~15-20 KiB (larger circuit than assisted wrap)
- External verifier work: One batch MSM over SRS generators (minimal)
- Composition: prove_standalone_recursive_chain composes arbitrary-length chains
- Status: IN PROGRESS (circuit structure exists but EndoMul outputs not yet wired to assertions, GLV encoding incomplete)
- Required for soundness: GLV signed-digit encoding (Scalar_challenge.to_field_checked), copy constraints wiring EndoMul outputs to assertion gates

### 6. STARK-in-Pickles (backends/stark_in_pickles.rs)
- Proves: A BabyBear STARK proof is valid, compressed into ~1-2 KiB Pickles proof
- Size: ~1-2 KiB output (from 24-48 KiB STARK input)
- External verifier work: Kimchi verification (assisted recursion level)
- Composition: compose_pickles_proofs merges two wrapped STARKs into one proof
- Status: SCAFFOLD. The wrapping uses prove_recursive_step (binding only). Full in-circuit STARK verification requires BabyBear Poseidon2 emulated as Kimchi gates (~272K gates, ~5s proving). The circuit skeleton exists (build_stark_verifier_circuit) but gate-level constraint code is not wired.

### 7. Kimchi Native Backend (backends/kimchi_native/)
- Proves: Derivation, fold, predicates, IVC, presentation natively in Kimchi
- Size: ~5-10 KiB per proof
- External verifier work: Kimchi verification (assisted recursion level)
- Composition: KimchiNativeBackend::prove_ivc supports up to 256 steps
- Status: STRUCTURAL. Circuits generate real Kimchi proofs that pass the verifier, but gate coefficients need hardening for adversarial soundness.

## STARK-in-Kimchi: Current State

The path exists as `stark_in_pickles.rs`. What is implemented:

1. Gate count estimation (feasibility proven: ~272K gates for full 80-query verification, ~50K for reduced 16-query mode)
2. BabyBear emulation gadgets (mul with mod reduction, add with mod reduction, range checks)
3. Poseidon2 emulation circuit skeleton (240 gates per hash)
4. Full verifier circuit layout (Fiat-Shamir + Merkle + constraint eval + FRI folding)
5. wrap_stark_in_pickles API (currently uses binding-only Pickles proof, not the full verifier circuit)
6. compose_pickles_proofs for recursive composition of wrapped STARKs

What remains: wiring the BabyBear Poseidon2 constraint code into real Kimchi gates with correct coefficients (~2000 lines of gate-level code).

## Do We Need Native Kimchi Predicates?

The kimchi_native backend reimplements derivation/fold/predicates/IVC/presentation as Kimchi circuits. Two production strategies:

**Strategy A: All-Kimchi.** Use kimchi_native for everything. Proof size is small (~5 KiB). Proving is slow (~1-2s per sub-proof). Recursion via Pickles gives unbounded chains. Requires hardening all gate coefficients (currently audit-flagged as vacuous).

**Strategy B: STARK-then-wrap.** Prove heavy computation with BabyBear STARK (~200us), wrap the STARK inside Pickles (~5s once). Best of both: fast proving for the computation, small proofs for transmission, recursive composition for unbounded chains. Requires completing the BabyBear Poseidon2 emulation.

**Recommendation:** Strategy B is cleaner. The STARK backend already has real constraints, real soundness, boundary constraint enforcement, and is battle-tested. Reimplementing everything in Kimchi doubles the audit surface. The STARK-in-Pickles wrapper is the correct compression layer.

## MAX_FOLD_DEPTH and Recursion

MAX_FOLD_DEPTH=16 exists because the BabyBear IVC is a hash-chain (not recursive). The circuit literally unrolls all N steps into one trace. With Pickles recursion (now operational):

- prove_recursive_step has NO depth limit (each step proves one transition + verifies one previous proof)
- prove_full_recursive_chain handles arbitrary-length transition sequences
- The Kimchi native IVC backend advertises max_chain_depth() = 256

For the STARK path, removing MAX_FOLD_DEPTH requires either: (a) switching to STARK-in-Pickles wrapping (compress each segment, compose recursively), or (b) segmented proving (prove 16-step segments, chain their commitments). Option (a) is architecturally cleaner.

## Clean Architecture

**Fast path** (latency-sensitive): BabyBear STARK. ~200us prove, ~48 KiB proof. Used for: agent-to-agent presentations where bandwidth is cheap and latency matters. MAX_FOLD_DEPTH=16 is acceptable for most real delegation chains.

**Small path** (bandwidth-sensitive): STARK-in-Pickles. Prove with STARK (~200us), wrap with Pickles (~5s). Final proof ~1-2 KiB. Used for: mobile clients, cross-federation bridges, stored credentials.

**Recursive path** (unbounded chains): Pickles assisted recursion. Each fold step is one prove_recursive_step call (~3s). Chain is unbounded. Final proof ~5 KiB. Used for: deeply-attenuated tokens, epoch compression, long-lived delegation chains.

**On-chain path** (Mina L1): Mina-equivalent dual-curve wrap. Prove chain via Pickles, final wrap on Pallas with in-circuit IPA verification (all ops except sg MSM). Result is a constant-size proof where the external verifier performs only `batch_dlog_accumulator_check` (one batch MSM over SRS generators) — the same verification model as Mina smart contracts. Used for: on-chain capability verification, bridge anchoring.

**Composition across paths**: STARK-in-Pickles is the universal adapter. Any STARK proof (membership, fold, derivation, presentation) can be compressed into Pickles form, then recursively composed with other Pickles proofs or verified on Mina L1.
