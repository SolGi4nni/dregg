# Bulletproofs / Ristretto MSM dispatch inventory

**Status:** source audit and measurement grounding, 2026-07-21.  No GPU MSM
backend is claimed here.  No new benchmark was run for this inventory.

This inventory answers a narrower question than “can Bulletproofs use the
GPU?”  It names every direct Bulletproofs use in the tree, derives the actual
Ristretto multiscalar-multiplication (MSM) sizes from the pinned implementations,
and separates shapes that are plausible GPU work from shapes where dispatch
overhead is likely to lose.

The short answer is:

* the ordinary transaction range proof is a **147-point verifier MSM**.  It is
  not a good one-dispatch-at-a-time GPU target;
* the verified threshold-decrypt relation is enormous: its three verifier MSMs
  are **1,056,812**, **532,522**, and **4,227,120** points per custody share;
* the private-book yoloproofs R1CS verifier is a **1,048,627-point MSM**, and its
  prover begins with MSMs as large as **870,319 points** before its 19-round
  inner-product argument;
* production distributed-input commitments are not range proofs, but they are
  repeated **12,436-point MSMs** and can use the same generic Ristretto engine;
* both Bulletproofs packages and all direct callers resolve to the same
  `curve25519-dalek 4.1.3`, so one Ristretto MSM implementation can serve them.
  The current upstream APIs call Dalek's static MSM methods directly, however,
  so sharing requires a provider seam or patched dependencies; it cannot be
  enabled by changing a call site alone.

## 1. Pinned dependency identities

There are two Bulletproofs package identities in `Cargo.lock`:

| Rust dependency | Package | Source | Direct users |
|---|---|---|---|
| `bulletproofs` | `bulletproofs 5.0.0` | crates.io | `cell-crypto`, `fhegg-fhe` range proofs and vector commitments |
| `bulletproofs_r1cs` | `bulletproofs 5.0.1` | zkcrypto git rev `04bce4e...` with `yoloproofs` | optional `fhegg-fhe` private-book R1CS |

Both depend on the one locked `curve25519-dalek 4.1.3` package.  The point and
scalar arithmetic below is therefore one curve/backend problem, not two.
Bulletproof generator namespaces and transcripts remain protocol-specific;
“one backend” means reusable MSM arithmetic, not mixing proof equations or
generator domains.

## 2. Direct cryptographic call sites

### 2.1 Stable v5 single-value range proofs

`cell-crypto/src/value_commitment.rs` is the sole stable-v5 implementation of
the ordinary value range proof:

* `RangeProof::prove_single(..., 64)` in `BulletproofRangeProof::prove_range`;
* `RangeProof::verify_single(..., 64)` in `verify_range`;
* `prove_conservation_with_range` creates one independent proof per output;
* `verify_conservation_with_range` verifies those independent proofs in a loop;
* the trait method named `batch_verify` also loops over `verify_range`.  It is
  not an aggregated Bulletproof verification.

The wrapper constructs `BulletproofGens::new(64, 1)` on every proof and every
verification.  Its own comment calls construction expensive.  Caching this
generator set is an independent CPU optimization and should be measured before
attributing all ordinary-proof time to MSM.

Runtime surfaces that reach this implementation are:

| Surface | Production behavior |
|---|---|
| `sdk/src/committed_turn.rs` | creates a proof in each `NoteCreate`, then creates another independent proof for each output in `FullConservationProof` |
| `intent/src/fulfillment.rs` | same per-output duplication as the SDK builder |
| `turn/src/executor/apply.rs` | verifies the `NoteCreate` proof during effect application |
| `turn/src/executor/finalize.rs` | recursively verifies every `NoteCreate` proof again at finalize |
| `turn/src/executor/membership_verifier.rs` | `PedersenBulletproofVerifier` delegates to `verify_range_bytes` |
| `wasm/src/privacy.rs` | byte APIs for single proof and full-conservation proof production/verification |
| `preflight/src/checks/privacy.rs` | one single-proof prove/verify health check |

`circuit-prove/tests/shielded_transfer_m2a.rs`,
`circuit-prove/tests/shielded_pool_m2b.rs`, Turn tests, and the `cell-crypto`
unit suite are test consumers of the same implementation, not additional proof
systems.

The SDK/intent builders' duplicate per-output production and Turn apply/finalize
duplicate verification are visible optimization candidates.  They must be
resolved at the protocol/container level; an MSM kernel alone does not remove
the redundant proof objects or verification passes.

### 2.2 Stable v5 aggregated threshold-decrypt ranges

`fhegg-fhe/src/threshold/quorum.rs` directly creates and verifies three
aggregated `RangeProof`s in every proof-carrying custody share:

1. 64-bit low limbs of `(smudge+B, B-smudge)`;
2. 32-bit high limbs of those same values;
3. 64-bit shifted signed quotients for the two exact BFV equations.

`decrypt_range_gens()` is cached and provisioned as
`BulletproofGens::new(64, 32_768)`.  For the current fold set
`N=4096, L=3`:

| Argument | Values `m` | Bits `n` | IPP dimension `d=n*m` |
|---|---:|---:|---:|
| smudge low | `2N = 8,192` | 64 | 524,288 = 2^19 |
| smudge high | `2N = 8,192` | 32 | 262,144 = 2^18 |
| quotients | `2LN = 24,576`, padded to 32,768 | 64 | 2,097,152 = 2^21 |

The source comment above `decrypt_range_gens()` still describes the former
two-modulus shape and says the quotient vector has 16,384 values.  HEAD's
`FOLD_MODULI` has three moduli, and the executable sizing code pads 24,576 to
32,768.  The table above follows code, not that stale comment.

Proof generation is entered only for parties assembled from verified VSS/DKG
material (`vss_setup_digest.is_some()`).  Legacy/semi-honest quorum tests use
the unproved path.  The real proof-carrying consumer is
`dreggnet-market/tests/descent_fhegg_settlement.rs`: it opens two curves with a
3-of-4 live roster, hence produces and verifies six custody-share relations,
or 18 aggregated range proofs in each direction.  Nextest classifies its test
`authenticated_encrypted_orders_gate_real_game_asset_settlement` as heavy and
records it as greater than 1,080 seconds in release.  That annotation is a
classification, not a fresh green result from this audit.

### 2.3 Experimental yoloproofs R1CS

`fhegg-fhe/src/private_book_bfv_zk.rs` is the only R1CS caller:

* `bulletproofs_r1cs::r1cs::Prover::prove(&BP_GENS)`;
* `Verifier::verify(..., &BP_GENS)`;
* one static `BulletproofGens::new(1 << 19, 1)`.

The fixed relation has exactly **444,567 multipliers**, derived from the source
gadgets:

| Relation part | Multipliers |
|---|---:|
| four 128-way one-hot order choices | 512 |
| Poseidon2 root relation | 115,159 |
| 12 short degree-4096 vectors plus six-bit ranges | 319,488 |
| 384 compressed BFV equations plus 24-bit quotient ranges | 9,408 |
| **total** | **444,567** |

The first randomized-phase commitment occurs after 435,159 phase-one
multipliers; phase two adds 9,408.  Bulletproofs pads the final vector to
524,288 = 2^19, matching `BP_GENS_CAPACITY`.

The APIs are consumed by:

* `fhegg-fhe/tests/private_book_bfv_zk.rs` (one proof and hostile public-input
  substitutions);
* `dreggnet-market/src/private_bfv_attested_clearing.rs`, whose
  `assemble_evidence` and public verifier both verify the R1CS proof;
* `dreggnet-market/tests/private_bfv_attested_clearing.rs` and
  `private_clearing_apex_e2e.rs`, which create the proof.

These binaries are deliberately in nextest's heavy profile.  Durable recorded
results include 65.765 s for the focused `private_book_bfv_zk` hostile test and
62.958 s for `private_bfv_attested_clearing` in `HORIZONLOG.md`.

A newer current-source hbox run is captured in
`/tmp/private-clearing-apex-cpu-timed.log` (2026-07-21).  Its relevant release
timings were:

| Operation | Time |
|---|---:|
| entire R1CS proof API | 63.153 s |
| `Prover::prove`, including phase-two synthesis | 62.821 s |
| phase-two relation synthesis inside that call | 1.983 s |
| one R1CS verify API | 7.07–7.76 s |
| `Verifier::verify`, including phase-two rebuild | 6.79–7.47 s |
| phase-two relation rebuild inside verification | 1.95–2.04 s |

The full apex was green in 124.158 s in that artifact.  This attribution does
not prove every non-relation millisecond is MSM, but it establishes a large
Bulletproof backend budget after the roughly two-second relation construction.

### 2.4 Bulletproof generators used only as vector-commitment bases

Two stable-v5 call sites use `BulletproofGens` without constructing a range or
R1CS proof:

* `fhegg-fhe/src/private_book_distributed_inputs.rs` computes direct
  `RistrettoPoint::multiscalar_mul` vector commitments.  Production width is
  `2 + 128 + 9 + 3*4096 + 8 = 12,435`, so each commitment is a
  **12,436-point MSM** after
  the blinding base is appended.  For `W` workers, one four-owner dealing and
  recipient opening pass performs `4(2W+1)` such MSMs (28 at `W=3`).
* `fhegg-fhe/src/private_book_canonical_backend.rs` recomputes four commitments
  per worker, again 12,436 points in production.  Its current tests use degree
  8 (35-point MSMs), and no production full-degree gate is captured.

These are excellent users of a generic Ristretto MSM provider, but they must
not be counted as Bulletproof range/R1CS proof acceleration.

## 3. Exact MSM shapes

The formulas below come from the pinned Bulletproofs source, not a generic
Bulletproofs paper estimate.

### 3.1 Stable range verifier

For `m` values of `n` bits, let `d=n*m` and `k=log2(d)`.  Stable v5 performs
one optional variable-time verifier MSM with:

```text
2d + m + 6 + 2k points
```

The terms are `G/H` vectors, value commitments, `A/S/T1/T2`, the two Pedersen
bases, and `L/R` inner-product points.

| Call shape | Verifier MSM points |
|---|---:|
| ordinary one-value 64-bit proof | 147 |
| threshold smudge low | 1,056,812 |
| threshold smudge high | 532,522 |
| threshold quotient | 4,227,120 |

### 3.2 Stable range prover

For every value, proof creation performs an `S` MSM of `2n+1` points (129 for
64 bits, 65 for 32 bits), plus small two-point Pedersen commitments.  The
inner-product proof then has `k` sequential rounds.  Each round has two MSMs
of sizes:

```text
d+1, d/2+1, d/4+1, ..., 3
```

and folds the generator arrays with many independent two-point MSMs.  A useful
GPU design must therefore support both batched small MSMs and a device-resident
sequential inner-product reduction; accelerating only the final verifier mega
MSM does not accelerate proving.

### 3.3 Yoloproofs R1CS prover and verifier

For the exact private-book relation, the prover commitments are:

| Commitment | Points |
|---|---:|
| `A_I1` | 870,319 |
| `A_O1` | 435,160 |
| `S1` | 870,319 |
| `A_I2` | 18,817 |
| `A_O2` | 9,409 |
| `S2` | 18,817 |

It then commits five polynomial coefficients with two-point Pedersen MSMs and
runs a 19-round inner-product argument over 524,288 entries.  Its two round
MSMs have sizes 524,289, 262,145, ..., 3, with generator-fold MSMs between
rounds.

There are no high-level externally committed `V` variables in this relation.
The verifier's one mega MSM is therefore:

```text
2*524,288 + 2*19 + 13 = 1,048,627 points
```

The 13 fixed terms are six phase commitments, five `T` points, and two
Pedersen bases.

## 4. Honest dispatch recommendation

One shared **Ristretto MSM provider** can serve all four workloads above.  A
shared **WGSL kernel** cannot serve BFV/TFHE polynomial arithmetic and
Ristretto group arithmetic; only adapter/queue selection, buffer pooling,
telemetry, hard-require policy, and test infrastructure are naturally shared
with the existing wgpu work.

Recommended dispatch classes:

| Shape | Initial policy before benchmarks | Reason |
|---|---|---|
| 147-point ordinary verifier; 129-point ordinary prover MSM | CPU | GPU launch/upload likely dominates; cache `BulletproofGens(64,1)` first |
| many independent ordinary proofs | CPU by default; benchmark a batched independent-proof queue | they are not one `verify_multiple` statement because they were produced independently |
| 12,436-point distributed commitments | benchmark CPU vs batched GPU | medium, repeated, fixed generators; plausible crossover target |
| 0.5M–4.2M-point threshold verifier MSMs | GPU-preferred with hard CPU parity | unmistakably large and fixed-shape |
| private-book R1CS prover/verifier | GPU-preferred with hard CPU parity | measured 62.8 s prove-call and 6.8–7.5 s verify-call budgets |

Do not set a universal point-count threshold from these source sizes alone.
Benchmark at least 147, 12,436, 262,144, 435,160, 524,288, 870,319,
1,048,627, and 4,227,120 points, with cold upload, warm resident generators,
and batches of repeated small MSMs reported separately.

## 5. Integration seam and correctness gates

The current crates call `RistrettoPoint::multiscalar_mul`,
`vartime_multiscalar_mul`, and `optional_multiscalar_mul` directly inside
dependency source.  A practical backend therefore needs one of:

1. a local patch of both Bulletproofs package identities that routes MSM calls
   through a provider trait; or
2. a Dalek-level provider seam used by both dependencies and the direct vector
   commitment callers.

The first is narrower and makes constant-time versus variable-time intent
explicit.  Proof verification uses variable-time MSM over public scalars and
points.  The initial prover commitments contain secret scalars and call
Dalek's constant-time `MultiscalarMul`; they must not be silently routed through
the verifier implementation.  The pinned inner-product prover itself later
uses `VartimeMultiscalarMul` with witness-derived scalars, so its inherited
side-channel posture also needs an explicit audit rather than an accidental
claim that the whole upstream prover is constant-time.

Minimum validation before enabling dispatch:

* deterministic point-level parity against Dalek for every benchmark size,
  including identity points, zero/one/maximum canonical scalars, duplicate
  points, cancellation, and randomized full-width scalars;
* unchanged proof-byte fixtures where prover randomness is deterministic, plus
  cross-backend matrices: CPU-prove/GPU-verify and GPU-prove/CPU-verify;
* hard GPU-required tests on hbox that fail closed if Vulkan/adapter dispatch is
  not actually used, alongside ordinary auto-fallback tests;
* transcript and generator derivation remain byte-identical on CPU; cache and
  upload the resulting fixed generator tables rather than inventing GPU-side
  generator derivation;
* report kernel, upload/download, point decode, generator-cache warmup, and
  total proof time separately.  A fast kernel with slower end-to-end proof time
  is not a win.

The highest-value first implementation is the public-variable verifier mega
MSM: it avoids secret-dependent timing concerns and has exact CPU verification
as an oracle.  The R1CS prover and stable range prover require the additional
constant-time and sequential-IPP design work described above.
