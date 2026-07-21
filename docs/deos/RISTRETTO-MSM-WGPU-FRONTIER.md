# Ristretto MSM on wgpu: the Bulletproofs backend boundary

**Status (2026-07-21): owned dispatch seam implemented; exact GPU scalar-window
stage implemented; group accumulation remains dalek/CPU. No GPU-MSM speedup is
claimed yet.**

The private-book R1CS prover spends most of its measured minute inside
`Prover::prove`. Its pinned Bulletproofs fork formerly called dalek directly at
six large commitment sites:

| Commitment | Points |
|---|---:|
| `A_I1` | 870,319 |
| `A_O1` | 435,160 |
| `S1` | 870,319 |
| `A_I2` | 18,817 |
| `A_O2` | 9,409 |
| `S2` | 18,817 |

Those six calls now route through one owned function in
`vendor/bulletproofs-r1cs-wgpu/src/msm_backend.rs`. The transcript, generator
derivation, commitment compression, and verifier equation are unchanged.

## What executes on the GPU now

With `DREGG_REQUIRE_WGPU=1`, every typed/canonical scalar entering one of the
six prover commitments is uploaded to a portable WGSL kernel. The kernel
derives the 32 unsigned radix-256 windows, and the host checks every returned
digit byte-for-byte against the scalar's canonical dalek encoding. A missing
adapter, CPU/software adapter, dimension overflow, map failure, or parity
mismatch aborts proof creation. The input, output, and readback device buffers
are cleared and awaited before release; host staging copies are scrubbed.

This is a real GPU dispatch through the production proof path, but it is a
**preparation tooth**, not a GPU group MSM. Dalek still performs the actual
Ristretto multiscalar multiplication and therefore remains the proof-byte
oracle and output producer.

Dispatch policy is explicit:

* unset: ordinary dalek CPU path, with no GPU allocations;
* `DREGG_BULLETPROOFS_WGPU=auto`: try the exact preparation stage and fall back
  to CPU if the GPU is unavailable;
* `DREGG_BULLETPROOFS_WGPU=1|required` or `DREGG_REQUIRE_WGPU=1`: fail closed
  unless a hardware adapter runs the parity-clean stage.

The hbox tooth is
`fhegg-fhe/tests/ristretto_msm_wgpu_required.rs`. It tests canonical scalar and
point validation, refuses the group-order scalar encoding, requires a hardware
adapter, then creates and CPU-verifies a real R1CS proof through the seam.

## The next exact kernel

The verifier and prover are different security jobs:

* The verifier's 1,048,627-point mega-MSM has public scalars and public points.
  A variable-time/window-indexed Pippenger implementation is appropriate. It
  is the cleanest first complete GPU MSM and can be checked against dalek before
  its identity result is accepted.
* The six prover commitments above contain witness-derived scalars. A naive
  bucket index leaks scalar windows through device addresses and contention.
  This lane needs constant-work, constant-address bucket accumulation, or an
  explicit deployment statement that the GPU and its microarchitectural side
  channels are inside the prover trust boundary. The present preparation
  kernel has fixed addressing and fixed work.

A portable complete implementation should keep generated points device
resident and use extended Edwards coordinates internally:

1. dalek canonically validates every Ristretto encoding and exports the
   representative's extended coordinates through a narrow additive fork API;
2. WGSL represents field elements with split-u32 limbs and applies complete
   Edwards add/double formulas modulo `2^255-19`;
3. public verifier MSM uses device-resident Pippenger buckets and a tree
   reduction; secret prover MSM uses the audited constant-address variant;
4. the returned point is canonically encoded, decompressed, and compared with
   dalek in qualification mode; malformed/non-canonical output is refused;
5. proof matrices cover CPU-prove/GPU-verify and GPU-prove/CPU-verify, alongside
   identity, cancellation, duplicates, zero/one/max-canonical scalars, and
   randomized full-width parity.

Generator derivation stays on the CPU and remains byte-identical. The payoff
comes from caching/uploading the fixed `G/H` tables once, not regenerating a
second generator universe on the GPU.

## Why this is the right boundary

The R1CS proof format should not know whether an MSM ran on AVX2, Vulkan, Metal,
or a CPU fallback. It should know only that the exact same Ristretto group
element was produced. Owning the six-call seam lets the arithmetic backend
change without changing the relation, transcript, proof bytes, or verifier;
the dalek result remains the ground truth until the full parity and proof
matrix is green.
