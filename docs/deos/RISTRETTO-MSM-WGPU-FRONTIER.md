# Ristretto MSM on wgpu: the Bulletproofs backend boundary

**Status (2026-07-21): exact GPU group addition and a complete bounded public-
scalar MSM are implemented and hard-gated on hbox. The implementation is still
a performance red and remains disabled by default. Secret prover MSM remains
dalek/CPU.**

This is classical Ristretto/Bulletproofs acceleration. It does not make the
proof post-quantum and is not the HidingFRI/TFHE cryptographic end state.

## What is real now

The vendored yoloproofs fork owns both MSM dispatch seams in
`vendor/bulletproofs-r1cs-wgpu/src/msm_backend.rs`:

* the six private-book prover commitments route through one owned function;
* the verifier's final optional MSM routes through a second owned function;
* both use the same exact `curve25519-dalek-dregg` point type and generator
  universe as the CPU path.

The prover seam handles witness-derived scalars. With wgpu required, it runs a
fixed-work, fixed-address scalar-window preparation kernel and checks every
returned byte against the canonical dalek scalar encoding. The actual secret
group MSM remains dalek's constant-time CPU operation. The public verifier seam
has a complete extended-Edwards GPU MSM:

1. validate canonical scalar and compressed Ristretto encodings on the CPU;
2. export checked extended Edwards coordinates through the narrow dalek fork;
3. build chunk-local Pippenger buckets on the device;
4. reduce chunks, collapse weighted buckets, and combine windows in four
   ordered dispatches in one compute pass;
5. read back one extended point; and
6. accept it only when dalek independently computes the same MSM and validates
   both its coordinates and canonical compressed encoding.

The device and shader pipeline are process-persistent. Each warm call currently
uploads points and scalars, creates its scratch buffers, performs four
dispatches, and does one readback. The bounded qualification implementation
refuses more than 4,096 terms before allocation. Consequently, it can exercise
an ordinary 147-point range verifier but cannot yet execute the real 0.5M–4.2M
threshold or private-book verifier MSMs. In `auto` mode those oversized calls
fall back to dalek; in `required` mode they fail closed.

Dispatch policy is explicit:

* unset or `off`: pure dalek, no GPU allocation;
* `DREGG_BULLETPROOFS_WGPU=auto`: try the qualified GPU path and explicitly
  fall back on refusal;
* `DREGG_BULLETPROOFS_WGPU=1|required` or `DREGG_REQUIRE_WGPU=1`: require a
  hardware adapter and exact parity, otherwise return an error.

The separate group-add tooth covers identity, cancellation, duplicates,
full-width scalars, and malformed encodings. The complete-MSM tooth covers the
same boundary laws plus a CPU-prove/GPU-required-verify R1CS matrix.

## Measured RX 6750 XT result

The current kernel chooses the best measured geometry in this bounded range:
radix 16 with 64-term chunks below 2,048 terms, and radix 128 with 256-term
chunks at or above 2,048. Field add/sub canonicalization was shortened, the
duplicate `Z1*Z2` product was removed, redundant post-add identity checks were
removed, and the adaptive window extractor handles windows that cross bytes.

The isolated release gate on hbox's RX 6750 XT passed exact parity 1/1:

| Terms | dalek CPU | warm GPU call | Geometry |
|---:|---:|---:|---|
| 17 | 0.219 ms | 0.973 s | radix 16, 1 chunk |
| 256 | 1.034 ms | 1.288 s | radix 16, 4 chunks |
| 1,024 | 2.991 ms | 2.333 s | radix 16, 16 chunks |
| 4,096 | 9.827 ms | 4.643 s | radix 128, 16 chunks |

The same process's cold 17-term call was 9.155 s end to end, including device
and shader initialization; driver-cache state makes cold compilation especially
variable. The 4,096-term warm row improves the first exact radix-16 baseline
from 7.508 s to 4.643 s, but it remains about 470 times slower than dalek. This
is correctness evidence, not a speedup claim, and the backend must stay
default-disabled.

In the immediately preceding fixed-radix-128 qualification, the exact 4,096
row was **4.722 s GPU versus 9.563 ms dalek**. The small difference from the
adaptive rerun above is ordinary run-to-run variance, not a distinct algorithm.

The performance cause is no longer launch count. The portable field currently
uses 32 base-256 `u32` limbs. One field multiply forms 1,024 limb products, and
every complete Edwards add performs several field multiplies. Wider windows
reduce group additions but multiply bucket scans; measured six- and eight-bit
alternatives both lost to the adaptive four/seven-bit choice. Pipeline caching,
four in-pass dispatches, and one readback are already in place.

Qualification command:

```sh
scripts/hbuild gpu-e2e env DREGG_BULLETPROOFS_WGPU=required \
  cargo nextest run --release \
  --manifest-path vendor/bulletproofs-r1cs-wgpu/Cargo.toml \
  --features wgpu-msm --test wgpu_msm_perf \
  --run-ignored all --no-capture
```

## Why a GPU still makes sense

The small ordinary range proof does not justify a one-off GPU dispatch. The
large real workloads do:

| Workload | MSM size |
|---|---:|
| ordinary 64-bit range verifier | 147 |
| distributed-input commitment | 12,436 |
| private-book R1CS verifier | 1,048,627 |
| threshold range verifiers | 532,522–4,227,120 |
| largest private-book initial prover commitment | 870,319 |

At those shapes, a compact field representation, resident fixed generators,
buffer reuse, and batch scheduling can amortize GPU setup and expose enough
parallelism. That is a sound reason to build the backend; it is not a reason to
enable this qualification kernel prematurely.

Verifier and prover remain different security jobs. Verifier scalars and points
are public, so variable-time bucket indexing is appropriate. Prover scalars are
witness-derived: the present Pippenger address pattern would leak scalar
windows. A production GPU prover therefore needs a constant-address design or
an explicit, audited claim that the device and its microarchitectural channels
are inside the prover trust boundary. The fixed-address preparation tooth does
not make the later group operation GPU-resident.

## Next implementation frontier

The next material speed step is field multiplication, with two concrete exact-
portable spikes worth measuring. A uniform 20-limb radix-2^13 representation
keeps its pre-carry convolution within `u32`, cuts multiplication from 1,024 to
400 limb products, and shrinks point/scratch storage without emulated 64-bit
arithmetic. A cooperative workgroup multiply instead assigns convolution
coefficients to lanes and keeps the wide scratch in workgroup memory, attacking
the current single-invocation serial depth and likely register spilling. Shader
compiler occupancy/scratch statistics on RADV should decide their order. A
10-limb 26/25-bit split-wide backend and native shader-`i64` specialization
remain further candidates.

Only after a compact/cooperative representation is exact and parity-green is
it worth lifting the 4,096-term ceiling, retaining generator tables and scratch
buffers across calls, and measuring the production 12K/0.5M/1M/4.2M shapes.

Further rungs are affine-Niels mixed addition for fixed tables, a genuinely
constant-address prover engine, and the full cross-backend proof matrix. Proof
transcripts, generator derivation, and compressed proof bytes stay unchanged;
only the exact group-arithmetic provider is allowed to vary.
