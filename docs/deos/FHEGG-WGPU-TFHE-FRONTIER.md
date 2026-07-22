# fhEgg portable GPU boundary

This note separates three mechanisms that are easy to collapse into “fhEgg GPU.”
It records the code at HEAD and the exact claim made by the first portable torus
kernel.

## What fhEgg executes

The older all-TFHE reference clear remains in `fhegg-fhe/src/lib.rs::fhe_clear`.
It encrypts unary order rows as `FheUint32`, sums every demand and supply column,
computes `min(D[p], S[p])`, and selects the lowest-price maximum volume.  For `K`
price buckets its crossing executes:

- `K` encrypted `ge` comparisons and `K` selects for the minima;
- `K - 1` encrypted strict-`gt` comparisons and `2(K - 1)` selects for the
  oblivious argmax.

That is `2K - 1` comparisons and `3K - 2` selects.  It is independent of the
number of orders after aggregation, but it remains PBS-class work in tfhe-rs.
The measured CPU envelope is minutes-class for useful grids.

The newer fhEgg construction does not send the BFV aggregate through this TFHE
crossing.  `fhegg-fhe/src/mpc.rs` states the cut explicitly: packed exact BFV does
the additive fold, the custodians derive shares at the output boundary, and a
PartyMPC comparison reveals only `(p*, V*)`.  Therefore the all-TFHE crossing is a
real comparison/PBS benchmark and a possible future backend target, not the live
private-clearing data path.

## Exact tfhe-rs shape

`fhegg-fhe` resolves tfhe-rs 1.6.3 with the `integer` feature and no `gpu` feature.
`ConfigBuilder::default()` consequently selects
`PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128`:

| parameter | value |
|---|---:|
| message modulus / carry modulus | 4 / 4 |
| `FheUint32` radix blocks | 16 |
| small / big LWE dimension | 918 / 2048 |
| GLWE dimension / size | 1 / 2 |
| polynomial size | 2048 |
| PBS decomposition | base log 23, level count 1 |
| key switch decomposition | base log 4, level count 4 |
| ciphertext modulus | native torus, `2^64` wrapping arithmetic |
| high-level key choice / PBS order | `Big` / key-switch then bootstrap |
| reported `log2_p_fail` | -129.581 |

The upstream high-level `ge`, `gt`, and `if_then_else` interfaces do not expose a
portable backend hook.  The crate's optional GPU implementation is CUDA-specific.
Its classic CPU PBS goes through modulus switching, blind rotation (successive
GGSW/GLWE CMUX external products), and sample extraction.  The public core-crypto
polynomial reference used by the new parity gate is
`polynomial_wrapping_add_mul_assign` over
`(Z/2^64Z)[X]/(X^N+1)`.

## What already uses wgpu

fhEgg did not abandon wgpu.  It uses WGSL for the packed BFV aggregation:

- `fhegg-fhe/src/shaders/bfv_fold.wgsl` is the bit-exact three-modulus RNS fold;
- `fhegg-fhe/src/gpu_arena.rs` retains the device, pipeline, and ciphertext
  buffers across folds and streams batches through adapter limits;
- the CPU path is a labelled capability fallback, while GPU execution errors are
  not hidden.

This is the right existing kernel because additive BFV fold is bandwidth-bound.
BFV ciphertext multiplication still delegates to fhe.rs; `bfv_mul.rs` names its
NTT GPU work as unbuilt.  There are no fhEgg HIP kernels and hbox does not have
ROCm/HIP installed.  Its AMD RX 6750 XT is available through Vulkan, which is
exactly the portable wgpu route.  Older `HBOX-24CORE-ENVELOPE.md` prose predates
that GPU observation and is a CPU measurement, not current hardware discovery.

## The implemented portable TFHE rung

`fhegg-fhe/src/tfhe_wgpu.rs` first implemented the coefficient-domain
native-torus polynomial MAC in
`fhegg-fhe/src/shaders/torus_negacyclic_mac.wgsl`:

```text
out = accumulator + sum_t lhs_t * rhs_t
      in (Z/2^64Z)[X]/(X^N+1)
```

The shader uses two `u32` limbs per torus coefficient and 16-bit partial products,
so every multiplication, carry, borrow, and negacyclic sign agrees bit-for-bit
with wrapping `u64`.  On top of that primitive the module now implements signed
TFHE gadget decomposition, the complete standard-domain GGSW-by-GLWE external
product, and encrypted CMUX.  The default-shape qualification gate compares the
CPU result, the portable backend, and an independent tfhe-rs core-crypto oracle at
`N=2048`, GLWE size two, base log 23, level count one.

The coefficient route is still quadratic, so the same public API now also owns an
exact subquadratic route in `fhegg-fhe/src/tfhe_ntt_wgpu.rs` and
`fhegg-fhe/src/shaders/torus_ntt_montgomery.wgsl`.  It performs a negacyclic RNS
NTT under four fixed primes whose product carries about 120 bits.  WGSL has no
portable native `u64`, so the shader implements exact `u32` Montgomery arithmetic
with 16-bit-split products; it does not use an approximate Fourier carrier or a
vendor extension.  All standard-GGSW product pairs are packed into one command
submission and one readback.  Host plans and GPU pipelines are retained, and the
root/twist plan is cached by degree.

CRT reconstruction is only admitted when a conservative signed-convolution bound
fits uniquely inside the centered four-prime product.  Unsupported degree/root
order, excessive parameter bounds, adapter limits, and malformed shapes fail
before dispatch or take an explicitly labelled capability fallback according to
the caller's policy.  A failure after the GPU is selected is returned; it is not
silently recomputed and reported as GPU work.  The qualification suite forces
both GPU algorithms, uses full-width random torus coefficients, and compares them
bit-for-bit with the CPU authority across `N=256..4096`; a second hostile case
uses two decomposition levels and base log 31.  It also reports process-cold cost
and parity-checked five-sample warm medians on the selected adapter.

## The device-resident blind-rotation slice

`fhegg-fhe/src/tfhe_blind_rotation_wgpu.rs` and
`fhegg-fhe/src/shaders/torus_blind_rotation.wgsl` now implement the exact classic
blind-rotation schedule over a native-modulus LWE mask/body and a standard
coefficient-domain bootstrapping key:

```text
acc <- LUT / X^modswitch(body)
for (a_i, GGSW(s_i)):
    difference <- acc * X^modswitch(a_i) - acc
    acc <- acc + GGSW(s_i) * Decomp(difference)
```

The two accumulator buffers ping-pong on-device, the complete standard BSK prefix
is uploaded once, rotation and signed gadget decomposition execute on the GPU, and
the dependent CMUX chain is encoded into one command submission with one final
readback.  The modulus-switch rounding, including the final bin wrapping through
zero, and every monomial exponent in `[0, 2N)` are differentially pinned to tfhe-rs
semantics.

The strict encrypted gate uses the deployed `N=2048`, GLWE-size-two, base-log-23,
level-one shape and four genuinely noisy GGSW selector ciphertexts.  Two strict
runs on hbox's AMD RX 6750 XT through Vulkan measured 5.826--5.914 ms for the exact
CPU authority, 71.087--121.063 ms process-cold GPU startup, and 2.865--2.882 ms
parity-checked warm GPU medians.  The gate also decrypts the result to the expected
aggregate LUT rotation and proves a one-bin mask edit changes the exact ciphertext.

## The remaining PBS boundary

The new rung is a real blind rotation, but it deliberately uses the exact
coefficient-domain external product inside the device-resident chain.  The current
RNS-NTT single-CMUX adapter performs gadget decomposition and CRT reconstruction on
the host, so it cannot yet be substituted between dependent rotations without
reintroducing a readback.  Closing that performance seam requires GPU-side CRT (or
a transform-form accumulator/BSK representation) across the whole chain.

The chain now has a PBS-shaped completion in
`fhegg-fhe/src/shaders/torus_pbs_extract_keyswitch.wgsl`:

```text
resident blind-rotation accumulator
    -> exact degree-zero GLWE sample extraction
    -> exact standard native-torus LWE key switch
    -> one final post-key-switch LWE readback
```

The CPU authority is bit-for-bit equal to tfhe-rs
`extract_lwe_sample_from_glwe_ciphertext` plus `keyswitch_lwe_ciphertext`.  The
strict GPU gate exercises the complete 2048-coefficient extracted input secret,
base-log-four/level-four key decomposition, and a deliberately narrow
eight-dimensional output key.  A standalone process on hbox's RX 6750 XT measured
13.377 ms CPU, 275.945 ms process-cold GPU, and a 6.474 ms parity-checked warm GPU
median.  In the combined strict regression, after the shared adapter and pipelines
had already been initialized by the blind-rotation gate, the same PBS gate measured
5.763 ms CPU, 57.652 ms for its first retained-context GPU call, and a 4.673 ms warm
GPU median.  These are different startup conditions, not interchangeable "cold"
measurements.  The standard KSK is load-bearing under mutation and the final
ciphertext decrypts to the same rounded message as tfhe-rs.

The production-dimension follow-on gate executes a complete reverse-order
qualification envelope, not yet the high-level `FheUint32` operation order.
It generates a real 918-bit input LWE secret, a genuinely noisy standard GGSW
encryption for every one of its BSK bits, and a real encrypted LWE input whose 918
mask coefficients all modulus-switch to nonzero rotations. It uses the full 57.38
MiB standard BSK, the complete 2048-to-918 standard key switch and its 57.44 MiB
KSK, and checks all 919 post-key-switch LWE coefficients bit-for-bit against
tfhe-rs. Clearing the final noisy BSK ciphertext changes the CPU authority, so slot
917 is load-bearing. This is a dense 918-CMUX gate, not sparse/no-op extrapolation.
Its order is bootstrap → 2048-to-918 key switch (`BootstrapKeyswitch`). The
default high-level parameter set encrypts under the 2048-dimensional big key and
uses 2048-to-918 key switch → bootstrap (`KeyswitchBootstrap`). Thus this gate
qualifies both exact kernels and deployed dimensions, but is not itself a typed
high-level ciphertext path.

`TorusPbsWgpuPlan` is the first explicit execution context for this path. Its
constructor validates the exact BSK/KSK shapes and uploads each immutable key
once. Repeated calls reuse those device buffers plus the process-retained adapter
and pipelines; only per-ciphertext accumulator/output buffers remain transient.
The plan rejects a 917-coefficient mask against its 918-coefficient binding and
continues to produce the uploaded result after the host BSK slice is changed,
demonstrating actual device custody rather than pointer-keyed host caching.

Encoding all 1,836 dependent decompose/external-product dispatches into one Vulkan
command buffer exhausted hbox's command/descriptor allocation even though the key
buffers fit comfortably. The exact dense route therefore submits at most 256 CMUX
steps per ordered command chunk. Both accumulator buffers, decomposition scratch,
BSK, and KSK remain device-resident across all four submissions, and there is still
only one final post-key-switch readback. Short schedules retain the single-command
path.

On hbox's RX 6750 XT, the final strict dense release gate passed in 9.667 seconds,
including real BSK/KSK generation, three full warm parity calls, hostile far-key
mutation, and an exact scaling sweep. The exact full CPU result took 1,493.795 ms,
plan creation plus both key uploads took 125.152 ms, the first prepared dense call
took 449.309 ms, and the parity-checked three-sample prepared median took 421.617
ms. That is about 3.5x faster than the exact CPU authority for the complete
coefficient-domain 918-step schedule.

With the same full 2048-to-918 key switch at every point, exact active-CMUX scaling
was: 64 steps, 106.232 ms CPU / 43.180 ms GPU; 256 steps, 417.605 / 128.940 ms;
512 steps, 830.367 / 243.958 ms; and 918 steps, 1,493.795 / 421.617 ms. The GPU
curve is still essentially linear in the blind-rotation step count. The result is
a strong exact baseline and a useful deployed fallback, not a substitute for
transform-form residency.

## Exact transform-resident dense PBS

`TorusPbsTransformWgpuPlan` closes that named performance seam for the measured
deployed-dimension kernel. Plan construction interprets every standard BSK coefficient as a centered
native-torus integer, maps it into the same four exact NTT primes, uploads the
complete 114.75 MiB residue carrier, and forward-transforms all 14,688
polynomial/modulus series once. The 57.44 MiB standard KSK and all root, twist,
Montgomery, and CRT tables are retained by the same device plan.

Each dependent CMUX then remains on-device:

```text
rotate / exact signed gadget decomposition
    -> four-prime forward NTT of both digit polynomials
    -> pointwise multiply-and-sum against resident BSK spectra
    -> inverse NTT of both product polynomials
    -> exact centered four-limb Garner CRT and native-torus add
```

The inverse path is not an approximate Fourier carrier. WGSL reconstructs the
unique centered integer under the existing conservative convolution bound using
four little-endian `u32` limbs, then retains its exact low 64 bits. Both
accumulator buffers and the shared digit/product scratch remain resident across
256-CMUX ordered command chunks. The final degree-zero sample extraction and full
2048-to-918 key switch execute against the resident accumulator, followed by the
only readback.

The strict gate compares every one of the 919 final coefficients with the
tfhe-rs/CPU authority for a genuinely dense 918-step encrypted input, repeats the
full transform result three times, and checks 64-, 256-, and 512-step exact
prefixes. Clearing the final noisy GGSW changes both CPU and a newly transformed
plan, while the original plan remains unchanged after the host BSK mutation. Both
coefficient and transform plans reject a 917-coefficient mask.

The final hbox RX 6750 XT release run passed in 10.519 seconds. One-time transform
plan construction took 259.949 ms. A one-CMUX call with the full output key switch
took 10.326 ms; dense 918 took 165.838 ms on its first call and 115.746 ms at the
three-sample warm median. In the same process the coefficient plan's warm median
was 422.847 ms and the exact CPU authority was 1,380.391 ms: transform residency
is about 3.65x faster than the portable coefficient GPU and 11.9x faster than CPU.

Exact scaling with the full 2048-to-918 key switch at every point was: 64 active
CMUX steps, 99.029 ms CPU / 43.780 ms coefficient GPU / 11.622 ms transform GPU;
256 steps, 389.560 / 132.751 / 28.049 ms; 512 steps, 774.481 / 245.173 / 52.973
ms; and 918 steps, 1,380.391 / 422.847 / 115.746 ms.

## Deployed high-level key-order weld

`fhegg-fhe/src/tfhe_high_level_wgpu.rs` now closes the typed one-block seam for
tfhe-rs 1.6's actual default `FheUint32` order. The adapter expands a retained
`CompressedServerKey` into its exact coefficient-domain BSK and KSK, uploads the
BSK through `TorusPbsTransformWgpuPlan`, and retains the KSK for the required
2048-to-918 pre-PBS key switch. This requires no tfhe-rs fork. A decompressed
`ServerKey` alone is insufficient because it retains only the Fourier BSK; key
setup must keep the compressed form from which both the ordinary server key and
the portable plan can be derived.

For each selected radix block the path is:

```text
ordinary big-key FheUint32 block
    -> exact tfhe-rs 2048-to-918 key switch
    -> the key's selected centered-mean modulus switch
    -> transform-resident 918-CMUX PBS
    -> degree-zero extraction without a trailing key switch
    -> ordinary big-key FheUint32 block
```

The new `extract_only` GPU terminal writes all 2,049 large-key LWE coefficients.
The adapter restores tfhe-rs degree/noise/modulus/atomic-pattern metadata and the
original high-level id, tag, rerandomization metadata, and untouched radix blocks.
`tests/tfhe_high_level_wgpu.rs` compares its decrypted result to tfhe-rs's own
`apply_lookup_table` and then feeds the GPU-produced value into a subsequent
normal high-level homomorphic addition. The fail-closed hbox RX 6750 XT release
gate passed 1/1 on 2026-07-21: exact compressed-key expansion, transform, and
upload took 317.965 ms; the first typed pre-key-switch + centered-mean transform
PBS + large-key reconstruction against that prepared plan took 143.891 ms. This
is a one-call qualification result, not a repeated-call median. The reverse-order dense qualification
also remained green after the shader extension.

This is a real typed high-level PBS/LUT primitive, not yet an automatic backend
for every overloaded integer operator. Comparisons still need their shortint
control flow wired to repeated plan calls, and the transform plan remains
restricted to `N=2048`, GLWE-two, PBS-23x1, and KS-4x4. Its spectrum memory and
per-PBS latency are real costs. Those are now dispatch/coverage boundaries rather
than a ciphertext/key-format blocker.

Consequently GPU output is still an accelerator result, never independent
protocol authority.  The bit-exact CPU/tfhe-rs definitions remain the acceptance
oracle, and the live fhEgg clearing path remains BFV aggregation plus PartyMPC as
described above. The next hard cut is to wire the typed plan into a real
comparison/control-flow operator and measure repeated calls—not infer full
`FheUint32` comparison throughput from one block LUT or the reverse-order dense
PBS benchmark.
