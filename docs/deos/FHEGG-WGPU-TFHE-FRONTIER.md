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
| LWE dimension | 918 |
| GLWE dimension / size | 1 / 2 |
| polynomial size | 2048 |
| PBS decomposition | base log 23, level count 1 |
| key switch decomposition | base log 4, level count 4 |
| ciphertext modulus | native torus, `2^64` wrapping arithmetic |
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

This is still not a complete high-level `FheUint32` backend.  The deployed
918-mask blind-rotation/918-output-key envelope has not yet been qualified, and
the default shortint key order plus integer comparison integration remains.  Those
are named implementation boundaries, not properties inferred from the four-step,
eight-output benchmark.

Consequently GPU output is still an accelerator result, never independent
protocol authority.  The bit-exact CPU/tfhe-rs definitions remain the acceptance
oracle, and the live fhEgg clearing path remains BFV aggregation plus PartyMPC as
described above.  The next hard performance cut is to keep the accumulator and
bootstrapping key in transform form across the full deployed blind rotation, then
qualify the full deployed key dimensions and wire the resulting PBS-shaped
primitive below an integer comparison—not extrapolate that result from a short
prefix.
