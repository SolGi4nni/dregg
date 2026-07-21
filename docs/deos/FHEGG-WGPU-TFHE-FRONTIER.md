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

## The remaining PBS boundary

This is a real exact external product and CMUX, but it is not yet a complete
programmable bootstrap or a high-level `FheUint32` backend.  Gadget decomposition
and CRT reconstruction currently happen on the host, and one readback remains per
external product.  Blind rotation would chain hundreds of dependent CMUX steps;
making that useful requires a device-resident accumulator, a transform-form
bootstrapping key, rotation/modulus-switch kernels, sample extraction, key switch,
and an integration seam below tfhe-rs integer comparison.

Consequently GPU output is still an accelerator result, never independent
protocol authority.  The bit-exact CPU/tfhe-rs definitions remain the acceptance
oracle, and the live fhEgg clearing path remains BFV aggregation plus PartyMPC as
described above.  The next hard performance cut is to keep the accumulator and
bootstrapping key resident across an entire blind rotation, then measure an actual
PBS and integer comparison—not extrapolate one from a single CMUX.
