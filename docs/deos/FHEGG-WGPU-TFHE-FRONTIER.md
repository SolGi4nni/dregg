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

## The implemented first TFHE primitive

`fhegg-fhe/src/tfhe_wgpu.rs` and
`fhegg-fhe/src/shaders/torus_negacyclic_mac.wgsl` implement:

```text
out = accumulator + sum_t lhs_t * rhs_t
      in (Z/2^64Z)[X]/(X^N+1)
```

The shader uses two `u32` limbs per torus coefficient and 16-bit partial products,
so every multiplication, carry, borrow, and negacyclic sign agrees bit-for-bit
with wrapping `u64`.  The gate compares both the CPU reference and the selected
portable backend directly with tfhe-rs at `N=2048` and the two-product shape of one
default external-product output row.  Zero/non-power-of-two degree, empty batches,
length disagreement, partial polynomials, and address-space overflow fail before
dispatch.  No adapter, no device, or insufficient adapter limits take an explicit
CPU fallback; a failure after GPU execution begins is returned.

This is only the coefficient-domain polynomial-MAC rung.  It is O(N^2), is not
wired into `FheUint32`, and does not implement signed gadget decomposition, a fast
transform, a complete GGSW external product, CMUX, blind rotation, sample
extraction, PBS, or integer comparison.  The next credible speed frontier is a
subquadratic exact transform (or a carefully parity-bounded Fourier carrier), then
the default-shape external product behind the same tfhe-rs differential gate.
