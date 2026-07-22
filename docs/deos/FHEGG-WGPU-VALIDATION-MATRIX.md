# fhEgg portable-GPU correctness matrix

fhEgg treats a GPU as an acceleration authority, never a semantic authority.
Every portable kernel must preserve an independently executable CPU definition
bit for bit, must report the backend that actually ran, and must reject malformed
inputs before adapter selection can affect acceptance.

The executable matrix lives in:

- `fhegg-fhe/tests/wgpu_correctness_matrix.rs` for the resident BFV fold and
  portable torus negacyclic MAC;
- `fhegg-fhe/tests/private_book_bfv_wgpu_matrix.rs` for the private-book
  signed-dot precompute behind `amm-input-binding`;
- `fhegg-fhe/tests/bfv_odd_ntt_wgpu_required.rs` for the standalone scheduled
  odd forward/inverse transforms used by the private-book NTT-family witness;
- focused kernel unit tests beside each implementation.

## Matrix

| Surface | Exact oracle | Randomized/adversarial coverage | Fallback law | Real-GPU tooth |
|---|---|---|---|---|
| BFV resident fold | `bfv_lean::fold` | degrees 1..4096; 1/2/many rows; zero, `q-1`, u32 carry boundary; level/shape/noncanonical/wrap refusals | CPU-only is explicit; unsupported RNS shape is labelled; malformed acceptance is adapter-independent | exact deployed RNS shape must report `GpuResident` |
| BFV RNS NTT multiply | `bfv_ntt_gpu::multiply_rns_cpu` | degrees 8..4096; zero, `q-1`, u32 carry boundary; row/degree/modulus/noncanonical refusals | CPU policy, unavailable adapter, and adapter-limit fallbacks have distinct labels; execution errors never fall back | deployed degree-4096, three-RNS shape must report `Wgpu` |
| BFV scheduled odd NTT | Lean `oddNtt`/`oddIntt` direct sums plus `transform_odd_rns_cpu` | every q0/q1/q2 output is CPU/GPU differential-checked; spread coefficients are independently checked against the direct sums; changed coefficient/input and wrong root/stage/modulus refuse | every execution carries a validated root/stage schedule and the actual backend label | standalone forward and inverse at degree 4096 must both report the same named `Wgpu` adapter |
| TFHE torus MAC frontier | `torus_negacyclic_mac_cpu` | power-of-two degrees; multiple products; `u64::MAX`, high-bit, carry and negacyclic-sign wraparound; malformed dimensions | capability fallback returns `CpuFallback(reason)`; execution errors after selection do not fall back | supported shape must report `Wgpu` |
| Private-book signed dots | local exact `i128` signed sum | word-boundary degrees; all-positive/all-negative/random signs; 37-bit RNS values across u32 carry | direct kernel never falls back; production is CPU unless wgpu is requested, then absence is an error | deployed-size shape must execute with a named adapter |

The ordinary tests are safe on headless CI: they still exercise CPU definitions,
preflight, fallback labels, and all malformed-input refusals. They do not pretend
that this proves a shader ran. The ignored tests are the hard residency teeth and
fail closed without a real adapter.

Run the complete hard lane on hbox:

```sh
scripts/hbuild gpu-e2e scripts/test-fhegg-wgpu-matrix.sh
```

`DREGG_REQUIRE_WGPU=1` is set by the script. A green run therefore means exact
CPU parity **and** actual wgpu residency for every supported kernel in the lane;
a capability fallback is a red result there.

## Admission rule for another kernel

A new GPU kernel is not part of the trusted fhEgg path until it has all four:

1. a small, executable CPU definition that is not a transcription of the shader;
2. deterministic randomized parity over legal shapes and arithmetic boundaries;
3. adversarial refusal tests for dimensions, modulus/range assumptions, overflow,
   and buffer/dispatch bounds;
4. an ignored hard-residency tooth wired into the hbox script.

Performance measurements are separate. A faster result with no parity tooth is
an experiment, not a backend.
