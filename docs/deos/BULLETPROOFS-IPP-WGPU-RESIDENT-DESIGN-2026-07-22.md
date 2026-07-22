# Resident WGPU inner-product fold design — 2026-07-22

This note freezes the implementation boundary for a possible resident WGPU
inner-product prover.  It is deliberately narrower than “move Bulletproofs to
the GPU”: the public generator fold and the witness-derived `L`/`R` MSMs have
different leakage properties, and the transcript orders them in a way that
prevents an isolated resident generator fold from being a production win.

## Production geometry

The largest authenticated-custody range proof has inner-product dimension
`N = 2,097,152 = 2^21`.  Its first round folds `N/2` G pairs and `N/2` H pairs,
so a combined pointwise dispatch processes `N` pairs and emits `N` points.

The qualified byte-radix shader represents each extended Edwards point as four
32-byte coordinates with every byte widened to `u32`: **512 bytes per point**.
At production size:

| resident object | byte-radix size |
|---|---:|
| G and H inputs, `2N` points | 2,147,483,648 B |
| one of G or H, `N` points | 1,073,741,824 B |
| first folded output, `N` points | 1,073,741,824 B |
| split inputs plus first output | about 3 GiB |

The RX 6750 XT on `hbox` reports both
`max_buffer_size = 2,147,483,647` and
`max_storage_buffer_binding_size = 2,147,483,647`.  A combined byte-radix G/H
binding therefore misses the binding ceiling by exactly one byte.  Split G and
H bindings fit.  A 64-thread pointwise dispatch needs `N/64 = 32,768`
workgroups, below the adapter's 65,535 per-dimension limit, and the approximately
3 GiB first-round ping-pong working set fits its 12 GiB VRAM.

The proposed qualification representation uses twenty radix-`2^13` `u32`
limbs per field element.  That is `4 * 20 * 4 = 320` bytes per extended point.
The combined initial G/H vector is then 1,342,177,280 bytes (1.25 GiB), within
one binding.  The representation removes the immediate binding failure, but it
does not by itself establish an arithmetic or end-to-end speedup.

## Transcript and security boundary

One inner-product round has this dependency order:

1. compute witness-derived `cL`, `cR`, `L`, and `R` using the current G/H;
2. append canonical `L` and `R` to the Merlin transcript;
3. derive the now-public challenge `u` and `u^-1`;
4. fold public G/H by `u` and `u^-1`, and fold secret `a`/`b`;
5. start the next round with the folded vectors.

The existing WGPU Pippenger kernel has scalar-dependent branches and addresses.
It is a public-verifier qualification path, not an acceptable implementation of
the witness-derived `L`/`R` MSMs.  A standalone GPU G/H fold would therefore
have to read the entire folded vector back before the next CPU `L`/`R` MSM.
Across all rounds that is approximately `2N` byte-radix points, or 2 GiB of
device-to-host output, plus synchronization and conversion.  Duplicating the
fold on CPU avoids the readback but removes the prospective speedup.

Consequently, the compact pointwise kernel in the first implementation stone is
**qualification-only**.  It may consume public points and public fixed scalars,
but it must not be wired into `inner_product_proof.rs` and must not accept a
secret-scalar workload.

## Smallest executable stone

The first stone is an additive compact-field Edwards kernel, because exact
group addition is the arithmetic core needed by both fixed-scalar multiplication
and pointwise folds.  It has these gates:

- a new radix-`2^13`, twenty-limb shader and isolated Rust adapter;
- canonical compressed Ristretto input only, with byte-for-byte round-trip
  refusal of malformed or non-canonical encodings;
- dalek computes every expected sum independently;
- GPU extended coordinates are accepted only through dalek's checked import and
  exact expected compressed encoding;
- exact parity at pair counts `1, 2, 63, 64, 65, 4096`;
- an allocation-free actual-adapter geometry check at `N = 2^21`;
- no production IPP wiring and no secret scalar API.

The executable pair-add path is bounded to 4,096 pairs unless a deliberately
named giant-public-buffer environment gate is set.  The `2^21` geometry check
does not allocate the 1.25 GiB input binding.

The stone is green on the qualified `hbox` RX 6750 XT over Vulkan.  Exact dalek
parity passed at `N = 1, 2, 63, 64, 65, 4096`; malformed compressed input was
refused; and the actual-adapter `2^21` preflight reported 1,342,177,280 input
bytes, 671,088,640 output bytes, and 32,768 workgroups without allocating those
buffers.  The complete release hardware tooth took 1.89 seconds:

```sh
scripts/hbuild gpu-e2e env DREGG_REQUIRE_WGPU=1 \
  cargo nextest run --release \
  --manifest-path vendor/bulletproofs-r1cs-wgpu/Cargo.toml \
  --features yoloproofs,wgpu-msm \
  --test wgpu_compact_edwards_parity --run-ignored all --no-capture
```

## Predetermined-public residency stone

The second qualification stone implements the fixed-public-scalar pointwise
fold without exposing a scalar input.  Round `r` uses a source-domain-derived,
nonzero public `u_r` and the pair `(u_r^-1, u_r)`.  The shader runs one uniform
256-bit simultaneous double-and-add schedule per pair; point addresses and the
schedule are fixed, while the remaining bit branches are public and uniform
across each dispatch.

One canonical public point vector, the complete challenge table, and a padded
public per-round control table are each uploaded once.  K ordered dependent
dispatches alternate two compact point buffers.  Only the final vector is
copied back, checked as canonical extended Edwards coordinates, and accepted
against an independently computed dalek fold.

The hardware tooth is green on the `hbox` RX 6750 XT for both odd and even
ping-pong endings.  Starting from 64 public points, K=5 returned two exact
points and K=6 returned one exact point.  Each run reported one point upload,
one complete challenge upload, one control-table upload, K dispatches, and one
readback.  Malformed compressed input and a non-halvable fold shape were
refused.  The combined release tooth took 2.36 seconds:

```sh
scripts/hbuild gpu-e2e env DREGG_REQUIRE_WGPU=1 \
  cargo nextest run --release \
  --manifest-path vendor/bulletproofs-r1cs-wgpu/Cargo.toml \
  --features yoloproofs,wgpu-msm \
  --test wgpu_public_fold_residency --run-ignored all --no-capture
```

This proves compact fixed-public-scalar arithmetic and intermediate device
residency.  The challenges are deliberately predetermined rather than drawn
from a live proof transcript, so it does **not** prove transcript integration
or make the kernel production prover authority.

## Production resident engine required

A production win requires one security-coherent resident engine rather than a
standalone fold:

- G/H remain device-resident in compact ping-pong buffers;
- witness `a`/`b` and the `cL`/`cR` reductions use fixed-address,
  constant-control-flow kernels;
- witness-derived `L`/`R` MSMs use a constant-address algorithm, not the current
  branch-bearing public Pippenger;
- each round reads back only the two canonical `L`/`R` points;
- the CPU transcript remains authoritative, derives `u`/`u^-1`, and uploads
  only those public 32-byte challenges;
- final proof bytes remain identical to the serial implementation.

This is the go/no-go line.  Compact group addition and public fixed-scalar
folding may advance independently as qualification stones.  They are not to be
called a production IPP optimization until the constant-address witness engine,
round-trip transcript parity, and measured end-to-end win exist together.
