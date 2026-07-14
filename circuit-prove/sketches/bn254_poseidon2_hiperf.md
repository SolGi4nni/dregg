# High-performance Poseidon2-BN254 WebGPU Merkle kernel

[`bn254_poseidon2_hiperf.wgsl`](./bn254_poseidon2_hiperf.wgsl) is a compact,
portable replacement for the generated BN254 hash section in
`gpu_backend.rs`. It preserves the backend's three entry points because a
whole Merkle tree needs a device-wide barrier between levels, which WebGPU
does not provide inside one dispatch. The Rust `bn254_merkle_root` method is
the host-side orchestration of these entries.

## Parity contract

The shader uses exactly the existing outer-MMCS construction:

- BN254 base-field modulus
  `0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`,
  represented as eight little-endian `u32` limbs.
- Montgomery radix `R = 2^256`, `N0_INV = 0xefffffff`, and
  `R^2 mod P = 0x0216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7`.
- Poseidon2 width 3 and degree-5 S-box, with 4 initial external rounds, 56
  internal rounds, and 4 terminal external rounds.
- The initial external linear layer and the layer after every full round are
  `J + diag(1,1,1)`, i.e. `[[2,1,1],[1,2,1],[1,1,2]]`. The internal layer is
  `J + diag(1,1,2)`, i.e. `[[2,1,1],[1,2,1],[1,1,3]]`.
- The exact `RC3_EXT_INITIAL`, `RC3_INTERNAL`, and `RC3_EXT_TERMINAL` values
  already imported by `gpu_backend.rs`. Do not maintain a second literal
  table for this shader; pack those arrays into binding 3 as described below.
- Leaf hashing is the same
  `MultiField32PaddingFreeSponge<BabyBear, Bn254, _, 3, 2, 1>`: canonicalize
  each BabyBear Montgomery word, add one, shifted-pack eight radix-`2^31`
  digits per BN254 rate element, overwrite-absorb two elements, and return
  state lane 0.
- Parent hashing and matrix injection are the same
  `TruncatedPermutation<_, 2, 1, 3>` operations.

Round constants and permutation state are Montgomery values. Matrix words are
BabyBear Montgomery values. Digest buffers and the final root are canonical
BN254 values, each stored as eight little-endian `u32` limbs. In particular,
do not upload canonical round constants directly.

## Bind group 0

All three pipelines use one bind group with this exact layout:

| Binding | WGSL address space | Host binding type | Contents |
| --- | --- | --- | --- |
| 0 | `storage, read` | read-only storage buffer | Matrix arena, previous digest layer, or injected digest layer |
| 1 | `storage, read` | read-only storage buffer | `u32` dispatch descriptor |
| 2 | `storage, read_write` | storage buffer | Canonical digest output; also the old left input for `combine_main` |
| 3 | `uniform` | uniform buffer | Immutable 2,592-byte `PoseidonParams` block |

Bindings 0-2 retain the current backend's array-of-digests format: digest `i`
occupies words `[8*i, 8*i+8)`. Add binding 3 to the hash bind-group layout and
to every hash bind group. It should be created once with `UNIFORM | COPY_DST`
usage and shared by the three pipelines. The buffer is far below WebGPU's
portable 64 KiB minimum maximum uniform-binding size.

### Binding 3 byte layout

`MontFp` is two `vec4<u32>` values, so its uniform-array stride is exactly 32
bytes. `PoseidonParams` is packed as follows:

| Byte range | Type | Value |
| --- | --- | --- |
| `0..2560` | `MontFp[80]` | Montgomery round constants |
| `2560..2576` | `vec4<u32>` | external diagonal `(1, 1, 1, 0)` |
| `2576..2592` | `vec4<u32>` | internal diagonal `(1, 1, 2, 0)` |

For every `MontFp`, `lo` holds limbs 0-3 and `hi` holds limbs 4-7. Pack the 80
constants in this order:

| `MontFp` index | Existing source value |
| --- | --- |
| `3*r + lane`, `r=0..3`, `lane=0..2` | `RC3_EXT_INITIAL[r][lane]` |
| `12 + r`, `r=0..55` | `RC3_INTERNAL[r]` |
| `68 + 3*r + lane`, `r=0..3`, `lane=0..2` | `RC3_EXT_TERMINAL[r][lane]` |

Use the same conversion already used by `hash_shader_source`:

```text
p = parse_hex(BN254_P_HEX)
r = (1 << 256) mod p
montgomery_constant = (parse_hex(existing_rc) * r) mod p
write limbs8(montgomery_constant) in little-endian order
```

This reuses the authoritative constants instead of duplicating them in WGSL,
and uniform loads are wave-uniform and cache-friendly.

## Entry points and descriptors

All entries use `@workgroup_size(64)`. Dispatch
`ceil(descriptor_count / 64)` workgroups in X and one in Y/Z. Only the final
workgroup takes the bounds-return path.

### `leaf_main`

Descriptor words are:

```text
[matrix_count, base_row, row_count, 0,
 matrix_0_src_offset_words, matrix_0_width,
 matrix_1_src_offset_words, matrix_1_width, ...]
```

Binding 0 contains the equal-height matrices, each in row-major BabyBear
Montgomery form at its declared word offset. Invocation `i < row_count` hashes
logical row `base_row + i` and writes canonical digest
`outd[8*row .. 8*row+8]`. This preserves the backend's watchdog chunking:
rewrite `base_row`/`row_count` between dispatches without rebinding the arena
or output buffer.

### `compress_main`

Descriptor words are `[output_count, base_output, 0, 0]`. Invocation `i`
computes output index `j = base_output + i` as:

```text
outd[j] = permute([src[2*j], src[2*j+1], 0])[0]
```

Bindings 0 and 2 must be different, non-overlapping layer buffers. Ping-pong
them between levels. Values on both sides are canonical at the buffer edge.

### `combine_main`

Descriptor words are `[output_count, base_output, 0, 0]`. Invocation `i`
computes output index `j = base_output + i` as:

```text
outd[j] = permute([old_outd[j], src[j], 0])[0]
```

Binding 0 is the same-height matrix-group digest layer being injected; binding
2 is the current tree layer. After all required leaf, compression, and
injection dispatches, the canonical Merkle root is words `outd[0..8]`.

## Performance design

- **Small compiler IR.** The 8-limb multiply, four/56/four round schedule, and
  all limb operations are real loops. No round constants are embedded in the
  module, so Mesa cannot constant-expand a giant permutation during pipeline
  creation.
- **CIOS Montgomery multiplication.** Product accumulation and Montgomery
  cancellation are interleaved. A 10-word accumulator replaces the old
  17-word schoolbook product plus reduction array, reducing per-invocation
  private state and register/spill pressure.
- **Statically addressed state lanes.** The three field lanes are named struct
  members rather than a dynamically indexed outer array, allowing backend
  scalarization even though each field's eight-limb arithmetic remains looped.
- **Cheap structured diffusion.** The MDS matrices are supplied in the uniform
  ABI but evaluated as `J + diag(d)`. Coefficients 1 and 2 use copies and field
  doubling, avoiding general field multiplications in every linear layer.
- **Uniform constant traffic.** Every invocation reads the same round constant
  at the same time. A 2.5 KiB uniform table fits comfortably in constant/uniform
  caches on Vulkan, Metal, and browser WebGPU implementations.
- **Controlled occupancy.** A 64-thread workgroup follows the backend's
  measured `HASH_WG` choice for the large 24-limb Poseidon state. Larger groups
  amplify VGPR/private-memory pressure without adding data reuse.
- **No unnecessary workgroup memory.** Nodes are independent and share no
  operands. Direct sequential digest loads avoid barriers and preserve cache
  capacity for the uniform table and Montgomery state.
- **Conversions only at buffer edges.** A node converts its two canonical
  inputs once, keeps all 64 rounds in Montgomery form, and converts only lane
  0 back for storage.
- **Portable control flow.** There are no subgroup operations, 64-bit integer
  requirements, extensions, atomics, or backend-specific intrinsics. The
  source validates as standard WGSL and uses only WebGPU core features.

The 64-thread value is the correct initial production setting. Benchmark 32
versus 64 on the target RADV generation only after parity tests are green;
do not increase it merely to fill a nominal 256-thread workgroup, because this
kernel is register-bound rather than synchronization- or latency-bound.
