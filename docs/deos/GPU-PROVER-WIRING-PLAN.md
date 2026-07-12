# GPU-Prover Wiring Plan — wgpu behind Plonky3's trait seams, measured

Status: PLAN + FIRST MEASURED INCREMENT (2026-07-12). The backend question is
settled (GPU-PROVER-PROTOTYPE.md §9-§11: ONE portable wgpu source; native
Metal buys ≤1.27x on the hash kernel and a tie on the NTT — no native seam).
This doc is the *wiring*: how the measured kernels get behind the actual
prover's trait seams, what fraction of the real prove each seam controls, and
the first trait-level measured number. Increment 1 (the wgpu
`TwoAdicSubgroupDft`) is BUILT and GREEN:
`circuit-prove/sketches/gpu-dft-plonky3/` (`cargo run --release` = the gate).

## 1. The exact trait seams (pinned Plonky3 rev 82cfad7)

Both provers are `TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>`:

- **outer/shrink**: `OuterPcs = TwoAdicFriPcs<BabyBear, Radix2DitParallel<BabyBear>,
  MerkleTreeMmcs<BabyBear, Bn254, MultiField32PaddingFreeSponge<BabyBear,Bn254,Poseidon2Bn254<3>,3,2,1>,
  TruncatedPermutation<Poseidon2Bn254<3>,2,1,3>, 2, 1>, ExtensionMmcs<...>>`
  (`circuit-prove/src/dregg_outer_config.rs:142-166`; the DFT alias at `:163`,
  built at `:385`). **Trace/quotient arithmetic and the DFT are BabyBear**
  (`dregg_outer_config.rs:133-137`); **only the MMCS hash/digest field is
  BN254** (`:5-12`). So the *NTT kernel* that applies to the shrink is the
  BabyBear one; the *hash kernel* the shrink needs is Poseidon2-**BN254** t=3
  — NOT the measured BabyBear-W16 hash kernel (that one applies to the inner
  config's MMCS, `plonky3_recursion_impl.rs:70-78`).
- **inner (apex fold)**: same shape, all-BabyBear (Poseidon2BabyBear<16>
  sponge/compress) — `dregg_outer_config.rs:14-23` table.

### Seam 1 — the DFT (`TwoAdicSubgroupDft<F>`, dft/src/traits.rs:27)

```rust
pub trait TwoAdicSubgroupDft<F: TwoAdicField>: Clone + Default {
    type Evaluations: BitReversibleMatrix<F> + 'static;              // traits.rs:37
    fn dft_batch(&self, mat: RowMajorMatrix<F>) -> Self::Evaluations; // traits.rs:61 (only required method)
    fn coset_lde_batch(&self, mat: RowMajorMatrix<F>, added_bits: usize, shift: F)
        -> Self::Evaluations;                                         // traits.rs:226 (default = idft → zero-pad → coset_dft)
    fn coset_lde_batch_with_transform<T>(...);                        // traits.rs:241 (used by some quotient paths)
}
```

Call site: `TwoAdicFriPcs::commit` →
`self.dft.coset_lde_batch(evals, self.fri.log_blowup, shift).bit_reverse_rows().to_row_major_matrix()`
with `shift = Val::GENERATOR / domain.shift()` (two_adic_pcs.rs:309-319; the
quotient twin at :336-344; opening re-evaluation uses `coset_idft_batch` +
`coset_dft_batch` at :382-388). `Radix2DitParallel::Evaluations =
BitReversedMatrixView<RowMajorMatrix<F>>` (radix_2_dit_parallel.rs:146) — the
inner matrix is stored in **bit-reversed row order**, so the PCS's
`.bit_reverse_rows().to_row_major_matrix()` is free. A GPU impl must produce
the same type/layout or it silently pays a 452-MiB host permute per commit.
The wiring delta once promoted: ONE type alias
(`dregg_outer_config.rs:163` and its inner twin
`plonky3_recursion_impl.rs:75`) — `OuterPcs::new(OuterDft::default(), ..)`
already constructs it via `Default` (`dregg_outer_config.rs:385`).

### Seam 2 — the MMCS (no batch seam exists; replace the tree BUILD)

`CryptographicHasher::hash_iter` (symmetric/src/hasher.rs:6) and
`PseudoCompressionFunction::compress` (symmetric/src/compression.rs) are
**per-node** calls. `MerkleTreeMmcs::commit` → `MerkleTree::new`
(merkle-tree/src/merkle_tree.rs:133,159) drives them from
`first_digest_layer` (rayon `par_chunks_exact_mut` over rows,
merkle_tree.rs:294-321, one `h.hash_iter(row)` per leaf) and
`compress_and_inject` (merkle_tree.rs:337-436, one `c.compress` per node,
re-hash-inject where shorter matrices join). There is nothing batchable at
the hasher trait: **a GPU MMCS is an alternative `Mmcs` impl whose `commit`
builds the digest layers with batched permutation kernels**, bit-exactly
reproducing: multi-matrix injection at matching heights, the sponge's
absorption layout (inner: `PaddingFreeSponge<_,16,8,8>` overwrite-mode;
outer: `MultiField32PaddingFreeSponge` **shifted radix-2^31 packing**,
`dregg_outer_config.rs:46-55`), compress (`TruncatedPermutation`; outer =
permute([l,r,0]).state[0], gold-KAT-pinned both sides,
`dregg_outer_config.rs:590-599`), and `cap_height` (0 here). `open()`/proofs
walk `ProverData` digest layers on the host, so the GPU build reads back all
layers (2^18-leaf BN254 tree ≈ 16 MB of digests — trivial on UMA).

### What stays CPU (permanently, by structure)

The FRI query phase and the `MultiField32Challenger` Fiat-Shamir transcript
are sequential and tiny; the per-query Merkle *openings* are host walks of
already-built layers. (GPU-PROVER-PROTOTYPE.md §5 item 3.)

## 2. The Amdahl breakdown — what fraction of the shrink prove is each seam

Grounding: shrink prove (real apex, blowup 8) = **~95 s** on this 12-core M2
Max (`dregg_outer_config.rs:120-126`, "~95s vs ~760s at blowup 64"); shape =
degree_bits **[9,9,15,14,15]** → LDE heights [2^12, 2^12, **2^18**, 2^17,
**2^18**] at `OUTER_FRI_LOG_BLOWUP = 3` (`dregg_outer_config.rs:127`);
5 instances + 2 non-primitive tables (HORIZONLOG.md:7713). Lineage: the wrap
went native-hash because the *emulated verifier* was ~188M R1CS of hashing
(WRAP-NATIVE-HASH-DECISION.md, "~185M R1CS" hashing term → ~5.2M native);
the same doc's red-team flagged the shrink *prover's* BN254 hash cost — that
cost is exactly seam 2.

Measured components (this repo, `gpu-dft-plonky3` bench, 2 runs):

| component | measured | implied share of ~95 s |
|---|---|---|
| BN254 MMCS commit rate (exact outer stack, rayon-12) | **0.17-0.19 Mperm/s** (5.2-6.1 µs/perm) | est. total perms ≈ 8-13M (main-trace leaves at the LDE heights above + quotient commit + FRI-phase trees + compresses; widths bracketed by the ~752-opened-cols figure, WRAP-NATIVE-HASH-DECISION.md) → **42-76 s ≈ 45-80% (central ~60%)** |
| CPU LDE, 2^15×452 → 2^18 (worst single table) | 0.23-0.28 s | all tables + quotient LDEs ≈ 0.5-1.5 s → **~1-2%** |
| remainder (constraint/quotient eval over BabyBear+EF4, FRI folds, challenger, misc) | — | **~20-50%** (by subtraction; not yet phase-profiled) |

Reading: **at blowup 8 the shrink prove is BN254-MMCS-hash-dominated.** (At
blowup 64 it was LDE-size-dominated — but both the hash and NTT terms scale
with LDE size, which is why the rebalance cut 8x; the *ratio* between them is
what the table above pins.) Two consequences, stated plainly:

1. **GPU-DFT alone moves the shrink e2e by ~1%.** It is the right FIRST
   wiring (cleanest seam, template for everything else, and it is measured
   below) — it is not the shrink's lever.
2. **The shrink's lever is the BN254 MMCS** — which needs the 256-bit-limb
   WGSL Poseidon2 (ZPrize WebGPU-MSM precedent; GPU-PROVER-PROTOTYPE.md
   §3.3) plus the tree-build integration of §1-seam-2. The BabyBear W16 tree
   kernels already measured (~300 Mhash/s, §11) serve the *inner* prover
   (apex fold, 241 s, all-BabyBear), not the shrink.

## 3. Data marshalling — unified memory, residency, and the trait's shape

- **Zero-conversion**: `BabyBear` is `repr(transparent)` over a
  Montgomery-form u32 (monty-31/src/monty_31.rs:35-42) and the kernels
  operate in Montgomery form — upload/readback are raw `&[u32]` casts.
  Measured upload+readback rides the ~354-397 GB/s copy path (§9); on Apple
  UMA there is no PCIe staging.
- **Layout**: the trait hands a row-major matrix; the tuned NTT kernels are
  column-contiguous. Increment 1 pays two tiled GPU transposes (in:
  row-major→column; out: column→row-major **with bit-reversed row order**, so
  `Evaluations` matches `Radix2DitParallel`'s free-for-the-PCS layout). The
  LDE's zero-pad is realized as the RISC0 stage-skip: the first `added_bits`
  DIT stages of a zero-padded input are pure replication, fused into one
  "expand" kernel with the iDFT finalize (index reversal + 1/h) and the coset
  `shift^j` scale — so blowup-8 costs 3 fewer stage passes, not 8x the
  butterfly work.
- **NTT→hash residency (the compounding win)**: `TwoAdicFriPcs::commit`
  pipes `coset_lde_batch` output straight into `mmcs.commit`
  (two_adic_pcs.rs:316-324). Today that hop is a host `RowMajorMatrix`. When
  the GPU MMCS lands, keep the LDE device-resident: either a residency cache
  keyed by the host allocation (GpuMmcs::commit checks whether the matrix's
  buffer is already on-device and skips the upload) or a `GpuMatrix: Matrix<BabyBear>`
  carrier type threaded through `commit_ldes` (two_adic_pcs.rs:352-354
  already separates `get_quotient_ldes` from `commit_ldes` — a natural
  seam). On UMA the penalty for NOT doing this is one memcpy each way
  (~1-3 ms per 452-MiB table) — a nice-to-have, not a gate; on discrete
  boards (hbox) it is the whole ballgame.
- **Capacity**: buffers are clamped to
  `min(max_buffer_size, max_storage_buffer_binding_size)` with transparent
  column-chunking beyond that; all measured shapes ran single-chunk on the
  M2 Max. Largest blowup-8 working set: 2 × 452 MiB work buffers + readback.

## 4. Honest per-kernel scope

| kernel | seam quality | status |
|---|---|---|
| BabyBear NTT / `coset_lde_batch` | CLEAN — pure trait impl, one type-alias swap | **BUILT + MEASURED (increment 1, below)** |
| BabyBear W16 Poseidon2 Merkle (inner MMCS) | deeper — replace tree BUILD inside an `Mmcs` impl; must reproduce injection/sponge/compress layout bit-exactly | kernels measured (§11: ~300 Mhash/s, 60-85x CPU); integration NOT started |
| BN254 t=3 Poseidon2 Merkle (outer MMCS — **the shrink's dominant term**) | deeper still — same tree build PLUS 256-bit limb arithmetic in WGSL + the shifted radix-2^31 row packing | NOT started; ZPrize precedent says writable; rate unmeasured — the next increment's first number |
| quotient/constraint eval (BabyBear+EF4 vecops) | medium — batch-stark internals, not a public trait seam | future; sized ~20-50% of the shrink with the two above done |
| FRI query phase, challenger/transcript | stays CPU (sequential, tiny) | permanent CPU |

## 5. MEASURED — increment 1: wgpu `TwoAdicSubgroupDft` behind the trait

`circuit-prove/sketches/gpu-dft-plonky3/` (standalone crate, `[workspace]`
opt-out; `cargo run --release` = parity gate + bench). Implements
`dft_batch` + `coset_lde_batch` on `GpuDft` (lazy adapter, permanent
`Radix2DitParallel` fallback below 2^12 rows or with no GPU), `Evaluations =
BitReversedMatrixView<RowMajorMatrix<BabyBear>>` — the exact
`Radix2DitParallel` type. Kernels: the §9-measured fused-tile + register-radix
plans, plus new tiled transposes and the fused expand (iDFT-finalize +
coset-scale + stage-skip zero-pad + bitrev).

**Parity gate (bit-exact vs `Radix2DitParallel`, every run): GREEN** — 8
mixed shapes (2^12-2^16, widths 3-64, added_bits 1-3, two shifts) + all four
prover-scale shapes below.

Timed expression = exactly the PCS line (two_adic_pcs.rs:316-318):
`dft.coset_lde_batch(mat, 3, GENERATOR).bit_reverse_rows().to_row_major_matrix()`.
GPU time includes upload, both transposes, expand, readback. Apple M2 Max,
12-thread rayon CPU baseline, 2 runs quoted as bands:

| shape (blowup 8) | CPU (rayon-12) | GPU (in-trait) | speedup |
|---|---|---|---|
| 2^15 × 64 → 2^18 | 47-73 ms | 7.9-11.1 ms | **4.2-9.2x** |
| 2^15 × 256 → 2^18 | 103-207 ms | 24-39 ms | **4.2-5.3x** |
| 2^15 × 452 → 2^18 (worst shrink table) | 231-278 ms | 47-54 ms | **4.2-6.0x** |
| 2^18 × 32 → 2^21 (tall stress) | 273-287 ms | 28-31 ms | **8.7-10.4x** |

**Does the kernel win survive the trait? Mostly, and honestly: yes at
4-10x, not at 38-64x.** The kernel-only NTT measured 8-14x vs the same rayon
baseline (28-47x vs 1 thread — the 38-64x headline numbers were
single-thread/scalar comparisons). Behind the trait, the surviving 4-10x
reflects real costs the kernel benchmark never paid: the iDFT half of the
LDE, two layout transposes, upload/readback of up to 452 MiB, and Rust-side
materialization. One instructive negative: a `dft_batch` benchmarked to
*natural-order host output* is ~1.0-1.3x — the host-side bit-reversal
permute dominates both backends — which is precisely why matching
`Radix2DitParallel`'s bit-reversed `Evaluations` layout (so the PCS
materializes nothing) is load-bearing, and why the pcs-shaped rows above are
the honest numbers.

## 6. Realistic end-to-end estimates (Amdahl-weighted, not promises)

- **Shrink prove (~95 s), GPU-DFT only**: ~1% — wire it for the template and
  the inner prover, not for this number.
- **Shrink prove, + GPU BN254 MMCS (the next increments)**: hash share
  45-80% (central ~60%). If the GPU tree build lands at even 10x the CPU's
  0.17-0.19 Mperm/s, e2e ≈ 1/(0.6/10 + 0.4) ≈ **2.2x**; hash-free ceiling ≈
  1/0.4 ≈ **2.5x** (range 1.8-5x across the hash-share bracket). After that
  the ~20-50% arithmetic remainder is the next wall — also BabyBear work,
  GPU-able, unscheduled.
- **Inner apex fold (241 s, all-BabyBear)**: both already-measured kernel
  classes apply (NTT 8-14x rayon; W16 Merkle 60-85x scalar-CPU). Its
  DFT/hash/eval split is unprofiled — profile before promising; plausible
  band with both seams wired: **~2-4x**, and it is the client-side prover,
  so it compounds with the strategic thesis (§7 of the prototype doc).
- Cross-check that the levers compound: blowup rebalance (DONE, 8x) →
  GPU MMCS (~2-2.5x) → GPU-DFT+eval (tail) — a credible path from 18 min
  (blowup-64 CPU) to **well under a minute** for the shrink, each step
  measured before claimed.

## 7. Next increment (named)

**The GPU MMCS tree build.** Two sub-steps, in order:

1. **BN254 t=3 WGSL permutation microprobe** (the shrink's dominant term):
   8×u32-limb Montgomery mul + the t=3/α=5/RF=8/RP=56 schedule; parity vs
   the gold KAT (`dregg_outer_config.rs:432-436`); measure Mperm/s vs the
   CPU's 0.17-0.19. This single number decides whether the shrink's ~60%
   collapses (goes like the BabyBear story) or resists (256-bit tax eats the
   parallelism).

   **MEASURED (2026-07-12, `circuit-prove/sketches/bn254-poseidon2-wgpu`,
   Apple M2 Max/Metal): it does NOT collapse — 0.85-1.09 Mperm/s**
   (wg=64 best 1.09, sustained ~0.85-1.0 under thermal droop; wg=128/256
   are ~20% slower — register pressure from the 8-limb state + 17-word
   product scratch favors small workgroups). Parity FIRST and green:
   1024 field mul/add KATs vs num-bigint, the `[0,1,2]` gold KAT
   (`bn254KATOutHex`) straight off the GPU, and 65536 permutations
   bit-exact vs the pinned p3 `Poseidon2Bn254<3>` (the exact `OuterPerm`).
   Ratio vs the 0.17-0.19 Mperm/s exact-outer-stack CPU rate: **4.5-6.4x**
   (central ~5-6x; vs the conservative 0.13 figure: 6.5-8.4x). CPU
   1-thread raw perm measured 0.06-0.09 Mperm/s alongside, consistent
   with the stack rate. Amdahl at hash ~60% of the ~95s shrink:
   **e2e ≈ 1.9-2.0x** (hash-free ceiling 2.5x) — the 256-bit Montgomery
   tax in 32-bit WGSL (16-bit-split mul32, SOS reduction, ~246 monty
   muls/perm) costs real throughput vs BabyBear's story but the GPU still
   clears the bar: **GPU-wiring the BN254 outer MMCS is worth it**;
   proceed to sub-step (2) for the outer config too, not just the inner.
2. **`GpuMmcs: Mmcs<BabyBear>`** reproducing `MerkleTree::new`'s layout
   (injection, sponge packing, compress, cap) with root-parity acceptance
   against the CPU MMCS on real LDE outputs — wired first for the inner
   BabyBear config (kernels already measured), then the BN254 outer once (1)
   measures well. Then the residency cache of §3 makes commit consume the
   GPU-resident LDE directly — the full NTT→hash GPU chain with zero copies
   on UMA.
