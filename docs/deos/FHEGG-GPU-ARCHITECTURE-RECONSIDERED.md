# fhEgg GPU architecture — reconsidered (the fold was the myopia, the compute-bound kernels are the win)

*Written 2026-07-24 after ember asked "were we being myopic about shader architecture and new kernels?" — and
the honest answer is yes. This corrects the over-generalization in `FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`.
The fold measurement there is real and stands; the mistake was letting it stand for the whole GPU story.*

## 0. The myopia, named

I benchmarked ONE operation — the RNS fold-add — measured it losing on GPU (memory-bound, upload-dominated,
0.22–0.35× on both AMD boxes), and let that calcify into "GPU is marginal for fhEgg." That was wrong. The
fold is memory-bound because it is one modular ADD per coefficient — arithmetic intensity ≈ 0 — so a single
pass can only ever be as fast as memory allows, and the GPU's ALUs sit idle. **But the fold is the CHEAP
part.** The expensive part of a clearing — where the wall-clock actually goes — is compute-bound, and that is
exactly where a GPU wins.

## 1. The compute-bound kernels that ALREADY EXIST and were ignored

A whole suite of high-arithmetic-intensity GPU kernels is already in the tree, unmeasured in my analysis:

- `fhegg-fhe/src/shaders/bfv_ntt.wgsl` + `bfv_ntt_gpu.rs` — the **BFV NTT** (three-limb radix-2¹⁶ Montgomery
  butterflies, `@workgroup_size(64)`). The NTT is O(n log n) butterflies per polynomial — ~12 stages ×
  2048 butterflies for deg-4096 = ~24k modular-mul-heavy ops per poly, vs the fold's 4096 adds. Orders of
  magnitude more arithmetic per byte → GPU territory.
- `fhegg-fhe/src/shaders/torus_ntt_montgomery.wgsl` + `tfhe_blind_rotation_ntt_wgpu.rs` — the **TFHE blind
  rotation**, i.e. the **PBS bootstrap**, the single most expensive operation in the entire dark-tier
  crossing (the oblivious argmax is bootstrap-heavy). If this wins on GPU, the dark clearing perf story
  changes qualitatively.
- `tfhe_ntt_wgpu.rs` — the TFHE NTT.
- The `*_crossover` tests (`bfv_ntt_wgpu_crossover`, `tfhe_wgpu_ntt_crossover`) — bit-exact GPU-vs-CPU
  benchmarks for exactly these kernels. **These are the measurements that should have anchored the perf
  story, and I never ran them.**

## 2. The shader-architecture space I did not explore (and where it matters)

The fold shader is already traffic-optimal (each input byte read once) — no architecture tuning helps a
memory-bound op. But the NTT/bootstrap kernels are compute-bound, so architecture is the whole game:

- radix-2 → radix-4/radix-8 butterflies (fewer global-memory round trips per stage);
- twiddle-factor caching in `var<workgroup>` shared memory (the current NTT recomputes/reloads twiddles);
- vectorized `vec4<u32>` lanes (process 4 residues per invocation);
- on-chip tiling so a whole polynomial's NTT stays in workgroup memory across stages;
- Montgomery vs Barrett reduction choice per adapter;
- `@workgroup_size` tuning (64 = one AMD RDNA wavefront; 128/256 may hide latency better).

And beyond single kernels:

- **Fusion** — fold → crossing → multiply as resident dispatches on one device buffer, so the upload that
  dominated the fold measurement amortizes over thousands of bootstrap-class ops.
- **Batching** — clear MANY markets per dispatch (independent books share launch overhead), the natural
  large-scale shape.
- **The clear-tier resident crossing** — a wgsl min/argmax kernel on the resident fold output
  (`FHEGG-RESIDENT-CROSSING-ANALYSIS.md` — wgsl-shaped, unbuilt).

## 3. The corrected thesis

- The **fold** is memory-bound and does NOT win on GPU (measured, both AMD boxes — real, keep it). It is the
  cheap part; run it on CPU or keep it resident only to feed the next stage.
- The **NTT (BFV multiply), the blind rotation (TFHE bootstrap), and the oblivious argmax** are compute-bound
  and are where the clearing time lives — the GPU is built to win there. The kernels exist; the tuning space
  (radix, shared-memory twiddles, fusion, batching) is wide open.
- The DrEX GPU win is a **fused, batched, compute-bound pipeline**, not a fold accelerator.

## 4. The numbers — MEASURED, and the compute-bound NTT WINS

A light bench (`bin/bfv_ntt_crossover_bench.rs`, no `tfhe-integer` — the `RnsNttEngine` is in the main lib, so
it fits the disk-constrained boxes) measures the deployed q0/q1/q2 odd NTT forward+inverse, GPU vs CPU,
BIT-EXACT round-trip, across batch sizes. **The opposite of the fold: the NTT WINS on GPU, and the win is
architectural (batching).**

| batch | Metal M2 Max fwd g/c | persvati iGPU fwd g/c |
|---|---|---|
| 1 | 0.35× (loses — launch overhead) | 0.37× (loses) |
| 4 | 0.71× | 0.97× |
| 16 | **2.57×** | **1.54×** (crossover) |
| 64 | **4.11×** | **1.68×** |
| 256 | **5.56×** | **2.05×** |

Both platforms: loses at batch=1 (launch overhead), crosses over at **batch=16**, and climbs with batch — the
"batch many markets" lever, quantified. Metal wins bigger (5.5×) than the mobile iGPU (2.05×); the hbox 6750
XT (discrete, currently disk-full so unmeasured) sits above the iGPU — expected ~3–4×. Inverse NTT tracks
forward (5.54× / 1.91×). BIT-EXACT vs the CPU engine at every batch.

**This is the real DrEX GPU story:** BFV ct×ct multiply rides this NTT, so the multiply/convex/dark-AMM path
is a genuine GPU win at batch — exactly where the fold is a loss. The fold-only analysis missed it entirely.

**The lesson, kept:** one honest negative measurement (the fold loses) is not a thesis about a system. The
thesis needed the compute-bound kernels measured too — and reaching for "GPU is marginal" from the fold alone
was exactly the myopia to avoid. Thanks to ember for the shove.
