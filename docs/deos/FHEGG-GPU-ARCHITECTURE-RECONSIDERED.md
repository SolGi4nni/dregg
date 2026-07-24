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

### The batch-many-markets asymptote (AMD iGPU, measured)

Extending the sweep finds where the "batch many markets" lever saturates on the RADV GFX1150 iGPU
(fwd GPU/CPU): batch 256 **1.97× (peak)**, 512 1.71×, 1024 1.80×, 2048 1.71× — all bit-exact. The win PEAKS
around **batch 256** (~2×) and PLATEAUS ~1.7–1.8× beyond: past batch 256 the 48 MB+ working set exceeds the
iGPU's cache sweet spot and the kernel goes bandwidth-limited (the iGPU shares system memory). So on this
mobile part, batch ≈ 256 is the optimal operating point; a discrete GPU (more compute + dedicated VRAM
bandwidth — the 6750 XT, or F2 HBM) would peak higher and at a larger batch. The lever is real but
hardware-bounded: pick the batch to the adapter's cache, do not just crank it.

### The decisive number: the FULL multiply (the convex-engine / dark-AMM op) — measured on both

Not the NTT primitive — the actual ct-poly multiply (forward NTT + pointwise + inverse NTT) the convex engine
and dark AMM hammer. GPU/CPU, bit-exact:

| batch | Metal M2 Max | AMD iGPU (RADV GFX1150) |
|---|---|---|
| 1 | 0.88× | 0.16× (launch overhead) |
| 16 | 4.93× | 1.24× (crossover) |
| 64 | 8.97× | 2.32× |
| 256 | **9.98× (peak)** | 3.07× |
| 1024 | 8.53× | **3.35× (peak)** |
| 2048 | 8.48× | 2.58× |

**The multiply wins bigger than the NTT** (Metal ~10× vs 5.5×; iGPU 3.35× vs 2.05×) and crosses over EARLIER
(batch 4–16) because it is more arithmetic-dense (2 forward NTTs + pointwise + 1 inverse per multiply). On the
iGPU it also PEAKS LATER (batch 1024) than the NTT (batch 256) — the extra compute keeps the ALUs busy further
before the shared-memory bandwidth wall. The discrete 6750 XT (disk-blocked) sits between the iGPU and Metal
(~5–7× expected).

**This is the load-bearing conclusion:** the FOLD loses on GPU, but the MULTIPLY — the op DrEX's
convex/dark-AMM path actually spends its time on — wins **3.35× on the mobile AMD iGPU and ~10× on Metal**,
bit-exact, batch-scaling. The fold-only analysis would have shipped "GPU is marginal" while the real hot op
runs an order of magnitude faster on the silicon. That is the myopia, fully corrected with the real operation
on the real hardware.

### The dark-tier bombshell: the TFHE bootstrap core op crosses over at the DEPLOYED degree (measured)

Disk cleanup (07-24: hbox 26G→255G, persvati 12G→784G free) unblocked the `tfhe-integer` crossover. The TFHE
external product — the core op inside the blind-rotation/PBS bootstrap, the single most expensive dark-tier
operation — measured GPU vs CPU on the persvati AMD iGPU (RADV GFX1150), via the exact-RNS-NTT GPU path,
bit-exact vs CPU:

| N | CPU | GPU exact-RNS-NTT | ntt/coeff |
|---|---|---|---|
| 256 | 0.079ms | 1.189ms | CPU wins |
| 512 | 0.360ms | 1.774ms | CPU wins |
| 1024 | 0.640ms | 1.904ms | CPU wins |
| 2048 | 1.393ms | 2.250ms | ~even (0.945) |
| **4096** | **5.722ms** | **2.243ms** | **GPU wins 2.55×** |

**The crossover is at N=4096 — the DEPLOYED degree.** At the size fhEgg actually runs, the bootstrap's core op
wins **2.55×** on the mobile iGPU (the exact-RNS-NTT path; the naive coefficient-domain path wins a weaker
1.48×). Below 4096 the op is too small (launch/transfer overhead dominates), consistent with every other
kernel here. A full bootstrap runs MANY external products (the blind-rotation loop), so the batched/repeated
pattern amortizes further — like the BFV multiply that hit 3.35× batched on the same iGPU.

**Implication for the dark tier:** the oblivious-argmax crossing (bootstrap-heavy) CAN be GPU-accelerated at
the deployed size — modestly on the mobile iGPU (2.55×), more on a discrete GPU (the 6750 XT, pending) and at
batch. So "the house is blind AND the clearing is fast" is a measured possibility, not just an aspiration —
the dark-tier op the fold-only analysis would have dismissed wins at the size that matters.

### hbox RX 6750 XT (discrete, the primary target) — the full picture, and an adapter-specific kernel choice

Disk freed (07-24), rsynced, measured. Bit-exact throughout.

**Multiply (convex/dark-AMM op), 6750 XT GPU/CPU:** batch 16 1.17×, 64 2.49×, 256 4.02×, 512 4.84×, **1024
5.13× (peak)**, 2048 3.44×. Exactly the predicted ~5× — between the iGPU (3.35×) and Metal (10×). The NTT
forward peaks ~2.4×, inverse ~3.2×.

**TFHE bootstrap external-product crossover, 6750 XT, at N=4096 (deployed degree):**
`cpu=10.985ms | coefficient-gpu=3.819ms (2.88×) | exact-rns-ntt-gpu=4.786ms (2.30×)`. Below N=4096 CPU wins
(op too small). **The dark-tier bootstrap core op wins 2.88× on the discrete 6750 XT at the deployed degree.**

**The adapter-specific finding (new architectural lever):** the 6750 XT wins MORE with the COEFFICIENT-domain
path (2.88×) than the NTT path (2.30×); the persvati iGPU is the opposite — NTT wins (2.55× vs coefficient
1.48×). The discrete GPU's raw ALU throughput favors the simpler, more-parallel coefficient kernel; the
bandwidth-limited iGPU favors the NTT's fewer memory ops. **Pick the bootstrap kernel to the adapter** — the
same "size the work to the hardware" lesson as batch-to-cache.

**Dark-tier verdict, both AMD targets:** the bootstrap core op wins **2.3–2.9× at the deployed degree** (best
path per adapter), and a full bootstrap runs many external products (batchable). So the house-blind dark
clearing is measurably GPU-accelerable on the real hardware — not doomed to be slow. The fold-only analysis
would have missed the entire dark-tier acceleration story.
