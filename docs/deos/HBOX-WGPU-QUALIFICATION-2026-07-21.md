# hbox wgpu qualification — 2026-07-21

This is the measured dispatch record for the existing exact BFV additive-fold
path on `hbox`. It is deliberately narrower than “GPU acceleration works”:
each row names the workload whose transfer and residency shape was actually
measured.

## Qualified host and backend

- Host: Intel i9-12900, 24 hardware threads, 123 GiB RAM.
- Adapter: AMD Radeon RX 6750 XT, 12 GiB.
- Compute API used by dregg: **wgpu over Vulkan**.
- This is not a CUDA, HIP, or ROCm qualification. Those toolchains were not
  present in the host probe and the BFV fold shader does not use them.
- One exact `degree=4096`, three-`FOLD_MODULI`, two-polynomial ciphertext is
  196,608 bytes. The adapter reported a 2,147,483,647-byte effective resident
  storage-binding ceiling, or 10,922 such ciphertexts per bounded chunk.

`fhegg-fhe::gpu_qualification` exposes the selected adapter, relevant limits,
actual backend, resident plan/capacity, and named CPU fallback reason as
serializable data. `gpu_fold_qualify` produces a machine-readable per-host
CPU-versus-wgpu report. A visible adapter is not evidence of execution: only an
actual `GpuResident` result is labelled GPU. The rows below come from green
arena benchmarks. The new machine-readable harness is also green and its exact
output is frozen at
[`artifacts/hbox-bfv-wgpu-qualification-2026-07-21.json`](artifacts/hbox-bfv-wgpu-qualification-2026-07-21.json).
Its SHA-256 is
`ff58718c1fa8ae295bd76d426816d15192f545ab0e61a8231907b6871fe741b1`.

Focused diagnostics gate: **3/3 passed**. The bounded real-adapter sweep used
`N=1,2,4,8,16,32,64,128,256`, three repetitions, a 5% win margin, and
`FHEGG_GPU_QUALIFY_REQUIRE_GPU=1`. All nine samples were bit-exact, dispatch was
stably `GpuResident`, the adapter was the RX 6750 XT over Vulkan, and no
one-shot crossover was observed. CPU/GPU median times ranged from
5.143/234.624 microseconds at `N=1` to 4.070/9.794 milliseconds at `N=256`.

Commands:

```sh
scripts/hbuild gpu-e2e cargo nextest run --release \
  -p fhegg-fhe --test gpu_qualification_diagnostics --no-capture

scripts/hbuild gpu-e2e env \
  FHEGG_GPU_QUALIFY_NS=1,2,4,8,16,32,64,128,256 \
  FHEGG_GPU_QUALIFY_REPS=3 \
  FHEGG_GPU_QUALIFY_MARGIN_BPS=500 \
  FHEGG_GPU_QUALIFY_REQUIRE_GPU=1 \
  cargo run --release --quiet -p fhegg-fhe --bin gpu_fold_qualify
```

## Result 1: a complete one-fold call is transfer-bound

This production-shaped measurement folds demand and supply groups. “GPU
separate” performs two resident folds with separate waits/readbacks; “GPU one
read” uses the paired path and downloads both outputs after one wait. Each cell
is best-of-three in release mode; `N` is ciphertexts per side and input MB is
the two sides together.

| N / side | Input MB | CPU pair | GPU separate | GPU one read | one-read / CPU |
|---:|---:|---:|---:|---:|---:|
| 1 | 0.4 | 0.01 ms | 0.49 ms | 0.38 ms | 32.53× slower |
| 2 | 0.8 | 0.07 ms | 0.56 ms | 0.56 ms | 7.89× slower |
| 4 | 1.6 | 0.14 ms | 0.68 ms | 0.66 ms | 4.87× slower |
| 8 | 3.1 | 0.20 ms | 0.76 ms | 0.62 ms | 3.15× slower |
| 16 | 6.3 | 0.40 ms | 1.14 ms | 1.10 ms | 2.74× slower |
| 64 | 25.2 | 1.80 ms | 4.51 ms | 4.66 ms | 2.59× slower |
| 256 | 100.7 | 8.30 ms | 19.55 ms | 18.69 ms | 2.25× slower |
| 1,024 | 402.7 | 34.12 ms | 114.20 ms | 108.36 ms | 3.18× slower |

Command:

```sh
scripts/hbuild gpu-e2e env \
  DREGG_REQUIRE_WGPU=1 \
  ARENA_PAIR_MAX_N=1024 \
  ARENA_PAIR_REPS=3 \
  cargo nextest run --release -p fhegg-fhe --lib \
  -E 'test(bench_paired_readback_crossover)' \
  --run-ignored only --no-capture
```

Consequence: the measured range does **not** establish a one-shot GPU
crossover. Do not install an automatic small-batch GPU threshold from these
numbers. The paired path saves a wait/readback and is worth retaining, but it
does not erase upload cost.

## Result 2: persistent residency wins

The same arithmetic changes character when one uploaded pattern is folded
eight times before the single final download. Every row was bit-exact against
the CPU result.

| N | Input MB | CPU, 8 folds | one-shot GPU ×8 | resident end-to-end | resident speedup |
|---:|---:|---:|---:|---:|---:|
| 1,024 | 201 | 137.1 ms | 998.0 ms | 51.0 ms | 2.69× |
| 4,096 | 805 | 548.0 ms | 3,759.8 ms | 193.3 ms | 2.83× |
| 8,192 | 1,611 | 1,079.8 ms | 7,528.9 ms | 565.9 ms | 1.91× |

Command:

```sh
scripts/hbuild gpu-e2e env \
  DREGG_REQUIRE_WGPU=1 \
  ARENA_K=8 \
  cargo nextest run --release -p fhegg-fhe --lib \
  -E 'test(bench_residency_thesis_upload_once_fold_k_times)' \
  --run-ignored only --no-capture
```

Consequence: the supported optimization is not “send every fold to the GPU.”
It is “keep multi-stage/repeated work resident.” A future automatic dispatcher
must key on at least batch shape and expected reuse count, and it must preserve
the CPU path for transfer-dominated calls.

## Build-host policy

`scripts/hbuild` reuses the isolated-lane `pbuild` protocol with `hbox` as the
host. It additionally requires the remote `swarm-build` resource wrapper and a
20 GiB free-space floor before it creates or synchronizes a lane. This makes
`hbox` the qualified primary host for the wgpu/FHE/prover work that needs its
RX 6750 XT or larger RAM.

The CPU-only choice between hbox and persvati remains an A/B measurement, not a
project invariant. Both expose 24 hardware threads, but topology, clocks,
cache warmth, and the exact crate dominate broad model-name comparisons.
