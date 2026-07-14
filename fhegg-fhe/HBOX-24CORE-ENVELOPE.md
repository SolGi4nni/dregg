# NO-VIEWER FHE Clearing — the 24-core desktop-class CPU envelope (hbox)

Companion re-measurement to `MEASURED-ENVELOPE.md` (the M2 Max / 12-core run).
Same crate, same real `tfhe-rs` (v1.6, exact-integer TFHE), same N/K grid, same
correctness check vs the plaintext reference. Re-run on **hbox — a 24-core
x86_64 desktop-class CPU, NO CUDA GPU** (`nvidia-smi` absent) — to get an honest
desktop-class CPU data-point and the real multi-core scaling, and to answer:
*does doubling the cores (12 → 24) buy the ~2× the intuition expects?*

**Answer: no. The 24-core CPU buys ~1.0–1.2× at tested sizes (≈1.6× extrapolated
at the largest), NOT ~2×.** This is an honest data-point, not a fix. The real
Tier-0 levers are elsewhere (algorithmic + cloud-GPU); see the last section.

The run was `nice -n 19` (low priority) alongside the box's live private
dregg-node + dreggcloud services, which stayed healthy throughout (node minted
blocks continuously, `consensus_live:true`, all service procs alive).

## Host + params

- **hbox: 24-core x86_64, Ubuntu 6.11, CPU only. No CUDA GPU** — so, exactly as
  on the M2, there is **no GPU number from this host**; the `gpu` tfhe-rs feature
  is NVIDIA/CUDA-only. This is the **24-core CPU** number.
- `tfhe-rs` **1.6**, high-level API, default params (`PARAM_MESSAGE_2_CARRY_2`,
  ≥128-bit, IND-CPA-D). `FheUint16` = 8 radix blocks. Release build (`lto=thin`,
  `opt-level=3`), built on hbox in **2m02s**.
- Correctness: **every config that runs is checked exactly equal** to the
  plaintext `reference_clear` (`p*`, `V*` match). All rows below: `MATCH=YES`.

## The measured envelope — N × K → latency (real runs, 24-core CPU) vs M2 (12-core)

Every non-extrapolated row is a real FHE clear, correctness-verified. `total
clear` = aggregate + crossing + decrypt (the homomorphic server work); `encrypt`
is the traders' one-time submit cost, listed separately. The last row exceeds
the 900 s per-config run budget on both hosts, so it is extrapolated from
measured per-op costs (labelled), on both.

| N | K | encrypt | aggregate | crossing | **hbox total** | M2 total | **24c/12c speedup** | correct |
|---|---|---|---|---|---|---|---|---|
| 32 | 64 | 0.81 s | 37.9 s | 10.4 s | **48.4 s** | 46.4 s | **0.96×** | ✅ p*=18 V*=383 |
| 32 | 256 | 3.11 s | 157.1 s | 41.9 s | **199.0 s** | 196.3 s | **0.99×** | ✅ p*=123 V*=490 |
| 128 | 64 | 2.65 s | 110.0 s | 10.6 s | **120.6 s** | 131.6 s | **1.09×** | ✅ p*=36 V*=2011 |
| 128 | 256 | 12.4 s | 439.8 s | 42.2 s | **482.1 s** | 563.7 s | **1.17×** | ✅ p*=138 V*=1473 |
| 512 | 64 | 10.6 s | 393.5 s | 10.6 s | **404.1 s** | 488.5 s | **1.21×** | ✅ p*=32 V*=1995 |
| 512 | 256 | ~54 s | ~1083 s | ~36 s | **~1119 s (~18.7 min)** | ~1830 s (~30 min) | **~1.64×** | *extrapolated* |

**Reading it: the speedup is ~1.0× at small N and climbs with N** (0.96× → 1.21×
across the real runs, ~1.6× extrapolated at N=512/K=256). At N=32 the 24-core
box is even a hair *slower* than the M2 — its per-core is not faster, and the
workload gives the extra cores nothing to do (see below). The desktop-class
verdict is the same shape as the M2 one: **minutes-to-tens-of-minutes batch, not
seconds** — 24 cores do not change the cadence class.

## Why not ~2× — the two structural ceilings (this is the real finding)

**1. Single radix ops don't parallelize past ~8 threads.** A `FheUint16` is 8
radix blocks; a single `ge`/`add`/`select` has only ~8 blocks of internal
parallelism, so it saturates early. Measured per-op is essentially **identical
to the M2** — the extra 12 cores are idle for a single op:

| op (`FheUint16`, CPU) | M2 (12c) | hbox (24c) |
|---|---|---|
| encrypt | 0.34 ms | 0.42 ms |
| decrypt | 0.006 ms | 0.007 ms |
| `ge` (compare) | 66.9 ms | 65.9 ms |
| `select` (if_then_else) | 74.4 ms | 74.2 ms |
| sequential add (carry-propagating `+`) | 70.7 ms | 77.9 ms |

The **crossing** phase is a sequential loop of one `ge`+`select` per bucket, so
it is single-op-latency-bound and shows **~0×** benefit from the extra cores:
~10.5 s at K=64 and ~42 s at K=256 on *both* hosts, at every N.

**2. The aggregation gives the cores work only when a bucket is large.** The
clear sums each price bucket with `FheUint16::sum` (a deferred-carry parallel
tree-reduction), but the K buckets are summed in a **sequential loop**, and each
bucket sum is over only **N/2** ciphertexts. So the parallelism available to the
24 cores scales with the *bucket size* N/2, not with the abundant K buckets:

- N=32 → 16-element bucket sums → tree depth 4 → the 24 cores are mostly idle →
  **no speedup** (rows 1–2).
- N=512 → 256-element bucket sums → real parallelism → **the speedup shows up**
  (rows 5–6).

## Multi-core scaling of the aggregation primitive (measured, `RAYON_NUM_THREADS`)

Isolated probe: best-of-2 `sum` of 512 ciphertexts (one big aggregation bucket)
and single-`ge` latency, at fixed thread counts. This is the primitive whose
parallelism the whole envelope rides on.

| threads | `sum`-512 (one bucket) | speedup | ms / input-add | single `ge` latency | `ge` speedup |
|---|---|---|---|---|---|
| 1 | 41.6 s | 1.00× | 81.3 ms | 187 ms | 1.00× |
| 2 | 21.5 s | 1.94× | 41.9 ms | 104 ms | 1.80× |
| 4 | 11.9 s | 3.51× | 23.2 ms | 74.7 ms | 2.50× |
| 8 | 7.78 s | 5.35× | 15.2 ms | 60.6 ms | 3.09× |
| 12 | 6.92 s | 6.01× | 13.5 ms | 65.6 ms | 2.85× |
| 24 | 6.13 s | **6.79×** | 12.0 ms | 67.1 ms | **2.79×** |

- **The parallel tree-sum scales to ~6.8× at 24 threads** — but with strong
  diminishing returns: **~5.4× is already reached at 8 threads**, and 8 → 24
  adds only ~1.3× more (Amdahl: the tree's upper levels and the final carry
  settle are serial). This is genuine multi-core scaling — and it is *exactly why
  N must be large for it to help the clear*, since only then is a bucket sum big
  enough to feed all the threads.
- **Single-op latency saturates by 8 threads at ~3×** and then flat/slightly
  worse (24-thread `ge` ≈ 8-thread `ge`). The crossing lives here → no core win.

Net: the 12→24 core doubling lands **well short of 2×** on this workload because
(a) the crossing and single ops are already core-saturated at ≤8 threads, and (b)
the aggregation only fills the cores at high N. The ~1.6× we do get at the
largest size is the aggregation tree-sum finally having enough elements.

## Honest framing — hbox is a data-point, not the solution

- **This is the 24-core *CPU* number, ~1.0–1.6× the M2. It is NOT a GPU number**
  — hbox has no CUDA GPU. Do not read this as "a bigger desktop solves it."
- **The real Tier-0 levers (both bigger than cores):**
  1. **The algorithmic fix — a quantized-approximate / CKKS-lattice *additive*
     scheme for the aggregation (carry-free adds).** The wall here is that an
     exact-integer TFHE add **carry-propagates (PBS-class, ~13 ms/element even in
     the deferred-carry tree-sum, ~10⁴× the "µs" the estimates assumed)**. An
     additive scheme makes the aggregation genuinely µs-cheap and SIMD-packs
     across buckets — a far larger win than any core count. (Being designed in the
     codex round-3 lane.)
  2. **A cloud NVIDIA GPU (H100), ember-gated.** Zama's published CPU→H100 is
     ~10–30× (PBS ~50 ms CPU-class → <1 ms on 8×H100). That is the GPU dream —
     and it is a **cloud** GPU, **not our desktop** (we don't have one; hbox's
     `nvidia-smi` is absent).
- What stays true regardless of host: the clear is **real, correct, and
  no-viewer** (orders never decrypted, only `p*`/`V*` open); privacy is
  unconditional; and the two thesis calls hold — **the crossing is O(K),
  N-independent** (confirmed: ~10.5 s @K=64, ~42 s @K=256 on both hosts), and
  **exact-integer aggregation dominates** because its adds are ms not µs.

## Reproduce (on hbox scratch)

```
rsync -az --exclude target/ fhegg-fhe/ hbox:scratch/fhegg-fhe/
ssh hbox 'cd ~/scratch/fhegg-fhe && nice -n 19 cargo build --release --bins'
ssh hbox 'cd ~/scratch/fhegg-fhe && nice -n 19 ./target/release/fhe-clearing-bench'
# scaling probe (src/bin/scaling.rs — sum-512 + single-ge across thread counts):
ssh hbox 'cd ~/scratch/fhegg-fhe && for t in 1 2 4 8 12 24; do RAYON_NUM_THREADS=$t nice -n 19 ./target/release/scaling; done'
```
