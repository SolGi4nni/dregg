# fhEgg GPU — real AMD numbers (hbox 6750 XT + persvati iGPU), 2026-07-24

*Measured on the actual target hardware (not Metal). Built from my current tree rsynced to each box
(`~/fhegg-bench-mac`, isolated from codex's working tree), `cargo run --release -p fhegg-fhe --bin
gpu_resident_bench`. The bench is BIT-EXACT vs the deployed CPU `bfv_lean::fold` at every N. K=8 folds/pattern;
ciphertext = 196608 B (deg-4096 × 3 RNS × 2 polys).*

## The residency thesis holds on AMD — but modestly (~2.7×), and it is UPLOAD-BOUND

| box | adapter | N | resident e2e | CPU K-folds | **res/CPU** | one-shot | upload share |
|---|---|---|---|---|---|---|---|
| hbox | RX 6750 XT (discrete) | 1000 | 47.3ms | 126.4ms | **2.67×** | 935ms (0.14×, LOSES) | 34/47ms = 72% |
| hbox | RX 6750 XT | 4096 | 185ms | 504ms | **2.72×** | 3529ms (LOSES) | 137/185ms = 74% |
| hbox | RX 6750 XT | 8192 | 374ms | 990ms | **2.65×** | 6888ms (LOSES) | 282/374ms = 75% |
| persvati | RADV GFX1150 (iGPU) | 1000 | 52.1ms | 148.8ms | **2.86×** | 812ms (LOSES) | — |
| persvati | RADV GFX1150 | 4096 | 223.8ms | 608ms | **2.72×** | 3365ms (LOSES) | — |
| persvati | RADV GFX1150 | 8192 | 532.5ms | 1208ms | **2.27×** | 7695ms (LOSES) | — |

## Honest reading (vs the Metal M2 47–73×)

- The one-shot fold LOSES ~6–7× on both AMD boxes (transfer-bound, as on Metal). Only the RESIDENT pattern
  (upload once, fold K times on-device, download once) wins — confirmed on real AMD, bit-exact.
- The AMD resident win (~2.7×) is far below Metal's 47–73× for TWO reasons, both honest: (1) the hbox/persvati
  CPU baselines are much faster than the M2's single-threaded fold, so the ratio is smaller; (2) on discrete
  AMD, **upload is ~72–75% of resident wall-clock** — the PCIe transfer of 197MB–1.6GB dominates. The iGPU
  (shared memory) does about the same net (cheaper upload, slower compute).
- **The two performance levers, named:**
  1. **Chunked arena** (the named `GpuResidentArenaChunking` residual): the 2GB buffer caps resident N at
     10922 cts, so the large-N histogram regime (measured 11.4× at N=1M on the 6750 XT earlier this session)
     is UNREACHABLE in one buffer. Chunking unlocks it — the biggest win.
  2. **Full-pipeline residency / higher K:** at K=8 upload is ~72%; the real DrEX clearing does
     fold→crossing→convex→multiply (many more resident ops), so the amortization improves sharply with more
     on-device work per upload. The 2.7× at K=8 is a floor, not the ceiling.

## What this means for DrEX perf

The resident GPU fold is a real, bit-exact win on the deployed AMD hardware — modest at K=8, and the clear
next stones (chunked arena for large-N; keeping the whole clearing pipeline resident) are exactly where the
larger wins live. The one-shot fold should NEVER be used (it loses); DrEX must drive the resident arena.

---

## UPDATE — the streaming single-clear LOSES (measured hbox 6750 XT): the fold is NOT the GPU win

Extended the bench to drive the production chunked path (`FoldEngine::fold` / `fold_streaming`) at large N —
a SINGLE aggregation of N orders (the real DrEX fold hot path), GPU vs CPU, BIT-EXACT. Result on the 6750 XT:

| N | ciphertext data | CPU fold | GPU stream | gpu/cpu | plan |
|---|---|---|---|---|---|
| 16384 | 3.0 GB | 259.8ms | 779.6ms | **0.33× (LOSES)** | 2 chunks, 1 reduction |
| 32768 | 6.0 GB | 521.5ms | 2120ms | **0.25×** | 4 chunks |
| 65536 | 12 GB | 1037ms | 4368ms | **0.24×** | 7 chunks |
| 100000 | 18.75 GB | 1552ms | 6947ms | **0.22×** | 10 chunks |

(500k/1M not run: N ciphertexts at 196 KB each is 93 GB / 187 GB of host RAM — a real host-memory ceiling, an
honest bench limit, not a GPU result.)

**The decisive correction to the perf story:** chunking is correct and works (GpuResident, exact plan), but a
SINGLE fold of N orders is one upload-bound streaming pass with NO reuse — and the single-threaded CPU fold is
a fast memory-streaming add with no PCIe transfer. So **the fold, done once, loses on the GPU at every size.**
The GPU win requires one of:
1. **REUSE** — keep the uploaded ciphertexts resident and do MANY ops on them (the K=8 resident bench wins
   2.65-2.72× precisely because it amortizes one upload over 8 folds);
2. **COMPUTE-BOUND ops** — the crossing/argmax HISTOGRAM won 11.4× at N=1M earlier this session; ct×ct
   multiply (NTT-bound) is the other. These are arithmetic-intensity-high, not memory-streaming.

**Implication for DrEX:** do NOT GPU-accelerate the fold in isolation — the CPU fold is fine and often faster.
The GPU pays only for the WHOLE resident clearing pipeline (upload once → fold → crossing/argmax → convex →
multiply, all on-device, then one download), where the many compute-bound ops amortize the upload. The
`DREX-GPU-RESIDENCY-PLAN.md` residency plan is therefore the real lever; a fold-only GPU path is a
de-optimization. Honest, measured, and it saves us from shipping a slower "GPU fold."

### persvati iGPU CONFIRMS: the streaming fold loses on BOTH AMD boxes

Same streaming single-clear on the RADV GFX1150 iGPU — the fold-loses finding is robust, not a discrete-PCIe
artifact:

| N | CPU fold | GPU stream | gpu/cpu |
|---|---|---|---|
| 16384 | 302.1ms | 893.9ms | **0.34×** |
| 32768 | 612.3ms | 1770.9ms | **0.35×** |
| 65536 | 1207.6ms | 3508.2ms | **0.34×** |
| 100000 | 1881.8ms | 5479.8ms | **0.34×** |

The iGPU loss is FLATTER (~0.34× everywhere) than the discrete 6750 XT (0.22–0.33×): shared memory makes the
"upload" cheaper but the compute slower, so the ratio is size-independent. Either way — **a single fold of N
orders loses on both AMD GPUs.** The measured conclusion stands on both targets: the fold is not the GPU win;
resident reuse + compute-bound ops (histogram/NTT/multiply) are.
