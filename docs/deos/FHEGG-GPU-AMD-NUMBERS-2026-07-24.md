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
