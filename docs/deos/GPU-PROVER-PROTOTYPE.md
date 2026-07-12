# Cross-Platform Prover Acceleration — strategy, feasibility, and a measured first probe

Status: PLAN + MEASURED MICROPROBE (2026-07-12). Nothing here is wired into the
prover yet. The one measured number in this doc was produced on this repo's dev
machine (Apple M2 Max, Metal via wgpu); everything else is cited or explicitly
marked unmeasured.

## 1. What we are accelerating

Two provers, two fields — this split structures the whole strategy:

| prover | field for arithmetic | field for hashing | measured cost (12-core laptop) | where it wants to run |
|---|---|---|---|---|
| INNER turn/apex fold (`ir2_leaf_wrap_config`, `ivc_turn_chain.rs:1203`) | BabyBear (31-bit) | BabyBear Poseidon2-W16 (`plonky3_recursion_impl.rs:75-89`) | apex fold ≈ 241–258 s (HORIZONLOG 2026-07-12) | CLIENT-SIDE candidate — a user's own Mac |
| OUTER shrink (`apex_shrink.rs:118` `shrink_apex_to_outer` → `prove_all_tables` at `apex_shrink.rs:226`) | BabyBear | **BN254** Poseidon2-t3 (`dregg_outer_config.rs:135-155`) | **1076 s ≈ 18 min** (HORIZONLOG.md:7725) | server-side (feeds gnark Groth16 → EVM) |

The shrink measurement context (HORIZONLOG.md:7725-7746): log_blowup 6
(blowup **64**), degree_bits `[9,9,15,14,15]` (2^15-row tables), 19 FRI
queries + 16 PoW bits (`dregg_outer_config.rs:120-124`), CPU-only Plonky3,
12 cores. The already-ranked lever list there puts **blowup rebalance first**
(config-only via `create_outer_config_with_fri`, plausibly 18 min → 1–3 min)
and GPU third. This doc is the GPU lever, planned so it *compounds* with the
rebalance instead of racing it.

### The hot loops (both provers, same three)

All three sit behind clean Plonky3 trait seams in the pinned rev `82cfad73`:

1. **LDE / NTT** — `TwoAdicFriPcs::commit` calls
   `TwoAdicSubgroupDft::coset_lde_batch` (`fri/src/two_adic_pcs.rs:317,344`;
   trait at `dft/src/traits.rs:27`, batch entry `:226`). Both configs
   instantiate it as `Radix2DitParallel<BabyBear>`
   (`dregg_outer_config.rs:156`, `plonky3_recursion_impl.rs:75`). **The NTT is
   over BabyBear in BOTH provers** — the outer config swaps only the hash
   field, not the arithmetic field. At blowup 64 the committed LDE is 64× the
   trace: the dominant term per the HORIZONLOG assessment.
2. **Merkle commit (MMCS)** — `MerkleTreeMmcs` leaf-hashes every LDE row and
   compresses levels (`merkle-tree/src/merkle_tree.rs:294,337,470`, rayon
   `par_chunks`). Inner: `PaddingFreeSponge<Poseidon2BabyBear<16>,16,8,8>`.
   Outer: `MultiField32PaddingFreeSponge<BabyBear,Bn254,_,3,2,1>`
   (`symmetric/src/sponge.rs:397`) + `TruncatedPermutation` compress — BN254
   Poseidon2 is scalar-only on CPU (no SIMD packing, noted at
   `dregg_outer_config.rs:146-147`), so per-permutation cost is ~µs-class vs
   ~tens-of-ns for BabyBear-W16.
3. **FRI fold** — per-round arity-2 folds + query openings. Vector-op scale,
   small next to (1) and (2); the query phase and the Fiat–Shamir challenger
   (`MultiField32Challenger`) are sequential and stay on CPU regardless.

### Why BabyBear-first

BabyBear elements are u32s: kernels are *simple* (32-bit Montgomery, one
register per element), portable to every GPU language, and they cover the
prover a **client** would run (turn proof, holding proof, apex fold). BN254 is
256-bit: 8×u32-limb arithmetic, painful in portability-constrained shader
languages, and it only appears in the *server-side* shrink — which has a
cheaper config-only lever queued anyway. So: **BabyBear kernels first; BN254
GPU only if, post-rebalance, the shrink is still the binding cost.**

## 2. Platform ground truth (probed 2026-07-12, this session)

| box | GPU | probe result |
|---|---|---|
| dev laptop | Apple M2 Max (Metal) | wgpu probe below ran on it |
| hbox (forge, gauntlet primary) | **AMD Radeon RX 6750 XT** (Navi 22) + Intel iGPU | `lspci` shows Navi 22; the RADV adapter string (§10) says **6750 XT** — the 18 Gbps GDDR6 bin, 432 GB/s spec (not 6700 XT/384). Measured §10. |
| persvati (forge secondary) | **AMD Radeon 880M/890M iGPU** (Strix) | `nvidia-smi` fails (CUDA userspace libs installed, no NVIDIA hw/driver) |
| NVIDIA/CUDA | none owned | cloud rental only |

**No machine we own has an NVIDIA GPU.** Any CUDA-first plan (ICICLE included)
is a plan to rent hardware. The GPUs we *do* own are AMD (hbox) and Apple
Silicon — exactly the two platforms CUDA-first ecosystems serve worst.

Caveat for hbox specifically: RX 6700/6750 XT is `gfx1031`, which is **not in
AMD's official ROCm support matrix** (the community workaround is
`HSA_OVERRIDE_GFX_VERSION=10.3.0`). A Vulkan-based path needs no ROCm at all —
a real point in wgpu's favor on hbox. **§10 confirms this empirically: the
stock Debian Vulkan loader + Mesa RADV that were already on the box ran both
probes bit-exact with zero installs.**

## 3. The options, honestly

### 3.1 ICICLE (Ingonyama) — investigated first, demoted to "one option"

What was verified this session:

- **No shipped Plonky3 backend.** [AIR-ICICLE part 1](https://hackmd.io/@Ingonyama/air-icicle)
  ([repo](https://github.com/ingonyama-zk/air-icicle)) integrates trace
  generation + symbolic constraints only; the authors state "We haven't
  currently implemented a backend prover and will do so in future work"; FRI
  marked upcoming. Wiring ICICLE under `TwoAdicSubgroupDft`/`Mmcs` is work
  *we* would do.
- **Primitives exist on CUDA**: babybear and bn254 are first-class
  ([libraries doc](https://dev.ingonyama.com/start/architecture/libraries)),
  with NTT, Poseidon2, Merkle tree, and (v3.8+) FRI Rust wrappers
  ([releases](https://github.com/ingonyama-zk/icicle/releases)).
- **Metal backend is partial and stalled for our loops**: introduced v3.6 with
  MSM/NTT/Sumcheck; "API implementations for Poseidon & Poseidon2 hashes,
  Merkle tree … are not yet included"
  ([ICICLE Goes Metal](https://medium.com/@ingonyama/icicle-goes-metal-v3-6-163fa7bbfa44)),
  and the release notes through **v4.0.0** never close that gap. So
  ICICLE-Metal cannot hash our Merkle trees on a Mac.
- **No AMD backend.** Vulkan got a build-system mention in v3.4 release notes
  and never shipped; ROCm/HIP absent. hbox is unserved.
- **Licensing**: frontend MIT, but GPU backends are "distributed under a
  special license" — free for research via Ingonyama's license server,
  production use requires a commercial arrangement
  ([repo README](https://github.com/ingonyama-zk/icicle), Metal post).
- **Rust consumption is a git dependency** (not crates.io), building the C++
  core via cmake.

Verdict: ICICLE is the right answer **only** in a "rent NVIDIA boxes for a
throughput prover service" future, and even then it carries a backend license
and a CUDA-only moat. It leaves both machines we own and the client-side
thesis unserved.

### 3.2 Futhark

One functional array-language source compiles to **CUDA, HIP, OpenCL, and
multicore CPU** backends
([usage docs](https://futhark.readthedocs.io/en/latest/usage.html),
[backend comparison](https://futhark-lang.org/blog/2024-07-17-opencl-cuda-hip.html)).
Strengths: HIP backend covers AMD (hbox) natively; NTTs are a natural fit for
an array language; the compiler autotunes; u64 exists so BabyBear Montgomery
is trivial and BN254 limb code is writable. Gaps: **no Metal backend**, and
Apple deprecated OpenCL on macOS — so no real Apple GPU story, i.e. no
client-side Mac proving. Integration is C FFI from Rust (Futhark emits a C
library). Verdict: the strongest *server-side AMD/NVIDIA* productivity option;
disqualified as the *primary* path only because Apple Silicon is a
first-class target for us.

### 3.3 wgpu + WGSL (Rust-native) — the recommendation for BabyBear

One WGSL compute-shader source runs on **Metal (Apple), Vulkan (AMD hbox +
NVIDIA), DX12, and GL** through [wgpu](https://github.com/gfx-rs/wgpu), a pure
Rust dependency — the only option that reaches Apple + AMD + NVIDIA from one
source with no C toolchain, no ROCm install, no vendor license, and (via the
same WGSL in a browser) a WebGPU path for the wasm surface later.

Honest limitations, assessed:

- **No 64-bit integers in WGSL** ([spec](https://www.w3.org/TR/WGSL/);
  [gpuweb#5152](https://github.com/gpuweb/gpuweb/issues/5152)). 32×32→64
  multiply must be emulated by 16-bit split (4 muls + carries). This taxes
  *every* field mul — and is priced into the measured number below.
- **256-bit (BN254) arithmetic in WGSL is possible but grim** — the ZPrize
  2023 [WebGPU MSM over BLS12-377](https://github.com/td-kwj-zp2023/webgpu-msm-bls12-377)
  proves 256-bit-class curve arithmetic ships in WGSL (u32-limb schoolbook +
  Montgomery), and also shows the ergonomic cost. This is why BN254 kernels
  are *not* the first target.
- **Perf ceiling below hand-tuned native**: no native mulhi, no inline PTX/AIR
  tricks, shader-compiler variance across drivers. Expectation: within a small
  factor of native Metal/CUDA for compute-bound 32-bit kernels; the gap is the
  price of one-source-three-platforms. If a measured kernel lands >2-3× off a
  native reference, the fallback ladder in §6 applies.

### 3.4 HIP (+ hipify)

One C++ source → AMD ROCm natively, NVIDIA via hipify. Peak AMD performance,
no Apple path, and on hbox specifically it inherits the gfx1031
out-of-support-matrix problem (§2). Keep as the *escalation* path for AMD
server throughput if Vulkan-via-wgpu measures poorly on hbox.

### 3.5 Raw per-platform kernels (CUDA + Metal [+ HIP])

Peak everything, three codebases. This is exactly what RISC Zero ships for the
same field family we use: their local prover runs **CUDA on NVIDIA and Metal
on Apple Silicon** ([RISC0 local proving docs](https://dev.risczero.com/api/generating-proofs/local-proving))
— BabyBear NTT + Poseidon2 on Metal is *shipped, production prior art*, which
de-risks our Apple-GPU claim independent of toolchain choice. We take this
road only kernel-by-kernel, where a measured wgpu kernel proves inadequate.

### Comparison table

| | Apple Silicon | AMD (hbox) | NVIDIA (cloud) | Rust-nativeness | BabyBear (u32) | BN254 (256-bit) | effort to first win |
|---|---|---|---|---|---|---|---|
| ICICLE | ✗ for our loops (Metal lacks Poseidon2/Merkle) | ✗ (no backend) | ✓✓ mature | FFI, git-dep, licensed backends | ✓ (CUDA only) | ✓ (CUDA only) | low *iff* NVIDIA rented |
| Futhark | ✗ (no Metal; macOS OpenCL deprecated) | ✓ (HIP) | ✓ (CUDA) | C FFI | ✓✓ trivial | ✓ writable | medium |
| **wgpu/WGSL** | **✓ (measured below)** | ✓ (Vulkan, no ROCm needed) | ✓ (Vulkan) | **pure Rust** | ✓ measured | painful (limb code) | **medium** |
| HIP | ✗ | ✓✓ (gfx1031 caveat) | ✓ (hipify) | C++ FFI | ✓ | ✓ | medium-high |
| raw CUDA+Metal | ✓✓ | (add HIP) | ✓✓ | FFI ×3 | ✓ | ✓ | highest |

## 4. MEASURED: WGSL BabyBear on Apple Silicon (this machine, this session)

Probe: `circuit-prove/sketches/wgpu-babybear-probe/` (standalone crate, not a
workspace member; also the session scratchpad original). It implements
BabyBear Montgomery multiplication in WGSL — 16-bit-split `mul64`, then
exactly the p3 monty-31 reduce (`monty-31/src/utils.rs:105`; constants
`P=0x78000001`, `MU=0x88000001` from `baby-bear/src/baby_bear.rs:18-21`) — and
checks bit-exact parity against the pinned Plonky3 rev `82cfad73` BabyBear.

Result (Apple M2 Max, wgpu 24 → Metal backend, 4,194,304 lanes × 128 chained
muls/lane):

```
adapter: Apple M2 Max (Metal)
GPU best: 5.1 ms  =  105.8 Gmul/s
CPU (1 thread, pinned p3, same chained loop): 2155 ms  =  0.25 Gmul/s
PARITY: all 4194304 lanes bit-exact vs Plonky3 BabyBear ✓
```

(Best of 5; run-to-run variance observed down to ~61 Gmul/s on a busy
machine — quote the band 60–105 Gmul/s, not the single best.)

Read this honestly:

- It **proves the recommendation's load-bearing claims**: WGSL expresses
  p3-bit-exact BabyBear Montgomery arithmetic despite no u64, and the Apple
  GPU sustains ~10^11 field-muls/s through wgpu *with* the 16-bit-split tax.
- The CPU column is the *same latency-chained loop* on one core — a fair
  like-for-like of the kernel, **not** a prover benchmark. Scaling it
  idealized-linearly to 12 cores (~3 Gmul/s) still leaves the GPU ~35× ahead
  on compute-bound field work; p3's NEON packing narrows that further on
  independent (non-chained) muls. Band, stated conservatively: **~10-35× raw
  field-arithmetic headroom on this laptop's own GPU.**
- An NTT is memory-bound with butterfly shuffles and a Poseidon2 round has
  different mul/add mix — **end-to-end prover speedup is unmeasured** and will
  be smaller than the microprobe ratio. P1/P2 below exist to measure it.

## 5. Integration surface (unchanged by toolchain choice)

Two Plonky3 trait seams, both already isolated in our configs — a backend
swap, not a prover rewrite. Sketch: `circuit-prove/sketches/gpu_dft_prototype.rs`.

1. **`TwoAdicSubgroupDft<BabyBear>`** (`dft/src/traits.rs:27`) — implement
   `dft_batch`/`coset_lde_batch` on a `GpuDft` handle; swap the one type alias
   (`dregg_outer_config.rs:156`, and its inner twin
   `plonky3_recursion_impl.rs:75`). Cleanest seam: pure math, only
   bit-reversal/coset-shift conventions to match, CPU fallback = keep
   `Radix2DitParallel` when no adapter. **First loop to GPU.**
2. **`Mmcs` (Merkle commit)** — the per-leaf `CryptographicHasher` trait
   (`symmetric/src/hasher.rs:6`) has no batch seam, so GPU hashing means a
   GPU-side tree builder behind the `Mmcs` trait that **bit-exactly
   reproduces** p3's layout: `PaddingFreeSponge` overwrite-mode absorption
   (inner) / `MultiField32PaddingFreeSponge` shifted radix-2^31 packing
   (outer, `dregg_outer_config.rs:46-55`) and `TruncatedPermutation`
   `[l,r,0]→state[0]` compress. Any deviation breaks the gnark twin — every
   kernel lands with a root-parity test against the CPU MMCS (the BN254 side
   already has the gold KAT discipline: `dregg_outer_config.rs:425-450`).
3. FRI fold vecops ride along after (1) and (2); the challenger and query
   phase stay CPU (sequential, negligible).

Memory sizing: largest shrink table LDE ≈ 2^21 rows × O(450) cols × 4 B ≈
**4 GB** (quotient columns in EF4 add 16 B/elem). Apple unified memory holds
this without any host↔device copy — a genuine Apple Silicon advantage over
PCIe-attached discrete cards, where staging this LDE is real latency. On 12 GB
(hbox RX 6700 XT) the NTT chunks per column-batch naturally; leaf hashing
streams row-chunks.

## 6. The plan (BabyBear-first, measure-gated)

- **P0 — DONE (this doc):** platform ground truth; toolchain comparison; WGSL
  BabyBear feasibility measured on Metal with p3 parity.
- **P1 — Poseidon2-BabyBear-W16 batch permutation in WGSL** (+W24), parity vs
  `default_babybear_poseidon2_16` test vectors, then a Merkle *level* builder
  reproducing `MerkleTreeMmcs` roots bit-exactly. Measure hashes/s vs the
  rayon CPU tree on: M2 Max (Metal) and hbox RX 6700 XT (Vulkan — same
  binary). This is the first number that predicts real prover minutes.
- **P2 — WGSL radix-2/4 BabyBear NTT** (forward+inverse, coset shift,
  bit-reversed output), wired behind `GpuDft`; differential-test vs
  `Radix2DitParallel` (`dft/src/testing.rs` harness); then run the **inner
  apex fold** with GPU DFT+MMCS and measure the 241 s baseline moving.
  Gate: if wgpu measures >2-3× off references (RISC0-Metal-class throughput on
  Mac; Futhark-HIP spot-check on hbox), escalate that kernel down the ladder
  wgpu → Futhark(HIP)/native Metal → raw CUDA, kernel by kernel.
  **→ The forward-NTT half of P2 is MEASURED — see §9. The gate did not fire:
  wgpu beat the RISC0-Metal reference architecture on this machine; no native
  escalation needed for the NTT.** (Remaining P2 tail: inverse/coset wiring
  behind `GpuDft` + the in-prover run.)
- **P3 — the shrink (BN254) decision, post-rebalance:** first land the
  HORIZONLOG lever #1 blowup rebalance (config-only, 18 min → est. 1–3 min,
  compounds with everything here). Only if the rebalanced shrink still binds:
  BN254 Poseidon2-t3 limb kernels (WGSL per ZPrize precedent, or Futhark/HIP
  on hbox, or ICICLE-CUDA on a rented 4090-class box — 24 GB VRAM suffices per
  §5). Until then the shrink stays a CPU/server cost, which its
  one-time-off-chain role tolerates (HORIZONLOG.md:7745).
- **P4 — client-side proving productization:** package the wgpu prover path
  (pure-Rust dep tree) so `dregg-sdk` on a user's Mac proves turns/holdings
  locally; same WGSL compiles for a future WebGPU/wasm surface.

## 7. The strategic angle (why Apple Silicon is not a nice-to-have)

Fast BabyBear proving on Apple Silicon is not a speed optimization — it is the
**client-side proving capability**: a user proves their own turn / own holding
on their own machine, and only the proof leaves it. That is the non-custodial
"prove it yourself" thesis in hardware terms. The pieces that are
client-feasible are exactly the BabyBear ones (turn proofs, holding leaves,
apex folds — u32 kernels, unified memory, no vendor GPU required); the pieces
that stay server-side are the BN254 shrink + Groth16 wrap (256-bit kernels,
SRS, one-time per publication). The wgpu choice is what makes the client-side
half *deployable*: a pure-Rust dependency an SDK can carry, running on the GPU
every Mac already has — and the same source serves hbox as the server
accelerator. One kernel suite, both halves of the thesis.

## 8. Honest verdict

- **Effort class:** backend swap at two named trait seams — *not* a prover
  rewrite — plus a kernel suite we own. Kernel suite (BabyBear NTT + Poseidon2
  + Merkle, parity-tested): weeks-scale, one lane. ICICLE would not have saved
  the seam work (no Plonky3 backend exists) and cannot serve two of our three
  platforms.
- **Fastest path to a measured prover speedup:** P1+P2 on this very laptop —
  no hardware purchase, no rental, no license. The forge (hbox) qualifies as
  the AMD/Vulkan test target with the same binary; it does **not** qualify for
  any CUDA plan.
- **Expected band:** microprobe-measured ~10-35× field-arithmetic headroom on
  M2 Max; end-to-end prover **unmeasured** (P2 produces the honest number).
  The 18-min shrink is expected to fall to low minutes via the *rebalance*
  (config-only) before GPU BN254 work is even evaluated.
- **Validated this session:** platform probes (hbox/persvati GPUs); WGSL
  BabyBear Montgomery parity + throughput on Metal; ICICLE's Plonky3/Metal/AMD
  gaps (cited). **Not validated:** any NTT/Poseidon2/Merkle GPU kernel,
  ICICLE CUDA numbers on our shapes, Futhark or HIP builds on hbox — all
  marked unmeasured above.

## 9. MEASURED: WGSL BabyBear NTT vs peak memory bandwidth (P2 probe, 2026-07-12)

Probe: `circuit-prove/sketches/wgpu-babybear-ntt/` (standalone crate, own
`[workspace]` opt-out; `cargo run --release` runs everything below). This is
the empirical answer to "does portable wgpu leave too much on the table on the
*memory-bound* kernel" — the microprobe in §4 only settled the compute-bound
one.

Method, in the order the probe enforces it:

1. **Convention lock + parity.** A host radix-2 DIT reference is checked
   against pinned p3 `Radix2DitParallel::dft` (natural-order evaluations,
   `w = two_adic_generator(logn)`), then every GPU plan below is checked
   value-exact against `dft_batch` on every shape, every run (72 parity
   checks/run, all green; data stays in Montgomery form on the GPU end-to-end,
   exactly p3's in-memory representation, so a real integration passes
   `&[BabyBear]` as `&[u32]` with zero conversion).
2. **The denominator is measured, not assumed.** A trivial copy kernel over a
   64 MiB working set measures achievable bandwidth: **354-397 GB/s across
   runs = 88-99% of the 400 GB/s M2 Max spec**
   ([Apple newsroom](https://www.apple.com/newsroom/2023/01/apple-unveils-m2-pro-and-m2-max-next-generation-chips-for-next-level-workflows/)).
   First result: *wgpu saturates Apple DRAM* — the abstraction costs nothing
   on pure streaming. (%-of-ceiling below is vs the same-run copy number; the
   dev machine is shared, so cross-run absolute times vary ~±10%, and two
   shapes small enough to sit in the M2's system-level cache show >100%
   "effective bandwidth" — flagged where it happens.)
3. **NTT plans, all parity-gated:** (a) `multipass` — bitrev pass + one global
   dispatch per stage (logn+1 memory roundtrips; this is architecturally the
   RISC0-shipped-Metal algorithm, see below); (b) shared-memory fused tiles
   (2 roundtrips); (c) 2D-tiled four-step-style passes (coalesced runs both
   directions); (d) register-tier radix-2^R (R fully-unrolled stages per
   roundtrip, no workgroup memory); (e) hybrids of (c)+(d).

### The numbers (quiet-run best per shape; effective GB/s = roundtrips x 8 B/elem / time)

| shape | best plan (passes) | time | Melem/s | eff GB/s | % of measured ceiling | vs p3 1-thread | vs p3 12-core rayon |
|---|---|---|---|---|---|---|---|
| 2^15 x 64 cols (8 MiB) | fused2d+radix hybrid (3) | **0.194 ms** | 10 833 | 260 | **73%** | 28x | 9.8x |
| 2^15 x 256 cols (32 MiB, DRAM-scale interpolate shape) | fused2d 2-pass | **0.637 ms** | 13 172 | 211 | **60%** | 33x | 8.1x |
| 2^18 x 16 (16 MiB) | hybrid (3) | 0.465 ms | 9 028 | 217 | 61% | 34x | 8.8x |
| 2^21 x 1 (8 MiB) | hybrid (4) | 0.276-0.312 ms | 6 700-7 600 | 215-243 | 61-67% | 228x | 35-44x |
| 2^21 x 8 (64 MiB, DRAM-honest LDE shape) | fused2d 3-pass / hybrid (4) | **2.32-2.54 ms** | 6 600-7 240 | 174-211 | **48-60%** | 47x | 10-14x |

CPU baseline detail (this machine, pinned p3, same natural-order output): e.g.
2^21x8: 120.5 ms single-thread, 19-35 ms full rayon (12 cores, run-dependent);
2^15x256: 21.1 ms / 5.2 ms. The GPU column is the same math, bit-exact.

Reading the efficiency column honestly: an NTT is not a copy — it must
traverse the data logn times unless stages are fused, and fusion is bounded by
the 32 KiB threadgroup memory (a *hardware* limit that binds native Metal
identically). Per-roundtrip, the probe's plain streaming stage kernel runs at
**268-292 GB/s effective = 76-81% of the measured ceiling** at DRAM scale;
whole-NTT effective bandwidth lands at **60-73% of ceiling** on every
production-relevant shape (48-60% on the single worst one). The residual gap
to ~100% is pass-count x per-pass-efficiency engineering (see "next lever"
below), not a wgpu tax.

### The two toolchain taxes found (both real, both removed via wgpu API)

These are the transferable findings — each one *looks* like "portable shader
abstractions are slow" until named:

1. **naga zero-initializes workgroup memory with thread 0 alone.** The
   WebGPU-mandated zero-init is emitted on Metal as
   `if (all(local_invocation_id == 0)) { tile = {}; }` — one lane serially
   writing the whole 16-32 KiB tile per workgroup launch. Measured: a
   **13-40x cliff** on any kernel with >8 KiB of workgroup memory
   (4 GB/s-class throughput). Fix: 
   `PipelineCompilationOptions::zero_initialize_workgroup_memory = false`
   (sound whenever every tile slot is written before read — true for all
   kernels here). Workgroup-size sweeps do NOT fix it (measured 256/512/1024
   identical) — if you hit a shared-memory cliff under wgpu/Metal, check this
   first.
2. **Default bounds checks cost ~2x on shared-memory kernels.** Switching to
   `create_shader_module_trusted(.., ShaderRuntimeChecks::unchecked())`
   (unsafe, index-audited kernels, parity still verifies every run) roughly
   halved the fused/tiled plans (e.g. 2^21x8 3-pass: 5.02 ms → 2.32 ms) and
   was worth ~15-25% even on the streaming kernels.

Also measured: 32 KiB tiles throttle occupancy (per-pass 70→106→141 GB/s for
32→16→8 KiB tiles pre-fix) — an Apple hardware property, not a wgpu one;
plans here therefore prefer 8-16 KiB tiles + register-tier radix passes.

### The native reference point (RISC0), pinned down

RISC0's shipped production Metal prover NTT
(`risc0-sys 5.0.0-rc.1: kernels/zkp/metal/ntt.metal`, driven by
`risc0-zkp/src/hal/metal.rs::batch_evaluate_ntt`) is **a separate
`multi_bit_reverse` pass plus one `multi_ntt_fwd_step` dispatch per stage** —
i.e. exactly the probe's `multipass` baseline architecture (theirs computes
twiddles by per-thread exponentiation; ours reads a table). No published
Apple-Silicon NTT throughput number was found (their benchmarks page ships a
generate-it-yourself harness only), so the honest comparison is: running that
same per-stage architecture *through wgpu* on this machine costs 11.0 ms on
2^21x8 at 76-81%-of-ceiling streaming — native-class per pass — and the
probe's fused/hybrid plans then beat the *architecture itself* by **4.3-4.7x**
(2.32-2.54 ms). Portable wgpu is not trailing the shipped native reference
here; it is ahead of it. (One genuinely useful trick in their HAL: for
blowup-expanded inputs the stage loop *starts at `1+expand_bits`* — the
zero-pad structure makes the first log2(blowup) stages trivial. At our blowup
64 that skips 6 of 21 stages of the real LDE — free extra headroom for the
`coset_lde_batch` integration, on top of everything measured here.)

### Subgroup ops

Available and requested (`Features::SUBGROUP` reported true on wgpu 24/Metal,
subgroup sizes 4..64) but **not used by the measured kernels — unmeasured
upside.** The next lever is the classic two-tier design (register radix-2^4/5
+ subgroup-shuffle exchange instead of threadgroup memory), which would cut
the 2^21 plans from 3-4 roundtrips toward 2 without the tile-occupancy cost;
WGSL has `subgroupShuffleXor` for exactly this. Estimated remaining headroom
from there: ~1.5-2x on the 64 MiB shape — and it is reachable *through wgpu*,
not a native-only capability.

### Verdict (the answer to "will wgpu hit max hardware perf?")

- On this kernel class the portable path is **not** the bottleneck: wgpu
  saturates DRAM on copy (88-99% of spec), streams butterfly passes at
  76-81% of the measured ceiling, lands whole-NTT at **60-73% of ceiling on
  the production shapes** (13.2 Gelem/s on the 2^15x256 shrink shape;
  0.64 ms), is **8-14x** the 12-core rayon p3 CPU NTT and **28-47x**
  single-thread, and **outruns the shipped native-Metal reference
  architecture by >4x** on identical hardware.
- **Recommendation: stay portable — do NOT open a native-Metal NTT seam.**
  The two big losses found were wgpu *defaults* (workgroup zero-init codegen,
  bounds checks), both already opted out in the probe and priced into the
  numbers above; the remaining gap is pass-structure engineering (subgroup
  two-tier, LDE stage-skip) that the same WGSL source can reach. A hand-tuned
  native kernel would face the same 32 KiB threadgroup memory and the same
  DRAM; its plausible edge is the ~1.5-2x that the subgroup lever also
  reaches. Revisit only if, after the `GpuDft` integration (P2 tail), the
  in-prover LDE measures far off the 60-73%-of-ceiling band established here.

## 10. MEASURED: AMD hbox — RX 6750 XT via wgpu/Vulkan/RADV (2026-07-12)

The same two probe crates (§4 mul, §9 NTT), rsynced to hbox and built there
unmodified (`~/scratch-wgpu-babybear/`, standalone `[workspace]` opt-outs; the
main breadstuffs tree on hbox untouched). First AMD GPU measurements in this
doc — everything before this section was M2 Max.

**Setup found, not installed:** hbox already had the Vulkan loader
(`libvulkan.so.1.3.290`) and the Mesa RADV ICD (`radeon_icd.x86_64.json`) —
zero packages were added. wgpu **auto-selected the real dGPU**:

```
adapter: AMD Radeon RX 6750 XT (RADV NAVI22) (Vulkan)
  max workgroup storage: 65536 B, subgroup ops available: true (sizes 32..64)
```

Not llvmpipe (the `lvp` software ICD is present but was not chosen — no
forcing needed). Hardware correction: the card is the **6750 XT** (Navi 22
refresh, 18 Gbps GDDR6, **432 GB/s** DRAM spec, 96 MB Infinity Cache), not the
6700 XT (384 GB/s) recorded from `lspci` in §2. Same die/`gfx1031`, so the
ROCm-unsupported caveat stands — and is now moot, per the verdict below.
(The probe's printed "% of 400 GB/s spec" column is the hard-coded M2
constant; the honest AMD spec fraction is computed against 432 here.)

### Montgomery-mul microprobe (compute-bound)

```
gpu runs: 169.96 / 198.01 / 195.87 / 195.88 / 191.35 Gmul/s
GPU best: 2.7 ms for 4194304 lanes x 128 chained muls = 198.01 Gmul/s
CPU (1 thread, pinned p3 rev 82cfad7): 1309.2 ms = 0.41 Gmul/s
PARITY: all 4194304 lanes bit-exact vs Plonky3 BabyBear ✓
```

**198 Gmul/s, stable (191-198 across post-warmup runs)** — **~1.9x the M2 Max
best (105.8) and ~2-3x its 60-105 band.** The 16-bit-split mul64 tax is priced
in on both. RDNA2 through RADV's shader compiler is simply a faster ALU target
for this kernel than Apple through Metal.

### Copy-bandwidth ceiling

`copy ceiling (256 MiB read+write): vec4 304.4 GB/s, u32x4 314.3 GB/s ->
ceiling 314.3 GB/s` (314-315 across the tuning runs) = **~73% of the 432 GB/s
spec**. The working set is now a 256 MiB buffer (src+dst = 512 MiB of traffic,
each thread streaming 8 u32) — well past the 96 MB Infinity Cache, so this is a
harder DRAM-honest denominator than the earlier 64 MiB copy (334 GB/s) and the
%-of-ceiling figures below are correspondingly stricter. Still less of the spec
than the M2 reaches (88-99%), typical for GDDR6 streaming vs Apple's LPDDR5
fabric.

**The Infinity Cache is loudly visible everywhere the working set fits**, and
%-of-ceiling readings above 100% below are exactly that, not measurement
error: whole cache-resident NTTs sustain 356-417 GB/s effective (106-125% of
the DRAM ceiling), and individual late radix passes peak at **904 GB/s
effective (270% of ceiling)**. On this card the NTT's logn roundtrips are
served by a 96 MB SRAM tier whenever the table is ≤~64 MiB — a structural
gift to exactly this kernel class that the M2 does not have at these sizes.

### NTT — RDNA2-tuned (300 parity checks/run, all green; `% ceil` vs the measured 314 GB/s)

The first AMD run (run 2) showed the tall shapes collapsing to 22-23% of
ceiling. The tuning run below (run 4) fixes it — see the diagnosis after the
table. Best plan per shape:

| shape | best plan (passes) | time | Melem/s | eff GB/s | % ceil | run-2 % ceil | vs p3 1-thr | vs p3 rayon |
|---|---|---|---|---|---|---|---|---|
| 2^15 x 64 (8 MiB) | hybrid E1=9 B=8 +radix[3,3] (3) | **0.140 ms** | 15 016 | 360.4 | **115%** | 106% | 154x | 32x |
| 2^15 x 256 (32 MiB) | hybrid E1=8 B=8 +radix[4,3] (3) | **0.485 ms** | 17 311 | 415.5 | **132%** | 125% | 144x | 16.4x |
| 2^18 x 16 (16 MiB) | hybrid E1=8 B=8 +radix[5,5] **+tw2m** (3) | **0.340 ms** | 12 331 | 295.9 | **94%** | 49% | 161x | 14.3x |
| 2^21 x 1 (8 MiB) | hybrid E1=8 B=8 +radix[5,4,4] **+tw2m** (4) | **0.216 ms** | 9 720 | 311.0 | **99%** | 23% | 418x | 34x |
| 2^21 x 8 (64 MiB) | hybrid E1=8 B=16 +radix[5,4,4] **+tw2m** (4) | **1.664 ms** | 10 083 | 322.7 | **103%** | 22% | 165x | 25x |
| 2^21 x 32 (256 MiB, closest to real LDE) | hybrid E1=8 B=8 +radix[4,4,5] **+tw2m** (4) | **9.151 ms** | 7 334 | 234.7 | **75%** | (n/a) | 94x | 15.3x |

The tall shapes went from **22-23% → 99-103% of ceiling** (a 2.0-2.2x wall-clock
speedup); 2^18x16 from 49% → 94%. The new 2^21x32 shape (256 MiB, spilled well
past the Infinity Cache — the honest large-LDE regime) lands at 75% of ceiling.
Wide/batch shapes are unchanged (the tune added variants, it did not disturb
the M2-class winners: the auto-tune still picks the plain `+radix` hybrid there
because the split below is not worth its extra multiply when twiddles are
already cache-hot).

### The collapse was the TWIDDLE gather, not the data-tile stride

Run 2's per-pass log showed one pass per tall-shape plan stuck at 14-37 GB/s
(4-12% of ceiling) while sibling passes in the same dispatch ran 158-900 GB/s.
The first hypothesis (large-stride *data*-array access defeating GDDR6 line
granularity) was **wrong**. The `+tw2` / `+tw2m` fix touches *only the twiddle
accessor* — every data load/store is byte-identical — and it lifts the
collapsing pass from **37 → 290-360 GB/s** (e.g. 2^21x1 pass2: 43→290 GB/s;
2^21x32 pass2: 37→325 GB/s). So the bottleneck was the twiddle-table read.

*Why:* a register-radix stage at bit offset `L` reads twiddle index
`(base + tlow) << (logn−L−stage−1)`. On a tall shape the shift is ≥12, so
adjacent lanes' twiddle indices differ by ≥2^12 — every lane in a wavefront
touches a **distinct 128 B line across the full n/2-entry (4 MiB at 2^21)
twiddle table**. That is ~32x request amplification; RDNA2's cache/channel
hardware collapses under it exactly as the log showed. The *data* reads in
those passes were already register-closed and coalesced.

*The fix (`+tw2`), bit-exact:* factor the twiddle as
`w^i = w^((i>>S)<<S) · w^(i mod 2^S)` and read it as a **Montgomery product of
two small tables** — `TW(i) = mmul(tw_hi[i>>S], tw_lo[i & (2^S−1)])`, with
`S = logn/2`. `tw_lo` is the head of the existing table (2^S ≈ 1-2 K entries),
`tw_hi` a compact appendix ((n/2)>>S ≈ 1-2 K entries). Both fit in a few KB and
stay cache-resident, so the per-lane scatter is gone. Because the mont product
of two Montgomery forms *is* the Montgomery form of the product, every one of
the 300 parity checks stays bit-exact vs Plonky3. `+tw2m` ("mixed") is the
auto-tune winner: **direct** twiddles in pass 1 (its shifts are small, so its
reads are already near-wave-uniform and the split would only add a dependent
load), **split** twiddles in the strided later passes.

### Did the 64 KB LDS (2x the M2's 32 KB) let RDNA2 pull ahead? No.

The probe sweeps 64 KB-tile plans (E1+LB = 14, e.g. `E1=11 B=8`) that cannot
fit on the M2. They **lose** on every shape: a 2^11-row strided pass-1 load is
itself non-coalesced (collapses to 49-108 GB/s) and the 64 KB tile depresses
occupancy. Every winner above uses a **small 2-4 KB coalesced tile + a
register-radix tail** — the same recipe that wins on the M2 — plus the twiddle
split. The extra LDS is not the lever here; the twiddle-gather fix is.

### AMD vs M2 Max, same binary

- **Compute-bound mul: AMD wins ~2x** (198 vs 105.8 Gmul/s).
- **Wide/batch NTT: AMD wins ~1.3x absolute** (17.3 vs 13.2 Gelem/s on
  2^15x256), riding the Infinity Cache above the DRAM roofline.
- **Tall 2^21 NTT: AMD now MATCHES or beats the M2** after the twiddle fix —
  9.7-10.1 Gelem/s at 2^21x{1,8} (was 4.6-4.9 pre-fix, i.e. the ~0.65x deficit
  is closed and inverted to a lead). The real LDE shape is 2^21 x O(450)
  *columns* (§5); the 2^21x32 measurement (75% of ceiling, IC-spilled) is the
  honest large-batch point, and the RISC0 stage-skip trick (§9) removes 6 of 21
  stages on top.
- The zero-init and bounds-check fixes from §9 carry over unchanged; subgroup
  ops are available on RADV (sizes 32..64) for the same unmeasured upside.

Probe changes for this tune (all in the standalone crate, not committed to the
hbox tree): a `TW()` twiddle accessor with direct/split/mixed modes swept as a
plan dimension; a 256 MiB working buffer + 2^21x32 shape; 64 KB-LDS plan
variants; a wider copy-ceiling kernel. Every added variant is parity-gated.

### Verdict: is wgpu/Vulkan the hbox production path?

**Yes.** The question this section existed to answer — does portable
wgpu-on-Vulkan-on-RADV saturate an AMD card well enough to skip both native
Vulkan compute and the ROCm/HIP escalation (§3.4) — comes back clearly:

- zero setup on a stock Debian box (loader + RADV were already there);
- correct adapter auto-selected, no llvmpipe trap;
- bit-exact p3 parity on every kernel, every shape, every run;
- compute-bound throughput ~2x the M2 Max;
- NTT at-or-above the DRAM roofline on batch shapes (the Infinity Cache is a
  real accelerant for this exact kernel), and the run-2 tall-shape deficit is
  **closed in WGSL** — the collapsing pass was a twiddle-table scatter, fixed
  by a bit-exact split-twiddle accessor that lifts tall shapes from 22-23% to
  99-103% of ceiling (2^21x1/x8 now beat the M2, 2^21x32 at 75%).

The HIP escalation path stays closed unless the `GpuDft` integration measures
far off this band on real LDE shapes. gfx1031's absence from the ROCm support
matrix is now irrelevant to the plan.

## 11. MEASURED: Poseidon2-BabyBear + Merkle commit — native Metal vs wgpu, M2 Max (2026-07-12)

Probe: `circuit-prove/sketches/poseidon2-merkle-bench/` (standalone crate, own
`[workspace]` opt-out; `cargo run --release` runs everything below). This was
the DECISIVE remaining measurement for the native-vs-portable question: the NTT
(§9/§10) is bandwidth-bound and came back a tie, but Poseidon2 is
**compute-bound** — 655 Montgomery muls + 1,309 modular add/subs per width-16
permutation against 128 B of I/O — and the shrink prover is **hash-dominated**
(WRAP-NATIVE-HASH-DECISION.md: ~11,000 w16 perms dominate the wrap's cost
structure; the Rust-side shrink prove is Merkle-commit-heavy the same way). The
hypothesis: the native ~3x ALU advantage on Montgomery mul (mulhi microprobe:
320 Gmul/s native vs 60-106 for the WGSL 16-bit split, §2/§4) translates into a
real ~2-3x here, which would justify a native-Metal seam for the hash side.

**It does not translate. Measured: native wins only ~1.2x on the permutation
and ~1.22-1.38x on the whole Merkle commit.**

What was measured (both backends bit-exact against pinned p3 82cfad7 before
any timing; interleaved A/B, best-of-5, two independent runs quoted as ranges):

- **The exact production permutation**: `Poseidon2BabyBear<16>` —
  x^7 S-box (`BABYBEAR_S_BOX_DEGREE = 7`, baby-bear/src/poseidon1.rs:38 — note:
  degree 7, not the x^5 sometimes assumed), RF=8, RP=13, MDSMat4 mds-light
  external layer, `1 + Diag(V)` internal layer; round constants extracted from
  the p3 arrays at runtime in Montgomery form. Both backends execute the
  IDENTICAL generated straight-line body (assignments over predeclared u32
  vars are the same source text in MSL and WGSL); only the mmul/addp prelude
  differs — native `mulhi` (4 hardware muls) vs the WGSL 16-bit-split
  emulation. Parity: the pinned KAT
  (baby-bear/src/poseidon2.rs `test_default_babybear_poseidon2_width_16`) +
  4,096 random states + 256 sixteen-chained states, bit-exact on both.
- **The exact MMCS commit pattern**: leaf = `PaddingFreeSponge<Perm,16,8,8>`,
  compress = `TruncatedPermutation<Perm,2,8,16>` — the pair the prover
  instantiates at `circuit-prove/src/plonky3_recursion_impl.rs:70-78` — built
  as a full binary tree to the root, one w16 perm per node. Roots verified
  bit-exact against the real p3 hasher/compressor at every measured size.

| measurement | native Metal | wgpu/WGSL | ratio |
|---|---|---|---|
| perm, CHAIN=1 (2^20 states, with I/O) | 2.97-3.31 ms = 317-354 Mperm/s | 3.59-4.26 ms = 246-292 Mperm/s | **1.21-1.29x** |
| perm, CHAIN=16 (ALU-bound, I/O amortized) | 246-331 Mperm/s = 161-217 Gmul-equiv/s | 206-276 Mperm/s = 135-181 Gmul-equiv/s | **1.19-1.20x** |
| Merkle 2^18 leaves (0.5M hashes) | 2.28-2.41 ms | 3.13-3.15 ms | 1.30-1.38x |
| Merkle 2^19 | 3.65-3.94 ms | 4.83-5.19 ms | 1.31-1.33x |
| Merkle 2^20 | 6.86-7.04 ms | 8.91-8.94 ms | 1.27-1.30x |
| Merkle 2^21 (4.2M hashes) | **13.8 ms** = ~304 Mhash/s | **16.9-17.2 ms** = ~244-249 Mhash/s | **1.22-1.24x** |

CPU reference (rayon over the scalar p3 perm, this machine): 2^21 tree =
1.0-1.2 s ≈ 3.5-4.2 Mhash/s — the GPU offload itself is worth **~60-85x**
over scalar-CPU hashing; the API choice within the GPU is worth ~1.25x.

### Why the 3x ALU advantage collapses (and it is NOT memory)

This is genuinely compute-bound — I/O runs at 2-45 GB/s against the ~400 GB/s
ceiling, and the tree sizes don't change the ratio much — so the NTT's excuse
(math hides behind DRAM) does not apply. Two things eat the gap instead:

1. **Instruction mix.** A permutation is 655 mmuls *plus* 1,309 modular
   add/subs (+ selects/halves), and the adds run at identical rate on both
   backends. Even a 3x mul tax is Amdahl-capped well below 2x end-to-end.
2. **The dependent-chain microprobe overstated the in-context split-mul tax.**
   In situ, wgpu sustains 135-191 Gmul-equiv/s — far above its own 60-106
   Gmul/s microprobe band — because the ~9-mul 16-bit-split DAG has internal
   ILP that a mixed instruction stream schedules well; the microprobe's
   serially-dependent chain was its worst case. Native meanwhile lands at
   161-217 Gmul-equiv/s, *below* its 320 pure-mul microprobe, diluted by the
   same add traffic. The effective in-situ mul tax is ~1.2x, not 3-5x.

### Verdict: the NTT's "stay portable" is CONFIRMED on the compute-bound kernel too

The premise "if native wins ~2-3x on the hash-dominated prover's dominant
kernel, the NTT verdict was wrong" is now settled by measurement: native's
best case on the dominant kernel is **~1.25x** (1.19-1.38x across every shape
and both runs) — the same order as this shared machine's run-to-run variance
band on the NTT (±10-15%). Whole-prover impact of a native seam, using the
hash:NTT:other split: with hashing a fraction H of GPU prove time, the seam
buys 1/(H/1.27 + (1-H)) — **1.12x at H=0.5, 1.17x at H=0.7, capped at 1.27x
even if the prove were pure hashing.** The NTT term is already a measured tie
(§10), so nothing else recovers the gap.

**Recommendation unchanged and now fully grounded: ONE portable wgpu backend,
no native-Metal seam — for both kernel classes.** The hash-dominated shrink
prover's real win is the offload itself (~300 Mhash/s ≈ a 2^21-leaf MMCS
commit in 14-17 ms, vs ~1 s on CPU); at these rates the 25 BabyBear lanes'
commit phases stop being the wall either way, and a permanent per-platform
seam is not worth ≤1.27x on one term. If a future Apple-GPU generation ships
a wider integer multiplier (or WGSL gains native mulhi — tracked upstream as
`u32`-widening proposals), re-run this probe: it is parity-gated and takes
~30 s.
