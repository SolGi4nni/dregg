# Carry-Free Additive Fold vs Exact-Integer TFHE — the Measured Tier-0 Envelope

The measurement of codex Round-3 Q1's core claim (`docs/deos/FHEGG-CODEX-ROUND3.md`
§B/Q1): the dark-pool aggregation's dominant cost — the exact-integer TFHE fold,
whose radix adds carry-propagate (PBS-class) — collapses under a **carry-free
additive scheme** (exact-quantized BFV), whose ciphertext add is a native modular
poly-add and which SIMD-packs all K buckets into one ciphertext. Companion to
`MEASURED-ENVELOPE.md` / `HBOX-24CORE-ENVELOPE.md` (the all-TFHE baseline).

**Real crypto both sides, no mock:** `tfhe-rs 1.6.3` (exact-integer TFHE) and
`fhe.rs 0.1.1` (Tancrède Lepoint — a real pure-Rust BFV/BGV, `R_q = Z_q[X]/(X^n+1)`,
SIMD-batched). Every fold on both sides is checked EXACTLY equal to the plaintext
`reference_clear`. Host: Apple Silicon, **CPU only** (no CUDA; same host caveats as
`MEASURED-ENVELOPE.md`). Reproduce: `cargo run --release --bin fhe-additive-bench`.

## Bottom line (the gate verdict)

**The Tier-0 additive-fold unlock is REAL. The fold is ~10⁵× faster and effectively
vanishes; correctness is EXACT and the quantization is mint-safe. But the end-to-end
speedup is capped by the crossing, which cannot be additive — so the honest headline
is "the fold stops being the bottleneck," not "the whole clear is now fast."**

- **Fold vs fold (the claim under test): 115,000×–228,000×.** The BFV additive fold
  is **sub-10 ms at every size** (0.0003 s at N=32, 0.0054 s at N=512); the
  exact-integer TFHE fold is **67 s–616 s** for the same books. The refuted "addition
  ≈ µs" premise of the estimates is **true again in an additive scheme** — confirmed,
  measured, not assumed.
- **The bottleneck SHIFTS, it does not disappear.** With the fold free, the two new
  costs are (a) the **TFHE crossing** — `D[p] ≥ S[p]`, ~12–17 s, O(K), N-independent
  (the thesis's predicted floor) — and (b) BFV **encrypt/packing**, 0.02–0.44 s. The
  crossing is now the floor because **there is no comparison from additive
  homomorphism alone** (codex's hard boundary): the crossing MUST stay on TFHE (or a
  scheme-switch). It is exactly the O(K) part the kernel always said was small.
- **End-to-end (BFV fold + TFHE crossing) vs all-TFHE: 4.9× (N=32) → 51× (N=512),**
  growing with N. The additive path is essentially **flat in N** (12–18 s, dominated
  by the fixed crossing) while all-TFHE grows with the fold (85 s → 640 s). This is
  the collapse-to-the-crossing the thesis predicted.
- **Correctness is EXACT, not "within Δ".** BFV is an exact-integer scheme (`Z_t`),
  so the fold has **no approximation noise** — the decrypted curves equal the
  plaintext reference bit-for-bit at every config (`MATCH=YES` everywhere, incl.
  N=512×K=256). The Δ tolerance lives in the *quantization of real-valued inputs onto
  the integer grid* (the mint-safe floor/ceil), not in the fold arithmetic.
- **Mint-safe:** the fold operates on the floor-in/ceil-out integer grid proven
  no-mint in `metatheory/Market/MintSafeQuantization.lean::mint_safe_floor_ceil`. The
  PoC runs the gate on the exact Lean instances: an honest clearing passes
  (`Σ⌈vout/Δ⌉=17 ≤ Σ⌊vin/Δ⌋=20`, `honest_clearing_passes`), a genuine mint is
  rejected (`20 ≤ 18` false, `mint_attempt_rejected`).

## The measured envelope — N × K → latency (real runs, same machine, same books)

`fold` is the aggregation under test. `additive path` = BFV enc + BFV fold + TFHE
crossing; `all-TFHE` = TFHE enc + TFHE agg + TFHE crossing. Every row correctness-
verified (`BFV=YES TFHE=YES`).

| N | K | **BFV fold** | TFHE fold (agg) | **fold speedup** | BFV enc | TFHE crossing | **additive path** | all-TFHE | **e2e speedup** |
|---|---|---|---|---|---|---|---|---|---|
| 32  | 64 | **0.0003 s** | 67.34 s  | **227,781×** | 0.023 s | 17.45 s | **17.47 s** | 85.44 s  | **4.9×** |
| 128 | 64 | **0.0013 s** | 171.23 s | **131,883×** | 0.125 s | 17.58 s | **17.71 s** | 194.19 s | **11.0×** |
| 512 | 64 | **0.0054 s** | 615.95 s | **115,126×** | 0.412 s | 12.09 s | **12.50 s** | 639.99 s | **51.2×** |
| 512 | 256 | **0.0054 s** | ~1080 s *(extrap.)* | **~200,000×** | 0.437 s | — | — | — | — |

- **The additive fold is ~K-insensitive.** BFV fold at K=256 is IDENTICAL to K=64
  (0.0054 s) because all K buckets ride in ONE packed ciphertext (SIMD, 4096 slots).
  The TFHE fold's cost is ~linear in K (K=256 would be ~1080 s, extrapolated). So the
  additive advantage **grows with K** as well as N.
- **The additive fold is O(N) carry-free adds** (510 adds at N=512 — one running sum
  each for demand/supply), vs TFHE's **O(N·K) carry-propagating adds** (32,640 at
  N=512×K=64). One packed ciphertext per order vs N·K scalar ciphertexts.
- **BFV parameters:** `fhe.rs default_parameters_128(20)`, degree-4096 set — 4096
  SIMD slots (≥ any K here), plaintext modulus t = 1,032,193 ≈ 2²⁰ (headroom over the
  largest bucket sum N·qmax = 16,384: **no wrap**), ~109-bit ciphertext modulus q
  (noise budget for millions of adds; the ≤510-add fold is deep inside it — **no
  bootstrap, no relin**), 128-bit security. Keygen 1 ms.

## Why the honest headline is nuanced (the two catches, measured)

**1. The crossing cannot be additive — it is the new floor.** codex's hard boundary
holds: sign/min/max/first-crossing are not affine, so *no additive scheme can do the
comparison*. The crossing stays on TFHE (or a scheme-switch), measured here at
**12–17 s** (O(K), N-independent — the same ~10 s class as the all-TFHE envelope's
crossing). Once the fold is free, this is what the total is made of. The additive
scheme delivers exactly what the kernel claimed — *"aggregation is the cheap part,
crossing is the small O(K) part"* — which the exact-integer measurement had inverted.

**2. The scheme-switch is a named, UN-measured seam.** To feed the BFV-folded curves
into the TFHE crossing without decrypting them (no-viewer), a real deployment needs a
**BFV→LWE/TFHE scheme-switch** (CHIMERA ePrint 2018/758, PEGASUS 2020/1606). There is
**no clean Rust implementation** of that switch (neither tfhe-rs nor fhe.rs exposes
it), so it is **not implemented here**: the PoC runs the two folds on the same book
independently, and the end-to-end number composes the *measured* BFV-fold and
*measured* TFHE-crossing phases with the switch cost excluded. Honest sizing of the
excluded cost: the switch is O(K) key-switch + coefficient-extraction + one PBS/bucket
— PBS-class, so ~K × (tens of ms) ≈ single-digit seconds at K=64, the SAME order as
the crossing itself. Even charged that, the additive path (~15–25 s) stays 25–40× under
all-TFHE at N=512, because the 67–616 s fold is gone. **This is the one real residual;
it does not overturn the unlock, it bounds it.**

## What was built (real, runs, cited)

- `src/additive.rs` — `bfv_fold`: expands each order's K-bucket unary increment,
  SIMD-packs it into one BFV ciphertext, folds N orders into the demand/supply curve
  ciphertexts by native carry-free `+=`, decrypts + checks vs `reference_clear`. Plus
  `mint_safe`: the deployable floor-in/ceil-out gate (`floor_ceil_gate`) that the Lean
  `mint_safe_floor_ceil` proves no-mint.
- `src/bin/additive_bench.rs` — the head-to-head: for each (N,K) it runs BOTH the real
  `fhe_clear` (TFHE) and `bfv_fold` (BFV) on identical books, checks both against the
  plaintext reference, and reports fold-vs-fold + end-to-end. Runs the mint-safe gate
  on the exact `MintSafeQuantization.lean` instances.

## Honest caveats (the full list)

- **CPU only, no GPU** (Apple Silicon has no CUDA). The all-TFHE fold would drop
  ~10–30× on an H100 (Zama's published figure) — but so would the crossing; the fold's
  ~10⁵× additive advantage is *algorithmic* and survives the GPU column.
- **No clean Rust CKKS** → BFV (fhe.rs) is the additive carrier. This is not a
  downgrade: BFV is the *exact-quantized* scheme codex named for the AUCTION fold
  specifically (CKKS is the approximate carrier for the T-step PDHG search). BFV being
  exact is why fold correctness is bit-exact, not within-Δ.
- **The scheme-switch cost is excluded** (see catch 2) — the single real residual.
- **Δ / precision** governs COMPLETENESS + input quantization, never soundness: the
  mint-safe gate forbids a mint at any Δ; the reserve an honest clearing must clear is
  `Δ·(n_in+n_out)` (`sufficient_surplus_passes_gate`).
- **BFV binding for the STARK is separate.** BFV computes + folds; the PQ-additive
  *commitment* binding independent orders to the accepted batch (BDLOP, the `(ct,C,Π)`
  carrier of `FHEGG-CODEX-ROUND3.md`) is a distinct piece, not built here.

## Verdict

The biggest Tier-0 lever is **real and measured**: swapping the exact-integer TFHE
fold for a carry-free additive BFV fold makes the aggregation **~10⁵× cheaper and
sub-10 ms**, exactly recovering the kernel's "aggregation is the cheap part" thesis
that the exact-integer measurement had refuted. The honest boundary: the fold is no
longer the bottleneck, the **O(K) crossing is** (~12–17 s, N-independent), the
comparison genuinely cannot be additive, and the BFV→TFHE scheme-switch that wires the
two together is a real un-measured seam (bounded at ~crossing-cost). End-to-end that is
**4.9×→51× and growing with N**, with the fold's minutes-scale cost eliminated.
