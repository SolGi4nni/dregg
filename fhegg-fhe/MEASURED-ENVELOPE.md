# NO-VIEWER FHE Clearing — the Measured Envelope (honest numbers)

Stage-2 companion to the ESTIMATES in `docs/deos/DREX-NO-VIEWER-SURPASS.md`,
`docs/deos/FHEGG-KERNEL.md`, `docs/deos/PRIVATE-CONVEX-ENGINE.md`. This crate
(`fhegg-fhe/`) builds a **real** no-viewer FHE uniform-price clear with
**tfhe-rs** (Zama TFHE, exact integers) — nobody ever decrypts an order, only
the public clearing price `p*` and aggregate volume `V*` — and **measures** it.
No mock FHE, no faked benchmark. Where a number is extrapolated it is labelled
and grounded in a measured per-op cost.

## Bottom line (the gate verdict)

**Does no-viewer FHE clearing genuinely perform at useful sizes? YES it works
and is CORRECT; NO it is not fast on exact-integer TFHE CPU — it is a
minutes-cadence batch, not a seconds one.**

- The no-viewer clear is **real and correctness-verified** for N ∈ {32,128,512},
  K ∈ {64,256}: the FHE `p*`/`V*` equal the plaintext reference at every size.
  Nobody decrypts an order — only `p*` and `V*` open. Privacy is unconditional.
- **Measured latency (CPU M2 Max, exact-integer tfhe-rs 1.6.3):** N=32–128 at
  K=64 clears in **~1–2 min**; N=512 or K=256 is **8–9 min**; N=512×K=256 is
  **~30 min** (extrapolated). This is **minutes-to-tens-of-minutes**, slower than
  the estimates' "tens of seconds" — which assumed **approximate CKKS** and/or
  **GPU**, not exact-integer TFHE on CPU (`DREX-NO-VIEWER-SURPASS.md §2.3`
  flagged exactly this).
- **Thesis audit (confirmed / refuted by real numbers):**
  - ✅ **crossing is O(K), N-independent** — confirmed exactly (~10 s at K=64 for
    all N; ~42 s at K=256).
  - ✅ **prox = ~2–3 PBS/pack per PDHG iteration** — confirmed (2.0 PBS-equiv/edge
    for a public box cap).
  - ❌ **"aggregation/matvec is bootstrap-free / the cheap part"** — REFUTED for
    exact-integer tfhe-rs: a radix add **carry-propagates (PBS-class, ~13–70 ms),
    not µs**, so the aggregation DOMINATES the clear (up to 45× the crossing) and
    the PDHG matvec is the LARGER half of the iteration. The "µs additions" hold
    only in an **additive scheme** (Pedersen/ElGamal/CKKS), which is the lever to
    recover the estimate's envelope (that + GPU + coarse K + per-pair sharding).
- **Separate residual (not built here):** tfhe-rs gives the compute and is
  itself lattice/PQ, but the **PQ-additive commitment binding for the STARK**
  (`PQ-SHIELDED-COMMITMENT.md`) is a distinct piece.

## What was built (real, runs)

- `src/lib.rs` — the NO-VIEWER clear. Each order is a **unary price-bucket
  increment vector** (`order_increment`): a bid of limit `L` puts its qty on
  buckets `0..=L`, an ask on `L..K`. The trader expands + encrypts this
  locally, so the limit `L` stays SECRET — the server only ever sums
  ciphertexts. The clear is:
  - **(a) aggregation** — `D[p]=Σ_bids row[p]`, `S[p]=Σ_asks row[p]` via
    `FheUint16::sum` (tfhe-rs `unchecked_sum_ciphertexts_vec_parallelized`: a
    parallel tree-reduction with **deferred carry propagation** — the additive
    primitive, not the per-add carry-propagating `+`);
  - **(b) crossing** — `c[p] = [D[p] >= S[p]]` (one homomorphic `ge` + select
    per bucket), then `p* = (Σ_p c[p]) - 1` (a cheap sum of bits). `D`
    non-increasing, `S` non-decreasing ⇒ `c` is a single downward step, so the
    crossing is O(K) comparisons, **independent of N**.
  - **(c) threshold-decrypt only the result** — decrypt `count → p*` and the
    two aggregates at the (now public) index `p*` to get `V*=min(D,S)`. The
    orders, the per-order increments, and the rest of the curve stay sealed. In
    production the final decrypt is a threshold-FHE committee decrypt of `p*`.
- `src/bin/bench.rs` — the sweep + correctness check vs a plaintext reference.
- `src/bin/pdhg.rs` — one PDHG (Chambolle–Pock) circulation flow-LP iteration
  under FHE, matvec (public `A`) vs box-prox split, per-iteration cost + T-step.
- `src/bin/smoke.rs` — minimal tfhe-rs liveness check.

Correctness: the FHE `p*`/`V*` are checked **exactly equal** to the plaintext
`reference_clear` at every config that runs.

## Host + params (honest about the hardware)

- **Apple M2 Max, 12 cores, CPU only.** Apple Silicon has **no CUDA**, and
  tfhe-rs's `gpu` feature is **NVIDIA/CUDA-only** — so there is **no GPU number
  from this host**. Zama's published CPU→H100 speedup is ~10–30× (PBS drops
  from ~50 ms CPU-class to <1 ms on 8×H100); apply that to read the GPU column.
- tfhe-rs **1.6.3**, high-level API, default params
  (`PARAM_MESSAGE_2_CARRY_2`, ≥128-bit, IND-CPA-D). `FheUint16` = 8 radix
  blocks (2 message bits each).

## Measured per-operation cost (the load-bearing finding)

| op (`FheUint16`, CPU M2 Max) | measured |
|---|---|
| encrypt | **0.34 ms** |
| decrypt | **0.006 ms** |
| `ge` (compare) | **66.9 ms** |
| `if_then_else` (select) | **74.4 ms** |
| sequential add `a + b` (carry-propagating) | **70.7 ms** |
| **`sum` of 512 cts** (deferred-carry parallel tree-sum) | **7.00 s → 13.7 ms per input-add** |

**The single biggest honest correction to the estimates:** the docs say
"ciphertext addition ≈ **µs**, no bootstrap — the cheap primitive." That is
true for an **additive scheme** (Pedersen / exponential-ElGamal / CKKS-packed),
which is what Penumbra and the FHEGG-KERNEL algebra actually use. It is **NOT
true for tfhe-rs exact-integer TFHE**: a multi-block radix add must **propagate
carries**, and carry propagation is **PBS-class**. So a single carry-propagating
`FheUint16` add is **70.7 ms**, ~the same as a comparison. Even the *right*
aggregation primitive — the deferred-carry parallel tree-sum — is **13.7 ms per
input element**, i.e. **~10⁴× the "µs" the estimate assumed**. Aggregation in
tfhe-rs is *cheaper than the crossing per-op and it parallelizes, but it is not
free*.

## The measured envelope — N × K → latency (real runs, CPU M2 Max)

Every row below is a **real FHE clear**, correctness-checked equal to the
plaintext reference (`p*`, `V*` match exactly), except the last (labelled
extrapolated, grounded in the measured per-op costs — it exceeds the 900 s
per-config run budget).

| N | K | encrypt (N·K cts) | **aggregate** (2K deferred-carry sums) | **crossing** (K `ge`+select) | decrypt result | **total clear** | correct |
|---|---|---|---|---|---|---|---|
| 32 | 64 | 0.67 s | 36.7 s | 9.67 s | <0.1 ms | **46.4 s** | ✅ p*=18 V*=383 |
| 32 | 256 | 2.60 s | 151.8 s | 44.5 s | <0.1 ms | **196.3 s** (3.3 min) | ✅ p*=123 V*=490 |
| 128 | 64 | 3.69 s | 122.1 s | 9.49 s | <0.1 ms | **131.6 s** (2.2 min) | ✅ p*=36 V*=2011 |
| 128 | 256 | 10.3 s | 522.6 s | 41.0 s | <0.1 ms | **563.7 s** (9.4 min) | ✅ p*=138 V*=1473 |
| 512 | 64 | 10.2 s | 477.9 s | 10.6 s | <0.1 ms | **488.5 s** (8.1 min) | ✅ p*=32 V*=1995 |
| 512 | 256 | ~44 s | ~1793 s | ~36 s | — | **~1830 s (~30 min)** | *extrapolated* |

(`total clear` counts aggregate + crossing + decrypt — the homomorphic work the
server does; `encrypt` is the traders' one-time submit cost, listed separately.)

## What the numbers say vs the estimates

- **"The crossing is O(K), independent of N" — CONFIRMED (the good half).** The
  crossing time depends only on K: **~9.5–10.6 s at K=64 for every N** (32, 128,
  512), **~41–44 s at K=256**. It does not grow with the number of orders. The
  monotone-crossing-as-a-sum-of-K-comparison-bits kernel works exactly as
  designed.
- **"Aggregation is the cheap part, the crossing is the cost" — REFUTED for
  exact-integer tfhe-rs.** The opposite is true here: **aggregation dominates
  every configuration** and grows ~linearly in N·K, while the crossing is the
  small N-independent tail. Aggregate-vs-crossing ratios measured: 3.8× (32/64),
  3.4× (32/256), 12.9× (128/64), 12.7× (128/256), **45.1× (512/64)**. Root
  cause: a tfhe-rs exact-integer add is **ms, not µs** — even the deferred-carry
  parallel tree-sum is 13.7 ms/element (carry propagation is PBS-class). The
  "matching cost evaporates into cheap additions" claim is right *only* against
  an O(N log²N)-bootstrap **sort**, and only in an **additive scheme** where the
  add really is µs; in exact TFHE the additions themselves are the wall.
- **"Minute-cadence to N≈few-thousand" (the estimate) — only partially, and not
  on exact-integer TFHE CPU.** Measured: N=32–128 at coarse **K=64** clears in
  **~1–2 min**; going to fine **K=256** or **N=512** pushes to **8–9.4 min**;
  **N=512, K=256 ≈ 30 min**. So the real cadence on this host is **minutes to
  tens-of-minutes**, and **N in the thousands is out of minute-cadence** — the
  estimate's tens-of-seconds figures were **approximate CKKS** (128 elts ~22 s)
  and/or **GPU**, exactly as `DREX-NO-VIEWER-SURPASS.md §2.3` itself cautioned
  ("exact-integer TFHE is slower than approximate CKKS"). The honest verdict:
  **the no-viewer FHE clear is REAL and CORRECT at these sizes, but on
  exact-integer TFHE CPU it is a minutes-cadence batch, not a seconds one.**

## One PDHG flow-LP iteration under FHE (the T-step convex-engine cost)

`src/bin/pdhg.rs` runs ONE Chambolle–Pock iteration of the circulation flow-LP
`max wᵀf s.t. Af=0, 0≤f≤c` over an **encrypted** `FheInt16` flow with a
**public** incidence `A`: matvec `Af`/`Aᵀy` (homomorphic add/sub + public-scalar
mul), the box prox `clamp(0,c)` (`max` then `min` per edge), extrapolation. Real
runs, CPU M2 Max, avg of 3 iterations:

| graph | matvec (public A) | box prox `clamp(0,c)` | extrapolation | **per-iter** | prox share | PBS-equiv/edge | T=100 | T=1000 |
|---|---|---|---|---|---|---|---|---|
| 6 nodes, m=8 | 3.31 s | 2.11 s | 1.15 s | **6.57 s** | 32% | **2.0** | 11 min | 1.8 h |
| 12 nodes, m=16 | 6.83 s | 4.29 s | 2.32 s | **13.44 s** | 32% | **2.0** | 22 min | 3.7 h |
| 24 nodes, m=32 | 14.60 s | 8.70 s | 4.90 s | **28.21 s** | 31% | **2.0** | 47 min | 7.8 h |

- **codex's "~2–3 PBS/pack per iteration" for the prox — CONFIRMED.** With a
  PUBLIC box cap, the prox is exactly one `max` + one `min` per edge = **2.0
  PBS-equiv/edge**, dead-on the estimate. (A *secret heterogeneous* cap would add
  the compare+mux and push toward 3, as `PRIVATE-CONVEX-ENGINE.md §1.4` notes.)
- **codex's "matvec is bootstrap-free, the prox is the cost" — REFUTED for
  exact-integer tfhe-rs.** The **matvec is the LARGER half** (~50% of the
  iteration) and the prox is only ~31–32%. Same root cause as the clearing
  aggregation: the matvec's `FheInt16` add/sub **carry-propagate (PBS-class)**,
  so the "homomorphic-linear step is free" premise does not hold in exact-integer
  TFHE — it holds only in an additive scheme (CKKS/lattice-additive) where the
  linear combination is genuinely cheap.
- **The T-step bill is heavy on CPU exact-integer.** Even a *tiny* graph (m=32)
  costs **~47 min for T=100**, **~7.8 h for T=1000**. A useful convex solve
  (T≈100–1000) under exact-integer FHE on CPU is **tens-of-minutes to hours** —
  confirming the convex engine is real in shape but far from real-time here. The
  levers are the same: additive-scheme matvec + GPU + small T (momentum,
  public preconditioning).

## What is real-now vs the frontier

- **Real now:** a genuine no-viewer FHE clear — orders never decrypted, only
  `p*`/`V*` open — correctness-proven against plaintext, on stock open-source
  tfhe-rs. The privacy property is unconditional (FHE hides inputs regardless of
  who runs the compute).
- **The performance frontier:** exact-integer TFHE additions being ms-scale.
  The paths that recover the estimate's envelope: (1) an **additive scheme for
  the aggregation** (CKKS-packed / lattice-additive commitments — µs adds, SIMD
  across buckets) with TFHE only for the O(K) crossing; (2) **GPU** (H100,
  ~10–30×); (3) **fewer, coarser price buckets K** and **per-pair sharding** to
  cut N.
- **Cheap verifiability (confirmed by construction):** the FHE circuit here is
  **deterministic** on public input ciphertexts, so correctness of the
  *evaluation* is re-checkable by re-running it — no verifiable-FHE needed; only
  the final threshold-decryption of `p*` needs a proof (Option A of
  `DREX-NO-VIEWER-SURPASS.md §4`).
- **Separate named residual (NOT closed here):** tfhe-rs gives the compute and
  is itself **lattice/PQ**, but the **PQ-additive commitment binding for the
  STARK** (`PQ-SHIELDED-COMMITMENT.md`) is a distinct piece this PoC does not
  build.
