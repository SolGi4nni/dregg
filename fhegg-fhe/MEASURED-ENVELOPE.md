# NO-VIEWER FHE Clearing — the Measured Envelope (honest numbers)

Stage-2 companion to the ESTIMATES in `docs/deos/DREX-NO-VIEWER-SURPASS.md`,
`docs/deos/FHEGG-KERNEL.md`, `docs/deos/PRIVATE-CONVEX-ENGINE.md`. This crate
(`fhegg-fhe/`) builds a **real** no-viewer FHE uniform-price clear with
**tfhe-rs** (Zama TFHE, exact integers) — nobody ever decrypts an order, only
the public clearing price `p*` and aggregate volume `V*` — and **measures** it.
No mock FHE, no faked benchmark. Where a number is extrapolated it is labelled
and grounded in a measured per-op cost.

> **2026-07-17 RE-MEASUREMENT.** The circuit changed after the original
> measurement (FheUint16 → FheUint32 aggregates; sum-of-crossing-bits → true
> uniform-price oblivious argmax) and the old table silently kept describing the
> superseded circuit. The tables in §"The measured envelope" below are the
> CURRENT circuit, re-run end-to-end. The original FheUint16-era tables are
> preserved at the bottom, marked **SUPERSEDED**, because their *shape* findings
> (aggregation dominates; crossing is N-independent) still hold and the
> old-vs-new delta is itself a finding.

## Bottom line (the gate verdict)

**Does no-viewer FHE clearing genuinely perform at useful sizes? YES it works
and is CORRECT; NO it is not fast on exact-integer TFHE CPU — it is a
minutes-cadence batch, not a seconds one — and the CURRENT (correct-rule,
non-wrapping) circuit is ~2.3–2.7× slower than the superseded circuit the old
table described.**

- The no-viewer clear is **real and correctness-verified** on the current
  circuit for (N,K) ∈ {(8,16),(32,64),(32,256),(128,64)}: the FHE `p*`/`V*`
  equal the plaintext reference at every size that ran. Nobody decrypts an
  order — only `p*` and `V*` open. The privacy of the *computation* is
  unconditional (the key-custody residual is separate; see
  `docs/deos/OUTPUT-BOUNDARY-MPC.md` §7.5, `NoViewerKeyCustodyResidual`).
- **Measured latency (current circuit, 24-core CPU, tfhe-rs 1.6.3):** N=8/K=16
  clears in **24 s**; N=32/K=64 in **~2 min**; N=128/K=64 in **~5 min**;
  N=32/K=256 in **~8.8 min**. N=512 or K=256 with N≥128 exceeds the 900 s
  per-config budget on the current circuit (they were real runs on the
  superseded one): **~19–21 min** extrapolated, **N=512/K=256 ≈ 76 min**
  extrapolated. Exact-integer TFHE CPU remains **minutes-to-tens-of-minutes**.
- **The all-TFHE path is the BASELINE, not the plan.** The measured Tier-0
  levers live in the companion docs: the carry-free additive BFV fold is
  **~10⁵× cheaper, sub-10 ms** (`ADDITIVE-FOLD-ENVELOPE.md`), and the
  output-boundary-MPC crossing takes AGG→p* to **17–76 ms**
  (`docs/deos/OUTPUT-BOUNDARY-MPC.md` §7.5). This file is what those numbers
  are measured AGAINST.

## The CURRENT circuit (what `src/lib.rs` actually computes)

Two changes vs the superseded measurement, both correctness-driven:

1. **Aggregates are `FheUint32`, not `FheUint16`** (16 radix blocks, not 8).
   A bucket sum of *legal* u16 quantities can exceed 2^16 — two 32768-lot bids
   sum to 65536, which a 16-bit ciphertext silently wraps to 0 (test
   `fhe_no_u16_overflow` pins this). The plaintext reference always accumulated
   in u32; the FHE side now matches it instead of quietly narrowing.
2. **The crossing is the true uniform-price rule, not sum-of-crossing-bits.**
   Current: `v[p] = min(D[p],S[p])` per bucket (one homomorphic `ge` + one
   select each), then an **oblivious argmax** scan over the K encrypted volumes
   (K−1 `gt` + 2(K−1) selects carrying the running `(best_v, best_p)`), ties to
   the LOWEST p. The superseded `p* = (Σ_p [D[p]≥S[p]]) − 1` clears at the
   *largest crossing*, which under-clears whenever the volume peak sits above
   the crossing edge — counter-witness D=(10,9), S=(5,20): old rule p*=0 V*=5,
   true rule p*=1 V*=9 (`reference_counter_witness`). The delta is LIVE in the
   sweep: on the identical seeded book at N=32/K=256 the superseded circuit
   cleared (p*=123, V*=490); the current one clears (p*=124, **V*=547**) — the
   old rule was really leaving volume on the table.

   Cost of honesty: the crossing is now ~3× the homomorphic ops
   (K `ge` + K sel + (K−1) `gt` + 2(K−1) sel vs K `ge` + K sel), on a 2×-wider
   type.

`src/bin/bench.rs` measures per-op costs on `FheUint32` (the type the circuit
uses) and models the extrapolation on the argmax crossing (not the superseded
one). Reproduce: `cargo run --release -p fhegg-fhe --features tfhe-integer --bin fhe-clearing-bench`
(set `FHEGG_HOST` so the log names the box).

## Host + params (honest about the hardware AND the contention)

- **persvati: 24-core AMD Ryzen AI 9 HX PRO 370, x86_64 Linux, CPU only** (no
  CUDA; tfhe-rs's `gpu` feature is NVIDIA-only — no GPU number from this host).
  Zama's published CPU→H100 speedup is ~10–30×; apply that to read a GPU column.
- **The box was CONTENDED during the run** (co-tenant cargo builds; load ~20–65
  on 24 cores). Treat these numbers as an honest *upper* bound for this CPU
  class, not a clean-room floor. Per-op costs and the sweep were measured in
  the SAME session, so the extrapolated rows are self-consistent with the
  measured ones (sanity check: the per-op model put the 128/64 clear at ~317 s;
  the real run took 298 s).
- Cross-host comparability: `HBOX-24CORE-ENVELOPE.md` measured a 24-core
  desktop-class x86 CPU at **0.96–1.21×** the M2 Max on this workload (single
  radix ops don't parallelize past ~8 threads), so comparing this table to the
  superseded M2 table is meaningful, and the ~2.3–2.7× delta is dominated by
  the **circuit change**, not the host change.
- tfhe-rs **1.6.3**, high-level API, default params (`PARAM_MESSAGE_2_CARRY_2`,
  ≥128-bit, IND-CPA-D). `FheUint32` = 16 radix blocks (2 message bits each).
  keygen 0.93 s.

## Measured per-operation cost (CURRENT type: FheUint32)

| op (`FheUint32`, CPU, 2026-07-17) | measured | superseded FheUint16 (M2) |
|---|---|---|
| encrypt | **1.60 ms** | 0.34 ms |
| decrypt | **0.022 ms** | 0.006 ms |
| `ge` (compare) | **161.8 ms** | 66.9 ms |
| `if_then_else` (select) | **114.2 ms** | 74.4 ms |
| sequential add `a + b` (carry-propagating) | **281.0 ms** | 70.7 ms |
| **`sum` of 512 cts** (deferred-carry parallel tree-sum) | **17.14 s → 33.5 ms per input-add** | 7.00 s → 13.7 ms |

The FheUint16-era headline correction stands, ~2.4× heavier at the honest
width: exact-integer radix addition **carry-propagates (PBS-class, tens of ms —
not µs)**, so in all-TFHE the aggregation dominates the clear. The "µs
additions" hold only in an **additive scheme** — now *measured* in
`ADDITIVE-FOLD-ENVELOPE.md` (BFV fold sub-10 ms, ~10⁵× cheaper) rather than
hypothesized.

## The measured envelope — N × K → latency (CURRENT circuit, real runs 2026-07-17)

Every non-extrapolated row is a **real FHE clear**, correctness-checked equal
to the plaintext reference (`p*`, `V*` match exactly). Rows exceeding the 900 s
per-config budget are extrapolated from the same-session per-op costs and
labelled. (`total clear` = aggregate + crossing + decrypt — the server's
homomorphic work; `encrypt` is the traders' one-time submit cost.)

| N | K | encrypt (N·K cts) | **aggregate** (2K deferred-carry sums) | **crossing** (K min-selects + argmax) | decrypt result | **total clear** | correct | vs superseded circuit |
|---|---|---|---|---|---|---|---|---|
| 8 | 16 | 0.11 s | 10.2 s | 13.8 s | <0.1 ms | **24.0 s** | ✅ p*=7 V*=54 | (new size) |
| 32 | 64 | 2.38 s | 84.0 s | 32.4 s | <0.1 ms | **116.5 s** (1.9 min) | ✅ p*=12 V*=383 | 46.4 s → **2.5×** |
| 32 | 256 | 5.45 s | 325.1 s | 203.3 s | <0.1 ms | **528.4 s** (8.8 min) | ✅ p*=124 V*=547 | 196.3 s → **2.7×** |
| 128 | 64 | 5.59 s | 264.8 s | 33.2 s | <0.1 ms | **297.9 s** (5.0 min) | ✅ p*=36 V*=2011 | 131.6 s → **2.3×** |
| 128 | 256 | ~52 s | ~1097 s | ~170 s | — | **~1267 s (~21 min)** | *extrapolated* | 563.7 s (was real) |
| 512 | 64 | ~52 s | ~1097 s | ~42 s | — | **~1139 s (~19 min)** | *extrapolated* | 488.5 s (was real) |
| 512 | 256 | ~209 s | ~4388 s | ~170 s | — | **~4559 s (~76 min)** | *extrapolated* | ~1830 s (extrap.) |

What ran vs what did not, said plainly: **N=8/16, 32/64, 32/256, 128/64 are
real end-to-end runs; 128/256, 512/64, 512/256 are extrapolations** — on the
superseded circuit the first two of those were real runs, and the current
circuit's ~2.3–2.7× cost pushed them over the same 900 s budget.

## What the current numbers say

- **"The crossing is O(K), independent of N" — still CONFIRMED.** ~32.4–33.2 s
  at K=64 for N=32 and N=128; 203 s at K=256. No N-dependence.
- **The argmax crossing is ~3.3–4.9× the superseded bit-sum crossing** (32.4 s
  vs 9.67 s at K=64; 203 s vs 44.5 s at K=256) — the compounded price of the
  correct clearing rule and the honest 32-bit width. At K=256 the crossing is
  now a substantial fraction of the clear (38% at N=32), which sharpens the
  case for the output-boundary-MPC crossing (ms-scale) rather than weakening it.
- **Aggregation still dominates at K=64** and grows with N·K, mildly
  sub-linearly in N (3.2× for 4× N at K=64 — the parallel tree-sum amortizes).
  Same root cause, now at 33.5 ms/input-add.
- **The correct rule pays real volume:** same book, 32/256 — V*=547 vs the
  superseded rule's 490. Correctness was not free (2.7×) but it was not
  cosmetic either.
- **Cadence class is unchanged: minutes.** The current circuit shifts the
  minute-count (2.3–2.7×), not the class. The class-changing levers remain the
  measured additive fold + boundary-MPC crossing (+GPU, +coarse K).

## One PDHG flow-LP iteration under FHE (unchanged code, numbers stand)

`src/bin/pdhg.rs` is UNCHANGED (`FheInt16`, separate circuit) — its original
M2 Max measurement still describes the code that exists:

| graph | matvec (public A) | box prox `clamp(0,c)` | extrapolation | **per-iter** | prox share | PBS-equiv/edge | T=100 | T=1000 |
|---|---|---|---|---|---|---|---|---|
| 6 nodes, m=8 | 3.31 s | 2.11 s | 1.15 s | **6.57 s** | 32% | **2.0** | 11 min | 1.8 h |
| 12 nodes, m=16 | 6.83 s | 4.29 s | 2.32 s | **13.44 s** | 32% | **2.0** | 22 min | 3.7 h |
| 24 nodes, m=32 | 14.60 s | 8.70 s | 4.90 s | **28.21 s** | 31% | **2.0** | 47 min | 7.8 h |

- **"~2–3 PBS/pack per iteration" for the prox — CONFIRMED** (2.0 with a
  public box cap; a secret heterogeneous cap pushes toward 3).
- **"matvec is bootstrap-free, the prox is the cost" — REFUTED for
  exact-integer tfhe-rs**: the matvec is the larger half (~50%) because
  `FheInt16` add/sub carry-propagate. Additive-scheme matvec is the fix
  (measured for the auction fold in `ADDITIVE-FOLD-ENVELOPE.md`).
- A useful T≈100–1000 solve under exact-integer CPU FHE is
  **tens-of-minutes to hours**.

## What is real-now vs the frontier

- **Real now:** a genuine no-viewer FHE clear under the TRUE uniform-price rule
  (argmax volume, ties-low), non-wrapping aggregates, correctness-proven
  against plaintext on every size that runs, on stock open-source tfhe-rs.
- **The performance frontier (measured, not hoped):** the additive BFV fold
  (`ADDITIVE-FOLD-ENVELOPE.md`: sub-10 ms, ~10⁵×) + the output-boundary-MPC
  crossing (`docs/deos/OUTPUT-BOUNDARY-MPC.md` §7.5: AGG→p* 17–76 ms) replace
  both all-TFHE phases; GPU (~10–30×, Zama H100 figure) and coarser K stack on
  top. The named residuals: BFV threshold key custody
  (`NoViewerKeyCustodyResidual` — mbfv is n-of-n with an upstream smudging
  TODO) and the PQ-additive commitment binding for the STARK
  (`PQ-SHIELDED-COMMITMENT.md`).
- **Cheap verifiability (unchanged):** the FHE evaluation is deterministic on
  public input ciphertexts — re-runnable, no verifiable-FHE needed; only the
  final threshold decryption of `p*` needs a proof.

---

---

# SUPERSEDED (2026-07-17) — the FheUint16 / sum-of-bits-crossing measurement

> **Everything below describes the OLD circuit** — `FheUint16` aggregates (can
> wrap on legal input: two 32768-lot orders in one bucket) and the
> `p* = Σ[D≥S] − 1` largest-crossing rule (under-clears off-peak;
> counter-witness above). Measured 2026-07 on Apple M2 Max (12 cores), tfhe-rs
> 1.6.3, `FheUint16` = 8 radix blocks. Kept because the shape findings
> (aggregation dominates; crossing O(K) N-independent; carry-propagation is
> PBS-class) were confirmed unchanged by the re-measurement, and the companion
> `HBOX-24CORE-ENVELOPE.md` (24-core x86, ~1.0–1.2× M2) measured THIS circuit.
> Do not quote these rows as the current circuit's cost — use the table above.

## [SUPERSEDED] Measured per-operation cost (FheUint16, M2 Max)

| op (`FheUint16`, CPU M2 Max) | measured |
|---|---|
| encrypt | 0.34 ms |
| decrypt | 0.006 ms |
| `ge` (compare) | 66.9 ms |
| `if_then_else` (select) | 74.4 ms |
| sequential add `a + b` (carry-propagating) | 70.7 ms |
| `sum` of 512 cts (deferred-carry parallel tree-sum) | 7.00 s → 13.7 ms per input-add |

## [SUPERSEDED] The envelope — N × K → latency (old circuit, real runs, M2 Max)

| N | K | encrypt (N·K cts) | aggregate (2K sums) | crossing (K `ge`+select) | decrypt | total clear | correct (OLD rule) |
|---|---|---|---|---|---|---|---|
| 32 | 64 | 0.67 s | 36.7 s | 9.67 s | <0.1 ms | 46.4 s | ✅ p*=18 V*=383 |
| 32 | 256 | 2.60 s | 151.8 s | 44.5 s | <0.1 ms | 196.3 s (3.3 min) | ✅ p*=123 V*=490 |
| 128 | 64 | 3.69 s | 122.1 s | 9.49 s | <0.1 ms | 131.6 s (2.2 min) | ✅ p*=36 V*=2011 |
| 128 | 256 | 10.3 s | 522.6 s | 41.0 s | <0.1 ms | 563.7 s (9.4 min) | ✅ p*=138 V*=1473 |
| 512 | 64 | 10.2 s | 477.9 s | 10.6 s | <0.1 ms | 488.5 s (8.1 min) | ✅ p*=32 V*=1995 |
| 512 | 256 | ~44 s | ~1793 s | ~36 s | — | ~1830 s (~30 min) | *extrapolated* |

("correct" above means: matched the plaintext reference *of the old rule*. The
old rule itself under-clears — see the counter-witness — which is exactly why
it was superseded.)

## [SUPERSEDED] The estimate-audit narrative (old circuit)

- ✅ crossing O(K), N-independent — confirmed (~9.5–10.6 s at K=64 ∀N; ~41–44 s
  at K=256). Still true on the current circuit at its higher constant.
- ✅ prox ≈ 2–3 PBS/pack per PDHG iteration — confirmed (2.0, public cap).
  (pdhg.rs unchanged; still current.)
- ❌ "aggregation/matvec is bootstrap-free / the cheap part" — REFUTED for
  exact-integer tfhe-rs: radix adds carry-propagate (PBS-class), aggregation
  dominated every config (3.4×–45× the crossing). Still true on the current
  circuit at K=64; at K=256 the heavier argmax narrows the ratio (1.6× at
  N=32). The "µs additions" claim holds only in an additive scheme — since
  MEASURED in `ADDITIVE-FOLD-ENVELOPE.md` (the recovery lever, ~10⁵×).
- "Minute-cadence to N≈few-thousand" — refuted on exact-integer TFHE CPU then
  (minutes to tens-of-minutes, thousands out of reach) and MORE refuted now
  (current circuit 2.3–2.7× heavier). The estimate's tens-of-seconds figures
  were approximate-CKKS/GPU numbers, as `DREX-NO-VIEWER-SURPASS.md §2.3` itself
  cautioned.
