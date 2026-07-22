# Direct-logic live prover capture (2026-07-22, M2 Max)

This is an **absolute measurement of the current executable path**, not a
speedup comparison:

```text
LogicProgram
  -> compile_logic_program
  -> EffectVmDescriptor2
  -> one_row_trace
  -> prove_vm_descriptor2
  -> verify_vm_descriptor2
```

It does not measure the abstract Lean optimizer, hybrid FHE schedules, a
conventional-circuit baseline, ModulusZK, network inclusion, or blockchain
finality. The formulas are deliberately small one-row finite-logic workloads.
All resulting batch proofs reported `degree_bits=0`.

## Reproduction

```sh
cargo build -p dregg-circuit --release --bin direct_logic_live_benchmark
DREGG_LOGIC_BENCH_COMPILE_SAMPLES=200 \
DREGG_LOGIC_BENCH_WITNESS_SAMPLES=2000 \
DREGG_LOGIC_BENCH_PROVE_SAMPLES=30 \
DREGG_LOGIC_BENCH_VERIFY_SAMPLES=100 \
DREGG_LOGIC_BENCH_WARMUPS=5 \
  target/release/direct_logic_live_benchmark > raw.log
```

The harness prints every timing sample in integer nanoseconds. `summary.csv`
uses the 50th and 95th percentiles, arithmetic mean, sample standard deviation,
and deterministic 10,000-resample percentile-bootstrap intervals for both the
median and mean. Regenerate it with
`python3 summarize.py /path/to/raw.log > reproduced-summary.csv` (NumPy 2.4.6
was used for this capture). Proof bytes are the length of the same postcard encoding used
by the live SDK proof path. Release proving does not perform the debug-only
self-verification; the harness separately verifies every warmup proof and the
retained measured proof, then times verification separately.

## Workloads and relation sizes

| workload | atoms / columns | constraints | retained Boolean expression nodes | descriptor bytes | proof bytes |
|---|---:|---:|---:|---:|---:|
| `bool-eq` | 1 | 2 | 1 | 498 | 9,262 |
| `enum-eq-4` | 4 | 6 | 1 | 1,158 | 9,342 |
| `enum-eq-16` | 16 | 18 | 1 | 3,387 | 9,721 |
| `enum-eq-64` | 64 | 66 | 1 | 12,363 | 10,924 |
| `forall-tautology-4` | 4 | 6 | 19 | 2,540 | 10,202 |
| `forall-tautology-8` | 8 | 10 | 39 | 4,696 | 11,165 |
| `forall-tautology-16` | 16 | 18 | 79 | 9,052 | 13,101 |

The equality-to-public-constant workloads simplify to one retained Boolean
atom; their increasing relation size comes from Booleanity and exact one-hot
input constraints. The quantified workloads retain deterministically unrolled
Boolean expressions. `forall-tautology-N` proves
`forall x : Fin N, input = x or not (input = x)`; it is intentionally not
constant-folded by the front end.

## Headline absolute measurements

| workload | prove median / p95 (ms) | verify median / p95 (ms) |
|---|---:|---:|
| `bool-eq` | 2.219 / 4.572 | 0.282 / 0.789 |
| `enum-eq-4` | 6.911 / 9.829 | 0.293 / 0.691 |
| `enum-eq-16` | 4.497 / 7.140 | 0.309 / 0.686 |
| `enum-eq-64` | 6.728 / 8.596 | 0.500 / 0.862 |
| `forall-tautology-4` | 19.637 / 23.838 | 0.361 / 0.794 |
| `forall-tautology-8` | 8.828 / 10.630 | 0.488 / 1.086 |
| `forall-tautology-16` | 26.833 / 31.437 | 0.800 / 1.695 |

The non-monotone proving medians are recorded as observed, not interpreted as
a scaling law. This capture ran on a shared development host at load averages
31.34 / 37.81 / 38.25, so contention is a material limitation. The complete
sample distribution is the evidence; no ratio or broad performance claim is
derived from these absolute numbers.

## Backend and environment

- Apple M2 Max, 12 logical CPUs, 96 GiB RAM; macOS 26.5.1 (Darwin 25.5.0).
- Rust `1.98.0-nightly (8b6558a02 2026-06-20)`.
- BabyBear, extension degree 4, FRI log blowup 6, 19 queries, 16 query-PoW
  bits, final polynomial log length 0, maximum log arity 3.
- Frontend SHA-256:
  `e9c998c412a64b63d2714b9ee6314a765c1a9ff0f89b6ee5d24e255d73bf1568`.
- Harness SHA-256:
  `b1492c385937f70d555a5a059b9dbdba95fc6a53ca832ff55fd6923e05a36907`.
- `Cargo.lock` SHA-256:
  `ec6ce78569f97efc3dce339328240447f0c26cfad75f56cec9077bbf9341f70f`.
- Raw log SHA-256:
  `66b37bf19bfffe505b967b03fdf44a0cc8bde22ca232493417fe3350b9ef3b1e`.
- Summary SHA-256:
  `39a623da8ea21a03e69a6f420d5b49ce52762a9e4cbb9fefbdb21e7ae661db73`.

The raw capture is `/tmp/direct-logic-live-20260722/raw.log` on the capture
host. The checked-in harness regenerates it; the raw log is intentionally not
presented as a stable cross-machine baseline.
