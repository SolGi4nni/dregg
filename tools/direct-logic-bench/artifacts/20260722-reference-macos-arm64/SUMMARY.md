# Direct logic benchmark run

- Suite: `direct-logic-v1`
- Run: `20260722-reference-macos-arm64`
- BabyBear modulus: `2013265921`
- Deterministic generated-case seed: `872038`

## Semantic admission gate

| lane | gate | supported | unsupported | mismatches |
|---|---:|---:|---:|---:|
| `M-SPEC` | fail | 10061 | 0 | 3936 |
| `G-FIELD-NAIVE` | fail | 6748 | 3313 | 1 |
| `D-NOWRAP` | pass | 6737 | 3324 | 0 |
| `D-BOOLGRAPH` | pass | 10061 | 0 | 0 |
| `C-AIR` | pass | 10061 | 0 | 0 |

A failing lane is retained as a falsification artifact but excluded from every speedup.
An unsupported D-NOWRAP row means the required integer accumulator bound was not established; it is not silently cast.

## Measurement boundary

This run measures Python relation-evaluator throughput and backend-neutral symbolic costs. It contains no proof generation, proof verification, FHE, deployment, finality, or monetary-cost measurement.
The public `M-SPEC` lane is an executable transcription of equations, not a public Modulus prover implementation.

Aggregate timing rows: 296; see `samples.csv` and `samples.jsonl` for raw samples.
See `summary.json` for eligible per-workload evaluator ratios; they are intentionally not called prover speedups.
