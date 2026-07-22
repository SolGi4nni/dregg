# Direct logic conformance and microbenchmark harness

This is an executable, semantics-first comparison of five precisely scoped
relations:

| lane | meaning | performance admission |
|---|---|---|
| `M-SPEC` | exact transcription of the zero-true connective, quantifier, and swap equations printed in the public BitLogic PDF | excluded if the semantic gate fails |
| `G-FIELD-NAIVE` | Gabbay-style squared positive residuals with `AND = sum`, naively reduced in BabyBear | excluded if cancellation falsifies it |
| `D-NOWRAP` | the corrected nonnegative-integer residual route; every atom and partial accumulator must be proved below the modulus before casting | admitted on its supported fragment |
| `D-BOOLGRAPH` | exact one-means-true Boolean graph with inverse-witness zero tests | admitted after conformance |
| `C-AIR` | independently written conventional gate-by-gate Boolean arithmetic baseline | admitted after conformance |

The governing rule is: **an unsound relation has no benchmark speedup**. Raw
evaluator timings are retained for audit, but a failing lane is automatically
excluded from `summary.json` ratios.

## Run it

The harness uses only the Python standard library and deterministic generated
inputs. Python 3.11 or newer is recommended.

```sh
cd tools/direct-logic-bench
python3 -m unittest discover -s tests -v
python3 direct_logic_bench.py --output /tmp/direct-logic-run
```

The default run checks the pinned adversarial/transaction corpus plus 10,000
generated formulas, then collects nine evaluator samples per pinned workload.
For a fast semantics-only replay:

```sh
python3 direct_logic_bench.py \
  --output /tmp/direct-logic-conformance \
  --random-cases 10000 \
  --no-timing
```

The output directory must not already exist. It contains:

- `META.json`: environment, input/harness hashes, command, source pins;
- `workloads.json`: the exact typed formula and residual corpus;
- `gates.json`: every lane/workload result and the aggregate admission gate;
- `costs.json` and `costs.csv`: backend-neutral symbolic ledger;
- `samples.jsonl`, `samples.csv`, and `stats.json`: raw and aggregate evaluator timings;
- `summary.json`: only gate-eligible ratios;
- `SUMMARY.md`: concise human-readable result.

## What is transcribed

`M-SPEC` is pinned to commit
`26f125b37f0442d92991e3066095b1dfeb1b0ce4` of the public
[BitLogic repository](https://github.com/ModulusZK/BitLogic-from-Modulus-zkFOL-Bitcoin).
The inspected PDF has SHA-256
`ea0e483ec9c7a3acfaae52ef0dfc0e07d141b760c2ce4b14461c1b89f324ba0c`.
Its printed swap relation is transcribed as:

```text
(A' - A + k) * (B' - B - f(k,s)) * (A*B - A'*B') = 0
```

The corpus includes the integer witness formalized by Lean theorem
`published_swap_accepts_invalid_witness`: the first factor is zero while the
other two are `988` and `-8891`. The public relation accepts it identically.

`G-FIELD-NAIVE` is separate because Gabbay's actual nonnegative-rational
construction uses the opposite positive connectives: addition for conjunction
and multiplication for disjunction. The BabyBear cancellation vector mirrors
Lean theorem `babyBear_false_and_false_accepted`.

## Cost ledger scope

The corrected symbolic rows mirror the recurrences proved in:

- `metatheory/Dregg2/Metatheory/ArithmetizationCost.lean`;
- `metatheory/Dregg2/Metatheory/FOLArithmetizationCorrected.lean`;
- `metatheory/Dregg2/Logic/BoolGraph.lean`.

Atoms are supplied as already-computed **signed** equality residuals, so the
application arithmetic producing those differences is excluded consistently.
The positive Gabbay/no-wrap lanes count the extra square that makes each signed
residual nonnegative. The conventional baseline applies the normal production
optimization for a pure conjunction: constrain every signed residual directly
rather than manufacture Boolean wires.

`M-SPEC` and `G-FIELD-NAIVE` rows describe their printed single-polynomial
expressions; they are not directly comparable constraint-graph counts. The
representation column makes that boundary machine-readable.

## What this does **not** measure

This harness has no public Modulus compiler/prover to call and does not pretend
that evaluating Python integers is a ZK benchmark. It measures:

1. semantic conformance/falsification;
2. backend-neutral symbolic equations, multiplications, witnesses, and degree;
3. Python relation-evaluator throughput as a reproducible implementation smoke
   benchmark.

It does **not** measure witness generation, proof generation, verification,
proof bytes, setup, zero knowledge, FHE, chain admission, data availability,
finality, or monetary cost. An external implementation should be added as a
new `M-IMPL` adapter only when source, parameters, build recipe, and raw proof
artifacts are available.
