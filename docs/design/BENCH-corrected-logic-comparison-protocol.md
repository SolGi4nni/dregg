# Corrected logic arithmetization: comparison and benchmark protocol

Status: design protocol, 2026-07-21. This document does not claim that the
corrected compiler exists or that any performance comparison has been won. It
defines what must be built and measured before such a claim is responsible.

The comparison has one governing rule:

> An unsound relation has no benchmark time. Correctness is an admission gate,
> not another metric on the Pareto frontier.

This protocol compares the corrected designs in
`DESIGN-corrected-logic-dual-lowering.md` with conventional circuit lowerings.
It also provides a public challenge format that ModulusZK or any other project
can implement. The publicly available BitLogic paper is a specification input,
not an executable competitor.

## 1. Separate the layers before measuring

Four costs must never be collapsed into one number:

1. **Semantic lowering:** typed formula to an exact proof relation or encrypted
   program.
2. **Arithmetization:** the relation represented as a descriptor/AIR, R1CS,
   PLONKish relation, integer/rational CCS, or another proof-system IR.
3. **Cryptographic backend:** witness generation, proving, verification, proof
   bytes, setup, and security parameters.
4. **Deployment:** batching, sequencer admission, data availability, L1 posting,
   and consolidated finality.

"Circuit bypass" is a front-end claim. It cannot by itself establish a prover
speedup: both paths ultimately supply a relation to a proof backend. Likewise,
"1--3 second finality" is a chain/deployment claim, not a synonym for proof
generation latency. Report the four layers separately.

There are two valid performance comparisons:

- **Arithmetization-isolated:** use the same field, commitment/hash, security
  target, prover implementation, hardware, and workload; vary only the lowering.
- **End-to-end:** run the best complete implementation of each path, but report
  backend and parameter differences and do not attribute the whole delta to the
  front-end technique.

## 2. Comparison lanes

Every workload begins as one versioned typed AST and one executable Boolean
reference evaluator. All lanes consume the same serialized inputs and must
return the same result.

| lane | purpose | required implementation |
|---|---|---|
| `REF` | semantic oracle | Lean evaluator plus a small independently implemented differential oracle |
| `D-BOOLGRAPH` | exact finite-field lowering | one-means-true Boolean wires, inverse-witness zero tests, range gadgets for order |
| `D-NOWRAP` | corrected positive-residual lowering | nonnegative integer residuals plus machine-checked partial-sum/product bounds below the modulus |
| `D-Q/ZINC` | exact integer/rational lowering | integer/rational constraints and the pinned Zinc/Zip-style projection configuration |
| `D-RANDOM` | randomized equation batching | commitment-before-challenge transcript and a proved, reported failure bound |
| `C-AIR` | conventional circuit baseline | the same source semantics lowered gate-by-gate to the same DREGG/Plonky3 backend |
| `C-R1CS` | conventional ecosystem baseline | Circom/R1CS plus a pinned snarkjs prover; constraint count and setup are reported separately |
| `M-SPEC` | public Modulus/BitLogic specification | executable transcription of the published equations, used for conformance/counterexamples only |
| `M-IMPL` | optional external implementation | admitted only when source, build recipe, parameters, proofs, and raw benchmark artifacts are public |

`M-SPEC` must never appear in a prover-latency bar chart: the public BitLogic
artifact does not provide a prover/compiler to time. If an executable Modulus
artifact is later published, add it without changing the pre-registered
workloads or gates.

For FHE, the same typed AST has separate lanes because proof and encrypted
execution have different cost structures:

| lane | carrier | expected strength |
|---|---|---|
| `F-BFV-RESIDUAL` | certified no-wrap residual | large conjunction/universal folds dominated by additions |
| `F-BFV-BOOL` | canonical encrypted bits | packed Boolean reductions where multiplicative depth is affordable |
| `F-TFHE-BOOL` | TFHE radix/PBS | comparisons, zero tests, negation, and small public LUTs |
| `F-BFV-MPC` | BFV additive body, MPC decision boundary | one equality/comparison at egress instead of many bootstraps |
| `F-TFHE-BASE` | all-TFHE conventional logic | complete but expensive baseline using the same plaintext workload |

## 3. Workload suite

The sizes below are a minimum grid. `S` is formula nodes, `N` a quantified
domain, `W` an integer width, `T` a public function-table size, and `D` nesting
or reduction depth.

### A. Semantic microkernels

1. Equality and inequality at `W = 8, 16, 32, 64`.
2. Homogeneous conjunction and disjunction at
   `N = 1, 2, 4, 16, 64, 256, 1024`.
3. Alternating formulas of equal `S` but depths `D = log2(S)` and `D = S`.
4. Negation over atomic and composite predicates.
5. Bounded `forall` and `exists` at the same `N` grid.

Every row includes all-true, exactly-one-false, exactly-one-true, all-false,
boundary, and adversarial cancellation inputs. These are both functional tests
and measurements of whether early-exit or witness-index optimizations changed
the intended semantics.

### B. Quantified and higher-order kernels

1. Existing `QuantifiedPredicate.allBelowCap`: public and committed vectors,
   `N = 3, 16, 64, 256`, `W = 16, 32`.
2. Existing `QuantifiedPredicate.anyIsFive` on the same sizes.
3. Finite function application for tables `T = 4, 16, 256, 4096` using
   interpolation, one-hot selection, authenticated lookup, and TFHE LUT lanes
   where applicable.
4. Extensional equality of finite functions at the same table sizes.
5. Composition, `map`, and quantified properties over finite functions. The
   report must include the expanded table cardinality; compact syntax is not a
   compact representation theorem.

### C. Transaction-shaped public challenge set

Transcribe the BitLogic paper's stated predicates before correcting them:

1. swap: three simultaneous equalities;
2. AMM update: two balance deltas plus constant-product invariant;
3. loan: signature, collateral-ratio ordering, and expiry ordering;
4. vault: three disjunctive spending paths;
5. inheritance: notarization, time ordering, and non-revocation;
6. dynamic spending limit: ordering or multisig.

For each, publish:

- the original formula and equation;
- an honest accepted witness;
- one mutation per conjunct/branch that must reject;
- a multi-fault witness;
- the corrected typed formula;
- all lane outputs and relation sizes.

This makes the comparison constructive: a participant can correct its compiler
and re-run the same corpus rather than debate prose.

### D. DREGG-native application set

Use real source adapters, not synthetic arithmetic only:

1. `Pred`/`RelPred` transfer conservation and range predicates;
2. bounded authority and committed membership predicates;
3. one cap attenuation policy;
4. one private-market predicate with proof/FHE same-opening;
5. composed batches of `1, 4, 16, 64` predicates.

The first publishable milestone should be `allBelowCap` and `anyIsFive` through
both proof and FHE lowerings, followed by one transaction-shaped workload.

### E. FHE-discriminating set

The FHE suite must contain workloads that help and hurt residual semantics:

1. `forall` of already nonnegative equality residuals, where BFV addition should
   be strong;
2. `exists`/large disjunction, which requires products, zero tests, or PBS;
3. comparisons at several widths, exposing actual radix/PBS cost;
4. mixed transaction predicates;
5. a SIMD packing sweep over slot occupancy;
6. one BFV-additive-then-MPC boundary case.

Without both favorable and unfavorable cases, a geometric-mean speedup is
selection bias.

## 4. Soundness and completeness gates

A lane is excluded from performance summaries until all applicable gates pass.

1. **Source semantics:** a total typed evaluator exists and the workload corpus
   has pinned expected results.
2. **Compiler soundness:** proof acceptance implies the source formula evaluates
   to true. The theorem targets the actual emitted relation/descriptor.
3. **Compiler completeness:** every true source formula in the supported
   fragment has an accepted witness/trace. Unsupported inputs reject explicitly.
4. **Carrier validity:** `D-NOWRAP` proves nonnegativity and bounds every partial
   accumulator; `D-RANDOM` proves and reports its failure probability;
   `D-Q/ZINC` pins projection primes and coefficient/bit-length bounds.
5. **Atom validity:** inequalities use a proved range/decomposition relation;
   nonzero tests bind inverse witnesses; Boolean values are constrained to
   `{0,1}`.
6. **Transcript validity:** all prover-controlled commitments and instance data
   are bound before Fiat--Shamir challenges. Domain separators, retries, and
   repetition count are pinned.
7. **Both polarities:** the suite proves/runs accepted honest cases and rejected
   adversarial cases. Mutation testing removes or corrupts one generated
   constraint and demonstrates that a test goes red.
8. **Differential testing:** at least 10,000 generated small formulas are checked
   against `REF`, with shrinking and retained counterexamples. Exhaustively test
   the smallest finite domains.
9. **Input binding:** public values, commitment openings, and FHE plaintexts are
   tied to one source environment. Proof/FHE agreement without same-opening does
   not pass.
10. **Cryptographic claim gate:** `zk` may be reported only for a hiding proof
    mode with its leakage/public-input manifest and security assumptions. A
    non-hiding FRI proof is still a validity proof, but not a privacy result.
11. **FHE correctness:** decryptions match `REF` over boundary/random vectors;
    noise/no-wrap certificates pass; deliberately undersized parameters fail
    the gate; only declared outputs are opened.

The result schema carries `gate_status`. Tooling must refuse to compute a
speedup when either numerator or denominator has a failing/unknown mandatory
gate.

## 5. Metrics

### 5.1 Semantic/lowering metrics

- source nodes, atom/connective/quantifier counts, quantified cardinality;
- compiler wall/CPU time and peak RSS;
- emitted artifact bytes and coefficient maximum bit length;
- field/modulus, maximum polynomial degree, claimed algebraic failure bound;
- witness variables/cells, public inputs, challenges;
- relation constraints, trace rows, columns, maximum transition/quotient degree,
  lookups, range bits, hash rows, Boolean and multiplication gates;
- preprocessing/setup time and artifact bytes.

Both **unoptimized** and **production-optimized** outputs are retained. A direct
lowering must not be compared to an intentionally unoptimized circuit.

### 5.2 Proof metrics

- reference evaluation and witness generation separately;
- prover cold and warm wall time, total CPU time, peak RSS, and accelerator
  memory;
- verifier wall/CPU time and peak RSS;
- proof bytes and verifier-key/common-data bytes;
- batching throughput and amortized proof/verification cost;
- verifier on-chain gas only when the same chain and verifier contract are used;
- explicit soundness bits, zero-knowledge mode, trusted-setup assumptions, and
  post-quantum status.

Report throughput and latency; neither substitutes for the other. Report failed
proof verification and malformed-proof behavior as robustness results, not
timings hidden from the table.

### 5.3 FHE metrics

- scheme/library/version, parameter identifier, estimated security and failure
  probability;
- plaintext/ciphertext moduli, slots, ciphertext and key bytes;
- encryption, evaluation, threshold-decision, and decryption time separately;
- ciphertext additions, public-scalar and ciphertext multiplications,
  multiplicative depth, rotations, relinearizations, key switches, PBS/LUT
  calls, and radix blocks per comparison;
- analytic and measured noise headroom/no-wrap bound;
- host/device transfers, kernel launches, cold setup, warm resident latency,
  peak host/device memory, single-request latency, and saturated throughput;
- opened outputs and custody/threshold assumptions.

Never import a vendor's primitive PBS speedup as an application speedup. The
application row must be measured end-to-end; vendor primitive numbers may be a
separately labelled calibration.

### 5.4 Deployment/finality metrics

- local admission time, proof-ready time, sequencer inclusion, data-availability
  publication, L1 submission, and consolidated/finalized time as separate
  timestamps;
- batch size, transaction mix, L1/network conditions, and trust model;
- observed p50/p95/p99 over a stated window.

A trusted-sequencer response is not consolidated validity-proof finality. Label
both if both are useful.

## 6. Experimental discipline

1. Pin source commit, compiler/toolchain lockfiles, backend commit, security
   configuration, OS/kernel, CPU microcode, CPU governor, memory, accelerator,
   driver, and environment variables in `META.json`.
2. Use one machine for each paired comparison. Randomize lane order and retain
   thermal/load telemetry. Do not compare a laptop result with a GPU server
   result as an arithmetization delta.
3. Compile release binaries once. Separate compilation/setup from steady-state
   proving. Report first/cold and resident/warm FHE measurements separately.
4. Criterion-style microbenchmarks use warmup plus enough samples for stable
   confidence intervals. Expensive end-to-end proving uses at least 10
   independent runs when feasible. Report median, p95, arithmetic mean, standard
   deviation, and a bootstrap 95% interval; retain every raw sample.
5. Use fixed public test-vector seeds for reproducibility, but obtain protocol
   randomness from the real transcript/RNG. A deterministic fake challenge is
   not a performance optimization.
6. Verify every generated proof and decrypt/check every FHE result inside the
   measured run or in an immediately paired correctness pass. Hash all inputs,
   outputs, proof artifacts, and logs.
7. Mark extrapolations in every table cell and exclude them from headline
   speedups. Timeout/OOM is a censored result, not an invented time.
8. Pre-register the workload/parameter matrix before optimization. Add new
   workloads, but never silently delete a losing case from the aggregate.
9. Compute each paired ratio first. If a suite aggregate is useful, publish the
   geometric mean plus min/max and every constituent ratio. Never publish only
   a ratio of hand-picked totals.
10. Define cost reduction explicitly. For latency,
    `speedup = baseline_time / candidate_time`; for monetary cost, publish the
    pricing date, provider, machine shape, utilization model, and raw runtime.

## 7. Artifact layout

Each captured run should be content-addressed and sufficient for an independent
replay:

```text
logic-bench/<suite-version>/<run-id>/
  META.json
  workloads/<id>.typed-ast.json
  workloads/<id>.inputs.json
  lanes/<lane>/<id>/compile.json
  lanes/<lane>/<id>/relation.json
  lanes/<lane>/<id>/gates.json
  lanes/<lane>/<id>/samples.jsonl
  lanes/<lane>/<id>/proofs/
  lanes/<lane>/<id>/logs/
  summary.json
  SUMMARY.md
```

`gates.json` records theorem names and axiom/lint output for formal lanes, the
counterexample/mutation corpus hash, proof verification counts, and FHE parity
checks. `summary.json` is generated only from raw samples and gate status.

The repository already has much of the measurement infrastructure:

- `perf/benches/` and `perf/scripts/capture-baseline.sh` provide Criterion,
  machine stamps, proof sizes, and saved comparisons over public APIs;
- `perf/benches/turn_witness_vs_proving.rs`, `cohort_circuit.rs`, and
  `recursion_fold.rs` already separate witness, leaf prove/verify, and fold cost;
- `fhegg-fhe/src/bin/bench.rs`, `additive_bench.rs`, `boundary_bench.rs`,
  `gpu_resident_bench.rs`, and `private_book_bfv_wgpu_bench.rs` provide real FHE
  application/per-operation and resident-path harnesses;
- `fhegg-fhe/MEASURED-ENVELOPE.md` is a good disclosure model because it labels
  changed circuits, real runs, extrapolations, host contention, and corrected
  claims.

The new suite should extend `dregg-perf` with public compiler APIs and add a
machine-readable FHE capture wrapper. Heavy captures belong on the build node in
release mode; the default loop remains smoke-sized.

## 8. Evidence levels and public language

Assign every external claim an evidence label:

| level | evidence | permitted wording |
|---|---|---|
| E0 | idea/roadmap | "we are exploring" |
| E1 | precise specification | "we specify" |
| E2 | executable artifact | "we implement" |
| E3 | independently reproducible benchmark | "we measured" |
| E4 | machine-checked semantic/refinement theorem | "we formally verify" (name the theorem and scope) |
| E5 | audited, deployed observation | "in the audited deployment/configuration" |

Do not transfer evidence between layers. A formal lowering theorem (E4) does not
prove cryptographic security, production readiness, or finality; a live RPC (E5
for availability) does not validate a compiler relation.

Responsible comparison language:

- "The public ModulusZK site states a 10--100x cost reduction, but we did not
  find a public workload, prover artifact, parameter set, or raw benchmark from
  which to reproduce that multiplier as of the audit date."
- "The public BitLogic equations are treated as a draft specification. Our
  challenge suite identifies cases that the stated equations accept/reject, and
  supplies corrected alternatives. This is not a claim about author intent."
- "On workload W, commit X, backend/parameters P, and machine H, corrected DREGG
  lowering A used R rows and proved in T milliseconds versus baseline B's R'
  rows and T' milliseconds (ratio Y, 95% interval Z). Both passed the same
  soundness gates."
- "DREGG's advantage is currently semantic assurance and an auditable benchmark
  path; a broad performance advantage remains a hypothesis until the matrix is
  captured."

Avoid "fake", "scam", "orders of magnitude", "same security", "production",
and "surpasses" unless the exact evidence needed by those words is attached.

## 9. Constructive engagement / CULT-facing comparison

Publish the typed workloads, reference results, failure corpus, lane interface,
and raw result schema under a neutral name. Invite ModulusZK/CULT to provide an
`M-IMPL` adapter or corrections to the transcription. Freeze the challenge-set
version before receiving their measurements, run both implementations on the
same host where licensing permits, and offer right-of-reply on factual artifact
descriptions.

The useful public contrast is then:

- ModulusZK's stated design and any evidence its team elects to contribute;
- DREGG's corrected, theorem-scoped designs;
- conventional executable baselines;
- a shared workload suite that makes both wins and costs visible.

That is a stronger marketing asset than a takedown: it turns a disputed slogan
into an open engineering standard, and it leaves a clean path for collaboration
if the Modulus/CULT relationship becomes technically productive.

## 10. Primary public references for the external baselines

- [Gabbay, *Arithmetisation of computation via polynomial semantics for
  first-order logic*](https://eprint.iacr.org/2024/954)
- [ModulusZK public product claims](https://www.moduluszk.io/)
- [Modulus zkEVM architecture documentation](https://docs.moduluszk.io/architecture)
- [ModulusZK BitLogic public repository](https://github.com/ModulusZK/BitLogic-from-Modulus-zkFOL-Bitcoin)
- [Zinc ePrint 2025/316](https://eprint.iacr.org/2025/316)
- [Circom's official R1CS background](https://docs.circom.io/background/background/)
- [snarkjs official repository](https://github.com/iden3/snarkjs)
- [Plonky3 official repository](https://github.com/Plonky3/Plonky3)
- [TFHE-rs official reproducible PBS benchmarks](https://docs.zama.org/tfhe-rs/get-started/benchmarks/gpu/gpu-programmable-bootstrapping)
