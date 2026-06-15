# dregg performance: benchmarking + profiling harness

This is the **instrument**, not the measurement. The `dregg-perf` crate carries
a criterion bench suite + report binaries over the real hot paths; this doc is
the recipe the perf-engineering lane runs to capture profiles on **persvati**
(the 24-core build node) once the code stabilizes, and the **hot-path map** that
says where to dig.

All benches call the crates' **public APIs** — `dregg-perf` depends on
`circuit` / `turn` / `cell` / `sdk` and never edits them. Every bench is
parameterized **SMOKE vs FULL**:

| regime | switch | inputs | use |
|---|---|---|---|
| SMOKE | default | tiny (1-effect transfer, 8-elem sponge, ...) | `--no-run`, cheap smoke run, CI |
| FULL  | `PERF_FULL=1` | realistic (1/4/16-effect ladder, 64-elem sponge) | the persvati capture run |

The switch is one function: `dregg_perf::perf_full()`.

---

## Bench inventory

`perf/benches/*.rs` (criterion, `harness = false`). The measured numbers these
produce live in **`docs/PERFORMANCE.md`**; this is the index.

| bench | hot path | public API | SMOKE / FULL |
|---|---|---|---|
| `turn_witness_vs_proving` | THE headline contrast: admit vs prove, one turn, every leg | `TurnExecutor::execute`, `generate_effect_vm_trace`, rotated `prove_full_turn` / `verify_full_turn` | 1 turn / amount ladder |
| `turn_proof`     | live rotated full-turn prove **and** verify | rotated `prove_full_turn` / `verify_full_turn` | 1 turn / ladder |
| `prove`          | full rotated turn + the IR-v2 descriptor leg in isolation | `prove_full_turn`, `prove_vm_descriptor2` | 1 turn / ladder |
| `verify`         | rotated full-turn verify (light-client cost) | `verify_full_turn` | 1 turn / ladder |
| `cohort_circuit` | the rotated IR-v2 multi-table batch STARK per effect cohort | `prove_vm_descriptor2` / `verify_vm_descriptor2` | transfer / + map·umem·absent |
| `recursion_fold` | the bundle-tree aggregation fold (N-leaf compress chain) | `prove_tree_fold_v2` / `verify_tree_fold_v2` | 2 leaves / 2·8·32·128 |
| `embedded_commit`| the verified Lean kernel commit (node / seL4-PD hot path) | `shadow_exec_full_forest_auth`, `decode_shadow_verdict` | same input |
| `ui_projection`  | the deos desktop: first-paint data + scene/affordance projection | `demo_world`/`demo_genesis`, `Shell::compose{,_scene}`, `AffordanceSurface::project_for` | same input |
| `executor_turn`  | live Rust executor turn | `TurnExecutor::execute` over a `Ledger` | same input |
| `trace_gen`      | witness gen + descriptor-matrix extension | `generate_effect_vm_trace`, `descriptor_recursion_matrix` | 1-eff / ladder |
| `commitment`     | canonical cell commitment v8 + v9 rotated | `compute_canonical_state_commitment{,_v9}` | same input |
| `poseidon2`      | width-16 permutation + 2→1 + sponge | `Poseidon2State::permute`, `hash_2_to_1`, `hash_many` | sponge 8 / 64 |

> NOTE: the full-turn prove/verify benches drive the LIVE **rotated** path
> (`prove_full_turn` with a real `RotationTurnWitness`). The v1
> `prove_turn_self_sovereign` entry is retired under the `recursion` default — it
> panics "thread a rotation witness" — so the benches build the witness via
> `dregg_turn::rotation_witness::produce` (the `dregg_perf::rotated_transfer_turn`
> helper, mirroring the C1 reference).

Report / microbench binaries (`perf/src/bin/*.rs`):

- `perf-report` — full human-readable map: every prove/verify primitive, the
  descriptor-vs-hand-AIR overhead, the witness-gen-vs-prove split, Merkle
  membership depth scaling, bespoke-stark-vs-p3, the full-turn commit path, and
  silver joint-turn aggregation, with proof sizes. `cargo run --release -p dregg-perf --bin perf-report`.
- `proof-sizes` — wire-byte microbench (regression-tracked): EffectVM hand-AIR,
  descriptor-interp (IR-v2 ~120 KiB), full self-sovereign turn (rotated ~144
  KiB). `--json` for baseline comparison.
- `perf-summary`, `orchestration-demo` — pre-existing report/demo binaries.

Smoke-compile + smoke-run locally:

```sh
cargo bench --no-run -p dregg-perf          # compile every bench (no measurement)
cargo bench -p dregg-perf --bench poseidon2 # cheapest real bench, seconds-scale
```

---

## Capturing profiles (flamegraph / samply)

Profile a **single** prove on a release build (the prover dominates; profile it
in FULL so the flamegraph reflects realistic work):

**cargo-flamegraph** (perf/dtrace under the hood):

```sh
cargo install flamegraph
# Linux (persvati): perf-based. Profile the proof-size microbench (one prove each).
PERF_FULL=1 cargo flamegraph -p dregg-perf --bin proof-sizes -o flame-prove.svg
# Or profile a single criterion bench's measured region:
PERF_FULL=1 cargo flamegraph -p dregg-perf --bench prove -o flame-bench.svg -- --bench
```

On Linux set `kernel.perf_event_paranoid` low enough (or run under sudo) for
`perf record` to sample.

**samply** (cross-platform, opens a Firefox-profiler view; good on macOS):

```sh
cargo install samply
cargo build --release -p dregg-perf --bin proof-sizes
PERF_FULL=1 samply record ./target/release/proof-sizes
```

Profile the **executor turn** (the non-proof path) the same way against the
`executor_turn` bench or a small driver — it is microseconds-scale, so wrap it
in a tight loop before sampling.

---

## Running the suite on persvati

persvati is the 24-core build node; `scripts/pbuild <lane> <cmd...>` rsyncs the
working tree (WIP included, `target/`/`.lake/` excluded) into an isolated lane
dir and runs the command there. The FULL prove benches are minutes-scale — run
them there, not on a laptop.

```sh
# offload the whole FULL suite to persvati:
git push persvati main      # (or rely on pbuild's rsync of the WIP tree)
scripts/pbuild perf 'PERF_FULL=1 cargo bench -p dregg-perf'

# a single bench:
scripts/pbuild perf 'PERF_FULL=1 cargo bench -p dregg-perf --bench prove'

# the wire-size microbench (regression numbers):
scripts/pbuild perf 'cargo run --release -p dregg-perf --bin proof-sizes -- --json'
```

---

## Saving + comparing a baseline (criterion `--save-baseline`)

Criterion's baseline feature is the regression gate. Capture once, compare later:

```sh
# capture (on persvati), names the baseline:
scripts/pbuild perf 'PERF_FULL=1 cargo bench -p dregg-perf -- --save-baseline main-YYYYMMDD'

# later, compare a change against it (criterion prints % deltas + significance):
scripts/pbuild perf 'PERF_FULL=1 cargo bench -p dregg-perf -- --baseline main-YYYYMMDD'
```

The **`perf/scripts/capture-baseline.sh`** script does the full capture in one
idempotent shot: the FULL criterion suite (`--save-baseline <name>`), the
`proof-sizes` JSON, and the `perf-report` text, into `perf/baselines/<name>/`
(gitignored; the committed reference numbers live in this doc). Run it on
persvati:

```sh
scripts/pbuild perf 'perf/scripts/capture-baseline.sh main-YYYYMMDD'
```

---

## Hot-path map — where we expect the time to go (the perf-engineering targets)

Config the numbers are measured against: BabyBear, FRI `log_blowup=3` (8× LDE),
50 queries, 16 PoW bits; the EffectVM AIR is base width 186 + Poseidon2-aux
columns.

Ordered by expected cost, **with why**, so the future lane has a map:

1. **The STARK prover — FRI + the LDE / Merkle commit (dominant).**
   Inside one EffectVM proof the `perf-report` witness-gen-vs-prove split shows
   witness-gen is a small % of prove; **FRI + the low-degree extension + the
   Merkle commitment dominate.** This is the long pole for "how long does a turn
   take to prove." Levers: blowup factor, query count, batching/folding across
   sub-proofs, parallel FRI. Profile target: `prove` / `turn_proof` benches.

2. **In-circuit Poseidon2 (the chip table + every commitment).**
   The rotated IR-v2 path computes **real in-circuit Poseidon2** in the chip
   table (the map-op/cap-root hashes the batch STARK commits). Poseidon2 is also
   the sole hash in the cell commitment — and the cell commitment is a
   measured outlier: the cap-root sorted-Poseidon2 tree costs ~225 ms (v8) /
   ~157 ms (v9), see `docs/PERFORMANCE.md`. Levers: the permutation
   S-box / linear-layer implementation, vectorization, the commitment
   witness-vs-recompute split. Profile target: `poseidon2`, `commitment`,
   `cohort_circuit`.

3. **Trace / witness generation (`generate_effect_vm_trace` + hash extension).**
   Sub-millisecond today and a small fraction of prove — but it is the
   embarrassingly-parallel part and a candidate to overlap with proving.
   Profile target: `trace_gen`.

4. **Proof VERIFY (the light-client cost).**
   Much cheaper than prove, but it is the cost a **light client / cross-fed
   peer** pays per turn, so it is tracked separately. Levers live in the FRI
   query count and proof size. Profile target: `verify`.

5. **Recursive aggregation FOLD (the bundle-tree compress chain).**
   The fold collapses N per-participant digests into one aggregate root; cost
   scales with fan-out. Measured: ~10 ms prove / ~2.4 ms verify for 2 leaves
   (`recursion_fold` bench). The rotated full-turn prove (~147 ms) wraps the
   ~52 ms descriptor leg in the recursion-binding proof — that wrap, not the leaf,
   is the majority of per-turn prove cost. Profile target: `recursion_fold`,
   `cohort_circuit` (the leaf), `turn_proof` (the wrapped whole).

6. **The executor turn (non-proof path).**
   `TurnExecutor::execute` — state lookup, authorization gating, effect
   application, receipt + commitment. Microseconds-scale and not the bottleneck,
   but it is on the latency path of *every* turn (proven or not), so it is
   tracked to catch a regression. Profile target: `executor_turn`.

### Tracked wire sizes (regression reference)

The `proof-sizes` microbench tracks the figures the docs cite:

- descriptor-interp (IR-v2) proof ≈ **120 KiB**
- rotated full self-sovereign turn proof ≈ **144 KiB**

Capture the actual JSON on persvati and diff it against the previous baseline to
catch a size regression.

---

## Discipline

- `dregg-perf` owns these benches; it **depends on** the crates under test and
  calls their public APIs. Never edit `circuit/`, `turn/`, `cell/`, `sdk/` from
  here.
- Add deps to `perf/Cargo.toml` only.
- SMOKE is the default everywhere so `--no-run` and CI stay cheap; FULL is the
  deliberate persvati capture (`PERF_FULL=1`).
- The heavy FULL benches run on persvati, not laptops.
