# Running the Rust test gauntlet

The workspace tests run under [`cargo-nextest`](https://nexte.st). The default
gauntlet is kept **fast** by segregating a handful of minute-scale
recursion / IVC / fold / proptest suites out of the default run. They are not
deleted — they run **on demand**.

## Fast default (what you run normally)

```sh
cargo nextest run --profile default      # or: scripts/test-gauntlet.sh
```

This excludes the heavy suites (below) and the standing kimchi/preflight
quarantine. A straggler is flagged at 45s; nothing is auto-killed before 180s.

`cargo nextest` does **not** run doctests. Run those separately with
`cargo test --doc` (or `--doc -p <crate>`).

## Heavy suite (on demand)

```sh
cargo nextest run --profile heavy --release   # recommended (debug is the slow part)
cargo nextest run --profile heavy             # debug; takes minutes
# or:
scripts/test-gauntlet.sh heavy-release
```

`--profile heavy` runs **only** the segregated heavy tests (the inverse of the
default filter), bounded to 4 test threads since the folds are CPU/memory-heavy.
Debug builds are the dominant cost for these proving/folding tests, so prefer
`--release`.

On the 24-core host, offload via `pbuild`:

```sh
scripts/pbuild test scripts/test-gauntlet.sh heavy-release
```

## Everything at once

```sh
cargo nextest run --profile full         # default + heavy, no filter, be patient
```

## The heavy set

All heavy suites live in crates under active rewrite, so they are split by
**nextest config only** (`.config/nextest.toml`) — never by editing their
source. Durations are from a reference debug gauntlet:

| Suite | Crate | ~debug time | Why |
|---|---|---|---|
| `rotation_batchstark_leaf_smoke` | circuit | ~342s (2 tests) | batch-STARK leaf fold + wrap |
| `proptest_invariants` | turn | ~289s (5 tests) | proptest invariant sweeps |
| `k_fold_turn_chain_proves_and_verifies` | circuit (lib) | >60s | k-fold IVC chain |
| `two_step_inductive_core_proves_and_verifies` | circuit (lib) | >60s | 2-step inductive fold |
| `three_cell_joint_turn_recursive_proves_and_verifies` | circuit (lib) | >60s | 3-cell joint recursive turn |
| `foreign_circuit_root_is_refused_by_vk_pin` | circuit (lib) | >60s | shares the fold setup |
| `effect_vm_descriptor_cutover_harness` | circuit | ~43s (13 tests) | descriptor cutover differential |
| `descriptor_leaf_recursion` | circuit | ~28s (1 test) | descriptor leaf prove + wrap |

The four circuit *library* tests are filtered by name (their binary holds ~960
fast tests we keep); the four integration suites are filtered whole-binary.

Already `#[ignore]`'d minute-scale tests (skipped by default anyway, run with
`--run-ignored all`): `proof_economics.rs::t3_ivc_root_k2` / `t3_ivc_root_k3`.

## Profiles

| Profile | What | When |
|---|---|---|
| `default` | fast; heavies + quarantine excluded | local dev |
| `ci` | same coverage as `default`, fail-fast | CI |
| `heavy` | **only** the heavy suite | on demand (prefer `--release`) |
| `full` | everything, no filter | full sweep |

See `.config/nextest.toml` for the exact filters.
