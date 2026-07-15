#!/usr/bin/env bash
# test-gauntlet.sh — the Rust test gauntlet, split into a FAST default and an
# on-demand HEAVY suite via cargo-nextest profiles (see .config/nextest.toml).
#
# The default workspace gauntlet is kept fast by SEGREGATING the minute-scale
# recursion / IVC / fold / proptest suites out of the `default`/`ci` nextest
# profiles' `default-filter`. They are NOT deleted — they run on demand here.
#
#   scripts/test-gauntlet.sh                # fast default (heavies excluded)
#   scripts/test-gauntlet.sh heavy          # ONLY the heavy suite (debug; minutes)
#   scripts/test-gauntlet.sh heavy-release  # ONLY the heavy suite, --release (recommended)
#   scripts/test-gauntlet.sh full           # EVERYTHING (default + heavy), one shot
#   scripts/test-gauntlet.sh ci             # default coverage, fail-fast
#   scripts/test-gauntlet.sh armed          # THE ARMED TEETH: the #[ignore]d suite, --release
#   scripts/test-gauntlet.sh gpu            # THE GPU LANE: the #[ignore]d GPU teeth (needs an adapter)
#
# ── THE ARMED LANE (`armed`) ────────────────────────────────────────────────
# "Expensive" must mean "runs nightly", never "runs never." A large set of this
# tree's most adversarial tests are `#[ignore]`d because they are minute-scale
# REAL recursion folds — and NOTHING ran them: `cargo test --workspace` (ci.yml)
# never runs ignored tests, and nothing here passed `--ignored` either. All 8
# `circuit-prove/tests/*_binding_deployed_tooth.rs` — the DEPLOYED light-client
# binding teeth, each forging a specific witness and requiring the fold to refuse
# it — were dead in automation. They were documentation.
#
# `armed` runs them: `--run-ignored ignored-only`, `--release` (debug is the
# dominant slowness in a fold). It is the nextest twin of
# `cargo test -- --ignored`, and it is what .github/workflows/armed-teeth.yml
# runs on a schedule.
#
# The GPU teeth are EXCLUDED from `armed` and get their own `gpu` mode: they
# fail CLOSED on a missing adapter (they assert `adapter_available()`), so
# running them on a GPU-less box is a guaranteed red that says nothing about the
# code. That is the one law: `#[ignore]` so a GPU-less runner skips explicitly,
# hard assert so an opted-in lane can never hollowly pass.
#
# Extra args are forwarded to nextest.
#
# ⚠ DO NOT PASS `-p` (this header used to recommend it, and it does not work).
# The nextest profiles name specific test binaries via `binary(...)`, and nextest
# validates EVERY profile's filterset against the binaries in scope on every
# invocation. Narrowing scope with `-p dregg-circuit` makes the out-of-scope names
# (e.g. `binary(proptest_invariants)`, which lives in dregg-turn) unresolvable, and
# nextest then hard-errors and runs NOTHING — regardless of which profile you asked
# for. To narrow, use a filterset instead:
#   scripts/test-gauntlet.sh heavy-release -E 'package(dregg-circuit)'
#   scripts/test-gauntlet.sh -E 'package(dregg-turn)'
#
# On the 24-core host, offload via pbuild (rsyncs WIP, isolated lane dir):
#   scripts/pbuild test scripts/test-gauntlet.sh heavy-release
#
# Which suites are "heavy"? (segregated in .config/nextest.toml, all in
# crates under active rewrite, so split by CONFIG only — no source edits):
#   circuit::rotation_batchstark_leaf_smoke          (~342s, 2 folds)
#   turn::proptest_invariants                        (~289s, 5 proptests)
#   circuit lib: k_fold / two_step / three_cell_joint / foreign_circuit_root  (>60s each)
#   circuit::descriptor_leaf_recursion               (~28s)
set -euo pipefail
cd "$(dirname "$0")/.."

mode="${1:-default}"
[ $# -gt 0 ] && shift || true

case "$mode" in
  default|"")    exec cargo nextest run --profile default "$@" ;;
  ci)            exec cargo nextest run --profile ci      "$@" ;;
  full)          exec cargo nextest run --profile full    "$@" ;;
  heavy)         exec cargo nextest run --profile heavy   "$@" ;;
  heavy-release) exec cargo nextest run --profile heavy --release "$@" ;;
  list-heavy)    exec cargo nextest list --profile heavy  "$@" ;;
  armed)         exec cargo nextest run --profile armed --release --run-ignored ignored-only "$@" ;;
  list-armed)    exec cargo nextest list --profile armed --run-ignored ignored-only "$@" ;;
  gpu)           exec cargo nextest run --profile gpu   --release --run-ignored ignored-only "$@" ;;
  list-gpu)      exec cargo nextest list --profile gpu   --run-ignored ignored-only "$@" ;;
  -*)
    # bare flags → default profile (e.g. `test-gauntlet.sh -p dregg-turn`)
    exec cargo nextest run --profile default "$mode" "$@" ;;
  *)
    echo "usage: $0 [default|ci|full|heavy|heavy-release|armed|gpu|list-heavy|list-armed|list-gpu] [nextest args...]" >&2
    exit 2 ;;
esac
