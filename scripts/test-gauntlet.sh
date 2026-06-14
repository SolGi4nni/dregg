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
#
# Extra args are forwarded to nextest, e.g.:
#   scripts/test-gauntlet.sh heavy-release -p dregg-circuit
#   scripts/test-gauntlet.sh -p dregg-turn
#
# On the 24-core host, offload via pbuild (rsyncs WIP, isolated lane dir):
#   scripts/pbuild test scripts/test-gauntlet.sh heavy-release
#
# Which suites are "heavy"? (segregated in .config/nextest.toml, all in
# crates under active rewrite, so split by CONFIG only — no source edits):
#   circuit::rotation_batchstark_leaf_smoke          (~342s, 2 folds)
#   turn::proptest_invariants                        (~289s, 5 proptests)
#   circuit lib: k_fold / two_step / three_cell_joint / foreign_circuit_root  (>60s each)
#   circuit::effect_vm_descriptor_cutover_harness    (~43s)
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
  -*)
    # bare flags → default profile (e.g. `test-gauntlet.sh -p dregg-turn`)
    exec cargo nextest run --profile default "$mode" "$@" ;;
  *)
    echo "usage: $0 [default|ci|full|heavy|heavy-release|list-heavy] [nextest args...]" >&2
    exit 2 ;;
esac
