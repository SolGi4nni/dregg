#!/usr/bin/env bash
# check-lean-marshal.sh — CI gate for the T8/T9 marshaller round-trip against the
# live Lean FFI kernel (`dregg-lean-ffi` marshal_roundtrip binary).
#
# Requires `dregg-lean-ffi/libdregg_lean.a` (produced by
# `dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh`). When the archive is absent
# the script skips gracefully so CI without a Lean build still passes.
#
# Usage:  scripts/check-lean-marshal.sh
# Exit:   0 = gate passed or skipped; nonzero = build or round-trip failure.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_LIB="$ROOT/dregg-lean-ffi/libdregg_lean.a"

if [ ! -f "$LEAN_LIB" ]; then
  echo "check-lean-marshal: SKIP — Lean static lib not built."
  echo "  Expected: $LEAN_LIB"
  echo "  Build first: dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh"
  exit 0
fi

echo "check-lean-marshal: building marshal_roundtrip (Lean lib present)..."
(
  cd "$ROOT"
  cargo build --release -p dregg-lean-ffi --bin marshal_roundtrip
)

echo "check-lean-marshal: running marshal_roundtrip gate..."
(
  cd "$ROOT"
  cargo run --release -p dregg-lean-ffi --bin marshal_roundtrip --quiet
)

echo "check-lean-marshal: PASS — marshaller round-trip gate green."