#!/usr/bin/env bash
# check-lean-marshal.sh — the Lean↔Rust FAITHFULNESS gate against the live Lean FFI
# kernel. Two legs, because serialization round-trip is NOT faithfulness:
#   (1) T8/T9 marshaller round-trip   (`dregg-lean-ffi` marshal_roundtrip binary) —
#       WireState serialization survives the Lean boundary.
#   (2) DENOTATIONAL differential     (`dregg-turn --features lean-shadow`) — the
#       verified Lean executor RUN as the state producer AGREES with the Rust
#       executor on full post-state + root (eval agreement, not just bytes). This is
#       the canonical check the byte-identity differential could not make; without it
#       a Lean↔Rust *evaluation* divergence would go uncaught.
#
# Requires `dregg-lean-ffi/libdregg_lean.a` (produced by
# `dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh`). When the archive is absent
# the script skips gracefully so CI without a Lean build still passes.
#
# Usage:  scripts/check-lean-marshal.sh
# Exit:   0 = gate passed or skipped; nonzero = build or differential failure.
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
  cargo build --release -p dregg-lean-ffi --features lean-lib --bin marshal_roundtrip
)

echo "check-lean-marshal: running marshal_roundtrip gate (leg 1: serialization)..."
(
  cd "$ROOT"
  cargo run --release -p dregg-lean-ffi --features lean-lib --bin marshal_roundtrip --quiet
)

echo "check-lean-marshal: running the DENOTATIONAL differential (leg 2: eval agreement)..."
(
  cd "$ROOT"
  cargo test -p dregg-turn --features lean-shadow \
    --test lean_state_producer_differential \
    --test lean_state_producer_widen
)

echo "check-lean-marshal: PASS — Lean↔Rust faithfulness gate green (serialization + eval agreement)."