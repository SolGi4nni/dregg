#!/usr/bin/env bash
# check-lean-marshal.sh — the Lean↔Rust FAITHFULNESS gate against the live Lean FFI
# kernel. Two legs, because serialization round-trip is NOT faithfulness:
#   (1) T8/T9 marshaller round-trip   (`dregg-lean-ffi` marshal_roundtrip binary) —
#       WireState serialization survives the Lean boundary.
#   (2) DENOTATIONAL differential     (`dregg-exec-lean` tests) — the
#       verified Lean executor RUN as the state producer AGREES with the Rust
#       executor on full post-state + root (eval agreement, not just bytes). This is
#       the canonical check the byte-identity differential could not make; without it
#       a Lean↔Rust *evaluation* divergence would go uncaught.
#
# Requires `dregg-lean-ffi/libdregg_lean.a`. Get one in MINUTES with
# `scripts/fetch-lean-seed.sh` (a CI-published seed release), or build one locally with
# `./scripts/bootstrap.sh`.
#
# THE SKIP IS A LIE DETECTOR, NOT A PASS. When the archive is absent this script has checked
# NOTHING — there is no live Lean kernel to be faithful to. It still exits 0 by default so a
# developer running the whole script set on a marshal-only checkout is not blocked. But a CI job
# that means to ASSERT faithfulness must set:
#
#     DREGG_REQUIRE_LEAN_GATE=1
#
# which turns the absent archive into a FAILURE. Without this, the gate is a checkmark that is
# structurally incapable of being red — it reports the same green whether the Lean↔Rust executors
# agree or whether nobody looked. ci.yml's lean-marshal-gate sets it (and fetches a seed first).
#
# Usage:  scripts/check-lean-marshal.sh
# Exit:   0 = gate passed (or skipped, when NOT armed); nonzero = failure, or armed-but-unseeded.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_LIB="$ROOT/dregg-lean-ffi/libdregg_lean.a"

# Accept 1/true/yes/on, case-insensitively; anything else (incl. unset) leaves the gate unarmed.
armed=0
case "$(printf '%s' "${DREGG_REQUIRE_LEAN_GATE:-}" | tr '[:upper:]' '[:lower:]')" in
  1|true|yes|on) armed=1 ;;
esac

if [ ! -f "$LEAN_LIB" ]; then
  if [ "$armed" -eq 1 ]; then
    echo "check-lean-marshal: FAIL — DREGG_REQUIRE_LEAN_GATE=1 but there is no Lean archive." >&2
    echo "  Expected: $LEAN_LIB" >&2
    echo "  This gate asserts the VERIFIED Lean executor and the Rust executor AGREE. With no" >&2
    echo "  archive there is no Lean executor to compare against, so a green here would mean" >&2
    echo "  nothing. Fetch a CI-published seed:  scripts/fetch-lean-seed.sh" >&2
    echo "  (or build one locally:  ./scripts/bootstrap.sh)" >&2
    exit 1
  fi
  echo "check-lean-marshal: SKIP — Lean static lib not built. NOTHING WAS CHECKED."
  echo "  Expected: $LEAN_LIB"
  echo "  Get one in minutes: scripts/fetch-lean-seed.sh   (or: ./scripts/bootstrap.sh)"
  echo "  To make this absence a FAILURE instead of a skip: DREGG_REQUIRE_LEAN_GATE=1"
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
  cargo test -p dregg-exec-lean \
    --test lean_state_producer_differential \
    --test lean_state_producer_widen
)

echo "check-lean-marshal: running the lean-lib runtime probes (leg 3: embeddable + overspend)..."
(
  # The two whole-file `#![cfg(feature = "lean-lib")]` integration tests in
  # dregg-lean-ffi (tests/embeddable_runtime_probe.rs, tests/overspend_probe.rs)
  # link the archive at RUN time — which is exactly why they were gated. Before
  # this leg NO CI step built them: the marshal gate built the `marshal_roundtrip`
  # BINARY under `--features lean-lib`, but `cargo build/run --bin` never compiles
  # test targets, so both probes sat dark on every run. They belong here — inside
  # the archive-present block, so they only execute when a real Lean kernel exists
  # to probe (embeddable_runtime_probe measures no-alloc-override / single-thread /
  # real-turn against the linked image; overspend_probe checks the GATED executor
  # rejects an overspend under unchecked-auth on the shadow marshal shape).
  cd "$ROOT"
  cargo test -p dregg-lean-ffi --features lean-lib \
    --test embeddable_runtime_probe \
    --test overspend_probe
)

echo "check-lean-marshal: PASS — Lean↔Rust faithfulness gate green (serialization + eval agreement + runtime probes)."