#!/usr/bin/env bash
# Executable conformance suite for the drorb network orchestrator.
#
# Builds the real binaries, then drives them with real clients and emits a
# PASS / FAIL / UNWIRED / SKIPPED verdict per scenario. This is a DIAGNOSTIC of
# what is actually wired into the running serve path — UNWIRED results are the
# valuable output, not a failure.
#
# One command: builds + runs + prints the table. Re-runnable.
#
#   conformance/run.sh
#
# Environment:
#   HACL_DIST   HACL*/EverCrypt gcc-compatible dist (default
#               $HOME/src/hacl-star/dist/gcc-compatible). Required to link the
#               crypto seam the JWT/QUIC paths reach.
#   SKIP_BUILD  set to 1 to skip the build step and only run scenarios.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="$HACL_DIST:${LIBRARY_PATH:-}"

echo "== drorb conformance suite =="
echo "repo:      $ROOT"
echo "HACL_DIST: $HACL_DIST"

if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo
  echo "-- building binaries (this is the slow part; re-run with SKIP_BUILD=1 to skip) --"
  # The stdin one-shot core and the native multi-protocol/QUIC socket servers.
  lake build orb orb-mac-multi orb-quic
  # The proven serve as a static archive, then the Rust dataplane host that links it.
  bash ffi/build-dataplane-lib.sh
  ( cd crates/dataplane && cargo build --release )
  # The live reverse-proxy upstream backends the proxy/fabric scenarios forward to.
  # Without these there is no real backend socket and those scenarios stay UNWIRED.
  ( cd crates/dataplane && cargo build --release --example proxy_backend )
fi

# aioquic client for the QUIC/H3 scenarios (optional; scenarios SKIP without it).
QUIC_VENV="${QUIC_VENV:-/tmp/drorb-conf-qv}"
export QUIC_PYTHON=""
if command -v python3 >/dev/null 2>&1; then
  if [ ! -x "$QUIC_VENV/bin/python" ]; then
    echo
    echo "-- creating aioquic venv at $QUIC_VENV --"
    python3 -m venv "$QUIC_VENV"
    "$QUIC_VENV/bin/pip" install -q --upgrade pip >/dev/null 2>&1 || true
    "$QUIC_VENV/bin/pip" install -q aioquic >/dev/null 2>&1 || true
  fi
  if "$QUIC_VENV/bin/python" -c "import aioquic" >/dev/null 2>&1; then
    export QUIC_PYTHON="$QUIC_VENV/bin/python"
  else
    echo "note: aioquic unavailable — QUIC/H3 scenarios will report SKIPPED"
  fi
fi

echo
echo "-- driving scenarios --"
exec python3 "$HERE/driver.py"
