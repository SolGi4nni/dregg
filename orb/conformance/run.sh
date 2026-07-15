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
  # The keep-alive HTTP/2 conformance host over the verified engine (the parity
  # harness's h2spec target). Links libdrorb.a; SKIPs the h2 group if absent.
  bash conformance/h2c-host/build.sh || echo "note: h2c-host build failed — parity h2 group will SKIP"
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
echo "-- driving scenarios (base suite: what is wired into the running serve) --"
python3 "$HERE/driver.py"

echo
echo "-- driving scenarios (parity harness: the reference test suites' catalogue) --"
# The parity harness ports the reference suites' scenario catalogue (PARITY-LEDGER
# §4) and drives drorb's real binaries so, scenario for scenario, drorb passes iff
# the reference asserts the same behaviour. It manages its own servers on its own
# ports, so it runs after the base suite without colliding. h2spec (Homebrew/go)
# is used for the HTTP/2 conformance group; the group SKIPs cleanly without it.
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-$HACL_DIST}"
python3 "$HERE/parity.py"

echo
echo "-- GATING suite: information-disclosure leak-scan (a leak FAILS the run) --"
# Unlike the driver/parity tables above — DIAGNOSTICS whose UNWIRED/FAIL rows are
# findings, not build failures — this is a HARD GATE. The leak-scan battery drives
# every route x every leak-class (request-byte reflection, internal/debug headers,
# stack-trace/source leaks, version banners) against a freshly launched serve and
# exits nonzero the moment any response discloses one. Under `set -e` that nonzero
# aborts this script, so a header/body leak fails CI — the same gating character as
# the RFC extended suite's harness-error exit, now covering info-disclosure too.
#
# It launches and reaps its OWN dedicated serve on DRORB_LEAK_PORT (default 18990),
# disjoint from the ports the base/parity suites bound above, so it never collides;
# override DRORB_LEAK_PORT if 18990 is taken on this host.
export DRORB_LEAK_PORT="${DRORB_LEAK_PORT:-18990}"
python3 "$HERE/leak_scan.py" --port "$DRORB_LEAK_PORT"
echo "-- leak-scan gate: clean (no route disclosed an internal artifact) --"

echo
echo "-- GATING suite: dual-path conformance + leak scan (BOTH serve paths) --"
# A HARD GATE across BOTH deployment serve paths: the default conformantServe path
# and the effect/continuation seam (DRORB_EFFECT_SEAM=1). dual_path.sh drives the
# core/extended/full RFC probes AND the info-disclosure leak-scan against EACH path
# on its own dedicated ports, and exits nonzero if EITHER path has a failing check
# or a disclosed leak, OR if the two paths DIVERGE check-for-check. Under `set -e`
# that nonzero aborts the run. This catches the class the single-path leak gate
# above cannot: a gap or disclosure that hides on one serve path but not the other
# (a leak that hid on the other path; a path-divergent framing/robustness bug). It
# reaps only the serves it launches, on ports disjoint from the leak-scan gate.
export DUAL_BASE_PORT="${DUAL_BASE_PORT:-18992}"
bash "$HERE/dual_path.sh"
echo "-- dual-path gate: clean (both serve paths agree, no leaks on either) --"
