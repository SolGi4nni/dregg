#!/usr/bin/env bash
# smoke-web-surface.sh — the N13 web-killer-demo verification (build + headless).
#
# Verifies "TWO TABS, ONE SURFACE, the share that REFUSES" (the web evaluation
# artifact, docs/FRONTIER-ROADMAP.md §4 web cut + docs/WEB-FORWARD-EVERYWHERE.md
# N13) end-to-end in a REAL headless browser against the BUILT dist:
#
#   1. Builds site/dist in Docker (node + browsers via the Playwright image) —
#      npm/node never run on the host.
#   2. Serves dist and runs two Playwright tests against it:
#        * tests/web-surface-demo.mjs           — the surface state machine:
#            open → read-only share → the GENUINE over-share DelegationDenied →
#            revoke darks the glass → the ⚠ banner at the pixel layer → the
#            in-tab verify_history anchor discipline.
#        * tests/web-surface-proving-worker.mjs — the off-thread proving Worker +
#            verify_devnet_history config-not-artifact discipline + responsiveness.
#
# The drift gate for the generated Studio catalogs is SKIPPED here
# (SKIP_CATALOG_DRIFT_CHECK=1): this is a web-lane verification build, and the
# catalog↔Lean drift (when present) is a metatheory-lane concern, not a web one.
# CI (`.github/workflows/pages.yml`) builds WITHOUT the skip and is the gate for
# catalog freshness.
#
# Usage:   scripts/smoke-web-surface.sh
# Env:     PW_IMAGE   (default mcr.microsoft.com/playwright:v1.60.0-noble)
#          PORT       (default 8099)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PW_IMAGE="${PW_IMAGE:-mcr.microsoft.com/playwright:v1.60.0-noble}"
PORT="${PORT:-8099}"

echo "=== web-surface N13 smoke — image=$PW_IMAGE port=$PORT ==="

docker run --rm \
  -e SKIP_CATALOG_DRIFT_CHECK=1 \
  -e "PORT=$PORT" \
  -v "$ROOT":/work -w /work/site \
  "$PW_IMAGE" sh -ec '
    echo "=== npm ci (linux node_modules) ==="
    npm ci >/tmp/npm-ci.log 2>&1 || { tail -30 /tmp/npm-ci.log; exit 1; }

    echo "=== node build.js (site/dist) ==="
    node build.js 2>&1 | tail -6

    echo "=== serve dist on :$PORT ==="
    npx serve dist -l "$PORT" >/tmp/serve.log 2>&1 &
    SERVE_PID=$!
    for i in $(seq 1 40); do
      if wget -q -O /dev/null "http://localhost:$PORT/playground/" 2>/dev/null; then break; fi
      sleep 0.5
    done

    RC=0
    echo "=== tests/web-surface-demo.mjs ==="
    PLAYGROUND_BASE="http://localhost:$PORT" node tests/web-surface-demo.mjs || RC=$?
    echo "=== tests/web-surface-proving-worker.mjs ==="
    PLAYGROUND_BASE="http://localhost:$PORT" node tests/web-surface-proving-worker.mjs || RC=$?

    kill $SERVE_PID 2>/dev/null || true
    exit $RC
  '

echo "=== web-surface N13 smoke: GREEN ==="
