#!/usr/bin/env bash
set -euo pipefail

# One discoverable gate for the Path of Angels braid.  `source` proves every
# component that does not require a completed deployment ceremony.  `release`
# additionally reproduces the post-genesis Lean bundle, authenticates its
# curator epoch, stages those exact bytes into the web surface, and runs the
# actual-bundle hostile tests.

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
mode="${1:-source}"

case "$mode" in
  source|release) ;;
  *)
    echo "usage: scripts/test-poa.sh [source|release]" >&2
    exit 2
    ;;
esac

run() {
  echo "+ $*"
  "$@"
}

cd "$repo_root"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

(
  cd metatheory
  run lake build Dregg2.Games.PathOfAngels.Canon
  run lake build Dregg2.Games.PathOfAngels.Emit
)
run bash -n scripts/check-poag1-artifacts.sh

run cargo nextest run --manifest-path poa-curator/Cargo.toml
run node --test scripts/tests/poa-devnet-manifest.test.mjs

# The explicit feature and target are deliberate: without them Cargo discovers
# zero PoA ingress tests while returning success.
run cargo nextest run -p dreggnet-market --features poa-expedition \
  --test poa_expedition_ingress

(
  cd extension
  run npm run typecheck
  run npm test
  run npm run test:dregg-poa
  run npm run build
  run npm run validate:extension-package
)

run node --check poa-web/src/app.js
run node --check poa-web/src/poag1.js
run node --check poa-web/src/content-epoch.js
run node --check poa-web/src/signal-runtime.js
run node --check poa-web/scripts/sync-artifacts.mjs
run node --check poa-web/serve.mjs
run node --test poa-web/tests/content-epoch.test.mjs poa-web/tests/csp.test.mjs

if [ "$mode" = release ]; then
  : "${POA_ROOT:?POA_ROOT must name the staged PoA genesis root}"
  : "${POA_CONTENT_EPOCH:?POA_CONTENT_EPOCH is the external release pin}"
  : "${POA_CURATOR_COUNTER:?POA_CURATOR_COUNTER is the external release pin}"
  run scripts/check-poag1-artifacts.sh check
  (
    cd poa-web
    run npm run artifacts
    run npm test
  )
fi

echo "Path of Angels $mode gate: PASS"
