#!/usr/bin/env bash
set -euo pipefail

# One discoverable gate for the Path of Angels braid.  `source` proves every
# component that does not require a completed deployment ceremony.  `release`
# additionally reproduces the post-genesis Lean bundle, authenticates its
# curator epoch, stages those exact bytes into the web surface, and runs the
# actual-bundle hostile tests.
# It does not claim that N=2 admission is live, authenticate NetworkJudge's
# caller, construct Dark Bazaar's private authorization, or smoke a promoted
# public deployment; each remains a separate fail-closed runtime/infra gate.

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

poa_lean_targets=(
  Dregg2.Games.PathOfAngels.Core
  Dregg2.Games.PathOfAngels.PlayerCounters
  Dregg2.Games.PathOfAngels.SignalTriangulation
  Dregg2.Games.PathOfAngels.RelayRepair
  Dregg2.Games.PathOfAngels.SalvageLock
  Dregg2.Games.PathOfAngels.FiniteTables
  Dregg2.Games.PathOfAngels.Judged
  Dregg2.Games.PathOfAngels.Canon
  Dregg2.Games.PathOfAngels.Emit
  Dregg2.Games.PathOfAngels.DailyMission
  Dregg2.Games.PathOfAngels.BlackBoxReconstruction
  Dregg2.Games.PathOfAngels.ContainmentInspection
  Dregg2.Games.PathOfAngels.DeckGraph
  Dregg2.Games.PathOfAngels.AssistProfile
  Dregg2.Games.PathOfAngels.DarkBazaar
  Dregg2.Games.PathOfAngels.FieldArchive
  Dregg2.Games.PathOfAngels.NetworkJudgeWire
  Dregg2.Games.PathOfAngels.NetworkJudge
)
run env AXIOM_GUARD_TARGETS="${poa_lean_targets[*]}" \
  scripts/axiom-hygiene-guard.sh "$repo_root"
run bash -n scripts/check-poag1-artifacts.sh

run cargo nextest run --manifest-path poa-curator/Cargo.toml
run node --test scripts/tests/poa-devnet-manifest.test.mjs
run node --test scripts/tests/poa-follower-package.test.mjs
run cargo nextest run -p dregg-node \
  -E 'test(/deployment_domain/) or test(/poa_strand_admission/)'

# The explicit feature and target are deliberate: without them Cargo discovers
# zero PoA ingress tests while returning success.
run cargo nextest run -p dreggnet-market --features poa-expedition \
  --test poa_expedition_ingress
run cargo nextest list -p dreggnet-market --features private-attested-clearing \
  --test poa_dark_bazaar_protocol

# Both poles of the native boundary are required. The first executes the real
# linked Lean export; the second proves archive absence is a named refusal and
# never silently selects a Rust judge.
run cargo nextest run -p dregg-lean-ffi --features lean-lib \
  --test poa_signal_judge_probe
run cargo nextest run -p dregg-lean-ffi --features no-lean-link --lib \
  -E 'test(/poa_ffi::tests::/)'

(
  cd extension
  run npm run typecheck
  run npm test
  run npm run test:dregg-poa
  run npm run build
  run npm run validate:extension-package
)

for source in poa-web/src/*.js; do
  run node --check "$source"
done
run node --check poa-web/scripts/sync-artifacts.mjs
run node --check poa-web/serve.mjs
run node --test poa-web/tests/*.test.mjs

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
