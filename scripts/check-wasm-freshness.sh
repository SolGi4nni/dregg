#!/usr/bin/env bash
# GATE: refuse a browser wasm bundle that does not match the source it is supposed to
# have been built from.
#
# THE WOUND THIS CLOSES
# ---------------------
# 2026-07-25: `/descent/play` — the flagship "Play" CTA — was serving a bundle built
# 2026-07-20 21:46. In between, ten commits touched `wasm/src`, four of them
# `bindings_native_descent.rs`, and the descent portable-record WIRE went v1 -> v3
# (`daySeedHex` in v2, `completion.bankedNotes` in v3). The served bundle exported v1
# envelopes; `/descent/native/submit` refuses anything that is not
# `native_descent_wire::PORTABLE_VERSION`. So every settled run from the hero CTA was
# rejected, silently, for five days.
#
# `descent_play.rs`'s module doc said "Missing/STALE wasm fails closed with a visible
# notice." Missing did (an honest 503, and it has a test). STALE did not exist at all —
# no mtime, no hash, no manifest, no comparison, anywhere in the tree. A documented
# wound is not a detected one, and a gate that cannot go red is not a gate.
#
# WHAT IT CHECKS
#   1. the provenance record exists at all (a bundle built by any path that does not
#      record provenance is REFUSED — there is no "assume fresh" fallback);
#   2. the artifact on disk still hashes to what the build recorded (a hand-patched or
#      half-copied `pkg/` is caught);
#   3. the wasm32 source closure hashes to what the build recorded (the actual
#      staleness check — see `scripts/wasm-source-fingerprint.sh` for exactly what is
#      in that closure and why it errs toward false-STALE).
#
# USAGE
#   scripts/check-wasm-freshness.sh                 # check ./wasm/pkg
#   scripts/check-wasm-freshness.sh <asset-dir>     # check a vendored/deployed dir
#                                                   # (e.g. $DESCENT_PLAY_ASSET_DIR)
#
# Exit 0 = current. Exit 1 = STALE / unverifiable. Run it in CI and in the deploy, and
# let it fail the deploy — that is the whole point.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIR="${1:-$ROOT/wasm/pkg}"
PROV="$DIR/dregg-wasm-provenance.json"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  else shasum -a 256 "$1" | awk '{print $1}'; fi
}

jget() { python3 -c 'import json,sys;print(json.load(open(sys.argv[1])).get(sys.argv[2],""))' "$1" "$2"; }

fail() { echo; echo "WASM FRESHNESS: RED — $*" >&2; exit 1; }

echo "=== wasm freshness gate ==="
echo "artifact dir: $DIR"

[ -d "$DIR" ] || fail "no such directory: $DIR"

if [ ! -f "$PROV" ]; then
  cat >&2 <<EOF

WASM FRESHNESS: RED — no provenance record at
  $PROV

This bundle was NOT produced by \`scripts/build-web-artifacts.sh\`, so there is nothing
to compare it against and NO WAY to tell whether it is current. That is exactly the
state \`/descent/play\` was in on 2026-07-25 while serving a five-day-old wire.

Rebuild it:  bash scripts/build-web-artifacts.sh
EOF
  exit 1
fi

recorded_src="$(jget "$PROV" source_sha256)"
recorded_wasm="$(jget "$PROV" wasm_sha256)"
built_at="$(jget "$PROV" built_at)"
git_head="$(jget "$PROV" git_head)"
[ -n "$recorded_src" ] || fail "provenance record has no source_sha256 (corrupt or an older schema)"

echo "built at:     ${built_at:-<unrecorded>}  (git ${git_head:-<unrecorded>})"

# (2) the artifact still IS what was built.
blob="$DIR/dregg_wasm_bg.wasm"
[ -f "$blob" ] || fail "provenance exists but $blob does not — a half-copied artifact dir"
actual_wasm="$(sha256_file "$blob")"
if [ -n "$recorded_wasm" ] && [ "$actual_wasm" != "$recorded_wasm" ]; then
  fail "$(printf 'dregg_wasm_bg.wasm does not match its own build record.\n  recorded %s\n  on disk  %s\nThe artifact was replaced or edited after the build that described it.' "$recorded_wasm" "$actual_wasm")"
fi

# (3) the source closure still IS what it was built from.
echo "recomputing the wasm32 source fingerprint..."
actual_src="$("$ROOT/scripts/wasm-source-fingerprint.sh")"

if [ "$actual_src" != "$recorded_src" ]; then
  cat >&2 <<EOF

WASM FRESHNESS: RED — the bundle is STALE.

  built from source  $recorded_src
  tree is now        $actual_src

The wasm32 source closure has changed since this bundle was built, so what
/descent/play serves is NOT what this tree says the game is. This is the failure that
shipped a v1 portable-record wire against a v3 server for five days: the bundle
answered 200, the browser played, and every settled run it exported was refused.

Rebuild it:  bash scripts/build-web-artifacts.sh
EOF
  exit 1
fi

echo
echo "WASM FRESHNESS: GREEN — bundle matches the wasm32 source closure."
