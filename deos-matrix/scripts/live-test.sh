#!/usr/bin/env bash
# Drive the LIVE deos-matrix homeserver round-trip end to end:
#   1. bring up a throwaway Conduit homeserver in Docker (docker-compose.test.yml);
#   2. wait for it to answer the client-server API;
#   3. register two users (A = ember, B = quill) via open registration;
#   4. run the creds-gated live tests against it (single-client + cross-user A→B,
#      INCLUDING `live_two_user_real_executor_membrane_roundtrip` — A ships the
#      GENUINE executor-minted membrane fixture A→B and B extracts it byte-intact);
#   5. tear the homeserver down (unless KEEP_HS=1).
#
# The executor-real membrane fixture (tests/fixtures/real_executor_membrane.json)
# is checked in. To REGENERATE it from the real Lean-backed executor (and prove the
# executor-side mint→rehydrate→drive→stitch with the conflict path in one run), from
# the repo root run:
#   cd starbridge-v2 && cargo test --no-default-features \
#     --features "embedded-executor dev-surfaces" --lib bake_real_executor_membrane_fixture
# (BAKE_FIXTURE=1 ./scripts/live-test.sh does this for you before the live run.)
#
# This is the realistic local-homeserver path per the repo's Docker convention —
# NO direct host install. `cargo test` without this script is GREEN (the live
# tests are creds-gated no-ops); this script supplies the real server + creds.
#
#   usage:  ./scripts/live-test.sh           # full cycle, tears down after
#           KEEP_HS=1 ./scripts/live-test.sh # leave the homeserver up afterward
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$HERE"

HS_URL="http://localhost:6167"
SERVER_NAME="deos.local"
USER_A="ember"
PASS_A="hunter2hunter2"
USER_B="quill"
PASS_B="hunter2hunter2"

COMPOSE="docker compose -f docker-compose.test.yml"

cleanup() {
  if [[ "${KEEP_HS:-0}" != "1" ]]; then
    echo "==> tearing down homeserver"
    $COMPOSE down -v >/dev/null 2>&1 || true
  else
    echo "==> KEEP_HS=1 — leaving homeserver up ($HS_URL)"
  fi
}
trap cleanup EXIT

# Optionally regenerate the executor-real membrane fixture from the Lean-backed
# executor before the live run (heavy build). The fixture is checked in, so this is
# off by default; set BAKE_FIXTURE=1 to refresh it (and re-prove the executor-side
# mint→rehydrate→drive→stitch loop in the same step).
if [[ "${BAKE_FIXTURE:-0}" == "1" ]]; then
  echo "==> baking the executor-real membrane fixture (real Lean-backed executor)"
  ( cd "$HERE/../starbridge-v2" && cargo test --no-default-features \
      --features "embedded-executor dev-surfaces" --lib \
      bake_real_executor_membrane_fixture -- --nocapture )
fi

echo "==> bringing up Conduit homeserver"
$COMPOSE up -d

echo "==> waiting for the client-server API at $HS_URL"
for i in $(seq 1 60); do
  if curl -sf "$HS_URL/_matrix/client/versions" >/dev/null 2>&1; then
    echo "    homeserver is up (after ${i}s)"
    break
  fi
  if [[ "$i" == "60" ]]; then
    echo "!! homeserver never came up; logs:" >&2
    $COMPOSE logs --tail 50 >&2
    exit 1
  fi
  sleep 1
done

register() {
  local u="$1" p="$2"
  # Conduit open registration: m.login.dummy, no token. A 200 (user created) or a
  # 400 M_USER_IN_USE (already registered from a prior run) are both fine.
  local resp
  resp="$(curl -sS -X POST "$HS_URL/_matrix/client/v3/register" \
    -H 'Content-Type: application/json' \
    -d "{\"username\":\"$u\",\"password\":\"$p\",\"auth\":{\"type\":\"m.login.dummy\"}}" || true)"
  if echo "$resp" | grep -q '"access_token"'; then
    echo "    registered $u"
  elif echo "$resp" | grep -q 'M_USER_IN_USE'; then
    echo "    $u already exists (reusing)"
  else
    echo "!! registration of $u may have failed: $resp" >&2
  fi
}

echo "==> registering users"
register "$USER_A" "$PASS_A"
register "$USER_B" "$PASS_B"

echo "==> running the live tests"
export DEOS_MATRIX_TEST_HS="$HS_URL"
# NB: we deliberately do NOT set DEOS_MATRIX_TEST_SERVERNAME. The bare-server-name
# `.well-known` discovery test needs a server name that resolves over real DNS with
# a published `.well-known/matrix/client` — our throwaway Conduit answers on
# http://localhost:6167 but "deos.local" is not real DNS, so that path cannot
# succeed here. Leaving the var unset makes that test a no-op (it is a separate
# discovery-flow concern, not the live chat round-trip this harness proves).
export DEOS_MATRIX_TEST_USER="$USER_A"
export DEOS_MATRIX_TEST_PASS="$PASS_A"
export DEOS_MATRIX_TEST_USER_B="$USER_B"
export DEOS_MATRIX_TEST_PASS_B="$PASS_B"

cargo test --test live_homeserver -- --nocapture --test-threads=1
echo "==> deos-matrix live tests passed"

# THE FULL LOOP IN ONE PROCESS — the true closure of the workspace seam (no fixture
# handoff): a single process in starbridge-v2 that links BOTH the real Lean-backed
# executor AND the live Matrix client. A's executor mints a membrane → ships it over
# THIS homeserver → B receives it off the wire → B rehydrates + drives a real verified
# turn + stitches it back (conflict path + Σδ=0). Heavy build (the embedded executor),
# so it is gated on FULL_LOOP=1. The env quintet above is already exported.
if [[ "${FULL_LOOP:-0}" == "1" ]]; then
  echo "==> running the single-process FULL membrane loop (real executor over real Matrix)"
  ( cd "$HERE/../starbridge-v2" && cargo test --no-default-features \
      --features "embedded-executor dev-surfaces" --lib \
      full_loop_one_process_real_executor_over_real_matrix -- --nocapture --test-threads=1 )
  echo "==> single-process full loop passed"
fi
