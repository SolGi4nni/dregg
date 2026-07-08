#!/usr/bin/env bash
# Local-binary dual of deos-matrix/scripts/live-test.sh — prove the co-driven-card
# membrane (Pillar 3 of docs/deos/GRAIN-HOMESERVER.md) rides OUR embedded
# continuwuity homeserver (this crate's `EmbeddedHomeserver`, run as the
# `deos-homeserver` subprocess) instead of an external Docker Conduit.
#
# Steps (mirrors live-test.sh, s/Docker Conduit/our binary/):
#   1. build + run the `deos-homeserver` bin (isolated 1.96.1 workspace), parse its
#      `READY <base_url>` line;
#   2. register the TWO users the card-carry test needs (A, B) via the CS-API UIAA
#      open-registration flow (POST /register -> 401 session -> POST m.login.dummy);
#   3. export the two-user env quintet pointing at OUR server;
#   4. run the card-carry live test(s) against it:
#        - deos-matrix  live_two_user_card_fork_carry_roundtrip (always);
#        - starbridge   full_loop_card_fork_over_real_matrix    (only if CARD_LOOP=1;
#          heavy agent-js/mozjs build, gated exactly like live-test.sh's CARD_LOOP);
#   5. tear down (kill the server) unless KEEP_HS=1.
#
#   usage:  bash deos-homeserver/scripts/card-carry-local.sh
#           KEEP_HS=1   ... # leave the homeserver process up afterward
#           CARD_LOOP=1 ... # also run the starbridge one-process card loop (heavy)
set -euo pipefail

# Absolute paths (agent threads reset cwd; be explicit).
HS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # deos-homeserver/
ROOT="$(cd "$HS_DIR/.." && pwd)"                            # breadstuffs/

SERVER_NAME="${SERVER_NAME:-localhost}"
USER_A="${USER_A:-ember}"
PASS_A="${PASS_A:-hunter2hunter2}"
USER_B="${USER_B:-quill}"
PASS_B="${PASS_B:-hunter2hunter2}"

HS_PID=""
HS_OUT="$(mktemp -t deos-hs-out.XXXXXX)"

cleanup() {
  if [[ -n "$HS_PID" ]] && kill -0 "$HS_PID" 2>/dev/null; then
    if [[ "${KEEP_HS:-0}" == "1" ]]; then
      echo "==> KEEP_HS=1 — leaving homeserver up (pid $HS_PID, $HS_URL)"
    else
      echo "==> tearing down homeserver (pid $HS_PID)"
      kill "$HS_PID" 2>/dev/null || true
      wait "$HS_PID" 2>/dev/null || true
    fi
  fi
  [[ "${KEEP_HS:-0}" == "1" ]] || rm -f "$HS_OUT"
}
trap cleanup EXIT

# 1. BUILD the server bin in the isolated workspace, then run it.
echo "==> building deos-homeserver bin (isolated 1.96.1 workspace)"
( cd "$HS_DIR" && cargo build --bin deos-homeserver )
HS_BIN="$HS_DIR/target/debug/deos-homeserver"

echo "==> starting deos-homeserver ($SERVER_NAME)"
"$HS_BIN" "$SERVER_NAME" >"$HS_OUT" 2>&1 &
HS_PID=$!

# 2. Parse the READY <url> line (bin waits until the CS API answers before printing).
HS_URL=""
for i in $(seq 1 180); do
  if ! kill -0 "$HS_PID" 2>/dev/null; then
    echo "!! deos-homeserver exited early; output:" >&2
    cat "$HS_OUT" >&2
    exit 1
  fi
  line="$(grep -m1 '^READY ' "$HS_OUT" 2>/dev/null || true)"
  if [[ -n "$line" ]]; then
    HS_URL="${line#READY }"
    HS_URL="${HS_URL%$'\r'}"
    echo "    homeserver READY at $HS_URL (after ${i}s)"
    break
  fi
  sleep 1
done
if [[ -z "$HS_URL" ]]; then
  echo "!! never saw READY line within timeout; output:" >&2
  cat "$HS_OUT" >&2
  exit 1
fi

# 3. Register the two users via the CS-API UIAA open-registration flow.
#    POST /register (no auth) -> 401 + a session -> POST with m.login.dummy + session.
#    The server has force_disable_first_run_mode, so the first user registers open.
register() {
  local u="$1" p="$2"
  local first session reg
  first="$(curl -sS -X POST "$HS_URL/_matrix/client/v3/register" \
    -H 'Content-Type: application/json' \
    -d "{\"username\":\"$u\",\"password\":\"$p\"}" || true)"
  # M_USER_IN_USE straight away => already registered from a prior KEEP_HS run.
  if echo "$first" | grep -q 'M_USER_IN_USE'; then
    echo "    $u already exists (reusing)"
    return 0
  fi
  session="$(echo "$first" | sed -n 's/.*"session"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n1)"
  if [[ -z "$session" ]]; then
    echo "!! no UIAA session for $u; register step-1 response: $first" >&2
    return 1
  fi
  reg="$(curl -sS -X POST "$HS_URL/_matrix/client/v3/register" \
    -H 'Content-Type: application/json' \
    -d "{\"username\":\"$u\",\"password\":\"$p\",\"auth\":{\"type\":\"m.login.dummy\",\"session\":\"$session\"}}" || true)"
  if echo "$reg" | grep -q '"access_token"'; then
    echo "    registered $u"
  elif echo "$reg" | grep -q 'M_USER_IN_USE'; then
    echo "    $u already exists (reusing)"
  else
    echo "!! registration of $u may have failed: $reg" >&2
    return 1
  fi
}

echo "==> registering users"
register "$USER_A" "$PASS_A"
register "$USER_B" "$PASS_B"

# 4. Export the two-user env quintet (exactly what the card-carry tests read) and run.
export DEOS_MATRIX_TEST_HS="$HS_URL"
export DEOS_MATRIX_TEST_USER="$USER_A"
export DEOS_MATRIX_TEST_PASS="$PASS_A"
export DEOS_MATRIX_TEST_USER_B="$USER_B"
export DEOS_MATRIX_TEST_PASS_B="$PASS_B"

echo "==> running the deos-matrix card-carry live test against OUR homeserver"
( cd "$ROOT" && cargo test -p deos-matrix --test live_homeserver \
    live_two_user_card_fork_carry_roundtrip -- --nocapture --test-threads=1 )
echo "==> deos-matrix card-carry live test passed"

# The starbridge one-process card-fork loop reads the SAME env quintet but needs the
# agent-js (mozjs) heavy build, so it is gated exactly like live-test.sh's CARD_LOOP.
if [[ "${CARD_LOOP:-0}" == "1" ]]; then
  echo "==> running the starbridge one-process card-fork loop (agent-js/mozjs)"
  ( cd "$ROOT/starbridge-v2" && cargo test --no-default-features \
      --features "agent-js dev-surfaces" --lib \
      full_loop_card_fork_over_real_matrix -- --nocapture --test-threads=1 )
  echo "==> starbridge card-fork loop passed"
fi

echo "==> ALL card-carry-local checks passed against the embedded homeserver ($HS_URL)"
