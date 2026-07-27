#!/usr/bin/env bash
# Drive a REAL off-the-shelf HTTP/3 client (quinn + h3 + rustls) against the
# deployed serve's QUIC/UDP path: a real 1-RTT handshake over the pinned
# X25519MLKEM768 hybrid, then a real GET.
#
# Brings up its own dedicated serve, runs three checks, reaps the serve:
#   1. hybrid  GET /health  -> 200 ok
#   2. hybrid  GET /        -> a routed status (distinct from /health)
#   3. classical-only X25519 -> REFUSED (no handshake): the negative control that
#      shows the hybrid pin is live on the wire, not merely asserted in source.
#
# Usage: h3_get.sh [PORT]
#
# Env:
#   QUIC_IO  the TCP reactor hosting the serve. Default `auto` (see quic/runner.sh).
set -u
PORT="${1:-18962}"
QUIC_IO="${QUIC_IO:-auto}"
DROOT="${DROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
BIN="$DROOT/target/release/dataplane"
CLI="$DROOT/conformance/quic/h3-client/target/release/h3-client"
LOG="$DROOT/conformance/quic/h3get-$PORT.log"

source "$DROOT/conformance/lib/harness.sh"

[ -x "$BIN" ] || { echo "no dataplane binary at $BIN" >&2; exit 3; }
[ -x "$CLI" ] || { echo "no h3 client at $CLI (cargo build --release in conformance/quic/h3-client)" >&2; exit 3; }

trap harness_reap EXIT
harness_require_free 127.0.0.1 "$PORT" || exit 1

"$BIN" --bind "127.0.0.1:$PORT" --udp "127.0.0.1:$PORT" --io "$QUIC_IO" >"$LOG" 2>&1 &
SRV=$!
harness_track "$SRV" "release/dataplane --bind 127.0.0.1:$PORT "

harness_wait_log "$LOG" "listening on .*${PORT}/udp" "$SRV" 40
case $? in
  0) ;;
  2) echo "serve died on startup:" >&2; cat "$LOG" >&2; exit 4 ;;
  *) echo "serve never announced UDP listen on :$PORT" >&2; cat "$LOG" >&2; exit 4 ;;
esac

fail=0

health=$("$CLI" "$PORT" /health 2>&1 | head -1)
echo "hybrid   GET /health   -> $health"
[ "$health" = "STATUS 200 BODY ok" ] || { echo "  FAIL: expected 'STATUS 200 BODY ok'"; fail=1; }

root=$("$CLI" "$PORT" / 2>&1 | head -1)
echo "hybrid   GET /         -> $root"
case "$root" in STATUS*) ;; *) echo "  FAIL: expected a routed status"; fail=1;; esac

classical=$("$CLI" "$PORT" /health localhost --kex x25519 2>&1 | head -1)
echo "classical X25519 only  -> $classical"
case "$classical" in ERROR*) ;; *) echo "  FAIL: classical-only KEX MUST be refused, got '$classical'"; fail=1;; esac

if [ "$fail" -eq 0 ]; then echo "h3_get: PASS (3/3)"; else echo "h3_get: FAIL"; fi
exit "$fail"
