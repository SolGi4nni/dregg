#!/usr/bin/env bash
# PQ hybrid KEX probe (supplementary to the QUIC battery).
#
# The QUIC datapath runs NO TLS handshake (see NOTES.md), so the X25519MLKEM768
# hybrid KEX cannot be exercised over QUIC on the deployed binary. This probes the
# same KEX where it IS reachable — the TLS-over-TCP edge — to establish that the
# post-quantum hybrid is real and enforced (fail-closed against classical).
#
# Usage: pq_kex_probe.sh [PORT]   (default 18952)
set -u
PORT="${1:-18952}"
DROOT="$HOME/dev/drorb"
BIN="$DROOT/target/release/dataplane"
CLIENT="$HOME/pq-xwing-client/target/release/pq-xwing-client"
LOG="$DROOT/conformance/quic/tlspq-$PORT.log"

[ -x "$BIN" ] || { echo "no dataplane at $BIN" >&2; exit 3; }
[ -x "$CLIENT" ] || { echo "no pq-xwing-client at $CLIENT" >&2; exit 3; }

cd "$DROOT" || exit 3
DRORB_TLS_LISTEN="127.0.0.1:$PORT" "$BIN" --bind "127.0.0.1:$((PORT+1))" --no-udp --io blocking >"$LOG" 2>&1 &
SRV=$!
trap 'kill "$SRV" 2>/dev/null; wait "$SRV" 2>/dev/null' EXIT
for i in $(seq 1 40); do
  grep -q "$PORT" "$LOG" 2>/dev/null && break
  kill -0 "$SRV" 2>/dev/null || { echo "serve died:"; cat "$LOG"; exit 4; }
  sleep 0.2
done

echo "=== pq-only: kx_groups restricted to X25519MLKEM768 (0x11EC) ==="
"$CLIENT" "127.0.0.1:$PORT" pq-only 2>&1 | head -12
echo
echo "=== classical: kx_groups restricted to X25519 (control) ==="
"$CLIENT" "127.0.0.1:$PORT" classical 2>&1 | head -12
