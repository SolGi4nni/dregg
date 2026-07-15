#!/usr/bin/env bash
# QUIC/H3 battery runner: bring up a dedicated serve instance on a UDP port,
# run the battery against it, then reap the instance. Self-contained + self-reaping.
#
# Usage: runner.sh [PORT]   (default 18950)
set -u
PORT="${1:-18950}"
DROOT="$HOME/dev/drorb"
BIN="$DROOT/target/release/dataplane"
HERE="$DROOT/conformance/quic"
LOG="$HERE/serve-$PORT.log"

if [ ! -x "$BIN" ]; then echo "no dataplane binary at $BIN" >&2; exit 3; fi

# Bring up a serve bound TCP+UDP on the dedicated port (UDP is the QUIC path).
"$BIN" --bind "127.0.0.1:$PORT" --udp "127.0.0.1:$PORT" --io blocking >"$LOG" 2>&1 &
SRV=$!
trap 'kill "$SRV" 2>/dev/null; wait "$SRV" 2>/dev/null' EXIT

# Wait for the UDP listener line (or up to ~8s).
for i in $(seq 1 40); do
  if grep -q "listening on .*${PORT}/udp" "$LOG" 2>/dev/null; then break; fi
  if ! kill -0 "$SRV" 2>/dev/null; then echo "serve died on startup:" >&2; cat "$LOG" >&2; exit 4; fi
  sleep 0.2
done

echo "--- serve log head ---"
head -6 "$LOG"
echo "--- battery ---"
python3 "$HERE/battery.py" 127.0.0.1 "$PORT"
RC=$?
echo "--- serve log tail (datagram outcomes) ---"
tail -20 "$LOG"
exit $RC
