#!/usr/bin/env bash
# QUIC/H3 battery runner: bring up a dedicated serve instance on a UDP port,
# run the battery against it, then reap the instance. Self-contained + self-reaping.
#
# Usage: runner.sh [PORT]   (default 18950)
#
# Env:
#   QUIC_IO  the TCP reactor the serve runs. Default `auto` = whatever the
#            shipped binary picks (io_uring on Linux). QUIC itself rides --udp,
#            but the TCP reactor selects which serve shell hosts the UDP loop,
#            so pinning `blocking` here attested a shell nobody deploys. Set
#            QUIC_IO=blocking to drive the portable path explicitly.
set -u
PORT="${1:-18950}"
QUIC_IO="${QUIC_IO:-auto}"
DROOT="${DROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
BIN="$DROOT/target/release/dataplane"
HERE="$DROOT/conformance/quic"
LOG="$HERE/serve-$PORT.log"

source "$DROOT/conformance/lib/harness.sh"

if [ ! -x "$BIN" ]; then echo "no dataplane binary at $BIN" >&2; exit 3; fi

trap harness_reap EXIT
# Refuse the port if a sibling already owns it — otherwise we would silently
# fail to bind and drive the WRONG serve, reporting a contaminated result.
harness_require_free 127.0.0.1 "$PORT" || exit 1

# Bring up a serve bound TCP+UDP on the dedicated port (UDP is the QUIC path).
"$BIN" --bind "127.0.0.1:$PORT" --udp "127.0.0.1:$PORT" --io "$QUIC_IO" >"$LOG" 2>&1 &
SRV=$!
harness_track "$SRV" "release/dataplane --bind 127.0.0.1:$PORT "

# Wait for the UDP listener line (or up to ~8s); fail fast if the serve dies.
harness_wait_log "$LOG" "listening on .*${PORT}/udp" "$SRV" 40
case $? in
  0) ;;
  2) echo "serve died on startup:" >&2; cat "$LOG" >&2; exit 4 ;;
  *) echo "serve never announced UDP listen on :$PORT" >&2; cat "$LOG" >&2; exit 4 ;;
esac

echo "--- serve log head ---"
head -6 "$LOG"
echo "--- battery ---"
python3 "$HERE/battery.py" 127.0.0.1 "$PORT"
RC=$?
echo "--- serve log tail (datagram outcomes) ---"
tail -20 "$LOG"
exit $RC
