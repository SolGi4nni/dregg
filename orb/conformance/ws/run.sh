#!/usr/bin/env bash
# RFC 6455 WebSocket conformance run: Autobahn testsuite fuzzingclient against
# the dataplane serve binary.
#
# Launches a single dataplane session on a dedicated port, runs the full
# Autobahn fuzzingclient case set (1.*-13.* including RFC 7692 permessage-deflate (12.*/13.*); the server
# ),
# writes HTML+JSON reports into ./reports, then reaps the serve process.
#
# Usage: ./run.sh [PORT]   (default 18966)
#
# Env:
#   WS_IO  dataplane --io reactor. Default `auto` = the mode the shipped binary
#          picks (io_uring on Linux, kqueue on macOS/BSD). This run used to be
#          hardcoded `--io blocking`, which is exactly why the WebSocket gap
#          survived: the upgrade fork was wired only on the portable fallback,
#          so a 514/517 Autobahn score attested a reactor nobody deploys. Set
#          WS_IO=blocking to drive the portable path explicitly.
set -u
PORT="${1:-18966}"
HERE="$(cd "$(dirname "$0")" && pwd)"

# Snapshot the serve binary under a neutral name: the tree is rebuilt
# concurrently (the binary may be replaced mid-run) and sibling jobs reap
# processes by name. The snapshot pins one build for the whole suite run.
source "$HERE/../lib/harness.sh"
BIN="$HERE/.ws-sut-snapshot"
cp "${DROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}/target/release/dataplane" "$BIN"
chmod +x "$BIN"

if ! harness_require_free 127.0.0.1 "$PORT"; then exit 1; fi

trap harness_reap EXIT
WS_IO="${WS_IO:-auto}"
"$BIN" --bind "127.0.0.1:$PORT" --no-udp --io "$WS_IO" &
SERVE_PID=$!
harness_track "$SERVE_PID" ".ws-sut-snapshot --bind 127.0.0.1:$PORT "

# Wait for the listener; fail fast if the serve dies on launch.
harness_wait_listen_tcp 127.0.0.1 "$PORT" "$SERVE_PID" 50
case $? in
  0) ;;
  2) echo "serve died on launch" >&2; exit 1 ;;
  *) echo "serve never bound on :$PORT" >&2; exit 1 ;;
esac

# The suite config binds the port in its URL; regenerate it to match $PORT.
sed "s|ws://127.0.0.1:[0-9]*|ws://127.0.0.1:$PORT|" \
    "$HERE/fuzzingclient.json" > "$HERE/fuzzingclient.gen.json"

docker run --rm --network host \
    -v "$HERE:/work" -w /work \
    crossbario/autobahn-testsuite \
    wstest -m fuzzingclient -s fuzzingclient.gen.json
RC=$?

# A run is only trustworthy if the serve survived it. If the process is gone,
# say so loudly — a dead serve turns every later case into "connection
# refused" and the suite aborts.
if kill -0 "$SERVE_PID" 2>/dev/null; then
    echo "SERVE-ALIVE: yes (pid $SERVE_PID survived the whole run)"
else
    echo "SERVE-ALIVE: NO — the serve process died during the run;" \
         "results below cover only the cases before the death" >&2
fi

python3 "$HERE/summarize.py" "$HERE/reports/index.json" | tee "$HERE/results_ws.txt"
exit $RC
