#!/usr/bin/env bash
# RFC 6455 WebSocket conformance run: Autobahn testsuite fuzzingclient against
# the dataplane serve binary.
#
# Launches a single dataplane session on a dedicated port, runs the full
# Autobahn fuzzingclient case set (1.*-13.* including RFC 7692 permessage-deflate (12.*/13.*); the server
# ),
# writes HTML+JSON reports into ./reports, then reaps the serve process.
#
# Usage: ./run.sh [PORT]   (default 18906)
set -u
PORT="${1:-18966}"
HERE="$(cd "$(dirname "$0")" && pwd)"

# Snapshot the serve binary under a neutral name: the tree is rebuilt
# concurrently (the binary may be replaced mid-run) and sibling jobs reap
# processes by name. The snapshot pins one build for the whole suite run.
BIN="$HERE/.ws-sut-snapshot"
cp "$HOME/dev/drorb/target/release/dataplane" "$BIN"
chmod +x "$BIN"

if ss -tln | grep -q ":$PORT "; then
    echo "port $PORT already in use — refusing" >&2
    exit 1
fi

"$BIN" --bind "127.0.0.1:$PORT" --no-udp --io blocking &
SERVE_PID=$!
trap 'kill -9 "$SERVE_PID" 2>/dev/null' EXIT

# Wait for the listener.
for _ in $(seq 1 50); do
    ss -tln | grep -q ":$PORT " && break
    kill -0 "$SERVE_PID" 2>/dev/null || { echo "serve died on launch" >&2; exit 1; }
    sleep 0.2
done

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
