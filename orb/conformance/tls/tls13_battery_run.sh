#!/usr/bin/env bash
# Runner for the TLS 1.3 conformance battery.
#
# Reaps its own listener, launches the serve's HTTPS front door on a dedicated
# port (default 18951) with the self-signed certificate pool under
# conformance/tls/, waits for readiness, runs tls13_battery.py my-hand against it,
# then tears the listener down. The serve BINARY is expected to already be
# built at target/release/dataplane (this runner never builds — another lane
# owns the build; it tolerates the binary changing).
#
#   conformance/tls/battery_run.sh                # default port 18951
#   TLS_PORT=18953 conformance/tls/battery_run.sh # pick another port
#
# The DURABLE deliverable is the harness + coverage; the score is a snapshot of
# whatever serve binary is on disk right now.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
cd "$ROOT"

TLS_PORT="${TLS_PORT:-18951}"
PLAIN_PORT="${PLAIN_PORT:-18852}"
BIN="${BIN:-$ROOT/target/release/dataplane}"
PQ_CLIENT="${PQ_CLIENT:-$HOME/pq-xwing-client/target/release/pq-xwing-client}"
LOG="/tmp/tls-battery-${TLS_PORT}.log"

reap() {
  pkill -f "DRORB_TLS_LISTEN=127.0.0.1:${TLS_PORT}" 2>/dev/null
  pkill -f "127.0.0.1:${PLAIN_PORT}" 2>/dev/null
  # anything still holding the TLS port
  local pid
  pid="$(ss -ltnp 2>/dev/null | awk -v p=":${TLS_PORT}" '$4 ~ p {print}' \
        | grep -oP 'pid=\K[0-9]+' | head -1)"
  [ -n "${pid:-}" ] && kill "$pid" 2>/dev/null
  sleep 1
}

trap reap EXIT
reap

if [ ! -x "$BIN" ]; then
  echo "error: serve binary not found / not executable: $BIN" >&2
  exit 2
fi

echo "-- launching serve HTTPS front door on 127.0.0.1:${TLS_PORT} --"
setsid env \
  DRORB_TLS_LISTEN="127.0.0.1:${TLS_PORT}" \
  DRORB_TLS_CERT="$ROOT/conformance/tls/cert.der" \
  DRORB_TLS_SEED="$ROOT/conformance/tls/seed.bin" \
  DRORB_TLS_ECDSA_CERT="$ROOT/conformance/tls/ecdsa-cert.der" \
  DRORB_TLS_ECDSA_KEY="$ROOT/conformance/tls/ecdsa-key.bin" \
  DRORB_TLS_RSA_CERT="$ROOT/conformance/tls/rsa-cert.der" \
  DRORB_TLS_RSA_N="$ROOT/conformance/tls/rsa-n.bin" \
  DRORB_TLS_RSA_E="$ROOT/conformance/tls/rsa-e.bin" \
  DRORB_TLS_RSA_D="$ROOT/conformance/tls/rsa-d.bin" \
  "$BIN" --bind "127.0.0.1:${PLAIN_PORT}" --no-udp --io blocking \
  >"$LOG" 2>&1 </dev/null &

# Wait for the TLS port to accept.
ready=0
for _ in $(seq 1 40); do
  if ss -ltn 2>/dev/null | grep -q ":${TLS_PORT} "; then ready=1; break; fi
  sleep 0.25
done
if [ "$ready" != "1" ]; then
  echo "error: TLS listener never bound on :${TLS_PORT}; log:" >&2
  cat "$LOG" >&2
  exit 3
fi
echo "-- listener up; running battery --"
echo

python3 "$HERE/tls13_battery.py" \
  --target "127.0.0.1:${TLS_PORT}" \
  --pq-client "$PQ_CLIENT" \
  --json "/tmp/tls-battery-${TLS_PORT}.json"
rc=$?

echo
echo "-- serve log tail --"
tail -5 "$LOG"
exit $rc
