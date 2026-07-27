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
# The reactor hosting the process. Default `auto` = whatever the shipped binary
# picks (io_uring on Linux). The TLS edge this battery drives is its OWN
# listener thread (docs/gateway/ENV-BY-REACTOR.md: every DRORB_TLS_* is read off
# the reactor), so --io does not select the TLS code under test — but the runner
# must still launch the process production launches, not a portable fallback.
TLS_IO="${TLS_IO:-auto}"

source "$ROOT/conformance/lib/harness.sh"
trap harness_reap EXIT

if [ ! -x "$BIN" ]; then
  echo "error: serve binary not found / not executable: $BIN" >&2
  exit 2
fi

# POSTURE: this battery asserts the HYBRID PIN (a classical-only ClientHello is
# rejected, never downgraded), so the serve MUST run in `required` KEX posture.
# The serve default is `preferred` (honors a classical downgrade) — launching
# under the default would turn the pin checks into false FAILs. Pin required.
harness_require_free 127.0.0.1 "${TLS_PORT}" || exit 3
harness_require_free 127.0.0.1 "${PLAIN_PORT}" || exit 3

echo "-- launching serve HTTPS front door on 127.0.0.1:${TLS_PORT} (KEX=required) --"
env \
  DRORB_TLS_KEX="${DRORB_TLS_KEX:-required}" \
  DRORB_TLS_LISTEN="127.0.0.1:${TLS_PORT}" \
  DRORB_TLS_CERT="$ROOT/conformance/tls/cert.der" \
  DRORB_TLS_SEED="$ROOT/conformance/tls/seed.bin" \
  DRORB_TLS_ECDSA_CERT="$ROOT/conformance/tls/ecdsa-cert.der" \
  DRORB_TLS_ECDSA_KEY="$ROOT/conformance/tls/ecdsa-key.bin" \
  DRORB_TLS_RSA_CERT="$ROOT/conformance/tls/rsa-cert.der" \
  DRORB_TLS_RSA_N="$ROOT/conformance/tls/rsa-n.bin" \
  DRORB_TLS_RSA_E="$ROOT/conformance/tls/rsa-e.bin" \
  DRORB_TLS_RSA_D="$ROOT/conformance/tls/rsa-d.bin" \
  "$BIN" --bind "127.0.0.1:${PLAIN_PORT}" --no-udp --io "$TLS_IO" \
  >"$LOG" 2>&1 </dev/null &
SRV=$!
harness_track "$SRV" "release/dataplane --bind 127.0.0.1:${PLAIN_PORT} "

# Wait for the TLS port (the port the battery drives) to accept.
harness_wait_listen_tcp 127.0.0.1 "${TLS_PORT}" "$SRV" 60
case $? in
  0) ;;
  2) echo "error: serve died before the TLS listener bound; log:" >&2; cat "$LOG" >&2; exit 3 ;;
  *) echo "error: TLS listener never bound on :${TLS_PORT}; log:" >&2; cat "$LOG" >&2; exit 3 ;;
esac
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
