#!/usr/bin/env bash
# run-h2spec.sh — HTTP/2 conformance battery (h2spec, cleartext h2c) for the
# two hosts of the verified HTTP/2 engine:
#
#   dataplane  the production Rust host: target/release/dataplane, which is
#              supposed to fork h2c prior-knowledge connections to the engine.
#   engine     the interactive C host (h2c_host.c relinked natively into
#              conformance/h2/bin/h2c-host) that threads
#              drorb_h2c_conn_init/feed across socket reads — the engine's
#              own conformance ceiling, independent of dataplane wiring.
#
# Runs the full h2spec suite (generic + hpack + http2) against the chosen
# host on a dedicated port and tears the server down. The full transcript is
# written to results/h2spec-<target>-<timestamp>.log next to this script.
#
# Usage:
#   conformance/h2/run-h2spec.sh [dataplane|engine] [PORT]
#
#   TARGET    which host to battery (default dataplane)
#   PORT      port to bind the server on (default 18907)
#
# Environment:
#   DATAPLANE  path to the dataplane binary (default: target/release/dataplane)
#   ENGINE     path to the engine host     (default: conformance/h2/bin/h2c-host)
#   H2SPEC     path to the h2spec binary   (default: conformance/h2/bin/h2spec)
#   H2_TIMEOUT per-test timeout in seconds (default 2, h2spec -o)
#   IO         dataplane --io mode: blocking|auto|uring|kqueue (default
#              `auto` = the mode the shipped binary picks, io_uring on Linux /
#              kqueue on macOS/BSD, so the battery drives the deployed
#              reactor). Every IO path forks h2c to the same interactive engine
#              host, so each can be batteried on its own fork; IO=blocking
#              still selects the portable fallback explicitly.
#
# Rebuilding the engine host natively (needs .lake/build/lib/libdrorb.a and
# the ffi/*.o objects; pq_stub.o supplies the fail-closed post-quantum
# symbols a standalone exe cannot get from the dataplane's Rust crate):
#   cc -O2 -I"$(lean --print-prefix)/include" -c ffi/pq_stub.c -o /tmp/pq_stub.o
#   cc -O2 -I"$(lean --print-prefix)/include" -o conformance/h2/bin/h2c-host \
#      conformance/h2c-host/h2c_host.c .lake/build/lib/libdrorb.a \
#      /tmp/pq_stub.o ffi/crypto_shim.o ffi/cgi_exec.o ffi/mac_udp.o \
#      ffi/derp_net.o ffi/tls_p256_shim.o target/release/libaes_fallback.a \
#      -L"$HOME/src/hacl-star/dist/gcc-compatible" -levercrypt \
#      -L"$(lean --print-prefix)/lib/lean" -lleanshared \
#      -Wl,-rpath,"$(lean --print-prefix)/lib/lean"
#
# Exit status is h2spec's own: 0 all pass, 1 any failure. Failures are the
# point — they map the gap between the host under test and RFC 9113 /
# RFC 7541; do not tune them away here.
set -euo pipefail
cd "$(dirname "$0")/../.."

TARGET="${1:-dataplane}"
PORT="${2:-18907}"
DATAPLANE="${DATAPLANE:-target/release/dataplane}"
ENGINE="${ENGINE:-conformance/h2/bin/h2c-host}"
H2SPEC="${H2SPEC:-conformance/h2/bin/h2spec}"
H2_TIMEOUT="${H2_TIMEOUT:-2}"
IO="${IO:-auto}"
OUT_DIR="conformance/h2/results"
mkdir -p "$OUT_DIR"
LOG="$OUT_DIR/h2spec-$TARGET-$IO-$(date +%Y%m%d-%H%M%S).log"
source conformance/lib/harness.sh

case "$TARGET" in
  dataplane) SERVER_BIN="$DATAPLANE"; SERVER_CMD=("$DATAPLANE" --bind "127.0.0.1:$PORT" --no-udp --io "$IO"); REAP_PAT="release/dataplane --bind 127.0.0.1:$PORT " ;;
  engine)    SERVER_BIN="$ENGINE";    SERVER_CMD=("$ENGINE" "$PORT"); REAP_PAT="h2c-host $PORT" ;;
  *) echo "unknown target '$TARGET' (want dataplane|engine)" >&2; exit 2 ;;
esac

[ -x "$SERVER_BIN" ] || { echo "no server binary at $SERVER_BIN" >&2; exit 2; }
[ -x "$H2SPEC" ] || { echo "no h2spec at $H2SPEC" >&2; exit 2; }

# Refuse to squat on a port someone else owns.
if ! harness_require_free 127.0.0.1 "$PORT"; then exit 2; fi

trap harness_reap EXIT
"${SERVER_CMD[@]}" &
SERVER_PID=$!
harness_track "$SERVER_PID" "$REAP_PAT"

# Wait for the listener (up to ~5s); fail fast if the server exits early.
rc=0; harness_wait_listen_tcp 127.0.0.1 "$PORT" "$SERVER_PID" 50 || rc=$?
case $rc in
  0) ;;
  2) echo "server exited before listening" >&2; exit 2 ;;
  *) echo "server never bound on :$PORT" >&2; exit 2 ;;
esac

{
  echo "# h2spec battery — $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# target: $TARGET (${SERVER_CMD[*]})"
  "$H2SPEC" --version
  echo
} | tee "$LOG"

set +e
"$H2SPEC" -h 127.0.0.1 -p "$PORT" -o "$H2_TIMEOUT" 2>&1 | tee -a "$LOG"
RC=${PIPESTATUS[0]}
set -e

echo
echo "full transcript: $LOG"
exit "$RC"
