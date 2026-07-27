#!/usr/bin/env bash
# PQ hybrid KEX probe (supplementary to the QUIC battery).
#
# The QUIC datapath runs NO TLS handshake (see NOTES.md), so the X25519MLKEM768
# hybrid KEX cannot be exercised over QUIC on the deployed binary. This probes the
# same KEX where it IS reachable — the TLS-over-TCP edge — to establish that the
# post-quantum hybrid is real and enforced (fail-closed against classical).
#
# Usage: pq_kex_probe.sh [PORT]   (default 18952)
#
# Env:
#   QUIC_IO  the reactor hosting the plain bind. Default `auto` = what the
#            shipped binary picks. NOTE the TLS edge this probe drives is its
#            own listener thread (docs/gateway/ENV-BY-REACTOR.md: every
#            DRORB_TLS_* is read off the reactor), so --io does not select the
#            code under probe here; running `auto` keeps the harness honest
#            about the process it launches, nothing more.
set -u
PORT="${1:-18952}"
QUIC_IO="${QUIC_IO:-auto}"
DROOT="${DROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
BIN="$DROOT/target/release/dataplane"
CLIENT="$HOME/pq-xwing-client/target/release/pq-xwing-client"
LOG="$DROOT/conformance/quic/tlspq-$PORT.log"

[ -x "$BIN" ] || { echo "no dataplane at $BIN" >&2; exit 3; }
[ -x "$CLIENT" ] || { echo "no pq-xwing-client at $CLIENT" >&2; exit 3; }

source "$DROOT/conformance/lib/harness.sh"
cd "$DROOT" || exit 3

PLAIN=$((PORT + 1))
trap harness_reap EXIT
# Own BOTH ports: the TLS edge (PORT, the port this probe drives) and the plain
# HTTP bind (PLAIN). Refuse if either is already held by a sibling serve.
harness_require_free 127.0.0.1 "$PORT" || exit 1
harness_require_free 127.0.0.1 "$PLAIN" || exit 1

# POSTURE (was a false-green bug): this probe asserts the hybrid is ENFORCED —
# fail-closed against a classical client. The serve default KEX posture is
# `preferred`, which HONORS a classical downgrade, so under the default the
# classical "control" below would COMPLETE and the enforcement claim would be a
# lie. Pin `required` so the control is a genuine negative (classical rejected).
DRORB_TLS_KEX=required DRORB_TLS_LISTEN="127.0.0.1:$PORT" \
  "$BIN" --bind "127.0.0.1:$PLAIN" --no-udp --io "$QUIC_IO" >"$LOG" 2>&1 &
SRV=$!
harness_track "$SRV" "release/dataplane --bind 127.0.0.1:$PLAIN "

# Wait for the TLS EDGE (PORT) to accept — the port the probe actually drives,
# not the plain bind. A weak log-grep on the bare port number could match the
# plain-bind startup line and proceed before the TLS edge was up.
harness_wait_listen_tcp 127.0.0.1 "$PORT" "$SRV" 40
case $? in
  0) ;;
  2) echo "serve died on startup:" >&2; cat "$LOG" >&2; exit 4 ;;
  *) echo "TLS edge never bound on :$PORT" >&2; cat "$LOG" >&2; exit 4 ;;
esac

echo "=== pq-only: kx_groups restricted to X25519MLKEM768 (0x11EC) ==="
"$CLIENT" "127.0.0.1:$PORT" pq-only 2>&1 | head -12
echo
echo "=== classical: kx_groups restricted to X25519 (control) ==="
"$CLIENT" "127.0.0.1:$PORT" classical 2>&1 | head -12
