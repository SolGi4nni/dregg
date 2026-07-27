#!/usr/bin/env bash
# Live WebRTC data-channel cross-check: drorb's proven-crypto driver
# (webrtc-live / WebrtcLive.lean) against a real WebRTC peer (dtls_peer.py —
# aiortc's OpenSSL DTLS 1.2 engine + aiortc's real RTCSctpTransport and
# data-channel stack). drorb completes the DTLS 1.2 handshake, opens an SCTP
# association (RFC 4960 four-way) inside the AES-128-GCM records, opens a data
# channel over DCEP (RFC 8832), and sends a string message — which aiortc's
# on("datachannel") / channel.on("message") events receive verbatim.
#
# Prereq: a Python venv with aiortc installed, path in $VENV (default: ./venv).
# HACL: set HACL_DIST / LIBRARY_PATH to the HACL*/EverCrypt dist if /opt/hacl-star
# is not symlinked.
#
# Run from the repository root:
#   VENV=/path/to/venv conformance/webrtc/run.sh [port]
set -euo pipefail

PORT="${1:-5570}"
VENV="${VENV:-./venv}"

"$VENV/bin/python" conformance/webrtc/dtls_peer.py "$PORT" &
SRV=$!
trap 'kill $SRV 2>/dev/null || true' EXIT
sleep 2

echo "===== drorb webrtc-live (proven-crypto DTLS 1.2 + SCTP + DCEP client) ====="
lake exe webrtc-live 127.0.0.1 "$PORT"
