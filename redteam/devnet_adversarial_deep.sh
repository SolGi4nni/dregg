#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# Live-devnet DEEP adversarial probe (Part B of the multi-node Byzantine red-team)
#
# Companion to `devnet_probe.sh`. This script captures the surfaces + findings
# discovered in the 2026-06-08 red-team pass:
#
#   * the public-edge proxy posture (Caddy serves the SPA for write routes ⇒
#     POST returns 405; the privileged write API is NOT publicly reachable),
#   * the loopback-origin write API (127.0.0.1:8420) — where the REAL Rust
#     handlers live, reachable only on the box,
#   * the unauthenticated-write rejection (401 at the `require_auth` gate),
#   * an AVAILABILITY probe (a submit that reaches execution can wedge the node
#     because STARK proving runs on the request path under a state-write lock —
#     finding F-DOS-1 / task #109).
#
# SAFETY: read + adversarial-submit + observe only. NO data destruction. The
# loopback section is GATED behind DREGG_DEVNET_LOOPBACK=1 and intended to be run
# FROM THE BOX (ssh), because submitting a proving turn can wedge the solo node
# (F-DOS-1). Do NOT run the loopback proving submit against the live public node
# without an operator on hand to `systemctl restart dregg-gateway` (non-
# destructive: redb state persists).
#
# Usage:
#   ./devnet_adversarial_deep.sh                      # public-edge probes only
#   DREGG_DEVNET_LOOPBACK=1 ./devnet_adversarial_deep.sh   # + loopback (on box)
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail

PUB="${DREGG_DEVNET_PUB:-https://devnet.dregg.fg-goose.online}"
LOOP="${DREGG_DEVNET_LOOP:-http://127.0.0.1:8420}"

hr() { printf '─%.0s' {1..72}; echo; }
code() { curl -s -m "${3:-12}" -o /dev/null -w "%{http_code}" "$2" -X "$1" "${@:4}"; }

echo "### PART B.1 — PUBLIC EDGE POSTURE (${PUB})"
hr
echo "[B.1.1] node /status (read, proxied):"
curl -s -m 12 "$PUB/status" | head -c 500; echo

echo "[B.1.2] write routes are SPA-shadowed — POST returns 405 (Allow: GET,HEAD):"
for ep in /turn/submit /turns/submit /cipherclerk/mint /api/faucet; do
  c=$(code POST "$PUB$ep")
  allow=$(curl -s -m 12 -D - -o /dev/null -X POST "$PUB$ep" | grep -i '^allow:' | tr -d '\r')
  echo "  POST $ep -> $c   ${allow}"
done
echo "  (FINDING F-EDGE-1: the public reverse proxy serves the static SPA for"
echo "   write paths; POSTs never reach the node. The privileged write API is"
echo "   NOT publicly reachable. This is a DEFENSE — but also means the public"
echo "   devnet cannot accept turns over HTTPS; the submit path is loopback-only.)"

echo
echo "[B.1.3] read endpoints that ARE proxied to the node:"
for ep in /status /api/cells /api/receipts /api/blocks /metrics; do
  ct=$(curl -s -m 12 -D - -o /dev/null "$PUB$ep" | grep -i '^content-type:' | tr -d '\r')
  echo "  GET $ep -> $(code GET "$PUB$ep")   ${ct}"
done

echo
echo "[B.1.4] path-traversal / injection on a proxied read route (must NOT 5xx / leak):"
for p in '/api/cell/..%2F..%2F..%2Fetc%2Fpasswd' '/api/cell/%00' '/api/cell/$(whoami)'; do
  echo "  GET $p -> $(code GET "$PUB$p")"
done

echo
echo "[B.1.5] oversized body (~16.8 MB) to the edge (must not OOM / 5xx):"
yes A | head -c 16800000 > /tmp/redteam_big.bin 2>/dev/null
echo "  POST /turn/submit (16.8MB) -> $(curl -s -m 30 -o /dev/null -w '%{http_code}' -X POST --data-binary @/tmp/redteam_big.bin "$PUB/turn/submit")"
rm -f /tmp/redteam_big.bin

echo
echo "[B.1.6] node still healthy after the edge barrage:"
curl -s -m 12 "$PUB/status" | grep -o '"healthy":[a-z]*\|"consensus_live":[a-z]*'

if [ "${DREGG_DEVNET_LOOPBACK:-0}" != "1" ]; then
  echo
  echo "### PART B.2 (loopback) SKIPPED — set DREGG_DEVNET_LOOPBACK=1 and run ON THE BOX."
  echo "    (loopback proving submit can wedge the solo node: F-DOS-1)"
  exit 0
fi

echo
echo "### PART B.2 — LOOPBACK ORIGIN (${LOOP}) — the REAL Rust handlers"
hr
echo "[B.2.1] loopback /status (node directly):"
curl -s -m 10 "$LOOP/status" | head -c 400; echo

echo "[B.2.2] malformed JSON to /turn/submit (must reject fast, not wedge):"
t0=$(date +%s.%N)
c=$(code POST "$LOOP/turn/submit" 10 -H 'content-type: application/json' --data '{not json')
t1=$(date +%s.%N)
echo "  -> $c  (t=$(echo "$t1-$t0" | bc)s)   [expect 401 unauth or 400 bad-request, sub-ms]"

echo "[B.2.3] unauthorized write (no bearer) — require_auth gate (expect 401):"
echo "  POST /turn/submit (no auth) -> $(code POST "$LOOP/turn/submit" 10 -H 'content-type: application/json' --data '{}')"
echo "  POST /cipherclerk/mint (no auth) -> $(code POST "$LOOP/cipherclerk/mint" 10 -H 'content-type: application/json' --data '{"amount":1000000}')"

echo "[B.2.4] forged-signature signed-turn envelope (expect accepted=false / 400):"
echo "  POST /turns/submit (garbage postcard) -> $(code POST "$LOOP/turns/submit" 10 --data-binary 'XX-not-a-signedturn-XX')"

echo "[B.2.5] liveness AFTER the loopback barrage (the F-DOS-1 check):"
for i in 1 2 3; do
  t0=$(date +%s.%N); c=$(curl -s -m 8 -o /dev/null -w '%{http_code}' "$LOOP/status"); t1=$(date +%s.%N)
  echo "  /status try $i -> $c  (t=$(echo "$t1-$t0" | bc)s)"
  [ "$c" = "000" ] && echo "  !! FINDING F-DOS-1 CONFIRMED: node wedged (0 bytes / timeout) after submit — proving on the request path starved the runtime. Restart: sudo systemctl restart dregg-gateway"
done
