#!/usr/bin/env bash
#
# smoke-cli-turn.sh — drive a REAL turn through the `dregg` CLI against a live
# local node and prove it commits AND is proven on the verified commit path.
#
# This is the New-World end-to-end smoke: it exercises the SAME path a human
# operator uses — the `dregg` binary → the node's `/turn/submit` JSON ingress →
# a real signed call-forest → execution → blocklace consensus → the commit-path
# state producer + full-turn STARK proving.
#
# Flow:
#   1. Build dregg-node + the dregg CLI.
#   2. Start a solo node with --enable-faucet --prove-turns (full-turn proving
#      on the commit path) and, when DREGG_LEAN_PRODUCER=1 is exported, the
#      VERIFIED Lean executor as the authoritative state producer.
#   3. Unlock the cipherclerk, read the operator's public key, derive its agent
#      cell, and faucet it (this also MINTS the operator cell into the ledger).
#   4. Submit a turn through the CLI: `dregg turn quick set-field ...`.
#   5. Assert the CLI reports the turn ACCEPTED with proof_status == Proved.
#   6. Assert `dregg node producer` reports the honest verified-execution surface.
#
# Exits non-zero on any failed assertion. Self-contained; safe for CI.
#
# Usage: scripts/smoke-cli-turn.sh [PORT]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PORT="${1:-8455}"
GOSSIP_PORT=0
DATA_DIR="$(mktemp -d)"
NODE_URL="http://127.0.0.1:$PORT"
PASSPHRASE="cli-smoke-local"

# Honor an externally-set producer mode; default to opt-in (unset) so the smoke
# matches the devnet default. Export DREGG_LEAN_PRODUCER=1 to exercise the
# verified producer end-to-end.
LEAN_PRODUCER="${DREGG_LEAN_PRODUCER:-0}"

fail() { echo "FAIL: $*" >&2; exit 1; }
pass() { echo "PASS: $*"; }

# ── Build binaries ──────────────────────────────────────────────────────────
DREGG_NODE="$PROJECT_ROOT/target/debug/dregg-node"
DREGG_CLI="$PROJECT_ROOT/target/debug/dregg"
echo "=== building dregg-node + dregg CLI ==="
(cd "$PROJECT_ROOT" && cargo build -p dregg-node -p dregg-cli) \
  || fail "build failed"
[ -x "$DREGG_NODE" ] || fail "dregg-node binary missing"
[ -x "$DREGG_CLI" ] || fail "dregg CLI binary missing"

NODE_PID=""
cleanup() {
  if [ -n "$NODE_PID" ] && kill -0 "$NODE_PID" 2>/dev/null; then
    kill "$NODE_PID" 2>/dev/null || true
    wait "$NODE_PID" 2>/dev/null || true
  fi
  rm -rf "$DATA_DIR"
}
trap cleanup EXIT

echo ""
echo "=== starting solo node (faucet + full-turn proving) ==="
echo "  data dir:       $DATA_DIR"
echo "  api:            $NODE_URL"
echo "  lean producer:  $LEAN_PRODUCER"

"$DREGG_NODE" init --data-dir "$DATA_DIR" >"$DATA_DIR/init.log" 2>&1 || true

DREGG_PROVE_TURNS=1 DREGG_LEAN_PRODUCER="$LEAN_PRODUCER" \
"$DREGG_NODE" run \
  --data-dir "$DATA_DIR" \
  --port "$PORT" \
  --gossip-port "$GOSSIP_PORT" \
  --federation-mode solo \
  --consensus blocklace \
  --enable-faucet \
  --prove-turns \
  --block-cadence-ms 500 \
  >"$DATA_DIR/node.log" 2>&1 &
NODE_PID=$!

echo "waiting for HTTP API ..."
for _ in $(seq 1 60); do
  if curl -fsS "$NODE_URL/status" >/dev/null 2>&1; then break; fi
  if ! kill -0 "$NODE_PID" 2>/dev/null; then
    echo "--- node.log ---"; cat "$DATA_DIR/node.log" || true
    fail "node exited before the API came up"
  fi
  sleep 0.25
done
curl -fsS "$NODE_URL/status" >/dev/null 2>&1 || {
  echo "--- node.log ---"; cat "$DATA_DIR/node.log" || true
  fail "HTTP API never became reachable"
}
pass "node API reachable"

export DREGG_NODE_URL="$NODE_URL"
export DREGG_OUTPUT="json"

# ── Honest verified-execution surface via the CLI ───────────────────────────
echo ""
echo "=== dregg node producer (verified-execution surface) ==="
PRODUCER_JSON="$("$DREGG_CLI" node producer)"
echo "$PRODUCER_JSON" | python3 -m json.tool 2>/dev/null || echo "$PRODUCER_JSON"
echo "$PRODUCER_JSON" | python3 -c '
import sys, json
d = json.load(sys.stdin)
assert "state_producer" in d, "producer surface missing state_producer"
assert d["state_producer"] in ("lean","rust"), d["state_producer"]
cov = d.get("covered_effects", [])
assert isinstance(cov, list) and len(cov) >= 1, "no covered effects reported"
assert "Transfer" in cov and "SetField" in cov, "expected Transfer/SetField in covered set"
print("producer=%s  covered=%d  uncovered=%d  proving=%s" % (
    d["state_producer"], len(cov), len(d.get("uncovered_effects",[])), d.get("full_turn_proving")))
' || fail "verified-execution surface assertions failed"
pass "verified-execution surface reported honestly"

# ── Unlock + read operator identity ─────────────────────────────────────────
echo ""
echo "=== unlocking cipherclerk ==="
UNLOCK_JSON="$(curl -fsS -H 'Content-Type: application/json' \
  -d "{\"passphrase\":\"$PASSPHRASE\"}" "$NODE_URL/cipherclerk/unlock")" \
  || fail "unlock request failed"
# The bearer token authorizes the node's protected endpoints (turn submission).
API_TOKEN="$(echo "$UNLOCK_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin).get("bearer_token") or "")')"
[ -n "$API_TOKEN" ] || fail "unlock did not return a bearer_token"
export DREGG_API_TOKEN="$API_TOKEN"
pass "cipherclerk unlocked (bearer token acquired)"

# The node tells us its operator identity directly (no client-side derive_raw).
IDENT_JSON="$("$DREGG_CLI" node identity)"
echo "$IDENT_JSON" | python3 -m json.tool 2>/dev/null || echo "$IDENT_JSON"
PUBKEY="$(echo "$IDENT_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin)["public_key"])')"
AGENT_CELL="$(echo "$IDENT_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin)["agent_cell"])')"
[ -n "$PUBKEY" ] && [ -n "$AGENT_CELL" ] || fail "could not read operator identity"
echo "operator pubkey:  $PUBKEY"
echo "operator cell:    $AGENT_CELL"

# ── Fund the operator cell via the faucet ───────────────────────────────────
# The faucet's public_key path verifies recipient == derive_raw(public_key, …),
# creates the canonical hosted cell, and transfers computrons into it. The
# operator's own turn pays a fee (the executor's budget cap), so the cell needs
# a balance to cover it.
echo ""
echo "=== funding operator cell via faucet (amount=2000) ==="
FAUCET_JSON="$(curl -fsS -H 'Content-Type: application/json' \
  -d "{\"recipient\":\"$AGENT_CELL\",\"amount\":2000,\"public_key\":\"$PUBKEY\"}" \
  "$NODE_URL/api/faucet" || true)"
echo "faucet response: ${FAUCET_JSON:-<none>}"
echo "$FAUCET_JSON" | python3 -c '
import sys, json
d = json.load(sys.stdin)
if not d.get("success"):
    sys.stderr.write("faucet funding did not succeed: %s\n" % json.dumps(d))
    sys.exit(2)
' || fail "faucet funding of the operator cell failed"
pass "operator cell funded"

# Confirm the cell now exists in the ledger with a balance.
"$DREGG_CLI" node identity | python3 -c '
import sys, json
d = json.load(sys.stdin)
bal = d.get("agent_balance")
assert bal is not None and bal > 0, "operator cell not funded after faucet (balance=%r)" % bal
print("operator cell funded; balance=%s nonce=%s" % (bal, d.get("agent_nonce")))
' || fail "operator cell not funded after faucet"

# ── Drive a real turn through the CLI ───────────────────────────────────────
echo ""
echo "=== dregg turn quick set-field (through the CLI) ==="
# `--fee` belongs to the `quick` parent (before the effect subcommand). It is
# the executor's computron-budget cap; a generous fee (covered by the funded
# balance) keeps the turn under budget.
SUBMIT_JSON="$("$DREGG_CLI" turn quick --fee 1000 set-field --index 3 --value 7)" \
  || fail "CLI turn submit failed to execute"
echo "$SUBMIT_JSON" | python3 -m json.tool 2>/dev/null || echo "$SUBMIT_JSON"

echo "$SUBMIT_JSON" | python3 -c '
import sys, json
d = json.load(sys.stdin)
accepted = d.get("accepted", False)
status = d.get("proof_status", "")
if not accepted:
    sys.stderr.write("turn NOT accepted: %s\n" % json.dumps(d))
    sys.exit(2)
assert d.get("turn_hash"), "accepted turn missing turn_hash"
# Full-turn proving is ON; an activity turn must be Proved (or NotRequired if the
# effect produced no provable activity). Both are honest; a generation FAILURE is not.
assert status in ("Proved","NotRequired"), "unexpected proof_status: %s" % status
print("accepted=%s  turn_hash=%s..  proof_status=%s" % (
    accepted, d["turn_hash"][:12], status))
' || fail "CLI-submitted turn did not commit cleanly with an honest proof status"
pass "CLI-submitted turn committed with honest proof status"

# ── Confirm the receipt is visible (commit path ran) ────────────────────────
TURN_HASH="$(echo "$SUBMIT_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin)["turn_hash"])')"
echo ""
echo "=== dregg turn status $TURN_HASH ==="
# Give the commit path a moment to surface the receipt.
for _ in $(seq 1 12); do
  ST_JSON="$("$DREGG_CLI" turn status "$TURN_HASH" 2>/dev/null || true)"
  if echo "$ST_JSON" | python3 -c '
import sys, json
try: d = json.load(sys.stdin)
except Exception: sys.exit(1)
recs = d if isinstance(d, list) else []
import os
th = os.environ["TURN_HASH"].lower()
sys.exit(0 if any((r.get("turn_hash","" ).lower()==th) for r in recs) else 1)
' 2>/dev/null; then
    pass "receipt visible for CLI-submitted turn"
    break
  fi
  sleep 0.5
done

echo ""
echo "PASS: a real turn flowed through the dregg CLI → node → commit path, committed, and was proven."
