#!/usr/bin/env bash
# run-node-10min.sh — from a fresh checkout to a running, health-checked dregg-node in ~10 minutes.
#
# The honest one-script path referenced by QUICKSTART.md. It:
#   1. tries to link the VERIFIED Lean executor via the seed release artifact (minutes), and
#      cleanly falls back to (or lets you choose) a MARSHAL-ONLY build when no seed is available;
#   2. builds dregg-node;
#   3. inits a data dir + starts the node with the faucet on;
#   4. curls /status and REPORTS whether the running node is verified (state_producer:lean) or
#      marshal-only, plus a faucet round-trip to prove a real turn lands.
#
# Usage:
#   scripts/run-node-10min.sh                 # verified if a seed is fetchable, else prompt
#   DREGG_SEED_MODE=marshal scripts/run-node-10min.sh   # skip the seed; marshal-only on purpose
#   DREGG_SEED_MODE=verified scripts/run-node-10min.sh  # require verified; fail if no seed
#   DREGG_NODE_PORT=8421 DREGG_DATA_DIR=/tmp/my-dregg scripts/run-node-10min.sh
#
# It leaves the node RUNNING in the background and prints how to stop it.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
PORT="${DREGG_NODE_PORT:-8421}"
# The gossip/QUIC port, and it MUST NOT be left at the node's 9420 default. The
# HTTP port here is already moved off 8420 so this script can run beside a node
# you started yourself — but gossip was not, and blocklace's bind failure is
# FAIL-OPEN: it logs `failed to create PeerNode for blocklace gossip: Address
# already in use`, returns, and the node serves HTTP forever with
# `consensus_live:false`, `block_count:0`, and every faucet grant accepted and
# never applied. Derive it from the HTTP port so the two move together.
GOSSIP_PORT="${DREGG_GOSSIP_PORT:-$((PORT + 1000))}"
DATA="${DREGG_DATA_DIR:-/tmp/dregg-10min}"
MODE="${DREGG_SEED_MODE:-auto}"     # auto | verified | marshal
PROFILE_DIR=debug

say()  { printf '\n\033[1m==> %s\033[0m\n' "$*"; }
warn() { printf '\033[33m    %s\033[0m\n' "$*"; }
die()  { printf '\n\033[31mFATAL: %s\033[0m\n' "$*" >&2; exit 1; }

command -v cargo >/dev/null 2>&1 || die "cargo not on PATH — install Rust (https://rustup.rs)."
command -v curl  >/dev/null 2>&1 || die "curl not on PATH."

# ── 1. seed (verified path) ───────────────────────────────────────────────────
seed_present() { [ -f dregg-lean-ffi/libdregg_lean.a ]; }
have_lean_toolchain() { command -v lake >/dev/null 2>&1; }

want_verified=0
case "$MODE" in
  verified) want_verified=1 ;;
  marshal)  want_verified=0 ;;
  auto)     want_verified=1 ;;   # try; degrade gracefully
  *) die "DREGG_SEED_MODE must be auto|verified|marshal (got '$MODE')" ;;
esac

if [ "$want_verified" -eq 1 ]; then
  say "Verified path: ensuring the Lean seed is present"
  if seed_present; then
    warn "seed already present ($(du -h dregg-lean-ffi/libdregg_lean.a | cut -f1 | tr -d ' '))."
  elif scripts/fetch-lean-seed.sh; then
    :
  else
    if [ "$MODE" = "verified" ]; then
      die "could not fetch a verified seed and DREGG_SEED_MODE=verified. Cut a seed release (see
  docs/LEAN-SEED-ARTIFACT.md) or run ./scripts/bootstrap.sh (slow), then re-run."
    fi
    warn "no seed available — falling back to a MARSHAL-ONLY (un-verified) build."
    warn "to get a verified node: cut a seed release (docs/LEAN-SEED-ARTIFACT.md) or ./scripts/bootstrap.sh."
    want_verified=0
  fi
fi

if [ "$want_verified" -eq 1 ]; then
  if ! have_lean_toolchain; then
    if [ "$MODE" = "verified" ]; then
      die "the seed is present but elan/lake is not on PATH — the seed links against the Lean
  toolchain runtime. Install elan: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh"
    fi
    warn "elan/lake not on PATH — the seed can't link without the toolchain; building marshal-only."
    warn "install elan (minutes, no mathlib compile) for the verified node: https://elan.lean-lang.org"
    want_verified=0
  else
    # Make the sysroot explicit so the build never falls back to marshal-only for a lookup miss.
    if [ -z "${DREGG_LEAN_SYSROOT:-}" ]; then
      # stderr is KEPT. It used to go to /dev/null, so a broken elan toolchain
      # produced an empty sysroot, no message, and a build that quietly degraded.
      if sr="$(cd metatheory && lake env printenv LEAN_SYSROOT)" && [ -n "$sr" ]; then
        export DREGG_LEAN_SYSROOT="$sr"
        warn "DREGG_LEAN_SYSROOT=$sr"
      else
        warn "could not read LEAN_SYSROOT from metatheory (lake output above) — the build will
    look the sysroot up itself, and DREGG_REQUIRE_LEAN=1 will fail loud if it cannot."
      fi
    fi
    export DREGG_REQUIRE_LEAN=1    # fail loud rather than silently degrade
  fi
fi

# ── 2. build ──────────────────────────────────────────────────────────────────
say "Building dregg-node (first build links the Lean archive — a few minutes)"
if [ "$want_verified" -eq 1 ]; then
  cargo build -p dregg-node || die "verified build failed — read the panic above (usually a stale
  seed vs Lean HEAD, or a missing toolchain). See docs/BUILD-LEAN-LINKED-NODE.md."
else
  DREGG_REQUIRE_LEAN=0 cargo build -p dregg-node || die "marshal-only build failed."
fi
BIN="target/$PROFILE_DIR/dregg-node"
[ -x "$BIN" ] || die "node binary not found at $BIN"

# ── 3. lay down a chain ───────────────────────────────────────────────────────
# `init` mints the chain: a one-validator genesis.json (carrying the consensus
# clock policy `run` refuses to start without), the devnet faucet supply and
# wells, the agent keys the boot-time starbridge seeding needs, and node.key AS
# THE COMMITTEE MEMBER's key.
#
# This used to be `genesis --output "$DATA-genesis"` followed by copying two files
# across, because `init` wrote nothing but an empty dir and an unrelated random
# key. Two things came of that workaround and both are gone now: a node.key that
# was not the published committee member (boots fine, then fails EVERY durable
# commit with "faithful note-root attestation has no valid author signature"), and
# a data dir missing agent-alice.key, which made the node skip all ten starbridge
# factory cells at boot.
#
# Output is NOT redirected to /dev/null. It was, and that is how a HARD BREAK hid:
# genesis never installed the verified PQ cores, so minting the committee ML-DSA
# key hit dregg-pq's fail-closed gate and died with `Abort trap: 6` — and the
# operator saw only "failed", never the gate's message naming the cause and the
# fix. The output stays visible so the NEXT thing that refuses here says so.
say "Minting a one-validator chain in $DATA (genesis.json + the committee key)"
rm -rf "$DATA"
"$BIN" init --data-dir "$DATA" || die "dregg-node init failed"
[ -f "$DATA/genesis.json" ] || die "init did not write $DATA/genesis.json"
[ -f "$DATA/node.key" ]     || die "init did not write $DATA/node.key"

# ── 4. run ────────────────────────────────────────────────────────────────────
say "Starting the node (data dir $DATA, http $PORT, gossip $GOSSIP_PORT, faucet on)"
# A seedless (marshal-only) build REFUSES to start unless the operator explicitly
# opts in — fail-closed by design. This script already told you which mode it
# built, so make the opt-in here rather than dying at a refusal the caller cannot
# read from a backgrounded process.
if [ "$want_verified" -eq 1 ]; then
  "$BIN" run --data-dir "$DATA" --enable-faucet --port "$PORT" --gossip-port "$GOSSIP_PORT" \
    >"$DATA/node.log" 2>&1 &
else
  DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 \
    "$BIN" run --data-dir "$DATA" --enable-faucet --port "$PORT" --gossip-port "$GOSSIP_PORT" \
      >"$DATA/node.log" 2>&1 &
fi
NODE_PID=$!
# wait for /status to answer (up to ~30s).
ok=0
for _ in $(seq 1 60); do
  if curl -fs "http://localhost:$PORT/status" >/dev/null 2>&1; then ok=1; break; fi
  sleep 0.5
done
[ "$ok" -eq 1 ] || { tail -20 "$DATA/node.log"; die "node did not answer /status (pid $NODE_PID). Log above."; }

# ANSWERING /status IS NOT BEING ALIVE. If blocklace cannot bind its gossip port
# it logs an error, returns, and the node serves HTTP forever without ever
# reaching consensus — no blocks, and every faucet grant accepted and never
# applied. That is the single most likely reason this script fails on a box that
# is already running a node, and it used to be invisible: the HTTP readiness probe
# above passed, the faucet answered success, and the script printed its green
# banner over the top of a node that had finalized nothing.
if grep -q "failed to create PeerNode for blocklace gossip" "$DATA/node.log"; then
  grep "failed to create PeerNode for blocklace gossip" "$DATA/node.log" | tail -1
  kill "$NODE_PID" 2>/dev/null || true   # it can never work; do not leave it holding the store
  die "blocklace could not bind gossip port $GOSSIP_PORT — this node will never reach
  consensus and no turn will ever land. Something else holds that port (another
  dregg-node, most likely). Re-run with a free one:
      DREGG_GOSSIP_PORT=<free-port> DREGG_NODE_PORT=$PORT $0"
fi

# ── 5. unlock ─────────────────────────────────────────────────────────────────
# Block production SIGNS. Until the first unlock the node answers reads, accepts
# submissions, and finalizes NOTHING (dag_height stays 0, healthy stays false) —
# including the faucet grant below. The first unlock sets the passphrase.
say "Unlocking the cipherclerk (nothing finalizes until this happens)"
# The body is PRINTED on failure, not discarded into /dev/null. `curl -fs` gives
# you an exit code and nothing else; the node's refusal message is in the body.
UNLOCK="$(curl -s -w '\n%{http_code}' -X POST "http://localhost:$PORT/cipherclerk/unlock" \
  -H 'content-type: application/json' -d '{"passphrase":"dregg-10min"}')"
UNLOCK_CODE="${UNLOCK##*$'\n'}"
if [ "$UNLOCK_CODE" != "200" ]; then
  printf '    HTTP %s: %s\n' "$UNLOCK_CODE" "${UNLOCK%$'\n'*}"
  die "cipherclerk unlock failed — the node cannot sign, so no turn will ever land"
fi
# Wait for the node to be HEALTHY. This is a GATE, not a courtesy pause: without
# consensus the node accepts turns and applies none of them, and everything below
# would report success over a chain that never moved.
#
# `healthy` is exactly three things — store readable, consensus task attached
# (`consensus_live`), and at least one block in the local DAG. Waiting on
# `consensus_live` alone was not enough: it flips true a beat before the first
# block is anchored, so the /status line printed just below read `healthy:false`,
# `dag_height:0`, `block_count:0` — the same fingerprint as a node that is broken —
# on a run that then worked. Wait for the whole thing and print a true status.
ready=0
for _ in $(seq 1 120); do
  curl -fs "http://localhost:$PORT/status" | grep -q '"healthy":true' && { ready=1; break; }
  sleep 0.5
done
if [ "$ready" -ne 1 ]; then
  LAST="$(curl -fs "http://localhost:$PORT/status" || echo '<no answer>')"
  printf '    last /status: %s\n' "$LAST"
  tail -20 "$DATA/node.log"
  die "the node never became healthy within 60s. \`healthy\` is store-readable +
  consensus attached + at least one block; the /status line above says which leg is
  missing. \`consensus_live:false\` means it is finalizing nothing and no turn
  submitted to it will ever be applied. Log tail above; $DATA/node.log has the rest.
  Left running as pid $NODE_PID; stop it with: kill $NODE_PID"
fi

# ── 6. verify ─────────────────────────────────────────────────────────────────
say "Node is up — /status:"
STATUS="$(curl -fs "http://localhost:$PORT/status")"
echo "    $STATUS"
# NB: extract with POSIX BRE only ([a-z]* — NOT \|, which BSD/macOS sed does not support).
producer="$(echo "$STATUS" | sed -n 's/.*"state_producer":"\([^"]*\)".*/\1/p')"
leanp="$(echo "$STATUS" | sed -n 's/.*"lean_producer":\([a-z][a-z]*\).*/\1/p')"

say "Faucet round-trip (a real verified turn lands)"
CID="$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')"
# Body AND status code. `curl -fs || true` threw both away on failure and printed
# an empty line where the node's refusal was.
FR="$(curl -s -w '\n%{http_code}' -X POST "http://localhost:$PORT/api/faucet" \
      -H 'content-type: application/json' -d "{\"recipient\":\"$CID\",\"amount\":1000}")"
FR_CODE="${FR##*$'\n'}"
FR="${FR%$'\n'*}"
echo "    HTTP $FR_CODE: $FR"
[ "$FR_CODE" = "200" ] || die "the faucet endpoint refused the request (HTTP $FR_CODE).
  Was the node started with --enable-faucet? Body above."
# `success:true` is the SUBMISSION answering, not the money moving: the grant is
# applied by FINALIZATION a moment later. Read the LEDGER back, because a grant
# that commits into a block and never credits anyone is exactly what shipped
# between 2026-07-21 and 2026-07-25 while this line said success.
granted=0
for _ in $(seq 1 60); do
  CELL="$(curl -fs "http://localhost:$PORT/api/cell/$CID" || true)"
  case "$CELL" in *'"balance":1000'*) granted=1; break;; esac
  sleep 0.5
done
if [ "$granted" -eq 1 ]; then
  printf '    \033[32mgrant CREDITED on the ledger (balance 1000) — finalization ran.\033[0m\n'
else
  # A FAILURE, and the script exits like one. It used to print this in red, then
  # print the green "VERIFIED node running" banner underneath it, and exit 0 — so
  # a newcomer following QUICKSTART saw the last line and a shell that succeeded.
  # The script knew; it just did not say so where anything could read it.
  printf '    \033[31mgrant NOT credited after 30s: %s\033[0m\n' "${CELL:-<no response>}"
  printf '    The faucet answered success; the ledger disagrees, so the node accepted a\n'
  printf '    turn it never applied. Node still running as pid %s for you to inspect.\n' "$NODE_PID"
  grep -E "failed application authorization|faithful note-root attestation|deterministic rejection recorded" \
    "$DATA/node.log" | tail -5
  die "faucet round-trip did not land — this node is NOT usable. Full log: $DATA/node.log
  Stop it with: kill $NODE_PID"
fi

echo
if [ "$producer" = "lean" ] && [ "$leanp" = "true" ]; then
  printf '\033[32m==> VERIFIED node running: state_producer=lean (the proved Lean executor).\033[0m\n'
else
  printf '\033[33m==> MARSHAL-ONLY node running: state_producer=%s (un-verified Rust executor).\033[0m\n' "${producer:-?}"
  printf '    For a verified node: fetch a seed (scripts/fetch-lean-seed.sh) + elan, then re-run.\n'
fi
cat <<EOF

  Node PID: $NODE_PID   ·   log: $DATA/node.log   ·   http://localhost:$PORT
  Try:   curl -s http://localhost:$PORT/status
         curl -s http://localhost:$PORT/api/cell/$CID
         ./target/$PROFILE_DIR/dregg --node-url http://localhost:$PORT demo --passphrase dregg-10min
  Stop:  kill $NODE_PID
  Next:  QUICKSTART.md (§2 the CLI, §4 the guided demo, §9 the federation read surface)
EOF
