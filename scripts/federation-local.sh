#!/usr/bin/env bash
# federation-local.sh — stand up a PRIVATE, localhost-bound, multi-node dregg
# federation on a single box and drive a real cross-node finality check.
#
# This is the "it is actually decentralized, not one node" harness: N distinct
# validator processes (distinct keys, distinct ports), one committee genesis,
# blocklace BFT consensus (Cordial Miners DAG + tau ordering) gossiping over
# QUIC. A turn submitted to ONE node finalizes across the WHOLE committee — the
# same attested-root height climbs identically on every node.
#
#   Usage:
#     scripts/federation-local.sh genesis     # roll a fresh N-validator committee + data dirs
#     scripts/federation-local.sh up          # launch the N node processes
#     scripts/federation-local.sh status      # print /status for every node
#     scripts/federation-local.sh finality    # submit a turn to node0, watch it finalize on all N
#     scripts/federation-local.sh heights [S]  # sample latest_height across all N for S seconds
#     scripts/federation-local.sh down        # stop the federation
#     scripts/federation-local.sh clean       # down + delete the run root
#
# Config (env overridable):
#   FED_N          committee size            (default 4; use 4+ — n=3 is unanimity/zero-slack, see doc)
#   FED_ROOT       run root                  (default ~/dregg-fed-local)
#   FED_BIN        dregg-node binary path    (default: first found under target/{debug,release})
#   FED_HTTP_BASE  base HTTP port            (default 8420 -> 8420,8421,...)
#   FED_GOSSIP_BASE base gossip port         (default 9420 -> 9420,9421,...)
#   FED_BIND       HTTP bind address         (default 127.0.0.1 — LOCALHOST ONLY, do NOT change to 0.0.0.0)
#
# HONEST SCOPE: this runs the MARSHAL (un-verified Rust) executor
# (DREGG_ALLOW_UNVERIFIED_CONSENSUS=1) — the default binary is not Lean-linked.
# CONSENSUS/finality (blocklace BFT, quorum, cross-node attestation) is REAL and
# proven; the STATE PRODUCER is the un-verified reference, not the Lean-shadowed
# kernel. For a verified-producer federation, build the Lean-linked node
# (scripts/bootstrap.sh, see docs/BUILD-LEAN-LINKED-NODE.md) and drop the escape
# hatch. See docs/LOCAL-FEDERATION.md for the full honest-scope discussion.
set -euo pipefail

FED_N="${FED_N:-4}"
FED_ROOT="${FED_ROOT:-$HOME/dregg-fed-local}"
FED_HTTP_BASE="${FED_HTTP_BASE:-8420}"
FED_GOSSIP_BASE="${FED_GOSSIP_BASE:-9420}"
FED_BIND="${FED_BIND:-127.0.0.1}"

find_bin() {
  if [ -n "${FED_BIN:-}" ]; then echo "$FED_BIN"; return; fi
  for c in target/debug/dregg-node target/release/dregg-node \
           "$HOME"/dregg-fed-local/dregg-node ./dregg-node; do
    [ -x "$c" ] && { echo "$c"; return; }
  done
  echo "ERROR: dregg-node binary not found; set FED_BIN=/abs/path/dregg-node" >&2
  exit 1
}
BIN="$(find_bin)"

http_port() { echo $((FED_HTTP_BASE + $1)); }
gossip_port() { echo $((FED_GOSSIP_BASE + $1)); }

cmd_genesis() {
  echo "== genesis: rolling a fresh $FED_N-validator committee =="
  rm -rf "$FED_ROOT"
  mkdir -p "$FED_ROOT/config"
  "$BIN" genesis --validators "$FED_N" --output "$FED_ROOT/config"
  local fedid threshold
  fedid=$(grep -o '"federation_id": *"[0-9a-f]*"' "$FED_ROOT/config/genesis.json" | head -1 | grep -o '[0-9a-f]\{64\}')
  threshold=$(grep -o '"threshold": *[0-9]*' "$FED_ROOT/config/genesis.json" | head -1 | grep -o '[0-9]*')
  echo "   federation_id=$fedid  threshold=$threshold  (of $FED_N)"
  for i in $(seq 0 $((FED_N - 1))); do
    local d="$FED_ROOT/node$i"
    mkdir -p "$d"
    cp "$FED_ROOT/config/genesis.json" "$d/genesis.json"
    cp "$FED_ROOT/config/.devnet" "$d/.devnet"
    cp "$FED_ROOT/config/node-$i.key" "$d/node.key"
    chmod 600 "$d/node.key"
  done
  echo "   data dirs: $FED_ROOT/node0 .. node$((FED_N - 1))"
}

cmd_up() {
  echo "== up: launching $FED_N nodes (marshal executor, blocklace full mode) =="
  for i in $(seq 0 $((FED_N - 1))); do
    local d="$FED_ROOT/node$i" hp gp peers=""
    hp=$(http_port "$i"); gp=$(gossip_port "$i")
    for j in $(seq 0 $((FED_N - 1))); do
      [ "$j" -eq "$i" ] && continue
      peers="${peers:+$peers,}127.0.0.1:$(gossip_port "$j")"
    done
    DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 RUST_LOG="${RUST_LOG:-info}" \
      nohup "$BIN" run \
        --data-dir "$d" --bind "$FED_BIND" --port "$hp" --gossip-port "$gp" \
        --federation-peers "$peers" \
        --federation-mode full --consensus blocklace \
        --idle-heartbeat-ms 2000 --block-cadence-ms 1000 --min-block-interval-ms 1000 \
        --enable-faucet \
        >"$d/node.log" 2>&1 &
    echo $! >"$d/node.pid"
    echo "   node$i: http=$hp gossip=$gp pid=$(cat "$d/node.pid") peers=[$peers]"
  done
  echo "   waiting for HTTP to come up..."
  for i in $(seq 0 $((FED_N - 1))); do
    local hp; hp=$(http_port "$i")
    for _ in $(seq 1 60); do
      curl -sf "http://127.0.0.1:$hp/status" >/dev/null 2>&1 && break
      sleep 1
    done
  done
  echo "   up. run: scripts/federation-local.sh status"
}

cmd_status() {
  for i in $(seq 0 $((FED_N - 1))); do
    local hp; hp=$(http_port "$i")
    printf 'node%s (http %s): ' "$i" "$hp"
    curl -sf "http://127.0.0.1:$hp/status" 2>/dev/null \
      | grep -o '"\(healthy\|peer_count\|latest_height\|dag_height\|block_count\|consensus_live\|federation_mode\|state_producer\)":[^,}]*' \
      | tr '\n' ' ' || echo "DOWN"
    echo
  done
}

# Sample latest_height across all nodes for SEC seconds (default 60).
cmd_heights() {
  local sec="${1:-60}" t=0
  echo "t(s)  $(for i in $(seq 0 $((FED_N-1))); do printf 'n%s ' "$i"; done)"
  while [ "$t" -le "$sec" ]; do
    printf '%4s  ' "$t"
    for i in $(seq 0 $((FED_N - 1))); do
      local hp h; hp=$(http_port "$i")
      h=$(curl -sf "http://127.0.0.1:$hp/status" 2>/dev/null | grep -o '"latest_height":[0-9]*' | grep -o '[0-9]*')
      printf '%3s ' "${h:-x}"
    done
    echo
    sleep 6; t=$((t + 6))
  done
}

# Submit a real state-mutating turn to node0 and confirm cross-node finality.
cmd_finality() {
  local recip amt=1 hp0 resp turn
  hp0=$(http_port 0)
  recip=$(head -c32 /dev/urandom | od -An -tx1 | tr -d ' \n')
  echo "== finality: POST /api/faucet to node0 (recipient=$recip amount=$amt) =="
  resp=$(curl -sf -X POST "http://127.0.0.1:$hp0/api/faucet" \
    -H 'content-type: application/json' \
    -d "{\"recipient\":\"$recip\",\"amount\":$amt}")
  echo "   response: $resp"
  turn=$(echo "$resp" | grep -o '"turn_hash":"[0-9a-f]*"' | grep -o '[0-9a-f]\{64\}' | head -1)
  echo "   turn_hash=$turn"
  echo "== waiting for the turn's receipt to replicate to ALL $FED_N nodes =="
  for _ in $(seq 1 40); do
    local seen=0
    for i in $(seq 0 $((FED_N - 1))); do
      local hp; hp=$(http_port "$i")
      if curl -sf "http://127.0.0.1:$hp/api/receipts" 2>/dev/null | grep -q "$turn"; then
        seen=$((seen + 1))
      fi
    done
    echo "   receipt for $turn present on $seen/$FED_N nodes"
    [ "$seen" -eq "$FED_N" ] && { echo "   CROSS-NODE FINALITY CONFIRMED: turn finalized on all $FED_N nodes"; break; }
    sleep 3
  done
  echo "== final heights (should agree) =="
  cmd_status
}

cmd_down() {
  echo "== down: stopping the federation =="
  for i in $(seq 0 $((FED_N - 1))); do
    local d="$FED_ROOT/node$i"
    if [ -f "$d/node.pid" ]; then
      local pid; pid=$(cat "$d/node.pid")
      kill "$pid" 2>/dev/null && echo "   node$i pid=$pid stopped" || echo "   node$i pid=$pid already gone"
      rm -f "$d/node.pid"
    fi
  done
}

cmd_clean() { cmd_down || true; rm -rf "$FED_ROOT"; echo "== cleaned $FED_ROOT =="; }

case "${1:-}" in
  genesis) cmd_genesis ;;
  up) cmd_up ;;
  status) cmd_status ;;
  heights) shift; cmd_heights "$@" ;;
  finality) cmd_finality ;;
  down) cmd_down ;;
  clean) cmd_clean ;;
  *) echo "usage: $0 {genesis|up|status|heights [sec]|finality|down|clean}" >&2; exit 2 ;;
esac
