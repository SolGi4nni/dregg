#!/usr/bin/env bash
# federation-join-poles.sh — drive BOTH poles of federation growth on REAL,
# separate `dregg-node` processes: a candidate that must get in, and one that
# must not.
#
# This exists because the join path was broken in a way no single-process `Node`
# test could have seen. Measured 2026-08-08 on a 4-node federation: the
# candidate authored a Join block, logged `proposed join to federation`, and
# that block id appeared in ZERO committee-node logs — every member dropped the
# envelope at the transport as an `unknown sender`, ~7,300 WARNs per node in
# three minutes, `participants=4, proposals=0` on all five nodes forever, and
# the wedged candidate reporting `"healthy": true`. Everything below is measured
# from the nodes' own HTTP surfaces and their own logs, never from an in-process
# value.
#
#   Usage:
#     scripts/federation-join-poles.sh all           # genesis, up, both poles
#     scripts/federation-join-poles.sh genesis|up|pole1|pole2|report|down|clean
#
# Config (env overridable):
#   JP_N        committee size                (default 4)
#   JP_ROOT     run root                      (default ~/dregg-join-poles)
#   JP_BIN      dregg-node binary             (default: target/debug/dregg-node)
#   JP_HTTP     base HTTP port                (default 8460)
#   JP_GOSSIP   base gossip port              (default 9460)
#   JP_WAIT     seconds to wait for admission (default 180)
#
# HONEST SCOPE: this runs the MARSHAL (un-verified Rust) executor
# (DREGG_ALLOW_UNVERIFIED_CONSENSUS=1) exactly as `federation-local.sh` does.
# What is under test here is MEMBERSHIP ADMISSION and the gossip gate, both of
# which are the same code in a Lean-linked build.
set -euo pipefail

JP_N="${JP_N:-4}"
JP_ROOT="${JP_ROOT:-$HOME/dregg-join-poles}"
JP_HTTP="${JP_HTTP:-8460}"
JP_GOSSIP="${JP_GOSSIP:-9460}"
JP_WAIT="${JP_WAIT:-180}"
JP_BIN="${JP_BIN:-target/debug/dregg-node}"

# The candidate and the impostor sit above the committee's port block.
CAND_IDX=$JP_N
IMP_IDX=$((JP_N + 1))

http_port() { echo $((JP_HTTP + $1)); }
gossip_port() { echo $((JP_GOSSIP + $1)); }

api() { curl -sf --max-time 5 "http://127.0.0.1:$1$2" 2>/dev/null || echo '{}'; }

jqf() { python3 -c "import sys,json;d=json.load(sys.stdin);print($1)" 2>/dev/null || echo "?"; }

cmd_genesis() {
  echo "== genesis: a fresh $JP_N-validator committee =="
  rm -rf "$JP_ROOT"; mkdir -p "$JP_ROOT/config"
  "$JP_BIN" genesis --validators "$JP_N" --output "$JP_ROOT/config" >"$JP_ROOT/genesis.log" 2>&1
  for i in $(seq 0 $((JP_N - 1))); do
    d="$JP_ROOT/node$i"; mkdir -p "$d"
    cp "$JP_ROOT/config/genesis.json" "$d/genesis.json"
    cp "$JP_ROOT/config/.devnet" "$d/.devnet"       # == --auto-approve-joins
    cp "$JP_ROOT/config/node-$i.key" "$d/node.key"; chmod 600 "$d/node.key"
  done

  # THE CANDIDATE (pole 1): the federation's real genesis descriptor, a key that
  # is NOT in the committee, and no `.devnet` (it is not approving anything).
  mkdir -p "$JP_ROOT/candidate"
  cp "$JP_ROOT/config/genesis.json" "$JP_ROOT/candidate/genesis.json"

  # THE IMPOSTOR (pole 2): a well-formed node with a VALID key of its own, asking
  # to join a federation it has no descriptor for. Its request is genuinely
  # signed and self-certifying — the transport will carry it — so what refuses it
  # is the MEMBERSHIP rule, which is the thing under test. A malformed byte
  # string would prove nothing: it would die in the parser.
  mkdir -p "$JP_ROOT/impostor" "$JP_ROOT/otherfed"
  "$JP_BIN" genesis --validators 1 --output "$JP_ROOT/otherfed" >"$JP_ROOT/otherfed.log" 2>&1
  cp "$JP_ROOT/otherfed/genesis.json" "$JP_ROOT/impostor/genesis.json"

  ours=$(grep -o '"federation_id": *"[0-9a-f]*"' "$JP_ROOT/config/genesis.json" | head -1 | grep -o '[0-9a-f]\{64\}')
  theirs=$(grep -o '"federation_id": *"[0-9a-f]*"' "$JP_ROOT/impostor/genesis.json" | head -1 | grep -o '[0-9a-f]\{64\}')
  echo "   committee federation_id = $ours"
  echo "   impostor  federation_id = $theirs"
  # THE MUTATION, ASSERTED PRESENT BEFORE ANY VERDICT IS READ.
  [ -n "$ours" ] && [ -n "$theirs" ] && [ "$ours" != "$theirs" ] || {
    echo "FATAL: the impostor's federation id is not actually different — pole 2 would be vacuous" >&2
    exit 1
  }
  echo "$ours"  >"$JP_ROOT/ours.fedid"
  echo "$theirs" >"$JP_ROOT/theirs.fedid"
}

launch_committee() {
  echo "== up: launching $JP_N committee nodes =="
  for i in $(seq 0 $((JP_N - 1))); do
    d="$JP_ROOT/node$i"; hp=$(http_port "$i"); gp=$(gossip_port "$i"); peers=""
    for j in $(seq 0 $((JP_N - 1))); do
      [ "$j" -eq "$i" ] && continue
      peers="${peers:+$peers,}127.0.0.1:$(gossip_port "$j")"
    done
    DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 RUST_LOG="${RUST_LOG:-info}" \
      nohup "$JP_BIN" run \
        --data-dir "$d" --bind 127.0.0.1 --port "$hp" --gossip-port "$gp" \
        --federation-peers "$peers" \
        --federation-mode full --consensus blocklace \
        --idle-heartbeat-ms 2000 --block-cadence-ms 1000 --min-block-interval-ms 1000 \
        --enable-faucet \
        >"$d/node.log" 2>&1 &
    echo $! >"$d/node.pid"
    echo "   node$i http=$hp gossip=$gp pid=$(cat "$d/node.pid")"
  done
  for i in $(seq 0 $((JP_N - 1))); do
    hp=$(http_port "$i")
    for _ in $(seq 1 90); do api "$hp" /status | grep -q dag_height && break; sleep 1; done
  done
  echo "   committee up"
}

launch_joiner() {
  local name="$1" idx="$2" d="$JP_ROOT/$1"
  local hp gp; hp=$(http_port "$idx"); gp=$(gossip_port "$idx")
  DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 RUST_LOG="${RUST_LOG:-info}" \
    nohup "$JP_BIN" join \
      --bootstrap "127.0.0.1:$(gossip_port 0)" \
      --data-dir "$d" --bind 127.0.0.1 --port "$hp" --gossip-port "$gp" \
      >"$d/node.log" 2>&1 &
  echo $! >"$d/node.pid"
  echo "   $name http=$hp gossip=$gp pid=$(cat "$d/node.pid") bootstrap=127.0.0.1:$(gossip_port 0)"
}

cmd_up() { launch_committee; }

participants_on() { api "$1" /api/membership | jqf 'len(d.get("participants",[]))'; }
proposals_on()    { api "$1" /api/membership | jqf 'len(d.get("proposals",[]))'; }

cmd_pole1() {
  echo
  echo "=============================================================="
  echo "POLE 1 — a candidate joins a LIVE committee, end to end"
  echo "=============================================================="
  local hp0; hp0=$(http_port 0)
  echo "   before: participants=$(participants_on "$hp0") proposals=$(proposals_on "$hp0")"
  launch_joiner candidate "$CAND_IDX"
  local chp; chp=$(http_port "$CAND_IDX")
  local t=0 n
  while [ "$t" -lt "$JP_WAIT" ]; do
    n=$(participants_on "$hp0")
    if [ "$n" = "$((JP_N + 1))" ]; then
      echo "   ADMITTED after ${t}s: participants=$n on node0"
      break
    fi
    printf '   t=%3ss participants=%s proposals=%s candidate_dag=%s\n' \
      "$t" "$n" "$(proposals_on "$hp0")" "$(api "$chp" /status | jqf 'd.get("dag_height","?")')"
    sleep 6; t=$((t + 6))
  done
  echo "   -- membership on EVERY node --"
  for i in $(seq 0 $((JP_N - 1))) "$CAND_IDX"; do
    local p; p=$(http_port "$i")
    echo "   port $p: participants=$(participants_on "$p") proposals=$(proposals_on "$p") self_participant=$(api "$p" /api/membership | jqf 'd.get("self",{}).get("participant","?")')"
  done
}

cmd_pole2() {
  echo
  echo "=============================================================="
  echo "POLE 2 — an UNAUTHORIZED join is refused, by name"
  echo "=============================================================="
  local hp0 before_p before_n
  hp0=$(http_port 0)
  before_p=$(proposals_on "$hp0"); before_n=$(participants_on "$hp0")
  echo "   before: participants=$before_n proposals=$before_p"
  launch_joiner impostor "$IMP_IDX"
  echo "   waiting 60s for the impostor to send and re-send its request..."
  sleep 60
  echo "   after:  participants=$(participants_on "$hp0") proposals=$(proposals_on "$hp0")"
  echo "   -- committee-side refusals, by name --"
  grep -ah "join request refused\|join request REFUSED" "$JP_ROOT"/node*/node.log | tail -8 || \
    echo "   (no refusal line found — THIS IS A FAILURE unless the impostor never reached anyone)"
  echo "   -- did any node ACCEPT it? --"
  grep -ah "join request ACCEPTED" "$JP_ROOT"/node*/node.log | tail -5 || echo "   (none — correct)"
}

cmd_report() {
  echo
  echo "=============================================================="
  echo "REPORT"
  echo "=============================================================="
  for i in $(seq 0 $((JP_N - 1))) "$CAND_IDX" "$IMP_IDX"; do
    local p; p=$(http_port "$i")
    printf 'port %s: ' "$p"
    api "$p" /status | jqf '" ".join(f"{k}={d[k]}" for k in ("healthy","peer_count","latest_height","dag_height","block_count","consensus_live") if k in d)'
  done
  echo
  echo "-- unknown_sender WARN counts (the old failure's signature) --"
  for i in $(seq 0 $((JP_N - 1))); do
    printf '   node%s: %s\n' "$i" "$(grep -ac 'unknown sender' "$JP_ROOT/node$i/node.log" || true)"
  done
  echo
  echo "-- narrow-channel admissions --"
  grep -ahc "narrow join channel: admitted" "$JP_ROOT"/node*/node.log 2>/dev/null | paste -sd' ' - || true
  echo
  echo "-- candidate's own join log --"
  grep -ah "join request\|now a federation participant" "$JP_ROOT/candidate/node.log" | tail -12 || true
}

cmd_down() {
  for d in "$JP_ROOT"/node* "$JP_ROOT/candidate" "$JP_ROOT/impostor"; do
    [ -f "$d/node.pid" ] || continue
    kill "$(cat "$d/node.pid")" 2>/dev/null || true
    rm -f "$d/node.pid"
  done
  echo "== down =="
}

cmd_clean() { cmd_down || true; rm -rf "$JP_ROOT"; }

case "${1:-}" in
  genesis) cmd_genesis ;;
  up) cmd_up ;;
  pole1) cmd_pole1 ;;
  pole2) cmd_pole2 ;;
  report) cmd_report ;;
  down) cmd_down ;;
  clean) cmd_clean ;;
  all) cmd_genesis; cmd_up; cmd_pole1; cmd_pole2; cmd_report ;;
  *) echo "usage: $0 {genesis|up|pole1|pole2|report|down|clean|all}" >&2; exit 2 ;;
esac
