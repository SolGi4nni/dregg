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
#     scripts/federation-join-poles.sh all           # genesis, up, all three poles
#     scripts/federation-join-poles.sh genesis|up|pole1|pole2|restart|report|down|clean
#
# Pole 3 (`restart`) is the one that was coded and never run: a live-joined
# validator is in NOBODY's genesis.json, so every node must relearn its ML-DSA-65
# key by scanning the chain at boot, or come back with `projected < admitted` and
# fail finality closed. See `cmd_restart`.
#
# Config (env overridable):
#   JP_N        committee size                (default 4)
#   JP_ROOT     run root                      (default ~/dregg-join-poles)
#   JP_BIN      dregg-node binary             (default: target/debug/dregg-node)
#   JP_HTTP     base HTTP port                (default 8460)
#   JP_GOSSIP   base gossip port              (default 9460)
#   JP_WAIT     seconds to wait for admission (default 180)
#   JP_CADENCE_MS    committee block cadence   (default 1000)
#   JP_HEARTBEAT_MS  committee idle heartbeat  (default 2000)
#
# ⚑ WHY THE CADENCE IS A KNOB, measured 2026-08-09 on hbox with an idle box.
# `produce_round_block` holds `lace.write()` across the VERIFIED ES round-advance
# gate FFI (`blocklace_sync.rs:1391` takes the lock, `:1438` consults the gate),
# and that gate is super-quadratic in lace size: `RoundAdvanceGate.advanceGateFast`
# → `mkPastCache` → `causalPastIncl` → `causalPastAux` → `List.filterTR_loop` →
# `List.elem`, a LINEAR list membership inside a nested walk. It runs inline on a
# tokio worker with NO `spawn_blocking` and NO budget (unlike the tau-order FFI,
# which has `verified_order_ffi_timeout`). At `--block-cadence-ms 1000` all four
# nodes reached `r=11` about 110 s in and every one of them wedged there —
# `lace.write()` held, 100% CPU each, `/status` timing out, `dag_height` frozen —
# stacks captured from three of them, identical. A debug-build candidate needs
# ~216 s just to finish genesis and send its first join request, so at a 1 s
# cadence the committee is ALREADY past the wall before pole 1 can start. Raising
# the cadence moves the wall out linearly while the lace grows slower; it does not
# fix anything and is not a substitute for the gate being cheap.
#
# ⚠ SO A PASS HERE IS NOT A CLAIM THAT THE FEDERATION IS HEALTHY. It is a claim
# about MEMBERSHIP ADMISSION, measured inside the window before the gate wall.
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
JP_CADENCE_MS="${JP_CADENCE_MS:-1000}"
JP_HEARTBEAT_MS="${JP_HEARTBEAT_MS:-2000}"

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
  echo "== up: launching $JP_N committee nodes (cadence=${JP_CADENCE_MS}ms heartbeat=${JP_HEARTBEAT_MS}ms) =="
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
        --idle-heartbeat-ms "$JP_HEARTBEAT_MS" --block-cadence-ms "$JP_CADENCE_MS" \
        --min-block-interval-ms "$JP_CADENCE_MS" \
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

cmd_restart() {
  echo
  echo "=============================================================="
  echo "POLE 3 — the federation SURVIVES A RESTART with a live-joined member"
  echo "=============================================================="
  # ⚑ WHY THIS EXISTS. `known_federation_ml_dsa_keys` is re-read from
  # `genesis.json` on EVERY boot, and a validator admitted by a LIVE join is not
  # in anyone's genesis.json. Committee replay restores it as a PARTICIPANT
  # anyway, so without the chain-scan restore in `run_blocklace_sync` every node
  # comes back with `projected < admitted` and `poll_finalized_blocks` FAILS
  # CLOSED: right committee, zero finality. A restart would silently un-join a
  # live validator and halt the federation. That path was coded and never run.
  local hp0 chp; hp0=$(http_port 0); chp=$(http_port "$CAND_IDX")

  # ── THE MUTATION, ASSERTED PRESENT BEFORE ANY VERDICT IS READ ──────────────
  # A restart is only evidence about live-joined keys if a member actually
  # joined LIVE. On a federation that never admitted anyone, every node restores
  # from genesis alone, the restore scan is a no-op, and this pole would pass
  # while proving nothing.
  local n_before; n_before=$(participants_on "$hp0")
  local cand_member; cand_member=$(api "$chp" /status | jqf 'd.get("join_member","absent")')
  echo "   participants before restart : $n_before (expected $((JP_N + 1)))"
  echo "   candidate join_member       : $cand_member"
  if [ "$n_before" != "$((JP_N + 1))" ] || [ "$cand_member" != "True" ]; then
    echo "   FATAL: no live-joined member is in this committee — pole 3 would be vacuous" >&2
    return 1
  fi
  local h_before; h_before=$(api "$hp0" /status | jqf 'd.get("dag_height",0)')
  echo "   node0 dag_height before     : $h_before"

  # ── DOWN, ALL OF THEM ──────────────────────────────────────────────────────
  echo "   -- stopping every node (committee + the live-joined member) --"
  for d in "$JP_ROOT"/node* "$JP_ROOT/candidate"; do
    [ -f "$d/node.pid" ] || continue
    kill "$(cat "$d/node.pid")" 2>/dev/null || true
  done
  for _ in $(seq 1 40); do
    pgrep -f "$JP_BIN (run|join)" >/dev/null 2>&1 || break
    sleep 1
  done
  pkill -9 -f "$JP_BIN (run|join)" 2>/dev/null || true
  sleep 2
  # Each node's log is rolled so the post-restart evidence cannot be confused
  # with the pre-restart run's.
  for d in "$JP_ROOT"/node* "$JP_ROOT/candidate"; do
    [ -f "$d/node.log" ] && mv "$d/node.log" "$d/node.prerestart.log"
  done
  echo "   -- all down --"

  # ── UP AGAIN, from the SAME data dirs ──────────────────────────────────────
  launch_committee
  launch_joiner candidate "$CAND_IDX"
  sleep 20

  # ── DID THE RESTORE ACTUALLY FIRE? ─────────────────────────────────────────
  # If it did not, whatever finality we observe afterwards is not evidence about
  # this path — it would mean the federation never needed it.
  echo "   -- chain-scan restore of live-joined ML-DSA-65 keys, per node --"
  local fired=0
  for i in $(seq 0 $((JP_N - 1))); do
    local line
    line=$(grep -ah "restored live-joined members" "$JP_ROOT/node$i/node.log" | tail -1)
    if [ -n "$line" ]; then
      fired=$((fired + 1))
      printf '   node%s: %s\n' "$i" "$(echo "$line" | grep -o 'restored_keys=[0-9]*')"
    else
      printf '   node%s: NO RESTORE LINE\n' "$i"
    fi
  done
  if [ "$fired" -eq 0 ]; then
    echo "   FATAL: not one node restored a live-joined key — this restart exercised nothing" >&2
    return 1
  fi

  # ── THE FAILURE THIS PREVENTS, named so its absence is meaningful ──────────
  echo "   -- fail-closed finality halts (the un-joined-on-restart signature) --"
  grep -ahc "projected < admitted\|fail.closed" "$JP_ROOT"/node*/node.log 2>/dev/null | paste -sd' ' - || true

  # ── VERDICT: does finality ADVANCE after the restart? ──────────────────────
  echo "   -- does the chain move again? --"
  local h_after t=0
  while [ "$t" -lt 90 ]; do
    h_after=$(api "$hp0" /status | jqf 'd.get("dag_height",0)')
    printf '   t=%2ss node0 dag_height=%s participants=%s\n' \
      "$t" "$h_after" "$(participants_on "$hp0")"
    sleep 10; t=$((t + 10))
  done
  echo "   -- post-restart status, every node --"
  for i in $(seq 0 $((JP_N - 1))) "$CAND_IDX"; do
    local p; p=$(http_port "$i")
    printf '   port %s: ' "$p"
    api "$p" /status | jqf '" ".join(f"{k}={d[k]}" for k in ("healthy","dag_height","latest_height","quorum_reachable","finality_stalled","live_committee_voters","ever_reached_quorum","join_member") if k in d)'
  done
}

cmd_report() {
  echo
  echo "=============================================================="
  echo "REPORT"
  echo "=============================================================="
  for i in $(seq 0 $((JP_N - 1))) "$CAND_IDX" "$IMP_IDX"; do
    local p; p=$(http_port "$i")
    printf 'port %s: ' "$p"
    api "$p" /status | jqf '" ".join(f"{k}={d[k]}" for k in ("healthy","peer_count","latest_height","dag_height","block_count","consensus_live","quorum_reachable","finality_stalled","join_member","join_requests_sent","join_waiting_secs","join_proposal_seen") if k in d)'
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
  restart) cmd_restart ;;
  report) cmd_report ;;
  down) cmd_down ;;
  clean) cmd_clean ;;
  all) cmd_genesis; cmd_up; cmd_pole1; cmd_pole2; cmd_restart; cmd_report ;;
  *) echo "usage: $0 {genesis|up|pole1|pole2|restart|report|down|clean|all}" >&2; exit 2 ;;
esac
