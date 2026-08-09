#!/usr/bin/env bash
# federation-leave-poles.sh — drive BOTH poles of federation SHRINKAGE on REAL,
# separate `dregg-node` processes.
#
# The join half of reconfiguration has a harness (`federation-join-poles.sh`).
# Leaving did not, and leaving is the direction the literature says you cannot
# make promises in: DBRB App. A.6 Thms. 81/82 prove — crash-only, one fault, a
# model strictly weaker than ours — that no algorithm can promise a departing
# participant delivery. So there is nothing to measure ON THE LEAVER. What is
# measurable, and what this script measures, is on the SURVIVORS:
#
#   POLE 1 — CONTINUE.  A member leaves a 5-node committee. Every survivor
#     installs the removal at the same committed position, the quorum threshold
#     moves 4 -> 3 (`supermajority_threshold`), the departing member's in-flight
#     finalization votes are RETIRED by the D7 drain
#     (`VoteCollector::retire_departed_votes`, the transcription of the authored
#     Lean rule `Dregg2.Distributed.LeaveDrain.drainTally`), and a NEW turn
#     submitted afterwards still finalizes across the survivors. The federation
#     kept running across the departure.
#
#   POLE 2 — REFUSED BY NAME.  The same removal from a 4-node committee is
#     REFUSED: `4 -> 3` lands on a roster whose Byzantine budget is ZERO, so the
#     Lean-authored step bound (`ConfigBoundary.classifyStep 4 0 1 =
#     .refuseRosterFloor`, transcribed as `constitution::config_step_allowed`)
#     refuses it and NOTHING is mutated. The committee stays at 4.
#
# ⚠ THE MUTATION IS ASSERTED PRESENT BEFORE THE VERDICT IS READ. Pole 2's
# "committee unchanged" is only evidence if the proposal ACTUALLY REACHED QUORUM
# — an unchanged committee because nobody voted proves nothing at all, and is
# exactly how a red-proof rots into a green no-op. So pole 2 requires
# `approvals >= required` on `/api/membership` BEFORE it looks at the roster, and
# FAILS LOUDLY if the proposal never got there. Same discipline in pole 1: the
# departing node must be a real, live, block-producing member first.
#
#   Usage:
#     scripts/federation-leave-poles.sh all      # genesis, up, both poles, report
#     scripts/federation-leave-poles.sh genesis|up|pole1|pole2|report|down|clean
#
# Config (env overridable):
#   LP_N        committee size for pole 1     (default 5 — 5->4 is an ALLOWED step)
#   LP_N2       committee size for pole 2     (default 4 — 4->3 is a REFUSED step)
#   LP_ROOT     run root                      (default ~/dregg-leave-poles)
#   LP_BIN      dregg-node binary             (default target/debug/dregg-node)
#               ⚠ USE A RELEASE BINARY. Measured 2026-08-09 on this laptop: a
#               DEBUG `dregg-node genesis --validators 5` had not returned after
#               400 s (ML-DSA-65 keygen is the cost, and `federation-join-poles.sh`
#               measures ~216 s for a debug candidate's genesis alone). Nine debug
#               nodes never reach the poles. `LP_BIN=target/release/dregg-node`.
#   LP_HTTP     base HTTP port                (default 8480)
#   LP_GOSSIP   base gossip port              (default 9480)
#   LP_WAIT     seconds to wait for an install (default 120)
#   LP_CADENCE_MS / LP_HEARTBEAT_MS  block cadence knobs (default 3000 / 3000)
#
# ⚑ THE CADENCE IS A KNOB FOR THE SAME REASON THE JOIN HARNESS MAKES IT ONE.
# `produce_round_block` consults the verified ES round-advance gate while holding
# `lace.write()`. That gate was EXPONENTIAL in round depth until `7a181f741`
# (~28 min at r=11 -> 3.8 ms); before that fix a 4-node federation wedged at
# round 11 with every node at 100% CPU and `/status` timing out. THAT FIX HAD
# NOT BEEN EXERCISED BY A REAL FEDERATION when this script was written. If the
# committee freezes at r~11 here, that is the old wall and NOT this script's
# poles failing — check `dag_height` in `report` before reading anything else.
#
# HONEST SCOPE: runs the MARSHAL (un-verified Rust) executor
# (DREGG_ALLOW_UNVERIFIED_CONSENSUS=1), exactly as `federation-local.sh` does.
# Under test here is MEMBERSHIP REMOVAL — the constitution, the step bound, the
# vote-collector drain — which is the same code in a Lean-linked build.
set -euo pipefail

LP_N="${LP_N:-5}"
LP_N2="${LP_N2:-4}"
LP_ROOT="${LP_ROOT:-$HOME/dregg-leave-poles}"
LP_HTTP="${LP_HTTP:-8480}"
LP_GOSSIP="${LP_GOSSIP:-9480}"
LP_WAIT="${LP_WAIT:-120}"
LP_BIN="${LP_BIN:-target/debug/dregg-node}"
LP_CADENCE_MS="${LP_CADENCE_MS:-3000}"
LP_HEARTBEAT_MS="${LP_HEARTBEAT_MS:-3000}"

[ -x "$LP_BIN" ] || { echo "FATAL: no dregg-node at $LP_BIN (set LP_BIN)" >&2; exit 1; }
BIN="$(cd "$(dirname "$LP_BIN")" && pwd)/$(basename "$LP_BIN")"

fail() { echo "‼ POLE FAILED: $*" >&2; exit 1; }
http_port() { echo $((LP_HTTP + $1)); }
gossip_port() { echo $((LP_GOSSIP + $1)); }
# Which committee ("a" = pole 1's LP_N nodes, "b" = pole 2's LP_N2 nodes).
grp_dir() { echo "$LP_ROOT/$1/node$2"; }
grp_n() { case "$1" in a) echo "$LP_N" ;; b) echo "$LP_N2" ;; esac; }
grp_http() { case "$1" in a) echo $((LP_HTTP + $2)) ;; b) echo $((LP_HTTP + 20 + $2)) ;; esac; }
grp_gossip() { case "$1" in a) echo $((LP_GOSSIP + $2)) ;; b) echo $((LP_GOSSIP + 20 + $2)) ;; esac; }

# `GET /api/membership` on one node, raw.
membership_json() {
  local g="$1" i="$2" hp; hp=$(grp_http "$g" "$i")
  curl -sf --max-time 10 "http://127.0.0.1:$hp/api/membership" 2>/dev/null
}

# The ed25519 validator pubkey of node `i` in group `g`, as the node itself
# reports it (never re-derived here — a key this script computed would be a
# second source of truth about identity).
node_pubkey() { membership_json "$1" "$2" | jq -r '.self.key // empty'; }

# How many participants node `i` currently believes the committee has.
participant_count() { membership_json "$1" "$2" | jq -r '(.participants // []) | length'; }

# The quorum threshold node `i` currently enforces.
threshold_of() { membership_json "$1" "$2" | jq -r '.threshold // empty'; }

# The newest un-applied Leave proposal node `i` has seen, and its tally.
leave_proposal_block() {
  membership_json "$1" "$2" | jq -r '[.proposals[]? | select(.kind=="leave")] | last | .proposal_block // empty'
}
leave_tally() {
  membership_json "$1" "$2" \
    | jq -r '[.proposals[]? | select(.kind=="leave")] | last | "\(.approvals // 0) \(.required // 0) \(.applied // false)"'
}

# ── genesis / up ────────────────────────────────────────────────────────────

roll_group() {
  local g="$1" n; n=$(grp_n "$g")
  mkdir -p "$LP_ROOT/$g/config"
  "$BIN" genesis --validators "$n" --output "$LP_ROOT/$g/config" >/dev/null
  for i in $(seq 0 $((n - 1))); do
    local d; d=$(grp_dir "$g" "$i"); mkdir -p "$d"
    cp "$LP_ROOT/$g/config/genesis.json" "$d/genesis.json"
    cp "$LP_ROOT/$g/config/.devnet" "$d/.devnet"
    cp "$LP_ROOT/$g/config/node-$i.key" "$d/node.key"
    chmod 600 "$d/node.key"
  done
  echo "   group $g: $n validators, threshold $(grep -o '"threshold": *[0-9]*' "$LP_ROOT/$g/config/genesis.json" | head -1 | grep -o '[0-9]*')"
}

cmd_genesis() {
  echo "== genesis: two independent committees =="
  rm -rf "$LP_ROOT"; mkdir -p "$LP_ROOT"
  roll_group a
  roll_group b
}

launch_group() {
  local g="$1" n; n=$(grp_n "$g")
  for i in $(seq 0 $((n - 1))); do
    local d hp gp peers=""; d=$(grp_dir "$g" "$i")
    hp=$(grp_http "$g" "$i"); gp=$(grp_gossip "$g" "$i")
    for j in $(seq 0 $((n - 1))); do
      [ "$j" -eq "$i" ] && continue
      peers="${peers:+$peers,}127.0.0.1:$(grp_gossip "$g" "$j")"
    done
    DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 RUST_LOG="${RUST_LOG:-info}" \
      nohup "$BIN" run \
        --data-dir "$d" --bind 127.0.0.1 --port "$hp" --gossip-port "$gp" \
        --federation-peers "$peers" \
        --federation-mode full --consensus blocklace \
        --idle-heartbeat-ms "$LP_HEARTBEAT_MS" --block-cadence-ms "$LP_CADENCE_MS" \
        --min-block-interval-ms "$LP_CADENCE_MS" --enable-faucet \
        >"$d/node.log" 2>&1 &
    echo $! >"$d/node.pid"
  done
  for i in $(seq 0 $((n - 1))); do
    local hp; hp=$(grp_http "$g" "$i")
    for _ in $(seq 1 90); do curl -sf "http://127.0.0.1:$hp/status" >/dev/null 2>&1 && break; sleep 1; done
  done
  echo "   group $g up ($n nodes, http $(grp_http "$g" 0)..$(grp_http "$g" $((n-1))))"
}

cmd_up() { echo "== up =="; launch_group a; launch_group b; }
# Bring up ONE group. Useful on a contended box: pole 2 needs only group b, and
# nine debug nodes beside a release build starve each other.
cmd_up_a() { echo "== up (group a only) =="; launch_group a; }
cmd_up_b() { echo "== up (group b only) =="; launch_group b; }

# ── the removal drive: propose on node0, approve on the rest ────────────────
#
# `propose-epoch-transition --remove` authors the Leave proposal block on a
# RUNNING node; `approve-membership` casts each other operator's vote. Both are
# the deployed operator verbs, not a test back door. Proposing is not authority:
# the change applies only when a quorum of the CURRENT committee ratifies it
# through finality.
drive_removal() {
  local g="$1" victim_idx="$2" n; n=$(grp_n "$g")
  local victim; victim=$(node_pubkey "$g" "$victim_idx")
  [ -n "$victim" ] || fail "could not read node$victim_idx's own pubkey from /api/membership (is it up?)"
  echo "   removing ${victim:0:12}… (node$victim_idx of group $g)"
  "$BIN" propose-epoch-transition --remove "$victim" --port "$(grp_http "$g" 0)" || \
    fail "propose-epoch-transition --remove was rejected by node0"
  # Every OTHER member (including the victim: it is still a member and its vote
  # is still admissible until the install) approves.
  for i in $(seq 1 $((n - 1))); do
    local hp; hp=$(grp_http "$g" "$i")
    local blk; blk=$(leave_proposal_block "$g" "$i")
    if [ -z "$blk" ]; then
      echo "   node$i has not seen the Leave proposal yet; waiting…"
      for _ in $(seq 1 "$LP_WAIT"); do
        blk=$(leave_proposal_block "$g" "$i")
        [ -n "$blk" ] && break
        sleep 2
      done
    fi
    [ -n "$blk" ] || fail "node$i never saw the Leave proposal — the proposal did not replicate, so neither pole can be read"
    "$BIN" approve-membership --proposal "$blk" --port "$hp" >/dev/null 2>&1 || \
      echo "   (node$i approve returned non-zero; its vote may already be counted)"
  done
}

# Wait until the proposal is at or above its required approvals on node0 — the
# MUTATION-PRESENT assertion both poles read their verdict after.
await_quorum() {
  local g="$1"
  for _ in $(seq 1 "$LP_WAIT"); do
    local ap req applied
    read -r ap req applied <<<"$(leave_tally "$g" 0)"
    if [ -n "${ap:-}" ] && [ "$ap" != "null" ] && [ "${req:-0}" -gt 0 ] && [ "$ap" -ge "$req" ]; then
      echo "   Leave proposal reached quorum on node0: approvals=$ap required=$req applied=$applied"
      return 0
    fi
    sleep 2
  done
  echo "   last seen tally on node0: approvals=${ap:-none} required=${req:-none}"
  return 1
}

# ── POLE 1 — CONTINUE ───────────────────────────────────────────────────────

cmd_pole1() {
  echo "== POLE 1 (CONTINUE): a member leaves a $LP_N-node committee =="
  local before_n before_t
  before_n=$(participant_count a 0)
  before_t=$(threshold_of a 0)
  [ "${before_n:-0}" -eq "$LP_N" ] || fail "group a is not at $LP_N participants (got ${before_n:-none}) — nothing to remove"
  echo "   before: participants=$before_n threshold=$before_t"
  # NOTE: `drive_removal` runs in the foreground and its `fail` exits non-zero;
  # keep it OUT of a command substitution so `set -e` still sees the status.
  drive_removal a $((LP_N - 1)) || fail "could not drive the Leave proposal through group a"
  await_quorum a || fail "the Leave never reached quorum on node0 — the mutation is ABSENT, so 'the committee continued' would prove nothing"
  echo "   waiting for every SURVIVOR to install the removal…"
  local ok=0
  for _ in $(seq 1 "$LP_WAIT"); do
    ok=0
    for i in $(seq 0 $((LP_N - 2))); do
      local pc; pc=$(participant_count a "$i")
      [ "${pc:-0}" -eq $((LP_N - 1)) ] && ok=$((ok + 1))
    done
    [ "$ok" -eq $((LP_N - 1)) ] && break
    sleep 2
  done
  [ "$ok" -eq $((LP_N - 1)) ] || fail "only $ok/$((LP_N - 1)) survivors installed the removal within ${LP_WAIT}s"
  local want_t; want_t=$(( (2 * (LP_N - 1)) / 3 + 1 ))
  for i in $(seq 0 $((LP_N - 2))); do
    local t; t=$(threshold_of a "$i")
    [ "${t:-0}" -eq "$want_t" ] || fail "node$i threshold is ${t:-none}, expected supermajority($((LP_N-1))) = $want_t"
  done
  echo "   ✅ every survivor: participants=$((LP_N - 1)) threshold=$want_t"
  # The drain is the mutation this pole is really about; surface it from the
  # nodes' OWN logs rather than an in-process value.
  echo "   D7 drain, from the survivors' own logs:"
  for i in $(seq 0 $((LP_N - 2))); do
    local d; d=$(grp_dir a "$i")
    printf '     node%s: ' "$i"
    grep -o 'D7 leave drain[^"]*' "$d/node.log" | tail -1 \
      || grep -o 'votes_retired=[0-9]* straddles_closed=[0-9]*' "$d/node.log" | tail -1 \
      || echo "(no drain line — the departing member had no in-flight votes at the install, which is a legitimate outcome)"
  done
  # THE COMMITTEE CONTINUES: a fresh turn must still finalize on the survivors.
  echo "   submitting a turn AFTER the removal — it must finalize on every survivor"
  local hp0 resp turn; hp0=$(grp_http a 0)
  resp=$(curl -sf -X POST "http://127.0.0.1:$hp0/api/faucet" -H 'content-type: application/json' \
    -d "{\"recipient\":\"$(head -c32 /dev/urandom | od -An -tx1 | tr -d ' \n')\",\"amount\":1}") \
    || fail "the faucet turn was refused after the removal — the committee did not continue"
  turn=$(echo "$resp" | grep -o '"turn_hash":"[0-9a-f]*"' | grep -o '[0-9a-f]\{64\}' | head -1)
  [ -n "$turn" ] || fail "no turn_hash in the post-removal faucet response: $resp"
  local seen=0
  for _ in $(seq 1 40); do
    seen=0
    for i in $(seq 0 $((LP_N - 2))); do
      local hp; hp=$(grp_http a "$i")
      curl -sf "http://127.0.0.1:$hp/api/receipts" 2>/dev/null | grep -q "$turn" && seen=$((seen + 1))
    done
    [ "$seen" -eq $((LP_N - 1)) ] && break
    sleep 3
  done
  [ "$seen" -eq $((LP_N - 1)) ] \
    || fail "the post-removal turn reached only $seen/$((LP_N - 1)) survivors — the committee did NOT continue"
  echo "   ✅ POLE 1 PASSED: turn $(echo "$turn" | cut -c1-12)… finalized on all $((LP_N - 1)) survivors at threshold $want_t"
}

# ── POLE 2 — REFUSED BY NAME ────────────────────────────────────────────────

cmd_pole2() {
  echo "== POLE 2 (REFUSED BY NAME): the same removal from a $LP_N2-node committee =="
  echo "   Lean: ConfigBoundary.classifyStep $LP_N2 0 1 = .refuseRosterFloor —"
  echo "   shrinking a BFT-capable roster onto one whose fault budget is ZERO."
  local before_n; before_n=$(participant_count b 0)
  [ "${before_n:-0}" -eq "$LP_N2" ] || fail "group b is not at $LP_N2 participants (got ${before_n:-none})"
  drive_removal b $((LP_N2 - 1)) || fail "could not drive the Leave proposal through group b"
  # ⚠ MUTATION PRESENT FIRST. Without this, an unchanged committee is just an
  # un-ratified proposal wearing a refusal's clothes.
  await_quorum b || fail "the Leave never reached quorum on group b — a REFUSAL cannot be read from a proposal that never passed"
  echo "   the proposal PASSED; now the step bound must refuse the install"
  sleep 10
  for i in $(seq 0 $((LP_N2 - 1))); do
    local pc; pc=$(participant_count b "$i")
    [ "${pc:-0}" -eq "$LP_N2" ] \
      || fail "node$i shrank to ${pc:-none} — the roster floor did NOT refuse a $LP_N2 -> $((LP_N2-1)) step"
  done
  echo "   ✅ every node still at $LP_N2 participants after a PASSED proposal"
  # And the refusal must be NAMED, not silent.
  local named=0
  for i in $(seq 0 $((LP_N2 - 1))); do
    local d; d=$(grp_dir b "$i")
    if grep -q 'REFUSED ConfigStep::RosterFloor' "$d/node.log"; then
      named=$((named + 1))
      printf '     node%s: ' "$i"; grep -o 'REFUSED ConfigStep::[A-Za-z]*[^"]*' "$d/node.log" | tail -1
    fi
  done
  [ "$named" -gt 0 ] \
    || fail "the roster stayed put but NO node named the refusal — a silent refusal is indistinguishable from a proposal that quietly did nothing"
  echo "   ✅ POLE 2 PASSED: refused BY NAME on $named/$LP_N2 nodes, roster unchanged"
}

cmd_report() {
  for g in a b; do
    local n; n=$(grp_n "$g")
    echo "== group $g =="
    for i in $(seq 0 $((n - 1))); do
      local hp; hp=$(grp_http "$g" "$i")
      printf '  node%s: ' "$i"
      curl -sf --max-time 5 "http://127.0.0.1:$hp/status" 2>/dev/null \
        | grep -o '"\(healthy\|peer_count\|latest_height\|dag_height\)":[^,}]*' | tr '\n' ' ' \
        || printf 'UNREACHABLE (a wedged node cannot answer /status — check for the round-advance wall)'
      printf '| membership: participants=%s threshold=%s' \
        "$(participant_count "$g" "$i")" "$(threshold_of "$g" "$i")"
      echo
    done
  done
}

cmd_down() {
  for g in a b; do
    local n; n=$(grp_n "$g")
    for i in $(seq 0 $((n - 1))); do
      local d; d=$(grp_dir "$g" "$i")
      [ -f "$d/node.pid" ] && { kill "$(cat "$d/node.pid")" 2>/dev/null || true; rm -f "$d/node.pid"; }
    done
  done
  echo "== down =="
}

cmd_clean() { cmd_down || true; rm -rf "$LP_ROOT"; }

case "${1:-}" in
  genesis) cmd_genesis ;;
  up) cmd_up ;;
  up-a) cmd_up_a ;;
  up-b) cmd_up_b ;;
  pole1) cmd_pole1 ;;
  pole2) cmd_pole2 ;;
  report) cmd_report ;;
  down) cmd_down ;;
  clean) cmd_clean ;;
  all) cmd_genesis; cmd_up; cmd_pole1; cmd_pole2; cmd_report ;;
  *) echo "usage: $0 {genesis|up|up-a|up-b|pole1|pole2|report|down|clean|all}" >&2; exit 2 ;;
esac
