#!/usr/bin/env bash
# conformance/tailnet-restart/quiet-probe.sh
#
# ★ DOES A QUIET COORDINATOR KEEP SERVING?
#
# The sibling probe (probe.sh) asks whether a live tailnet survives a coordinator
# RESTART. This one asks the opposite question, the one a homelab actually lives
# in: what happens when NOTHING happens. Two bugs lived in that gap, and they hid
# each other:
#
#   A. ControlLive.acceptLoop treated an expired `tcpAccept` as a reason to stop:
#      after 300 s with no NEW inbound connection it printed "accept idle 300s;
#      exiting" and returned. The process did not even die — the policy-reload and
#      approval watcher tasks keep the Lean runtime alive — so it lingered holding
#      the listening socket with nobody accepting. Observed: Recv-Q 5 on the LISTEN
#      socket, five unread noise initiations, and `tailscale up` on a new node
#      timing out with `context canceled`.
#
#   B. ControlLive.pushLoop capped ONE open map long-poll at 240 ticks of 500 ms —
#      so a HEALTHY, quiet client had its netmap stream closed every ~2 minutes and
#      redialled. That redial is what kept resetting bug A's accept clock, which is
#      why the restart probe never tripped it.
#
# Both are now "log and keep serving", with an opt-in bound (DRORB_ACCEPT_IDLE_EXIT,
# DRORB_PUSH_MAX_TICKS; both default to never). This probe fails if either comes back.
#
# It also covers the DURABILITY half of the same commit path: Control.Durable must
# actually issue fsync(file) and fsync(containing directory) around the rename, which
# is what makes an ACKNOWLEDGED registration survive a power cut and not just a
# killed process. That half needs no clients and runs anywhere.
#
#   usage:  conformance/tailnet-restart/quiet-probe.sh [--store-only] [--full]
#           --store-only  just the fsync half (no tailscaled needed)
#           --full        quiet window at the SHIPPED 300 s accept tick (~12 min)
#                         instead of the scaled-down 15 s tick (~3 min)
#   env:    PORT_BASE (default 37500), RUN_DIR (default /tmp/drorb-quiet-probe)
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="$ROOT/.lake/build/bin"
CTL="$BIN/drorb-ctl"
RUN_DIR="${RUN_DIR:-/tmp/drorb-quiet-probe}"
PORT_BASE="${PORT_BASE:-37500}"
FULL=0; STORE_ONLY=0
for a in "$@"; do
  case "$a" in --full) FULL=1 ;; --store-only) STORE_ONLY=1 ;; esac
done
COORD_PORT=$((PORT_BASE)); DERP_PORT=$((PORT_BASE+1)); DERP_PLAIN_PORT=$((PORT_BASE+2))
FRONT_PORT=$((PORT_BASE+3)); STUN_PORT=$((PORT_BASE+4)); SERVE_PORT=$((PORT_BASE+5))
TS_PORT_A=$((PORT_BASE+6)); TS_PORT_B=$((PORT_BASE+7))
FAIL=0
ok()   { echo "  ok   $*"; }
bad()  { echo "  FAIL $*"; FAIL=1; }
note() { echo "  --   $*"; }

# ── the DURABILITY half: the commit path must force BOTH the file and the dir ──
fsync_probe() {
  echo "== durability: the commit path forces the file AND the containing directory =="
  [ -x "$CTL" ] || { bad "missing $CTL (lake build drorb-ctl)"; return; }
  command -v strace >/dev/null || { note "no strace — cannot witness the syscalls; skipping"; return; }
  local d="$RUN_DIR/fsync"; rm -rf "$d"; mkdir -p "$d"
  local S="$d/coord.log"
  DRORB_STORE="$S" "$CTL" nodes register --key "$(printf 'aa%.0s' {1..32})" >/dev/null 2>&1
  strace -f -e trace=openat,rename,fsync -o "$d/tr.txt" \
    env DRORB_STORE="$S" "$CTL" nodes register --key "$(printf 'bb%.0s' {1..32})" >/dev/null 2>&1
  # the ORDER is the whole point: force the temp file's data, THEN rename, THEN
  # force the directory that now names it. A rename whose directory block is only
  # in the page cache is not durable, and that is the half normally missed.
  local l_tmp l_ren l_dir f1 f2
  l_tmp=$(grep -n 'coord\.log\.tmp", O_WRONLY)' "$d/tr.txt" | head -1 | cut -d: -f1)
  l_ren=$(grep -n 'rename(' "$d/tr.txt" | head -1 | cut -d: -f1)
  l_dir=$(grep -n 'O_RDONLY|O_DIRECTORY' "$d/tr.txt" | head -1 | cut -d: -f1)
  f1=$(awk -v a="${l_tmp:-0}" -v b="${l_ren:-0}" 'NR>a && NR<b && /fsync\(/ {print NR; exit}' "$d/tr.txt")
  f2=$(awk -v a="${l_dir:-0}" 'NR>a && /fsync\(/ {print NR; exit}' "$d/tr.txt")
  if [ -n "$l_tmp" ] && [ -n "$l_ren" ] && [ -n "$f1" ] && [ "$f1" -lt "$l_ren" ]; then
    ok "the TEMP FILE is fsync'd BEFORE the rename (its data reaches stable storage first)"
  else
    bad "no fsync between writing the temp file and renaming it over the store"
  fi
  if [ -n "$l_dir" ] && [ -n "$f2" ] && [ -n "$l_ren" ] && [ "$l_dir" -gt "$l_ren" ]; then
    ok "the CONTAINING DIRECTORY is opened O_DIRECTORY and fsync'd AFTER the rename (the rename itself is made durable)"
  else
    bad "no directory fsync after the rename — it survives a process kill but NOT a power cut"
  fi
  # and the store still means what Control.Store says it means
  local got; got="$(DRORB_STORE="$S" "$CTL" nodes list 2>/dev/null | head -1)"
  [ "$got" = "NODES (2)" ] && ok "the durably-committed store still replays (2 nodes)" \
                           || bad "store replayed as [$got] after a durable commit"
}

teardown() {
  local D="$1"
  for f in tsd-a.pid tsd-b.pid coord.pid derp.pid stun.pid dataplane.pid; do
    [ -f "$D/$f" ] && kill "$(cat "$D/$f")" 2>/dev/null
  done
  sleep 0.5
}

# ── the QUIET half: a coordinator with nothing to do keeps doing its job ──────
quiet_probe() {
  command -v tailscaled >/dev/null || { note "no tailscaled on this box — skipping the live half"; return; }
  command -v jq >/dev/null || { note "no jq — skipping the live half"; return; }
  local LAN; LAN=$(hostname -I 2>/dev/null | tr ' ' '\n' | grep -E '^(192[.]168|10[.]|172[.](1[6-9]|2[0-9]|3[01]))[.]' | head -1)
  [ -n "$LAN" ] || { note "no LAN address — skipping the live half"; return; }

  # The scaled-down run keeps the SHAPE (many expired accept ticks, a long-poll
  # held far past the old 240-tick push cap) at a fraction of the wall time. The
  # old push cap was ~120 s, so any window past that exercises it either way.
  local TICK QUIET
  if [ "$FULL" = "1" ]; then TICK=300000; QUIET=660
  else                       TICK=15000;  QUIET=150; fi

  local D="$RUN_DIR/live"; rm -rf "$D"; mkdir -p "$D"
  cat > "$D/policy.hujson" <<'POL'
{ "acls": [ { "action": "accept", "src": ["*"], "dst": ["*:*"] } ] }
POL
  echo "== quiet: bring the plane up on :$PORT_BASE.. (accept tick ${TICK}ms, quiet window ${QUIET}s) =="
  DRORB_ACCEPT_TICK_MS="$TICK" \
  HOST_BIND="$LAN" DRORB_DERP_ADDR="$LAN" \
  COORD_PORT=$COORD_PORT DERP_PORT=$DERP_PORT DERP_PLAIN_PORT=$DERP_PLAIN_PORT \
  FRONT_PORT=$FRONT_PORT STUN_PORT=$STUN_PORT SERVE_PORT=$SERVE_PORT \
  RUN_DIR="$D" DRORB_STORE="$D/coord.log" DRORB_POLICY="$D/policy.hujson" \
    "$ROOT/scripts/run-tailnet.sh" up > "$D/up.log" 2>&1 \
    || { bad "run-tailnet.sh up failed (see $D/up.log)"; return; }
  ok "plane up (coordinator $COORD_PORT, DERP $DERP_PORT, STUN $STUN_PORT, front $FRONT_PORT)"

  local SA="$D/ts-a.sock"
  mkdir -p "$D/ts-a-state"
  tailscaled --tun=userspace-networking --socket="$SA" --statedir="$D/ts-a-state" --port=$TS_PORT_A > "$D/tsd-a.log" 2>&1 &
  echo $! > "$D/tsd-a.pid"
  sleep 3
  tailscale --socket="$SA" up --login-server="http://$LAN:$FRONT_PORT/" --authkey=tskey-auth-drorb-h2noise-selftest >/dev/null 2>&1
  sleep 8
  local A0; A0=$(tailscale --socket="$SA" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  case "$A0" in 100.64.*) ok "node A enrolled as $A0, holding a map long-poll" ;;
                *) bad "node A has no CGNAT address ($A0)"; teardown "$D"; return ;; esac

  # ---- now do NOTHING for the quiet window --------------------------------------
  echo "== quiet: $QUIET s with no new inbound connection and no client change =="
  local CP; CP=$(cat "$D/coord.pid")
  sleep "$QUIET"

  kill -0 "$CP" 2>/dev/null && ok "coordinator process still alive after ${QUIET}s of quiet" \
                            || bad "coordinator process died during the quiet window"
  grep -q "accept idle .*exiting" "$D/coord.out" \
    && bad "coordinator treated an idle accept as fatal (the bug is back)" \
    || ok "no idle-exit: an expired accept tick is not a reason to stop"
  local TICKS; TICKS=$(grep -c "accept idle tick" "$D/coord.out" 2>/dev/null || echo 0)
  [ "${TICKS:-0}" -ge 1 ] && ok "$TICKS accept tick(s) expired and the loop CONTINUED (the regression is exercised)" \
                          || bad "no accept tick expired — the quiet window did not exercise the bug"
  grep -q "hit time bound" "$D/coord.out" \
    && bad "pushLoop closed a healthy long-poll on a time bound (the sibling bug is back)" \
    || ok "no push-loop time bound: the quiet client's map stream was never closed for being quiet"

  # the listener must still be ACCEPTING, not just LISTENING: a backlog that is
  # filling up is exactly what the wedged coordinator looked like.
  local RQ; RQ=$(ss -ltn "( sport = :$COORD_PORT )" 2>/dev/null | tail -n +2 | awk '{print $2}')
  [ "${RQ:-0}" = "0" ] && ok "listen backlog empty (connections are being accepted, not queued)" \
                       || bad "listen backlog Recv-Q=$RQ — dials are piling up unaccepted"

  local SA_STATE A1
  SA_STATE=$(tailscale --socket="$SA" status --json 2>/dev/null | jq -r '.BackendState')
  A1=$(tailscale --socket="$SA" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  [ "$SA_STATE" = "Running" ] && ok "node A still Running after the quiet window" || bad "node A backend is $SA_STATE"
  [ "$A1" = "$A0" ] && ok "node A kept its address ($A1)" || bad "node A address changed: $A0 -> $A1"

  # ---- and the coordinator can still ADMIT A NEW NODE --------------------------
  echo "== quiet: a NEW node enrols against the quiet coordinator =="
  local SB="$D/ts-b.sock"; mkdir -p "$D/ts-b-state"
  tailscaled --tun=userspace-networking --socket="$SB" --statedir="$D/ts-b-state" --port=$TS_PORT_B > "$D/tsd-b.log" 2>&1 &
  echo $! > "$D/tsd-b.pid"
  sleep 3
  timeout 60 tailscale --socket="$SB" up --login-server="http://$LAN:$FRONT_PORT/" --authkey=tskey-auth-drorb-h2noise-selftest >/dev/null 2>&1
  sleep 8
  local B0; B0=$(tailscale --socket="$SB" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  case "$B0" in 100.64.*) ok "node B enrolled as $B0 AFTER the quiet window (the coordinator was still accepting)" ;;
                *) bad "node B could not enrol after the quiet window ($B0) — the coordinator went deaf" ;; esac
  timeout 30 tailscale --socket="$SA" ping -c 2 "$B0" >/dev/null 2>&1 \
    && ok "A can ping the newly-joined B" || bad "A cannot ping the newly-joined B"
  teardown "$D"
}

mkdir -p "$RUN_DIR"
echo "== drorb QUIET-COORDINATOR probe =="
fsync_probe
[ "$STORE_ONLY" = "1" ] || quiet_probe
echo
[ $FAIL -eq 0 ] && { echo "PROBE PASS"; exit 0; } || { echo "PROBE FAIL"; exit 1; }
