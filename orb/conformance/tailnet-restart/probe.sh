#!/usr/bin/env bash
# conformance/tailnet-restart/probe.sh
#
# ★ DOES A LIVE TAILNET SURVIVE A COORDINATOR RESTART?
#
# `Control.Ipam.restart_sound` / `Control.Store.restart_sound` prove the STATE
# replays. They say nothing about whether CONNECTED STOCK CLIENTS recover their
# map long-poll, keep their addresses and keep passing traffic. This probe drives
# that, end to end, against real `tailscaled` 1.98.x:
#
#   1. bring up an isolated plane (coordinator + DERP + STUN + front door)
#   2. enrol two isolated stock clients, assert both Running with 100.64.x addrs
#      and a working `tailscale ping` between them
#   3. STOP the coordinator and START it again against the SAME DRORB_STORE,
#      leaving both clients running and untouched
#   4. assert: addresses UNCHANGED, backend still Running (no `tailscale up`, no
#      re-auth), ACL filter re-served, peers still ping — and report how long the
#      map long-poll took to come back
#   5. repeat for the DERP relay and the STUN server
#   6. the DURABILITY half, which needs no clients: a store TORN at the tail must
#      still replay every event committed before the tear
#      (`Control.Store.recoverStore_torn_write`)
#
# Steps 1-5 need a working `tailscaled`; step 6 does not, and runs regardless, so
# the durability regression cannot rot on a box without tailscale.
#
#   usage:  conformance/tailnet-restart/probe.sh [--store-only]
#   env:    PORT_BASE (default 36900) — the probe uses PORT_BASE..PORT_BASE+5
#           RUN_DIR   (default /tmp/drorb-restart-probe)
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="$ROOT/.lake/build/bin"
CTL="$BIN/drorb-ctl"
COORD="$BIN/control-live"
RUN_DIR="${RUN_DIR:-/tmp/drorb-restart-probe}"
PORT_BASE="${PORT_BASE:-36900}"
COORD_PORT=$((PORT_BASE)); DERP_PORT=$((PORT_BASE+1)); DERP_PLAIN_PORT=$((PORT_BASE+2))
FRONT_PORT=$((PORT_BASE+3)); STUN_PORT=$((PORT_BASE+4)); SERVE_PORT=$((PORT_BASE+5))
TS_PORT_A=$((PORT_BASE+6)); TS_PORT_B=$((PORT_BASE+7))
FAIL=0
ok()   { echo "  ok   $*"; }
bad()  { echo "  FAIL $*"; FAIL=1; }
note() { echo "  --   $*"; }

# ── 6. DURABILITY: a torn store still replays (no clients needed) ──────────────
store_probe() {
  echo "== durability: a TORN durable log still replays =="
  [ -x "$CTL" ] || { bad "missing $CTL (lake build drorb-ctl)"; return; }
  local d="$RUN_DIR/store"; rm -rf "$d"; mkdir -p "$d"
  local S="$d/coord.log"
  DRORB_STORE="$S" "$CTL" nodes register --key "$(printf 'aa%.0s' {1..32})" >/dev/null 2>&1
  DRORB_STORE="$S" "$CTL" nodes register --key "$(printf 'bb%.0s' {1..32})" >/dev/null 2>&1
  local base; base="$(DRORB_STORE="$S" "$CTL" nodes list 2>/dev/null | head -1)"
  [ "$base" = "NODES (2)" ] || { bad "two registered nodes did not persist ($base)"; return; }
  # the framed magic must be there: that is what makes the tail recoverable
  if head -c 8 "$S" | grep -q 'DRORB1'; then ok "store is the framed append-only format"
  else bad "store is not framed (no DRORB1 magic) — a torn tail would lose everything"; fi
  local sz; sz=$(stat -c %s "$S")
  # tear the tail at several depths; every event committed before the tear must survive
  local k
  for k in 1 3 9 25; do
    [ "$sz" -gt "$k" ] || continue
    cp "$S" "$d/torn.log"; truncate -s $((sz-k)) "$d/torn.log"
    local got; got="$(DRORB_STORE="$d/torn.log" "$CTL" nodes list 2>/dev/null | head -1)"
    if [ "$got" = "NODES (2)" ]; then ok "store truncated by $k byte(s): both nodes still replay"
    else bad "store truncated by $k byte(s): replayed as [$got] — torn tail lost committed state"; fi
  done
  # a write interrupted by SIGKILL must never leave a half-written LIVE store
  local i bads=0
  for i in $(seq 1 40); do
    DRORB_STORE="$S" "$CTL" preauthkeys create --reusable >/dev/null 2>&1 &
    local p=$!
    perl -e "select(undef,undef,undef,0.$((100+RANDOM%400)))" 2>/dev/null || sleep 0.2
    kill -9 $p 2>/dev/null; wait $p 2>/dev/null
    [ "$(DRORB_STORE="$S" "$CTL" nodes list 2>/dev/null | head -1)" = "NODES (2)" ] || { bads=1; break; }
  done
  [ $bads -eq 0 ] && ok "40x SIGKILL mid-write: the live store never lost a node" \
                  || bad "SIGKILL mid-write left the live store unreadable"
}

# ── 1-5. the LIVE half ─────────────────────────────────────────────────────────
live_probe() {
  command -v tailscaled >/dev/null || { note "no tailscaled on this box — skipping the live half"; return; }
  command -v jq >/dev/null || { note "no jq — skipping the live half"; return; }
  local LAN; LAN=$(hostname -I 2>/dev/null | tr ' ' '\n' | grep -E '^(192[.]168|10[.]|172[.](1[6-9]|2[0-9]|3[01]))[.]' | head -1)
  [ -n "$LAN" ] || { note "no LAN address — skipping the live half"; return; }
  local D="$RUN_DIR/live"; rm -rf "$D"; mkdir -p "$D"
  cat > "$D/policy.hujson" <<'POL'
{ "acls": [ { "action": "accept", "src": ["*"], "dst": ["*:*"] } ] }
POL
  echo "== live: bring the plane up on :$PORT_BASE.. =="
  HOST_BIND="$LAN" DRORB_DERP_ADDR="$LAN" \
  COORD_PORT=$COORD_PORT DERP_PORT=$DERP_PORT DERP_PLAIN_PORT=$DERP_PLAIN_PORT \
  FRONT_PORT=$FRONT_PORT STUN_PORT=$STUN_PORT SERVE_PORT=$SERVE_PORT \
  RUN_DIR="$D" DRORB_STORE="$D/coord.log" DRORB_POLICY="$D/policy.hujson" \
    "$ROOT/scripts/run-tailnet.sh" up > "$D/up.log" 2>&1 \
    || { bad "run-tailnet.sh up failed (see $D/up.log)"; return; }
  ok "plane up (coordinator $COORD_PORT, DERP $DERP_PORT, STUN $STUN_PORT, front $FRONT_PORT)"

  local SA="$D/ts-a.sock" SB="$D/ts-b.sock"
  local n
  for n in a b; do mkdir -p "$D/ts-$n-state"; done
  tailscaled --tun=userspace-networking --socket="$SA" --statedir="$D/ts-a-state" --port=$TS_PORT_A > "$D/tsd-a.log" 2>&1 &
  echo $! > "$D/tsd-a.pid"
  tailscaled --tun=userspace-networking --socket="$SB" --statedir="$D/ts-b-state" --port=$TS_PORT_B > "$D/tsd-b.log" 2>&1 &
  echo $! > "$D/tsd-b.pid"
  sleep 3
  tailscale --socket="$SA" up --login-server="http://$LAN:$FRONT_PORT/" --authkey=tskey-auth-drorb-h2noise-selftest >/dev/null 2>&1
  tailscale --socket="$SB" up --login-server="http://$LAN:$FRONT_PORT/" --authkey=tskey-auth-drorb-h2noise-selftest >/dev/null 2>&1
  sleep 8
  local A0 B0
  A0=$(tailscale --socket="$SA" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  B0=$(tailscale --socket="$SB" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  case "$A0" in 100.64.*) ok "node A enrolled as $A0" ;; *) bad "node A has no CGNAT address ($A0)"; teardown "$D"; return ;; esac
  case "$B0" in 100.64.*) ok "node B enrolled as $B0" ;; *) bad "node B has no CGNAT address ($B0)"; teardown "$D"; return ;; esac
  timeout 30 tailscale --socket="$SA" ping -c 2 "$B0" >/dev/null 2>&1 \
    && ok "A can ping B before the restart" || { bad "A cannot ping B before the restart"; teardown "$D"; return; }

  # ---- the restart, the way an operator upgrading drorb does it ----------------
  echo "== live: restart the COORDINATOR against the same DRORB_STORE =="
  local CERT; CERT=$("$BIN/derp-relay" certname "$ROOT/conformance/tls/cert.der")
  local OLD; OLD=$(cat "$D/coord.pid"); local T0; T0=$(date +%s)
  kill "$OLD" 2>/dev/null; while kill -0 "$OLD" 2>/dev/null; do sleep 0.05; done
  DRORB_DERP_ADDR="$LAN" DRORB_DERP_PORT=$DERP_PORT DRORB_STUN_PORT=$STUN_PORT \
  DRORB_DERP_CERTNAME="$CERT" DRORB_POLICY="$D/policy.hujson" \
    stdbuf -oL -eL nohup "$COORD" h2coord-multi $COORD_PORT "$D/coord.log" > "$D/coord2.out" 2>&1 &
  echo $! > "$D/coord.pid"
  while ! ss -ltn 2>/dev/null | grep -q ":$COORD_PORT"; do sleep 0.05; done
  ok "coordinator back in $(( $(date +%s) - T0 ))s (clients NOT touched)"
  for t in $(seq 1 40); do grep -q "recovered" "$D/coord2.out" && break; sleep 0.25; done
  grep -q "recovered" "$D/coord2.out" && ok "coordinator replayed the durable log ($(grep -c recovered "$D/coord2.out") node(s) recovered)" \
                                      || bad "coordinator did not recover any node from the log"

  # ---- recovery, observed on the clients --------------------------------------
  local t deadline=$(( $(date +%s) + 90 )) back=0
  while [ "$(date +%s)" -lt "$deadline" ]; do
    if grep -q "new network map" "$D/tsd-a.log" && grep -q "new network map" "$D/tsd-b.log"; then
      # both have logged at least one netmap; give the later one a moment
      back=1; break
    fi
    sleep 1
  done
  sleep 12   # let the long-poll actually re-establish
  local A1 B1 SA_STATE SB_STATE
  A1=$(tailscale --socket="$SA" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  B1=$(tailscale --socket="$SB" status --json 2>/dev/null | jq -r '.Self.TailscaleIPs[0]')
  SA_STATE=$(tailscale --socket="$SA" status --json 2>/dev/null | jq -r '.BackendState')
  SB_STATE=$(tailscale --socket="$SB" status --json 2>/dev/null | jq -r '.BackendState')
  [ "$A1" = "$A0" ] && ok "node A KEPT its address ($A1)" || bad "node A address changed: $A0 -> $A1"
  [ "$B1" = "$B0" ] && ok "node B KEPT its address ($B1)" || bad "node B address changed: $B0 -> $B1"
  [ "$SA_STATE" = "Running" ] && ok "node A still Running (no re-auth, no \`tailscale up\`)" || bad "node A backend is $SA_STATE"
  [ "$SB_STATE" = "Running" ] && ok "node B still Running (no re-auth, no \`tailscale up\`)" || bad "node B backend is $SB_STATE"
  local NF; NF=$(tailscale --socket="$SA" debug netmap 2>/dev/null | jq '.PacketFilter | length')
  [ "${NF:-0}" -ge 1 ] && ok "ACL PacketFilter re-served after the restart ($NF rule(s))" || bad "no ACL filter after the restart"
  timeout 30 tailscale --socket="$SA" ping -c 2 "$B0" >/dev/null 2>&1 \
    && ok "A can still ping B after the coordinator restart" || bad "A cannot ping B after the coordinator restart"

  # ---- DERP and STUN restarts (an upgrade restarts all of them) ---------------
  echo "== live: restart the DERP relay and the STUN server =="
  local DOLD; DOLD=$(cat "$D/derp.pid"); kill "$DOLD" 2>/dev/null; sleep 0.3
  DRORB_DERP_LISTEN=127.0.0.1 stdbuf -oL -eL nohup "$BIN/derp-relay" server $DERP_PLAIN_PORT > "$D/derp2.out" 2>&1 &
  echo $! > "$D/derp.pid"; sleep 12
  grep -q "REGISTERED and HELD OPEN" "$D/derp2.out" && ok "clients re-registered on the restarted DERP relay by themselves" \
                                                    || bad "no client reconnected to the restarted DERP relay"
  local SOLD; SOLD=$(cat "$D/stun.pid"); kill "$SOLD" 2>/dev/null; sleep 0.3
  stdbuf -oL -eL nohup "$BIN/stun-live" server $STUN_PORT "$LAN" > "$D/stun2.out" 2>&1 &
  echo $! > "$D/stun.pid"; sleep 1
  # An idle stock client only re-STUNs on its own netcheck cadence (a full report can be
  # 5 minutes apart), so do not wait on that: ASK a client for a netcheck and assert that
  # the RESTARTED server answers it. `UDP: true` means the reflexive address came back
  # from the drorb STUN server, and the server logs the binding it served.
  local NC; NC=$(timeout 60 tailscale --socket="$SA" netcheck 2>/dev/null)
  echo "$NC" | grep -qE '\* UDP: true' && ok "netcheck through the RESTARTED STUN server: UDP true (reflexive addr learned)" \
                                        || bad "netcheck reports no UDP after the STUN restart"
  grep -q "Binding response" "$D/stun2.out" && ok "the restarted STUN server served the live client a Binding response" \
                                            || bad "the restarted STUN server logged no Binding response"
  timeout 30 tailscale --socket="$SA" ping -c 2 "$B0" >/dev/null 2>&1 \
    && ok "A can still ping B after DERP+STUN restarts" || bad "A cannot ping B after DERP+STUN restarts"
  teardown "$D"
}

teardown() {
  local D="$1"
  for f in tsd-a.pid tsd-b.pid coord.pid derp.pid stun.pid dataplane.pid; do
    [ -f "$D/$f" ] && kill "$(cat "$D/$f")" 2>/dev/null
  done
  sleep 0.5
}

mkdir -p "$RUN_DIR"
echo "== drorb tailnet RESTART probe =="
store_probe
[ "${1:-}" = "--store-only" ] || live_probe
echo
[ $FAIL -eq 0 ] && { echo "PROBE PASS"; exit 0; } || { echo "PROBE FAIL"; exit 1; }
