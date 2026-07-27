#!/usr/bin/env bash
# run-tailnet.sh — bring up drorb as a verified Tailscale control plane on a homelab.
#
# Starts four processes on isolated loopback ports:
#   1. control-live h2coord-multi  — the verified coordinator (ts2021 Noise + h2 +
#      IPAM + durable Store); serves the netmap whose PacketFilter IS the ACL
#      compiler output (servedMapFor_filter_is_acl_compile).
#   2. derp-relay server           — the verified DERP relay (Derp.Server.dispatch),
#      the region-1 home a client falls back to when it has no direct path.
#   3. stun-live server            — the verified STUN Binding server
#      (Stun.respond / respond_success_correct), the service a stock client's
#      netcheck probes to learn its OWN reflexive endpoint. Without it netcheck
#      reports udp=false and the client's candidate set holds only local-interface
#      addresses, so peers that do not already share a link never leave the relay.
#      The served netmap ADVERTISES its port (Join.derpMapToWireAtPortStun_stunPort).
#   4. dataplane (control front + DERP TLS front) — the HTTP/1.1 /key + /ts2021 front
#      door that a STOCK tailscale client hits (on 101 Switching Protocols it splices
#      the raw controlbase stream to the verified coordinator), AND — when DERP_TLS=1,
#      the default — the DERP relay's TLS front: a stock client dials its home region
#      over HTTPS, so each connection is terminated by the VERIFIED TLS 1.3 terminator
#      (drorb_tls_terminate: the same handshake, record layer and cert selection as the
#      HTTPS front door) and the decrypted stream is spliced to the verified Lean relay
#      on loopback. (Additive host glue; the Noise crypto, the TLS, the DERP framing and
#      the forwarding all stay the verified Lean.)
#
# Usage:
#   scripts/run-tailnet.sh [up]     # start the plane (idempotent)
#   scripts/run-tailnet.sh stop     # stop the plane (kills only its own pids)
#   scripts/run-tailnet.sh status   # show listeners + pids
#
# Config (env overrides, all default to loopback + isolated ports):
#   DRORB_ROOT     drorb checkout            (default: script's ../ )
#   COORD_PORT     coordinator port          (default: 3352)
#   DERP_PORT      DERP relay port           (default: 3340) -- BOTH the relay's bind
#                  port AND the port the served netmap ADVERTISES (passed to the
#                  coordinator as DRORB_DERP_PORT), so they cannot disagree.
#   FRONT_PORT     stock-client front door   (default: 3351)
#   DERP_BIND      interface the DERP relay BINDS  (default: $HOST_BIND)
#   DERP_TLS       1 (default) = a STOCK client can reach the relay: the dataplane
#                  terminates TLS on $DERP_BIND:$DERP_PORT over the verified terminator
#                  and splices plaintext to the Lean relay on 127.0.0.1:$DERP_PLAIN_PORT.
#                  0 = the pre-existing plaintext relay bound directly on $DERP_PORT
#                  (drorb's own derp clients only; a stock client dials https:// and gets
#                  `no HTTP upgrade`).
#   DERP_PLAIN_PORT loopback port of the Lean relay behind the TLS front (default: 3341)
#   DERP_CERT      leaf DER the DERP TLS front presents  (default: conformance/tls/cert.der)
#   DERP_SEED      its 32-byte Ed25519 seed             (default: conformance/tls/seed.bin)
#   STUN_PORT      STUN Binding server port  (default: 3478) -- BOTH the bind port AND
#                  the port the served netmap ADVERTISES (passed to the coordinator as
#                  DRORB_STUN_PORT), so they cannot disagree. Set STUN_PORT=0 to run NO
#                  STUN service and advertise none (the pre-STUN behaviour).
#   STUN_BIND      interface the STUN server BINDS  (default: $DERP_BIND)
#   DRORB_DERP_ADDR addr the served netmap ADVERTISES for the relay
#                   (default: the reachable addr for $HOST_BIND) -- this is the IP a
#                   client on ANOTHER host dials, so it must NOT be 127.0.0.1 cross-host
#   SERVE_PORT     dataplane HTTP serve port (default: 8085; must be free)
#   RUN_DIR        pidfiles + logs + store   (default: /tmp/drorb-tailnet)
#   DRORB_STORE    durable event log         (default: $RUN_DIR/coord.log)
#
# The coordinator reads DRORB_STORE ONCE at startup, so mint any operator
# pre-auth keys (drorb-ctl preauthkeys create) BEFORE `up`, or re-run `up` after
# minting. Two built-in demo keys are always present without any minting:
#   tskey-auth-drorb-h2noise-selftest   (a stock client can use this verbatim)
set -euo pipefail

SELF="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DRORB_ROOT="${DRORB_ROOT:-$(cd "$SELF/.." && pwd)}"
COORD_PORT="${COORD_PORT:-3352}"
DERP_PORT="${DERP_PORT:-3340}"
FRONT_PORT="${FRONT_PORT:-3351}"
# HOST_BIND: the interface the control front binds. 127.0.0.1 (default) keeps
# it loopback-only; 0.0.0.0 or a LAN IP makes it routable so a stock tailscale
# client on ANOTHER host can reach --login-server=http://<this-host>:$FRONT_PORT/.
# The coordinator + DERP stay loopback: the control front is the only front a
# stock client talks to; it splices the raw controlbase stream inward to them.
HOST_BIND="${HOST_BIND:-127.0.0.1}"
# ── DERP env block ──────────────────────────────────────────────────────────────
# DERP_BIND is the interface the verified relay LISTENS on (DRORB_DERP_LISTEN);
# DRORB_DERP_ADDR is the addr the served MapResponse ADVERTISES for it. They are
# separate on purpose: bind wide (0.0.0.0), advertise a single reachable IP. Both
# follow HOST_BIND by default, so the same-host default stays pure loopback. The
# advertised PORT is not a third knob: DERP_PORT is threaded to the coordinator as
# DRORB_DERP_PORT (Control.Join.drorbDerpMapAtPort), so bind and advertisement move
# together -- a non-3340 plane advertises its OWN port, not a dead 3340.
DERP_BIND="${DERP_BIND:-$HOST_BIND}"
# ── DERP TLS block ──────────────────────────────────────────────────────────────
# A STOCK tailscale client dials its home DERP region over HTTPS
# (https://<host>:<DERPPort>/derp). The verified Lean relay speaks plaintext, so with
# DERP_TLS=1 the dataplane binds $DERP_PORT, terminates each connection over the
# VERIFIED terminator (drorb_tls_terminate) and splices the decrypted stream to the
# relay on 127.0.0.1:$DERP_PLAIN_PORT. The served netmap must ALSO carry the
# certificate pin -- a self-hosted leaf is signed by no public CA, and derphttp accepts
# it only when the node names CertName=sha256-raw:<sha256 of the leaf DER>. That value
# is DERIVED below from $DERP_CERT (via `derp-relay certname`), so the advertised pin
# cannot drift from the certificate the front presents.
DERP_TLS="${DERP_TLS:-1}"
DERP_PLAIN_PORT="${DERP_PLAIN_PORT:-3341}"
DERP_CERT="${DERP_CERT:-$DRORB_ROOT/conformance/tls/cert.der}"
DERP_SEED="${DERP_SEED:-$DRORB_ROOT/conformance/tls/seed.bin}"
# ── STUN env block ──────────────────────────────────────────────────────────────
# The STUN Binding server is what lets a stock client discover a DIRECT path: netcheck
# learns its own reflexive transport address only by STUNning a DERP region in the served
# netmap. STUN_PORT is threaded to the coordinator as DRORB_STUN_PORT
# (Control.Join.drorbDerpMapAtPortStun), so the ADVERTISED port is by construction the
# port this script BINDS. STUN_PORT=0 disables both halves together.
STUN_PORT="${STUN_PORT:-3478}"
STUN_BIND="${STUN_BIND:-$DERP_BIND}"
SERVE_PORT="${SERVE_PORT:-8085}"
RUN_DIR="${RUN_DIR:-/tmp/drorb-tailnet}"
DRORB_STORE="${DRORB_STORE:-$RUN_DIR/coord.log}"

BIN="$DRORB_ROOT/.lake/build/bin"
CONTROL_LIVE="$BIN/control-live"
DERP_RELAY="$BIN/derp-relay"
STUN_LIVE="$BIN/stun-live"
DRORB_CTL="$BIN/drorb-ctl"
DATAPLANE="$DRORB_ROOT/target/release/dataplane"

reachable_addr() {
  # The address a client on another host should point --login-server at.
  case "$HOST_BIND" in
    0.0.0.0|"") hostname -I 2>/dev/null | tr " " "\n" \
                  | grep -E "^(192[.]168|10[.]|172[.](1[6-9]|2[0-9]|3[01]))[.]" \
                  | head -1 || echo 127.0.0.1 ;;
    *) printf "%s" "$HOST_BIND" ;;
  esac
}

# The relay addr the netmap advertises: explicit DRORB_DERP_ADDR wins, else the
# reachable addr for HOST_BIND (127.0.0.1 when the plane is loopback-only).
derp_adv_addr() { printf "%s" "${DRORB_DERP_ADDR:-$(reachable_addr)}"; }

port_busy() { ss -ltn 2>/dev/null | awk '{print $4}' | grep -qE "[:.]${1}\$"; }
# The UDP sibling: the STUN server binds a DATAGRAM port, invisible to `ss -ltn`.
udp_port_busy() { ss -lun 2>/dev/null | awk '{print $4}' | grep -qE "[:.]${1}\$"; }
udp_port_owner_pids() {
  ss -lunp 2>/dev/null | awk -v pat="[:.]${1}\$" '$4 ~ pat' \
    | grep -oE 'pid=[0-9]+' | cut -d= -f2 | sort -u || true
}

# ── port OWNERSHIP ──────────────────────────────────────────────────────────────
# "is the port busy" is NOT "is it MINE". If a component loses a bind race to an
# already-running process (a stale relay, another operator's plane, a foreign
# service), a busy-port check reports SUCCESS while the plane silently ADOPTS
# someone else's listener — you believe you are running a verified relay and you
# are pointing clients at an unknown one. Every component is therefore checked
# for PROCESS-ALIVE *and* PID-OWNS-THE-PORT, and a foreign owner is fatal.

# The pids listening on :PORT, per `ss -ltnp`. A listener owned by another USER
# (or root) shows NO pid= field — that prints nothing, which the caller treats as
# "not mine", i.e. still fatal. Never silently adopt.
port_owner_pids() {
  ss -ltnp 2>/dev/null | awk -v pat="[:.]${1}\$" '$4 ~ pat' \
    | grep -oE 'pid=[0-9]+' | cut -d= -f2 | sort -u || true
}

# The UDP pre-flight: same refusal-to-adopt discipline as the TCP one.
preflight_udp_port() {
  local port="$1" name="$2"
  if udp_port_busy "$port"; then
    local owners; owners="$(udp_port_owner_pids "$port" | tr '\n' ' ')"
    echo "! $name UDP port :$port is ALREADY BOUND${owners:+ by pid(s) ${owners% }}." >&2
    echo "  Refusing to start: this plane would either lose the bind race and ADOPT" >&2
    echo "  that listener, or run alongside it. Stop it, or pick a free port." >&2
    return 1
  fi
}

# After launching a UDP component: alive AND owns the datagram port.
wait_own_udp() {
  local port="$1" name="$2" pidfile="$3" tries=0 pid owners
  pid="$(cat "$pidfile" 2>/dev/null || true)"
  [ -n "$pid" ] || { echo "! $name: no pid recorded in $pidfile" >&2; return 1; }
  while :; do
    if ! kill -0 "$pid" 2>/dev/null; then
      echo "! $name (pid $pid) DIED before it owned UDP :$port — last log lines:" >&2
      tail -n 15 "$RUN_DIR/$(basename "${pidfile%.pid}").out" >&2 2>/dev/null || true
      return 1
    fi
    if udp_port_busy "$port"; then
      owners="$(udp_port_owner_pids "$port")"
      if printf '%s\n' $owners | grep -qx "$pid"; then
        echo "        ownership OK: pid $pid owns UDP :$port"
        return 0
      fi
      echo "! $name: UDP :$port is held by FOREIGN pid(s) [${owners:-unknown/other-user}], not by our pid $pid." >&2
      echo "  This plane would have ADOPTED a STUN server it does not own. Refusing." >&2
      return 1
    fi
    tries=$((tries+1))
    if [ "$tries" -gt 50 ]; then
      echo "! $name (pid $pid) did not bind UDP :$port in 5s" >&2
      return 1
    fi
    sleep 0.1
  done
}

# Fail before we launch anything if a port we are about to bind is already taken.
preflight_port() {
  local port="$1" name="$2"
  if port_busy "$port"; then
    local owners; owners="$(port_owner_pids "$port" | tr '\n' ' ')"
    echo "! $name port :$port is ALREADY BOUND${owners:+ by pid(s) ${owners% }}." >&2
    echo "  Refusing to start: this plane would either lose the bind race and ADOPT" >&2
    echo "  that listener, or run alongside it. Stop it, or pick a free port." >&2
    return 1
  fi
}

# After launching: the pidfile process must be alive AND own the port. This is the
# check that catches a LOST BIND RACE (we exited/lost, someone else holds :port).
wait_own() {
  local port="$1" name="$2" pidfile="$3" tries=0 pid owners
  pid="$(cat "$pidfile" 2>/dev/null || true)"
  [ -n "$pid" ] || { echo "! $name: no pid recorded in $pidfile" >&2; return 1; }
  while :; do
    if ! kill -0 "$pid" 2>/dev/null; then
      echo "! $name (pid $pid) DIED before it owned :$port — last log lines:" >&2
      tail -n 15 "$RUN_DIR/$(basename "${pidfile%.pid}").out" >&2 2>/dev/null || true
      return 1
    fi
    if port_busy "$port"; then
      owners="$(port_owner_pids "$port")"
      if printf '%s\n' $owners | grep -qx "$pid"; then
        echo "        ownership OK: pid $pid owns :$port"
        return 0
      fi
      # busy, but NOT by us: a foreign listener holds the port. Do NOT adopt it.
      echo "! $name: :$port is held by FOREIGN pid(s) [${owners:-unknown/other-user}], not by our pid $pid." >&2
      echo "  This plane would have ADOPTED a relay it does not own. Refusing." >&2
      echo "  (our $name process pid $pid is alive but failed to bind; see $RUN_DIR/)" >&2
      return 1
    fi
    tries=$((tries+1))
    if [ "$tries" -gt 50 ]; then
      echo "! $name (pid $pid) did not bind :$port in 5s" >&2
      return 1
    fi
    sleep 0.1
  done
}

kill_pidfile() {
  local f="$1"
  [ -f "$f" ] || return 0
  local p; p="$(cat "$f" 2>/dev/null || true)"
  if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then kill "$p" 2>/dev/null || true; fi
  rm -f "$f"
}

cmd_stop() {
  echo "== stopping the drorb tailnet plane =="
  kill_pidfile "$RUN_DIR/dataplane.pid"
  kill_pidfile "$RUN_DIR/stun.pid"
  kill_pidfile "$RUN_DIR/derp.pid"
  kill_pidfile "$RUN_DIR/coord.pid"
  sleep 0.5
  echo "  stopped (only this plane's pids were touched)."
}

cmd_status() {
  echo "== drorb tailnet plane — listeners =="
  ss -ltnp 2>/dev/null | grep -E "[:.]($COORD_PORT|$DERP_PORT|$DERP_PLAIN_PORT|$FRONT_PORT|$SERVE_PORT)\b" || echo "  (nothing listening on the configured TCP ports)"
  if [ "$STUN_PORT" != "0" ]; then
    ss -lunp 2>/dev/null | grep -E "[:.]($STUN_PORT)\b" || echo "  (nothing listening on UDP :$STUN_PORT — no STUN)"
  fi
}

cmd_up() {
  for f in "$CONTROL_LIVE" "$DERP_RELAY" "$DRORB_CTL" "$DATAPLANE"; do
    [ -x "$f" ] || { echo "missing binary: $f" >&2
      echo "build first:  lake build control-live derp-relay drorb-ctl stun-live" >&2
      echo "         and: cargo build --release -p dataplane" >&2
      exit 1; }
  done
  if [ "$STUN_PORT" != "0" ] && [ ! -x "$STUN_LIVE" ]; then
    echo "missing binary: $STUN_LIVE" >&2
    echo "build first:  lake build stun-live      (or set STUN_PORT=0 to run without STUN)" >&2
    exit 1
  fi
  mkdir -p "$RUN_DIR"

  # idempotent: tear down any previous instance of THIS plane before starting.
  cmd_stop >/dev/null 2>&1 || true

  # ── PRE-FLIGHT: every port this plane binds must be FREE. ────────────────────
  # SERVE_PORT was already checked this way; COORD/DERP/FRONT were not, and a busy
  # DERP_PORT was the actual hole — the relay lost the bind race and the plane
  # ADOPTED a foreign relay while reporting success. All four are checked now, and
  # each component is re-checked for ownership after it launches (`wait_own`).
  preflight_port "$SERVE_PORT" "SERVE_PORT (dataplane HTTP serve)" || exit 1
  preflight_port "$COORD_PORT" "COORD_PORT (coordinator)"          || exit 1
  preflight_port "$DERP_PORT"  "DERP_PORT (DERP relay)"            || exit 1
  if [ "$DERP_TLS" = "1" ]; then
    preflight_port "$DERP_PLAIN_PORT" "DERP_PLAIN_PORT (Lean relay behind the TLS front)" || exit 1
  fi
  preflight_port "$FRONT_PORT" "FRONT_PORT (control front door)"   || exit 1
  if [ "$STUN_PORT" != "0" ]; then
    preflight_udp_port "$STUN_PORT" "STUN_PORT (STUN Binding server)" || exit 1
  fi

  echo "== drorb verified tailnet control plane =="
  echo "   root   : $DRORB_ROOT"
  echo "   store  : $DRORB_STORE"
  echo

  # 1. the verified coordinator (reads the durable store once, here).
  DERP_ADV="$(derp_adv_addr)"
  # The certificate pin the served netmap advertises, DERIVED from the leaf the TLS
  # front will present -- never typed twice. Empty when the relay is plaintext, which
  # reproduces the pre-existing served shape byte for byte
  # (Join.derpMapToWireAtPortStun_no_certName).
  DERP_CERTNAME=""
  if [ "$DERP_TLS" = "1" ]; then
    if [ ! -r "$DERP_CERT" ]; then
      echo "! DERP_TLS=1 but the leaf $DERP_CERT is unreadable — a stock client cannot reach the relay." >&2
      exit 1
    fi
    DERP_CERTNAME="$("$DERP_RELAY" certname "$DERP_CERT")" || {
      echo "! could not derive the DERP CertName from $DERP_CERT" >&2; exit 1; }
  fi
  echo "-- [1/4] control-live h2coord-multi  (coordinator)  :$COORD_PORT"
  if [ "$DERP_TLS" = "1" ]; then
    echo "        DERP: TLS front binds $DERP_BIND:$DERP_PORT (VERIFIED terminator) -> Lean relay 127.0.0.1:$DERP_PLAIN_PORT"
    echo "              served netmap ADVERTISES $DERP_ADV:$DERP_PORT"
  else
    echo "        DERP: relay binds $DERP_BIND:$DERP_PORT PLAINTEXT; served netmap ADVERTISES $DERP_ADV:$DERP_PORT"
  fi
  if [ "$STUN_PORT" != "0" ]; then
    echo "        STUN: server binds $STUN_BIND:$STUN_PORT/udp; served netmap ADVERTISES $DERP_ADV:$STUN_PORT"
  else
    echo "        STUN: DISABLED (STUN_PORT=0) — clients will report udp=false and learn no reflexive endpoint"
  fi
  if [ "$DERP_ADV" = "127.0.0.1" ] && [ "$HOST_BIND" != "127.0.0.1" ]; then
    echo "        ! the front is routable but DERP advertises LOOPBACK — a cross-host client" >&2
    echo "          cannot reach the relay. Set DRORB_DERP_ADDR=<this host's LAN IP>." >&2
  fi
  # DRORB_DERP_PORT is the ADVERTISED relay port. It is passed the SAME value the
  # relay BINDS below, so the served MapResponse can never name a port nothing is
  # listening on (it used to be the hardcoded `Join.drorbDerpPort = 3340`).
  DRORB_DERP_ADDR="$DERP_ADV" \
  DRORB_DERP_PORT="$DERP_PORT" \
  DRORB_STUN_PORT="$STUN_PORT" \
  DRORB_DERP_CERTNAME="$DERP_CERTNAME" \
  stdbuf -oL -eL nohup "$CONTROL_LIVE" h2coord-multi "$COORD_PORT" "$DRORB_STORE" \
    > "$RUN_DIR/coord.out" 2>&1 &
  echo $! > "$RUN_DIR/coord.pid"
  wait_own "$COORD_PORT" "coordinator" "$RUN_DIR/coord.pid" || exit 1
  # the coordinator prints its Noise responder static pubkey; the front door pins it.
  NOISE_PUB=""
  for _ in $(seq 1 30); do
    NOISE_PUB="$(grep -oE 'static pub .*: [0-9a-f]{64}' "$RUN_DIR/coord.out" 2>/dev/null | grep -oE '[0-9a-f]{64}' | head -1 || true)"
    [ -n "$NOISE_PUB" ] && break
    sleep 0.1
  done
  [ -n "$NOISE_PUB" ] || { echo "  ! could not read coordinator Noise pubkey" >&2; cat "$RUN_DIR/coord.out" >&2; exit 1; }
  echo "        Noise static pub: $NOISE_PUB"

  # 2. the verified DERP relay (persistent N-connection region). With DERP_TLS=1 it
  #    binds LOOPBACK and the dataplane's verified TLS front owns the public port.
  if [ "$DERP_TLS" = "1" ]; then
    RELAY_BIND=127.0.0.1; RELAY_PORT="$DERP_PLAIN_PORT"
    echo "-- [2/4] derp-relay server           (DERP region 1, behind the TLS front) :$RELAY_PORT"
    echo "        CertName advertised: $DERP_CERTNAME"
  else
    RELAY_BIND="$DERP_BIND"; RELAY_PORT="$DERP_PORT"
    echo "-- [2/4] derp-relay server           (DERP region 1) :$RELAY_PORT"
  fi
  DRORB_DERP_LISTEN="$RELAY_BIND" \
  stdbuf -oL -eL nohup "$DERP_RELAY" server "$RELAY_PORT" \
    > "$RUN_DIR/derp.out" 2>&1 &
  echo $! > "$RUN_DIR/derp.pid"
  # ★ the check that closes the adopt-a-foreign-relay hole.
  wait_own "$RELAY_PORT" "DERP relay" "$RUN_DIR/derp.pid" || exit 1

  # 3. the verified STUN Binding server — the reflexive-endpoint half of direct paths.
  if [ "$STUN_PORT" != "0" ]; then
    echo "-- [3/4] stun-live server            (STUN Binding)  :$STUN_PORT/udp"
    stdbuf -oL -eL nohup "$STUN_LIVE" server "$STUN_PORT" "$STUN_BIND" \
      > "$RUN_DIR/stun.out" 2>&1 &
    echo $! > "$RUN_DIR/stun.pid"
    wait_own_udp "$STUN_PORT" "STUN server" "$RUN_DIR/stun.pid" || exit 1
  else
    echo "-- [3/4] stun-live server            SKIPPED (STUN_PORT=0)"
  fi

  # 4. the stock-client HTTP front door (dataplane host glue).
  if [ "$DERP_TLS" = "1" ]; then
    echo "-- [4/4] dataplane control front     (/key + /ts2021) :$FRONT_PORT"
    echo "         + DERP TLS front            (verified terminator) :$DERP_PORT"
    DERP_ENV=(DRORB_DERP_TLS_LISTEN="$DERP_BIND:$DERP_PORT"
              DRORB_DERP_PLAIN="127.0.0.1:$DERP_PLAIN_PORT")
  else
    echo "-- [4/4] dataplane control front     (/key + /ts2021) :$FRONT_PORT"
    # An unset DRORB_DERP_TLS_LISTEN is what keeps the front from binding at all; an
    # EMPTY one is not the same thing, so the var is added or omitted, never blanked.
    DERP_ENV=()
  fi
  env DRORB_BIND="127.0.0.1:$SERVE_PORT" \
      DRORB_CONTROL_LISTEN="$HOST_BIND:$FRONT_PORT" \
      DRORB_CONTROL_RESPONDER="127.0.0.1:$COORD_PORT" \
      DRORB_CONTROL_NOISE_PUB="$NOISE_PUB" \
      DRORB_TLS_CERT="$DERP_CERT" \
      DRORB_TLS_SEED="$DERP_SEED" \
      "${DERP_ENV[@]}" \
      stdbuf -oL -eL nohup "$DATAPLANE" > "$RUN_DIR/dataplane.out" 2>&1 &
  echo $! > "$RUN_DIR/dataplane.pid"
  wait_own "$FRONT_PORT" "control front door" "$RUN_DIR/dataplane.pid" || exit 1
  # ★ the same refusal-to-adopt check on the DERP TLS front's port: the dataplane pid
  #   must OWN :$DERP_PORT, or we would be pointing clients at someone else's listener.
  if [ "$DERP_TLS" = "1" ]; then
    wait_own "$DERP_PORT" "DERP TLS front" "$RUN_DIR/dataplane.pid" || exit 1
  fi

  # health: the front door must serve the coordinator's pubkey verbatim.
  echo
  echo "== health =="
  # probe the addr the front actually BOUND: with HOST_BIND=<LAN IP> there is no
  # listener on 127.0.0.1, so the old hardcoded loopback probe reported a healthy
  # plane as broken.
  KEY_JSON="$(curl -s "http://$(reachable_addr):$FRONT_PORT/key?v=90" || true)"
  if printf '%s' "$KEY_JSON" | grep -q "$NOISE_PUB"; then
    echo "  GET /key  -> mkey:$NOISE_PUB  (front door pins the verified responder static) OK"
  else
    echo "  ! GET /key did not return the coordinator pubkey:" >&2
    echo "    $KEY_JSON" >&2
  fi
  cmd_status
  echo
  echo "== the plane is up. next, as the operator: =="
  echo "  # (optional) mint a fresh reusable pre-auth key, then re-run \`$0 up\`:"
  echo "  DRORB_STORE=$DRORB_STORE $DRORB_CTL preauthkeys create --reusable --tags tag:server"
  echo
  echo "  # point a stock tailscale client at the plane (built-in demo key shown):"
  RA="$(reachable_addr)"
  LOGIN_SERVER="http://$RA:$FRONT_PORT/"
  echo "  tailscale up --login-server=$LOGIN_SERVER --authkey=tskey-auth-drorb-h2noise-selftest"
  echo
  echo "  # login server : $LOGIN_SERVER"
  if [ "$DERP_TLS" = "1" ]; then
    echo "  # served DERP  : region 1 at https://$DERP_ADV:$DERP_PORT/derp — VERIFIED TLS 1.3 terminator"
    echo "  #                (drorb_tls_terminate) in front of the verified Lean relay on 127.0.0.1:$DERP_PLAIN_PORT"
    echo "  #                CertName $DERP_CERTNAME (derived from $DERP_CERT)"
  else
    echo "  # served DERP  : region 1 at $DERP_ADV:$DERP_PORT PLAINTEXT (relay bound on $DERP_BIND)"
    echo "  #                NOTE a STOCK client dials https:// here and will fail; set DERP_TLS=1"
  fi
  if [ "$STUN_PORT" != "0" ]; then
    echo "  # served STUN  : $DERP_ADV:$STUN_PORT/udp (bound on $STUN_BIND) — netcheck learns its reflexive endpoint here"
  fi
  grep -m1 "advertising DERP region" "$RUN_DIR/coord.out" 2>/dev/null \
    | sed "s/^/  # coord says  : /" || true
  if [ "$HOST_BIND" != "127.0.0.1" ]; then
    echo "  # control front is routable on $HOST_BIND:$FRONT_PORT (reach it as http://$RA:$FRONT_PORT/)"
    echo "  # NOTE: PLAINTEXT HTTP. A verified-TLS front (https://) needs the Lean"
    echo "  #       decrypted-duplex export (see report); a stock client accepts a"
    echo "  #       self-signed cert there (control-cert verification is demoted to a warning)."
  fi
  echo
  echo "  # manage:"
  echo "  DRORB_STORE=$DRORB_STORE $DRORB_CTL nodes list"
  echo "  DRORB_STORE=$DRORB_STORE $DRORB_CTL routes list"
  echo "  $0 stop     # bring the plane down"
}

case "${1:-up}" in
  up|"")   cmd_up ;;
  stop)    cmd_stop ;;
  status)  cmd_status ;;
  *) echo "usage: $0 [up|stop|status]" >&2; exit 2 ;;
esac
