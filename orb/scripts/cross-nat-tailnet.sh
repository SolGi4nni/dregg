#!/usr/bin/env bash
# cross-nat-tailnet.sh — a GENUINE two-NAT topology for testing drorb hole punching.
#
# The claim this harness exists to make falsifiable: when two stock `tailscale`
# clients enrol against a drorb plane from behind SEPARATE NATs, and they cannot
# reach each other's private addresses at all, any `direct` path that later
# appears MUST have been punched through both NATs. A demo where the two clients
# share an L2 (or can route to each other's private addresses) proves nothing —
# `direct` there is just "they were already reachable".
#
# ── the topology ───────────────────────────────────────────────────────────────
#
#   host netns (the drorb plane: coordinator / DERP / STUN, bound on 10.77.0.1)
#        │  drorbnat-h0  10.77.0.1/24
#        │
#        │  drorbnat-n0  10.77.0.2/24
#   ┌────┴───────────────── netns drorbnat-net ──────────────────────────────┐
#   │  "the internet": pure IP forwarding, NO nat, and — critically — NO      │
#   │  route to either client's private subnet. This is what makes the two    │
#   │  clients mutually unreachable by private address.                       │
#   │    drorbnat-na 10.77.1.1/24            drorbnat-nb 10.77.2.1/24         │
#   └────┬────────────────────────────────────────────┬──────────────────────┘
#        │ drorbnat-au 10.77.1.2                      │ drorbnat-bu 10.77.2.2
#   ┌────┴── netns drorbnat-an ──┐              ┌─────┴── netns drorbnat-bn ──┐
#   │ NAT A: MASQUERADE out      │              │ NAT B: MASQUERADE out       │
#   │   drorbnat-au, ip_forward  │              │   drorbnat-bu, ip_forward   │
#   │   drorbnat-ai 10.77.11.1   │              │   drorbnat-bi 10.77.12.1    │
#   └────┬───────────────────────┘              └─────┬───────────────────────┘
#        │ drorbnat-ac 10.77.11.2/24                  │ drorbnat-bc 10.77.12.2/24
#   ┌────┴── netns drorbnat-a ───┐              ┌─────┴── netns drorbnat-b ───┐
#   │ stock tailscaled (client)  │              │ stock tailscaled (client)   │
#   └────────────────────────────┘              └─────────────────────────────┘
#
# So each client's PRIVATE address (10.77.11.2 / 10.77.12.2) exists only inside
# its own NAT, and drorbnat-net holds no route to either. Its PUBLIC address is
# its NAT's uplink (10.77.1.2 / 10.77.2.2) — the address the drorb STUN server
# reflects back to it, and the only address the other client could ever aim at.
#
# ── safety ─────────────────────────────────────────────────────────────────────
# Everything created is prefixed `drorbnat-`. In the HOST netns this harness adds
# exactly three things, all removed by `down`:
#   1. the veth pair drorbnat-h0/drorbnat-n0   (n0 is moved into drorbnat-net)
#   2. one route: 10.77.0.0/16 via 10.77.0.2 dev drorbnat-h0
#   3. one INPUT rule scoped to that interface: -i drorbnat-h0 -j ACCEPT
#      (the host's INPUT policy is DROP; without this the plane never answers)
# It never touches the default route, the LAN interface, ssh, or any tailscaled
# outside its own namespaces. The host's PRODUCTION tailscaled is not signalled.
#
# Usage:
#   scripts/cross-nat-tailnet.sh selftest    # ★ THE GATE: up -> prove isolation ->
#                                            #   plane -> enrol -> ASSERT direct both
#                                            #   ways -> re-prove isolation -> tear
#                                            #   down. Non-zero on any failure; exit
#                                            #   77 (with the reason) if a prerequisite
#                                            #   is absent. Wired into scripts/ci.sh
#                                            #   --cross-nat.
#   scripts/cross-nat-tailnet.sh preflight   # just the prerequisite check (0/77)
#   scripts/cross-nat-tailnet.sh up          # build the topology
#   scripts/cross-nat-tailnet.sh isolation   # PROVE A and B cannot reach each other
#   scripts/cross-nat-tailnet.sh punchprobe  # characterise the NATs WITHOUT tailscale
#   scripts/cross-nat-tailnet.sh enrol       # start a stock tailscaled in each client ns
#   scripts/cross-nat-tailnet.sh watch       # status + ping, both directions
#   scripts/cross-nat-tailnet.sh down        # tear EVERYTHING down
#   scripts/cross-nat-tailnet.sh verify-clean# assert nothing of ours remains
set -uo pipefail

SELF="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DRORB_ROOT="${DRORB_ROOT:-$(cd "$SELF/.." && pwd)}"

PFX=drorbnat
NS_NET="$PFX-net"
NS_AN="$PFX-an"; NS_BN="$PFX-bn"
NS_A="$PFX-a";   NS_B="$PFX-b"
IF_H0="$PFX-h0"; IF_N0="$PFX-n0"
IF_NA="$PFX-na"; IF_AU="$PFX-au"
IF_NB="$PFX-nb"; IF_BU="$PFX-bu"
IF_AI="$PFX-ai"; IF_AC="$PFX-ac"
IF_BI="$PFX-bi"; IF_BC="$PFX-bc"

# the plane's address, on the host side of the host<->internet link.
PLANE_IP="${PLANE_IP:-10.77.0.1}"
NET_IP=10.77.0.2
A_PUB=10.77.1.2;  A_GW=10.77.1.1
B_PUB=10.77.2.2;  B_GW=10.77.2.1
A_PRIV=10.77.11.2; A_PRIV_GW=10.77.11.1
B_PRIV=10.77.12.2; B_PRIV_GW=10.77.12.1
HOST_ROUTE=10.77.0.0/16

FRONT_PORT="${FRONT_PORT:-3351}"
DERP_PORT="${DERP_PORT:-3340}"
STUN_PORT="${STUN_PORT:-3478}"
AUTHKEY="${AUTHKEY:-tskey-auth-drorb-h2noise-selftest}"
RUN="${CROSSNAT_RUN:-/tmp/drorbnat}"
TS_PORT_A="${TS_PORT_A:-41641}"
TS_PORT_B="${TS_PORT_B:-41641}"

S=sudo
say() { printf '\n== %s\n' "$*"; }

nsx() { $S ip netns exec "$@"; }

# ── topology ───────────────────────────────────────────────────────────────────
cmd_up() {
  cmd_down >/dev/null 2>&1 || true
  mkdir -p "$RUN"
  say "building the two-NAT topology"

  for n in "$NS_NET" "$NS_AN" "$NS_BN" "$NS_A" "$NS_B"; do $S ip netns add "$n"; done

  # host <-> internet
  $S ip link add "$IF_H0" type veth peer name "$IF_N0"
  $S ip link set "$IF_N0" netns "$NS_NET"
  $S ip addr add "$PLANE_IP/24" dev "$IF_H0"
  $S ip link set "$IF_H0" up
  nsx "$NS_NET" ip addr add "$NET_IP/24" dev "$IF_N0"
  nsx "$NS_NET" ip link set "$IF_N0" up
  nsx "$NS_NET" ip link set lo up
  nsx "$NS_NET" sysctl -qw net.ipv4.ip_forward=1

  # internet <-> NAT A, NAT A <-> client A
  $S ip link add "$IF_NA" type veth peer name "$IF_AU"
  $S ip link set "$IF_NA" netns "$NS_NET"; $S ip link set "$IF_AU" netns "$NS_AN"
  nsx "$NS_NET" ip addr add "$A_GW/24" dev "$IF_NA";  nsx "$NS_NET" ip link set "$IF_NA" up
  nsx "$NS_AN"  ip addr add "$A_PUB/24" dev "$IF_AU"; nsx "$NS_AN"  ip link set "$IF_AU" up
  $S ip link add "$IF_AI" type veth peer name "$IF_AC"
  $S ip link set "$IF_AI" netns "$NS_AN"; $S ip link set "$IF_AC" netns "$NS_A"
  nsx "$NS_AN" ip addr add "$A_PRIV_GW/24" dev "$IF_AI"; nsx "$NS_AN" ip link set "$IF_AI" up
  nsx "$NS_A"  ip addr add "$A_PRIV/24"    dev "$IF_AC"; nsx "$NS_A"  ip link set "$IF_AC" up
  nsx "$NS_AN" ip link set lo up; nsx "$NS_A" ip link set lo up
  nsx "$NS_AN" ip route add default via "$A_GW"
  nsx "$NS_A"  ip route add default via "$A_PRIV_GW"
  nsx "$NS_AN" sysctl -qw net.ipv4.ip_forward=1
  # the NAT itself: plain MASQUERADE, no --random, so the mapping is the ordinary
  # Linux port-preserving one a homelab router actually has.
  nsx "$NS_AN" iptables -t nat -A POSTROUTING -o "$IF_AU" -j MASQUERADE
  # ★ the FILTERING half of a NAT, and it is not optional — see the note by NAT B.
  nsx "$NS_AN" iptables -A INPUT -i "$IF_AU" -m conntrack --ctstate INVALID,NEW -j DROP

  # internet <-> NAT B, NAT B <-> client B
  $S ip link add "$IF_NB" type veth peer name "$IF_BU"
  $S ip link set "$IF_NB" netns "$NS_NET"; $S ip link set "$IF_BU" netns "$NS_BN"
  nsx "$NS_NET" ip addr add "$B_GW/24" dev "$IF_NB";  nsx "$NS_NET" ip link set "$IF_NB" up
  nsx "$NS_BN"  ip addr add "$B_PUB/24" dev "$IF_BU"; nsx "$NS_BN"  ip link set "$IF_BU" up
  $S ip link add "$IF_BI" type veth peer name "$IF_BC"
  $S ip link set "$IF_BI" netns "$NS_BN"; $S ip link set "$IF_BC" netns "$NS_B"
  nsx "$NS_BN" ip addr add "$B_PRIV_GW/24" dev "$IF_BI"; nsx "$NS_BN" ip link set "$IF_BI" up
  nsx "$NS_B"  ip addr add "$B_PRIV/24"    dev "$IF_BC"; nsx "$NS_B"  ip link set "$IF_BC" up
  nsx "$NS_BN" ip link set lo up; nsx "$NS_B" ip link set lo up
  nsx "$NS_BN" ip route add default via "$B_GW"
  nsx "$NS_B"  ip route add default via "$B_PRIV_GW"
  nsx "$NS_BN" sysctl -qw net.ipv4.ip_forward=1
  nsx "$NS_BN" iptables -t nat -A POSTROUTING -o "$IF_BU" -j MASQUERADE
  # ★ THE FILTERING HALF OF A NAT — and it changes the answer, so it is documented.
  # A NAT is a mapping AND a filter: an unsolicited inbound datagram addressed to the
  # WAN address is DROPPED. Every home router does this. Without the rule the NAT box
  # ACCEPTS the packet into its own stack, conntrack CONFIRMS the entry, and that
  # confirmed entry then owns the external tuple -- so when the inside host later opens
  # its own flow to that same peer, nf_nat must pick a DIFFERENT source port. The NAT is
  # cone, but it now looks SYMMETRIC to exactly that one peer, and STUN cannot see it
  # (STUN's own flow still holds the original port). That is NAT port shadowing, and with
  # it the two clients here punch at ports the far NAT no longer maps: measured 2026-07-25,
  # STUN said 10.77.2.2:50802 while the wire showed 10.77.2.2:57983. With the rule the
  # mapping stays put and the punch lands. `cross-nat-punch-probe.py` [3] measures this.
  nsx "$NS_BN" iptables -A INPUT -i "$IF_BU" -m conntrack --ctstate INVALID,NEW -j DROP

  # the host's two additive bits, both scoped to our veth.
  $S ip route add "$HOST_ROUTE" via "$NET_IP" dev "$IF_H0"
  $S iptables -I INPUT 1 -i "$IF_H0" -j ACCEPT

  # per-netns resolv.conf so a client never blocks on the host's resolver.
  for n in "$NS_A" "$NS_B"; do
    $S mkdir -p "/etc/netns/$n"
    printf 'nameserver 127.0.0.53\n' | $S tee "/etc/netns/$n/resolv.conf" >/dev/null
  done

  echo "  topology up. client A private $A_PRIV behind NAT $A_PUB; client B private $B_PRIV behind NAT $B_PUB"
}

# ── the isolation proof ────────────────────────────────────────────────────────
# Run BEFORE any client starts. If this does not fail the way it claims to, the
# whole demo is worthless and the harness says so and exits nonzero.
cmd_isolation() {
  local fail=0
  say "ISOLATION PROOF (must run BEFORE the clients start)"

  echo "-- routing table the 'internet' namespace has (note: NO 10.77.11/12 route):"
  nsx "$NS_NET" ip -4 route

  echo
  echo "-- [1] A reaches the drorb plane at $PLANE_IP  (this MUST work)"
  if nsx "$NS_A" ping -c2 -W2 "$PLANE_IP"; then echo "   OK: A -> plane"; else echo "   FAIL: A cannot reach the plane"; fail=1; fi
  echo "-- [2] B reaches the drorb plane at $PLANE_IP  (this MUST work)"
  if nsx "$NS_B" ping -c2 -W2 "$PLANE_IP"; then echo "   OK: B -> plane"; else echo "   FAIL: B cannot reach the plane"; fail=1; fi

  echo
  echo "-- [3] A -> B PRIVATE address $B_PRIV  (this MUST FAIL)"
  if nsx "$NS_A" ping -c2 -W2 "$B_PRIV"; then echo "   FAIL: A CAN reach B privately — the topology is fake"; fail=1
  else echo "   OK: unreachable"; fi
  echo "-- [4] B -> A PRIVATE address $A_PRIV  (this MUST FAIL)"
  if nsx "$NS_B" ping -c2 -W2 "$A_PRIV"; then echo "   FAIL: B CAN reach A privately — the topology is fake"; fail=1
  else echo "   OK: unreachable"; fi

  echo
  echo "-- [5] the 'internet' namespace has NO ROUTE to either private subnet"
  echo "   ip route get $B_PRIV, from inside $NS_NET:"
  nsx "$NS_NET" ip route get "$B_PRIV" 2>&1 | sed 's/^/     /'
  nsx "$NS_NET" ip route get "$A_PRIV" 2>&1 | sed 's/^/     /'
  echo "   (RTNETLINK/unreachable above = the two clients are not on a shared L2 and"
  echo "    nothing between them can forward a private-addressed packet)"

  echo
  echo "-- [7] the NAT is REAL: A's source address as the plane SEES it"
  echo "   A private addr: $(nsx "$NS_A" ip -4 -o addr show "$IF_AC" | awk '{print $4}')"
  echo "   plane-side view of an A packet:"
  $S timeout 4 tcpdump -n -i "$IF_H0" -c1 "icmp and dst $PLANE_IP" >"$RUN/nat-a.pcap.txt" 2>/dev/null &
  local tp=$!; sleep 1; nsx "$NS_A" ping -c3 -W1 "$PLANE_IP" >/dev/null 2>&1 || true; wait $tp 2>/dev/null || true
  cat "$RUN/nat-a.pcap.txt" 2>/dev/null || true
  echo "   (source must read $A_PUB, NOT $A_PRIV — that is the NAT rewriting)"

  echo
  if [ "$fail" = 0 ]; then
    echo "ISOLATION PROVEN: both clients reach the plane; neither can reach the other's"
    echo "private address. Any 'direct' path that forms from here MUST be punched."
  else
    echo "ISOLATION NOT PROVEN — refusing to call anything that follows a NAT demo." >&2
    return 1
  fi
}

# ── clients ────────────────────────────────────────────────────────────────────
start_client() {
  local ns="$1" tag="$2" port="$3"
  local d="$RUN/$tag"
  $S rm -rf "$d"; $S mkdir -p "$d"
  $S sh -c "TS_DEBUG_MAP=1 nohup ip netns exec $ns /usr/sbin/tailscaled \
      --tun=userspace-networking \
      --statedir=$d --socket=$d/ts.sock --port=$port --verbose=1 \
      >$d/tailscaled.log 2>&1 & echo \$! >$d/pid"
  sleep 2
  echo "   $tag tailscaled pid $($S cat "$d/pid") (netns $ns, udp :$port)"
}

cmd_enrol() {
  say "starting a stock tailscaled in each client namespace"
  start_client "$NS_A" a "$TS_PORT_A"
  start_client "$NS_B" b "$TS_PORT_B"
  sleep 2
  for t in a b; do
    local ns; [ "$t" = a ] && ns="$NS_A" || ns="$NS_B"
    echo "-- enrolling $t"
    $S ip netns exec "$ns" tailscale --socket="$RUN/$t/ts.sock" up \
      --login-server="http://$PLANE_IP:$FRONT_PORT/" \
      --authkey="$AUTHKEY" --hostname="natnode-$t" \
      --accept-dns=false --accept-routes=false 2>&1 | sed 's/^/     /'
  done
}

ts() { local t="$1"; shift; local ns; [ "$t" = a ] && ns="$NS_A" || ns="$NS_B"
       $S ip netns exec "$ns" tailscale --socket="$RUN/$t/ts.sock" "$@"; }

cmd_watch() {
  say "tailscale status / ping, both directions"
  for t in a b; do echo "-- client $t status"; ts "$t" status 2>&1 | sed 's/^/   /'; done
  local ipa ipb
  ipa="$(ts a ip -4 2>/dev/null | head -1)"; ipb="$(ts b ip -4 2>/dev/null | head -1)"
  echo "-- A($ipa) ping B($ipb)"; ts a ping -c 6 "$ipb" 2>&1 | sed 's/^/   /'
  echo "-- B($ipb) ping A($ipa)"; ts b ping -c 6 "$ipa" 2>&1 | sed 's/^/   /'
  for t in a b; do echo "-- client $t status (after ping)"; ts "$t" status 2>&1 | sed 's/^/   /'; done
}

cmd_stopclients() {
  for t in a b; do
    local p; p="$($S cat "$RUN/$t/pid" 2>/dev/null || true)"
    if [ -n "$p" ]; then
      # kill by EXACT pid, and only if it is one of ours (in our netns).
      if $S readlink "/proc/$p/ns/net" >/dev/null 2>&1; then $S kill "$p" 2>/dev/null || true; fi
      echo "  killed client $t pid $p"
    fi
  done
  sleep 1
  # tailscaled forks a child; reap any left in OUR namespaces only, by exact pid.
  for ns in "$NS_A" "$NS_B"; do
    local pids; pids="$($S ip netns pids "$ns" 2>/dev/null || true)"
    for p in $pids; do echo "  reaping leftover pid $p in $ns"; $S kill "$p" 2>/dev/null || true; done
  done
}

# ── teardown ───────────────────────────────────────────────────────────────────
cmd_down() {
  say "tearing down (netns, veths, host route, host INPUT rule)"
  cmd_stopclients 2>/dev/null || true
  sleep 1
  for ns in "$NS_A" "$NS_B" "$NS_AN" "$NS_BN" "$NS_NET"; do
    $S ip netns pids "$ns" >/dev/null 2>&1 && $S ip netns pids "$ns" | xargs -r $S kill -9 2>/dev/null || true
    $S ip netns del "$ns" 2>/dev/null && echo "  netns $ns removed" || true
  done
  for l in "$IF_H0" "$IF_N0" "$IF_NA" "$IF_AU" "$IF_NB" "$IF_BU" "$IF_AI" "$IF_AC" "$IF_BI" "$IF_BC"; do
    $S ip link del "$l" 2>/dev/null && echo "  link $l removed" || true
  done
  $S ip route del "$HOST_ROUTE" via "$NET_IP" dev "$IF_H0" 2>/dev/null && echo "  host route removed" || true
  while $S iptables -C INPUT -i "$IF_H0" -j ACCEPT 2>/dev/null; do
    $S iptables -D INPUT -i "$IF_H0" -j ACCEPT && echo "  host INPUT rule removed"
  done
  for n in "$NS_A" "$NS_B"; do $S rm -rf "/etc/netns/$n"; done
  $S rmdir /etc/netns 2>/dev/null || true
  echo "  teardown complete."
}

cmd_verify_clean() {
  say "VERIFY CLEAN"
  echo "-- ip netns list:"; $S ip netns list; echo "   (empty above = no namespaces of ours)"
  echo "-- links named $PFX-*:"; ip -o link show | grep -F "$PFX-" || echo "   (none)"
  echo "-- host routes 10.77.*:"; ip -4 route | grep -F 10.77 || echo "   (none)"
  echo "-- host INPUT rules mentioning $PFX:"; $S iptables -S INPUT | grep -F "$PFX" || echo "   (none)"
  echo "-- host nat POSTROUTING:"; $S iptables -t nat -L POSTROUTING -n
  echo "-- /etc/netns:"; ls /etc/netns 2>&1 || true
  echo "-- PROD tailscaled pid 2379:"; ps -p 2379 -o pid,etime,cmd || echo "   !! MISSING !!"
}

cmd_punchprobe() { python3 "$SELF/cross-nat-punch-probe.py"; }

# ── the SELF-CHECKING gate ─────────────────────────────────────────────────────
# Everything above is a hand-driven verb: `up`, then `isolation`, then start a
# plane, then `enrol`, then read `watch` with your eyes. That is exactly how the
# cross-NAT row in the quickstart became a dated my-hand result that nothing
# re-runs — and un-re-run results rot silently (the endpoint plumbing rotted for
# weeks under a green build). `selftest` is the one entrypoint that stands the
# topology up, PROVES the isolation, brings the drorb plane up on the harness
# address, enrols two stock clients, ASSERTS a `direct` path in BOTH directions
# to the far NAT's PUBLIC address, re-proves the isolation while that path is up,
# and tears everything down — non-zero on any failure, and non-zero if anything
# of ours survives the teardown.
#
# Exit codes (scripts/ci.sh reads them):
#   0   PASS   — direct both ways, isolation proven before AND during, clean after
#   77  SKIP   — a PREREQUISITE is absent (no root, no tailscaled, 10.77/16 in
#                use, binaries not built). Always printed with the reason.
#   1   FAIL   — the demo ran and did not reproduce.
SELFTEST_DIRECT_TIMEOUT="${SELFTEST_DIRECT_TIMEOUT:-120}"
PLANE_RUN="${PLANE_RUN:-/tmp/drorbnat-plane}"

skip() { echo; echo "SKIP: $*" >&2; echo "  (cross-NAT selftest needs root, a stock tailscaled, a free 10.77.0.0/16," >&2
         echo "   and built drorb binaries; it is opt-in for exactly this reason.)" >&2; exit 77; }
fail() { echo; echo "FAIL: $*" >&2; exit 1; }

cmd_preflight() {
  say "PRE-FLIGHT (every prerequisite named out loud)"
  local ok=1

  # root — the harness creates netns, veths and iptables rules.
  if [ "$(id -u)" != 0 ]; then
    if ! sudo -n true 2>/dev/null; then
      skip "no non-interactive root (\`sudo -n true\` failed) — netns/iptables need it"
    fi
    echo "  root:        via passwordless sudo  OK"
  else
    echo "  root:        uid 0  OK"
  fi

  # tools
  for t in ip iptables ss python3; do
    if command -v "$t" >/dev/null 2>&1; then echo "  tool $t:      $(command -v "$t")  OK"
    else skip "missing tool: $t"; fi
  done
  [ -x /usr/sbin/tailscaled ] || skip "no stock tailscaled at /usr/sbin/tailscaled (this gate tests a STOCK client, not a drorb client)"
  command -v tailscale >/dev/null 2>&1 || skip "no stock \`tailscale\` CLI on PATH"
  echo "  tailscaled:  $(/usr/sbin/tailscaled --version 2>/dev/null | head -1)  OK"

  # the drorb plane's binaries (the gate must not silently test nothing)
  local bin="$DRORB_ROOT/.lake/build/bin"
  for b in control-live derp-relay stun-live drorb-ctl; do
    [ -x "$bin/$b" ] || skip "missing $bin/$b — run: lake build control-live derp-relay stun-live drorb-ctl"
  done
  [ -x "$DRORB_ROOT/target/release/dataplane" ] || skip "missing $DRORB_ROOT/target/release/dataplane — run: bash ffi/build-dataplane-lib.sh && cargo build --release -p dataplane"
  echo "  binaries:    control-live, derp-relay, stun-live, drorb-ctl, dataplane  OK"

  # the address space must be OURS. A host that already routes 10.77/16 would
  # make the isolation proof meaningless (and we would tear down someone's route).
  if ip -4 route show | grep -qE '(^|via |dev )10\.77\.'; then
    ip -4 route show | grep -E '10\.77\.' | sed 's/^/    /'
    skip "10.77.0.0/16 is already routed on this host — refusing to touch it"
  fi
  if ip -4 -o addr show | grep -q ' 10\.77\.'; then
    skip "10.77.0.0/16 is already addressed on this host — refusing to touch it"
  fi
  echo "  10.77/16:    free  OK"

  # no leftovers of ours (a previous crashed run) — refuse rather than adopt.
  if $S ip netns list 2>/dev/null | grep -q "^$PFX-"; then
    $S ip netns list | sed 's/^/    /'
    skip "a previous $PFX- netns still exists — run \`$0 down\` first"
  fi
  if ip -o link show 2>/dev/null | grep -qF "$PFX-"; then
    skip "a previous $PFX- link still exists — run \`$0 down\` first"
  fi
  echo "  namespaces:  no $PFX-* leftovers  OK"

  # the plane's ports
  for p in "$FRONT_PORT" "$DERP_PORT"; do
    if ss -ltn 2>/dev/null | awk '{print $4}' | grep -qE "[:.]${p}\$"; then
      skip "TCP port :$p is already bound — the plane would adopt a foreign listener"
    fi
  done
  if ss -lun 2>/dev/null | awk '{print $4}' | grep -qE "[:.]${STUN_PORT}\$"; then
    skip "UDP port :$STUN_PORT is already bound — the plane would adopt a foreign STUN server"
  fi
  echo "  ports:       $FRONT_PORT/tcp $DERP_PORT/tcp $STUN_PORT/udp free  OK"

  # the PRODUCTION tailnet must be untouched by anything we do. Record its pid so
  # the post-run assertion can prove we did not signal it.
  PROD_TS_PID="$(pgrep -f '^/usr/sbin/tailscaled --state=' | head -1 || true)"
  if [ -n "$PROD_TS_PID" ]; then
    echo "  prod tailscaled: pid $PROD_TS_PID (recorded; asserted alive after teardown)"
  else
    echo "  prod tailscaled: none running"
  fi
  return 0
}

# Bring the drorb plane up ON the harness address, so the clients reach a plane
# that is inside the topology's routing (10.77.0.1), never the host's LAN.
plane_up() {
  say "starting the drorb plane on $PLANE_IP (control front, DERP TLS front, STUN)"
  rm -rf "$PLANE_RUN"; mkdir -p "$PLANE_RUN"
  if ! HOST_BIND="$PLANE_IP" FRONT_PORT="$FRONT_PORT" DERP_PORT="$DERP_PORT" \
       STUN_PORT="$STUN_PORT" RUN_DIR="$PLANE_RUN" \
       bash "$SELF/run-tailnet.sh" up >"$PLANE_RUN/up.log" 2>&1; then
    tail -n 30 "$PLANE_RUN/up.log" >&2
    fail "the drorb plane did not come up (see $PLANE_RUN/up.log)"
  fi
  grep -E 'ownership OK|GET /key' "$PLANE_RUN/up.log" | sed 's/^/  /'
}

plane_down() {
  [ -d "$PLANE_RUN" ] || return 0
  HOST_BIND="$PLANE_IP" RUN_DIR="$PLANE_RUN" bash "$SELF/run-tailnet.sh" stop >/dev/null 2>&1 || true
}

# The single teardown, wired to EXIT so a failure anywhere still cleans up.
selftest_cleanup() {
  local rc=$?
  say "TEARDOWN (runs on every exit path, including failure)"
  plane_down
  cmd_down >/dev/null 2>&1 || true
  # and PROVE it is gone — a teardown that half-worked is a dirty box.
  local dirty=0
  $S ip netns list 2>/dev/null | grep -q "^$PFX-" && { echo "  !! netns of ours REMAIN:" >&2; $S ip netns list >&2; dirty=1; }
  ip -o link show 2>/dev/null | grep -qF "$PFX-" && { echo "  !! links of ours REMAIN:" >&2; ip -o link show | grep -F "$PFX-" >&2; dirty=1; }
  ip -4 route show 2>/dev/null | grep -qE '10\.77\.' && { echo "  !! host routes REMAIN:" >&2; ip -4 route show | grep -E '10\.77\.' >&2; dirty=1; }
  $S iptables -S INPUT 2>/dev/null | grep -qF "$PFX-" && { echo "  !! host INPUT rules REMAIN:" >&2; dirty=1; }
  echo "  ip netns list -> $($S ip netns list 2>/dev/null | tr '\n' ' ')(empty = clean)"
  if [ -n "${PROD_TS_PID:-}" ]; then
    # /proc, not `kill -0`: the production daemon runs as root, and `kill -0` from a
    # non-root shell fails with EPERM on a LIVE process — which reported the production
    # tailnet dead on every run and failed an otherwise clean teardown.
    if [ -d "/proc/$PROD_TS_PID" ]; then
      echo "  production tailscaled pid $PROD_TS_PID: STILL ALIVE (never signalled)  OK"
    else
      echo "  !! production tailscaled pid $PROD_TS_PID is GONE" >&2; dirty=1
    fi
  fi
  if [ "$dirty" != 0 ]; then
    echo "TEARDOWN INCOMPLETE — failing even if the demo passed." >&2
    exit 1
  fi
  echo "  clean."
  exit $rc
}

# `tailscale status` line for the peer, on client $1.
# Matched by the peer's tailnet ADDRESS ($2), never by hostname: the netmap names
# nodes `node-N`, so a hostname grep silently matches nothing and this gate would
# time out on a run that actually worked — it did, the first time it was wired.
peer_status_line() { ts "$1" status 2>/dev/null | grep -F "$2" | head -1; }

# Wait until BOTH clients report `direct <far NAT public>:port` for each other,
# driving traffic (a `tailscale ping` is what makes magicsock start punching).
await_direct() {
  local deadline=$((SECONDS + SELFTEST_DIRECT_TIMEOUT))
  local ipa ipb la lb
  ipa="$(ts a ip -4 2>/dev/null | head -1)"; ipb="$(ts b ip -4 2>/dev/null | head -1)"
  [ -n "$ipa" ] && [ -n "$ipb" ] || fail "a client never got a tailnet address (A='$ipa' B='$ipb') — enrolment did not complete"
  echo "  A=$ipa  B=$ipb ; driving traffic until both report direct (timeout ${SELFTEST_DIRECT_TIMEOUT}s)"
  while [ "$SECONDS" -lt "$deadline" ]; do
    ts a ping -c 2 "$ipb" >/dev/null 2>&1 || true
    ts b ping -c 2 "$ipa" >/dev/null 2>&1 || true
    la="$(peer_status_line a "$ipb")"; lb="$(peer_status_line b "$ipa")"
    if printf '%s' "$la" | grep -qE "direct $B_PUB:[0-9]+" \
       && printf '%s' "$lb" | grep -qE "direct $A_PUB:[0-9]+"; then
      echo "  A sees: $la"
      echo "  B sees: $lb"
      return 0
    fi
    sleep 3
  done
  echo "  A sees: ${la:-<no peer line>}" >&2
  echo "  B sees: ${lb:-<no peer line>}" >&2
  return 1
}

cmd_selftest() {
  cmd_preflight || exit 1
  trap selftest_cleanup EXIT INT TERM

  cmd_up      || fail "topology did not come up"
  cmd_isolation || fail "ISOLATION NOT PROVEN before the run — any 'direct' after this would prove nothing"
  plane_up
  cmd_enrol   || fail "enrolment failed"

  say "ASSERTING a punched DIRECT path in BOTH directions"
  if ! await_direct; then
    say "diagnostics (the run did NOT reach direct)"
    for t in a b; do echo "-- client $t status"; ts "$t" status 2>&1 | sed 's/^/   /'; done
    echo "-- coordinator NAT reports (last 20):"
    grep 'NAT report' "$PLANE_RUN/coord.out" 2>/dev/null | tail -20 | sed 's/^/   /'
    fail "no direct path within ${SELFTEST_DIRECT_TIMEOUT}s — the punch did not land"
  fi

  # The isolation proof is worthless if the topology quietly gained a route WHILE
  # the clients ran. Re-prove it with the direct path UP: the private addresses
  # must still be unreachable, so the path that exists is through both NATs.
  say "RE-PROVING isolation WITH the direct path up"
  if nsx "$NS_A" ping -c2 -W2 "$B_PRIV" >/dev/null 2>&1; then
    fail "A can now reach B's PRIVATE address — the 'direct' path above is not a punch"
  fi
  if nsx "$NS_B" ping -c2 -W2 "$A_PRIV" >/dev/null 2>&1; then
    fail "B can now reach A's PRIVATE address — the 'direct' path above is not a punch"
  fi
  echo "  still unreachable by private address, in both directions  OK"
  nsx "$NS_NET" ip route get "$B_PRIV" 2>&1 | sed 's/^/    /'

  say "PASS — two stock clients behind two separate NATs hold a DIRECT path"
  echo "  A -> $B_PUB   B -> $A_PUB   (each other's NAT PUBLIC address)"
  echo "  isolation proven BEFORE and DURING; teardown follows."
}


case "${1:-}" in
  selftest)     cmd_selftest ;;
  preflight)    cmd_preflight ;;
  up)           cmd_up ;;
  isolation)    cmd_isolation ;;
  punchprobe)   cmd_punchprobe ;;
  enrol)        cmd_enrol ;;
  watch)        cmd_watch ;;
  stopclients)  cmd_stopclients ;;
  down)         cmd_down ;;
  verify-clean) cmd_verify_clean ;;
  *) echo "usage: $0 {selftest|preflight|up|isolation|punchprobe|enrol|watch|stopclients|down|verify-clean}" >&2; exit 2 ;;
esac
