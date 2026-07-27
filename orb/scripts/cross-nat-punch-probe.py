#!/usr/bin/env python3
"""cross-nat-punch-probe.py — characterise the two-NAT topology WITHOUT tailscale.

Answers three questions with raw UDP sockets, so the answer cannot be confounded
by anything drorb or magicsock does:

  1. MAPPING BEHAVIOUR. Does one internal (ip,port) map to the SAME external port
     for different destinations (endpoint-INDEPENDENT / cone, punchable) or a
     different one (endpoint-DEPENDENT / symmetric, not punchable by plain STUN)?
  2. IS THE TOPOLOGY PUNCHABLE AT ALL? A textbook simultaneous open: both sides
     learn their reflexive port from the drorb STUN server, exchange it out of
     band, then send to each other at the same moment. If bytes arrive, the two
     NATs can be punched and any failure above this layer is a discovery failure,
     not a network one.
  3. PORT SHADOWING. If the PEER's packet reaches the NAT before the local side
     has created its own outbound flow to that peer, does the NAT remap the
     source port? This is the race that makes a cone NAT look symmetric to a
     peer, and it is invisible to STUN (whose own flow keeps the old mapping).

Run from the host netns: it drives netns drorbnat-a / drorbnat-b via `ip netns exec`.
"""
import json
import os
import socket
import struct
import subprocess
import sys
import time

NS_A, NS_B = "drorbnat-a", "drorbnat-b"
A_PRIV, B_PRIV = "10.77.11.2", "10.77.12.2"
A_PUB, B_PUB = "10.77.1.2", "10.77.2.2"
PLANE, STUN_PORT = "10.77.0.1", 3478

# The worker that runs INSIDE a client namespace. Kept as a string so the whole
# probe is one file; `ip netns exec ... python3 -c` runs it.
WORKER = r'''
import json, socket, struct, sys, time, os, secrets

def stun_reflexive(sock, server, port):
    """One RFC 5389 Binding request; return the XOR-MAPPED-ADDRESS the drorb
    verified STUN server reflects back (this is the same service tailscale
    netcheck uses)."""
    txid = secrets.token_bytes(12)
    req = struct.pack("!HHI12s", 0x0001, 0, 0x2112A442, txid)
    sock.sendto(req, (server, port))
    sock.settimeout(3)
    data, _ = sock.recvfrom(2048)
    mtype, mlen, cookie, rtx = struct.unpack("!HHI12s", data[:20])
    off = 20
    while off + 4 <= len(data):
        atype, alen = struct.unpack("!HH", data[off:off+4])
        val = data[off+4:off+4+alen]
        if atype == 0x0020:            # XOR-MAPPED-ADDRESS
            xport = struct.unpack("!H", val[2:4])[0] ^ (0x2112A442 >> 16)
            xip = bytes(b ^ c for b, c in zip(val[4:8], struct.pack("!I", 0x2112A442)))
            return socket.inet_ntoa(xip), xport
        off += 4 + alen + ((4 - alen % 4) % 4)
    return None, None

cmd = json.loads(sys.argv[1])
bindip, bindport = cmd["bind"]
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind((bindip, bindport))
out = {}

if cmd["op"] == "stun":
    ip, port = stun_reflexive(s, cmd["stun"][0], cmd["stun"][1])
    out["reflexive"] = [ip, port]

elif cmd["op"] == "punch":
    ip, port = stun_reflexive(s, cmd["stun"][0], cmd["stun"][1])
    out["reflexive"] = [ip, port]
    # wait until the agreed wall-clock instant, then simultaneous open
    while time.time() < cmd["at"]:
        time.sleep(0.005)
    peer = tuple(cmd["peer"])
    got = []
    s.settimeout(0.4)
    for i in range(25):
        try:
            s.sendto(("punch-%s-%d" % (cmd["tag"], i)).encode(), peer)
        except OSError as e:
            out.setdefault("senderr", str(e))
        try:
            d, src = s.recvfrom(2048)
            got.append([d.decode("utf8", "replace"), "%s:%d" % src])
        except socket.timeout:
            pass
    out["received"] = got

elif cmd["op"] == "shadow":
    # establish the STUN mapping first (this is what the peer will be told)
    ip, port = stun_reflexive(s, cmd["stun"][0], cmd["stun"][1])
    out["reflexive_before"] = [ip, port]
    out["local_port"] = s.getsockname()[1]
    while time.time() < cmd["at"]:
        time.sleep(0.005)
    # NOW send outbound to the peer -- AFTER the peer has (or has not) already
    # sprayed this NAT. The host reads the resulting external port off the wire.
    for i in range(6):
        s.sendto(b"post-shadow-%d" % i, tuple(cmd["peer"]))
        time.sleep(0.2)
    ip2, port2 = stun_reflexive(s, cmd["stun"][0], cmd["stun"][1])
    out["reflexive_after"] = [ip2, port2]

elif cmd["op"] == "spray":
    while time.time() < cmd["at"]:
        time.sleep(0.005)
    for i in range(8):
        s.sendto(b"peer-first-%d" % i, tuple(cmd["peer"]))
        time.sleep(0.15)
    out["sprayed"] = True

print(json.dumps(out))
'''


def run_in(ns, cmd, background=False):
    argv = ["sudo", "ip", "netns", "exec", ns, "python3", "-c", WORKER, json.dumps(cmd)]
    if background:
        return subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p = subprocess.run(argv, capture_output=True, text=True)
    if p.returncode != 0:
        return {"error": p.stderr.strip()[-400:]}
    return json.loads(p.stdout)


def reap(p):
    o, e = p.communicate()
    try:
        return json.loads(o)
    except Exception:
        return {"error": (e or o).decode()[-400:]}


def tcpdump(ns, iface, expr, seconds, path):
    return subprocess.Popen(
        ["sudo", "ip", "netns", "exec", ns, "timeout", str(seconds),
         "tcpdump", "-n", "-l", "-i", iface, expr],
        stdout=open(path, "w"), stderr=subprocess.DEVNULL)


def hdr(n, s):
    print("\n" + "=" * 72)
    print("[%d] %s" % (n, s))
    print("=" * 72)


# ── 1. mapping behaviour ───────────────────────────────────────────────────────
hdr(1, "MAPPING BEHAVIOUR — same internal port, three destinations")
cap = tcpdump("drorbnat-bn", "drorbnat-bu", "udp and src %s and not port 41641" % B_PUB,
              10, "/tmp/drorbnat/map.txt")
time.sleep(1.5)
subprocess.run(["sudo", "ip", "netns", "exec", NS_B, "python3", "-c", r'''
import socket, time
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind(("%s", 50601))
for dst in [("%s", 3478), ("%s", 9999), ("10.77.2.1", 9999)]:
    s.sendto(b"m", dst); time.sleep(0.4)
''' % (B_PRIV, PLANE, A_PUB)], capture_output=True)
cap.wait()
print(open("/tmp/drorbnat/map.txt").read().strip() or "(no packets captured)")
print("\n  -> all three lines showing the SAME external source port means the NAT is")
print("     ENDPOINT-INDEPENDENT (cone): STUN's answer is usable by a peer, punchable.")

# ── 2. is the topology punchable at all ────────────────────────────────────────
hdr(2, "SIMULTANEOUS OPEN — is this topology punchable at all?")
at = time.time() + 4.0
pa = run_in(NS_A, {"op": "stun", "bind": [A_PRIV, 50701], "stun": [PLANE, STUN_PORT]})
pb = run_in(NS_B, {"op": "stun", "bind": [B_PRIV, 50702], "stun": [PLANE, STUN_PORT]})
print("  A reflexive (from the VERIFIED drorb STUN server): %s" % (pa.get("reflexive"),))
print("  B reflexive (from the VERIFIED drorb STUN server): %s" % (pb.get("reflexive"),))
if pa.get("reflexive") and pb.get("reflexive") and pa["reflexive"][0]:
    at = time.time() + 3.0
    ha = run_in(NS_A, {"op": "punch", "bind": [A_PRIV, 50701], "stun": [PLANE, STUN_PORT],
                       "peer": pb["reflexive"], "at": at, "tag": "A"}, background=True)
    hb = run_in(NS_B, {"op": "punch", "bind": [B_PRIV, 50702], "stun": [PLANE, STUN_PORT],
                       "peer": pa["reflexive"], "at": at, "tag": "B"}, background=True)
    ra, rb = reap(ha), reap(hb)
    print("  A received %d datagram(s) from B: %s" % (len(ra.get("received", [])), ra.get("received", [])[:2]))
    print("  B received %d datagram(s) from A: %s" % (len(rb.get("received", [])), rb.get("received", [])[:2]))
    if ra.get("received") and rb.get("received"):
        print("\n  -> ★ PUNCHED. Two hosts behind two separate NATs, each unable to reach the")
        print("     other's private address, exchanged UDP directly using ONLY the reflexive")
        print("     addresses the VERIFIED drorb STUN server gave them. The topology is")
        print("     punchable; any failure above this layer is an ENDPOINT DISCOVERY failure.")
    else:
        print("\n  -> NOT punched even with correct ports — the topology itself blocks traversal.")
else:
    print("  !! STUN did not answer; cannot run the punch. %s %s" % (pa, pb))

# ── 3. port shadowing ──────────────────────────────────────────────────────────
hdr(3, "PORT SHADOWING — does the peer's packet arriving FIRST move the mapping?")
cap = tcpdump("drorbnat-bn", "drorbnat-bu", "udp and dst %s and not port 41641" % A_PUB,
              16, "/tmp/drorbnat/shadow.txt")
time.sleep(1.5)
at = time.time() + 3.0
# A sprays B's about-to-be-used external port BEFORE B has any outbound flow to A.
spray = run_in(NS_A, {"op": "spray", "bind": [A_PRIV, 50801], "peer": [B_PUB, 50802],
                      "at": at}, background=True)
shadow = run_in(NS_B, {"op": "shadow", "bind": [B_PRIV, 50802], "stun": [PLANE, STUN_PORT],
                       "peer": [A_PUB, 50801], "at": at + 1.5}, background=True)
reap(spray)
res = reap(shadow)
cap.wait()
print("  B's internal port                     : %s" % res.get("local_port"))
print("  B's reflexive BEFORE the peer sprayed : %s" % (res.get("reflexive_before"),))
print("  B's reflexive AFTER  (what STUN says) : %s" % (res.get("reflexive_after"),))
print("  B's ACTUAL external port toward A, on the wire:")
print(open("/tmp/drorbnat/shadow.txt").read().strip() or "  (no packets)")
print("\n  -> If the wire port differs from what STUN reports, the peer's early packet")
print("     SHADOWED the mapping: the NAT is cone, but looks symmetric to that one peer,")
print("     and STUN cannot see it because STUN's own flow still holds the old port.")
