#!/usr/bin/env python3
"""How many concurrent connections does ONE source actually get past
`max-connections 4`?

The reproduction behind dos/FINDING-per-shard-standing.md. On the shipped
reactor the per-source standing state is a per-SHARD field, so the cap is
silently multiplied by the shard count; this counts the REAL response lines off
REAL sockets so the multiplier is a measured number, not an inference.

    python3 dos/shard_gate_probe.py 19090                 # shipped reactor
    PROBE_IO=blocking python3 dos/shard_gate_probe.py 19091
    DRORB_SHARDS=1    python3 dos/shard_gate_probe.py 19092   # the control

Env:
  PROBE_IO  the `--io` reactor. Default `auto` = what the binary ships.
  CAP       the `max-connections` directive under probe (default 4).
  CONNS     concurrent connections to open (default 200).
"""
import os
import socket
import subprocess
import sys
import tempfile
import time

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 19090
CAP = int(os.environ.get("CAP", "4"))
CONNS = int(os.environ.get("CONNS", "200"))
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")

fd, cfg = tempfile.mkstemp(prefix="shard-gate-probe-", suffix=".conf")
os.write(fd, b"max-connections %d\n" % CAP)
os.close(fd)

log = open("/tmp/shard-gate-probe-%d.log" % PORT, "w")
proc = subprocess.Popen(
    [BIN, "--bind", "127.0.0.1:%d" % PORT, "--no-udp",
     "--io", os.environ.get("PROBE_IO", "auto")],
    env=dict(os.environ, DRORB_CONFIG=cfg),
    stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)

for _ in range(200):
    try:
        socket.create_connection(("127.0.0.1", PORT), 0.2).close()
        break
    except OSError:
        time.sleep(0.05)
else:
    print("serve never bound on :%d" % PORT)
    proc.kill()
    sys.exit(3)

# Open every connection FIRST, so they are genuinely concurrent: the gate is
# about simultaneous occupancy, and probing one at a time would let each close
# before the next arrives.
socks = []
for _ in range(CONNS):
    try:
        s = socket.create_connection(("127.0.0.1", PORT), 2.0)
        s.settimeout(2.0)
        socks.append(s)
    except OSError:
        break

codes = {}
for s in socks:
    try:
        s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
        line = s.recv(64).split(b"\r\n")[0].decode("latin1")
        codes[line] = codes.get(line, 0) + 1
    except OSError as e:
        key = "<socket error: %s>" % e
        codes[key] = codes.get(key, 0) + 1
    finally:
        s.close()

served = sum(v for k, v in codes.items() if "200" in k)
print("io=%-8s shards=%-4s cap=%d  opened=%d"
      % (os.environ.get("PROBE_IO", "auto"),
         os.environ.get("DRORB_SHARDS", "default"), CAP, len(socks)))
for k in sorted(codes, key=lambda k: -codes[k]):
    print("    %-40s %d" % (k, codes[k]))
print("    => admitted and SERVED under a cap of %d: %d" % (CAP, served))

proc.terminate()
try:
    proc.wait(5)
except subprocess.TimeoutExpired:
    proc.kill()
os.unlink(cfg)
