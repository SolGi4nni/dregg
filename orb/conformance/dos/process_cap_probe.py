#!/usr/bin/env python3
"""Does the PROCESS-WIDE hard connection ceiling mean what it says, at every
shard count?

The reproduction for the hard cap half of `dos/FINDING-per-shard-standing.md`.
`MAX_CONNS_PER_SHARD` was 16384 PER SHARD, so the real process ceiling was
`16384 * nproc` (393,216 on a 24-core host) and it moved when you changed
`--shards`. A ceiling that multiplies by the core count is not a ceiling.

This states a small ceiling (`DRORB_MAX_CONNS`), opens far more concurrent
connections than that from one source with NO `max-connections` directive in
force, and counts the REAL response lines off REAL sockets. The number must be
the ceiling, and must NOT move with the shard count.

    python3 dos/process_cap_probe.py 19120

Env:
  CAP     the process ceiling under probe (default 8)
  CONNS   concurrent connections to open (default 40)
"""
import os
import socket
import subprocess
import sys
import time

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 19120
CAP = int(os.environ.get("CAP", "8"))
CONNS = int(os.environ.get("CONNS", "40"))
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")


def probe(io, shards, port, cap):
    env = dict(os.environ)
    if cap is not None:
        env["DRORB_MAX_CONNS"] = str(cap)
    else:
        env.pop("DRORB_MAX_CONNS", None)
    argv = [BIN, "--bind", "127.0.0.1:%d" % port, "--no-udp", "--io", io]
    if shards:
        env["DRORB_SHARDS"] = str(shards)
    logpath = "/tmp/process-cap-probe-%d.log" % port
    log = open(logpath, "w")
    proc = subprocess.Popen(argv, env=env, stdout=log, stderr=subprocess.STDOUT,
                            stdin=subprocess.DEVNULL)
    try:
        for _ in range(300):
            try:
                socket.create_connection(("127.0.0.1", port), 0.2).close()
                break
            except OSError:
                time.sleep(0.05)
        else:
            print("  serve never bound on :%d" % port)
            return None
        # That readiness probe closed, so the process is back to 0 held.
        time.sleep(0.3)
        # Open every connection FIRST so they are genuinely concurrent.
        socks = []
        for _ in range(CONNS):
            try:
                s = socket.create_connection(("127.0.0.1", port), 2.0)
                s.settimeout(2.0)
                socks.append(s)
            except OSError:
                socks.append(None)
        # ADMITTED = the reactor took the connection into its slab and answered on
        # it (a 200, or the fold-level per-source 503 — either way the process
        # accepted and holds it). DROPPED = the process ceiling disposed of it at
        # accept: the ceiling writes NOTHING, so the read returns EOF.
        admitted = 0
        dropped = 0
        for s in socks:
            if s is None:
                dropped += 1
                continue
            try:
                s.sendall(b"GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n")
                data = s.recv(4096)
                if data.startswith(b"HTTP/1.1"):
                    admitted += 1
                else:
                    dropped += 1
            except OSError:
                dropped += 1
        served, refused = admitted, dropped
        for s in socks:
            if s:
                s.close()
        line = [l for l in open(logpath) if "connection ceiling" in l]
        return served, refused, (line[0].strip() if line else "<no ceiling line>")
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        log.close()


print("%d concurrent connections from one source, no max-connections directive."
      % CONNS)
print("ADMITTED = answered on the wire (the process holds it); "
      "DROPPED = closed at accept with no bytes (the ceiling).")
print()
print("DRORB_MAX_CONNS=%d:" % CAP)
for i, (io, shards) in enumerate(
    [("auto", None), ("auto", 1), ("auto", 24), ("blocking", None)]
):
    r = probe(io, shards, PORT + i, CAP)
    if r is None:
        continue
    admitted, dropped, line = r
    print("  io=%-8s shards=%-7s -> ADMITTED %d, DROPPED %d"
          % (io, shards if shards else "default", admitted, dropped))
    if i == 0:
        print("     startup: %s" % line)
print()
print("CONTROL, ceiling at its default (32768) - nothing should be dropped:")
r = probe("auto", None, PORT + 8, None)
if r:
    admitted, dropped, line = r
    print("  io=auto     shards=default -> ADMITTED %d, DROPPED %d"
          % (admitted, dropped))
    print("     startup: %s" % line)
