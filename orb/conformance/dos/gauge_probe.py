#!/usr/bin/env python3
"""Does the admin surface report the connections the process is ACTUALLY holding?

The reproduction for `dos/FINDING-active-conns-zero.md`. On the shipped reactor
`/admin/connections` and `drorb_active_connections` read `crate::ACTIVE_CONNS`,
which only the BLOCKING host increments — so a shard reactor holding N connections
reported 0, forever, for every N.

This holds N real sockets open against a real serve and reads the admin surface
over a SEPARATE listener (so the reading connection is not itself counted), on the
shipped reactor and on the portable fallback.

    python3 gauge_probe.py 19110

Env:
  CONNS   sockets to hold open (default 25)
"""
import os
import socket
import subprocess
import sys
import time

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 19110
ADMIN = PORT + 1
CONNS = int(os.environ.get("CONNS", "25"))
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")


def http_get(port, path):
    s = socket.create_connection(("127.0.0.1", port), 3.0)
    s.settimeout(3.0)
    s.sendall(b"GET %s HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n" % path.encode())
    buf = b""
    while True:
        try:
            b = s.recv(65536)
        except OSError:
            break
        if not b:
            break
        buf += b
    s.close()
    return buf.decode("utf-8", "replace")


def run(io):
    log = open("/tmp/gauge-probe-%s-%d.log" % (io, PORT), "w")
    proc = subprocess.Popen(
        [BIN, "--bind", "127.0.0.1:%d" % PORT, "--no-udp", "--io", io],
        env=dict(os.environ, DRORB_ADMIN_LISTEN=str(ADMIN)),
        stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    try:
        for _ in range(300):
            try:
                socket.create_connection(("127.0.0.1", ADMIN), 0.2).close()
                break
            except OSError:
                time.sleep(0.05)
        else:
            print("  serve never bound (io=%s)" % io)
            return None

        before = http_get(ADMIN, "/admin/connections").rsplit("\r\n\r\n", 1)[-1].strip()
        socks = []
        for _ in range(CONNS):
            s = socket.create_connection(("127.0.0.1", PORT), 3.0)
            s.settimeout(3.0)
            # A real request, so the connection is genuinely serving, then held
            # open by keep-alive.
            s.sendall(b"GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n")
            socks.append(s)
        for s in socks:
            s.recv(4096)
        time.sleep(0.3)
        during = http_get(ADMIN, "/admin/connections").rsplit("\r\n\r\n", 1)[-1].strip()
        metrics = http_get(ADMIN, "/metrics")
        gauge = [l for l in metrics.splitlines() if l.startswith("drorb_active_connections ")]
        for s in socks:
            s.close()
        time.sleep(0.6)
        after = http_get(ADMIN, "/admin/connections").rsplit("\r\n\r\n", 1)[-1].strip()
        print("io=%-8s held=%d" % (io, CONNS))
        print("   before : %s" % before)
        print("   DURING : %s" % during)
        print("   gauge  : %s" % (gauge[0] if gauge else "<missing>"))
        print("   after  : %s" % after)
        return during
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        log.close()


for io in ("auto", "blocking"):
    run(io)
