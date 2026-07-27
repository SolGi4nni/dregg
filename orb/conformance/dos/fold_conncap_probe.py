#!/usr/bin/env python3
"""At how many CONCURRENT connections from one source does a DEFAULT deployment
start answering 503?

Not a gate test — a MEASUREMENT of a live threshold nobody configured. This walks
the concurrency up and prints the status every connection got, so the threshold is
a measured number rather than a reading of the Lean.

HISTORY: this probe exists because the two per-source connection gates DISAGREED.
The accept-path gate honoured the config (`max-connections`, default 512); the
proven serve FOLD carried a second one whose cap was a FIXED Lean constant,
`Reactor.Stage.ConnLimit.connCap := 4`, fed the source's standing count from the
same table — so a default deployment 503'd any source at FIVE concurrent
connections, below what a browser opens. Fixed 2026-07-25 (in Lean: the cap is now
threaded from `max-connections`, defaulting to 512 — see
`FINDING-dos-class-sweep-2.md` (R1)). EXPECTED OUTPUT NOW: all `200` through
concurrent=8 on both backends. Any 503 here is that regression returning.

To measure whether the KNOB reaches the fold (as opposed to the threshold), use
`conncap_knob_probe.py` — it also isolates seam-switching from cap-changing.

    python3 dos/fold_conncap_probe.py 19170

No directives are set: whatever this prints is what an operator who configured
nothing gets.
"""
import os
import socket
import subprocess
import sys
import time

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 19170
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")


def walk(io, port):
    log = open("/tmp/fold-conncap-%d.log" % port, "w")
    proc = subprocess.Popen(
        [BIN, "--bind", "127.0.0.1:%d" % port, "--no-udp", "--io", io],
        stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    try:
        for _ in range(300):
            try:
                socket.create_connection(("127.0.0.1", port), 0.2).close()
                break
            except OSError:
                time.sleep(0.05)
        else:
            print("  serve never bound on :%d" % port)
            return
        for n in (1, 2, 3, 4, 5, 6, 8):
            socks = [socket.create_connection(("127.0.0.1", port), 2.0) for _ in range(n)]
            for s in socks:
                s.settimeout(2.0)
            codes = []
            for s in socks:
                s.sendall(b"GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n")
                try:
                    codes.append(s.recv(20).split()[1].decode())
                except (OSError, IndexError):
                    codes.append("EOF")
            print("  io=%-8s concurrent=%-2d -> %s" % (io, n, " ".join(codes)))
            for s in socks:
                s.close()
            time.sleep(0.5)
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        log.close()


print("DEFAULT config (no directives at all; the accept-path cap defaults to 512).")
print("A browser opens ~6 parallel connections per origin.")
for i, io in enumerate(("auto", "blocking")):
    walk(io, PORT + i)
