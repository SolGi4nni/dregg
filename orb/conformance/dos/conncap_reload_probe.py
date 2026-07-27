#!/usr/bin/env python3
"""Does the PROVEN fold's per-source connection gate bind on the seam operators run?

The accept-path (Rust) connection gate refuses an over-cap arrival BEFORE the request
is ever dispatched, so on a steady deployment the fold's gate can never be the one that
answers — both gates read the same `max-connections` and the accept path wins the race
by construction. That makes "the fold gate binds" untestable on a steady wire.

There is exactly one operator-real situation where the two gates DISAGREE, and it is the
one this probe drives: a RELOAD that TIGHTENS the cap under connections that are already
open. The accept-path gate ran once, at accept, under the OLD cap; it does not re-gate a
live connection. The fold gate decides per REQUEST, on the standing count the host
threads. So after `max-connections` is lowered and SIGHUP'd:

  * if the fold gate is LIVE on this seam, the next request on each already-open
    connection is answered the proven `503`;
  * if the fold gate is a PASS-THROUGH on this seam, every one of them is answered `200`
    and the operator's new cap is not enforced on the connections that are already there.

That is the exact discriminator for `drorb_serve_metered_cfg_conformant` — the seam taken
whenever a NON-EMPTY `DRORB_CONFIG` is in force, i.e. by every realistic deployment.

    python3 conformance/dos/conncap_reload_probe.py [base-port] [io]

Arms:
  TIGHTEN  max-connections 8 -> 4 under 6 open connections. The fold gate must answer 503.
  CONTROL  max-connections 8 -> 8 (same reload, same SIGHUP) under 6 open connections.
           Nothing may change: all 200. This is what separates "the cap moved" from
           "the reload disturbed the connections".
"""
import os
import signal
import socket
import subprocess
import sys
import tempfile
import time

BASE = int(sys.argv[1]) if len(sys.argv) > 1 else 19900
IO = sys.argv[2] if len(sys.argv) > 2 else ("uring" if sys.platform.startswith("linux") else "kqueue")
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")
NCONN = 6

REQ = b"GET /health HTTP/1.1\r\nHost: localhost\r\nConnection: keep-alive\r\n\r\n"


def read_response(sock):
    """Read one whole HTTP/1.1 response; return (status, body_len) or ('EOF', 0)."""
    buf = b""
    while b"\r\n\r\n" not in buf:
        try:
            chunk = sock.recv(4096)
        except OSError:
            return ("TIMEOUT", 0)
        if not chunk:
            return ("EOF", 0)
        buf += chunk
    head, rest = buf.split(b"\r\n\r\n", 1)
    try:
        status = head.split(b"\r\n", 1)[0].split()[1].decode()
    except IndexError:
        return ("BAD", 0)
    clen = 0
    for line in head.split(b"\r\n")[1:]:
        if line.lower().startswith(b"content-length:"):
            try:
                clen = int(line.split(b":", 1)[1].strip())
            except ValueError:
                clen = 0
    while len(rest) < clen:
        try:
            chunk = sock.recv(4096)
        except OSError:
            break
        if not chunk:
            break
        rest += chunk
    return (status, len(rest))


def arm(label, cap_before, cap_after, port):
    cfg = tempfile.NamedTemporaryFile("w", suffix=".conf", delete=False)
    cfg.write("bind 127.0.0.1\nmax-connections %d\n" % cap_before)
    cfg.close()
    env = dict(os.environ)
    env["DRORB_CONFIG"] = cfg.name
    log = open("/tmp/conncap-reload-%d.log" % port, "w")
    proc = subprocess.Popen(
        [BIN, "--bind", "127.0.0.1:%d" % port, "--no-udp", "--io", IO],
        stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env)
    try:
        for _ in range(400):
            try:
                socket.create_connection(("127.0.0.1", port), 0.2).close()
                break
            except OSError:
                time.sleep(0.05)
        else:
            print("  %-8s serve never bound on :%d" % (label, port))
            return
        # Open NCONN concurrent connections and prove each serves under the OLD cap.
        socks = [socket.create_connection(("127.0.0.1", port), 3.0) for _ in range(NCONN)]
        for s in socks:
            s.settimeout(3.0)
        before = []
        for s in socks:
            s.sendall(REQ)
            before.append(read_response(s)[0])
        # TIGHTEN the cap under the still-open connections, then SIGHUP.
        with open(cfg.name, "w") as f:
            f.write("bind 127.0.0.1\nmax-connections %d\n" % cap_after)
        proc.send_signal(signal.SIGHUP)
        time.sleep(0.6)
        after = []
        for s in socks:
            try:
                s.sendall(REQ)
                after.append(read_response(s)[0])
            except OSError:
                after.append("EOF")
        print("  %-8s cap %d->%d  io=%-6s open=%d" % (label, cap_before, cap_after, IO, NCONN))
        print("           before reload: %s" % " ".join(before))
        print("           after  reload: %s" % " ".join(after))
        for s in socks:
            s.close()
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        os.unlink(cfg.name)


if __name__ == "__main__":
    print("conncap reload probe  bin=%s" % BIN)
    arm("TIGHTEN", 8, 4, BASE)
    arm("CONTROL", 8, 8, BASE + 1)
