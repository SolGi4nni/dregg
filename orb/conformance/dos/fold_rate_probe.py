#!/usr/bin/env python3
"""Does the PROVEN fold's per-source RATE gate bind — and can it be told apart from
the unproven Rust accept-path gate?

THE DISCRIMINATOR IS ON THE WIRE. The two gates answer `429` with DIFFERENT bodies:

  proven fold, PER-SOURCE stick gate                  "aggregated request limit exceeded"
    (Reactor.Stage.StickTable.resp429)                 -> reported as 429/FOLD

  everything else that answers 429                     "rate limit exceeded"
    - the Rust accept-path blob (uring.rs RATE_LIMIT_429), and
    - the proven PER-CONNECTION token bucket
      (Reactor.Stage.Rate.resp429, `burst-cap` requests/conn, default 512)
                                                          -> reported as 429/other

so every arm reports WHICH gate answered, not merely that something did. The two
"other" sources share a body, which is why the arms below are sized to separate them:
the per-connection bucket cannot fire before request `burst-cap`+1 (512+1 by default,
and these arms are 8 requests long), and it cannot fire at all on a fresh connection
(seq 0). See conformance/dos/burst_cap_probe.py for the per-CONNECTION bound itself --
three different bounds, three different quantities.

THE SCENARIO WHERE THEY GENUINELY DISAGREE. The accept-path gate runs once per
`accept()`: it counts CONNECTION arrivals. On a kept-alive connection, requests
2..N never reach it at all — a single connection can issue ten thousand requests
and its window count stays 1. So the per-source REQUEST-rate bound the `rate-limit`
directive names ("at most n request arrivals from one source within each
rate-window") was, before this wave, not enforced on any request after the first of
each connection.

The fold gate is fed a REQUEST-arrival count, so it sees exactly what the accept
gate structurally cannot. That is not a contrived contrast: it is one keep-alive
connection, which is what every browser and every HTTP client library does.

  ARM 1  KEEPALIVE-BURST   one connection, 8 requests, rate-limit 3.
                           Accept gate: 1 connection arrival -> CANNOT fire.
                           Per-conn bucket: `burst-cap` 512 -> CANNOT fire in 8.
                           Fold stick gate: 429/FOLD from request 4 on.
  ARM 2  CONTROL-OFF       identical traffic, rate-limit 0 (disabled).
                           Nothing may fire: all 200. Separates "the per-source gate
                           bound" from "something else refuses the 4th request".
  ARM 3  FRESH-CONNS       8 separate connections, one request each, rate-limit 3.
                           The accept gate refuses the over-limit ARRIVAL before
                           dispatch, so this arm is answered by the RUST gate (the
                           per-connection bucket sees seq 0 on every one of them) --
                           the proof that the two are distinguishable and that arm 1
                           really was the fold.

    python3 conformance/dos/fold_rate_probe.py [base-port] [io]
"""
import os
import socket
import subprocess
import sys
import tempfile
import time

BASE = int(sys.argv[1]) if len(sys.argv) > 1 else 19940
IO = sys.argv[2] if len(sys.argv) > 2 else ("uring" if sys.platform.startswith("linux") else "kqueue")
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")
NREQ = 8
LIMIT = 3

REQ = b"GET /health HTTP/1.1\r\nHost: localhost\r\nConnection: keep-alive\r\n\r\n"

FOLD_MARK = b"aggregated request limit exceeded"
RUST_MARK = b"rate limit exceeded"


def read_response(sock):
    """Read one whole HTTP/1.1 response; return (status, which-gate)."""
    buf = b""
    while b"\r\n\r\n" not in buf:
        try:
            chunk = sock.recv(4096)
        except OSError:
            return ("TIMEOUT", "")
        if not chunk:
            return ("EOF", "")
        buf += chunk
    head, rest = buf.split(b"\r\n\r\n", 1)
    try:
        status = head.split(b"\r\n", 1)[0].split()[1].decode()
    except IndexError:
        return ("BAD", "")
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
    gate = ""
    if status == "429":
        if FOLD_MARK in rest:
            gate = "FOLD"
        elif RUST_MARK in rest:
            gate = "other"
        else:
            gate = "?"
    return (status, gate)


def boot(port, limit):
    cfg = tempfile.NamedTemporaryFile("w", suffix=".conf", delete=False)
    cfg.write("bind 127.0.0.1\nrate-limit %d\nrate-window 60000\n" % limit)
    cfg.close()
    env = dict(os.environ)
    env["DRORB_CONFIG"] = cfg.name
    log = open("/tmp/fold-rate-%d.log" % port, "w")
    proc = subprocess.Popen(
        [BIN, "--bind", "127.0.0.1:%d" % port, "--no-udp", "--io", IO],
        stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env)
    for _ in range(400):
        try:
            socket.create_connection(("127.0.0.1", port), 0.2).close()
            break
        except OSError:
            time.sleep(0.05)
    else:
        proc.terminate()
        return None, None, cfg.name, log
    return proc, port, cfg.name, log


def stop(proc, cfgname, log):
    if proc:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
    try:
        os.unlink(cfgname)
    except OSError:
        pass
    log.close()


def fmt(results):
    return " ".join(s if not g else "%s/%s" % (s, g) for s, g in results)


def arm_keepalive(label, port, limit):
    proc, port, cfgname, log = boot(port, limit)
    if proc is None:
        print("  %-16s serve never bound on :%d" % (label, port))
        return
    try:
        # The probe's own boot poll opened (and closed) one connection; that is a
        # CONNECTION arrival, not a request, so it cannot perturb the request window.
        s = socket.create_connection(("127.0.0.1", port), 3.0)
        s.settimeout(3.0)
        out = []
        for _ in range(NREQ):
            try:
                s.sendall(REQ)
                out.append(read_response(s))
            except OSError:
                out.append(("EOF", ""))
                break
        s.close()
        print("  %-16s rate-limit=%d  1 keep-alive conn, %d requests  io=%s"
              % (label, limit, NREQ, IO))
        print("                   %s" % fmt(out))
    finally:
        stop(proc, cfgname, log)


def arm_fresh(label, port, limit):
    proc, port, cfgname, log = boot(port, limit)
    if proc is None:
        print("  %-16s serve never bound on :%d" % (label, port))
        return
    try:
        out = []
        for _ in range(NREQ):
            try:
                s = socket.create_connection(("127.0.0.1", port), 3.0)
                s.settimeout(3.0)
                s.sendall(REQ)
                out.append(read_response(s))
                s.close()
            except OSError:
                out.append(("EOF", ""))
        print("  %-16s rate-limit=%d  %d fresh connections, 1 request each  io=%s"
              % (label, limit, NREQ, IO))
        print("                   %s" % fmt(out))
    finally:
        stop(proc, cfgname, log)


if __name__ == "__main__":
    print("fold rate probe  bin=%s" % BIN)
    print("  429/FOLD  = 'aggregated request limit exceeded' -> the PROVEN per-source stick gate")
    print("  429/other = 'rate limit exceeded' -> the Rust accept blob OR the per-connection bucket")
    arm_keepalive("KEEPALIVE-BURST", BASE, LIMIT)
    arm_keepalive("CONTROL-OFF", BASE + 1, 0)
    arm_fresh("FRESH-CONNS", BASE + 2, LIMIT)
