#!/usr/bin/env python3
"""THE PER-CONNECTION BURST CAP — is it reachable from operator config?

The third hardcoded admission constant. `Reactor/Stage/Rate.lean` carried

    def rateCap  : Nat := 8     -- burst capacity, requests per CONNECTION
    def rateRate : Nat := 1     -- refill, tokens per elapsed second

as Lean literals. No directive in the config grammar reached them, so a DEFAULT
drorb answered `429` to the NINTH request on a single keep-alive connection --
while one page load on one H2/keep-alive connection is dozens of requests.

THE THREE BOUNDS ARE DIFFERENT THINGS and this probe keeps them apart on the
wire, by the response BODY each gate emits:

  per-CONNECTION token bucket    Reactor.Stage.Rate.resp429      "rate limit exceeded"
      directives: burst-cap / burst-refill              -> reported 429/CONN
  per-SOURCE arrival limit       Reactor.Stage.StickTable.resp429
      directives: rate-limit / rate-window   "aggregated request limit exceeded"
                                                        -> reported 429/SRC
  per-SOURCE connection cap      Reactor.Stage.ConnLimit.resp503 (503, not 429)
      directive:  max-connections

ARMS
  1 DEFAULT        no DRORB_CONFIG at all. N requests on ONE keep-alive conn.
  2 KNOBS-MAXED    rate-limit and max-connections set enormous. If the burst cap
                   were reachable through EITHER of the per-source knobs, this
                   would move it. It must not: they bound a different quantity.
  3 BURST-LOW      burst-cap K, burst-refill 0. Must refuse at exactly K+1.
  4 BURST-OFF      burst-cap 0 -> the gate is disabled, as `max-connections 0`
                   and `rate-limit 0` already read.
  5 RECOVERY       burst-cap K, burst-refill R: exhaust, sleep, and the SAME
                   connection is served again -- a live bucket, not a latch.

    python3 burst_cap_probe.py [base-port] [nreq] [burst-cap] [burst-refill]
"""
import os
import socket
import subprocess
import sys
import tempfile
import time

BASE = int(sys.argv[1]) if len(sys.argv) > 1 else 19960
NREQ = int(sys.argv[2]) if len(sys.argv) > 2 else 50
KCAP = int(sys.argv[3]) if len(sys.argv) > 3 else 4
KRATE = int(sys.argv[4]) if len(sys.argv) > 4 else 2
IO = os.environ.get("DOS_IO", "uring" if sys.platform.startswith("linux") else "kqueue")
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")

REQ = b"GET /health HTTP/1.1\r\nHost: localhost\r\nConnection: keep-alive\r\n\r\n"
CONN_MARK = b"rate limit exceeded"
SRC_MARK = b"aggregated request limit exceeded"


def read_response(sock):
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
        if SRC_MARK in rest:
            gate = "SRC"
        elif CONN_MARK in rest:
            gate = "CONN"
        else:
            gate = "?"
    return (status, gate)


def boot(port, conf):
    env = dict(os.environ)
    name = None
    if conf is None:
        env.pop("DRORB_CONFIG", None)
    else:
        cfg = tempfile.NamedTemporaryFile("w", suffix=".conf", delete=False)
        cfg.write(conf)
        cfg.close()
        name = cfg.name
        env["DRORB_CONFIG"] = name
    log = open("/tmp/burst-cap-%d.log" % port, "w")
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
        return None, name, log
    return proc, name, log


def stop(proc, name, log):
    if proc:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
    if name:
        try:
            os.unlink(name)
        except OSError:
            pass
    log.close()


def burst(sock, n):
    out = []
    for _ in range(n):
        try:
            sock.sendall(REQ)
            out.append(read_response(sock))
        except OSError:
            out.append(("EOF", ""))
            break
    return out


def summarize(out):
    n200 = sum(1 for st, _ in out if st == "200")
    first = next((i + 1 for i, (st, g) in enumerate(out) if st == "429" and g == "CONN"), None)
    other = sorted({"%s%s" % (st, "/" + g if g else "") for st, g in out} - {"200"})
    return n200, first, other


def arm(label, port, conf, nreq=NREQ, pause_at=None, pause_s=0.0):
    proc, name, log = boot(port, conf)
    if proc is None:
        print("  %-12s serve never bound on :%d" % (label, port))
        return None
    try:
        s = socket.create_connection(("127.0.0.1", port), 3.0)
        s.settimeout(5.0)
        if pause_at is None:
            out = burst(s, nreq)
            tail = []
        else:
            out = burst(s, pause_at)
            time.sleep(pause_s)
            tail = burst(s, 2)
        s.close()
        n200, first, other = summarize(out)
        print("  %-12s %s" % (label, (conf or "<no DRORB_CONFIG>").replace("\n", " ; ").strip()))
        print("               %d requests on ONE keep-alive connection: %d x 200, other=%s"
              % (len(out), n200, ",".join(other) or "none"))
        print("               first per-CONNECTION 429 at request: %s"
              % (first if first else "NONE in %d" % len(out)))
        if tail:
            print("               after %.1fs on the SAME connection: %s"
                  % (pause_s, " ".join("%s%s" % (st, "/" + g if g else "") for st, g in tail)))
        return first
    finally:
        stop(proc, name, log)


if __name__ == "__main__":
    print("per-connection burst-cap probe   bin=%s  io=%s" % (BIN, IO))
    print("  429/CONN = 'rate limit exceeded'               -> PER-CONNECTION token bucket")
    print("  429/SRC  = 'aggregated request limit exceeded' -> PER-SOURCE arrival gate")
    a = arm("DEFAULT", BASE, None)
    b = arm("KNOBS-MAXED", BASE + 1,
            "bind 127.0.0.1\nrate-limit 1000000\nrate-window 60000\nmax-connections 1000000\n")
    c = arm("BURST-LOW", BASE + 2,
            "bind 127.0.0.1\nburst-cap %d\nburst-refill 0\n" % KCAP, nreq=KCAP + 4)
    d = arm("BURST-OFF", BASE + 3, "bind 127.0.0.1\nburst-cap 0\n")
    e = arm("RECOVERY", BASE + 4,
            "bind 127.0.0.1\nburst-cap %d\nburst-refill %d\n" % (KCAP, KRATE),
            pause_at=KCAP + 2, pause_s=1.4)
    print("  ---")
    print("  DEFAULT=%s  KNOBS-MAXED=%s  BURST-LOW(cap=%d)=%s  BURST-OFF=%s  RECOVERY=%s"
          % (a, b, KCAP, c, d, e))
