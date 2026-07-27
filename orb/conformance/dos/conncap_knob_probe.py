#!/usr/bin/env python3
"""Does the operator's `max-connections` REACH the proven serve fold?

`dos/fold_conncap_probe.py` measures the threshold a DEFAULT deployment refuses at.
This probe measures the KNOB: it walks the same concurrency under three configs and
prints where each one starts answering 503, so "the config moved the gate" is a
measured claim rather than a reading of the Lean.

It also isolates WHICH gate answered, which the raw threshold cannot: the presence
of a `DRORB_CONFIG` file switches the serve seam (a non-empty config leaves the
dense metered default for the cfg route table), and on that seam the fold's DoS
gates get no accept-path readings at all — so a 503 there is the Rust ACCEPT-PATH
gate, not the fold. Arm B below is the control that shows this: a config that says
NOTHING about connections still changes the observed threshold, which is only
possible if the seam, not the number, moved.

    python3 dos/conncap_knob_probe.py [base-port]

To drive the FOLD's cap directly (the arm no wire test on the cfg seam can reach),
run the shipped export body with explicit (active, cap) readings:

    lake env lean <<'EOF'
    import Dataplane
    #eval (drorbServePipelineConformant "".toUTF8 0 5 0 4  req).toList.take 12   -- 503
    #eval (drorbServePipelineConformant "".toUTF8 0 5 0 16 req).toList.take 12   -- 200
    EOF
"""
import os
import socket
import subprocess
import sys
import tempfile
import time

BASE = int(sys.argv[1]) if len(sys.argv) > 1 else 19800
BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane")
STEPS = (2, 4, 5, 6, 8, 12)


def walk(io, port, cfg_text, label):
    env = dict(os.environ)
    env.pop("DRORB_CONFIG", None)
    if cfg_text is not None:
        f = tempfile.NamedTemporaryFile("w", suffix=".conf", delete=False)
        f.write(cfg_text)
        f.close()
        env["DRORB_CONFIG"] = f.name
    log = open("/tmp/conncap-knob-%d.log" % port, "w")
    proc = subprocess.Popen(
        [BIN, "--bind", "127.0.0.1:%d" % port, "--no-udp", "--io", io],
        stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env)
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
        for n in STEPS:
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
            print("  %-34s io=%-8s concurrent=%-3d -> %s" % (label, io, n, " ".join(codes)))
            for s in socks:
                s.close()
            time.sleep(0.4)
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        log.close()


ARMS = [
    # (label, config text or None for "no DRORB_CONFIG at all")
    ("A: no config (dense fold seam)", None),
    ("B: config, NO conn directive", "rate-limit 2000\n"),
    ("C: max-connections 3", "max-connections 3\n"),
    ("D: max-connections 6", "max-connections 6\n"),
]

print("Where does one source start getting 503, per config?")
print("A browser opens ~6 parallel connections per origin.\n")
port = BASE
for label, cfg in ARMS:
    for io in ("auto", "blocking"):
        walk(io, port, cfg, label)
        port += 1
    print()
