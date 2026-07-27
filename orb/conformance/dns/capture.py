#!/usr/bin/env python3
"""Capture real DNS wire messages by relaying dig through a local socket.

dig sends its real query bytes to 127.0.0.1:<port>; this relay forwards them
verbatim to a public resolver and hands the real response bytes back to dig.
Both directions are recorded verbatim as hex, alongside dig's own decoded view
of the answer (the comparison oracle for battery.py).

UDP cases record the datagrams; the `tcp` case runs dig +tcp through a TCP
relay and records the raw RFC 1035 §4.2.2 length-prefixed stream octets of
both directions (the manifest line carries a `tcp` marker).

Outputs, per case, under captures/:
  <case>.q.hex    the exact query octets dig sent
  <case>.r.hex    the exact response octets the resolver returned
  <case>.dig.txt  dig's decoded output for the same exchange
  manifest.txt    one line per case: <case> <q-hex> <r-hex> [tcp]
"""

import os
import shutil
import socket
import subprocess
import sys
import threading

UPSTREAM = ("1.1.1.1", 53)
HERE = os.path.dirname(os.path.abspath(__file__))
CAPDIR = os.path.join(HERE, "captures")

# A dig new enough for +cookie and typed HTTPS output, when available;
# the system dig otherwise (those cases are skipped then).
DIG = shutil.which("dig") or "dig"
for cand in ("/opt/homebrew/opt/bind/bin/dig", "/usr/local/opt/bind/bin/dig"):
    if os.path.exists(cand):
        NEW_DIG = cand
        break
else:
    NEW_DIG = None


def dig_supports_cookie(dig):
    try:
        out = subprocess.run([dig, "-h"], capture_output=True, text=True, timeout=10)
        return "+cookie" in out.stdout or "+[no]cookie" in out.stdout
    except OSError:
        return False


# (case-name, dig arguments, mode). Coverage: RFC 1035 core types, compression
# (every real resolver response compresses names), EDNS(0) OPT (dig sends it
# by default), RFC 4034 DNSSEC records, RFC 5155 NSEC3/NSEC3PARAM, RFC 9460
# HTTPS/SVCB (typed SvcParams), an untyped-here RR (CAA), NXDOMAIN with an
# NSEC3 authority section, a no-EDNS query, a mixed-case QNAME (RFC 1035
# §2.3.3), an RFC 7873 cookie option, and RFC 1035 §4.2.2 TCP framing.
CASES = [
    ("a-multi",    ["example.com", "A"], "udp"),
    ("aaaa",       ["example.com", "AAAA"], "udp"),
    ("cname",      ["www.github.com", "A"], "udp"),
    ("mx",         ["gmail.com", "MX"], "udp"),
    ("txt",        ["example.com", "TXT"], "udp"),
    ("ns",         ["example.com", "NS"], "udp"),
    ("soa",        ["example.com", "SOA"], "udp"),
    ("ptr",        ["-x", "1.1.1.1"], "udp"),
    ("dnskey",     ["example.com", "DNSKEY", "+dnssec"], "udp"),
    ("a-dnssec",   ["example.com", "A", "+dnssec"], "udp"),
    ("ds",         ["example.com", "DS", "+dnssec"], "udp"),
    ("nxdomain",   ["no-such-name-4711.org", "A", "+dnssec"], "udp"),
    ("https-svcb", ["cloudflare.com", "TYPE65"], "udp"),
    ("caa-other",  ["google.com", "TYPE257"], "udp"),
    ("noedns",     ["example.com", "A", "+noedns"], "udp"),
    ("nsec3param", ["org", "NSEC3PARAM"], "udp"),
    ("mixedcase",  ["ExAmPlE.CoM", "A"], "udp"),
    ("tcp",        ["example.com", "A", "+tcp"], "tcp"),
    ("cookie",     ["example.com", "A", "+cookie"], "newdig"),
    ("https-typed", ["cloudflare.com", "HTTPS"], "newdig"),
]


def run_dig(dig, digargs, port, extra):
    return subprocess.run(
        [dig, "@127.0.0.1", "-p", str(port)] + digargs
        + ["+time=10", "+tries=1"] + extra,
        capture_output=True, text=True, timeout=30,
    )


def capture_udp(dig, digargs, port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("127.0.0.1", port))
    sock.settimeout(15)
    got = {}

    def relay():
        try:
            q, addr = sock.recvfrom(65535)
            up = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            up.settimeout(10)
            up.sendto(q, UPSTREAM)
            r, _ = up.recvfrom(65535)
            up.close()
            sock.sendto(r, addr)
            got["q"] = q
            got["r"] = r
        except OSError as e:
            got["err"] = str(e)

    t = threading.Thread(target=relay)
    t.start()
    out = run_dig(dig, digargs, port, ["+notcp"])
    t.join(20)
    sock.close()
    if "q" not in got or "r" not in got:
        return None, out.stdout + out.stderr, got.get("err", "no exchange seen")
    return (got["q"], got["r"]), out.stdout + out.stderr, None


def recv_framed(conn):
    """Read one RFC 1035 §4.2.2 length-prefixed message; return raw stream
    octets (prefix included)."""
    hdr = b""
    while len(hdr) < 2:
        chunk = conn.recv(2 - len(hdr))
        if not chunk:
            return None
        hdr += chunk
    need = (hdr[0] << 8) | hdr[1]
    body = b""
    while len(body) < need:
        chunk = conn.recv(need - len(body))
        if not chunk:
            return None
        body += chunk
    return hdr + body


def capture_tcp(dig, digargs, port):
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind(("127.0.0.1", port))
    srv.listen(1)
    srv.settimeout(15)
    got = {}

    def relay():
        try:
            conn, _ = srv.accept()
            conn.settimeout(10)
            q = recv_framed(conn)
            if q is None:
                got["err"] = "no framed query"
                return
            up = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            up.settimeout(10)
            up.connect(UPSTREAM)
            up.sendall(q)
            r = recv_framed(up)
            up.close()
            if r is None:
                got["err"] = "no framed response"
                return
            conn.sendall(r)
            conn.close()
            got["q"] = q
            got["r"] = r
        except OSError as e:
            got["err"] = str(e)

    t = threading.Thread(target=relay)
    t.start()
    out = run_dig(dig, digargs, port, [])
    t.join(20)
    srv.close()
    if "q" not in got or "r" not in got:
        return None, out.stdout + out.stderr, got.get("err", "no exchange seen")
    return (got["q"], got["r"]), out.stdout + out.stderr, None


def main():
    os.makedirs(CAPDIR, exist_ok=True)
    manifest = []
    port = 15353
    failures = 0
    cookie_dig = NEW_DIG if NEW_DIG and dig_supports_cookie(NEW_DIG) else (
        DIG if dig_supports_cookie(DIG) else None)
    for name, digargs, mode in CASES:
        port += 1
        if mode == "newdig":
            if cookie_dig is None:
                print(f"capture {name}: SKIPPED (no dig with +cookie/HTTPS support)",
                      file=sys.stderr)
                continue
            pair, digout, err = capture_udp(cookie_dig, digargs, port)
            marker = ""
        elif mode == "tcp":
            pair, digout, err = capture_tcp(DIG, digargs, port)
            marker = " tcp"
        else:
            pair, digout, err = capture_udp(DIG, digargs, port)
            marker = ""
        with open(os.path.join(CAPDIR, f"{name}.dig.txt"), "w") as f:
            f.write(digout)
        if pair is None:
            print(f"capture {name}: FAILED ({err})", file=sys.stderr)
            failures += 1
            continue
        q, r = pair
        with open(os.path.join(CAPDIR, f"{name}.q.hex"), "w") as f:
            f.write(q.hex())
        with open(os.path.join(CAPDIR, f"{name}.r.hex"), "w") as f:
            f.write(r.hex())
        manifest.append(f"{name} {q.hex()} {r.hex()}{marker}")
        print(f"capture {name}: {len(q)}q/{len(r)}r octets")
    with open(os.path.join(CAPDIR, "manifest.txt"), "w") as f:
        f.write("\n".join(manifest) + "\n")
    print(f"captured {len(manifest)}/{len(CASES)} cases")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
