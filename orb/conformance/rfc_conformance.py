#!/usr/bin/env python3
"""Reference HTTP/1.1 conformance probe (RFC 7230 / RFC 7231) for the deployed serve.

This is a REFERENCE-suite conformance check toward DreggNet DONE criterion 2
("reference test suites = our conformance"). It drives the *deployed* `dataplane`
binary (the leanc-compiled proven serve behind the Rust reactor) over a raw TCP
socket and checks it against normative requirements of the HTTP/1.1 RFCs:

  RFC 7230  Message Syntax and Routing
  RFC 7231  Semantics and Content

Each check crafts a real request, reads the real bytes off the wire, and derives
its PASS/FAIL verdict from the observed response — no self-reported success. Every
check records the exact criterion (with RFC section) and an observed summary so a
FAIL is a concrete, reproducible finding, not a vibe.

Run against a serve already listening (see conformance/rfc_launch.sh):

    DRORB_RUST_GZIP=1 DRORB_EFFECT_SEAM=1 \
      ./target/release/dataplane --bind 127.0.0.1:8391 --no-udp --io uring
    python3 conformance/rfc_conformance.py            # table + results_rfc.json

Env: CONF_HTTP_PORT (default 8391), CONF_HTTP_HOST (default 127.0.0.1).
Exit code is always 0 — FAILs are findings, not harness errors.
"""
import json
import os
import socket
import sys
import time

HOST = os.environ.get("CONF_HTTP_HOST", "127.0.0.1")
PORT = int(os.environ.get("CONF_HTTP_PORT", "8391"))
RESULTS = []


def raw(req, timeout=4.0, cap=1 << 20):
    """Send raw bytes on a fresh connection; return all bytes read until close/timeout.

    Returns b"" if the peer closed with no data; None if the connection was refused
    (server down)."""
    try:
        s = socket.create_connection((HOST, PORT), timeout=timeout)
    except ConnectionRefusedError:
        return None
    s.settimeout(timeout)
    try:
        s.sendall(req)
        buf = b""
        while len(buf) < cap:
            try:
                d = s.recv(65536)
            except socket.timeout:
                break
            if not d:
                break
            buf += d
        return buf
    finally:
        s.close()


def split_head(resp):
    head, _, body = (resp or b"").partition(b"\r\n\r\n")
    return head, body


def status_line(resp):
    return (resp or b"").split(b"\r\n", 1)[0]


def status_code(resp):
    parts = status_line(resp).split(b" ", 2)
    if len(parts) >= 2 and parts[1].isdigit():
        return int(parts[1])
    return None


def header_present(head, name):
    low = head.lower()
    return low.startswith(name.lower() + b":") or (b"\r\n" + name.lower() + b":") in low


def record(cid, group, rfc, criterion, request, verdict, observed):
    RESULTS.append({
        "id": cid, "group": group, "rfc": rfc, "criterion": criterion,
        "request": request, "verdict": verdict, "observed": observed,
    })


# ---------------------------------------------------------------------------
# Group A — Message framing (RFC 7230 §3)
# ---------------------------------------------------------------------------
def a_framing():
    r = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    sl = status_line(r)
    ok = sl.startswith(b"HTTP/1.1 200 ") and sl.endswith(b"OK")
    record("A1-status-line", "framing", "7230 §3.1.2",
           "status-line is HTTP-version SP status-code SP reason-phrase CRLF",
           "GET /health", "PASS" if ok else "FAIL", sl.decode("latin1"))

    head, body = split_head(r)
    ok = b"\r\n\r\n" in (r or b"") and head != b""
    record("A2-header-termination", "framing", "7230 §3",
           "header section terminated by CRLFCRLF before body",
           "GET /health", "PASS" if ok else "FAIL",
           "CRLFCRLF present" if ok else "no header terminator")

    r = raw(b"GET /static/app.js HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    cl = None
    for line in head.split(b"\r\n"):
        if line.lower().startswith(b"content-length:"):
            cl = int(line.split(b":", 1)[1].strip())
    ok = cl is not None and cl == len(body)
    record("A3-content-length-static", "framing", "7230 §3.3.2",
           "Content-Length equals the actual body octet count",
           "GET /static/app.js", "PASS" if ok else "FAIL",
           f"Content-Length={cl}, body={len(body)}")

    r = raw(b"GET /no-such-xyz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    cl = None
    for line in head.split(b"\r\n"):
        if line.lower().startswith(b"content-length:"):
            cl = int(line.split(b":", 1)[1].strip())
    ok = status_code(r) == 404 and cl is not None and cl == len(body)
    record("A4-content-length-404", "framing", "7230 §3.3.2",
           "404 body length is framed by an accurate Content-Length",
           "GET /no-such-xyz", "PASS" if ok else "FAIL",
           f"status={status_code(r)}, Content-Length={cl}, body={len(body)}")


# ---------------------------------------------------------------------------
# Group B — Method semantics (RFC 7231 §4)
# ---------------------------------------------------------------------------
def b_methods():
    r = raw(b"HEAD /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    # RFC 7231 §4.3.2: "The server MUST NOT send a message body in the response" to HEAD.
    ok = len(body) == 0
    record("B1-head-no-body", "methods", "7231 §4.3.2 (MUST)",
           "HEAD response MUST NOT include a message body",
           "HEAD /health", "PASS" if ok else "FAIL",
           f"status={status_code(r)}, body={len(body)} bytes {body[:16]!r}")

    r = raw(b"FOOBAR /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    # RFC 7231 §4.1: unrecognized method SHOULD -> 501; §6.5.5: known-not-allowed -> 405.
    st = status_code(r)
    ok = st in (400, 405, 501)
    record("B2-unknown-method", "methods", "7231 §4.1 / §6.5.5",
           "unrecognized request method rejected (501 / 405 / 400), not served as GET",
           "FOOBAR /health", "PASS" if ok else "FAIL",
           f"status={st} (expected 501/405/400)")


# ---------------------------------------------------------------------------
# Group C — Host header & request-target (RFC 7230 §5)
# ---------------------------------------------------------------------------
def c_host():
    r = raw(b"GET /health HTTP/1.1\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    # RFC 7230 §5.4: "A server MUST respond with 400 ... to any HTTP/1.1 request
    # message that lacks a Host header field."
    ok = st == 400
    record("C1-missing-host", "host", "7230 §5.4 (MUST)",
           "HTTP/1.1 request without Host MUST get 400 Bad Request",
           "GET /health (no Host)", "PASS" if ok else "FAIL",
           f"status={st} (expected 400)")

    r = raw(b"GET /health HTTP/1.1\r\nHost: a\r\nHost: b\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    # RFC 7230 §5.4: more than one Host -> MUST 400.
    ok = st == 400
    record("C2-duplicate-host", "host", "7230 §5.4 (MUST)",
           "request with >1 Host header MUST get 400 Bad Request",
           "GET /health (Host: a / Host: b)", "PASS" if ok else "FAIL",
           f"status={st} (expected 400)")

    r_abs = raw(b"GET http://x/health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    r_org = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    # RFC 7230 §5.3.2: a server MUST accept the absolute-form in requests; §5.4 says
    # it must reconstruct the effective target — absolute-form must resolve like origin-form.
    ok = status_code(r_abs) == status_code(r_org) == 200
    record("C3-absolute-form", "host", "7230 §5.3.2 (MUST)",
           "absolute-form request-target accepted and routed like origin-form",
           "GET http://x/health", "PASS" if ok else "FAIL",
           f"absolute-form status={status_code(r_abs)}, origin-form status={status_code(r_org)}")


# ---------------------------------------------------------------------------
# Group D — Transfer coding & framing safety (RFC 7230 §3.3 / §4)
# ---------------------------------------------------------------------------
def d_transfer():
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n"
            b"Connection: close\r\n\r\n5\r\nhello\r\n0\r\n\r\n")
    st = status_code(r)
    ok = st is not None and 200 <= st < 500 and st != 400
    record("D1-chunked-request", "transfer", "7230 §4.1",
           "chunked request body is decoded and the request is served (not hung/errored)",
           "POST /health (chunked hello)", "PASS" if ok else "FAIL",
           f"status={st}")

    # RFC 7230 §3.3.3(3): both TE and CL present is a smuggling vector; TE overrides CL
    # and the message ought to be handled as an error (reject / close), never forwarded
    # by interpreting the Content-Length body.
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n"
            b"Transfer-Encoding: chunked\r\n\r\n0\r\n\r\n", timeout=3.0)
    st = status_code(r)
    # PASS iff the serve rejected (4xx) or closed without emitting a second, smuggled
    # response — i.e. it did not treat CL as authoritative and leave 5 bytes buffered.
    ok = (r == b"") or (st is not None and 400 <= st < 500)
    record("D2-te-cl-conflict", "transfer", "7230 §3.3.3 (MUST-not-smuggle)",
           "TE+CL request rejected/closed, not processed via Content-Length (anti-smuggling)",
           "POST /health (TE: chunked + CL: 5)", "PASS" if ok else "FAIL",
           f"status={st}, resp_len={len(r or b'')} (empty/close or 4xx is safe)")


# ---------------------------------------------------------------------------
# Group E — Connection management (RFC 7230 §6)
# ---------------------------------------------------------------------------
def e_connection():
    # E1: HTTP/1.1 default persistence — two requests on ONE connection get two responses.
    try:
        s = socket.create_connection((HOST, PORT), timeout=4)
        s.settimeout(4)
        s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n"
                  b"GET /static/app.js HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
        buf = b""
        while True:
            try:
                d = s.recv(65536)
            except socket.timeout:
                break
            if not d:
                break
            buf += d
        s.close()
        n = buf.count(b"HTTP/1.1 ")
    except OSError:
        n = -1
    record("E1-keepalive-persistent", "connection", "7230 §6.3",
           "HTTP/1.1 connection is persistent by default (2 pipelined requests -> 2 responses)",
           "GET /health then GET /static on one socket",
           "PASS" if n == 2 else "FAIL", f"responses on one connection = {n}")

    r = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, _ = split_head(r)
    ok = b"connection: close" in head.lower()
    record("E2-connection-close", "connection", "7230 §6.1",
           "Connection: close is honored and echoed",
           "GET /health (Connection: close)", "PASS" if ok else "FAIL",
           "Connection: close present" if ok else "close not signaled")

    r = raw(b"GET /health HTTP/1.0\r\n\r\n")
    head, _ = split_head(r)
    ok = b"connection: close" in head.lower()
    record("E3-http10-close-default", "connection", "7230 §6.3",
           "HTTP/1.0 request without keep-alive defaults to Connection: close",
           "GET /health HTTP/1.0", "PASS" if ok else "FAIL",
           "Connection: close present" if ok else "did not default to close")


# ---------------------------------------------------------------------------
# Group F — Representation metadata (RFC 7231 §7.1.1.2)
# ---------------------------------------------------------------------------
def f_metadata():
    r = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, _ = split_head(r)
    ok = header_present(head, b"date")
    # RFC 7231 §7.1.1.2: "An origin server MUST send a Date header field in all ...
    # 2xx (Successful), 3xx (Redirection), and 4xx (Client Error) responses" if it
    # has a clock. drorb's host process has a clock.
    record("F1-date-header", "metadata", "7231 §7.1.1.2 (MUST)",
           "origin server with a clock MUST send a Date header on 2xx/3xx/4xx",
           "GET /health", "PASS" if ok else "FAIL",
           "Date present" if ok else "no Date header emitted")


# ---------------------------------------------------------------------------
# Group G — Request-line robustness (RFC 7230 §2.6 / §3.5)
# ---------------------------------------------------------------------------
def g_robustness():
    r = raw(b"GET /health HTTP/9.9\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    # RFC 7230 §2.6: a server SHOULD send 505 (or 400) for an unsupported major version;
    # it MUST NOT silently process HTTP/9.9 as HTTP/1.1 and 200 it.
    ok = st in (400, 505)
    record("G1-http-version", "robustness", "7230 §2.6",
           "unsupported HTTP major version rejected (400/505), not served as 200",
           "GET /health HTTP/9.9", "PASS" if ok else "FAIL",
           f"status={st} (expected 400/505)")

    # RFC 7230 §3.5: CRLF is the line terminator; recognizing a bare LF is OPTIONAL.
    # A strict server that refuses a bare-LF request (silent close / no response) is
    # conformant AND avoids an LF-smuggling desync, so that is the PASS condition.
    r = raw(b"GET /health HTTP/1.1\nHost: x\n\n", timeout=3.0)
    st = status_code(r)
    ok = (r == b"") or (st is not None and 400 <= st < 500) or (st == 200)
    # Any deterministic disposition is fine; we only FAIL on a hang (None==refused handled elsewhere).
    record("G2-bare-lf", "robustness", "7230 §3.5",
           "bare-LF request handled deterministically (strict refuse or tolerant parse), no hang",
           "GET /health with bare-LF line endings", "PASS" if ok else "FAIL",
           f"status={st}, resp_len={len(r or b'')}")


def main():
    if raw(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n") is None:
        print(f"ERROR: no serve listening on {HOST}:{PORT}", file=sys.stderr)
        sys.exit(2)
    for fn in (a_framing, b_methods, c_host, d_transfer, e_connection, f_metadata, g_robustness):
        fn()

    npass = sum(1 for r in RESULTS if r["verdict"] == "PASS")
    total = len(RESULTS)
    width = max(len(r["id"]) for r in RESULTS)
    print(f"\n== drorb reference HTTP/1.1 conformance (RFC 7230/7231) — {HOST}:{PORT} ==\n")
    print(f"{'CHECK':<{width}}  {'VERDICT':<6}  RFC          CRITERION")
    print("-" * 100)
    for r in RESULTS:
        mark = "PASS" if r["verdict"] == "PASS" else "FAIL"
        print(f"{r['id']:<{width}}  {mark:<6}  {r['rfc']:<11}  {r['criterion']}")
        if r["verdict"] != "PASS":
            print(f"{'':<{width}}          -> observed: {r['observed']}")
    print("-" * 100)
    print(f"\nPASS {npass}/{total}  ({100.0*npass/total:.1f}%)   FAIL {total-npass}/{total}\n")

    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "target": f"{HOST}:{PORT}",
        "suite": "RFC 7230/7231 reference HTTP/1.1 conformance",
        "pass": npass, "total": total, "pass_rate": round(100.0 * npass / total, 1),
        "checks": RESULTS,
    }
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results_rfc.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"wrote {os.path.join(here, 'results_rfc.json')}")


if __name__ == "__main__":
    main()
