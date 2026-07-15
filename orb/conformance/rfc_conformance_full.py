#!/usr/bin/env python3
"""Comprehensive HTTP/1.1 RFC conformance battery for the deployed serve.

This is a full-breadth MUST/SHOULD/capability probe of the running HTTP/1.1
origin server, covering the core semantics + syntax RFC family:

  RFC 7230 / 9112  Message Syntax and Routing (framing, targets, chunked, conn)
  RFC 7231 / 9110  Semantics: methods, status codes, negotiation, conditionals
  RFC 7232         Conditional Requests (If-Match / If-None-Match / If-*-Since)
  RFC 7233 / §14   Range Requests (byte-range, multipart, If-Range, 416)
  RFC 7234 / 9111  Caching (Cache-Control, Age, Vary, response cacheability)
  RFC 7235         Authentication framing (401 / WWW-Authenticate shape)
  RFC 3986         URI syntax (percent-encoding, path normalization)

It drives the server over raw TCP sockets and derives EVERY verdict from the
observed response bytes — never from a self-report. Each check records the exact
normative criterion (with RFC section and MUST / SHOULD / capability strength) so
a FAIL is a concrete, reproducible finding.

Strength taxonomy in the `rfc` column:
  (MUST)        a normative requirement — a FAIL is a true protocol violation.
  (SHOULD)      a recommendation — a FAIL is a conformance weakness worth noting.
  (capability)  an optional feature — a FAIL means the feature is absent (a gap
                on the coverage map), not a violation. Reported separately.

Run against a serve already listening on CONF_HTTP_PORT:

    python3 rfc_conformance_full.py

Env:
  CONF_HTTP_HOST     target host          (default 127.0.0.1)
  CONF_HTTP_PORT     target port          (default 8391)
  CONF_STATIC_PATH   a static asset path  (default /static/app.js)
  CONF_HEALTH_PATH   a 200 liveness path  (default /health)
  CONF_DESTRUCTIVE   run the resource-limit group that can crash the serve (0/1)

Exit code is always 0 — a FAIL is a finding, not a harness error. Every check
asserts the RFC-CORRECT behavior; the suite is NOT tuned to pass. A high FAIL
count on missing/partial features is the expected, valuable output: the gap map.
"""
import json
import os
import re
import socket
import sys
import time

HOST = os.environ.get("CONF_HTTP_HOST", "127.0.0.1")
PORT = int(os.environ.get("CONF_HTTP_PORT", "8391"))
STATIC = os.environ.get("CONF_STATIC_PATH", "/static/app.js")
HEALTH = os.environ.get("CONF_HEALTH_PATH", "/health")
DESTRUCTIVE = os.environ.get("CONF_DESTRUCTIVE", "0") == "1"
RESULTS = []


# --------------------------------------------------------------------------
# Wire helpers
# --------------------------------------------------------------------------
def raw(req, timeout=4.0, cap=1 << 20):
    """Send raw bytes on a fresh connection; return all bytes until close/timeout.

    b"" = peer closed with no data; None = connection refused (server down)."""
    if isinstance(req, str):
        req = req.encode("latin1")
    try:
        s = socket.create_connection((HOST, PORT), timeout=timeout)
    except (ConnectionRefusedError, OSError):
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
        try:
            s.close()
        except OSError:
            pass


def raw_delayed(head, body, gap=0.4, timeout=4.0, cap=1 << 20):
    """Send `head`, pause `gap` seconds, then `body` — for Expect/100-continue and
    interim-response timing. Returns bytes read across the whole exchange."""
    if isinstance(head, str):
        head = head.encode("latin1")
    if isinstance(body, str):
        body = body.encode("latin1")
    try:
        s = socket.create_connection((HOST, PORT), timeout=timeout)
    except (ConnectionRefusedError, OSError):
        return None, None
    s.settimeout(timeout)
    interim = b""
    try:
        s.sendall(head)
        time.sleep(gap)
        s.setblocking(False)
        try:
            interim = s.recv(65536)
        except (BlockingIOError, socket.error):
            interim = b""
        s.setblocking(True)
        s.settimeout(timeout)
        s.sendall(body)
        buf = interim
        while len(buf) < cap:
            try:
                d = s.recv(65536)
            except socket.timeout:
                break
            if not d:
                break
            buf += d
        return buf, interim
    finally:
        try:
            s.close()
        except OSError:
            pass


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


def reason_phrase(resp):
    parts = status_line(resp).split(b" ", 2)
    return parts[2].decode("latin1") if len(parts) >= 3 else ""


def header_value(head, name):
    if isinstance(name, str):
        name = name.encode("latin1")
    for line in head.split(b"\r\n"):
        if line.lower().startswith(name.lower() + b":"):
            return line.split(b":", 1)[1].strip()
    return None


def header_all(head, name):
    if isinstance(name, str):
        name = name.encode("latin1")
    out = []
    for line in head.split(b"\r\n"):
        if line.lower().startswith(name.lower() + b":"):
            out.append(line.split(b":", 1)[1].strip())
    return out


def header_present(head, name):
    return header_value(head, name) is not None


def all_status_codes(buf):
    return [int(m) for m in re.findall(rb"HTTP/1\.\d (\d{3}) ", buf or b"")]


def alive():
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH, timeout=3.0)
    return r is not None and status_code(r) == 200


def rec(cid, group, rfc, criterion, request, ok, observed):
    RESULTS.append({
        "id": cid, "group": group, "rfc": rfc, "criterion": criterion,
        "request": request, "verdict": "PASS" if ok else "FAIL", "observed": observed,
    })


def rec_v(cid, group, rfc, criterion, request, verdict, observed):
    RESULTS.append({
        "id": cid, "group": group, "rfc": rfc, "criterion": criterion,
        "request": request, "verdict": verdict, "observed": observed,
    })


def safe_or_4xx(r):
    """A framing-safety PASS: the server rejected (4xx) or closed with no smuggled
    second response. NOT a hang and NOT a 2xx that silently consumed the body."""
    if r is None:
        return False  # refused = server down; caller handles
    st = status_code(r)
    return (r == b"") or (st is not None and 400 <= st < 500)


# Discovered static-asset facts (filled by discover()).
ASSET = {"etag": None, "clen": None, "body_len": None, "accept_ranges": None,
         "last_modified": None, "ctype": None, "body": b""}


def discover():
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % STATIC)
    head, body = split_head(r)
    et = header_value(head, "etag")
    cl = header_value(head, "content-length")
    ar = header_value(head, "accept-ranges")
    lm = header_value(head, "last-modified")
    ct = header_value(head, "content-type")
    ASSET["etag"] = et.decode("latin1") if et else None
    ASSET["clen"] = int(cl) if (cl and cl.isdigit()) else None
    ASSET["accept_ranges"] = ar.decode("latin1") if ar else None
    ASSET["last_modified"] = lm.decode("latin1") if lm else None
    ASSET["ctype"] = ct.decode("latin1") if ct else None
    ASSET["body"] = body
    ASSET["body_len"] = len(body)


# ==========================================================================
# Group A — Message framing & start-line (RFC 9112 §2-4)
# ==========================================================================
def a_framing():
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    sl = status_line(r)
    rec("A01-status-line-shape", "framing", "9112 §4 (MUST)",
        "status-line = HTTP-version SP status-code SP [reason] CRLF",
        "GET %s" % HEALTH, bool(re.match(rb"HTTP/1\.1 \d{3} ", sl)),
        sl.decode("latin1"))

    rec("A02-version-token", "framing", "9112 §2.3 (MUST)",
        "server responds with HTTP/1.1 version token",
        "GET %s" % HEALTH, sl.startswith(b"HTTP/1.1 "),
        sl.decode("latin1"))

    st = status_code(r)
    rp = reason_phrase(r)
    rec("A03-status-200-reason", "framing", "9110 §15.3.1 (SHOULD)",
        "200 carries a sensible reason phrase (OK)",
        "GET %s" % HEALTH, st == 200 and "OK" in rp,
        "status=%s reason=%r" % (st, rp))

    head, body = split_head(r)
    rec("A04-header-terminator", "framing", "9112 §2.1 (MUST)",
        "header section terminated by an empty line (CRLFCRLF)",
        "GET %s" % HEALTH, b"\r\n\r\n" in (r or b"") and head != b"",
        "CRLFCRLF present" if b"\r\n\r\n" in (r or b"") else "no terminator")

    cl = header_value(head, "content-length")
    clv = int(cl) if (cl and cl.isdigit()) else None
    rec("A05-content-length-accurate", "framing", "9112 §6.2 (MUST)",
        "Content-Length equals the actual message-body octet count",
        "GET %s" % HEALTH, clv is not None and clv == len(body),
        "Content-Length=%s body=%d" % (cl, len(body)))

    r2 = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % STATIC)
    h2, b2 = split_head(r2)
    cl2 = header_value(h2, "content-length")
    clv2 = int(cl2) if (cl2 and cl2.isdigit()) else None
    rec("A06-content-length-static", "framing", "9112 §6.2 (MUST)",
        "static asset Content-Length equals served body octet count",
        "GET %s" % STATIC, clv2 is not None and clv2 == len(b2),
        "Content-Length=%s body=%d" % (cl2, len(b2)))

    r3 = raw("GET /definitely-no-such-path-xyz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    h3, b3 = split_head(r3)
    cl3 = header_value(h3, "content-length")
    clv3 = int(cl3) if (cl3 and cl3.isdigit()) else None
    rec("A07-404-framed", "framing", "9112 §6.2 (MUST)",
        "404 error body is framed by an accurate Content-Length",
        "GET /definitely-no-such-path-xyz",
        status_code(r3) == 404 and clv3 is not None and clv3 == len(b3),
        "status=%s Content-Length=%s body=%d" % (status_code(r3), cl3, len(b3)))

    rec("A08-single-status-line", "framing", "9112 §2.1 (MUST)",
        "exactly one start-line before the header section",
        "GET %s" % HEALTH, len(all_status_codes(head + b"\r\n\r\n")) == 1,
        "start-lines in head=%d" % len(all_status_codes(head + b"\r\n\r\n")))


# ==========================================================================
# Group B — Methods (RFC 9110 §9)
# ==========================================================================
def b_methods():
    # GET
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("B01-get", "methods", "9110 §9.3.1 (MUST)",
        "GET on a valid resource returns 2xx", "GET %s" % HEALTH,
        status_code(r) == 200, "status=%s" % status_code(r))

    # HEAD: no body
    rh = raw("HEAD %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    hh, hb = split_head(rh)
    rec("B02-head-no-body", "methods", "9110 §9.3.2 (MUST)",
        "HEAD response MUST NOT include a message body",
        "HEAD %s" % HEALTH, len(hb) == 0,
        "status=%s body=%d %r" % (status_code(rh), len(hb), hb[:16]))

    # HEAD: same Content-Length as GET would send
    rg = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % STATIC)
    gh, gb = split_head(rg)
    rh2 = raw("HEAD %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % STATIC)
    hh2, _ = split_head(rh2)
    g_cl = header_value(gh, "content-length")
    h_cl = header_value(hh2, "content-length")
    rec("B03-head-matches-get", "methods", "9110 §9.3.2 (SHOULD)",
        "HEAD Content-Length equals what GET would return",
        "HEAD %s vs GET" % STATIC, g_cl is not None and g_cl == h_cl,
        "GET CL=%s HEAD CL=%s" % (g_cl, h_cl))

    # POST
    rp = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("B04-post-answered", "methods", "9110 §9.3.3 (MUST)",
        "POST is answered with a final status (not ignored/hung)",
        "POST %s" % HEALTH, status_code(rp) is not None,
        "status=%s" % status_code(rp))

    # PUT
    rpu = raw("PUT %s HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("B05-put-answered", "methods", "9110 §9.3.4 / §15.5.6 (MUST)",
        "PUT is answered with a final status (2xx if supported, else 405/501)",
        "PUT %s" % HEALTH, status_code(rpu) is not None,
        "status=%s" % status_code(rpu))

    # DELETE
    rd = raw("DELETE %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("B06-delete-answered", "methods", "9110 §9.3.5 (MUST)",
        "DELETE is answered with a final status",
        "DELETE %s" % HEALTH, status_code(rd) is not None,
        "status=%s" % status_code(rd))

    # OPTIONS
    ro = raw("OPTIONS %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    oh, ob = split_head(ro)
    rec("B07-options-answered", "methods", "9110 §9.3.7 (MUST)",
        "OPTIONS answered with a final status (2xx) or 405/501",
        "OPTIONS %s" % HEALTH, status_code(ro) is not None,
        "status=%s" % status_code(ro))
    rec("B08-options-allow", "methods", "9110 §9.3.7 / §10.2.1 (SHOULD)",
        "a 2xx OPTIONS response advertises supported methods in Allow",
        "OPTIONS %s" % HEALTH,
        (status_code(ro) in (200, 204) and header_present(oh, "allow")) or
        status_code(ro) in (405, 501),
        "status=%s Allow=%r" % (status_code(ro), header_value(oh, "allow")))

    # OPTIONS *
    ros = raw("OPTIONS * HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    rec("B09-options-asterisk", "methods", "9112 §3.2.4 (SHOULD)",
        "asterisk-form OPTIONS * answered deterministically (2xx/4xx), no hang",
        "OPTIONS *", status_code(ros) is not None,
        "status=%s len=%d" % (status_code(ros), len(ros or b"")))

    # TRACE (commonly disabled -> 405/501; if enabled must echo request)
    rt = raw("TRACE %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(rt)
    rec("B10-trace-safe", "methods", "9110 §9.3.8 (MUST)",
        "TRACE either disabled (405/501) or a message/http echo — not a generic 200 page",
        "TRACE %s" % HEALTH,
        st in (405, 501) or (st == 200 and b"message/http" in (rt or b"").lower()),
        "status=%s (405/501 disabled, or 200+message/http echo)" % st)

    # CONNECT (must be rejected for an origin server that is not a tunnel)
    rc = raw("CONNECT example.com:443 HTTP/1.1\r\nHost: example.com:443\r\nConnection: close\r\n\r\n")
    st = status_code(rc)
    rec("B11-connect-rejected", "methods", "9110 §9.3.6 (MUST)",
        "CONNECT to a non-tunnel origin server is rejected (405/501/400), not 200",
        "CONNECT example.com:443",
        st in (400, 403, 405, 501) or (rc == b""),
        "status=%s len=%d" % (st, len(rc or b"")))

    # Unknown method
    ru = raw("FROBNICATE %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(ru)
    rec("B12-unknown-method-501", "methods", "9110 §9.1 / §15.6.6 (MUST)",
        "unrecognized method rejected (501 preferred, or 405/400) — never served as GET",
        "FROBNICATE %s" % HEALTH, st in (400, 405, 501),
        "status=%s (expected 501/405/400)" % st)

    # Case sensitivity: methods are case-sensitive tokens; "get" != "GET"
    rl = raw("get %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(rl)
    rec("B13-method-case-sensitive", "methods", "9110 §9.1 (MUST)",
        "method names are case-sensitive; lowercase 'get' is not GET (400/501, not 200)",
        "get %s" % HEALTH, st in (400, 405, 501) or (rl == b""),
        "status=%s len=%d (200 = case-folded, a violation)" % (st, len(rl or b"")))

    # 405 responses MUST carry Allow
    if status_code(ru) == 405 or status_code(rpu) == 405 or status_code(rd) == 405:
        for tag, rr in (("PUT", rpu), ("DELETE", rd), ("FROBNICATE", ru)):
            if status_code(rr) == 405:
                hh405, _ = split_head(rr)
                rec("B14-405-allow", "methods", "9110 §15.5.6 (MUST)",
                    "a 405 Method Not Allowed response MUST include an Allow header",
                    "%s %s -> 405" % (tag, HEALTH), header_present(hh405, "allow"),
                    "Allow=%r" % header_value(hh405, "allow"))
                break
    else:
        rec_v("B14-405-allow", "methods", "9110 §15.5.6 (MUST)",
              "a 405 Method Not Allowed response MUST include an Allow header",
              "no 405 observed from unsupported methods", "SKIP",
              "server did not emit any 405 (methods answered otherwise)")


# ==========================================================================
# Group C — Request-target forms (RFC 9112 §3.2)
# ==========================================================================
def c_targets():
    r_org = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    r_abs = raw("GET http://x%s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("C01-absolute-form", "targets", "9112 §3.2.2 (MUST)",
        "absolute-form request-target accepted and routed like origin-form",
        "GET http://x%s" % HEALTH,
        status_code(r_abs) == status_code(r_org) == 200,
        "abs=%s org=%s" % (status_code(r_abs), status_code(r_org)))

    # authority-form is only legal for CONNECT; a GET with authority-form is malformed
    r_auth = raw("GET x:80 HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r_auth)
    rec("C02-authority-form-get", "targets", "9112 §3.2.3 (MUST)",
        "authority-form target is only valid for CONNECT; a GET with it is 400, not 200",
        "GET x:80", st == 400 or (r_auth == b"") or st in (404,),
        "status=%s (200 = mis-parsed authority-form)" % st)

    # query string preserved / routed
    r_q = raw("GET %s?a=1&b=2 HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("C03-query-string", "targets", "9112 §3.2.1 (MUST)",
        "origin-form with a query component is accepted and routed",
        "GET %s?a=1&b=2" % HEALTH, status_code(r_q) == 200,
        "status=%s" % status_code(r_q))

    # fragment MUST NOT be sent by clients; a server seeing one should not 200 a
    # different resource — reject (400) or treat literally (404), not silently strip to 200.
    r_frag = raw("GET %s#frag HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r_frag)
    rec("C04-fragment-in-target", "targets", "9112 §3.2 / 3986 §3.5 (SHOULD)",
        "a fragment in the request-target is rejected (400) or 404, not silently served as 200",
        "GET %s#frag" % HEALTH, st in (400, 404) or (r_frag == b""),
        "status=%s (200 = fragment silently stripped)" % st)

    # empty target
    r_empty = raw("GET  HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r_empty)
    rec("C05-empty-target", "targets", "9112 §3 (MUST)",
        "an empty request-target is a malformed request-line ⇒ 400 (or close)",
        "GET <empty>", st == 400 or (r_empty == b""),
        "status=%s len=%d" % (st, len(r_empty or b"")))

    # target not starting with '/' (relative) is malformed for origin-form
    r_rel = raw("GET health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r_rel)
    rec("C06-relative-target", "targets", "9112 §3.2.1 (SHOULD)",
        "a bare relative target ('health', no leading /) is rejected (400) or 404, not 200",
        "GET health", st in (400, 404) or (r_rel == b""),
        "status=%s" % st)

    # double slash path
    r_ds = raw("GET //%s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH.lstrip("/"))
    rec_v("C07-double-slash", "targets", "9110 §4.1 (capability)",
          "path with a leading double slash handled deterministically (routed or 404)",
          "GET //%s" % HEALTH.lstrip("/"),
          "PASS" if status_code(r_ds) in (200, 404, 400) else "FAIL",
          "status=%s" % status_code(r_ds))


# ==========================================================================
# Group D — Host header (RFC 9112 §3.2, RFC 9110)
# ==========================================================================
def d_host():
    r = raw("GET %s HTTP/1.1\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("D01-missing-host", "host", "9112 §3.2 (MUST)",
        "HTTP/1.1 request lacking a Host header MUST be answered with 400",
        "GET %s (no Host)" % HEALTH, st == 400,
        "status=%s (expected 400)" % st)

    r = raw("GET %s HTTP/1.1\r\nHost: a\r\nHost: b\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("D02-duplicate-host", "host", "9112 §3.2 (MUST)",
        "request with more than one Host header MUST get 400",
        "GET %s (Host: a / Host: b)" % HEALTH, st == 400,
        "status=%s (expected 400)" % st)

    r = raw("GET %s HTTP/1.1\r\nHost:\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec_v("D03-empty-host", "host", "9110 §7.2 (capability)",
          "an empty Host is handled deterministically (accepted for a single-tenant origin, or 400)",
          "GET %s (Host: <empty>)" % HEALTH,
          "PASS" if st in (200, 400) else "FAIL",
          "status=%s" % st)

    # Host with invalid character (space in authority)
    r = raw("GET %s HTTP/1.1\r\nHost: bad host\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("D04-host-invalid-char", "host", "9110 §4.2 / 3986 §3.2.2 (SHOULD)",
        "a Host with an invalid authority (embedded space) is rejected (400), not 200",
        "GET %s (Host: 'bad host')" % HEALTH, st == 400 or (r == b""),
        "status=%s (200 = invalid authority accepted)" % st)

    # Host with port
    r = raw("GET %s HTTP/1.1\r\nHost: x:80\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("D05-host-with-port", "host", "9110 §4.2 (MUST)",
        "a Host with an explicit port is a valid authority and routes normally",
        "GET %s (Host: x:80)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # absolute-form authority takes precedence; Host may differ but request still valid
    r = raw("GET http://authority.example%s HTTP/1.1\r\nHost: other\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("D06-absform-host-precedence", "host", "9112 §3.2.2 (MUST)",
        "with absolute-form, the target authority is authoritative even if Host differs (still valid)",
        "GET http://authority.example%s (Host: other)" % HEALTH,
        status_code(r) == 200, "status=%s" % status_code(r))


# ==========================================================================
# Group E — Header field syntax & parsing (RFC 9110 §5, RFC 9112 §5)
# ==========================================================================
def e_fields():
    # whitespace before colon MUST be rejected
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nX-Foo : bar\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("E01-ws-before-colon", "fields", "9112 §5.1 (MUST)",
        "whitespace between field-name and colon MUST yield 400 (no OWS before ':')",
        "GET %s (\"X-Foo : bar\")" % HEALTH, st == 400,
        "status=%s (expected 400)" % st)

    # obs-fold: must be rejected (400) OR SP-replaced and still routed
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nX-Fold: a\r\n b\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("E02-obs-fold", "fields", "9112 §5.2 (MUST)",
        "obs-fold (line-folded value) MUST be rejected (400) or replaced with SP and still routed (200)",
        "GET %s (folded X-Fold)" % HEALTH, st in (200, 400),
        "status=%s (other = message mis-framed by the fold)" % st)

    # empty field name
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\n: emptyname\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("E03-empty-field-name", "fields", "9110 §5.1 (MUST)",
        "a header line with an empty field-name is malformed ⇒ 400 (or close)",
        "GET %s (\": emptyname\")" % HEALTH, st == 400 or (r == b""),
        "status=%s (200 = empty field-name accepted)" % st)

    # header names are case-insensitive: hOsT works
    r = raw("GET %s HTTP/1.1\r\nhOsT: x\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("E04-header-name-case-insensitive", "fields", "9110 §5.1 (MUST)",
        "field names are case-insensitive; 'hOsT' satisfies the Host requirement",
        "GET %s (hOsT: x)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # value OWS trimming: leading/trailing spaces around the value are stripped, still routes
    r = raw("GET %s HTTP/1.1\r\nHost:    x   \r\nConnection: close\r\n\r\n" % HEALTH)
    rec("E05-value-ows-trim", "fields", "9112 §5 (MUST)",
        "optional whitespace around a field value is trimmed; request still routes",
        "GET %s (Host:    x   )" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # control char (bare CR) inside a field value is invalid
    r = raw(b"GET " + HEALTH.encode() + b" HTTP/1.1\r\nHost: x\r\nX-Bad: a\rb\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    rec("E06-ctl-in-value", "fields", "9110 §5.5 (MUST)",
        "a control char (bare CR) inside a field value is rejected (400) or the request closed",
        "GET %s (X-Bad: a<CR>b)" % HEALTH, st == 400 or (r == b""),
        "status=%s len=%d" % (st, len(r or b"")))

    # NUL byte in field value
    r = raw(b"GET " + HEALTH.encode() + b" HTTP/1.1\r\nHost: x\r\nX-Nul: a\x00b\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    rec("E07-nul-in-value", "fields", "9110 §5.5 (MUST)",
        "a NUL octet inside a field value is rejected (400) or the connection closed",
        "GET %s (X-Nul: a<NUL>b)" % HEALTH, st == 400 or (r == b""),
        "status=%s len=%d" % (st, len(r or b"")))

    # many small headers (bounded) — should not crash, deterministic answer
    many = "".join("X-H%d: v\r\n" % i for i in range(100))
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\n%sConnection: close\r\n\r\n" % (HEALTH, many))
    st = status_code(r)
    rec("E08-many-headers", "fields", "9110 §5 (SHOULD)",
        "a request with 100 small headers is handled deterministically (200 or 431/400), no crash",
        "GET %s (100 headers)" % HEALTH, st in (200, 400, 431),
        "status=%s len=%d" % (st, len(r or b"")))

    # duplicate comma-list header combining: two Accept lines are semantically one list
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept: text/html\r\nAccept: text/plain\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("E09-dup-list-header", "fields", "9110 §5.2 (SHOULD)",
        "two instances of a list-valued header (Accept) are accepted (combinable), request routes",
        "GET %s (Accept x2)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))


# ==========================================================================
# Group F — Content-Length framing (RFC 9112 §6.2)
# ==========================================================================
def f_content_length():
    # non-numeric CL
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: abc\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("F01-nonnumeric-cl", "content-length", "9112 §6.2 (MUST)",
        "a non-numeric Content-Length is invalid ⇒ 400 (or close)",
        "POST %s (Content-Length: abc)" % HEALTH, st == 400 or (r == b""),
        "status=%s len=%d" % (st, len(r or b"")))

    # negative CL
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: -5\r\nConnection: close\r\n\r\nhello" % HEALTH)
    st = status_code(r)
    rec("F02-negative-cl", "content-length", "9112 §6.2 (MUST)",
        "a negative Content-Length is invalid ⇒ 400 (or close)",
        "POST %s (Content-Length: -5)" % HEALTH, st == 400 or (r == b""),
        "status=%s" % st)

    # CL with plus sign
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: +5\r\nConnection: close\r\n\r\nhello" % HEALTH)
    st = status_code(r)
    rec("F03-plus-cl", "content-length", "9112 §6.2 (MUST)",
        "a Content-Length with a '+' sign is not a valid 1*DIGIT ⇒ 400 (or close)",
        "POST %s (Content-Length: +5)" % HEALTH, st == 400 or (r == b""),
        "status=%s" % st)

    # CL with whitespace inside
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 5 5\r\nConnection: close\r\n\r\nhello" % HEALTH)
    st = status_code(r)
    rec("F04-cl-internal-ws", "content-length", "9112 §6.2 (MUST)",
        "a Content-Length containing embedded whitespace is invalid ⇒ 400 (or close)",
        "POST %s (Content-Length: '5 5')" % HEALTH, st == 400 or (r == b""),
        "status=%s" % st)

    # valid CL body consumed correctly (request served, connection framed)
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nConnection: close\r\n\r\nhello" % HEALTH)
    rec("F05-valid-cl-body", "content-length", "9112 §6.2 (MUST)",
        "a valid Content-Length body is consumed and the request served",
        "POST %s (Content-Length: 5, hello)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))


# ==========================================================================
# Group G — Transfer-Encoding / chunked (RFC 9112 §6-7)
# ==========================================================================
def g_chunked():
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n0\r\n\r\n" % HEALTH)
    rec("G01-chunked-basic", "chunked", "9112 §7.1 (MUST)",
        "a valid chunked request body is decoded and the request served",
        "POST %s (chunked hello)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # chunk extension parsed & ignored
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5;ext=1\r\nhello\r\n0\r\n\r\n" % HEALTH)
    rec("G02-chunk-ext", "chunked", "9112 §7.1.1 (MUST)",
        "chunk extensions are parsed and ignored; request still served",
        "POST %s (5;ext=1)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # trailer section accepted
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n0\r\nX-Trailer: v\r\n\r\n" % HEALTH)
    rec("G03-chunk-trailer", "chunked", "9112 §7.1.2 (MUST)",
        "a trailer section after the last-chunk is accepted; request served",
        "POST %s (chunk + trailer)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # uppercase hex chunk size
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\nA\r\nHELLOWORLD\r\n0\r\n\r\n" % HEALTH)
    rec("G04-chunk-hex-upper", "chunked", "9112 §7.1 (MUST)",
        "an uppercase-hex chunk size (A = 10) is valid and decoded",
        "POST %s (chunk size 'A')" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # non-hex chunk size — framing error
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\nZZ\r\nhello\r\n0\r\n\r\n" % HEALTH)
    rec("G05-chunk-badsize", "chunked", "9112 §7.1 (MUST)",
        "a non-hex chunk size is a framing error ⇒ reject/close, never parsed as data",
        "POST %s (chunk size 'ZZ')" % HEALTH, safe_or_4xx(r),
        "status=%s len=%d" % (status_code(r), len(r or b"")))

    # TE value is case-insensitive: "Chunked"
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: Chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n0\r\n\r\n" % HEALTH)
    rec("G06-te-case-insensitive", "chunked", "9112 §6.1 (MUST)",
        "the transfer-coding name is case-insensitive; 'Chunked' is decoded",
        "POST %s (TE: Chunked)" % HEALTH, status_code(r) == 200,
        "status=%s" % status_code(r))

    # TE where chunked is not the final coding — unframable ⇒ 400/close
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked, gzip\r\nConnection: close\r\n\r\n5\r\nhello\r\n0\r\n\r\n" % HEALTH)
    rec("G07-te-chunked-not-final", "chunked", "9112 §6.3 (MUST)",
        "TE with chunked NOT the final coding ⇒ 400/close (unframable body, smuggling vector)",
        "POST %s (TE: chunked, gzip)" % HEALTH, safe_or_4xx(r),
        "status=%s len=%d (200 = decoded anyway = smuggling risk)" % (status_code(r), len(r or b"")))

    # incomplete chunked (missing final 0-chunk) must not hang forever / not 200
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n" % HEALTH, timeout=3.0)
    st = status_code(r)
    rec("G08-incomplete-chunked", "chunked", "9112 §7.1 (MUST)",
        "an incomplete chunked body (no terminating 0-chunk) is not answered 200; closes or 400",
        "POST %s (chunk, no 0-terminator)" % HEALTH,
        (r == b"") or (st is not None and st != 200) or (st is None),
        "status=%s len=%d" % (st, len(r or b"")))


# ==========================================================================
# Group H — Request smuggling class (RFC 9112 §6.1, §6.3)
# ==========================================================================
def h_smuggling():
    # TE + CL both present: TE wins, message must be rejected/closed (not CL-framed)
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n" % HEALTH, timeout=3.0)
    rec("H01-te-cl-conflict", "smuggling", "9112 §6.3 (MUST)",
        "a message with both Transfer-Encoding and Content-Length is rejected/closed (anti-smuggling)",
        "POST %s (TE: chunked + CL: 5)" % HEALTH, safe_or_4xx(r),
        "status=%s len=%d" % (status_code(r), len(r or b"")))

    # two Content-Length with differing values
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nContent-Length: 6\r\nConnection: close\r\n\r\nhello" % HEALTH)
    rec("H02-dup-cl-differ", "smuggling", "9112 §6.2 (MUST)",
        "two Content-Length fields with DIFFERING values ⇒ 400 (or close)",
        "POST %s (CL: 5 / CL: 6)" % HEALTH, safe_or_4xx(r),
        "status=%s len=%d" % (status_code(r), len(r or b"")))

    # single Content-Length with a comma list of differing values
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 5, 6\r\nConnection: close\r\n\r\nhello" % HEALTH)
    rec("H03-cl-comma-differ", "smuggling", "9112 §6.2 (MUST)",
        "a Content-Length whose comma-list values differ (5, 6) ⇒ 400 (or close)",
        "POST %s (CL: '5, 6')" % HEALTH, safe_or_4xx(r),
        "status=%s" % status_code(r))

    # duplicate CL with SAME value is permitted -> serve
    r = raw("POST %s HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nContent-Length: 5\r\nConnection: close\r\n\r\nhello" % HEALTH)
    st = status_code(r)
    rec_v("H04-dup-cl-same", "smuggling", "9112 §6.2 (SHOULD)",
          "duplicate Content-Length with an IDENTICAL value may be accepted and served",
          "POST %s (CL: 5 / CL: 5)" % HEALTH,
          "PASS" if (st == 200 or safe_or_4xx(r)) else "FAIL",
          "status=%s (200 = merged, 400 = strict-reject; both defensible)" % st)


# ==========================================================================
# Group I — Connection management (RFC 9112 §9)
# ==========================================================================
def i_connection():
    # default persistence: two pipelined requests -> two responses on one socket
    n = -1
    try:
        s = socket.create_connection((HOST, PORT), timeout=4)
        s.settimeout(4)
        s.sendall(("GET %s HTTP/1.1\r\nHost: x\r\n\r\n"
                   "GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % (HEALTH, STATIC)).encode())
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
        n = len(all_status_codes(buf))
    except OSError:
        pass
    rec("I01-keepalive-default", "connection", "9112 §9.3 (MUST)",
        "HTTP/1.1 is persistent by default; two pipelined requests yield two responses",
        "GET %s then GET %s on one socket" % (HEALTH, STATIC), n == 2,
        "responses on one connection = %d" % n)

    # Connection: close honored & echoed
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    head, _ = split_head(r)
    rec("I02-connection-close", "connection", "9112 §9.6 (MUST)",
        "Connection: close is honored (response signals close and the socket is closed)",
        "GET %s (Connection: close)" % HEALTH,
        b"close" in (header_value(head, "connection") or b"").lower(),
        "Connection=%r" % header_value(head, "connection"))

    # HTTP/1.0 defaults to close
    r = raw("GET %s HTTP/1.0\r\nHost: x\r\n\r\n" % HEALTH)
    head, _ = split_head(r)
    conn = (header_value(head, "connection") or b"").lower()
    rec("I03-http10-default-close", "connection", "9112 §9.3 (MUST)",
        "an HTTP/1.0 request without keep-alive is treated as non-persistent (close)",
        "GET %s HTTP/1.0" % HEALTH,
        b"close" in conn or (b"keep-alive" not in conn),
        "Connection=%r" % header_value(head, "connection"))

    # HTTP/1.0 with explicit keep-alive: server may honor it (capability)
    keptalive = False
    try:
        s = socket.create_connection((HOST, PORT), timeout=4)
        s.settimeout(3)
        s.sendall(("GET %s HTTP/1.0\r\nHost: x\r\nConnection: keep-alive\r\n\r\n" % HEALTH).encode())
        first = b""
        while b"\r\n\r\n" not in first:
            d = s.recv(4096)
            if not d:
                break
            first += d
        # try a second request on the same socket
        s.sendall(("GET %s HTTP/1.0\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH).encode())
        second = b""
        while True:
            try:
                d = s.recv(4096)
            except socket.timeout:
                break
            if not d:
                break
            second += d
        s.close()
        keptalive = status_code(second) == 200
    except OSError:
        pass
    rec_v("I04-http10-keepalive", "connection", "9112 §9.3 (capability)",
          "HTTP/1.0 Connection: keep-alive may hold the connection open for a 2nd request",
          "GET %s HTTP/1.0 (keep-alive) x2" % HEALTH,
          "PASS" if keptalive else "FAIL",
          "2nd-response-on-same-socket=%s" % keptalive)

    # pipelined ordering across 3 requests
    codes = []
    try:
        s = socket.create_connection((HOST, PORT), timeout=5)
        s.settimeout(5)
        s.sendall(("GET %s HTTP/1.1\r\nHost: x\r\n\r\n"
                   "GET /no-such-xyz HTTP/1.1\r\nHost: x\r\n\r\n"
                   "GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % (HEALTH, STATIC)).encode())
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
        codes = all_status_codes(buf)
    except OSError:
        pass
    rec("I05-pipeline-order", "connection", "9112 §9.3.2 (MUST)",
        "pipelined requests are answered in the SAME order received",
        "GET %s, /no-such-xyz, %s" % (HEALTH, STATIC), codes == [200, 404, 200],
        "codes in order = %s (expected [200, 404, 200])" % codes)


# ==========================================================================
# Group J — Conditional requests (RFC 9110 §13 / RFC 7232)
# ==========================================================================
def j_conditional():
    etag = ASSET["etag"]
    if not etag:
        rec("J00-etag-present", "conditional", "9110 §8.8.3 (SHOULD)",
            "static asset carries a strong/weak validator (ETag)",
            "GET %s" % STATIC, False, "no ETag on static asset")
        return
    rec("J00-etag-present", "conditional", "9110 §8.8.3 (SHOULD)",
        "static asset carries a validator (ETag) for conditional requests",
        "GET %s" % STATIC, True, "ETag=%s" % etag)

    # If-None-Match matching -> 304
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-None-Match: %s\r\nConnection: close\r\n\r\n" % (STATIC, etag))
    rec("J01-inm-match-304", "conditional", "9110 §13.1.2 (MUST)",
        "If-None-Match with a matching validator ⇒ 304 for GET",
        "GET %s (If-None-Match: %s)" % (STATIC, etag), status_code(r) == 304,
        "status=%s (expected 304)" % status_code(r))

    # 304 no body
    head, body = split_head(r)
    rec("J02-304-no-body", "conditional", "9110 §15.4.5 (MUST)",
        "a 304 Not Modified response MUST NOT include a message body",
        "GET %s (If-None-Match match)" % STATIC,
        status_code(r) == 304 and len(body) == 0,
        "status=%s body=%d" % (status_code(r), len(body)))

    # 304 preserves the validator (ETag)
    rec("J03-304-keeps-etag", "conditional", "9110 §15.4.5 (SHOULD)",
        "a 304 response echoes the ETag so caches can update stored metadata",
        "GET %s (If-None-Match match)" % STATIC,
        status_code(r) == 304 and header_present(head, "etag"),
        "status=%s ETag=%r" % (status_code(r), header_value(head, "etag")))

    # If-None-Match: * -> 304 on existing
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-None-Match: *\r\nConnection: close\r\n\r\n" % STATIC)
    rec("J04-inm-star-304", "conditional", "9110 §13.1.2 (MUST)",
        "If-None-Match: * on an existing representation ⇒ 304 for GET",
        "GET %s (If-None-Match: *)" % STATIC, status_code(r) == 304,
        "status=%s (expected 304)" % status_code(r))

    # If-None-Match non-matching -> 200
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-None-Match: \"deadbeef\"\r\nConnection: close\r\n\r\n" % STATIC)
    rec("J05-inm-nomatch-200", "conditional", "9110 §13.1.2 (MUST)",
        "If-None-Match with a NON-matching validator ⇒ perform GET (200)",
        "GET %s (If-None-Match: \"deadbeef\")" % STATIC, status_code(r) == 200,
        "status=%s (expected 200)" % status_code(r))

    # If-Match matching -> 200
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Match: %s\r\nConnection: close\r\n\r\n" % (STATIC, etag))
    st = status_code(r)
    rec("J06-ifmatch-match-200", "conditional", "9110 §13.1.1 (MUST)",
        "If-Match with a matching validator ⇒ perform the method (200), never 304",
        "GET %s (If-Match: %s)" % (STATIC, etag), st == 200,
        "status=%s (304 here = If-Match handled as If-None-Match)" % st)

    # If-Match non-matching -> 412
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Match: \"00000000\"\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec("J07-ifmatch-nomatch-412", "conditional", "9110 §13.1.1 (MUST)",
        "If-Match with no matching validator ⇒ 412 Precondition Failed",
        "GET %s (If-Match: \"00000000\")" % STATIC, st == 412,
        "status=%s (expected 412)" % st)

    # If-Match: * on existing -> 200
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Match: *\r\nConnection: close\r\n\r\n" % STATIC)
    rec("J08-ifmatch-star-200", "conditional", "9110 §13.1.1 (MUST)",
        "If-Match: * on an existing representation ⇒ perform the method (200)",
        "GET %s (If-Match: *)" % STATIC, status_code(r) == 200,
        "status=%s" % status_code(r))

    # If-Modified-Since in the far future -> 304
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Modified-Since: Sat, 01 Jan 2050 00:00:00 GMT\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec("J09-ims-future-304", "conditional", "9110 §13.1.3 (MUST)",
        "If-Modified-Since after the representation's date ⇒ 304 (GET/HEAD)",
        "GET %s (If-Modified-Since: 2050)" % STATIC, st == 304,
        "status=%s (200 = IMS not implemented)" % st)

    # If-Modified-Since in the far past -> 200
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Modified-Since: Thu, 01 Jan 1970 00:00:00 GMT\r\nConnection: close\r\n\r\n" % STATIC)
    rec("J10-ims-past-200", "conditional", "9110 §13.1.3 (MUST)",
        "If-Modified-Since before the representation's date ⇒ 200 (send the body)",
        "GET %s (If-Modified-Since: 1970)" % STATIC, status_code(r) == 200,
        "status=%s" % status_code(r))

    # If-Unmodified-Since far past -> 412
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Unmodified-Since: Thu, 01 Jan 1970 00:00:00 GMT\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec("J11-ius-past-412", "conditional", "9110 §13.1.4 (MUST)",
        "If-Unmodified-Since before the representation's date ⇒ 412 Precondition Failed",
        "GET %s (If-Unmodified-Since: 1970)" % STATIC, st == 412,
        "status=%s (200 = IUS not implemented)" % st)

    # Precedence: If-None-Match takes precedence over If-Modified-Since (§13.2.2)
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-None-Match: \"deadbeef\"\r\nIf-Modified-Since: Sat, 01 Jan 2050 00:00:00 GMT\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec("J12-inm-over-ims", "conditional", "9110 §13.2.2 (MUST)",
        "If-None-Match takes precedence over If-Modified-Since (non-match ⇒ 200 despite future IMS)",
        "GET %s (INM nomatch + IMS 2050)" % STATIC, st == 200,
        "status=%s (304 = IMS wrongly honored over INM)" % st)


# ==========================================================================
# Group K — Range requests (RFC 9110 §14 / RFC 7233)
# ==========================================================================
def k_range():
    ar = (ASSET["accept_ranges"] or "").lower()
    advertises = ar == "bytes"
    rec("K00-accept-ranges", "range", "9110 §14.3 (capability)",
        "the static asset advertises Accept-Ranges: bytes",
        "GET %s" % STATIC, advertises, "Accept-Ranges=%r" % ASSET["accept_ranges"])

    # satisfiable range -> 206 + Content-Range
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nRange: bytes=0-3\r\nConnection: close\r\n\r\n" % STATIC)
    head, body = split_head(r)
    st = status_code(r)
    rec("K01-range-206", "range", "9110 §14.2/§15.3.7 (MUST-if-supported)",
        "a satisfiable Range on a range-advertising resource ⇒ 206 + Content-Range",
        "GET %s (Range: bytes=0-3)" % STATIC,
        st == 206 and header_present(head, "content-range") and len(body) == 4,
        "status=%s body=%d Content-Range=%r" % (st, len(body), header_value(head, "content-range")))

    # 206 body length equals requested range
    rec("K02-206-body-len", "range", "9110 §14.4 (MUST)",
        "a 206 for bytes=0-3 returns exactly 4 octets",
        "GET %s (Range: bytes=0-3)" % STATIC, st == 206 and len(body) == 4,
        "status=%s body=%d (expected 4)" % (st, len(body)))

    # suffix range bytes=-4 -> last 4 octets
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nRange: bytes=-4\r\nConnection: close\r\n\r\n" % STATIC)
    head, body = split_head(r)
    st = status_code(r)
    rec("K03-suffix-range", "range", "9110 §14.1.2 (MUST-if-supported)",
        "a suffix range (bytes=-4) ⇒ 206 with the last 4 octets",
        "GET %s (Range: bytes=-4)" % STATIC, st == 206 and len(body) == 4,
        "status=%s body=%d" % (st, len(body)))

    # open-ended range bytes=2- -> from offset 2 to end
    if ASSET["body_len"]:
        want = ASSET["body_len"] - 2
        r = raw("GET %s HTTP/1.1\r\nHost: x\r\nRange: bytes=2-\r\nConnection: close\r\n\r\n" % STATIC)
        head, body = split_head(r)
        st = status_code(r)
        rec("K04-open-range", "range", "9110 §14.1.2 (MUST-if-supported)",
            "an open-ended range (bytes=2-) ⇒ 206 from offset 2 to the end",
            "GET %s (Range: bytes=2-)" % STATIC, st == 206 and len(body) == want,
            "status=%s body=%d (expected %d)" % (st, len(body), want))

    # unsatisfiable range -> 416 + Content-Range: bytes */len
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nRange: bytes=99999990-100000000\r\nConnection: close\r\n\r\n" % STATIC)
    head, _ = split_head(r)
    st = status_code(r)
    cr = header_value(head, "content-range")
    rec("K05-range-416", "range", "9110 §14.4/§15.5.17 (MUST-if-supported)",
        "an unsatisfiable Range ⇒ 416 Range Not Satisfiable with Content-Range: bytes */len",
        "GET %s (Range: bytes=99999990-)" % STATIC,
        st == 416 and cr is not None and cr.startswith(b"bytes */"),
        "status=%s Content-Range=%r (expected 416 + 'bytes */len')" % (st, cr))

    # multiple ranges -> 206 multipart/byteranges
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nRange: bytes=0-1,3-4\r\nConnection: close\r\n\r\n" % STATIC)
    head, _ = split_head(r)
    st = status_code(r)
    ct = (header_value(head, "content-type") or b"").lower()
    rec("K06-multi-range", "range", "9110 §14.2/§15.3.7 (capability)",
        "multiple ranges ⇒ 206 with Content-Type multipart/byteranges (or a single coalesced 206)",
        "GET %s (Range: bytes=0-1,3-4)" % STATIC,
        st == 206 and (b"multipart/byteranges" in ct or header_present(head, "content-range")),
        "status=%s Content-Type=%r" % (st, ct))

    # If-Range with matching ETag -> 206
    if ASSET["etag"]:
        r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Range: %s\r\nRange: bytes=0-3\r\nConnection: close\r\n\r\n" % (STATIC, ASSET["etag"]))
        st = status_code(r)
        rec("K07-ifrange-match-206", "range", "9110 §13.1.5 (MUST-if-supported)",
            "If-Range with a matching validator ⇒ send the requested range (206)",
            "GET %s (If-Range match + Range)" % STATIC, st == 206,
            "status=%s (expected 206)" % st)

        # If-Range non-matching -> 200 full
        r = raw("GET %s HTTP/1.1\r\nHost: x\r\nIf-Range: \"00000000\"\r\nRange: bytes=0-3\r\nConnection: close\r\n\r\n" % STATIC)
        head, body = split_head(r)
        st = status_code(r)
        rec("K08-ifrange-nomatch-200", "range", "9110 §13.1.5 (MUST-if-supported)",
            "If-Range with a NON-matching validator ⇒ ignore Range, send full 200",
            "GET %s (If-Range nomatch + Range)" % STATIC,
            st == 200 and (ASSET["body_len"] is None or len(body) == ASSET["body_len"]),
            "status=%s body=%d (expected full 200)" % (st, len(body)))

    # non-bytes range unit -> ignored, 200 full
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nRange: items=0-3\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec("K09-unknown-range-unit", "range", "9110 §14.2 (MUST)",
        "an unrecognized range unit is ignored ⇒ 200 full response, never 206/416",
        "GET %s (Range: items=0-3)" % STATIC, st == 200,
        "status=%s (206/416 = mis-handled unknown unit)" % st)


# ==========================================================================
# Group L — Content negotiation (RFC 9110 §12)
# ==========================================================================
def l_negotiation():
    # Accept: */* -> 200
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept: */*\r\nConnection: close\r\n\r\n" % STATIC)
    rec("L01-accept-any", "negotiation", "9110 §12.5.1 (MUST)",
        "Accept: */* is satisfiable ⇒ 200",
        "GET %s (Accept: */*)" % STATIC, status_code(r) == 200,
        "status=%s" % status_code(r))

    # Accept with matching media type -> 200
    ct = (ASSET["ctype"] or "application/octet-stream").split(";")[0]
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept: %s\r\nConnection: close\r\n\r\n" % (STATIC, ct))
    rec("L02-accept-match", "negotiation", "9110 §12.5.1 (MUST)",
        "Accept naming the resource's media type ⇒ 200",
        "GET %s (Accept: %s)" % (STATIC, ct), status_code(r) == 200,
        "status=%s" % status_code(r))

    # Accept excluding the only representation: 406 or serve-anyway (both allowed)
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept: application/x-nonesuch\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec_v("L03-accept-unsatisfiable", "negotiation", "9110 §12.5.1/§15.5.7 (capability)",
          "an Accept that excludes the only representation ⇒ 406, or serve it anyway (both conformant)",
          "GET %s (Accept: application/x-nonesuch)" % STATIC,
          "PASS" if st in (200, 406) else "FAIL",
          "status=%s (406 = strict negotiation; 200 = serve-anyway)" % st)

    # Accept-Encoding: gzip -> may compress (Content-Encoding: gzip) + Vary
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept-Encoding: gzip\r\nConnection: close\r\n\r\n" % STATIC)
    head, _ = split_head(r)
    ce = (header_value(head, "content-encoding") or b"").lower()
    rec_v("L04-accept-encoding-gzip", "negotiation", "9110 §12.5.3 (capability)",
          "Accept-Encoding: gzip may yield Content-Encoding: gzip (else identity is still valid)",
          "GET %s (Accept-Encoding: gzip)" % STATIC,
          "PASS" if (status_code(r) == 200) else "FAIL",
          "status=%s Content-Encoding=%r" % (status_code(r), header_value(head, "content-encoding")))

    # a response that varies on Accept-Encoding SHOULD carry Vary
    if b"gzip" in ce:
        rec("L05-vary-on-encoding", "negotiation", "9110 §12.5.5 (SHOULD)",
            "a content-coding-negotiated response carries Vary: Accept-Encoding",
            "GET %s (Accept-Encoding: gzip)" % STATIC,
            b"accept-encoding" in (header_value(head, "vary") or b"").lower(),
            "Vary=%r" % header_value(head, "vary"))
    else:
        rec_v("L05-vary-on-encoding", "negotiation", "9110 §12.5.5 (SHOULD)",
              "a content-coding-negotiated response carries Vary: Accept-Encoding",
              "GET %s (Accept-Encoding: gzip)" % STATIC, "SKIP",
              "server did not gzip; Vary check not applicable")

    # Accept-Encoding: identity;q=0 with no acceptable coding -> 406 (SHOULD) or 200 identity
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept-Encoding: identity;q=0, *;q=0\r\nConnection: close\r\n\r\n" % STATIC)
    st = status_code(r)
    rec_v("L06-encoding-all-refused", "negotiation", "9110 §12.5.3 (capability)",
          "Accept-Encoding refusing every coding (incl. identity) may yield 406, or be served identity",
          "GET %s (Accept-Encoding: identity;q=0, *;q=0)" % STATIC,
          "PASS" if st in (200, 406) else "FAIL",
          "status=%s" % st)

    # Accept-Language is a hint; a single-language origin serves 200
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nAccept-Language: zz\r\nConnection: close\r\n\r\n" % STATIC)
    rec("L07-accept-language", "negotiation", "9110 §12.5.4 (MUST)",
        "Accept-Language for an unavailable language still yields a usable 200 (language negotiation optional)",
        "GET %s (Accept-Language: zz)" % STATIC, status_code(r) == 200,
        "status=%s" % status_code(r))


# ==========================================================================
# Group M — Expect / 100-continue (RFC 9110 §10.1.1)
# ==========================================================================
def m_expect():
    # 100-continue: server sends interim 100 then final, or a final directly — no hang
    buf, interim = raw_delayed(
        "POST %s HTTP/1.1\r\nHost: x\r\nExpect: 100-continue\r\nContent-Length: 5\r\nConnection: close\r\n\r\n" % HEALTH,
        "hello", gap=0.4, timeout=4.0)
    codes = all_status_codes(buf)
    rec("M01-100-continue-answered", "expect", "9110 §10.1.1 (MUST)",
        "Expect: 100-continue is answered deterministically (interim 100 and/or final), no hang",
        "POST %s (Expect: 100-continue)" % HEALTH, len(codes) >= 1,
        "codes=%s interim=%r" % (codes, (interim or b"")[:20]))

    # ideally an interim 100 precedes the final
    rec_v("M02-100-interim-sent", "expect", "9110 §10.1.1 (SHOULD)",
          "server sends an interim 100 (Continue) before reading the body it will accept",
          "POST %s (Expect: 100-continue)" % HEALTH,
          "PASS" if (interim and status_code(interim) == 100) else "FAIL",
          "interim_status=%s" % (status_code(interim) if interim else None))

    # unknown expectation -> 417
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nExpect: some-unknown-99\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("M03-expect-unknown-417", "expect", "9110 §10.1.1/§15.5.18 (MUST)",
        "an unsupported Expect value MUST yield 417 Expectation Failed",
        "GET %s (Expect: some-unknown-99)" % HEALTH, st == 417,
        "status=%s (200 = expectation silently ignored)" % st)


# ==========================================================================
# Group N — Caching (RFC 9111 / RFC 7234)
# ==========================================================================
def n_caching():
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % STATIC)
    head, _ = split_head(r)
    cc = header_value(head, "cache-control")
    rec_v("N01-cache-control-present", "caching", "9111 §5.2 (capability)",
          "a static asset advertises freshness via Cache-Control (max-age / public / immutable)",
          "GET %s" % STATIC,
          "PASS" if cc is not None else "FAIL",
          "Cache-Control=%r" % cc)

    # Age header, if present, must be a non-negative integer
    age = header_value(head, "age")
    if age is not None:
        rec("N02-age-syntax", "caching", "9111 §5.1 (MUST)",
            "an Age header value is a non-negative decimal integer",
            "GET %s" % STATIC, age.isdigit(),
            "Age=%r" % age)
    else:
        rec_v("N02-age-syntax", "caching", "9111 §5.1 (capability)",
              "Age header present and well-formed (origin responses often omit Age)",
              "GET %s" % STATIC, "SKIP", "no Age header (origin default)")

    # a 200 response is cacheable by default only with explicit freshness or a validator
    has_validator = header_present(head, "etag") or header_present(head, "last-modified")
    rec("N03-cacheability-signal", "caching", "9111 §3/§4.2 (SHOULD)",
        "a cacheable static response carries a validator (ETag/Last-Modified) or explicit freshness",
        "GET %s" % STATIC, has_validator or cc is not None,
        "ETag=%s Last-Modified=%s Cache-Control=%s"
        % (header_present(head, "etag"), header_present(head, "last-modified"), cc is not None))

    # Vary header, if present, is a valid field-name list (or *)
    vary = header_value(head, "vary")
    if vary is not None:
        toks = [t.strip() for t in vary.split(b",")]
        ok = vary == b"*" or all(re.match(rb"^[!#$%&'*+\-.^_`|~0-9A-Za-z]+$", t) for t in toks if t)
        rec("N04-vary-syntax", "caching", "9110 §12.5.5 (MUST)",
            "a Vary header is '*' or a comma list of valid field-names",
            "GET %s" % STATIC, ok, "Vary=%r" % vary)
    else:
        rec_v("N04-vary-syntax", "caching", "9110 §12.5.5 (capability)",
              "Vary present and well-formed (absent when the response does not vary)",
              "GET %s" % STATIC, "SKIP", "no Vary header")

    # a request with Cache-Control: no-cache still returns a fresh 200 from the origin
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nCache-Control: no-cache\r\nConnection: close\r\n\r\n" % STATIC)
    rec("N05-request-no-cache", "caching", "9111 §5.2.1.4 (MUST)",
        "an origin server honors a request even with Cache-Control: no-cache (returns a fresh 200)",
        "GET %s (Cache-Control: no-cache)" % STATIC, status_code(r) == 200,
        "status=%s" % status_code(r))


# ==========================================================================
# Group O — Status-code & error-response semantics (RFC 9110 §15)
# ==========================================================================
def o_status():
    # 404 for a missing resource
    r = raw("GET /surely-no-such-resource-9z HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    rec("O01-404-missing", "status", "9110 §15.5.5 (MUST)",
        "a request for a non-existent resource yields 404 Not Found",
        "GET /surely-no-such-resource-9z", status_code(r) == 404,
        "status=%s" % status_code(r))

    # 400 reason class for a malformed request-line (garbage version)
    r = raw("GET %s HTTP/9.9\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    st = status_code(r)
    rec("O02-bad-version", "status", "9112 §2.3/§15.6.6 (MUST)",
        "an unsupported HTTP major version is rejected (505 or 400), never served as 200",
        "GET %s HTTP/9.9" % HEALTH, st in (400, 505),
        "status=%s (expected 400/505)" % st)

    # garbage request line (not a method) -> 400
    r = raw("!@#$ garbage line\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    rec("O03-garbage-request-line", "status", "9112 §3 (MUST)",
        "a malformed request-line is answered 400 (or the connection is closed)",
        "!@#$ garbage line", st == 400 or (r == b""),
        "status=%s len=%d" % (st, len(r or b"")))

    # error responses carry a body framed by Content-Length (already partly in A07)
    r = raw("GET /nope-xyz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    cl = header_value(head, "content-length")
    rec("O04-error-body-framed", "status", "9112 §6 (MUST)",
        "a 404 response is self-delimiting (Content-Length present, or connection closed)",
        "GET /nope-xyz", cl is not None or b"close" in (header_value(head, "connection") or b"").lower(),
        "Content-Length=%r Connection=%r" % (cl, header_value(head, "connection")))

    # reason phrase for 404 is present & sensible
    r = raw("GET /nope-xyz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    rp = reason_phrase(r)
    rec("O05-404-reason", "status", "9110 §15.3 (SHOULD)",
        "the 404 status-line carries a non-empty reason phrase",
        "GET /nope-xyz", status_code(r) == 404 and len(rp.strip()) > 0,
        "reason=%r" % rp)

    # a 200 to GET does not carry a body-forbidding status (sanity: 1xx/204/304 have no body)
    # here we confirm 200 GET DOES carry a body (the inverse safety)
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    _, body = split_head(r)
    rec("O06-200-has-body", "status", "9110 §6.4.1 (MUST)",
        "a 200 GET response includes the representation body",
        "GET %s" % HEALTH, status_code(r) == 200 and len(body) > 0,
        "body=%d" % len(body))


# ==========================================================================
# Group P — Percent-encoding & path normalization (RFC 3986 / 9110 §4)
# ==========================================================================
def p_encoding():
    # percent-encoded path decodes to the same resource
    enc = "/" + "".join("%%%02X" % ord(c) for c in HEALTH.lstrip("/"))
    r_enc = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % enc)
    r_plain = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    rec("P01-percent-decode", "encoding", "3986 §2.1 (SHOULD)",
        "a fully percent-encoded path decodes to the same resource as the plain form",
        "GET %s" % enc, status_code(r_enc) == status_code(r_plain) == 200,
        "encoded=%s plain=%s" % (status_code(r_enc), status_code(r_plain)))

    # invalid percent-encoding (%ZZ) -> 400 (or 404), never mis-decoded to 200
    r = raw("GET /%ZZbad HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    rec("P02-invalid-percent", "encoding", "3986 §2.1/9110 §4 (SHOULD)",
        "an invalid percent-escape (%ZZ) is rejected (400) or 404, not silently 200",
        "GET /%ZZbad", st in (400, 404) or (r == b""),
        "status=%s" % st)

    # encoded NUL (%00) in path -> rejected/404, never 200 (truncation/bypass vector)
    r = raw("GET /health%00.txt HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    rec("P03-encoded-nul", "encoding", "9110 §4.1 (SHOULD)",
        "an encoded NUL (%00) in the path does not resolve to a different resource (no 200 via truncation)",
        "GET /health%00.txt", st in (400, 404) or (r == b""),
        "status=%s (200 = %%00 truncation)" % st)

    # dot-segment traversal must not escape the document root -> 404/400, never a 200 leak
    r = raw("GET /../../../../etc/passwd HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    st = status_code(r)
    leaked = b"root:" in (body or b"")
    rec("P04-path-traversal", "encoding", "9110 §4.1 (MUST)",
        "dot-segment traversal (../../etc/passwd) does not escape the root or leak a file",
        "GET /../../../../etc/passwd", (st in (400, 404) or (r == b"")) and not leaked,
        "status=%s leaked_passwd=%s" % (st, leaked))

    # encoded traversal (%2e%2e%2f) likewise contained
    r = raw("GET /%2e%2e%2f%2e%2e%2fetc%2fpasswd HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    st = status_code(r)
    leaked = b"root:" in (body or b"")
    rec("P05-encoded-traversal", "encoding", "9110 §4.1 (MUST)",
        "percent-encoded traversal (%2e%2e%2f) is normalized/contained, no file leak",
        "GET /%2e%2e%2f...etc%2fpasswd", (st in (400, 404) or (r == b"")) and not leaked,
        "status=%s leaked_passwd=%s" % (st, leaked))


# ==========================================================================
# Group Q — Header injection / CRLF & response-splitting safety (security)
# ==========================================================================
def q_injection():
    # a request header value carrying CRLF-injected text must not appear as a
    # separate response header (response splitting via reflected input)
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nX-Inject: foo\r\nX-Evil: injected\r\nConnection: close\r\n\r\n" % HEALTH)
    head, _ = split_head(r)
    rec("Q01-no-request-header-reflection", "injection", "9110 §5.5 (SHOULD)",
        "arbitrary request header names are not reflected verbatim into the response header block",
        "GET %s (X-Evil: injected)" % HEALTH,
        not header_present(head, "x-evil"),
        "x-evil-reflected=%s" % header_present(head, "x-evil"))

    # a path containing an encoded CRLF must not split the response
    r = raw("GET /health%0d%0aX-Injected:%20yes HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, _ = split_head(r)
    rec("Q02-encoded-crlf-path", "injection", "9110 §4.1 (MUST)",
        "an encoded CRLF in the path does not inject a response header (no response splitting)",
        "GET /health%0d%0aX-Injected:%20yes",
        not header_present(head, "x-injected"),
        "x-injected-present=%s status=%s" % (header_present(head, "x-injected"), status_code(r)))

    # a lone LF between headers should not desync framing (bare-LF line ending)
    r = raw("GET %s HTTP/1.1\r\nHost: x\nX-Bare: 1\r\nConnection: close\r\n\r\n" % HEALTH, timeout=3.0)
    st = status_code(r)
    n = len(all_status_codes(r or b""))
    rec("Q03-bare-lf-no-desync", "injection", "9112 §2.2 (SHOULD)",
        "a bare LF within the header block does not desync framing into two responses",
        "GET %s (bare LF before X-Bare)" % HEALTH,
        n <= 1 and (st in (200, 400) or (r == b"")),
        "responses=%d status=%s" % (n, st))


# ==========================================================================
# Group R — Response metadata (RFC 9110 §6.6.1, §10.2)
# ==========================================================================
def r_metadata():
    r = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)
    head, _ = split_head(r)
    rec("R01-date-header", "metadata", "9110 §6.6.1 (MUST)",
        "an origin server with a clock sends a Date header on 2xx/3xx/4xx",
        "GET %s" % HEALTH, header_present(head, "date"),
        "Date=%r" % header_value(head, "date"))

    # Date value is IMF-fixdate format
    dv = header_value(head, "date")
    imf = re.match(rb"^[A-Z][a-z][a-z], \d\d [A-Z][a-z][a-z] \d{4} \d\d:\d\d:\d\d GMT$", dv or b"")
    rec("R02-date-imf-format", "metadata", "9110 §5.6.7 (MUST)",
        "the Date value is an IMF-fixdate (e.g. 'Sun, 06 Nov 1994 08:49:37 GMT')",
        "GET %s" % HEALTH, imf is not None,
        "Date=%r" % dv)

    # Content-Type present on a body-bearing 200
    r2 = raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % STATIC)
    h2, _ = split_head(r2)
    rec("R03-content-type", "metadata", "9110 §8.3 (SHOULD)",
        "a body-bearing 200 response declares its media type via Content-Type",
        "GET %s" % STATIC, header_present(h2, "content-type"),
        "Content-Type=%r" % header_value(h2, "content-type"))

    # Server header, if present, is a valid product token (no CR/LF/control)
    sv = header_value(head, "server")
    if sv is not None:
        ok = all(0x20 <= b < 0x7f for b in sv)
        rec("R04-server-token", "metadata", "9110 §10.2.4 (MUST)",
            "the Server header, if present, is printable product tokens (no control chars)",
            "GET %s" % HEALTH, ok, "Server=%r" % sv)
    else:
        rec_v("R04-server-token", "metadata", "9110 §10.2.4 (capability)",
              "Server header present and well-formed (optional)",
              "GET %s" % HEALTH, "SKIP", "no Server header")

    # multiple identical requests give a stable status (determinism)
    codes = [status_code(raw("GET %s HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" % HEALTH)) for _ in range(3)]
    rec("R05-deterministic-status", "metadata", "operational (determinism)",
        "repeated identical safe requests return a stable status code",
        "GET %s x3" % HEALTH, len(set(codes)) == 1 and codes[0] == 200,
        "codes=%s" % codes)


# ==========================================================================
# Group Z — Resource-limit robustness (DESTRUCTIVE, opt-in)
# ==========================================================================
def z_resource_limit():
    if not alive():
        rec("Z01-large-head-dos", "resource-limit", "availability (robustness)",
            "serve is up before the destructive probe", "-", False,
            "serve not answering before Z1 — cannot attribute")
        return
    big = ("GET %s HTTP/1.1\r\nHost: x\r\nX-Big: " % HEALTH) + ("A" * (32 * 1024)) + "\r\nConnection: close\r\n\r\n"
    r = raw(big, timeout=6.0)
    time.sleep(0.6)
    survived = alive()
    rec("Z01-large-head-dos", "resource-limit", "availability (robustness)",
        "a single ~32 KiB request head does not crash the serve (bounded parse)",
        "GET %s (32 KiB header value)" % HEALTH, survived,
        "response=%r alive_after=%s (dead = unbounded-parse crash)"
        % (status_line(r).decode("latin1", "replace"), survived))

    if not alive():
        return
    longuri = "GET /" + ("a" * (32 * 1024)) + " HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
    r = raw(longuri, timeout=6.0)
    time.sleep(0.6)
    survived = alive()
    rec("Z02-long-uri-dos", "resource-limit", "availability (robustness)",
        "a single ~32 KiB request-target does not crash the serve (bounded URI parse; 414 preferred)",
        "GET /<32 KiB> " + HEALTH, survived,
        "response=%r alive_after=%s" % (status_line(r).decode("latin1", "replace"), survived))


# ==========================================================================
def main():
    if not alive():
        print("ERROR: no serve listening on %s:%d" % (HOST, PORT), file=sys.stderr)
        sys.exit(2)

    discover()

    groups = [a_framing, b_methods, c_targets, d_host, e_fields, f_content_length,
              g_chunked, h_smuggling, i_connection, j_conditional, k_range,
              l_negotiation, m_expect, n_caching, o_status, p_encoding,
              q_injection, r_metadata]
    for fn in groups:
        try:
            fn()
        except Exception as e:  # a check crashing is itself a finding, not a harness abort
            rec_v("%s-EXC" % fn.__name__, fn.__name__, "harness", "group raised",
                  "-", "FAIL", "exception: %r" % e)
        if not alive():
            rec_v("LIVENESS-after-%s" % fn.__name__, "liveness", "availability",
                  "serve still answering after this group", "-", "FAIL",
                  "serve stopped responding after %s (a prior check may have crashed it)" % fn.__name__)
            # try to continue; subsequent groups will mostly record refused
    if DESTRUCTIVE:
        z_resource_limit()   # LAST — may abort the serve
    else:
        rec_v("Z01-large-head-dos", "resource-limit", "availability (robustness)",
              "a single ~32 KiB request head does not crash the serve", "-", "SKIP",
              "destructive group not run (set CONF_DESTRUCTIVE=1)")
        rec_v("Z02-long-uri-dos", "resource-limit", "availability (robustness)",
              "a single ~32 KiB request-target does not crash the serve", "-", "SKIP",
              "destructive group not run (set CONF_DESTRUCTIVE=1)")

    graded = [r for r in RESULTS if r["verdict"] in ("PASS", "FAIL")]
    npass = sum(1 for r in graded if r["verdict"] == "PASS")
    nfail = sum(1 for r in graded if r["verdict"] == "FAIL")
    nskip = sum(1 for r in RESULTS if r["verdict"] == "SKIP")
    total = len(graded)
    width = max(len(r["id"]) for r in RESULTS)

    print("\n== comprehensive HTTP/1.1 RFC conformance battery — %s:%d ==\n" % (HOST, PORT))
    print("%-*s  %-6s  %-34s  %s" % (width, "CHECK", "VERDICT", "RFC", "CRITERION"))
    print("-" * 132)
    for r in RESULTS:
        print("%-*s  %-6s  %-34s  %s" % (width, r["id"], r["verdict"], r["rfc"], r["criterion"]))
        if r["verdict"] == "FAIL":
            print("%-*s          -> observed: %s" % (width, "", r["observed"]))
    print("-" * 132)
    print("\nTOTAL graded %d   PASS %d   FAIL %d   (+%d SKIP)   pass-rate %.1f%%\n"
          % (total, npass, nfail, nskip, (100.0 * npass / total if total else 0.0)))

    # gap map: the FAILs, grouped, MUST first
    fails = [r for r in RESULTS if r["verdict"] == "FAIL"]
    if fails:
        must = [r for r in fails if "(MUST)" in r["rfc"]]
        should = [r for r in fails if "(SHOULD)" in r["rfc"]]
        other = [r for r in fails if r not in must and r not in should]
        print("== GAP MAP (%d failing checks) ==" % len(fails))
        for label, bucket in (("MUST violations", must), ("SHOULD gaps", should), ("capability/other gaps", other)):
            if bucket:
                print("\n-- %s (%d) --" % (label, len(bucket)))
                for r in bucket:
                    print("  %-30s %s" % (r["id"], r["criterion"]))
                    print("  %-30s   observed: %s" % ("", r["observed"]))
        print()

    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "target": "%s:%d" % (HOST, PORT),
        "suite": "comprehensive HTTP/1.1 RFC conformance battery (7230-7235 / 9110-9112 / 3986)",
        "destructive": DESTRUCTIVE,
        "pass": npass, "fail": nfail, "skip": nskip, "total_graded": total,
        "pass_rate": round(100.0 * npass / total, 1) if total else 0.0,
        "checks": RESULTS,
    }
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results_rfc_full.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("wrote %s" % os.path.join(here, "results_rfc_full.json"))


if __name__ == "__main__":
    main()
