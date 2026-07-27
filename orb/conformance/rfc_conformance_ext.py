#!/usr/bin/env python3
"""Extended reference HTTP/1.1 conformance probe (RFC 7230/7231/7232/7233).

Companion to `rfc_conformance.py` (the base 17). This suite pushes past message
framing into the parts of HTTP/1.1 that most origin servers get *subtly* wrong and
that carry real security/interop weight:

  RFC 7230 §3.2.4  field parsing strictness (whitespace-before-colon, obs-fold)
  RFC 7230 §3.3.x  request smuggling class (TE-not-final, multi Content-Length)
  RFC 7230 §4.1    chunked transfer coding correctness (extensions, trailers, bad size)
  RFC 7230 §6.3    connection persistence & pipelined response ordering
  RFC 7231 §5.1.1  Expect / 100-continue expectation handling
  RFC 7232 §3.1/2  conditional requests (If-Match / If-None-Match ⇒ 304 / 412)
  RFC 7233 §2.3/3  range requests (Accept-Ranges honesty ⇒ 206 / 416)
  (operational)    response amplification / request-content disclosure
  (availability)   resource-limit robustness — large request head DoS  [DESTRUCTIVE]

Like the base suite it drives the *deployed* `dataplane` binary over a raw socket
and derives every verdict from the observed bytes. The static-asset ETag used by
the conditional checks is discovered at runtime (not hard-coded) so the suite does
not drift when the asset changes.

Run against a serve already listening (see conformance/rfc_launch.sh):

    python3 conformance/rfc_conformance_ext.py          # table + results_rfc_ext.json

The last group (Z, resource-limit) is DESTRUCTIVE — it can abort the serve — and is
skipped unless CONF_DESTRUCTIVE=1. When enabled it runs LAST so it cannot poison the
other verdicts. Env: CONF_HTTP_HOST (127.0.0.1), CONF_HTTP_PORT (8391),
CONF_DESTRUCTIVE (0). Exit code is always 0 — FAILs are findings, not harness errors.
"""
import json
import os
import re
import socket
import sys
import time

HOST = os.environ.get("CONF_HTTP_HOST", "127.0.0.1")
PORT = int(os.environ.get("CONF_HTTP_PORT", "8391"))
DESTRUCTIVE = os.environ.get("CONF_DESTRUCTIVE", "0") == "1"
STATIC = os.environ.get("CONF_STATIC_PATH", "/static/app.js")
RESULTS = []


def raw(req, timeout=5.0, cap=1 << 20):
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


def header_value(head, name):
    for line in head.split(b"\r\n"):
        if line.lower().startswith(name.lower() + b":"):
            return line.split(b":", 1)[1].strip()
    return None


def alive():
    r = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n", timeout=3.0)
    return r is not None and status_code(r) == 200


def record(cid, group, rfc, criterion, request, verdict, observed):
    RESULTS.append({
        "id": cid, "group": group, "rfc": rfc, "criterion": criterion,
        "request": request, "verdict": verdict, "observed": observed,
    })


# Discover the live ETag of the static asset so conditional checks don't drift.
def discover_etag():
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    head, _ = split_head(r)
    et = header_value(head, b"etag")
    ar = header_value(head, b"accept-ranges")
    return (et.decode("latin1") if et else None,
            ar.decode("latin1") if ar else None)


# ---------------------------------------------------------------------------
# Group H — Conditional requests (RFC 7232)
# ---------------------------------------------------------------------------
def h_conditional(etag):
    if not etag:
        record("H0-etag-present", "conditional", "7232 §2.3",
               "static asset carries a validator (ETag) for conditional requests",
               f"GET {STATIC}", "FAIL", "no ETag header on static asset")
        return
    record("H0-etag-present", "conditional", "7232 §2.3",
           "static asset carries a validator (ETag) for conditional requests",
           f"GET {STATIC}", "PASS", f"ETag={etag}")

    # H1: If-None-Match with the matching validator -> 304 (GET/HEAD).  §3.2
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nIf-None-Match: {etag}\r\nConnection: close\r\n\r\n")
    ok = status_code(r) == 304
    record("H1-inm-match-304", "conditional", "7232 §3.2 (MUST)",
           "If-None-Match with matching ETag ⇒ 304 Not Modified for GET",
           f"GET {STATIC} (If-None-Match: {etag})", "PASS" if ok else "FAIL",
           f"status={status_code(r)} (expected 304)")

    # H2: 304 MUST NOT carry a message body.  §4.1
    head, body = split_head(r)
    ok = status_code(r) == 304 and len(body) == 0
    record("H2-304-no-body", "conditional", "7232 §4.1 (MUST)",
           "304 response MUST NOT include a message body",
           f"GET {STATIC} (If-None-Match: {etag})", "PASS" if ok else "FAIL",
           f"status={status_code(r)}, body={len(body)} bytes")

    # H3: If-None-Match: * on an existing resource -> 304 (GET/HEAD).  §3.2
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nIf-None-Match: *\r\nConnection: close\r\n\r\n")
    ok = status_code(r) == 304
    record("H3-inm-star-304", "conditional", "7232 §3.2 (MUST)",
           "If-None-Match: * on an existing representation ⇒ 304 for GET",
           f"GET {STATIC} (If-None-Match: *)", "PASS" if ok else "FAIL",
           f"status={status_code(r)} (expected 304)")

    # H4: If-Match with the matching validator -> proceed (200), NOT 304.  §3.1
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nIf-Match: {etag}\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    ok = st == 200
    record("H4-ifmatch-match-200", "conditional", "7232 §3.1 (MUST)",
           "If-Match with matching ETag ⇒ perform method (200), never 304",
           f"GET {STATIC} (If-Match: {etag})", "PASS" if ok else "FAIL",
           f"status={st} (expected 200; 304 here = If-Match handled as If-None-Match)")

    # H5: If-Match with a non-matching validator -> 412 Precondition Failed.  §3.1
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nIf-Match: \"00000000\"\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    ok = st == 412
    record("H5-ifmatch-nomatch-412", "conditional", "7232 §3.1 (MUST)",
           "If-Match with no matching ETag ⇒ 412 Precondition Failed",
           f"GET {STATIC} (If-Match: \"00000000\")", "PASS" if ok else "FAIL",
           f"status={st} (expected 412)")


# ---------------------------------------------------------------------------
# Group I — Range requests (RFC 7233)
# ---------------------------------------------------------------------------
def i_range(accept_ranges):
    advertises = (accept_ranges or "").lower() == "bytes"
    record("I0-accept-ranges", "range", "7233 §2.3",
           "Accept-Ranges advertisement observed (sets the honesty bar for I1/I2)",
           f"GET {STATIC}", "PASS" if advertises else "FAIL",
           f"Accept-Ranges={accept_ranges!r}")

    # I1: a satisfiable byte range on a resource that advertises Accept-Ranges: bytes
    # should yield 206 Partial Content with a Content-Range.  §4.1
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nRange: bytes=0-3\r\nConnection: close\r\n\r\n")
    head, body = split_head(r)
    st = status_code(r)
    ok = st == 206 and header_value(head, b"content-range") is not None
    note = "" if advertises else " [Accept-Ranges not advertised; §3.1 permits ignoring]"
    record("I1-range-206", "range", "7233 §3.1/§4.1 (consistency)",
           "advertised Accept-Ranges: bytes ⇒ a satisfiable Range yields 206 (else drop the advertisement)",
           f"GET {STATIC} (Range: bytes=0-3)", "PASS" if ok else "FAIL",
           f"status={st}, body={len(body)} (expected 206 + Content-Range; 200-full = Range ignored){note}")

    # I2: an unsatisfiable range on a range-advertising resource -> 416.  §4.4
    r = raw(f"GET {STATIC} HTTP/1.1\r\nHost: x\r\nRange: bytes=99999990-100000000\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    ok = st == 416
    record("I2-range-416", "range", "7233 §4.4 (consistency)",
           "advertised Accept-Ranges: bytes ⇒ an unsatisfiable Range yields 416",
           f"GET {STATIC} (Range: bytes=99999990-)", "PASS" if ok else "FAIL",
           f"status={st} (expected 416; 200-full = Range ignored)")


# ---------------------------------------------------------------------------
# Group J — Expect / 100-continue (RFC 7231 §5.1.1)
# ---------------------------------------------------------------------------
def j_expect():
    # J1: a 100-continue expectation must be answered deterministically — an interim
    # 100 (Continue) OR a final status — never a hang.  §5.1.1
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nExpect: 100-continue\r\n"
            b"Content-Length: 5\r\nConnection: close\r\n\r\nhello", timeout=3.0)
    st = status_code(r)
    ok = st is not None
    record("J1-100-continue", "expect", "7231 §5.1.1",
           "Expect: 100-continue answered deterministically (interim 100 or final status), no hang",
           "POST /health (Expect: 100-continue)", "PASS" if ok else "FAIL",
           f"status={st}, resp_len={len(r or b'')}")

    # J2: an unsupported expectation MUST draw 417 Expectation Failed.  §5.1.1
    r = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nExpect: drorb-nonsense-99\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    ok = st == 417
    record("J2-expect-unknown-417", "expect", "7231 §5.1.1 (MUST)",
           "unsupported Expect value MUST yield 417 Expectation Failed",
           "GET /health (Expect: drorb-nonsense-99)", "PASS" if ok else "FAIL",
           f"status={st} (expected 417; 200 = expectation silently ignored)")


# ---------------------------------------------------------------------------
# Group K — Chunked transfer coding correctness (RFC 7230 §4.1)
# ---------------------------------------------------------------------------
def k_chunked():
    # K1: chunk extensions (chunk-size ";" name=value) MUST be parsed and ignored.  §4.1.1
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n"
            b"Connection: close\r\n\r\n5;name=value\r\nhello\r\n0\r\n\r\n", timeout=3.0)
    st = status_code(r)
    ok = st == 200
    record("K1-chunk-ext", "chunked", "7230 §4.1.1",
           "chunk extension is parsed and ignored; request still served",
           "POST /health (chunk 5;name=value)", "PASS" if ok else "FAIL",
           f"status={st} (expected 200)")

    # K2: a trailer section after the last-chunk is accepted, request served.  §4.1.2
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n"
            b"Connection: close\r\n\r\n5\r\nhello\r\n0\r\nX-Trailer: v\r\n\r\n", timeout=3.0)
    st = status_code(r)
    ok = st == 200
    record("K2-chunk-trailer", "chunked", "7230 §4.1.2",
           "trailer section after last-chunk accepted; request served",
           "POST /health (chunked + trailer)", "PASS" if ok else "FAIL",
           f"status={st} (expected 200)")

    # K3: a non-hex chunk size is a framing error — reject/close, never treat as data.  §4.1
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n"
            b"Connection: close\r\n\r\nZZ\r\nhello\r\n0\r\n\r\n", timeout=3.0)
    st = status_code(r)
    ok = (r == b"") or (st is not None and 400 <= st < 500)
    record("K3-chunk-badsize", "chunked", "7230 §4.1 (framing-safety)",
           "invalid (non-hex) chunk size rejected/closed, not parsed as body",
           "POST /health (chunk size 'ZZ')", "PASS" if ok else "FAIL",
           f"status={st}, resp_len={len(r or b'')} (empty/close or 4xx is safe)")


# ---------------------------------------------------------------------------
# Group L — Request smuggling class, extended (RFC 7230 §3.3.x)
# ---------------------------------------------------------------------------
def l_smuggling():
    # L1: Transfer-Encoding where chunked is NOT the final coding -> cannot frame the
    # body reliably; server MUST 400 and close.  §3.3.3(3) / §3.3.1
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked, gzip\r\n"
            b"Connection: close\r\n\r\n5\r\nhello\r\n0\r\n\r\n", timeout=3.0)
    st = status_code(r)
    ok = (r == b"") or (st is not None and 400 <= st < 500)
    record("L1-te-chunked-not-final", "smuggling", "7230 §3.3.3 (MUST)",
           "TE with chunked not the final coding ⇒ 400/close (unframable body, smuggling vector)",
           "POST /health (TE: chunked, gzip)", "PASS" if ok else "FAIL",
           f"status={st}, resp_len={len(r or b'')} (200 = decoded anyway = smuggling risk)")

    # L2: two Content-Length fields with DIFFERING values -> MUST be an error.  §3.3.2
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n"
            b"Content-Length: 6\r\nConnection: close\r\n\r\nhello", timeout=3.0)
    st = status_code(r)
    ok = (r == b"") or (st is not None and 400 <= st < 500)
    record("L2-dup-cl-differ", "smuggling", "7230 §3.3.2 (MUST)",
           "two Content-Length fields with differing values rejected/closed",
           "POST /health (Content-Length: 5 / 6)", "PASS" if ok else "FAIL",
           f"status={st}, resp_len={len(r or b'')} (empty/close or 4xx is safe)")

    # L3: duplicate Content-Length with the SAME value is permitted -> serve.  §3.3.2
    r = raw(b"POST /health HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n"
            b"Content-Length: 5\r\nConnection: close\r\n\r\nhello", timeout=3.0)
    st = status_code(r)
    ok = st == 200
    record("L3-dup-cl-same", "smuggling", "7230 §3.3.2",
           "duplicate Content-Length with identical value accepted; request served",
           "POST /health (Content-Length: 5 / 5)", "PASS" if ok else "FAIL",
           f"status={st} (expected 200)")


# ---------------------------------------------------------------------------
# Group M — Field parsing strictness (RFC 7230 §3.2.4)
# ---------------------------------------------------------------------------
def m_field_parsing():
    # M1: whitespace between field-name and colon MUST be rejected with 400.  §3.2.4
    r = raw(b"GET /health HTTP/1.1\r\nHost : x\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    ok = st == 400
    record("M1-ws-before-colon", "field-parsing", "7230 §3.2.4 (MUST)",
           "whitespace between field-name and colon MUST yield 400",
           "GET /health (\"Host : x\")", "PASS" if ok else "FAIL",
           f"status={st} (expected 400)")

    # M2: obs-fold (line folding) MUST be rejected (400) OR replaced with SP and the
    # request still processed correctly (here: /health ⇒ 200).  §3.2.4
    r = raw(b"GET /health HTTP/1.1\r\nHost: x\r\nX-Fold: a\r\n b\r\nConnection: close\r\n\r\n")
    st = status_code(r)
    ok = st == 400 or st == 200
    record("M2-obs-fold", "field-parsing", "7230 §3.2.4 (MUST)",
           "obs-fold header MUST be rejected (400) or SP-replaced and still routed (200)",
           "GET /health (folded X-Fold)", "PASS" if ok else "FAIL",
           f"status={st} (expected 400 or 200; other = message mis-framed by the fold)")


# ---------------------------------------------------------------------------
# Group N — Persistence / pipelining ordering & amplification
# ---------------------------------------------------------------------------
def n_pipeline_amp():
    # N1: three pipelined requests -> three responses, IN REQUEST ORDER.  §6.3.2
    codes = []
    try:
        s = socket.create_connection((HOST, PORT), timeout=5)
        s.settimeout(5)
        s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n"
                  b"GET /no-such-xyz HTTP/1.1\r\nHost: x\r\n\r\n"
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
        # Pipelined responses are glued back-to-back (a body's last octet directly
        # precedes the next status line), so scan the whole buffer, not line-split.
        codes = [int(m) for m in re.findall(rb"HTTP/1\.1 (\d{3}) ", buf)]
    except OSError:
        pass
    ok = codes == [200, 404, 200]
    record("N1-pipeline-order", "persistence", "7230 §6.3.2 (MUST)",
           "pipelined requests answered in the SAME order they were received",
           "GET /health, /no-such-xyz, /static on one socket", "PASS" if ok else "FAIL",
           f"response codes in order = {codes} (expected [200, 404, 200])")

    # N2: response size must not be a large multiple of request size (amplification /
    # request-content disclosure). The serve echoes the request head into an x-corr /
    # x-upstream debug header as dotted-decimal, ~3x the input.  (operational)
    val = b"A" * 8192
    req = b"GET /health HTTP/1.1\r\nHost: x\r\nX-Probe: " + val + b"\r\nConnection: close\r\n\r\n"
    r = raw(req)
    ratio = (len(r or b"") / len(req)) if r else 0.0
    head, _ = split_head(r)
    echoes = header_value(head, b"x-corr") is not None
    ok = ratio <= 2.0 and not echoes
    record("N2-amplification", "persistence", "operational (amplification/disclosure)",
           "response is not a large multiple of request size and does not echo request bytes",
           "GET /health with 8 KiB X-Probe header", "PASS" if ok else "FAIL",
           f"resp/req ratio={ratio:.2f}x, request-bytes-echoed-in-header={echoes} "
           f"(x-corr replays the request head as dotted-decimal)")


# ---------------------------------------------------------------------------
# Group Z — Resource-limit robustness (DESTRUCTIVE, availability)
# ---------------------------------------------------------------------------
def z_resource_limit():
    # Z1: a single large request HEAD (long URI / big header / many headers) must not
    # crash the serve. The deployed serve aborts with a thread stack overflow at ~30 KiB
    # of request head (long URI, one big header, or many headers all trigger it; a large
    # BODY is safe). Verified by a liveness probe after the request.
    if not alive():
        record("Z1-large-head-dos", "resource-limit", "availability (DoS)",
               "serve is up before the destructive check", "-", "FAIL",
               "serve not answering before Z1 — cannot attribute")
        return
    big_head = b"GET /health HTTP/1.1\r\nHost: x\r\nX-Big: " + b"A" * (32 * 1024) + b"\r\nConnection: close\r\n\r\n"
    r = raw(big_head, timeout=6.0)
    time.sleep(0.6)
    survived = alive()
    ok = survived
    record("Z1-large-head-dos", "resource-limit", "availability (DoS)",
           "a single ~32 KiB request head does not crash the serve (bounded parse, no stack blowup)",
           "GET /health with a 32 KiB header value", "PASS" if ok else "FAIL",
           f"response={status_line(r).decode('latin1','replace')!r}, resp_len={len(r or b'')}, "
           f"serve_alive_after={survived} (dead = stack-overflow abort of the whole process)")


def main():
    if not alive():
        print(f"ERROR: no serve listening on {HOST}:{PORT}", file=sys.stderr)
        sys.exit(2)

    etag, accept_ranges = discover_etag()
    h_conditional(etag)
    i_range(accept_ranges)
    j_expect()
    k_chunked()
    l_smuggling()
    m_field_parsing()
    n_pipeline_amp()
    if DESTRUCTIVE:
        z_resource_limit()   # LAST: may abort the serve
    else:
        record("Z1-large-head-dos", "resource-limit", "availability (DoS)",
               "a single ~32 KiB request head does not crash the serve",
               "GET /health with a 32 KiB header value", "SKIP",
               "destructive check not run (set CONF_DESTRUCTIVE=1); confirmed FAIL manually — see CONFORMANCE-EXT.md")

    graded = [r for r in RESULTS if r["verdict"] in ("PASS", "FAIL")]
    npass = sum(1 for r in graded if r["verdict"] == "PASS")
    total = len(graded)
    width = max(len(r["id"]) for r in RESULTS)
    print(f"\n== drorb EXTENDED HTTP/1.1 conformance (RFC 7230/31/32/33) — {HOST}:{PORT} ==\n")
    print(f"{'CHECK':<{width}}  {'VERDICT':<6}  RFC                      CRITERION")
    print("-" * 118)
    for r in RESULTS:
        print(f"{r['id']:<{width}}  {r['verdict']:<6}  {r['rfc']:<24}  {r['criterion']}")
        if r["verdict"] != "PASS":
            print(f"{'':<{width}}          -> observed: {r['observed']}")
    print("-" * 118)
    print(f"\nPASS {npass}/{total}  ({100.0 * npass / total:.1f}%)   "
          f"FAIL {total - npass}/{total}   (+{len(RESULTS) - total} skipped)\n")

    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "target": f"{HOST}:{PORT}",
        "suite": "RFC 7230/7231/7232/7233 extended HTTP/1.1 conformance",
        "destructive": DESTRUCTIVE,
        "pass": npass, "total_graded": total,
        "pass_rate": round(100.0 * npass / total, 1),
        "checks": RESULTS,
    }
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results_rfc_ext.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"wrote {os.path.join(here, 'results_rfc_ext.json')}")


if __name__ == "__main__":
    main()
