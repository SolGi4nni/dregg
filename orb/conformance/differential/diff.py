#!/usr/bin/env python3
"""Differential HTTP harness.

Sends an identical corpus of raw HTTP/1.1 requests to two servers — the system
under test (SUT) and a stock reference server — over real TCP sockets, parses
each response, normalizes volatile headers, and reports every DIVERGENCE.

Divergences are the deliverable: a status/header/body difference is a mapped
behavioural gap, not a harness failure. Nothing here tunes for a pass.

Usage:
    diff.py [--sut-port N] [--ref-port N] [--host H] [--json OUT] [--show-same]

Requests are raw bytes so malformed/edge-case inputs are exact. Each is sent on
a fresh connection (Connection: close where a well-formed request allows it) to
keep responses independent.

REACHABILITY IS A PRECONDITION, NOT A RESULT
--------------------------------------------
A differ that compares two silences sees no difference. Pointed at two dead
ports this harness used to send all 63 requests, fail identically on both
sides, observe zero divergences, print "0/63 requests diverged" and exit 0 — a
clean score for testing nothing. Two guards close that:

  * liveness precondition (`assert_live`): before ANY comparison, every
    endpoint must answer a known-good probe with a parseable HTTP status line.
    A refused connect, a black-hole listener that accepts and closes, or a
    non-HTTP peer aborts the run with FATAL and exit 2. No score is printed.
  * transport-fault accounting: a connect/send failure mid-run (a server that
    died under us) is an infrastructure fault, not a behaviour — the run is
    INVALID and exits 2. "Both sides errored" is never scored as agreement:
    even a symmetric recv-level failure is reported as a `both-error`
    divergence, because no response was compared.

Ports come from CLI flags, then $SUT_PORT/$REF_PORT (what launch.sh exports),
then the built-in defaults — one knob, so the launcher and the differ cannot
disagree about which ports to drive. `selftest.py` pins all of this.
"""
import argparse
import json
import os
import socket
import sys

# ---------------------------------------------------------------------------
# Volatile headers: present-or-not and value both vary per server/run/instant.
# We compare presence separately from value: a header both emit but with a
# server-specific value (Date, Server, ETag, connection ids) is normalized so
# it does not drown the real divergences. We STILL flag when one server emits a
# volatile header the other omits, because presence is a real behaviour.
VOLATILE_VALUE = {
    "date", "server", "etag", "last-modified", "connection",
    "keep-alive", "x-backend",
}
# Headers whose ABSENCE/PRESENCE we also ignore (pure server identity / noise).
VOLATILE_PRESENCE = {"server", "date", "connection", "keep-alive"}


def parse_response(raw):
    """Parse a raw HTTP/1.1 response into (status_line, headers, body).

    headers: list of (lower-name, value) preserving order and duplicates.
    Returns None if no CRLFCRLF header terminator is present.
    """
    idx = raw.find(b"\r\n\r\n")
    if idx < 0:
        return None
    head = raw[:idx].decode("latin-1")
    body = raw[idx + 4:]
    lines = head.split("\r\n")
    status_line = lines[0] if lines else ""
    headers = []
    for ln in lines[1:]:
        if ":" in ln:
            k, v = ln.split(":", 1)
            headers.append((k.strip().lower(), v.strip()))
    return status_line, headers, body


def recv_all(host, port, req, timeout=5.0):
    """Send raw bytes on a fresh connection, read until close or timeout.

    Returns (raw_bytes, error_str). error_str is set on connect/timeout/reset.
    """
    try:
        s = socket.create_connection((host, port), timeout=timeout)
    except OSError as e:
        return b"", f"connect: {e}"
    s.settimeout(timeout)
    try:
        s.sendall(req)
    except OSError as e:
        s.close()
        return b"", f"send: {e}"
    chunks = []
    try:
        while True:
            b = s.recv(65536)
            if not b:
                break
            chunks.append(b)
            # Guard: if the response is content-length framed and we clearly
            # have head+body already, a server that keeps the socket open would
            # hang us to timeout. We rely on Connection: close in the corpus for
            # well-formed requests; the timeout is the backstop otherwise.
    except socket.timeout:
        pass
    except OSError as e:
        if not chunks:
            s.close()
            return b"", f"recv: {e}"
    s.close()
    return b"".join(chunks), None


def status_code(status_line):
    parts = status_line.split(" ", 2)
    if len(parts) >= 2 and parts[1].isdigit():
        return parts[1]
    return None


# ---------------------------------------------------------------------------
# Reachability: preconditions and fault classification.
#
# recv_all's error strings carry their phase. connect/send failures mean the
# request never reached the peer — the harness could not test anything. recv
# failures mean the request WAS delivered and the peer dropped us; that is a
# behaviour, but still not a comparable response.
FAULT_PHASES = ("connect:", "send:")


def is_transport_fault(err):
    """True if this error string means the request never reached the server."""
    return isinstance(err, str) and err.startswith(FAULT_PHASES)


# A request every server in this lane must answer: the static docroot's
# smallest file. Any parseable HTTP status line proves a live HTTP peer.
LIVENESS_TARGET = "/static/hello.txt"


def probe_liveness(host, port, attempts=5, delay=0.2, timeout=3.0):
    """Send one known-good request. Return (ok: bool, detail: str).

    ok requires: connect succeeds, bytes come back, they parse as HTTP, and the
    status line carries a status code. A listener that accepts and closes
    without writing (the black hole that also produces identical 'agreement' on
    both sides) fails here, which is the point.
    """
    import time
    detail = "no attempt"
    for i in range(attempts):
        req = (f"GET {LIVENESS_TARGET} HTTP/1.1\r\nHost: {host}:{port}\r\n"
               f"Connection: close\r\n\r\n").encode("latin-1")
        raw, err = recv_all(host, port, req, timeout=timeout)
        if err:
            detail = err
        elif not raw:
            detail = "accepted the connection then closed with NO bytes (not an HTTP server)"
        else:
            parsed = parse_response(raw)
            if parsed is None:
                detail = f"unparseable response ({len(raw)} bytes, no CRLFCRLF): {raw[:60]!r}"
            elif status_code(parsed[0]) is None:
                detail = f"no HTTP status code in status line: {parsed[0]!r}"
            else:
                return True, f"{parsed[0].strip()} ({len(parsed[2])} body bytes)"
        if i + 1 < attempts:
            time.sleep(delay)
    return False, detail


def assert_live(host, endpoints, stream=sys.stderr):
    """Precondition: every (name, port) must answer the known-good probe.

    Returns the list of (name, port, detail) on success. On ANY failure prints
    a loud FATAL block and exits 2 — a comparison across an unreachable
    endpoint is not a result, and must never be reported as one.
    """
    ok, bad = [], []
    for name, port in endpoints:
        good, detail = probe_liveness(host, port)
        (ok if good else bad).append((name, port, detail))
    if bad:
        print("", file=stream)
        print("=" * 72, file=stream)
        print("FATAL: liveness precondition FAILED — refusing to compare.", file=stream)
        for name, port, detail in bad:
            print(f"  UNREACHABLE  {name:6s} {host}:{port}  ->  {detail}", file=stream)
        for name, port, detail in ok:
            print(f"  live         {name:6s} {host}:{port}  ->  {detail}", file=stream)
        print("", file=stream)
        print("  Every endpoint must answer "
              f"GET {LIVENESS_TARGET} before any request is compared.", file=stream)
        print("  Identical failures on both sides are NOT agreement: a differ", file=stream)
        print("  pointed at dead ports sees no divergence and scores a clean", file=stream)
        print("  run while testing nothing. Start the lane (launch.sh), and", file=stream)
        print("  check the ports match — this harness reads $SUT_PORT/$REF_PORT", file=stream)
        print("  so the launcher's env and the CLI flags cannot disagree.", file=stream)
        print("=" * 72, file=stream)
        sys.exit(2)
    for name, port, detail in ok:
        print(f"live: {name} {host}:{port} -> {detail}")
    return ok


def env_port(name, default):
    """Port default from the environment — the knob launch.sh exports.

    Precedence is CLI flag > env > built-in default. Before this, launch.sh
    honoured $SUT_PORT while diff.py silently used its own baked-in default,
    so overriding the lane's ports pointed the differ at dead ones.
    """
    raw = os.environ.get(name)
    if raw is None or raw == "":
        return default
    try:
        return int(raw)
    except ValueError:
        print(f"FATAL: ${name}={raw!r} is not a port number", file=sys.stderr)
        sys.exit(2)


def norm_headers(headers):
    """Map for comparison: dict name -> list of values, with volatile-value
    headers' values replaced by a placeholder (so presence still compares)."""
    out = {}
    for k, v in headers:
        val = "<vol>" if k in VOLATILE_VALUE else v
        out.setdefault(k, []).append(val)
    return out


def compare(sut, ref):
    """Return a list of divergence dicts between two parsed responses.

    Each side is either a parsed tuple, None (unparseable), or an error string.
    """
    divs = []

    # Transport-level: one side errored / gave no parseable response.
    def as_state(x):
        if isinstance(x, str):
            return ("error", x)
        if x is None:
            return ("unparseable", None)
        return ("ok", x)

    ss, se = as_state(sut)
    rs, re_ = as_state(ref)

    if ss != "ok" or rs != "ok":
        if ss != rs or (ss == "error" and rs == "error" and se != re_):
            divs.append({
                "kind": "transport",
                "detail": f"sut={ss}:{se if ss!='ok' else ''} ref={rs}:{re_ if rs!='ok' else ''}",
            })
        elif ss == "error" and rs == "error":
            # SAME error on both sides. This is the false-green shape: two
            # identical failures are not agreement, because no response was
            # ever compared. Report it. (Both-unparseable IS agreement: the
            # request was delivered and both peers answered with a close —
            # that is observable behaviour, and the liveness precondition has
            # already proved both peers are live HTTP servers.)
            divs.append({
                "kind": "both-error",
                "detail": f"both sides failed identically: {se} "
                          f"(no response compared — NOT agreement)",
            })
        # If both are the same non-ok state, nothing further to compare.
        if ss != "ok" or rs != "ok":
            return divs

    s_status, s_hdr, s_body = sut
    r_status, r_hdr, r_body = ref

    # Status code.
    sc, rc = status_code(s_status), status_code(r_status)
    if sc != rc:
        divs.append({"kind": "status", "detail": f"sut={sc!r} ref={rc!r}",
                     "sut_status": s_status, "ref_status": r_status})

    sh, rh = norm_headers(s_hdr), norm_headers(r_hdr)

    # Header presence (skip pure-noise presence headers).
    s_keys = set(sh) - VOLATILE_PRESENCE
    r_keys = set(rh) - VOLATILE_PRESENCE
    for k in sorted(r_keys - s_keys):
        divs.append({"kind": "missing-header", "detail": f"{k}: {rh[k]}"})
    for k in sorted(s_keys - r_keys):
        divs.append({"kind": "extra-header", "detail": f"{k}: {sh[k]}"})

    # Header VALUE mismatch for headers both emit (non-volatile value only).
    for k in sorted(s_keys & r_keys):
        if k in VOLATILE_VALUE:
            continue
        if sh[k] != rh[k]:
            divs.append({"kind": "header-value",
                         "detail": f"{k}: sut={sh[k]} ref={rh[k]}"})

    # Body: compare length and, if small, content. Big bodies compare by
    # length + sha to avoid dumping.
    if s_body != r_body:
        import hashlib
        if len(s_body) != len(r_body):
            divs.append({"kind": "body-length",
                         "detail": f"sut={len(s_body)} ref={len(r_body)}"})
        else:
            divs.append({
                "kind": "body-bytes",
                "detail": f"len={len(s_body)} sut_sha={hashlib.sha256(s_body).hexdigest()[:12]} "
                          f"ref_sha={hashlib.sha256(r_body).hexdigest()[:12]}",
            })
    return divs


# ---------------------------------------------------------------------------
def build_corpus(host, sp, rp):
    """Return list of (id, category, description, raw_bytes). The Host header
    value is filled per-server at send time via {HOST} placeholder."""
    H = "{HOST}"
    C = []

    def add(cid, cat, desc, raw):
        C.append((cid, cat, desc, raw))

    def req(method, target, extra="", body=b"", host_hdr=True, close=True):
        lines = [f"{method} {target} HTTP/1.1"]
        if host_hdr:
            lines.append(f"Host: {H}")
        if close:
            lines.append("Connection: close")
        if extra:
            lines.append(extra)
        blob = ("\r\n".join(lines) + "\r\n\r\n").encode("latin-1") + body
        return blob

    # --- static GET: content types & basics ------------------------------
    add("get-index-html", "static", "GET /static/index.html", req("GET", "/static/index.html"))
    add("get-hello-txt", "static", "GET /static/hello.txt", req("GET", "/static/hello.txt"))
    add("get-data-json", "static", "GET /static/data.json", req("GET", "/static/data.json"))
    add("get-style-css", "static", "GET /static/style.css", req("GET", "/static/style.css"))
    add("get-script-js", "static", "GET /static/script.js", req("GET", "/static/script.js"))
    add("get-no-ext", "static", "GET /static/no-ext (unknown type)", req("GET", "/static/no-ext"))
    add("get-empty", "static", "GET /static/empty.txt (0 bytes)", req("GET", "/static/empty.txt"))
    add("get-sub-page", "static", "GET /static/sub/page.html", req("GET", "/static/sub/page.html"))
    add("get-hidden", "static", "GET /static/.hidden.txt (dotfile)", req("GET", "/static/.hidden.txt"))
    add("get-space", "static", "GET /static/sp%20ace.txt (encoded space)", req("GET", "/static/sp%20ace.txt"))
    add("get-utf8", "static", "GET /static/caf%C3%A9.txt (utf8 name)", req("GET", "/static/caf%C3%A9.txt"))

    # --- directory & index behaviour -------------------------------------
    add("get-dir-slash", "dir", "GET /static/ (root dir)", req("GET", "/static/"))
    add("get-subdir-slash", "dir", "GET /static/sub/ (subdir)", req("GET", "/static/sub/"))
    add("get-subdir-noslash", "dir", "GET /static/sub (no trailing slash)", req("GET", "/static/sub"))

    # --- not found / errors ----------------------------------------------
    add("get-404", "notfound", "GET /static/nope.txt (missing)", req("GET", "/static/nope.txt"))
    add("get-404-nostatic", "notfound", "GET /nowhere (outside static prefix)", req("GET", "/nowhere"))
    add("get-root", "notfound", "GET / (bare root)", req("GET", "/"))

    # --- HEAD -------------------------------------------------------------
    add("head-index", "head", "HEAD /static/index.html", req("HEAD", "/static/index.html"))
    add("head-404", "head", "HEAD /static/nope.txt", req("HEAD", "/static/nope.txt"))
    add("head-hello", "head", "HEAD /static/hello.txt", req("HEAD", "/static/hello.txt"))

    # --- methods ----------------------------------------------------------
    add("post-static", "method", "POST /static/hello.txt (unsupported on file)",
        req("POST", "/static/hello.txt", extra="Content-Length: 0"))
    add("put-static", "method", "PUT /static/hello.txt", req("PUT", "/static/hello.txt", extra="Content-Length: 0"))
    add("delete-static", "method", "DELETE /static/hello.txt", req("DELETE", "/static/hello.txt"))
    add("options-static", "method", "OPTIONS /static/hello.txt", req("OPTIONS", "/static/hello.txt"))
    add("options-star", "method", "OPTIONS *", req("OPTIONS", "*"))
    add("trace-static", "method", "TRACE /static/hello.txt", req("TRACE", "/static/hello.txt"))
    add("bogus-method", "method", "FROB /static/hello.txt (unknown method)", req("FROB", "/static/hello.txt"))
    add("lowercase-method", "method", "get /static/hello.txt (lowercase method)", req("get", "/static/hello.txt"))

    # --- conditional GET --------------------------------------------------
    add("cond-inm-star", "conditional", "GET If-None-Match: * ",
        req("GET", "/static/hello.txt", extra="If-None-Match: *"))
    add("cond-ims-future", "conditional", "GET If-Modified-Since (future)",
        req("GET", "/static/hello.txt", extra="If-Modified-Since: Sat, 01 Jan 2050 00:00:00 GMT"))
    add("cond-ims-past", "conditional", "GET If-Modified-Since (past)",
        req("GET", "/static/hello.txt", extra="If-Modified-Since: Thu, 01 Jan 1970 00:00:00 GMT"))
    add("cond-inm-bogus", "conditional", 'GET If-None-Match: "bogus"',
        req("GET", "/static/hello.txt", extra='If-None-Match: "does-not-match"'))

    # --- range requests ---------------------------------------------------
    add("range-first16", "range", "GET Range: bytes=0-15",
        req("GET", "/static/big.bin", extra="Range: bytes=0-15"))
    add("range-mid", "range", "GET Range: bytes=100-199",
        req("GET", "/static/big.bin", extra="Range: bytes=100-199"))
    add("range-suffix", "range", "GET Range: bytes=-100 (suffix)",
        req("GET", "/static/big.bin", extra="Range: bytes=-100"))
    add("range-openend", "range", "GET Range: bytes=204700- (open end)",
        req("GET", "/static/big.bin", extra="Range: bytes=204700-"))
    add("range-unsat", "range", "GET Range: bytes=999999999-1000000000 (unsatisfiable)",
        req("GET", "/static/big.bin", extra="Range: bytes=999999999-1000000000"))
    add("range-multi", "range", "GET Range: bytes=0-9,20-29 (multipart)",
        req("GET", "/static/big.bin", extra="Range: bytes=0-9,20-29"))
    add("range-bad-unit", "range", "GET Range: items=0-15 (bad unit)",
        req("GET", "/static/big.bin", extra="Range: items=0-15"))

    # --- gzip / content negotiation --------------------------------------
    add("gzip-lorem", "encoding", "GET Accept-Encoding: gzip (compressible)",
        req("GET", "/static/lorem.txt", extra="Accept-Encoding: gzip"))
    add("gzip-hello", "encoding", "GET Accept-Encoding: gzip (tiny)",
        req("GET", "/static/hello.txt", extra="Accept-Encoding: gzip"))
    add("gzip-identity", "encoding", "GET Accept-Encoding: identity",
        req("GET", "/static/lorem.txt", extra="Accept-Encoding: identity"))
    add("gzip-star", "encoding", "GET Accept-Encoding: *",
        req("GET", "/static/lorem.txt", extra="Accept-Encoding: *"))

    # --- path traversal / security ---------------------------------------
    add("trav-dotdot", "security", "GET /static/../outside/secret.txt",
        req("GET", "/static/../outside/secret.txt"))
    add("trav-enc-dotdot", "security", "GET /static/%2e%2e/outside/secret.txt (encoded)",
        req("GET", "/static/%2e%2e/outside/secret.txt"))
    add("trav-deep", "security", "GET /static/../../../../etc/passwd",
        req("GET", "/static/../../../../etc/passwd"))
    add("trav-doubleslash", "security", "GET /static//sub//page.html (double slash)",
        req("GET", "/static//sub//page.html"))
    add("trav-dot", "security", "GET /static/./hello.txt (single dot)",
        req("GET", "/static/./hello.txt"))
    add("trav-nul", "security", "GET /static/hello.txt%00.png (nul byte)",
        req("GET", "/static/hello.txt%00.png"))
    add("trav-backslash", "security", "GET /static/sub\\page.html (backslash)",
        req("GET", "/static/sub\\page.html"))

    # --- malformed / protocol edge cases ---------------------------------
    add("no-host", "malformed", "GET /static/hello.txt with NO Host header (HTTP/1.1)",
        req("GET", "/static/hello.txt", host_hdr=False))
    add("http-1-0", "malformed", "GET HTTP/1.0 (no Host)",
        b"GET /static/hello.txt HTTP/1.0\r\nConnection: close\r\n\r\n")
    add("dup-host", "malformed", "GET with two Host headers",
        b"GET /static/hello.txt HTTP/1.1\r\nHost: a\r\nHost: b\r\nConnection: close\r\n\r\n")
    add("bad-version", "malformed", "GET HTTP/9.9 (bad version)",
        b"GET /static/hello.txt HTTP/9.9\r\nHost: {HOST}\r\nConnection: close\r\n\r\n")
    add("space-in-target", "malformed", "GET with space in target (invalid request line)",
        b"GET /static/hel lo.txt HTTP/1.1\r\nHost: {HOST}\r\nConnection: close\r\n\r\n")
    add("bare-lf", "malformed", "GET with bare-LF line endings",
        b"GET /static/hello.txt HTTP/1.1\nHost: {HOST}\nConnection: close\n\n")
    add("garbage-line", "malformed", "non-HTTP garbage",
        b"THIS IS NOT HTTP AT ALL\r\n\r\n")
    add("empty-request", "malformed", "empty request (just CRLFCRLF)", b"\r\n\r\n")
    add("huge-target", "malformed", "GET with 8KB target (URI too long)",
        ("GET /static/" + "a" * 8000 + " HTTP/1.1\r\nHost: {HOST}\r\nConnection: close\r\n\r\n").encode()),
    add("cl-post", "malformed", "POST with body and Content-Length",
        req("POST", "/api", extra="Content-Length: 5", body=b"hello"))

    # --- reverse proxy ----------------------------------------------------
    add("proxy-api", "proxy", "GET /api (reverse-proxy route)", req("GET", "/api"))
    add("proxy-api-path", "proxy", "GET /api/users (proxy subpath)", req("GET", "/api/users"))
    add("proxy-api-post", "proxy", "POST /api (proxy w/ body)",
        req("POST", "/api", extra="Content-Length: 4", body=b"data"))

    return C


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default=os.environ.get("DIFF_HOST", "127.0.0.1"))
    ap.add_argument("--sut-port", type=int, default=env_port("SUT_PORT", 18930),
                    help="default: $SUT_PORT, else 18930")
    ap.add_argument("--ref-port", type=int, default=env_port("REF_PORT", 18931),
                    help="default: $REF_PORT, else 18931")
    ap.add_argument("--json", default=None)
    ap.add_argument("--show-same", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    # --- precondition: both endpoints are live HTTP servers ---------------
    # Runs BEFORE the corpus. Exits 2 if either side cannot answer.
    assert_live(args.host, [("sut", args.sut_port), ("ref", args.ref_port)])

    corpus = build_corpus(args.host, args.sut_port, args.ref_port)

    results = []
    n_div = 0
    faults = []          # infrastructure faults: the request never landed
    for cid, cat, desc, raw in corpus:
        sut_raw, sut_err = recv_all(args.host, args.sut_port,
                                    raw.replace(b"{HOST}", f"{args.host}:{args.sut_port}".encode()))
        ref_raw, ref_err = recv_all(args.host, args.ref_port,
                                    raw.replace(b"{HOST}", f"{args.host}:{args.ref_port}".encode()))
        for side, err in (("sut", sut_err), ("ref", ref_err)):
            if is_transport_fault(err):
                faults.append({"id": cid, "side": side, "error": err})
        sut = sut_err if sut_err else parse_response(sut_raw)
        ref = ref_err if ref_err else parse_response(ref_raw)
        divs = compare(sut, ref)
        results.append({"id": cid, "category": cat, "desc": desc,
                        "divergences": divs,
                        "sut_status": (sut[0] if isinstance(sut, tuple) else f"ERR:{sut}"),
                        "ref_status": (ref[0] if isinstance(ref, tuple) else f"ERR:{ref}")})
        if divs:
            n_div += 1

    # --- report -----------------------------------------------------------
    print(f"\n=== differential: {len(corpus)} requests, SUT :{args.sut_port} vs REF :{args.ref_port} ===\n")
    for r in results:
        if not r["divergences"] and not args.show_same:
            continue
        mark = "DIVERGE" if r["divergences"] else "same"
        print(f"[{mark}] {r['id']}  ({r['category']})  {r['desc']}")
        if r["divergences"]:
            print(f"    sut: {r['sut_status']}")
            print(f"    ref: {r['ref_status']}")
            for d in r["divergences"]:
                print(f"    - {d['kind']}: {d['detail']}")
        print()

    # --- infrastructure faults invalidate the run -------------------------
    # A connect/send failure mid-run means a server went away under us: the
    # remaining requests were never delivered, so the divergence count below
    # is not a measurement of anything. Say so, loudly, and fail.
    if faults:
        sides = sorted({f["side"] for f in faults})
        print("")
        print("=" * 72)
        print(f"FATAL: {len(faults)} transport fault(s) during the run "
              f"({', '.join(sides)} went unreachable).")
        for f in faults[:10]:
            print(f"  {f['side']:3s} {f['id']}: {f['error']}")
        if len(faults) > 10:
            print(f"  ... and {len(faults) - 10} more")
        print("  The run is INVALID — requests that never landed cannot agree.")
        print("=" * 72)
        if args.json:
            with open(args.json, "w") as f:
                json.dump({"invalid": True, "faults": faults, "results": results},
                          f, indent=2)
            print(f"wrote {args.json}")
        return 2

    print(f"=== {n_div}/{len(corpus)} requests diverged (each divergence = a mapped gap) ===")

    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, indent=2)
        print(f"wrote {args.json}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
