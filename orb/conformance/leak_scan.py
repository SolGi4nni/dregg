#!/usr/bin/env python3
"""Information-disclosure leak-scan gate for the drorb serve.

Drives EVERY known route (health, bulk, static, 404, admin, api, root,
conditional, HEAD, error responses) plus a corpus of adversarial requests, and
FAILS if any response leaks an internal or dangerous artifact:

  L1  request-byte reflection   the serve echoes raw request bytes back in a
                                response header (literal OR dotted-decimal /
                                hex encoded) — request-content disclosure.
  L2  internal header           a response carries an internal/debug header the
                                outside world must never see (x-corr, x-upstream,
                                and the usual debug-banner names).
  L3  stack trace / source leak the body exposes a panic, backtrace, source-file
                                path, or runtime internal.
  L4  server-version banner     the Server header advertises a product/version
                                beyond the bare policy token, or an X-Powered-By
                                / X-Runtime style banner is present.

This is the gate the RFC core (17/17) and extended (21/21) suites structurally
MISS. The extended N2 amplification check only inspects `GET /health`, where the
serve does not stamp `x-corr`; the request-byte-echo header appears on the
static-file path instead, so the leak sails through green. And `x-upstream` — a
per-response internal-address disclosure on EVERY route — is never checked at
all. This battery drives every route x every leak-class, closing the hole.

Usage:
    python3 conformance/leak_scan.py                 # launch the default serve, scan, report
    python3 conformance/leak_scan.py --target H:P    # scan a serve already listening on H:P
    python3 conformance/leak_scan.py --port 18990    # launch on a specific port

Exit code:
    0  clean — no route leaked any class
    1  at least one leak found (the finding IS the deliverable — do NOT tune to pass)
    2  harness error — the serve would not start / is unreachable

Env:
    DRORB_LEAK_PORT   port to launch/scan on (default 18990)
    HACL_DIST         EverCrypt gcc-compatible dist (needed to launch the serve)
"""
import argparse
import json
import os
import re
import socket
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATAPLANE = os.path.join(REPO, "target", "release", "dataplane")

# A high-entropy token we inject into request bytes (path query, custom header,
# User-Agent). If it comes back in ANY response header — literally, dotted-decimal,
# or hex — the serve reflected request content.
MARKER = "Zq7LeakPr0be9x"
MARKERB = MARKER.encode()
MARKER_DOTDEC = ".".join(str(b) for b in MARKERB)          # x-corr's encoding
MARKER_HEX = MARKERB.hex()

# Header names that must NEVER appear on a response to an outside client. `x-corr`
# and `x-upstream` are the two the deployed serve currently stamps; the rest are
# the common debug/internal banners a hardened edge must also refuse to emit.
INTERNAL_HEADERS = {
    b"x-corr", b"x-upstream", b"x-debug", b"x-internal", b"x-trace",
    b"x-backend", b"x-backend-server", b"x-cache-key", b"x-served-by",
    b"x-source", b"x-real-backend", b"x-forwarded-server", b"x-node",
    b"x-worker", b"x-pid", b"x-request-body", b"x-orig-request",
}
# Banner headers that disclose the implementation product/version/runtime.
BANNER_HEADERS = {
    b"x-powered-by", b"x-aspnet-version", b"x-aspnetmvc-version",
    b"x-runtime", b"x-generator", b"x-drupal-cache",
}
# Server header policy: the ONLY acceptable value is this bare product token.
# Anything with a version, slash, build string, or a different product leaks.
POLICY_SERVER = b"drorb"

# Body patterns that betray a stack trace / source path / runtime internal.
TRACE_PATTERNS = [
    re.compile(rb"panic", re.I),
    re.compile(rb"thread '", re.I),
    re.compile(rb"backtrace", re.I),
    re.compile(rb"RUST_BACKTRACE", re.I),
    re.compile(rb"\.rs:\d+", re.I),
    re.compile(rb"stack overflow", re.I),
    re.compile(rb"index out of bounds", re.I),
    re.compile(rb"unwrap\(\)|called `Option::unwrap|called `Result::unwrap", re.I),
    re.compile(rb"note: run with", re.I),
    re.compile(rb"/home/[a-z]+/|/Users/[a-z]+/", re.I),
    re.compile(rb"segmentation fault|SIGSEGV|SIGABRT", re.I),
]

HOST = "127.0.0.1"
PORT = int(os.environ.get("DRORB_LEAK_PORT", "18990"))


# --------------------------------------------------------------------------- #
# Raw HTTP client (full byte control, reads lower-case headers the serve emits)
# --------------------------------------------------------------------------- #
def raw(req, timeout=5.0, cap=1 << 20):
    """Send raw bytes on a fresh connection; return all bytes until close/timeout.
    b"" = peer closed with no data; None = connection refused."""
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


def header_lines(head):
    """[(lower-name, raw-value)] for every response header line after the status."""
    out = []
    for line in head.split(b"\r\n")[1:]:
        if b":" in line:
            name, _, val = line.partition(b":")
            out.append((name.strip().lower(), val.strip()))
    return out


def decode_dotted(val):
    """If `val` is a dotted-decimal byte sequence (e.g. `71.69.84...`), decode it
    back to the original bytes; else None. This un-masks the x-corr encoding."""
    parts = val.split(b".")
    if len(parts) < 4:
        return None
    try:
        nums = [int(p) for p in parts]
    except ValueError:
        return None
    if any(n < 0 or n > 255 for n in nums):
        return None
    return bytes(nums)


# --------------------------------------------------------------------------- #
# The route battery. Each entry: (name, description, raw-request-bytes).
# MARKER is woven into a subset so L1 reflection can be pinned to a known token.
# --------------------------------------------------------------------------- #
def battery():
    def req(line, headers=None, body=b""):
        h = "".join(f"{k}: {v}\r\n" for k, v in (headers or {}).items())
        return f"{line}\r\nHost: {HOST}:{PORT}\r\n{h}Connection: close\r\n\r\n".encode() + body

    marker_hdrs = {"X-Probe": MARKER, "User-Agent": MARKER, "X-Trace-Id": MARKER}
    # A per-run cache-buster so static/conditional routes deterministically hit the
    # ORIGIN serve path (a fresh key = a cache miss) rather than a warmed variant.
    # Without this the x-corr origin-path leak appears or hides depending on request
    # ordering / cache state; the gate must fail the SAME way every run.
    cb = os.urandom(6).hex()
    return [
        ("health",            "liveness endpoint",            req("GET /health HTTP/1.1")),
        ("health-marked",     "health + marker in headers",   req("GET /health?q=" + MARKER + " HTTP/1.1", marker_hdrs)),
        ("root",              "site root",                    req("GET / HTTP/1.1")),
        ("bulk",              "bulk endpoint",                req("GET /bulk HTTP/1.1")),
        ("static",            "static asset",                 req(f"GET /static/app.js?cb={cb}1 HTTP/1.1")),
        ("static-marked",     "static + marker in headers",   req(f"GET /static/app.js?cb={cb}2&v=" + MARKER + " HTTP/1.1", marker_hdrs)),
        ("static-missing",    "static 404 path",              req("GET /static/does-not-exist.js HTTP/1.1")),
        ("notfound",          "unknown route (404)",          req("GET /no-such-xyz-" + MARKER + " HTTP/1.1")),
        ("admin",             "admin surface probe",          req("GET /admin HTTP/1.1", marker_hdrs)),
        ("api",               "api surface probe",            req("GET /api HTTP/1.1", marker_hdrs)),
        ("head-health",       "HEAD health",                  req("HEAD /health HTTP/1.1")),
        ("head-static",       "HEAD static",                  req(f"HEAD /static/app.js?cb={cb}3 HTTP/1.1")),
        ("cond-inm",          "conditional If-None-Match",    req(f"GET /static/app.js?cb={cb}4 HTTP/1.1", {"If-None-Match": '"deadbeef"'})),
        ("cond-ims",          "conditional If-Modified-Since",req(f"GET /static/app.js?cb={cb}5 HTTP/1.1", {"If-Modified-Since": "Wed, 21 Oct 2099 07:28:00 GMT"})),
        ("options",           "OPTIONS root",                 req("OPTIONS / HTTP/1.1")),
        ("trace",             "TRACE (must not echo)",        req("TRACE / HTTP/1.1", marker_hdrs)),
        ("weird-method",      "unknown method",               req("FROBNICATE /health HTTP/1.1", marker_hdrs)),
        ("bad-version",       "bogus HTTP version",           req("GET /health HTTP/9.9")),
        ("traversal-dotdot",  "path traversal (..)",          req("GET /static/../../../../etc/passwd HTTP/1.1")),
        ("traversal-encoded", "path traversal (%2e)",         req("GET /static/%2e%2e/%2e%2e/etc/passwd HTTP/1.1")),
        ("null-path",         "NUL in path",                  req("GET /%00 HTTP/1.1")),
        ("query-reflect",     "marker in query only",         req("GET /health?reflectme=" + MARKER + " HTTP/1.1")),
        ("big-head",          "oversized header + marker",    req("GET /health HTTP/1.1", {"X-Big": "A" * 4096, "X-Probe": MARKER})),
        ("malformed-line",    "garbage request line",         b"GET\t/health\tHTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"),
        ("bare-lf",           "bare-LF request",              b"GET /health HTTP/1.1\nHost: x\nX-Probe: " + MARKERB + b"\n\n"),
    ]


# --------------------------------------------------------------------------- #
# Leak-class evaluators. Each returns a list of evidence strings (empty = clean).
# --------------------------------------------------------------------------- #
def scan_L1_reflection(resp, marker_injected):
    """Raw request bytes echoed in a response header (literal or encoded)."""
    ev = []
    head, _ = split_head(resp)
    for name, val in header_lines(head):
        low = val.lower()
        # Marker reflection (only meaningful when we injected it).
        if marker_injected:
            if MARKERB.lower() in low:
                ev.append(f"{name.decode()}: reflects marker literally")
            elif MARKER_DOTDEC.encode() in val:
                ev.append(f"{name.decode()}: reflects marker as dotted-decimal")
            elif MARKER_HEX.encode() in low:
                ev.append(f"{name.decode()}: reflects marker as hex")
        # Generic: a dotted-decimal header value that decodes to request bytes.
        dec = decode_dotted(val)
        if dec is not None and (b"HTTP/" in dec or b"Host:" in dec or dec.startswith(b"GET ")
                                or dec.startswith(b"HEAD ") or b"User-Agent" in dec):
            snippet = dec[:48].decode("latin1", "replace")
            ev.append(f"{name.decode()}: decodes to raw request head -> {snippet!r}...")
    # De-dup while preserving order.
    seen, out = set(), []
    for e in ev:
        if e not in seen:
            seen.add(e); out.append(e)
    return out


def scan_L2_internal(resp):
    ev = []
    head, _ = split_head(resp)
    for name, _ in header_lines(head):
        if name in INTERNAL_HEADERS:
            ev.append(f"internal header present: {name.decode()}")
    return ev


def scan_L3_trace(resp):
    ev = []
    _, body = split_head(resp)
    for pat in TRACE_PATTERNS:
        m = pat.search(body)
        if m:
            ev.append(f"body matches {pat.pattern.decode('latin1')!r}: {m.group(0).decode('latin1','replace')!r}")
    return ev


def scan_L4_banner(resp):
    ev = []
    head, _ = split_head(resp)
    for name, val in header_lines(head):
        if name == b"server" and val != POLICY_SERVER:
            ev.append(f"Server banner beyond policy: {val.decode('latin1','replace')!r} (policy = {POLICY_SERVER.decode()!r})")
        if name in BANNER_HEADERS:
            ev.append(f"version/runtime banner header: {name.decode()}: {val.decode('latin1','replace')!r}")
    return ev


CLASSES = [
    ("L1", "request-byte-reflection", scan_L1_reflection),
    ("L2", "internal-header",         scan_L2_internal),
    ("L3", "stack-trace",             scan_L3_trace),
    ("L4", "server-banner",           scan_L4_banner),
]


# --------------------------------------------------------------------------- #
# Serve lifecycle
# --------------------------------------------------------------------------- #
def wait_tcp(port, tries=60):
    for _ in range(tries):
        try:
            with socket.create_connection((HOST, port), timeout=0.3):
                return True
        except OSError:
            time.sleep(0.1)
    return False


def launch_serve():
    if not os.path.exists(DATAPLANE):
        print(f"HARNESS ERROR: dataplane binary missing at {DATAPLANE}", file=sys.stderr)
        sys.exit(2)
    env = dict(os.environ)
    env["DRORB_EFFECT_SEAM"] = "1"
    env.setdefault("HACL_DIST", os.path.join(os.path.expanduser("~"), "src", "hacl-star", "dist", "gcc-compatible"))
    env["LIBRARY_PATH"] = env["HACL_DIST"] + ":" + env.get("LIBRARY_PATH", "")
    proc = subprocess.Popen(
        [DATAPLANE, "--bind", f"{HOST}:{PORT}", "--no-udp", "--io", "blocking"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env, cwd=REPO)
    if not wait_tcp(PORT):
        proc.terminate()
        print(f"HARNESS ERROR: serve did not come up on {HOST}:{PORT}", file=sys.stderr)
        sys.exit(2)
    return proc


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #
def main():
    global HOST, PORT
    ap = argparse.ArgumentParser(description="drorb info-disclosure leak-scan gate")
    ap.add_argument("--target", help="scan a serve already listening at HOST:PORT (skip launch)")
    ap.add_argument("--port", type=int, default=PORT, help="port to launch/scan on")
    ap.add_argument("--json", metavar="PATH", help="also write machine-readable results here")
    args = ap.parse_args()

    proc = None
    if args.target:
        HOST, PORT = args.target.rsplit(":", 1)
        PORT = int(PORT)
        if not wait_tcp(PORT, tries=10):
            print(f"HARNESS ERROR: no serve at {HOST}:{PORT}", file=sys.stderr)
            sys.exit(2)
    else:
        PORT = args.port
        proc = launch_serve()

    routes = battery()
    marker_routes = {"health-marked", "static-marked", "admin", "api", "trace",
                     "weird-method", "query-reflect", "big-head", "notfound", "bare-lf"}
    results = []
    try:
        for name, desc, req in routes:
            resp = raw(req)
            row = {"route": name, "desc": desc, "reachable": resp is not None,
                   "status": None, "leaks": {}}
            if resp:
                sl = resp.split(b"\r\n", 1)[0]
                m = re.match(rb"HTTP/\d\.\d (\d{3})", sl)
                row["status"] = int(m.group(1)) if m else None
            for cid, cname, fn in CLASSES:
                if cid == "L1":
                    ev = fn(resp, name in marker_routes) if resp else []
                else:
                    ev = fn(resp) if resp else []
                if ev:
                    row["leaks"][cid] = ev
            results.append(row)
    finally:
        if proc is not None:
            proc.terminate()
            try:
                proc.wait(timeout=4)
            except subprocess.TimeoutExpired:
                proc.kill()

    # --- Report ---------------------------------------------------------- #
    print("=" * 78)
    print(f"drorb leak-scan  —  {len(routes)} routes x {len(CLASSES)} leak-classes  @ {HOST}:{PORT}")
    print("=" * 78)
    hdr = f"{'route':<20} {'status':>6}  " + "  ".join(c[0] for c in CLASSES)
    print(hdr)
    print("-" * len(hdr))
    total_leaks = 0
    for row in results:
        cells = []
        for cid, _, _ in CLASSES:
            if cid in row["leaks"]:
                cells.append("LEAK")
                total_leaks += len(row["leaks"][cid])
            else:
                cells.append("  . ")
        st = row["status"] if row["status"] is not None else ("--" if row["reachable"] else "DOWN")
        print(f"{row['route']:<20} {str(st):>6}  " + "  ".join(cells))
    print("-" * len(hdr))
    print("classes: " + " | ".join(f"{c[0]}={c[1]}" for c in CLASSES))

    # --- Itemized findings ----------------------------------------------- #
    leaking = [r for r in results if r["leaks"]]
    print()
    if leaking:
        print(f"FINDINGS — {len(leaking)} route(s) leaked, {total_leaks} evidence item(s):")
        for row in leaking:
            print(f"\n  [{row['route']}]  {row['desc']}  (HTTP {row['status']})")
            for cid, ev in row["leaks"].items():
                for e in ev:
                    print(f"      {cid}  {e}")
    else:
        print("no leaks found.")

    print()
    verdict = "FAIL" if leaking else "PASS"
    print(f"VERDICT: {verdict}  ({len(leaking)}/{len(routes)} routes leak)")

    if args.json:
        with open(args.json, "w") as f:
            json.dump({"host": HOST, "port": PORT, "verdict": verdict,
                       "routes": len(routes), "classes": [c[1] for c in CLASSES],
                       "results": results}, f, indent=2)
        print(f"wrote {args.json}")

    sys.exit(1 if leaking else 0)


if __name__ == "__main__":
    main()
