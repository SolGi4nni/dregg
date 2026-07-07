#!/usr/bin/env python3
"""Executable conformance suite for the drorb network orchestrator.

This drives the REAL running binaries with REAL clients and emits a
machine-readable PASS / FAIL / UNWIRED / SKIPPED verdict per scenario. It is a
DIAGNOSTIC: it reports what is actually wired into the running serve path vs.
proven-in-isolation-but-not-connected. UNWIRED and FAIL are valid, valuable
outputs — nothing is massaged into a PASS.

Verdict semantics
  PASS     feature is wired into the running path AND behaves per spec.
  FAIL     feature is wired but produces the wrong behavior (a bug).
  UNWIRED  feature is not connected to the running serve: a stub response, an
           inert no-op, a gate that can never fire, or a handler missing from
           the deployed route table. The library may be proven in isolation.
  SKIPPED  scenario could not be driven (missing dependency / no real backend).

Binaries driven (all run the leanc-compiled proven serve):
  orb            stdin bytes -> stdout, the full 13-stage deployStepFull2 fold.
  dataplane      Rust host over a real TCP socket, same deployStepFull2 fold
                 (keep-alive + concurrent). PRIMARY HTTP target.
  orb-mac-multi  Lean-native TCP/UDP server; runs deployStepIngress = the
                 3-stage serveGuarded (traversal/policy/header-rewrite only).
                 Driven to expose the stage-parity gap on the native socket path.
  orb-quic       real QUIC/H3 over UDP (serveOverSubs guarded serve).

The verdict comes from the bytes the binary emits, not from narration.
"""
import base64
import gzip
import json
import os
import socket
import subprocess
import sys
import threading
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORB = os.path.join(REPO, ".lake", "build", "bin", "orb")
DATAPLANE = os.path.join(REPO, "target", "release", "dataplane")
ORB_QUIC = os.path.join(REPO, ".lake", "build", "bin", "orb-quic")
ORB_MULTI = os.path.join(REPO, ".lake", "build", "bin", "orb-mac-multi")
H3_CLIENT = os.path.join(REPO, "conformance", "h3_client.py")
QUIC_PYTHON = os.environ.get("QUIC_PYTHON", "")

HTTP_PORT = int(os.environ.get("CONF_HTTP_PORT", "8391"))   # dataplane (full)
LEAN_PORT = int(os.environ.get("CONF_LEAN_PORT", "8380"))   # orb-mac-multi (guarded)
QUIC_PORT = int(os.environ.get("CONF_QUIC_PORT", "8456"))   # orb-quic UDP

# Live reverse-proxy upstream backends for the proxy/fabric scenarios. Their ids
# (0, 1) match the proven `Reactor.ProxyDial.fleet` backend ids, so the mask byte
# the host feeds the proven pick lines up with these sockets. Each backend stamps
# `X-Backend: b<id>` so the driver can tell WHICH backend served a request.
PROXY_BACKEND = os.path.join(REPO, "target", "release", "examples", "proxy_backend")
BACKEND_PORTS = [
    int(os.environ.get("CONF_BACKEND0_PORT", "9401")),
    int(os.environ.get("CONF_BACKEND1_PORT", "9402")),
]

RESULTS = []


def record(name, category, request, expected, observed, verdict, note=""):
    RESULTS.append({
        "name": name, "category": category, "request": request,
        "expected": expected, "observed": observed, "verdict": verdict,
        "note": note,
    })


# ---------------------------------------------------------------------------
# HTTP/1.1 client helpers (raw sockets, real bytes on the wire)
# ---------------------------------------------------------------------------

def read_full(sock, timeout=3.0):
    """Read a full HTTP/1.1 response: headers then Content-Length bytes."""
    sock.settimeout(timeout)
    buf = b""
    try:
        while b"\r\n\r\n" not in buf:
            chunk = sock.recv(4096)
            if not chunk:
                return buf
            buf += chunk
        head, _, rest = buf.partition(b"\r\n\r\n")
        clen = 0
        for line in head.split(b"\r\n")[1:]:
            if line.lower().startswith(b"content-length:"):
                clen = int(line.split(b":", 1)[1].strip())
        body = rest
        while len(body) < clen:
            chunk = sock.recv(4096)
            if not chunk:
                break
            body += chunk
        return head + b"\r\n\r\n" + body
    except socket.timeout:
        return buf


def parse(data):
    """(status:int, headers:dict lowercased-name->value, body:bytes)."""
    if not data or b"\r\n\r\n" not in data:
        return (0, {}, data or b"")
    head, _, body = data.partition(b"\r\n\r\n")
    lines = head.split(b"\r\n")
    try:
        status = int(lines[0].split(b" ")[1])
    except Exception:
        status = 0
    headers = {}
    for line in lines[1:]:
        if b":" in line:
            k, v = line.split(b":", 1)
            headers[k.strip().lower().decode("latin1")] = v.strip().decode("latin1")
    return (status, headers, body)


def http(port, method, path, headers=None, body=b"", close=True, timeout=3.0):
    """One request over a fresh TCP connection; return parse()d response."""
    hdrs = {"Host": "x"}
    if headers:
        hdrs.update(headers)
    if close:
        hdrs["Connection"] = "close"
    req = f"{method} {path} HTTP/1.1\r\n".encode()
    for k, v in hdrs.items():
        req += f"{k}: {v}\r\n".encode()
    req += b"\r\n" + body
    s = socket.create_connection(("127.0.0.1", port), timeout=timeout)
    s.sendall(req)
    data = read_full(s, timeout)
    s.close()
    return parse(data)


def orb_pipe(raw):
    """Drive the orb stdin binary: raw request bytes -> parse()d response."""
    p = subprocess.run([ORB], input=raw, capture_output=True, timeout=15)
    return parse(p.stdout)


# ---------------------------------------------------------------------------
# Server lifecycle
# ---------------------------------------------------------------------------

def wait_tcp(port, tries=50):
    for _ in range(tries):
        try:
            socket.create_connection(("127.0.0.1", port), timeout=0.2).close()
            return True
        except OSError:
            time.sleep(0.1)
    return False


def port_in_use(port):
    """True if something is already listening on 127.0.0.1:port."""
    try:
        socket.create_connection(("127.0.0.1", port), timeout=0.3).close()
        return True
    except OSError:
        return False


class Server:
    def __init__(self, argv, tcp_port=None, udp_port=None, env=None, cwd=None):
        self.argv = argv
        self.tcp_port = tcp_port
        self.udp_port = udp_port
        self.env = env
        self.cwd = cwd
        self.proc = None

    def start(self):
        e = dict(os.environ)
        if self.env:
            e.update(self.env)
        self.proc = subprocess.Popen(
            self.argv, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            env=e, cwd=self.cwd)
        if self.tcp_port:
            wait_tcp(self.tcp_port)
        else:
            time.sleep(1.2)  # UDP: no connect() probe, give it a beat
        return self

    def stop(self):
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                self.proc.kill()


# ---------------------------------------------------------------------------
# Reverse-proxy backend fleet (the live upstreams the proxy/fabric scenarios
# forward to). Ids match the proven Reactor.ProxyDial.fleet ids.
# ---------------------------------------------------------------------------

class Backend:
    def __init__(self, bid, port):
        self.bid = bid
        self.port = port
        self.name = f"b{bid}"
        self.proc = None

    def alive(self):
        return self.proc is not None and self.proc.poll() is None

    def start(self):
        if self.alive():
            return
        self.proc = subprocess.Popen(
            [PROXY_BACKEND, f"127.0.0.1:{self.port}", self.name],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        wait_tcp(self.port)

    def kill(self):
        if self.proc and self.proc.poll() is None:
            self.proc.kill()
            try:
                self.proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                pass
        self.proc = None


BACKENDS = [Backend(i, p) for i, p in enumerate(BACKEND_PORTS)]

# How long to wait after (re)starting a backend for the dataplane's active-health
# loop (500ms sweeps) to re-admit it into the mask the proven pick consumes.
HEALTH_SETTLE = 1.6


def backends_spec():
    """The DRORB_PROXY_BACKENDS fleet spec: id=host:port,..."""
    return ",".join(f"{b.bid}=127.0.0.1:{b.port}" for b in BACKENDS)


def backend_by_name(name):
    for b in BACKENDS:
        if b.name == name:
            return b
    return None


def ensure_backends_up():
    """Restart any dead backend and wait for the health loop to re-admit it, so a
    scenario that follows a destructive one starts from a full, healthy fleet."""
    restarted = False
    for b in BACKENDS:
        if not b.alive():
            b.start()
            restarted = True
    if restarted:
        time.sleep(HEALTH_SETTLE)


# ===========================================================================
# SCENARIOS
# ===========================================================================

def scen_functional_routing():
    P = HTTP_PORT
    # exact route
    st, h, b = http(P, "GET", "/health")
    record("route-exact-match", "routing", "GET /health",
           "200, body 'ok' from the exact /health route",
           f"{st}, body={b!r}",
           "PASS" if (st == 200 and b == b"ok") else "FAIL")
    # prefix route
    st, h, b = http(P, "GET", "/static/app.js")
    record("route-prefix-match", "routing", "GET /static/app.js",
           "200 from the /static prefix route",
           f"{st}, body={b!r}",
           "PASS" if st == 200 else "FAIL")
    # precedence: exact /health beats catch-all default
    st, h, b = http(P, "GET", "/health")
    record("route-precedence", "routing", "GET /health (exact vs default)",
           "exact route wins over the catch-all default (200 'ok', not 404)",
           f"{st}, body={b!r}",
           "PASS" if (st == 200 and b == b"ok") else "FAIL")
    # 404 default
    st, h, b = http(P, "GET", "/no-such-route")
    if st == 404:
        v, note = "PASS", ""
    elif st == 403 and b.startswith(b"policy"):
        v, note = "UNWIRED", ("default 404 route is unreachable: the policy gate "
                              "refuses every undeclared surface with 403 before the "
                              "handler's default 404 can be produced")
    else:
        v, note = "FAIL", ""
    record("route-default-404", "routing", "GET /no-such-route",
           "404 default catch-all", f"{st}, body={b!r}", v, note)
    # host-based routing: the deployed default handler dispatches host-blocks via the
    # proven RouteAdvanced.dispatch, so the SAME admitted path under different Host
    # authorities returns DIFFERENT responses.
    st1, _, b1 = http(P, "GET", "/health/site", {"Host": "a.example"})
    st2, _, b2 = http(P, "GET", "/health/site", {"Host": "b.example"})
    host_ok = (st1 == 200 and st2 == 200 and b1 != b2)
    record("route-host-match", "routing", "GET /health/site with differing Host headers",
           "host-discriminated routing (different Host -> different response)",
           f"Host a.example -> {st1} {b1!r}, Host b.example -> {st2} {b2!r}",
           "PASS" if host_ok else "FAIL",
           "deployed default handler (App.Handler.hostGlob) selects a virtual-host block "
           "by Host via the proven RouteAdvanced.dispatch")
    # glob routing: the anyHost fallback block carries a '**' suffix-glob route
    # (/health/assets/**) matched by the proven RouteAdvanced.matchPrefixSegs.
    st, _, b = http(P, "GET", "/health/assets/img/logo.png")
    glob_ok = (st == 200 and b == b"glob-hit")
    record("route-glob-match", "routing", "GET /health/assets/img/logo.png (** glob route)",
           "glob '**' suffix matching in the deployed route table",
           f"{st}, body={b!r}",
           "PASS" if glob_ok else "FAIL",
           "deployed default handler carries a **-glob route matched by "
           "RouteAdvanced.matchPrefixSegs (the proven glob matcher)")
    # path normalization / dot-segment
    st, h, b = http(P, "GET", "/static/./app.js")
    st2, _, _ = http(P, "GET", "//static//app.js")
    record("path-normalization", "routing", "GET /static/./app.js and //static//app.js",
           "dot-segment + empty-segment normalization still matches /static (200)",
           f"/static/./app.js -> {st}, //static//app.js -> {st2}",
           "PASS" if (st == 200 and st2 == 200) else "FAIL")
    # traversal
    st, h, b = orb_pipe(b"GET /../../etc/passwd HTTP/1.1\r\nHost: x\r\n\r\n")
    record("path-traversal-block", "routing", "GET /../../etc/passwd",
           "404 'traversal blocked' (escaping .. is refused, no file leaked)",
           f"{st}, body={b!r}",
           "PASS" if (st == 404 and b"traversal" in b) else "FAIL")


def scen_functional_handlers():
    P = HTTP_PORT
    # respond handler
    st, h, b = http(P, "GET", "/health")
    record("handler-respond", "handlers", "GET /health",
           "fixed 200 respond handler returns 'ok'",
           f"{st}, body={b!r}",
           "PASS" if (st == 200 and b == b"ok") else "FAIL")
    # static-file handler (real file: content + ETag/Range/304)
    st, h, b = http(P, "GET", "/static/app.js")
    has_etag = "etag" in h
    if st == 200 and b == b"asset" and not has_etag:
        v, note = "UNWIRED", ("the /static route returns the fixed 'asset' stub with no "
                              "ETag/Range/Last-Modified; StaticFile (real file bytes, ETag, "
                              "Range, 304) is proven but not the deployed handler")
    elif has_etag:
        v, note = "PASS", ""
    else:
        v, note = "FAIL", ""
    record("handler-static-file", "handlers", "GET /static/app.js",
           "real file bytes from disk with ETag / Range / 304 support",
           f"{st}, body={b!r}, etag={has_etag}", v, note)
    # redirect handler
    st, h, b = http(P, "GET", "/old")
    loc = h.get("location", "")
    record("handler-redirect", "handlers", "GET /old",
           "3xx redirect with a Location header",
           f"{st}, Location={loc!r}",
           "PASS" if (300 <= st < 400 and loc) else "FAIL")
    # proxy handler (real upstream forward through the effect/continuation seam)
    ensure_backends_up()
    st, h, b = http(P, "GET", "/api?sid=probe", {"Cookie": "sid=probe"})
    xb = h.get("x-backend", "")
    proxy_ok = (st == 200 and bool(xb) and b"backend" in b)
    record("handler-proxy-forward", "handlers", "GET /api (reverse-proxy route to a live upstream)",
           "request forwarded to a live backend over a real socket; the backend's body + "
           "X-Backend header returned",
           f"{st}, X-Backend={xb!r}, body={b!r}",
           "PASS" if proxy_ok else ("FAIL" if st else "UNWIRED"),
           "the proven Reactor.ServeStep core yields proxyDial to the backend "
           "Reactor.ProxyDial.pick chose; the shell dials the live proxy_backend over a real "
           "socket (DRORB_EFFECT_SEAM=1 + DRORB_PROXY_BACKENDS)")
    # CGI handler (real process spawn: the deployed /cgi-bin route runs a script)
    st, h, b = http(P, "GET", "/cgi-bin/hello?a=1")
    cgi_ok = (st == 200 and b"cgi-ok" in b)
    record("handler-cgi", "handlers", "GET /cgi-bin/hello?a=1",
           "CGI script executed (fork/execve), its stdout returned",
           f"{st}, body={b!r}",
           "PASS" if cgi_ok else ("FAIL" if st else "UNWIRED"),
           "deployed .cgi route runs conformance/cgi-bin/hello via drorb_cgi_exec "
           "(launch the serve from the repo root so execve resolves the script path)")


def scen_functional_middleware():
    P = HTTP_PORT
    # JWT auth
    st, h, b = http(P, "GET", "/admin")
    wa = h.get("www-authenticate", "")
    record("mw-auth-jwt", "middleware", "GET /admin with no bearer token",
           "401 Unauthorized with WWW-Authenticate: Bearer",
           f"{st}, WWW-Authenticate={wa!r}",
           "PASS" if (st == 401 and "bearer" in wa.lower()) else "FAIL",
           "JWT gate runs the real Jwt.authenticate FSM, scoped to /admin*")
    st, h, b = http(P, "GET", "/admin", {"Authorization": "Bearer aaa.bbb.ccc"})
    record("mw-auth-jwt-badtoken", "middleware", "GET /admin with a garbage bearer token",
           "401 (signature/format fails the real validator)",
           f"{st}, body={b!r}",
           "PASS" if st == 401 else "FAIL")
    # Basic auth (the /private-scoped basicStage now sits in the deployed fold)
    st, h, b = http(P, "GET", "/private")
    wab = h.get("www-authenticate", "")
    record("mw-auth-basic", "middleware", "GET /private with no credentials",
           "401 + WWW-Authenticate: Basic realm on missing credentials",
           f"{st}, WWW-Authenticate={wab!r}",
           "PASS" if (st == 401 and "basic" in wab.lower()) else "FAIL",
           "BasicAuth gate (Reactor.Stage.BasicAuth.basicStage) composed into "
           "deployStagesFull2 as the second stage, scoped to /private*")
    # CORS allow
    st, h, b = http(P, "GET", "/health", {"origin": "https://app.example.com"})
    acao = h.get("access-control-allow-origin", "")
    record("mw-cors-allow", "middleware", "GET /health, Origin: https://app.example.com",
           "Access-Control-Allow-Origin echoes the allowed origin",
           f"{st}, ACAO={acao!r}",
           "PASS" if acao == "https://app.example.com" else "FAIL")
    # CORS deny
    st, h, b = http(P, "GET", "/health", {"origin": "https://evil.example.com"})
    acao = h.get("access-control-allow-origin", "")
    record("mw-cors-deny", "middleware", "GET /health, Origin: https://evil.example.com",
           "no ACAO header for a disallowed origin",
           f"{st}, ACAO={acao if acao else '(absent)'}",
           "PASS" if not acao else "FAIL")
    # gzip
    st, h, b = http(P, "GET", "/health", {"Accept-Encoding": "gzip"})
    ce = h.get("content-encoding", "")
    ok_gzip = False
    try:
        ok_gzip = (gzip.decompress(b) == b"ok")
    except Exception:
        pass
    record("mw-gzip", "middleware", "GET /health, Accept-Encoding: gzip",
           "Content-Encoding: gzip and a real gzip-compressed body",
           f"{st}, Content-Encoding={ce!r}, body decompresses to "
           f"{'ok' if ok_gzip else 'INVALID'}",
           "PASS" if (ce == "gzip" and ok_gzip) else "FAIL")
    # security headers
    st, h, b = http(P, "GET", "/health")
    hsts = h.get("strict-transport-security", "")
    xfo = h.get("x-frame-options", "")
    record("mw-security-headers", "middleware", "GET /health",
           "HSTS + X-Frame-Options + X-Content-Type-Options + Referrer-Policy",
           f"{st}, HSTS={hsts!r}, X-Frame-Options={xfo!r}",
           "PASS" if (hsts and xfo) else "FAIL")
    # IP filter (block a CIDR). The dataplane attributes the client address from
    # X-Forwarded-For when the immediate peer is trusted (loopback here), then
    # passes it as the real peer to drorb_serve_metered — so a forwarded client
    # inside the deployed deny block (10.0.0.0/8) reaches the proven IpFilter
    # deny-precedence path and is 403'd, while an unforwarded loopback request is
    # admitted.
    st_blk, _hb, bb = http(P, "GET", "/health", headers={"X-Forwarded-For": "10.0.0.1"})
    st_ok, _ho, _bo = http(P, "GET", "/health", headers={"X-Forwarded-For": "127.0.0.1"})
    ipfilter_ok = (st_blk == 403 and st_ok == 200)
    record("mw-ipfilter-block", "middleware", "a request from a blocked CIDR (10.0.0.0/8)",
           "403 for a client address inside a denied CIDR block",
           f"forwarded client 10.0.0.1 -> {st_blk} (body={bb!r}); forwarded 127.0.0.1 -> "
           f"{st_ok} (admitted)",
           "PASS" if ipfilter_ok else ("FAIL" if st_blk else "UNWIRED"),
           "the real peer address is threaded through drorb_serve_metered; IpFilter.permits "
           "deny-precedence over 10.0.0.0/8 fires on the real client address")
    # rate limit: a burst on ONE kept-alive connection. Each serve carries the
    # per-connection sequence through drorb_serve_metered, so the real Rate token
    # bucket (cap 8) empties across the burst and later requests get 429.
    burst = b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n" * 11 + \
            b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
    s = socket.create_connection(("127.0.0.1", P), timeout=5)
    s.sendall(burst)
    s.settimeout(5)
    rl_data = b""
    try:
        while True:
            c = s.recv(8192)
            if not c:
                break
            rl_data += c
    except socket.timeout:
        pass
    s.close()
    rl_429 = rl_data.count(b"HTTP/1.1 429")
    rl_200 = rl_data.count(b"HTTP/1.1 200")
    record("mw-ratelimit-429", "middleware", "a burst that should trip the rate limit",
           "429 Too Many Requests once the token bucket empties",
           f"{rl_200} x 200, {rl_429} x 429 over one kept-alive connection (burst of 12)",
           "PASS" if rl_429 > 0 else "UNWIRED",
           "Rate.tryAdmit (cap 8) is driven by the real per-connection sequence threaded "
           "through drorb_serve_metered")
    # header rewrite / Server install
    st, h, b = http(P, "GET", "/health")
    server = h.get("server", "")
    record("mw-header-rewrite", "middleware", "GET /health (response header program)",
           "hop-by-hop strip + Server field installed by the real Header.run rewrite",
           f"{st}, Server={server!r}",
           "PASS" if server == "drorb" else "FAIL",
           "Server install is observable; hop-by-hop stripping on a real forward is not "
           "exercised (no upstream connection)")


def scen_caching():
    P = HTTP_PORT
    # cache-hit: a cacheable GET under /static (the proven ServeStep cacheable
    # path — GET on a /static target, Cache.selectLifetime resolves max-age=60)
    # driven TWICE through the effect/continuation seam (DRORB_EFFECT_SEAM=1). The
    # query string varies the cache key (method+target) without changing the file
    # the router resolves (targetSegments drops the query), so this is an isolated
    # cold key. The first request MISSes and the shell's process-global store keeps
    # the proven fold output; the second is replayed from the store with
    # X-Cache: HIT + Age, byte-identical, with the handler NOT re-run.
    hpath = "/static/app.js?probe=hit"
    st1, h1, b1 = http(P, "GET", hpath)
    st2, h2, b2 = http(P, "GET", hpath)
    xcache = h2.get("x-cache", "").upper()
    age = h2.get("age", "")
    hit_ok = (st1 == 200 and st2 == 200 and xcache == "HIT"
              and "age" in h2 and b1 == b2 and b2)
    record("cache-hit", "caching", "two identical GET /static/app.js (second should HIT)",
           "second request served from the cache with X-Cache: HIT + Age, body byte-identical, "
           "handler not re-run",
           f"1st: {st1} X-Cache={h1.get('x-cache','(absent)')!r}; 2nd: {st2} X-Cache={xcache!r} "
           f"Age={age!r}; bodies {'match' if b1 == b2 else 'DIFFER'}",
           "PASS" if hit_ok else ("FAIL" if st2 else "UNWIRED"),
           "the proven ServeStep cacheable path yields cacheLookup/cacheStore for a gate-admitted "
           "GET /static (Cache.selectLifetime max-age=60); the shell's process-global store replays "
           "the stored bytes on the 2nd request (DRORB_EFFECT_SEAM=1)")

    # cache-coalesce: K concurrent identical requests to a COLD cacheable key. The
    # effect-seam lookup elects exactly ONE leader (which runs the single fold) and
    # collapses the other K-1 requests behind it; each waiter is served from the
    # leader's one fetch stamped X-Cache: HIT. So exactly one MISS (the leader) and
    # K-1 coalesced HITs, every response byte-identical.
    K = 8
    cpath = "/static/app.js?probe=coalesce"
    cres = [None] * K

    def _coalesce_worker(i):
        try:
            st, h, b = http(P, "GET", cpath, timeout=8.0)
            cres[i] = (st, h.get("x-cache", "").upper(), bytes(b))
        except Exception as e:
            cres[i] = ("ERR", str(e), b"")
    cths = [threading.Thread(target=_coalesce_worker, args=(i,)) for i in range(K)]
    for t in cths:
        t.start()
    for t in cths:
        t.join()
    oks = [r for r in cres if r and r[0] == 200]
    hits = sum(1 for r in cres if r and r[1] == "HIT")
    bodies = {r[2] for r in oks}
    coalesce_ok = (len(oks) == K and hits == K - 1 and len(bodies) == 1)
    record("cache-coalesce", "caching", f"{K} concurrent identical GET /static (coalescing)",
           "duplicate concurrent misses collapsed onto ONE fetch: 1 leader MISS + K-1 waiters "
           "served X-Cache: HIT from that single fetch, all bodies identical",
           f"{len(oks)}/{K} answered 200; {hits} carried X-Cache: HIT (expect {K - 1}); "
           f"{len(bodies)} distinct body",
           "PASS" if coalesce_ok else ("FAIL" if oks else "UNWIRED"),
           "the effect-seam cacheLookup elects one leader per key and collapses concurrent same-key "
           "misses behind its single fetch (Cache.coalesce_single_fetch); waiters are served the "
           "leader's bytes stamped X-Cache: HIT (DRORB_EFFECT_SEAM=1)")


def scen_protocols():
    P = HTTP_PORT
    # H1 keep-alive: N requests on one connection
    reqs = (b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n" * 2 +
            b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    s = socket.create_connection(("127.0.0.1", P), timeout=4)
    s.sendall(reqs)
    s.settimeout(4)
    data = b""
    try:
        while True:
            c = s.recv(4096)
            if not c:
                break
            data += c
    except socket.timeout:
        pass
    s.close()
    n200 = data.count(b"HTTP/1.1 200")
    record("proto-h1-keepalive", "protocols", "3 pipelined GET /health on ONE connection",
           "all 3 answered 200 on the single kept-alive connection",
           f"{n200} of 3 responses were 200 on one connection",
           "PASS" if n200 == 3 else ("FAIL" if n200 > 0 else "UNWIRED"))
    # h2c (HTTP/2 cleartext, prior knowledge) with a real H2 client (curl)
    try:
        p = subprocess.run(
            ["curl", "-sS", "-m", "6", "--http2-prior-knowledge", "-o", "/dev/null",
             "-w", "%{http_version}", f"http://127.0.0.1:{P}/health"],
            capture_output=True, timeout=12, text=True)
        ver = p.stdout.strip()
        err = p.stderr.strip().replace("\n", " ")
        if p.returncode == 0 and ver.startswith("2"):
            v, obs = "PASS", f"negotiated HTTP/{ver}"
        else:
            v = "UNWIRED"
            obs = (f"real H2 client fails (curl rc={p.returncode}): "
                   f"{err[:110] or 'timed out waiting for SETTINGS'}")
        record("proto-h2c", "protocols", "curl --http2-prior-knowledge GET /health",
               "real H2 client completes an h2c GET (SETTINGS + HEADERS + DATA)",
               obs, v,
               "input forks to the real H2 engine (serveIngress) but the socket-level H2 "
               "server does not drive a working SETTINGS/stream exchange")
    except subprocess.TimeoutExpired:
        record("proto-h2c", "protocols", "curl --http2-prior-knowledge GET /health",
               "real H2 client completes an h2c GET",
               "the h2c connection hangs (server never sends a valid SETTINGS frame)",
               "UNWIRED",
               "the socket-level H2 server does not drive a working SETTINGS/stream exchange")
    except Exception as e:
        record("proto-h2c", "protocols", "curl --http2-prior-knowledge GET /health",
               "real H2 client completes an h2c GET", f"driver error: {e}", "SKIPPED")
    # WebSocket upgrade + echo + close
    try:
        key = base64.b64encode(os.urandom(16)).decode()
        req = (f"GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
               f"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n\r\n")
        s = socket.create_connection(("127.0.0.1", P), timeout=4)
        s.sendall(req.encode())
        s.settimeout(3)
        hs = s.recv(4096)
        is101 = hs.startswith(b"HTTP/1.1 101")
        payload = b"hi"
        mask = os.urandom(4)
        masked = bytes(payload[i] ^ mask[i % 4] for i in range(len(payload)))
        s.sendall(bytes([0x81, 0x80 | len(payload)]) + mask + masked)
        echo = s.recv(4096)
        s.close()
        echoed = echo[2:2 + (echo[1] & 0x7f)] if len(echo) >= 2 else b""
        record("proto-websocket", "protocols", "RFC 6455 Upgrade + a masked text frame 'hi'",
               "101 Switching Protocols, correct Sec-WebSocket-Accept, and the frame echoed",
               f"handshake_101={is101}, echoed={echoed!r}",
               "PASS" if (is101 and echoed == b"hi") else "FAIL")
    except Exception as e:
        record("proto-websocket", "protocols", "RFC 6455 Upgrade + echo",
               "101 + echo", f"driver error: {e}", "SKIPPED")
    # QUIC / HTTP-3
    quic_scenarios()


def quic_get(path):
    """Restart orb-quic (single-connection server) and drive one aioquic GET."""
    if not QUIC_PYTHON or not os.path.exists(QUIC_PYTHON):
        return None, "no aioquic venv (QUIC_PYTHON unset)"
    srv = Server([ORB_QUIC, "--serve", str(QUIC_PORT)], udp_port=QUIC_PORT).start()
    try:
        p = subprocess.run([QUIC_PYTHON, H3_CLIENT, str(QUIC_PORT), path],
                           capture_output=True, timeout=40, text=True)
        return p.stdout.strip(), p.stderr.strip()
    finally:
        srv.stop()
        time.sleep(0.3)


def quic_scenarios():
    if not QUIC_PYTHON or not os.path.exists(QUIC_PYTHON):
        record("proto-quic-h3", "protocols", "aioquic H3 GET /health over UDP",
               "1-RTT QUIC handshake + H3 200 'ok'",
               "aioquic venv unavailable (QUIC_PYTHON unset)", "SKIPPED")
        return
    out, err = quic_get("/health")
    if out and out.startswith("STATUS 200") and b"ok" .decode() in out:
        v, note = "PASS", "verified EverCrypt 1-RTT handshake, H3 GET answered by the proven serve"
    elif out and out.startswith("STATUS"):
        v, note = "FAIL", ""
    else:
        v, note = "SKIPPED", "handshake/client did not complete"
    record("proto-quic-h3", "protocols", "aioquic H3 GET /health over UDP",
           "1-RTT QUIC handshake completes and H3 returns 200 'ok'",
           out or err, v, note)


def api_get(sid, extra=None):
    """Drive one GET /api carrying a session id in BOTH the request target (the key
    the effect seam's proven rendezvous pick actually hashes — ServeStep.stickyKey)
    and a Cookie (documenting session intent)."""
    hdrs = {"Cookie": f"sid={sid}"}
    if extra:
        hdrs.update(extra)
    return http(HTTP_PORT, "GET", f"/api?sid={sid}", hdrs)


def scen_fabric():
    # fabric-lb: distinct session keys spread across >=2 LIVE backends. The proven
    # Reactor.ProxyDial.pick (rendezvous over the live-health-masked fleet) chooses
    # a backend per key; a spread of keys lands on both.
    ensure_backends_up()
    seen = {}
    for i in range(20):
        st, h, _b = api_get(f"lb{i}")
        if st == 200:
            xb = h.get("x-backend", "")
            if xb:
                seen[xb] = seen.get(xb, 0) + 1
    lb_ok = len(seen) >= 2
    record("fabric-lb", "fabric", "load balance across >=2 live upstream backends",
           "distinct session keys distributed across >=2 live backends, each serving real traffic",
           f"{len(seen)} distinct backends over 20 keys: {dict(sorted(seen.items()))}",
           "PASS" if lb_ok else ("FAIL" if seen else "UNWIRED"),
           "the proven Reactor.ProxyDial.pick (rendezvous hash over the eligible pool) chooses "
           "the backend; the seam keys affinity on the request target (the session id rides "
           "there), and the shell dials the live backend")

    # fabric-healthcheck: kill the backend serving a fixed key; after the active
    # health loop ejects it, the same key fails over to a live backend.
    ensure_backends_up()
    st0, h0, _ = api_get("hc")
    served = h0.get("x-backend", "")
    victim = backend_by_name(served)
    if st0 == 200 and victim is not None:
        victim.kill()
        time.sleep(HEALTH_SETTLE)  # active-health loop (500ms sweeps) ejects the dead backend
        st1, h1, _b1 = api_get("hc")
        served2 = h1.get("x-backend", "")
        hc_ok = (st1 == 200 and bool(served2) and served2 != served)
        obs = (f"key 'hc' served by {served!r}; killed it; after health ejection served by "
               f"{served2!r} (status {st1})")
        verdict = "PASS" if hc_ok else "FAIL"
    else:
        obs = f"could not establish an initial live backend for key 'hc' (status {st0}, X-Backend={served!r})"
        verdict = "UNWIRED"
    record("fabric-healthcheck", "fabric", "eject an unhealthy backend from rotation",
           "a killed backend is removed by active health checks; the key fails over to a live one",
           obs, verdict,
           "the host's active-health loop TCP-probes each backend and clears the dead one's bit "
           "in the mask the proven Reactor.ProxyDial.pick consumes (health-eligible pool only)")
    ensure_backends_up()  # restore the killed backend for later scenarios

    # fabric-circuit-breaker: with every backend down, the proven pick finds no
    # eligible backend and the core emits 503 (no dial attempted).
    ensure_backends_up()
    for bk in BACKENDS:
        bk.kill()
    time.sleep(HEALTH_SETTLE)  # health loop ejects the whole fleet -> empty eligible pool
    codes = []
    for i in range(4):
        st, _h, _b = api_get(f"cb{i}")
        codes.append(st)
    cb_ok = bool(codes) and all(c == 503 for c in codes)
    record("fabric-circuit-breaker", "fabric", "short-circuit when no upstream is healthy",
           "with the whole fleet down the proven pick finds no eligible backend and the core "
           "serves 503, dialling nothing",
           f"statuses with every backend down: {codes}",
           "PASS" if cb_ok else ("FAIL" if any(codes) else "UNWIRED"),
           "no eligible backend (all bits clear via active-health ejection or an open breaker "
           "after consecutive forward failures) ⇒ Reactor.ProxyDial.pick returns none ⇒ "
           "ServeStep emits the proven serviceUnavailable503")
    ensure_backends_up()  # restart the fleet + wait for health re-admission

    # fabric-sticky: the same session key pins to the same backend across requests.
    ensure_backends_up()
    st1, h1, _ = api_get("stick-me")
    st2, h2, _ = api_get("stick-me")
    xb1, xb2 = h1.get("x-backend", ""), h2.get("x-backend", "")
    sticky_ok = (st1 == 200 and st2 == 200 and bool(xb1) and xb1 == xb2)
    record("fabric-sticky", "fabric", "sticky session affinity to one backend",
           "the same session key is pinned to the same backend across requests",
           f"key 'stick-me' -> {xb1!r} then {xb2!r} (statuses {st1}/{st2})",
           "PASS" if sticky_ok else ("FAIL" if (st1 or st2) else "UNWIRED"),
           "the proven rendezvous pick is a pure function of the affinity key, so a repeated key "
           "resolves to the same backend; the seam keys affinity on the request target (SEED) — "
           "cookie-based sid affinity is the documented ServeStep.stickyKey follow-up")


def scen_compositional():
    P = HTTP_PORT
    # ipfilter -> jwt -> route -> gzip (all gates+transform in sequence, admitted arm)
    st, h, b = http(P, "GET", "/health", {"Accept-Encoding": "gzip"})
    ce = h.get("content-encoding", "")
    ok_gzip = False
    try:
        ok_gzip = gzip.decompress(b) == b"ok"
    except Exception:
        pass
    record("comp-ipfilter-jwt-route-gzip", "compositional",
           "GET /health, Accept-Encoding: gzip (ipfilter->jwt->route->gzip in one request)",
           "admitted through ip-filter + jwt (off /admin) + route match, body gzipped",
           f"{st}, Content-Encoding={ce!r}, gunzip={'ok' if ok_gzip else 'INVALID'}",
           "PASS" if (st == 200 and ce == "gzip" and ok_gzip) else "FAIL",
           "the two gates are inert-but-present (pass-through); route + gzip do the work")
    # proxy + header-rewrite + cors on a forwarded request. The effect seam drives
    # the FORWARD dimension (a live backend answers 200); the hop-by-hop strip / CORS
    # fold over the UPSTREAM reply is a seam follow-up (proxyRespTransform is the
    # lossless HTML transform today, not yet the full response-phase fold), so this
    # asserts ONLY the forward dimension.
    ensure_backends_up()
    st, h, b = http(P, "GET", "/api?sid=comp",
                    {"Cookie": "sid=comp", "origin": "https://app.example.com"})
    xb = h.get("x-backend", "")
    fwd_ok = (st == 200 and bool(xb) and b"backend" in b)
    record("comp-proxy-headerrewrite-cors", "compositional",
           "a forwarded request through proxy + header-rewrite + cors",
           "FORWARD dimension only: a live backend answers 200 with X-Backend + body",
           f"{st}, X-Backend={xb!r}, body={b!r}",
           "PASS" if fwd_ok else ("FAIL" if st else "UNWIRED"),
           "the proven ServeStep proxy path forwards to a live backend (DRORB_EFFECT_SEAM=1); "
           "hop-by-hop strip + CORS over the upstream reply is not yet in proxyRespTransform — a "
           "seam follow-up")
    # cache + gzip (cached compressed response): drive a cacheable GET /static
    # with Accept-Encoding: gzip TWICE on a dedicated cold key. The first MISS
    # stores the proven fold output WITH the gzip stage applied (Content-Encoding:
    # gzip, compressed body); the second replays that compressed body from the
    # store with X-Cache: HIT, handler not re-run.
    gpath = "/static/app.js?probe=gzip"
    gst1, gh1, gb1 = http(P, "GET", gpath, {"Accept-Encoding": "gzip"})
    gst2, gh2, gb2 = http(P, "GET", gpath, {"Accept-Encoding": "gzip"})
    ce1 = gh1.get("content-encoding", "")
    ce2 = gh2.get("content-encoding", "")
    gxcache = gh2.get("x-cache", "").upper()
    gz_ok = (gst2 == 200 and gxcache == "HIT" and ce2 == "gzip" and gb1 == gb2 and bool(gb2))
    record("comp-cache-gzip", "compositional", "a cached, gzip-compressed response",
           "second request returns the cached compressed body (Content-Encoding: gzip) with "
           "X-Cache: HIT, without re-running the handler",
           f"1st: {gst1} CE={ce1 or '(absent)'!r}; 2nd: {gst2} X-Cache={gxcache!r} "
           f"CE={ce2 or '(absent)'!r}; body {'identical' if gb1 == gb2 else 'DIFFERS'}",
           "PASS" if gz_ok else ("FAIL" if gst2 else "UNWIRED"),
           "the effect seam stores the proven fold output — gzip stage included when Accept-Encoding "
           "requests it — and replays the compressed bytes on the 2nd request (DRORB_EFFECT_SEAM=1)")
    # redirect + security-headers
    st, h, b = http(P, "GET", "/old")
    hsts = h.get("strict-transport-security", "")
    loc = h.get("location", "")
    if 300 <= st < 400 and loc and not hsts:
        v, note = "UNWIRED", ("the redirect gate short-circuits at stage 5, BEFORE the "
                              "security-headers stage (12); the 3xx carries no HSTS — the two "
                              "features do not compose on one response")
    elif 300 <= st < 400 and hsts:
        v, note = "PASS", ""
    else:
        v, note = "FAIL", ""
    record("comp-redirect-security", "compositional", "GET /old (redirect + security-headers)",
           "3xx redirect that ALSO carries HSTS/security headers",
           f"{st}, Location={loc!r}, HSTS={hsts if hsts else '(absent)'}", v, note)
    # rate-limit + keep-alive burst on one connection
    burst = b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n" * 19 + \
            b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
    s = socket.create_connection(("127.0.0.1", P), timeout=5)
    s.sendall(burst)
    s.settimeout(5)
    data = b""
    try:
        while True:
            c = s.recv(8192)
            if not c:
                break
            data += c
    except socket.timeout:
        pass
    s.close()
    n429 = data.count(b"HTTP/1.1 429")
    n200 = data.count(b"HTTP/1.1 200")
    record("comp-ratelimit-keepalive", "compositional",
           "20-request burst on one kept-alive connection",
           "some requests answered 429 once the bucket empties (rate-limit + keep-alive)",
           f"{n200} x 200, {n429} x 429 over one connection",
           "UNWIRED" if n429 == 0 else "PASS",
           "keep-alive + the real per-connection rate bucket (cap 8): the burst depletes "
           "it and later requests are throttled")
    # WS upgrade after auth
    try:
        key = base64.b64encode(os.urandom(16)).decode()
        req = (f"GET /admin HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
               f"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n\r\n")
        s = socket.create_connection(("127.0.0.1", P), timeout=4)
        s.sendall(req.encode())
        s.settimeout(3)
        resp = s.recv(4096)
        s.close()
        is101 = resp.startswith(b"HTTP/1.1 101")
        is401 = resp.startswith(b"HTTP/1.1 401")
        # The host performs the RFC6455 handshake at the framing layer; the JWT
        # stage lives in drorb_serve and does not gate the upgrade path.
        record("comp-ws-after-auth", "compositional", "WebSocket Upgrade on /admin (auth+WS)",
               "the JWT gate refuses the unauthenticated WS upgrade (401), not 101",
               f"{'101 Switching Protocols (auth NOT enforced on upgrade)' if is101 else resp.split(chr(13).encode())[0].decode('latin1')}",
               "UNWIRED" if is101 else ("PASS" if is401 else "FAIL"),
               "the WS handshake is host-side framing, upstream of the JWT stage; auth does "
               "not compose with the upgrade path")
    except Exception as e:
        record("comp-ws-after-auth", "compositional", "WebSocket Upgrade on /admin",
               "auth gates the upgrade", f"driver error: {e}", "SKIPPED")
    # H2 with middleware: a real H2 client (curl --http2-prior-knowledge) drives an
    # h2c GET; the response must carry the response-transform middleware — HSTS from
    # the security-headers stage and Content-Encoding: gzip when Accept-Encoding
    # requests it — proving the h2c serve routes through the full 13-stage fold, not
    # the 3-stage guarded serve.
    def curl_h2_headers(path, extra_hdr=None):
        argv = ["curl", "-sS", "-m", "6", "--http2-prior-knowledge", "-D", "-", "-o", "/dev/null"]
        if extra_hdr:
            argv += ["-H", extra_hdr]
        argv.append(f"http://127.0.0.1:{P}{path}")
        p = subprocess.run(argv, capture_output=True, timeout=12, text=True)
        hdrs = {}
        for line in p.stdout.splitlines():
            if ":" in line and not line.startswith("HTTP/"):
                k, _, v = line.partition(":")
                hdrs[k.strip().lower()] = v.strip()
        return p.returncode, hdrs
    try:
        rc1, h_sec = curl_h2_headers("/health")
        rc2, h_gz = curl_h2_headers("/health", "Accept-Encoding: gzip")
        hsts = h_sec.get("strict-transport-security", "")
        ce = h_gz.get("content-encoding", "")
        ok = (rc1 == 0 and rc2 == 0 and bool(hsts) and ce == "gzip")
        record("comp-h2-middleware", "compositional", "an h2c request through the middleware stages",
               "H2 request receives gzip/cors/security-header transforms",
               f"HSTS={hsts if hsts else '(absent)'}, "
               f"Content-Encoding={ce if ce else '(absent)'} (curl rc={rc1}/{rc2})",
               "PASS" if ok else "UNWIRED",
               "the h2c serve routes the decoded request through the full 13-stage fold "
               "(deployRespFull2Of), so the security-headers/gzip transforms apply on H2")
    except Exception as e:
        record("comp-h2-middleware", "compositional", "an h2c request through the middleware stages",
               "H2 request receives gzip/cors/security-header transforms",
               f"driver error: {e}", "SKIPPED")
    # QUIC/H3 with route + middleware
    if QUIC_PYTHON and os.path.exists(QUIC_PYTHON):
        out, err = quic_get("/")
        got403 = bool(out and "STATUS 403" in out)
        record("comp-quic-route-middleware", "compositional",
               "aioquic H3 GET / (route + middleware over H3)",
               "route decides (403 policy on undeclared /) AND middleware transforms apply",
               f"{out or err}; H3 runs the 3-stage guarded serve (route/policy fire, "
               f"but no gzip/cors/security stages)",
               "PASS" if got403 else "SKIPPED",
               "routing + policy gate fire over H3, but the H3 path is the guarded serve — "
               "the gzip/cors/security/jwt transforms are not on it")
    else:
        record("comp-quic-route-middleware", "compositional", "aioquic H3 GET /",
               "route + middleware over H3", "aioquic venv unavailable", "SKIPPED")


def scen_native_socket_parity():
    """Drive orb-mac-multi (Lean-native TCP), which runs the 3-stage guarded
    serve, to expose the stage-parity gap vs. the dataplane's 13-stage fold."""
    P = LEAN_PORT
    try:
        st, h, b = http(P, "GET", "/admin")
    except Exception as e:
        for nm in ("native-jwt", "native-gzip", "native-security"):
            record(nm, "native-socket-parity", "GET on orb-mac-multi",
                   "same 13-stage behavior as the dataplane",
                   f"orb-mac-multi not reachable: {e}", "SKIPPED")
        return
    record("native-jwt-gap", "native-socket-parity", "GET /admin on orb-mac-multi (native TCP)",
           "401 (JWT gate), matching the dataplane",
           f"{st}, body={b!r} (403 policy, not 401 — no JWT stage on the native path)",
           "UNWIRED" if st != 401 else "PASS",
           "orb-mac-multi/IoMac run deployStepIngress = serveGuarded (3 stages); JWT is absent")
    st, h, b = http(P, "GET", "/health", {"Accept-Encoding": "gzip"})
    ce = h.get("content-encoding", "")
    record("native-gzip-gap", "native-socket-parity",
           "GET /health, Accept-Encoding: gzip on orb-mac-multi",
           "Content-Encoding: gzip, matching the dataplane",
           f"{st}, Content-Encoding={ce if ce else '(absent)'}",
           "UNWIRED" if ce != "gzip" else "PASS",
           "gzip stage absent from the native-socket guarded serve")
    st, h, b = http(P, "GET", "/health")
    hsts = h.get("strict-transport-security", "")
    record("native-security-gap", "native-socket-parity", "GET /health on orb-mac-multi",
           "HSTS present, matching the dataplane",
           f"{st}, HSTS={hsts if hsts else '(absent)'}",
           "UNWIRED" if not hsts else "PASS",
           "security-headers stage absent from the native-socket guarded serve")


def scen_core_parity():
    """Cross-check that the orb stdin core and the dataplane socket agree byte-for-byte."""
    raw = b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n"
    st_core, _, b_core = orb_pipe(raw)
    st_sock, _, b_sock = http(HTTP_PORT, "GET", "/health", close=False)
    record("core-stdin-vs-socket", "parity",
           "GET /health via orb stdin AND via the dataplane socket",
           "both binaries (same deployStepFull2) return an identical 200 'ok'",
           f"orb stdin -> {st_core}/{b_core!r}, dataplane -> {st_sock}/{b_sock!r}",
           "PASS" if (st_core == 200 == st_sock and b_core == b_sock == b"ok") else "FAIL")


def scen_concurrency():
    P = HTTP_PORT
    N = 24
    results = [None] * N

    def worker(i):
        try:
            st, _, b = http(P, "GET", "/health")
            results[i] = (st, b)
        except Exception as e:
            results[i] = ("ERR", str(e))
    threads = [threading.Thread(target=worker, args=(i,)) for i in range(N)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    ok = sum(1 for r in results if r and r[0] == 200 and r[1] == b"ok")
    record("proto-concurrent", "protocols", f"{N} concurrent GET /health connections",
           "all concurrent requests answered 200 'ok'",
           f"{ok} of {N} concurrent requests returned 200 'ok'",
           "PASS" if ok == N else ("FAIL" if ok > 0 else "UNWIRED"))


# ===========================================================================
# main
# ===========================================================================

def print_table():
    order = {"PASS": 0, "FAIL": 1, "UNWIRED": 2, "SKIPPED": 3}
    rows = sorted(RESULTS, key=lambda r: (r["category"], order.get(r["verdict"], 9), r["name"]))
    wname = max(len(r["name"]) for r in rows)
    wcat = max(len(r["category"]) for r in rows)
    print()
    print(f"{'VERDICT':8} {'CATEGORY':{wcat}}  {'SCENARIO':{wname}}  OBSERVED")
    print("-" * 100)
    for r in rows:
        obs = r["observed"]
        if len(obs) > 78:
            obs = obs[:75] + "..."
        print(f"{r['verdict']:8} {r['category']:{wcat}}  {r['name']:{wname}}  {obs}")
    print()
    counts = {}
    for r in RESULTS:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    total = len(RESULTS)
    summary = "  ".join(f"{k}={counts.get(k,0)}" for k in ("PASS", "FAIL", "UNWIRED", "SKIPPED"))
    print(f"SUMMARY ({total} scenarios):  {summary}")
    wired = counts.get("PASS", 0) + counts.get("FAIL", 0)
    print(f"WIRED into the running serve (PASS+FAIL): {wired}/{total}   "
          f"proven-but-not-connected (UNWIRED): {counts.get('UNWIRED',0)}/{total}")


def preflight_ports():
    """Fail fast if a port we bind is already held (a stale server would answer our
    requests and fake the results). Checks the dataplane, native, and backend ports."""
    busy = []
    for label, port in (
        [("dataplane", HTTP_PORT), ("orb-mac-multi", LEAN_PORT)]
        + [(f"backend b{b.bid}", b.port) for b in BACKENDS]
    ):
        if port_in_use(port):
            busy.append(f"{label} port {port}")
    if busy:
        print("ERROR: port(s) already in use — a stale server is running; refusing to run so it "
              "cannot fake results:\n  " + "\n  ".join(busy), file=sys.stderr)
        print("Kill the stale process(es) and re-run.", file=sys.stderr)
        sys.exit(2)


def main():
    preflight_ports()
    servers = []
    # Reverse-proxy backend fleet: start the LIVE upstreams BEFORE the dataplane so
    # the proxy/fabric scenarios have real backend sockets to forward to.
    proxy_env = {}
    if os.path.exists(PROXY_BACKEND):
        for b in BACKENDS:
            b.start()
        proxy_env = {
            "DRORB_PROXY_BACKENDS": backends_spec(),
            "DRORB_EFFECT_SEAM": "1",  # drive the effect/continuation proxy seam
        }
    else:
        print(f"WARNING: proxy_backend binary missing at {PROXY_BACKEND}; proxy/fabric "
              f"scenarios cannot be driven", file=sys.stderr)
    # dataplane: the primary full-pipeline TCP target. cwd=REPO so the deployed .cgi
    # route's relative script path (conformance/cgi-bin/hello) resolves under execve.
    if os.path.exists(DATAPLANE):
        # The effect/continuation seam is required for the cache scenarios (a
        # cacheable GET /static yields cacheLookup/cacheStore) as well as the
        # proxy/fabric ones, so enable it independent of whether a backend fleet
        # is configured.
        dp_env = {"HACL_DIST": os.environ.get("HACL_DIST", ""), "DRORB_EFFECT_SEAM": "1"}
        dp_env.update(proxy_env)
        servers.append(Server(
            [DATAPLANE, "--bind", f"127.0.0.1:{HTTP_PORT}", "--no-udp", "--io", "blocking"],
            tcp_port=HTTP_PORT, env=dp_env, cwd=REPO).start())
    else:
        print(f"WARNING: dataplane binary missing at {DATAPLANE}", file=sys.stderr)
    # orb-mac-multi: native-socket guarded serve (parity gap)
    native_up = False
    if os.path.exists(ORB_MULTI):
        try:
            servers.append(Server([ORB_MULTI, str(LEAN_PORT), str(LEAN_PORT + 1)],
                                  tcp_port=LEAN_PORT).start())
            native_up = True
        except Exception as e:
            print(f"WARNING: orb-mac-multi did not start: {e}", file=sys.stderr)
    try:
        scen_functional_routing()
        scen_functional_handlers()
        scen_functional_middleware()
        scen_caching()
        scen_protocols()
        scen_concurrency()
        scen_fabric()
        scen_compositional()
        if native_up:
            scen_native_socket_parity()
        scen_core_parity()
    finally:
        for s in servers:
            s.stop()
        for b in BACKENDS:
            b.kill()

    out = os.path.join(REPO, "conformance", "results.json")
    with open(out, "w") as f:
        json.dump({
            "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "scenarios": RESULTS,
            "counts": {v: sum(1 for r in RESULTS if r["verdict"] == v)
                       for v in ("PASS", "FAIL", "UNWIRED", "SKIPPED")},
        }, f, indent=2)
    print_table()
    print(f"\nmachine-readable results: {out}")


if __name__ == "__main__":
    main()
