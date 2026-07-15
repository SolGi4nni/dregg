#!/usr/bin/env python3
"""Proxy / gateway (intermediary) conformance battery for the serve.

Exercises the upstream-forwarding path (the reverse-proxy lane) against the
RFC 9110 / RFC 7230 rules an HTTP intermediary must obey. It stands up its own
trivial upstream(s), launches the serve pointed at them (via DRORB_PROXY_BACKENDS),
and drives raw-socket HTTP requests through the proxy route (/api...), inspecting
BOTH what the client received AND what the upstream actually saw (the upstream
echoes the exact request bytes it received back in its response body).

This is a NEW, standalone battery. Failures on missing/partial intermediary
features are EXPECTED and are the point: they form the gap map. Nothing here is
tuned to pass.

Checks (RFC 9110 §7.6.x, RFC 7230 §5.7 / §6.1):
  a) hop-by-hop request headers STRIPPED before forwarding
     (Connection + its listed tokens, Transfer-Encoding, Keep-Alive, TE,
      Upgrade, Proxy-Connection)
  b) Via header added to the forwarded request (and to the response)
  c) X-Forwarded-For / Forwarded added (if applicable)
  d) 502 on upstream connect-fail; 504 on upstream timeout
  e) end-to-end headers preserved (both directions)
  f) request body forwarded (fixed Content-Length AND chunked)
  g) response body streamed intact

Run: python3 battery.py [--serve /path/to/dataplane] [--base-port 18950]
Honest pass/fail only; every result comes from a real request this script sent.
"""

import argparse
import json
import os
import socket
import subprocess
import sys
import threading
import time

# ---------------------------------------------------------------------------
# Trivial upstream: echoes the exact request bytes it received into its response
# body so the client can inspect what the intermediary forwarded. Special paths
# override the behaviour (slow / chunked-response / large-body / custom header).
# ---------------------------------------------------------------------------

class Upstream:
    def __init__(self, port):
        self.port = port
        self.srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.srv.bind(("127.0.0.1", port))
        self.srv.listen(64)
        self.stop = False
        self.t = threading.Thread(target=self._loop, daemon=True)

    def start(self):
        self.t.start()

    def close(self):
        self.stop = True
        try:
            self.srv.close()
        except OSError:
            pass

    def _read_full_request(self, c):
        """Read a full HTTP/1.1 request: head, then Content-Length or chunked body."""
        buf = b""
        c.settimeout(3.0)
        try:
            while b"\r\n\r\n" not in buf:
                d = c.recv(65536)
                if not d:
                    return buf
                buf += d
            head_end = buf.index(b"\r\n\r\n") + 4
            head = buf[:head_end]
            lower = head.lower()
            # Fixed length
            clen = None
            for line in head.split(b"\r\n"):
                if line.lower().startswith(b"content-length:"):
                    try:
                        clen = int(line.split(b":", 1)[1].strip())
                    except ValueError:
                        clen = None
            if clen is not None:
                while len(buf) - head_end < clen:
                    d = c.recv(65536)
                    if not d:
                        break
                    buf += d
                return buf
            if b"transfer-encoding:" in lower and b"chunked" in lower:
                # read until terminating 0-length chunk
                while b"0\r\n\r\n" not in buf[head_end:]:
                    d = c.recv(65536)
                    if not d:
                        break
                    buf += d
                return buf
            return buf
        except socket.timeout:
            return buf

    def _loop(self):
        while not self.stop:
            try:
                c, _ = self.srv.accept()
            except OSError:
                return
            threading.Thread(target=self._handle, args=(c,), daemon=True).start()

    def _handle(self, c):
        try:
            req = self._read_full_request(c)
            target = b""
            if req:
                first = req.split(b"\r\n", 1)[0].split(b" ")
                if len(first) >= 2:
                    target = first[1]

            if target.startswith(b"/api/slow"):
                time.sleep(1.5)  # exceed the 500ms upstream read timeout
                body = b"slow-ok"
                resp = (b"HTTP/1.1 200 OK\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s"
                        % (len(body), body))
                c.sendall(resp)
            elif target.startswith(b"/api/chunkedresp"):
                head = (b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n"
                        b"Transfer-Encoding: chunked\r\nConnection: close\r\n\r\n")
                c.sendall(head)
                for part in (b"hello ", b"chunked ", b"world"):
                    c.sendall(b"%x\r\n%s\r\n" % (len(part), part))
                c.sendall(b"0\r\n\r\n")
            elif target.startswith(b"/api/big"):
                payload = (b"X" * 1024) * 100  # 100 KiB
                head = (b"HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\n"
                        b"Content-Length: %d\r\nConnection: close\r\n\r\n" % len(payload))
                c.sendall(head + payload)
            elif target.startswith(b"/api/close"):
                # accept then close with no response head: passes the connect-only
                # health probe but fails the actual forward -> exercises the
                # dial/forward-fail -> 502 path (distinct from pool-empty 503).
                pass  # fall through to finally: close immediately
            elif target.startswith(b"/api/e2ehdr"):
                body = b"e2e-body"
                resp = (b"HTTP/1.1 200 OK\r\nContent-Length: %d\r\n"
                        b"X-Custom-End: value123\r\nETag: \"abc\"\r\n"
                        b"Connection: close\r\n\r\n%s" % (len(body), body))
                c.sendall(resp)
            else:
                # echo mode: reflect the exact received request bytes into the body
                body = req
                resp = (b"HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\n"
                        b"X-Upstream: yes\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s"
                        % (len(body), body))
                c.sendall(resp)
        except OSError:
            pass
        finally:
            try:
                c.close()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Raw HTTP client helpers
# ---------------------------------------------------------------------------

def send_raw(port, raw, timeout=4.0, read_all=True):
    """Send raw bytes to 127.0.0.1:port, return the full response bytes."""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(timeout)
    out = b""
    try:
        s.connect(("127.0.0.1", port))
        s.sendall(raw)
        while True:
            try:
                d = s.recv(65536)
            except socket.timeout:
                break
            if not d:
                break
            out += d
            if not read_all:
                break
    except OSError as e:
        return b"", str(e)
    finally:
        try:
            s.close()
        except OSError:
            pass
    return out, None


def split_head_body(resp):
    idx = resp.find(b"\r\n\r\n")
    if idx < 0:
        return resp, b""
    return resp[:idx], resp[idx + 4:]


def status_of(resp):
    line = resp.split(b"\r\n", 1)[0]
    parts = line.split(b" ")
    if len(parts) >= 2 and parts[1].isdigit():
        return int(parts[1])
    return None


def header_present(head, name):
    n = name.lower().encode()
    for line in head.split(b"\r\n")[1:]:
        if line.lower().startswith(n + b":"):
            return line.split(b":", 1)[1].strip()
    return None


# ---------------------------------------------------------------------------
# Serve process management
# ---------------------------------------------------------------------------

class Serve:
    def __init__(self, serve_bin, bind_port, backends, logpath):
        env = dict(os.environ)
        env["DRORB_PROXY_BACKENDS"] = backends
        env.pop("DRORB_EFFECT_SEAM", None)  # keep the established proxy hook lane
        self.log = open(logpath, "wb")
        # The reverse-proxy forwarding lane is wired in the blocking IO backend;
        # the uring/kqueue fast paths serve /api locally, so force blocking here.
        self.p = subprocess.Popen(
            [serve_bin, "--bind", "127.0.0.1:%d" % bind_port, "--no-udp", "--io", "blocking"],
            env=env, stdout=self.log, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, start_new_session=True,
        )
        self.port = bind_port

    def wait_ready(self, timeout=10.0):
        deadline = time.time() + timeout
        while time.time() < deadline:
            if self.p.poll() is not None:
                return False
            s = socket.socket()
            s.settimeout(0.5)
            try:
                s.connect(("127.0.0.1", self.port))
                s.close()
                return True
            except OSError:
                time.sleep(0.15)
            finally:
                try:
                    s.close()
                except OSError:
                    pass
        return False

    def close(self):
        try:
            self.p.terminate()
            self.p.wait(timeout=5)
        except Exception:
            try:
                self.p.kill()
            except Exception:
                pass
        try:
            self.log.close()
        except OSError:
            pass


# ---------------------------------------------------------------------------
# Battery
# ---------------------------------------------------------------------------

RESULTS = []

def record(cid, desc, rfc, passed, detail, expected_gap=False):
    RESULTS.append({
        "id": cid, "desc": desc, "rfc": rfc,
        "pass": bool(passed), "detail": detail,
        "expected_gap": expected_gap,
    })
    tag = "PASS" if passed else "FAIL"
    gap = "  (known-gap)" if (expected_gap and not passed) else ""
    print("[%s] %-6s %s -- %s%s" % (tag, cid, desc, detail, gap))


def run_battery(serve_port, dead_serve_port):
    HOST = "Host: t\r\n"

    # --- (a) hop-by-hop request headers must be stripped -----------------
    hbh_req = (
        b"GET /api/echo HTTP/1.1\r\n"
        b"Host: t\r\n"
        b"Connection: keep-alive, X-Custom-Hop\r\n"
        b"X-Custom-Hop: should-be-dropped\r\n"
        b"Keep-Alive: timeout=5, max=1000\r\n"
        b"TE: trailers\r\n"
        b"Upgrade: websocket\r\n"
        b"Proxy-Connection: keep-alive\r\n"
        b"X-End-To-End: preserve-me\r\n"
        b"\r\n"
    )
    resp, err = send_raw(serve_port, hbh_req)
    if err or not resp:
        record("a", "hop-by-hop request headers stripped", "9110 7.6.1", False,
               "no response from proxy: %s" % err, expected_gap=True)
        seen = b""
    else:
        _, upstream_saw = split_head_body(resp)
        seen = upstream_saw.lower()
        leaked = [h for h in (b"connection", b"keep-alive", b"te", b"upgrade",
                              b"proxy-connection", b"x-custom-hop")
                  if (b"\r\n" + h + b":") in (b"\r\n" + seen)]
        record("a", "hop-by-hop request headers stripped", "9110 7.6.1",
               len(leaked) == 0,
               ("all stripped" if not leaked
                else "leaked to upstream: %s" % ",".join(x.decode() for x in leaked)),
               expected_gap=True)
        # end-to-end request header should survive (verbatim path preserves it)
        record("e-req", "client end-to-end request header reaches upstream",
               "9110 7.6.1", (b"x-end-to-end:" in seen and b"preserve-me" in upstream_saw.lower()),
               "X-End-To-End " + ("present" if b"x-end-to-end:" in seen else "MISSING") + " upstream-side")

    # --- (b) Via header added --------------------------------------------
    resp, err = send_raw(serve_port, b"GET /api/echo HTTP/1.1\r\n" + HOST.encode() + b"\r\n")
    if err or not resp:
        record("b-req", "Via added to forwarded request", "9110 7.6.3", False,
               "no response: %s" % err, expected_gap=True)
        record("b-resp", "Via added to response", "9110 7.6.3", False,
               "no response: %s" % err, expected_gap=True)
    else:
        rhead, ubody = split_head_body(resp)
        req_via = (b"\r\nvia:" in ubody.lower())
        record("b-req", "Via added to forwarded request", "9110 7.6.3",
               req_via, "Via " + ("present" if req_via else "ABSENT") + " upstream-side",
               expected_gap=True)
        resp_via = header_present(rhead, "Via") is not None
        record("b-resp", "Via added to response", "9110 7.6.3",
               resp_via, "Via " + ("present" if resp_via else "ABSENT") + " client-side",
               expected_gap=True)

    # --- (c) X-Forwarded-For / Forwarded ---------------------------------
    resp, err = send_raw(serve_port, b"GET /api/echo HTTP/1.1\r\n" + HOST.encode() + b"\r\n")
    if err or not resp:
        record("c", "X-Forwarded-For / Forwarded added", "de-facto / 9110 7.6.2",
               False, "no response: %s" % err, expected_gap=True)
    else:
        _, ubody = split_head_body(resp)
        low = ubody.lower()
        xff = (b"\r\nx-forwarded-for:" in low) or (b"\r\nforwarded:" in low) \
            or (b"\r\nx-forwarded-proto:" in low)
        record("c", "X-Forwarded-For / Forwarded added", "de-facto / 9110 7.6.2",
               xff, "forwarding header " + ("present" if xff else "ABSENT") + " upstream-side",
               expected_gap=True)

    # --- (d1) gateway error surfaced when the only backend is unreachable -
    # A backend that never accepts is ejected by the active health probe, so the
    # eligible pool is empty and the proven pick returns none -> 503 "no healthy
    # upstream" (rather than a per-request 502). Either way a 5xx gateway error
    # must be surfaced, not a hang or a 200.
    resp, err = send_raw(dead_serve_port, b"GET /api/echo HTTP/1.1\r\nHost: t\r\n\r\n")
    st = status_of(resp) if resp else None
    record("d1", "5xx surfaced when backend unreachable (health-ejected pool)",
           "9110 15.6.3/15.6.4", st in (502, 503),
           "status=%s (%s)" % (st, "503=pool-empty path" if st == 503 else "502=dial-fail path"))

    # --- (d1b) 502 on forward failure (backend accepts, no valid response) -
    # The backend passes the connect-only health probe but drops the connection
    # without a response head; the forward fails and the host must send 502.
    resp, err = send_raw(serve_port, b"GET /api/close HTTP/1.1\r\nHost: t\r\n\r\n")
    st = status_of(resp) if resp else None
    record("d1b", "502 Bad Gateway on upstream forward failure", "9110 15.6.3",
           st == 502, "status=%s (err=%s)" % (st, err))

    # --- (d2) 504 on upstream timeout ------------------------------------
    resp, err = send_raw(serve_port, b"GET /api/slow HTTP/1.1\r\n" + HOST.encode() + b"\r\n", timeout=6.0)
    st = status_of(resp) if resp else None
    record("d2", "504 Gateway Timeout on upstream timeout", "9110 15.6.5",
           st == 504, "status=%s (a 502/close also indicates upstream-timeout not distinguished)" % st,
           expected_gap=True)

    # --- (e) end-to-end response headers preserved -----------------------
    resp, err = send_raw(serve_port, b"GET /api/e2ehdr HTTP/1.1\r\n" + HOST.encode() + b"\r\n")
    if err or not resp:
        record("e-resp", "end-to-end response headers preserved", "9110 7.6.1",
               False, "no response: %s" % err)
    else:
        rhead, _ = split_head_body(resp)
        custom = header_present(rhead, "X-Custom-End")
        etag = header_present(rhead, "ETag")
        record("e-resp", "end-to-end response headers preserved", "9110 7.6.1",
               custom == b"value123" and etag is not None,
               "X-Custom-End=%s ETag=%s" % (custom, etag))

    # --- (f1) fixed-length request body forwarded ------------------------
    body = b"the-quick-brown-fox-body-payload"
    req = (b"POST /api/echo HTTP/1.1\r\nHost: t\r\n"
           b"Content-Type: text/plain\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s"
           % (len(body), body))
    resp, err = send_raw(serve_port, req)
    if err or not resp:
        record("f1", "fixed-length request body forwarded", "7230 3.3",
               False, "no response: %s" % err)
    else:
        _, ubody = split_head_body(resp)
        record("f1", "fixed-length request body forwarded", "7230 3.3",
               body in ubody, "body " + ("forwarded" if body in ubody else "NOT forwarded") + " to upstream")

    # --- (f2) chunked request body forwarded -----------------------------
    marker = b"chunkbodymarker42"
    chunked = (b"POST /api/echo HTTP/1.1\r\nHost: t\r\n"
               b"Transfer-Encoding: chunked\r\nConnection: close\r\n\r\n"
               b"%x\r\n%s\r\n0\r\n\r\n" % (len(marker), marker))
    resp, err = send_raw(serve_port, chunked)
    if err or not resp:
        record("f2", "chunked request body forwarded", "7230 4.1",
               False, "no response: %s" % err, expected_gap=True)
    else:
        _, ubody = split_head_body(resp)
        record("f2", "chunked request body forwarded", "7230 4.1",
               marker in ubody, "chunk payload " + ("reached" if marker in ubody else "did NOT reach") + " upstream",
               expected_gap=True)

    # --- (g1) large response body streamed intact ------------------------
    resp, err = send_raw(serve_port, b"GET /api/big HTTP/1.1\r\n" + HOST.encode() + b"\r\n", timeout=6.0)
    if err or not resp:
        record("g1", "large response body streamed intact", "7230 3.3",
               False, "no response: %s" % err)
    else:
        rhead, rbody = split_head_body(resp)
        cl = header_present(rhead, "Content-Length")
        expect = 100 * 1024
        ok = (rbody.count(b"X") == expect) or (len(rbody) == expect)
        record("g1", "large response body streamed intact", "7230 3.3",
               ok, "got %d body bytes (expect %d), Content-Length=%s" % (len(rbody), expect, cl))

    # --- (g2) chunked response streamed & framed -------------------------
    resp, err = send_raw(serve_port, b"GET /api/chunkedresp HTTP/1.1\r\n" + HOST.encode() + b"\r\n", timeout=6.0)
    if err or not resp:
        record("g2", "chunked response streamed to client", "7230 4.1",
               False, "no response: %s" % err)
    else:
        rhead, rbody = split_head_body(resp)
        # payload should be "hello chunked world" whether re-chunked or de-chunked
        joined = rbody.replace(b"\r\n", b"")
        got_payload = b"hello" in rbody and b"chunked" in rbody and b"world" in rbody
        record("g2", "chunked response streamed to client", "7230 4.1",
               got_payload, "payload " + ("intact" if got_payload else "CORRUPT/missing"))

    # --- (h) upstream hop-by-hop response headers not blindly leaked -----
    # e2ehdr upstream sends `Connection: close`; the intermediary should manage
    # the client connection disposition itself (this is informational).
    resp, err = send_raw(serve_port, b"GET /api/e2ehdr HTTP/1.1\r\n" + HOST.encode() + b"\r\n")
    if resp:
        rhead, _ = split_head_body(resp)
        conn = header_present(rhead, "Connection")
        record("h", "response Connection header managed by intermediary", "9110 7.6.1",
               conn is not None, "client-side Connection=%s (informational)" % conn)


def main():
    ap = argparse.ArgumentParser()
    # The harness lives at <repo>/conformance/proxy/; the serve binary is the
    # release build two levels up. Override with --serve for other locations.
    here = os.path.dirname(os.path.abspath(__file__))
    default_bin = os.path.normpath(os.path.join(here, "..", "..", "target", "release", "dataplane"))
    ap.add_argument("--serve", default=default_bin)
    ap.add_argument("--base-port", type=int, default=18950)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()

    bp = args.base_port
    serve_port = bp          # 18950 : live-backend serve
    upstream_port = bp + 1   # 18951 : live upstream
    dead_serve_port = bp + 2 # 18952 : serve pointed at a dead backend
    dead_backend = bp + 9    # 18959 : nothing listens here

    if not os.path.exists(args.serve):
        print("serve binary not found: %s" % args.serve, file=sys.stderr)
        sys.exit(2)

    up = Upstream(upstream_port)
    up.start()

    serve_a = Serve(args.serve, serve_port, "0=127.0.0.1:%d" % upstream_port,
                    "/tmp/proxy-battery-serve-%d.log" % serve_port)
    serve_b = Serve(args.serve, dead_serve_port, "0=127.0.0.1:%d" % dead_backend,
                    "/tmp/proxy-battery-serve-%d.log" % dead_serve_port)

    ok_a = serve_a.wait_ready()
    ok_b = serve_b.wait_ready()
    print("upstream: 127.0.0.1:%d up" % upstream_port)
    print("serve(live-backend): 127.0.0.1:%d ready=%s" % (serve_port, ok_a))
    print("serve(dead-backend): 127.0.0.1:%d ready=%s" % (dead_serve_port, ok_b))
    print("-" * 72)

    try:
        if not ok_a:
            print("live-backend serve failed to start; see log", file=sys.stderr)
        run_battery(serve_port, dead_serve_port)
    finally:
        serve_a.close()
        serve_b.close()
        up.close()

    total = len(RESULTS)
    passed = sum(1 for r in RESULTS if r["pass"])
    gaps = [r for r in RESULTS if (not r["pass"]) and r["expected_gap"]]
    hard = [r for r in RESULTS if (not r["pass"]) and not r["expected_gap"]]
    print("-" * 72)
    print("SCORE: %d/%d passed  |  %d known-gap fails  |  %d unexpected fails"
          % (passed, total, len(gaps), len(hard)))
    if args.json:
        with open(args.json, "w") as f:
            json.dump({"passed": passed, "total": total, "results": RESULTS}, f, indent=2)
        print("wrote %s" % args.json)


if __name__ == "__main__":
    main()
