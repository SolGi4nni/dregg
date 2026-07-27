#!/usr/bin/env python3
"""Bare-LF RESPONSE-head splitting probe against the reverse-proxy path.

The mirror of `barelf_smuggle.py`, on the other direction.

The proven response forward (`Reactor.ProxyForward.forwardRespHead`) and the
proven upstream parse (`Reactor.ServeStep.parseUpstream`) both terminate header
lines ONLY on CRLF (`Reactor.ServeStep.splitCRLFLines`). RFC 9112 s2.2 lets a
recipient recognise a BARE LF as a line terminator. So an upstream response head
carrying a bare LF has TWO admissible parses: to drorb everything after the bare
LF is part of the PREVIOUS field's value; to an LF-tolerant downstream client it
is a field-line of its own -- or, after a bare LF LF, an entirely new message.

RFC 9110 s7.6.1 makes the intermediary responsible for the head it hands its
client. Two hops disagreeing about where a response's fields (and hence its body)
begin is HTTP response splitting.

This script stands up a HOSTILE upstream that returns crafted response heads,
runs the dataplane in reverse-proxy mode in front of it, and prints the EXACT
bytes the downstream client received, plus the LF-tolerant parse of them (the
parse curl / most clients take).

Honest output only: every line printed comes from a real socket read.

Usage: respsplit_probe.py [dataplane] [base-port]
Env: PROXY_IO=uring|auto|blocking (which reactor to exercise)
"""

import os
import socket
import subprocess
import sys
import threading
import time

# ---------------------------------------------------------------------------
# The crafted upstream response heads. Each is returned VERBATIM by the hostile
# upstream; the injected content sits behind a BARE LF (never a CRLF), so a
# CRLF-only parse sees it inside the previous field's value.
# ---------------------------------------------------------------------------

VECTORS = {
    # 1. Field injection: a `Set-Cookie` the intermediary never saw as a field.
    b"/api/cookie": (
        b"HTTP/1.1 200 OK\r\n"
        b"Content-Type: text/plain\r\n"
        b"X-Tag: a\nSet-Cookie: sess=EVIL; Path=/\r\n"
        b"Content-Length: 3\r\n"
        b"\r\n"
        b"ok\n"
    ),
    # 2. Full response split: a bare LF LF ends the head for an LF-tolerant
    #    client, and a WHOLE second HTTP response follows inside what drorb
    #    reads as one header value. All-LF so drorb's CRLFCRLF head scan still
    #    lands on the real terminator.
    b"/api/split": (
        b"HTTP/1.1 200 OK\r\n"
        b"Content-Type: text/plain\r\n"
        b"X-Tag: a\n\nHTTP/1.1 200 OK\nX-Injected: yes\n\nOWNED!\r\n"
        b"Content-Length: 3\r\n"
        b"\r\n"
        b"ok\n"
    ),
    # 3. Control: the same fields, all CRLF, nothing hidden.
    b"/api/control": (
        b"HTTP/1.1 200 OK\r\n"
        b"Content-Type: text/plain\r\n"
        b"X-Tag: a\r\n"
        b"Content-Length: 3\r\n"
        b"\r\n"
        b"ok\n"
    ),
}


class HostileUpstream:
    """Returns a crafted (bare-LF) response head chosen by the request target."""

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

    def _loop(self):
        while not self.stop:
            try:
                c, _ = self.srv.accept()
            except OSError:
                return
            threading.Thread(target=self._handle, args=(c,), daemon=True).start()

    def _handle(self, c):
        buf = b""
        c.settimeout(3.0)
        try:
            while b"\r\n\r\n" not in buf:
                d = c.recv(65536)
                if not d:
                    break
                buf += d
        except socket.timeout:
            pass
        target = b""
        first = buf.split(b"\r\n", 1)[0]
        parts = first.split(b" ")
        if len(parts) >= 2:
            target = parts[1]
        raw = VECTORS.get(target, VECTORS[b"/api/control"])
        try:
            c.sendall(raw)
        except OSError:
            pass
        try:
            c.close()
        except OSError:
            pass


def send_raw(port, raw, timeout=4.0):
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
    except OSError as e:
        return out, str(e)
    finally:
        try:
            s.close()
        except OSError:
            pass
    return out, None


def lf_tolerant_head(resp):
    """Split the response the way an RFC 9112 s2.2 LF-tolerant client may:
    normalise CRLF to LF, then the head ends at the first blank line."""
    norm = resp.replace(b"\r\n", b"\n")
    i = norm.find(b"\n\n")
    if i < 0:
        return norm, b""
    return norm[:i], norm[i + 2:]


# Fields that only an LF-tolerant parse can turn into a field-line here. NOT
# `Connection` -- drorb legitimately stamps its own client disposition, so
# counting it would be a false positive.
HOP = (b"set-cookie", b"x-injected", b"keep-alive",
       b"transfer-encoding", b"content-security-policy", b"location")


def main():
    serve_bin = sys.argv[1] if len(sys.argv) > 1 else "target/release/dataplane"
    base = int(sys.argv[2]) if len(sys.argv) > 2 else 18974
    serve_port, up_port = base, base + 1

    up = HostileUpstream(up_port)
    up.start()

    env = dict(os.environ)
    env["DRORB_PROXY_BACKENDS"] = "0=127.0.0.1:%d" % up_port
    # PROXY_SEAM=1 exercises the OTHER response-head consumers: with the effect
    # seam on, the proxied reply is threaded through the proven serve
    # (`Reactor.ServeStep.proxyRespTransformGated` / `parseUpstream`) — and, on the
    # io_uring native passthrough-streaming path, through
    # `Reactor.ServeStep.proxyStreamHeadGated` (`drorb_serve_proxy_stream_head`),
    # which is reached FIRST for a fixed-Content-Length reply and so must be gated
    # too. All of them split lines CRLF-only, and all now refuse a bare-LF head.
    if os.environ.get("PROXY_SEAM") in ("1", "true", "yes", "on"):
        env["DRORB_EFFECT_SEAM"] = "1"
    else:
        env.pop("DRORB_EFFECT_SEAM", None)
    logpath = "/tmp/respsplit-serve-%d.log" % serve_port
    log = open(logpath, "wb")
    io_mode = os.environ.get("PROXY_IO", "auto")
    p = subprocess.Popen(
        [serve_bin, "--bind", "127.0.0.1:%d" % serve_port, "--no-udp",
         "--io", io_mode],
        env=env, stdout=log, stderr=subprocess.STDOUT,
        stdin=subprocess.DEVNULL, start_new_session=True)

    deadline = time.time() + 10
    ready = False
    while time.time() < deadline:
        try:
            s = socket.create_connection(("127.0.0.1", serve_port), 0.5)
            s.close()
            ready = True
            break
        except OSError:
            time.sleep(0.15)
    print("serve 127.0.0.1:%d ready=%s io=%s   hostile upstream 127.0.0.1:%d"
          % (serve_port, ready, io_mode, up_port))
    print("serve log: %s" % logpath)

    seam = os.environ.get("PROXY_SEAM") in ("1", "true", "yes", "on")
    if seam:
        print("PROXY_SEAM=1: the reply is threaded through the effect seam "
              "(Reactor.ServeStep.proxyRespTransformGated via drorb_serve_resume, and "
              "Reactor.ServeStep.proxyStreamHeadGated via drorb_serve_proxy_stream_head "
              "on the native passthrough-streaming path), NOT through "
              "Reactor.ProxyForward.forwardRespHeadGated. BOTH seam consumers are now "
              "gated on Body.FrameRaw.noBareLF, so this path is GRADED like the default "
              "one: a bare-LF upstream head must be refused with 502.")

    fails = 0
    for target in (b"/api/control", b"/api/cookie", b"/api/split"):
        raw = (b"GET " + target + b" HTTP/1.1\r\nHost: 127.0.0.1\r\n"
               b"Connection: close\r\n\r\n")
        resp, err = send_raw(serve_port, raw)
        print("=" * 74)
        print("TARGET %s" % target.decode())
        print("  upstream returned : %r" % VECTORS[target])
        print("  client received   : %r" % resp)
        if err:
            print("  socket err        : %s" % err)
        if not resp:
            print("  ** no response from proxy")
            continue
        head, rest = lf_tolerant_head(resp)
        fields = [l for l in head.split(b"\n")[1:] if l]
        print("  LF-tolerant head  :")
        for f in fields:
            print("      %r" % f)
        print("  LF-tolerant rest  : %r" % rest)
        injected = [f for f in fields
                    if f.split(b":", 1)[0].strip().lower() in HOP]
        second = rest.startswith(b"HTTP/1.") or b"\nHTTP/1." in rest
        status = resp.split(b"\r\n", 1)[0]
        if injected:
            print("  ** INJECTED FIELD IN THE CLIENT-VISIBLE HEAD: %r" % injected)
            fails += 1
        if second:
            print("  ** A SECOND HTTP RESPONSE IS VISIBLE TO THE CLIENT (split)")
            fails += 1
        if not injected and not second:
            print("  clean: no injected field, no second message")
        # The expectation, once the proven gate is routed:
        #   control -> forwarded 200, untouched;
        #   bare-LF -> refused at the gate, surfaced as 502 Bad Gateway.
        # Both paths (default AND seam) are held to this, since 2026-07-25.
        if target == b"/api/control":
            ok = status.startswith(b"HTTP/1.1 200")
            print("  EXPECT 200 forwarded : %s (%r)" % ("PASS" if ok else "FAIL", status))
            if not ok:
                fails += 1
        else:
            ok = status.startswith(b"HTTP/1.1 502")
            print("  EXPECT 502 refused   : %s (%r)" % ("PASS" if ok else "FAIL", status))
            if not ok:
                fails += 1

    # A REAL client's parse, not just this script's model of one: curl dumps the
    # header set it actually believes the response carried.
    print("=" * 74)
    print("REAL CLIENT (curl -D -) on /api/cookie:")
    try:
        cp = subprocess.run(
            ["curl", "-sS", "-D", "-", "-o", "/dev/null", "--max-time", "5",
             "http://127.0.0.1:%d/api/cookie" % serve_port],
            capture_output=True, timeout=15)
        for line in cp.stdout.decode("utf-8", "replace").splitlines():
            print("      %s" % line)
        if cp.stderr:
            print("      stderr: %s" % cp.stderr.decode("utf-8", "replace").strip())
    except Exception as e:
        print("      curl unavailable: %s" % e)

    print("=" * 74)
    print("RESPONSE-SPLIT FINDINGS%s: %d" % (" (seam path)" if seam else "", fails))
    try:
        p.terminate()
        p.wait(timeout=5)
    except Exception:
        p.kill()
    log.close()
    up.close()
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
