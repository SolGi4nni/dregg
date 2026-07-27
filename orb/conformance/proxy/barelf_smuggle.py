#!/usr/bin/env python3
"""Bare-LF header smuggling probe against the reverse-proxy path.

The proven framing gate (`Body.FrameRaw.frameRaw`) and the proven forward
(`Reactor.ProxyForward.stripHopByHop`) both terminate header lines ONLY on
CRLF (`Body.FrameRaw.takeLine`, `Reactor.ServeStep.splitCRLFLines`). A head
containing a BARE LF is nevertheless ADMITTED by the gate, so a hop-by-hop
field sitting after a bare LF is not a field-line to drorb -- it is part of the
PREVIOUS field's value -- and is forwarded to the upstream unstripped.

RFC 9112 §2.2 lets a recipient recognize a bare LF as a line terminator, so an
upstream MAY split there and see a `Connection` / `Transfer-Encoding` field
this intermediary did not strip. RFC 9112 §11.2: differing parses between
intermediary and upstream is request smuggling.

This script stands up an upstream that reports the EXACT bytes it received,
runs the dataplane in reverse-proxy mode in front of it, and sends the crafted
head. Honest output only: it prints what the upstream actually saw.
"""

import os
import socket
import subprocess
import sys
import threading
import time

RECEIVED = []


class Upstream:
    """Echoes the raw request bytes it received into its response body."""

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
        c.settimeout(2.0)
        try:
            while b"\r\n\r\n" not in buf:
                d = c.recv(65536)
                if not d:
                    break
                buf += d
        except socket.timeout:
            pass
        RECEIVED.append(buf)
        body = b"upstream-ok\n"
        c.sendall(b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: %d\r\n\r\n%s"
                  % (len(body), body))
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


def lf_tolerant_fields(head):
    """Split the head the way an RFC 9112 §2.2 LF-tolerant recipient may."""
    lines = head.replace(b"\r\n", b"\n").split(b"\n")
    return [l for l in lines[1:] if l]


def main():
    serve_bin = sys.argv[1] if len(sys.argv) > 1 else "target/release/dataplane"
    base = int(sys.argv[2]) if len(sys.argv) > 2 else 18970
    serve_port, up_port = base, base + 1

    up = Upstream(up_port)
    up.start()

    env = dict(os.environ)
    env["DRORB_PROXY_BACKENDS"] = "0=127.0.0.1:%d" % up_port
    env.pop("DRORB_EFFECT_SEAM", None)
    log = open("/tmp/barelf-serve-%d.log" % serve_port, "wb")
    p = subprocess.Popen(
        [serve_bin, "--bind", "127.0.0.1:%d" % serve_port, "--no-udp",
         "--io", os.environ.get("PROXY_IO", "auto")],
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
    print("serve 127.0.0.1:%d ready=%s   upstream 127.0.0.1:%d"
          % (serve_port, ready, up_port))

    cases = [
        ("CONTROL  (all CRLF, hop-by-hop on its own line)",
         b"GET /api/probe HTTP/1.1\r\n"
         b"Host: 127.0.0.1\r\n"
         b"X-Probe: 1\r\n"
         b"Connection: keep-alive\r\n"
         b"\r\n"),
        ("BARE-LF  (Connection: keep-alive after a bare LF)",
         b"GET /api/probe HTTP/1.1\r\n"
         b"Host: 127.0.0.1\r\n"
         b"X-Probe: 1\nConnection: keep-alive\r\n"
         b"\r\n"),
        ("BARE-LF  (Transfer-Encoding: chunked after a bare LF)",
         b"GET /api/probe HTTP/1.1\r\n"
         b"Host: 127.0.0.1\r\n"
         b"X-Probe: 1\nTransfer-Encoding: chunked\r\n"
         b"\r\n"),
    ]

    fails = 0
    for name, raw in cases:
        RECEIVED.clear()
        resp, err = send_raw(serve_port, raw)
        print("=" * 72)
        print(name)
        print("  client->proxy  : %r" % raw)
        print("  proxy status   : %s%s"
              % (resp.split(b"\r\n", 1)[0] if resp else b"<no response>",
                 "  err=%s" % err if err else ""))
        if not RECEIVED:
            print("  upstream saw   : <nothing -- proxy did not forward>")
            continue
        seen = RECEIVED[0]
        print("  upstream saw   : %r" % seen)
        head = seen.split(b"\r\n\r\n", 1)[0]
        fields = lf_tolerant_fields(head)
        leaked = [f for f in fields
                  if f.split(b":", 1)[0].strip().lower() in
                  (b"connection", b"keep-alive", b"transfer-encoding", b"te",
                   b"upgrade", b"trailer", b"proxy-connection",
                   b"proxy-authorization", b"proxy-authenticate")]
        if leaked:
            print("  ** HOP-BY-HOP REACHED UPSTREAM (LF-tolerant parse): %r" % leaked)
            fails += 1
        else:
            print("  no hop-by-hop field in the LF-tolerant parse of what upstream saw")

    print("=" * 72)
    print("SMUGGLE-LEAKS: %d" % fails)
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
