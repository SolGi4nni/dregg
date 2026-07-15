#!/usr/bin/env python3
"""Minimal RFC 6455 pre-flight probe against a running ws serve.

Checks, over a raw socket (no ws library):
  1. the 101 upgrade handshake (Sec-WebSocket-Accept token),
  2. whether permessage-deflate is negotiated when offered,
  3. a small masked text frame is echoed back,
  4. ping is answered with pong,
  5. close is answered with close.

Usage: probe.py [PORT]   (default 18906)
"""
import base64
import hashlib
import os
import socket
import struct
import sys

GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"


def mask(payload: bytes, key: bytes) -> bytes:
    return bytes(b ^ key[i % 4] for i, b in enumerate(payload))


def frame(opcode: int, payload: bytes, fin: bool = True) -> bytes:
    b0 = (0x80 if fin else 0) | opcode
    key = os.urandom(4)
    n = len(payload)
    if n < 126:
        head = struct.pack("!BB", b0, 0x80 | n)
    elif n < 1 << 16:
        head = struct.pack("!BBH", b0, 0x80 | 126, n)
    else:
        head = struct.pack("!BBQ", b0, 0x80 | 127, n)
    return head + key + mask(payload, key)


def read_frame(sock):
    hdr = sock.recv(2)
    if len(hdr) < 2:
        return None, b""
    b0, b1 = hdr
    opcode = b0 & 0x0F
    n = b1 & 0x7F
    if n == 126:
        n = struct.unpack("!H", sock.recv(2))[0]
    elif n == 127:
        n = struct.unpack("!Q", sock.recv(8))[0]
    if b1 & 0x80:  # server frames must not be masked; tolerate for reporting
        sock.recv(4)
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            break
        buf += chunk
    return opcode, buf


def handshake(port: int, offer_deflate: bool):
    s = socket.create_connection(("127.0.0.1", port), timeout=5)
    key = base64.b64encode(os.urandom(16)).decode()
    ext = ("Sec-WebSocket-Extensions: permessage-deflate; "
           "client_max_window_bits\r\n" if offer_deflate else "")
    req = (f"GET / HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\n"
           "Upgrade: websocket\r\nConnection: Upgrade\r\n"
           f"Sec-WebSocket-Key: {key}\r\n{ext}"
           "Sec-WebSocket-Version: 13\r\n\r\n").encode()
    s.sendall(req)
    resp = b""
    while b"\r\n\r\n" not in resp:
        chunk = s.recv(4096)
        if not chunk:
            break
        resp += chunk
    head = resp.split(b"\r\n\r\n")[0].decode("latin-1")
    expect = base64.b64encode(
        hashlib.sha1((key + GUID).encode()).digest()).decode()
    ok_101 = head.startswith("HTTP/1.1 101")
    accept_lines = [ln.split(":", 1)[1].strip() for ln in head.split("\r\n")
                    if ln.lower().startswith("sec-websocket-accept:")]
    ok_accept = accept_lines == [expect]
    deflate = "permessage-deflate" in head.lower()
    return s, ok_101, ok_accept, deflate


def main(port: int):
    results = []

    s, ok_101, ok_accept, _ = handshake(port, offer_deflate=False)
    results.append(("101 handshake", ok_101))
    results.append(("Sec-WebSocket-Accept token", ok_accept))

    s.sendall(frame(0x1, b"hello-conformance"))
    op, payload = read_frame(s)
    results.append(("text echo", op == 0x1 and payload == b"hello-conformance"))

    s.sendall(frame(0x9, b"pingdata"))
    op, payload = read_frame(s)
    results.append(("ping -> pong (same payload)",
                    op == 0xA and payload == b"pingdata"))

    s.sendall(frame(0x8, struct.pack("!H", 1000)))
    op, payload = read_frame(s)
    results.append(("close -> close reply", op == 0x8))
    s.close()

    s2, ok, _, deflate = handshake(port, offer_deflate=True)
    results.append(("handshake with deflate offer still 101", ok))
    results.append(("permessage-deflate negotiated when offered (RFC 7692)",
                    deflate))
    s2.close()

    width = max(len(n) for n, _ in results)
    fails = 0
    for name, passed in results:
        print(f"{name:<{width}}  {'PASS' if passed else 'FAIL'}")
        fails += 0 if passed else 1
    print(f"\n{len(results) - fails}/{len(results)} probe checks passed")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 18906))
