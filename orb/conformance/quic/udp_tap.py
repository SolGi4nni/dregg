#!/usr/bin/env python3
"""A UDP tap: forward datagrams between a client and the serve, recording both
directions as hex so a failing exchange can be replayed into `orb-quic --bridge`
and inspected deterministically.

Usage: udp_tap.py <listen_port> <serve_port> [out.hex]
Records `C2S <hex>` / `S2C <hex>` lines; the C2S lines feed the bridge directly.
"""
import socket
import sys
import threading

listen_port = int(sys.argv[1])
serve_port = int(sys.argv[2])
out_path = sys.argv[3] if len(sys.argv) > 3 else "tap.hex"

front = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
front.bind(("127.0.0.1", listen_port))
back = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
back.bind(("127.0.0.1", 0))

out = open(out_path, "w")
lock = threading.Lock()
client_addr = [None]


def log(tag, data):
    with lock:
        out.write(f"{tag} {data.hex()}\n")
        out.flush()


def c2s():
    while True:
        data, addr = front.recvfrom(65535)
        client_addr[0] = addr
        log("C2S", data)
        back.sendto(data, ("127.0.0.1", serve_port))


def s2c():
    while True:
        data, _ = back.recvfrom(65535)
        log("S2C", data)
        if client_addr[0]:
            front.sendto(data, client_addr[0])


threading.Thread(target=c2s, daemon=True).start()
t = threading.Thread(target=s2c, daemon=True)
t.start()
threading.Event().wait()
