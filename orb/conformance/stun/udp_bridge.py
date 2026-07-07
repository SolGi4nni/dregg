#!/usr/bin/env python3
"""UDP bridge for the STUN Binding-server harness (RFC 5389, RFC 5780).

Binds the server's UDP sockets and forwards each received datagram — together
with the receiving socket's identity and the sender's real transport address —
to the proven `Stun.serve` step running in the Lean harness subprocess (one
line per datagram, one line back). The bridge owns only the sockets; every
byte of every response, the choice of which socket answers (RFC 5780
CHANGE-REQUEST), and all credential decisions (RFC 5389 short-term) come from
the Lean core.

Sockets: the primary port, and — unless --no-alt — an alternate port on the
same address. On a host with a single usable address the RFC 5780 alternate
differs in port only, and OTHER-ADDRESS advertises exactly that.

Usage (from the repository root):
    python3 conformance/stun/udp_bridge.py [port] [--alt-port N] [--no-alt]
        [--addr A.B.C.D] [--username STR] [--password STR]
Default port: 3478; default alternate: port+1; default addr: 127.0.0.1.
--username/--password configure the short-term credential (for ICE
connectivity checks); without them the server is a plain Binding service.
"""
import argparse
import select
import socket
import subprocess


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("port", nargs="?", type=int, default=3478)
    ap.add_argument("--alt-port", type=int, default=None)
    ap.add_argument("--no-alt", action="store_true")
    ap.add_argument("--addr", default="127.0.0.1")
    ap.add_argument("--username", default=None)
    ap.add_argument("--password", default=None)
    args = ap.parse_args()

    alt_port = args.alt_port if args.alt_port is not None else args.port + 1
    addr_hex = bytes(int(x) for x in args.addr.split(".")).hex()

    harness_cmd = ["lake", "env", "lean", "--run", "conformance/stun/harness.lean",
                   "--", "--primary", f"1:{args.port}:{addr_hex}"]
    if not args.no_alt:
        harness_cmd += ["--alternate", f"1:{alt_port}:{addr_hex}"]
    if args.username is not None and args.password is not None:
        harness_cmd += ["--username", args.username.encode().hex(),
                        "--key", args.password.encode().hex()]

    harness = subprocess.Popen(
        harness_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    # recvSock/sendSock encoding: bit 0x2 = alternate IP, bit 0x1 = alternate
    # port. One loopback address ⇒ the IP bit maps onto the same two sockets.
    socks = {}
    s_primary = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s_primary.bind(("0.0.0.0", args.port))
    socks[0] = s_primary
    if args.no_alt:
        by_flag = {0: s_primary, 1: s_primary, 2: s_primary, 3: s_primary}
    else:
        s_alt = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s_alt.bind(("0.0.0.0", alt_port))
        socks[1] = s_alt
        by_flag = {0: s_primary, 1: s_alt, 2: s_primary, 3: s_alt}
    print(f"stun bridge: primary 0.0.0.0:{args.port}/udp"
          + ("" if args.no_alt else f", alternate 0.0.0.0:{alt_port}/udp"),
          flush=True)

    while True:
        ready, _, _ = select.select(list(socks.values()), [], [])
        for sock in ready:
            recv_flag = next(f for f, s in socks.items() if s is sock)
            data, (host, sport) = sock.recvfrom(65536)
            src_hex = bytes(int(x) for x in host.split(".")).hex()
            line = f"{recv_flag} 1 {sport} {src_hex} {data.hex() or '-'}\n"
            harness.stdin.write(line)
            harness.stdin.flush()
            reply = harness.stdout.readline().strip()
            if reply and reply != "-":
                flag_s, hex_s = reply.split(" ", 1)
                by_flag[int(flag_s)].sendto(bytes.fromhex(hex_s), (host, sport))


if __name__ == "__main__":
    main()
