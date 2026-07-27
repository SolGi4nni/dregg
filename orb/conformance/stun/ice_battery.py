#!/usr/bin/env python3
"""aioice (the aiortc ICE stack) battery against the STUN/ICE server core.

Part 1 — RFC 5389: server-reflexive candidate gathering through the Binding
service on the primary bridge (start it first:
`python3 conformance/stun/udp_bridge.py 3478`).

Part 2 — RFC 8445: a full ICE negotiation. aioice is the controlling agent;
`Stun.serve` behind its own bridge (short-term credentials) is the controlled
peer answering connectivity checks. `Connection.connect()` only returns once a
candidate pair is nominated, which requires every answer to carry a
MESSAGE-INTEGRITY that verifies under the session password — aioice discards
unauthenticated answers. One remote candidate is advertised per local IPv4
the client gathered on (the bridge binds 0.0.0.0); the check list finds the
pair that works.

Run from the repository root:
    python3 conformance/stun/ice_battery.py
"""
import asyncio
import os
import subprocess
import sys
import time

import aioice

ICE_PORT = 3480
UFRAG = "drorbufrag"
PWD = "drorbpassword0123456789abc"  # >= 22 characters, RFC 8445 5.3


def ipv4_host_ips(conn: aioice.Connection) -> list:
    ips = []
    for c in conn.local_candidates:
        if c.type == "host" and "." in c.host and c.host not in ips:
            ips.append(c.host)
    return ips


async def part1_gather() -> bool:
    conn = aioice.Connection(ice_controlling=True,
                             stun_server=("127.0.0.1", 3478))
    await conn.gather_candidates()
    srflx = [c for c in conn.local_candidates if c.type == "srflx"]
    await conn.close()
    print(f"gather: srflx={srflx}")
    return bool(srflx)


async def part2_full_ice() -> bool:
    conn = aioice.Connection(ice_controlling=True)
    await conn.gather_candidates()
    # expected USERNAME in inbound checks: "<served-ufrag>:<checker-ufrag>"
    username = f"{UFRAG}:{conn.local_username}"
    bridge = subprocess.Popen(
        [sys.executable, "conformance/stun/udp_bridge.py", str(ICE_PORT),
         "--no-alt", "--username", username, "--password", PWD],
        env=os.environ, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True)
    print("bridge:", bridge.stdout.readline().strip())
    time.sleep(20)  # allow the Lean harness to finish elaborating
    try:
        conn.remote_username = UFRAG
        conn.remote_password = PWD
        for i, ip in enumerate(ipv4_host_ips(conn)):
            await conn.add_remote_candidate(aioice.Candidate(
                foundation=str(i + 1), component=1, transport="udp",
                priority=2130706431 - i, host=ip, port=ICE_PORT, type="host"))
        await conn.add_remote_candidate(None)
        t0 = time.monotonic()
        await asyncio.wait_for(conn.connect(), timeout=30)
        dt = time.monotonic() - t0
        nominated = {k: (p.remote_candidate.host, p.remote_candidate.port)
                     for k, p in conn._nominated.items()}
        print(f"connect(): completed in {dt:.2f}s; nominated={nominated}")
        await conn.close()
        return True
    except Exception as exc:
        print(f"connect(): FAILED: {exc!r}")
        await conn.close()
        return False
    finally:
        bridge.terminate()


async def main() -> None:
    ok1 = await part1_gather()
    print("srflx via STUN Binding service:", "SUCCESS" if ok1 else "FAILURE")
    ok2 = await part2_full_ice()
    print("full ICE connect() vs the served responder:",
          "SUCCESS" if ok2 else "FAILURE")


if __name__ == "__main__":
    asyncio.run(main())
