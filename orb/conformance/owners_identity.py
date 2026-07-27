#!/usr/bin/env python3
"""Byte-identity + crash-safety probe for the multi-owner serve lever
(`DRORB_SERVE_OWNERS=k`).

The lever attaches k-1 extra owner threads to the one process-global runtime;
this probe checks the OBSERVABLE contract: every served byte with the lever
ENABLED is identical to the single-owner baseline, under real cross-connection
concurrency, with zero failed/short responses and no server crash.

Method: a fixed corpus of raw HTTP/1.1 requests is PIPELINED on one connection
(the last request carries `Connection: close`), and the ENTIRE response byte
stream is read to EOF. That makes the unit of comparison a single `cmp`-style
byte string — no tolerant parsing, any reordering / interleaving / corruption /
truncation anywhere in the stream is a mismatch.

  capture  — record the baseline stream (run against a single-owner server)
  verify   — sequential re-check + N-thread concurrent hammer (run against a
             multi-owner server); every thread opens fresh connections, so
             distinct owner threads cross the runtime concurrently.

Exit 0 = every stream byte-identical, 0 failures. Nonzero = mismatch (first
divergence saved next to the baseline) or connection failure.
"""

import argparse
import socket
import sys
import threading
import time
from pathlib import Path

# The pipelined corpus: the deployed arms a real client mix exercises —
# the 1 MiB /bulk body, the tiny /health arm, the root arm, a 404 arm, a
# HEAD (body-stripped) arm, and a conditional revalidation arm. One byte
# string; the final request closes so read-to-EOF terminates.
CORPUS = (
    b"GET /bulk HTTP/1.1\r\nHost: x\r\n\r\n"
    b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n"
    b"GET / HTTP/1.1\r\nHost: x\r\n\r\n"
    b"GET /no-such-arm HTTP/1.1\r\nHost: x\r\n\r\n"
    b"HEAD /bulk HTTP/1.1\r\nHost: x\r\n\r\n"
    b"GET /bulk HTTP/1.1\r\nHost: x\r\nIf-None-Match: \"drorb-bulk-v1\"\r\n\r\n"
    b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
)

BASENAME = "owners-baseline-stream.bin"


def fetch_stream(port: int, payload: bytes = CORPUS, timeout: float = 15.0) -> bytes:
    """Send `payload` on a fresh connection, read the full response stream to EOF."""
    with socket.create_connection(("127.0.0.1", port), timeout=timeout) as s:
        s.sendall(payload)
        chunks = []
        while True:
            b = s.recv(1 << 16)
            if not b:
                break
            chunks.append(b)
    return b"".join(chunks)


def capture(port: int, outdir: Path) -> int:
    outdir.mkdir(parents=True, exist_ok=True)
    a = fetch_stream(port)
    time.sleep(1.5)  # straddle a wall-clock second: catches any time-varying byte
    b = fetch_stream(port)
    if a != b:
        print("CAPTURE FAIL: two sequential fetches differ — response is not "
              "time-invariant; a byte-identity gate cannot be run this way.")
        (outdir / "capture-a.bin").write_bytes(a)
        (outdir / "capture-b.bin").write_bytes(b)
        return 2
    (outdir / BASENAME).write_bytes(a)
    print(f"captured baseline stream: {len(a)} bytes (time-invariant across 1.5s), "
          f"-> {outdir / BASENAME}")
    return 0


def verify(port: int, outdir: Path, threads: int, iters: int) -> int:
    expected = (outdir / BASENAME).read_bytes()

    # Phase 1: sequential re-check.
    got = fetch_stream(port)
    if got != expected:
        diverge = next((i for i, (x, y) in enumerate(zip(got, expected)) if x != y),
                       min(len(got), len(expected)))
        (outdir / "mismatch-sequential.bin").write_bytes(got)
        print(f"SEQUENTIAL MISMATCH: {len(got)} vs {len(expected)} bytes, "
              f"first divergence at offset {diverge}")
        return 1
    print(f"sequential: stream identical ({len(expected)} bytes)")

    # Phase 2: concurrent hammer. Each worker runs `iters` fresh connections;
    # every full stream must be byte-identical to the baseline.
    failures = []
    ok_count = [0] * threads
    lock = threading.Lock()

    def worker(tid: int):
        for i in range(iters):
            try:
                got = fetch_stream(port)
            except OSError as e:
                with lock:
                    failures.append((tid, i, f"connection error: {e}"))
                return
            if got != expected:
                with lock:
                    failures.append((tid, i, f"byte mismatch ({len(got)} vs "
                                              f"{len(expected)} bytes)"))
                    (outdir / f"mismatch-t{tid}-i{i}.bin").write_bytes(got)
                return
            ok_count[tid] += 1

    ts = [threading.Thread(target=worker, args=(t,)) for t in range(threads)]
    t0 = time.monotonic()
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    dt = time.monotonic() - t0

    total_ok = sum(ok_count)
    total_reqs = total_ok * 7  # 7 requests per pipelined stream
    print(f"concurrent: {threads} threads x {iters} conns, {total_ok} identical "
          f"streams ({total_reqs} requests, {total_ok * len(expected) / 1e6:.0f} MB) "
          f"in {dt:.1f}s")
    if failures:
        for f in failures[:10]:
            print(f"  FAILURE thread={f[0]} iter={f[1]}: {f[2]}")
        return 1
    print("concurrent: every stream byte-identical, 0 failures")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["capture", "verify"])
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--dir", type=Path, required=True,
                    help="baseline directory (written by capture, read by verify)")
    ap.add_argument("--threads", type=int, default=32)
    ap.add_argument("--iters", type=int, default=100)
    a = ap.parse_args()
    if a.mode == "capture":
        return capture(a.port, a.dir)
    return verify(a.port, a.dir, a.threads, a.iters)


if __name__ == "__main__":
    sys.exit(main())
