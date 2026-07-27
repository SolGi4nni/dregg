#!/usr/bin/env python3
"""DoS-gate conformance battery for the deployed serve.

Drives the FIVE accept-path / header-phase DoS gates the reactor enforces, each
against a serve launched under a config that arms exactly the directive under
test. Every verdict is derived from response bytes this script actually read off
a real socket — never from a self-report, never from a metric counter.

The gates (directive -> observable):

  1. rate-429-with-refill   `rate-limit N` + `rate-window MS`
       A burst of arrivals past N within the window is refused a REAL 429 at
       accept. After the window elapses the bucket REFILLS and a fresh arrival
       is served again — the refill half is what separates a live token bucket
       from a latch that trips once and stays tripped.
  2. conn-limit-503         `max-connections N`
       N+ CONCURRENT connections from one source: the ones over the cap are
       refused a REAL 503 at accept, without spawning a serve.
  3. slowloris-408          `slowloris-timeout MS`
       A request head dripped byte-by-byte past the deadline is refused a REAL
       408. Only the FIRST request on a connection is guarded (the classic
       defense), so the drip must be the connection's opening request.
  4. body-413-declared      `max-body-size N`
       A declared `Content-Length` over the cap is refused a REAL 413 BEFORE the
       body lands (the cheap path: no over-cap bytes are ever read).
  5. body-413-chunked       `max-body-size N`
       The BYPASS: a chunked body carries NO Content-Length, so the declared
       check above cannot see it. The gate must catch the actual accumulated
       bytes crossing the cap mid-stream. A serve that only checked
       Content-Length would pass check 4 and FAIL this one — that asymmetry is
       the point of running both.

Gate interaction (why one serve per gate, not one serve for all): on the accept
path the connection-cap `admit` runs BEFORE the rate `rate_note`. A config arming
both would let the 503 gate answer the burst the 429 gate was meant to catch, and
the rate check would score a false FAIL. Each gate therefore gets its own serve
under a config that arms ONLY its directive.

Run:  python3 battery.py [--serve PATH] [--base-port 18940] [--json OUT]
Exit: 0 = every gate fired, 1 = a gate did not.

Env:
  DOS_IO  the `--io` reactor the gated serves run under. Default `auto` = the
          reactor the binary ships (io_uring on Linux).

WAS RED ON THE SHIPPED REACTOR, FIXED 2026-07-25 — do NOT re-pin to `blocking`.
This battery was launched with a hardcoded `--io blocking` for its whole history
and scored 8/8. Pointed at the reactor that actually ships it scored 6/8:
`dos-rate-429` and `dos-conn-limit-503` did not fire at all, because the
per-source standing state was a PER-SHARD field on io_uring (`uring.rs`,
`struct Shard.standing`) rather than the process-wide table the blocking host
used, so `max-connections N` admitted about N x nproc (measured: 94 served under
a cap of 4 on a 24-core host). Every reactor now shares the one process-wide
table and both gates score 8/8 on the shipped reactor. See
dos/FINDING-per-shard-standing.md and dos/shard_gate_probe.py.

The default here stays `auto` — the reactor that ships. Setting DOS_IO=blocking
tests the portable fallback, which is a different thing from testing production,
and pinning it there is how the gap above stayed invisible.
"""

import argparse
import json
import os
import socket
import subprocess
import sys
import tempfile
import time

RESULTS = []


def record(name, gate, criterion, expected, observed, verdict):
    RESULTS.append(
        dict(
            name=name,
            gate=gate,
            criterion=criterion,
            expected=expected,
            observed=observed,
            verdict=verdict,
        )
    )
    mark = "PASS" if verdict == "PASS" else "FAIL"
    print(f"[{mark}] {name:24s} {criterion}")
    print(f"         -> {observed}")


# ---------------------------------------------------------------------------
# serve lifecycle
# ---------------------------------------------------------------------------


def wait_listen(port, proc, timeout=40.0):
    """Return True once the port accepts; False if it never does / serve dies."""
    deadline = time.time() + timeout
    while time.time() < deadline:
        if proc.poll() is not None:
            return False
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.5):
                return True
        except OSError:
            time.sleep(0.1)
    return False


class Serve:
    """A serve launched under a directive config, reaped on context exit.

    Port-exact ownership: the caller picks a free port and this object holds the
    PID it launched, so a reap can only ever hit THIS serve — never a sibling's
    or a co-tenant's.
    """

    def __init__(self, binary, port, directives):
        self.binary = binary
        self.port = port
        self.directives = directives
        self.proc = None
        self.cfg = None
        self.log = None

    def __enter__(self):
        # Refuse to squat a port a sibling owns: driving someone else's serve
        # would be a contaminated result, not a conformance verdict.
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=0.5):
                raise SystemExit(
                    f"HARNESS ERROR: 127.0.0.1:{self.port} already in use "
                    f"(a sibling serve?) — pick a free --base-port."
                )
        except OSError:
            pass

        fd, self.cfg = tempfile.mkstemp(prefix="drorb-dos-", suffix=".conf")
        with os.fdopen(fd, "w") as f:
            f.write(self.directives + "\n")
        self.log = open(f"/tmp/drorb-dos-{self.port}.log", "w")
        env = dict(os.environ, DRORB_CONFIG=self.cfg)
        self.proc = subprocess.Popen(
            [self.binary, "--bind", f"127.0.0.1:{self.port}", "--no-udp",
             "--io", os.environ.get("DOS_IO", "auto")],
            stdout=self.log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
            env=env,
        )
        if not wait_listen(self.port, self.proc):
            self.__exit__(None, None, None)
            raise SystemExit(f"serve never bound on :{self.port}")
        return self

    def __exit__(self, *exc):
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait(timeout=5)
        if self.log:
            self.log.close()
        if self.cfg and os.path.exists(self.cfg):
            os.unlink(self.cfg)
        return False


def status_of(data):
    """First status code out of a raw response, or None."""
    if not data.startswith(b"HTTP/1.1 "):
        return None
    try:
        return int(data[9:12])
    except ValueError:
        return None


def one_shot(port, payload, timeout=3.0, read=4096):
    """Send payload on a fresh connection, read the first response bytes."""
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=timeout) as s:
            s.settimeout(timeout)
            s.sendall(payload)
            return s.recv(read)
    except OSError:
        return b""


GET = b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"


# ---------------------------------------------------------------------------
# 1. rate-limit 429 + refill
# ---------------------------------------------------------------------------


def check_rate(binary, port):
    # rate-limit 8 over a 1000ms window. NO max-connections: the conn-cap gate
    # runs first on the accept path and would answer 503 to the very burst this
    # check needs the rate gate to answer 429.
    with Serve(binary, port, "rate-limit 8\nrate-window 1000"):
        codes = []
        for _ in range(24):
            codes.append(status_of(one_shot(port, GET)))
        n429 = codes.count(429)
        n200 = codes.count(200)
        record(
            "dos-rate-429", "rate",
            "a burst past `rate-limit 8` in the window is refused a REAL 429 at accept",
            "at least one 429 once the bucket empties",
            f"{n200} x 200, {n429} x 429 over a 24-arrival burst",
            "PASS" if n429 > 0 else "FAIL",
        )

        # REFILL: let the window pass, then a fresh arrival must be served again.
        # A latch that tripped once and stayed tripped fails here.
        time.sleep(1.6)
        after = status_of(one_shot(port, GET))
        record(
            "dos-rate-refill", "rate",
            "the bucket REFILLS after `rate-window` — a later arrival is served again",
            "200 after the window elapses",
            f"status={after} on a fresh arrival 1.6s after the burst",
            "PASS" if after == 200 else "FAIL",
        )


# ---------------------------------------------------------------------------
# 2. conn-limit 503
# ---------------------------------------------------------------------------


def check_conn_limit(binary, port):
    with Serve(binary, port, "max-connections 4"):
        held, codes = [], []
        try:
            # Hold 10 CONCURRENT connections open from one source, each with a
            # request in flight, so the cap is exceeded simultaneously (a
            # sequential loop would never exceed a CONCURRENCY cap).
            for _ in range(10):
                try:
                    s = socket.create_connection(("127.0.0.1", port), timeout=3)
                    s.settimeout(3)
                    s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
                    held.append(s)
                except OSError:
                    codes.append(None)
            for s in held:
                try:
                    codes.append(status_of(s.recv(4096)))
                except OSError:
                    codes.append(None)
        finally:
            for s in held:
                try:
                    s.close()
                except OSError:
                    pass
        n503 = codes.count(503)
        n200 = codes.count(200)
        record(
            "dos-conn-limit-503", "conn-limit",
            "concurrent connections over `max-connections 4` are refused a REAL 503",
            "at least one 503; the under-cap connections still served",
            f"{n200} x 200, {n503} x 503 over 10 concurrent connections",
            "PASS" if n503 > 0 and n200 > 0 else "FAIL",
        )


# ---------------------------------------------------------------------------
# 3. slowloris 408
# ---------------------------------------------------------------------------


def check_slowloris(binary, port):
    with Serve(binary, port, "slowloris-timeout 400"):
        # ACTIVE drip: bytes keep arriving (so the socket idle-timeout is not what
        # reaps this) but the head does not complete until well past the deadline.
        # This must be the connection's FIRST request — only conn_seq == 0 is
        # guarded, which is the classic slowloris defense.
        head = b"GET /health HTTP/1.1\r\nHost: x\r\nX-Drip: "
        got = None
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=6) as s:
                s.settimeout(6)
                s.sendall(head)
                for _ in range(30):  # 30 x 50ms = 1.5s >> the 400ms deadline
                    try:
                        s.sendall(b"a")
                    except OSError:
                        break
                    time.sleep(0.05)
                try:
                    s.sendall(b"\r\n\r\n")
                except OSError:
                    pass
                try:
                    got = status_of(s.recv(4096))
                except OSError:
                    got = None
        except OSError:
            got = None
        record(
            "dos-slowloris-408", "slowloris",
            "a head dripped past `slowloris-timeout 400` is refused a REAL 408",
            "408 Request Timeout",
            f"status={got} after a 1.5s active byte-drip of the first request head",
            "PASS" if got == 408 else "FAIL",
        )

        # NEGATIVE CONTROL: a PROMPT request on the same armed serve is served
        # normally. Without this, a serve that 408'd everything would score a
        # false PASS above.
        prompt = status_of(one_shot(port, GET))
        record(
            "dos-slowloris-prompt-ok", "slowloris",
            "control: a prompt request under the same deadline is NOT refused",
            "200 (the gate discriminates, it does not blanket-408)",
            f"status={prompt} on a promptly-completed head",
            "PASS" if prompt == 200 else "FAIL",
        )


# ---------------------------------------------------------------------------
# 4 + 5. body-limit 413 (declared + the chunked bypass)
# ---------------------------------------------------------------------------


def check_body_limit(binary, port):
    with Serve(binary, port, "max-body-size 1024"):
        # DECLARED: Content-Length over the cap is refused before the body lands.
        # Send only the head — a conforming gate answers without reading a body.
        declared = (
            b"POST /health HTTP/1.1\r\nHost: x\r\n"
            b"Content-Length: 65536\r\n\r\n"
        )
        got_declared = status_of(one_shot(port, declared))
        record(
            "dos-body-413-declared", "body-limit",
            "a declared Content-Length over `max-body-size 1024` is refused a REAL 413",
            "413 Content Too Large, body never read",
            f"status={got_declared} for Content-Length: 65536 (head only, no body sent)",
            "PASS" if got_declared == 413 else "FAIL",
        )

        # CHUNKED BYPASS: no Content-Length at all, so the declared check above is
        # blind. The actual accumulated bytes must trip the cap mid-stream.
        got_chunked = None
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=4) as s:
                s.settimeout(4)
                s.sendall(
                    b"POST /health HTTP/1.1\r\nHost: x\r\n"
                    b"Transfer-Encoding: chunked\r\n\r\n"
                )
                # Push 8 x 512B chunks = 4096B of body, no Content-Length anywhere.
                # The cap (1024) is crossed at the third chunk.
                for _ in range(8):
                    try:
                        s.sendall(b"200\r\n" + b"z" * 512 + b"\r\n")
                    except OSError:
                        break
                    time.sleep(0.02)
                try:
                    s.sendall(b"0\r\n\r\n")
                except OSError:
                    pass
                try:
                    got_chunked = status_of(s.recv(4096))
                except OSError:
                    got_chunked = None
        except OSError:
            got_chunked = None
        record(
            "dos-body-413-chunked", "body-limit",
            "THE BYPASS: a chunked body (NO Content-Length) over the cap is still 413",
            "413 — the gate bounds ACTUAL bytes, not just the declared length",
            f"status={got_chunked} for 4096B of chunked body, no Content-Length",
            "PASS" if got_chunked == 413 else "FAIL",
        )

        # NEGATIVE CONTROL: an UNDER-cap body is served normally, so the two 413s
        # above are a real bound and not a serve that refuses every POST.
        under = (
            b"POST /health HTTP/1.1\r\nHost: x\r\nContent-Length: 16\r\n"
            b"Connection: close\r\n\r\n" + b"y" * 16
        )
        got_under = status_of(one_shot(port, under))
        record(
            "dos-body-under-cap-ok", "body-limit",
            "control: an under-cap body is NOT refused (the cap is a bound, not a ban)",
            "a served status (not 413)",
            f"status={got_under} for a 16-byte body under the 1024 cap",
            "PASS" if got_under is not None and got_under != 413 else "FAIL",
        )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--serve", default=os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane"))
    ap.add_argument("--base-port", type=int, default=18940)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()

    if not os.access(args.serve, os.X_OK):
        print(f"error: serve binary not executable: {args.serve}", file=sys.stderr)
        return 2

    p = args.base_port
    print(f"== DoS-gate battery ==\nserve: {args.serve}\n")
    check_rate(args.serve, p)
    check_conn_limit(args.serve, p + 1)
    check_slowloris(args.serve, p + 2)
    check_body_limit(args.serve, p + 3)

    npass = sum(1 for r in RESULTS if r["verdict"] == "PASS")
    total = len(RESULTS)
    print("\n" + "-" * 74)
    print(f"SCORE: {npass}/{total} passed")
    if args.json:
        with open(args.json, "w") as f:
            json.dump(dict(passed=npass, total=total, results=RESULTS), f, indent=2)
        print(f"wrote {args.json}")
    return 0 if npass == total else 1


if __name__ == "__main__":
    sys.exit(main())
