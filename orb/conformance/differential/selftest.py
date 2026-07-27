#!/usr/bin/env python3
"""Self-test for the differential harness: does it FAIL when it should?

A differ that compares two silences sees no difference. Before this file
existed, `diff.py --sut-port DEAD --ref-port DEAD` sent all 63 requests, failed
identically on both sides, found zero divergences, printed

    === 0/63 requests diverged (each divergence = a mapped gap) ===

and exited 0. A clean score for testing nothing. `multi.py` was worse: three
dead ports produced `clean (all 3 agree) : 63`.

This file pins the catches the way Hygiene/SelfTest.lean pins its own: each
check drives the real harness as a subprocess against deliberately broken
endpoints and asserts on the ACTUAL output and exit code. If someone loosens
the liveness precondition, a check here goes red.

The last checks are the other half of the vise: with two LIVE servers that
genuinely differ, the harness must still run and still report divergences. A
guard that only ever fails is no better than one that only ever passes.

    python3 conformance/differential/selftest.py        # exit 0 = all pinned

No dataplane, no nginx, no network: every server here is a thread in this
process on an ephemeral loopback port.
"""
import os
import socket
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DIFF = os.path.join(HERE, "diff.py")
MULTI = os.path.join(HERE, "multi.py")
HOST = "127.0.0.1"

FAILURES = []
CHECKS = 0


# ---------------------------------------------------------------------------
# Tiny servers, each on an ephemeral port, each shut down at the end.
class MiniServer(threading.Thread):
    """Serves one canned reply per connection, or hangs up, per `mode`.

    mode="reply"  : read the request, write `self.reply`, close.
    mode="blackhole": accept and close immediately, writing nothing. This is
                    the subtle false-green shape: the port IS open, so a naive
                    connect-only liveness check passes, yet no side ever
                    produces a response and every request "agrees".
    """

    def __init__(self, mode="reply", reply=None):
        super().__init__(daemon=True)
        self.mode = mode
        self.reply = reply or (b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n"
                               b"Content-Length: 3\r\nConnection: close\r\n\r\nhi\n")
        self.sock = socket.socket()
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind((HOST, 0))
        self.sock.listen(64)
        self.port = self.sock.getsockname()[1]
        self._stop = False

    def run(self):
        while not self._stop:
            try:
                conn, _ = self.sock.accept()
            except OSError:
                return
            try:
                if self.mode == "reply":
                    conn.settimeout(1.0)
                    try:
                        conn.recv(65536)
                    except OSError:
                        pass
                    try:
                        conn.sendall(self.reply)
                    except OSError:
                        pass
            finally:
                try:
                    conn.close()
                except OSError:
                    pass

    def stop(self):
        self._stop = True
        try:
            self.sock.close()
        except OSError:
            pass


def dead_port():
    """A port number with nothing listening: bind ephemeral, read it, close."""
    s = socket.socket()
    s.bind((HOST, 0))
    p = s.getsockname()[1]
    s.close()
    return p


def assert_dead(port):
    """Prove to the reader (and to CI) that the port really is dead."""
    try:
        c = socket.create_connection((HOST, port), timeout=0.5)
        c.close()
        return False
    except OSError:
        return True


# ---------------------------------------------------------------------------
def run_harness(script, argv, env_extra=None, timeout=180):
    env = dict(os.environ)
    # Strip the lane knobs so a check's own env is the whole story.
    for k in ("SUT_PORT", "REF_PORT", "CADDY_PORT", "H2O_PORT", "DIFF_HOST"):
        env.pop(k, None)
    if env_extra:
        env.update({k: str(v) for k, v in env_extra.items()})
    p = subprocess.run([sys.executable, script] + [str(a) for a in argv],
                       capture_output=True, text=True, env=env, timeout=timeout)
    return p.returncode, p.stdout, p.stderr


def check(name, cond, detail=""):
    global CHECKS
    CHECKS += 1
    if cond:
        print(f"  ok   {name}")
    else:
        print(f"  FAIL {name}")
        if detail:
            for ln in detail.splitlines():
                print(f"       | {ln}")
        FAILURES.append(name)


def line_with(text, *needles):
    """True if some single output line contains all needles."""
    return any(all(n in ln for n in needles) for ln in text.splitlines())


def show(label, rc, out, err, keep=6):
    body = (out + err).strip().splitlines()
    txt = "\n".join(body[-keep:]) if body else "(no output)"
    return f"{label}: exit={rc}\n{txt}"


# ---------------------------------------------------------------------------
def check_dead_ports():
    """THE CANARY: point the differ at two dead ports; it must FAIL LOUD."""
    sp, rp = dead_port(), dead_port()
    print(f"\n[1] two dead ports (sut :{sp}, ref :{rp})")
    check("ports really are dead", assert_dead(sp) and assert_dead(rp))
    rc, out, err = run_harness(DIFF, ["--sut-port", sp, "--ref-port", rp])
    both = out + err
    check("diff.py exits non-zero on dead ports", rc != 0, show("diff.py", rc, out, err))
    check("says liveness FAILED", "liveness precondition FAILED" in both,
          show("diff.py", rc, out, err))
    check("names both endpoints UNREACHABLE",
          both.count("UNREACHABLE") >= 2, show("diff.py", rc, out, err))
    check("does NOT print a divergence score (the old false green)",
          "requests diverged" not in both, show("diff.py", rc, out, err))


def check_half_dead():
    """One side live, one side dead: still a fatal, and it names the dead one."""
    live = MiniServer()
    live.start()
    dp = dead_port()
    print(f"\n[2] half-dead lane (sut :{live.port} live, ref :{dp} dead)")
    try:
        rc, out, err = run_harness(DIFF, ["--sut-port", live.port, "--ref-port", dp])
        both = out + err
        check("exits non-zero", rc != 0, show("diff.py", rc, out, err))
        check("flags the dead ref", line_with(both, "UNREACHABLE", "ref", f":{dp}"),
              show("diff.py", rc, out, err))
        check("reports the live sut as live",
              line_with(both, "live", "sut", f":{live.port}"),
              show("diff.py", rc, out, err))
        check("no divergence score", "requests diverged" not in both,
              show("diff.py", rc, out, err))
    finally:
        live.stop()


def check_blackhole():
    """Ports OPEN but nothing speaks HTTP: connect succeeds, no bytes ever.

    This is the false green a connect-only liveness check would still let
    through — both sides "agree" on 63 empty answers.
    """
    a, b = MiniServer(mode="blackhole"), MiniServer(mode="blackhole")
    a.start()
    b.start()
    print(f"\n[3] black-hole listeners (accept-then-close, :{a.port} :{b.port})")
    try:
        check("both ports accept connections", not assert_dead(a.port) and not assert_dead(b.port))
        rc, out, err = run_harness(DIFF, ["--sut-port", a.port, "--ref-port", b.port])
        both = out + err
        check("exits non-zero", rc != 0, show("diff.py", rc, out, err))
        check("liveness rejects a non-HTTP peer", "liveness precondition FAILED" in both,
              show("diff.py", rc, out, err))
        check("no divergence score", "requests diverged" not in both,
              show("diff.py", rc, out, err))
    finally:
        a.stop()
        b.stop()


def check_multi_dead():
    """multi.py had the worse version of the bug: 3 dead ports = 63 clean."""
    p1, p2, p3 = dead_port(), dead_port(), dead_port()
    print(f"\n[4] multi.py, three dead ports (:{p1} :{p2} :{p3})")
    rc, out, err = run_harness(MULTI, ["--sut-port", p1, "--caddy-port", p2,
                                       "--h2o-port", p3])
    both = out + err
    check("multi.py exits non-zero", rc != 0, show("multi.py", rc, out, err))
    check("says liveness FAILED", "liveness precondition FAILED" in both,
          show("multi.py", rc, out, err))
    check("does NOT print 'clean (all 3 agree)'", "clean (all 3 agree)" not in both,
          show("multi.py", rc, out, err))


def check_live_pair_still_works():
    """The other jaw of the vise: two LIVE servers that differ must still be
    compared, and the divergences must still be reported."""
    sut = MiniServer(reply=b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n"
                           b"Content-Type: text/plain\r\nConnection: close\r\n\r\nhi\n")
    ref = MiniServer(reply=b"HTTP/1.1 404 Not Found\r\nContent-Length: 3\r\n"
                           b"Content-Type: text/html\r\nConnection: close\r\n\r\nno\n")
    sut.start()
    ref.start()
    print(f"\n[5] two LIVE servers that differ (:{sut.port} 200 vs :{ref.port} 404)")
    try:
        rc, out, err = run_harness(DIFF, ["--sut-port", sut.port, "--ref-port", ref.port])
        both = out + err
        check("exits 0 (a live comparison is a valid run)", rc == 0,
              show("diff.py", rc, out, err))
        check("passes liveness", "liveness precondition FAILED" not in both,
              show("diff.py", rc, out, err))
        check("reports every request as diverged", "63/63 requests diverged" in both,
              show("diff.py", rc, out, err))
        check("names the status divergence", "status: sut='200' ref='404'" in both,
              show("diff.py", rc, out, err))
    finally:
        sut.stop()
        ref.stop()


def check_env_and_cli_agree():
    """The knob the launcher turns and the knob the differ reads are one knob.

    launch.sh honours $SUT_PORT/$REF_PORT; diff.py used to ignore them and use
    its own baked-in defaults, so a lane started on other ports was compared at
    18930/18931 — dead ports, clean score. Now: CLI > env > default.
    """
    sut, ref = MiniServer(), MiniServer(
        reply=b"HTTP/1.1 500 Oops\r\nContent-Length: 0\r\nConnection: close\r\n\r\n")
    sut.start()
    ref.start()
    print(f"\n[6] env/CLI knob reconciliation (live pair :{sut.port} :{ref.port})")
    try:
        # No CLI flags at all: the env must drive the ports.
        rc, out, err = run_harness(DIFF, [], env_extra={"SUT_PORT": sut.port,
                                                        "REF_PORT": ref.port})
        both = out + err
        check("$SUT_PORT/$REF_PORT drive the run with no CLI flags",
              rc == 0 and line_with(both, "live:", "sut", f":{sut.port}")
              and line_with(both, "live:", "ref", f":{ref.port}"),
              show("diff.py", rc, out, err))

        # CLI must win over env: env points at dead ports, CLI at the live pair.
        d1, d2 = dead_port(), dead_port()
        rc, out, err = run_harness(DIFF, ["--sut-port", sut.port, "--ref-port", ref.port],
                                   env_extra={"SUT_PORT": d1, "REF_PORT": d2})
        check("explicit CLI flags override the env", rc == 0,
              show("diff.py", rc, out, err))

        # And the reverse of the bug: env pointing at dead ports with no flags
        # must fail loud rather than score.
        rc, out, err = run_harness(DIFF, [], env_extra={"SUT_PORT": d1, "REF_PORT": d2})
        check("env pointing at dead ports fails loud",
              rc != 0 and "liveness precondition FAILED" in (out + err),
              show("diff.py", rc, out, err))
    finally:
        sut.stop()
        ref.stop()


def check_both_error_is_not_agreement():
    """Unit-level: compare() must never score two identical failures as clean."""
    print("\n[7] compare(): identical transport failures are not agreement")
    sys.path.insert(0, HERE)
    import diff as D
    err = "connect: [Errno 111] Connection refused"
    divs = D.compare(err, err)
    check("both-sides-errored yields a divergence", len(divs) > 0, repr(divs))
    check("it is labelled both-error",
          any(d["kind"] == "both-error" for d in divs), repr(divs))
    # And the genuine agreement case still is one: both peers answered by
    # closing the connection with no bytes (empty-request does this today).
    divs2 = D.compare(None, None)
    check("both-unparseable is still agreement (a delivered request, both closed)",
          divs2 == [], repr(divs2))
    # getattr, not attribute access: run against a diff.py that predates the
    # guard (git show HEAD~:...) this must report a red check, not crash.
    fault = getattr(D, "is_transport_fault", None)
    check("is_transport_fault distinguishes connect from recv",
          callable(fault) and fault("connect: refused") and not fault("recv: reset"))


def main():
    print("=== differential harness self-test: does it fail when it should? ===")
    t0 = time.time()
    check_dead_ports()
    check_half_dead()
    check_blackhole()
    check_multi_dead()
    check_live_pair_still_works()
    check_env_and_cli_agree()
    check_both_error_is_not_agreement()
    print(f"\n=== {CHECKS - len(FAILURES)}/{CHECKS} checks passed "
          f"in {time.time() - t0:.1f}s ===")
    if FAILURES:
        print("FAILED:")
        for f in FAILURES:
            print(f"  - {f}")
        print("\nA red check here means the harness can score a run it never ran.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
