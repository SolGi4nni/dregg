#!/usr/bin/env python3
"""Malformed / boundary / adversarial HTTP fuzzer for the drorb serve.

Owns the serve lifecycle so it can detect a crash unambiguously (the child
process exits) rather than guessing from a dropped connection. Throws two
families of input at the running dataplane:

  1. STRUCTURED cases — hand-authored adversarial requests, each named and
     reproducible: truncated requests, header-count bombs, oversized headers,
     bad chunked encodings, embedded NULs, overlong URIs, integer-boundary
     Content-Length / Range, request smuggling (CL+TE, double CL), CRLF
     injection / response-splitting probes, pipeline floods, slowloris partial
     sends.
  2. MUTATION cases — a seeded random mutator over a small corpus of valid-ish
     requests (bit flips, byte insert/delete, field corruption, CRLF spraying,
     NUL injection, truncation). The seed is printed so any finding replays.

Classification per case:
  CRASH      the serve child process died (poll() != None) OR a post-case
             liveness probe (fresh GET /health) fails while the process is gone.
  HANG       a COMPLETE, well-framed request drew no response within the read
             timeout while the serve is still alive (should have answered).
  VIOLATION  the serve answered but the response breaks a safety invariant:
             attacker-controlled CRLF reflected into the header block (response
             splitting), or a raw non-HTTP response line.
  OK         well-formed rejection (4xx/close) or a valid response. Expected and
             welcome — a clean 400 on garbage is CORRECT behavior, not a bug.

Only CRASH / HANG / VIOLATION are bugs. Everything is scored from an ACTUAL
socket exchange; nothing is asserted without a run.

Usage:
    fuzz_serve.py --port 18937 [--bin PATH] [--cases 3000] [--seed 0]
                  [--no-manage]   # drive an already-running serve, no lifecycle
"""
import argparse
import json
import os
import random
import socket
import subprocess
import sys
import time

# --------------------------------------------------------------------------
# serve lifecycle
# --------------------------------------------------------------------------

class Serve:
    """Owns the dataplane child so a crash is observable as proc death."""

    def __init__(self, binpath, port, manage=True):
        self.binpath = binpath
        self.port = port
        self.manage = manage
        self.proc = None
        self.log = f"/tmp/fuzz-serve-{port}.log"

    def start(self):
        if not self.manage:
            return self._wait_up(20)
        self._reap_port()
        f = open(self.log, "ab")
        self.proc = subprocess.Popen(
            [self.binpath, "--bind", f"127.0.0.1:{self.port}",
             "--no-udp", "--io", os.environ.get("FUZZ_IO", "auto")],
            stdout=f, stderr=f, stdin=subprocess.DEVNULL,
            start_new_session=True)
        return self._wait_up(30)

    def _reap_port(self):
        # best-effort: kill anything already on our port (a prior run of ours)
        try:
            out = subprocess.run(["bash", "-c", f"lsof -ti tcp:{self.port} 2>/dev/null"],
                                 capture_output=True, text=True).stdout.split()
            for pid in out:
                try:
                    os.kill(int(pid), 9)
                except Exception:
                    pass
            if out:
                time.sleep(0.4)
        except Exception:
            pass

    def _wait_up(self, tries):
        for _ in range(tries):
            try:
                with socket.create_connection(("127.0.0.1", self.port), timeout=1):
                    return True
            except OSError:
                time.sleep(0.3)
        return False

    def alive(self):
        """True iff the child is still running (managed) or the port answers."""
        if self.manage:
            return self.proc is not None and self.proc.poll() is None
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=1):
                return True
        except OSError:
            return False

    def liveness(self):
        """Fresh, well-formed GET /health must return 200 within a short budget."""
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=3) as s:
                s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
                s.settimeout(3)
                buf = b""
                while len(buf) < 64:
                    chunk = s.recv(1024)
                    if not chunk:
                        break
                    buf += chunk
                return buf.startswith(b"HTTP/1.1 200")
        except OSError:
            return False

    def tail_log(self, n=40):
        try:
            with open(self.log, "rb") as f:
                data = f.read()
            return data[-4000:].decode("utf-8", "replace").splitlines()[-n:]
        except Exception:
            return []

    def proc_died(self):
        """Managed mode only: True iff the child PROCESS has actually exited
        (a hard crash), as opposed to being alive-but-unresponsive."""
        return self.manage and self.proc is not None and self.proc.poll() is not None

    def settled_dead(self, window=8.0):
        """Probe repeatedly over `window` seconds. Returns a verdict dict:
          {"dead": bool, "proc_died": bool, "recovered": bool, "rc": int|None}
        `dead` is True only if the serve NEVER answered a fresh liveness probe
        within the window (a real hang/crash). If it answered on any retry the
        failure was a transient stall and `recovered` is True, `dead` False.
        This is what separates a genuine crash from accept-backlog/thread churn."""
        deadline = time.time() + window
        proc_died = False
        while time.time() < deadline:
            if self.proc_died():
                proc_died = True  # a dead process will not recover
                break
            if self.liveness():
                return {"dead": False, "proc_died": False, "recovered": True,
                        "rc": None}
            time.sleep(0.4)
        rc = self.proc.poll() if (self.manage and self.proc) else None
        # one last chance for a slow-but-alive server
        if not proc_died and self.liveness():
            return {"dead": False, "proc_died": False, "recovered": True, "rc": None}
        return {"dead": True, "proc_died": proc_died, "recovered": False, "rc": rc}

    def stop(self):
        if self.proc and self.proc.poll() is None:
            try:
                self.proc.terminate()
                self.proc.wait(timeout=3)
            except Exception:
                try:
                    self.proc.kill()
                except Exception:
                    pass


# --------------------------------------------------------------------------
# raw exchange
# --------------------------------------------------------------------------

def exchange(port, payload, *, read_timeout=4.0, slow=False, hold=False,
             chunk_delay=0.05):
    """Send `payload` and collect whatever comes back.

    slow  — dribble the bytes one small chunk at a time (slowloris flavor).
    hold  — after sending, keep the socket open through the read window
            (do not half-close) to probe partial-request handling.
    Returns (response_bytes, timed_out_bool, error_or_None).
    """
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=3)
    except OSError as e:
        return b"", False, f"connect: {e}"
    resp = b""
    timed_out = False
    try:
        if slow:
            for i in range(0, len(payload), 3):
                s.sendall(payload[i:i + 3])
                time.sleep(chunk_delay)
        else:
            s.sendall(payload)
        if not hold:
            try:
                s.shutdown(socket.SHUT_WR)
            except OSError:
                pass
        s.settimeout(read_timeout)
        deadline = time.time() + read_timeout
        while time.time() < deadline:
            try:
                chunk = s.recv(4096)
            except socket.timeout:
                timed_out = True
                break
            except OSError as e:
                return resp, timed_out, f"recv: {e}"
            if not chunk:
                break
            resp += chunk
            if len(resp) > 1 << 20:
                break
    finally:
        try:
            s.close()
        except OSError:
            pass
    return resp, timed_out, None


# --------------------------------------------------------------------------
# structured adversarial cases
# --------------------------------------------------------------------------

def structured_cases():
    """Yield dicts: name, payload(bytes), complete(bool), kwargs for exchange,
    and an optional splitting-marker to check for reflected CRLF injection."""
    C = []

    def add(name, payload, complete=True, **kw):
        C.append({"name": name, "payload": payload, "complete": complete, "kw": kw})

    # --- truncation ---
    add("truncated-request-line", b"GET /", complete=False)
    add("truncated-headers-no-crlfcrlf", b"GET / HTTP/1.1\r\nHost: x\r\n", complete=False)
    add("only-method", b"GET", complete=False)
    add("empty-request", b"", complete=False)
    add("just-crlf", b"\r\n")
    add("just-crlfcrlf", b"\r\n\r\n")
    add("bare-lf-lines", b"GET / HTTP/1.1\nHost: x\n\n")

    # --- oversized / count bombs ---
    add("overlong-uri-64k", b"GET /" + b"a" * 65536 + b" HTTP/1.1\r\nHost: x\r\n\r\n")
    add("overlong-uri-1m", b"GET /" + b"a" * (1 << 20) + b" HTTP/1.1\r\nHost: x\r\n\r\n")
    add("huge-single-header-1m",
        b"GET / HTTP/1.1\r\nHost: x\r\nX-Big: " + b"z" * (1 << 20) + b"\r\n\r\n")
    hdrbomb = b"".join(b"X-H%d: v\r\n" % i for i in range(10000))
    add("header-count-bomb-10k", b"GET / HTTP/1.1\r\nHost: x\r\n" + hdrbomb + b"\r\n")
    add("header-count-bomb-100k",
        b"GET / HTTP/1.1\r\nHost: x\r\n" + b"".join(b"X-H%d: v\r\n" % i for i in range(100000)) + b"\r\n")
    add("long-method-64k", b"A" * 65536 + b" / HTTP/1.1\r\nHost: x\r\n\r\n")
    add("many-empty-header-values",
        b"GET / HTTP/1.1\r\nHost: x\r\n" + b"X:\r\n" * 5000 + b"\r\n")

    # --- NUL / control chars ---
    add("nul-in-uri", b"GET /a\x00b HTTP/1.1\r\nHost: x\r\n\r\n")
    add("nul-in-header-value", b"GET / HTTP/1.1\r\nHost: x\r\nX-Y: a\x00b\r\n\r\n")
    add("nul-in-header-name", b"GET / HTTP/1.1\r\nHost: x\r\nX\x00Y: v\r\n\r\n")
    add("all-controls-uri", b"GET /" + bytes(range(1, 32)) + b" HTTP/1.1\r\nHost: x\r\n\r\n")
    add("high-bytes-header", b"GET / HTTP/1.1\r\nHost: x\r\nX-Hi: " + bytes(range(128, 256)) + b"\r\n\r\n")

    # --- bad chunked encodings ---
    add("chunk-bad-size-hex",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\nZZZ\r\ndata\r\n0\r\n\r\n")
    add("chunk-negative-size",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n-5\r\ndata\r\n0\r\n\r\n")
    add("chunk-huge-size",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\nffffffffffffffff\r\nx\r\n0\r\n\r\n")
    add("chunk-size-no-data",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n10\r\n", complete=False)
    add("chunk-missing-terminator",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n4\r\ndata\r\n", complete=False)
    add("chunk-ext-bomb",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n4;" + b"a" * 65536 + b"\r\ndata\r\n0\r\n\r\n")
    add("chunk-lf-only",
        b"POST /e HTTP/1.1\nHost: x\nTransfer-Encoding: chunked\n\n4\ndata\n0\n\n")

    # --- integer-boundary Content-Length ---
    for cl in ["-1", "18446744073709551616", "99999999999999999999999999",
               "+5", "0x10", " 5", "5 ", "0 0", "", "9999999999"]:
        add(f"content-length={cl!r}",
            b"POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: " + cl.encode("latin1") +
            b"\r\n\r\nbody", complete=False)
    add("content-length-huge-no-body",
        b"POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 4294967296\r\n\r\n", complete=False)
    add("double-content-length",
        b"POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nContent-Length: 5\r\n\r\nbody")
    add("cl-and-te-smuggle",
        b"POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\nGET /admin HTTP/1.1\r\n\r\n")
    add("te-then-cl-smuggle",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nContent-Length: 4\r\n\r\n0\r\n\r\n")
    add("te-obs-fold-smuggle",
        b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding:\r\n chunked\r\nContent-Length: 4\r\n\r\n0\r\n\r\n")

    # --- Range integer boundaries ---
    for rg in ["bytes=0-18446744073709551616", "bytes=-1", "bytes=0-0,1-1," + "2-2," * 10000,
               "bytes=99999999999999999999-", "bytes=" + "0" * 100000 + "-", "bytes=0-,-0",
               "bytes=1-0"]:
        add(f"range={rg[:32]!r}",
            b"GET /health HTTP/1.1\r\nHost: x\r\nRange: " + rg.encode("latin1") + b"\r\nConnection: close\r\n\r\n")

    # --- version / method oddities ---
    add("http-0.9-style", b"GET /\r\n")
    add("http-9.9-version", b"GET / HTTP/9.9\r\nHost: x\r\n\r\n")
    add("bad-version-token", b"GET / HHHH/1.1\r\nHost: x\r\n\r\n")
    add("version-no-slash", b"GET / HTTP1.1\r\nHost: x\r\n\r\n")
    add("space-in-method", b"GE T / HTTP/1.1\r\nHost: x\r\n\r\n")
    add("tab-separators", b"GET\t/\tHTTP/1.1\r\nHost: x\r\n\r\n")
    add("many-spaces", b"GET   /   HTTP/1.1\r\nHost: x\r\n\r\n")
    add("lowercase-method", b"get / HTTP/1.1\r\nHost: x\r\n\r\n")
    add("weird-method", b"\x01\x02\x03 / HTTP/1.1\r\nHost: x\r\n\r\n")
    add("connect-authority", b"CONNECT evil:443 HTTP/1.1\r\nHost: x\r\n\r\n")

    # --- CRLF / response-splitting reflection probes ---
    # marker: if these injected header bytes appear verbatim in the RESPONSE
    # header block, that is a response-splitting VIOLATION.
    add("crlf-in-uri-split",
        b"GET /a%0d%0aInjected-Header:%20pwned HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
    add("raw-crlf-in-uri",
        b"GET /a\r\nInjected-Header: pwned\r\n / HTTP/1.1\r\nHost: x\r\n\r\n")
    add("crlf-in-header-value",
        b"GET /health HTTP/1.1\r\nHost: x\r\nX-Ref: a\r\nInjected-Header: pwned\r\nConnection: close\r\n\r\n")
    add("obs-fold-header",
        b"GET /health HTTP/1.1\r\nHost: x\r\nX-Fold: a\r\n\tb\r\nConnection: close\r\n\r\n")
    add("reflect-host-injection",
        b"GET /health HTTP/1.1\r\nHost: x\r\nInjected-Header: pwned\r\nConnection: close\r\n\r\n")

    # --- duplicate / missing / malformed structure ---
    add("no-host", b"GET / HTTP/1.1\r\n\r\n")
    add("multi-host", b"GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n")
    add("header-no-colon", b"GET / HTTP/1.1\r\nHost: x\r\nBadHeaderNoColon\r\n\r\n")
    add("header-leading-space", b"GET / HTTP/1.1\r\n Host: x\r\n\r\n")
    add("colon-only-header", b"GET / HTTP/1.1\r\nHost: x\r\n: value\r\n\r\n")
    add("huge-header-name",
        b"GET / HTTP/1.1\r\nHost: x\r\n" + b"N" * 65536 + b": v\r\n\r\n")
    add("crlfcrlf-early", b"\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n")
    add("leading-whitespace", b"    GET / HTTP/1.1\r\nHost: x\r\n\r\n")

    # --- binary garbage ---
    add("random-binary-256", bytes((i * 37 + 11) & 0xFF for i in range(256)))
    add("all-zeros-1k", b"\x00" * 1024)
    add("all-ff-1k", b"\xff" * 1024)
    add("tls-clienthello-lookalike",
        b"\x16\x03\x01\x02\x00\x01\x00\x01\xfc\x03\x03" + b"\x00" * 500)

    return C


# --------------------------------------------------------------------------
# mutation fuzzer
# --------------------------------------------------------------------------

CORPUS = [
    b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n",
    b"GET / HTTP/1.1\r\nHost: x\r\nAccept-Encoding: gzip\r\nConnection: close\r\n\r\n",
    b"POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello",
    b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n",
    b"GET /health HTTP/1.1\r\nHost: x\r\nRange: bytes=0-10\r\nIf-None-Match: \"abc\"\r\n\r\n",
    b"GET /health HTTP/1.1\r\nHost: x\r\n" + b"".join(b"X-H%d: v\r\n" % i for i in range(20)) + b"\r\n",
    b"GET /../../etc/passwd HTTP/1.1\r\nHost: x\r\n\r\n",
    b"OPTIONS * HTTP/1.1\r\nHost: x\r\nOrigin: http://evil\r\n\r\n",
]

INJECT = [b"\x00", b"\r\n", b"\n", b"\r", b":", b" ", b"\t", b"\xff", b"%00",
          b"\r\nX: y", b"AAAA" * 64, b"9999999999", b"-1", b";"]


def mutate(rng, seed_bytes):
    b = bytearray(seed_bytes)
    n = rng.randint(1, 8)
    for _ in range(n):
        if not b:
            b = bytearray(b"GET / HTTP/1.1\r\n\r\n")
        op = rng.randint(0, 8)
        if op == 0:  # bit flip
            i = rng.randrange(len(b))
            b[i] ^= 1 << rng.randrange(8)
        elif op == 1:  # byte set random
            i = rng.randrange(len(b))
            b[i] = rng.randrange(256)
        elif op == 2:  # delete a span
            i = rng.randrange(len(b))
            del b[i:i + rng.randint(1, 16)]
        elif op == 3:  # insert an injection token
            i = rng.randrange(len(b) + 1)
            tok = rng.choice(INJECT)
            b[i:i] = tok
        elif op == 4:  # truncate
            b = b[:rng.randrange(len(b) + 1)]
        elif op == 5:  # duplicate a span (grow)
            i = rng.randrange(len(b))
            j = min(len(b), i + rng.randint(1, 64))
            b[i:i] = b[i:j]
        elif op == 6:  # repeat CRLF
            i = rng.randrange(len(b) + 1)
            b[i:i] = b"\r\n" * rng.randint(1, 8)
        elif op == 7:  # overwrite a digit region (length corruption)
            i = rng.randrange(len(b))
            b[i:i + 1] = str(rng.choice([0, 9, -1, 2 ** 31])).encode()[:1]
        else:  # append junk
            b += bytes(rng.randrange(256) for _ in range(rng.randint(1, 128)))
    return bytes(b)


# --------------------------------------------------------------------------
# classification + driver
# --------------------------------------------------------------------------

def response_status(resp):
    if resp.startswith(b"HTTP/"):
        try:
            return int(resp.split(b" ", 2)[1])
        except Exception:
            return -1
    return None


def check_splitting(resp):
    """Attacker CRLF reflected into the header block => response splitting."""
    head = resp.split(b"\r\n\r\n", 1)[0]
    return b"Injected-Header: pwned" in head


def classify(name, resp, timed_out, err, complete, serve):
    """Return (verdict, detail). CRASH determined by caller via liveness."""
    if b"Injected-Header: pwned" in resp.split(b"\r\n\r\n", 1)[0]:
        return "VIOLATION", "attacker CRLF reflected into response header block"
    if resp and not resp.startswith(b"HTTP/"):
        # a raw, non-HTTP response line to an HTTP-ish request is suspect
        return "VIOLATION", f"non-HTTP response line: {resp[:40]!r}"
    if not resp and timed_out and complete:
        return "HANG", "complete request drew no response within read timeout"
    if err and err.startswith("connect"):
        return "CRASH?", err
    return "OK", (f"status={response_status(resp)}" if resp else
                  ("no-response(incomplete)" if not complete else "closed-no-response"))


def run(args):
    serve = Serve(args.bin, args.port, manage=not args.no_manage)
    if not serve.start():
        print(json.dumps({"fatal": "serve did not come up", "log": serve.tail_log()}))
        return 2

    findings = []
    observations = []  # informational load/behavior notes (not bugs)
    counts = {"OK": 0, "HANG": 0, "VIOLATION": 0, "CRASH": 0, "STALL": 0}
    cases_run = 0
    restarts = 0

    def record(kind, name, payload, detail, resp=b"", extra=None):
        counts[kind] = counts.get(kind, 0) + 1
        if kind != "OK":
            f = {
                "verdict": kind, "case": name, "detail": detail,
                "payload_len": len(payload),
                "payload_hex": payload[:512].hex(),
                "resp_head": resp[:200].decode("latin1", "replace"),
            }
            if extra:
                f.update(extra)
            findings.append(f)

    def after_case(name, payload):
        """Liveness gate. Returns True if serve survived (possibly after a
        transient stall). Only a serve that never recovers within the window is
        a CRASH (proc died) or HANG (proc alive but wedged)."""
        nonlocal restarts
        if serve.liveness():
            return True
        v = serve.settled_dead()
        if not v["dead"]:
            record("STALL", name, payload,
                   "liveness failed then RECOVERED — transient stall, not a crash",
                   extra={"proc_died": False, "recovered": True})
            return True
        kind = "CRASH" if v["proc_died"] else "HANG"
        record(kind, name, payload,
               f"serve did not recover in window (proc_died={v['proc_died']} "
               f"rc={v['rc']}); log tail: {serve.tail_log(12)}",
               extra={"proc_died": v["proc_died"], "rc": v["rc"]})
        if not args.no_manage:
            serve.stop()
            if serve.start():
                restarts += 1
                return True
        return False

    t0 = time.time()

    # ---- structured pass (liveness-checked after EVERY case) ----
    for c in structured_cases():
        resp, to, err = exchange(args.port, c["payload"], **c["kw"])
        v, detail = classify(c["name"], resp, to, err, c["complete"], serve)
        if v == "CRASH?":
            # connect failure — verify with the recovery-windowed probe
            sd = serve.settled_dead()
            if sd["dead"]:
                kind = "CRASH" if sd["proc_died"] else "HANG"
                record(kind, c["name"], c["payload"], detail, resp,
                       extra={"proc_died": sd["proc_died"], "rc": sd["rc"]})
                if not args.no_manage:
                    serve.stop(); serve.start(); restarts += 1
                cases_run += 1
                continue
            v, detail = "OK", "transient connect, serve recovered"
        record(v if v in counts else "OK", c["name"], c["payload"], detail, resp)
        cases_run += 1
        if not after_case(c["name"], c["payload"]):
            print(json.dumps({"fatal": "serve unrecoverable after structured case",
                              "case": c["name"]}))
            break

    # ---- slowloris / partial-hold pass ----
    slow_cases = [
        ("slowloris-headers", b"GET / HTTP/1.1\r\nHost: x\r\nX-A: 1\r\nX-B: 2\r\n", False,
         {"slow": True, "hold": True, "read_timeout": 6.0}),
        ("partial-hold-open", b"GET / HTTP/1.1\r\nHost: x\r\n", False,
         {"hold": True, "read_timeout": 6.0}),
        ("slow-body-drip", b"POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 100\r\n\r\nab", False,
         {"slow": True, "hold": True, "read_timeout": 6.0}),
    ]
    for name, pl, comp, kw in slow_cases:
        resp, to, err = exchange(args.port, pl, **kw)
        # informational: does the serve keep answering OTHERS while this drips?
        observations.append(
            {"case": name, "note": f"held-open resp={response_status(resp)} "
             f"timed_out={to} serves_others={serve.liveness()}"})
        counts["OK"] += 1
        cases_run += 1
        if not after_case(name, pl):  # after_case is the sole crash authority
            break

    # ---- concurrent slowloris flood (many held partials at once) ----
    held = []
    try:
        for _ in range(200):
            try:
                s = socket.create_connection(("127.0.0.1", args.port), timeout=2)
                s.sendall(b"GET / HTTP/1.1\r\nHost: x\r\n")
                held.append(s)
            except OSError:
                break
        time.sleep(1.0)
        alive = serve.liveness()
        observations.append(
            {"case": "slowloris-flood-200",
             "note": f"held={len(held)} concurrent partial conns; "
             f"serve_still_answers_new={alive}"})
        counts["OK"] += 1
        cases_run += 1
    finally:
        for s in held:
            try:
                s.close()
            except OSError:
                pass
    after_case("slowloris-flood-200", b"")

    # ---- pipeline flood (many requests one connection) ----
    for label, k in [("pipeline-100", 100), ("pipeline-5000", 5000)]:
        pl = b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n" * k
        pl = pl[:-len(b"\r\n\r\n")] + b"Connection: close\r\n\r\n"  # close last
        resp, to, err = exchange(args.port, pl, read_timeout=10.0)
        n200 = resp.count(b"HTTP/1.1 200")
        observations.append(
            {"case": label,
             "note": f"pipelined {k} reqs -> {n200} responses seen; timed_out={to}"})
        counts["OK"] += 1
        cases_run += 1
        if not after_case(label, pl[:64]):
            break

    # ---- mutation pass ----
    rng = random.Random(args.seed)
    live_check_every = 25
    mut_since_check = 0
    pending = []  # (name, payload) since last liveness check, for crash bisect
    for i in range(args.cases):
        base = rng.choice(CORPUS)
        pl = mutate(rng, base)
        name = f"mut#{i}"
        resp, to, err = exchange(args.port, pl, read_timeout=2.5)
        v, detail = classify(name, resp, to, err, True, serve)
        # HANG on a mutated (usually incomplete) request is not reliable —
        # only flag splitting/violation here; crash is caught by the periodic probe.
        if v == "VIOLATION":
            record("VIOLATION", name, pl, detail, resp)
        else:
            counts["OK"] += 1
        pending.append((name, pl))
        cases_run += 1
        mut_since_check += 1
        if mut_since_check >= live_check_every:
            mut_since_check = 0
            if not serve.liveness():
                sd = serve.settled_dead()
                if sd["dead"]:
                    # unrecovered — try to isolate the single input by replay
                    culprit, reproduced = bisect_crash(serve, args, pending)
                    kind = "CRASH" if sd["proc_died"] else "HANG"
                    record(kind, culprit[0] if culprit else "mut-batch",
                           culprit[1] if culprit else b"",
                           f"unrecovered after batch (proc_died={sd['proc_died']} "
                           f"rc={sd['rc']}); isolated_repro={reproduced}; "
                           f"log tail: {serve.tail_log(12)}",
                           extra={"proc_died": sd["proc_died"], "rc": sd["rc"],
                                  "isolated_repro": reproduced})
                    if args.no_manage or not serve.start():
                        break
                    restarts += 1
                else:
                    record("STALL", "mut-batch", b"",
                           "batch liveness stall that RECOVERED — transient, not a crash",
                           extra={"recovered": True})
            pending = []

    elapsed = time.time() - t0
    serve.stop()

    report = {
        "port": args.port,
        "cases_run": cases_run,
        "elapsed_sec": round(elapsed, 1),
        "seed": args.seed,
        "mutation_cases": args.cases,
        "restarts_after_recovery_fail": restarts,
        "counts": counts,
        "findings": findings,
        "observations": observations,
    }
    print(json.dumps(report, indent=2))
    with open(args.out, "w") as f:
        json.dump(report, f, indent=2)
    return 0


def bisect_crash(serve, args, pending):
    """Replay the pending batch on a FRESH serve to find the single input that
    kills it, and CONFIRM by re-sending that one input to a clean serve in
    isolation. Returns ((name, payload)|None, reproduced_bool). reproduced=True
    only if a single input deterministically re-kills a fresh serve — that is a
    real crashing input; otherwise the batch failure was cumulative/transient."""
    if args.no_manage:
        return None, False
    serve.stop()
    if not serve.start():
        return None, False
    suspect = None
    for name, pl in pending:
        exchange(args.port, pl, read_timeout=2.0)
        sd = serve.settled_dead(window=4.0)
        if sd["dead"]:
            suspect = (name, pl)
            break
    if suspect is None:
        return None, False
    # confirm in isolation on a fresh serve
    serve.stop()
    if not serve.start():
        return suspect, False
    exchange(args.port, suspect[1], read_timeout=2.0)
    sd = serve.settled_dead(window=4.0)
    return suspect, bool(sd["dead"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--bin", default=os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "target/release/dataplane"))
    ap.add_argument("--cases", type=int, default=3000, help="mutation case count")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--no-manage", action="store_true",
                    help="drive an already-running serve; no lifecycle/crash-restart")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    if args.out is None:
        args.out = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), f"conformance/fuzz/results_fuzz_{args.port}.json")
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
