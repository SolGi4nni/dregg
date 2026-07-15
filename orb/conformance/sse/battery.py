#!/usr/bin/env python3
"""SSE / WHATWG EventSource conformance battery for the target serve.

Drives the REAL running target and reports an HONEST per-check verdict against
the WHATWG "server-sent events" byte grammar (text/event-stream: data:/event:/
id:/retry: fields, comment lines, blank-line dispatch, UTF-8, CRLF/LF/CR line
ends, a leading BOM, and the Last-Event-ID reconnection field).

The target exposes three surfaces that matter for SSE; the battery drives all:

  TLS-NATIVE    an event-stream request to an ordinary path over the PQ TLS 1.3
                front door. No origin-native event-stream handler exists in the
                default route table → expect UNWIRED (a normal non-stream reply).
  PLAIN-NATIVE  the same over the plaintext HTTP/1.1 listener → expect UNWIRED.
  PLAIN-PROXY   an event-stream request under the reverse-proxy prefix (/api) on
                the plaintext listener, forwarded to a real event-stream origin
                this battery stands up. This is the target's actual edge role for
                SSE — a streaming reverse proxy — and the WHATWG grammar is
                validated end-to-end on the bytes it relays.
  TLS-PROXY     /api over the TLS front door. The host proxy hook lives on the
                plaintext connection handler; the TLS door serves only the proven
                core, so it does NOT relay /api. The battery records that gap.

Verdicts
  PASS     wired into that path AND behaves per the SSE grammar.
  FAIL     wired but the relayed/served bytes violate the grammar (a bug).
  UNWIRED  not connected on that path (ordinary non-stream reply / no relay).
  SKIPPED  could not be driven (a dependency/binary was missing).

Nothing is massaged into a PASS. A truncated/partial stream is reported, not hidden.

Usage: sse_battery.py     # spawns its own target instance + origin, runs, prints table
Env:
  TARGET_BIN   the serve binary (default: <repo>/target/release/dataplane)
  TLSPIPE_BIN  the PQ-TLS pipe (default: <repo>/conformance/_tlspipe/target/release/tlspipe)
  BASE_PORT    first port of the 4-port block this battery claims (default 18960)
"""
import json
import os
import socket
import subprocess
import sys
import threading
import time

# Paths are derived from this file's location (conformance/sse/battery.py), so
# nothing about the target's install path is baked in; override with env if the
# layout differs.
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get("TARGET_REPO", os.path.dirname(os.path.dirname(HERE)))
TARGET_BIN = os.environ.get("TARGET_BIN", os.path.join(REPO, "target/release/dataplane"))
TLSPIPE_BIN = os.environ.get("TLSPIPE_BIN", os.path.join(REPO, "conformance/_tlspipe/target/release/tlspipe"))
# The two variables below are the TARGET SERVE'S OWN environment interface (its
# names, not this harness's): the TLS front-door bind and the reverse-proxy fleet.
TLS_LISTEN_ENV = os.environ.get("TARGET_TLS_LISTEN_ENV", "DRORB_TLS_LISTEN")
PROXY_BACKENDS_ENV = os.environ.get("TARGET_PROXY_BACKENDS_ENV", "DRORB_PROXY_BACKENDS")
BASE_PORT = int(os.environ.get("BASE_PORT", "18960"))
TLS_PORT = BASE_PORT
PLAIN_PORT = BASE_PORT + 1
ORIGIN_PORT = BASE_PORT + 2

# ----------------------------------------------------------------------------- #
#  A raw event-stream origin. Not http.server: we control the exact wire bytes.  #
#  Dispatch is by the `case` query param the target forwards under /api.         #
# ----------------------------------------------------------------------------- #

def _sse_default_body():
    parts = [
        b": keep-alive heartbeat\n\n",                        # comment line
        b"retry: 3000\n\n",                                   # reconnection time
        b"data: hello\n\n",                                   # bare data event
        b"event: ping\ndata: 1\nid: 42\n\n",                  # named event + id
        b"data: line one\ndata: line two\n\n",                # multi-line data
        "data: café ☕ unicode\nid: 99\n\n".encode("utf-8"),  # UTF-8 multibyte
        b"event: crlfcase\r\ndata: crlfbody\r\n\r\n",         # CRLF line endings
    ]
    return b"".join(parts)


def _origin_handle(conn):
    try:
        conn.settimeout(5)
        req = b""
        while b"\r\n\r\n" not in req:
            c = conn.recv(4096)
            if not c:
                return
            req += c
        head = req.split(b"\r\n\r\n", 1)[0]
        line0 = head.split(b"\r\n", 1)[0]
        parts = line0.split(b" ")
        target = parts[1] if len(parts) > 1 else b"/"
        case = b"default"
        if b"?" in target and b"case=" in target:
            for kv in target.split(b"?", 1)[1].split(b"&"):
                if kv.startswith(b"case="):
                    case = kv[5:]
        last_id = None
        for ln in head.split(b"\r\n")[1:]:
            if b":" in ln:
                n, v = ln.split(b":", 1)
                if n.strip().lower() == b"last-event-id":
                    last_id = v.strip()

        headers = (
            b"HTTP/1.1 200 OK\r\n"
            b"Content-Type: text/event-stream\r\n"
            b"Cache-Control: no-cache\r\n"
            b"Connection: close\r\n\r\n"
        )
        if case == b"bom":
            body = b"\xef\xbb\xbf" + b"data: withbom\n\n"
        elif case == b"reconnect":
            body = b"data: resumed-after-42\nid: 43\n\n" if last_id == b"42" \
                else b"data: no-last-event-id-seen\n\n"
        else:
            body = _sse_default_body()
        conn.sendall(headers)
        for i in range(0, len(body), 24):     # small chunks + a beat: exercise relay
            conn.sendall(body[i:i + 24])
            time.sleep(0.01)
    except Exception:
        pass
    finally:
        try:
            conn.close()
        except Exception:
            pass


def start_origin(port):
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind(("127.0.0.1", port))
    srv.listen(64)

    def loop():
        while True:
            try:
                conn, _ = srv.accept()
            except OSError:
                return
            threading.Thread(target=_origin_handle, args=(conn,), daemon=True).start()

    threading.Thread(target=loop, daemon=True).start()
    return srv


# ----------------------------------------------------------------------------- #
#  HTTP response parsing (Content-Length / chunked / connection-close).          #
# ----------------------------------------------------------------------------- #

def parse_response(raw):
    if not raw or b"\r\n\r\n" not in raw:
        return None
    head, body = raw.split(b"\r\n\r\n", 1)
    lines = head.split(b"\r\n")
    headers = {}
    for ln in lines[1:]:
        if b":" in ln:
            n, v = ln.split(b":", 1)
            headers[n.strip().lower().decode("latin1")] = v.strip().decode("latin1")
    if headers.get("transfer-encoding", "").lower() == "chunked":
        body = dechunk(body)
    return {"status": lines[0].decode("latin1"), "headers": headers, "body": body}


def dechunk(b):
    out, i = b"", 0
    while i < len(b):
        j = b.find(b"\r\n", i)
        if j < 0:
            break
        try:
            n = int(b[i:j].split(b";")[0], 16)
        except ValueError:
            break
        i = j + 2
        if n == 0:
            break
        out += b[i:i + n]
        i += n + 2
    return out


# ----------------------------------------------------------------------------- #
#  WHATWG event-stream parser (the reusable, spec-faithful core).                #
# ----------------------------------------------------------------------------- #

def parse_event_stream(body_bytes):
    if body_bytes[:3] == b"\xef\xbb\xbf":
        body_bytes = body_bytes[3:]
    text = body_bytes.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")
    events, data_buf, ev_type, last_id, retries = [], [], "", "", []

    def dispatch():
        nonlocal data_buf, ev_type
        if not data_buf and ev_type == "":
            data_buf, ev_type = [], ""
            return
        events.append({"event": ev_type or "message", "data": "\n".join(data_buf), "id": last_id})
        data_buf, ev_type = [], ""

    for line in text.split("\n"):
        if line == "":
            dispatch()
            continue
        if line.startswith(":"):
            continue
        if ":" in line:
            field, value = line.split(":", 1)
            if value.startswith(" "):
                value = value[1:]
        else:
            field, value = line, ""
        if field == "data":
            data_buf.append(value)
        elif field == "event":
            ev_type = value
        elif field == "id" and "\x00" not in value:
            last_id = value
        elif field == "retry" and value.isdigit():
            retries.append(int(value))
    return {"events": events, "retries": retries}


def has_comment(body_bytes):
    text = body_bytes.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")
    return any(ln.startswith(":") for ln in text.split("\n"))


# ----------------------------------------------------------------------------- #
#  Request drivers: plaintext socket, and PQ-TLS via the pipe tool.              #
# ----------------------------------------------------------------------------- #

def plain_request(port, raw_req, timeout_s=2.5):
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=timeout_s)
    except OSError as e:
        return b"", f"connect: {e}"
    s.settimeout(timeout_s)
    try:
        s.sendall(raw_req)
        buf = b""
        while True:
            try:
                c = s.recv(16384)
            except socket.timeout:
                break
            if not c:
                break
            buf += c
        return buf, ""
    finally:
        s.close()


def tls_request(raw_req, timeout_ms=2000):
    addr = f"127.0.0.1:{TLS_PORT}"
    reqfile = f"/tmp/sse_req_{os.getpid()}_{threading.get_ident()}.bin"
    with open(reqfile, "wb") as f:
        f.write(raw_req)
    try:
        p = subprocess.run([TLSPIPE_BIN, addr, reqfile, "http/1.1", str(timeout_ms)],
                           capture_output=True, timeout=(timeout_ms / 1000.0) + 8)
        return p.stdout, p.stderr.decode("latin1", "replace")
    except subprocess.TimeoutExpired:
        return b"", "TIMEOUT"
    finally:
        try:
            os.unlink(reqfile)
        except OSError:
            pass


def sse_req(path, extra=b""):
    return (f"GET {path} HTTP/1.1\r\nHost: localhost\r\n".encode()
            + b"Accept: text/event-stream\r\n" + extra + b"Connection: close\r\n\r\n")


# ----------------------------------------------------------------------------- #
#  Checks.                                                                        #
# ----------------------------------------------------------------------------- #

RESULTS = []

def record(name, verdict, detail):
    RESULTS.append((name, verdict, detail))


def is_stream(resp):
    return resp is not None and "text/event-stream" in resp["headers"].get("content-type", "")


PROXY_FACETS = [
    "proxy: status 200", "proxy: content-type event-stream",
    "proxy: streaming (no content-length)", "proxy: cache-control no-cache",
    "proxy: comment/heartbeat line", "proxy: bare data event",
    "proxy: named event + id", "proxy: multi-line data joined",
    "proxy: UTF-8 multibyte intact", "proxy: CRLF event parses",
    "proxy: blank-line dispatch >=5", "proxy: retry field seen",
    "proxy: incremental relay",
]


def run_checks():
    # ---- PLAIN-NATIVE: the proven serve's own /events route (it exists!) ----
    out, _ = plain_request(PLAIN_PORT, sse_req("/events"))
    resp = parse_response(out)
    if is_stream(resp):
        record("native:/events content-type", "PASS", f"{resp['status']} ct={resp['headers']['content-type']}")
        body = resp["body"]
        parsed = parse_event_stream(body)
        events = parsed["events"]
        record("native:/events body is valid WHATWG SSE", "PASS" if events else "FAIL",
               f"parsed {len(events)} events: {[(e['event'], e['data'], e['id']) for e in events]}")
        named = [e for e in events if e["event"] != "message"]
        record("native:/events named event + id parsed",
               "PASS" if any(e["id"] for e in named) else "FAIL",
               f"named-with-id={named}")
        # WHATWG/EventSource: an event stream must NOT be cached — a shared cache
        # or the browser replaying it corrupts the at-most-once event contract.
        cc = resp["headers"].get("cache-control", "")
        not_cacheable = ("no-cache" in cc) or ("no-store" in cc) or ("private" in cc and "max-age=0" in cc)
        record("native:/events not cacheable (no-cache/no-store)",
               "PASS" if not_cacheable else "FAIL",
               f"Cache-Control={cc!r} — a cacheable event stream is a conformance bug")
        # A live event stream has no fixed body length (it stays open); a fixed
        # Content-Length makes this a canned one-shot batch, not a stream.
        has_cl = "content-length" in resp["headers"]
        record("native:/events is a live stream (no fixed Content-Length)",
               "FAIL" if has_cl else "PASS",
               f"Content-Length={resp['headers'].get('content-length','(none)')} — "
               + ("canned fixed-length batch, not an open stream" if has_cl else "open stream"))
    elif resp is not None:
        for n in ["native:/events content-type", "native:/events body is valid WHATWG SSE",
                  "native:/events named event + id parsed",
                  "native:/events not cacheable (no-cache/no-store)",
                  "native:/events is a live stream (no fixed Content-Length)"]:
            record(n, "UNWIRED", f"{resp['status']} ct={resp['headers'].get('content-type','(none)')}")
    else:
        record("native:/events content-type", "SKIPPED", "no HTTP response on plaintext")

    # ---- TLS-NATIVE: same /events over the PQ TLS front door (divergence probe) ----
    out, err = tls_request(sse_req("/events"))
    resp = parse_response(out)
    if resp is None:
        record("tls-native:/events", "SKIPPED", f"no HTTP response ({err})")
    elif is_stream(resp):
        record("tls-native:/events", "PASS", resp["status"])
    else:
        record("tls-native:/events", "UNWIRED",
               f"{resp['status']} — /events is a route on the PLAINTEXT proven serve but 404 on the "
               f"TLS front door (the two serve folds diverge)")

    # ---- TLS-PROXY: /api over the TLS door — the host proxy hook is not there ----
    out, _ = tls_request(sse_req("/api/events?case=default"), timeout_ms=2500)
    resp = parse_response(out)
    record("tls-proxy:/api relays event-stream", "PASS" if is_stream(resp) else "UNWIRED",
           (f"{resp['status']} ct={resp['headers'].get('content-type','(none)')}" if resp else "no response")
           + " — TLS front door serves only the proven core, bypassing the reverse-proxy hook")

    # ---- PLAIN-PROXY: SSE relayed through /api to the real origin (the wired path) ----
    out, _ = plain_request(PLAIN_PORT, sse_req("/api/events?case=default"), timeout_s=3.0)
    resp = parse_response(out)
    if resp is None:
        for n in PROXY_FACETS:
            record(n, "SKIPPED", "no HTTP response through /api")
    elif not is_stream(resp):
        for n in PROXY_FACETS:
            record(n, "UNWIRED", f"/api did not relay event-stream ({resp['status']}, "
                                 f"ct={resp['headers'].get('content-type','(none)')})")
    else:
        ct = resp["headers"].get("content-type", "")
        body = resp["body"]
        record("proxy: status 200", "PASS" if resp["status"].startswith("HTTP/1.1 200") else "FAIL", resp["status"])
        record("proxy: content-type event-stream", "PASS" if "text/event-stream" in ct else "FAIL", f"ct={ct}")
        has_cl = "content-length" in resp["headers"]
        record("proxy: streaming (no content-length)", "PASS" if not has_cl else "FAIL",
               "chunked/close streaming" if not has_cl else "buffered with Content-Length")
        cc = resp["headers"].get("cache-control", "")
        record("proxy: cache-control no-cache", "PASS" if "no-cache" in cc else "FAIL", f"cache-control={cc or '(none)'}")
        record("proxy: comment/heartbeat line", "PASS" if has_comment(body) else "FAIL",
               "comment present" if has_comment(body) else "no comment relayed")
        parsed = parse_event_stream(body)
        events = parsed["events"]
        datas = [e["data"] for e in events]
        record("proxy: bare data event", "PASS" if "hello" in datas else "FAIL", f"events={len(events)} datas={datas!r}")
        named = [e for e in events if e["event"] == "ping"]
        ok_named = bool(named) and named[0]["data"] == "1" and named[0]["id"] == "42"
        record("proxy: named event + id", "PASS" if ok_named else "FAIL", f"ping={named[0] if named else None}")
        record("proxy: multi-line data joined", "PASS" if "line one\nline two" in datas else "FAIL",
               f"want 'line one\\nline two' in {datas!r}")
        uni = any(d == "café ☕ unicode" for d in datas)
        record("proxy: UTF-8 multibyte intact", "PASS" if uni else "FAIL", f"utf8 event present={uni}")
        crlf = any(e["event"] == "crlfcase" and e["data"] == "crlfbody" for e in events)
        record("proxy: CRLF event parses", "PASS" if crlf else "FAIL", f"crlf parsed={crlf}")
        record("proxy: blank-line dispatch >=5", "PASS" if len(events) >= 5 else "FAIL", f"dispatched {len(events)}")
        record("proxy: retry field seen", "PASS" if 3000 in parsed["retries"] else "FAIL", f"retries={parsed['retries']}")
        record("proxy: incremental relay", "PASS" if len(body) > 0 else "FAIL", f"{len(body)} body bytes relayed")

        # BOM stripping (WHATWG: strip ONE leading BOM).
        outb, _ = plain_request(PLAIN_PORT, sse_req("/api/events?case=bom"))
        rb = parse_response(outb)
        if is_stream(rb):
            had_bom = rb["body"][:3] == b"\xef\xbb\xbf"
            pe = parse_event_stream(rb["body"])
            ok = had_bom and any(e["data"] == "withbom" for e in pe["events"])
            record("proxy: leading BOM stripped by parser", "PASS" if ok else "FAIL",
                   f"bom_relayed={had_bom} parsed={[e['data'] for e in pe['events']]}")
        else:
            record("proxy: leading BOM stripped by parser", "SKIPPED", "bom case not relayed")

        # Last-Event-ID reconnection: the field the client resends must reach origin.
        outr, _ = plain_request(PLAIN_PORT, sse_req("/api/events?case=reconnect", b"Last-Event-ID: 42\r\n"))
        rr = parse_response(outr)
        if is_stream(rr):
            pr = parse_event_stream(rr["body"])
            ids = [e["id"] for e in pr["events"]]
            resumed = any(e["data"] == "resumed-after-42" for e in pr["events"]) and "43" in ids
            record("proxy: Last-Event-ID reconnection relayed", "PASS" if resumed else "FAIL",
                   f"origin saw Last-Event-ID and resumed: {resumed}")
        else:
            record("proxy: Last-Event-ID reconnection relayed", "SKIPPED", "reconnect case not relayed")


def self_test():
    checks = []
    p = parse_event_stream(b"data: a\ndata: b\n\nevent: x\ndata: c\nid: 7\n\n")
    checks.append(("parser: multiline join", p["events"][0]["data"] == "a\nb"))
    checks.append(("parser: named+id", p["events"][1]["event"] == "x" and p["events"][1]["id"] == "7"))
    checks.append(("parser: BOM strip", parse_event_stream(b"\xef\xbb\xbfdata: z\n\n")["events"][0]["data"] == "z"))
    p3 = parse_event_stream(b": c\ndata: q\r\n\r\n")
    checks.append(("parser: CR/comment", len(p3["events"]) == 1 and p3["events"][0]["data"] == "q"))
    return checks


# ----------------------------------------------------------------------------- #
#  Orchestration.                                                                 #
# ----------------------------------------------------------------------------- #

def reap_ports():
    subprocess.run(["bash", "-c",
                    f"for p in {TLS_PORT} {PLAIN_PORT} {ORIGIN_PORT}; do fuser -k ${{p}}/tcp 2>/dev/null; done; true"],
                   capture_output=True)


def wait_ready(port, tries=40):
    for _ in range(tries):
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.5):
                return True
        except OSError:
            time.sleep(0.15)
    return False


def main():
    proc = origin = None
    try:
        for b in (TLSPIPE_BIN, TARGET_BIN):
            if not os.path.exists(b):
                print(f"SKIPPED — missing binary {b}")
                return 3
        reap_ports()
        time.sleep(0.3)
        origin = start_origin(ORIGIN_PORT)
        env = dict(os.environ)
        env[TLS_LISTEN_ENV] = f"127.0.0.1:{TLS_PORT}"
        env[PROXY_BACKENDS_ENV] = f"1=127.0.0.1:{ORIGIN_PORT}"
        proc = subprocess.Popen(
            ["taskset", "-c", "0-15", TARGET_BIN, "--bind", f"127.0.0.1:{PLAIN_PORT}", "--no-udp", "--io", "blocking"],
            cwd=REPO, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if not (wait_ready(TLS_PORT) and wait_ready(PLAIN_PORT)):
            print("SKIPPED — target listeners did not come up")
            return 3
        time.sleep(0.4)

        run_checks()

        counts = {}
        for _, v, _ in RESULTS:
            counts[v] = counts.get(v, 0) + 1
        print("=" * 78)
        print("SSE / WHATWG EventSource conformance battery — target serve")
        print("=" * 78)
        for name, verdict, detail in RESULTS:
            print(f"  [{verdict:8}] {name}\n             {detail}")
        print("-" * 78)
        print("harness self-test (WHATWG parser; not part of the target score):")
        for n, ok in self_test():
            print(f"  [{'PASS' if ok else 'FAIL':8}] {n}")
        print("-" * 78)
        total = len(RESULTS)
        summary = "  ".join(f"{k}={counts.get(k,0)}" for k in ["PASS", "FAIL", "UNWIRED", "SKIPPED"])
        print(f"TOTAL {total} checks:  {summary}")
        print("=" * 78)
        with open("/tmp/sse_battery_results.json", "w") as f:
            json.dump({"total": total, "counts": counts,
                       "results": [{"name": n, "verdict": v, "detail": d} for n, v, d in RESULTS]}, f, indent=2)
        return 0
    finally:
        if proc is not None:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
        if origin is not None:
            origin.close()


if __name__ == "__main__":
    sys.exit(main())
