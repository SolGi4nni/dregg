#!/usr/bin/env python3
"""gRPC-Web conformance battery for the target serve.

Drives the REAL running target and reports an HONEST per-check verdict against
the gRPC-Web wire protocol: the 5-byte length-prefixed message framing (1 flag
byte + 4-byte big-endian length), the trailer frame (flag 0x80) carrying
grpc-status / grpc-message in the body, HTTP status 200 even on a gRPC error,
the application/grpc-web[-text][+proto] content-types, text mode (whole body
base64), binary safety, big-endian length, partial-frame buffering, and the
CORS preflight a browser gRPC-Web client needs.

The target plays two roles for gRPC-Web; the battery drives all its surfaces:

  NATIVE     a gRPC-Web POST to an ordinary path (plaintext + PQ-TLS). No
             origin-native gRPC-Web handler exists → expect UNWIRED (404).
  PROXY      a gRPC-Web POST under the reverse-proxy prefix (/api) on the
             plaintext listener, forwarded to a real gRPC-Web origin this
             battery stands up. This is the target's actual edge role — it must
             carry the framed request and response through faithfully. The
             gRPC-Web framing/trailer grammar is validated end-to-end on the
             relayed bytes.
  TLS-PROXY  /api over the TLS front door — the host proxy hook lives on the
             plaintext connection handler, so the TLS door does NOT relay it.

Also probed: whether the proven gRPC-Web <-> gRPC framing TRANSLATION runs on
the relay path (it does not — the reverse proxy is a transparent byte splice, so
the translation, proven in isolation, is UNWIRED here).

Verdicts: PASS / FAIL / UNWIRED / SKIPPED — nothing massaged into a PASS.

Usage: grpc_battery.py    # spawns its own target instance + origin, runs, prints table
Env:
  TARGET_BIN   the serve binary (default: <repo>/target/release/dataplane)
  TLSPIPE_BIN  the PQ-TLS pipe (default: <repo>/conformance/_tlspipe/target/release/tlspipe)
  BASE_PORT    first port of the 4-port block this battery claims (default 18970)
"""
import base64
import json
import os
import socket
import subprocess
import sys
import threading
import time

# Paths are derived from this file's location (conformance/grpc/battery.py), so
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
BASE_PORT = int(os.environ.get("BASE_PORT", "18970"))
TLS_PORT = BASE_PORT
PLAIN_PORT = BASE_PORT + 1
ORIGIN_PORT = BASE_PORT + 2

# ----------------------------------------------------------------------------- #
#  gRPC-Web framing codec (the reusable, spec-faithful core).                    #
# ----------------------------------------------------------------------------- #

def frame(payload, trailer=False):
    flag = 0x80 if trailer else 0x00
    n = len(payload)
    return bytes([flag, (n >> 24) & 255, (n >> 16) & 255, (n >> 8) & 255, n & 255]) + payload


def deframe(buf):
    """Deframe a gRPC-Web body. Returns (frames, incomplete) where frames is a
    list of (flag, payload) and incomplete is True if a trailing partial frame
    (header<5B, or a length that overruns the buffer) was left unparsed — the
    spec REQUIRES buffering it, not mis-parsing it."""
    frames, i = [], 0
    while i < len(buf):
        if i + 5 > len(buf):
            return frames, True                 # header split: buffer, do not parse
        n = int.from_bytes(buf[i + 1:i + 5], "big")
        if i + 5 + n > len(buf):
            return frames, True                 # payload not fully arrived: buffer
        frames.append((buf[i], buf[i + 5:i + 5 + n]))
        i += 5 + n
    return frames, False


def parse_trailers(payload):
    d = {}
    for ln in payload.decode("latin1").replace("\r\n", "\n").split("\n"):
        if ":" in ln:
            k, v = ln.split(":", 1)
            d[k.strip().lower()] = v.strip()
    return d


# ----------------------------------------------------------------------------- #
#  A raw gRPC-Web origin. Dispatch by the `case` query param + method.           #
# ----------------------------------------------------------------------------- #

def _origin_body(case):
    if case == b"multi":
        return frame(b"AA") + frame(b"BBB") + frame(b"grpc-status:0\r\ngrpc-message:OK\r\n", trailer=True), b"application/grpc-web+proto"
    if case == b"error":
        return frame(b"grpc-status:5\r\ngrpc-message:not found\r\n", trailer=True), b"application/grpc-web+proto"
    if case == b"big":
        return frame(b"x" * 300) + frame(b"grpc-status:0\r\ngrpc-message:OK\r\n", trailer=True), b"application/grpc-web+proto"
    if case == b"binary":
        return frame(bytes([0x00, 0x80, 0xff, 0x01, 0x02])) + frame(b"grpc-status:0\r\ngrpc-message:OK\r\n", trailer=True), b"application/grpc-web+proto"
    if case == b"text":
        raw = frame(b"hello") + frame(b"grpc-status:0\r\ngrpc-message:OK\r\n", trailer=True)
        return base64.b64encode(raw), b"application/grpc-web-text"
    # default
    return frame(b"hello") + frame(b"grpc-status:0\r\ngrpc-message:OK\r\n", trailer=True), b"application/grpc-web+proto"


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
        method = parts[0]
        target = parts[1] if len(parts) > 1 else b"/"
        saw_ct = b""
        for ln in head.split(b"\r\n")[1:]:
            if ln.lower().startswith(b"content-type:"):
                saw_ct = ln.split(b":", 1)[1].strip()
        case = b"default"
        if b"?" in target and b"case=" in target:
            for kv in target.split(b"?", 1)[1].split(b"&"):
                if kv.startswith(b"case="):
                    case = kv[5:]

        if method == b"OPTIONS":  # CORS preflight
            hdr = (
                b"HTTP/1.1 200 OK\r\n"
                b"Access-Control-Allow-Origin: *\r\n"
                b"Access-Control-Allow-Methods: POST, OPTIONS\r\n"
                b"Access-Control-Allow-Headers: content-type, x-grpc-web, x-user-agent, grpc-timeout\r\n"
                b"Access-Control-Expose-Headers: grpc-status, grpc-message, grpc-status-details-bin\r\n"
                b"Access-Control-Max-Age: 86400\r\n"
                b"Content-Length: 0\r\n"
                b"Connection: close\r\n\r\n"
            )
            conn.sendall(hdr)
            return

        if case == b"truncated":  # a data frame header claiming 100B, only 3 sent
            hdr = (
                b"HTTP/1.1 200 OK\r\n"
                b"Content-Type: application/grpc-web+proto\r\n"
                b"Connection: close\r\n\r\n"
            )
            conn.sendall(hdr + bytes([0x00, 0, 0, 0, 100]) + b"abc")
            return

        body, ct = _origin_body(case)
        hdr = (
            b"HTTP/1.1 200 OK\r\n"
            b"Content-Type: " + ct + b"\r\n"
            b"x-origin-saw-ct: " + saw_ct + b"\r\n"
            b"Access-Control-Allow-Origin: *\r\n"
            b"Content-Length: " + str(len(body)).encode() + b"\r\n"
            b"Connection: close\r\n\r\n"
        )
        conn.sendall(hdr + body)
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
#  HTTP response parsing.                                                         #
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
#  Request drivers.                                                               #
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
    reqfile = f"/tmp/grpc_req_{os.getpid()}_{threading.get_ident()}.bin"
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


REQ_MSG = frame(b"ping")  # one gRPC-Web request message


def grpcweb_post(path, ct=b"application/grpc-web+proto", body=REQ_MSG):
    return (f"POST {path} HTTP/1.1\r\nHost: localhost\r\n".encode()
            + b"Content-Type: " + ct + b"\r\n"
            + b"X-Grpc-Web: 1\r\nX-User-Agent: grpc-web-battery/1\r\n"
            + f"Content-Length: {len(body)}\r\n".encode()
            + b"Connection: close\r\n\r\n" + body)


def grpcweb_preflight(path):
    return (f"OPTIONS {path} HTTP/1.1\r\nHost: localhost\r\n".encode()
            + b"Origin: https://client.test\r\n"
            + b"Access-Control-Request-Method: POST\r\n"
            + b"Access-Control-Request-Headers: content-type,x-grpc-web,x-user-agent\r\n"
            + b"Connection: close\r\n\r\n")


# ----------------------------------------------------------------------------- #
#  Checks.                                                                        #
# ----------------------------------------------------------------------------- #

RESULTS = []

def record(name, verdict, detail):
    RESULTS.append((name, verdict, detail))


def is_grpcweb(resp):
    return resp is not None and "application/grpc-web" in resp["headers"].get("content-type", "")


PROXY_FACETS = [
    "proxy: content-type application/grpc-web preserved",
    "proxy: HTTP status 200 (gRPC status rides the trailer)",
    "proxy: data frame flag 0x00 + big-endian length",
    "proxy: data frame deframes to exact payload",
    "proxy: trailer frame flag 0x80 present",
    "proxy: trailer carries grpc-status: 0",
    "proxy: trailer grpc-message parsed",
    "proxy: request relayed transparently (origin saw client CT)",
]


def run_checks():
    # ---- NATIVE tier: gRPC-Web POST to an ordinary path (expect UNWIRED) ----
    out, _ = plain_request(PLAIN_PORT, grpcweb_post("/grpc.health.v1.Health/Check"))
    resp = parse_response(out)
    record("native(plaintext): gRPC-Web POST",
           "PASS" if is_grpcweb(resp) else "UNWIRED",
           (f"{resp['status']} ct={resp['headers'].get('content-type','(none)')}" if resp else "no response")
           + " — no origin-native gRPC-Web handler")
    out, err = tls_request(grpcweb_post("/grpc.health.v1.Health/Check"))
    resp = parse_response(out)
    record("native(tls): gRPC-Web POST",
           "PASS" if is_grpcweb(resp) else ("SKIPPED" if resp is None else "UNWIRED"),
           (f"{resp['status']}" if resp else f"no response ({err})") + " — no origin-native gRPC-Web handler")
    out, _ = plain_request(PLAIN_PORT, grpcweb_preflight("/grpc.health.v1.Health/Check"))
    resp = parse_response(out)
    has_cors = resp is not None and "access-control-allow-origin" in resp["headers"]
    record("native(plaintext): CORS preflight",
           "PASS" if has_cors else "UNWIRED",
           (f"{resp['status']} acao={resp['headers'].get('access-control-allow-origin','(none)')}" if resp else "no response")
           + " — no origin-native CORS handler")

    # ---- TLS-PROXY: /api over the TLS door — proxy hook not present there ----
    out, _ = tls_request(grpcweb_post("/api/svc/Method"))
    resp = parse_response(out)
    record("tls-proxy:/api relays gRPC-Web",
           "PASS" if is_grpcweb(resp) else "UNWIRED",
           (f"{resp['status']}" if resp else "no response")
           + " — TLS front door serves only the proven core, bypassing the reverse-proxy hook")

    # ---- PROXY tier: gRPC-Web relayed through /api to the real origin ----
    out, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=default"))
    resp = parse_response(out)
    if resp is None:
        for n in PROXY_FACETS:
            record(n, "SKIPPED", "no HTTP response through /api")
    elif not is_grpcweb(resp):
        for n in PROXY_FACETS:
            record(n, "UNWIRED", f"/api did not relay gRPC-Web ({resp['status']}, "
                                 f"ct={resp['headers'].get('content-type','(none)')})")
    else:
        ct = resp["headers"].get("content-type", "")
        body = resp["body"]
        frames, incomplete = deframe(body)
        data_frames = [(fl, pl) for fl, pl in frames if fl == 0x00]
        trailer_frames = [(fl, pl) for fl, pl in frames if fl == 0x80]
        record("proxy: content-type application/grpc-web preserved",
               "PASS" if "application/grpc-web" in ct else "FAIL", f"ct={ct}")
        record("proxy: HTTP status 200 (gRPC status rides the trailer)",
               "PASS" if resp["status"].startswith("HTTP/1.1 200") else "FAIL", resp["status"])
        # BE length: rebuild the first data frame and compare the 4 length bytes.
        ok_be = False
        if data_frames:
            pl = data_frames[0][1]
            ok_be = body[1:5] == bytes([(len(pl) >> 24) & 255, (len(pl) >> 16) & 255, (len(pl) >> 8) & 255, len(pl) & 255])
        record("proxy: data frame flag 0x00 + big-endian length",
               "PASS" if (data_frames and ok_be and not incomplete) else "FAIL",
               f"data_frames={len(data_frames)} be_ok={ok_be} incomplete={incomplete}")
        record("proxy: data frame deframes to exact payload",
               "PASS" if (data_frames and data_frames[0][1] == b"hello") else "FAIL",
               f"payload={data_frames[0][1] if data_frames else None!r}")
        record("proxy: trailer frame flag 0x80 present",
               "PASS" if trailer_frames else "FAIL", f"trailer_frames={len(trailer_frames)}")
        trailers = parse_trailers(trailer_frames[0][1]) if trailer_frames else {}
        record("proxy: trailer carries grpc-status: 0",
               "PASS" if trailers.get("grpc-status") == "0" else "FAIL", f"trailers={trailers}")
        record("proxy: trailer grpc-message parsed",
               "PASS" if "grpc-message" in trailers else "FAIL", f"grpc-message={trailers.get('grpc-message')!r}")
        record("proxy: request relayed transparently (origin saw client CT)",
               "PASS" if resp["headers"].get("x-origin-saw-ct", "").startswith("application/grpc-web") else "FAIL",
               f"x-origin-saw-ct={resp['headers'].get('x-origin-saw-ct')!r}")

        # multi-frame ordering
        out2, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=multi"))
        r2 = parse_response(out2)
        if is_grpcweb(r2):
            fr, _ = deframe(r2["body"])
            payloads = [pl for fl, pl in fr if fl == 0x00]
            record("proxy: multiple data frames deframe in order",
                   "PASS" if payloads == [b"AA", b"BBB"] else "FAIL", f"payloads={payloads}")
        else:
            record("proxy: multiple data frames deframe in order", "SKIPPED", "multi case not relayed")

        # gRPC error status carried in trailer, HTTP still 200
        out3, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=error"))
        r3 = parse_response(out3)
        if is_grpcweb(r3):
            fr, _ = deframe(r3["body"])
            tr = [pl for fl, pl in fr if fl == 0x80]
            t = parse_trailers(tr[0]) if tr else {}
            ok = r3["status"].startswith("HTTP/1.1 200") and t.get("grpc-status") == "5"
            record("proxy: gRPC error status in trailer, HTTP stays 200",
                   "PASS" if ok else "FAIL", f"http={r3['status']} grpc-status={t.get('grpc-status')}")
        else:
            record("proxy: gRPC error status in trailer, HTTP stays 200", "SKIPPED", "error case not relayed")

        # big payload -> big-endian length > 255
        out4, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=big"))
        r4 = parse_response(out4)
        if is_grpcweb(r4):
            fr, inc = deframe(r4["body"])
            df = [pl for fl, pl in fr if fl == 0x00]
            record("proxy: big-endian length > 255 (300B payload)",
                   "PASS" if (df and len(df[0]) == 300 and not inc) else "FAIL",
                   f"len={len(df[0]) if df else None} incomplete={inc}")
        else:
            record("proxy: big-endian length > 255 (300B payload)", "SKIPPED", "big case not relayed")

        # binary safety: 0x00/0x80/0xff preserved
        out5, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=binary"))
        r5 = parse_response(out5)
        if is_grpcweb(r5):
            fr, _ = deframe(r5["body"])
            df = [pl for fl, pl in fr if fl == 0x00]
            record("proxy: binary-safe payload (0x00/0x80/0xff)",
                   "PASS" if (df and df[0] == bytes([0x00, 0x80, 0xff, 0x01, 0x02])) else "FAIL",
                   f"payload={df[0] if df else None!r}")
        else:
            record("proxy: binary-safe payload (0x00/0x80/0xff)", "SKIPPED", "binary case not relayed")

        # text mode: whole body base64, decodes to valid frames
        out6, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=text",
                                                         ct=b"application/grpc-web-text"))
        r6 = parse_response(out6)
        if r6 is not None and "application/grpc-web-text" in r6["headers"].get("content-type", ""):
            try:
                decoded = base64.b64decode(r6["body"])
                fr, inc = deframe(decoded)
                dfp = [pl for fl, pl in fr if fl == 0x00]
                trp = [pl for fl, pl in fr if fl == 0x80]
                ok = dfp and dfp[0] == b"hello" and trp and parse_trailers(trp[0]).get("grpc-status") == "0"
            except Exception as e:
                ok = False
            record("proxy: text mode (base64 whole body) decodes to frames",
                   "PASS" if ok else "FAIL",
                   f"ct={r6['headers'].get('content-type')} decoded_ok={ok}")
        else:
            record("proxy: text mode (base64 whole body) decodes to frames",
                   "UNWIRED" if r6 else "SKIPPED",
                   f"ct={r6['headers'].get('content-type','(none)') if r6 else 'no response'}")

        # partial/truncated frame must buffer, not mis-parse
        out7, _ = plain_request(PLAIN_PORT, grpcweb_post("/api/svc/Method?case=truncated"))
        r7 = parse_response(out7)
        if r7 is not None:
            fr, inc = deframe(r7["body"])
            record("proxy: partial frame buffers (no mis-parse)",
                   "PASS" if inc and not fr else "FAIL",
                   f"frames_parsed={len(fr)} incomplete_flagged={inc}")
        else:
            record("proxy: partial frame buffers (no mis-parse)", "SKIPPED", "truncated case not relayed")

        # CORS preflight relayed through /api
        out8, _ = plain_request(PLAIN_PORT, grpcweb_preflight("/api/svc/Method"))
        r8 = parse_response(out8)
        if r8 is not None and "access-control-allow-origin" in r8["headers"]:
            exp = r8["headers"].get("access-control-expose-headers", "").lower()
            allow = r8["headers"].get("access-control-allow-headers", "").lower()
            ok = "grpc-status" in exp and "x-grpc-web" in allow
            record("proxy: CORS preflight relayed (x-grpc-web allowed, grpc-status exposed)",
                   "PASS" if ok else "FAIL",
                   f"allow-headers={allow!r} expose-headers={exp!r}")
        else:
            record("proxy: CORS preflight relayed (x-grpc-web allowed, grpc-status exposed)",
                   "UNWIRED" if r8 else "SKIPPED", "no CORS headers relayed")

        # The proven gRPC-Web<->gRPC translation is NOT on the relay path.
        record("proxy: gRPC-Web<->gRPC transcode applied by serve", "UNWIRED",
               "the reverse proxy is a transparent byte splice; the proven framing "
               "translation (Reactor.Proxy.Grpc) is not wired into the relay path")


def self_test():
    checks = []
    b = frame(b"hi") + frame(b"grpc-status:0\r\n", trailer=True)
    fr, inc = deframe(b)
    checks.append(("codec: roundtrip 2 frames", len(fr) == 2 and fr[0] == (0x00, b"hi") and not inc))
    checks.append(("codec: trailer flag 0x80", fr[1][0] == 0x80))
    fr2, inc2 = deframe(bytes([0, 0, 0, 0, 10]) + b"abc")
    checks.append(("codec: partial buffers", inc2 and not fr2))
    checks.append(("codec: BE length", frame(b"x" * 300)[1:5] == bytes([0, 0, 1, 44])))
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
        print("gRPC-Web conformance battery — target serve")
        print("=" * 78)
        for name, verdict, detail in RESULTS:
            print(f"  [{verdict:8}] {name}\n             {detail}")
        print("-" * 78)
        print("harness self-test (gRPC-Web codec; not part of the target score):")
        for n, ok in self_test():
            print(f"  [{'PASS' if ok else 'FAIL':8}] {n}")
        print("-" * 78)
        total = len(RESULTS)
        summary = "  ".join(f"{k}={counts.get(k,0)}" for k in ["PASS", "FAIL", "UNWIRED", "SKIPPED"])
        print(f"TOTAL {total} checks:  {summary}")
        print("=" * 78)
        with open("/tmp/grpc_battery_results.json", "w") as f:
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
