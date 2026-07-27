#!/usr/bin/env python3
"""Deep socket-level mutation fuzzer for the WebSocket, HTTP/2 (h2c), and
chunked-body CODEC HOST GLUE of the serve — the Rust paths the in-process
seam fuzzer cannot reach: the WS reassembly / fragmentation FSM, the h2
connection host loop, and the chunked body accumulator around the proven
framer. Owns the serve child so a crash is observable as process death.

Per case a FRESH connection is used (a stateful codec fault should not be
masked by a prior case). Classification:
  CRASH      the serve child exited (proc death) — a real bug; the exact
             triggering bytes are recorded.
  HANG       a complete, well-framed exchange drew no response and no close
             within the read budget while the serve is still alive.
  5XX        the serve answered a codec probe with a 5xx (server-side error) —
             recorded as suspect (a codec fault should be a clean close/1002,
             not a 500).
  OK         clean close, protocol-error close frame, GOAWAY/RST, or a valid
             echo/response. Expected and welcome.

Every number is from an actual socket exchange. Malformed input is SUPPOSED
to be refused cleanly; a clean refusal is correct, not a finding.
"""
import argparse, json, os, random, socket, struct, subprocess, sys, time, base64, hashlib

# --------------------------------------------------------------------- serve
class Serve:
    def __init__(self, binpath, port):
        self.binpath, self.port = binpath, port
        self.proc = None
        self.log = f"/tmp/deep-serve-{port}.log"

    def _reap(self):
        try:
            out = subprocess.run(["bash","-c",f"lsof -ti tcp:{self.port} 2>/dev/null"],
                                 capture_output=True, text=True).stdout.split()
            for pid in out:
                try: os.kill(int(pid), 9)
                except Exception: pass
            if out: time.sleep(0.4)
        except Exception: pass

    def start(self):
        self._reap()
        f = open(self.log, "ab")
        self.proc = subprocess.Popen(
            [self.binpath, "--bind", f"127.0.0.1:{self.port}", "--no-udp", "--io", os.environ.get("FUZZ_IO", "auto")],
            stdout=f, stderr=f, stdin=subprocess.DEVNULL, start_new_session=True)
        for _ in range(60):
            try:
                with socket.create_connection(("127.0.0.1", self.port), timeout=1):
                    return True
            except OSError:
                if self.proc.poll() is not None:
                    return False
                time.sleep(0.3)
        return False

    def proc_died(self):
        return self.proc is not None and self.proc.poll() is not None

    def liveness(self):
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=3) as s:
                s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
                s.settimeout(3)
                buf = b""
                while len(buf) < 12:
                    c = s.recv(256)
                    if not c: break
                    buf += c
                return buf.startswith(b"HTTP/1.1 2") or buf.startswith(b"HTTP/1.1 4")
        except OSError:
            return False

    def settled_dead(self, window=6.0):
        deadline = time.time() + window
        while time.time() < deadline:
            if self.proc_died(): return {"dead": True, "proc_died": True, "rc": self.proc.poll()}
            if self.liveness(): return {"dead": False, "proc_died": False, "rc": None}
            time.sleep(0.3)
        return {"dead": True, "proc_died": self.proc_died(), "rc": self.proc.poll()}

    def tail(self, n=15):
        try:
            with open(self.log,"rb") as f: d=f.read()
            return d[-3000:].decode("utf-8","replace").splitlines()[-n:]
        except Exception: return []

    def stop(self):
        if self.proc and self.proc.poll() is None:
            try: self.proc.terminate(); self.proc.wait(timeout=3)
            except Exception:
                try: self.proc.kill()
                except Exception: pass

# --------------------------------------------------------------------- ws
def ws_handshake(port, path=b"/", timeout=3.0):
    """Open a connection and complete the RFC6455 upgrade. Returns the socket
    positioned right after the 101, or None."""
    key = base64.b64encode(os.urandom(16))
    req = (b"GET " + path + b" HTTP/1.1\r\nHost: x\r\n"
           b"Upgrade: websocket\r\nConnection: Upgrade\r\n"
           b"Sec-WebSocket-Key: " + key + b"\r\nSec-WebSocket-Version: 13\r\n\r\n")
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        s.sendall(req)
        s.settimeout(timeout)
        buf = b""
        while b"\r\n\r\n" not in buf:
            c = s.recv(1024)
            if not c: s.close(); return None
            buf += c
            if len(buf) > 4096: break
        if not buf.startswith(b"HTTP/1.1 101"):
            s.close(); return None
        return s
    except OSError:
        return None

def ws_frame(fin, opcode, payload, mask=True, rsv=0, mask_key=None, length_override=None):
    b0 = (0x80 if fin else 0) | ((rsv & 7) << 4) | (opcode & 0x0F)
    n = len(payload) if length_override is None else length_override
    hdr = bytearray([b0])
    mbit = 0x80 if mask else 0
    if n < 126:
        hdr.append(mbit | n)
    elif n < 65536:
        hdr.append(mbit | 126); hdr += struct.pack(">H", n)
    else:
        hdr.append(mbit | 127); hdr += struct.pack(">Q", n)
    if mask:
        mk = mask_key if mask_key is not None else os.urandom(4)
        hdr += mk
        payload = bytes(b ^ mk[i & 3] for i, b in enumerate(payload))
    return bytes(hdr) + payload

WS_OPCODES = [0x0,0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8,0x9,0xA,0xB,0xC,0xD,0xE,0xF]

def ws_structured():
    """Named adversarial WS frame sequences (client->server)."""
    C = []
    def add(name, frames): C.append((name, frames if isinstance(frames, list) else [frames]))
    for op in WS_OPCODES:
        add(f"opcode-{op:#x}", ws_frame(True, op, b"hi", mask=True))
    for rsv in (1,2,4,7):
        add(f"rsv-{rsv}", ws_frame(True, 0x1, b"x", mask=True, rsv=rsv))
    add("unmasked-text", ws_frame(True, 0x1, b"nomask", mask=False))
    add("control-fragmented", ws_frame(False, 0x9, b"x", mask=True))
    add("control-too-big", ws_frame(True, 0x9, b"z"*126, mask=True))
    add("close-too-big", ws_frame(True, 0x8, b"z"*126, mask=True))
    add("cont-without-start", ws_frame(True, 0x0, b"orphan", mask=True))
    add("new-data-mid-fragment", [ws_frame(False,0x1,b"a",mask=True), ws_frame(False,0x2,b"b",mask=True)])
    add("double-fin-start", [ws_frame(False,0x1,b"a",mask=True), ws_frame(True,0x1,b"b",mask=True)])
    add("frag-then-cont-fin", [ws_frame(False,0x1,b"he",mask=True), ws_frame(True,0x0,b"llo",mask=True)])
    add("len-lies-bigger", ws_frame(True,0x2,b"short",mask=True,length_override=100))
    add("len-lies-smaller", ws_frame(True,0x2,b"a"*50,mask=True,length_override=2))
    add("ext16-min", ws_frame(True,0x2,b"a"*200,mask=True))
    add("ext64-huge-declared", bytes([0x82,0xFF])+struct.pack(">Q",1<<40)+b"\x00\x00\x00\x00")
    add("ext64-topbit-set", bytes([0x82,0xFF])+struct.pack(">Q",1<<63)+b"\x00\x00\x00\x00")
    add("over-16mib", ws_frame(True,0x2,b"",mask=True,length_override=(16<<20)+1))
    for code in (999,1000,1004,1005,1006,1015,1016,2999,3000,4999,5000,65535):
        add(f"close-code-{code}", ws_frame(True,0x8, struct.pack(">H",code), mask=True))
    add("close-1byte", ws_frame(True,0x8, b"\x01", mask=True))
    add("text-bad-utf8", ws_frame(True,0x1, b"\xff\xfe\xfd", mask=True))
    add("text-truncated-utf8", ws_frame(True,0x1, b"\xe2\x82", mask=True))  # incomplete 3-byte seq
    add("ping-then-text", [ws_frame(True,0x9,b"pp",mask=True), ws_frame(True,0x1,b"ok",mask=True)])
    add("nested-frag-deep", [ws_frame(False,0x1,b"a",mask=True)] + [ws_frame(False,0x0,b"b",mask=True) for _ in range(50)] + [ws_frame(True,0x0,b"c",mask=True)])
    return C

def ws_exchange(port, frames, dribble=False, read_timeout=3.0):
    s = ws_handshake(port)
    if s is None:
        return None, "no-upgrade"
    resp = b""
    try:
        payload = b"".join(frames)
        if dribble:
            for i in range(0, len(payload), 2):
                s.sendall(payload[i:i+2]); time.sleep(0.005)
        else:
            s.sendall(payload)
        s.settimeout(read_timeout)
        deadline = time.time() + read_timeout
        while time.time() < deadline:
            try: c = s.recv(4096)
            except socket.timeout: return resp, "timeout"
            except OSError as e: return resp, f"recv:{e}"
            if not c: break
            resp += c
            if len(resp) > (1<<20): break
        return resp, None
    finally:
        try: s.close()
        except OSError: pass

# --------------------------------------------------------------------- h2c
H2_PREFACE = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"
def h2_frame(length, ftype, flags, sid, payload=b""):
    return struct.pack(">I", length)[1:] + bytes([ftype & 0xFF, flags & 0xFF]) + struct.pack(">I", sid & 0x7FFFFFFF) + payload
SETTINGS_EMPTY = h2_frame(0,4,0,0)
HDR_GET = bytes([0x82,0x86,0x84,0x41,0x01,ord('x')])  # :method GET :scheme http :path / :authority x
HEADERS_GET = h2_frame(len(HDR_GET),1,0x5,1,HDR_GET)

def h2_structured():
    C = []
    def add(name, body): C.append((name, H2_PREFACE + body))
    add("valid-get", SETTINGS_EMPTY + HEADERS_GET)
    add("data-on-stream-0", SETTINGS_EMPTY + h2_frame(4,0,0,0,b"abcd"))
    add("headers-on-stream-0", SETTINGS_EMPTY + h2_frame(len(HDR_GET),1,0x5,0,HDR_GET))
    add("frame-type-unknown", SETTINGS_EMPTY + h2_frame(3,0xEF,0,1,b"xyz"))
    add("oversized-len-declared", SETTINGS_EMPTY + h2_frame(0xFFFFFF,0,0,1))
    add("settings-odd-len", H2_PREFACE[:0] + h2_frame(5,4,0,0,b"AAAAA"))  # settings len not %6
    add("settings-ack-with-body", h2_frame(1,4,0x1,0,b"A"))
    add("continuation-flood", SETTINGS_EMPTY + h2_frame(len(HDR_GET),1,0,1,HDR_GET) + b"".join(h2_frame(1,9,0,1,b"A") for _ in range(200)) + h2_frame(1,9,0x4,1,b"A"))
    add("hpack-garbage", SETTINGS_EMPTY + h2_frame(8,1,0x5,1,bytes([0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF])))
    add("hpack-huge-index", SETTINGS_EMPTY + h2_frame(6,1,0x5,1,bytes([0xFF,0xFF,0xFF,0xFF,0xFF,0x7F])))
    add("hpack-index-0", SETTINGS_EMPTY + h2_frame(1,1,0x5,1,bytes([0x80])))
    add("rst-unknown-stream", SETTINGS_EMPTY + h2_frame(4,3,0,99,b"\x00\x00\x00\x00"))
    add("window-update-0", SETTINGS_EMPTY + h2_frame(4,8,0,0,b"\x00\x00\x00\x00"))
    add("ping-len-wrong", SETTINGS_EMPTY + h2_frame(4,6,0,0,b"AAAA"))
    add("goaway-from-client", SETTINGS_EMPTY + h2_frame(8,7,0,0,b"\x00\x00\x00\x00\x00\x00\x00\x00"))
    add("priority-self-dep", SETTINGS_EMPTY + h2_frame(5,2,0,1,b"\x80\x00\x00\x01\x00"))
    add("many-empty-headers", SETTINGS_EMPTY + b"".join(HEADERS_GET for _ in range(100)))
    add("push-promise-from-client", SETTINGS_EMPTY + h2_frame(4,5,0x4,1,b"\x00\x00\x00\x02"))
    add("frame-len-1-type-loop", SETTINGS_EMPTY + b"".join(h2_frame(0,0,0,1) for _ in range(500)))
    return C

def h2_exchange(port, payload, read_timeout=3.0):
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=3)
    except OSError as e:
        return None, f"connect:{e}"
    resp = b""
    try:
        s.sendall(payload)
        s.settimeout(read_timeout)
        deadline = time.time() + read_timeout
        while time.time() < deadline:
            try: c = s.recv(4096)
            except socket.timeout: return resp, "timeout"
            except OSError as e: return resp, f"recv:{e}"
            if not c: break
            resp += c
            if len(resp) > (1<<20): break
        return resp, None
    finally:
        try: s.close()
        except OSError: pass

# --------------------------------------------------------------------- chunked (host body glue)
def chunked_structured():
    C = []
    def add(name, body, comp=True): C.append((name, body, comp))
    add("ext-bomb", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n4;"+b"a"*200000+b"\r\ndata\r\n0\r\n\r\n")
    add("trailer-bomb", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n"+b"".join(b"X-T%d: v\r\n"%i for i in range(20000))+b"\r\n")
    add("huge-chunk-size", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\nfffffffffffffff0\r\nx\r\n0\r\n\r\n")
    add("many-tiny-chunks", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n"+b"1\r\na\r\n"*50000+b"0\r\n\r\n")
    add("chunk-size-leading-zeros", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n0000000000000004\r\ndata\r\n0\r\n\r\n")
    add("crlf-in-chunk-data", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n6\r\na\r\nb\r\n0\r\n\r\n")
    add("bad-hex-then-valid", b"POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\ng\r\ndata\r\n0\r\n\r\n")
    return C

def chunked_exchange(port, payload, read_timeout=4.0):
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=3)
    except OSError as e:
        return None, f"connect:{e}"
    resp = b""
    try:
        s.sendall(payload)
        try: s.shutdown(socket.SHUT_WR)
        except OSError: pass
        s.settimeout(read_timeout)
        deadline = time.time() + read_timeout
        while time.time() < deadline:
            try: c = s.recv(4096)
            except socket.timeout: return resp, "timeout"
            except OSError as e: return resp, f"recv:{e}"
            if not c: break
            resp += c
        return resp, None
    finally:
        try: s.close()
        except OSError: pass

# --------------------------------------------------------------------- mutation
WS_CORPUS = [ws_frame(True,0x1,b"hello",mask=True), ws_frame(True,0x2,b"\x00\x01\x02",mask=True),
             ws_frame(False,0x1,b"ab",mask=True)+ws_frame(True,0x0,b"cd",mask=True),
             ws_frame(True,0x8,struct.pack(">H",1000),mask=True), ws_frame(True,0x9,b"p",mask=True)]
H2_CORPUS = [SETTINGS_EMPTY+HEADERS_GET, SETTINGS_EMPTY+h2_frame(4,0,0,1,b"data")+HEADERS_GET]

def mutate(rng, seed):
    b = bytearray(seed)
    for _ in range(rng.randint(1,6)):
        if not b: b = bytearray(b"\x00")
        op = rng.randint(0,6)
        if op==0: b[rng.randrange(len(b))] ^= 1<<rng.randrange(8)
        elif op==1: b[rng.randrange(len(b))] = rng.randrange(256)
        elif op==2:
            i=rng.randrange(len(b)); del b[i:i+rng.randint(1,8)]
        elif op==3:
            i=rng.randrange(len(b)+1); b[i:i]=bytes(rng.randrange(256) for _ in range(rng.randint(1,8)))
        elif op==4: b=b[:rng.randrange(len(b)+1)]
        elif op==5:
            i=rng.randrange(len(b)); j=min(len(b),i+rng.randint(1,32)); b[i:i]=b[i:j]
        else:
            i=rng.randrange(len(b)+1); b[i:i]=bytes([0x80,0x81,0x82,0x88,0xFF,0x7F][rng.randrange(6)])
    return bytes(b)

# --------------------------------------------------------------------- driver
def run(args):
    serve = Serve(args.bin, args.port)
    if not serve.start():
        print(json.dumps({"fatal":"serve did not come up","log":serve.tail()})); return 2
    findings=[]; counts={"OK":0,"HANG":0,"CRASH":0,"5XX":0,"NO_UPGRADE":0}; cases=0; restarts=0

    def is_5xx(resp):
        return resp and resp[:12].startswith(b"HTTP/1.1 5")

    def record(kind,label,payload,detail,resp=b""):
        counts[kind]=counts.get(kind,0)+1
        if kind!="OK":
            findings.append({"verdict":kind,"case":label,"detail":detail,
                             "payload_len":len(payload),"payload_hex":payload[:400].hex(),
                             "resp_head":resp[:120].decode("latin1","replace")})

    def after(label,payload):
        nonlocal restarts
        if serve.liveness(): return True
        v=serve.settled_dead()
        if not v["dead"]: return True
        kind="CRASH" if v["proc_died"] else "HANG"
        record(kind,label,payload,f"serve unrecovered proc_died={v['proc_died']} rc={v['rc']} log={serve.tail(10)}")
        serve.stop()
        if serve.start(): restarts+=1; return True
        return False

    # ---- WS structured ----
    for name,frames in ws_structured():
        payload=b"".join(frames)
        resp,err=ws_exchange(args.port,frames)
        if err=="no-upgrade":
            record("NO_UPGRADE",f"ws:{name}",payload,"handshake refused/absent")
        elif is_5xx(resp):
            record("5XX",f"ws:{name}",payload,"5xx to ws frame",resp)
        else:
            counts["OK"]+=1
        cases+=1
        if not after(f"ws:{name}",payload):
            print(json.dumps({"fatal":"unrecoverable","case":f"ws:{name}"})); break

    # ---- h2c structured ----
    for name,payload in h2_structured():
        resp,err=h2_exchange(args.port,payload)
        if is_5xx(resp): record("5XX",f"h2:{name}",payload,"5xx",resp)
        else: counts["OK"]+=1
        cases+=1
        if not after(f"h2:{name}",payload):
            print(json.dumps({"fatal":"unrecoverable","case":f"h2:{name}"})); break

    # ---- chunked structured ----
    for name,payload,_ in chunked_structured():
        resp,err=chunked_exchange(args.port,payload)
        if is_5xx(resp): record("5XX",f"chunk:{name}",payload,"5xx",resp)
        else: counts["OK"]+=1
        cases+=1
        if not after(f"chunk:{name}",payload): break

    # ---- WS mutation ----
    rng=random.Random(args.seed)
    for i in range(args.ws_cases):
        base=rng.choice(WS_CORPUS); pl=mutate(rng,base)
        resp,err=ws_exchange(args.port,[pl],read_timeout=0.4)
        if is_5xx(resp): record("5XX",f"ws-mut#{i}",pl,"5xx",resp)
        else: counts["OK"]+=1
        cases+=1
        if i%50==49 and not after(f"ws-mut#{i}",pl):
            print(json.dumps({"fatal":"unrecoverable","case":f"ws-mut#{i}"})); break

    # ---- h2 mutation ----
    for i in range(args.h2_cases):
        base=rng.choice(H2_CORPUS); pl=H2_PREFACE+mutate(rng,base)
        resp,err=h2_exchange(args.port,pl,read_timeout=0.4)
        if is_5xx(resp): record("5XX",f"h2-mut#{i}",pl,"5xx",resp)
        else: counts["OK"]+=1
        cases+=1
        if i%50==49 and not after(f"h2-mut#{i}",pl):
            print(json.dumps({"fatal":"unrecoverable","case":f"h2-mut#{i}"})); break

    serve.stop()
    report={"port":args.port,"cases":cases,"counts":counts,"restarts":restarts,
            "seed":args.seed,"findings":findings}
    print(json.dumps(report,indent=2))
    if args.out:
        with open(args.out,"w") as f: json.dump(report,f,indent=2)
    return 0

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--port",type=int,required=True)
    ap.add_argument("--bin",default=os.path.expanduser("~/dev/drorb/target/release/dataplane"))
    ap.add_argument("--ws-cases",type=int,default=1500)
    ap.add_argument("--h2-cases",type=int,default=1500)
    ap.add_argument("--seed",type=int,default=0)
    ap.add_argument("--out",default=None)
    args=ap.parse_args()
    if args.out is None:
        args.out=os.path.expanduser(f"~/dev/drorb/conformance/fuzz/deep/results_ws_h2_{args.port}.json")
    return run(args)

if __name__=="__main__":
    sys.exit(main())
