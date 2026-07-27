#!/usr/bin/env python3
"""Deterministically regenerate the WS-mutation stream (same seed/corpus/mutator
as deep_ws_h2_fuzz.py) and replay a window of cases ONE PER FRESH SERVE to
isolate the exact frame that aborts the serve. Prints the first index whose
single frame kills a clean serve, with its bytes."""
import os, socket, struct, subprocess, sys, time, random, base64

BIN=os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))), "target/release/dataplane")
PORT=int(sys.argv[1]) if len(sys.argv)>1 else 18956
LO=int(sys.argv[2]) if len(sys.argv)>2 else 0
HI=int(sys.argv[3]) if len(sys.argv)>3 else 350
SEED=int(sys.argv[4]) if len(sys.argv)>4 else 42

def ws_frame(fin,opcode,payload,mask=True,rsv=0):
    b0=(0x80 if fin else 0)|((rsv&7)<<4)|(opcode&0x0F); n=len(payload)
    h=bytearray([b0]); mb=0x80 if mask else 0
    if n<126: h.append(mb|n)
    elif n<65536: h.append(mb|126); h+=struct.pack(">H",n)
    else: h.append(mb|127); h+=struct.pack(">Q",n)
    if mask:
        mk=os.urandom(4); h+=mk; payload=bytes(b^mk[i&3] for i,b in enumerate(payload))
    return bytes(h)+payload
WS_CORPUS=[ws_frame(True,0x1,b"hello"),ws_frame(True,0x2,b"\x00\x01\x02"),
           ws_frame(False,0x1,b"ab")+ws_frame(True,0x0,b"cd"),
           ws_frame(True,0x8,struct.pack(">H",1000)),ws_frame(True,0x9,b"p")]
def mutate(rng,seed):
    b=bytearray(seed)
    for _ in range(rng.randint(1,6)):
        if not b: b=bytearray(b"\x00")
        op=rng.randint(0,6)
        if op==0: b[rng.randrange(len(b))]^=1<<rng.randrange(8)
        elif op==1: b[rng.randrange(len(b))]=rng.randrange(256)
        elif op==2: i=rng.randrange(len(b)); del b[i:i+rng.randint(1,8)]
        elif op==3: i=rng.randrange(len(b)+1); b[i:i]=bytes(rng.randrange(256) for _ in range(rng.randint(1,8)))
        elif op==4: b=b[:rng.randrange(len(b)+1)]
        elif op==5: i=rng.randrange(len(b)); j=min(len(b),i+rng.randint(1,32)); b[i:i]=b[i:j]
        else: i=rng.randrange(len(b)+1); b[i:i]=bytes([0x80,0x81,0x82,0x88,0xFF,0x7F][rng.randrange(6)])
    return bytes(b)

def reap():
    out=subprocess.run(["bash","-c",f"lsof -ti tcp:{PORT} 2>/dev/null"],capture_output=True,text=True).stdout.split()
    for p in out:
        try: os.kill(int(p),9)
        except Exception: pass
    if out: time.sleep(0.3)

def start():
    reap()
    f=open(f"/tmp/wsiso-{PORT}.log","ab")
    p=subprocess.Popen([BIN,"--bind",f"127.0.0.1:{PORT}","--no-udp","--io",os.environ.get("FUZZ_IO","auto")],
                       stdout=f,stderr=f,stdin=subprocess.DEVNULL,start_new_session=True)
    for _ in range(50):
        try:
            with socket.create_connection(("127.0.0.1",PORT),timeout=1): return p
        except OSError:
            if p.poll() is not None: return None
            time.sleep(0.2)
    return p

def handshake():
    key=base64.b64encode(os.urandom(16))
    req=(b"GET / HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
         b"Sec-WebSocket-Key: "+key+b"\r\nSec-WebSocket-Version: 13\r\n\r\n")
    s=socket.create_connection(("127.0.0.1",PORT),timeout=3); s.sendall(req); s.settimeout(3)
    buf=b""
    while b"\r\n\r\n" not in buf:
        c=s.recv(1024)
        if not c: s.close(); return None
        buf+=c
    return s if buf.startswith(b"HTTP/1.1 101") else (s.close() or None)

# regenerate the exact stream
rng=random.Random(SEED)
payloads=[]
for i in range(HI+1):
    base=rng.choice(WS_CORPUS); payloads.append(mutate(rng,base))

proc=start()
if not proc: print("serve did not start"); sys.exit(2)
for i in range(LO,HI+1):
    pl=payloads[i]
    if proc.poll() is not None:
        proc=start()
    try:
        s=handshake()
        if s:
            s.sendall(pl); s.settimeout(0.4)
            try:
                while True:
                    if not s.recv(4096): break
            except socket.timeout: pass
            s.close()
    except OSError: pass
    time.sleep(0.05)
    if proc.poll() is not None:
        print(f"CULPRIT ws-mut#{i} rc={proc.returncode} len={len(pl)} hex={pl.hex()}")
        # confirm in isolation on a fresh serve
        proc=start()
        try:
            s=handshake(); s.sendall(pl); time.sleep(0.4); s.close()
        except OSError: pass
        time.sleep(0.5)
        confirmed = proc.poll() is not None
        print(f"CONFIRMED_ISOLATED={confirmed}")
        with open(f"/tmp/wsiso-{PORT}.log") as f: print("LOG:", f.read().splitlines()[-3:])
        reap(); sys.exit(0)
reap()
print(f"no single-frame culprit in [{LO},{HI}] (crash may be cumulative across frames on one conn)")
