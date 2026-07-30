#!/usr/bin/env python3
"""
`mina-besttip` — fetch a live Mina peer's best tip and emit the raw binprot
`Protocol_state.Value` bytes.

This is the byte source behind `bridge/src/mina_head.rs`'s
`CommandProtocolStateSource`. With `--emit-protocol-state` it writes the response
payload from the Option tag onward to STDOUT and nothing else, which is exactly
the contract `MinaProtocolStateSource` asks for: bytes, or a nonzero exit.

    mina-besttip.py --emit-protocol-state > tip.bin

⚑ WHAT THIS IS, PRECISELY
=========================

It is an I/O client. It speaks:

    TCP -> pnet(XSalsa20) -> multistream-select -> Noise_XX_25519_ChaChaPoly_SHA256
        -> multistream-select -> /coda/yamux/1.0.0 -> multistream-select
        -> coda/rpcs/0.0.1 -> get_best_tip v2

and it decides NOTHING. It does not parse a consensus state, it does not know
which bytes are `min_window_density`, and it cannot make the client accept a
chain. Every byte it produces goes through the Lean decoder
(`Dregg2/Bridge/MinaBinprot.lean`) and then through Samasika's `select`
(`Dregg2/Bridge/MinaForkChoiceGate.lean`). The worst a hostile or broken source
achieves is to be REFUSED, or to withhold — and withholding is not defensible by
any light client, by any means.

That is why a hand-written transport is acceptable here and a hand-written
DECODER was not: the transport carries no semantics.

⚑ WHAT IT IS NOT
================

It is not the production path and it is not audited crypto. openmina
(`~/dev/mina-rust`) is a complete, maintained Rust implementation of this same
stack and is the thing to link when this moves out of `tools/`. This script
exists because it is small, dependency-light (`cryptography` only), and
reproducible — it is how `Dregg2/Bridge/MinaBinprotRealBlock.lean`'s 1,544-byte
devnet block 540186 fixture was obtained, and re-running it is how anyone checks
that the Lean decoder still reads what a real peer really serves.

Devnet only. No keys, no state, nothing persisted.

All protocol constants were read from openmina source, cited per line:
  - preshared key:   crates/core/src/chain_id.rs:303  blake2b256("/coda/0.0.1/" + hex(chain_id))
  - pnet directions: crates/p2p/src/network/pnet/p2p_network_pnet_reducer.rs
  - xsalsa20:        vendor/salsa-simple/src/lib.rs
  - ms tokens:       crates/p2p/src/network/select/token.rs
  - noise:           crates/p2p/src/network/noise/p2p_network_noise_{state,reducer}.rs
  - noise payload:   crates/node/common/src/service/p2p.rs:118
  - yamux frames:    crates/p2p/src/network/yamux/p2p_network_yamux_state.rs:294
  - rpc handshake:   crates/p2p/src/network/rpc/p2p_network_rpc_state.rs:72
  - rpc envelope:    crates/p2p-messages/src/rpc_kernel.rs
  - get_best_tip v2: crates/p2p-messages/src/rpc.rs:163

⚑ One noise detail that is easy to get wrong and fails silently as a MAC error:
message 3 encrypts the static key at counter 1 (not 0); `se` then rekeys and the
payload goes at counter 0 (`p2p_network_noise_state.rs`).
"""


import hashlib
import hmac
import os
import socket
import struct
import sys
import time

from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305

CRYPTO_LIB = "cryptography"

OUTDIR = os.environ.get("MINA_BESTTIP_OUTDIR", os.path.dirname(os.path.abspath(__file__)))
# `--emit-protocol-state`: stdout carries the bytes, stderr carries the log.
EMIT_STDOUT = "--emit-protocol-state" in sys.argv

DEVNET_CHAIN_ID = "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6"
SEEDS = [
    ("seed-1.devnet.gcp.o1test.net", 10003),
    ("seed-2.devnet.gcp.o1test.net", 10003),
    ("seed-3.devnet.gcp.o1test.net", 10003),
]

PALLAS_BASE_MODULUS = 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001

T0 = time.time()


def log(*a):
    # ⚑ STDERR, always. stdout is the byte channel under `--emit-protocol-state`, and one stray
    # log line there is a corrupted protocol state that the Lean decoder would (correctly, but
    # confusingly) refuse.
    print("[%7.3f]" % (time.time() - T0), *a, flush=True, file=sys.stderr)


def hx(b, n=64):
    b = bytes(b)
    s = b[:n].hex()
    return s + ("..." if len(b) > n else "")


# --------------------------------------------------------------------------
# Salsa20 / XSalsa20  (matches vendor/salsa-simple)
# --------------------------------------------------------------------------

_SIGMA = (0x61707865, 0x3320646E, 0x79622D32, 0x6B206574)
_M32 = 0xFFFFFFFF


def _rotl(v, c):
    return ((v << c) | (v >> (32 - c))) & _M32


def _qr(s, a, b, c, d):
    s[b] ^= _rotl((s[a] + s[d]) & _M32, 7)
    s[c] ^= _rotl((s[b] + s[a]) & _M32, 9)
    s[d] ^= _rotl((s[c] + s[b]) & _M32, 13)
    s[a] ^= _rotl((s[d] + s[c]) & _M32, 18)


def _rounds(state, n=10):
    s = list(state)
    for _ in range(n):
        _qr(s, 0, 4, 8, 12)
        _qr(s, 5, 9, 13, 1)
        _qr(s, 10, 14, 2, 6)
        _qr(s, 15, 3, 7, 11)
        _qr(s, 0, 1, 2, 3)
        _qr(s, 5, 6, 7, 4)
        _qr(s, 10, 11, 8, 9)
        _qr(s, 15, 12, 13, 14)
    return s


def hsalsa20(key, inp16):
    k = struct.unpack("<8I", key)
    n = struct.unpack("<4I", inp16)
    state = [
        _SIGMA[0], k[0], k[1], k[2],
        k[3], _SIGMA[1], n[0], n[1],
        n[2], n[3], _SIGMA[2], k[4],
        k[5], k[6], k[7], _SIGMA[3],
    ]
    s = _rounds(state)
    idx = [0, 5, 10, 15, 6, 7, 8, 9]
    return struct.pack("<8I", *[s[i] for i in idx])


class XSalsa20:
    """Stateful XSalsa20 keystream, counter starts at 0, position preserved
    across apply() calls (like salsa_simple::XSalsa20::apply_keystream)."""

    def __init__(self, key, nonce24):
        assert len(key) == 32 and len(nonce24) == 24
        subkey = hsalsa20(key, nonce24[:16])
        k = struct.unpack("<8I", subkey)
        iv = struct.unpack("<2I", nonce24[16:24])
        self.state = [
            _SIGMA[0], k[0], k[1], k[2],
            k[3], _SIGMA[1], iv[0], iv[1],
            0, 0, _SIGMA[2], k[4],
            k[5], k[6], k[7], _SIGMA[3],
        ]
        self.buf = b""
        self.pos = 0

    def _block(self):
        s = _rounds(self.state)
        out = struct.pack("<16I", *[(s[i] + self.state[i]) & _M32 for i in range(16)])
        ctr = (self.state[8] | (self.state[9] << 32)) + 1
        self.state[8] = ctr & _M32
        self.state[9] = (ctr >> 32) & _M32
        return out

    def apply(self, data):
        out = bytearray(data)
        i = 0
        n = len(out)
        while i < n:
            if self.pos == 0 or self.pos >= 64:
                self.buf = self._block()
                self.pos = 0
            take = min(64 - self.pos, n - i)
            ks = self.buf
            p = self.pos
            for j in range(take):
                out[i + j] ^= ks[p + j]
            i += take
            self.pos += take
            if self.pos >= 64:
                self.pos = 0
        return bytes(out)


def _selftest_salsa():
    k = bytes.fromhex("1b27556473e985d462cd51197a9a46c76009549eac6474f206c4ee0844f68389")
    n16 = bytes.fromhex("69696ee955b62b73cd62bda875fc73d6")
    want = "dc908dda0b9344a953629b7338207788" "80f3ceb421bb61b91cbd4c3e66256ce4"
    got = hsalsa20(k, n16).hex()
    ok1 = got == want
    log("selftest hsalsa20:", "PASS" if ok1 else "FAIL got=%s" % got)
    # NOTE: the full-stream vector is deliberately not asserted here. The
    # authoritative validation of the stream path is the live run itself: pnet
    # XSalsa20 decrypts every byte beneath noise, and a single wrong keystream
    # byte makes the very first ChaCha20Poly1305 transport tag fail.
    n24 = bytes.fromhex("69696ee955b62b73cd62bda875fc73d68219e0036b7a0b37")
    log("xsalsa20 stream[0:32] =", XSalsa20(k, n24).apply(b"\x00" * 32).hex())
    return ok1


# --------------------------------------------------------------------------
# pnet transport
# --------------------------------------------------------------------------

def preshared_key(chain_id_hex):
    h = hashlib.blake2b(digest_size=32)
    h.update(b"/coda/0.0.1/")
    h.update(chain_id_hex.encode("ascii"))
    return h.digest()


class PnetStream:
    def __init__(self, sock, psk):
        self.sock = sock
        self.buf = bytearray()
        my_nonce = os.urandom(24)
        self.out = XSalsa20(psk, my_nonce)
        sock.sendall(my_nonce)
        log("pnet: sent our nonce", hx(my_nonce))
        their = self._raw_exact(24)
        log("pnet: got their nonce", hx(their))
        self.inc = XSalsa20(psk, their)

    def _raw_exact(self, n):
        out = bytearray()
        while len(out) < n:
            c = self.sock.recv(n - len(out))
            if not c:
                raise EOFError("tcp closed during pnet nonce")
            out += c
        return bytes(out)

    def _fill(self):
        c = self.sock.recv(65536)
        if not c:
            raise EOFError("tcp closed (pnet)")
        self.buf += self.inc.apply(c)

    def read_exact(self, n):
        while len(self.buf) < n:
            self._fill()
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def write(self, data):
        self.sock.sendall(self.out.apply(data))


# --------------------------------------------------------------------------
# multistream-select
# --------------------------------------------------------------------------

def uvarint(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def ms_msg(s):
    body = s.encode() if isinstance(s, str) else s
    return uvarint(len(body)) + body


class MsChannel:
    """multistream-select over any object with read_exact(n)/write(b)."""

    def __init__(self, rd, wr, name):
        self.rd = rd
        self.wr = wr
        self.name = name

    def read_token(self):
        n = 0
        shift = 0
        while True:
            b = self.rd(1)[0]
            n |= (b & 0x7F) << shift
            if not (b & 0x80):
                break
            shift += 7
            if shift > 28:
                raise ValueError("varint too long")
        if n > 4096:
            raise ValueError("ms token too long: %d" % n)
        return self.rd(n)

    def negotiate(self, proto):
        self.wr(ms_msg("/multistream/1.0.0\n") + ms_msg(proto))
        t1 = self.read_token()
        log("  ms[%s] <- %r" % (self.name, t1))
        if t1 != b"/multistream/1.0.0\n":
            raise ValueError("ms[%s]: bad handshake token %r" % (self.name, t1))
        t2 = self.read_token()
        log("  ms[%s] <- %r" % (self.name, t2))
        if t2 != proto.encode():
            raise ValueError("ms[%s]: peer refused %r, said %r" % (self.name, proto, t2))
        return True


# --------------------------------------------------------------------------
# Noise XX initiator (libp2p flavour)
# --------------------------------------------------------------------------

PROTO_NAME = b"Noise_XX_25519_ChaChaPoly_SHA256"  # exactly 32 bytes


def hkdf2(ck, ikm):
    prk = hmac.new(ck, ikm, hashlib.sha256).digest()
    t1 = hmac.new(prk, b"\x01", hashlib.sha256).digest()
    t2 = hmac.new(prk, t1 + b"\x02", hashlib.sha256).digest()
    return t1, t2


def aead_nonce(counter):
    return b"\x00\x00\x00\x00" + struct.pack("<Q", counter)


class NoiseHS:
    def __init__(self):
        self.h = hashlib.sha256(PROTO_NAME).digest()  # mix_hash(b"") over h0=name
        self.ck = PROTO_NAME
        self.k = b"\x00" * 32

    def mix_hash(self, data):
        self.h = hashlib.sha256(self.h + data).digest()

    def mix_secret(self, secret):
        self.ck, self.k = hkdf2(self.ck, secret)

    def encrypt(self, counter, plaintext):
        ct = ChaCha20Poly1305(self.k).encrypt(aead_nonce(counter), plaintext, self.h)
        self.h = hashlib.sha256(self.h + ct).digest()
        return ct  # ciphertext||tag

    def decrypt(self, counter, ct):
        pt = ChaCha20Poly1305(self.k).decrypt(aead_nonce(counter), ct, self.h)
        self.h = hashlib.sha256(self.h + ct).digest()
        return pt

    def split(self):
        return hkdf2(self.ck, b"")


def pb_bytes(field, data):
    return bytes([(field << 3) | 2]) + uvarint(len(data)) + data


def raw_pub(x25519_sk):
    return x25519_sk.public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw
    )


class NoiseTransport:
    """Noise transport-mode framing over a PnetStream."""

    MAX_PLAIN = 65535 - 16

    def __init__(self, pnet, send_key, recv_key):
        self.pnet = pnet
        self.send_key = send_key
        self.recv_key = recv_key
        self.send_n = 0
        self.recv_n = 0
        self.buf = bytearray()

    def _pull(self):
        hdr = self.pnet.read_exact(2)
        ln = struct.unpack(">H", hdr)[0]
        ct = self.pnet.read_exact(ln)
        pt = ChaCha20Poly1305(self.recv_key).decrypt(aead_nonce(self.recv_n), ct, b"")
        self.recv_n += 1
        self.buf += pt

    def read_exact(self, n):
        while len(self.buf) < n:
            self._pull()
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def write(self, data):
        out = bytearray()
        for i in range(0, len(data), self.MAX_PLAIN):
            chunk = data[i:i + self.MAX_PLAIN]
            ct = ChaCha20Poly1305(self.send_key).encrypt(aead_nonce(self.send_n), chunk, b"")
            self.send_n += 1
            out += struct.pack(">H", len(ct)) + ct
        self.pnet.write(bytes(out))


def noise_xx_initiator(pnet):
    esk = X25519PrivateKey.generate()
    ssk = X25519PrivateKey.generate()
    epk = raw_pub(esk)
    spk = raw_pub(ssk)

    ident = Ed25519PrivateKey.generate()
    ident_pub = ident.public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw
    )
    # PublicKey { Type type = 1 (Ed25519 = 1); bytes Data = 2 }
    key_pb = b"\x08\x01" + pb_bytes(2, ident_pub)
    assert len(key_pb) == 36, len(key_pb)
    sig = ident.sign(b"noise-libp2p-static-key:" + spk)
    payload = b"\x0a\x24" + key_pb + b"\x12\x40" + sig
    assert len(payload) == 104, len(payload)

    ns = NoiseHS()
    # ---- msg1: -> e
    ns.mix_hash(epk)
    ns.mix_hash(b"")
    pnet.write(struct.pack(">H", 32) + epk)
    log("noise: sent msg1 (e), epk=%s" % hx(epk))

    # ---- msg2: <- e, ee, s, es
    ln = struct.unpack(">H", pnet.read_exact(2))[0]
    msg = pnet.read_exact(ln)
    log("noise: got msg2, %d bytes" % ln)
    if ln < 200:
        raise ValueError("noise msg2 too short (%d): %s" % (ln, hx(msg, 300)))
    r_epk = msg[0:32]
    s_ct = msg[32:80]           # 32 ct + 16 tag
    pay_ct = msg[80:]
    ns.mix_hash(r_epk)
    ns.mix_secret(esk.exchange(X25519PublicKey.from_public_bytes(r_epk)))
    r_spk = ns.decrypt(0, s_ct)
    ns.mix_secret(esk.exchange(X25519PublicKey.from_public_bytes(r_spk)))
    r_payload = ns.decrypt(0, pay_ct)
    log("noise: remote static=%s, payload %d bytes" % (hx(r_spk), len(r_payload)))
    remote_id = r_payload[4:36] if len(r_payload) >= 36 else b""
    log("noise: remote ed25519 identity=%s" % hx(remote_id))
    if len(r_payload) > 104:
        log("noise: remote early-data ext: %r" % r_payload[104:])

    # ---- msg3: -> s, se
    s_ct3 = ns.encrypt(1, spk)
    ns.mix_secret(ssk.exchange(X25519PublicKey.from_public_bytes(r_epk)))
    pay_ct3 = ns.encrypt(0, payload)
    body = s_ct3 + pay_ct3
    pnet.write(struct.pack(">H", len(body)) + body)
    log("noise: sent msg3 (s, se), %d bytes" % len(body))

    send_key, recv_key = ns.split()
    return NoiseTransport(pnet, send_key, recv_key)


# --------------------------------------------------------------------------
# yamux
# --------------------------------------------------------------------------

TYPE_DATA, TYPE_WINDOW, TYPE_PING, TYPE_GOAWAY = 0, 1, 2, 3
F_SYN, F_ACK, F_FIN, F_RST = 1, 2, 4, 8
INITIAL_WINDOW = 256 * 1024
TARGET_WINDOW = 16 * 1024 * 1024


class Yamux:
    def __init__(self, tr):
        self.tr = tr
        self.streams = {}       # sid -> bytearray
        self.consumed = {}      # sid -> bytes consumed since last window update
        self.closed = set()
        self.goaway = None

    def _ensure(self, sid):
        if sid not in self.streams:
            self.streams[sid] = bytearray()
        if sid not in self.consumed:
            self.consumed[sid] = 0
        return self.streams[sid]

    def _frame(self, typ, flags, sid, length_or_data):
        if typ == TYPE_DATA:
            data = length_or_data
            return struct.pack(">BBHII", 0, typ, flags, sid, len(data)) + data
        return struct.pack(">BBHII", 0, typ, flags, sid, length_or_data)

    def send_data(self, sid, data, flags=0):
        self.tr.write(self._frame(TYPE_DATA, flags, sid, data))

    def window_update(self, sid, delta, flags=0):
        self.tr.write(self._frame(TYPE_WINDOW, flags, sid, delta))

    def pump_one(self):
        hdr = self.tr.read_exact(12)
        ver, typ, flags, sid, val = struct.unpack(">BBHII", hdr)
        if ver != 0:
            raise ValueError("yamux: bad version %d (hdr=%s)" % (ver, hx(hdr)))
        if typ == TYPE_DATA:
            data = self.tr.read_exact(val) if val else b""
            self._ensure(sid)
            self.streams[sid] += data
            self.consumed[sid] += len(data)
            if self.consumed[sid] >= 32 * 1024:
                self.window_update(sid, self.consumed[sid])
                self.consumed[sid] = 0
            if flags & F_FIN:
                self.closed.add(sid)
            if flags & F_RST:
                self.closed.add(sid)
                log("yamux: RST on stream %d" % sid)
            return ("data", sid, len(data))
        elif typ == TYPE_WINDOW:
            if flags & F_SYN and sid != 0:
                log("yamux: peer opened stream %d (ignoring)" % sid)
                self._ensure(sid)
            if flags & (F_RST | F_FIN):
                self.closed.add(sid)
            return ("window", sid, val)
        elif typ == TYPE_PING:
            if flags & F_SYN:
                self.tr.write(self._frame(TYPE_PING, F_ACK, sid, val))
            return ("ping", sid, val)
        elif typ == TYPE_GOAWAY:
            self.goaway = val
            log("yamux: GO_AWAY code=%d" % val)
            return ("goaway", sid, val)
        else:
            raise ValueError("yamux: unknown type %d" % typ)

    def read_stream_exact(self, sid, n, deadline):
        buf = self._ensure(sid)
        while len(buf) < n:
            if self.goaway is not None:
                raise EOFError("yamux GO_AWAY while waiting on stream %d" % sid)
            if sid in self.closed and len(buf) < n:
                raise EOFError("yamux stream %d closed with %d/%d bytes" % (sid, len(buf), n))
            if time.time() > deadline:
                raise TimeoutError("timeout waiting for %d bytes on stream %d (have %d)"
                                   % (n, sid, len(buf)))
            self.pump_one()
            buf = self.streams[sid]
        out = bytes(buf[:n])
        del buf[:n]
        return out


class StreamIO:
    """read_exact/write bound to one yamux stream."""

    def __init__(self, yam, sid, deadline_fn):
        self.yam = yam
        self.sid = sid
        self.deadline_fn = deadline_fn
        self.first = True

    def read_exact(self, n):
        return self.yam.read_stream_exact(self.sid, n, self.deadline_fn())

    def write(self, data):
        flags = F_SYN if self.first else 0
        self.first = False
        self.yam.send_data(self.sid, data, flags)


# --------------------------------------------------------------------------
# binprot helpers
# --------------------------------------------------------------------------

def write_nat0(v):
    if v < 0x80:
        return bytes([v])
    if v < 0x10000:
        return b"\xfe" + struct.pack("<H", v)
    if v < 0x100000000:
        return b"\xfd" + struct.pack("<I", v)
    return b"\xfc" + struct.pack("<Q", v)


def read_int(b, off):
    c = b[off]
    if c < 0x80:
        return c, off + 1
    if c == 0xFF:
        return struct.unpack("<b", b[off + 1:off + 2])[0], off + 2
    if c == 0xFE:
        return struct.unpack("<H", b[off + 1:off + 3])[0], off + 3
    if c == 0xFD:
        return struct.unpack("<I", b[off + 1:off + 5])[0], off + 5
    if c == 0xFC:
        return struct.unpack("<Q", b[off + 1:off + 9])[0], off + 9
    raise ValueError("bad binprot int code 0x%02x at %d" % (c, off))


def rpc_frame(payload):
    return struct.pack("<Q", len(payload)) + payload


RPC_HANDSHAKE_PAYLOAD = bytes.fromhex("02fd5250430001")


def build_get_best_tip_query(qid=1):
    tag = b"get_best_tip"
    p = b"\x01"                       # Message::Query
    p += write_nat0(len(tag)) + tag   # Rpc_tag (CharString)
    p += write_nat0(2)                # version
    p += write_nat0(qid)              # query id
    p += write_nat0(1) + b"\x00"      # NeedsLength(unit)
    return p


# --------------------------------------------------------------------------
# the run
# --------------------------------------------------------------------------

def run_against(host, port, psk, overall_timeout=180.0):
    stage = "tcp"
    t_end = time.time() + overall_timeout

    def deadline():
        return t_end

    log("=== connecting to %s:%d ===" % (host, port))
    sock = socket.create_connection((host, port), timeout=30)
    sock.settimeout(30)
    log("tcp: connected")

    try:
        stage = "pnet"
        pnet = PnetStream(sock, psk)

        stage = "multistream-select(auth)"
        ms = MsChannel(pnet.read_exact, pnet.write, "auth")
        ms.negotiate("/noise\n")
        log("select: negotiated /noise")

        stage = "noise-xx"
        tr = noise_xx_initiator(pnet)
        log("noise: handshake done, transport keys derived")

        stage = "multistream-select(mux)"
        ms2 = MsChannel(tr.read_exact, tr.write, "mux")
        ms2.negotiate("/coda/yamux/1.0.0\n")
        log("select: negotiated /coda/yamux/1.0.0")

        stage = "yamux"
        yam = Yamux(tr)
        sid = 1
        sio = StreamIO(yam, sid, deadline)

        stage = "multistream-select(rpc)"
        # first DATA frame carries SYN and opens the stream
        sio.write(ms_msg("/multistream/1.0.0\n") + ms_msg("coda/rpcs/0.0.1\n"))
        yam.window_update(sid, TARGET_WINDOW - INITIAL_WINDOW)
        log("yamux: opened stream %d (SYN) + window bumped to %d" % (sid, TARGET_WINDOW))

        ms3 = MsChannel(sio.read_exact, sio.write, "rpc")
        t1 = ms3.read_token()
        log("  ms[rpc] <- %r" % t1)
        if t1 != b"/multistream/1.0.0\n":
            raise ValueError("ms[rpc]: bad handshake %r" % t1)
        t2 = ms3.read_token()
        log("  ms[rpc] <- %r" % t2)
        if t2 != b"coda/rpcs/0.0.1\n":
            raise ValueError("ms[rpc]: peer refused rpcs, said %r" % t2)
        log("select: negotiated coda/rpcs/0.0.1")

        stage = "rpc-handshake"
        sio.write(rpc_frame(RPC_HANDSHAKE_PAYLOAD))
        log("rpc: sent handshake frame %s" % hx(rpc_frame(RPC_HANDSHAKE_PAYLOAD)))

        def read_rpc_frame():
            ln = struct.unpack("<Q", sio.read_exact(8))[0]
            if ln > 64 * 1024 * 1024:
                raise ValueError("rpc frame absurdly large: %d" % ln)
            return sio.read_exact(ln)

        hs = read_rpc_frame()
        log("rpc: got frame %d bytes: %s" % (len(hs), hx(hs, 32)))

        stage = "rpc-query"
        q = build_get_best_tip_query(1)
        sio.write(rpc_frame(q))
        log("rpc: sent get_best_tip query, payload=%s" % q.hex())

        stage = "rpc-response"
        full = None
        while True:
            if time.time() > t_end:
                raise TimeoutError("no response before deadline")
            f = read_rpc_frame()
            if not f:
                log("rpc: empty frame, skipping")
                continue
            tag = f[0]
            if tag == 0x00:
                log("rpc: heartbeat (%d bytes)" % len(f))
                continue
            if tag == 0x02:
                qid, off = read_int(f, 1)
                if qid == 4411474:
                    log("rpc: peer handshake response")
                    continue
                log("rpc: RESPONSE frame %d bytes, query id=%d" % (len(f), qid))
                full = f
                break
            if tag == 0x01:
                log("rpc: incoming query from peer (%d bytes), ignoring" % len(f))
                continue
            log("rpc: unknown message tag 0x%02x (%d bytes): %s" % (tag, len(f), hx(f, 48)))

        # dissect
        off = 1
        qid, off = read_int(full, off)
        result_kind = full[off]
        off += 1
        if result_kind != 0:
            raise ValueError("RpcResult::Err, remaining=%s" % hx(full[off:], 64))
        plen, off = read_int(full, off)
        payload = full[off:off + plen]
        log("rpc: NeedsLength=%d, actual remaining=%d" % (plen, len(full) - off))

        return full, payload

    finally:
        try:
            sock.close()
        except Exception:
            pass


def main():
    _selftest_salsa()
    psk = preshared_key(DEVNET_CHAIN_ID)
    log("pnet preshared key = %s" % psk.hex())
    log("crypto backend = %s" % CRYPTO_LIB)

    last_err = None
    for host, port in SEEDS:
        try:
            full, payload = run_against(host, port, psk)
        except Exception as e:
            import traceback
            log("!! FAILED against %s:%d -> %s: %s" % (host, port, type(e).__name__, e))
            traceback.print_exc()
            last_err = e
            continue

        if EMIT_STDOUT:
            # The contract: the response payload from the Option tag onward, and
            # nothing else on stdout. The protocol state is the prefix of it; the
            # Lean decoder takes what it needs and ignores the remainder.
            if not payload or payload[0] != 1:
                log("peer answered None (no best tip); refusing rather than emitting")
                return 1
            sys.stdout.buffer.write(payload[1:])
            sys.stdout.buffer.flush()
            log("emitted %d bytes of Protocol_state.Value + remainder to stdout"
                % (len(payload) - 1))
            return 0

        p_full = os.path.join(OUTDIR, "best_tip_full_frame.bin")
        p_resp = os.path.join(OUTDIR, "best_tip_response.bin")
        with open(p_full, "wb") as f:
            f.write(full)
        with open(p_resp, "wb") as f:
            f.write(payload)

        log("=" * 66)
        log("SUCCESS against %s:%d" % (host, port))
        log("full frame bytes : %d  -> %s" % (len(full), p_full))
        log("response payload : %d  -> %s" % (len(payload), p_resp))
        log("payload head     : %s" % hx(payload, 48))
        opt = payload[0]
        log("Option tag       : 0x%02x (%s)" % (opt, "Some" if opt == 1 else "None/unexpected"))
        if opt == 1:
            psh = payload[1:33]
            val = int.from_bytes(psh, "little")
            log("previous_state_hash (LE bytes) = %s" % psh.hex())
            log("  as integer  = %d" % val)
            log("  modulus     = %d" % PALLAS_BASE_MODULUS)
            log("  canonical (< modulus)? %s" % (val < PALLAS_BASE_MODULUS))
        return 0

    log("ALL SEEDS FAILED; last error: %r" % (last_err,))
    return 1


if __name__ == "__main__":
    sys.exit(main())
