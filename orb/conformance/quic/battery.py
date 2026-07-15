#!/usr/bin/env python3
"""QUIC / HTTP-3 conformance battery for the serve's UDP datagram path.

A from-scratch RFC 9000 / RFC 9001 QUIC-Initial prober (no aioquic — it cannot
offer the X25519MLKEM768 hybrid the target requires anyway, and it is not
installed here). Crypto is the stdlib `cryptography` package: HKDF-SHA256 for the
Initial key schedule (RFC 9001 sec 5.2), AES-128-GCM for AEAD payload protection
(sec 5.3), AES-ECB single-block for header protection (sec 5.4.3) — exactly the
QUIC v1 Initial suite every real client's first flight uses.

The battery crafts Initial packets on the wire, sends them over UDP, and inspects
what comes back. Failures are EXPECTED and welcome: the target's deployed UDP path
is a decrypt-Initial -> H3-dispatch demo, not a full QUIC connection, so the gap
map (handshake / version negotiation / connection lifecycle) is the deliverable.

Every score printed is from an actual send/recv against the running target.
"""

import os
import socket
import struct
import sys
import hashlib
import hmac

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

# ---------------------------------------------------------------------------
# RFC 9001 sec 5.2 QUIC v1 Initial salt.
INITIAL_SALT = bytes.fromhex("38762cf7f55934b34d179ae6a4c80cadccbb7f0a")


def hkdf_extract(salt: bytes, ikm: bytes) -> bytes:
    return hmac.new(salt, ikm, hashlib.sha256).digest()


def hkdf_expand(prk: bytes, info: bytes, length: int) -> bytes:
    out = b""
    t = b""
    i = 1
    while len(out) < length:
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        out += t
        i += 1
    return out[:length]


def expand_label(secret: bytes, label: str, length: int) -> bytes:
    full = b"tls13 " + label.encode()
    info = struct.pack(">H", length) + bytes([len(full)]) + full + b"\x00"
    return hkdf_expand(secret, info, length)


def client_initial_keys(dcid: bytes):
    initial_secret = hkdf_extract(INITIAL_SALT, dcid)
    cis = expand_label(initial_secret, "client in", 32)
    key = expand_label(cis, "quic key", 16)
    iv = expand_label(cis, "quic iv", 12)
    hp = expand_label(cis, "quic hp", 16)
    return key, iv, hp


def server_initial_keys(dcid: bytes):
    initial_secret = hkdf_extract(INITIAL_SALT, dcid)
    sis = expand_label(initial_secret, "server in", 32)
    key = expand_label(sis, "quic key", 16)
    iv = expand_label(sis, "quic iv", 12)
    hp = expand_label(sis, "quic hp", 16)
    return key, iv, hp


def aes_ecb_block(hp: bytes, sample: bytes) -> bytes:
    enc = Cipher(algorithms.AES(hp), modes.ECB()).encryptor()
    return enc.update(sample[:16]) + enc.finalize()


def record_nonce(iv: bytes, pn: int) -> bytes:
    pnb = pn.to_bytes(8, "big")
    b = bytearray(iv)
    for i in range(8):
        b[12 - 8 + i] ^= pnb[i]
    return bytes(b)


def varint(v: int) -> bytes:
    if v < (1 << 6):
        return bytes([v])
    if v < (1 << 14):
        return struct.pack(">H", v | 0x4000)
    if v < (1 << 30):
        return struct.pack(">I", v | 0x80000000)
    return struct.pack(">Q", v | 0xC000000000000000)


def build_initial(payload: bytes, dcid: bytes, version: int = 1,
                  scid: bytes = b"", pn: int = 0, pnlen: int = 1,
                  pad_to: int = 1200) -> bytes:
    """Craft one QUIC v1 long-header Initial carrying `payload` (frame bytes),
    AES-128-GCM sealed + AES-ECB header-protected under keys derived from `dcid`."""
    key, iv, hp = client_initial_keys(dcid)

    if pad_to:
        # PADDING frames (0x00) after the payload to reach a realistic Initial size.
        need = pad_to - (7 + len(dcid) + len(scid) + 4 + len(payload) + 16)
        if need > 0:
            payload = payload + b"\x00" * need

    ct_len = len(payload) + 16  # AEAD tag is 16 bytes
    length_field = varint(pnlen + ct_len)

    first_byte = 0xC0 | (pnlen - 1)  # long, fixed, Initial type, reserved 0
    hdr_prefix = (
        bytes([first_byte])
        + struct.pack(">I", version)
        + bytes([len(dcid)]) + dcid
        + bytes([len(scid)]) + scid
        + varint(0)            # token length 0
        + length_field
    )
    pn_bytes = pn.to_bytes(pnlen, "big")
    pn_off = len(hdr_prefix)
    aad = hdr_prefix + pn_bytes

    nonce = record_nonce(iv, pn)
    ct = AESGCM(key).encrypt(nonce, payload, aad)

    # Header protection (RFC 9001 sec 5.4): sample at pn_off+4.
    sample_start = 4 - pnlen  # offset into ct
    sample = ct[sample_start:sample_start + 16]
    mask = aes_ecb_block(hp, sample)[:5]
    fb_masked = first_byte ^ (mask[0] & 0x0F)
    pn_masked = bytes(pn_bytes[i] ^ mask[1 + i] for i in range(pnlen))

    packet = bytes([fb_masked]) + hdr_prefix[1:] + pn_masked + ct
    return packet


# ---------------------------------------------------------------------------
# H3 / QUIC frame helpers.

def h3_headers_get(path: str) -> bytes:
    """A minimal HTTP/3 HEADERS frame (RFC 9114) with a QPACK field section
    (RFC 9204) for `GET <path>`. :method GET is static index 17 (0xD1); :path is
    static index 1 — indexed (0xC1) for "/", else a literal name-reference."""
    if path == "/":
        block = b"\x00\x00" + b"\xd1" + b"\xc1"  # RIC/base prefix, GET, :path /
    else:
        val = path.encode()
        # literal field line, name-ref static idx 1 (:path), raw value.
        lit = bytes([0x51, len(val)]) + val
        block = b"\x00\x00" + b"\xd1" + lit
    return bytes([0x01, len(block)]) + block  # HEADERS frame: type 0x01, len, block


def stream_frame(data: bytes, sid: int = 0, fin: bool = False,
                 with_len: bool = True, offset=None) -> bytes:
    ft = 0x08
    body = varint(sid)
    if offset is not None:
        ft |= 0x04
        body += varint(offset)
    if with_len:
        ft |= 0x02
        body += varint(len(data))
    if fin:
        ft |= 0x01
    return bytes([ft]) + body + data


def crypto_frame(data: bytes) -> bytes:
    # CRYPTO frame: type 0x06, offset varint, length varint, data.
    return b"\x06" + varint(0) + varint(len(data)) + data


# ---------------------------------------------------------------------------
# Transport + reporting.

class Target:
    def __init__(self, host, port, timeout=2.0):
        self.addr = (host, port)
        self.timeout = timeout

    def send_recv(self, packet: bytes):
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(self.timeout)
        try:
            s.sendto(packet, self.addr)
            try:
                data, _ = s.recvfrom(65536)
                return data
            except socket.timeout:
                return None
        finally:
            s.close()


RESULTS = []


def check(cat, name, ok, detail):
    RESULTS.append((cat, name, ok, detail))
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] ({cat}) {name}\n        {detail}")


def preview(resp):
    if resp is None:
        return "<no datagram back (drop/timeout)>"
    txt = resp[:120].decode("latin-1").replace("\r", "\\r").replace("\n", "\\n")
    return f"{len(resp)}B: {txt}"


def is_http(resp):
    return resp is not None and resp[:5] == b"HTTP/"


def status(resp):
    """The HTTP status line the serve returned (the datapath answers H3 with a
    raw HTTP/1.1 serialization), or None."""
    if resp is None or resp[:5] != b"HTTP/":
        return None
    try:
        return int(resp.split(b" ", 2)[1])
    except Exception:
        return None


def is_quic_packet(resp):
    """Would a real QUIC client accept this as a QUIC packet? Long header has the
    fixed bit (0x40) set with high bit (0x80); short header has 0x40 set, 0x80
    clear. A raw 'HTTP/...' response (first byte 'H'=0x48) is NEITHER."""
    return resp is not None and len(resp) >= 1 and (resp[0] & 0x40) != 0 and resp[0] != 0x48


# Oracle convention below: PASS == the target is RFC-conformant / the capability
# is present; FAIL == a genuine gap. QUIC here is deliberately partial, so the
# FAILs ARE the deliverable (the gap map). Nothing is tuned to pass.
def run(target):
    print(f"== QUIC/H3 battery vs {target.addr[0]}:{target.addr[1]} ==\n")

    # (a) CAPABILITY: a real QUIC v1 AES-128-GCM Initial, header-protected with
    # AES-ECB, is decrypted by the target's verified EverCrypt packet protection
    # and its STREAM-framed HTTP/3 request is dispatched. Cross-impl agreement:
    # our independent `cryptography` seal is opened by the target's EverCrypt.
    dcid = os.urandom(8)
    root = target.send_recv(build_initial(stream_frame(h3_headers_get("/")), dcid))
    check("a-decrypt", "AES-128-GCM/AES-ECB Initial decrypts + H3-dispatches",
          is_http(root), preview(root))

    # (f) CAPABILITY: the H3 HEADERS+QPACK request is decoded and routed by :path
    # through the proven serve. Distinct paths => distinct responses.
    hp = target.send_recv(build_initial(stream_frame(h3_headers_get("/health")), os.urandom(8)))
    check("f-h3", "GET /health -> 200 ok (proven serve over H3)",
          status(hp) == 200 and b"ok" in (hp or b""), preview(hp))
    check("f-h3", "GET / routed distinctly (H3 :path decode reaches the serve)",
          is_http(root) and status(root) != status(hp), preview(root))

    # (a) GAP: the QUIC HANDSHAKE (and the X25519MLKEM768 PQ KEX) is NOT on the
    # datapath. A CRYPTO-frame ClientHello should elicit a server Initial flight
    # carrying a ServerHello. `drorbServeDatagram` parses only STREAM frames and
    # never invokes QuicServer, so the ClientHello bytes fall through into the H3
    # path and 400. Conformant == a decryptable ServerHello came back.
    dcid = os.urandom(8)
    fake_ch = b"\x01\x00\x01\xfc\x03\x03" + os.urandom(120)  # TLS ClientHello-shaped
    r = target.send_recv(build_initial(crypto_frame(fake_ch), dcid))
    got_serverhello = r is not None and is_quic_packet(r) and b"\x02\x00" in r
    check("a-handshake", "CRYPTO ClientHello -> QUIC ServerHello flight (PQ KEX on wire)",
          got_serverhello, preview(r) + "  [GAP: handshake/PQ-KEX proven but unwired -> 400]")

    # (b) GAP: version negotiation. RFC 9000 sec 6: an unsupported version SHOULD
    # get a Version Negotiation packet. Conformant == a VN packet (or a drop).
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/")), os.urandom(8),
                                       version=0x1A2A3A4B))
    is_vn = r is not None and len(r) >= 5 and (r[0] & 0x80) and r[1:5] == b"\x00\x00\x00\x00"
    check("b-versneg", "non-v1 version -> Version Negotiation packet",
          is_vn, preview(r) + "  [GAP: version field ignored, no VN]")
    # (b) GAP: the version is not validated at all — a non-v1 packet is served as
    # if v1 (fixed v1 salt regardless). Conformant == not served under a bogus version.
    check("b-versneg", "non-v1 version rejected/validated",
          not is_http(r), preview(r) + "  [GAP: served anyway under fixed v1 salt]")

    # (c) CAPABILITY: a STREAM frame with the FIN bit and implicit length (data to
    # end of packet) is dispatched — single-datagram stream data works.
    r = target.send_recv(build_initial(
        stream_frame(h3_headers_get("/health"), fin=True, with_len=False),
        os.urandom(8), pad_to=0))
    check("c-stream", "STREAM FIN + implicit-length -> served",
          status(r) == 200, preview(r))
    # (c) CAPABILITY: a 2-byte-varint stream id parses.
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/"), sid=16383), os.urandom(8)))
    check("c-stream", "STREAM sid=16383 (2-byte varint) parses + serves",
          is_http(r), preview(r))
    # (c) GAP: a non-zero stream OFFSET is ignored — no reassembly. A conformant
    # receiver buffers data at offset 100 and does NOT complete a request from it.
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/"), offset=100), os.urandom(8)))
    check("c-stream", "STREAM offset=100 buffered (not served as offset 0)",
          not is_http(r), preview(r) + "  [GAP: offset ignored, no reassembly]")

    # (d) GAP: QUIC frame types other than a leading STREAM are not interpreted.
    # A conformant receiver skips PADDING and processes the following STREAM; here
    # the non-STREAM leading byte routes the whole plaintext into H3 -> 400.
    r = target.send_recv(build_initial(b"\x00\x00\x00" + stream_frame(h3_headers_get("/")),
                                       os.urandom(8)))
    check("d-frames", "PADDING then STREAM -> STREAM still processed",
          status(r) == 404 or status(r) == 200, preview(r) + "  [GAP: leading PADDING breaks dispatch -> 400]")
    # (d) GAP: PING (0x01) should be consumed silently (no application error).
    r = target.send_recv(build_initial(b"\x01" + b"\x00" * 20, os.urandom(8)))
    check("d-frames", "PING frame consumed (no HTTP error response)",
          r is None or len(r) == 0, preview(r) + "  [GAP: PING misparsed into H3 -> 400]")
    # (d) GAP: ACK (0x02) should be processed, not answered with an HTTP 400.
    r = target.send_recv(build_initial(b"\x02\x00\x00\x00\x00" + b"\x00" * 20, os.urandom(8)))
    check("d-frames", "ACK frame processed (no HTTP error response)",
          r is None or len(r) == 0, preview(r) + "  [GAP: ACK misparsed into H3 -> 400]")

    # (e) GAP: CONNECTION_CLOSE (0x1c) should tear the connection down silently,
    # not answer with an HTTP 400. No lifecycle FSM on the datapath.
    cc = b"\x1c" + varint(0) + varint(0) + varint(0)
    r = target.send_recv(build_initial(cc + b"\x00" * 20, os.urandom(8)))
    check("e-close", "CONNECTION_CLOSE handled (no HTTP error, no reply)",
          r is None or len(r) == 0, preview(r) + "  [GAP: no lifecycle FSM, misparsed -> 400]")

    # (e) GAP: the 1-RTT response is NOT a QUIC packet — the served bytes are raw
    # HTTP/1.1, so a real QUIC/H3 client cannot consume them. Conformant == the
    # response is a QUIC-framed (short-header, encrypted) packet.
    check("e-response", "response is a QUIC 1-RTT packet (client-consumable)",
          is_quic_packet(hp), preview(hp) + "  [GAP: raw HTTP bytes, not QUIC-encrypted]")

    # (e) SECURITY CAPABILITY: a forged Initial (AEAD tag flipped) fails auth and
    # is silently dropped — the EverCrypt authenticity gate.
    bad = bytearray(build_initial(stream_frame(h3_headers_get("/")), os.urandom(8)))
    bad[-1] ^= 0xFF
    r = target.send_recv(bytes(bad))
    check("e-security", "forged Initial (tag flipped) -> silent drop (AEAD auth)",
          r is None or len(r) == 0, preview(r))
    # (e) ROBUSTNESS: truncated garbage does not crash the listener, no reply.
    r = target.send_recv(b"\xc0\x00\x00\x00\x01\x08" + os.urandom(4))
    check("e-security", "truncated garbage -> no crash, no reply",
          r is None or len(r) == 0, preview(r))
    # (e) ROBUSTNESS: the listener still serves after the malformed inputs.
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/health")), os.urandom(8)))
    check("e-security", "listener still serving after malformed input",
          status(r) == 200, preview(r))

    # ---- summary ----
    npass = sum(1 for _, _, ok, _ in RESULTS if ok)
    print(f"\n== {npass}/{len(RESULTS)} checks passed ==")
    cats = {}
    for cat, _, ok, _ in RESULTS:
        d = cats.setdefault(cat, [0, 0])
        d[0] += 1 if ok else 0
        d[1] += 1
    for cat in sorted(cats):
        p, t = cats[cat]
        print(f"   {cat:14s} {p}/{t}")
    return npass, len(RESULTS)


if __name__ == "__main__":
    host = sys.argv[1] if len(sys.argv) > 1 else "127.0.0.1"
    port = int(sys.argv[2]) if len(sys.argv) > 2 else 18950
    t = Target(host, port)
    run(t)
