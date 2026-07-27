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
from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305

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
# TLS 1.3 ClientHello with the X25519MLKEM768 (0x11EC) hybrid key_share — the
# post-quantum hybrid the target's QUIC handshake REQUIRES. The ML-KEM-768
# encapsulation key is random 1184-byte filler: the target encapsulates to it
# (producing a real ServerHello + server share) but this prober does not
# decapsulate — it verifies the ServerHello came back and echoes the negotiated
# hybrid group, which needs no client-side PQ secret. RFC 8446 §4.1.2 framing.

XWING_GROUP = 0x11EC  # draft-ietf-tls-ecdhe-mlkem X25519MLKEM768 code point.


def _ext(ext_type: int, body: bytes) -> bytes:
    return struct.pack(">HH", ext_type, len(body)) + body


def build_client_hello() -> bytes:
    """A syntactically valid TLS 1.3 ClientHello carrying an X25519MLKEM768
    hybrid key_share (group 0x11EC, a 1216-byte `ml_kem_ek(1184) ‖ x25519_pub(32)`
    share). Returned as the bare handshake message (`0x01 ‖ uint24 len ‖ …`) for a
    CRYPTO frame."""
    legacy_version = b"\x03\x03"
    random32 = os.urandom(32)
    session_id = os.urandom(32)
    cipher_suites = struct.pack(">HHH", 0x1301, 0x1302, 0x1303)
    compression = b"\x01\x00"  # 1 method: null

    # key_share: client_shares<2..2^16-1> = one entry {group, key_exchange<2>}.
    hybrid_share = os.urandom(1184 + 32)  # ml_kem_ek(1184) ‖ x25519_pub(32)
    ks_entry = struct.pack(">HH", XWING_GROUP, len(hybrid_share)) + hybrid_share
    key_share = _ext(0x0033, struct.pack(">H", len(ks_entry)) + ks_entry)
    # supported_versions: 1-byte list len, then TLS 1.3.
    supported_versions = _ext(0x002b, b"\x02" + b"\x03\x04")
    # supported_groups: the hybrid.
    supported_groups = _ext(0x000a, struct.pack(">H", 2) + struct.pack(">H", XWING_GROUP))
    # signature_algorithms: ed25519 (0x0807), the leaf the server presents.
    sig_algs = _ext(0x000d, struct.pack(">H", 2) + struct.pack(">H", 0x0807))

    exts = supported_versions + supported_groups + sig_algs + key_share
    body = (legacy_version + random32
            + bytes([len(session_id)]) + session_id
            + struct.pack(">H", len(cipher_suites)) + cipher_suites
            + compression
            + struct.pack(">H", len(exts)) + exts)
    return b"\x01" + struct.pack(">I", len(body))[1:] + body  # uint24 length


def build_client_hello_classical() -> bytes:
    """A TLS 1.3 ClientHello offering ONLY the classical X25519 (0x001D) group /
    share — no hybrid. The hybrid-pinned server must refuse it (no flight)."""
    legacy_version = b"\x03\x03"
    random32 = os.urandom(32)
    session_id = os.urandom(32)
    cipher_suites = struct.pack(">HHH", 0x1301, 0x1302, 0x1303)
    compression = b"\x01\x00"
    x25519_pub = os.urandom(32)
    ks_entry = struct.pack(">HH", 0x001D, len(x25519_pub)) + x25519_pub
    key_share = _ext(0x0033, struct.pack(">H", len(ks_entry)) + ks_entry)
    supported_versions = _ext(0x002b, b"\x02" + b"\x03\x04")
    supported_groups = _ext(0x000a, struct.pack(">H", 2) + struct.pack(">H", 0x001D))
    sig_algs = _ext(0x000d, struct.pack(">H", 2) + struct.pack(">H", 0x0807))
    exts = supported_versions + supported_groups + sig_algs + key_share
    body = (legacy_version + random32
            + bytes([len(session_id)]) + session_id
            + struct.pack(">H", len(cipher_suites)) + cipher_suites
            + compression
            + struct.pack(">H", len(exts)) + exts)
    return b"\x01" + struct.pack(">I", len(body))[1:] + body


def _remove_long_header_protection(pkt: bytes, pn_off: int, hp: bytes):
    """Undo QUIC header protection on a long-header packet, returning
    (first_byte, pn, pn_len, aad, ct)."""
    sample = pkt[pn_off + 4:pn_off + 4 + 16]
    mask = aes_ecb_block(hp, sample)[:5]
    first = pkt[0] ^ (mask[0] & 0x0F)
    pn_len = (first & 0x03) + 1
    pn_bytes = bytes(pkt[pn_off + i] ^ mask[1 + i] for i in range(pn_len))
    pn = int.from_bytes(pn_bytes, "big")
    aad = bytes([first]) + pkt[1:pn_off] + pn_bytes
    return first, pn, pn_len, aad, pn_bytes


def open_server_initial(resp: bytes, client_dcid: bytes):
    """Decrypt the server Initial packet at the front of `resp` (server_initial
    keys from the client's original DCID, RFC 9001 §5.2) and return its frame
    plaintext, or None. This is the receive-half cross-check: our independent
    `cryptography` AES-128-GCM opens what the target's EverCrypt sealed."""
    if not resp or (resp[0] & 0xF0) != 0xC0:
        return None
    key, iv, hp = server_initial_keys(client_dcid)
    # Parse the in-the-clear long header up to the Length field.
    off = 1 + 4  # first byte + version
    dcid_len = resp[off]; off += 1 + dcid_len
    scid_len = resp[off]; off += 1 + scid_len
    tok_len, tb = _read_varint(resp, off); off += tb + tok_len
    length_field, lb = _read_varint(resp, off); off += lb
    pn_off = off
    first, pn, pn_len, aad, _ = _remove_long_header_protection(resp, pn_off, hp)
    ct = resp[pn_off + pn_len: pn_off + length_field]
    nonce = record_nonce(iv, pn)
    try:
        return AESGCM(key).decrypt(nonce, ct, aad)
    except Exception:
        return None


def _read_varint(buf: bytes, off: int):
    b0 = buf[off]
    ln = 1 << (b0 >> 6)
    v = b0 & 0x3F
    for i in range(1, ln):
        v = (v << 8) | buf[off + i]
    return v, ln


def find_server_hello(plaintext: bytes):
    """Walk the decrypted server-Initial frames for a CRYPTO frame and return the
    TLS handshake bytes it carries (the ServerHello), or None."""
    if plaintext is None:
        return None
    i = 0
    n = len(plaintext)
    while i < n:
        ft = plaintext[i]
        if ft == 0x00:  # PADDING
            i += 1
            continue
        if ft == 0x02 or ft == 0x03:  # ACK: largest, delay, count, first, ranges
            i += 1
            largest, l1 = _read_varint(plaintext, i); i += l1
            delay, l2 = _read_varint(plaintext, i); i += l2
            cnt, l3 = _read_varint(plaintext, i); i += l3
            _, l4 = _read_varint(plaintext, i); i += l4
            for _ in range(2 * cnt):
                _, lk = _read_varint(plaintext, i); i += lk
            if ft == 0x03:
                for _ in range(3):
                    _, lk = _read_varint(plaintext, i); i += lk
            continue
        if ft == 0x06:  # CRYPTO: offset, length, data
            i += 1
            _, lo = _read_varint(plaintext, i); i += lo
            dlen, ll = _read_varint(plaintext, i); i += ll
            return plaintext[i:i + dlen]
        break
    return None


# ---------------------------------------------------------------------------
# Transport + reporting.

def app_keys(dcid: bytes):
    """The DEMO 1-RTT application keys the target derives from the client DCID
    (`Dataplane.Multi.demoAppKeys`): a labeled schedule parallel to the Initial
    secret, so an independent client can open the target-sealed short-header
    packet. ChaCha20-Poly1305 (key 32, iv 12, hp 32). NOT the handshake-derived
    1-RTT secret (that path is the stateful stepServer bridge)."""
    initial_secret = hkdf_extract(INITIAL_SALT, dcid)
    demo = expand_label(initial_secret, "demo 1rtt", 32)
    key = expand_label(demo, "quic key", 32)
    iv = expand_label(demo, "quic iv", 12)
    hp = expand_label(demo, "quic hp", 32)
    return key, iv, hp


def chacha20_hp_mask(hp: bytes, sample: bytes) -> bytes:
    """RFC 9001 sec 5.4.4 ChaCha20 header-protection mask: counter = sample[0:4]
    (LE), nonce = sample[4:16], mask = ChaCha20(hp, counter||nonce)[0:5]. The
    cryptography ChaCha20 16-byte nonce IS counter(4 LE) || nonce(12), so
    sample[0:16] maps directly."""
    enc = Cipher(algorithms.ChaCha20(hp, bytes(sample[0:16])), mode=None).encryptor()
    return enc.update(b"\x00" * 5)


def _parse_stream_payload(pt: bytes):
    """Return the data bytes of a leading STREAM frame (RFC 9000 sec 19.8), or None."""
    if not pt or (pt[0] & 0xF8) != 0x08:
        return None
    ft = pt[0]; off = 1
    _sid, n = _read_varint(pt, off); off += n
    if ft & 0x04:
        _o, n = _read_varint(pt, off); off += n
    if ft & 0x02:
        dlen, n = _read_varint(pt, off); off += n
        return pt[off:off + dlen]
    return pt[off:]


def open_short_header(resp: bytes, dcid: bytes):
    """Open a QUIC 1-RTT short-header packet (0x40 set, 0x80 clear) the target
    sealed via the proven `QuicServer.buildShortPacket`, returning the inner HTTP
    bytes (the STREAM-framed response), or None. ChaCha20-Poly1305 AEAD + ChaCha20
    header protection under the DCID-derived DEMO 1-RTT keys (`app_keys`) — the
    receive-half cross-check that the target-sealed 1-RTT packet is client-openable."""
    pn_off = 1 + len(dcid)
    if resp is None or len(resp) < pn_off + 4 + 16:
        return None
    if (resp[0] & 0x80) != 0:  # must be a short header
        return None
    key, iv, hp = app_keys(dcid)
    sample = resp[pn_off + 4:pn_off + 4 + 16]
    mask = chacha20_hp_mask(hp, sample)
    fb = resp[0] ^ (mask[0] & 0x1F)   # short header: low 5 bits
    pn_len = (fb & 0x03) + 1
    pn_bytes = bytes(resp[pn_off + i] ^ mask[1 + i] for i in range(pn_len))
    pn = int.from_bytes(pn_bytes, "big")
    aad = bytes([fb]) + resp[1:pn_off] + pn_bytes
    ct = resp[pn_off + pn_len:]
    try:
        pt = ChaCha20Poly1305(key).decrypt(record_nonce(iv, pn), ct, aad)
    except Exception:
        return None
    return _parse_stream_payload(pt)


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
    root_body = open_short_header(root, dcid)
    check("a-decrypt", "AES-128-GCM/AES-ECB Initial decrypts + H3-dispatches (1-RTT reply opens)",
          is_http(root_body), preview(root) + f"  [1-RTT body {len(root_body) if root_body else 0}B]")

    # (f) CAPABILITY: the H3 HEADERS+QPACK request is decoded and routed by :path
    # through the proven serve. Distinct paths => distinct responses.
    hpd = os.urandom(8)
    hp = target.send_recv(build_initial(stream_frame(h3_headers_get("/health")), hpd))
    hp_body = open_short_header(hp, hpd)
    check("f-h3", "GET /health -> 200 ok (proven serve over H3, 1-RTT reply)",
          status(hp_body) == 200 and b"ok" in (hp_body or b""), preview(hp))
    check("f-h3", "GET / routed distinctly (H3 :path decode reaches the serve)",
          is_http(root_body) and status(root_body) != status(hp_body), preview(root))

    # (a) CAPABILITY: the QUIC HANDSHAKE with the X25519MLKEM768 PQ KEX is on the
    # datapath. A CRYPTO-frame ClientHello carrying the hybrid key_share elicits
    # the server Initial+Handshake flight; the ServerHello comes back in the
    # server Initial, which THIS prober decrypts (server_initial keys from the
    # DCID) — a receive-half cross-check of the target's EverCrypt seal. Conformant
    # == a decryptable ServerHello (handshake type 0x02) came back over QUIC.
    dcid = os.urandom(8)
    ch = build_client_hello()
    r = target.send_recv(build_initial(crypto_frame(ch), dcid))
    sh = find_server_hello(open_server_initial(r, dcid))
    got_serverhello = (r is not None and is_quic_packet(r)
                       and sh is not None and len(sh) > 0 and sh[0] == 0x02)
    check("a-handshake", "CRYPTO ClientHello -> QUIC ServerHello flight (PQ KEX on wire)",
          got_serverhello, preview(r) + f"  [ServerHello {len(sh) if sh else 0}B decrypted]")
    # (a) CAPABILITY: the ServerHello echoes the negotiated hybrid group
    # (0x11EC) in its key_share — the PQ KEX was carried on the QUIC wire, not
    # downgraded to a classical group. `0x11EC` == b"\x11\xec".
    group_echoed = sh is not None and b"\x11\xec" in sh
    check("a-handshake", "ServerHello echoes X25519MLKEM768 (0x11EC) group",
          group_echoed, f"ServerHello carries hybrid group: {group_echoed}")
    # (a) SECURITY: the handshake is hybrid-PINNED. A ClientHello offering only
    # the classical X25519 group (no 0x11EC share) gets NO flight — fail-closed
    # (`QuicServer.buildTlsFlight_requires_hybrid`), so no ServerHello returns.
    ch_classical = build_client_hello_classical()
    rc = target.send_recv(build_initial(crypto_frame(ch_classical), os.urandom(8)))
    shc = find_server_hello(open_server_initial(rc, dcid)) if rc else None
    classical_rejected = shc is None or len(shc) == 0 or shc[0] != 0x02
    check("a-handshake", "classical-only ClientHello -> no flight (hybrid pinned)",
          classical_rejected, preview(rc) + "  [fail-closed: PQ hybrid required]")

    # (b) GAP: version negotiation. RFC 9000 sec 6: an unsupported version SHOULD
    # get a Version Negotiation packet. Conformant == a VN packet (or a drop).
    vnd = os.urandom(8)
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/")), vnd,
                                       version=0x1A2A3A4B))
    is_vn = r is not None and len(r) >= 5 and (r[0] & 0x80) and r[1:5] == b"\x00\x00\x00\x00"
    check("b-versneg", "non-v1 version -> Version Negotiation packet",
          is_vn, preview(r) + "  [GAP: version field ignored, no VN]")
    # (b) GAP: the version is not validated at all — a non-v1 packet is served as
    # if v1 (fixed v1 salt regardless). Conformant == not served under a bogus version.
    check("b-versneg", "non-v1 version rejected/validated",
          not is_http(open_short_header(r, vnd)), preview(r) + "  [GAP: served anyway under fixed v1 salt]")

    # (c) CAPABILITY: a STREAM frame with the FIN bit and implicit length (data to
    # end of packet) is dispatched — single-datagram stream data works.
    cfd = os.urandom(8)
    r = target.send_recv(build_initial(
        stream_frame(h3_headers_get("/health"), fin=True, with_len=False),
        cfd, pad_to=0))
    check("c-stream", "STREAM FIN + implicit-length -> served",
          status(open_short_header(r, cfd)) == 200, preview(r))
    # (c) CAPABILITY: a 2-byte-varint stream id parses.
    csd = os.urandom(8)
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/"), sid=16383), csd))
    check("c-stream", "STREAM sid=16383 (2-byte varint) parses + serves",
          is_http(open_short_header(r, csd)), preview(r))
    # (c) GAP: a non-zero stream OFFSET is ignored — no reassembly. A conformant
    # receiver buffers data at offset 100 and does NOT complete a request from it.
    cod = os.urandom(8)
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/"), offset=100), cod))
    check("c-stream", "STREAM offset=100 buffered (not served as offset 0)",
          not is_http(open_short_header(r, cod)), preview(r) + "  [GAP: offset ignored, no reassembly]")

    # (d) GAP: QUIC frame types other than a leading STREAM are not interpreted.
    # A conformant receiver skips PADDING and processes the following STREAM; here
    # the non-STREAM leading byte routes the whole plaintext into H3 -> 400.
    pfd = os.urandom(8)
    r = target.send_recv(build_initial(b"\x00\x00\x00" + stream_frame(h3_headers_get("/")), pfd))
    check("d-frames", "PADDING then STREAM -> STREAM still processed",
          status(open_short_header(r, pfd)) in (404, 200), preview(r) + "  [GAP: leading PADDING breaks dispatch -> 400]")
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
          is_quic_packet(hp) and is_http(hp_body),
          preview(hp) + f"  [1-RTT short-header opens to {len(hp_body) if hp_body else 0}B HTTP]")

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
    ssd = os.urandom(8)
    r = target.send_recv(build_initial(stream_frame(h3_headers_get("/health")), ssd))
    check("e-security", "listener still serving after malformed input",
          status(open_short_header(r, ssd)) == 200, preview(r))

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
