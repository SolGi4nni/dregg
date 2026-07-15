#!/usr/bin/env python3
"""TLS 1.3 conformance battery for the serve's HTTPS front door.

The target is a TLS 1.3 listener that REQUIRES a hybrid post-quantum key
exchange: it offers `[X25519MLKEM768 (0x11EC), X25519 (0x001D)]` but PINS the
hybrid group — a ClientHello that carries no X25519MLKEM768 share is rejected,
never silently downgraded to a classical shared secret.

This battery exercises RFC 8446 (TLS 1.3) behaviour plus that hybrid pin:

  A  hybrid X-Wing handshake succeeds (0x11EC negotiated + application data)
  B  a classical-only client is REJECTED (the require, not a downgrade)
  C  group / cipher negotiation (selected group on the wire, HelloRetryRequest
     when the client omits the hybrid share, unsupported-group rejection)
  D  version negotiation (a TLS 1.2 / sub-1.3 client is rejected)
  E  alert behaviour (garbage record, unexpected first message)
  F  the Certificate message is well-formed (a strict client parses it)
  G  0-RTT / early-data handling
  H  downgrade-sentinel resistance (ServerHello.random is clean)

Three probe engines are used, each honest about what it can see:

  * a hybrid-capable subprocess client drives a REAL X25519MLKEM768 handshake to
    completion — the only way to reach a real ServerHello / Certificate, since
    raw Python cannot produce an ML-KEM share;
  * a transparent recording TAP proxy sits between that client and the target
    and captures the plaintext server flight (ServerHello is cleartext in TLS
    1.3) so its selected group / cipher / version / random can be inspected on
    the wire;
  * hand-built raw ClientHellos exercise the rejection / HelloRetryRequest /
    version paths, where a valid key share is not required because the server
    decides before any ECDHE completes.

Every result is from an ACTUAL connection made by this run. Nothing is stubbed
to pass; FAIL / GAP rows are the useful output. Run:

    tls13_battery.py --target 127.0.0.1:18951 [--pq-client PATH]
"""

import argparse
import json
import os
import socket
import struct
import subprocess
import sys
import threading
import time

# ---- TLS constants -------------------------------------------------------
CT_CHANGE_CIPHER_SPEC = 0x14
CT_ALERT = 0x15
CT_HANDSHAKE = 0x16
CT_APP_DATA = 0x17

HS_CLIENT_HELLO = 0x01
HS_SERVER_HELLO = 0x02
HS_FINISHED = 0x14

GRP_X25519 = 0x001D
GRP_SECP256R1 = 0x0017
GRP_SECP521R1 = 0x0019
GRP_X25519MLKEM768 = 0x11EC

TLS12 = 0x0303
TLS13 = 0x0304

CIPHER_AES128_GCM = 0x1301
CIPHER_AES256_GCM = 0x1302
CIPHER_CHACHA20 = 0x1303

# RFC 8446 §4.1.3: HelloRetryRequest is a ServerHello whose random is this fixed
# value (SHA-256 of "HelloRetryRequest").
HRR_RANDOM = bytes.fromhex(
    "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c"
)

# RFC 8446 §4.1.3: a TLS 1.3 server that negotiates a lower version stamps these
# 8 bytes into the last 8 of ServerHello.random as a downgrade sentinel. A server
# that negotiates 1.3 MUST NOT set them.
DOWNGRADE_SENTINEL_13 = bytes.fromhex("444F574E47524401")  # "DOWNGRD\x01"
DOWNGRADE_SENTINEL_12 = bytes.fromhex("444F574E47524400")  # "DOWNGRD\x00"

ALERT_NAMES = {
    0: "close_notify", 10: "unexpected_message", 20: "bad_record_mac",
    22: "record_overflow", 40: "handshake_failure", 42: "bad_certificate",
    46: "certificate_unknown", 47: "illegal_parameter", 48: "unknown_ca",
    50: "decode_error", 51: "decrypt_error", 70: "protocol_version",
    71: "insufficient_security", 80: "internal_error", 86: "inappropriate_fallback",
    109: "missing_extension", 110: "unsupported_extension",
    112: "unrecognized_name", 120: "no_application_protocol",
}


# ---- record / ClientHello construction -----------------------------------
def u16(n):
    return struct.pack(">H", n)


def u24(n):
    return struct.pack(">I", n)[1:]


def ext(etype, body):
    return u16(etype) + u16(len(body)) + body


def record(ctype, payload, version=TLS12):
    return bytes([ctype]) + u16(version) + u16(len(payload)) + payload


def build_client_hello(
    supported_groups,
    key_shares,          # list of (group, kex_bytes)
    versions=(TLS13,),
    ciphers=(CIPHER_AES128_GCM, CIPHER_AES256_GCM, CIPHER_CHACHA20),
    include_supported_versions=True,
    server_name="localhost",
    add_early_data=False,
    legacy_version=TLS12,
    alpn=None,
):
    exts = b""
    if server_name is not None:
        host = server_name.encode()
        sni = u16(len(host) + 3) + b"\x00" + u16(len(host)) + host
        exts += ext(0x0000, sni)
    # supported_groups
    sg = b"".join(u16(g) for g in supported_groups)
    exts += ext(0x000A, u16(len(sg)) + sg)
    # signature_algorithms (ed25519, ecdsa-p256, rsa_pss_rsae_sha256, rsa_pkcs1)
    sa_list = [0x0807, 0x0403, 0x0804, 0x0401, 0x0805, 0x0806]
    sa = b"".join(u16(s) for s in sa_list)
    exts += ext(0x000D, u16(len(sa)) + sa)
    # key_share
    ks = b""
    for grp, kex in key_shares:
        ks += u16(grp) + u16(len(kex)) + kex
    exts += ext(0x0033, u16(len(ks)) + ks)
    # supported_versions
    if include_supported_versions:
        sv = b"".join(u16(v) for v in versions)
        exts += ext(0x002B, bytes([len(sv)]) + sv)
    # psk_key_exchange_modes (needed for a well-formed 1.3 CH; psk_dhe_ke)
    exts += ext(0x002D, bytes([1, 0x01]))
    if alpn is not None:
        protos = b""
        for p in alpn:
            pb = p.encode()
            protos += bytes([len(pb)]) + pb
        exts += ext(0x0010, u16(len(protos)) + protos)
    if add_early_data:
        exts += ext(0x002A, b"")

    body = (
        u16(legacy_version)
        + b"\x00" * 32                       # random
        + bytes([32]) + os.urandom(32)       # legacy_session_id (compat)
        + u16(len(ciphers) * 2) + b"".join(u16(c) for c in ciphers)
        + bytes([1, 0x00])                   # legacy_compression = null
        + u16(len(exts)) + exts
    )
    hs = bytes([HS_CLIENT_HELLO]) + u24(len(body)) + body
    return record(CT_HANDSHAKE, hs)


# ---- record reading / parsing --------------------------------------------
def read_server_flight(sock, timeout=3.0, max_bytes=65536):
    """Read whatever the server sends until it stalls / closes. Returns bytes."""
    sock.settimeout(timeout)
    buf = b""
    try:
        while len(buf) < max_bytes:
            chunk = sock.recv(4096)
            if not chunk:
                break
            buf += chunk
            sock.settimeout(0.6)  # short quiet window after first bytes
    except socket.timeout:
        pass
    except (ConnectionResetError, OSError):
        pass
    return buf


def split_records(buf):
    """Return a list of (content_type, version, payload) for complete records."""
    i = 0
    out = []
    while i + 5 <= len(buf):
        ctype = buf[i]
        ver = (buf[i + 1] << 8) | buf[i + 2]
        ln = (buf[i + 3] << 8) | buf[i + 4]
        if i + 5 + ln > len(buf):
            break
        out.append((ctype, ver, buf[i + 5:i + 5 + ln]))
        i += 5 + ln
    return out


def parse_server_hello(hs_payload):
    """Parse a handshake ServerHello body. Returns dict or None."""
    if not hs_payload or hs_payload[0] != HS_SERVER_HELLO:
        return None
    ln = (hs_payload[1] << 16) | (hs_payload[2] << 8) | hs_payload[3]
    body = hs_payload[4:4 + ln]
    p = 0
    legacy_version = (body[p] << 8) | body[p + 1]; p += 2
    random = body[p:p + 32]; p += 32
    sid_len = body[p]; p += 1
    p += sid_len
    cipher = (body[p] << 8) | body[p + 1]; p += 2
    p += 1  # compression
    ext_len = (body[p] << 8) | body[p + 1]; p += 2
    exts_end = p + ext_len
    selected_version = None
    key_share_group = None
    while p + 4 <= exts_end:
        et = (body[p] << 8) | body[p + 1]; p += 2
        el = (body[p] << 8) | body[p + 1]; p += 2
        ev = body[p:p + el]; p += el
        if et == 0x002B and len(ev) >= 2:
            selected_version = (ev[0] << 8) | ev[1]
        if et == 0x0033 and len(ev) >= 2:
            key_share_group = (ev[0] << 8) | ev[1]
    return {
        "legacy_version": legacy_version,
        "random": random,
        "cipher": cipher,
        "is_hrr": random == HRR_RANDOM,
        "selected_version": selected_version,
        "key_share_group": key_share_group,
    }


def first_handshake_serverhello(buf):
    for ctype, _ver, payload in split_records(buf):
        if ctype == CT_HANDSHAKE:
            sh = parse_server_hello(payload)
            if sh:
                return sh
    return None


def first_alert(buf):
    for ctype, _ver, payload in split_records(buf):
        if ctype == CT_ALERT and len(payload) >= 2:
            return {"level": payload[0], "desc": payload[1],
                    "name": ALERT_NAMES.get(payload[1], "alert_%d" % payload[1])}
    return None


# ---- transparent recording TAP proxy -------------------------------------
class Tap:
    """Accept one client connection, forward to `target`, record server bytes."""

    def __init__(self, target_host, target_port):
        self.th, self.tp = target_host, target_port
        self.srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.srv.bind(("127.0.0.1", 0))
        self.srv.listen(1)
        self.port = self.srv.getsockname()[1]
        self.server_bytes = b""
        self._t = None

    def start(self):
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()

    def _run(self):
        try:
            self.srv.settimeout(15)
            cs, _ = self.srv.accept()
        except socket.timeout:
            return
        us = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            us.connect((self.th, self.tp))
        except OSError:
            cs.close()
            return

        def pump(src, dst, record_it=False):
            try:
                while True:
                    d = src.recv(4096)
                    if not d:
                        break
                    if record_it:
                        self.server_bytes += d
                    dst.sendall(d)
            except OSError:
                pass
            finally:
                try:
                    dst.shutdown(socket.SHUT_WR)
                except OSError:
                    pass

        t1 = threading.Thread(target=pump, args=(cs, us, False), daemon=True)
        t2 = threading.Thread(target=pump, args=(us, cs, True), daemon=True)
        t1.start(); t2.start()
        t1.join(); t2.join()
        cs.close(); us.close()

    def stop(self):
        try:
            self.srv.close()
        except OSError:
            pass


# ---- probe primitives ----------------------------------------------------
def raw_probe(host, port, hello_bytes, timeout=3.0):
    """Send a hand-built ClientHello, return the server flight bytes (or b'')."""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect((host, port))
        s.sendall(hello_bytes)
        return read_server_flight(s, timeout=timeout)
    except OSError as e:
        return ("ERR:" + str(e)).encode()
    finally:
        try:
            s.close()
        except OSError:
            pass


def run_pq_client(pq_client, addr, mode, timeout=25):
    try:
        r = subprocess.run([pq_client, addr, mode], capture_output=True,
                           text=True, timeout=timeout)
        return r.returncode, r.stdout, r.stderr
    except FileNotFoundError:
        return None, "", "pq-client-not-found"
    except subprocess.TimeoutExpired:
        return None, "", "timeout"


# ---- the battery ---------------------------------------------------------
class Battery:
    def __init__(self, host, port, pq_client):
        self.host, self.port, self.pq_client = host, port, pq_client
        self.addr = "%s:%d" % (host, port)
        self.results = []
        self._sh_cache = None

    def add(self, cid, group, desc, status, detail):
        self.results.append({
            "id": cid, "group": group, "desc": desc,
            "status": status, "detail": detail,
        })

    def capture_serverhello(self):
        """Run ONE real hybrid handshake through a recording tap and cache
        everything the pq-only path yields: the pq-client's stdout (negotiated
        group / HTTP status — for check A1 / F1) and the plaintext server flight
        (the on-wire ServerHello — for A2 / C3 / D3 / H1). A successful handshake
        blocks until the server idle-closes the kept-alive connection, so doing
        it once keeps the battery from paying that latency several times over."""
        if self._sh_cache is not None:
            return self._sh_cache
        tap = Tap(self.host, self.port)
        tap.start()
        time.sleep(0.2)
        rc, out, _err = run_pq_client(self.pq_client, "127.0.0.1:%d" % tap.port,
                                      "pq-only")
        time.sleep(0.3)
        tap.stop()
        sh = first_handshake_serverhello(tap.server_bytes)
        self._sh_cache = (sh, rc, out, tap.server_bytes)
        return self._sh_cache

    # ---- A: hybrid handshake succeeds ----
    def check_A_hybrid_success(self):
        sh, rc, out, raw = self.capture_serverhello()
        if rc is None:
            self.add("A1", "A hybrid", "X25519MLKEM768 handshake completes",
                     "SKIP", "pq-client unavailable")
            return
        kv = dict(l.split("=", 1) for l in out.splitlines() if "=" in l)
        grp = kv.get("NEGOTIATED_GROUP_HEX", "")
        status_line = kv.get("HTTP_STATUS_LINE", "")
        ok = rc == 0 and grp == "0x11EC" and "200" in status_line
        self.add("A1", "A hybrid",
                 "X25519MLKEM768 (0x11EC) handshake completes + app data",
                 "PASS" if ok else "FAIL",
                 "rc=%s group=%s status=%r bytes=%s" %
                 (rc, grp, status_line, kv.get("RESPONSE_BYTES")))

    def check_A_serverhello_group_on_wire(self):
        sh, rc, out, raw = self.capture_serverhello()
        if sh is None:
            self.add("A2", "A hybrid",
                     "ServerHello selects 0x11EC on the wire",
                     "FAIL" if raw else "SKIP",
                     "no ServerHello captured (%d server bytes, pq rc=%s)" %
                     (len(raw), rc))
            return
        grp = sh["key_share_group"]
        ok = grp == GRP_X25519MLKEM768 and not sh["is_hrr"]
        self.add("A2", "A hybrid",
                 "ServerHello key_share group == 0x11EC on the wire",
                 "PASS" if ok else "FAIL",
                 "selected_group=0x%04X hrr=%s cipher=0x%04X" %
                 (grp or 0, sh["is_hrr"], sh["cipher"]))

    # ---- B: classical rejected ----
    def check_B_classical_client_rejected(self):
        rc, out, err = run_pq_client(self.pq_client, self.addr, "classical")
        if rc is None:
            self.add("B1", "B require", "classical-only client rejected",
                     "SKIP", "pq-client unavailable: " + err.strip())
            return
        blob = (out + err).lower()
        rejected = rc != 0 and ("handshakefailure" in blob or "alert" in blob
                                or "failed" in blob)
        self.add("B1", "B require",
                 "classical-only (X25519) client is REJECTED, not downgraded",
                 "PASS" if rejected else "FAIL",
                 "rc=%s signal=%r" % (rc, (err or out).strip()[:120]))

    def check_B_classical_raw_rejected(self):
        # supported_groups omits the hybrid entirely -> must reject.
        hello = build_client_hello(
            supported_groups=[GRP_X25519],
            key_shares=[(GRP_X25519, b"\x11" * 32)],
        )
        buf = raw_probe(self.host, self.port, hello)
        alert = first_alert(buf)
        sh = first_handshake_serverhello(buf)
        completed = sh is not None and not sh["is_hrr"]
        ok = (alert is not None or buf == b"" or buf.startswith(b"ERR:")) and not completed
        self.add("B2", "B require",
                 "raw classical-only ClientHello (no hybrid) is rejected",
                 "PASS" if ok else "FAIL",
                 "alert=%s serverhello=%s bytes=%d" %
                 (alert, bool(sh), len(buf)))

    # ---- C: group / cipher negotiation ----
    def check_C_hrr_on_missing_hybrid_share(self):
        # RFC 8446 §4.1.4: when the client offers a supported group in
        # `supported_groups` but sends no key_share for it, the server SHOULD
        # HelloRetryRequest for that group. We advertise the hybrid group two
        # ways — with NO key_share at all, and with only a classical share — and
        # accept an HRR selecting 0x11EC from EITHER.
        forms = [
            ("no key_share", []),
            ("classical share only", [(GRP_X25519, b"\x22" * 32)]),
        ]
        outcomes = []
        hrr_ok = False
        for label, ks in forms:
            hello = build_client_hello(
                supported_groups=[GRP_X25519MLKEM768, GRP_X25519],
                key_shares=ks,
            )
            buf = raw_probe(self.host, self.port, hello)
            sh = first_handshake_serverhello(buf)
            alert = first_alert(buf)
            if sh and sh["is_hrr"] and sh["key_share_group"] == GRP_X25519MLKEM768:
                hrr_ok = True
                outcomes.append("%s->HRR(0x11EC)" % label)
            else:
                outcomes.append("%s->%s" % (
                    label,
                    ("alert=%s" % alert["name"]) if alert else
                    ("SH" if sh else "bytes=%d" % len(buf))))
        self.add("C1", "C negotiation",
                 "HelloRetryRequest selects 0x11EC when the hybrid share is omitted",
                 "PASS" if hrr_ok else "FAIL",
                 "; ".join(outcomes))

    def check_C_unsupported_group_rejected(self):
        # Offer only a group the server does not support (secp521r1), no hybrid.
        hello = build_client_hello(
            supported_groups=[GRP_SECP521R1],
            key_shares=[],
        )
        buf = raw_probe(self.host, self.port, hello)
        alert = first_alert(buf)
        sh = first_handshake_serverhello(buf)
        completed = sh is not None and not sh["is_hrr"]
        ok = not completed and (alert is not None or buf == b"" or buf.startswith(b"ERR:"))
        self.add("C2", "C negotiation",
                 "unsupported-group-only ClientHello rejected (no downgrade)",
                 "PASS" if ok else "FAIL",
                 "alert=%s serverhello=%s bytes=%d" % (alert, bool(sh), len(buf)))

    def check_C_cipher_is_tls13_aead(self):
        sh, rc, out, raw = self.capture_serverhello()
        if sh is None:
            self.add("C3", "C negotiation", "negotiated cipher is a TLS 1.3 AEAD",
                     "SKIP", "no ServerHello captured")
            return
        ok = sh["cipher"] in (CIPHER_AES128_GCM, CIPHER_AES256_GCM, CIPHER_CHACHA20)
        self.add("C3", "C negotiation",
                 "negotiated cipher is a TLS 1.3 AEAD suite",
                 "PASS" if ok else "FAIL", "cipher=0x%04X" % sh["cipher"])

    # ---- D: version negotiation ----
    def check_D_tls12_client_rejected(self):
        # Pure TLS 1.2 ClientHello: legacy_version 0x0303, NO supported_versions.
        hello = build_client_hello(
            supported_groups=[GRP_X25519MLKEM768, GRP_X25519],
            key_shares=[(GRP_X25519, b"\x33" * 32)],
            include_supported_versions=False,
            legacy_version=TLS12,
        )
        buf = raw_probe(self.host, self.port, hello)
        alert = first_alert(buf)
        sh = first_handshake_serverhello(buf)
        negotiated_13 = sh is not None and not sh["is_hrr"] and sh["selected_version"] == TLS13
        ok = not negotiated_13 and (alert is not None or buf == b"" or buf.startswith(b"ERR:")
                                    or (sh is not None and sh["is_hrr"]))
        self.add("D1", "D version",
                 "TLS 1.2 ClientHello (no supported_versions) is not served 1.3",
                 "PASS" if ok else "FAIL",
                 "alert=%s serverhello=%s sel_ver=%s" %
                 (alert, bool(sh), sh["selected_version"] if sh else None))

    def check_D_supported_versions_only_12(self):
        hello = build_client_hello(
            supported_groups=[GRP_X25519MLKEM768, GRP_X25519],
            key_shares=[(GRP_X25519, b"\x44" * 32)],
            include_supported_versions=True,
            versions=(TLS12,),
        )
        buf = raw_probe(self.host, self.port, hello)
        alert = first_alert(buf)
        sh = first_handshake_serverhello(buf)
        negotiated_13 = sh is not None and not sh["is_hrr"] and sh["selected_version"] == TLS13
        ok = not negotiated_13 and (alert is not None or buf == b"" or buf.startswith(b"ERR:")
                                    or (sh is not None and sh["is_hrr"]))
        self.add("D2", "D version",
                 "supported_versions=[TLS1.2] only is rejected (1.3-only server)",
                 "PASS" if ok else "FAIL",
                 "alert=%s serverhello=%s sel_ver=%s" %
                 (alert, bool(sh), sh["selected_version"] if sh else None))

    def check_D_serverhello_version_tls13(self):
        sh, rc, out, raw = self.capture_serverhello()
        if sh is None:
            self.add("D3", "D version", "ServerHello supported_versions == 0x0304",
                     "SKIP", "no ServerHello captured")
            return
        ok = sh["selected_version"] == TLS13 and sh["legacy_version"] == TLS12
        self.add("D3", "D version",
                 "ServerHello advertises TLS 1.3 (0x0304) via supported_versions",
                 "PASS" if ok else "FAIL",
                 "selected_version=%s legacy=0x%04X" %
                 (hex(sh["selected_version"]) if sh["selected_version"] else None,
                  sh["legacy_version"]))

    # ---- E: alert behaviour ----
    def check_E_garbage_record(self):
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(6)
        try:
            s.connect((self.host, self.port))
            s.sendall(b"GARBAGE not a tls record \x00\x01\x02\x03\r\n\r\n")
            buf = read_server_flight(s, timeout=4)
        except OSError as e:
            buf = ("ERR:" + str(e)).encode()
        finally:
            s.close()
        alert = first_alert(buf)
        completed = first_handshake_serverhello(buf) is not None
        ok = not completed  # any non-completion (alert or close) is acceptable
        self.add("E1", "E alert",
                 "garbage / non-TLS record does not yield a handshake",
                 "PASS" if ok else "FAIL",
                 "alert=%s bytes=%d" %
                 (alert, len(buf) if isinstance(buf, bytes) else 0))

    def check_E_unexpected_first_message(self):
        # A valid handshake record whose first message is Finished, not
        # ClientHello -> unexpected_message / decode / handshake_failure / close.
        fin = bytes([HS_FINISHED]) + u24(32) + b"\x00" * 32
        rec = record(CT_HANDSHAKE, fin)
        buf = raw_probe(self.host, self.port, rec)
        alert = first_alert(buf)
        sh = first_handshake_serverhello(buf)
        completed = sh is not None and not sh["is_hrr"]
        ok = not completed
        self.add("E2", "E alert",
                 "unexpected first handshake message (Finished) is not accepted",
                 "PASS" if ok else "FAIL",
                 "alert=%s bytes=%d" % (alert, len(buf)))

    def check_E_app_data_before_handshake(self):
        rec = record(CT_APP_DATA, b"\xde\xad\xbe\xef" * 8)
        buf = raw_probe(self.host, self.port, rec)
        alert = first_alert(buf)
        completed = first_handshake_serverhello(buf) is not None
        ok = not completed
        self.add("E3", "E alert",
                 "application_data before the handshake is not accepted",
                 "PASS" if ok else "FAIL",
                 "alert=%s bytes=%d" % (alert, len(buf)))

    # ---- F: certificate well-formed ----
    def check_F_certificate_wellformed(self):
        # The Certificate message is inside the encrypted flight; only a client
        # that completes the handshake can parse it. The subprocess client parses
        # the Certificate structurally before its (accept-any) verifier runs, so a
        # completed handshake means the Certificate message decoded cleanly. This
        # reuses the single cached hybrid handshake (no extra connection).
        sh, rc, out, raw = self.capture_serverhello()
        if rc is None:
            self.add("F1", "F cert", "Certificate message parses (strict client)",
                     "SKIP", "pq-client unavailable")
            return
        kv = dict(l.split("=", 1) for l in out.splitlines() if "=" in l)
        ok = rc == 0 and "200" in kv.get("HTTP_STATUS_LINE", "")
        self.add("F1", "F cert",
                 "server Certificate message is well-formed (strict client parses it)",
                 "PASS" if ok else "FAIL",
                 "handshake-completed=%s (client decoded Certificate) rc=%s" %
                 (ok, rc))

    # ---- G: 0-RTT / early data ----
    def check_G_early_data(self):
        # The deployment gates 0-RTT on an env opt-in; unset => resumption only.
        # EncryptedExtensions (where early_data acceptance would show) is
        # encrypted and the subprocess client performs no resumption, so a full
        # 0-RTT accept/reject assertion is not reachable with available tooling.
        # We assert the negative safety property: an early_data extension without
        # a PSK does not trip a real 1.3 ServerHello acceptance on the wire.
        hello = build_client_hello(
            supported_groups=[GRP_X25519MLKEM768, GRP_X25519],
            key_shares=[(GRP_X25519, b"\x55" * 32)],
            add_early_data=True,
        )
        buf = raw_probe(self.host, self.port, hello)
        sh = first_handshake_serverhello(buf)
        alert = first_alert(buf)
        completed = sh is not None and not sh["is_hrr"] and sh["selected_version"] == TLS13
        observable = not completed
        self.add("G1", "G early-data",
                 "early_data without PSK does not yield a 1.3 ServerHello (0-RTT gated)",
                 "PARTIAL" if observable else "FAIL",
                 "note: EncryptedExtensions not observable raw; "
                 "serverhello=%s hrr=%s alert=%s" %
                 (bool(sh), sh["is_hrr"] if sh else None, alert))

    # ---- H: downgrade sentinel ----
    def check_H_downgrade_sentinel(self):
        sh, rc, out, raw = self.capture_serverhello()
        if sh is None:
            self.add("H1", "H downgrade",
                     "ServerHello.random has no downgrade sentinel",
                     "SKIP", "no ServerHello captured")
            return
        last8 = sh["random"][-8:]
        clean = last8 not in (DOWNGRADE_SENTINEL_13, DOWNGRADE_SENTINEL_12)
        ok = clean and not sh["is_hrr"]
        self.add("H1", "H downgrade",
                 "TLS 1.3 ServerHello.random carries no downgrade sentinel",
                 "PASS" if ok else "FAIL",
                 "random_tail=%s hrr=%s" % (last8.hex(), sh["is_hrr"]))

    def run(self):
        checks = [
            self.check_A_hybrid_success,
            self.check_A_serverhello_group_on_wire,
            self.check_B_classical_client_rejected,
            self.check_B_classical_raw_rejected,
            self.check_C_hrr_on_missing_hybrid_share,
            self.check_C_unsupported_group_rejected,
            self.check_C_cipher_is_tls13_aead,
            self.check_D_tls12_client_rejected,
            self.check_D_supported_versions_only_12,
            self.check_D_serverhello_version_tls13,
            self.check_E_garbage_record,
            self.check_E_unexpected_first_message,
            self.check_E_app_data_before_handshake,
            self.check_F_certificate_wellformed,
            self.check_G_early_data,
            self.check_H_downgrade_sentinel,
        ]
        for c in checks:
            t0 = time.time()
            sys.stderr.write("[battery] %s ...\n" % c.__name__)
            sys.stderr.flush()
            try:
                c()
            except Exception as e:  # a probe bug must not abort the battery
                self.add(c.__name__, "?", c.__name__, "ERROR", repr(e))
            sys.stderr.write("[battery] %s done (%.1fs)\n" % (c.__name__, time.time() - t0))
            sys.stderr.flush()
        return self.results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", default=os.environ.get("TLS_TARGET", "127.0.0.1:18951"))
    ap.add_argument("--pq-client",
                    default=os.environ.get("PQ_CLIENT",
                        os.path.expanduser("~/pq-xwing-client/target/release/pq-xwing-client")))
    ap.add_argument("--json", default=None, help="write JSON results to this path")
    args = ap.parse_args()
    host, port = args.target.rsplit(":", 1)
    port = int(port)

    b = Battery(host, port, args.pq_client)
    results = b.run()

    counts = {}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1

    print("=" * 78)
    print("TLS 1.3 conformance battery — target %s" % args.target)
    print("=" * 78)
    print("%-5s %-14s %-8s %s" % ("ID", "GROUP", "STATUS", "CHECK"))
    print("-" * 78)
    for r in results:
        print("%-5s %-14s %-8s %s" % (r["id"], r["group"], r["status"], r["desc"]))
        print("        -> %s" % r["detail"])
    print("-" * 78)
    n = len(results)
    summary = "  ".join("%s=%d" % (k, counts[k]) for k in sorted(counts))
    print("%d checks:  %s" % (n, summary))

    if args.json:
        with open(args.json, "w") as f:
            json.dump({"target": args.target, "counts": counts, "results": results},
                      f, indent=2)
        print("wrote %s" % args.json)

    hard = counts.get("FAIL", 0) + counts.get("ERROR", 0)
    sys.exit(1 if hard else 0)


if __name__ == "__main__":
    main()
