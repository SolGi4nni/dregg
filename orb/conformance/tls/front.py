#!/usr/bin/env python3
"""TCP front for the TLS 1.3 handshake oracle (`tls-wire-oracle`).

This process is deliberately dumb: it accepts TCP connections and splits the
byte stream into TLS records (the 5-byte `type ‖ version ‖ length` header) —
nothing else. Every protocol decision and all cryptography happen in the
spawned oracle process (`TlsHandshake.serverStep` over EverCrypt); this front
merely shuttles each record to the oracle as a hex line and writes the
oracle's reply bytes back to the socket.

Record dispatch (RFC 8446 §5.1 content types):
  0x16 handshake         -> a ClientHello goes to the oracle as `CH <hex>`; the
                            oracle answers with the server flight, a
                            HelloRetryRequest, or a fatal alert
  0x14 change_cipher_spec-> dropped (RFC 8446 §5, middlebox compatibility:
                            "an implementation ... MUST simply drop it")
  0x17 application_data  -> during the handshake this is the client's
                            encrypted Finished flight (`FIN <hex>`); after
                            establishment it is application data driven through
                            the oracle's record layer as `APP <hex>`, which
                            serves HTTP over TLS
  0x15 alert             -> before establishment closes the connection; after,
                            forwarded as `APP <hex>` so the oracle can
                            reciprocate a close_notify

The oracle is authoritative for every protocol byte and every crypto decision;
this front only frames records and shuttles them.

Usage: front.py <oracle-binary> <cert.der> <seed.bin> [port] [chain.der ...]
"""

import socket
import socketserver
import subprocess
import sys

ORACLE, CERT, SEED = sys.argv[1], sys.argv[2], sys.argv[3]
PORT = int(sys.argv[4]) if len(sys.argv) > 4 else 4433
CHAIN = sys.argv[5:]


def read_exact(sock, n):
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            return None
        buf += chunk
    return buf


def read_record(sock):
    """Read one TLS record (header + payload). None on EOF/garbage."""
    hdr = read_exact(sock, 5)
    if hdr is None:
        return None
    ctype = hdr[0]
    if ctype not in (0x14, 0x15, 0x16, 0x17):
        return None  # not TLS record framing (e.g. an SSLv2 hello)
    length = (hdr[3] << 8) | hdr[4]
    if length > 1 << 14 + 8:
        return None
    body = read_exact(sock, length)
    if body is None:
        return None
    return ctype, hdr + body


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        self.request.settimeout(15)
        proc = subprocess.Popen(
            [ORACLE, CERT, SEED] + CHAIN,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        )

        def ask(line):
            proc.stdin.write(line + "\n")
            proc.stdin.flush()
            return (proc.stdout.readline() or "").strip()

        def send_hex(resp):
            """Write the hex payload of a `<TAG> <hex>` oracle reply."""
            self.request.sendall(bytes.fromhex(resp.split(" ", 1)[1]))

        try:
            # --- ClientHello(s): the oracle may ask for one HelloRetryRequest
            # round before producing the server flight. ---
            established = False
            while True:
                rec = read_record(self.request)
                if rec is None or rec[0] != 0x16:
                    return
                resp = ask("CH " + rec[1].hex())
                if resp.startswith("FLIGHT "):
                    send_hex(resp)
                    break
                if resp.startswith("HRR "):
                    send_hex(resp)
                    continue  # await the retried ClientHello
                if resp.startswith("ALERT "):
                    send_hex(resp)  # emit the fatal alert (RFC 8446 §6), close
                    return
                return  # unexpected

            # --- client Finished (CCS dropped per RFC 8446 §5) ---
            while not established:
                rec = read_record(self.request)
                if rec is None:
                    return
                ctype, raw = rec
                if ctype == 0x14:
                    continue
                if ctype == 0x15:
                    return
                if ctype == 0x17:
                    resp = ask("FIN " + raw.hex())
                    if resp == "ESTABLISHED":
                        established = True
                    elif resp.startswith("ESTABLISHED "):
                        # the oracle issued a NewSessionTicket record (and,
                        # after accepted 0-RTT, possibly the early response)
                        established = True
                        send_hex(resp)
                    elif resp == "CONT":
                        # 0-RTT phase: an early-data record, EndOfEarlyData,
                        # or a trial-skipped rejected-early record
                        continue
                    elif resp.startswith("ALERT "):
                        send_hex(resp)
                        return
                    else:
                        return
                else:
                    return

            # --- established: drive application data through the oracle's
            # record layer, which serves HTTP over TLS. ---
            while True:
                rec = read_record(self.request)
                if rec is None:
                    return
                ctype, raw = rec
                if ctype == 0x14:
                    continue
                if ctype in (0x17, 0x15):
                    resp = ask("APP " + raw.hex())
                    if resp.startswith("SEND "):
                        send_hex(resp)
                    elif resp.startswith("CLOSE ") or resp.startswith("ALERT "):
                        send_hex(resp)
                        return
                    elif resp == "NONE":
                        continue
                    else:
                        return
                else:
                    return
        except (socket.timeout, ConnectionError, BrokenPipeError, OSError):
            pass
        finally:
            try:
                proc.stdin.close()
            except OSError:
                pass
            proc.terminate()
            proc.wait(timeout=5)


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


if __name__ == "__main__":
    with Server(("127.0.0.1", PORT), Handler) as srv:
        print(f"tls front listening on 127.0.0.1:{PORT}", flush=True)
        srv.serve_forever()
