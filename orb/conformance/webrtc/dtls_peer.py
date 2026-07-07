#!/usr/bin/env python3
"""A real WebRTC peer's DTLS + SCTP + data-channel stack (aiortc) on a raw UDP socket.

Stands up aiortc's *exact* DTLS server — the SSL context aiortc's
`RTCDtlsTransport` builds (OpenSSL `DTLS_METHOD`, aiortc's cipher list, a freshly
generated ECDSA certificate, `use_srtp`) — and, once the DTLS 1.2 handshake
completes, drives aiortc's *real* `RTCSctpTransport` over that same DTLS
connection. That is the identical SCTP association / DCEP / data-channel code a
browser or aiortc peer runs; the only thing removed is the
RTCPeerConnection/ICE/SDP wrapper, so drorb's live driver (WebrtcLive.lean) can
reach it directly once ICE (which already interoperates with aiortc's aioice,
see conformance/stun/ice_battery.py) has selected the path.

The SCTP transport is wired to a thin stand-in for `RTCDtlsTransport` that
encrypts outbound SCTP with the live OpenSSL DTLS `SSL.Connection` and hands it
decrypted inbound SCTP; the SCTP association, the DCEP DATA_CHANNEL_OPEN/ACK, and
the string data-channel message are all aiortc's own code. When drorb opens a
channel and sends a message, aiortc's `on("datachannel")` and the channel's
`on("message")` fire — the real WebRTC events — and this peer prints them.

By default the server keeps aiortc's mutual-auth posture
(VERIFY_PEER | VERIFY_FAIL_IF_NO_PEER_CERT). Pass --server-auth-only to drop the
client-certificate requirement.

Usage (from the repository root):
    python3 conformance/webrtc/dtls_peer.py [port] [--server-auth-only]
Default port: 5556.
"""
import argparse
import asyncio
import socket
import types

from OpenSSL import SSL
from aiortc.rtcdtlstransport import RTCCertificate, SRTP_PROFILES
from aiortc.rtcsctptransport import RTCSctpCapabilities, RTCSctpTransport


def build_context(server_auth_only: bool) -> SSL.Context:
    cert = RTCCertificate.generateCertificate()
    ctx = cert._create_ssl_context(srtp_profiles=SRTP_PROFILES)
    if server_auth_only:
        ctx.set_verify(SSL.VERIFY_NONE, lambda *args: True)
    return ctx


def flush_bio(conn: SSL.Connection, sock: socket.socket, peer) -> None:
    """Send whatever DTLS records OpenSSL has queued on its write BIO."""
    while True:
        try:
            out = conn.bio_read(1500)
        except SSL.WantReadError:
            break
        if not out:
            break
        sock.sendto(out, peer)


class RawDtlsTransport:
    """Minimal `RTCDtlsTransport` stand-in that carries SCTP over a live OpenSSL
    DTLS `SSL.Connection`. `RTCSctpTransport` needs exactly: a `.state`, a
    `.transport.role` (to decide client/server — "controlled" makes aiortc the
    SCTP *server*, so drorb is the SCTP client that sends INIT), the data-receiver
    registration hooks, and `_send_data` to emit encrypted SCTP."""

    def __init__(self, conn: SSL.Connection, sock: socket.socket, peer) -> None:
        self.conn = conn
        self.sock = sock
        self.peer = peer
        self.state = "connected"
        self._data_receiver = None
        # role != "controlling" => RTCSctpTransport.is_server is True
        self.transport = types.SimpleNamespace(role="controlled")

    def _register_data_receiver(self, receiver) -> None:
        self._data_receiver = receiver

    def _unregister_data_receiver(self, receiver) -> None:
        if self._data_receiver is receiver:
            self._data_receiver = None

    async def _send_data(self, data: bytes) -> None:
        self.conn.send(data)
        flush_bio(self.conn, self.sock, self.peer)


async def run(port: int, server_auth_only: bool) -> None:
    ctx = build_context(server_auth_only)

    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("127.0.0.1", port))
    sock.setblocking(False)
    print(f"aiortc-dtls: server on 127.0.0.1:{port}/udp "
          f"({'server-auth-only' if server_auth_only else 'mutual-auth'})",
          flush=True)

    loop = asyncio.get_running_loop()
    conn = SSL.Connection(ctx)
    conn.set_accept_state()

    peer = None
    handshake_done = False
    sctp = None
    state = {"channel": None, "message": None}

    while True:
        try:
            data, addr = await asyncio.wait_for(
                loop.sock_recvfrom(sock, 65536), timeout=20)
        except asyncio.TimeoutError:
            print("aiortc-dtls: idle timeout, exiting", flush=True)
            break

        if peer is None:
            peer = addr
            print(f"aiortc-dtls: first datagram from {addr}, {len(data)} bytes; "
                  f"content-type={data[0]} version={data[1]:02x}{data[2]:02x}",
                  flush=True)

        conn.bio_write(data)

        if not handshake_done:
            try:
                conn.do_handshake()
            except SSL.WantReadError:
                pass
            except SSL.Error as exc:
                print(f"aiortc-dtls: handshake error: {exc}", flush=True)
            else:
                handshake_done = True
                print("aiortc-dtls: HANDSHAKE COMPLETE; cipher="
                      f"{conn.get_cipher_name()}", flush=True)

                # Wire aiortc's real SCTP + data-channel stack onto this DTLS conn.
                raw = RawDtlsTransport(conn, sock, peer)
                sctp = RTCSctpTransport(raw, port=5000)

                @sctp.on("datachannel")
                def _on_datachannel(channel):
                    state["channel"] = channel
                    print("aiortc-dtls: DATA CHANNEL OPEN "
                          f"(label={channel.label!r}, id={channel.id}, "
                          f"ordered={channel.ordered})", flush=True)

                    @channel.on("message")
                    def _on_message(msg):
                        state["message"] = msg
                        print(f"aiortc-dtls: DATACHANNEL MESSAGE RECEIVED: {msg!r}",
                              flush=True)

                await sctp.start(
                    RTCSctpCapabilities(maxMessageSize=65536), 5000)
            flush_bio(conn, sock, peer)

        if handshake_done:
            # Drain and dispatch every decrypted SCTP packet to aiortc's SCTP.
            while True:
                try:
                    pkt = conn.recv(65536)
                except SSL.WantReadError:
                    break
                except SSL.ZeroReturnError:
                    break
                except SSL.Error:
                    break
                if not pkt:
                    break
                await sctp._handle_data(pkt)
            flush_bio(conn, sock, peer)

            if state["message"] is not None:
                # Give aiortc a moment to emit its final SACK, then we are done.
                await asyncio.sleep(0.1)
                print("aiortc-dtls: data channel exchange complete", flush=True)
                break


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("port", nargs="?", type=int, default=5556)
    ap.add_argument("--server-auth-only", action="store_true")
    args = ap.parse_args()
    asyncio.run(run(args.port, args.server_auth_only))


if __name__ == "__main__":
    main()
