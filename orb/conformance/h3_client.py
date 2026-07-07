#!/usr/bin/env python3
"""Minimal HTTP/3 client for the conformance suite.

Drives a single GET over QUIC/H3 against a local server using aioquic, prints
one line `STATUS <code> BODY <repr>` (or `ERROR <msg>`). Run with the venv
python that has aioquic installed (see run.sh). CERT_NONE: the server presents a
self-signed Ed25519 cert, so chain trust is disabled exactly as for any
self-signed test server.

Usage: h3_client.py <port> <path>
"""
import asyncio
import ssl
import sys

from aioquic.asyncio import connect
from aioquic.asyncio.protocol import QuicConnectionProtocol
from aioquic.quic.configuration import QuicConfiguration
from aioquic.h3.connection import H3Connection
from aioquic.h3.events import HeadersReceived, DataReceived


class H3Client(QuicConnectionProtocol):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._http = H3Connection(self._quic)
        self.done = asyncio.Event()
        self.status = None
        self.body = b""

    def quic_event_received(self, event):
        for he in self._http.handle_event(event):
            if isinstance(he, HeadersReceived):
                for k, v in he.headers:
                    if k == b":status":
                        self.status = v.decode()
            elif isinstance(he, DataReceived):
                self.body += he.data
                if he.stream_ended:
                    self.done.set()

    async def get(self, path):
        sid = self._quic.get_next_available_stream_id()
        self._http.send_headers(
            sid,
            [(b":method", b"GET"), (b":scheme", b"https"),
             (b":authority", b"x"), (b":path", path.encode())],
            end_stream=True,
        )
        self.transmit()
        await asyncio.wait_for(self.done.wait(), timeout=8)


async def run(port, path):
    cfg = QuicConfiguration(is_client=True, alpn_protocols=["h3"])
    cfg.verify_mode = ssl.CERT_NONE
    async with connect("127.0.0.1", int(port), configuration=cfg,
                       create_protocol=H3Client) as c:
        await c.get(path)
        print("STATUS", c.status, "BODY", repr(c.body))


if __name__ == "__main__":
    try:
        asyncio.run(run(sys.argv[1], sys.argv[2]))
    except Exception as e:  # noqa: BLE001 - report any failure as a driven result
        print("ERROR", type(e).__name__, str(e))
