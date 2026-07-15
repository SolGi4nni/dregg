# QUIC / HTTP-3 conformance battery — NOTES & gap map

A from-scratch RFC 9000 / RFC 9001 QUIC-Initial prober for the serve's UDP
datagram path, plus a supplementary post-quantum KEX probe on the TLS edge.
Every number in the report below is from an actual send/recv run on this host.

## Files (all new, disjoint)

- `battery.py`  — the battery. Crafts QUIC v1 Initial packets on the wire
  (AES-128-GCM AEAD + AES-ECB header protection + HKDF-SHA256 Initial keys,
  RFC 9001 §5.2–5.4), sends over UDP, inspects the reply. Pure `cryptography`
  (stdlib-adjacent, already installed); NO aioquic dependency.
- `runner.sh`   — brings up a dedicated serve on a UDP port, runs the battery,
  reaps the serve. Self-contained + self-reaping. `runner.sh [PORT]`.
- `pq_kex_probe.sh` — supplementary: drives `pq-xwing-client` against the TLS/TCP
  edge to show the X25519MLKEM768 hybrid is real + enforced. `pq_kex_probe.sh [PORT]`.

## Client availability

No off-the-shelf QUIC client was obtainable: aioquic is not installed and pip has
no network here (system python has no `pip`/`ensurepip`; the project venv is
broken). aioquic would not help anyway — it offers only classical X25519, and the
serve's QUIC handshake **requires** the X25519MLKEM768 hybrid. So the battery is a
**minimal protocol prober built from scratch** over the stdlib `cryptography`
package (v42.0.5, OpenSSL 3.3.1). This host is x86-64 with AES-NI, so the
RFC-9001-mandated AES-128-GCM Initial suite works here (unlike the arm64 origin
box the QUIC READMEs were written on, where AES-GCM was unavailable).

## Score — 8 / 17 checks pass (an HONEST partial; failures are the deliverable)

    a-decrypt      1/1   AES-128-GCM/AES-ECB Initial decrypt + H3 dispatch
    f-h3           2/2   GET /health -> 200 ok; GET / routed distinctly (404)
    c-stream       2/3   FIN+implicit-len served; sid=16383 served; offset ignored (FAIL)
    e-security     3/3   forged-tag drop; garbage no-crash; still-serving
    a-handshake    0/1   no QUIC handshake / no PQ KEX on the datapath
    b-versneg      0/2   no version negotiation; version not validated
    d-frames       0/3   PADDING / PING / ACK not interpreted (leak into H3 -> 400)
    e-close        0/1   CONNECTION_CLOSE not handled (leak into H3 -> 400)
    e-response     0/1   1-RTT reply is raw HTTP bytes, not a QUIC packet

## What actually works (verified my-hand on the wire)

1. **Verified EverCrypt QUIC Initial packet protection round-trips against an
   INDEPENDENT implementation.** Our `cryptography`-sealed, AES-ECB-header-protected
   v1 Initial is decrypted by the target's EverCrypt AES-128-GCM + AES-ECB and
   dispatched. Cross-impl agreement on RFC 9001 §5.2–5.4. (`a-decrypt`)
2. **HTTP/3 over QUIC serves.** A STREAM-framed H3 HEADERS+QPACK request decodes
   (RFC 9114 / RFC 9204 static table) and routes by `:path` through the proven
   serve: `GET /health -> 200 ok`, `GET / -> 404`. (`f-h3`)
3. **The AEAD authenticity gate holds.** A forged Initial (one tag byte flipped)
   is silently dropped — no reply. Malformed/truncated input does not crash the
   listener; it keeps serving. (`e-security`)
4. **Single-datagram STREAM framing:** FIN bit + implicit length parse; 2-byte
   varint stream ids parse. (`c-stream`)

## The gap map (deployed QUIC/UDP path — `drorbServeDatagram`)

The deployed UDP path is a **decrypt-one-Initial → H3-dispatch demo**, not a QUIC
connection. It parses a long-header Initial, AES-ECB-strips header protection,
AES-128-GCM-opens the payload, reads the FIRST frame as a STREAM frame, feeds its
bytes to the proven H3 dispatch, and returns the serve's **raw HTTP/1.1 bytes**.
Consequences, each observed:

- **No handshake, no PQ KEX on the QUIC wire.** `QuicServer.lean` (ServerHello,
  the X25519MLKEM768 hybrid KEX, `requireHybridKex=true`, the cert flight) is
  proven with zero sorries but is **not wired** into `drorbServeDatagram`. A
  CRYPTO-frame ClientHello never reaches it — the bytes fall through into H3 and
  400. So over QUIC the PQ KEX is presently untestable end-to-end. (`a-handshake`)
- **No version negotiation, no version validation.** `locateInitial` skips the
  4 version bytes without reading them, and the Initial salt is fixed to v1
  regardless, so a bogus version (0x1A2A3A4B) is served as if v1, and no Version
  Negotiation packet is ever sent (RFC 9000 §6). (`b-versneg`)
- **Only a LEADING STREAM frame is interpreted.** PADDING (0x00), PING (0x01),
  ACK (0x02), CRYPTO (0x06), CONNECTION_CLOSE (0x1c) as the first frame are NOT
  QUIC-parsed; the whole plaintext is handed to H3, which rejects it with a
  **400 Bad Request**. Multi-frame packets (PADDING-then-STREAM) break dispatch.
  (`d-frames`, `e-close`)
- **No connection / stream lifecycle.** Each datagram is independent — no
  connection-ID table, no stream reassembly (a non-zero STREAM offset is ignored
  and the data served as if offset 0), no close FSM, no loss recovery, no ACKs.
  (`c-stream` offset, `e-close`)
- **The response is not a QUIC packet.** The reply is cleartext HTTP/1.1, not a
  1-RTT-encrypted short-header packet, so no real QUIC/H3 client could consume it.
  (`e-response`)

## PQ KEX — where it IS real (supplementary TLS-edge probe)

The X25519MLKEM768 hybrid is proven and **enforced** on the TLS-over-TCP edge.
`pq_kex_probe.sh` observed, my-hand:

    MODE=pq-only  NEGOTIATED_GROUP=X25519MLKEM768  NEGOTIATED_GROUP_HEX=0x11EC  HTTP/1.1 200 OK
    MODE=classical  HANDSHAKE/WRITE FAILED: received fatal alert: HandshakeFailure

i.e. the server negotiates the PQ hybrid (0x11EC) and **fail-closes** a
classical-X25519-only client. `QuicServer.lean` uses the *same* hybrid with the
same `requireHybridKex=true` fail-closed gate — so when the handshake is wired
onto the QUIC datapath, the PQ KEX should carry over. It is proven; it is just
not on the deployed QUIC wire yet.

## Residual / next

- Wire `QuicServer.lean`'s handshake into `drorbServeDatagram` (CRYPTO-frame
  ClientHello → server Initial+Handshake flight), then the battery's
  `a-handshake` check can assert a real ServerHello and the PQ KEX end-to-end
  over QUIC. The battery already sends the ClientHello Initial; only the oracle
  flips from "gap" to "pass" once the flight comes back.
- Re-encrypt the 1-RTT response as a QUIC short-header packet so a real client
  can consume it; then swap in aioquic (once installable) for `e-response` and a
  full connection-lifecycle sweep.
- Version-negotiation and per-frame handling (PADDING/PING/ACK/CONNECTION_CLOSE)
  are unimplemented on the datapath; the battery checks are in place to flip to
  pass when they land.

## Box hygiene

Every serve this harness starts is on a dedicated port (18950+), started SYNC and
reaped by the runner's `trap ... EXIT`. Sibling lanes' serves (e.g. 8391, 18988)
are left alone. No drorb build was run by this lane.
