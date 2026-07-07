# QUIC-SERVER — the server response flight (RFC 9000 / RFC 9001)

`IoQuic` decrypts a real off-the-shelf client's QUIC Initial (verified EverCrypt
AES-128-GCM under AES-ECB header protection) and recovers the TLS ClientHello.
That is the *receive* half. `QuicServer.lean` is the *send* half: on a decrypted
ClientHello it derives the TLS 1.3 handshake secrets (X25519 DHE + the
`TlsCrypto`/`TlsHandshake` key schedule) and emits the server's response flight
as real QUIC packets, so an off-the-shelf client can **complete the 1-RTT
handshake**.

## What is real

* **The crypto is the verified EverCrypt seam throughout.** X25519 DHE
  (`Crypto.x25519`), the HKDF key schedule (`TlsCrypto`), ChaCha20-Poly1305 and
  AES-128-GCM AEAD packet protection, AES-ECB / ChaCha20 header protection
  (`QuicHeaderProt`), the Ed25519 CertificateVerify (`Crypto.ed25519Sign`), and
  SHA-256 transcript hashing. No unverified crypto is introduced.
* **The TLS content is `TlsHandshake` unchanged** — ServerHello,
  EncryptedExtensions, Certificate, CertificateVerify, Finished, the key
  schedule, the transcript. `QuicServer` supplies only the QUIC *carriage*:
  CRYPTO frames instead of the TLS record layer, the `quic_transport_parameters`
  extension real clients require, the QUIC packet framing, and the QUIC key
  labels (`quic key` / `quic iv` / `quic hp`).
* **The server flight is:** a server **Initial** packet (ACK + ServerHello in a
  CRYPTO frame, AES-128-GCM) coalesced with a server **Handshake** packet
  (EncryptedExtensions ‖ Certificate ‖ CertificateVerify ‖ Finished in a CRYPTO
  frame, ChaCha20-Poly1305 under the server_handshake_traffic_secret). On the
  client Finished the 1-RTT keys are installed and a HANDSHAKE_DONE is sent.
* **The certificate is a real self-signed Ed25519 X.509** whose public key is the
  Ed25519 public key of the signing seed, so a client's CertificateVerify
  signature check passes (chain trust is separately disabled with `CERT_NONE`,
  as for any self-signed test server).

## Simplifications (named honestly — the minimal 1-RTT, one connection)

* **One connection at a time.** No connection-ID table; the server tracks a
  single `Conn` (a demo, not a multi-tenant server).
* **1-byte packet numbers**, one CRYPTO frame per level at offset 0, no CRYPTO
  reassembly across frames/packets.
* **ACK-only, no loss recovery / retransmission / PTO**, no flow-control frame
  bookkeeping beyond generous initial transport-parameter limits.
* **No Retry, no version negotiation, no connection migration, no key update.**
* **Cipher fixed to `TLS_CHACHA20_POLY1305_SHA256`** for the handshake and 1-RTT
  levels (the server selects it); the Initial level is AES-128-GCM per RFC 9001
  §5.2. None of this touches the crypto — both AEADs are the verified primitives.
* **Static server ephemeral / random / SCID / cert seed** (so the flight is
  reproducible); a production server samples these per connection.

## HTTP/3 — a full GET body, and the residual

An off-the-shelf HTTP/3 client (aioquic 1.3.0) now completes the 1-RTT handshake
**and receives a full HTTP/3 response body**. `GET /health` returns the proven
serve's `200`/`ok`; `GET /` returns the Policy gate's `403`/`policy: undeclared
surface` — the same guarded responses the TCP/H1 path serves, re-expressed as
HTTP/3. The three pieces that close it:

* **QPACK Huffman decode** (`H3/Qpack.lean` — `rfc7541Huffman`, the RFC 7541
  Appendix B code) replaces the reject-all stub, so the client's Huffman-coded
  request field lines decode. The full RFC 9204 Appendix A static table (indices
  0–98) is modeled, so header names like `user-agent` (static index 95) resolve.
* **The server control stream + SETTINGS** (`buildH3Response`): a
  server-initiated unidirectional stream (id 3, type `0x00`) carrying a SETTINGS
  frame, which the client requires before accepting a response. The empty SETTINGS
  advertises QPACK max-table-capacity 0, so the client encodes its request with
  the static table + literals + Huffman (no QPACK **dynamic** table / encoder
  stream needed on either side).
* **The response as H3 HEADERS + DATA** (`serveH3` → `encodeH3Response`): the
  proven `Reactor.Response` is QPACK-encoded — `:status` via the static-table
  index when it has one (200/404/…), every other field a literal without Huffman
  (so no QPACK *encoder* Huffman is needed) — as a HEADERS frame, then a DATA
  frame for the body, on request stream 0.

Named simplifications: one connection at a time; the response is a single 1-RTT
packet (no response fragmentation) on request stream 0 (aioquic's first client
bidi stream); no QPACK dynamic table (forced off by the empty SETTINGS); and no
ACK / loss recovery on the 1-RTT leg (a single request/response exchange).
