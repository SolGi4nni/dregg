/-
Dataplane.Multi — the datagram and WebSocket-frame seams of the proven serve,
exposed with a C ABI for the native (Rust) dataplane host to drive alongside the
byte-stream `drorb_serve`.

`Dataplane.lean` exports `drorb_serve` (`ByteArray -> ByteArray`) — the TCP
byte-stream fork (HTTP/1.1 + h2c prior-knowledge to the real H2 engine). This
module adds the two seams a multi-protocol host needs, as the SAME kind of
`@[export]` the host calls per unit of work:

  * `drorb_serve_ws_frame` — one inbound (client→server, masked) WebSocket
    frame's bytes in; the proven `Reactor.Ws.wsFeedFn` decodes/unmasks/reassembles
    them (real length ladder + real `applyMask` + real `Ws.Reassembly` fold) and
    each delivered logical frame is re-encoded to the wire by the proven
    `Reactor.Ws.wsEncodeFn` (server frames unmasked) — a proven-path echo. The
    host owns the RFC 6455 Upgrade handshake (socket + the one `Sec-WebSocket-
    Accept` SHA-1, which the proven core does not ship) and the open connection;
    the WebSocket DATA path is entirely this proven function. Identical to
    `IoMacMulti.wsHandle`, only the caller (Rust) differs.

  * `drorb_serve_datagram` — one UDP datagram's bytes in (a QUIC long-header
    Initial packet); a QUIC 1-RTT short-header response packet out (the served HTTP
    re-encrypted via the proven `QuicServer.buildShortPacket`). The datagram is DECRYPTED
    in Lean by the verified EverCrypt QUIC packet protection (RFC 9001 §5: HKDF
    Initial key schedule, AES-ECB header protection removal §5.4.3, AES-128-GCM
    AEAD open §5.3) before its STREAM frame's HTTP/3 bytes reach the UNCHANGED
    proven `Reactor.QuicIngress.datagramServe` (real `Quic.step` + `H3.decFrame` +
    QPACK decode + `RingSubmission.dispatch`), which is then served through the
    same proven guarded pipeline the TCP forks run (`Reactor.Ingress.serveOverSubs`).

## Provenance of the QUIC decrypt path

The QUIC Initial locate/derive/open/parse below is the library-safe form of the
`orb-quic` transport path (`IoQuic`): identical computation over the identical
verified primitives (`Crypto.hkdfExtract`, `TlsCrypto.expandLabel`,
`Crypto.aesGcmOpen`, `QuicHeaderProt.removeHpAes` → HACL*/EverCrypt), differing
only in that `IoQuic` also carries an exe `main` (a real C `main` symbol) that
cannot be pulled into a host binary that has its own `main`. So this file
re-expresses the pure decrypt orchestration in the `Dataplane.Multi` namespace and
reuses the SAME proven crypto and the SAME proven `datagramServe`/`serveOverSubs`.
No crypto is reimplemented — every AEAD/HKDF/AES-ECB step is a call to the verified
seam. The RFC 9001 A.1 vectors that anchor those primitives are checked by
`quic-transport-selftest`; this file adds no new trusted crypto.

Zero `sorry`; the exports are total `ByteArray -> ByteArray` `def`s.
-/
import Reactor.Ingress
import Reactor.Quic
import Reactor.QuicIngress
import Reactor.Ws
import Crypto
import TlsCrypto
import QuicHeaderProt
import QuicServer
import H3.Request
import H3.Qpack

namespace Dataplane
namespace Multi

open Crypto TlsCrypto
open Proto (Bytes)

/-! ## (1) The WebSocket frame seam — the real frame engine, echoed -/

/-- **`drorb_serve_ws_frame`.** The bytes of one inbound (masked, client→server)
WebSocket frame in; the proven `Reactor.Ws.wsFeedFn` decodes them (real length
ladder + real `applyMask` unmask + real `Ws.Reassembly` fold), delivering the
logical frames, each of which is re-encoded to the wire by the proven
`Reactor.Ws.wsEncodeFn` (server frames unmasked). A proven-path echo — the same
pipeline `IoMacMulti.wsHandle` runs; the host writes these bytes straight back
over the open connection. Nothing here knows a socket exists. -/
-- RETIRED EXPORT (`drorb_serve_ws_frame`). This one-shot whole-frame echo was the
-- WebSocket exemplar; the RUNNING WebSocket engine crosses the INCREMENTAL proven
-- seam family instead — `drorb_ws_header` (Ws.Decode frame verdict),
-- `drorb_ws_admit` / `drorb_ws_utf8` / `drorb_ws_close_body` (Ws.Reassembly*), and
-- `drorb_ws_encode_header` / `drorb_ws_encode_close` (Ws.Encode) — all six
-- DEFAULT-PATH on all three reactors, and together strictly more than this echo
-- (fragmentation, control frames, close handshake, streaming). The host's
-- `Seam::WsFrame` dispatch arm was dead: nothing constructed the variant.
-- Definition and theorems unchanged.
def drorbServeWsFrame (frame : ByteArray) : ByteArray :=
  let out := Reactor.Ws.wsFeedFn ({} : Proto.WsCodec) frame.toList
  let echoed := (out.frames.map Reactor.Ws.wsEncodeFn).flatten
  ByteArray.mk echoed.toArray

/-! ## (2) The QUIC Initial packet protection — verified EverCrypt derivations

Every step below is a call to the verified `Crypto`/`TlsCrypto`/`QuicHeaderProt`
seam (HACL*/EverCrypt), the same primitives `QuicTransport`/`IoQuic` are built on
and `quic-transport-selftest` checks against the RFC 9001 Appendix A.1 vectors. -/

/-- RFC 9001 §5.2 QUIC v1 initial salt. -/
def initialSalt : ByteArray :=
  ByteArray.mk #[0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
                 0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a]

/-- `HKDF-Extract(initial_salt, DCID)` then `HKDF-Expand-Label(·,"client in","",32)`
(RFC 9001 §5.2) — real HKDF over EverCrypt. -/
def clientInitialSecret (dcid : ByteArray) : Option ByteArray :=
  (hkdfExtract initialSalt dcid).bind
    (fun s => expandLabel s "client in".toUTF8 ByteArray.empty 32)

/-- One level's AES-128-GCM packet keys: AEAD `key`/write-`iv` (RFC 9001 §5.3) and
the header-protection key `hp` (§5.4). -/
structure PacketKeys where
  key : ByteArray
  iv : ByteArray
  hp : ByteArray

/-- The **AES-128-GCM** Initial keys (RFC 9001 §5.2): `key = HKDF-Expand-Label(
secret,"quic key","",16)`, `iv = …("quic iv","",12)`, `hp = …("quic hp","",16)` —
the cipher §5.2 mandates for QUIC Initial packets. Real HKDF over EverCrypt. -/
def deriveAesKeys (secret : ByteArray) : Option PacketKeys :=
  match expandLabel secret "quic key".toUTF8 ByteArray.empty 16,
        expandLabel secret "quic iv".toUTF8 ByteArray.empty 12,
        expandLabel secret "quic hp".toUTF8 ByteArray.empty 16 with
  | some k, some iv, some hp => some { key := k, iv := iv, hp := hp }
  | _, _, _ => none

/-- Open an **AES-128-GCM** protected packet: `Crypto.aesGcmOpen` at the RFC 9001
§5.3 per-packet nonce (`TlsCrypto.recordNonce`), QUIC header as additional data. -/
def openPacketAes (pk : PacketKeys) (pn : Nat) (header ct : ByteArray) : Option ByteArray :=
  aesGcmOpen pk.key (recordNonce pk.iv pn) header ct

/-! ## (3) QUIC wire parse — locate the header-protected fields -/

/-- Read a QUIC variable-length integer (RFC 9000 §16). Returns `(value, len)`. -/
def readVarint (bs : List UInt8) : Option (Nat × Nat) :=
  match bs with
  | [] => none
  | b0 :: _ =>
    let len := 1 <<< (b0 >>> 6).toNat
    if bs.length < len then none
    else
      let first := (b0 &&& 0x3f).toNat
      let rest := (bs.drop 1).take (len - 1)
      let v := rest.foldl (fun acc x => acc * 256 + x.toNat) first
      some (v, len)

/-- What the header parse locates before header protection is removed: the DCID
(Initial-key input), the packet-number field offset `pnOff`, and the packet. -/
structure Located where
  dcid : ByteArray
  pnOff : Nat
  pkt : List UInt8

/-- Parse a QUIC long-header **Initial** packet (RFC 9000 §17.2.2) up to the start
of the header-protected packet number. Only the header type (bits 4–7 of the first
byte) and DCID are read in the clear. -/
def locateInitial (dg : ByteArray) : Option Located :=
  let bs := dg.toList
  match bs[0]? with
  | none => none
  | some b0 =>
    if (b0 &&& 0xF0) != 0xC0 then none else
    let dcidLenOff := 1 + 4
    match bs[dcidLenOff]? with
    | none => none
    | some dcidLenB =>
      let dcidLen := dcidLenB.toNat
      let dcidStart := dcidLenOff + 1
      let dcid := (bs.drop dcidStart).take dcidLen
      let scidLenOff := dcidStart + dcidLen
      match bs[scidLenOff]? with
      | none => none
      | some scidLenB =>
        let scidLen := scidLenB.toNat
        let tokLenOff := scidLenOff + 1 + scidLen
        match readVarint (bs.drop tokLenOff) with
        | none => none
        | some (tokLen, tokLenBytes) =>
          let lenOff := tokLenOff + tokLenBytes + tokLen
          match readVarint (bs.drop lenOff) with
          | none => none
          | some (_lenField, lenBytes) =>
            let pnOff := lenOff + lenBytes
            some { dcid := ⟨dcid.toArray⟩, pnOff := pnOff, pkt := bs }

/-- **Cipher-agile Initial open** (AES-128-GCM, the RFC 9001 §5.2 Initial suite).
Derive the client AES-128-GCM Initial keys from the DCID, REMOVE AES-ECB header
protection (§5.4.3 — `QuicHeaderProt.removeHpAes` over `Crypto.aesEcbBlock`) to
recover the unprotected first byte + packet number, then open the protected payload
with `openPacketAes` (real AES-128-GCM, unprotected header as AAD, decoded packet
number as the nonce input). Returns `(pn, plaintext)`. `none` on any derivation /
HP / AEAD-auth failure. -/
def openInitial (loc : Located) (expectedPn : Nat := 0) : Option (Nat × ByteArray) :=
  match clientInitialSecret loc.dcid with
  | none => none
  | some clientSecret =>
    match deriveAesKeys clientSecret with
    | none => none
    | some pk =>
      match QuicHeaderProt.removeHpAes loc.pkt loc.pnOff pk.hp expectedPn with
      | none => none
      | some up =>
        let ct : ByteArray := ⟨(loc.pkt.drop (loc.pnOff + up.pnLen)).toArray⟩
        match openPacketAes pk up.pn up.header ct with
        | none => none
        | some pt => some (up.pn, pt)

/-- Parse a QUIC **STREAM** frame (RFC 9000 §19.8) out of the decrypted payload:
frame type `0b0000_1off`. Returns `(streamId, streamData)`. -/
def parseStreamFrame (pt : ByteArray) : Option (Nat × List UInt8) :=
  let bs := pt.toList
  match bs[0]? with
  | none => none
  | some ft =>
    if (ft &&& 0xF8) != 0x08 then none else
    match readVarint (bs.drop 1) with
    | none => none
    | some (sid, sidBytes) =>
      let afterSid := 1 + sidBytes
      let afterOff :=
        if (ft &&& 0x04) != 0 then
          match readVarint (bs.drop afterSid) with
          | some (_, ob) => afterSid + ob
          | none => afterSid
        else afterSid
      if (ft &&& 0x02) != 0 then
        match readVarint (bs.drop afterOff) with
        | some (dlen, lb) => some (sid, (bs.drop (afterOff + lb)).take dlen)
        | none => none
      else
        some (sid, bs.drop afterOff)

/-! ## (4) The datagram seam — the QUIC handshake, then H3 dispatch -/

/-- **The QUIC handshake completion on the datagram seam.** A received Initial
whose CRYPTO frames reassemble a complete TLS ClientHello is answered with the
server response flight: a server Initial carrying the ServerHello and a server
Handshake carrying EncryptedExtensions ‖ Certificate ‖ CertificateVerify ‖
Finished, coalesced and padded to 1200 bytes. The whole flight is the proven
`QuicServer.buildFlightFromCH` over the verified EverCrypt primitives — the
REQUIRED `X25519MLKEM768` post-quantum hybrid KEX (`QuicServer.quicKex`, pinned
`requireHybridKex = true`: a classical-only ClientHello gets no flight,
`QuicServer.buildTlsFlight_requires_hybrid`), the RFC 8446 key schedule, and the
RFC 9001 §5 packet protection. The client Initial is decrypted with
`QuicServer.decryptInitialFrames` (verified AES-128-GCM under AES-ECB header
protection) and its CRYPTO segments reassembled by the proven
`QuicServer.assembleFrom` (`assembleFrom_exact`).

Stateless, matching this one-datagram seam: the first Initial's ClientHello is
answered directly with the flight. What this seam does NOT do (it holds no
connection table across datagrams): stateless-Retry address validation, a
multi-packet ClientHello spanning Initials, and installing the 1-RTT keys on the
client Finished. Those need the stateful `QuicServer.stepServer` machine with a
host-side `ServerState`. `none` when the datagram carries no complete ClientHello
or the offered KEX is not the required hybrid (fail-closed). -/
def datagramHandshake (dg : ByteArray) : Option ByteArray := do
  let loc ← QuicServer.locateLong dg.toList
  -- Only an Initial packet carries the ClientHello; the AES-128-GCM Initial-key
  -- decrypt below would fail-closed for any other level anyway.
  guard (loc.kind == QuicServer.PktKind.initial)
  let (pn, frs) ← QuicServer.decryptInitialFrames dg.toList loc 0
  let segs := frs.foldl (fun (acc : List (Nat × List UInt8)) f =>
    match f with
    | .crypto off d => QuicServer.insSeg acc off d
    | _ => acc) []
  let ch ← QuicServer.completeHsMsg (QuicServer.assembleFrom segs segs.length 0)
  let (flight, _conn) ← QuicServer.buildFlightFromCH loc.dcid loc.dcid loc.scid
    ⟨ch.toArray⟩ [pn] 0
  some flight

/-- DEMO 1-RTT application keys from the client DCID: a labeled demo schedule
(`HKDF-Expand-Label(HKDF-Extract(initial_salt, DCID), "demo 1rtt", "", 32)` then the
ChaCha20-Poly1305 `key`/`iv`/`hp`), parallel to the Initial secret. It lets the
app-over-Initial response be re-encrypted as a REAL QUIC short-header packet by the
proven `QuicServer.buildShortPacket`, openable by an independent client that derives
the same DCID-keyed secret. It is NOT the handshake-derived 1-RTT secret; the real
1-RTT keying is on the stateful `QuicServer.stepServer` path. -/
def demoAppKeys (dcid : ByteArray) : Option QuicServer.PacketKeys :=
  (hkdfExtract initialSalt dcid).bind (fun s =>
    (expandLabel s "demo 1rtt".toUTF8 ByteArray.empty 32).bind
      QuicServer.deriveChachaKeys)

/-- The served 1-RTT reply for one app request stream: the proven guarded serve
of the H3 request bytes (real `datagramServe` → `serveFull2OverSubs`),
re-encrypted as a REAL QUIC short-header packet (RFC 9000 §17.3) under the DEMO
1-RTT keys via `QuicServer.buildShortPacket`. Falls back to the raw served bytes
only if key derivation or the seal fails (unreachable for a well-formed
response). -/
def demoServe (dcid : ByteArray) (sid : Nat) (h3 : List UInt8) : ByteArray :=
  let ev := Reactor.Quic.DatagramEvent.recvDatagram .appData 0
              (Reactor.Quic.Payload.stream sid h3)
  let subs := (Reactor.QuicIngress.datagramServe
    Reactor.QuicIngress.demoConfig Reactor.QuicIngress.demoState ev).2
  let served : ByteArray :=
    ByteArray.mk (Reactor.Ingress.serveFull2OverSubs subs h3).toArray
  match demoAppKeys dcid with
  | none => served
  | some ap =>
    let frame := QuicServer.streamFrame sid 0 true served
    match QuicServer.buildShortPacket dcid 0 false false frame ap with
    | none => served
    | some pkt => pkt

/-- Whether the datagram is a QUIC long-header packet (RFC 9000 §17.2: high bit of
the first byte set). -/
def isLongHeader (dg : ByteArray) : Bool :=
  match dg.toList[0]? with
  | some b => (b &&& 0x80) != 0
  | none => false

/-- Whether a long-header datagram's version field is QUIC v1 (`0x00000001`, bytes
1–4). A non-v1 long header is answered with Version Negotiation, never served. -/
def isV1 (dg : ByteArray) : Bool :=
  (dg.toList.drop 1).take 4 == [0x00, 0x00, 0x00, 0x01]

/-! ## (4a) The HTTP/3 response encoder — real H3 HEADERS+DATA

The 1-RTT reply an off-the-shelf HTTP/3 client can actually consume is a HEADERS
frame (QPACK field section) followed by a DATA frame, NOT the H1 serialization the
demo path stuffs in a STREAM frame. `serveH3Multi` is the H3 sibling of the H1
serve: it runs the same proven `Reactor.QuicIngress.datagramServe` + full
`deployStagesFull2` middleware fold, then re-frames the guarded `Reactor.Response`
as the HTTP/3 stream payload. The `stepServer` 1-RTT path (`QuicServer.onShort`)
serves through this, so a client's request stream gets a real H3 response under the
handshake-derived keys.

These QPACK-encode defs mirror `IoQuic` verbatim (same proven functions); they are
re-expressed here because `IoQuic` carries an exe `main` that cannot be linked into
the dataplane host, exactly as the QUIC decrypt path above is. (Candidate for a
shared `H3.Encode` module, so this and `IoQuic` share one encoder.) -/

/-- QPACK prefix-integer encode (RFC 9204 §4.1.1). -/
partial def encQpackInt (prefixBits : Nat) (flags : UInt8) (v : Nat) : ByteArray :=
  let maxP := 2 ^ prefixBits - 1
  if v < maxP then ByteArray.mk #[flags ||| UInt8.ofNat v]
  else
    let rec go (n : Nat) (acc : ByteArray) : ByteArray :=
      if n < 128 then acc.push (UInt8.ofNat n)
      else go (n / 128) (acc.push (UInt8.ofNat (n % 128 + 128)))
    go (v - maxP) (ByteArray.mk #[flags ||| UInt8.ofNat maxP])

/-- A QPACK string literal (Huffman bit clear). -/
def encQpackStr (prefixBits : Nat) (flags : UInt8) (bs : ByteArray) : ByteArray :=
  encQpackInt prefixBits flags bs.size ++ bs

/-- Literal field line with literal name, no Huffman (RFC 9204 §4.5.6). -/
def encQpackLiteral (name value : ByteArray) : ByteArray :=
  encQpackStr 3 0x20 name ++ encQpackStr 7 0x00 value

/-- The RFC 9204 Appendix A static-table index of a `:status` code, when it has one. -/
def qpackStatusIndex (status : Nat) : Option Nat :=
  if status = 103 then some 24
  else if status = 200 then some 25
  else if status = 304 then some 26
  else if status = 404 then some 27
  else if status = 503 then some 28
  else none

/-- The `:status` field: indexed static field line for a code in the static table,
else a literal `:status` field with the decimal code as value. -/
def encQpackStatus (status : Nat) : ByteArray :=
  match qpackStatusIndex status with
  | some idx => ByteArray.mk #[UInt8.ofNat (0xC0 ||| idx)]
  | none => encQpackLiteral (String.toUTF8 ":status")
              ⟨(Reactor.natToDec status).toArray⟩

/-- Lowercase one ASCII byte. -/
def lowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat && b.toNat ≤ 90 then UInt8.ofNat (b.toNat + 32) else b

def lowerName (bs : List UInt8) : ByteArray := ⟨(bs.map lowerByte).toArray⟩

/-- The QPACK field section for a response: section prefix, `:status`, a derived
`content-length`, then every response header as a lowercased literal field. -/
def encQpackHeaderBlock (resp : Reactor.Response) : ByteArray :=
  let sectionPrefix := ByteArray.mk #[0x00, 0x00]
  let status := encQpackStatus resp.status
  let clen := encQpackLiteral (String.toUTF8 "content-length")
                ⟨(Reactor.natToDec resp.body.length).toArray⟩
  let hdrs := resp.headers.foldl
    (fun acc h => acc ++ encQpackLiteral (lowerName h.1) ⟨h.2.toArray⟩) ByteArray.empty
  sectionPrefix ++ status ++ clen ++ hdrs

/-- Encode a `Reactor.Response` as the HTTP/3 stream-0 payload: a HEADERS frame
(type `0x01`) carrying the QPACK field section, then a DATA frame (type `0x00`)
carrying the body. -/
def encodeH3Response (resp : Reactor.Response) : ByteArray :=
  let block := encQpackHeaderBlock resp
  let headersFrame := ByteArray.mk #[0x01] ++ QuicServer.encVarint block.size ++ block
  let body : ByteArray := ⟨resp.body.toArray⟩
  let dataFrame := ByteArray.mk #[0x00] ++ QuicServer.encVarint body.size ++ body
  headersFrame ++ dataFrame

/-- The Huffman-capable H3 lane config (the deployed RFC 7541 Huffman decoder). -/
def huffConfig : Reactor.Quic.QuicConfig := ⟨_root_.H3.Qpack.rfc7541Huffman⟩

/-- An empty QPACK/arena store to decode a request field section against. -/
def h3EmptyStore : Arena.Store := { main := #[], sidecar := #[], entries := [] }

/-- The canned `400 Bad Request` for a request the RFC 9114 front end rejects. -/
def malformedH3Resp : Reactor.Response :=
  Reactor.error4xx 400 Reactor.reasonBad Reactor.badBody

/-- Re-frame a decoded request stream's raw QPACK field section and content as a
canonical, grease-free HTTP/3 request stream for the proven dispatcher. -/
def reframeRequest (enc body : List UInt8) : ByteArray :=
  let hdr := ByteArray.mk #[0x01] ++ QuicServer.encVarint enc.length ++ ⟨enc.toArray⟩
  let dat := ByteArray.mk #[0x00] ++ QuicServer.encVarint body.length ++ ⟨body.toArray⟩
  hdr ++ dat

/-- **The H3 request front end** (RFC 9114 §4.1 + §4.3.1): run the raw
request-stream bytes through the proven `readRequestStream`, decode the field
section, apply the §4.3.1 gate, then dispatch through the SAME proven
`datagramServe` + `deployStagesFull2` fold the TCP dataplane runs. -/
def serveH3Resp (h3 : ByteArray) : Reactor.Response × List UInt8 :=
  match _root_.H3.readRequestStream h3.toList with
  | .incomplete => (malformedH3Resp, [])
  | .malformed => (malformedH3Resp, [])
  | .request enc body _trailers =>
    match _root_.H3.Qpack.decodeFieldSection _root_.H3.Qpack.rfc7541Huffman h3EmptyStore enc with
    | .error _ => (malformedH3Resp, [])
    | .ok d =>
      if _root_.H3.validRequestHead d.store d.pseudo d.fields then
        let method := (d.pseudo.method.map (_root_.H3.resolvedBytes d.store)).getD []
        let canonical := reframeRequest enc body
        let ev := Reactor.Quic.DatagramEvent.recvDatagram .appData 0
                    (Reactor.Quic.Payload.stream 0 canonical.toList)
        let subs := (Reactor.QuicIngress.datagramServe huffConfig
          Reactor.QuicIngress.demoState ev).2
        let feed := canonical.toList
        let resp := match Reactor.Deploy.dispatchReqOf subs with
          | some req => Reactor.Deploy.deployRespFull2Of feed req
          | none => Reactor.Ingress.ingressResp subs feed
        (resp, method)
      else (malformedH3Resp, [])

/-- Serve one reassembled H3 request-stream through the proven QUIC/H3 front end
and re-frame the response as the HTTP/3 stream payload (HEADERS ‖ DATA). HEAD
suppresses the body (proven `H3.headSuppressedBody`). -/
def serveH3Multi (h3 : ByteArray) : ByteArray :=
  let (resp, method) := serveH3Resp h3
  encodeH3Response { resp with body := _root_.H3.headSuppressedBody method resp.body }

/-! ## (4b) Host-owned `ServerState` (de)serialization — the pure seam threads the
connection table + 1-RTT keys across datagrams as an opaque blob the host carries.

The host owns the QUIC connection state (matching the dataplane's pure-seam
architecture: the proven core stays a pure `ByteArray → ByteArray`, the mutable
loop state lives in the host). Each datagram call receives the prior serialized
`QuicServer.ServerState` and returns the advanced one; the host stores it verbatim
and replays it on the next datagram — so the handshake-derived 1-RTT keys inside
each `QuicServer.Conn` persist across datagrams, keyed by connection ID inside the
proven `stepServer`-style router. This encoding is host-private (never parsed by
the host); its only contract is round-trip fidelity -- PROVEN by `decState_encState`
below for every well-formed state (the `#guard` sample below smoke-tests it too). -/

/-- 8-byte big-endian length/count. -/
def be64 (n : Nat) : ByteArray :=
  ⟨((List.range 8).map (fun p => UInt8.ofNat (n >>> (8 * (7 - p))))).toArray⟩

def putBA (b : ByteArray) : ByteArray := be64 b.size ++ b
def putBytesL (l : List UInt8) : ByteArray := be64 l.length ++ ⟨l.toArray⟩
def putBool (x : Bool) : ByteArray := ByteArray.mk #[if x then 1 else 0]
def putListB {α} (f : α → ByteArray) (xs : List α) : ByteArray :=
  xs.foldl (fun acc x => acc ++ f x) (be64 xs.length)
def putOptB {α} (f : α → ByteArray) : Option α → ByteArray
  | none => putBool false
  | some x => putBool true ++ f x
def putPK (k : QuicServer.PacketKeys) : ByteArray := putBA k.key ++ putBA k.iv ++ putBA k.hp
def putPhase : QuicServer.Phase → ByteArray
  | .awaitFinished => ByteArray.mk #[0]
  | .established => ByteArray.mk #[1]
  | .closed => ByteArray.mk #[2]
  | .failed => ByteArray.mk #[3]

def putConn (c : QuicServer.Conn) : ByteArray :=
  putBA c.odcid ++ putBA c.cscid ++ putListB putBA c.myCids ++ putBA c.dhe
    ++ putPK c.srvInitial ++ putPK c.srvHs ++ putPK c.cliHs
    ++ putOptB putPK c.srvApp ++ putOptB putPK c.cliApp
    ++ putBA c.sApSec ++ putBA c.cApSec ++ putBool c.keyPhase
    ++ putBA c.cHsSecret ++ putBA c.thSF
    ++ be64 c.initPn ++ be64 c.hsPn ++ be64 c.appPn
    ++ putListB be64 c.recvHs ++ putListB be64 c.recvApp
    ++ putBool c.spin ++ be64 c.spinPn ++ putPhase c.phase
    ++ putListB (fun s => be64 s.1 ++ putBytesL s.2.1 ++ putBool s.2.2) c.streams
    ++ be64 c.chalCtr ++ putOptB putBytesL c.lastChallenge ++ putBool c.pathValidated

def putPending (p : QuicServer.Pending) : ByteArray :=
  putBA p.odcid ++ putBA p.origDcid ++ putBA p.cscid
    ++ putListB (fun s => be64 s.1 ++ putBytesL s.2) p.segs
    ++ putListB be64 p.recvPns ++ be64 p.sendPn

def encState (st : QuicServer.ServerState) : ByteArray :=
  putListB putConn st.conns ++ putListB putPending st.pending

/-- Byte-consuming decoder monad: state is the remaining input, failure is `none`. -/
abbrev DecM := StateT (List UInt8) Option

def getU8 : DecM UInt8 := fun s => match s with | b :: r => some (b, r) | [] => none
def getBytesN (n : Nat) : DecM (List UInt8) := fun s =>
  if s.length < n then none else some (s.take n, s.drop n)
def getBE64 : DecM Nat := do
  let bs ← getBytesN 8
  pure (bs.foldl (fun a b => a * 256 + b.toNat) 0)
def getBA : DecM ByteArray := do let n ← getBE64; let l ← getBytesN n; pure ⟨l.toArray⟩
def getBytesL : DecM (List UInt8) := do let n ← getBE64; getBytesN n
def getBool : DecM Bool := do let b ← getU8; pure (b != 0)
def getListD {α} (d : DecM α) : DecM (List α) := do
  let n ← getBE64; (List.range n).mapM (fun _ => d)
def getOptD {α} (d : DecM α) : DecM (Option α) := do
  let t ← getBool; if t then (do let x ← d; pure (some x)) else pure none
def getPK : DecM QuicServer.PacketKeys := do
  let key ← getBA; let iv ← getBA; let hp ← getBA
  pure { key := key, iv := iv, hp := hp }
def getPhase : DecM QuicServer.Phase := do
  let b ← getU8
  pure (match b with
    | 0 => .awaitFinished | 1 => .established | 2 => .closed | _ => .failed)

/-! The `Conn` decode is split into three field-group decoders rather than one
26-binder `do`-block. This is not cosmetic: elaboration of a `do`-chain in
`DecM` (= `StateT (List UInt8) Option`) costs memory EXPONENTIALLY in the number
of binders in a single block — measured on this module at ~2.7x per added
binder (4 binders 0.34 GB / 0.5 s; 8: 0.38 GB / 0.9 s; 12: 0.97 GB / 45 s; 16:
does not fit in 8 GB; the 26-binder original does not fit in 24 GB and was still
climbing past 38 GB when given 64 GB). Keeping each group under the knee makes
the module compile in 0.54 GB / ~4 s. The decode ORDER — which is the wire
format — is preserved exactly across the three groups, and the fields are
reassembled into the same `Conn` literal, so the decoded value is unchanged. -/

/-- `Conn` fields 1-9, in wire order. -/
def getConnA : DecM (ByteArray × ByteArray × List ByteArray × ByteArray ×
    QuicServer.PacketKeys × QuicServer.PacketKeys × QuicServer.PacketKeys ×
    Option QuicServer.PacketKeys × Option QuicServer.PacketKeys) := do
  let odcid ← getBA; let cscid ← getBA; let myCids ← getListD getBA; let dhe ← getBA
  let srvInitial ← getPK; let srvHs ← getPK; let cliHs ← getPK
  let srvApp ← getOptD getPK; let cliApp ← getOptD getPK
  pure (odcid, cscid, myCids, dhe, srvInitial, srvHs, cliHs, srvApp, cliApp)

/-- `Conn` fields 10-19, in wire order. -/
def getConnB : DecM (ByteArray × ByteArray × Bool × ByteArray × ByteArray ×
    Nat × Nat × Nat × List Nat × List Nat) := do
  let sApSec ← getBA; let cApSec ← getBA; let keyPhase ← getBool
  let cHsSecret ← getBA; let thSF ← getBA
  let initPn ← getBE64; let hsPn ← getBE64; let appPn ← getBE64
  let recvHs ← getListD getBE64; let recvApp ← getListD getBE64
  pure (sApSec, cApSec, keyPhase, cHsSecret, thSF, initPn, hsPn, appPn, recvHs, recvApp)

/-- `Conn` fields 20-26, in wire order. -/
def getConnC : DecM (Bool × Nat × QuicServer.Phase × List (Nat × List UInt8 × Bool) ×
    Nat × Option (List UInt8) × Bool) := do
  let spin ← getBool; let spinPn ← getBE64; let phase ← getPhase
  let streams ← getListD (do let sid ← getBE64; let buf ← getBytesL; let r ← getBool; pure (sid, buf, r))
  let chalCtr ← getBE64; let lastChallenge ← getOptD getBytesL; let pathValidated ← getBool
  pure (spin, spinPn, phase, streams, chalCtr, lastChallenge, pathValidated)

def getConn : DecM QuicServer.Conn := do
  let (odcid, cscid, myCids, dhe, srvInitial, srvHs, cliHs, srvApp, cliApp) ← getConnA
  let (sApSec, cApSec, keyPhase, cHsSecret, thSF, initPn, hsPn, appPn, recvHs, recvApp) ← getConnB
  let (spin, spinPn, phase, streams, chalCtr, lastChallenge, pathValidated) ← getConnC
  pure { odcid := odcid, cscid := cscid, myCids := myCids, dhe := dhe,
         srvInitial := srvInitial, srvHs := srvHs, cliHs := cliHs,
         srvApp := srvApp, cliApp := cliApp, sApSec := sApSec, cApSec := cApSec,
         keyPhase := keyPhase, cHsSecret := cHsSecret, thSF := thSF,
         initPn := initPn, hsPn := hsPn, appPn := appPn, recvHs := recvHs, recvApp := recvApp,
         spin := spin, spinPn := spinPn, phase := phase, streams := streams,
         chalCtr := chalCtr, lastChallenge := lastChallenge, pathValidated := pathValidated }

def getPending : DecM QuicServer.Pending := do
  let odcid ← getBA; let origDcid ← getBA; let cscid ← getBA
  let segs ← getListD (do let off ← getBE64; let d ← getBytesL; pure (off, d))
  let recvPns ← getListD getBE64; let sendPn ← getBE64
  pure { odcid := odcid, origDcid := origDcid, cscid := cscid,
         segs := segs, recvPns := recvPns, sendPn := sendPn }

def getState : DecM QuicServer.ServerState := do
  let conns ← getListD getConn; let pending ← getListD getPending
  pure { conns := conns, pending := pending }

/-- Decode a serialized `ServerState`; empty/short input decodes to the empty
state (the host's first-datagram sentinel). -/
def decState (bs : List UInt8) : QuicServer.ServerState :=
  match getState bs with
  | some (st, _) => st
  | none => QuicServer.ServerState.empty

/-- Round-trip fidelity of the `ServerState` codec on a fully-populated state
(one established `Conn` with both key generations installed, plus one pending
ClientHello reassembly): `decode ∘ encode` re-encodes byte-identically. -/
def sampleBA : ByteArray := ⟨#[0x11, 0x22, 0x33]⟩
def samplePK : QuicServer.PacketKeys := { key := ⟨#[1,2,3]⟩, iv := ⟨#[4,5]⟩, hp := ⟨#[6]⟩ }
def sampleConn : QuicServer.Conn :=
  { odcid := sampleBA, cscid := ⟨#[9,9]⟩, myCids := [⟨#[1]⟩, ⟨#[2,2]⟩], dhe := ⟨#[7,7,7]⟩,
    srvInitial := samplePK, srvHs := samplePK, cliHs := samplePK,
    srvApp := some samplePK, cliApp := some samplePK,
    sApSec := ⟨#[8]⟩, cApSec := ⟨#[8,8]⟩, keyPhase := true,
    cHsSecret := ⟨#[3,3]⟩, thSF := ⟨#[4,4,4]⟩,
    initPn := 5, hsPn := 300, appPn := 70000, recvHs := [3,2,1], recvApp := [9,0],
    spin := true, spinPn := 4, phase := .established,
    streams := [(0, [72, 73], true), (4, [], false)],
    chalCtr := 2, lastChallenge := some [1,2,3], pathValidated := true }
def samplePending : QuicServer.Pending :=
  { odcid := ⟨#[1,1]⟩, origDcid := ⟨#[2,2]⟩, cscid := ⟨#[3,3]⟩,
    segs := [(0, [1,2]), (2, [3])], recvPns := [1,0], sendPn := 1 }
def sampleState : QuicServer.ServerState := { conns := [sampleConn], pending := [samplePending] }
/- Round-trip SANITY CHECK on one fully-populated sample: decoding the encoding
re-encodes byte-identically. This is a TEST, honestly labeled -- it checks ONE sample,
it is not assurance.

It was a `native_decide` theorem. The reason to prefer `#guard` here is ONE thing only:
`native_decide` puts `Lean.ofReduceBool` in the trusted base (it is checked by the
COMPILER, not the kernel), whereas `#guard` is a command and adds NO axiom.

What is NOT a reason, and was wrongly claimed in an earlier version of this comment:
`#guard` is NOT kernel-evaluated either -- it is `evalExpr` (Lean/Elab/Tactic/Guard.lean),
i.e. the same compiler/interpreter path `native_decide` uses. Measured: the two cost the
SAME here (533MB). An earlier claim that this swap fixed a 61.4G build runaway was FALSE;
that runaway has another (still uncharacterized) cause -- most likely parallel `lean`
processes summing box-wide, which the build cgroup cap now contains regardless.

The GENERAL round-trip theorem `decState (encState s) = s` for all well-formed `s`
is PROVEN below as `decState_encState` (axioms subset {propext, Classical.choice,
Quot.sound}); this `#guard` remains only as a fast one-sample smoke test. -/
#guard (encState (decState (encState sampleState).toList)).toList
         == (encState sampleState).toList

/-! ## (4b-rt) General round-trip fidelity of the `ServerState` codec

The `#guard` above is one sample. The real obligation is that `decState` inverts
`encState` for EVERY well-formed state. "Well-formed" is exactly the honest
precondition the 8-byte big-endian framing needs: every length/count/packet-number
that goes through `be64` must fit in 64 bits (`< 2 ^ 64`). Sizes above that would be
truncated by `be64` and could not round-trip — so the bound is genuinely necessary,
not decorative. Nothing else is required.

The proof is a parser/serializer agreement, threaded through the leftover input
(`∀ rest, get (put x ++ rest) = some (x, rest)`), by structural induction over the
lists (`conns`, `pending`, and the nested `myCids`/`recvHs`/`recvApp`/`streams`/
`segs`/`recvPns`). Pure kernel: axioms ⊆ {propext, Classical.choice, Quot.sound} —
no `native_decide`, no `Lean.ofReduceBool`, no `sorry`. -/

/-- `ByteArray.toList` is well-founded-recursive and opaque to the kernel; this
rewrites it to the structural `data.toList`, which the kernel reduces. -/
private theorem ba_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ (n i : Nat) (r : List UInt8),
      bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro n
    induction n with
    | zero =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hnlt : ¬ i < bs.size := by omega
      simp only [hnlt, if_false]
      have hdrop : bs.data.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]
        have : bs.data.size = bs.size := rfl
        omega
      rw [hdrop, List.append_nil]
    | succ n ih =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hlt : i < bs.size := by omega
      simp only [hlt, if_true]
      rw [ih (i+1) (bs.get! i :: r) (by omega)]
      have hidx : i < bs.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hsz : i < bs.data.size := by rw [← Array.length_toList]; exact hidx
      have hget : bs.get! i = bs.data.toList[i]'hidx := by
        rw [show bs.get! i = bs.data[i]! from rfl,
            getElem!_pos bs.data i hsz, ← Array.getElem_toList hsz]
      rw [List.drop_eq_getElem_cons hidx, List.reverse_cons, hget, List.append_assoc]
      rfl
  have h := key bs.size 0 [] (by omega)
  rw [ByteArray.toList]
  simpa using h

private theorem ba_data_size (bs : ByteArray) : bs.data.size = bs.size := rfl

private theorem mk_toArray_toList (l : List UInt8) : (ByteArray.mk l.toArray).toList = l := by
  rw [ba_toList_eq]

private theorem BA_append_toList (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  rw [ba_toList_eq (a ++ b), ba_toList_eq a, ba_toList_eq b]
  exact ByteArray.toList_data_append'

private theorem ba_length (b : ByteArray) : b.toList.length = b.size := by
  rw [ba_toList_eq, Array.length_toList, ba_data_size]

private theorem mk_toList_toArray (b : ByteArray) : ByteArray.mk b.toList.toArray = b := by
  rw [ba_toList_eq, Array.toArray_toList]

/-! ### The 8-byte big-endian codec round-trip -/

private theorem be64_toList (n : Nat) :
    (be64 n).toList = (List.range 8).map (fun p => UInt8.ofNat (n >>> (8 * (7 - p)))) := by
  rw [show be64 n = ByteArray.mk ((List.range 8).map (fun p => UInt8.ofNat (n >>> (8 * (7 - p))))).toArray from rfl,
      mk_toArray_toList]

private theorem be64_length (n : Nat) : (be64 n).toList.length = 8 := by
  rw [be64_toList]; simp

private theorem foldBE64_be64 (n : Nat) (h : n < 2^64) :
    ((be64 n).toList).foldl (fun a b => a * 256 + b.toNat) 0 = n := by
  rw [be64_toList, show List.range 8 = [0,1,2,3,4,5,6,7] from by decide]
  simp only [List.map, List.foldl, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  omega

/-! ### Decoder-monad primitives (`DecM = StateT (List UInt8) Option`) -/

private theorem getBytesN_append (l rest : List UInt8) (n : Nat) (h : l.length = n) :
    getBytesN n (l ++ rest) = some (l, rest) := by
  unfold getBytesN
  have h1 : ¬ (l ++ rest).length < n := by rw [List.length_append, h]; omega
  simp only [h1, if_false]
  rw [← h, List.take_left, List.drop_left]

private theorem getBE64_roundtrip (n : Nat) (h : n < 2^64) (rest : List UInt8) :
    getBE64 ((be64 n).toList ++ rest) = some (n, rest) := by
  unfold getBE64
  simp only [bind, StateT.bind, getBytesN_append (be64 n).toList rest 8 (be64_length n),
             Option.bind, pure, StateT.pure]
  rw [foldBE64_be64 n h]

private theorem getU8_cons (b : UInt8) (r : List UInt8) : getU8 (b :: r) = some (b, r) := rfl

private theorem getBA_roundtrip (b : ByteArray) (h : b.size < 2^64) (rest : List UInt8) :
    getBA ((putBA b).toList ++ rest) = some (b, rest) := by
  have e : (putBA b).toList ++ rest = (be64 b.size).toList ++ (b.toList ++ rest) := by
    rw [show putBA b = be64 b.size ++ b from rfl, BA_append_toList, List.append_assoc]
  rw [e]
  unfold getBA
  simp only [bind, StateT.bind, getBE64_roundtrip b.size h, Option.bind,
             getBytesN_append b.toList rest b.size (ba_length b), pure, StateT.pure]
  rw [mk_toList_toArray]

private theorem getBytesL_roundtrip (l rest : List UInt8) (h : l.length < 2^64) :
    getBytesL ((putBytesL l).toList ++ rest) = some (l, rest) := by
  have e : (putBytesL l).toList ++ rest = (be64 l.length).toList ++ (l ++ rest) := by
    rw [show putBytesL l = be64 l.length ++ ByteArray.mk l.toArray from rfl]
    simp only [BA_append_toList, mk_toArray_toList, List.append_assoc]
  rw [e]
  unfold getBytesL
  simp only [bind, StateT.bind, getBE64_roundtrip l.length h, Option.bind,
             getBytesN_append l rest l.length rfl, pure, StateT.pure]

private theorem putBool_toList (x : Bool) : (putBool x).toList = [if x then 1 else 0] := by
  rw [show putBool x = ByteArray.mk #[if x then 1 else 0] from rfl, ba_toList_eq]

private theorem getBool_roundtrip (x : Bool) (rest : List UInt8) :
    getBool ((putBool x).toList ++ rest) = some (x, rest) := by
  rw [putBool_toList]
  unfold getBool
  cases x <;>
    simp only [bind, StateT.bind, List.cons_append, List.nil_append, getU8_cons, Option.bind,
               pure, StateT.pure, if_true, if_false] <;> rfl

private theorem getPhase_roundtrip (p : QuicServer.Phase) (rest : List UInt8) :
    getPhase ((putPhase p).toList ++ rest) = some (p, rest) := by
  cases p <;>
  · simp only [putPhase]
    rw [ba_toList_eq]
    unfold getPhase
    simp only [List.cons_append, List.nil_append, bind, StateT.bind, getU8_cons, Option.bind,
               pure, StateT.pure]
    try rfl

private theorem getPK_roundtrip (k : QuicServer.PacketKeys)
    (h1 : k.key.size < 2^64) (h2 : k.iv.size < 2^64) (h3 : k.hp.size < 2^64)
    (rest : List UInt8) :
    getPK ((putPK k).toList ++ rest) = some (k, rest) := by
  have e : (putPK k).toList ++ rest
      = (putBA k.key).toList ++ ((putBA k.iv).toList ++ ((putBA k.hp).toList ++ rest)) := by
    rw [show putPK k = putBA k.key ++ putBA k.iv ++ putBA k.hp from rfl,
        BA_append_toList, BA_append_toList, List.append_assoc, List.append_assoc]
  rw [e]
  unfold getPK
  simp only [bind, StateT.bind, getBA_roundtrip k.key h1, Option.bind,
             getBA_roundtrip k.iv h2, getBA_roundtrip k.hp h3, pure, StateT.pure]

/-! ### List/`Option` combinator round-trips -/

private theorem foldl_putB_toList {α} (f : α → ByteArray) :
    ∀ (xs : List α) (init : ByteArray),
    (xs.foldl (fun acc x => acc ++ f x) init).toList
      = init.toList ++ xs.flatMap (fun x => (f x).toList)
  | [], init => by simp
  | x :: xs, init => by
    rw [List.foldl_cons, foldl_putB_toList f xs (init ++ f x), BA_append_toList,
        List.flatMap_cons, List.append_assoc]

private theorem putListB_toList {α} (f : α → ByteArray) (xs : List α) :
    (putListB f xs).toList
      = (be64 xs.length).toList ++ xs.flatMap (fun x => (f x).toList) := by
  rw [show putListB f xs = xs.foldl (fun acc x => acc ++ f x) (be64 xs.length) from rfl,
      foldl_putB_toList]

private theorem mapM_map_const {α β γ} (g : DecM β) (h : γ → α) :
    ∀ (l : List γ), (l.map h).mapM (fun _ => g) = l.mapM (fun _ => g)
  | [] => rfl
  | a :: t => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map_const g h t]

private theorem mapM_range_flat {α} (g : DecM α) (f : α → ByteArray) (P : α → Prop)
    (Hg : ∀ x, P x → ∀ rest, g ((f x).toList ++ rest) = some (x, rest)) :
    ∀ (xs : List α), (∀ x ∈ xs, P x) → ∀ (rest : List UInt8),
      (List.range xs.length).mapM (fun _ => g)
          (xs.flatMap (fun x => (f x).toList) ++ rest) = some (xs, rest)
  | [], _, rest => rfl
  | x :: xs, hxs, rest => by
    have hx : P x := hxs x (List.mem_cons_self)
    have hxs' : ∀ y ∈ xs, P y := fun y hy => hxs y (List.mem_cons_of_mem x hy)
    rw [show (x :: xs).length = xs.length + 1 from rfl, List.range_succ_eq_map,
        List.mapM_cons, mapM_map_const g Nat.succ,
        List.flatMap_cons, List.append_assoc]
    simp only [bind, StateT.bind, Hg x hx (xs.flatMap (fun x => (f x).toList) ++ rest),
               Option.bind, mapM_range_flat g f P Hg xs hxs' rest, pure, StateT.pure]

private theorem getListD_roundtrip {α} (g : DecM α) (f : α → ByteArray) (P : α → Prop)
    (Hg : ∀ x, P x → ∀ rest, g ((f x).toList ++ rest) = some (x, rest))
    (xs : List α) (hxs : ∀ x ∈ xs, P x) (hlen : xs.length < 2^64) (rest : List UInt8) :
    getListD g ((putListB f xs).toList ++ rest) = some (xs, rest) := by
  rw [putListB_toList, List.append_assoc]
  unfold getListD
  simp only [bind, StateT.bind, getBE64_roundtrip xs.length hlen, Option.bind]
  exact mapM_range_flat g f P Hg xs hxs rest

private theorem getOptD_roundtrip {α} (d : DecM α) (f : α → ByteArray) (P : α → Prop)
    (Hd : ∀ x, P x → ∀ rest, d ((f x).toList ++ rest) = some (x, rest))
    (o : Option α) (ho : ∀ x, o = some x → P x) (rest : List UInt8) :
    getOptD d ((putOptB f o).toList ++ rest) = some (o, rest) := by
  cases o with
  | none =>
    rw [show putOptB f none = putBool false from rfl]
    unfold getOptD
    simp only [bind, StateT.bind, getBool_roundtrip false, Option.bind, pure, StateT.pure]
    rfl
  | some x =>
    have hx : P x := ho x rfl
    rw [show putOptB f (some x) = putBool true ++ f x from rfl, BA_append_toList,
        List.append_assoc]
    unfold getOptD
    simp only [bind, StateT.bind, getBool_roundtrip true, Option.bind, if_true,
               Hd x hx rest, pure, StateT.pure]

/-! ### Per-entry round-trips for the inline `streams` and `segs` element codecs -/

private theorem getStreamEntry_roundtrip (s : Nat × List UInt8 × Bool)
    (h1 : s.1 < 2^64) (h2 : s.2.1.length < 2^64) (rest : List UInt8) :
    (do let sid ← getBE64; let buf ← getBytesL; let r ← getBool; pure (sid, buf, r))
        ((be64 s.1 ++ putBytesL s.2.1 ++ putBool s.2.2).toList ++ rest) = some (s, rest) := by
  rw [BA_append_toList, BA_append_toList, List.append_assoc, List.append_assoc]
  simp only [bind, StateT.bind, getBE64_roundtrip s.1 h1, Option.bind,
             getBytesL_roundtrip s.2.1 ((putBool s.2.2).toList ++ rest) h2,
             getBool_roundtrip s.2.2, pure, StateT.pure]

private theorem getSegEntry_roundtrip (s : Nat × List UInt8)
    (h1 : s.1 < 2^64) (h2 : s.2.length < 2^64) (rest : List UInt8) :
    (do let off ← getBE64; let d ← getBytesL; pure (off, d))
        ((be64 s.1 ++ putBytesL s.2).toList ++ rest) = some (s, rest) := by
  rw [BA_append_toList, List.append_assoc]
  simp only [bind, StateT.bind, getBE64_roundtrip s.1 h1, Option.bind,
             getBytesL_roundtrip s.2 rest h2, pure, StateT.pure]

/-! ### Well-formedness: every `be64`-framed field fits in 64 bits -/

/-- A `PacketKeys` is well-formed when each key material blob's size is `< 2 ^ 64`. -/
structure PacketKeysWF (k : QuicServer.PacketKeys) : Prop where
  key : k.key.size < 2^64
  iv : k.iv.size < 2^64
  hp : k.hp.size < 2^64

/-- A `Conn` is well-formed when every `be64`-encoded size, count, and packet number
inside it is `< 2 ^ 64` (the exact precondition the 8-byte framing needs). -/
structure ConnWF (c : QuicServer.Conn) : Prop where
  odcid : c.odcid.size < 2^64
  cscid : c.cscid.size < 2^64
  myCidsLen : c.myCids.length < 2^64
  myCidsAll : ∀ x ∈ c.myCids, x.size < 2^64
  dhe : c.dhe.size < 2^64
  srvInitial : PacketKeysWF c.srvInitial
  srvHs : PacketKeysWF c.srvHs
  cliHs : PacketKeysWF c.cliHs
  srvApp : ∀ k, c.srvApp = some k → PacketKeysWF k
  cliApp : ∀ k, c.cliApp = some k → PacketKeysWF k
  sApSec : c.sApSec.size < 2^64
  cApSec : c.cApSec.size < 2^64
  cHsSecret : c.cHsSecret.size < 2^64
  thSF : c.thSF.size < 2^64
  initPn : c.initPn < 2^64
  hsPn : c.hsPn < 2^64
  appPn : c.appPn < 2^64
  recvHsLen : c.recvHs.length < 2^64
  recvHsAll : ∀ x ∈ c.recvHs, x < 2^64
  recvAppLen : c.recvApp.length < 2^64
  recvAppAll : ∀ x ∈ c.recvApp, x < 2^64
  spinPn : c.spinPn < 2^64
  streamsLen : c.streams.length < 2^64
  streamsAll : ∀ s ∈ c.streams, s.1 < 2^64 ∧ s.2.1.length < 2^64
  chalCtr : c.chalCtr < 2^64
  lastChallenge : ∀ l, c.lastChallenge = some l → l.length < 2^64

/-- A `Pending` reassembly slot is well-formed when every `be64`-encoded size, count,
and packet number inside it is `< 2 ^ 64`. -/
structure PendingWF (p : QuicServer.Pending) : Prop where
  odcid : p.odcid.size < 2^64
  origDcid : p.origDcid.size < 2^64
  cscid : p.cscid.size < 2^64
  segsLen : p.segs.length < 2^64
  segsAll : ∀ s ∈ p.segs, s.1 < 2^64 ∧ s.2.length < 2^64
  recvPnsLen : p.recvPns.length < 2^64
  recvPnsAll : ∀ x ∈ p.recvPns, x < 2^64
  sendPn : p.sendPn < 2^64

/-- A `ServerState` is well-formed when its connection/pending lists are `< 2 ^ 64`
long and every entry is well-formed. -/
structure ServerStateWF (st : QuicServer.ServerState) : Prop where
  connsLen : st.conns.length < 2^64
  connsAll : ∀ c ∈ st.conns, ConnWF c
  pendingLen : st.pending.length < 2^64
  pendingAll : ∀ p ∈ st.pending, PendingWF p

/-! ### Structure round-trips -/

private theorem getConn_roundtrip (c : QuicServer.Conn) (h : ConnWF c) (rest : List UInt8) :
    getConn ((putConn c).toList ++ rest) = some (c, rest) := by
  simp only [putConn, BA_append_toList, List.append_assoc]
  unfold getConn getConnA getConnB getConnC
  simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
    getBA_roundtrip c.odcid h.odcid,
    getBA_roundtrip c.cscid h.cscid,
    getListD_roundtrip getBA putBA (fun b => b.size < 2^64)
      (fun b hb r => getBA_roundtrip b hb r) c.myCids h.myCidsAll h.myCidsLen,
    getBA_roundtrip c.dhe h.dhe,
    getPK_roundtrip c.srvInitial h.srvInitial.key h.srvInitial.iv h.srvInitial.hp,
    getPK_roundtrip c.srvHs h.srvHs.key h.srvHs.iv h.srvHs.hp,
    getPK_roundtrip c.cliHs h.cliHs.key h.cliHs.iv h.cliHs.hp,
    getOptD_roundtrip getPK putPK PacketKeysWF
      (fun k hk r => getPK_roundtrip k hk.key hk.iv hk.hp r) c.srvApp h.srvApp,
    getOptD_roundtrip getPK putPK PacketKeysWF
      (fun k hk r => getPK_roundtrip k hk.key hk.iv hk.hp r) c.cliApp h.cliApp,
    getBA_roundtrip c.sApSec h.sApSec,
    getBA_roundtrip c.cApSec h.cApSec,
    getBool_roundtrip c.keyPhase,
    getBA_roundtrip c.cHsSecret h.cHsSecret,
    getBA_roundtrip c.thSF h.thSF,
    getBE64_roundtrip c.initPn h.initPn,
    getBE64_roundtrip c.hsPn h.hsPn,
    getBE64_roundtrip c.appPn h.appPn,
    getListD_roundtrip getBE64 be64 (fun n => n < 2^64)
      (fun n hn r => getBE64_roundtrip n hn r) c.recvHs h.recvHsAll h.recvHsLen,
    getListD_roundtrip getBE64 be64 (fun n => n < 2^64)
      (fun n hn r => getBE64_roundtrip n hn r) c.recvApp h.recvAppAll h.recvAppLen,
    getBool_roundtrip c.spin,
    getBE64_roundtrip c.spinPn h.spinPn,
    getPhase_roundtrip c.phase,
    getListD_roundtrip
      (StateT.bind getBE64 fun sid => StateT.bind getBytesL fun buf =>
        StateT.bind getBool fun r => StateT.pure (sid, buf, r))
      (fun s => be64 s.1 ++ putBytesL s.2.1 ++ putBool s.2.2)
      (fun s => s.1 < 2^64 ∧ s.2.1.length < 2^64)
      (fun s hs r => getStreamEntry_roundtrip s hs.1 hs.2 r) c.streams
      h.streamsAll h.streamsLen,
    getBE64_roundtrip c.chalCtr h.chalCtr,
    getOptD_roundtrip getBytesL putBytesL (fun l => l.length < 2^64)
      (fun l hl r => getBytesL_roundtrip l r hl) c.lastChallenge h.lastChallenge,
    getBool_roundtrip c.pathValidated]

private theorem getPending_roundtrip (p : QuicServer.Pending) (h : PendingWF p) (rest : List UInt8) :
    getPending ((putPending p).toList ++ rest) = some (p, rest) := by
  simp only [putPending, BA_append_toList, List.append_assoc]
  unfold getPending
  simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
    getBA_roundtrip p.odcid h.odcid,
    getBA_roundtrip p.origDcid h.origDcid,
    getBA_roundtrip p.cscid h.cscid,
    getListD_roundtrip
      (StateT.bind getBE64 fun off => StateT.bind getBytesL fun d => StateT.pure (off, d))
      (fun s => be64 s.1 ++ putBytesL s.2)
      (fun s => s.1 < 2^64 ∧ s.2.length < 2^64)
      (fun s hs r => getSegEntry_roundtrip s hs.1 hs.2 r) p.segs h.segsAll h.segsLen,
    getListD_roundtrip getBE64 be64 (fun n => n < 2^64)
      (fun n hn r => getBE64_roundtrip n hn r) p.recvPns h.recvPnsAll h.recvPnsLen,
    getBE64_roundtrip p.sendPn h.sendPn]

private theorem getState_roundtrip (st : QuicServer.ServerState) (h : ServerStateWF st)
    (rest : List UInt8) :
    getState ((encState st).toList ++ rest) = some (st, rest) := by
  rw [show encState st = putListB putConn st.conns ++ putListB putPending st.pending from rfl,
      BA_append_toList, List.append_assoc]
  unfold getState
  simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
    getListD_roundtrip getConn putConn ConnWF
      (fun c hc r => getConn_roundtrip c hc r) st.conns h.connsAll h.connsLen,
    getListD_roundtrip getPending putPending PendingWF
      (fun p hp r => getPending_roundtrip p hp r) st.pending h.pendingAll h.pendingLen]

/-- **General round-trip fidelity of the host-owned `ServerState` codec.** For EVERY
well-formed state, decoding its encoding recovers the same state — the real
obligation the one-sample `#guard` above only smoke-tested. Structural induction over
the connection/pending lists and their nested list fields; pure kernel (axioms ⊆
{propext, Classical.choice, Quot.sound}). -/
theorem decState_encState (st : QuicServer.ServerState) (h : ServerStateWF st) :
    decState (encState st).toList = st := by
  unfold decState
  rw [show (encState st).toList = (encState st).toList ++ [] from (List.append_nil _).symm,
      getState_roundtrip st h []]


/-- The precondition is inhabited (so `decState_encState` is not vacuous): the
fully-populated sample — an established `Conn` with both key generations installed
plus a pending ClientHello reassembly — is well-formed. -/
theorem sampleState_wf : ServerStateWF sampleState := by
  refine ⟨by decide, ?_, by decide, ?_⟩
  · intro c hc
    simp only [sampleState, List.mem_singleton] at hc
    subst hc
    exact {
      odcid := by decide, cscid := by decide, myCidsLen := by decide,
      myCidsAll := by decide, dhe := by decide,
      srvInitial := ⟨by decide, by decide, by decide⟩,
      srvHs := ⟨by decide, by decide, by decide⟩,
      cliHs := ⟨by decide, by decide, by decide⟩,
      srvApp := by intro k hk; simp only [sampleConn, Option.some.injEq] at hk; subst hk; exact ⟨by decide, by decide, by decide⟩,
      cliApp := by intro k hk; simp only [sampleConn, Option.some.injEq] at hk; subst hk; exact ⟨by decide, by decide, by decide⟩,
      sApSec := by decide, cApSec := by decide, cHsSecret := by decide, thSF := by decide,
      initPn := by decide, hsPn := by decide, appPn := by decide,
      recvHsLen := by decide, recvHsAll := by decide,
      recvAppLen := by decide, recvAppAll := by decide,
      spinPn := by decide, streamsLen := by decide, streamsAll := by decide,
      chalCtr := by decide,
      lastChallenge := by intro l hl; simp only [sampleConn, Option.some.injEq] at hl; subst hl; decide }
  · intro p hp
    simp only [sampleState, List.mem_singleton] at hp
    subst hp
    exact {
      odcid := by decide, origDcid := by decide, cscid := by decide,
      segsLen := by decide, segsAll := by decide,
      recvPnsLen := by decide, recvPnsAll := by decide, sendPn := by decide }

/-! ## (4c) The stateful datagram step — no-Retry router over the proven per-connection
machine, with the legacy demo fallback preserved.

Reuses the PROVEN `QuicServer` per-connection functions unchanged — `onInitialNew`
(handshake flight + 1-RTT key derivation, keyed by connection ID), `onShort` (a
1-RTT short-header request served via `serveH3Multi` under the handshake-derived
keys), `onHandshake` (client Finished → install 1-RTT), `updateConn`/`ownsCid`
routing — but without the stateless-Retry gate `QuicServer.stepServer` enforces (a
first Initial is served directly, `orig := wire DCID`), so a client that offers the
required hybrid completes in one flight. A bare app-over-Initial STREAM (the from-
scratch prober's probe, no CRYPTO) keeps the legacy stateless `demoServe`. -/
def routeOne (st : QuicServer.ServerState) (pkt : List UInt8) :
    QuicServer.ServerState × Array ByteArray :=
  match pkt[0]? with
  | none => (st, #[])
  | some b0 =>
    match QuicServer.classify b0 with
    | .short =>
      let dcid := (pkt.drop 1).take 8
      QuicServer.updateConn st (fun c => QuicServer.ownsCid c dcid)
        (fun c => QuicServer.onShort serveH3Multi c pkt)
    | .handshake =>
      match QuicServer.locateLong pkt with
      | none => (st, #[])
      | some loc =>
        QuicServer.updateConn st (fun c => QuicServer.ownsCid c loc.dcid.toList)
          (fun c => QuicServer.onHandshake c pkt)
    | .initial =>
      match QuicServer.locateLong pkt with
      | none => (st, #[])
      | some loc =>
        if st.conns.any (fun c => QuicServer.ownsCid c loc.dcid.toList) then (st, #[])
        else
          match QuicServer.decryptInitialFrames pkt loc 0 with
          | none => QuicServer.onInitialNew st pkt loc loc.dcid
          | some (_pn, frs) =>
            if frs.any (fun f => match f with | .crypto _ _ => true | _ => false) then
              QuicServer.onInitialNew st pkt loc loc.dcid
            else
              match frs.findSome? (fun f =>
                match f with
                | .stream sid off _fin d => if off == 0 && !d.isEmpty then some (sid, d) else none
                | _ => none) with
              | some (sid, h3) => (st, #[demoServe loc.dcid sid h3])
              | none => (st, #[])
    | .other => (st, #[])

/-- One received UDP datagram in, `(advanced state, datagrams out)`. Version
negotiation statelessly (RFC 9000 §6.1), then each coalesced packet routed by
`routeOne`. -/
def seamStep (st : QuicServer.ServerState) (dg : ByteArray) :
    QuicServer.ServerState × Array ByteArray :=
  let bs := dg.toList
  match bs[0]? with
  | none => (st, #[])
  | some b0 =>
    let isLong := (b0 &&& 0x80) != 0
    let ver := (bs.drop 1).take 4
    if isLong && ver != [0x00, 0x00, 0x00, 0x01] then
      if ver == [0x00, 0x00, 0x00, 0x00] || bs.length < 1200 then (st, #[])
      else match QuicServer.vnDatagram bs with
        | some vn => (st, #[vn])
        | none => (st, #[])
    else
      (QuicServer.splitPackets 16 bs).foldl
        (fun (acc : QuicServer.ServerState × Array ByteArray) pkt =>
          let (st', outs) := routeOne acc.1 pkt
          (st', acc.2 ++ outs))
        (st, #[])

/-- **`drorb_serve_datagram`.** The stateful QUIC/H3 datagram seam. The host passes
`stateLen(4 BE) ‖ prior serialized ServerState ‖ datagram bytes`; this decodes the
carried state, runs `seamStep` (the proven per-connection machine — handshake
flight, 1-RTT install, H3 serve under the handshake-derived keys, all keyed by
connection ID), and returns `newStateLen(4 BE) ‖ new serialized ServerState ‖
k(2 BE) ‖ (dgLen(4 BE) ‖ datagram)*k`. The host stores the new state verbatim for
the next datagram and sends each of the `k` output datagrams. The seam stays a pure
`ByteArray → ByteArray`; the connection state (and thus the handshake-derived 1-RTT
keys) lives host-side, carried across datagrams. On a datagram the core drops (a
forged/corrupt packet) `k = 0` and the host sends nothing. -/
@[export drorb_serve_datagram]
def drorbServeDatagram (input : ByteArray) : ByteArray :=
  let bs := input.toList
  let stateLen := (bs.take 4).foldl (fun a b => a * 256 + b.toNat) 0
  let stateBytes := (bs.drop 4).take stateLen
  let dg : ByteArray := ⟨((bs.drop 4).drop stateLen).toArray⟩
  let st := decState stateBytes
  let (st', outs) := seamStep st dg
  let newState := encState st'
  let be32 (n : Nat) : ByteArray :=
    ⟨((List.range 4).map (fun p => UInt8.ofNat (n >>> (8 * (3 - p))))).toArray⟩
  let be16 (n : Nat) : ByteArray :=
    ⟨((List.range 2).map (fun p => UInt8.ofNat (n >>> (8 * (1 - p))))).toArray⟩
  let framed := outs.foldl (fun acc d => acc ++ be32 d.size ++ d) ByteArray.empty
  be32 newState.size ++ newState ++ be16 outs.size ++ framed

/-! ## (5) The protocol-upgrade auth gate — the handshake cannot bypass auth -/

/-- **`drorb_upgrade_gate`.** The deployed `/admin` JWT auth gate on a protocol
upgrade REQUEST (RFC 6455 WebSocket Upgrade), so the host-side handshake cannot
bypass authentication. The upgrade request bytes in; if the request targets a
protected `/admin*` path with no/invalid bearer token, the REAL
`Reactor.Deploy.jwtAdminStage` (the same gate the full thirteen-stage fold runs)
refuses it and this returns the serialized `401` bytes the host writes instead of
`101 Switching Protocols`; otherwise it returns NO bytes, meaning the upgrade is
authorized and the host completes the handshake. The request is recovered from the
raw bytes through the same proven `deploySubs` reactor the request path uses. -/
@[export drorb_upgrade_gate]
def drorbUpgradeGate (input : ByteArray) : ByteArray :=
  let c := Reactor.Deploy.ctxOf input.toList
  match Reactor.Deploy.jwtAdminStage.onRequest c with
  | .respond r => ByteArray.mk (Reactor.serialize r).toArray
  | .continue _ => ByteArray.empty

end Multi
end Dataplane
