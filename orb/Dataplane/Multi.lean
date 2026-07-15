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
@[export drorb_serve_ws_frame]
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

/-- **`drorb_serve_datagram`.** A real UDP datagram's bytes in (a QUIC long-header
Initial packet); the datagram(s) to send back out. First the QUIC handshake: a
CRYPTO-frame ClientHello carrying the required `X25519MLKEM768` hybrid share gets
the server Initial+Handshake ServerHello flight (`datagramHandshake`). Otherwise
the datagram is DECRYPTED by the verified EverCrypt QUIC packet protection
(RFC 9001 §5: HKDF Initial key schedule, AES-ECB header-protection removal §5.4.3,
AES-128-GCM AEAD open §5.3) and its STREAM frame's HTTP/3 bytes drive the
UNCHANGED proven `Reactor.QuicIngress.datagramServe` (real QUIC/H3 dispatch),
served through the proven guarded pipeline `Reactor.Ingress.serveOverSubs`. On any
parse/auth failure returns no bytes (the host then sends nothing — an
attacker-forged packet is silently dropped, exactly as the AEAD's authenticity
gate dictates). -/
@[export drorb_serve_datagram]
def drorbServeDatagram (dg : ByteArray) : ByteArray :=
  match datagramHandshake dg with
  | some flight => flight
  | none =>
    match locateInitial dg with
    | none => ByteArray.empty
    | some loc =>
      match openInitial loc with
      | none => ByteArray.empty
      | some (_pn, plaintext) =>
        let (sid, h3) :=
          match parseStreamFrame plaintext with
          | some (s, d) => (s, d)
          | none => (0, plaintext.toList)
        let ev := Reactor.Quic.DatagramEvent.recvDatagram .appData 0
                    (Reactor.Quic.Payload.stream sid h3)
        let subs := (Reactor.QuicIngress.datagramServe
          Reactor.QuicIngress.demoConfig Reactor.QuicIngress.demoState ev).2
        let served : ByteArray :=
          ByteArray.mk (Reactor.Ingress.serveFull2OverSubs subs h3).toArray
        -- RE-ENCRYPT the served HTTP as a QUIC 1-RTT short-header packet
        -- (RFC 9000 §17.3) via the proven `QuicServer.buildShortPacket`: the
        -- response is a real ChaCha20-Poly1305-sealed, ChaCha20-header-protected
        -- 1-RTT packet a client consumes, not raw HTTP. Keys are the DEMO 1-RTT
        -- schedule (`demoAppKeys`, DCID-derived); the handshake-derived 1-RTT keys
        -- live on the stateful `QuicServer.stepServer` path. Falls back to the raw
        -- served bytes if key derivation or the seal fails (unreachable for a
        -- well-formed response).
        match demoAppKeys loc.dcid with
        | none => served
        | some ap =>
          let frame := QuicServer.streamFrame sid 0 true served
          match QuicServer.buildShortPacket loc.dcid 0 false false frame ap with
          | none => served
          | some pkt => pkt

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
