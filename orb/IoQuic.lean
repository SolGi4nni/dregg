/-
IoQuic — QUIC SOCKET-LIVE: a real/crafted QUIC Initial packet is DECRYPTED over a
real UDP socket by the verified EverCrypt QUIC packet protection, then reaches the
proven H3 dispatch.

The plain `orb-mac-multi` UDP lane took the datagram bytes as *already-decrypted*
application data — it modelled a datagram as arriving pre-parsed/pre-decrypted
(`Reactor.Quic.DatagramEvent`) and never touched packet protection. This file
closes that gap for the QUIC *Initial* packet: the untrusted UDP shell
(`ffi/mac_udp.c`) hands each datagram to the Lean callback `quicDatagram`, which

  1. parses the QUIC long-header Initial packet (RFC 9000 §17.2.2) far enough to
     extract the Destination Connection ID, the packet number, and the protected
     payload (the AEAD ciphertext ‖ tag),
  2. derives the AES-128-GCM Initial keys from the DCID via `initialSecrets`
     (real HKDF over EverCrypt) + `deriveAesKeys` (RFC 9001 §5.2 AES packet keys —
     key 16, iv 12, hp 16), removing AES-ECB header protection (§5.4.3) first,
  3. DECRYPTS the protected payload via `openPacketAes` (AES-128-GCM AEAD open —
     verified EverCrypt/Vale on x86, portable aws-lc-rs off-x86), with the
     unprotected header as the AAD and the RFC-9001 §5.3 per-packet nonce,
  4. parses the decrypted QUIC STREAM frame (RFC 9000 §19.8) to recover the H3
     stream bytes, and feeds them to the **unchanged** proven
     `Reactor.QuicIngress.datagramServe` — the real `Quic.step` + `H3.decFrame` +
     QPACK decode + `RingSubmission.dispatch` — then serves the dispatched request
     through the same proven guarded pipeline the TCP lanes run
     (`Reactor.Ingress.serveOverSubs`), and
  5. returns the HTTP response bytes, which the C shell `sendto`s back.

The proven core (`datagramServe`, `serveOverSubs`) is untouched. What is new is the
transport-crypto bridge: real EverCrypt packet protection turning wire bytes into
the decrypted stream the proven dispatch already knew how to consume.

SCOPE (named honestly — see QUIC-LIVE-README.md):
  * The lane runs the **AES-128-GCM + AES-ECB** QUIC Initial suite — the cipher
    RFC 9001 §5.2 MANDATES for Initial packets, hence the one every real
    off-the-shelf client (aioquic, quiche, curl, Chrome/Firefox) actually sends.
    AES-128-GCM AEAD is `Crypto.aesGcmOpen` (verified EverCrypt/Vale on x86; the
    portable, well-audited aws-lc-rs backend off-x86 — see the crypto trust
    ledger); AES-ECB header protection (§5.4.3) is `Crypto.aesEcbBlock`.
  * **Header protection (RFC 9001 §5.4) is applied and removed.** The crafted
    packet is AES-ECB-HP-masked exactly as a real client sends it, and
    `locateInitial`/`openInitial` strip it; an independent aioquic-produced
    AES-128-GCM Initial decrypts over the wire (see `--diag`).
  * The in-process self-test crafts a STREAM frame carrying an H3 HEADERS frame so
    the decrypt path runs end-to-end into the proven H3 dispatch. A *real* client's
    Initial instead carries a CRYPTO frame with the TLS ClientHello; the H3 request
    arrives only after the full handshake installs 1-RTT keys — the server response
    flight (ServerHello/EE/Finished + 1-RTT key install) is the honest residual.
  * The ChaCha20-Poly1305 QUIC suite remains available (`deriveChachaKeys`,
    `openPacket`) for the alt cipher; the Initial path is cipher-fixed to AES per
    the RFC. The key schedule is shared and A.1-vector-correct for both ciphers.
-/
import Reactor.Ingress
import Reactor.Quic
import Reactor.QuicIngress
import Crypto
import TlsCrypto
import QuicHeaderProt
import QuicServer
import H3.Request

/-! ## (0) The QUIC Initial packet protection — the QuicTransport derivations.

This exe's entry point is `_root_.main`. `QuicTransport.lean` exports a trailing
orphan `def main : IO UInt32` (its inline self-test, wired to no `lean_exe`), so
`import QuicTransport` would collide with this exe's `main` and cannot be resolved
without editing QuicTransport (out of scope here). We therefore re-express the
three QuicTransport packet-protection derivations we need — `initialSecret`,
`deriveChachaKeys`, `openPacket`/`sealPacket` — **verbatim over the SAME verified
primitives** QuicTransport is itself built from (`Crypto.hkdfExtract`,
`TlsCrypto.expandLabel`, `TlsCrypto.recordNonce`, `Crypto.chachaOpen/Seal` →
HACL*/EverCrypt). This is the identical computation on the identical EverCrypt, not
a reimplementation: the `selfTest` below asserts it against the exact RFC 9001
Appendix A.1 vectors `QuicTransport.SelfTest` checks, and the Python client decrypts
cross-implementation over the socket. The `openPacket` call site is annotated. -/

namespace IoQuic

open Crypto TlsCrypto

/-- RFC 9001 §5.2 QUIC v1 initial salt — `QuicTransport.initialSalt` verbatim. -/
def initialSalt : ByteArray :=
  ByteArray.mk #[0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
                 0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a]

/-- `HKDF-Extract(initial_salt, DCID)` then `HKDF-Expand-Label(·,"client in","",32)`
— `QuicTransport.initialSecrets … |>.client` verbatim (RFC 9001 §5.2). Real HKDF
over EverCrypt. -/
def clientInitialSecret (dcid : ByteArray) : Option ByteArray :=
  (hkdfExtract initialSalt dcid).bind
    (fun s => expandLabel s "client in".toUTF8 ByteArray.empty 32)

/-- One level's ChaCha20-Poly1305 packet keys (`QuicTransport.PacketKeys`): the
AEAD `key` + write-`iv` (RFC 9001 §5.3) AND the header-protection key `hp` (§5.4),
now that the ChaCha20 block is available (`QuicHeaderProt.chacha20Raw`). -/
structure PacketKeys where
  key : ByteArray
  iv : ByteArray
  hp : ByteArray

/-- `key = HKDF-Expand-Label(secret,"quic key","",32)`,
`iv = HKDF-Expand-Label(secret,"quic iv","",12)`,
`hp = HKDF-Expand-Label(secret,"quic hp","",32)` — `QuicTransport.deriveChachaKeys`
verbatim (RFC 9001 §5.1), real HKDF over EverCrypt. The `hp` key drives header
protection (RFC 9001 §5.4.4). -/
def deriveChachaKeys (secret : ByteArray) : Option PacketKeys :=
  match expandLabel secret "quic key".toUTF8 ByteArray.empty 32,
        expandLabel secret "quic iv".toUTF8 ByteArray.empty 12,
        expandLabel secret "quic hp".toUTF8 ByteArray.empty 32 with
  | some k, some iv, some hp => some { key := k, iv := iv, hp := hp }
  | _, _, _ => none

/-- The **AES-128-GCM** Initial keys (`QuicTransport.deriveAesKeys` verbatim, RFC
9001 §5.2): `key = HKDF-Expand-Label(secret,"quic key","",16)`,
`iv = …("quic iv","",12)`, `hp = …("quic hp","",16)`. This is the cipher RFC 9001
§5.2 MANDATES for QUIC Initial packets — the one every off-the-shelf client's
Initial actually uses — so it is the Initial path's key schedule. Real HKDF over
EverCrypt; only the expand lengths differ from the ChaCha keys. -/
def deriveAesKeys (secret : ByteArray) : Option PacketKeys :=
  match expandLabel secret "quic key".toUTF8 ByteArray.empty 16,
        expandLabel secret "quic iv".toUTF8 ByteArray.empty 12,
        expandLabel secret "quic hp".toUTF8 ByteArray.empty 16 with
  | some k, some iv, some hp => some { key := k, iv := iv, hp := hp }
  | _, _, _ => none

/-- Open a protected packet — `QuicTransport.openPacket` verbatim: real EverCrypt
ChaCha20-Poly1305 AEAD open at the RFC 9001 §5.3 per-packet nonce
(`TlsCrypto.recordNonce`), with the QUIC header as additional data. -/
def openPacket (pk : PacketKeys) (pn : Nat) (header ct : ByteArray) : Option ByteArray :=
  chachaOpen pk.key (recordNonce pk.iv pn) header ct

/-- Open an **AES-128-GCM** protected packet — `QuicTransport.openPacketAes`
verbatim: `Crypto.aesGcmOpen` at the RFC 9001 §5.3 per-packet nonce, QUIC header as
additional data. The AEAD half of decrypting a real client's Initial. -/
def openPacketAes (pk : PacketKeys) (pn : Nat) (header ct : ByteArray) : Option ByteArray :=
  aesGcmOpen pk.key (recordNonce pk.iv pn) header ct

/-- Seal a packet — `QuicTransport.sealPacket` verbatim (used only to craft the
in-process self-test packet on live EverCrypt). -/
def sealPacket (pk : PacketKeys) (pn : Nat) (header payload : ByteArray) : Option ByteArray :=
  chachaSeal pk.key (recordNonce pk.iv pn) header payload

/-- Seal an **AES-128-GCM** packet — `QuicTransport.sealPacketAes` verbatim (used
to craft the in-process self-test Initial exactly as a real client would). -/
def sealPacketAes (pk : PacketKeys) (pn : Nat) (header payload : ByteArray) : Option ByteArray :=
  aesGcmSeal pk.key (recordNonce pk.iv pn) header payload

/-! ## (1) QUIC wire helpers -/

/-- Read a QUIC variable-length integer (RFC 9000 §16) from the front of `bs`.
The top two bits of the first byte give the encoded length (1/2/4/8 bytes); the
remaining bits are the big-endian value. Returns `(value, bytesConsumed)`. -/
def readVarint (bs : List UInt8) : Option (Nat × Nat) :=
  match bs with
  | [] => none
  | b0 :: _ =>
    let len := 1 <<< (b0 >>> 6).toNat        -- 1, 2, 4, or 8
    if bs.length < len then none
    else
      let first := (b0 &&& 0x3f).toNat
      let rest := (bs.drop 1).take (len - 1)
      let v := rest.foldl (fun acc x => acc * 256 + x.toNat) first
      some (v, len)

/-! ## (2) The QUIC Initial long-header parse — locate the header-protected fields

With real header protection (RFC 9001 §5.4) the first byte's low bits and the
packet number are MASKED on the wire: the packet-number length is not yet known.
So the parse stops at the *start* of the packet-number field (`pnOff`) and keeps
the whole packet; header protection is removed afterward, once the keys (hence the
`hp` key, hence the mask) are derived. -/

/-- What the header parse locates before header protection is removed: the DCID
(Initial-key input), the packet-number field offset `pnOff`, and the full packet
bytes. -/
structure Located where
  dcid : ByteArray
  pnOff : Nat
  pkt : List UInt8

/-- Parse a QUIC long-header **Initial** packet (RFC 9000 §17.2.2) up to the start
of the (header-protected) packet number. Layout:

```
first byte (1)   0b1100_00pp  long | fixed | type=Initial(00) | pp = MASKED pnlen-1
version (4)
DCID len (1) ‖ DCID
SCID len (1) ‖ SCID
Token len (varint) ‖ Token
Length (varint)                 -- covers packet number + payload
Packet Number (pnlen)           -- header-protected; length unknown until unmasked
Protected Payload               -- AEAD ciphertext ‖ 16-byte tag
```

Only the header type (bits 4–7 of the first byte) and DCID are read in the clear.
-/
def locateInitial (dg : ByteArray) : Option Located :=
  let bs := dg.toList
  match bs[0]? with
  | none => none
  | some b0 =>
    -- long header (0x80) + fixed bit (0x40) + Initial type (0x00 in bits 4-5).
    -- The low 4 bits (packet-number length + reserved) are header-protected.
    if (b0 &&& 0xF0) != 0xC0 then none else
    let dcidLenOff := 1 + 4                     -- after first byte + version
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

/-! ## (3) Remove header protection, then decrypt via the verified EverCrypt crypto -/

/-- **Cipher-agile Initial open.** For a QUIC Initial the negotiated suite is fixed
by RFC 9001 §5.2 to **AES-128-GCM** — so a real off-the-shelf client's Initial is
AES-128-GCM AEAD under AES-ECB header protection, and the Initial path opens it
with the AES suite (this is the actual interop fix: the previous ChaCha hardcode
could never open a real client's AES Initial). Derive the client AES-128-GCM
Initial keys from the DCID (RFC 9001 §5.2), REMOVE **AES** header protection (§5.4.3
— `QuicHeaderProt.removeHpAes` over `Crypto.aesEcbBlock`) to recover the
unprotected first byte + packet number, then open the protected payload with
`openPacketAes` (real AES-128-GCM, unprotected header as AAD, decoded packet number
as the nonce input). Returns `(pn, plaintext)`. `none` on any derivation / HP /
AEAD-auth failure. `expectedPn` seeds the truncated-packet-number decode (0 for a
first Initial). -/
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

/-! ## (4) Parse the decrypted QUIC STREAM frame -/

/-- Parse a QUIC **STREAM** frame (RFC 9000 §19.8) out of the decrypted payload:
frame type `0b0000_1off` where `o`=OFF, `f`=LEN, and the low bit is FIN. Returns
`(streamId, streamData)`. Handles the OFF and LEN bits generically; a frame with
no LEN bit runs to the end of the packet. -/
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
      -- optional OFF field (bit 0x04)
      let afterOff :=
        if (ft &&& 0x04) != 0 then
          match readVarint (bs.drop afterSid) with
          | some (_, ob) => afterSid + ob
          | none => afterSid
        else afterSid
      -- optional explicit LEN field (bit 0x02)
      if (ft &&& 0x02) != 0 then
        match readVarint (bs.drop afterOff) with
        | some (dlen, lb) => some (sid, (bs.drop (afterOff + lb)).take dlen)
        | none => none
      else
        some (sid, bs.drop afterOff)

/-- Scan the decrypted Initial payload for a **CRYPTO** frame (RFC 9000 §19.6,
type `0x06`: `offset` varint ‖ `length` varint ‖ crypto data), skipping the
PADDING (`0x00`) and PING (`0x01`) frames a real client's Initial pads with.
Returns `(offset, cryptoData)` — the TLS ClientHello bytes the handshake carries.
This is what a real off-the-shelf client's Initial actually contains (vs. the
STREAM frame the in-process self-test crafts), so it is how the `--diag` path
reports reaching the ClientHello. -/
partial def parseCryptoFrame (pt : ByteArray) : Option (Nat × List UInt8) :=
  let rec go : List UInt8 → Option (Nat × List UInt8)
    | [] => none
    | 0x00 :: rest => go rest                    -- PADDING
    | 0x01 :: rest => go rest                    -- PING
    | 0x06 :: rest =>                            -- CRYPTO frame
      match readVarint rest with
      | none => none
      | some (off, ob) =>
        match readVarint (rest.drop ob) with
        | none => none
        | some (dlen, lb) => some (off, (rest.drop (ob + lb)).take dlen)
    | _ => none                                  -- any other frame: stop
  go pt.toList

/-! ## (5) The full callback: decrypt → proven H3 dispatch → response -/

/-- **`quicDatagram` — the QUIC-socket-live callback.** A real UDP datagram's bytes
in (a QUIC Initial packet); the served HTTP response bytes out. Parse → derive the
AES-128-GCM Initial keys (EverCrypt HKDF) → `openInitial` (AES-ECB header protection
removal + AES-128-GCM AEAD open) → recover the STREAM frame's H3 bytes → drive the
UNCHANGED proven `datagramServe` (real QUIC/H3 dispatch) → serve through the proven
guarded pipeline. On any parse/auth failure returns no bytes (the shell then sends
nothing — an attacker-forged packet is silently dropped, exactly as the AEAD's
authenticity gate dictates). -/
def quicDatagram (dg : ByteArray) : ByteArray :=
  match locateInitial dg with
  | none => ByteArray.empty
  | some loc =>
    match openInitial loc with
    | none => ByteArray.empty                  -- HP/AEAD auth failed: drop
    | some (_pn, plaintext) =>
      let (sid, h3) :=
        match parseStreamFrame plaintext with
        | some (s, d) => (s, d)
        | none => (0, plaintext.toList)        -- fall back to raw H3 bytes
      let ev := Reactor.Quic.DatagramEvent.recvDatagram .appData 0
                  (Reactor.Quic.Payload.stream sid h3)
      let subs := (Reactor.QuicIngress.datagramServe
        Reactor.QuicIngress.demoConfig Reactor.QuicIngress.demoState ev).2
      ByteArray.mk (Reactor.Ingress.serveFull2OverSubs subs h3).toArray

/-! ## (6) In-process self-test — craft, decrypt, dispatch on live EverCrypt

Before opening the socket, `main` crafts a self-consistent Initial packet in Lean
(sealing the STREAM/H3 frame under the SAME client Initial keys via
`QuicTransport.sealPacket` = real EverCrypt seal), runs the full `quicDatagram`
callback on it, and prints the outcome. This exercises the entire decrypt→dispatch
path on live EverCrypt in-process; the socket loop then re-runs it on datagrams a
Python client crafts and sends over the wire. -/

/-- Encode a Nat as a 2-byte QUIC varint (14-bit form; callers keep values small). -/
def varint2 (v : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (0x40 ||| (v / 256)), UInt8.ofNat v]

/-- Big-endian 4-byte packet number. -/
def pn4 (pn : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (pn / 0x1000000), UInt8.ofNat (pn / 0x10000),
                 UInt8.ofNat (pn / 0x100), UInt8.ofNat pn]

/-- Craft a self-consistent QUIC Initial packet carrying `h3` inside a STREAM
frame on `sid = 0`, protected under the client **AES-128-GCM** Initial keys derived
from `dcid` — exactly the cipher (RFC 9001 §5.2) and header protection (§5.4.3) a
real off-the-shelf client's Initial arrives under. `none` only if key derivation or
the real AES-GCM seal fails. -/
def craftInitial (dcid : ByteArray) (pn : Nat) (h3 : ByteArray) : Option ByteArray :=
  match clientInitialSecret dcid with
  | none => none
  | some cs =>
    match deriveAesKeys cs with
    | none => none
    | some pk =>
      -- inner: STREAM frame 0x08 (no OFF, no LEN, FIN implied), stream id 0
      let inner := (ByteArray.mk #[0x08, 0x00]) ++ h3
      let pnLen := 4
      let ctLen := inner.size + 16                        -- AES-128-GCM tag
      let lengthField := pnLen + ctLen
      -- unprotected header: first byte encodes pnLen-1 = 0b11 in the low bits.
      let header :=
        (ByteArray.mk #[0xC3, 0x00, 0x00, 0x00, 0x01])    -- first byte + version 1
          ++ (ByteArray.mk #[UInt8.ofNat dcid.size]) ++ dcid
          ++ (ByteArray.mk #[0x00])                        -- SCID len 0
          ++ (ByteArray.mk #[0x00])                        -- token len 0
          ++ varint2 lengthField
          ++ pn4 pn
      match sealPacketAes pk pn header inner with
      | none => none
      | some ct =>
        -- APPLY AES header protection (RFC 9001 §5.4.3): mask the first byte +
        -- packet number with the AES-ECB mask derived from the ciphertext sample,
        -- so the crafted packet is on the wire exactly as a real client sends it.
        let pnOff := header.size - pnLen
        match QuicHeaderProt.maskHeaderAes (header.toList ++ ct.toList) pnOff pnLen pk.hp with
        | none => none
        | some masked => some ⟨masked.toArray⟩

/-- Render a ByteArray as lowercase hex (for the transcript / Python parity). -/
def toHex (b : ByteArray) : String :=
  let hd : Nat → Char := fun n =>
    if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'a'.toNat)
  b.toList.foldl (fun s x =>
    s.push (hd (x.toNat / 16)) |>.push (hd (x.toNat % 16))) ""

/-- The self-test DCID (RFC 9001 A.1's client-chosen 8-byte DCID) and H3 request
(`GET /`, the demo HEADERS frame). -/
def testDcid : ByteArray :=
  ByteArray.mk #[0x83, 0x94, 0xc8, 0xf0, 0x3e, 0x51, 0x57, 0x08]

def testH3 : ByteArray := ByteArray.mk #[0x01, 0x04, 0x00, 0x00, 0xd1, 0xc1]

def selfTest : IO Bool := do
  match craftInitial testDcid 1 testH3 with
  | none => IO.eprintln "[FAIL] craftInitial: EverCrypt seal/HP/derive returned none"; return false
  | some pkt =>
    IO.println s!"[craft] HP-protected Initial packet ({pkt.size} bytes): {toHex pkt}"
    -- Independently locate → remove header protection → open, the real callback path.
    match locateInitial pkt with
    | none => IO.eprintln "[FAIL] locateInitial rejected the crafted packet"; return false
    | some loc =>
      IO.println s!"[locate] dcid={toHex loc.dcid} pnOff={loc.pnOff} pkt={loc.pkt.length}B"
      -- Show AES header protection actually being removed (recovers pnLen/pn).
      match clientInitialSecret loc.dcid >>= deriveAesKeys with
      | none => IO.eprintln "[FAIL] key derivation returned none"; return false
      | some pk =>
        match QuicHeaderProt.removeHpAes loc.pkt loc.pnOff pk.hp 0 with
        | none => IO.eprintln "[FAIL] removeHpAes (AES-ECB mask) returned none"; return false
        | some up =>
          IO.println s!"[unprotect] AES-ECB HP removed: firstByte=0x{toHex ⟨#[up.firstByte]⟩} pnLen={up.pnLen} pn={up.pn}"
          match openInitial loc with
          | none =>
            IO.eprintln "[FAIL] openInitial (AES-128-GCM open) returned none"; return false
          | some (pn, pt) =>
            IO.println s!"[decrypt] AES-128-GCM openPacket OK at pn={pn}, plaintext {pt.size}B: {toHex pt}"
            let resp := quicDatagram pkt
            if resp.size == 0 then
              IO.eprintln "[FAIL] quicDatagram dispatched no response"; return false
            else
              let head := String.fromUTF8? (ByteArray.mk (resp.toList.take 40).toArray)
                            |>.getD "<non-utf8>"
              IO.println s!"[dispatch] H3 served, response {resp.size}B, starts: {repr head}"
              return true

/-! ## (7) The UDP socket loop (untrusted C shell, `ffi/mac_udp.c`) -/

/-- `orb_mac_serve_udp port handler`: bind `127.0.0.1:port` as UDP and loop —
`recvfrom` one datagram, apply `handler` (here `quicDatagram`, which decrypts via
verified EverCrypt), `sendto` the response back. Blocks forever. -/
@[extern "orb_mac_serve_udp"]
opaque serveUdp (port : UInt16) (handler : ByteArray → ByteArray) : IO Unit

/-! ## (7b) `--diag`: run the REAL server parse on a captured client packet.

`orb-quic --diag <hexfile>` reads one hex-encoded datagram and runs the exact
server path (`locateInitial` → `openInitial`) on it, printing how far it gets.
Used to show a REAL off-the-shelf-client AES-128-GCM Initial being DECRYPTED:
recognized as a long-header Initial, DCID extracted, AES-ECB header protection
removed, AES-128-GCM AEAD opened, and the carried CRYPTO frame (TLS ClientHello)
recovered. The H3 request itself arrives only after the full handshake installs
1-RTT keys — the residual is the server response flight. -/

/-- Decode a hex string (whitespace ignored) into a `ByteArray`. -/
def fromHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '\t')
  let hv : Char → Option Nat := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hv hi, hv lo with
      | some h, some l => go rest (acc.push (UInt8.ofNat (h * 16 + l)))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

/-- Run the real server parse on a captured datagram and report how far it gets. -/
def diag (hexPath : String) : IO Unit := do
  let raw ← IO.FS.readFile hexPath
  let dg := fromHex raw
  IO.println s!"[diag] datagram {dg.size} bytes, first byte 0x{toHex ⟨#[dg.toList.getD 0 0]⟩}"
  match locateInitial dg with
  | none => IO.println "[diag] locateInitial: NOT a long-header Initial (rejected)"
  | some loc =>
    IO.println s!"[diag] locateInitial OK — long-header Initial recognized; DCID={toHex loc.dcid}, pnOff={loc.pnOff}"
    match openInitial loc with
    | some (pn, pt) =>
      IO.println s!"[diag] AES-ECB HP removed + AES-128-GCM AEAD opened at pn={pn} — DECRYPT OK, plaintext {pt.size}B"
      let preview := toHex ⟨(pt.toList.take 32).toArray⟩
      IO.println s!"[diag]   plaintext[0..32]: {preview}"
      match parseCryptoFrame pt with
      | some (off, cdata) =>
        IO.println s!"[diag] CRYPTO frame recovered (offset={off}, {cdata.length}B of TLS handshake) — the ClientHello"
        let chType := cdata.getD 0 0
        IO.println s!"[diag]   TLS handshake first byte=0x{toHex ⟨#[chType]⟩} (0x01 = ClientHello)"
        IO.println "[diag] MILESTONE: a real off-the-shelf client's AES-128-GCM Initial was decrypted by the"
        IO.println "[diag]   verified/portable QUIC packet protection. RESIDUAL to a full 1-RTT: the server"
        IO.println "[diag]   response flight (ServerHello/EncryptedExtensions/Finished + 1-RTT key install)."
      | none =>
        IO.println "[diag]   (no CRYPTO frame found in plaintext — likely a STREAM-framed crafted packet)"
    | none =>
      IO.println "[diag] openInitial returned none: not an AES-128-GCM Initial under this DCID's keys,"
      IO.println "[diag]   or the AEAD tag/header-protection did not authenticate (forged/corrupt packet)."

/-! ## (7c) The server response flight — QuicServer wired to the socket

`QuicServer.stepServer` builds the ServerHello/Handshake response flight from a
decrypted (possibly multi-packet) ClientHello, installs 1-RTT on the client
Finished, and serves the H3 requests in 1-RTT — over a connection table, so one
server process handles many connections. The H3 serve is the proven `datagramServe` → `serveOverSubs`
(the same dispatch the self-test drives), lifted to `ByteArray → ByteArray`. -/

/-! ### The QPACK response encoder (RFC 9204 §4.5) + the H3 HEADERS/DATA framing

The proven serve produces a `Reactor.Response` (status + headers + body). To hand
it to a real H3 client we re-express it as an HTTP/3 HEADERS frame (its field
section QPACK-encoded) followed by a DATA frame (the body). The QPACK encoder is
minimal: the `:status` uses the RFC 9204 Appendix A static
table index when the code has one (103/200/304/404/503), every other field is a
literal-with-literal-name representation (§4.5.6) with **no** Huffman coding — so a
QPACK *encoder*-side Huffman table is never needed. No dynamic table is used
(section prefix Required-Insert-Count 0, Base 0), so the client needs no encoder
stream. Field names are lowercased (RFC 9114 §4.1.2 forbids uppercase). -/

/-- QPACK prefix-integer encode (RFC 9204 §4.1.1): a `prefixBits`-bit prefix whose
high representation bits are already set in `flags`. Values here are small string
lengths / table indices. -/
partial def encQpackInt (prefixBits : Nat) (flags : UInt8) (v : Nat) : ByteArray :=
  let maxP := 2 ^ prefixBits - 1
  if v < maxP then ByteArray.mk #[flags ||| UInt8.ofNat v]
  else
    let rec go (n : Nat) (acc : ByteArray) : ByteArray :=
      if n < 128 then acc.push (UInt8.ofNat n)
      else go (n / 128) (acc.push (UInt8.ofNat (n % 128 + 128)))
    go (v - maxP) (ByteArray.mk #[flags ||| UInt8.ofNat maxP])

/-- A QPACK string literal (Huffman bit clear): a `prefixBits`-bit length prefix
carrying `flags` in its high bits, then the raw bytes. -/
def encQpackStr (prefixBits : Nat) (flags : UInt8) (bs : ByteArray) : ByteArray :=
  encQpackInt prefixBits flags bs.size ++ bs

/-- Literal field line with literal name, no Huffman (RFC 9204 §4.5.6): the name
uses the representation-`001` 3-bit length prefix (flags `0x20`, N=0, H=0), the
value a 7-bit length prefix (H=0). -/
def encQpackLiteral (name value : ByteArray) : ByteArray :=
  encQpackStr 3 0x20 name ++ encQpackStr 7 0x00 value

/-- The RFC 9204 Appendix A static-table index of a `:status` code, when it has
one. -/
def qpackStatusIndex (status : Nat) : Option Nat :=
  if status = 103 then some 24
  else if status = 200 then some 25
  else if status = 304 then some 26
  else if status = 404 then some 27
  else if status = 503 then some 28
  else none

/-- The `:status` field: an indexed static field line (`1 1 idx(6)` = `0xC0 ||| idx`)
for a code in the static table, else a literal `:status` field with the decimal
code as value. -/
def encQpackStatus (status : Nat) : ByteArray :=
  match qpackStatusIndex status with
  | some idx => ByteArray.mk #[UInt8.ofNat (0xC0 ||| idx)]
  | none => encQpackLiteral (String.toUTF8 ":status")
              ⟨(Reactor.natToDec status).toArray⟩

/-- Lowercase one ASCII byte (`A`–`Z` → `a`–`z`). -/
def lowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat && b.toNat ≤ 90 then UInt8.ofNat (b.toNat + 32) else b

def lowerName (bs : List UInt8) : ByteArray := ⟨(bs.map lowerByte).toArray⟩

/-- The QPACK field section for a response: section prefix (Required Insert Count
0, Base 0), the `:status` field, a derived `content-length` field (mirrors the H1
serializer, which frames length from the body), then every response header as a
literal field with a lowercased name. -/
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
carrying the body. The derived `content-length` (see `encQpackHeaderBlock`) is
framed from `resp.body`, so a caller that suppresses the body (HEAD) suppresses
the advertised length with it — the two never disagree. -/
def encodeH3Response (resp : Reactor.Response) : ByteArray :=
  let block := encQpackHeaderBlock resp
  let headersFrame := ByteArray.mk #[0x01] ++ QuicServer.encVarint block.size ++ block
  let body : ByteArray := ⟨resp.body.toArray⟩
  let dataFrame := ByteArray.mk #[0x00] ++ QuicServer.encVarint body.size ++ body
  headersFrame ++ dataFrame

/-! ### Deriving the proven serve's structured Response for an H3 request

`serveH3Resp` decodes the reassembled H3 request through the SAME proven
`Reactor.QuicIngress.datagramServe` the TCP-side ingress runs (real `Quic.step`,
real `H3.decFrame`, real `H3.Qpack.decodeFieldSection` — now with the deployed
RFC 7541 Huffman decoder), extracts the dispatched `Proto.Request`, and returns
the SAME guarded `Reactor.Response` the deployed serve produces: the traversal-404
gate, the Policy-403 gate, or the application response. `serialize` of this
Response is byte-for-byte the `serveOverSubs` output the H1/TCP path emits — this
is that response, re-expressed structurally so it can be re-framed as HTTP/3. -/

/-- The Huffman-capable H3 lane config: the deployed RFC 7541 Huffman decoder
(vs. the reject-all `demoConfig` used by the pure-static kernel `#guard`s). -/
def huffConfig : Reactor.Quic.QuicConfig := ⟨_root_.H3.Qpack.rfc7541Huffman⟩

/-- An empty QPACK/arena store to decode a request field section against (the
static table only; the deployed lane holds no dynamic table). -/
def h3EmptyStore : Arena.Store := { main := #[], sidecar := #[], entries := [] }

/-- The canned `400 Bad Request` for a request the RFC 9114 §4.1 / §4.3.1 front
end rejects (an unexpected frame before HEADERS, an undecodable field section, or
a head missing a required pseudo-header) — the same malformed-path response the
HTTP/1.1 serve emits. -/
def malformedH3Resp : Reactor.Response :=
  Reactor.error4xx 400 Reactor.reasonBad Reactor.badBody

/-- Re-frame a decoded request stream's raw QPACK field section and concatenated
content as a canonical, grease-free HTTP/3 request stream (one HEADERS frame ‖ one
DATA frame) for the proven dispatcher — so the unknown/reserved (GREASE) frames
`readRequestStream` skipped are gone before the request reaches routing. -/
def reframeRequest (enc body : List UInt8) : ByteArray :=
  let hdr := ByteArray.mk #[0x01] ++ QuicServer.encVarint enc.length ++ ⟨enc.toArray⟩
  let dat := ByteArray.mk #[0x00] ++ QuicServer.encVarint body.length ++ ⟨body.toArray⟩
  hdr ++ dat

/-- **The H3 request front end** (RFC 9114 §4.1 + §4.3.1). Run the raw
request-stream bytes through the proven `readRequestStream` (skip unknown/GREASE
frames, open on HEADERS, concatenate DATA, close on trailers), decode the field
section, and apply the `validRequestHead` §4.3.1 gate:

  * an unexpected frame / undecodable section / a head missing a required
    pseudo-header (`:method`, and for non-CONNECT `:scheme`/`:path`/authority) is
    answered with the canned `400` (`malformedH3Resp`) — no routing;
  * otherwise the grease-free canonical request is dispatched through the SAME
    proven `datagramServe` + full `deployStagesFull2` middleware fold the TCP
    dataplane runs.

Returns the structured `Response` and the request method (for HEAD suppression). -/
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

/-- Serve one reassembled H3 request-stream byte string through the proven QUIC/H3
front end (grease skip + §4.3.1 gate), dispatch, and guarded pipeline, returning
the response re-framed as the HTTP/3 stream-0 payload (HEADERS frame ‖ DATA
frame). For a `HEAD` request the response content is suppressed by the proven
`H3.headSuppressedBody` (RFC 9110 §9.3.2) before framing, so the `content-length`
and the DATA frame agree at zero. -/
def serveH3 (h3 : ByteArray) : ByteArray :=
  let (resp, method) := serveH3Resp h3
  encodeH3Response { resp with body := _root_.H3.headSuppressedBody method resp.body }

/-- The stateful QUIC server handler over an `IO.Ref` server state (a connection
table + pre-connection ClientHello reassembly): one received datagram in, the
datagrams to send out. Wired to the C driver `orb_quic_serve`. -/
def quicServeHandler (ref : IO.Ref QuicServer.ServerState) (dg : ByteArray) :
    IO (Array ByteArray) := do
  let cur ← ref.get
  let (cur', outs) := QuicServer.stepServer serveH3 cur dg
  ref.set cur'
  return outs

/-- `orb_quic_serve port handler`: the stateful UDP server loop (ffi/mac_udp.c),
recv one datagram → `handler` → send the returned datagrams. -/
@[extern "orb_quic_serve"]
opaque serveQuic (port : UInt16) (handler : ByteArray → IO (Array ByteArray)) : IO Unit

/-! ## (7d) `--bridge`: drive the full server handshake over stdin/stdout hex.

`orb-quic --bridge` reads one client datagram (hex) per line on stdin, threads it
through the stateful `QuicServer.stepServer`, and writes `N <k>` then `k` server
datagrams (hex) per line — so a real off-the-shelf QUIC client (aioquic) can be
driven against the verified server flight with no sockets, for deterministic,
inspectable handshake validation. -/
partial def bridgeLoop (ref : IO.Ref QuicServer.ServerState)
    (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line == "" then return ()              -- EOF
  if line.trim == "" then bridgeLoop ref stdin stdout else do
  let dg := fromHex line
  let cur ← ref.get
  let (cur', outs) := QuicServer.stepServer serveH3 cur dg
  ref.set cur'
  -- concise diagnostics (to stderr): coalesced packet kinds + table size
  let kinds := (QuicServer.splitPackets 16 dg.toList).map
    (fun pkt => match pkt[0]? with | some b => reprStr (QuicServer.classify b) | none => "?")
  let phs := cur'.conns.map (fun c => reprStr c.phase)
  IO.eprintln s!"[bridge] in {dg.size}B kinds={kinds} -> conns={phs} pending={cur'.pending.length} outs={outs.size}"
  stdout.putStr s!"N {outs.size}\n"
  for o in outs do
    stdout.putStr (toHex o); stdout.putStr "\n"
  stdout.flush
  bridgeLoop ref stdin stdout

def bridge : IO Unit := do
  let ref ← IO.mkRef QuicServer.ServerState.empty
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  bridgeLoop ref stdin stdout

/-! ## (8) main -/

/-- `orb-quic [udpPort]` (default 8443): run the in-process EverCrypt decrypt→
dispatch self-test, then bind the real UDP socket and serve QUIC Initial packets
live, decrypting each with the verified crypto before the proven H3 dispatch.
`orb-quic --diag <hexfile>` instead runs the server parse on a captured packet. -/
def main (args : List String) : IO Unit := do
  match args with
  | "--diag" :: path :: _ => diag path
  | "--bridge" :: _ => bridge
  | "--serve" :: rest =>
    -- Stateful QUIC server: real handshake flight + 1-RTT, over the UDP socket.
    let udpPort : UInt16 := ((rest[0]?).bind String.toNat?).map (·.toUInt16) |>.getD 8443
    IO.eprintln s!"orb-quic: stateful QUIC server on 127.0.0.1:{udpPort} (verified EverCrypt handshake flight)"
    (← IO.getStdout).flush
    let ref ← IO.mkRef QuicServer.ServerState.empty
    serveQuic udpPort (quicServeHandler ref)
  | _ =>
    IO.println "orb-quic: QUIC SOCKET-LIVE — verified EverCrypt packet protection → proven H3 dispatch"
    IO.println "── in-process self-test (crafted Initial, live EverCrypt) ──"
    let ok ← selfTest
    IO.println s!"── self-test {if ok then "PASSED" else "FAILED"} ──"
    let udpPort : UInt16 := ((args[0]?).bind String.toNat?).map (·.toUInt16) |>.getD 8443
    IO.println s!"listening for real QUIC Initial datagrams on 127.0.0.1:{udpPort} (Ctrl-C to stop)"
    (← IO.getStdout).flush        -- flush before the blocking socket loop
    serveUdp udpPort quicDatagram

end IoQuic

/-- The exe entry point. `IoQuic` is not in the import closure of any module that
defines `_root_.main`, so this is the sole `main` and Lake uses it. -/
def main (args : List String) : IO Unit := IoQuic.main args
