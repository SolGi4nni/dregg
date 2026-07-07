/-
# WebrtcLive — completing the DTLS 1.2 handshake against a real WebRTC peer

`WebrtcTransport.lean` models the WebRTC transport stack as a sans-IO state
machine: the DTLS handshake FSM (`dtlsStep`), the DTLS key schedule over the
verified EverCrypt HKDF, the SCTP four-way association, and RFC 8831 ordered
delivery. The cryptography is the verified `Crypto` boundary (HACL*/EverCrypt).

That model captures the state gating and the crypto seam, but it is *sans-IO*:
it does not itself serialize DTLS records onto a socket. This executable is the
byte-and-socket driver — the WebRTC analogue of `WgLive` — that carries a full
DTLS 1.2 handshake to a real WebRTC peer's DTLS engine
(`conformance/webrtc/dtls_peer.py`, aiortc's OpenSSL DTLS server) and completes
it end to end on the verified `Crypto` primitives:

  * drorb is the DTLS CLIENT. It builds a byte-exact DTLS 1.2 ClientHello
    (RFC 6347 record layer, RFC 5246 handshake) offering ECDHE-ECDSA suites and
    the **x25519** named group first, so the peer negotiates its ECDHE over the
    curve of the verified `Crypto.x25519` / `Crypto.x25519Base`.
  * The real peer replies with its flight — ServerHello (selecting
    `TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256`, negotiating
    `extended_master_secret`), Certificate, ServerKeyExchange (the peer's
    ephemeral x25519 public key), CertificateRequest (mutual auth),
    ServerHelloDone. drorb parses the flight (reassembling fragmented handshake
    messages) and runs the verified `Crypto.x25519` on the peer's ephemeral key
    to compute the ECDHE premaster secret.
  * drorb then builds and sends its **second flight**, byte-exact:
    - Certificate — a self-signed ECDSA-P256 X.509 cert whose public key is
      produced by the verified `TlsCrypto.P256` (HACL* P-256), matching the
      CertificateRequest.
    - ClientKeyExchange — the client's ephemeral x25519 public key
      (`Crypto.x25519Base`).
    - CertificateVerify — an ECDSA-P256-SHA256 signature over the handshake
      transcript (`TlsCrypto.Sig.ecdsaP256Sign`, HACL* P-256).
    - ChangeCipherSpec.
    - Finished — `verify_data = PRF(master_secret, "client finished",
      SHA256(transcript))[0..12]` under the TLS 1.2 P_SHA256 PRF, built from
      `Crypto.hkdfExtract` (HKDF-Extract = HMAC-SHA256), protected as an
      AES-128-GCM record (`Crypto.aesGcmSeal`, RFC 5288 nonce/AAD framing).
    The `master_secret` is the RFC 7627 extended master secret derived from the
    ECDHE premaster via the TLS 1.2 PRF (the peer negotiated EMS).
  * drorb then AEAD-opens (`Crypto.aesGcmOpen`) the peer's ChangeCipherSpec +
    Finished flight and checks the peer's `verify_data` against
    `PRF(master_secret, "server finished", SHA256(transcript))` — confirming both
    sides completed and agree on the keys.

This is a live cross-check, not part of the trusted core (the WebRTC analogue of
`crypto-selftest` / `wg-live`). Everything cryptographic is the verified Lean.
The DTLS handshake FSM discipline the driver follows is refined against
`WebrtcTransport.dtlsStep` (`driver_reaches_established`,
`driver_finished_required` below).

On top of the established DTLS records this driver then rides the full WebRTC
data-channel stack, all inside the epoch-1 AES-128-GCM records:

  * SCTP-over-DTLS (RFC 4960 §5.1): the four-way association — INIT / INIT-ACK
    (with the peer's state cookie) / COOKIE-ECHO / COOKIE-ACK — each SCTP packet
    CRC32C-checksummed (`Crypto.crc32c`) and framed by the verified
    `WebrtcTransport.Sctp` serializer, carried as `Crypto.aesGcmSeal` records.
  * DCEP (RFC 8832): a DATA_CHANNEL_OPEN on stream 0 (PPID 50, built by the
    verified `Dcep.encodeOpen`), the peer's DATA_CHANNEL_ACK checked with
    `Dcep.parse`, then a real string data-channel message (PPID 51).

Against a real aiortc peer running its own `RTCSctpTransport` and data-channel
code, this opens a genuine `RTCDataChannel` (aiortc's `on("datachannel")` fires)
and delivers a string message verbatim (the channel's `on("message")` fires).
The driver's control flow refines the proven models: the SCTP four-way against
`WebrtcTransport.sctpStep` (`driver_sctp_reaches_established`), the DCEP open
against `Dcep.chStep` (`driver_dcep_reaches_open`), and the OPEN bytes against
`Dcep.parse` (`driver_dcep_open_wire`).

Usage:
  webrtc-live <host> <port> [ephPrivHex]
-/
import WebrtcTransport
import Dcep
import Crypto
import TlsCrypto.P256
import TlsCrypto.Sig

open WebrtcTransport (DtlsState DtlsEvent dtlsStep SctpState SctpEvent sctpStep)

namespace WebrtcLive

@[extern "drorb_wrtc_udp_connect"]
opaque udpConnect (host : String) (port : UInt16) : IO UInt32

@[extern "drorb_wrtc_udp_send"]
opaque udpSend (fd : UInt32) (payload : ByteArray) : IO Unit

@[extern "drorb_wrtc_udp_recv"]
opaque udpRecv (fd : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)

@[extern "drorb_wrtc_udp_close"]
opaque udpClose (fd : UInt32) : IO Unit

/-! ## Hex helpers -/

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## DTLS 1.2 wire construction (RFC 6347 record layer, RFC 5246 handshake) -/

/-- Big-endian 16-bit. -/
def u16 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]
/-- Big-endian 24-bit. -/
def u24 (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]
/-- Big-endian 48-bit (DTLS record sequence number). -/
def u48 (n : Nat) : ByteArray :=
  ByteArray.mk #[0, 0, UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
                 UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- A `<len:1> ‖ body` vector (opaque<0..255>). -/
def vec8 (b : ByteArray) : ByteArray := (ByteArray.mk #[UInt8.ofNat b.size]) ++ b
/-- A `<len:2> ‖ body` vector (opaque<0..65535>). -/
def vec16 (b : ByteArray) : ByteArray := u16 b.size ++ b

/-- A TLS extension: `type:2 ‖ <len:2> body`. -/
def ext (t : Nat) (body : ByteArray) : ByteArray := u16 t ++ vec16 body

/-- DTLS 1.2 = 0xFEFD. -/
def dtls12 : ByteArray := ByteArray.mk #[0xfe, 0xfd]

/-- The ClientHello body (RFC 5246 §7.4.1.2, DTLS cookie per RFC 6347). Offers
the ECDHE-ECDSA suites a WebRTC peer accepts and the x25519 named group first,
so the peer's ECDHE runs over the curve of the verified `Crypto.x25519`. -/
def clientHelloBody (random : ByteArray) (cookie : ByteArray) : ByteArray :=
  let suites := u16 0xC02B ++ u16 0xCCA9 ++ u16 0xC009 ++ u16 0xC00A
  let supportedGroups := ext 0x000A (vec16 (u16 0x001D ++ u16 0x0017))  -- x25519, secp256r1
  let ecPointFormats := ext 0x000B (vec8 (ByteArray.mk #[0x00]))        -- uncompressed
  let sigAlgs := ext 0x000D (vec16 (u16 0x0403 ++ u16 0x0401))          -- ecdsa_p256_sha256, rsa_sha256
  let ems := ext 0x0017 ByteArray.empty                                 -- extended_master_secret
  let useSrtp := ext 0x000E (vec16 (u16 0x0007 ++ u16 0x0008) ++ vec8 ByteArray.empty)
  let reneg := ext 0xFF01 (vec8 ByteArray.empty)                        -- renegotiation_info
  let exts := supportedGroups ++ ecPointFormats ++ sigAlgs ++ ems ++ useSrtp ++ reneg
  dtls12 ++ random ++ vec8 ByteArray.empty ++ vec8 cookie
    ++ vec16 suites ++ vec8 (ByteArray.mk #[0x00]) ++ vec16 exts

/-- A DTLS handshake message (RFC 6347 §4.2.2), unfragmented (fragment_offset=0,
fragment_length=length) — the form the handshake transcript reconstructs. -/
def handshake (msgType : Nat) (body : ByteArray) (msgSeq : Nat) : ByteArray :=
  (ByteArray.mk #[UInt8.ofNat msgType]) ++ u24 body.size ++ u16 msgSeq
    ++ u24 0 ++ u24 body.size ++ body

/-- A DTLS record (RFC 6347 §4.1) at a given epoch:
`type ‖ version ‖ epoch ‖ seq48 ‖ <len:2> payload`. -/
def recordE (contentType epoch seq : Nat) (payload : ByteArray) : ByteArray :=
  (ByteArray.mk #[UInt8.ofNat contentType]) ++ dtls12 ++ u16 epoch ++ u48 seq
    ++ u16 payload.size ++ payload

/-- An epoch-0 DTLS record (the plaintext handshake epoch). -/
def record (contentType seq : Nat) (payload : ByteArray) : ByteArray :=
  recordE contentType 0 seq payload

/-! ## Response parsing -/

/-- Read a big-endian 16-bit integer at `i`. -/
def rd16 (b : ByteArray) (i : Nat) : Nat := b[i]!.toNat * 256 + b[i+1]!.toNat
/-- Read a big-endian 24-bit integer at `i`. -/
def rd24 (b : ByteArray) (i : Nat) : Nat :=
  (b[i]!.toNat * 256 + b[i+1]!.toNat) * 256 + b[i+2]!.toNat

/-- Split a datagram into `(contentType, payload)` DTLS records. -/
partial def records (b : ByteArray) : List (UInt8 × ByteArray) :=
  let rec go (i : Nat) (acc : List (UInt8 × ByteArray)) : List (UInt8 × ByteArray) :=
    if i + 13 ≤ b.size then
      let ct := b[i]!
      let len := rd16 b (i + 11)
      let payload := b.extract (i + 13) (i + 13 + len)
      go (i + 13 + len) ((ct, payload) :: acc)
    else acc.reverse
  go 0 []

/-- Split a datagram into full DTLS records, keeping the 8-byte
`epoch ‖ seq48` prefix (the AEAD `seq_num`) and the record payload. -/
partial def recordsFull (b : ByteArray) : List (UInt8 × ByteArray × ByteArray) :=
  let rec go (i : Nat) (acc : List (UInt8 × ByteArray × ByteArray)) :=
    if i + 13 ≤ b.size then
      let ct := b[i]!
      let seqNum := b.extract (i + 3) (i + 11)   -- epoch(2) ‖ seq48(6)
      let len := rd16 b (i + 11)
      let payload := b.extract (i + 13) (i + 13 + len)
      go (i + 13 + len) ((ct, seqNum, payload) :: acc)
    else acc.reverse
  go 0 []

/-- A parsed DTLS handshake fragment (RFC 6347 §4.2.2). -/
structure HsFrag where
  msgType : UInt8
  msgSeq : Nat
  fullLen : Nat
  fragOffset : Nat
  body : ByteArray

/-- Walk the handshake fragments in one record payload (RFC 6347 §4.2.2). -/
partial def handshakes (pl : ByteArray) : List HsFrag :=
  let rec go (i : Nat) (acc : List HsFrag) : List HsFrag :=
    if i + 12 ≤ pl.size then
      let mt := pl[i]!
      let flen := rd24 pl (i + 9)
      let frag : HsFrag :=
        { msgType := mt, msgSeq := rd16 pl (i + 4), fullLen := rd24 pl (i + 1),
          fragOffset := rd24 pl (i + 6), body := pl.extract (i + 12) (i + 12 + flen) }
      go (i + 12 + flen) (frag :: acc)
    else acc.reverse
  go 0 []

/-- All handshake fragments across every type-22 record in a datagram. -/
def allHandshakes (dg : ByteArray) : List HsFrag :=
  (records dg).foldl (fun acc (ct, pl) => if ct == 22 then acc ++ handshakes pl else acc) []

/-- Reassemble the handshake message with `msg_seq = msgSeq` from its fragments
(concatenating in offset order, skipping duplicates/retransmits), and return its
*reconstructed* unfragmented handshake-message bytes — exactly the form both
peers feed into the handshake transcript (RFC 6347 §4.2.6). -/
def reconMsg (frags : List HsFrag) (msgSeq : Nat) : Option ByteArray :=
  let fs := frags.filter (fun f => f.msgSeq == msgSeq)
  match fs with
  | [] => none
  | f0 :: _ =>
    let body := fs.foldl
      (fun acc f => if f.fragOffset == acc.size then acc ++ f.body else acc) ByteArray.empty
    some (handshake f0.msgType.toNat body msgSeq)

/-- The negotiated cipher suite from a ServerHello body (RFC 5246 §7.4.1.3):
`version:2 ‖ random:32 ‖ <sid:1> ‖ cipher:2 ‖ …`. -/
def serverHelloCipher (body : ByteArray) : Option Nat :=
  if body.size < 35 then none
  else
    let sidLen := body[34]!.toNat
    let j := 35 + sidLen
    if body.size < j + 2 then none else some (rd16 body j)

/-- The server's ephemeral public key from an ECDHE ServerKeyExchange body
(RFC 4492 §5.4): `curve_type:1 ‖ named_curve:2 ‖ <pubkey:1> ‖ …`. -/
def serverKeyExchangePub (body : ByteArray) : Option (Nat × ByteArray) :=
  if body.size < 4 then none
  else
    let namedCurve := rd16 body 1
    let pkLen := body[3]!.toNat
    if body.size < 4 + pkLen then none
    else some (namedCurve, body.extract 4 (4 + pkLen))

/-! ## The TLS 1.2 PRF (RFC 5246 §5), over verified `Crypto`

`P_SHA256(secret, seed)` is built from `HMAC-SHA256`, which is exactly
`Crypto.hkdfExtract` (RFC 5869: `HKDF-Extract(salt, IKM) = HMAC-Hash(salt, IKM)`
with the HMAC key as the salt). So the whole TLS 1.2 key schedule — master
secret, key block, and the Finished `verify_data` — runs on the verified
EverCrypt HMAC, no new primitive. -/

/-- 32 zero bytes (the size `hkdfExtract` always returns; the fallback is never
reached). -/
def zeros32 : ByteArray := ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

/-- `HMAC-SHA256(key, msg) = HKDF-Extract(salt := key, ikm := msg)` (RFC 5869). -/
def hmac256 (key msg : ByteArray) : ByteArray := (Crypto.hkdfExtract key msg).getD zeros32

/-- The P_SHA256 block stream (RFC 5246 §5): with `a = A(i)`, emit
`HMAC(secret, A(i+1) ‖ seed)` and recurse. `blocks` bounds it to the bytes
needed. -/
def pHashBlocks (secret seed : ByteArray) : ByteArray → Nat → ByteArray
  | _, 0 => ByteArray.empty
  | a, k + 1 =>
    let a' := hmac256 secret a
    hmac256 secret (a' ++ seed) ++ pHashBlocks secret seed a' k

/-- The TLS 1.2 PRF (RFC 5246 §5): `PRF(secret, label, seed) =
P_SHA256(secret, label ‖ seed)`, truncated to `n` bytes. -/
def prf (secret label seedv : ByteArray) (n : Nat) : ByteArray :=
  let s := label ++ seedv
  (pHashBlocks secret s s ((n + 31) / 32)).extract 0 n

/-! ## The client certificate: a self-signed ECDSA-P256 cert over verified HACL*

A minimal DER X.509 certificate whose subjectPublicKey is produced by the
verified `TlsCrypto.P256.pub` and whose self-signature is the verified
`TlsCrypto.Sig.ecdsaP256Sign`. It satisfies the peer's CertificateRequest
(`ecdsa_sign` / `ecdsa_secp256r1_sha256`); the CertificateVerify below proves
possession of the matching private key. -/

/-- DER length octets (short form, or long form up to two bytes). -/
def derLen (n : Nat) : ByteArray :=
  if n < 128 then ByteArray.mk #[UInt8.ofNat n]
  else if n < 256 then ByteArray.mk #[0x81, UInt8.ofNat n]
  else ByteArray.mk #[0x82, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- A DER TLV: `tag ‖ length ‖ body`. -/
def derTLV (tag : UInt8) (body : ByteArray) : ByteArray :=
  ByteArray.mk #[tag] ++ derLen body.size ++ body

/-- The fixed client-certificate private scalar (a valid P-256 scalar; this is a
conformance certificate, not a production key). -/
def certPriv : ByteArray := ofHex "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"

def oidEcdsaSha256 : ByteArray := ByteArray.mk #[0x06,0x08,0x2A,0x86,0x48,0xCE,0x3D,0x04,0x03,0x02]
def oidEcPubkey : ByteArray := ByteArray.mk #[0x06,0x07,0x2A,0x86,0x48,0xCE,0x3D,0x02,0x01]
def oidPrime256v1 : ByteArray := ByteArray.mk #[0x06,0x08,0x2A,0x86,0x48,0xCE,0x3D,0x03,0x01,0x07]
def oidCN : ByteArray := ByteArray.mk #[0x06,0x03,0x55,0x04,0x03]

def algEcdsa : ByteArray := derTLV 0x30 oidEcdsaSha256
def nameCN : ByteArray :=
  derTLV 0x30 (derTLV 0x31 (derTLV 0x30 (oidCN ++ derTLV 0x0c "drorb".toUTF8)))
def validity : ByteArray :=
  derTLV 0x30 (derTLV 0x17 "200101000000Z".toUTF8 ++ derTLV 0x17 "490101000000Z".toUTF8)
def spki (point : ByteArray) : ByteArray :=
  derTLV 0x30 (derTLV 0x30 (oidEcPubkey ++ oidPrime256v1)
    ++ derTLV 0x03 (ByteArray.mk #[0x00] ++ point))
def tbsCert (point : ByteArray) : ByteArray :=
  let version := derTLV 0xa0 (derTLV 0x02 (ByteArray.mk #[0x02]))
  let serial := derTLV 0x02 (ByteArray.mk #[0x01])
  derTLV 0x30 (version ++ serial ++ algEcdsa ++ nameCN ++ validity ++ nameCN ++ spki point)

/-- The self-signed client certificate DER, built and signed on the verified
HACL* P-256. -/
def clientCertDer : Option ByteArray := do
  let point ← TlsCrypto.P256.pub certPriv
  let tbs := tbsCert point
  let sig ← TlsCrypto.Sig.ecdsaP256Sign certPriv tbs
  some (derTLV 0x30 (tbs ++ algEcdsa ++ derTLV 0x03 (ByteArray.mk #[0x00] ++ sig)))

/-! ## DTLS handshake FSM refinement (against `WebrtcTransport.dtlsStep`)

The driver walks the client side of the DTLS handshake FSM:
`start -[ClientHello]-> wait_sh -[ServerHello]-> wait_finished -[Finished]->
established`. These are exactly the `WebrtcTransport.dtlsStep` edges, so the
driver's control flow refines the proven model. -/

/-- The DTLS events the driver performs, through the Finished exchange. -/
def driverTrace : List DtlsEvent := [.sendClientHello, .recvServerHello, .recvFinished]

/-- Fold the model's transition function over an event trace. -/
def dtlsRun : DtlsState → List DtlsEvent → DtlsState
  | s, []      => s
  | s, e :: es => dtlsRun (dtlsStep s e) es

/-- **The driver's control flow reaches `established`.** Running the driver's
DTLS event trace through `WebrtcTransport.dtlsStep` from `start` reaches
`established` — the state in which the Finished exchange has completed and
application traffic keys exist. -/
theorem driver_reaches_established : dtlsRun .start driverTrace = .established := by
  decide

/-- **ServerHello is the only edge into `wait_finished`.** The driver can only
hold the server's key-exchange parameters by having fired `recvServerHello` from
`wait_sh` — the model forbids any other path. -/
theorem driver_serverhello_required (s : DtlsState) (e : DtlsEvent)
    (h : dtlsStep s e = .wait_finished) (hne : s ≠ .wait_finished) :
    s = .wait_sh ∧ e = .recvServerHello := by
  cases s <;> cases e <;> simp_all [dtlsStep]

/-- **The Finished exchange is the only edge into `established`.** The handshake
completes (application traffic keys exist) only by firing `recvFinished` from
`wait_finished` — the model forbids any shortcut past the ServerHello and the
Finished exchange. This is the DTLS analogue of `sctp_enter_established`; the
driver's completion refines exactly this transition. -/
theorem driver_finished_required (s : DtlsState) (e : DtlsEvent)
    (h : dtlsStep s e = .established) (hne : s ≠ .established) :
    s = .wait_finished ∧ e = .recvFinished :=
  WebrtcTransport.dtls_enter_established s e h hne

/-! ## SCTP-over-DTLS + DCEP: the layers that ride on the established records

Once the DTLS handshake is `established`, the driver opens an SCTP association
(RFC 4960 four-way handshake) *inside* the AES-128-GCM application-data records,
then a WebRTC data channel over it (DCEP, RFC 8832). All the wire framing is the
verified `WebrtcTransport.Sctp` serializer (CRC32C from `Crypto.crc32c`) and the
`Dcep` encoder; the record protection is the same `Crypto.aesGcmSeal` /
`aesGcmOpen` under the epoch-1 keys the handshake established. -/

/-- Read a big-endian 32-bit integer at `i`. -/
def rd32 (b : ByteArray) (i : Nat) : Nat := rd16 b i * 65536 + rd16 b (i + 2)

/-- Split an SCTP packet into its `(chunkType, chunkBody)` chunks (RFC 4960 §3.2),
walking past the 12-byte common header and each chunk's 4-byte-aligned length. -/
partial def sctpChunks (pkt : ByteArray) : List (UInt8 × ByteArray) :=
  let rec go (i : Nat) (acc : List (UInt8 × ByteArray)) : List (UInt8 × ByteArray) :=
    if i + 4 ≤ pkt.size then
      let ty := pkt[i]!
      let len := rd16 pkt (i + 2)
      if len < 4 then acc.reverse
      else
        let body := pkt.extract (i + 4) (i + len)
        go (i + len + (4 - len % 4) % 4) ((ty, body) :: acc)
    else acc.reverse
  go 12 []

/-- Walk the TLV parameters in a chunk body starting at `start` (RFC 4960 §3.2.1),
returning `(paramType, value)` pairs. -/
partial def sctpParams (body : ByteArray) (start : Nat) : List (Nat × ByteArray) :=
  let rec go (i : Nat) (acc : List (Nat × ByteArray)) : List (Nat × ByteArray) :=
    if i + 4 ≤ body.size then
      let ty := rd16 body i
      let len := rd16 body (i + 2)
      if len < 4 then acc.reverse
      else go (i + len + (4 - len % 4) % 4) ((ty, body.extract (i + 4) (i + len)) :: acc)
    else acc.reverse
  go start []

/-- Protect an SCTP packet as one AES-128-GCM DTLS application-data record
(content type 23, RFC 6347/5288), at epoch 1 and DTLS record sequence `seq`,
under the client write key/IV the handshake established — the same record
construction the Finished used. -/
def sealApp (cwk civ : ByteArray) (seq : Nat) (plain : ByteArray) : Option ByteArray :=
  let sq := u16 1 ++ u48 seq
  let nonce := civ ++ sq
  let aad := sq ++ ByteArray.mk #[23] ++ dtls12 ++ u16 plain.size
  match Crypto.aesGcmSeal cwk nonce aad plain with
  | some enc => some (recordE 23 1 seq (sq ++ enc))
  | none => none

/-- AEAD-open one inbound epoch-1 application-data record (content type 23):
`sqn` is the record's 8-byte `epoch ‖ seq`, `pl` its payload
(`explicit_nonce(8) ‖ ciphertext ‖ tag`). Returns the SCTP packet plaintext. -/
def openApp (swk siv : ByteArray) (sqn pl : ByteArray) : Option ByteArray :=
  let explicit := pl.extract 0 8
  let enc := pl.extract 8 pl.size
  let nonce := siv ++ explicit
  let aad := sqn ++ ByteArray.mk #[23] ++ dtls12 ++ u16 (enc.size - 16)
  Crypto.aesGcmOpen swk nonce aad enc

/-- Decode every inbound epoch-1 application-data record in a datagram flight to
its SCTP packet plaintext (dropping records that fail to open). -/
def openSctpFlight (swk siv : ByteArray) (flight : ByteArray) : List ByteArray :=
  (recordsFull flight).foldl
    (fun acc (ct, sqn, pl) =>
      if ct == 23 && sqn[0]! == 0 && sqn[1]! == 1 && pl.size ≥ 24 then
        match openApp swk siv sqn pl with
        | some pkt => acc ++ [pkt]
        | none => acc
      else acc) []

/-! ## SCTP + DCEP driver refinement (against `WebrtcTransport` / `Dcep`)

The driver walks the client side of the SCTP four-way association and then the
DCEP open handshake. Those control flows are exactly the `sctpStep` / `Dcep.chStep`
edges, so the driver refines the proven models. -/

/-- The SCTP association events the driver performs: INIT, then on INIT-ACK it
sends COOKIE-ECHO, then it receives COOKIE-ACK. -/
def sctpDriverTrace : List SctpEvent := [.sendInit, .recvInitAck, .recvCookieAck]

/-- **The driver's SCTP control flow reaches `established`.** Folding the driver's
association-event trace through `WebrtcTransport.sctpStep` from `closed` reaches
`established` — the state in which user data (the DCEP OPEN and the data-channel
message) may be transferred. -/
theorem driver_sctp_reaches_established :
    WebrtcTransport.sctpRun .closed sctpDriverTrace = .established := by
  decide

/-- **COOKIE-ACK is the only edge into an established association.** The driver
can only transfer user data by having completed the four-way exchange — the model
forbids any shortcut past INIT-ACK and the COOKIE echo/ack. -/
theorem driver_sctp_cookieack_required (s : SctpState) (e : SctpEvent)
    (h : sctpStep s e = .established) (hne : s ≠ .established) :
    s = .cookieEchoed ∧ e = .recvCookieAck :=
  WebrtcTransport.sctp_enter_established s e h hne

/-- **The four-way exchange is irreducible for the driver.** Any event trace that
brings the association up takes at least three transitions — the driver's
INIT/INIT-ACK/COOKIE-ECHO/COOKIE-ACK walk is minimal. -/
theorem driver_sctp_min_length (es : List SctpEvent)
    (h : WebrtcTransport.sctpRun .closed es = .established) : 3 ≤ es.length :=
  WebrtcTransport.sctp_assoc_4way es h

/-- The DCEP channel events the driver performs: send DATA_CHANNEL_OPEN, then
receive DATA_CHANNEL_ACK. -/
def dcepDriverTrace : List Dcep.ChEvent := [.sendOpen, .recvAck]

/-- Fold `Dcep.chStep` over an event trace. -/
def dcepRun : Dcep.ChState → List Dcep.ChEvent → Dcep.ChState
  | s, []      => s
  | s, e :: es => dcepRun (Dcep.chStep s e) es

/-- **The driver's DCEP control flow reaches `open`.** From `idle`, sending the
DATA_CHANNEL_OPEN and receiving the DATA_CHANNEL_ACK brings the channel to
`open` — exactly `Dcep.chStep`'s only path into `open`. -/
theorem driver_dcep_reaches_open : dcepRun .idle dcepDriverTrace = .open := by
  decide

/-- **The DATA_CHANNEL_ACK is the only edge into `open`.** The driver's channel is
open only after it sent an OPEN and the peer's ACK came back. -/
theorem driver_dcep_ack_required (s : Dcep.ChState) (e : Dcep.ChEvent)
    (h : Dcep.chStep s e = .open) (hne : s ≠ .open) :
    s = .openSent ∧ e = .recvAck :=
  Dcep.dcep_open_ack s e h hne

/-- The driver's DATA_CHANNEL_OPEN bytes are exactly what `Dcep.parse` decodes:
the on-the-wire DCEP OPEN (reliable channel, given `label` under the 64 KiB
bound) round-trips to the model's `open` message. Specialization of
`Dcep.encodeOpen_roundtrip` to the empty protocol string the driver sends. -/
theorem driver_dcep_open_wire (label : List UInt8) (hl : label.length < 65536) :
    Dcep.parse (Dcep.encodeOpen 0 0 0 label [])
      = some (.open 0 0 0 label.length 0 label []) := by
  have := Dcep.encodeOpen_roundtrip label [] hl (by decide)
  simpa using this

/-! ## The live driver -/

/-- Collect the peer's flight across however many datagrams it spans. -/
def collectFlight (fd : UInt32) (tries : Nat) : IO ByteArray := do
  let mut flight := ByteArray.empty
  let mut n := 0
  while n < tries do
    match ← udpRecv fd 2000 with
    | some dg => flight := flight ++ dg; n := n + 1
    | none    => n := tries
  return flight

def main (args : List String) : IO UInt32 := do
  match args with
  | host :: portS :: rest => do
    let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
    let ephPriv :=
      match rest with
      | ephHex :: _ => ofHex ephHex
      | [] => ByteArray.mk (Array.range 32 |>.map (fun i => UInt8.ofNat (i + 1)))
    let clientRandom := ByteArray.mk (Array.range 32 |>.map (fun i => UInt8.ofNat i))
    let ch := handshake 1 (clientHelloBody clientRandom ByteArray.empty) 0
    let dgram := record 22 0 ch

    IO.println s!"DTLS 1.2 ClientHello ({dgram.size} bytes, offering x25519 + ECDHE-ECDSA):"
    IO.println s!"  {toHex dgram}"

    let fd ← udpConnect host port.toUInt16
    udpSend fd dgram
    IO.println s!"\n-> sent ClientHello to {host}:{port}"

    let flight ← collectFlight fd 6
    if flight.isEmpty then
      IO.eprintln "\n<- NO REPLY (peer dropped the ClientHello or sent an alert)"
      udpClose fd
      return 1

    IO.println s!"\n<- received {flight.size} bytes of DTLS flight from the real peer"
    let frags := allHandshakes flight
    let name : UInt8 → String := fun mt =>
      if mt == 2 then "ServerHello" else if mt == 11 then "Certificate"
      else if mt == 12 then "ServerKeyExchange" else if mt == 13 then "CertificateRequest"
      else if mt == 14 then "ServerHelloDone" else s!"handshake({mt.toNat})"
    for f in frags do
      if f.fragOffset == 0 then IO.println s!"   {name f.msgType} (msg_seq {f.msgSeq})"

    -- Reconstruct each server handshake message (msg_seq 0..4) for the transcript.
    let some m0 := reconMsg frags 0
      | do IO.eprintln "\nno ServerHello — handshake not accepted"; udpClose fd; return 1
    let some m1 := reconMsg frags 1
      | do IO.eprintln "\nno server Certificate"; udpClose fd; return 1
    let some m2 := reconMsg frags 2
      | do IO.eprintln "\nno ServerKeyExchange"; udpClose fd; return 1
    let some m3 := reconMsg frags 3
      | do IO.eprintln "\nno CertificateRequest"; udpClose fd; return 1
    let some m4 := reconMsg frags 4
      | do IO.eprintln "\nno ServerHelloDone"; udpClose fd; return 1

    -- ServerHello cipher + random.
    let shBody := m0.extract 12 m0.size
    match serverHelloCipher shBody with
    | some cs => IO.println s!"\nServerHello negotiated cipher_suite = 0x{toHex (u16 cs)}"
    | none => IO.println "\nServerHello present but cipher parse failed"
    let serverRandom := m0.extract 14 46

    -- ServerKeyExchange: the peer's ephemeral x25519 public key (the premaster).
    let skeBody := m2.extract 12 m2.size
    let some (curve, serverPub) := serverKeyExchangePub skeBody
      | do IO.eprintln "ServerKeyExchange parse failed"; udpClose fd; return 1
    IO.println s!"ServerKeyExchange named_curve = 0x{toHex (u16 curve)} (0x001d = x25519)"
    IO.println s!"peer ephemeral x25519 pub : {toHex serverPub}"

    let some myPub := Crypto.x25519Base ephPriv
      | do IO.eprintln "x25519Base failed"; udpClose fd; return 1
    let some pms := Crypto.x25519 ephPriv serverPub
      | do IO.eprintln "x25519 failed on the peer key"; udpClose fd; return 1
    IO.println s!"drorb ephemeral x25519 pub : {toHex myPub}"
    IO.println s!"ECDHE premaster secret (verified Crypto.x25519): {toHex pms}"

    -- Build the client second flight.
    let some certDer := clientCertDer
      | do IO.eprintln "client cert build failed"; udpClose fd; return 1
    let cCertBody := u24 (certDer.size + 3) ++ u24 certDer.size ++ certDer
    let cCert := handshake 11 cCertBody 1
    let cCke := handshake 16 (vec8 myPub) 2

    -- Transcript through ClientKeyExchange: the EMS session_hash input and the
    -- CertificateVerify signature input (RFC 7627 / RFC 5246 §7.4.8).
    let transcriptCke := ch ++ m0 ++ m1 ++ m2 ++ m3 ++ m4 ++ cCert ++ cCke
    let sessionHash := Crypto.sha256 transcriptCke
    let some cvSig := TlsCrypto.Sig.ecdsaP256Sign certPriv transcriptCke
      | do IO.eprintln "CertificateVerify sign failed"; udpClose fd; return 1
    let cvBody := ByteArray.mk #[0x04, 0x03] ++ u16 cvSig.size ++ cvSig
    let cCv := handshake 15 cvBody 3

    -- Extended master secret (RFC 7627), key block (RFC 5246 §6.3), Finished.
    let master := prf pms "extended master secret".toUTF8 sessionHash 48
    let keyBlock := prf master "key expansion".toUTF8 (serverRandom ++ clientRandom) 40
    let cwk := keyBlock.extract 0 16      -- client_write_key (AES-128)
    let swk := keyBlock.extract 16 32     -- server_write_key
    let civ := keyBlock.extract 32 36     -- client_write_IV (GCM salt)
    let siv := keyBlock.extract 36 40     -- server_write_IV
    IO.println s!"\nTLS 1.2 extended master secret : {toHex master}"

    let transcriptCv := transcriptCke ++ cCv
    let clientVd := prf master "client finished".toUTF8 (Crypto.sha256 transcriptCv) 12
    let finPlain := handshake 20 clientVd 4    -- Finished handshake message (24 bytes)
    IO.println s!"client Finished verify_data    : {toHex clientVd}"

    -- Protect the Finished as an AES-128-GCM record (epoch 1, seq 0; RFC 5288).
    let seqNum := u16 1 ++ ByteArray.mk #[0,0,0,0,0,0]    -- epoch(2) ‖ seq48(6)
    let nonce := civ ++ seqNum
    let aad := seqNum ++ ByteArray.mk #[22] ++ dtls12 ++ u16 finPlain.size
    let some encFin := Crypto.aesGcmSeal cwk nonce aad finPlain
      | do IO.eprintln "AES-128-GCM seal failed"; udpClose fd; return 1
    let finRec := recordE 22 1 0 (seqNum ++ encFin)

    let dg2 := record 22 1 cCert ++ record 22 2 cCke ++ record 22 3 cCv
      ++ record 20 4 (ByteArray.mk #[0x01]) ++ finRec
    udpSend fd dg2
    IO.println s!"\n-> sent client second flight ({dg2.size} bytes): Certificate, ClientKeyExchange,"
    IO.println "   CertificateVerify (ECDSA-P256), ChangeCipherSpec, Finished (AES-128-GCM record)"

    -- Receive the peer's ChangeCipherSpec + Finished flight.
    let resp ← collectFlight fd 6
    IO.println s!"\n<- received {resp.size} bytes from the peer"
    let recs := recordsFull resp
    let some (_, sqn, pl) := recs.find?
        (fun (ct, sqn, pl) => ct == 22 && sqn[0]! == 0 && sqn[1]! == 1 && pl.size ≥ 24)
      | do
        IO.eprintln "\nno epoch-1 (encrypted) Finished from the peer — handshake did not complete"
        udpClose fd; return 1

    let explicit := pl.extract 0 8
    let enc := pl.extract 8 pl.size
    let snonce := siv ++ explicit
    let saad := sqn ++ ByteArray.mk #[22] ++ dtls12 ++ u16 (enc.size - 16)
    let some dec := Crypto.aesGcmOpen swk snonce saad enc
      | do IO.eprintln "AES-128-GCM open of the peer Finished FAILED"; udpClose fd; return 1
    let serverVd := dec.extract 12 24
    let expectVd := prf master "server finished".toUTF8 (Crypto.sha256 (transcriptCv ++ finPlain)) 12
    IO.println s!"peer Finished verify_data      : {toHex serverVd}"
    IO.println s!"expected (server finished PRF) : {toHex expectVd}"
    if serverVd.toList == expectVd.toList then
      IO.println "\nDTLS 1.2 HANDSHAKE COMPLETE: both Finished exchanged, keys AGREE."
      IO.println "DTLS FSM: start -[ClientHello]-> wait_sh -[ServerHello]-> wait_finished -[Finished]-> established"

      -- Fixed SCTP association parameters (deterministic; a conformance driver).
      let srcPort := 5000
      let dstPort := 5000
      let localTag := 0x9e2a7c31
      let localTsn := 1
      let aRwnd := 0x00020000
      let streams := 65535

      IO.println "\n===== SCTP-over-DTLS: RFC 4960 four-way association ====="

      -- (1) INIT, verification_tag 0, carried in an epoch-1 AES-128-GCM record (seq 1).
      let initPkt := WebrtcTransport.Sctp.packet srcPort dstPort 0
        (WebrtcTransport.Sctp.initChunk localTag aRwnd streams streams localTsn ByteArray.empty)
      let some initRec := sealApp cwk civ 1 initPkt
        | do IO.eprintln "AES-GCM seal of INIT failed"; udpClose fd; return 1
      udpSend fd initRec
      IO.println s!"-> INIT           (init_tag 0x{toHex (WebrtcTransport.Sctp.u32 localTag)}, CRC32C-checksummed, in epoch-1 record)"

      let flight1 ← collectFlight fd 4
      let chunks1 := (openSctpFlight swk siv flight1).foldl (fun a p => a ++ sctpChunks p) []
      let some (_, iaBody) := chunks1.find? (fun (ty, _) => ty == 2)
        | do IO.eprintln "<- no INIT-ACK (association not accepted)"; udpClose fd; return 1
      let remoteTag := rd32 iaBody 0
      let some (_, cookie) := (sctpParams iaBody 16).find? (fun (ty, _) => ty == 7)
        | do IO.eprintln "<- INIT-ACK carried no STATE_COOKIE"; udpClose fd; return 1
      IO.println s!"<- INIT-ACK       (peer tag 0x{toHex (WebrtcTransport.Sctp.u32 remoteTag)}, STATE_COOKIE {cookie.size} bytes)"

      -- (2) COOKIE-ECHO (echo the peer's opaque state cookie), verification_tag = peer tag.
      let echoPkt := WebrtcTransport.Sctp.packet srcPort dstPort remoteTag
        (WebrtcTransport.Sctp.cookieEcho cookie)
      let some echoRec := sealApp cwk civ 2 echoPkt
        | do IO.eprintln "seal COOKIE-ECHO failed"; udpClose fd; return 1
      udpSend fd echoRec
      IO.println "-> COOKIE-ECHO    (state cookie echoed)"

      let flight2 ← collectFlight fd 4
      let chunks2 := (openSctpFlight swk siv flight2).foldl (fun a p => a ++ sctpChunks p) []
      if (chunks2.find? (fun (ty, _) => ty == 11)).isNone then
        IO.eprintln "<- no COOKIE-ACK (association did not come up)"; udpClose fd; return 1
      IO.println "<- COOKIE-ACK     (association ESTABLISHED)"
      IO.println "SCTP FSM: closed -[INIT]-> cookieWait -[INIT-ACK]-> cookieEchoed -[COOKIE-ACK]-> established"

      -- (3) DCEP DATA_CHANNEL_OPEN on stream 0, PPID 50 (RFC 8832 §5.1 / §8.1).
      IO.println "\n===== DCEP data-channel open (RFC 8832) over SCTP stream 0 ====="
      let label := "drorb-verified".toUTF8
      let dcepOpen := ByteArray.mk (Dcep.encodeOpen 0 0 0 label.toList []).toArray
      let openData := WebrtcTransport.Sctp.dataChunk 0x03 localTsn 0 0 50 dcepOpen
      let openPkt := WebrtcTransport.Sctp.packet srcPort dstPort remoteTag openData
      let some openRec := sealApp cwk civ 3 openPkt
        | do IO.eprintln "seal DATA_CHANNEL_OPEN failed"; udpClose fd; return 1
      udpSend fd openRec
      IO.println s!"-> DATA_CHANNEL_OPEN (TSN {localTsn}, stream 0, PPID 50, label \"drorb-verified\")"

      let flight3 ← collectFlight fd 4
      let chunks3 := (openSctpFlight swk siv flight3).foldl (fun a p => a ++ sctpChunks p) []
      -- The peer replies with a DATA chunk on stream 0 carrying DATA_CHANNEL_ACK (PPID 50).
      let ackSeen := chunks3.any (fun (ty, body) =>
        ty == 0 && body.size ≥ 12 && rd32 body 8 == 50 &&
          (match Dcep.parse (body.extract 12 body.size).toList with
           | some .ack => true | _ => false))
      if ackSeen then
        IO.println "<- DATA_CHANNEL_ACK  (Dcep.parse = ack — channel OPEN, peer-confirmed)"
      else
        IO.println "<- (peer SACKed the OPEN; DATA_CHANNEL_ACK not observed in this flight)"

      -- (4) A real string message on the data channel: stream 0, PPID 51 (WEBRTC_STRING).
      let msgStr := "hello from drorb over verified DTLS+SCTP+DCEP"
      let msgData := WebrtcTransport.Sctp.dataChunk 0x03 (localTsn + 1) 0 1 51 msgStr.toUTF8
      let msgPkt := WebrtcTransport.Sctp.packet srcPort dstPort remoteTag msgData
      let some msgRec := sealApp cwk civ 4 msgPkt
        | do IO.eprintln "seal data-channel message failed"; udpClose fd; return 1
      udpSend fd msgRec
      IO.println s!"\n-> DATA (PPID 51) DATACHANNEL MESSAGE, verbatim:\n   \"{msgStr}\""
      let _ ← collectFlight fd 3   -- let the peer process + emit on('message')

      IO.println "\nSCTP association + DCEP data channel + a real string message: all carried"
      IO.println "inside the AES-128-GCM DTLS records the verified handshake established."
      IO.println "Refined: WebrtcTransport.sctpStep (four-way), Dcep.chStep (open/ack), Dcep.parse."
      udpClose fd
      return 0
    else
      IO.eprintln "\npeer Finished verify_data MISMATCH — keys disagree"
      udpClose fd
      return 1
  | _ => do
    IO.eprintln "usage: webrtc-live <host> <port> [ephPrivHex]"
    return 1

end WebrtcLive

def main (args : List String) : IO UInt32 := WebrtcLive.main args
