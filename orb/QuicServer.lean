/-
# QuicServer — the QUIC v1 server transport (RFC 9000 / RFC 9001)

`IoQuic` decrypts a real off-the-shelf client's QUIC Initial (verified EverCrypt
AES-128-GCM AEAD under AES-ECB header protection) and recovers the TLS
ClientHello from its CRYPTO frames. That is the *receive* half. This module is
the *send* half and the connection machine: on a decrypted ClientHello it derives
the TLS 1.3 handshake secrets (X25519 DHE via `Crypto.x25519` + the
`TlsCrypto`/`TlsHandshake` key schedule) and emits the server's response flight
as real QUIC packets —

  * a **server Initial** packet carrying an ACK and the ServerHello in a CRYPTO
    frame, AEAD-protected under the server Initial keys (RFC 9001 §5.2), and
  * a **server Handshake** packet carrying EncryptedExtensions, Certificate,
    CertificateVerify and Finished in a CRYPTO frame, AEAD-protected under the
    server handshake keys —

coalesced into one UDP datagram (padded to 1200 bytes per RFC 9000 §14.1), both
header-protected exactly as a real server sends them (`QuicHeaderProt`). On the
client's Handshake-level Finished it verifies the client `verify_data`
(RFC 8446 §4.4.4), installs the 1-RTT (application) keys, and confirms with
HANDSHAKE_DONE; 1-RTT packets carrying H3 requests then drive the proven
`Reactor.QuicIngress.datagramServe`, and each response goes back in 1-RTT.

Beyond the minimal handshake, the transport now implements:

  * **ACK generation in every packet-number space** (RFC 9000 §13.2 / RFC 9002):
    received packet numbers are tracked per space and every ack-eliciting packet
    is answered with an ACK frame whose ranges encode exactly the tracked set
    (`ackRuns` — see `ackRuns_exact` below), so PING elicits an acknowledgement.
  * **Multiple connections per process** (RFC 9000 §5): a connection table keyed
    by the server-issued connection IDs, plus a pre-connection buffer that
    reassembles a ClientHello spanning several Initial packets/CRYPTO frames
    (RFC 9000 §7.5 — see `assembleFrom_exact` below).
  * **Version negotiation** (RFC 9000 §6): a long-header packet with an unknown
    version elicits a Version Negotiation packet echoing the client's CIDs.
  * **Connection ID issuance and rotation** (RFC 9000 §5.1.1): NEW_CONNECTION_ID
    frames are issued at handshake confirmation and short-header packets are
    routed by any issued CID, so a client-driven server-CID change keeps working.
  * **Key update** (RFC 9001 §6): a flipped key-phase bit re-derives both
    directions' AEAD keys from the `"quic ku"`-labelled next-generation secrets;
    the header-protection key is unchanged (`nextGenKeys_preserves_hp`).
  * **Path validation** (RFC 9000 §8.2): PATH_CHALLENGE frames are sent alongside
    responses to client activity and PATH_RESPONSE echoes are verified; a client
    PATH_CHALLENGE is answered with the mandatory PATH_RESPONSE. The UDP shell
    does not expose the peer address to this layer, so the path is (legally,
    §8.2.1) probed continuously rather than on an observed address change.
  * **Latency spin bit** (RFC 9000 §17.4): the server echoes the spin value of
    the highest-numbered received 1-RTT packet.
  * **Multiple request streams** (RFC 9000 §2): every client-initiated
    bidirectional stream carrying request bytes is answered on that stream.
  * **CONNECTION_CLOSE** (RFC 9000 §10.2): a received CONNECTION_CLOSE drops the
    connection from the table.
  * **Address validation by Retry** (RFC 9000 §8.1.2, RFC 9001 §5.8): a client
    Initial without a token is answered with a stateless Retry (integrity tag by
    the verified AEAD under the fixed v1 key); the tokened Initial recovers the
    original DCID from the token (`checkRetryToken_sound` below) and the
    handshake carries `original_destination_connection_id` +
    `retry_source_connection_id`.

Scope (named honestly): in-order stream reassembly only; no loss recovery /
retransmission / PTO timers (the receive loop has no timer source); no
session resumption / 0-RTT tickets; no idle-timeout teardown (closed connections
leave the table, idle ones age out only by table cap); 2-byte packet numbers on
the 1-RTT leg (65535 packets per connection); ChaCha20-Poly1305 for the
handshake and 1-RTT levels (the server selects `TLS_CHACHA20_POLY1305_SHA256`).
None of these touch the crypto: the AEAD, HKDF, X25519 and Ed25519 are the
verified EverCrypt primitives throughout.
-/
import Crypto
import TlsCrypto
import TlsHandshake
import QuicHeaderProt
import Reactor.Ingress
import Reactor.Quic
import Reactor.QuicIngress
import H3.Frame

namespace QuicServer

open Crypto TlsCrypto TlsHandshake

/-! ## (0) The packet-protection derivations, over the verified primitives.

Re-expressed here (as in `IoQuic`) rather than imported from `QuicTransport`,
whose trailing self-test `def main` would collide with the `orb-quic` exe's
`main`. Identical computation on identical EverCrypt. -/

/-- RFC 9001 §5.2 QUIC v1 Initial salt. -/
def initialSalt : ByteArray :=
  ByteArray.mk #[0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
                 0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a]

/-- One encryption level's packet-protection material. -/
structure PacketKeys where
  key : ByteArray
  iv : ByteArray
  hp : ByteArray

/-- `HKDF-Extract(initial_salt, DCID)` then the client/server Initial secret. -/
def initialSecretRaw (dcid : ByteArray) : Option ByteArray := hkdfExtract initialSalt dcid

def clientInitialSecret (dcid : ByteArray) : Option ByteArray :=
  (initialSecretRaw dcid).bind (fun s => expandLabel s "client in".toUTF8 ByteArray.empty 32)

def serverInitialSecret (dcid : ByteArray) : Option ByteArray :=
  (initialSecretRaw dcid).bind (fun s => expandLabel s "server in".toUTF8 ByteArray.empty 32)

/-- AES-128-GCM Initial keys (key 16, iv 12, hp 16) — RFC 9001 §5.2. -/
def deriveAesKeys (secret : ByteArray) : Option PacketKeys :=
  match expandLabel secret "quic key".toUTF8 ByteArray.empty 16,
        expandLabel secret "quic iv".toUTF8 ByteArray.empty 12,
        expandLabel secret "quic hp".toUTF8 ByteArray.empty 16 with
  | some k, some iv, some hp => some { key := k, iv := iv, hp := hp }
  | _, _, _ => none

/-- ChaCha20-Poly1305 packet keys (key 32, iv 12, hp 32) — the handshake and
1-RTT levels, since the server selects `TLS_CHACHA20_POLY1305_SHA256`. -/
def deriveChachaKeys (secret : ByteArray) : Option PacketKeys :=
  match expandLabel secret "quic key".toUTF8 ByteArray.empty 32,
        expandLabel secret "quic iv".toUTF8 ByteArray.empty 12,
        expandLabel secret "quic hp".toUTF8 ByteArray.empty 32 with
  | some k, some iv, some hp => some { key := k, iv := iv, hp := hp }
  | _, _, _ => none

def sealAes (pk : PacketKeys) (pn : Nat) (header payload : ByteArray) : Option ByteArray :=
  aesGcmSeal pk.key (recordNonce pk.iv pn) header payload
def openAes (pk : PacketKeys) (pn : Nat) (header ct : ByteArray) : Option ByteArray :=
  aesGcmOpen pk.key (recordNonce pk.iv pn) header ct
def sealCha (pk : PacketKeys) (pn : Nat) (header payload : ByteArray) : Option ByteArray :=
  chachaSeal pk.key (recordNonce pk.iv pn) header payload
def openCha (pk : PacketKeys) (pn : Nat) (header ct : ByteArray) : Option ByteArray :=
  chachaOpen pk.key (recordNonce pk.iv pn) header ct

/-- The next-generation traffic secret for a key update:
`HKDF-Expand-Label(secret, "quic ku", "", 32)` (RFC 9001 §6.1). -/
def nextGenSecret (s : ByteArray) : Option ByteArray :=
  expandLabel s "quic ku".toUTF8 ByteArray.empty 32

/-- Next-generation packet keys for a key update (RFC 9001 §6.1): the AEAD key
and IV are re-derived from the updated secret; the header-protection key is
**not** updated (see `nextGenKeys_preserves_hp`). Returns the new keys and the
new secret (the input to the following update). -/
def nextGenKeys (old : PacketKeys) (sec : ByteArray) : Option (PacketKeys × ByteArray) :=
  match nextGenSecret sec with
  | none => none
  | some s' =>
    match deriveChachaKeys s' with
    | none => none
    | some k => some ({ k with hp := old.hp }, s')

/-! ## (1) QUIC wire encoding helpers -/

/-- Encode a QUIC variable-length integer (RFC 9000 §16). -/
def encVarint (v : Nat) : ByteArray :=
  if v < 64 then ByteArray.mk #[UInt8.ofNat v]
  else if v < 16384 then
    ByteArray.mk #[UInt8.ofNat (0x40 ||| (v >>> 8)), UInt8.ofNat (v &&& 0xff)]
  else if v < 1073741824 then
    ByteArray.mk #[UInt8.ofNat (0x80 ||| (v >>> 24)), UInt8.ofNat ((v >>> 16) &&& 0xff),
                   UInt8.ofNat ((v >>> 8) &&& 0xff), UInt8.ofNat (v &&& 0xff)]
  else
    ByteArray.mk (((List.range 8).map (fun i => UInt8.ofNat ((v >>> ((7 - i) * 8)) &&& 0xff))).toArray)
      |>.set! 0 (UInt8.ofNat (0xc0 ||| ((v >>> 56) &&& 0x3f)))

/-- Read a QUIC varint (value, bytes consumed). -/
def readVarint (bs : List UInt8) : Option (Nat × Nat) :=
  match bs with
  | [] => none
  | b0 :: _ =>
    let len := 1 <<< (b0 >>> 6).toNat
    if bs.length < len then none
    else
      let first := (b0 &&& 0x3f).toNat
      let rest := (bs.drop 1).take (len - 1)
      some (rest.foldl (fun acc x => acc * 256 + x.toNat) first, len)

/-- `pnLen`-byte big-endian packet number. -/
def encPacketNumber (pn pnLen : Nat) : ByteArray :=
  ByteArray.mk (((List.range pnLen).map
    (fun i => UInt8.ofNat ((pn >>> ((pnLen - 1 - i) * 8)) &&& 0xff))).toArray)

/-- The 4-byte QUIC v1 version. -/
def version1 : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x01]

/-- Concatenate a list of byte strings. -/
def concatBAs (l : List ByteArray) : ByteArray := l.foldl (· ++ ·) ByteArray.empty

/-! ## (2) Received-packet-number tracking + ACK frame generation (RFC 9000 §13.2)

Received packet numbers are tracked per space as a strictly-descending list
(newest first, bounded window). The ACK frame encodes the tracked set as ranges;
`ackRuns` groups the list into maximal consecutive runs and `ackRuns_exact`
proves the runs decode back to exactly the tracked list, so the emitted ACK
acknowledges precisely the packets that were received. -/

/-- Insert `pn` into a strictly-descending list, keeping order; no-op if already
present. -/
def insertDesc (pn : Nat) : List Nat → List Nat
  | [] => [pn]
  | q :: r =>
    if q < pn then pn :: q :: r
    else if pn == q then q :: r
    else q :: insertDesc pn r

/-- Group a descending packet-number list into runs `(largest, smallest)` of
consecutive values — the range structure of an ACK frame (RFC 9000 §19.3.1). -/
def ackRuns : List Nat → List (Nat × Nat)
  | [] => []
  | p :: rest =>
    match ackRuns rest with
    | [] => [(p, p)]
    | (hi, lo) :: rs => if hi + 1 = p then (p, lo) :: rs else (p, p) :: (hi, lo) :: rs

/-- The ACK frame for a (descending, distinct) received-PN list: type `0x02`,
largest, delay 0, range count, first range, then `(gap, range)` pairs — RFC 9000
§19.3. Empty for an empty list. -/
def ackFrameOf (pns : List Nat) : ByteArray :=
  match ackRuns pns with
  | [] => ByteArray.empty
  | (hi, lo) :: rest =>
    let rec tail (prevLo : Nat) : List (Nat × Nat) → ByteArray
      | [] => ByteArray.empty
      | (h, l) :: rs => encVarint (prevLo - h - 2) ++ encVarint (h - l) ++ tail l rs
    ByteArray.mk #[0x02] ++ encVarint hi ++ encVarint 0 ++ encVarint rest.length
      ++ encVarint (hi - lo) ++ tail lo rest

/-! ## (3) Frames -/

/-- A CRYPTO frame (RFC 9000 §19.6): `0x06 ‖ offset ‖ length ‖ data`. -/
def cryptoFrame (offset : Nat) (data : ByteArray) : ByteArray :=
  ByteArray.mk #[0x06] ++ encVarint offset ++ encVarint data.size ++ data

/-- A STREAM frame (RFC 9000 §19.8) with explicit offset + length, FIN optional:
`0x0e|(fin) ‖ stream_id ‖ offset ‖ length ‖ data` (type 0x0e = OFF+LEN bits). -/
def streamFrame (sid offset : Nat) (fin : Bool) (data : ByteArray) : ByteArray :=
  let ty : UInt8 := if fin then 0x0f else 0x0e
  ByteArray.mk #[ty] ++ encVarint sid ++ encVarint offset ++ encVarint data.size ++ data

/-- The HANDSHAKE_DONE frame (RFC 9000 §19.20): `0x1e`. -/
def handshakeDoneFrame : ByteArray := ByteArray.mk #[0x1e]

/-- A PATH_CHALLENGE frame (RFC 9000 §19.17): `0x1a ‖ 8 bytes`. -/
def pathChallengeFrame (d : ByteArray) : ByteArray := ByteArray.mk #[0x1a] ++ d

/-- A PATH_RESPONSE frame (RFC 9000 §19.18): `0x1b ‖ the echoed 8 bytes`. -/
def pathResponseFrame (d : ByteArray) : ByteArray := ByteArray.mk #[0x1b] ++ d

/-- A NEW_CONNECTION_ID frame (RFC 9000 §19.15):
`0x18 ‖ seq ‖ retire_prior_to=0 ‖ len ‖ cid ‖ reset token (16)`. -/
def newCidFrame (seq : Nat) (cid token : ByteArray) : ByteArray :=
  ByteArray.mk #[0x18] ++ encVarint seq ++ encVarint 0
    ++ ByteArray.mk #[UInt8.ofNat cid.size] ++ cid ++ token

/-! ### The received-frame walker (RFC 9000 §19)

A decrypted payload is a sequence of frames; the server must walk **all** of
them (a PING after a NEW_CONNECTION_ID must still elicit an ACK). The walker
recognizes every frame type a v1 client sends, extracts the ones the server
acts on, and skips the rest field-accurately. -/

inductive Fr where
  | ping
  | ack
  | crypto (off : Nat) (data : List UInt8)
  | stream (sid off : Nat) (fin : Bool) (data : List UInt8)
  | pathChallenge (data : List UInt8)
  | pathResponse (data : List UInt8)
  | retireCid (seq : Nat)
  | close
  | handshakeDone
  | skipped                    -- recognized, acted on only by ACKing
  | unknown                    -- unrecognized: the walk stops
  deriving Repr, BEq

/-- Skip `n` varints. -/
def skipVs : Nat → List UInt8 → Option (List UInt8)
  | 0, l => some l
  | n + 1, l =>
    match readVarint l with
    | some (_, k) => skipVs n (l.drop k)
    | none => none

/-- Parse one frame given its (consumed) type byte, returning the frame and the
remaining bytes. `none` on a malformed frame. -/
def frameStep (b : UInt8) (r : List UInt8) : Option (Fr × List UInt8) :=
  if b == 0x01 then some (.ping, r)
  else if b == 0x02 || b == 0x03 then do   -- ACK (0x03: +3 ECN counts)
    let (_, k1) ← readVarint r                       -- largest
    let r1 := r.drop k1
    let (_, k2) ← readVarint r1                      -- delay
    let r2 := r1.drop k2
    let (cnt, k3) ← readVarint r2                    -- range count
    let r3 := r2.drop k3
    let (_, k4) ← readVarint r3                      -- first range
    let r4 ← skipVs (2 * cnt) (r3.drop k4)
    let r5 ← if b == 0x03 then skipVs 3 r4 else some r4
    some (.ack, r5)
  else if b == 0x04 then (skipVs 3 r).map ((.skipped, ·))      -- RESET_STREAM
  else if b == 0x05 then (skipVs 2 r).map ((.skipped, ·))      -- STOP_SENDING
  else if b == 0x06 then do                                     -- CRYPTO
    let (off, k1) ← readVarint r
    let (len, k2) ← readVarint (r.drop k1)
    let d := (r.drop (k1 + k2)).take len
    if d.length != len then none
    else some (.crypto off d, r.drop (k1 + k2 + len))
  else if b == 0x07 then do                                     -- NEW_TOKEN
    let (len, k) ← readVarint r
    some (.skipped, r.drop (k + len))
  else if (b &&& 0xF8) == 0x08 then do                          -- STREAM
    let (sid, k1) ← readVarint r
    let hasOff := (b &&& 0x04) != 0
    let hasLen := (b &&& 0x02) != 0
    let fin := (b &&& 0x01) != 0
    let (off, k2) ← if hasOff then readVarint (r.drop k1) else some (0, 0)
    let r2 := r.drop (k1 + k2)
    if hasLen then do
      let (len, k3) ← readVarint r2
      let d := (r2.drop k3).take len
      if d.length != len then none
      else some (.stream sid off fin d, r2.drop (k3 + len))
    else some (.stream sid off fin r2, [])
  else if b == 0x10 then (skipVs 1 r).map ((.skipped, ·))       -- MAX_DATA
  else if b == 0x11 then (skipVs 2 r).map ((.skipped, ·))       -- MAX_STREAM_DATA
  else if b == 0x12 || b == 0x13 || b == 0x14 then (skipVs 1 r).map ((.skipped, ·))
  else if b == 0x15 then (skipVs 2 r).map ((.skipped, ·))       -- STREAM_DATA_BLOCKED
  else if b == 0x16 || b == 0x17 then (skipVs 1 r).map ((.skipped, ·))
  else if b == 0x18 then do                                     -- NEW_CONNECTION_ID
    let (_, k1) ← readVarint r
    let (_, k2) ← readVarint (r.drop k1)
    match r.drop (k1 + k2) with
    | [] => none
    | lenB :: rest =>
      let cl := lenB.toNat
      if rest.length < cl + 16 then none else some (.skipped, rest.drop (cl + 16))
  else if b == 0x19 then do                                     -- RETIRE_CONNECTION_ID
    let (seq, k) ← readVarint r
    some (.retireCid seq, r.drop k)
  else if b == 0x1a then
    if r.length < 8 then none else some (.pathChallenge (r.take 8), r.drop 8)
  else if b == 0x1b then
    if r.length < 8 then none else some (.pathResponse (r.take 8), r.drop 8)
  else if b == 0x1c then do                                     -- CONNECTION_CLOSE (transport)
    let (_, k1) ← readVarint r
    let (_, k2) ← readVarint (r.drop k1)
    let (rl, k3) ← readVarint (r.drop (k1 + k2))
    some (.close, r.drop (k1 + k2 + k3 + rl))
  else if b == 0x1d then do                                     -- CONNECTION_CLOSE (application)
    let (_, k1) ← readVarint r
    let (rl, k2) ← readVarint (r.drop k1)
    some (.close, r.drop (k1 + k2 + rl))
  else if b == 0x1e then some (.handshakeDone, r)
  else if b == 0x30 then some (.skipped, [])                    -- DATAGRAM, no length
  else if b == 0x31 then do                                     -- DATAGRAM with length
    let (len, k) ← readVarint r
    some (.skipped, r.drop (k + len))
  else none

/-- Walk all frames of a decrypted payload (PADDING collapsed away). -/
def parseFrames : Nat → List UInt8 → List Fr
  | 0, _ => []
  | _, [] => []
  | fuel + 1, 0x00 :: r => parseFrames fuel r      -- PADDING
  | fuel + 1, b :: r =>
    match frameStep b r with
    | some (f, rest) => f :: parseFrames fuel rest
    | none => [.unknown]

/-- Whether a frame list makes its packet ack-eliciting (RFC 9000 §13.2:
everything except ACK, PADDING and CONNECTION_CLOSE). An unparsable tail counts
as eliciting — the packet authenticated, so acknowledging it is always sound. -/
def ackEliciting (frs : List Fr) : Bool :=
  frs.any fun f =>
    match f with
    | .ack | .close => false
    | _ => true

/-! ## (4) CRYPTO reassembly (RFC 9000 §7.5)

A ClientHello may span several CRYPTO frames across several Initial packets
(e.g. a padded post-quantum-sized hello). Segments are collected keyed by
offset and the contiguous prefix from offset 0 is reassembled;
`assembleFrom_exact` proves the reassembly reconstructs the original stream
from its segments in **any** arrival order. -/

/-- Record a segment (first frame at a given offset wins; empties dropped). -/
def insSeg (segs : List (Nat × List UInt8)) (off : Nat) (d : List UInt8) :
    List (Nat × List UInt8) :=
  if d.isEmpty || segs.any (·.1 == off) then segs else (off, d) :: segs

/-- Assemble the contiguous byte stream from offset `pos`: repeatedly append the
segment starting exactly at the cursor. `fuel` bounds the number of segments
consumed. -/
def assembleFrom (segs : List (Nat × List UInt8)) : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, pos =>
    match segs.find? (fun s => s.1 == pos) with
    | some (_, d) => d ++ assembleFrom segs fuel (pos + d.length)
    | none => []

/-- The complete TLS handshake message at the front of an assembled crypto
stream, if fully present: `type(1) ‖ uint24 len ‖ body`. -/
def completeHsMsg (assembled : List UInt8) : Option (List UInt8) :=
  match assembled with
  | t :: l1 :: l2 :: l3 :: _ =>
    let len := l1.toNat * 65536 + l2.toNat * 256 + l3.toNat
    if t == 0x01 && assembled.length ≥ 4 + len then some (assembled.take (4 + len))
    else none
  | _ => none

/-! ## (5) Packet assembly + protection -/

/-- Long-header type bits in the first byte: Initial = 0x00, Handshake = 0x20. -/
def tInitial : UInt8 := 0x00
def tHandshake : UInt8 := 0x20

/-- Build a protected long-header packet. `aes` selects the Initial cipher
(AES-128-GCM + AES header protection); otherwise ChaCha20-Poly1305 + ChaCha20 HP
(handshake level). `payload` is the frame bytes; the AEAD tag is added by the
seal. Header protection (RFC 9001 §5.4) is applied last. `none` on any crypto
size failure. Uses a 1-byte packet number. -/
def buildLongPacket (typeBits : UInt8) (isInitial aes : Bool)
    (dcid scid : ByteArray) (pn : Nat) (payload : ByteArray) (pk : PacketKeys) :
    Option ByteArray :=
  let pnLen := 1
  let firstByte : UInt8 := 0xC0 ||| typeBits ||| UInt8.ofNat (pnLen - 1)
  let pnBytes := encPacketNumber pn pnLen
  let ctLen := payload.size + 16
  let lengthField := pnLen + ctLen
  let tokenPart : ByteArray := if isInitial then encVarint 0 else ByteArray.empty
  let header :=
    ByteArray.mk #[firstByte] ++ version1
      ++ ByteArray.mk #[UInt8.ofNat dcid.size] ++ dcid
      ++ ByteArray.mk #[UInt8.ofNat scid.size] ++ scid
      ++ tokenPart ++ encVarint lengthField ++ pnBytes
  let sealed := if aes then sealAes pk pn header payload else sealCha pk pn header payload
  match sealed with
  | none => none
  | some ct =>
    let full := header.toList ++ ct.toList
    let pnOff := header.size - pnLen
    let masked := if aes then QuicHeaderProt.maskHeaderAes full pnOff pnLen pk.hp
                  else QuicHeaderProt.maskHeader full pnOff pnLen pk.hp
    masked.map (fun m => ⟨m.toArray⟩)

/-! ### Short-header header protection (RFC 9001 §5.4.1)

`QuicHeaderProt.maskHeader`/`removeHp` mask the low **4** bits of the first byte —
correct for LONG headers (2 reserved + 2 pn-length bits). A SHORT header instead
masks the low **5** bits (1 key-phase + 2 reserved + 2 pn-length). So a 1-RTT
packet needs its own apply/remove that XORs the first byte under `& 0x1f`; the
pn-byte masking is identical. Both use `QuicHeaderProt.chachaHpMask`. -/

/-- Apply/remove short-header header protection (XOR is self-inverse). -/
def applyHpShort (full : List UInt8) (pnOff pnLen : Nat) (hpKey : ByteArray) :
    Option (List UInt8) :=
  let sample := (full.drop (pnOff + 4)).take 16
  match QuicHeaderProt.chachaHpMask hpKey ⟨sample.toArray⟩ with
  | none => none
  | some mask =>
    let m := mask.toList
    let fb := (full.getD 0 0) ^^^ ((m.getD 0 0) &&& 0x1f)   -- SHORT: low 5 bits
    let full1 := full.set 0 fb
    let full2 := (List.range pnLen).foldl
      (fun acc i => acc.set (pnOff + i) ((acc.getD (pnOff + i) 0) ^^^ (m.getD (1 + i) 0))) full1
    some full2

/-- Remove short-header header protection, recovering pnLen / pn / the AAD. -/
def removeHpShort (pkt : List UInt8) (pnOff : Nat) (hpKey : ByteArray) (expectedPn : Nat) :
    Option QuicHeaderProt.Unprotected :=
  let sample := (pkt.drop (pnOff + 4)).take 16
  match QuicHeaderProt.chachaHpMask hpKey ⟨sample.toArray⟩ with
  | none => none
  | some mask =>
    let m := mask.toList
    let fb := (pkt.getD 0 0) ^^^ ((m.getD 0 0) &&& 0x1f)    -- SHORT: low 5 bits
    let pnLen := (fb &&& 0x03).toNat + 1
    let rawPn := (pkt.drop pnOff).take pnLen
    if rawPn.length ≠ pnLen then none else
    let unPn := (List.range pnLen).map (fun i => (rawPn.getD i 0) ^^^ (m.getD (1 + i) 0))
    let truncated := unPn.foldl (fun a x => a * 256 + x.toNat) 0
    let pn := QuicHeaderProt.decodePacketNumber truncated pnLen expectedPn
    let hdr := ((pkt.take pnOff).set 0 fb) ++ unPn
    some { firstByte := fb, pnLen := pnLen, pn := pn, header := ⟨hdr.toArray⟩ }

/-- Build a protected short-header (1-RTT) packet (RFC 9000 §17.3): first byte
`0b010K_S0pp` (K = key phase, S = spin), DCID (no length prefix), a 2-byte packet
number, then the ChaCha20-Poly1305 protected payload; ChaCha20 header protection
applied last. -/
def buildShortPacket (dcid : ByteArray) (pn : Nat) (spin keyPhase : Bool)
    (payload0 : ByteArray) (pk : PacketKeys) : Option ByteArray :=
  let pnLen := 2
  -- Header protection samples 16 bytes at `pnOff + 4` (RFC 9001 §5.4.2); pad the
  -- payload with PADDING frames (0x00) so a short packet is always long enough.
  let payload := if payload0.size < 4 then
      payload0 ++ ByteArray.mk (Array.mkArray (4 - payload0.size) 0) else payload0
  let firstByte : UInt8 := 0x40
    ||| (if spin then 0x20 else 0x00)
    ||| (if keyPhase then 0x04 else 0x00)
    ||| UInt8.ofNat (pnLen - 1)
  let pnBytes := encPacketNumber pn pnLen
  let header := ByteArray.mk #[firstByte] ++ dcid ++ pnBytes
  match sealCha pk pn header payload with
  | none => none
  | some ct =>
    let full := header.toList ++ ct.toList
    let pnOff := header.size - pnLen
    (applyHpShort full pnOff pnLen pk.hp).map (fun m => ⟨m.toArray⟩)

/-! ## (6) Parsing received packets (locate boundaries, then decrypt) -/

/-- The kind of a received QUIC packet, by its (still header-protected) first
byte and long-header type. -/
inductive PktKind where
  | initial | handshake | short | other
  deriving DecidableEq, Repr

def classify (firstByte : UInt8) : PktKind :=
  if (firstByte &&& 0x80) == 0 then .short
  else
    let ty := (firstByte >>> 4) &&& 0x03
    if ty == 0 then .initial
    else if ty == 2 then .handshake
    else .other

/-- A located long-header packet: its kind, DCID, SCID, the offset of the
packet-number field, and the total on-wire length of this packet (so a coalesced
datagram can be split). -/
structure LocLong where
  kind : PktKind
  dcid : ByteArray
  scid : ByteArray
  pnOff : Nat
  total : Nat        -- bytes from packet start to end of this packet

/-- Locate a long-header packet at the front of `bs` (RFC 9000 §17.2). Reads the
in-the-clear fields (type, DCID, SCID, token, Length) — the packet number and
payload stay header-protected. -/
def locateLong (bs : List UInt8) : Option LocLong :=
  match bs[0]? with
  | none => none
  | some b0 =>
    let kind := classify b0
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
        let scidStart := scidLenOff + 1
        let scid := (bs.drop scidStart).take scidLen
        let afterScid := scidStart + scidLen
        -- Initial has a token; Handshake does not.
        let afterToken :=
          if kind == .initial then
            match readVarint (bs.drop afterScid) with
            | some (tokLen, tb) => afterScid + tb + tokLen
            | none => afterScid
          else afterScid
        match readVarint (bs.drop afterToken) with
        | none => none
        | some (lenField, lb) =>
          let pnOff := afterToken + lb
          some { kind := kind, dcid := ⟨dcid.toArray⟩, scid := ⟨scid.toArray⟩,
                 pnOff := pnOff, total := pnOff + lenField }

/-- Remove header protection (ChaCha20) and decrypt a long-header packet whose
bytes are `pkt` (exactly `total` long) with the given keys, returning
`(pn, plaintext)`. `expectedPn` seeds the truncated-PN decode. -/
def openLongCha (pkt : List UInt8) (pnOff : Nat) (pk : PacketKeys) (expectedPn : Nat) :
    Option (Nat × ByteArray) :=
  match QuicHeaderProt.removeHp pkt pnOff pk.hp expectedPn with
  | none => none
  | some up =>
    let ct : ByteArray := ⟨(pkt.drop (pnOff + up.pnLen)).toArray⟩
    (openCha pk up.pn up.header ct).map (fun pt => (up.pn, pt))

/-! ## (7) Splitting a received datagram into its coalesced packets -/

/-- Split a UDP datagram into its coalesced QUIC packets (RFC 9000 §12.2). Long
headers carry a Length so their extent is known in the clear; a short header (or
an all-zero PADDING tail) runs to the end. `fuel` bounds the coalescing depth. -/
def splitPackets : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, bs =>
    match bs[0]? with
    | none => []
    | some b0 =>
      if (b0 &&& 0x80) == 0 then [bs]          -- short header: rest is one packet
      else if b0 == 0x00 then []               -- PADDING tail after last packet
      else
        match locateLong bs with
        | none => [bs]
        | some loc =>
          if loc.total == 0 || loc.total > bs.length then [bs]
          else (bs.take loc.total) :: splitPackets fuel (bs.drop loc.total)

/-! ## (8) The server's static parameters (ephemeral key, random, certificate) -/

/-- The `quic_transport_parameters` extension body (RFC 9000 §18): the minimal
set a real client validates — `original_destination_connection_id` (0x00),
`initial_source_connection_id` (0x0f) and, after a Retry,
`retry_source_connection_id` (0x10) — plus generous stream/data limits so the
H3 request streams are permitted. Each parameter is `id ‖ length ‖ value`
(varints). -/
def transportParams (odcid sscid : ByteArray) (retryScid : Option ByteArray) : ByteArray :=
  let p (id : Nat) (v : ByteArray) : ByteArray := encVarint id ++ encVarint v.size ++ v
  let pInt (id v : Nat) : ByteArray := encVarint id ++ encVarint (encVarint v).size ++ encVarint v
  p 0x00 odcid
    ++ p 0x0f sscid
    ++ (match retryScid with | some r => p 0x10 r | none => ByteArray.empty)
    ++ pInt 0x04 1048576      -- initial_max_data
    ++ pInt 0x05 1048576      -- initial_max_stream_data_bidi_local
    ++ pInt 0x06 1048576      -- initial_max_stream_data_bidi_remote
    ++ pInt 0x07 1048576      -- initial_max_stream_data_uni
    ++ pInt 0x08 128          -- initial_max_streams_bidi
    ++ pInt 0x09 128          -- initial_max_streams_uni
    ++ pInt 0x01 30000        -- max_idle_timeout (ms)
    ++ pInt 0x0e 4            -- active_connection_id_limit

/-- The client's offered ALPN protocol names (RFC 7301), from the raw
ClientHello handshake-message bytes. -/
def chAlpns (chMsg : List UInt8) : List (List UInt8) :=
  let go : Option (List (List UInt8)) := do
    -- msg hdr (4) ‖ version (2) ‖ random (32) ‖ session_id<u8> ‖ suites<u16> ‖
    -- compression<u8> ‖ extensions<u16>
    let r0 := chMsg.drop (4 + 2 + 32)
    let sidLen ← r0[0]?
    let r1 := r0.drop (1 + sidLen.toNat)
    let (csLen, _) ← TlsHandshake.rd16 r1
    let r2 := r1.drop (2 + csLen)
    let compLen ← r2[0]?
    let r3 := r2.drop (1 + compLen.toNat)
    let (extLen, _) ← TlsHandshake.rd16 r3
    let extBytes := (r3.drop 2).take extLen
    let exts := TlsHandshake.walkExts extBytes.length extBytes
    let alpnBody ← TlsHandshake.extBody exts 0x0010
    let (_, entries0) ← TlsHandshake.rd16 alpnBody
    let rec names : Nat → List UInt8 → List (List UInt8)
      | 0, _ => []
      | _, [] => []
      | fuel + 1, len :: rest =>
        (rest.take len.toNat) :: names fuel (rest.drop len.toNat)
    some (names entries0.length entries0)
  go.getD []

/-- The server's ALPN selection: `h3` when offered, else the client's first
offer, else `h3`. -/
def chooseAlpn (chMsg : List UInt8) : ByteArray :=
  let names := chAlpns chMsg
  let h3 := "h3".toUTF8.toList
  if names.isEmpty || names.contains h3 then "h3".toUTF8
  else ⟨(names.headD h3).toArray⟩

/-- EncryptedExtensions carrying the ALPN selection and the QUIC transport
parameters (extension type 0x0039). This is the QUIC-specific EE the empty
`TlsHandshake.buildEncryptedExtensions` lacked. -/
def buildEncryptedExtensionsQuic (odcid sscid alpn : ByteArray)
    (retryScid : Option ByteArray) : ByteArray :=
  let alpnList := vec8 alpn                     -- ProtocolName ‖…
  let alpnExt := u16 0x0010 ++ vec16 (vec16 alpnList)
  let tp := transportParams odcid sscid retryScid
  let tpExt := u16 0x0039 ++ vec16 tp
  hsMsg 8 (vec16 (alpnExt ++ tpExt))

/-- The server's fixed ephemeral X25519 private key (demo: static, so the whole
flight is reproducible). A production server samples this per connection. -/
def ephemeralPriv : ByteArray :=
  ByteArray.mk (((List.range 32).map (fun i => UInt8.ofNat (0x40 + i))).toArray)

/-- The server's fixed 32-byte ServerHello random. -/
def serverRandom : ByteArray :=
  ByteArray.mk (((List.range 32).map (fun i => UInt8.ofNat (0xA0 + i))).toArray)

/-- The Ed25519 signing seed (RFC 8032) whose public key is embedded in
`certData`. Fixed seed `00 01 … 1f`; the self-signed certificate in `certData`
carries exactly `Ed25519(seed).public`. -/
def certSeed : ByteArray :=
  ByteArray.mk (((List.range 32).map (fun i => UInt8.ofNat i)).toArray)

/-- A self-signed Ed25519 X.509 certificate (DER) whose SubjectPublicKeyInfo is
the Ed25519 public key of `certSeed`. A real client verifies the
CertificateVerify signature against this key (RFC 8446 §4.4.3). -/
def certData : ByteArray := ByteArray.mk #[
  0x30,0x81,0xd6,0x30,0x81,0x89,0xa0,0x03,0x02,0x01,0x02,0x02,0x01,0x01,0x30,0x05,
  0x06,0x03,0x2b,0x65,0x70,0x30,0x14,0x31,0x12,0x30,0x10,0x06,0x03,0x55,0x04,0x03,
  0x0c,0x09,0x6c,0x6f,0x63,0x61,0x6c,0x68,0x6f,0x73,0x74,0x30,0x20,0x17,0x0d,0x32,
  0x34,0x30,0x31,0x30,0x31,0x30,0x30,0x30,0x30,0x30,0x30,0x5a,0x18,0x0f,0x32,0x31,
  0x30,0x30,0x30,0x31,0x30,0x31,0x30,0x30,0x30,0x30,0x30,0x30,0x5a,0x30,0x14,0x31,
  0x12,0x30,0x10,0x06,0x03,0x55,0x04,0x03,0x0c,0x09,0x6c,0x6f,0x63,0x61,0x6c,0x68,
  0x6f,0x73,0x74,0x30,0x2a,0x30,0x05,0x06,0x03,0x2b,0x65,0x70,0x03,0x21,0x00,0x03,
  0xa1,0x07,0xbf,0xf3,0xce,0x10,0xbe,0x1d,0x70,0xdd,0x18,0xe7,0x4b,0xc0,0x99,0x67,
  0xe4,0xd6,0x30,0x9b,0xa5,0x0d,0x5f,0x1d,0xdc,0x86,0x64,0x12,0x55,0x31,0xb8,0x30,
  0x05,0x06,0x03,0x2b,0x65,0x70,0x03,0x41,0x00,0xac,0x10,0xbb,0xbd,0x03,0x3f,0xb4,
  0xeb,0x05,0x48,0x47,0xd6,0x06,0x86,0x5b,0x4d,0x0f,0x9f,0x11,0x92,0xd5,0x6a,0xb3,
  0x0e,0x3a,0x49,0x81,0xa7,0xd1,0x1b,0xdb,0xd1,0x16,0x28,0x0b,0x37,0x1f,0x8d,0x06,
  0x70,0x44,0xea,0x7b,0x97,0x35,0xdb,0xa0,0x6d,0xef,0x37,0x92,0x51,0x6a,0x19,0x5c,
  0x93,0x9c,0x43,0xe0,0xb1,0x8e,0x89,0xf2,0x02]

/-- A derived 8-byte connection ID (deterministic per connection + sequence). -/
def deriveCid (seed : ByteArray) (seq : Nat) : ByteArray :=
  (Crypto.sha256 (seed ++ ByteArray.mk #[UInt8.ofNat seq])).extract 0 8

/-- The per-connection server source connection ID. -/
def connScid (odcid cscid : ByteArray) : ByteArray := deriveCid (odcid ++ cscid) 0

/-- A 16-byte stateless-reset token for an issued CID (RFC 9000 §10.3 shape). -/
def resetToken (cid : ByteArray) : ByteArray :=
  (Crypto.sha256 (cid ++ "rt".toUTF8)).extract 0 16

/-- Deterministic 8-byte PATH_CHALLENGE data for probe number `n`. -/
def challengeData (odcid : ByteArray) (n : Nat) : ByteArray :=
  (Crypto.sha256 (odcid ++ "pc".toUTF8 ++ ByteArray.mk #[UInt8.ofNat n])).extract 0 8

/-! ### Address validation by Retry (RFC 9000 §8.1.2 + RFC 9001 §5.8)

A client Initial without a token is answered with a stateless Retry packet
whose token binds the original DCID; the client repeats the token in its next
Initial, from which the original DCID is recovered (it becomes the
`original_destination_connection_id` transport parameter, while the Retry's
SCID becomes `retry_source_connection_id`). The Retry Integrity Tag is the
AES-128-GCM tag over the Retry pseudo-packet under the fixed QUIC v1 key and
nonce (RFC 9001 §5.8), computed by the verified EverCrypt AEAD. -/

/-- The token's 16-byte authenticator over the original DCID. -/
def retryTokenMac (odcid : ByteArray) : ByteArray :=
  (Crypto.sha256 (odcid ++ "retry-token".toUTF8)).extract 0 16

/-- The Retry token: `0x52 ‖ odcid_len ‖ odcid ‖ mac16` (stateless — the server
keeps nothing between the Retry and the tokened Initial). -/
def retryToken (odcid : ByteArray) : ByteArray :=
  ByteArray.mk #[0x52, UInt8.ofNat odcid.size] ++ odcid ++ retryTokenMac odcid

/-- Validate a Retry token, recovering the original DCID. -/
def checkRetryToken (tok : List UInt8) : Option ByteArray :=
  match tok with
  | 0x52 :: lenB :: rest =>
    let len := lenB.toNat
    if len == 0 || len > 20 || rest.length != len + 16 then none
    else
      let odcid : ByteArray := ⟨(rest.take len).toArray⟩
      if rest.drop len == (retryTokenMac odcid).toList then some odcid else none
  | _ => none

/-- The fixed QUIC v1 Retry-integrity AEAD key (RFC 9001 §5.8). -/
def retryIntegrityKey : ByteArray :=
  ByteArray.mk #[0xbe, 0x0c, 0x69, 0x0b, 0x9f, 0x66, 0x57, 0x5a,
                 0x1d, 0x76, 0x6b, 0x54, 0xe3, 0x68, 0xc8, 0x4e]

/-- The fixed QUIC v1 Retry-integrity nonce (RFC 9001 §5.8). -/
def retryIntegrityNonce : ByteArray :=
  ByteArray.mk #[0x46, 0x15, 0x99, 0xd3, 0x5d, 0x63, 0x2b, 0xf2, 0x23, 0x98, 0x25, 0xbb]

/-- Build the Retry packet (RFC 9000 §17.2.5) answering a client Initial with
DCID `odcid` and SCID `cscid`: type bits `11`, the client's SCID as DCID, the
server-chosen `connScid odcid cscid` as SCID (repeated verbatim in the tokened
connection's `retry_source_connection_id`), the token, then the integrity tag —
the AES-128-GCM tag over `odcid_len ‖ odcid ‖ retry-sans-tag` under the fixed
v1 key/nonce, with an empty plaintext (RFC 9001 §5.8). -/
def buildRetry (odcid cscid : ByteArray) : Option ByteArray :=
  let rscid := connScid odcid cscid
  let body := ByteArray.mk #[0xF0] ++ version1
    ++ ByteArray.mk #[UInt8.ofNat cscid.size] ++ cscid
    ++ ByteArray.mk #[UInt8.ofNat rscid.size] ++ rscid
    ++ retryToken odcid
  let pseudo := ByteArray.mk #[UInt8.ofNat odcid.size] ++ odcid ++ body
  (aesGcmSeal retryIntegrityKey retryIntegrityNonce pseudo ByteArray.empty).map
    (fun tag => body ++ tag)

/-- The token field of a client Initial (RFC 9000 §17.2.2): version(4) after the
first byte, DCID, SCID, then `token_len ‖ token`. -/
def initialToken (bs : List UInt8) : Option (List UInt8) := do
  let dcidLenB ← bs[5]?
  let scidLenOff := 6 + dcidLenB.toNat
  let scidLenB ← bs[scidLenOff]?
  let afterScid := scidLenOff + 1 + scidLenB.toNat
  let (tokLen, tb) ← readVarint (bs.drop afterScid)
  let tok := (bs.drop (afterScid + tb)).take tokLen
  if tok.length != tokLen then none else some tok

/-! ## (9) The connection state -/

inductive Phase where
  | awaitFinished | established | closed | failed
  deriving DecidableEq, Repr, BEq

structure Conn where
  odcid : ByteArray
  cscid : ByteArray
  myCids : List ByteArray            -- server-issued CIDs; head = handshake SCID
  dhe : ByteArray
  srvInitial : PacketKeys
  srvHs : PacketKeys
  cliHs : PacketKeys
  srvApp : Option PacketKeys
  cliApp : Option PacketKeys
  sApSec : ByteArray                 -- current-generation app secrets (key update)
  cApSec : ByteArray
  keyPhase : Bool
  cHsSecret : ByteArray
  thSF : ByteArray
  initPn : Nat                       -- send packet numbers
  hsPn : Nat
  appPn : Nat
  recvHs : List Nat                  -- received PNs, descending, bounded
  recvApp : List Nat
  spin : Bool
  spinPn : Nat
  phase : Phase
  streams : List (Nat × List UInt8 × Bool)   -- sid ↦ (request bytes, responded)
  chalCtr : Nat
  lastChallenge : Option (List UInt8)
  pathValidated : Bool

/-! ## (10) Building the server response flight from a decrypted ClientHello -/

/-- Given the client's original DCID, the server SCID, the ALPN selection, the
post-Retry `retry_source_connection_id` (if the connection was retried) and the
ClientHello handshake-message bytes, derive the handshake secrets and build the
server's CRYPTO content (raw TLS messages) plus the transcript needed for 1-RTT.
Returns the ServerHello, the handshake-flight bytes (EE‖Cert‖CV‖Finished), and
the `Established` transcript material. -/
def buildTlsFlight (odcid sscid alpn chMsg : ByteArray) (retryScid : Option ByteArray)
    (ch : ClientHello) : Option (ByteArray × ByteArray × Established) := do
  let cpub ← ch.keyShare
  let serverPub ← x25519Base ephemeralPriv
  let dhe ← x25519 ephemeralPriv (ofBytes cpub)
  let sh := buildServerHello chachaSuite serverRandom (ofBytes ch.sessionId) serverPub
  let thHS := sha256 (chMsg ++ sh)
  let ee := buildEncryptedExtensionsQuic odcid sscid alpn retryScid
  let cert := buildCertificate [certData]
  let es ← earlySecretNoPsk
  let hs ← handshakeSecret es dhe
  let sHs ← serverHsTrafficSecret hs thHS
  let cv ← buildCertificateVerify certSeed (sha256 (chMsg ++ sh ++ ee ++ cert))
  let sFin ← buildFinished sHs (sha256 (chMsg ++ sh ++ ee ++ cert ++ cv))
  let thSF := sha256 (chMsg ++ sh ++ ee ++ cert ++ cv ++ sFin)
  let est : Established := { dhe := dhe, thHS := thHS, thSF := thSF, alpn := .h1 }
  some (sh, ee ++ cert ++ cv ++ sFin, est)

/-- The server handshake-level packet keys (server + client handshake ChaCha
keys) from the DHE + the CH..SH transcript hash. -/
def handshakeKeys (dhe thHS : ByteArray) :
    Option (PacketKeys × PacketKeys × ByteArray) := do
  let es ← earlySecretNoPsk
  let hs ← handshakeSecret es dhe
  let sHsSecret ← serverHsTrafficSecret hs thHS
  let cHsSecret ← clientHsTrafficSecret hs thHS
  let srvHs ← deriveChachaKeys sHsSecret
  let cliHs ← deriveChachaKeys cHsSecret
  some (srvHs, cliHs, cHsSecret)

/-- Build the coalesced Initial+Handshake response datagram and the connection
state from a complete (reassembled) ClientHello. `wireDcid` is the DCID the
client's Initial carried on the wire (post-Retry this is the Retry SCID, and
both Initial key derivations use it — RFC 9001 §5.2); `origDcid` is the original
DCID recovered from the Retry token (the `original_destination_connection_id`
transport parameter). `recvPns` are the Initial-space packet numbers to
acknowledge; `initPn` is the server's next Initial-space send packet number.
`none` if the ClientHello is undecodable or on any crypto failure. The datagram
is padded to 1200 bytes (RFC 9000 §14.1). -/
def buildFlightFromCH (wireDcid origDcid cscid chMsg : ByteArray) (recvPns : List Nat)
    (initPn : Nat) : Option (ByteArray × Conn) := do
  let ch ← parseClientHello chMsg.toList
  let retried := wireDcid.toList != origDcid.toList
  let sscid := if retried then wireDcid else connScid origDcid cscid
  let retryScid := if retried then some wireDcid else none
  let alpn := chooseAlpn chMsg.toList
  let (sh, hsFlight, est) ← buildTlsFlight origDcid sscid alpn chMsg retryScid ch
  let srvInitSecret ← serverInitialSecret wireDcid
  let srvInit ← deriveAesKeys srvInitSecret
  let (srvHs, cliHs, cHsSecret) ← handshakeKeys est.dhe est.thHS
  let hsPkt ← buildLongPacket tHandshake false false cscid sscid 0
                (cryptoFrame 0 hsFlight) srvHs
  let initPayload0 := ackFrameOf recvPns ++ cryptoFrame 0 sh
  let initPkt0 ← buildLongPacket tInitial true true cscid sscid initPn initPayload0 srvInit
  -- pad the datagram to 1200 bytes with PADDING frames inside the Initial packet
  let deficit := 1200 - (initPkt0.size + hsPkt.size)
  let initPayload := initPayload0 ++ ByteArray.mk (Array.mkArray deficit 0)
  let initPkt ← buildLongPacket tInitial true true cscid sscid initPn initPayload srvInit
  let conn : Conn :=
    { odcid := origDcid, cscid := cscid, myCids := [sscid], dhe := est.dhe,
      srvInitial := srvInit, srvHs := srvHs, cliHs := cliHs,
      srvApp := none, cliApp := none,
      sApSec := ByteArray.empty, cApSec := ByteArray.empty, keyPhase := false,
      cHsSecret := cHsSecret, thSF := est.thSF,
      initPn := initPn + 1, hsPn := 1, appPn := 0,
      recvHs := [], recvApp := [], spin := false, spinPn := 0,
      phase := .awaitFinished, streams := [],
      chalCtr := 0, lastChallenge := none, pathValidated := false }
  some (initPkt ++ hsPkt, conn)

/-! ## (11) Installing 1-RTT on the client Finished -/

/-- The application (1-RTT) traffic secrets, from the master secret and the
transcript through the server Finished. -/
def appSecrets (conn : Conn) : Option (ByteArray × ByteArray) := do
  let es ← earlySecretNoPsk
  let hs ← handshakeSecret es conn.dhe
  let ms ← masterSecret hs
  let sAp ← serverApTrafficSecret ms conn.thSF
  let cAp ← clientApTrafficSecret ms conn.thSF
  some (sAp, cAp)

/-- Verify the client's Handshake Finished (RFC 8446 §4.4.4) and, on success,
install the 1-RTT keys, moving the connection to `established`. -/
def onClientFinished (conn : Conn) (finishedMsg : List UInt8) :
    Option Conn := do
  -- expected verify_data = HMAC(client finished key, thSF)
  let expected ← verifyData conn.cHsSecret conn.thSF
  -- finishedMsg = 0x14 ‖ uint24 len ‖ verify_data
  guard (finishedMsg.take 1 == [0x14])
  let vd := (finishedMsg.drop 4).take expected.size
  guard (vd == expected.toList)
  let (sAp, cAp) ← appSecrets conn
  let srvApp ← deriveChachaKeys sAp
  let cliApp ← deriveChachaKeys cAp
  some { conn with srvApp := some srvApp, cliApp := some cliApp,
                   sApSec := sAp, cApSec := cAp, phase := .established }

/-! ## (12) The 1-RTT connection step -/

/-- Record STREAM data for a stream (in-order segments only; a duplicate or
out-of-order segment is dropped — the request streams a client sends fit the
in-order case, and a retransmission re-offers the same offset). -/
def feedStream (streams : List (Nat × List UInt8 × Bool)) (sid off : Nat)
    (data : List UInt8) : List (Nat × List UInt8 × Bool) :=
  match streams.find? (·.1 == sid) with
  | none => if off == 0 then (sid, data, false) :: streams else streams
  | some (_, buf, r) =>
    if off == buf.length && data ≠ [] then
      streams.map (fun s => if s.1 == sid then (sid, buf ++ data, r) else s)
    else streams

/-- The server's advertised HTTP/3 SETTINGS (RFC 9114 §7.2.4): the QPACK limits
(RFC 9204 §5) — `SETTINGS_QPACK_MAX_TABLE_CAPACITY` (0x01) and
`SETTINGS_QPACK_BLOCKED_STREAMS` (0x07) — plus `SETTINGS_MAX_FIELD_SECTION_SIZE`
(0x06). The QPACK capacity is advertised as 0: the deployed QPACK path decodes
the static table only (no encoder-stream / dynamic-table insertions), so a 0
capacity is the value that is both honest and keeps every peer's request field
sections decodable. The identifiers are still emitted, so a peer's
`received_settings` is non-empty. -/
def serverSettings : List (Nat × Nat) := [(0x01, 0), (0x07, 0), (0x06, 65536)]

/-- The SETTINGS payload bytes, emitted by the proven `H3.encSettings` (the exact
inverse of the deployed `decSettings`, `H3.decSettings_encSettings`). The
identifiers/values above are all in varint range, so the encode never fails; `[]`
is unreachable. -/
def settingsPayload : ByteArray :=
  ⟨((_root_.H3.encSettings serverSettings).getD []).toArray⟩

/-- The server control stream (id 3, type `0x00`) carrying a real SETTINGS frame
(`0x04 ‖ len ‖ payload`) — required by an H3 client before it accepts responses
(RFC 9114 §6.2.1). The payload advertises the server's QPACK / field-section
limits via `H3.encSettings`, so a peer sees a non-empty `received_settings`. -/
def ctrlStreamFrame : ByteArray :=
  let settingsFrame := ByteArray.mk #[0x04] ++ encVarint settingsPayload.size ++ settingsPayload
  streamFrame 3 0 false (ByteArray.mk #[0x00] ++ settingsFrame)

/-- Handshake confirmation outputs (one 1-RTT packet): HANDSHAKE_DONE, three
NEW_CONNECTION_ID frames (seq 1–3, so the client can rotate the server CID), and
the H3 control stream. -/
def establishOutputs (conn : Conn) : Conn × Array ByteArray :=
  match conn.srvApp with
  | none => (conn, #[])
  | some ap =>
    let extra := (List.range 3).map (fun i =>
      let cid := deriveCid conn.odcid (i + 1)
      (cid, newCidFrame (i + 1) cid (resetToken cid)))
    let payload := handshakeDoneFrame ++ concatBAs (extra.map (·.2)) ++ ctrlStreamFrame
    match buildShortPacket conn.cscid conn.appPn conn.spin conn.keyPhase payload ap with
    | none => (conn, #[])
    | some out =>
      ({ conn with appPn := conn.appPn + 1, myCids := conn.myCids ++ extra.map (·.1) },
       #[out])

/-- A duplicate client Finished (our confirmation was lost): resend
HANDSHAKE_DONE. -/
def resendDone (conn : Conn) : Conn × Array ByteArray :=
  match conn.srvApp with
  | none => (conn, #[])
  | some ap =>
    match buildShortPacket conn.cscid conn.appPn conn.spin conn.keyPhase
            handshakeDoneFrame ap with
    | none => (conn, #[])
    | some out => ({ conn with appPn := conn.appPn + 1 }, #[out])

/-- Process a client Handshake-level packet: ACK tracking + the client Finished
(verify → install 1-RTT → HANDSHAKE_DONE + CID issuance + H3 SETTINGS). -/
def onHandshake (conn : Conn) (pkt : List UInt8) : Conn × Array ByteArray :=
  match locateLong pkt with
  | none => (conn, #[])
  | some loc =>
    let expected := match conn.recvHs with | [] => 0 | p :: _ => p + 1
    match openLongCha pkt loc.pnOff conn.cliHs expected with
    | none => (conn, #[])
    | some (pn, pt) =>
      if conn.recvHs.contains pn then (conn, #[]) else
      let conn := { conn with recvHs := (insertDesc pn conn.recvHs).take 48 }
      let frs := parseFrames pt.size pt.toList
      let cryptos := frs.filterMap (fun f =>
        match f with | .crypto off d => some (off, d) | _ => none)
      match conn.phase, cryptos.find? (·.1 == 0) with
      | .awaitFinished, some (_, fin) =>
        (match onClientFinished conn fin with
         | none => ({ conn with phase := .failed }, #[])
         | some conn' => establishOutputs conn')
      | .established, some _ => resendDone conn
      | _, _ => (conn, #[])

/-- Process a client 1-RTT (short-header) packet: key-phase handling, PN/spin
tracking, frame walk, stream collection, path frames, request service, and the
ACK response. -/
def onShort (h3serve : ByteArray → ByteArray) (conn : Conn) (pkt : List UInt8) :
    Conn × Array ByteArray :=
  match conn.cliApp, conn.srvApp with
  | some cap, some sap =>
    let expected := match conn.recvApp with | [] => 0 | p :: _ => p + 1
    let pnOff := 1 + 8
    match removeHpShort pkt pnOff cap.hp expected with
    | none => (conn, #[])
    | some up =>
      if conn.recvApp.contains up.pn then (conn, #[]) else
      let phaseBit := (up.firstByte &&& 0x04) != 0
      let spinBit := (up.firstByte &&& 0x20) != 0
      let ct : ByteArray := ⟨(pkt.drop (pnOff + up.pnLen)).toArray⟩
      -- select the AEAD generation by the key-phase bit (RFC 9001 §6);
      -- the header-protection key never rotates, so HP removal above is valid
      -- for both generations.
      let opened : Option (ByteArray × Option (PacketKeys × PacketKeys × ByteArray × ByteArray)) :=
        if phaseBit == conn.keyPhase then
          (openCha cap up.pn up.header ct).map (fun pt => (pt, none))
        else do
          let (cliK, cSec') ← nextGenKeys cap conn.cApSec
          let pt ← openCha cliK up.pn up.header ct
          let (srvK, sSec') ← nextGenKeys sap conn.sApSec
          some (pt, some (cliK, srvK, cSec', sSec'))
      match opened with
      | none => (conn, #[])
      | some (pt, rot) =>
        -- commit the key update in BOTH directions (RFC 9001 §6.2)
        let conn := match rot with
          | none => conn
          | some (cliK, srvK, cSec', sSec') =>
            { conn with cliApp := some cliK, srvApp := some srvK,
                        cApSec := cSec', sApSec := sSec', keyPhase := !conn.keyPhase }
        let sendKeys := conn.srvApp.getD sap
        -- PN + spin tracking (spin follows the highest-numbered packet, §17.4)
        let conn := { conn with
          recvApp := (insertDesc up.pn conn.recvApp).take 48,
          spin := if up.pn ≥ conn.spinPn then spinBit else conn.spin,
          spinPn := max conn.spinPn up.pn }
        let frs := parseFrames pt.size pt.toList
        if frs.any (· == .close) then ({ conn with phase := .closed }, #[]) else
        -- STREAM collection
        let conn := frs.foldl (fun c f =>
          match f with
          | .stream sid off _fin d => { c with streams := feedStream c.streams sid off d }
          | _ => c) conn
        -- client PATH_CHALLENGE → mandatory PATH_RESPONSE (RFC 9000 §8.2.2)
        let pathResps := frs.filterMap (fun f =>
          match f with
          | .pathChallenge d => some (pathResponseFrame ⟨d.toArray⟩)
          | _ => none)
        -- our PATH_RESPONSE echo → path validated (RFC 9000 §8.2.3)
        let conn :=
          if frs.any (fun f =>
              match f with
              | .pathResponse d => conn.lastChallenge == some d
              | _ => false)
          then { conn with pathValidated := true, lastChallenge := none }
          else conn
        -- serve every unanswered client-bidi request stream
        let served := conn.streams.foldr
          (fun (s : Nat × List UInt8 × Bool) (acc : List (Nat × List UInt8 × Bool) × List ByteArray) =>
            let (sid, buf, done) := s
            if !done && sid % 4 == 0 && !buf.isEmpty then
              ((sid, buf, true) :: acc.1,
               streamFrame sid 0 true (h3serve ⟨buf.toArray⟩) :: acc.2)
            else (s :: acc.1, acc.2))
          ([], [])
        let conn := { conn with streams := served.1 }
        -- probe the path on client activity (PING / request) — §8.2.1 allows
        -- validation at any time; the UDP shell hides the peer address, so a
        -- rebound path is validated by this standing probe.
        let active := frs.any (fun f =>
          match f with
          | .ping => true
          | .stream _ _ _ _ => true
          | _ => false)
        let (conn, chal) :=
          if active then
            let d := challengeData conn.odcid conn.chalCtr
            ({ conn with chalCtr := conn.chalCtr + 1, lastChallenge := some d.toList },
             [pathChallengeFrame d])
          else (conn, [])
        if !(ackEliciting frs) then (conn, #[]) else
        let payload := ackFrameOf conn.recvApp
          ++ concatBAs chal ++ concatBAs pathResps ++ concatBAs served.2
        match buildShortPacket conn.cscid conn.appPn conn.spin conn.keyPhase
                payload sendKeys with
        | none => (conn, #[])
        | some out => ({ conn with appPn := conn.appPn + 1 }, #[out])
  | _, _ => (conn, #[])

/-! ## (13) The server state: a connection table + ClientHello reassembly -/

/-- Pre-connection state for a client whose ClientHello is still arriving:
CRYPTO segments and received Initial packet numbers, keyed by the on-wire DCID
(post-Retry, the Retry SCID). `origDcid` is the original DCID recovered from the
Retry token. -/
structure Pending where
  odcid : ByteArray
  origDcid : ByteArray
  cscid : ByteArray
  segs : List (Nat × List UInt8)
  recvPns : List Nat
  sendPn : Nat

structure ServerState where
  conns : List Conn
  pending : List Pending

def ServerState.empty : ServerState := ⟨[], []⟩

/-- Decrypt a client Initial packet (verified AES-128-GCM under AES-ECB header
protection) and walk its frames. -/
def decryptInitialFrames (bs : List UInt8) (loc : LocLong) (expected : Nat) :
    Option (Nat × List Fr) := do
  let cliInitSecret ← clientInitialSecret loc.dcid
  let k ← deriveAesKeys cliInitSecret
  let up ← QuicHeaderProt.removeHpAes bs loc.pnOff k.hp expected
  -- the AEAD ciphertext ends at the packet's Length boundary, not the datagram
  -- end (client Initials are PADDING-inflated at the datagram level)
  let ctLen := loc.total - (loc.pnOff + up.pnLen)
  let ct : ByteArray := ⟨((bs.drop (loc.pnOff + up.pnLen)).take ctLen).toArray⟩
  let pt ← openAes k up.pn up.header ct
  some (up.pn, parseFrames pt.size pt.toList)

/-- An Initial-space ACK-only packet (sent while a multi-packet ClientHello is
still being reassembled, so the client learns its Initials arrived). Keys derive
from the on-wire DCID; the SCID matches the one the eventual response flight
will carry (post-Retry, the wire DCID itself). -/
def buildInitialAck (wireDcid origDcid cscid : ByteArray) (sendPn : Nat)
    (recvPns : List Nat) : Option ByteArray := do
  let s ← serverInitialSecret wireDcid
  let k ← deriveAesKeys s
  let sscid := if wireDcid.toList != origDcid.toList then wireDcid
               else connScid origDcid cscid
  buildLongPacket tInitial true true cscid sscid sendPn (ackFrameOf recvPns) k

/-- Process a client Initial (carrying a validated Retry token recovering
`orig`) for a not-yet-established connection: decrypt, merge its CRYPTO segments
into the pending buffer, and either complete the handshake flight (ClientHello
fully reassembled) or acknowledge and keep waiting. -/
def onInitialNew (st : ServerState) (bs : List UInt8) (loc : LocLong)
    (orig : ByteArray) : ServerState × Array ByteArray :=
  let p0 := (st.pending.find? (·.odcid.toList == loc.dcid.toList)).getD
    { odcid := loc.dcid, origDcid := orig, cscid := loc.scid,
      segs := [], recvPns := [], sendPn := 0 }
  let expected := match p0.recvPns with | [] => 0 | q :: _ => q + 1
  match decryptInitialFrames bs loc expected with
  | none => (st, #[])
  | some (pn, frs) =>
    if p0.recvPns.contains pn then (st, #[]) else
    let segs := frs.foldl (fun acc f =>
      match f with
      | .crypto off d => insSeg acc off d
      | _ => acc) p0.segs
    let recv := insertDesc pn p0.recvPns
    let othersP := st.pending.filter (fun q => !(q.odcid.toList == loc.dcid.toList))
    match completeHsMsg (assembleFrom segs segs.length 0) with
    | some ch =>
      match buildFlightFromCH loc.dcid p0.origDcid p0.cscid ⟨ch.toArray⟩ recv p0.sendPn with
      | some (flight, conn) =>
        ({ conns := (conn :: st.conns).take 32, pending := othersP }, #[flight])
      | none => (st, #[])
    | none =>
      let ack := buildInitialAck loc.dcid p0.origDcid loc.scid p0.sendPn recv
      let p1 := { p0 with cscid := loc.scid, segs := segs, recvPns := recv,
                          sendPn := p0.sendPn + 1 }
      ({ st with pending := (p1 :: othersP).take 16 },
       match ack with | some a => #[a] | none => #[])

/-- Apply a per-connection step to the connection selected by `sel`, dropping it
from the table when it reaches `closed`. -/
def updateConn (st : ServerState) (sel : Conn → Bool)
    (f : Conn → Conn × Array ByteArray) : ServerState × Array ByteArray :=
  match st.conns.find? sel with
  | none => (st, #[])
  | some c =>
    let (c', outs) := f c
    let conns' :=
      if c'.phase == .closed then st.conns.filter (fun x => !(sel x))
      else st.conns.map (fun x => if sel x then c' else x)
    ({ st with conns := conns' }, outs)

/-- Whether a connection owns a (list-encoded) destination CID. -/
def ownsCid (c : Conn) (dcid : List UInt8) : Bool :=
  c.myCids.any (·.toList == dcid)

/-- Route one coalesced packet to its connection (by DCID) or to the
new-connection Initial path. -/
def routePacket (h3serve : ByteArray → ByteArray) (st : ServerState)
    (pkt : List UInt8) : ServerState × Array ByteArray :=
  match pkt[0]? with
  | none => (st, #[])
  | some b0 =>
    match classify b0 with
    | .short =>
      let dcid := (pkt.drop 1).take 8
      updateConn st (ownsCid · dcid) (onShort h3serve · pkt)
    | .initial =>
      (match locateLong pkt with
       | none => (st, #[])
       | some loc =>
         -- an Initial addressed to an issued CID is a post-flight Initial ACK:
         -- nothing to do (ACK-only packets are not acknowledged)
         if st.conns.any (ownsCid · loc.dcid.toList) then (st, #[])
         else
           match initialToken pkt with
           | none => (st, #[])
           | some tok =>
             match checkRetryToken tok with
             | some orig => onInitialNew st pkt loc orig
             | none =>
               -- no (or an unverifiable) token: stateless address validation by
               -- Retry (RFC 9000 §8.1.2) — the tokened Initial comes back here
               (st, match buildRetry loc.dcid loc.scid with
                    | some r => #[r]
                    | none => #[]))
    | .handshake =>
      (match locateLong pkt with
       | none => (st, #[])
       | some loc => updateConn st (ownsCid · loc.dcid.toList) (onHandshake · pkt))
    | .other => (st, #[])

/-- A Version Negotiation packet (RFC 9000 §17.2.1) echoing the client's CIDs
(swapped) and offering QUIC v1: version field 0, then the supported list. -/
def vnDatagram (bs : List UInt8) : Option ByteArray :=
  match bs[5]? with
  | none => none
  | some dcidLenB =>
    let dcidLen := dcidLenB.toNat
    let dcid := (bs.drop 6).take dcidLen
    let scidLenOff := 6 + dcidLen
    match bs[scidLenOff]? with
    | none => none
    | some scidLenB =>
      let scidLen := scidLenB.toNat
      let scid := (bs.drop (scidLenOff + 1)).take scidLen
      if scid.length != scidLen || dcid.length != dcidLen then none else
      some (ByteArray.mk #[0xC0, 0x00, 0x00, 0x00, 0x00]
        ++ ByteArray.mk #[UInt8.ofNat scid.length] ++ ⟨scid.toArray⟩
        ++ ByteArray.mk #[UInt8.ofNat dcid.length] ++ ⟨dcid.toArray⟩
        ++ version1)

/-- The top-level server step: one received UDP datagram in, the datagrams to
send out. Handles version negotiation statelessly, then routes each coalesced
packet by connection ID. -/
def stepServer (h3serve : ByteArray → ByteArray) (st : ServerState)
    (dg : ByteArray) : ServerState × Array ByteArray :=
  let bs := dg.toList
  match bs[0]? with
  | none => (st, #[])
  | some b0 =>
    let isLong := (b0 &&& 0x80) != 0
    let ver := (bs.drop 1).take 4
    if isLong && ver != [0x00, 0x00, 0x00, 0x01] then
      -- unknown version: Version Negotiation (only for full-size datagrams,
      -- RFC 9000 §6.1; never in response to a VN packet, version 0)
      if ver == [0x00, 0x00, 0x00, 0x00] || bs.length < 1200 then (st, #[])
      else
        match vnDatagram bs with
        | some vn => (st, #[vn])
        | none => (st, #[])
    else
      (splitPackets 16 bs).foldl
        (fun (acc : ServerState × Array ByteArray) pkt =>
          let (st', outs) := routePacket h3serve acc.1 pkt
          (st', acc.2 ++ outs))
        (st, #[])

/-! ## (14) Correctness theorems

The new transport behaviors with byte-level specs, proven of the pure functions
the server runs (no `sorry`, nothing vacuous):

  * `insertDesc_mem` / `insertDesc_sorted` — the received-PN tracker records
    exactly the received packet numbers and keeps them strictly descending.
  * `ackRuns_exact` — the ACK frame's range structure decodes back to exactly
    the tracked packet-number list: the server acknowledges precisely what it
    received (RFC 9000 §13.1, §19.3).
  * `ackRuns_gaps` — on a strictly-descending list the inter-range gaps satisfy
    `lo > hi' + 1`, so the `gap = lo - hi' - 2` fields of the emitted ACK frame
    never underflow (RFC 9000 §19.3.1).
  * `assembleFrom_exact` — CRYPTO reassembly reconstructs the original handshake
    byte stream from its segments arriving in any order (RFC 9000 §7.5).
  * `nextGenKeys_preserves_hp` — a key update re-derives the AEAD key/IV but
    never the header-protection key (RFC 9001 §6.1).
  * `checkRetryToken_sound` — an accepted Retry token is byte-for-byte one the
    server minted, and it pins the original DCID the handshake echoes as
    `original_destination_connection_id` (RFC 9000 §8.1.3).
-/

theorem insertDesc_mem (pn a : Nat) (l : List Nat) :
    a ∈ insertDesc pn l ↔ a = pn ∨ a ∈ l := by
  induction l with
  | nil => simp [insertDesc]
  | cons q r ih =>
    unfold insertDesc
    by_cases h1 : q < pn
    · rw [if_pos h1]
      simp [List.mem_cons]
    · rw [if_neg h1]
      by_cases h2 : pn = q
      · subst h2
        rw [if_pos (beq_self_eq_true pn)]
        simp only [List.mem_cons]
        constructor
        · intro h; exact .inr h
        · rintro (h | h)
          · exact .inl h
          · exact h
      · rw [if_neg (by simp [h2])]
        simp only [List.mem_cons, ih]
        constructor
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

theorem insertDesc_sorted (pn : Nat) (l : List Nat) (h : l.Pairwise (· > ·)) :
    (insertDesc pn l).Pairwise (· > ·) := by
  induction l with
  | nil => simp [insertDesc]
  | cons q r ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hq, hr⟩ := h
    unfold insertDesc
    by_cases h1 : q < pn
    · rw [if_pos h1]
      rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with hb | hb
        · omega
        · have := hq b hb; omega
      · rw [List.pairwise_cons]; exact ⟨hq, hr⟩
    · rw [if_neg h1]
      by_cases h2 : pn = q
      · subst h2
        rw [if_pos (beq_self_eq_true pn)]
        rw [List.pairwise_cons]; exact ⟨hq, hr⟩
      · rw [if_neg (by simp [h2])]
        rw [List.pairwise_cons]
        refine ⟨?_, ih hr⟩
        intro b hb
        rcases (insertDesc_mem pn b r).mp hb with hb | hb
        · omega
        · exact hq b hb

/-- Expand one ACK run `(hi, lo)` to its packet numbers, descending. -/
def runPns (hi lo : Nat) : List Nat :=
  if _h : lo < hi then hi :: runPns (hi - 1) lo else [hi]
termination_by hi - lo
decreasing_by omega

/-- Expand a run list to its packet numbers, in order. -/
def runsPns : List (Nat × Nat) → List Nat
  | [] => []
  | r :: rs => runPns r.1 r.2 ++ runsPns rs

theorem runPns_succ (hi lo : Nat) (h : lo ≤ hi) :
    runPns (hi + 1) lo = (hi + 1) :: runPns hi lo := by
  rw [runPns]
  simp only [Nat.add_sub_cancel]
  rw [dif_pos (by omega)]

/-- Every run is well-formed: its smallest end is ≤ its largest. -/
theorem ackRuns_wf (l : List Nat) : ∀ r ∈ ackRuns l, r.2 ≤ r.1 := by
  induction l with
  | nil => intro r hr; simp [ackRuns] at hr
  | cons p rest ih =>
    intro r hr
    unfold ackRuns at hr
    cases hrs : ackRuns rest with
    | nil =>
      rw [hrs] at hr
      simp at hr
      simp [hr]
    | cons hd tl =>
      rw [hrs] at hr
      rw [hrs] at ih
      by_cases hm : hd.1 + 1 = p
      · simp only [hm, if_pos] at hr
        rcases List.mem_cons.mp hr with hr | hr
        · have := ih hd (.head _)
          subst hr; simp; omega
        · exact ih r (.tail _ hr)
      · simp only [if_neg hm] at hr
        rcases List.mem_cons.mp hr with hr | hr
        · subst hr; simp
        · exact ih r hr

/-- **The ACK ranges decode to exactly the tracked packet numbers.** For any
received-PN list, expanding the runs emitted by `ackRuns` yields the list back:
the ACK frame acknowledges precisely the received packets, no more, no fewer
(RFC 9000 §13.1). -/
theorem ackRuns_exact (l : List Nat) : runsPns (ackRuns l) = l := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    unfold ackRuns
    cases hrs : ackRuns rest with
    | nil =>
      have hrest : rest = [] := by rw [← ih, hrs]; rfl
      subst hrest
      show runPns p p ++ runsPns [] = [p]
      rw [runPns, dif_neg (Nat.lt_irrefl p)]
      rfl
    | cons hd tl =>
      obtain ⟨hi, lo⟩ := hd
      dsimp only
      by_cases hm : hi + 1 = p
      · rw [if_pos hm]
        have hwf : lo ≤ hi := ackRuns_wf rest (hi, lo) (by rw [hrs]; exact .head _)
        show runPns p lo ++ runsPns tl = p :: rest
        rw [← hm, runPns_succ hi lo hwf]
        have hres : runPns hi lo ++ runsPns tl = rest := by
          rw [← ih, hrs]; rfl
        simp [hres]
      · rw [if_neg hm]
        show runPns p p ++ runsPns ((hi, lo) :: tl) = p :: rest
        rw [runPns, dif_neg (Nat.lt_irrefl p)]
        show p :: runsPns ((hi, lo) :: tl) = p :: rest
        congr 1
        rw [← ih, hrs]

/-- The largest endpoint of every emitted run is a received packet number. -/
theorem ackRuns_hi_mem (l : List Nat) : ∀ r ∈ ackRuns l, r.1 ∈ l := by
  induction l with
  | nil => intro r hr; simp [ackRuns] at hr
  | cons p rest ih =>
    intro r hr
    unfold ackRuns at hr
    cases hrs : ackRuns rest with
    | nil =>
      rw [hrs] at hr; simp at hr; simp [hr]
    | cons hd tl =>
      rw [hrs] at hr
      rw [hrs] at ih
      by_cases hm : hd.1 + 1 = p
      · simp only [hm, if_pos] at hr
        rcases List.mem_cons.mp hr with hr | hr
        · subst hr; exact .head _
        · exact .tail _ (ih r (.tail _ hr))
      · simp only [if_neg hm] at hr
        rcases List.mem_cons.mp hr with hr | hr
        · subst hr; exact .head _
        · exact .tail _ (ih r hr)

/-- **The ACK gap fields never underflow.** On a strictly-descending tracked
list, consecutive runs `(hi, lo)` then `(hi', lo')` satisfy `hi' + 1 < lo`, so
the emitted `gap = lo - hi' - 2` is the true gap (RFC 9000 §19.3.1). -/
theorem ackRuns_gaps (l : List Nat) (h : l.Pairwise (· > ·)) :
    (ackRuns l).Pairwise (fun a b => b.1 + 1 < a.2) := by
  induction l with
  | nil => simp [ackRuns]
  | cons p rest ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hp, hrest⟩ := h
    unfold ackRuns
    cases hrs : ackRuns rest with
    | nil => simp
    | cons hd tl =>
      obtain ⟨hi, lo⟩ := hd
      have ihp := ih hrest
      rw [hrs] at ihp
      rw [List.pairwise_cons] at ihp
      obtain ⟨ihd, itl⟩ := ihp
      by_cases hm : hi + 1 = p
      · simp only [hm, if_pos]
        rw [List.pairwise_cons]
        exact ⟨ihd, itl⟩
      · simp only [if_neg hm]
        rw [List.pairwise_cons, List.pairwise_cons]
        have hhi : hi ∈ rest := ackRuns_hi_mem rest (hi, lo) (by rw [hrs]; exact .head _)
        have hip : hi < p := hp hi hhi
        have hwf : lo ≤ hi := ackRuns_wf rest (hi, lo) (by rw [hrs]; exact .head _)
        refine ⟨?_, ⟨ihd, itl⟩⟩
        intro b hb
        rcases List.mem_cons.mp hb with hb | hb
        · subst hb; simp; omega
        · have := ihd b hb; simp; omega

/-- The segments of a byte stream split into consecutive chunks starting at
`base`. -/
def chunkSegs (base : Nat) : List (List UInt8) → List (Nat × List UInt8)
  | [] => []
  | c :: cs => (base, c) :: chunkSegs (base + c.length) cs

/-- Concatenate chunks. -/
def joinChunks : List (List UInt8) → List UInt8
  | [] => []
  | c :: cs => c ++ joinChunks cs

theorem chunkSegs_offset_ge (cs : List (List UInt8)) (base : Nat) :
    ∀ s ∈ chunkSegs base cs, base ≤ s.1 := by
  induction cs generalizing base with
  | nil => intro s hs; simp [chunkSegs] at hs
  | cons c cs ih =>
    intro s hs
    unfold chunkSegs at hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst hs; simp
    · have := ih (base + c.length) s hs; omega

theorem find?_eq_of_mem_unique {α} (p : α → Bool) (l : List α) (a : α)
    (ha : a ∈ l) (hp : p a = true) (huniq : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    by_cases hx : p x = true
    · have hxa : x = a := huniq x (.head _) hx
      subst hxa
      simp [List.find?_cons_of_pos _ hx]
    · have hax : a ≠ x := fun e => hx (e ▸ hp)
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h hax
        · exact h
      rw [List.find?_cons_of_neg _ (by simpa using hx)]
      exact ih ha' (fun b hb hpb => huniq b (.tail _ hb) hpb)

/-- **CRYPTO reassembly is exact, in any arrival order.** If the recorded
segments are (as a set) exactly the chunks of a byte stream, reassembling from
the stream's start reconstructs the stream — regardless of the order the
segments arrived in (RFC 9000 §7.5). -/
theorem assembleFrom_exact (cs : List (List UInt8))
    (segs : List (Nat × List UInt8))
    (hne : ∀ c ∈ cs, c ≠ [])
    (hiff : ∀ s, s ∈ segs ↔ s ∈ chunkSegs 0 cs)
    (fuel : Nat) (hfuel : cs.length ≤ fuel) :
    assembleFrom segs fuel 0 = joinChunks cs := by
  -- generalized invariant over the remaining suffix of chunks
  suffices h : ∀ (cs' : List (List UInt8)) (pos fuel' : Nat),
      cs'.length ≤ fuel' →
      (∀ c ∈ cs', c ≠ []) →
      (∀ s ∈ chunkSegs pos cs', s ∈ chunkSegs 0 cs) →
      (∀ s ∈ chunkSegs 0 cs, pos ≤ s.1 → s ∈ chunkSegs pos cs') →
      assembleFrom segs fuel' pos = joinChunks cs' by
    refine h cs 0 fuel hfuel hne (fun s hs => hs) (fun s hs _ => hs)
  intro cs'
  induction cs' with
  | nil =>
    intro pos fuel' _ _ _ hsuf
    cases fuel' with
    | zero => rfl
    | succ fuel' =>
      show assembleFrom segs (fuel' + 1) pos = []
      unfold assembleFrom
      have : segs.find? (fun s => s.1 == pos) = none := by
        rw [List.find?_eq_none]
        intro s hs hp
        have hfull := (hiff s).mp hs
        have hpos : pos ≤ s.1 := by
          have : s.1 = pos := by simpa using hp
          omega
        have := hsuf s hfull hpos
        simp [chunkSegs] at this
      rw [this]
  | cons c cs' ih =>
    intro pos fuel' hfuel' hne' hsub hsuf
    cases fuel' with
    | zero => simp at hfuel'
    | succ fuel' =>
      have hmem : (pos, c) ∈ segs :=
        (hiff _).mpr (hsub _ (by unfold chunkSegs; exact .head _))
      have hcne : c ≠ [] := hne' c (.head _)
      have hclen : 0 < c.length := List.length_pos.mpr hcne
      have huniq : ∀ b ∈ segs, (b.1 == pos) = true → b = (pos, c) := by
        intro b hb hbp
        have hbf := (hiff b).mp hb
        have hbpos : b.1 = pos := by simpa using hbp
        have := hsuf b hbf (by omega)
        unfold chunkSegs at this
        rcases List.mem_cons.mp this with h | h
        · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h
          exact Prod.ext (by simpa using hbpos) (by rw [h]; )
        · have := chunkSegs_offset_ge cs' (pos + c.length) b h
          omega
      show assembleFrom segs (fuel' + 1) pos = c ++ joinChunks cs'
      unfold assembleFrom
      rw [find?_eq_of_mem_unique (fun s => s.1 == pos) segs (pos, c) hmem
            (by simp) huniq]
      show c ++ assembleFrom segs fuel' (pos + c.length) = c ++ joinChunks cs'
      congr 1
      refine ih (pos + c.length) fuel' (by simpa using Nat.le_of_succ_le_succ hfuel')
        (fun d hd => hne' d (.tail _ hd))
        (fun s hs => hsub s (by unfold chunkSegs; exact .tail _ hs))
        ?_
      intro s hs hle
      have := hsuf s hs (by omega)
      unfold chunkSegs at this
      rcases List.mem_cons.mp this with h | h
      · subst h; simp at hle; omega
      · exact h

/-- **The server accepts only tokens of its own mint** (RFC 9000 §8.1.3): a
token `checkRetryToken` validates to `orig` is byte-for-byte
`0x52 ‖ len(orig) ‖ orig ‖ mac(orig)` — exactly the shape `retryToken orig`
issues — with the recovered original DCID nonempty and ≤ 20 bytes. So the
post-Retry handshake's `original_destination_connection_id` is precisely the
DCID the Retry was minted for. -/
theorem checkRetryToken_sound (tok : List UInt8) (orig : ByteArray)
    (h : checkRetryToken tok = some orig) :
    0 < orig.size ∧ orig.size ≤ 20 ∧
    tok = 0x52 :: UInt8.ofNat orig.size :: (orig.data.toList ++ (retryTokenMac orig).toList) := by
  unfold checkRetryToken at h
  split at h
  next lenB rest =>
    dsimp only at h
    split at h
    · cases h
    · next hg =>
      split at h
      · next hm =>
        cases h
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, beq_iff_eq,
                   bne_iff_ne, ne_eq, decide_eq_true_eq, gt_iff_lt,
                   Nat.not_lt] at hg
        obtain ⟨⟨hlen0, hlen20⟩, hrlen'⟩ := hg
        have hrlen : rest.length = lenB.toNat + 16 := Decidable.byContradiction hrlen'
        have hsize : (ByteArray.mk (rest.take lenB.toNat).toArray).size = lenB.toNat := by
          show (rest.take lenB.toNat).toArray.size = lenB.toNat
          simp
          omega
        have htl : (ByteArray.mk (rest.take lenB.toNat).toArray).data.toList
            = rest.take lenB.toNat := by
          show (rest.take lenB.toNat).toArray.toList = rest.take lenB.toNat
          simp
        refine ⟨by omega, by omega, ?_⟩
        rw [hsize, htl]
        have hmac : rest.drop lenB.toNat
            = (retryTokenMac (ByteArray.mk (rest.take lenB.toNat).toArray)).toList :=
          eq_of_beq hm
        rw [← hmac, List.take_append_drop, UInt8.ofNat_toNat]
      · cases h
  next => cases h

/-- **A key update never rotates the header-protection key** (RFC 9001 §6.1):
the next-generation keys re-derive the AEAD key and IV from the `"quic ku"`
secret, but keep `hp` byte-for-byte. -/
theorem nextGenKeys_preserves_hp (old : PacketKeys) (sec : ByteArray)
    (k : PacketKeys) (s' : ByteArray)
    (h : nextGenKeys old sec = some (k, s')) : k.hp = old.hp := by
  unfold nextGenKeys at h
  cases h1 : nextGenSecret sec with
  | none => rw [h1] at h; cases h
  | some sNew =>
    rw [h1] at h
    dsimp only at h
    cases h2 : deriveChachaKeys sNew with
    | none => rw [h2] at h; cases h
    | some kNew =>
      rw [h2] at h
      dsimp only at h
      cases h
      rfl

end QuicServer
