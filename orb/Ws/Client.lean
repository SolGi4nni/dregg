import WsFrameCorrect

/-!
# WebSocket client (RFC 6455) — the opening handshake and client-side frames

The `Ws` library models the *server* side of RFC 6455: it decodes inbound frames
(`Reactor.Ws.decodeFrame`), unmasks them (`Ws.Mask`), reassembles fragments
(`Ws.Reassembly`), and encodes *server* frames unmasked (`Reactor.Ws.wsEncodeFn`).
This module supplies the missing *client* side and pins it to the standard:

* **The opening handshake (RFC 6455 §1.3, §4.1).** A client sends a random 16-octet
  nonce base64-encoded as `Sec-WebSocket-Key`. The server replies with
  `Sec-WebSocket-Accept = base64(SHA-1(key ‖ GUID))`, where `GUID` is the fixed
  `258EAFA5-E914-47DA-95CA-C5AB0DC85B11`. The client MUST verify that the reply
  equals this value before treating the connection as open (§4.1, step 4). We
  implement SHA-1 and base64 as total pure functions here — no crypto axiom is
  needed for the handshake — so `acceptKey` is the genuine RFC computation
  (the §1.3 test vector `dGhlIHNhbXBsZSBub25jZQ==` ↦ `s3pPLMBiTxaQ9kYGzzhZRbK+xOo=`
  reduces through it; see the companion check).

* **Client-to-server framing (RFC 6455 §5.3).** A client MUST mask every frame it
  sends with a fresh 4-octet key; the transformed octet `i` is `payload[i] ⊕
  key[i mod 4]`. `encodeClientFrame` builds exactly that wire frame — mask bit set,
  key emitted, payload masked — and the server's real decoder recovers the frame.

Headline results:

* `ws_client_handshake` — the client accepts a reply **iff** it equals the RFC
  `base64(SHA-1(key ‖ GUID))` for the key it sent: the honest server's accept
  passes and nothing else does.
* `ws_client_frame_roundtrip` — a masked client frame decodes, through the real
  server decoder, back to exactly the frame that was sent (its unmasked payload).
* `ws_client_masks` — every client frame `encodeClientFrame` produces has the
  §5.3 mask bit set: clients always mask.

Deliberately out of scope: TLS (`wss://`), permessage-deflate (RFC 7692), and the
randomness quality of the nonce/mask key (a wire-format model, not an RNG model).
-/

open Ws (Bytes Frame Opcode)

namespace Ws.Client

private theorem u8_toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := rfl

/-! ## SHA-1 (FIPS 180-4 §6.1) — a total pure implementation

SHA-1 is broken for collision resistance and MUST NOT be used as a security
primitive. RFC 6455 uses it only as a *fixed, public* mixing function in the
handshake — the accept value carries no secret and the security of the
connection does not rest on SHA-1. We therefore implement it directly (no FFI,
no axiom) so the handshake is a closed, checkable computation. -/

/-- 32-bit left rotate. -/
def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- Big-endian pack of the low four bytes of a `Nat` as `UInt8`s. -/
def beBytes32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
   UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Read four bytes big-endian into a `UInt32`. -/
def beWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

/-- RFC/FIPS padding: append `0x80`, zero-pad to 56 mod 64, then the 64-bit
big-endian bit length. -/
def sha1Pad (msg : List UInt8) : List UInt8 :=
  let len := msg.length
  let bitLen := 8 * len
  let rem := (len + 1) % 64
  let zeros := if rem ≤ 56 then 56 - rem else 120 - rem
  let lenBytes : List UInt8 :=
    beBytes32 (bitLen / 4294967296) ++ beBytes32 bitLen
  msg ++ (0x80 :: List.replicate zeros 0x00) ++ lenBytes

/-- Split a byte list into 64-byte blocks (the last block is full after
padding). Fuel-driven on the length so it is structurally terminating. -/
def chunk64Aux : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, l => l.take 64 :: chunk64Aux fuel (l.drop 64)

/-- Split a byte list into 64-byte blocks. -/
def chunk64 (l : List UInt8) : List (List UInt8) := chunk64Aux (l.length + 1) l

/-- The 16 big-endian message-schedule words of one 64-byte block. -/
def blockWords (blk : List UInt8) : Array UInt32 := Id.run do
  let a := blk.toArray
  let mut w : Array UInt32 := Array.mkEmpty 16
  for i in [0:16] do
    let j := 4 * i
    w := w.push (beWord (a.getD j 0) (a.getD (j+1) 0) (a.getD (j+2) 0) (a.getD (j+3) 0))
  return w

/-- Compress one block into the running state `(h0..h4)`. -/
def sha1Block (h : Array UInt32) (blk : List UInt8) : Array UInt32 := Id.run do
  let mut w := blockWords blk
  for t in [16:80] do
    let v := rotl (w.getD (t-3) 0 ^^^ w.getD (t-8) 0 ^^^ w.getD (t-14) 0 ^^^ w.getD (t-16) 0) 1
    w := w.push v
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  for t in [0:80] do
    let (f, k) :=
      if t < 20 then ((b &&& c) ||| ((~~~b) &&& d), (0x5A827999 : UInt32))
      else if t < 40 then (b ^^^ c ^^^ d, (0x6ED9EBA1 : UInt32))
      else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), (0x8F1BBCDC : UInt32))
      else (b ^^^ c ^^^ d, (0xCA62C1D6 : UInt32))
    let temp := rotl a 5 + f + e + k + w.getD t 0
    e := d; d := c; c := rotl b 30; b := a; a := temp
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d, h.getD 4 0 + e]

/-- SHA-1 digest (20 bytes, big-endian) of a byte message (FIPS 180-4 §6.1). -/
def sha1 (msg : List UInt8) : List UInt8 := Id.run do
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  for blk in chunk64 (sha1Pad msg) do
    h := sha1Block h blk
  return (List.range 5).flatMap (fun i => beBytes32 (h.getD i 0).toNat)

/-! ## Base64 (RFC 4648 §4) — total pure encoder -/

/-- The standard base64 alphabet (RFC 4648 §4). -/
def b64Alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

/-- The base64 character for a 6-bit value. -/
def b64Char (n : Nat) : Char := b64Alphabet.getD (n % 64) 'A'

/-- Base64-encode a byte list (RFC 4648 §4, with `=` padding). -/
def base64Encode : List UInt8 → String
  | [] => ""
  | [b0] =>
    let n := b0.toNat * 65536
    String.mk [b64Char (n / 262144), b64Char (n / 4096), '=', '=']
  | [b0, b1] =>
    let n := b0.toNat * 65536 + b1.toNat * 256
    String.mk [b64Char (n / 262144), b64Char (n / 4096), b64Char (n / 64), '=']
  | b0 :: b1 :: b2 :: rest =>
    let n := b0.toNat * 65536 + b1.toNat * 256 + b2.toNat
    String.mk [b64Char (n / 262144), b64Char (n / 4096), b64Char (n / 64), b64Char n]
      ++ base64Encode rest

/-! ## The opening handshake (RFC 6455 §1.3, §4.1) -/

/-- The fixed handshake GUID (RFC 6455 §1.3). -/
def magicGuid : String := "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- The `Sec-WebSocket-Accept` value the server must return for a given
`Sec-WebSocket-Key`: `base64(SHA-1(key ‖ GUID))` (RFC 6455 §4.2.2 step 5 /
§1.3). This is the exact RFC computation. -/
def acceptKey (clientKey : String) : String :=
  base64Encode (sha1 (clientKey ++ magicGuid).toUTF8.toList)

/-- The `Sec-WebSocket-Key` a client sends: the base64 of its 16-octet nonce
(RFC 6455 §4.1). -/
def clientKeyOf (nonce : List UInt8) : String := base64Encode nonce

/-- The client's §4.1 verification of the server reply: accept the handshake
exactly when the returned accept equals the RFC value for the key it sent. -/
def clientVerifyAccept (serverAccept clientKey : String) : Bool :=
  serverAccept == acceptKey clientKey

/-- **Handshake acceptance (RFC 6455 §4.1).** The client accepts the server reply
**iff** it is the RFC `base64(SHA-1(key ‖ GUID))` for the key it sent: the honest
server's accept passes, and any other value is rejected. -/
theorem ws_client_handshake (serverAccept clientKey : String) :
    clientVerifyAccept serverAccept clientKey = true ↔ serverAccept = acceptKey clientKey := by
  unfold clientVerifyAccept
  exact beq_iff_eq

/-- The honest server's accept passes verification (the ⇐ direction, spelled
out): the client always accepts the RFC-correct reply for its own key. -/
theorem ws_client_handshake_honest (clientKey : String) :
    clientVerifyAccept (acceptKey clientKey) clientKey = true :=
  (ws_client_handshake _ _).mpr rfl

/-- **Soundness / mutant:** any reply that is *not* the RFC value is rejected — a
server (or attacker) that returns a wrong accept fails the client's check. -/
theorem ws_client_handshake_sound (serverAccept clientKey : String)
    (h : serverAccept ≠ acceptKey clientKey) :
    clientVerifyAccept serverAccept clientKey = false := by
  unfold clientVerifyAccept
  exact beq_eq_false_iff_ne.mpr h

/-! ## Client-to-server frames (RFC 6455 §5.2, §5.3) -/

/-- Encode a client-to-server frame on the wire (RFC 6455 §5.2, §5.3): FIN and
opcode in byte 0, the **mask bit set** and 7-bit length in byte 1, the extended
length on the minimal rung (`Ws.encodeLenField`), the 4-octet masking `key`, then
the payload masked by the §5.3 transform (`Ws.applyMask`). The FIN/opcode and
mask/length fields occupy disjoint bit ranges, so the field sum equals the wire
`|`-packing. -/
def encodeClientFrame (key : Bytes) (f : Frame) : Bytes :=
  let b0 := UInt8.ofNat ((if f.fin then 128 else 0) + Reactor.Ws.opcodeNat f.opcode)
  let enc := Ws.encodeLenField f.payload.length
  let b1 := UInt8.ofNat (128 + enc.1)
  b0 :: b1 :: (enc.2 ++ key ++ Ws.applyMask key f.payload)

/-! ### Bit lemmas for the header bytes -/

/-- Bit 7 of `128 + o` for a sub-`2⁷` field is set. -/
theorem testBit7_add (o : Nat) (h : o < 128) : (128 + o).testBit 7 = true := by
  have hpow : (2 : Nat) ^ 7 = 128 := rfl
  have := Nat.testBit_two_pow_add_eq o 7
  rw [hpow] at this
  rw [this, Nat.testBit_lt_two_pow (by rw [hpow]; exact h)]
  rfl

/-- Bit 7 of a sub-`2⁷` value is clear. -/
theorem testBit7_lt (o : Nat) (h : o < 128) : o.testBit 7 = false :=
  Nat.testBit_lt_two_pow (by change o < 2 ^ 7; exact h)

/-- The minimal length marker is at most 127 (it never collides with the mask
bit). -/
theorem lenMarker_le (n : Nat) : Ws.lenMarker n ≤ 127 := by
  unfold Ws.lenMarker
  split
  · omega
  · split <;> omega

/-! ### The masking invariant -/

/-- **Clients always mask (RFC 6455 §5.3).** Byte 1 of any frame
`encodeClientFrame` produces has the mask bit (bit 7) set — for every payload
length. -/
theorem ws_client_masks (key : Bytes) (f : Frame) :
    ∃ b0 b1 rest, encodeClientFrame key f = b0 :: b1 :: rest ∧ b1.toNat.testBit 7 = true := by
  refine ⟨_, _, _, rfl, ?_⟩
  show (UInt8.ofNat (128 + (Ws.encodeLenField f.payload.length).1)).toNat.testBit 7 = true
  have hm : (Ws.encodeLenField f.payload.length).1 = Ws.lenMarker f.payload.length := rfl
  rw [hm]
  have hle := lenMarker_le f.payload.length
  have hlt : 128 + Ws.lenMarker f.payload.length < 256 := by omega
  rw [u8_toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact testBit7_add _ (by omega)

/-! ### The client-to-server frame round trip -/

/-- **Client frame round trip (RFC 6455 §5.2, §5.3).** A masked client frame
decodes, through the real server-side decoder `Reactor.Ws.decodeFrame`, back to
exactly the frame that was sent: same FIN, same opcode, and the payload recovered
by unmasking with the emitted key. Stated for a well-formed client frame — a
4-octet mask key, a defined opcode (`opcode` round-trips its nibble), and an
inline-length payload (`≤ 125` octets) — which is the common case; the mask
transform is exercised in full generality over the payload and key. -/
theorem ws_client_frame_roundtrip (key : Bytes) (f : Frame)
    (hkey : key.length = 4)
    (hop : Opcode.ofNat (Reactor.Ws.opcodeNat f.opcode) = f.opcode)
    (hlt : Reactor.Ws.opcodeNat f.opcode < 16)
    (hlen : f.payload.length ≤ 125) :
    Reactor.Ws.decodeFrame (encodeClientFrame key f) = some (f, []) := by
  rw [WsFrameCorrect.decodeFrame_eq_specDecode]
  have hMlen : (Ws.applyMask key f.payload).length = f.payload.length :=
    Ws.applyMask_length key f.payload
  -- Header byte 0: FIN + opcode, disjoint fields
  have hb0lt : (if f.fin then 128 else 0) + Reactor.Ws.opcodeNat f.opcode < 256 := by
    cases f.fin <;> simp <;> omega
  have hb0nat : (UInt8.ofNat ((if f.fin then 128 else 0) + Reactor.Ws.opcodeNat f.opcode)).toNat
      = (if f.fin then 128 else 0) + Reactor.Ws.opcodeNat f.opcode := by
    rw [u8_toNat_ofNat, Nat.mod_eq_of_lt hb0lt]
  -- length field is inline: marker = length, ext = []
  have hmk : (Ws.encodeLenField f.payload.length).1 = f.payload.length := by
    show Ws.lenMarker f.payload.length = f.payload.length
    unfold Ws.lenMarker; rw [if_pos (by omega)]
  have hext : (Ws.encodeLenField f.payload.length).2 = [] := by
    show Ws.lenExt f.payload.length = []
    unfold Ws.lenExt; rw [if_pos (by omega)]
  have hb1lt : 128 + (Ws.encodeLenField f.payload.length).1 < 256 := by rw [hmk]; omega
  have hb1nat : (UInt8.ofNat (128 + (Ws.encodeLenField f.payload.length).1)).toNat
      = 128 + f.payload.length := by
    rw [u8_toNat_ofNat, Nat.mod_eq_of_lt hb1lt, hmk]
  -- Field extractions
  have hfin : WsFrameCorrect.hiBit ((if f.fin then 128 else 0)
      + Reactor.Ws.opcodeNat f.opcode) = f.fin := by
    unfold WsFrameCorrect.hiBit
    cases hf : f.fin
    · rw [if_neg (by simp), Nat.zero_add]; exact testBit7_lt _ (by omega)
    · rw [if_pos rfl]; exact testBit7_add _ (by omega)
  have hnib : Opcode.ofNat (WsFrameCorrect.nibble ((if f.fin then 128 else 0)
      + Reactor.Ws.opcodeNat f.opcode)) = f.opcode := by
    unfold WsFrameCorrect.nibble
    have hmod : ((if f.fin then 128 else 0) + Reactor.Ws.opcodeNat f.opcode) % 16
        = Reactor.Ws.opcodeNat f.opcode := by cases f.fin <;> simp <;> omega
    rw [hmod, hop]
  have hmask : WsFrameCorrect.hiBit (128 + f.payload.length) = true := by
    unfold WsFrameCorrect.hiBit; exact testBit7_add _ (by omega)
  have hl7 : WsFrameCorrect.len7 (128 + f.payload.length) = f.payload.length := by
    unfold WsFrameCorrect.len7; omega
  have hec : WsFrameCorrect.extCount f.payload.length = 0 := by
    unfold WsFrameCorrect.extCount; rw [if_neg (by omega), if_neg (by omega)]
  have hsl : WsFrameCorrect.specLen f.payload.length [] = f.payload.length := by
    unfold WsFrameCorrect.specLen; rw [if_pos (by omega)]
  -- Reduce specDecode
  simp only [encodeClientFrame, WsFrameCorrect.specDecode, hext, List.nil_append,
    hb0nat, hb1nat, hfin, hnib, hmask, hl7, hec, List.take_zero, List.length_nil,
    Nat.lt_irrefl, if_false, List.drop_zero, hsl, if_true]
  -- The buffer is `key ++ M`; extract the 4-byte key then the masked payload.
  rw [List.take_left' hkey]
  simp only [hkey, Nat.lt_irrefl, if_false]
  rw [List.drop_left' hkey]
  rw [show f.payload.length = (Ws.applyMask key f.payload).length from hMlen.symm,
      List.take_length, List.drop_length]
  simp only [Nat.lt_irrefl, if_false]
  -- Unmask: xorCycle key (applyMask key payload) = applyMask key (applyMask key payload) = payload.
  rw [← WsFrameCorrect.applyMask_eq_xorCycle, Ws.applyMask_involution]

end Ws.Client
