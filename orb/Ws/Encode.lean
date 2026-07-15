import Ws.Decode
import Ws.Mask
import Ws.ReassemblyClose

/-!
# The outbound server-frame encoder (RFC 6455 §5.1/§5.2/§5.5.1) — in the core

The inbound half of the open-connection frame codec is already governed: the
header verdict is `Ws.Decode.decodeHeader`, the reassembly admission, UTF-8,
and close-body decisions are the proven core's. The OUTBOUND half — the bytes
this endpoint writes: echo frames, pongs, and close frames — was still host
code: a hand-rolled header assembly (FIN/opcode octet, the three-rung length
ladder, no mask per §5.1) that no theorem connected to the proven grammar.
A misencoded rung or a stray mask bit there desyncs every conforming peer.

This module lifts the construction into the core:

* `frameHeader fin op n` — the §5.2 server-frame header for a payload of
  length `n`: FIN·2⁷ + opcode, the **proven canonical ladder**
  (`Ws.lenMarker` / `Ws.lenExt`, minimal rung per §5.2's sender rule), and the
  mask bit ZERO (§5.1: a server MUST NOT mask).
* `encodeFrame fin op payload = frameHeader ‥ payload.length ++ payload` — the
  full frame factors as header ++ payload (`encodeFrame_eq`), so a host may
  append the payload bytes itself: its contribution is a memcpy, never a
  header decision.
* `encodeClose code = encodeFrame true 8 (toBE16 code)` — the §5.5.1 close
  frame: 2-octet big-endian status code, empty reason, 4 octets total
  (`encodeClose_bytes`).

The round trip, against the PROVEN inbound side:

* `decode_maskedWire` — **decode inverts encode**: the emitted frame, put on
  the client wire (mask bit set, a 4-octet key inserted, payload masked per
  §5.3 — `maskedWire`, the only transform separating a server frame from a
  client one), is admitted by the proven header verdict
  (`Ws.Decode.decodeHeader`) with EXACTLY the encoded fin/opcode/length/key.
* `payload_roundtrip` — unmasking the wire tail past the decoded header
  (`Ws.Mask.applyMask`, the proven involution) recovers the encoded payload
  byte-for-byte. `encode_decode_roundtrip` states both together.
* `closeBody_encodeClose` — the close body this endpoint emits round-trips
  through the proven inbound close-body verdict
  (`Ws.ReassemblyClose.closeBody`) to `echo code`: a peer running this same
  proven machinery reads back exactly the code we sent.
* `frameHeader_unmasked` / `frameHeader_length` / `encodeFrame_canonical` —
  the mask bit is provably zero, the header is `2 + extCount` octets (≤ 10),
  and the emitted length field is ladder-canonical (the §5.2 sender MUST).
* Kernel-checked vectors, including the RFC 6455 §1.3 pair: the server
  `"Hello"` frame `81 05 48 65 6c 6c 6f`, and its client-wire image under the
  §1.3 key equal to the §1.3 masked example octet-for-octet.

`drorb_ws_encode_header` (`@[export]`) is the C-ABI seam: (fin, opcode,
payload length) in, the header octets out — 2 ≤ size ≤ 10
(`frameHeaderExport_size_bounds`), the shape the host asserts before copying.
`drorb_ws_encode_close` returns the complete 4-octet close frame
(`encodeCloseExport_size`). The host's outbound codec keeps only the payload
memcpy; every header octet it writes is this module's.
-/

namespace Ws
namespace Encode

/-! ## The encoder -/

/-- The §5.2 SERVER-frame header for a payload of length `n`: octet 0 is
FIN·2⁷ + opcode, octet 1 is the canonical ladder marker with the mask bit
ZERO (§5.1 — a server never masks), then the canonical extended-length octets
(`Ws.lenExt`, minimal rung per the §5.2 sender rule). -/
def frameHeader (fin : Bool) (op : Nat) (n : Nat) : Bytes :=
  UInt8.ofNat ((if fin then 128 else 0) + op)
    :: UInt8.ofNat (lenMarker n)
    :: lenExt n

/-- Encode one complete server frame: the header for the payload's length,
then the payload verbatim (unmasked, §5.1). -/
def encodeFrame (fin : Bool) (op : Nat) (payload : Bytes) : Bytes :=
  frameHeader fin op payload.length ++ payload

/-- The §5.5.1 close frame carrying status `code` and an empty reason: FIN
close with the 2-octet big-endian code as its whole payload. -/
def encodeClose (code : Nat) : Bytes :=
  encodeFrame true 8 (toBE16 code)

/-- **The header/payload factorization.** The frame is exactly the header
followed by the payload — so a host that obtains the header from this module
and appends the payload bytes itself writes this module's frame: its
contribution is data movement, not a single header decision. -/
theorem encodeFrame_eq (fin : Bool) (op : Nat) (payload : Bytes) :
    encodeFrame fin op payload = frameHeader fin op payload.length ++ payload := rfl

/-! ## Header shape: size and the §5.1 mask bit -/

/-- The header is exactly `2 + extCount` octets — the fixed two plus the
canonical extended-length octets. -/
theorem frameHeader_length (fin : Bool) (op n : Nat) :
    (frameHeader fin op n).length = 2 + Decode.extCount (lenMarker n) := by
  simp only [frameHeader, List.length_cons, Decode.lenExt_length]
  omega

/-- A header never exceeds 10 octets (2 fixed + at most 8 extended-length —
no key octets: server frames carry none). -/
theorem frameHeader_le_10 (fin : Bool) (op n : Nat) :
    (frameHeader fin op n).length ≤ 10 := by
  have := Decode.extCount_le (lenMarker n)
  rw [frameHeader_length]
  omega

/-- **§5.1 — the mask bit is zero.** Octet 1 of every emitted header is the
bare ladder marker, below 128: a frame from this encoder can never claim to
be masked. -/
theorem frameHeader_unmasked (fin : Bool) (op n : Nat) :
    ∃ b0 rest, frameHeader fin op n = b0 :: UInt8.ofNat (lenMarker n) :: rest
      ∧ (UInt8.ofNat (lenMarker n)).toNat < 128 := by
  refine ⟨_, _, rfl, ?_⟩
  have := Decode.lenMarker_lt n
  rw [toNat_ofNat]
  omega

/-- **The §5.2 sender rule.** The emitted length field is ladder-canonical:
the marker sits on the minimal rung that fits the payload length. -/
theorem encodeFrame_canonical (payload : Bytes)
    (h : payload.length < 2 ^ 64) :
    LenFieldCanonical (lenMarker payload.length) (lenExt payload.length) :=
  encodeLenField_canonical payload.length h

/-! ## The client-wire image and the round trip -/

/-- Put a server frame on the CLIENT wire — the transform a conforming client
applies to the same logical frame (§5.1/§5.3): set the mask bit on octet 1,
insert a 4-octet key after the extended length, and mask the payload. This is
the only difference between the two directions, so decoding this image with
the proven inbound verdict is the round trip. -/
def maskedWire (key : Bytes) : Bytes → Bytes
  | b0 :: b1 :: rest =>
    b0 :: UInt8.ofNat (128 + b1.toNat % 128)
      :: (rest.take (Decode.extCount (b1.toNat % 128)) ++ key
          ++ applyMask key (rest.drop (Decode.extCount (b1.toNat % 128))))
  | bs => bs

/-- The client-wire image of an emitted frame is exactly the proven grammar's
header (`Ws.Decode.encodeHeader`) followed by the masked payload. -/
theorem maskedWire_encodeFrame (key : Bytes) (fin : Bool) (op : Nat) (payload : Bytes) :
    maskedWire key (encodeFrame fin op payload)
      = Decode.encodeHeader fin op key payload.length ++ applyMask key payload := by
  have hmlt := Decode.lenMarker_lt payload.length
  have hm : (UInt8.ofNat (lenMarker payload.length)).toNat % 128
      = lenMarker payload.length := by
    rw [toNat_ofNat]; omega
  simp only [encodeFrame, frameHeader, List.cons_append, maskedWire]
  rw [hm, ← Decode.lenExt_length, List.take_left, List.drop_left]
  simp only [Decode.encodeHeader, List.cons_append, List.append_assoc]

/-- The proven grammar's header is `2 + extCount + 4` octets (given the
4-octet key). -/
theorem encodeHeader_length (fin : Bool) (op : Nat) (key : Bytes) (n : Nat)
    (hkey : key.length = 4) :
    (Decode.encodeHeader fin op key n).length
      = 2 + Decode.extCount (lenMarker n) + 4 := by
  simp only [Decode.encodeHeader, List.length_cons, List.length_append,
    Decode.lenExt_length, hkey]
  omega

/-- **Decode inverts encode (header).** The client-wire image of any emitted
frame — a defined opcode, any 4-octet key, a length below 2⁶³, the §5.5 shape
if control — is ADMITTED by the proven inbound header verdict with exactly
the encoded FIN, opcode, payload length, and the inserted key. -/
theorem decode_maskedWire (key : Bytes) (fin : Bool) (op : Nat) (payload : Bytes)
    (hop : isDefinedOpcode op = true) (hkey : key.length = 4)
    (hn : payload.length < 2 ^ 63)
    (hctl : (Opcode.ofNat op).isControl = true → fin = true ∧ payload.length ≤ 125) :
    Decode.decodeHeader (maskedWire key (encodeFrame fin op payload))
      = .done
          { fin := fin, opcode := Opcode.ofNat op
            len := payload.length, mask := key }
          (2 + Decode.extCount (lenMarker payload.length) + 4) := by
  rw [maskedWire_encodeFrame]
  exact Decode.decode_encode fin op key payload.length (applyMask key payload)
    hop hkey hn hctl

/-- **Decode inverts encode (payload).** Unmasking the wire octets past the
decoded header (the proven involution, `Ws.Mask.applyMask`) recovers the
encoded payload byte-for-byte. -/
theorem payload_roundtrip (key : Bytes) (fin : Bool) (op : Nat) (payload : Bytes)
    (hkey : key.length = 4) :
    applyMask key ((maskedWire key (encodeFrame fin op payload)).drop
        (2 + Decode.extCount (lenMarker payload.length) + 4)) = payload := by
  rw [maskedWire_encodeFrame, ← encodeHeader_length fin op key payload.length hkey,
    List.drop_left, applyMask_involution]

/-- **The encode/decode round trip, in one statement.** A peer running the
proven inbound machinery on the client-wire image of an emitted frame reads
back exactly what was encoded: the header verdict admits (fin, opcode,
length, key), and unmasking the remainder yields the payload. -/
theorem encode_decode_roundtrip (key : Bytes) (fin : Bool) (op : Nat) (payload : Bytes)
    (hop : isDefinedOpcode op = true) (hkey : key.length = 4)
    (hn : payload.length < 2 ^ 63)
    (hctl : (Opcode.ofNat op).isControl = true → fin = true ∧ payload.length ≤ 125) :
    Decode.decodeHeader (maskedWire key (encodeFrame fin op payload))
      = .done
          { fin := fin, opcode := Opcode.ofNat op
            len := payload.length, mask := key }
          (2 + Decode.extCount (lenMarker payload.length) + 4)
    ∧ applyMask key ((maskedWire key (encodeFrame fin op payload)).drop
        (2 + Decode.extCount (lenMarker payload.length) + 4)) = payload :=
  ⟨decode_maskedWire key fin op payload hop hkey hn hctl,
   payload_roundtrip key fin op payload hkey⟩

/-! ## The close frame -/

/-- The close frame, octet-exact: `88 02` then the big-endian code. -/
theorem encodeClose_bytes (code : Nat) :
    encodeClose code = 0x88 :: 0x02 :: toBE16 code := rfl

/-- The emitted close frame is frame-well-formed (`Ws.Frame.Wf`): FIN control,
2-octet payload — in particular never the §5.5.1 length-1 protocol error. -/
theorem encodeClose_wf (code : Nat) :
    Frame.Wf { fin := true, opcode := .close, payload := toBE16 code } :=
  ⟨fun _ => ⟨rfl, by rw [toBE16_length]; omega⟩,
   fun _ => by rw [toBE16_length]; omega⟩

/-- **The close-code round trip.** The close body this endpoint emits, fed to
the PROVEN inbound close-body verdict (the one the host's own close machinery
crosses), is echoed with exactly the code we sent — for every 16-bit code the
§7.4 registry admits. -/
theorem closeBody_encodeClose (code : Nat) (hlt : code < 2 ^ 16)
    (hok : Decode.closeCodeOk code = true) :
    ReassemblyClose.closeBody (toBE16 code) = .echo code := by
  have hcode : (UInt8.ofNat (code / 256)).toNat * 256 + (UInt8.ofNat code).toNat
      = code := by
    rw [toNat_ofNat, toNat_ofNat]; omega
  have h := ReassemblyClose.echo_complete (b0 := UInt8.ofNat (code / 256))
    (b1 := UInt8.ofNat code) (reason := [])
    (by rw [hcode]; exact hok) (by decide)
  rw [hcode] at h
  exact h

/-- The header round trip, instantiated at the close frame: the client-wire
image of `encodeClose` is admitted as a FIN close of length 2 with `used = 6`. -/
theorem decode_maskedWire_close (key : Bytes) (code : Nat) (hkey : key.length = 4) :
    Decode.decodeHeader (maskedWire key (encodeClose code))
      = .done { fin := true, opcode := .close, len := 2, mask := key } 6 :=
  decode_maskedWire key true 8 (toBE16 code) (by decide) hkey
    (by rw [toBE16_length]; omega)
    (fun _ => ⟨rfl, by rw [toBE16_length]; omega⟩)

/-- The close codes this endpoint originates (normal, protocol-error,
invalid-payload, too-big) are all registry-admitted, so `closeBody_encodeClose`
covers every close frame the host constructs. -/
theorem sent_codes_registered :
    Decode.closeCodeOk closeNormal ∧ Decode.closeCodeOk closeProtocolError
      ∧ Decode.closeCodeOk ReassemblyClose.closeInvalidPayload
      ∧ Decode.closeCodeOk closeTooBig := by decide

/-! ## Kernel-checked wire vectors (non-vacuity) -/

/-- RFC 6455 §1.3, server side: the unmasked `"Hello"` text frame is
`81 05` + the payload. -/
theorem vec_hello : encodeFrame true 0x1 [0x48, 0x65, 0x6c, 0x6c, 0x6f]
    = [0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] := by decide

/-- RFC 6455 §1.3, the round trip made concrete: the client-wire image of our
server `"Hello"` frame under the §1.3 key is the §1.3 masked example,
octet-for-octet — the exact bytes `Ws.Decode.vec_hello_admitted` admits. -/
theorem vec_hello_wire :
    maskedWire [0x37, 0xfa, 0x21, 0x3d]
        (encodeFrame true 0x1 [0x48, 0x65, 0x6c, 0x6c, 0x6f])
      = [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] := by decide

/-- An empty pong is `8A 00`. -/
theorem vec_pong_empty : encodeFrame true 0xA [] = [0x8A, 0x00] := by decide

/-- A normal-closure close frame is `88 02 03 E8`. -/
theorem vec_close_1000 : encodeClose 1000 = [0x88, 0x02, 0x03, 0xE8] := by decide

/-- …and its body echoes through the proven inbound verdict as 1000. -/
theorem vec_close_1000_roundtrip :
    ReassemblyClose.closeBody (toBE16 1000) = .echo 1000 := by decide

/-- The 16-bit rung, at its lower boundary: a 126-octet payload's header. -/
theorem vec_16bit_rung : frameHeader true 0x2 126 = [0x82, 126, 0x00, 0x7E] := by decide

/-- The 64-bit rung: a 70000-octet payload's header (70000 = 0x11170). -/
theorem vec_64bit_rung : frameHeader true 0x2 70000
    = [0x82, 127, 0, 0, 0, 0, 0, 0x01, 0x11, 0x70] := by decide

/-! ## The host-facing C-ABI seam -/

/-- **`drorb_ws_encode_header`.** The seam the host's outbound codec crosses
instead of assembling the header itself: (fin, opcode nibble, payload length)
in, the header octets out. The host appends the payload bytes after it
(`encodeFrame_eq`). The opcode rides its low nibble; the length is the full
64-bit payload length. -/
@[export drorb_ws_encode_header]
def frameHeaderExport (fin : UInt8) (op : UInt8) (len : UInt64) : ByteArray :=
  ByteArray.mk (frameHeader (fin != 0) (op.toNat % 16) len.toNat).toArray

/-- **`drorb_ws_encode_close`.** The complete 4-octet close frame carrying
`code` (low 16 bits) and an empty reason. -/
@[export drorb_ws_encode_close]
def encodeCloseExport (code : UInt32) : ByteArray :=
  ByteArray.mk (encodeClose (code.toNat % 2 ^ 16)).toArray

/-- The exported header is `2 + extCount` octets. -/
theorem frameHeaderExport_size (fin op : UInt8) (len : UInt64) :
    (frameHeaderExport fin op len).size
      = 2 + Decode.extCount (lenMarker len.toNat) := by
  simp only [frameHeaderExport, ByteArray.size, ByteArray.data,
    Array.size_toArray]
  exact frameHeader_length _ _ _

/-- **The ABI shape the host asserts**: an exported header is 2–10 octets. -/
theorem frameHeaderExport_size_bounds (fin op : UInt8) (len : UInt64) :
    2 ≤ (frameHeaderExport fin op len).size
      ∧ (frameHeaderExport fin op len).size ≤ 10 := by
  have := Decode.extCount_le (lenMarker len.toNat)
  rw [frameHeaderExport_size]
  omega

/-- **The ABI shape the host asserts**: an exported close frame is exactly 4
octets. -/
theorem encodeCloseExport_size (code : UInt32) :
    (encodeCloseExport code).size = 4 := by
  simp only [encodeCloseExport, ByteArray.size, ByteArray.data,
    Array.size_toArray, encodeClose_bytes, List.length_cons, toBE16_length]

/-- **ABI vector.** The exported close frame for 1000, octet by octet. -/
theorem vec_close_abi :
    (encodeCloseExport 1000).data = #[0x88, 0x02, 0x03, 0xE8] := by decide

/-- **ABI vector.** The exported header for the §1.3 server `"Hello"` frame. -/
theorem vec_header_abi :
    (frameHeaderExport 1 0x1 5).data = #[0x81, 0x05] := by decide

end Encode
end Ws
