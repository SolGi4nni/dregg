import H2.Frame

/-!
# HTTP/2 frame **encoding** (RFC 9113 §4, §6) — the dual of `H2.Frame.decode`

`H2/Frame.lean` decodes the 9-octet frame header and the frame taxonomy into a
`Frame`. This module is the **encoder**: `encodeFrame : Frame → Bytes` lays each
frame back onto the wire, and every constructor round-trips against the *existing*
decoder — `decode (encodeFrame f) mfs = .complete f (9 + payloadLen)` — so a
drorb H2 client and a drorb H2 server agree on every framing octet.

The header layout is exactly the one `parseHeader` inverts (RFC 9113 §4.1):

```text
Length (24) | Type (8) | Flags (8) | R(1)+Stream Id (31) | Payload (0..)
```

* `frameHdr` — the 9-octet header encoder; the stream id is masked to 31 bits
  (the reserved `R` bit is sent clear, matching the parse mask).
* `encodeFrame` — one wire image per `Frame` constructor. The surfaced flags
  (`END_STREAM` bit 0, `END_HEADERS` bit 2, `ACK` bit 0) are re-laid into the
  flags octet; every other flag bit is sent clear.
* `decode_encode_frame` — the headline round-trip: for any frame whose stream id
  is a 31-bit value and whose payload is within `2^24` and the size limit, the
  existing decoder recovers the frame exactly (an unknown/extension type
  additionally needs its type octet to classify as unknown). Per-type corollaries
  (`decode_encode_data`, `decode_encode_headers`, …) discharge each frame kind.

Grounded on concrete wire octets (`example … := rfl`) so no theorem is vacuous.
-/

namespace H2
namespace FrameEncode

open H2

/-! ## Big-endian field encoders (RFC 9113 §4.1) -/

/-- Big-endian 24-bit (the frame Length field). -/
def be24 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Big-endian 32-bit (the reserved-bit + stream-identifier word). -/
def be32 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- The 9-octet frame header (RFC 9113 §4.1). The stream id is masked to 31 bits,
so the reserved high bit is always sent clear — matching `parseHeader`'s mask. -/
def frameHdr (len ty fl sid : Nat) : Bytes :=
  be24 len ++ [UInt8.ofNat ty, UInt8.ofNat fl] ++ be32 (sid % 2 ^ 31)

theorem frameHdr_length (len ty fl sid : Nat) : (frameHdr len ty fl sid).length = 9 := rfl

/-- **Header-parse inverts the header encoder**: `parseHeader` recovers exactly
the fields `frameHdr` was given (length < 2^24, type/flags octets < 256, stream
id < 2^31), for any following bytes. -/
theorem parseHeader_frameHdr (len ty fl sid : Nat) (rest : Bytes)
    (hlen : len < 2 ^ 24) (hty : ty < 256) (hfl : fl < 256) (hsid : sid < 2 ^ 31) :
    parseHeader (frameHdr len ty fl sid ++ rest)
      = some { length := len, frameType := ty, flags := fl, streamId := sid } := by
  simp only [frameHdr, be24, be32, List.cons_append, List.nil_append,
    List.append_assoc, parseHeader, parseHeaderAux, Option.some.injEq,
    FrameHeader.mk.injEq, UInt8.toNat_ofNat']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ## Flag-octet lemmas -/

/-- The `END_STREAM`/`ACK` bit (bit 0) round-trips through `flagSet`. -/
theorem flagSet_bit0 (b : Bool) : flagSet (if b then 1 else 0) 0 = b := by
  cases b <;> rfl

/-- The `END_HEADERS` bit (bit 2) round-trips through `flagSet`. -/
theorem flagSet_bit2 (b : Bool) : flagSet (if b then 4 else 0) 2 = b := by
  cases b <;> rfl

/-- A HEADERS frame carries both bits; each reads back independently. -/
theorem flagSet_headers0 (es eh : Bool) :
    flagSet ((if es then 1 else 0) + (if eh then 4 else 0)) 0 = es := by
  cases es <;> cases eh <;> rfl

theorem flagSet_headers2 (es eh : Bool) :
    flagSet ((if es then 1 else 0) + (if eh then 4 else 0)) 2 = eh := by
  cases es <;> cases eh <;> rfl

/-! ## The frame encoder -/

/-- Encode one `Frame` to its wire octets (RFC 9113 §6). Payloads are laid raw;
the surfaced flags are re-laid into the flags octet and every other flag bit is
clear. An `unknown` frame is laid with a zeroed payload of its declared length —
the decoder discards an unknown payload, so only type/stream/length matter. -/
def encodeFrame : Frame → Bytes
  | .data sid es payload =>
    frameHdr payload.length 0x0 (if es then 1 else 0) sid ++ payload
  | .headers sid es eh payload =>
    frameHdr payload.length 0x1 ((if es then 1 else 0) + (if eh then 4 else 0)) sid ++ payload
  | .priority sid payload => frameHdr payload.length 0x2 0 sid ++ payload
  | .rstStream sid payload => frameHdr payload.length 0x3 0 sid ++ payload
  | .settings sid ack payload =>
    frameHdr payload.length 0x4 (if ack then 1 else 0) sid ++ payload
  | .pushPromise sid payload => frameHdr payload.length 0x5 0 sid ++ payload
  | .ping sid ack payload =>
    frameHdr payload.length 0x6 (if ack then 1 else 0) sid ++ payload
  | .goaway sid payload => frameHdr payload.length 0x7 0 sid ++ payload
  | .windowUpdate sid payload => frameHdr payload.length 0x8 0 sid ++ payload
  | .continuation sid eh payload =>
    frameHdr payload.length 0x9 (if eh then 4 else 0) sid ++ payload
  | .unknown ft sid len => frameHdr len ft 0 sid ++ List.replicate len 0

/-- The stream id an encoded frame carries. -/
def encStreamId : Frame → Nat
  | .data s _ _ => s
  | .headers s _ _ _ => s
  | .priority s _ => s
  | .rstStream s _ => s
  | .settings s _ _ => s
  | .pushPromise s _ => s
  | .ping s _ _ => s
  | .goaway s _ => s
  | .windowUpdate s _ => s
  | .continuation s _ _ => s
  | .unknown _ s _ => s

/-- The declared payload length an encoded frame carries. -/
def encPayloadLen : Frame → Nat
  | .data _ _ p => p.length
  | .headers _ _ _ p => p.length
  | .priority _ p => p.length
  | .rstStream _ p => p.length
  | .settings _ _ p => p.length
  | .pushPromise _ p => p.length
  | .ping _ _ p => p.length
  | .goaway _ p => p.length
  | .windowUpdate _ p => p.length
  | .continuation _ _ p => p.length
  | .unknown _ _ l => l

/-! ## The round-trip: `decode (encodeFrame f) = f`

The common core: after the header inverts and the two guards pass (within the
size limit, payload fully present), `decode` reduces to the taxonomy dispatch on
the encoded octets. -/

/-- The post-header reduction of a decode over an encoded frame. -/
theorem decode_frameHdr_reduce (ty fl sid : Nat) (payload : Bytes) (mfs : Nat)
    (hlen : payload.length < 2 ^ 24) (hty : ty < 256) (hfl : fl < 256)
    (hsid : sid < 2 ^ 31) (hmfs : payload.length ≤ mfs) :
    decode (frameHdr payload.length ty fl sid ++ payload) mfs =
      (match FrameType.ofNat ty with
       | .data => .complete (.data sid (flagSet fl 0) payload) (9 + payload.length)
       | .headers =>
         .complete (.headers sid (flagSet fl 0) (flagSet fl 2) payload) (9 + payload.length)
       | .priority => .complete (.priority sid payload) (9 + payload.length)
       | .rstStream => .complete (.rstStream sid payload) (9 + payload.length)
       | .settings => .complete (.settings sid (flagSet fl 0) payload) (9 + payload.length)
       | .pushPromise => .complete (.pushPromise sid payload) (9 + payload.length)
       | .ping => .complete (.ping sid (flagSet fl 0) payload) (9 + payload.length)
       | .goaway => .complete (.goaway sid payload) (9 + payload.length)
       | .windowUpdate => .complete (.windowUpdate sid payload) (9 + payload.length)
       | .continuation =>
         .complete (.continuation sid (flagSet fl 2) payload) (9 + payload.length)
       | .unknown t => .complete (.unknown t sid payload.length) (9 + payload.length)) := by
  have hcomp : ¬ (frameHdr payload.length ty fl sid ++ payload).length < 9 + payload.length := by
    rw [List.length_append, frameHdr_length]; omega
  have hdrop : (frameHdr payload.length ty fl sid ++ payload).drop 9 = payload := by
    rw [← frameHdr_length payload.length ty fl sid]; exact List.drop_left
  have htake : payload.take payload.length = payload := List.take_length
  unfold decode
  rw [parseHeader_frameHdr payload.length ty fl sid payload hlen hty hfl hsid]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr hmfs), if_neg hcomp, hdrop, htake]
  rfl

/-! ### Per-type corollaries (one per frame kind, RFC 9113 §6) -/

theorem decode_encode_data (sid : Nat) (es : Bool) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.data sid es payload)) mfs
      = .complete (.data sid es payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x0 (if es then 1 else 0) sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x0 (if es then 1 else 0) sid payload mfs hlen
      (by cases es <;> decide) (by cases es <;> decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x0 = FrameType.data from rfl, flagSet_bit0]

theorem decode_encode_headers (sid : Nat) (es eh : Bool) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.headers sid es eh payload)) mfs
      = .complete (.headers sid es eh payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x1 ((if es then 1 else 0) + (if eh then 4 else 0)) sid
      ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x1 ((if es then 1 else 0) + (if eh then 4 else 0)) sid payload mfs
      hlen (by cases es <;> cases eh <;> decide) (by cases es <;> cases eh <;> decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x1 = FrameType.headers from rfl,
    flagSet_headers0, flagSet_headers2]

theorem decode_encode_rstStream (sid : Nat) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.rstStream sid payload)) mfs
      = .complete (.rstStream sid payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x3 0 sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x3 0 sid payload mfs hlen (by decide) (by decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x3 = FrameType.rstStream from rfl]

theorem decode_encode_settings (sid : Nat) (ack : Bool) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.settings sid ack payload)) mfs
      = .complete (.settings sid ack payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x4 (if ack then 1 else 0) sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x4 (if ack then 1 else 0) sid payload mfs hlen
      (by cases ack <;> decide) (by cases ack <;> decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x4 = FrameType.settings from rfl, flagSet_bit0]

theorem decode_encode_ping (sid : Nat) (ack : Bool) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.ping sid ack payload)) mfs
      = .complete (.ping sid ack payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x6 (if ack then 1 else 0) sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x6 (if ack then 1 else 0) sid payload mfs hlen
      (by cases ack <;> decide) (by cases ack <;> decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x6 = FrameType.ping from rfl, flagSet_bit0]

theorem decode_encode_goaway (sid : Nat) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.goaway sid payload)) mfs
      = .complete (.goaway sid payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x7 0 sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x7 0 sid payload mfs hlen (by decide) (by decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x7 = FrameType.goaway from rfl]

theorem decode_encode_windowUpdate (sid : Nat) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.windowUpdate sid payload)) mfs
      = .complete (.windowUpdate sid payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x8 0 sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x8 0 sid payload mfs hlen (by decide) (by decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x8 = FrameType.windowUpdate from rfl]

theorem decode_encode_priority (sid : Nat) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.priority sid payload)) mfs
      = .complete (.priority sid payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x2 0 sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x2 0 sid payload mfs hlen (by decide) (by decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x2 = FrameType.priority from rfl]

theorem decode_encode_pushPromise (sid : Nat) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.pushPromise sid payload)) mfs
      = .complete (.pushPromise sid payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x5 0 sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x5 0 sid payload mfs hlen (by decide) (by decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x5 = FrameType.pushPromise from rfl]

theorem decode_encode_continuation (sid : Nat) (eh : Bool) (payload : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : payload.length < 2 ^ 24) (hmfs : payload.length ≤ mfs) :
    decode (encodeFrame (.continuation sid eh payload)) mfs
      = .complete (.continuation sid eh payload) (9 + payload.length) := by
  show decode (frameHdr payload.length 0x9 (if eh then 4 else 0) sid ++ payload) mfs = _
  rw [decode_frameHdr_reduce 0x9 (if eh then 4 else 0) sid payload mfs hlen
      (by cases eh <;> decide) (by cases eh <;> decide) hsid hmfs]
  simp only [show FrameType.ofNat 0x9 = FrameType.continuation from rfl, flagSet_bit2]

theorem decode_encode_unknown (ft sid len : Nat) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : len < 2 ^ 24) (hmfs : len ≤ mfs) (hty : ft < 256)
    (hunk : isKnownType ft = false) :
    decode (encodeFrame (.unknown ft sid len)) mfs
      = .complete (.unknown ft sid len) (9 + len) := by
  have hrep : (List.replicate len (0 : UInt8)).length = len := List.length_replicate ..
  have key := decode_frameHdr_reduce ft 0 sid (List.replicate len 0) mfs
      (by rw [hrep]; exact hlen) hty (by decide) hsid (by rw [hrep]; exact hmfs)
  rw [hrep] at key
  show decode (frameHdr len ft 0 sid ++ List.replicate len 0) mfs = _
  rw [key, FrameType.ofNat_unknown ft hunk]

/-! ### The headline round-trip -/

/-- **Frame encode/decode round-trip** (RFC 9113 §4, §6): for any frame whose
stream id is a 31-bit value and whose payload fits within `2^24` and the peer's
`maxFrameSize`, the existing decoder recovers the frame exactly. An unknown type
additionally needs its type octet to classify as unknown (`isKnownType = false`,
a valid 8-bit non-standard type) — its payload is discarded by design, so only
type/stream/length are recovered. -/
theorem decode_encode_frame (f : Frame) (mfs : Nat)
    (hsid : encStreamId f < 2 ^ 31) (hlen : encPayloadLen f < 2 ^ 24)
    (hmfs : encPayloadLen f ≤ mfs)
    (hunk : ∀ t s l, f = .unknown t s l → isKnownType t = false ∧ t < 256) :
    decode (encodeFrame f) mfs = .complete f (9 + encPayloadLen f) := by
  cases f with
  | data s es p => exact decode_encode_data s es p mfs hsid hlen hmfs
  | headers s es eh p => exact decode_encode_headers s es eh p mfs hsid hlen hmfs
  | priority s p => exact decode_encode_priority s p mfs hsid hlen hmfs
  | rstStream s p => exact decode_encode_rstStream s p mfs hsid hlen hmfs
  | settings s ack p => exact decode_encode_settings s ack p mfs hsid hlen hmfs
  | pushPromise s p => exact decode_encode_pushPromise s p mfs hsid hlen hmfs
  | ping s ack p => exact decode_encode_ping s ack p mfs hsid hlen hmfs
  | goaway s p => exact decode_encode_goaway s p mfs hsid hlen hmfs
  | windowUpdate s p => exact decode_encode_windowUpdate s p mfs hsid hlen hmfs
  | continuation s eh p => exact decode_encode_continuation s eh p mfs hsid hlen hmfs
  | unknown t s l =>
    obtain ⟨hk, ht⟩ := hunk t s l rfl
    exact decode_encode_unknown t s l mfs hsid hlen hmfs ht hk

/-! ## Wire vectors, checker-verified (the round-trips are not vacuous) -/

/-- DATA on stream 1, `END_STREAM` set, 3-byte payload — the exact octets
`H2.Frame`'s own vector decodes. -/
example : encodeFrame (.data 1 true [0xaa, 0xbb, 0xcc])
    = [0x00, 0x00, 0x03, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0xaa, 0xbb, 0xcc] := rfl

example : decode (encodeFrame (.data 1 true [0xaa, 0xbb, 0xcc])) 16384
    = .complete (.data 1 true [0xaa, 0xbb, 0xcc]) 12 := rfl

/-- HEADERS on stream 3, `END_HEADERS` set, `END_STREAM` clear. -/
example : encodeFrame (.headers 3 false true [0x82, 0x86])
    = [0x00, 0x00, 0x02, 0x01, 0x04, 0x00, 0x00, 0x00, 0x03, 0x82, 0x86] := rfl

example : decode (encodeFrame (.headers 3 false true [0x82, 0x86])) 16384
    = .complete (.headers 3 false true [0x82, 0x86]) 11 := rfl

/-- WINDOW_UPDATE on stream 1, 4-byte increment. -/
example : decode (encodeFrame (.windowUpdate 1 [0x00, 0x00, 0x00, 0x40])) 16384
    = .complete (.windowUpdate 1 [0x00, 0x00, 0x00, 0x40]) 13 := rfl

/-- PING with 8 opaque octets, ACK set. -/
example : decode (encodeFrame (.ping 0 true [1, 2, 3, 4, 5, 6, 7, 8])) 16384
    = .complete (.ping 0 true [1, 2, 3, 4, 5, 6, 7, 8]) 17 := rfl

/-- RST_STREAM carrying a 4-byte error code. -/
example : decode (encodeFrame (.rstStream 5 [0x00, 0x00, 0x00, 0x08])) 16384
    = .complete (.rstStream 5 [0x00, 0x00, 0x00, 0x08]) 13 := rfl

/-- GOAWAY: last-stream-id + error code (8 octets). -/
example : decode (encodeFrame (.goaway 0 [0, 0, 0, 3, 0, 0, 0, 0])) 16384
    = .complete (.goaway 0 [0, 0, 0, 3, 0, 0, 0, 0]) 17 := rfl

/-- SETTINGS, empty payload, no ACK. -/
example : decode (encodeFrame (.settings 0 false [])) 16384
    = .complete (.settings 0 false []) 9 := rfl

end FrameEncode
end H2
