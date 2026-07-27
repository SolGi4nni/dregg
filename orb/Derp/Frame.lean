import Derp
/-!
# DERP frame codec — the named MAX_FRAME_SIZE cap and its rejection theorem

`Derp.lean` proves the length-prefixed frame envelope (`parseFrame` / `serializeFrame`,
`derp_parse_serialize` round-trip, `derp_frame_bounds`). Its cap is a *parameter*
(`maxLen`) so the codec is reusable at any bound. This module pins that parameter to the
**DERP wire constant** `MAX_FRAME_SIZE = 1 MiB` (`1 <<< 20`) and adds the one property the
parametric codec does not state on its own: a frame whose declared length exceeds the cap
is **rejected** (`parseFrame` returns `none`), never truncated and never over-read.

Everything here is additive over the proven `Derp` codec — no re-implementation, no weakening.
-/

namespace Derp

/-- The DERP wire packet cap: `MAX_FRAME_SIZE = 1 MiB` (`1 <<< 20` bytes). A relay
rejects any frame declaring a longer payload. -/
def maxFrameSize : Nat := 1 <<< 20

theorem maxFrameSize_eq : maxFrameSize = 1048576 := by decide

theorem maxFrameSize_lt_addr : maxFrameSize < 16777216 := by decide

/-- The canonical wire encode/decode at the DERP cap. -/
def encodeFrame (f : Frame) : Bytes := serializeFrame f
def decodeFrame (bs : Bytes) : Option (Frame × Bytes) := parseFrame maxFrameSize bs

/-- **Over-size frames are rejected.** A 5+-byte stream whose declared big-endian
length exceeds `maxFrameSize` is rejected by the capped decoder — `none`, not a
truncated payload. This is the `MAX_FRAME_SIZE` bound the spec requires, proven on
the actual parser (the `len ≤ maxLen` guard fails, so no frame is produced). -/
theorem derp_reject_oversize (t l0 l1 l2 l3 : UInt8) (rest : Bytes)
    (h : maxFrameSize < be32 l0 l1 l2 l3) :
    decodeFrame (t :: l0 :: l1 :: l2 :: l3 :: rest) = none := by
  unfold decodeFrame parseFrame
  have hcond : ¬ (be32 l0 l1 l2 l3 ≤ maxFrameSize ∧ be32 l0 l1 l2 l3 ≤ rest.length) := by
    rintro ⟨hle, _⟩; omega
  simp only [hcond, if_false]

/-- **Any decoded frame is within the cap.** Whatever `decodeFrame` accepts has a
payload no longer than `maxFrameSize` — the capped codec never yields an over-cap
frame (a corollary of `derp_frame_bounds` at the pinned cap). -/
theorem derp_decode_bounded {bs : Bytes} {f : Frame} {rest : Bytes}
    (h : decodeFrame bs = some (f, rest)) : f.payload.length ≤ maxFrameSize :=
  (derp_frame_bounds maxFrameSize bs h).1

/-- **Round-trip at the DERP cap.** Encoding a frame whose payload fits the cap and
whose type tag round-trips, then decoding, recovers the frame and the untouched tail. -/
theorem derp_frame_roundtrip (f : Frame) (tail : Bytes)
    (hcap : f.payload.length ≤ maxFrameSize)
    (htype : FrameType.ofByte (FrameType.toByte f.ftype) = f.ftype) :
    decodeFrame (encodeFrame f ++ tail) = some (f, tail) :=
  derp_parse_serialize maxFrameSize f tail hcap
    (Nat.lt_of_le_of_lt hcap maxFrameSize_lt_addr) htype

/-- **Every named frame type round-trips through the codec at the cap** — the 16
assigned DERP frame types (`ServerKey 0x01 … Restarting 0x15`, `ForwardPacket 0x0a`)
each survive encode∘decode for an in-cap payload. -/
theorem derp_frame_roundtrip_named (f : Frame) (tail : Bytes)
    (hcap : f.payload.length ≤ maxFrameSize)
    (hnamed : ∀ b, f.ftype ≠ FrameType.unknown b) :
    decodeFrame (encodeFrame f ++ tail) = some (f, tail) :=
  derp_frame_roundtrip f tail hcap (derp_type_roundtrip_named f.ftype hnamed)

/-! ## Evaluation — the cap on concrete data (non-vacuous) -/

-- MAX_FRAME_SIZE is exactly the 1-MiB DERP constant.
#guard maxFrameSize = 1048576

-- A frame declaring length 0x00200000 (2 MiB > 1 MiB) is rejected.
#guard decodeFrame (0x04 :: 0x00 :: 0x20 :: 0x00 :: 0x00 :: []) = none

-- A small SendPacket-shaped frame round-trips through the capped codec.
#guard decodeFrame (encodeFrame { ftype := .sendPacket, payload := [0x01, 0x02, 0x03] } ++ [0xFF])
        = some ({ ftype := .sendPacket, payload := [0x01, 0x02, 0x03] }, [0xFF])

end Derp
