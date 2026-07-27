import H3.Varint

/-!
# HTTP/3 unidirectional stream types (RFC 9114 §6.2)

Every HTTP/3 unidirectional stream opens with a variable-length integer naming
its type. The types this endpoint understands (RFC 9114 §6.2 / §8, RFC 9204
§4.2):

| type | stream                                   |
|------|------------------------------------------|
| 0x00 | control stream (§6.2.1)                  |
| 0x01 | push stream (§6.2.2)                     |
| 0x02 | QPACK encoder stream (RFC 9204 §4.2)     |
| 0x03 | QPACK decoder stream (RFC 9204 §4.2)     |

Every other value is a reserved / extension type and MUST be ignored — the
stream is drained (§6.2, §8.1 greasing: reserved types `0x1f * N + 0x21`). The
classification is total; the type-prefix codec round-trips on the proven QUIC
varint (`H3.Varint`).
-/

namespace H3

/-- The unidirectional stream taxonomy (RFC 9114 §6.2, RFC 9204 §4.2).
`reserved` carries the raw type of an unknown/extension stream (drained). -/
inductive StreamType where
  | control
  | push
  | qpackEncoder
  | qpackDecoder
  | reserved (t : Nat)
deriving Repr, DecidableEq

/-- Total classification of a decoded stream-type varint. -/
def StreamType.ofNat (t : Nat) : StreamType :=
  if t = 0x00 then .control
  else if t = 0x01 then .push
  else if t = 0x02 then .qpackEncoder
  else if t = 0x03 then .qpackDecoder
  else .reserved t

/-- The known (structured) stream-type codes. -/
def StreamType.isKnown (t : Nat) : Bool :=
  t = 0x00 || t = 0x01 || t = 0x02 || t = 0x03

/-- The wire type code of a classified stream type (`reserved` keeps its own). -/
def StreamType.toNat : StreamType → Nat
  | .control => 0x00
  | .push => 0x01
  | .qpackEncoder => 0x02
  | .qpackDecoder => 0x03
  | .reserved t => t

/-- Every unknown type classifies as `reserved` and is drained, never rejected
(RFC 9114 §6.2). With the known cases this makes `ofNat` total. -/
theorem StreamType.ofNat_reserved (t : Nat) (h : StreamType.isKnown t = false) :
    StreamType.ofNat t = .reserved t := by
  unfold StreamType.isKnown at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  unfold StreamType.ofNat
  simp [h0, h1, h2, h3]

/-- `ofNat` inverts `toNat` on the known codes, and is the identity on the
reserved carrier: classification never loses the type. -/
theorem StreamType.ofNat_toNat (s : StreamType) (h : ∀ t, s = .reserved t → StreamType.isKnown t = false) :
    StreamType.ofNat s.toNat = s := by
  cases s with
  | control => rfl
  | push => rfl
  | qpackEncoder => rfl
  | qpackDecoder => rfl
  | reserved t => exact StreamType.ofNat_reserved t (h t rfl)

/-! ## The stream-type prefix codec -/

/-- Encode a unidirectional stream's opening type prefix. `none` iff the type
exceeds the varint range. -/
def encStreamType (s : StreamType) : Option Bytes := Varint.encVarint s.toNat

/-- Decode a unidirectional stream's opening type prefix from the head of `bs`,
returning the classified type and the bytes consumed. -/
def decStreamType (bs : Bytes) : Option (StreamType × Nat) :=
  match Varint.decVarint bs with
  | none => none
  | some (t, n) => some (StreamType.ofNat t, n)

/-- **Stream-type round-trip.** For every well-formed stream type (a reserved
carrier must be a genuinely unknown code), the opening prefix decodes back to
exactly that type, consuming exactly the encoding. -/
theorem decStreamType_encStreamType (s : StreamType) (bs tail : Bytes)
    (hwf : ∀ t, s = .reserved t → StreamType.isKnown t = false)
    (h : encStreamType s = some bs) :
    decStreamType (bs ++ tail) = some (s, bs.length) := by
  unfold encStreamType at h
  unfold decStreamType
  rw [Varint.decVarint_encVarint s.toNat bs tail h]
  dsimp only
  rw [StreamType.ofNat_toNat s hwf]

/-! ## Wire vectors, checker-verified -/

#guard StreamType.ofNat 0x00 = .control
#guard StreamType.ofNat 0x02 = .qpackEncoder
#guard StreamType.ofNat 0x03 = .qpackDecoder
#guard StreamType.ofNat 0x21 = .reserved 0x21          -- a grease type is drained
#guard encStreamType .control = some [0x00]
#guard encStreamType .qpackEncoder = some [0x02]
#guard decStreamType [0x03] = some (.qpackDecoder, 1)
-- a reserved type crossing the 1-byte varint boundary still round-trips
#guard decStreamType [0x40, 0x21] = some (.reserved 0x21, 2)

#print axioms decStreamType_encStreamType

end H3
