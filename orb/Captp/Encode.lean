/-
Captp.Encode — the wire encoder, and a bounded round-trip against the decoder.

`Captp.Frame` fixed a total, consumed-monotone *decoder* (`decodeFrame`): every
frame decode strictly advances the cursor, so a frame stream always terminates
(crash-safety / boundedness of the read side).  What it did not fix is the other
half of a *codec*: an encoder, and the round-trip that the two compose to the
identity.  Without it "the decoder is total" says nothing about faithfulness — a
decoder that ignores its input is total too.

This file supplies the encoder (`encodeFrame`) and proves the round-trip

    decodeFrame (encodeFrame f ++ rest) = some (f, rest)

for every *well-formed* frame `f` (`Frame.WF`) and any trailing bytes `rest`.
Well-formedness is the boundedness the fixed-width little-endian fields demand:
every position/length fits in its `u32` field (`< 2^32`), every GC weight in its
`u64` field (`0 ≤ w < 2^64`).  These are exactly the ranges the reference TLV
can represent; a frame outside them is not encodable, not a decoder bug.  The
`Frame` bytes are opaque octets — the round-trip copies them verbatim and needs
no bound on their *values*, only on the length fields that frame them.

The round-trip is *value-exact* (it recovers the whole `Frame`, positions and
byte strings included), where `Captp.Frame`'s theorems were value-agnostic
(cursor-only).  Together the two give a crash-safe, faithful wire codec: the
decoder always terminates and strictly consumes (`decodeFrame_consumes`), and on
anything the encoder produced it recovers exactly what was encoded, leaving the
tail untouched.
-/
import Captp.Frame

namespace Captp

open Reader

/-! ### Little-endian fixed-width encoding, inverse to `leNat` -/

/-- Encode `n` as `w` little-endian octets (low octet first).  Inverse to the
decoder's `leNat` fold on values below `256 ^ w`. -/
def toLE : Nat → Nat → List Byte
  | 0,     _ => []
  | w + 1, n => (n % 256) :: toLE w (n / 256)

@[simp] theorem toLE_length (w n : Nat) : (toLE w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLE, ih]

/-- The core inverse: `leNat` recovers exactly what `toLE` encoded, for any value
that fits in the `w`-octet field. -/
theorem leNat_toLE (w n : Nat) (h : n < 256 ^ w) : leNat (toLE w n) = n := by
  induction w generalizing n with
  | zero =>
    simp only [Nat.pow_zero] at h
    simp only [toLE, leNat]
    omega
  | succ w ih =>
    simp only [toLE, leNat]
    have hdiv : n / 256 < 256 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h
    rw [ih (n / 256) hdiv]
    omega

/-! ### `bind` composed with a round-tripping prefix reader -/

/-- If a reader `r` consumes exactly the prefix `pre` off `pre ++ suf` and yields
`a`, then a bound `r >>= f` continues as `f a` on the remaining `suf`. -/
theorem bind_roundtrip {α β : Type} {r : Reader α} {f : α → Reader β}
    {pre suf : List Byte} {a : α} (h : r (pre ++ suf) = some (a, suf)) :
    (r >>= f) (pre ++ suf) = f a suf := by
  rw [Reader.bind_eq]
  simp only [Reader.bind', h, Option.bind_some]

/-- `takeN` reads back exactly the prefix it was handed. -/
theorem takeN_append (bs rest : List Byte) :
    takeN bs.length (bs ++ rest) = some (bs, rest) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, List.cons_append, takeN, ih]

/-! ### Field encoders -/

/-- A `u32`: four little-endian octets. -/
def encU32 (p : Position) : List Byte := toLE 4 p

/-- An `i64` (unsigned interpretation): eight little-endian octets. -/
def encI64 (z : Int) : List Byte := toLE 8 z.toNat

/-- A boolean octet: `1` for true, `0` for false. -/
def encBool (b : Bool) : List Byte := [if b then 1 else 0]

/-- An optional `u32`: a presence octet, then the value when present. -/
def encOptU32 : Option Position → List Byte
  | none => encBool false
  | some p => encBool true ++ encU32 p

/-- A length-prefixed byte string: a `u32` length then the octets. -/
def encBytes (bs : List Byte) : List Byte := encU32 bs.length ++ bs

/-! ### Field round-trips -/

theorem readU32_roundtrip (p : Position) (rest : List Byte) (h : p < 256 ^ 4) :
    readU32 (encU32 p ++ rest) = some (p, rest) := by
  have ht : takeN 4 (encU32 p ++ rest) = some (encU32 p, rest) := by
    have hh := takeN_append (encU32 p) rest
    simpa [encU32, toLE_length] using hh
  unfold readU32
  rw [bind_roundtrip ht]
  simp only [Reader.pure_eq, Reader.pure', encU32, leNat_toLE 4 p h]

theorem readI64_roundtrip (z : Int) (rest : List Byte)
    (hpos : 0 ≤ z) (h : z.toNat < 256 ^ 8) :
    readI64 (encI64 z ++ rest) = some (z, rest) := by
  have ht : takeN 8 (encI64 z ++ rest) = some (encI64 z, rest) := by
    have hh := takeN_append (encI64 z) rest
    simpa [encI64, toLE_length] using hh
  unfold readI64
  rw [bind_roundtrip ht]
  simp only [Reader.pure_eq, Reader.pure', encI64, leNat_toLE 8 z.toNat h]
  rw [Int.toNat_of_nonneg hpos]

theorem readBool_roundtrip (b : Bool) (rest : List Byte) :
    readBool (encBool b ++ rest) = some (b, rest) := by
  cases b <;> rfl

theorem readOptU32_roundtrip (o : Option Position) (rest : List Byte)
    (h : ∀ p, o = some p → p < 256 ^ 4) :
    readOptU32 (encOptU32 o ++ rest) = some (o, rest) := by
  cases o with
  | none =>
    show readOptU32 (encBool false ++ rest) = some (none, rest)
    unfold readOptU32
    rw [bind_roundtrip (readBool_roundtrip false rest)]
    simp only [Reader.pure_eq, Reader.pure']
  | some p =>
    have hp : p < 256 ^ 4 := h p rfl
    show readOptU32 ((encBool true ++ encU32 p) ++ rest) = some (some p, rest)
    rw [List.append_assoc]
    unfold readOptU32
    rw [bind_roundtrip (readBool_roundtrip true (encU32 p ++ rest))]
    show (do let q ← readU32; pure (some q)) (encU32 p ++ rest) = some (some p, rest)
    rw [bind_roundtrip (readU32_roundtrip p rest hp)]
    simp only [Reader.pure_eq, Reader.pure']

theorem readBytes_roundtrip (bs rest : List Byte) (h : bs.length < 256 ^ 4) :
    readBytes (encBytes bs ++ rest) = some (bs, rest) := by
  show readBytes ((encU32 bs.length ++ bs) ++ rest) = _
  rw [List.append_assoc]
  unfold readBytes
  rw [bind_roundtrip (readU32_roundtrip bs.length (bs ++ rest) h)]
  exact takeN_append bs rest

/-! ### Descriptor encoder and round-trip -/

/-- Encode a descriptor: its tag octet then its fields. -/
def encDescriptor : Descriptor → List Byte
  | .ImportObject p => descTag.importObject :: encU32 p
  | .ImportPromise p => descTag.importPromise :: encU32 p
  | .Export p => descTag.export :: encU32 p
  | .Answer p => descTag.answer :: encU32 p
  | .HandoffGive k l s =>
      descTag.handoffGive :: (encBytes k ++ encBytes l ++ encBytes s)
  | .HandoffReceive rs sd =>
      descTag.handoffReceive :: (encBytes rs ++ encBytes sd)

/-- Boundedness of a descriptor's fields: every position and every byte-string
length fits in its `u32` field. -/
def Descriptor.WF : Descriptor → Prop
  | .ImportObject p | .ImportPromise p | .Export p | .Answer p => p < 256 ^ 4
  | .HandoffGive k l s =>
      k.length < 256 ^ 4 ∧ l.length < 256 ^ 4 ∧ s.length < 256 ^ 4
  | .HandoffReceive rs sd => rs.length < 256 ^ 4 ∧ sd.length < 256 ^ 4

/-- `readDescriptor` continues a bound after popping the tag octet. -/
theorem readDescriptor_cons (t : Byte) (rest : List Byte) :
    readDescriptor (t :: rest) = descBody t rest := by
  show (Reader.pop >>= descBody) (t :: rest) = _
  rw [Reader.bind_eq]
  simp only [Reader.bind', Reader.pop, Option.bind_some]

theorem readDescriptor_roundtrip (d : Descriptor) (rest : List Byte)
    (h : d.WF) : readDescriptor (encDescriptor d ++ rest) = some (d, rest) := by
  cases d with
  | Export p =>
    show readDescriptor (descTag.export :: (encU32 p ++ rest)) = _
    rw [readDescriptor_cons]
    show descBody descTag.export (encU32 p ++ rest) = _
    unfold descBody
    simp only [descTag.export, descTag.importObject, descTag.importPromise,
      show ¬ (0x12 : Byte) = 0x10 by decide, show ¬ (0x12 : Byte) = 0x11 by decide,
      if_false, if_true, reduceIte]
    rw [bind_roundtrip (readU32_roundtrip p rest h)]
    simp only [Reader.pure_eq, Reader.pure']
  | ImportObject p =>
    show readDescriptor (descTag.importObject :: (encU32 p ++ rest)) = _
    rw [readDescriptor_cons]
    show descBody descTag.importObject (encU32 p ++ rest) = _
    unfold descBody
    simp only [descTag.importObject, if_true, reduceIte]
    rw [bind_roundtrip (readU32_roundtrip p rest h)]
    simp only [Reader.pure_eq, Reader.pure']
  | ImportPromise p =>
    show readDescriptor (descTag.importPromise :: (encU32 p ++ rest)) = _
    rw [readDescriptor_cons]
    show descBody descTag.importPromise (encU32 p ++ rest) = _
    unfold descBody
    simp only [descTag.importObject, descTag.importPromise,
      show ¬ (0x11 : Byte) = 0x10 by decide, if_false, reduceIte]
    rw [bind_roundtrip (readU32_roundtrip p rest h)]
    simp only [Reader.pure_eq, Reader.pure']
  | Answer p =>
    show readDescriptor (descTag.answer :: (encU32 p ++ rest)) = _
    rw [readDescriptor_cons]
    show descBody descTag.answer (encU32 p ++ rest) = _
    unfold descBody
    simp only [descTag.importObject, descTag.importPromise, descTag.export, descTag.answer,
      show ¬ (0x13 : Byte) = 0x10 by decide, show ¬ (0x13 : Byte) = 0x11 by decide,
      show ¬ (0x13 : Byte) = 0x12 by decide, if_false, reduceIte]
    rw [bind_roundtrip (readU32_roundtrip p rest h)]
    simp only [Reader.pure_eq, Reader.pure']
  | HandoffGive k l s =>
    obtain ⟨hk, hl, hs⟩ := h
    show readDescriptor (descTag.handoffGive :: (encBytes k ++ encBytes l ++ encBytes s ++ rest)) = _
    rw [readDescriptor_cons]
    show descBody descTag.handoffGive (encBytes k ++ encBytes l ++ encBytes s ++ rest) = _
    unfold descBody
    simp only [descTag.importObject, descTag.importPromise, descTag.export, descTag.answer,
      descTag.handoffGive,
      show ¬ (0x14 : Byte) = 0x10 by decide, show ¬ (0x14 : Byte) = 0x11 by decide,
      show ¬ (0x14 : Byte) = 0x12 by decide, show ¬ (0x14 : Byte) = 0x13 by decide,
      if_false, reduceIte]
    simp only [List.append_assoc]
    rw [bind_roundtrip (readBytes_roundtrip k (encBytes l ++ (encBytes s ++ rest)) hk)]
    rw [bind_roundtrip (readBytes_roundtrip l (encBytes s ++ rest) hl)]
    rw [bind_roundtrip (readBytes_roundtrip s rest hs)]
    simp only [Reader.pure_eq, Reader.pure']
  | HandoffReceive rs sd =>
    obtain ⟨hr, hsd⟩ := h
    show readDescriptor (descTag.handoffReceive :: (encBytes rs ++ encBytes sd ++ rest)) = _
    rw [readDescriptor_cons]
    show descBody descTag.handoffReceive (encBytes rs ++ encBytes sd ++ rest) = _
    unfold descBody
    simp only [descTag.importObject, descTag.importPromise, descTag.export, descTag.answer,
      descTag.handoffGive, descTag.handoffReceive,
      show ¬ (0x15 : Byte) = 0x10 by decide, show ¬ (0x15 : Byte) = 0x11 by decide,
      show ¬ (0x15 : Byte) = 0x12 by decide, show ¬ (0x15 : Byte) = 0x13 by decide,
      show ¬ (0x15 : Byte) = 0x14 by decide, if_false, reduceIte]
    simp only [List.append_assoc]
    rw [bind_roundtrip (readBytes_roundtrip rs (encBytes sd ++ rest) hr)]
    rw [bind_roundtrip (readBytes_roundtrip sd rest hsd)]
    simp only [Reader.pure_eq, Reader.pure']

/-! ### The frame encoder -/

/-- Encode a frame: its tag octet then its fields, in decoder order. -/
def encodeFrame : Frame → List Byte
  | .Deliver t m a ap =>
      frameTag.deliver :: (encDescriptor t ++ encBytes m ++ encBytes a ++ encOptU32 ap)
  | .DeliverOnly t m a =>
      frameTag.deliverOnly :: (encDescriptor t ++ encBytes m ++ encBytes a)
  | .Listen t w => frameTag.listen :: (encU32 t ++ encBool w)
  | .GcExport p d => frameTag.gcExport :: (encU32 p ++ encI64 d)
  | .GcAnswer p => frameTag.gcAnswer :: encU32 p
  | .Abort r => frameTag.abort :: encBytes r

/-- Boundedness of a frame's fields — every fixed-width field is in range. -/
def Frame.WF : Frame → Prop
  | .Deliver t m a ap =>
      t.WF ∧ m.length < 256 ^ 4 ∧ a.length < 256 ^ 4 ∧ (∀ p, ap = some p → p < 256 ^ 4)
  | .DeliverOnly t m a => t.WF ∧ m.length < 256 ^ 4 ∧ a.length < 256 ^ 4
  | .Listen t _ => t < 256 ^ 4
  | .GcExport p d => p < 256 ^ 4 ∧ 0 ≤ d ∧ d.toNat < 256 ^ 8
  | .GcAnswer p => p < 256 ^ 4
  | .Abort r => r.length < 256 ^ 4

/-- `decodeFrame` continues a bound after popping the tag octet. -/
theorem decodeFrame_cons (t : Byte) (rest : List Byte) :
    decodeFrame (t :: rest) = frameBody t rest := by
  show (Reader.pop >>= frameBody) (t :: rest) = _
  rw [Reader.bind_eq]
  simp only [Reader.bind', Reader.pop, Option.bind_some]

/-- **Round-trip (headline).** For every well-formed frame, encoding then
decoding recovers exactly the frame and leaves the trailing bytes untouched.
Composed with `decodeFrame_consumes` (the decoder always strictly advances), the
two give a crash-safe, value-faithful wire codec. -/
theorem decodeFrame_encodeFrame (f : Frame) (rest : List Byte) (h : f.WF) :
    decodeFrame (encodeFrame f ++ rest) = some (f, rest) := by
  cases f with
  | Deliver t m a ap =>
    obtain ⟨ht, hm, ha, hap⟩ := h
    show decodeFrame (frameTag.deliver ::
      (encDescriptor t ++ encBytes m ++ encBytes a ++ encOptU32 ap ++ rest)) = _
    rw [decodeFrame_cons]
    show frameBody frameTag.deliver
      (encDescriptor t ++ encBytes m ++ encBytes a ++ encOptU32 ap ++ rest) = _
    unfold frameBody
    simp only [frameTag.deliver, if_true, reduceIte]
    simp only [List.append_assoc]
    rw [bind_roundtrip (readDescriptor_roundtrip t
      (encBytes m ++ (encBytes a ++ (encOptU32 ap ++ rest))) ht)]
    rw [bind_roundtrip (readBytes_roundtrip m
      (encBytes a ++ (encOptU32 ap ++ rest)) hm)]
    rw [bind_roundtrip (readBytes_roundtrip a (encOptU32 ap ++ rest) ha)]
    rw [bind_roundtrip (readOptU32_roundtrip ap rest hap)]
    simp only [Reader.pure_eq, Reader.pure']
  | DeliverOnly t m a =>
    obtain ⟨ht, hm, ha⟩ := h
    show decodeFrame (frameTag.deliverOnly ::
      (encDescriptor t ++ encBytes m ++ encBytes a ++ rest)) = _
    rw [decodeFrame_cons]
    show frameBody frameTag.deliverOnly
      (encDescriptor t ++ encBytes m ++ encBytes a ++ rest) = _
    unfold frameBody
    simp only [frameTag.deliver, frameTag.deliverOnly,
      show ¬ (0x02 : Byte) = 0x01 by decide, if_false, reduceIte]
    simp only [List.append_assoc]
    rw [bind_roundtrip (readDescriptor_roundtrip t
      (encBytes m ++ (encBytes a ++ rest)) ht)]
    rw [bind_roundtrip (readBytes_roundtrip m (encBytes a ++ rest) hm)]
    rw [bind_roundtrip (readBytes_roundtrip a rest ha)]
    simp only [Reader.pure_eq, Reader.pure']
  | Listen t w =>
    show decodeFrame (frameTag.listen :: (encU32 t ++ encBool w ++ rest)) = _
    rw [decodeFrame_cons]
    show frameBody frameTag.listen (encU32 t ++ encBool w ++ rest) = _
    unfold frameBody
    simp only [frameTag.deliver, frameTag.deliverOnly, frameTag.listen,
      show ¬ (0x03 : Byte) = 0x01 by decide, show ¬ (0x03 : Byte) = 0x02 by decide,
      if_false, reduceIte]
    simp only [List.append_assoc]
    rw [bind_roundtrip (readU32_roundtrip t (encBool w ++ rest) h)]
    rw [bind_roundtrip (readBool_roundtrip w rest)]
    simp only [Reader.pure_eq, Reader.pure']
  | GcExport p d =>
    obtain ⟨hp, hpos, hd⟩ := h
    show decodeFrame (frameTag.gcExport :: (encU32 p ++ encI64 d ++ rest)) = _
    rw [decodeFrame_cons]
    show frameBody frameTag.gcExport (encU32 p ++ encI64 d ++ rest) = _
    unfold frameBody
    simp only [frameTag.deliver, frameTag.deliverOnly, frameTag.listen, frameTag.gcExport,
      show ¬ (0x04 : Byte) = 0x01 by decide, show ¬ (0x04 : Byte) = 0x02 by decide,
      show ¬ (0x04 : Byte) = 0x03 by decide, if_false, reduceIte]
    simp only [List.append_assoc]
    rw [bind_roundtrip (readU32_roundtrip p (encI64 d ++ rest) hp)]
    rw [bind_roundtrip (readI64_roundtrip d rest hpos hd)]
    simp only [Reader.pure_eq, Reader.pure']
  | GcAnswer p =>
    show decodeFrame (frameTag.gcAnswer :: (encU32 p ++ rest)) = _
    rw [decodeFrame_cons]
    show frameBody frameTag.gcAnswer (encU32 p ++ rest) = _
    unfold frameBody
    simp only [frameTag.deliver, frameTag.deliverOnly, frameTag.listen, frameTag.gcExport,
      frameTag.gcAnswer,
      show ¬ (0x05 : Byte) = 0x01 by decide, show ¬ (0x05 : Byte) = 0x02 by decide,
      show ¬ (0x05 : Byte) = 0x03 by decide, show ¬ (0x05 : Byte) = 0x04 by decide,
      if_false, reduceIte]
    rw [bind_roundtrip (readU32_roundtrip p rest h)]
    simp only [Reader.pure_eq, Reader.pure']
  | Abort r =>
    show decodeFrame (frameTag.abort :: (encBytes r ++ rest)) = _
    rw [decodeFrame_cons]
    show frameBody frameTag.abort (encBytes r ++ rest) = _
    unfold frameBody
    simp only [frameTag.deliver, frameTag.deliverOnly, frameTag.listen, frameTag.gcExport,
      frameTag.gcAnswer, frameTag.abort,
      show ¬ (0x06 : Byte) = 0x01 by decide, show ¬ (0x06 : Byte) = 0x02 by decide,
      show ¬ (0x06 : Byte) = 0x03 by decide, show ¬ (0x06 : Byte) = 0x04 by decide,
      show ¬ (0x06 : Byte) = 0x05 by decide, if_false, reduceIte]
    rw [bind_roundtrip (readBytes_roundtrip r rest h)]
    simp only [Reader.pure_eq, Reader.pure']

/-- **Encoder injectivity (corollary).** Distinct well-formed frames never share
an encoding: the encoder is one-to-one on well-formed frames.  Immediate from the
round-trip at `rest = []`. -/
theorem encodeFrame_injective {f g : Frame} (hf : f.WF) (hg : g.WF)
    (h : encodeFrame f = encodeFrame g) : f = g := by
  have hf' := decodeFrame_encodeFrame f [] hf
  have hg' := decodeFrame_encodeFrame g [] hg
  rw [h] at hf'
  rw [hg'] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf'
  exact hf'.1.symm

end Captp
