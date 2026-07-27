/-
# Pki.Der — DER (X.690) encoding primitives, with a proven decoder round-trip

The ACME `finalize` request (RFC 8555 §7.4) carries a PKCS#10
`CertificationRequest` (RFC 2986) as base64url DER. drorb had no DER *encoder*:
`Pki.Acme.Csr` only wraps already-formed bytes. This module is the encoder, and
`Pki.Csr` builds the CSR on top of it.

The load-bearing correctness property is **unambiguity**: DER is a
tag-length-value encoding, and a CSR is a tree of nested TLVs whose parents'
lengths are computed from their children. If the length encoding were wrong the
CA would reject (or, worse, misparse) the request. So the theorem below is not a
shape lemma but a real decoder round-trip: `readTlv` recovers exactly the tag,
the body, and the untouched remainder from anything `tlv` produced
(`readTlv_tlv`), which gives injectivity of the encoding (`tlv_injective`).

Scope: definite-length encodings with bodies < 2¹⁶ bytes, which covers every
structure in a CSR (the largest is the request info, a few hundred bytes). The
`Wf` predicate carries that bound and every constructor here preserves it.
-/
import Init.Data.List.Lemmas

namespace Pki.Der

/-! ## Lengths (X.690 §8.1.3)

Short form for `n < 128` (one byte); long form otherwise, with a leading
`0x80 ‖ octet-count`. Two long-form widths suffice below 2¹⁶. -/

/-- The DER length octets for a body of `n` bytes (`n < 65536`). -/
def len (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n]
  else if n < 256 then [0x81, UInt8.ofNat n]
  else [0x82, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- Bodies this module encodes: short enough for the two long-form widths. -/
def Wf (body : List UInt8) : Prop := body.length < 65536

/-- A tag-length-value item. -/
def tlv (tag : UInt8) (body : List UInt8) : List UInt8 :=
  tag :: len body.length ++ body

/-! ## The decoder

`readTlv bs` splits `bs` into the leading TLV item and the remainder. It is the
adversary's reader: it re-derives the length from the octets alone, with no
knowledge of what produced them. -/

/-- Read the length octets: returns the length and the bytes after them. -/
def readLen : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else if b = 0x81 then
      match rest with
      | [] => none
      | n :: rest' => some (n.toNat, rest')
    else if b = 0x82 then
      match rest with
      | hi :: lo :: rest' => some (hi.toNat * 256 + lo.toNat, rest')
      | _ => none
    else none

/-- Read one TLV item: the tag, its body, and the bytes following the item. -/
def readTlv : List UInt8 → Option (UInt8 × List UInt8 × List UInt8)
  | [] => none
  | tag :: rest =>
    match readLen rest with
    | none => none
    | some (n, body) =>
      if body.length < n then none
      else some (tag, body.take n, body.drop n)

/-! ## The round-trip

`readLen` recovers the length `len` encoded, for every width. The three branches
are separate arithmetic facts; `omega` closes the bounds and `UInt8.toNat_ofNat`
the truncation. -/

/-- A byte-ranged `Nat` survives the trip through `UInt8`. -/
theorem u8_toNat (n : Nat) (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  have hm : n % 256 = n := Nat.mod_eq_of_lt h
  simp [hm]

theorem readLen_len (n : Nat) (h : n < 65536) (rest : List UInt8) :
    readLen (len n ++ rest) = some (n, rest) := by
  unfold len
  by_cases h1 : n < 128
  · simp [h1, readLen, u8_toNat n (by omega)]
  · by_cases h2 : n < 256
    · simp [h1, h2, readLen, u8_toNat n (by omega)]
    · simp [h1, h2, readLen, u8_toNat (n / 256) (by omega), u8_toNat (n % 256) (by omega)]
      omega

/-- **The encoder round-trip.** A decoder that knows nothing but the octets
recovers from `tlv tag body ++ rest` exactly the tag, exactly the body, and
exactly the untouched remainder. This is what makes nested length computation
sound: a parent's body is the concatenation of its children's TLVs, and each
child is recovered without consuming any of its siblings. -/
theorem readTlv_tlv (tag : UInt8) (body : List UInt8) (h : Wf body)
    (rest : List UInt8) :
    readTlv (tlv tag body ++ rest) = some (tag, body, rest) := by
  unfold tlv readTlv
  simp only [List.cons_append, List.append_assoc]
  rw [readLen_len body.length h]
  simp

/-- Encoding is injective in the tag and the body: two well-formed items with
the same octets are the same item. (Corollary of the round-trip — apply the
decoder to both sides.) -/
theorem tlv_injective {t₁ t₂ : UInt8} {b₁ b₂ : List UInt8}
    (h₁ : Wf b₁) (h₂ : Wf b₂) (h : tlv t₁ b₁ = tlv t₂ b₂) :
    t₁ = t₂ ∧ b₁ = b₂ := by
  have r₁ := readTlv_tlv t₁ b₁ h₁ []
  have r₂ := readTlv_tlv t₂ b₂ h₂ []
  rw [h, r₂] at r₁
  simp at r₁
  exact ⟨r₁.1.symm, r₁.2.symm⟩

/-! ## Constructors (X.690 §8, X.680 tag numbers) -/

/-- `SEQUENCE` (constructed, universal 16). -/
def seq (body : List UInt8) : List UInt8 := tlv 0x30 body
/-- `SET` (constructed, universal 17). -/
def set (body : List UInt8) : List UInt8 := tlv 0x31 body
/-- `OBJECT IDENTIFIER` from its content octets. -/
def oid (content : List UInt8) : List UInt8 := tlv 0x06 content
/-- `OCTET STRING`. -/
def octetString (body : List UInt8) : List UInt8 := tlv 0x04 body
/-- `IA5String` (ASCII), used for `dNSName` SANs. -/
def ia5String (s : List UInt8) : List UInt8 := tlv 0x16 s
/-- `UTF8String`, used for the subject common name. -/
def utf8String (s : List UInt8) : List UInt8 := tlv 0x0C s
/-- `NULL`. -/
def null : List UInt8 := tlv 0x05 []

/-- `BIT STRING` with no unused bits — the leading `0x00` is the unused-bit
count (X.690 §8.6.2.2), not part of the value. -/
def bitString (body : List UInt8) : List UInt8 := tlv 0x03 (0x00 :: body)

/-- A non-negative `INTEGER` from unsigned big-endian content: strip leading
zeros (keeping one for the value zero), then prepend `0x00` when the top bit is
set, since DER INTEGERs are two's-complement signed (X.690 §8.3.2). -/
def integer (b : List UInt8) : List UInt8 :=
  let stripped := b.dropWhile (· == 0)
  let v := if stripped.isEmpty then [0] else stripped
  let v := if v.headD 0 ≥ 0x80 then 0x00 :: v else v
  tlv 0x02 v

/-- The small `INTEGER`s the CSR needs (version 0). -/
def integerNat (n : Nat) : List UInt8 := integer [UInt8.ofNat n]

/-- A context-specific *constructed* tag `[n]` (implicit-tagged structures). -/
def ctxConstructed (n : UInt8) (body : List UInt8) : List UInt8 :=
  tlv (0xA0 + n) body

/-- A context-specific *primitive* tag `[n]` — `GeneralName.dNSName` is
`[2] IMPLICIT IA5String`, so the IA5String tag is replaced, not wrapped. -/
def ctxPrimitive (n : UInt8) (body : List UInt8) : List UInt8 :=
  tlv (0x80 + n) body

/-! ## Well-formedness is preserved

Every constructor stays inside the encodable range as long as its body does, so
a CSR built from these never escapes `Wf`. The bound is stated where it is
actually used (the top-level `tlv` calls); `readTlv_tlv` needs nothing more. -/

theorem tlv_length (tag : UInt8) (body : List UInt8) :
    (tlv tag body).length = 1 + (len body.length).length + body.length := by
  simp [tlv, List.length_append]
  omega

/-- The header never exceeds three octets, so a body under 65532 bytes yields a
well-formed item — the composition bound the CSR builder relies on. -/
theorem len_length_le (n : Nat) : (len n).length ≤ 3 := by
  unfold len
  split
  · simp
  · split <;> simp

theorem tlv_wf (tag : UInt8) (body : List UInt8) (h : body.length < 65532) :
    Wf (tlv tag body) := by
  have := len_length_le body.length
  unfold Wf
  rw [tlv_length]
  omega

end Pki.Der
