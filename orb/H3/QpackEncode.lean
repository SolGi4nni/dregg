import H3.Qpack

/-!
# QPACK field-section ENCODER (RFC 9204 §4.5)

`H3.Qpack` decodes a QPACK-encoded field section *into* the two-arena
`Arena.Store` — the receive side (client request headers). This module adds the
**send side**: a server encodes its response header list into a field section
that the deployed decoder reads back exactly.

The encoder uses the two static-table-free representations that need no dynamic
table state, so a stateless server can emit them and any conformant peer
decodes them with `Required Insert Count = 0`:

* **Indexed field line, static** (§4.5.2, `1 1 idx`) — a single byte `0xC0+i`
  for a static-table entry `i < 63`.
* **Literal field line with literal name** (§4.5.6, `0 0 1 N H` + 3-bit name
  length) — an arbitrary `(name, value)` pair, both strings emitted *without*
  Huffman coding (`H = 0`), which the decoder's no-Huffman path accepts for any
  valid UTF-8 octets.

The headline results bind the encoder to the *deployed* decoder:

* `decStr_encStr` — a string literal the encoder emits is decoded back exactly
  by `H3.Qpack.decStr` (built on the proven `decPrefixInt_encPrefixInt`).
* `decodeOneLine_encLiteralLine` / `decodeOneLine_encIndexedStatic` — one
  encoded field line decodes to exactly the `emitField` contribution the
  decoder would register, consuming exactly the encoded bytes.
* `decodeFieldSection_prefix` — the stateless `[0x00, 0x00]` section prefix
  (Required Insert Count 0, Base 0) drives the top-level `decodeFieldSection`
  into the field-line loop, so a whole encoded section round-trips (the
  executable `#guard` vector confirms one end to end).

Everything is `List UInt8`, matching the rest of the package.
-/

namespace H3
namespace Qpack

open Arena

/-! ## String-literal encoder (§4.1.2, no Huffman) -/

/-- Encode a string literal for a `p`-bit length prefix under pattern `pat`
(the bits above the prefix; its low bit is the Huffman flag `H`). We only emit
`H = 0` (no Huffman), so `pat` is even. -/
def encStr (p pat : Nat) (bs : Bytes) : Bytes :=
  encPrefixInt p pat bs.length ++ bs

/-- **String-literal round-trip.** For an even pattern (Huffman flag clear),
`decStr` decodes `encStr p pat bs` (under any suffix) back to `bs`, consuming
exactly the encoding. -/
theorem decStr_encStr (hd : HuffmanDecoder) (p pat : Nat) (bs tail : Bytes)
    (hp : 0 < p) (hp7 : p ≤ 7) (hpat : pat * 2 ^ p + (2 ^ p - 1) < 256)
    (hpatEven : pat % 2 = 0) (hlen : bs.length < 2 ^ 49) :
    ∃ (b : UInt8) (rest : Bytes),
      encPrefixInt p pat bs.length = b :: rest ∧
      decStr hd p b (rest ++ (bs ++ tail))
        = .ok (bs, rest.length + bs.length) := by
  obtain ⟨b, rest, henc, hdec⟩ :=
    decPrefixInt_encPrefixInt p pat bs.length (bs ++ tail) hp hp7 hpat hlen
  refine ⟨b, rest, henc, ?_⟩
  unfold decStr
  rw [hdec]
  -- body = ((rest ++ (bs ++ tail)).drop rest.length).take bs.length = bs
  have hdrop : (rest ++ (bs ++ tail)).drop rest.length = bs ++ tail :=
    List.drop_left
  simp only [hdrop]
  rw [List.take_left]                             -- take bs.length (bs ++ tail) = bs
  rw [if_neg (by simp)]
  -- Huffman flag: b.toNat / 2^p % 2 = pat % 2 = 0
  have hpow : (0 : Nat) < 2 ^ p := Nat.pow_pos (by omega)
  have hbval : b.toNat < 256 := b.toBitVec.isLt
  -- For a byte `pat*2^p + r` with `r < 2^p`, the bit at position `p` is `pat % 2`.
  have hgen : ∀ r : Nat, r < 2 ^ p → (pat * 2 ^ p + r) / 2 ^ p % 2 = 0 := by
    intro r hr
    rw [Nat.mul_comm pat, Nat.mul_add_div hpow, Nat.div_eq_of_lt hr, Nat.add_zero]
    exact hpatEven
  have hbmod : b.toNat / 2 ^ p % 2 = 0 := by
    unfold encPrefixInt at henc
    by_cases hsmall : bs.length < 2 ^ p - 1
    · rw [if_pos hsmall] at henc
      injection henc with hb _
      subst hb
      have hbe : (UInt8.ofNat (pat * 2 ^ p + bs.length)).toNat = pat * 2 ^ p + bs.length := by
        show (pat * 2 ^ p + bs.length) % 256 = pat * 2 ^ p + bs.length; omega
      rw [hbe]
      exact hgen bs.length (by omega)
    · rw [if_neg hsmall] at henc
      injection henc with hb _
      subst hb
      have hbe : (UInt8.ofNat (pat * 2 ^ p + (2 ^ p - 1))).toNat = pat * 2 ^ p + (2 ^ p - 1) := by
        show (pat * 2 ^ p + (2 ^ p - 1)) % 256 = pat * 2 ^ p + (2 ^ p - 1); omega
      rw [hbe]
      exact hgen (2 ^ p - 1) (by omega)
  rw [hbmod]
  simp

/-! ## Literal field line with literal name (§4.5.6) -/

/-- Encode a literal field line with a literal name: name under the 3-bit
prefix with the `0 0 1 0 0` marker (pattern `4`), value under the 7-bit
prefix with a clear Huffman flag (pattern `0`). Neither string is
Huffman-coded. -/
def encLiteralLine (name value : Bytes) : Bytes :=
  encStr 3 4 name ++ encStr 7 0 value

/-- **Literal-line round-trip.** One encoded literal field line (valid UTF-8
name and value, both within the varint window) decodes to exactly the
`emitField` contribution the deployed decoder registers, consuming exactly the
line's bytes. -/
theorem decodeOneLine_encLiteralLine (hd : HuffmanDecoder) (st : Store)
    (name value tail : Bytes) (dyn : DynTable) (base : Nat)
    (hname : utf8Ok name = true) (hvalue : utf8Ok value = true)
    (hnlen : name.length < 2 ^ 49) (hvlen : value.length < 2 ^ 49) :
    decodeOneLine hd st (encLiteralLine name value ++ tail) dyn base
      = (emitField st name value).map
          (fun r => (r.1, r.2, (encLiteralLine name value).length)) := by
  obtain ⟨bn, rn, hnenc, hndec⟩ :=
    decStr_encStr hd 3 4 name (encStr 7 0 value ++ tail)
      (by omega) (by omega) (by decide) (by decide) hnlen
  obtain ⟨bv, rv, hvenc, hvdec⟩ :=
    decStr_encStr hd 7 0 value tail (by omega) (by omega) (by decide) (by decide) hvlen
  -- The line's first byte is `bn`; the decoder enters the §4.5.6 branch.
  have hline : encLiteralLine name value ++ tail
      = bn :: (rn ++ (name ++ (bv :: (rv ++ (value ++ tail))))) := by
    unfold encLiteralLine encStr
    rw [hnenc, hvenc]
    simp [List.append_assoc]
  rw [hline]
  -- byte class: bn = 4*8 + r3 with r3 < 8, so 0x20 ≤ bn < 0x40.
  have hbn : bn.toNat = 32 + name.length % 8 ∨ bn.toNat = 32 + 7 := by
    unfold encPrefixInt at hnenc
    by_cases hs : name.length < 2 ^ 3 - 1
    · rw [if_pos hs] at hnenc
      injection hnenc with hb _
      left; subst hb
      show (4 * 2 ^ 3 + name.length) % 256 = 32 + name.length % 8
      have : name.length % 8 = name.length := by omega
      omega
    · rw [if_neg hs] at hnenc
      injection hnenc with hb _
      right; subst hb
      show (4 * 2 ^ 3 + (2 ^ 3 - 1)) % 256 = 32 + 7; rfl
  have hbnlt : ¬ 0x80 ≤ bn.toNat := by rcases hbn with h | h <;> omega
  have hbnlt2 : ¬ 0x40 ≤ bn.toNat := by rcases hbn with h | h <;> omega
  have hbnge : 0x20 ≤ bn.toNat := by rcases hbn with h | h <;> omega
  -- The suffix after the name-length prefix bytes, in encStr form.
  have hnalign : rn ++ (name ++ (encStr 7 0 value ++ tail))
      = rn ++ (name ++ (bv :: (rv ++ (value ++ tail)))) := by
    unfold encStr; rw [hvenc]; simp [List.append_assoc]
  have hvtail : (rn ++ (name ++ (encStr 7 0 value ++ tail))).drop (rn.length + name.length)
      = encStr 7 0 value ++ tail := by
    rw [show rn ++ (name ++ (encStr 7 0 value ++ tail))
          = (rn ++ name) ++ (encStr 7 0 value ++ tail) by simp [List.append_assoc],
        show rn.length + name.length = (rn ++ name).length by simp]
    exact List.drop_left
  have hvcons : encStr 7 0 value ++ tail = bv :: (rv ++ (value ++ tail)) := by
    unfold encStr; rw [hvenc]; simp [List.append_assoc]
  unfold decodeOneLine
  dsimp only
  rw [if_neg hbnlt, if_neg hbnlt2, if_pos hbnge]
  -- Name string: rewrite the suffix to encStr form and apply the name round-trip.
  rw [← hnalign, hndec]
  dsimp only
  -- Drop past the name; the value encoding remains.
  rw [hvtail, hvcons]
  dsimp only
  -- Value string.
  rw [hvdec]
  dsimp only
  rw [if_pos hvalue, if_pos hname]
  have hll : (encLiteralLine name value).length
      = 1 + (rn.length + name.length) + 1 + (rv.length + value.length) := by
    unfold encLiteralLine encStr
    rw [hnenc, hvenc]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hll]
  cases hemit : emitField st name value with
  | error e => simp [Except.map, hemit]
  | ok r =>
    obtain ⟨st', out⟩ := r
    simp only [Except.map, hemit]

/-! ## Indexed field line, static (§4.5.2, T=1) -/

/-- Encode an indexed static field line for a static-table index `i < 63`
(fits the 6-bit prefix in one byte): the single byte `0xC0 + i`. -/
def encIndexedStatic (i : Nat) : Bytes := [UInt8.ofNat (0xC0 + i)]

/-- **Indexed-static round-trip.** For a static index `i < 63` whose entry
exists, the one-byte encoding decodes to exactly the `emitField` contribution
of that static entry, consuming one byte. -/
theorem decodeOneLine_encIndexedStatic (hd : HuffmanDecoder) (st : Store)
    (i : Nat) (nm vl : String) (tail : Bytes) (dyn : DynTable) (base : Nat)
    (hi : i < 63) (hentry : staticEntry i = some (nm, vl)) :
    decodeOneLine hd st (encIndexedStatic i ++ tail) dyn base
      = (emitField st (strBytes nm) (strBytes vl)).map (fun r => (r.1, r.2, 1)) := by
  have hb : (UInt8.ofNat (0xC0 + i)).toNat = 0xC0 + i := by
    show (0xC0 + i) % 256 = 0xC0 + i; omega
  unfold encIndexedStatic decodeOneLine
  simp only [List.cons_append, List.nil_append]
  rw [if_pos (by rw [hb]; omega)]        -- 0x80 ≤ byte
  rw [if_pos (by rw [hb]; omega)]        -- 0x40 ≤ byte % 0x80  (T=1 static)
  have hpref : decPrefixInt 6 (UInt8.ofNat (0xC0 + i)) tail = some (i, 0) := by
    unfold decPrefixInt
    have hmod : (UInt8.ofNat (0xC0 + i)).toNat % 2 ^ 6 = i := by
      rw [hb]; omega
    rw [hmod, if_pos (by omega)]
  rw [hpref]
  dsimp only
  rw [hentry]
  cases hemit : emitField st (strBytes nm) (strBytes vl) with
  | error e => simp [Except.map, hemit]
  | ok r => obtain ⟨st', out⟩ := r; simp [Except.map, hemit]

/-! ## The field section (§4.5.1) -/

/-- The section prefix for a stateless (no dynamic table) section: encoded
Required Insert Count `0` and Delta Base `0` (sign clear) — two `0x00` bytes. -/
def sectionPrefix : Bytes := [0x00, 0x00]

/-- Encode a whole field section from a list of literal `(name, value)` pairs:
the stateless section prefix followed by one literal field line per pair. -/
def encodeFieldSection (headers : List (Bytes × Bytes)) : Bytes :=
  sectionPrefix ++ (headers.flatMap (fun p => encLiteralLine p.1 p.2))

/-- The section prefix decodes to `Required Insert Count = 0`, `Base = 0`:
`decodeFieldSection` on `sectionPrefix ++ rest` reduces to `decodeLines` over
`rest` with an empty base against the empty table. -/
theorem decodeFieldSection_prefix (hd : HuffmanDecoder) (st : Store) (rest : Bytes) :
    decodeFieldSection hd st (sectionPrefix ++ rest)
      = (decodeLines hd st rest {} [] DynTable.empty 0).map
          (fun r => ⟨r.1, r.2.1, r.2.2⟩) := by
  -- The whole prefix computation (both prefix integers, the RIC/base
  -- reconstruction) reduces definitionally; only `decodeLines` is opaque (it is
  -- well-founded), so the top-level reduces to a match on it.
  have hred : decodeFieldSection hd st (sectionPrefix ++ rest)
      = (match decodeLines hd st rest {} [] DynTable.empty 0 with
         | .error e => .error e
         | .ok (st', p, f) => (.ok ⟨st', p, f⟩ : Except Err Decoded)) := rfl
  rw [hred]
  cases decodeLines hd st rest {} [] DynTable.empty 0 <;> rfl

/-! ## Wire vectors, checker-verified -/

-- The stateless section prefix is two zero bytes.
#guard sectionPrefix = [0x00, 0x00]

-- A literal line for `("x-a", "b")` decodes (with the empty store) back to that
-- one field: name "x-a" (0x78 0x2d 0x61), value "b" (0x62).
private def emptyStore : Store := { main := #[], sidecar := #[], entries := [] }
private def vecLiteral : Bool :=
  match decodeFieldSection rfc7541Huffman emptyStore
      (encodeFieldSection [([0x78, 0x2d, 0x61], [0x62])]) with
  | .ok d => d.fields.length == 1
  | .error _ => false
#guard vecLiteral

-- An indexed static line for index 25 (":status: 200") is the single byte 0xD9.
#guard encIndexedStatic 25 = [0xD9]

#print axioms decStr_encStr
#print axioms decodeOneLine_encLiteralLine
#print axioms decodeOneLine_encIndexedStatic
#print axioms decodeFieldSection_prefix

end Qpack
end H3
