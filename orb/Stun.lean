/-!
# STUN messages (RFC 5389) — parsing, serialization, integrity, and the Binding service

A total, sans-IO codec and server behavior for STUN messages as they arrive on
the wire. STUN (Session Traversal Utilities for NAT) is the base framing that
ICE connectivity checks (RFC 8445) ride on: every check is a STUN Binding
request/response, so a data-channel stack cannot form a candidate pair without
first agreeing on this frame.

## What this file captures

* **RFC 5389 §6 — the message header.** Every STUN message begins with a fixed
  20-byte header: a 16-bit message type (whose two most significant bits are
  zero), a 16-bit message length, the 32-bit magic cookie `0x2112A442`, and a
  96-bit (12-byte) transaction id. `parse` reads exactly this layout and
  requires the declared length to cover the entire rest of the datagram — a
  message with trailing bytes past the declared length is malformed.
* **RFC 5389 §15 — TLV attributes.** After the header come zero or more
  attributes, each a 16-bit type, a 16-bit length (of the value, before
  padding), the value, and 0–3 bytes of padding so each attribute ends on a
  32-bit boundary. `parseAttrs` walks them; `encodeAttrs` serializes them.
* **RFC 5389 §6/§7 — serialization.** `encode` builds a message from type,
  transaction id, and attributes; `parse_encode` proves the codec round-trips.
* **RFC 5389 §15.2 — XOR-MAPPED-ADDRESS.** `xorMappedValue`/`decodeXorMapped`
  obfuscate/recover the reflexive transport address; `xorMapped_roundtrip`
  proves decode ∘ encode = id.
* **RFC 5389 §15.4 — MESSAGE-INTEGRITY.** A real, executable HMAC-SHA1
  (FIPS 180-4 SHA-1, RFC 2104 HMAC) over the message prefix with the length
  field adjusted to cover the attribute, exactly as §15.4 prescribes.
  `messageIntegrity_roundtrip` proves sign-then-verify succeeds.
* **RFC 5389 §15.5 — FINGERPRINT.** A real CRC-32 (ISO 3309, reflected
  0xEDB88320 polynomial) xored with 0x5354554E. `fingerprint_roundtrip`
  proves append-then-verify succeeds.
* **RFC 5389 §7.2.1 — the Binding request transaction.** `Tx` models the
  retransmission schedule: initial RTO 500 ms, doubling per retransmission,
  Rc = 7 transmissions total, then a final Rm × RTO wait. `tx_schedule`
  pins the exact timer sequence (500, 1000, …, 16000, 8000 ms — the §7.2.1
  example), and `tx_gives_up` that the transaction stops at Rc transmissions.
* **RFC 5389 §7.3.1/§15.9 — unknown attributes and error responses.**
  `unknownComprehensionRequired` flags unknown attribute types in the
  comprehension-required range (0x0000–0x7FFF); `bindingError` builds the 420
  response carrying ERROR-CODE (§15.6) and UNKNOWN-ATTRIBUTES (§15.9);
  `respond` is the full Binding-server step: success with XOR-MAPPED-ADDRESS
  and FINGERPRINT, or 420, or silence for non-requests and malformed input.

## Notes on SHA-1 and CRC-32

These are the concrete functions RFC 5389 names, implemented directly so the
integrity checks are computable and the round-trip theorems are about the real
computation, not an abstract boundary. Neither is a cryptographic assumption
in the sense of the AEAD/signature seams elsewhere: FINGERPRINT is a checksum
for demultiplexing, and MESSAGE-INTEGRITY's security rests on the secrecy of
the short-term credential, which this module does not model — it states only
functional correctness of the computation.
-/

namespace Stun

/-- Raw byte strings, modeled as lists to match the sibling libraries. -/
abbrev Bytes := List UInt8

/-- Big-endian decode of two bytes into a 16-bit value. -/
def be16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- The magic cookie (RFC 5389 §6), `0x2112A442` in network byte order. -/
def magicCookie : Bytes := [0x21, 0x12, 0xA4, 0x42]

/-! ## Attributes (RFC 5389 §15) -/

/-- A decoded TLV attribute: the 16-bit type and the value (padding stripped).
The declared length equals `value.length`. -/
structure Attr where
  type : Nat
  value : Bytes
deriving Repr, DecidableEq

/-- The number of padding bytes appended after a value of length `n` so the
attribute ends on a 32-bit boundary (§15): `(4 - n mod 4) mod 4`. -/
def padLen (n : Nat) : Nat := (4 - n % 4) % 4

theorem padLen_lt (n : Nat) : padLen n < 4 := by
  simp only [padLen]; omega

/-- Walk a body region into a list of TLV attributes. Structurally recursive on
`fuel` (the body length is always enough fuel, since each attribute consumes at
least its 4-byte TLV header). A step reads the 16-bit type and 16-bit length,
takes `len` value bytes, and skips `len + padLen len` bytes to the next
attribute; it fails if the declared value plus padding would run past the
remaining buffer, or if a stray 1–3 bytes remain. -/
def parseAttrsF : Nat → Bytes → Option (List Attr)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, t1 :: t0 :: l1 :: l0 :: rest =>
    let typ := be16 t1 t0
    let len := be16 l1 l0
    let pad := padLen len
    if len + pad ≤ rest.length then
      let value := rest.take len
      let rest' := rest.drop (len + pad)
      match parseAttrsF fuel rest' with
      | some attrs => some ({ type := typ, value := value } :: attrs)
      | none => none
    else none
  | _ + 1, _ => none

/-- Parse the attribute region of a body: fuel is exactly the body length. -/
def parseAttrs (body : Bytes) : Option (List Attr) := parseAttrsF body.length body

/-! ## The message -/

/-- A decoded STUN message (RFC 5389 §6): the 16-bit type, the declared length,
the 12-byte transaction id, and the attribute list. -/
structure Message where
  typ : Nat
  length : Nat
  txid : Bytes
  attrs : List Attr
deriving Repr

/-- Parse a STUN message. Reads the 20-byte header (type, length, magic cookie,
transaction id), rejects any message whose cookie is not `0x2112A442`, requires
the declared length to equal the number of bytes remaining after the header
(§6: the length field MUST contain the size of the message — trailing bytes
make the datagram malformed), then parses the attributes. Total: returns
`none` on any malformed or truncated input. -/
def parse (b : Bytes) : Option Message :=
  match b with
  | ty1 :: ty0 :: ln1 :: ln0 :: m3 :: m2 :: m1 :: m0 :: rest =>
    if [m3, m2, m1, m0] = magicCookie then
      let typ := be16 ty1 ty0
      let len := be16 ln1 ln0
      let txid := rest.take 12
      let afterTx := rest.drop 12
      if 12 ≤ rest.length ∧ len = afterTx.length then
        let body := afterTx.take len
        match parseAttrs body with
        | some attrs => some { typ := typ, length := len, txid := txid, attrs := attrs }
        | none => none
      else none
    else none
  | _ => none

/-! ## Parsing theorems -/

/-- **Magic-cookie guard (RFC 5389 §6).** A message whose 32-bit cookie field is
not `0x2112A442` is rejected outright. This is what lets a receiver tell STUN
apart from the media it is multiplexed with on the same port. -/
theorem stun_magic_checked
    (ty1 ty0 ln1 ln0 m3 m2 m1 m0 : UInt8) (rest : Bytes)
    (h : [m3, m2, m1, m0] ≠ magicCookie) :
    parse (ty1 :: ty0 :: ln1 :: ln0 :: m3 :: m2 :: m1 :: m0 :: rest) = none := by
  simp only [parse, if_neg h]

/-- **Totality.** The decoder returns for every input, with exactly two possible
shapes: rejection or a single decoded message. No partial/stuck outcome. -/
theorem stun_parse_total (b : Bytes) :
    parse b = none ∨ ∃ m, parse b = some m := by
  cases h : parse b with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, rfl⟩

/-- A message shorter than the fixed 20-byte header is rejected (a corollary of
the header shape: fewer than the eight leading bytes cannot match). -/
theorem stun_parse_short (b : Bytes) (h : b.length < 8) : parse b = none := by
  match b with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- Every attribute produced by `parseAttrsF` has a value no longer than the
body it was read from. Proved by induction on the fuel. -/
theorem parseAttrsF_value_bound (fuel : Nat) :
    ∀ (body : Bytes) (attrs : List Attr), parseAttrsF fuel body = some attrs →
      ∀ a ∈ attrs, a.value.length ≤ body.length := by
  induction fuel with
  | zero =>
    intro body attrs h a ha
    match body with
    | [] =>
      simp only [parseAttrsF, Option.some.injEq] at h
      subst h; simp at ha
    | _ :: _ => simp [parseAttrsF] at h
  | succ n ih =>
    intro body attrs h a ha
    match body with
    | [] =>
      simp only [parseAttrsF, Option.some.injEq] at h
      subst h; simp at ha
    | [_] => simp [parseAttrsF] at h
    | [_, _] => simp [parseAttrsF] at h
    | [_, _, _] => simp [parseAttrsF] at h
    | t1 :: t0 :: l1 :: l0 :: rest =>
      simp only [parseAttrsF] at h
      by_cases hb : be16 l1 l0 + padLen (be16 l1 l0) ≤ rest.length
      · rw [if_pos hb] at h
        cases hrec : parseAttrsF n (rest.drop (be16 l1 l0 + padLen (be16 l1 l0))) with
        | none => rw [hrec] at h; simp at h
        | some tail =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp ha with hhd | htl
          · subst hhd
            simp only [List.length_take]
            calc min (be16 l1 l0) rest.length ≤ rest.length := Nat.min_le_right _ _
              _ ≤ (t1 :: t0 :: l1 :: l0 :: rest).length := by simp only [List.length_cons]; omega
          · have hbound := ih _ _ hrec a htl
            have hdrop : (rest.drop (be16 l1 l0 + padLen (be16 l1 l0))).length ≤ rest.length :=
              by rw [List.length_drop]; omega
            calc a.value.length ≤ (rest.drop (be16 l1 l0 + padLen (be16 l1 l0))).length := hbound
              _ ≤ rest.length := hdrop
              _ ≤ (t1 :: t0 :: l1 :: l0 :: rest).length := by simp only [List.length_cons]; omega
      · rw [if_neg hb] at h; simp at h

/-- **Attribute bounds (RFC 5389 §15).** In any successfully parsed message,
every attribute's value stays within the declared message length. The decoder
never reports an attribute reaching past the region the header claimed. -/
theorem stun_attr_bounds (b : Bytes) (m : Message) (h : parse b = some m) :
    ∀ a ∈ m.attrs, a.value.length ≤ m.length := by
  intro a ha
  match b with
  | ty1 :: ty0 :: ln1 :: ln0 :: c3 :: c2 :: c1 :: c0 :: rest =>
    simp only [parse] at h
    by_cases hc : [c3, c2, c1, c0] = magicCookie
    · rw [if_pos hc] at h
      by_cases hlen : 12 ≤ rest.length ∧ be16 ln1 ln0 = (rest.drop 12).length
      · rw [if_pos hlen] at h
        cases hrec : parseAttrs ((rest.drop 12).take (be16 ln1 ln0)) with
        | none => rw [hrec] at h; simp at h
        | some attrs =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          -- m.attrs = attrs, m.length = be16 ln1 ln0
          have hbody := parseAttrsF_value_bound _ _ _ hrec a ha
          have hbl : ((rest.drop 12).take (be16 ln1 ln0)).length ≤ be16 ln1 ln0 := by
            rw [List.length_take]; exact Nat.min_le_left _ _
          exact Nat.le_trans hbody hbl
      · rw [if_neg hlen] at h; simp at h
    · rw [if_neg hc] at h; simp at h
  | [] => simp [parse] at h
  | [_] => simp [parse] at h
  | [_, _] => simp [parse] at h
  | [_, _, _] => simp [parse] at h
  | [_, _, _, _] => simp [parse] at h
  | [_, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _, _] => simp [parse] at h

/-- **Length exactness (RFC 5389 §6).** A successfully parsed datagram is
exactly the 20-byte header plus the declared message length: the parser
accepts no trailing bytes past the declared length. -/
theorem stun_length_exact (b : Bytes) (m : Message) (h : parse b = some m) :
    b.length = 20 + m.length := by
  match b with
  | ty1 :: ty0 :: ln1 :: ln0 :: c3 :: c2 :: c1 :: c0 :: rest =>
    simp only [parse] at h
    by_cases hc : [c3, c2, c1, c0] = magicCookie
    · rw [if_pos hc] at h
      by_cases hlen : 12 ≤ rest.length ∧ be16 ln1 ln0 = (rest.drop 12).length
      · rw [if_pos hlen] at h
        cases hrec : parseAttrs ((rest.drop 12).take (be16 ln1 ln0)) with
        | none => rw [hrec] at h; simp at h
        | some attrs =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_cons]
          obtain ⟨h12, hexact⟩ := hlen
          rw [List.length_drop] at hexact
          omega
      · rw [if_neg hlen] at h; simp at h
    · rw [if_neg hc] at h; simp at h
  | [] => simp [parse] at h
  | [_] => simp [parse] at h
  | [_, _] => simp [parse] at h
  | [_, _, _] => simp [parse] at h
  | [_, _, _, _] => simp [parse] at h
  | [_, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _, _] => simp [parse] at h

/-- The transaction id of any successfully parsed message is exactly 12 bytes
(RFC 5389 §6: a 96-bit field). -/
theorem stun_txid_length (b : Bytes) (m : Message) (h : parse b = some m) :
    m.txid.length = 12 := by
  match b with
  | ty1 :: ty0 :: ln1 :: ln0 :: c3 :: c2 :: c1 :: c0 :: rest =>
    simp only [parse] at h
    by_cases hc : [c3, c2, c1, c0] = magicCookie
    · rw [if_pos hc] at h
      by_cases hlen : 12 ≤ rest.length ∧ be16 ln1 ln0 = (rest.drop 12).length
      · rw [if_pos hlen] at h
        cases hrec : parseAttrs ((rest.drop 12).take (be16 ln1 ln0)) with
        | none => rw [hrec] at h; simp at h
        | some attrs =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_take]
          obtain ⟨h12, _⟩ := hlen
          omega
      · rw [if_neg hlen] at h; simp at h
    · rw [if_neg hc] at h; simp at h
  | [] => simp [parse] at h
  | [_] => simp [parse] at h
  | [_, _] => simp [parse] at h
  | [_, _, _] => simp [parse] at h
  | [_, _, _, _] => simp [parse] at h
  | [_, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _] => simp [parse] at h
  | [_, _, _, _, _, _, _] => simp [parse] at h

/-! ## Serialization (RFC 5389 §6, §7) -/

/-- Big-endian encode of a 16-bit value into two bytes (the inverse of `be16`
for values below `2^16`). -/
def enc16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- `n` zero bytes (attribute padding, §15). -/
def zeros : Nat → Bytes
  | 0 => []
  | n + 1 => 0 :: zeros n

@[simp] theorem zeros_length (n : Nat) : (zeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeros, ih]

theorem be16_enc16 (n : Nat) (h : n < 65536) :
    be16 (UInt8.ofNat (n / 256)) (UInt8.ofNat (n % 256)) = n := by
  simp [be16, UInt8.toNat_ofNat]
  omega

/-- Serialize one TLV attribute: 16-bit type, 16-bit value length, the value,
then zero padding to a 32-bit boundary (§15). -/
def encodeAttr (a : Attr) : Bytes :=
  enc16 a.type ++ enc16 a.value.length ++ a.value ++ zeros (padLen a.value.length)

/-- The wire size of one attribute: 4-byte TLV header + value + padding. -/
def attrSize (a : Attr) : Nat := 4 + a.value.length + padLen a.value.length

theorem encodeAttr_length (a : Attr) : (encodeAttr a).length = attrSize a := by
  simp [encodeAttr, attrSize, enc16]
  omega

/-- Serialize an attribute list back-to-back (§15). -/
def encodeAttrs : List Attr → Bytes
  | [] => []
  | a :: rest => encodeAttr a ++ encodeAttrs rest

theorem encodeAttrs_append (l1 l2 : List Attr) :
    encodeAttrs (l1 ++ l2) = encodeAttrs l1 ++ encodeAttrs l2 := by
  induction l1 with
  | nil => rfl
  | cons a rest ih => simp [encodeAttrs, ih]

/-- Serialize a full STUN message (§6): type, body length, magic cookie,
12-byte transaction id, then the attributes. -/
def encode (typ : Nat) (txid : Bytes) (attrs : List Attr) : Bytes :=
  enc16 typ ++ enc16 (encodeAttrs attrs).length ++ magicCookie ++ txid ++ encodeAttrs attrs

/-- **Attribute codec round-trip (§15).** Parsing a serialized attribute list
(with sufficient fuel) yields exactly the original attributes, provided each
attribute's type and value length fit their 16-bit wire fields. -/
theorem parseAttrsF_encodeAttrs :
    ∀ (attrs : List Attr) (fuel : Nat), (encodeAttrs attrs).length ≤ fuel →
      (∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536) →
      parseAttrsF fuel (encodeAttrs attrs) = some attrs
  | [], fuel, _, _ => by cases fuel <;> rfl
  | a :: rest, fuel, hf, hwf => by
    obtain ⟨ht, hv⟩ := hwf a (List.mem_cons_self a rest)
    have hrest : ∀ x ∈ rest, x.type < 65536 ∧ x.value.length < 65536 :=
      fun x hx => hwf x (List.mem_cons_of_mem a hx)
    have hsz : 4 ≤ attrSize a := by simp [attrSize]; omega
    have hlen : (encodeAttrs (a :: rest)).length
        = attrSize a + (encodeAttrs rest).length := by
      simp [encodeAttrs, encodeAttr_length]
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      have hshape : encodeAttrs (a :: rest) =
          UInt8.ofNat (a.type / 256) :: UInt8.ofNat (a.type % 256) ::
          UInt8.ofNat (a.value.length / 256) :: UInt8.ofNat (a.value.length % 256) ::
          (a.value ++ (zeros (padLen a.value.length) ++ encodeAttrs rest)) := by
        simp [encodeAttrs, encodeAttr, enc16]
      rw [hshape]
      simp only [parseAttrsF]
      rw [be16_enc16 a.type ht, be16_enc16 a.value.length hv]
      have hcond : a.value.length + padLen a.value.length
          ≤ (a.value ++ (zeros (padLen a.value.length) ++ encodeAttrs rest)).length := by
        simp only [List.length_append, zeros_length]
        omega
      rw [if_pos hcond]
      rw [List.take_left' rfl]
      rw [show a.value ++ (zeros (padLen a.value.length) ++ encodeAttrs rest)
          = (a.value ++ zeros (padLen a.value.length)) ++ encodeAttrs rest by
        simp [List.append_assoc]]
      rw [List.drop_left' (by simp only [List.length_append, zeros_length])]
      rw [parseAttrsF_encodeAttrs rest fuel (by omega) hrest]

/-- **Codec round-trip (RFC 5389 §6, §7).** Parsing a serialized message yields
exactly the original type, transaction id, and attributes, with the length
field set to the serialized body length — under the wire-field well-formedness
side conditions (16-bit type and lengths, 12-byte transaction id). -/
theorem parse_encode (typ : Nat) (txid : Bytes) (attrs : List Attr)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536) :
    parse (encode typ txid attrs) =
      some { typ := typ, length := (encodeAttrs attrs).length,
             txid := txid, attrs := attrs } := by
  have hshape : encode typ txid attrs =
      UInt8.ofNat (typ / 256) :: UInt8.ofNat (typ % 256) ::
      UInt8.ofNat ((encodeAttrs attrs).length / 256) ::
      UInt8.ofNat ((encodeAttrs attrs).length % 256) ::
      0x21 :: 0x12 :: 0xA4 :: 0x42 :: (txid ++ encodeAttrs attrs) := by
    simp [encode, enc16, magicCookie]
  rw [hshape]
  simp only [parse]
  rw [if_pos (show ([0x21, 0x12, 0xA4, 0x42] : Bytes) = magicCookie from rfl)]
  rw [be16_enc16 typ htyp, be16_enc16 _ hblen]
  have hdrop : (txid ++ encodeAttrs attrs).drop 12 = encodeAttrs attrs :=
    List.drop_left' htx
  have htake : (txid ++ encodeAttrs attrs).take 12 = txid :=
    List.take_left' htx
  have hcond : 12 ≤ (txid ++ encodeAttrs attrs).length ∧
      (encodeAttrs attrs).length = ((txid ++ encodeAttrs attrs).drop 12).length := by
    constructor
    · simp [htx]
    · rw [hdrop]
  rw [if_pos hcond, htake, hdrop, List.take_length]
  rw [show parseAttrs (encodeAttrs attrs) = some attrs from
    parseAttrsF_encodeAttrs attrs (encodeAttrs attrs).length (Nat.le_refl _) hwf]

/-! ## SHA-1 (FIPS 180-4), HMAC-SHA1 (RFC 2104), CRC-32 (ISO 3309)

The two checksum functions STUN's integrity attributes are built from
(§15.4 MESSAGE-INTEGRITY, §15.5 FINGERPRINT), implemented directly so the
checks are computable and the sign/verify round-trip theorems below are about
the real computation. -/

/-- Left-rotate a 32-bit word by `n < 32` bits. -/
def rotl (n : Nat) (x : UInt32) : UInt32 :=
  (x <<< UInt32.ofNat n) ||| (x >>> UInt32.ofNat (32 - n))

/-- Byte `i` of a buffer (0 past the end; callers only read in-bounds). -/
def byteAt (b : Bytes) (i : Nat) : UInt8 := b.getD i 0

/-- Big-endian 32-bit word at byte offset `i`. -/
def word32At (b : Bytes) (i : Nat) : UInt32 :=
  (byteAt b i).toUInt32 <<< 24 ||| (byteAt b (i + 1)).toUInt32 <<< 16 |||
  (byteAt b (i + 2)).toUInt32 <<< 8 ||| (byteAt b (i + 3)).toUInt32

/-- Big-endian bytes of a 32-bit word. -/
def u32Bytes (x : UInt32) : Bytes :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

@[simp] theorem u32Bytes_length (x : UInt32) : (u32Bytes x).length = 4 := rfl

/-- Big-endian bytes of a 64-bit value (the SHA-1 padding trailer). -/
def u64Bytes (n : Nat) : Bytes :=
  (List.range 8).map fun i => UInt8.ofNat (n >>> ((7 - i) * 8))

/-- The five-word SHA-1 chaining state. -/
structure Sha1State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32

/-- FIPS 180-4 §5.3.1 initial hash value. -/
def sha1Init : Sha1State :=
  ⟨0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0⟩

/-- FIPS 180-4 §6.1.2 message schedule: 16 words from the chunk, extended to 80. -/
def sha1Schedule (chunk : Bytes) : Array UInt32 :=
  let w := (List.range 16).foldl (fun w j => w.push (word32At chunk (4 * j)))
    (#[] : Array UInt32)
  (List.range 64).foldl (fun w i =>
    w.push (rotl 1 (w[i + 13]! ^^^ w[i + 8]! ^^^ w[i + 2]! ^^^ w[i]!))) w

/-- One FIPS 180-4 §6.1.2 round: the round function and constant depend on the
round index quarter. -/
def sha1Round (st : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (t : Nat)
    (wt : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 :=
  let (a, b, c, d, e) := st
  let f : UInt32 :=
    if t < 20 then (b &&& c) ||| ((~~~b) &&& d)
    else if t < 40 then b ^^^ c ^^^ d
    else if t < 60 then (b &&& c) ||| (b &&& d) ||| (c &&& d)
    else b ^^^ c ^^^ d
  let k : UInt32 :=
    if t < 20 then 0x5A827999
    else if t < 40 then 0x6ED9EBA1
    else if t < 60 then 0x8F1BBCDC
    else 0xCA62C1D6
  (rotl 5 a + f + e + k + wt, a, rotl 30 b, c, d)

/-- Compress one 64-byte chunk into the chaining state. -/
def sha1Chunk (st : Sha1State) (chunk : Bytes) : Sha1State :=
  let w := sha1Schedule chunk
  let (a, b, c, d, e) := (List.range 80).foldl
    (fun s t => sha1Round s t w[t]!) (st.h0, st.h1, st.h2, st.h3, st.h4)
  ⟨st.h0 + a, st.h1 + b, st.h2 + c, st.h3 + d, st.h4 + e⟩

/-- FIPS 180-4 §5.1.1 padding: a 0x80 byte, zeros to 56 mod 64, then the
big-endian 64-bit bit length. -/
def sha1Pad (msg : Bytes) : Bytes :=
  msg ++ [0x80] ++ zeros ((119 - msg.length % 64) % 64) ++ u64Bytes (msg.length * 8)

/-- SHA-1 (FIPS 180-4): 20-byte digest. -/
def sha1 (msg : Bytes) : Bytes :=
  let padded := sha1Pad msg
  let st := (List.range (padded.length / 64)).foldl
    (fun st i => sha1Chunk st ((padded.drop (64 * i)).take 64)) sha1Init
  u32Bytes st.h0 ++ u32Bytes st.h1 ++ u32Bytes st.h2 ++ u32Bytes st.h3 ++ u32Bytes st.h4

theorem sha1_length (msg : Bytes) : (sha1 msg).length = 20 := by
  simp [sha1]

/-- HMAC-SHA1 (RFC 2104), block size 64. -/
def hmacSha1 (key msg : Bytes) : Bytes :=
  let k0 := if 64 < key.length then sha1 key else key
  let k := k0 ++ zeros (64 - k0.length)
  sha1 ((k.map (· ^^^ 0x5c)) ++ sha1 ((k.map (· ^^^ 0x36)) ++ msg))

theorem hmacSha1_length (key msg : Bytes) : (hmacSha1 key msg).length = 20 :=
  sha1_length _

/-- One byte of the reflected CRC-32 (polynomial 0xEDB88320). -/
def crc32Byte (c : UInt32) (b : UInt8) : UInt32 :=
  (List.range 8).foldl
    (fun c _ => if c &&& 1 == 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1)
    (c ^^^ b.toUInt32)

/-- CRC-32 (ISO 3309 / ITU-T V.42, as used by RFC 5389 §15.5). -/
def crc32 (msg : Bytes) : UInt32 :=
  msg.foldl crc32Byte 0xFFFFFFFF ^^^ 0xFFFFFFFF

/-! ## MESSAGE-INTEGRITY (§15.4) and FINGERPRINT (§15.5) -/

/-- Well-known attribute types (RFC 5389 §18.2, RFC 8445 §16.1). -/
def attrMappedAddress : Nat := 0x0001
def attrUsername : Nat := 0x0006
def attrMessageIntegrity : Nat := 0x0008
def attrErrorCode : Nat := 0x0009
def attrUnknownAttributes : Nat := 0x000A
def attrRealm : Nat := 0x0014
def attrNonce : Nat := 0x0015
def attrXorMappedAddress : Nat := 0x0020
def attrPriority : Nat := 0x0024
def attrUseCandidate : Nat := 0x0025
def attrChangeRequest : Nat := 0x0003
def attrPadding : Nat := 0x0026
def attrResponsePort : Nat := 0x0027
def attrSoftware : Nat := 0x8022
def attrFingerprint : Nat := 0x8028

/-- The FINGERPRINT xor constant (§15.5). -/
def fingerprintMask : UInt32 := 0x5354554E

/-- Byte offset, within the attribute region, of the first attribute of type
`t` in a decoded attribute list (each earlier attribute occupies its TLV
header, value, and padding on the wire). -/
def offsetOf (t : Nat) : List Attr → Option Nat
  | [] => none
  | a :: rest =>
    if a.type = t then some 0
    else (offsetOf t rest).map (attrSize a + ·)

/-- **MESSAGE-INTEGRITY verification (§15.4).** Locates the MESSAGE-INTEGRITY
attribute, recomputes HMAC-SHA1 over the message up to (excluding) that
attribute with the header length field rewritten to point past it — exactly
the §15.4 input — and compares with the carried digest. -/
def messageIntegrityOk (key msg : Bytes) : Bool :=
  ((parse msg).bind fun m =>
    (offsetOf attrMessageIntegrity m.attrs).bind fun boff =>
      (m.attrs.find? fun a => a.type == attrMessageIntegrity).map fun a =>
        hmacSha1 key
          (msg.take 2 ++ enc16 (boff + 24) ++ (msg.drop 4).take (16 + boff))
          == a.value).getD false

/-- **FINGERPRINT verification (§15.5).** Locates the FINGERPRINT attribute and
compares it with `crc32` of the message up to that attribute, xored with
`0x5354554E`. -/
def fingerprintOk (msg : Bytes) : Bool :=
  ((parse msg).bind fun m =>
    (offsetOf attrFingerprint m.attrs).bind fun boff =>
      (m.attrs.find? fun a => a.type == attrFingerprint).map fun a =>
        a.value == u32Bytes (crc32 (msg.take (20 + boff)) ^^^ fingerprintMask)).getD false

/-- Serialize a message and append a MESSAGE-INTEGRITY attribute whose HMAC is
computed with the length field already covering the attribute (§15.4). -/
def withMessageIntegrity (key : Bytes) (typ : Nat) (txid : Bytes)
    (attrs : List Attr) : Bytes :=
  let body := encodeAttrs attrs
  let pre := enc16 typ ++ enc16 (body.length + 24) ++ magicCookie ++ txid ++ body
  pre ++ encodeAttr { type := attrMessageIntegrity, value := hmacSha1 key pre }

/-- Serialize a message and append a FINGERPRINT attribute whose CRC covers the
whole message before it, with the length field already covering the attribute
(§15.5). -/
def withFingerprint (typ : Nat) (txid : Bytes) (attrs : List Attr) : Bytes :=
  let body := encodeAttrs attrs
  let pre := enc16 typ ++ enc16 (body.length + 8) ++ magicCookie ++ txid ++ body
  pre ++ encodeAttr { type := attrFingerprint,
                      value := u32Bytes (crc32 pre ^^^ fingerprintMask) }

/-! ### Round-trip machinery -/

theorem find?_append_last (attrs : List Attr) (a : Attr) (t : Nat)
    (hat : a.type = t) (h : ∀ x ∈ attrs, x.type ≠ t) :
    (attrs ++ [a]).find? (fun x => x.type == t) = some a := by
  induction attrs with
  | nil =>
    rw [List.nil_append]
    exact List.find?_cons_of_pos _ (by simp [hat])
  | cons x rest ih =>
    rw [List.cons_append, List.find?_cons_of_neg _ (by
      simp only [beq_iff_eq]
      exact h x (List.mem_cons_self x rest))]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem offsetOf_append_last (attrs : List Attr) (a : Attr) (t : Nat)
    (hat : a.type = t) (h : ∀ x ∈ attrs, x.type ≠ t) :
    offsetOf t (attrs ++ [a]) = some (encodeAttrs attrs).length := by
  induction attrs with
  | nil => simp [offsetOf, hat, encodeAttrs]
  | cons x rest ih =>
    have hx : x.type ≠ t := h x (List.mem_cons_self x rest)
    have := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.cons_append, offsetOf, if_neg hx, this, Option.map_some']
    simp [encodeAttrs, encodeAttr_length]

/-- Appending one serialized attribute, seen at the `encode` level. -/
theorem encode_snoc (typ : Nat) (txid : Bytes) (attrs : List Attr) (a : Attr) :
    encode typ txid (attrs ++ [a]) =
      (enc16 typ ++ enc16 ((encodeAttrs attrs).length + attrSize a) ++
        magicCookie ++ txid ++ encodeAttrs attrs) ++ encodeAttr a := by
  simp [encode, encodeAttrs_append, encodeAttrs, encodeAttr_length,
    List.append_assoc]

/-- The `withMessageIntegrity` output, seen as a plain `encode` of the
extended attribute list. -/
theorem withMessageIntegrity_eq_encode (key : Bytes) (typ : Nat) (txid : Bytes)
    (attrs : List Attr) :
    withMessageIntegrity key typ txid attrs =
      encode typ txid (attrs ++ [⟨attrMessageIntegrity,
        hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
          magicCookie ++ txid ++ encodeAttrs attrs)⟩]) := by
  rw [encode_snoc]
  have hsz : attrSize (⟨attrMessageIntegrity,
      hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
        magicCookie ++ txid ++ encodeAttrs attrs)⟩ : Attr) = 24 := by
    simp [attrSize, hmacSha1_length, padLen]
  rw [hsz]
  rfl

/-- The `withFingerprint` output, seen as a plain `encode` of the extended
attribute list. -/
theorem withFingerprint_eq_encode (typ : Nat) (txid : Bytes) (attrs : List Attr) :
    withFingerprint typ txid attrs =
      encode typ txid (attrs ++ [⟨attrFingerprint,
        u32Bytes (crc32 (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 8) ++
          magicCookie ++ txid ++ encodeAttrs attrs) ^^^ fingerprintMask)⟩]) := by
  rw [encode_snoc]
  have hsz : attrSize (⟨attrFingerprint,
      u32Bytes (crc32 (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 8) ++
        magicCookie ++ txid ++ encodeAttrs attrs) ^^^ fingerprintMask)⟩ : Attr) = 8 := by
    simp [attrSize, padLen]
  rw [hsz]
  rfl

/-- A MESSAGE-INTEGRITY-protected message parses back to the extended
attribute list, with the length field covering the integrity attribute. -/
theorem withMessageIntegrity_parses (key : Bytes) (typ : Nat) (txid : Bytes)
    (attrs : List Attr) (mac : Bytes)
    (hmac : hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
      magicCookie ++ txid ++ encodeAttrs attrs) = mac)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 24 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536) :
    parse (withMessageIntegrity key typ txid attrs) =
      some { typ := typ, length := (encodeAttrs attrs).length + 24, txid := txid,
             attrs := attrs ++ [⟨attrMessageIntegrity, mac⟩] } := by
  have hmaclen : mac.length = 20 := by rw [← hmac]; exact hmacSha1_length key _
  have henc : withMessageIntegrity key typ txid attrs =
      encode typ txid (attrs ++ [⟨attrMessageIntegrity, mac⟩]) := by
    rw [← hmac]
    exact withMessageIntegrity_eq_encode key typ txid attrs
  have hblenA : (encodeAttrs (attrs ++ [(⟨attrMessageIntegrity, mac⟩ : Attr)])).length
      = (encodeAttrs attrs).length + 24 := by
    simp only [encodeAttrs_append, encodeAttrs, encodeAttr_length, attrSize,
      List.append_nil, List.length_append, List.length_nil, padLen, hmaclen]
  have hwfA : ∀ a ∈ attrs ++ [(⟨attrMessageIntegrity, mac⟩ : Attr)],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact hwf a h1
    · simp only [List.mem_singleton] at h2
      subst h2
      exact ⟨by simp [attrMessageIntegrity], by simp [hmaclen]⟩
  rw [henc, parse_encode typ txid _ htyp htx (by rw [hblenA]; exact hblen) hwfA,
    hblenA]

/-- A FINGERPRINT-protected message parses back to the extended attribute
list, with the length field covering the fingerprint attribute. -/
theorem withFingerprint_parses (typ : Nat) (txid : Bytes) (attrs : List Attr)
    (fpv : Bytes)
    (hfp : u32Bytes (crc32 (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 8) ++
      magicCookie ++ txid ++ encodeAttrs attrs) ^^^ fingerprintMask) = fpv)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 8 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536) :
    parse (withFingerprint typ txid attrs) =
      some { typ := typ, length := (encodeAttrs attrs).length + 8, txid := txid,
             attrs := attrs ++ [⟨attrFingerprint, fpv⟩] } := by
  have hfplen : fpv.length = 4 := by rw [← hfp]; exact u32Bytes_length _
  have henc : withFingerprint typ txid attrs =
      encode typ txid (attrs ++ [⟨attrFingerprint, fpv⟩]) := by
    rw [← hfp]
    exact withFingerprint_eq_encode typ txid attrs
  have hblenA : (encodeAttrs (attrs ++ [(⟨attrFingerprint, fpv⟩ : Attr)])).length
      = (encodeAttrs attrs).length + 8 := by
    simp only [encodeAttrs_append, encodeAttrs, encodeAttr_length, attrSize,
      List.append_nil, List.length_append, List.length_nil, padLen, hfplen]
  have hwfA : ∀ a ∈ attrs ++ [(⟨attrFingerprint, fpv⟩ : Attr)],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact hwf a h1
    · simp only [List.mem_singleton] at h2
      subst h2
      exact ⟨by simp [attrFingerprint], by simp [hfplen]⟩
  rw [henc, parse_encode typ txid _ htyp htx (by rw [hblenA]; exact hblen) hwfA,
    hblenA]

/-- **Sign/verify round-trip for MESSAGE-INTEGRITY (§15.4).** Appending a
MESSAGE-INTEGRITY attribute and then verifying it with the same key succeeds —
a statement about the real HMAC-SHA1 computation on both sides. -/
theorem messageIntegrity_roundtrip (key : Bytes) (typ : Nat) (txid : Bytes)
    (attrs : List Attr)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 24 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536)
    (hno : ∀ a ∈ attrs, a.type ≠ attrMessageIntegrity) :
    messageIntegrityOk key (withMessageIntegrity key typ txid attrs) = true := by
  obtain ⟨mac, hmac⟩ : ∃ mac, hmacSha1 key (enc16 typ ++
      enc16 ((encodeAttrs attrs).length + 24) ++ magicCookie ++ txid ++
      encodeAttrs attrs) = mac := ⟨_, rfl⟩
  have hpe := withMessageIntegrity_parses key typ txid attrs mac hmac htyp htx
    hblen hwf
  simp only [messageIntegrityOk, hpe, Option.some_bind]
  rw [offsetOf_append_last attrs ⟨attrMessageIntegrity, mac⟩ attrMessageIntegrity
    rfl hno]
  simp only [Option.some_bind]
  rw [find?_append_last attrs ⟨attrMessageIntegrity, mac⟩ attrMessageIntegrity
    rfl hno]
  simp only [Option.map_some', Option.getD_some]
  -- Reconstruct the §15.4 input: it is exactly the signed prefix.
  have hv2 : withMessageIntegrity key typ txid attrs =
      enc16 typ ++ (enc16 ((encodeAttrs attrs).length + 24) ++ (magicCookie ++
        (txid ++ (encodeAttrs attrs ++ encodeAttr ⟨attrMessageIntegrity,
          hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
            magicCookie ++ txid ++ encodeAttrs attrs)⟩)))) := by
    simp [withMessageIntegrity, List.append_assoc]
  have hv4 : withMessageIntegrity key typ txid attrs =
      (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24)) ++
      ((magicCookie ++ (txid ++ encodeAttrs attrs)) ++
        encodeAttr ⟨attrMessageIntegrity,
          hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
            magicCookie ++ txid ++ encodeAttrs attrs)⟩) := by
    simp [withMessageIntegrity, List.append_assoc]
  have htk2 : (withMessageIntegrity key typ txid attrs).take 2 = enc16 typ := by
    rw [hv2]
    exact List.take_left' rfl
  have hd4 : (withMessageIntegrity key typ txid attrs).drop 4 =
      (magicCookie ++ (txid ++ encodeAttrs attrs)) ++
        encodeAttr ⟨attrMessageIntegrity,
          hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
            magicCookie ++ txid ++ encodeAttrs attrs)⟩ := by
    rw [hv4]
    exact List.drop_left' rfl
  have htkP : ((magicCookie ++ (txid ++ encodeAttrs attrs)) ++
      encodeAttr ⟨attrMessageIntegrity,
        hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
          magicCookie ++ txid ++ encodeAttrs attrs)⟩).take
      (16 + (encodeAttrs attrs).length) = magicCookie ++ (txid ++ encodeAttrs attrs) := by
    apply List.take_left'
    simp only [List.length_append, htx, magicCookie, List.length_cons,
      List.length_nil]
    omega
  rw [htk2, hd4, htkP]
  have hfin : enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
      (magicCookie ++ (txid ++ encodeAttrs attrs)) =
      enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++ magicCookie ++ txid ++
        encodeAttrs attrs := by
    simp [List.append_assoc]
  rw [hfin, hmac]
  simp

/-- **Append/verify round-trip for FINGERPRINT (§15.5).** Appending a
FINGERPRINT attribute and then verifying it succeeds — a statement about the
real CRC-32 computation on both sides. -/
theorem fingerprint_roundtrip (typ : Nat) (txid : Bytes) (attrs : List Attr)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 8 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536)
    (hno : ∀ a ∈ attrs, a.type ≠ attrFingerprint) :
    fingerprintOk (withFingerprint typ txid attrs) = true := by
  obtain ⟨fpv, hfp⟩ : ∃ v, u32Bytes (crc32 (enc16 typ ++
      enc16 ((encodeAttrs attrs).length + 8) ++ magicCookie ++ txid ++
      encodeAttrs attrs) ^^^ fingerprintMask) = v := ⟨_, rfl⟩
  have hpe := withFingerprint_parses typ txid attrs fpv hfp htyp htx hblen hwf
  simp only [fingerprintOk, hpe, Option.some_bind]
  rw [offsetOf_append_last attrs ⟨attrFingerprint, fpv⟩ attrFingerprint rfl hno]
  simp only [Option.some_bind]
  rw [find?_append_last attrs ⟨attrFingerprint, fpv⟩ attrFingerprint rfl hno]
  simp only [Option.map_some', Option.getD_some]
  -- The CRC input recovered by the verifier is exactly the signed prefix.
  have hv : withFingerprint typ txid attrs =
      (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 8) ++ magicCookie ++ txid ++
        encodeAttrs attrs) ++ encodeAttr ⟨attrFingerprint,
          u32Bytes (crc32 (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 8) ++
            magicCookie ++ txid ++ encodeAttrs attrs) ^^^ fingerprintMask)⟩ := rfl
  rw [hv, List.take_left' (by
    simp only [enc16, magicCookie, List.length_append, List.length_cons,
      List.length_nil, htx]), hfp]
  simp

/-! ## XOR-MAPPED-ADDRESS (§15.2) -/

/-- A transport address: family (1 = IPv4, 2 = IPv6), port, and the raw
address bytes in network order (4 or 16 of them). -/
structure Endpoint where
  family : Nat
  port : Nat
  addr : Bytes
deriving Repr, DecidableEq

/-- Pointwise xor of a buffer against a key stream (truncating to the shorter). -/
def xorBytes (a k : Bytes) : Bytes := List.zipWith (· ^^^ ·) a k

theorem u8_xor_cancel (x y : UInt8) : x ^^^ y ^^^ y = x := by
  cases x with | mk xv => cases y with | mk yv =>
  show UInt8.mk ((xv ^^^ yv) ^^^ yv) = UInt8.mk xv
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xorBytes_involutive (a k : Bytes) (h : a.length ≤ k.length) :
    xorBytes (xorBytes a k) k = a := by
  induction a generalizing k with
  | nil => simp [xorBytes]
  | cons x xs ih =>
    match k with
    | [] =>
      simp only [List.length_cons, List.length_nil] at h
      omega
    | y :: ys =>
      simp only [xorBytes, List.zipWith_cons_cons]
      rw [u8_xor_cancel]
      have h' : xs.length ≤ ys.length := by
        simp only [List.length_cons] at h
        omega
      have htail := ih ys h'
      simp only [xorBytes] at htail
      rw [htail]

/-- Serialize the XOR-MAPPED-ADDRESS value (§15.2): a zero byte, the family,
the port xored with the cookie's high 16 bits, and the address xored with the
cookie (IPv4) or cookie ++ transaction id (IPv6). -/
def xorMappedValue (txid : Bytes) (ep : Endpoint) : Bytes :=
  [0, UInt8.ofNat ep.family] ++ enc16 (ep.port ^^^ 0x2112) ++
    xorBytes ep.addr (magicCookie ++ txid)

/-- Decode an XOR-MAPPED-ADDRESS value (§15.2), un-xoring port and address. -/
def decodeXorMapped (txid v : Bytes) : Option Endpoint :=
  match v with
  | _ :: fam :: p1 :: p0 :: xaddr =>
    if (fam = 0x01 ∧ xaddr.length = 4) ∨ (fam = 0x02 ∧ xaddr.length = 16) then
      some { family := fam.toNat, port := be16 p1 p0 ^^^ 0x2112,
             addr := xorBytes xaddr (magicCookie ++ txid) }
    else none
  | _ => none

/-- **XOR-MAPPED-ADDRESS round-trip (§15.2).** Decoding a serialized
XOR-MAPPED-ADDRESS value recovers exactly the original family, port, and
address, for both IPv4 and IPv6. -/
theorem xorMapped_roundtrip (txid : Bytes) (ep : Endpoint)
    (htx : txid.length = 12) (hport : ep.port < 65536)
    (hfam : (ep.family = 1 ∧ ep.addr.length = 4) ∨
            (ep.family = 2 ∧ ep.addr.length = 16)) :
    decodeXorMapped txid (xorMappedValue txid ep) = some ep := by
  have hklen : (magicCookie ++ txid : Bytes).length = 16 := by
    simp [magicCookie, htx]
  have hpow : (2 : Nat) ^ 16 = 65536 := by decide
  have hxlt : ep.port ^^^ 0x2112 < 65536 := by
    rw [← hpow]
    exact Nat.xor_lt_two_pow (by rw [hpow]; exact hport) (by rw [hpow]; omega)
  have hshape : xorMappedValue txid ep =
      (0 : UInt8) :: UInt8.ofNat ep.family ::
      UInt8.ofNat ((ep.port ^^^ 0x2112) / 256) ::
      UInt8.ofNat ((ep.port ^^^ 0x2112) % 256) ::
      xorBytes ep.addr (magicCookie ++ txid) := by
    simp [xorMappedValue, enc16]
  have hinv : xorBytes (xorBytes ep.addr (magicCookie ++ txid)) (magicCookie ++ txid)
      = ep.addr := by
    apply xorBytes_involutive
    rw [hklen]
    rcases hfam with ⟨_, h4⟩ | ⟨_, h16⟩ <;> omega
  rcases hfam with ⟨hf, hlen⟩ | ⟨hf, hlen⟩
  · -- IPv4
    have hzlen : (xorBytes ep.addr (magicCookie ++ txid)).length = 4 := by
      simp only [xorBytes, List.length_zipWith, hklen, hlen]
      omega
    have hfamval : (UInt8.ofNat ep.family).toNat = ep.family := by
      have hm : ep.family % 256 = ep.family := by rw [hf]
      simpa [UInt8.toNat_ofNat] using hm
    rw [hshape]
    simp only [decodeXorMapped]
    rw [if_pos (Or.inl ⟨by rw [hf]; rfl, hzlen⟩)]
    rw [be16_enc16 _ hxlt, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, hinv, hfamval]
  · -- IPv6
    have hzlen : (xorBytes ep.addr (magicCookie ++ txid)).length = 16 := by
      simp only [xorBytes, List.length_zipWith, hklen, hlen]
      omega
    have hfamval : (UInt8.ofNat ep.family).toNat = ep.family := by
      have hm : ep.family % 256 = ep.family := by rw [hf]
      simpa [UInt8.toNat_ofNat] using hm
    rw [hshape]
    simp only [decodeXorMapped]
    rw [if_pos (Or.inr ⟨by rw [hf]; rfl, hzlen⟩)]
    rw [be16_enc16 _ hxlt, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, hinv, hfamval]

/-! ## Unknown attributes and error responses (§7.3.1, §15.6, §15.9) -/

/-- Message types for the Binding method (§6, §18.1). -/
def bindingRequest : Nat := 0x0001
def bindingIndication : Nat := 0x0011
def bindingSuccessType : Nat := 0x0101
def bindingErrorType : Nat := 0x0111

/-- The comprehension-required attribute types this implementation knows
(RFC 5389 §18.2, the ICE connectivity-check attributes of RFC 8445 §16.1, and
the RFC 5780 NAT-discovery Binding-request attributes — CHANGE-REQUEST with
zero flags is what common clients send on a plain Binding test). Types in
0x0000–0x7FFF outside this list must trigger a 420 error (§7.3.1). -/
def knownComprehensionRequired : List Nat :=
  [attrMappedAddress, attrChangeRequest, attrUsername, attrMessageIntegrity,
   attrErrorCode, attrUnknownAttributes, attrRealm, attrNonce,
   attrXorMappedAddress, attrPriority, attrUseCandidate, attrPadding,
   attrResponsePort]

/-- The types of comprehension-required (0x0000–0x7FFF) attributes the
implementation does not understand (§7.3.1). Comprehension-optional types
(0x8000–0xFFFF) are never flagged. -/
def unknownComprehensionRequired (attrs : List Attr) : List Nat :=
  (attrs.filter fun a =>
    decide (a.type < 0x8000) && decide (a.type ∉ knownComprehensionRequired)).map
    (·.type)

/-- **Unknown-attribute classification (§7.3.1).** A type is flagged iff some
attribute carries it, it is in the comprehension-required range, and it is not
a known type. In particular comprehension-optional attributes never trigger
a 420. -/
theorem unknownComprehensionRequired_spec (attrs : List Attr) (t : Nat) :
    t ∈ unknownComprehensionRequired attrs ↔
      t < 0x8000 ∧ t ∉ knownComprehensionRequired ∧ ∃ a ∈ attrs, a.type = t := by
  simp only [unknownComprehensionRequired, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, hlt, hnk⟩, rfl⟩
    exact ⟨hlt, hnk, a, ha, rfl⟩
  · rintro ⟨hlt, hnk, a, ha, rfl⟩
    exact ⟨a, ⟨ha, hlt, hnk⟩, rfl⟩

/-- The ERROR-CODE attribute value (§15.6): 21 zero bits, the class (hundreds
digit), the number (0–99), then the UTF-8 reason phrase. -/
def errorCodeValue (code : Nat) (reason : Bytes) : Bytes :=
  [0, 0, UInt8.ofNat (code / 100), UInt8.ofNat (code % 100)] ++ reason

/-- The UNKNOWN-ATTRIBUTES value (§15.9): the 16-bit unknown types, packed. -/
def unknownAttrsValue (ts : List Nat) : Bytes := ts.flatMap enc16

theorem unknownAttrsValue_length (ts : List Nat) :
    (unknownAttrsValue ts).length = 2 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    simp only [unknownAttrsValue, List.flatMap_cons, List.length_append, enc16,
      List.length_cons, List.length_nil] at *
    omega

/-- ASCII "Unknown Attribute". -/
def unknownAttrReason : Bytes :=
  [0x55, 0x6e, 0x6b, 0x6e, 0x6f, 0x77, 0x6e, 0x20,
   0x41, 0x74, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x65]

/-- Build a Binding error response (§7.3.1.1, §15.6): ERROR-CODE first, and
UNKNOWN-ATTRIBUTES when the error is a 420. -/
def bindingError (txid : Bytes) (code : Nat) (reason : Bytes)
    (unknown : List Nat) : Bytes :=
  encode bindingErrorType txid
    ({ type := attrErrorCode, value := errorCodeValue code reason } ::
     (if unknown.isEmpty then []
      else [{ type := attrUnknownAttributes, value := unknownAttrsValue unknown }]))

/-- Build a Binding success response (§7.3.1.2): XOR-MAPPED-ADDRESS carrying
the request's source transport address, protected by FINGERPRINT. -/
def bindingSuccess (txid : Bytes) (src : Endpoint) : Bytes :=
  withFingerprint bindingSuccessType txid
    [{ type := attrXorMappedAddress, value := xorMappedValue txid src }]

/-- **The Binding server step (§7.3.1).** For a well-formed Binding request:
a 420 error listing the unknown comprehension-required attributes if there are
any, otherwise a success response reflecting the source address. Malformed
datagrams and non-request messages (indications, responses) get silence. -/
def respond (msg : Bytes) (src : Endpoint) : Option Bytes :=
  (parse msg).bind fun m =>
    if m.typ = bindingRequest then
      if unknownComprehensionRequired m.attrs = [] then
        some (bindingSuccess m.txid src)
      else
        some (bindingError m.txid 420 unknownAttrReason
          (unknownComprehensionRequired m.attrs))
    else none

/-- Malformed datagrams are silently discarded (§7.3). -/
theorem respond_malformed (msg : Bytes) (src : Endpoint)
    (h : parse msg = none) : respond msg src = none := by
  simp [respond, h]

/-- Only Binding requests are answered; indications and responses arriving at
the server produce no reply (§7.3.1). -/
theorem respond_only_requests (msg : Bytes) (m : Message) (src : Endpoint)
    (hp : parse msg = some m) (ht : m.typ ≠ bindingRequest) :
    respond msg src = none := by
  simp only [respond, hp, Option.some_bind, if_neg ht]

/-- A request with unknown comprehension-required attributes draws exactly the
420 error response listing them (§7.3.1). -/
theorem respond_unknown_yields_420 (msg : Bytes) (m : Message) (src : Endpoint)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (hu : unknownComprehensionRequired m.attrs ≠ []) :
    respond msg src = some (bindingError m.txid 420 unknownAttrReason
      (unknownComprehensionRequired m.attrs)) := by
  simp only [respond, hp, Option.some_bind, if_pos ht]
  rw [if_neg hu]

/-- The 420 error response is itself a well-formed STUN message: it parses as
a Binding error response that echoes the transaction id (§7.3.1.1). -/
theorem bindingError_parses (txid : Bytes) (code : Nat) (reason : Bytes)
    (unk : List Nat) (htx : txid.length = 12)
    (hr : reason.length < 60000) (hk : unk.length < 1000) :
    ∃ mr, parse (bindingError txid code reason unk) = some mr ∧
      mr.typ = bindingErrorType ∧ mr.txid = txid := by
  have hul := unknownAttrsValue_length unk
  have hecl : (errorCodeValue code reason).length = 4 + reason.length := by
    simp only [errorCodeValue, List.length_append, List.length_cons,
      List.length_nil]
  have hpl := padLen_lt (4 + reason.length)
  have hpu := padLen_lt (2 * unk.length)
  by_cases hemp : unk.isEmpty = true
  · simp only [bindingError, if_pos hemp]
    refine ⟨_, parse_encode bindingErrorType txid _ (by simp [bindingErrorType])
      htx ?_ ?_, rfl, rfl⟩
    · simp only [encodeAttrs, encodeAttr_length, attrSize, List.length_append,
        List.length_nil, hecl]
      omega
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨by simp [attrErrorCode], by simp only [hecl]; omega⟩
  · simp only [bindingError, if_neg hemp]
    refine ⟨_, parse_encode bindingErrorType txid _ (by simp [bindingErrorType])
      htx ?_ ?_, rfl, rfl⟩
    · simp only [encodeAttrs, encodeAttr_length, attrSize, List.length_append,
        List.length_nil, hecl, hul]
      omega
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact ⟨by simp [attrErrorCode], by simp only [hecl]; omega⟩
      · exact ⟨by simp [attrUnknownAttributes], by simp only [hul]; omega⟩

/-- **Binding success correctness (§7.3.1.2, §15.2, §15.5).** For a parsed
Binding request with no unknown comprehension-required attributes, `respond`
produces a reply that (i) parses as a Binding success response, (ii) echoes
the request's transaction id, (iii) carries an XOR-MAPPED-ADDRESS that decodes
back to exactly the request's source endpoint, and (iv) carries a FINGERPRINT
that verifies. -/
theorem respond_success_correct (msg : Bytes) (m : Message) (src : Endpoint)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (hu : unknownComprehensionRequired m.attrs = [])
    (hport : src.port < 65536)
    (hfam : (src.family = 1 ∧ src.addr.length = 4) ∨
            (src.family = 2 ∧ src.addr.length = 16)) :
    ∃ r mr, respond msg src = some r ∧ parse r = some mr ∧
      mr.typ = bindingSuccessType ∧ mr.txid = m.txid ∧
      fingerprintOk r = true ∧
      ∃ a ∈ mr.attrs, a.type = attrXorMappedAddress ∧
        decodeXorMapped m.txid a.value = some src := by
  have htx : m.txid.length = 12 := stun_txid_length msg m hp
  have haddr16 : src.addr.length ≤ 16 := by
    rcases hfam with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hxlen : (xorMappedValue m.txid src).length = 4 + src.addr.length := by
    simp only [xorMappedValue, List.length_append, List.length_cons,
      List.length_nil, enc16, xorBytes, List.length_zipWith, magicCookie, htx]
    omega
  have hwf1 : ∀ a ∈ [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨by simp [attrXorMappedAddress], by simp only [hxlen]; omega⟩
  have hblen1 : (encodeAttrs
      [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)]).length + 8
      < 65536 := by
    have hpx := padLen_lt (4 + src.addr.length)
    simp only [encodeAttrs, encodeAttr_length, attrSize, List.length_append,
      List.length_nil, hxlen]
    omega
  have hno1 : ∀ a ∈ [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)],
      a.type ≠ attrFingerprint := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    simp [attrXorMappedAddress, attrFingerprint]
  obtain ⟨fpv, hfpv⟩ : ∃ v, u32Bytes (crc32 (enc16 bindingSuccessType ++
      enc16 ((encodeAttrs
        [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)]).length + 8) ++
      magicCookie ++ m.txid ++
      encodeAttrs [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)]) ^^^
      fingerprintMask) = v := ⟨_, rfl⟩
  have hpe := withFingerprint_parses bindingSuccessType m.txid
    [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)] fpv hfpv
    (by simp [bindingSuccessType]) htx hblen1 hwf1
  refine ⟨bindingSuccess m.txid src, _, ?_, hpe, rfl, rfl, ?_,
    ⟨attrXorMappedAddress, xorMappedValue m.txid src⟩, ?_, rfl, ?_⟩
  · simp [respond, hp, ht, hu]
  · exact fingerprint_roundtrip bindingSuccessType m.txid
      [(⟨attrXorMappedAddress, xorMappedValue m.txid src⟩ : Attr)]
      (by simp [bindingSuccessType]) htx hblen1 hwf1 hno1
  · simp
  · exact xorMapped_roundtrip m.txid src htx hport hfam

/-! ## The Binding request transaction (§7.2.1) -/

/-- Default initial retransmission timeout, in milliseconds (§7.2.1). -/
def defaultRto : Nat := 500

/-- Rc: the total number of transmissions before giving up (§7.2.1). -/
def txRc : Nat := 7

/-- Rm: the multiplier for the wait after the final transmission (§7.2.1). -/
def txRm : Nat := 16

/-- A Binding request transaction over UDP: how many transmissions have been
made and the current retransmission timeout. -/
structure Tx where
  transmits : Nat
  rto : Nat
deriving Repr, DecidableEq

/-- The state right after the first transmission. -/
def Tx.start : Tx := { transmits := 1, rto := defaultRto }

/-- The timer armed after the latest transmission: the current RTO while
retransmissions remain, and `Rm × RTO` after the final (Rc-th) transmission. -/
def Tx.timer (t : Tx) : Nat :=
  if t.transmits < txRc then t.rto else txRm * defaultRto

/-- On timer expiry: retransmit with doubled RTO, or fail once Rc
transmissions have been made (§7.2.1). -/
def Tx.onTimeout (t : Tx) : Option Tx :=
  if t.transmits < txRc then
    some { transmits := t.transmits + 1, rto := t.rto * 2 }
  else none

/-- The sequence of timer values a transaction runs through, from a given
state until failure (fuel-bounded; `txRc` is always enough fuel from start). -/
def Tx.timeline (fuel : Nat) (t : Tx) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    t.timer :: match t.onTimeout with
      | some t' => Tx.timeline fuel t'
      | none => []

/-- **The §7.2.1 retransmission schedule, exactly.** From the initial state the
timers are 500, 1000, 2000, 4000, 8000, 16000 ms between transmissions, then
Rm × RTO = 8000 ms after the seventh — i.e. transmissions at 0, 500, 1500,
3500, 7500, 15500, 31500 ms and failure at 39500 ms, the example sequence the
RFC prescribes. -/
theorem tx_schedule :
    Tx.timeline 8 Tx.start = [500, 1000, 2000, 4000, 8000, 16000, 8000] := by
  decide

/-- The transaction makes exactly Rc = 7 transmissions before giving up. -/
theorem tx_transmission_count : (Tx.timeline 8 Tx.start).length = txRc := by
  decide

/-- Total time from first transmission to failure: 39500 ms (§7.2.1 example). -/
theorem tx_gives_up_at : (Tx.timeline 8 Tx.start).sum = 39500 := by
  decide

/-- After the Rc-th transmission the transaction never retransmits again. -/
theorem tx_gives_up (t : Tx) (h : txRc ≤ t.transmits) : t.onTimeout = none := by
  simp [Tx.onTimeout]
  omega

/-- The transmission count never exceeds Rc along any timeout path. -/
theorem tx_transmit_bound (t t' : Tx) (h : t.onTimeout = some t') :
    t'.transmits ≤ txRc := by
  simp only [Tx.onTimeout] at h
  by_cases hc : t.transmits < txRc
  · rw [if_pos hc] at h
    cases h
    show t.transmits + 1 ≤ txRc
    omega
  · rw [if_neg hc] at h
    cases h

/-- Each retransmission doubles the timeout (exponential backoff, §7.2.1). -/
theorem tx_backoff_doubles (t t' : Tx) (h : t.onTimeout = some t') :
    t'.rto = 2 * t.rto := by
  simp only [Tx.onTimeout] at h
  by_cases hc : t.transmits < txRc
  · rw [if_pos hc] at h
    cases h
    show t.rto * 2 = 2 * t.rto
    omega
  · rw [if_neg hc] at h
    cases h

/-! ## MD5 (RFC 1321) — the long-term-credential key digest (RFC 5389 §15.4)

RFC 5389 §15.4 defines the long-term-credential HMAC key as
`MD5(username ":" realm ":" SASLprep(password))`. MD5 is implemented directly
(like SHA-1 above) so the derivation is computable inside the core; it is a
key-derivation step here, not a collision-resistance assumption. -/

/-- Little-endian 32-bit word at byte offset `i`. -/
def word32LeAt (b : Bytes) (i : Nat) : UInt32 :=
  (byteAt b i).toUInt32 ||| (byteAt b (i + 1)).toUInt32 <<< 8 |||
  (byteAt b (i + 2)).toUInt32 <<< 16 ||| (byteAt b (i + 3)).toUInt32 <<< 24

/-- Little-endian bytes of a 32-bit word. -/
def u32LeBytes (x : UInt32) : Bytes :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

@[simp] theorem u32LeBytes_length (x : UInt32) : (u32LeBytes x).length = 4 := rfl

/-- Little-endian bytes of a 64-bit value (the MD5 length trailer). -/
def u64LeBytes (n : Nat) : Bytes :=
  (List.range 8).map fun i => UInt8.ofNat (n >>> (i * 8))

/-- RFC 1321 §3.4 sine-derived round constants. -/
def md5K : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
  0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
  0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
  0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
  0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
  0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
  0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
  0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
  0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/-- RFC 1321 §3.4 per-round left-rotation amounts. -/
def md5S : Array Nat := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- The four-word MD5 chaining state (RFC 1321 §3.3). -/
structure Md5State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32

/-- RFC 1321 §3.3 initial state. -/
def md5Init : Md5State := ⟨0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476⟩

/-- One RFC 1321 §3.4 round: the auxiliary function and message-word index
depend on the round quarter. -/
def md5Round (chunk : Bytes) (st : UInt32 × UInt32 × UInt32 × UInt32) (i : Nat) :
    UInt32 × UInt32 × UInt32 × UInt32 :=
  let (a, b, c, d) := st
  let f : UInt32 :=
    if i < 16 then (b &&& c) ||| ((~~~b) &&& d)
    else if i < 32 then (d &&& b) ||| ((~~~d) &&& c)
    else if i < 48 then b ^^^ c ^^^ d
    else c ^^^ (b ||| (~~~d))
  let g : Nat :=
    if i < 16 then i
    else if i < 32 then (5 * i + 1) % 16
    else if i < 48 then (3 * i + 5) % 16
    else (7 * i) % 16
  (d, b + rotl (md5S[i]!) (a + f + md5K[i]! + word32LeAt chunk (4 * g)), b, c)

/-- Compress one 64-byte chunk into the chaining state. -/
def md5Chunk (st : Md5State) (chunk : Bytes) : Md5State :=
  let (a, b, c, d) := (List.range 64).foldl (md5Round chunk) (st.a, st.b, st.c, st.d)
  ⟨st.a + a, st.b + b, st.c + c, st.d + d⟩

/-- RFC 1321 §3.1/§3.2 padding: a 0x80 byte, zeros to 56 mod 64, then the
little-endian 64-bit bit length. -/
def md5Pad (msg : Bytes) : Bytes :=
  msg ++ [0x80] ++ zeros ((119 - msg.length % 64) % 64) ++ u64LeBytes (msg.length * 8)

/-- MD5 (RFC 1321): 16-byte digest. -/
def md5 (msg : Bytes) : Bytes :=
  let padded := md5Pad msg
  let st := (List.range (padded.length / 64)).foldl
    (fun st i => md5Chunk st ((padded.drop (64 * i)).take 64)) md5Init
  u32LeBytes st.a ++ u32LeBytes st.b ++ u32LeBytes st.c ++ u32LeBytes st.d

theorem md5_length (msg : Bytes) : (md5 msg).length = 16 := by
  simp [md5]

/-- **Long-term credential key (RFC 5389 §15.4).** The HMAC key for the
long-term mechanism: `MD5(username ":" realm ":" password)`, with the password
already SASLprep-processed. -/
def longTermKey (username realm password : Bytes) : Bytes :=
  md5 (username ++ [0x3a] ++ realm ++ [0x3a] ++ password)

theorem longTermKey_length (username realm password : Bytes) :
    (longTermKey username realm password).length = 16 := md5_length _

/-! ## MESSAGE-INTEGRITY and FINGERPRINT together (§15.4, §15.5)

An authenticated success response — the shape RFC 8445 §7.3 requires for ICE
connectivity-check answers — carries XOR-MAPPED-ADDRESS, MESSAGE-INTEGRITY,
then FINGERPRINT. Each integrity attribute is computed with the header length
field adjusted per its own rule: the HMAC sees the length covering up to the
end of MESSAGE-INTEGRITY (but not FINGERPRINT), the CRC sees the final length. -/

/-- Serialize a message and append MESSAGE-INTEGRITY then FINGERPRINT (§15.4,
§15.5). The HMAC input is the message with the length field pointing past the
MESSAGE-INTEGRITY attribute; the CRC input is the message with the final
length, up to the FINGERPRINT attribute. -/
def withIntegrityFingerprint (key : Bytes) (typ : Nat) (txid : Bytes)
    (attrs : List Attr) : Bytes :=
  let body := encodeAttrs attrs
  let mac := hmacSha1 key
    (enc16 typ ++ enc16 (body.length + 24) ++ magicCookie ++ txid ++ body)
  let body2 := body ++ encodeAttr { type := attrMessageIntegrity, value := mac }
  let pre2 := enc16 typ ++ enc16 (body.length + 32) ++ magicCookie ++ txid ++ body2
  pre2 ++ encodeAttr { type := attrFingerprint,
                       value := u32Bytes (crc32 pre2 ^^^ fingerprintMask) }

/-- The HMAC value `withIntegrityFingerprint` carries (§15.4 input). -/
def wifMac (key : Bytes) (typ : Nat) (txid : Bytes) (attrs : List Attr) : Bytes :=
  hmacSha1 key (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
    magicCookie ++ txid ++ encodeAttrs attrs)

/-- The CRC value `withIntegrityFingerprint` carries (§15.5 input). -/
def wifFp (key : Bytes) (typ : Nat) (txid : Bytes) (attrs : List Attr) : Bytes :=
  u32Bytes (crc32 (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 32) ++
    magicCookie ++ txid ++
    (encodeAttrs attrs ++
      encodeAttr ⟨attrMessageIntegrity, wifMac key typ txid attrs⟩)) ^^^
    fingerprintMask)

/-- `find?` locates an attribute appended after a prefix free of its type,
regardless of what follows it. -/
theorem find?_append_mid (attrs : List Attr) (a : Attr) (tail : List Attr) (t : Nat)
    (hat : a.type = t) (h : ∀ x ∈ attrs, x.type ≠ t) :
    (attrs ++ a :: tail).find? (fun x => x.type == t) = some a := by
  induction attrs with
  | nil =>
    rw [List.nil_append]
    exact List.find?_cons_of_pos _ (by simp [hat])
  | cons x rest ih =>
    rw [List.cons_append, List.find?_cons_of_neg _ (by
      simp only [beq_iff_eq]
      exact h x (List.mem_cons_self x rest))]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

/-- `offsetOf` of an attribute appended after a prefix free of its type is the
serialized prefix length, regardless of what follows it. -/
theorem offsetOf_append_mid (attrs : List Attr) (a : Attr) (tail : List Attr) (t : Nat)
    (hat : a.type = t) (h : ∀ x ∈ attrs, x.type ≠ t) :
    offsetOf t (attrs ++ a :: tail) = some (encodeAttrs attrs).length := by
  induction attrs with
  | nil => simp [offsetOf, hat, encodeAttrs]
  | cons x rest ih =>
    have hx : x.type ≠ t := h x (List.mem_cons_self x rest)
    have := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.cons_append, offsetOf, if_neg hx, this, Option.map_some']
    simp [encodeAttrs, encodeAttr_length]

/-- Appending two serialized attributes, seen at the `encode` level. -/
theorem encode_snoc2 (typ : Nat) (txid : Bytes) (attrs : List Attr) (a b : Attr) :
    encode typ txid (attrs ++ [a, b]) =
      (enc16 typ ++
        enc16 ((encodeAttrs attrs).length + attrSize a + attrSize b) ++
        magicCookie ++ txid ++ (encodeAttrs attrs ++ encodeAttr a)) ++
      encodeAttr b := by
  simp [encode, encodeAttrs_append, encodeAttrs, encodeAttr_length,
    List.append_assoc, Nat.add_assoc]

/-- The `withIntegrityFingerprint` output, seen as a plain `encode` of the
extended attribute list. -/
theorem withIntegrityFingerprint_eq_encode (key : Bytes) (typ : Nat)
    (txid : Bytes) (attrs : List Attr) :
    withIntegrityFingerprint key typ txid attrs =
      encode typ txid (attrs ++
        [⟨attrMessageIntegrity, wifMac key typ txid attrs⟩,
         ⟨attrFingerprint, wifFp key typ txid attrs⟩]) := by
  rw [encode_snoc2]
  have hszMi : attrSize (⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr)
      = 24 := by
    simp [attrSize, wifMac, hmacSha1_length, padLen]
  have hszFp : attrSize (⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr)
      = 8 := by
    simp [attrSize, wifFp, padLen]
  rw [hszMi, hszFp]
  simp only [withIntegrityFingerprint, wifFp, wifMac]
  try simp [List.append_assoc]

/-- An integrity-and-fingerprint-protected message parses back to the extended
attribute list, with the length field covering both attributes. -/
theorem withIntegrityFingerprint_parses (key : Bytes) (typ : Nat) (txid : Bytes)
    (attrs : List Attr)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 32 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536) :
    parse (withIntegrityFingerprint key typ txid attrs) =
      some { typ := typ, length := (encodeAttrs attrs).length + 32, txid := txid,
             attrs := attrs ++
               [⟨attrMessageIntegrity, wifMac key typ txid attrs⟩,
                ⟨attrFingerprint, wifFp key typ txid attrs⟩] } := by
  have hmaclen : (wifMac key typ txid attrs).length = 20 := hmacSha1_length _ _
  have hfplen : (wifFp key typ txid attrs).length = 4 := u32Bytes_length _
  have hblenA : (encodeAttrs (attrs ++
      [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr),
       (⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr)])).length
      = (encodeAttrs attrs).length + 32 := by
    simp only [encodeAttrs_append, encodeAttrs, encodeAttr_length, attrSize,
      List.append_nil, List.length_append, List.length_nil, padLen, hmaclen,
      hfplen]
  have hwfA : ∀ a ∈ attrs ++
      [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr),
       (⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr)],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact hwf a h1
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact ⟨by simp [attrMessageIntegrity], by simp [hmaclen]⟩
      · rcases List.mem_singleton.mp h3 with rfl
        exact ⟨by simp [attrFingerprint], by simp [hfplen]⟩
  rw [withIntegrityFingerprint_eq_encode,
    parse_encode typ txid _ htyp htx (by rw [hblenA]; exact hblen) hwfA, hblenA]

/-- **Authenticated-response round-trip (§15.4 with §15.5 present).** A message
protected by `withIntegrityFingerprint` passes MESSAGE-INTEGRITY verification
under the same key: the verifier recomputes the HMAC over the §15.4 input —
with the length field rewritten to exclude the trailing FINGERPRINT — and it
matches. This is the property RFC 8445 §7.3 needs from connectivity-check
responses. -/
theorem withIntegrityFingerprint_integrity_ok (key : Bytes) (typ : Nat)
    (txid : Bytes) (attrs : List Attr)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 32 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536)
    (hnoMI : ∀ a ∈ attrs, a.type ≠ attrMessageIntegrity) :
    messageIntegrityOk key (withIntegrityFingerprint key typ txid attrs) = true := by
  have hpe := withIntegrityFingerprint_parses key typ txid attrs htyp htx hblen hwf
  simp only [messageIntegrityOk, hpe, Option.some_bind]
  rw [show (attrs ++ [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr),
        (⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr)]) =
      attrs ++ (⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr) ::
        [(⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr)] from rfl]
  rw [offsetOf_append_mid attrs _ _ attrMessageIntegrity rfl hnoMI]
  simp only [Option.some_bind]
  rw [find?_append_mid attrs _ _ attrMessageIntegrity rfl hnoMI]
  simp only [Option.map_some', Option.getD_some]
  -- Reconstruct the §15.4 input: it is exactly the HMAC'd prefix.
  have hv2 : withIntegrityFingerprint key typ txid attrs =
      enc16 typ ++ (enc16 ((encodeAttrs attrs).length + 32) ++ (magicCookie ++
        (txid ++ ((encodeAttrs attrs ++
          encodeAttr ⟨attrMessageIntegrity, wifMac key typ txid attrs⟩) ++
          encodeAttr ⟨attrFingerprint, wifFp key typ txid attrs⟩)))) := by
    simp only [withIntegrityFingerprint, wifFp, wifMac]
    simp [List.append_assoc]
  have hv4 : withIntegrityFingerprint key typ txid attrs =
      (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 32)) ++
      ((magicCookie ++ (txid ++ encodeAttrs attrs)) ++
        (encodeAttr ⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ ++
         encodeAttr ⟨attrFingerprint, wifFp key typ txid attrs⟩)) := by
    simp only [withIntegrityFingerprint, wifFp, wifMac]
    simp [List.append_assoc]
  have htk2 : (withIntegrityFingerprint key typ txid attrs).take 2 = enc16 typ := by
    rw [hv2]
    exact List.take_left' rfl
  have hd4 : (withIntegrityFingerprint key typ txid attrs).drop 4 =
      (magicCookie ++ (txid ++ encodeAttrs attrs)) ++
        (encodeAttr ⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ ++
         encodeAttr ⟨attrFingerprint, wifFp key typ txid attrs⟩) := by
    rw [hv4]
    exact List.drop_left' rfl
  have htkP : ((magicCookie ++ (txid ++ encodeAttrs attrs)) ++
      (encodeAttr ⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ ++
       encodeAttr ⟨attrFingerprint, wifFp key typ txid attrs⟩)).take
      (16 + (encodeAttrs attrs).length) = magicCookie ++ (txid ++ encodeAttrs attrs) := by
    apply List.take_left'
    simp only [List.length_append, htx, magicCookie, List.length_cons,
      List.length_nil]
    omega
  rw [htk2, hd4, htkP]
  have hfin : enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++
      (magicCookie ++ (txid ++ encodeAttrs attrs)) =
      enc16 typ ++ enc16 ((encodeAttrs attrs).length + 24) ++ magicCookie ++ txid ++
        encodeAttrs attrs := by
    simp [List.append_assoc]
  rw [hfin]
  simp [wifMac]

/-- **FINGERPRINT still verifies when MESSAGE-INTEGRITY is present (§15.5).**
The CRC covers the whole message up to the FINGERPRINT attribute, including
MESSAGE-INTEGRITY. -/
theorem withIntegrityFingerprint_fingerprint_ok (key : Bytes) (typ : Nat)
    (txid : Bytes) (attrs : List Attr)
    (htyp : typ < 65536) (htx : txid.length = 12)
    (hblen : (encodeAttrs attrs).length + 32 < 65536)
    (hwf : ∀ a ∈ attrs, a.type < 65536 ∧ a.value.length < 65536)
    (hnoFP : ∀ a ∈ attrs, a.type ≠ attrFingerprint) :
    fingerprintOk (withIntegrityFingerprint key typ txid attrs) = true := by
  have hpe := withIntegrityFingerprint_parses key typ txid attrs htyp htx hblen hwf
  simp only [fingerprintOk, hpe, Option.some_bind]
  have hsplit : (attrs ++ [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr),
        (⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr)]) =
      (attrs ++ [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr)]) ++
        (⟨attrFingerprint, wifFp key typ txid attrs⟩ : Attr) :: [] := by
    simp [List.append_assoc]
  have hnoFP' : ∀ x ∈ attrs ++
      [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr)],
      x.type ≠ attrFingerprint := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact hnoFP x h1
    · rcases List.mem_singleton.mp h2 with rfl
      simp [attrMessageIntegrity, attrFingerprint]
  rw [hsplit, offsetOf_append_mid _ _ _ attrFingerprint rfl hnoFP',
    find?_append_mid _ _ _ attrFingerprint rfl hnoFP']
  simp only [Option.some_bind, Option.map_some', Option.getD_some]
  have hlenMi : (encodeAttrs (attrs ++
      [(⟨attrMessageIntegrity, wifMac key typ txid attrs⟩ : Attr)])).length =
      (encodeAttrs attrs).length + 24 := by
    simp only [encodeAttrs_append, encodeAttrs, encodeAttr_length, attrSize,
      List.append_nil, List.length_append, List.length_nil, padLen,
      hmacSha1_length, wifMac]
  rw [hlenMi]
  -- The CRC input recovered by the verifier is exactly the CRC'd prefix.
  have hv : withIntegrityFingerprint key typ txid attrs =
      (enc16 typ ++ enc16 ((encodeAttrs attrs).length + 32) ++ magicCookie ++
        txid ++ (encodeAttrs attrs ++
          encodeAttr ⟨attrMessageIntegrity, wifMac key typ txid attrs⟩)) ++
      encodeAttr ⟨attrFingerprint, wifFp key typ txid attrs⟩ := by
    simp only [withIntegrityFingerprint, wifFp, wifMac]
  rw [hv, List.take_left' (by
    simp only [enc16, magicCookie, List.length_append, List.length_cons,
      List.length_nil, htx, encodeAttr_length, attrSize, padLen,
      hmacSha1_length, wifMac]
    try omega)]
  simp [wifFp]

/-! ## Short-term credentials and the authenticated server (§10.1)

RFC 5389 §10.1.2 receipt rules for a server requiring short-term credentials,
which is exactly the ICE connectivity-check server role (RFC 8445 §7.3):
missing USERNAME or MESSAGE-INTEGRITY draws 400, an unknown username or a
failing HMAC draws 401, and success responses are themselves protected by
MESSAGE-INTEGRITY under the same key. -/

/-- A short-term credential (§10.1): the USERNAME value a request must carry
and the HMAC-SHA1 key. For ICE the username is `local-ufrag ":" remote-ufrag`
from the checker's perspective and the key is the checked side's password
(RFC 8445 §7.2.2). -/
structure ShortTermAuth where
  username : Bytes
  key : Bytes
deriving Repr, DecidableEq

/-- First attribute of a given type. -/
def findAttr (t : Nat) (attrs : List Attr) : Option Attr :=
  attrs.find? (·.type == t)

/-- ASCII "Bad Request" (§15.6, code 400). -/
def badRequestReason : Bytes :=
  [0x42, 0x61, 0x64, 0x20, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74]

/-- ASCII "Unauthorized" (§15.6, code 401). -/
def unauthorizedReason : Bytes :=
  [0x55, 0x6e, 0x61, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x7a, 0x65, 0x64]

/-- The outcome of the §10.1.2 credential check. -/
inductive AuthResult
  | ok (signKey : Option Bytes)
  | failed (code : Nat) (reason : Bytes)
deriving Repr, DecidableEq

/-- **§10.1.2 receipt rules.** With no credential configured the request is
admitted unauthenticated. With one configured: a request missing
MESSAGE-INTEGRITY or USERNAME draws 400; a wrong username or a failing HMAC
draws 401; otherwise the request is admitted and the response must be signed
with the same key. -/
def authCheck (auth : Option ShortTermAuth) (msg : Bytes) (m : Message) :
    AuthResult :=
  match auth with
  | none => .ok none
  | some a =>
    match findAttr attrMessageIntegrity m.attrs with
    | none => .failed 400 badRequestReason
    | some _ =>
      match findAttr attrUsername m.attrs with
      | none => .failed 400 badRequestReason
      | some u =>
        if u.value = a.username then
          if messageIntegrityOk a.key msg then .ok (some a.key)
          else .failed 401 unauthorizedReason
        else .failed 401 unauthorizedReason

/-! ## NAT-behavior discovery attributes (RFC 5780) -/

/-- RESPONSE-ORIGIN (RFC 5780 §7.3): the transport address the response was
sent from. -/
def attrResponseOrigin : Nat := 0x802b

/-- OTHER-ADDRESS (RFC 5780 §7.4): the server's alternate transport address. -/
def attrOtherAddress : Nat := 0x802c

/-- The MAPPED-ADDRESS wire value (§15.1, also used by RESPONSE-ORIGIN and
OTHER-ADDRESS): a zero byte, the family, the port, the address — un-xored. -/
def mappedValue (ep : Endpoint) : Bytes :=
  [0, UInt8.ofNat ep.family] ++ enc16 ep.port ++ ep.addr

/-- Decode the CHANGE-REQUEST value (RFC 5780 §7.2): a 32-bit word whose
0x04 bit asks for the alternate IP and whose 0x02 bit asks for the alternate
port. `none` for a malformed length. -/
def changeRequestFlags : Bytes → Option (Bool × Bool)
  | [_, _, _, b0] => some (b0 &&& 4 == 4, b0 &&& 2 == 2)
  | _ => none

/-- Which of the server's sockets a datagram is on: `(alternate IP?,
alternate port?)`. `(false, false)` is the primary socket. -/
abbrev SockId := Bool × Bool

/-- Server configuration: an optional short-term credential (§10.1), and the
RFC 5780 primary/alternate transport addresses when NAT-behavior discovery is
deployed (the alternate needs its own sockets). -/
structure Config where
  auth : Option ShortTermAuth := none
  primary : Option Endpoint := none
  alternate : Option Endpoint := none

/-- Bounded transport addresses (what the wire format can carry). -/
def Endpoint.Wf (ep : Endpoint) : Prop :=
  ep.family < 256 ∧ ep.port < 65536 ∧ ep.addr.length ≤ 16

/-- Configured addresses are bounded. -/
def Config.Wf (cfg : Config) : Prop :=
  (∀ p, cfg.primary = some p → p.Wf) ∧ (∀ a, cfg.alternate = some a → a.Wf)

/-- The transport address of a given server socket, from the configured
primary/alternate pair: the alternate contributes its IP and/or its port. -/
def originEndpoint (cfg : Config) : SockId → Option Endpoint
  | (false, false) => cfg.primary
  | (false, true) =>
    match cfg.primary, cfg.alternate with
    | some p, some a => some { p with port := a.port }
    | _, _ => none
  | (true, false) =>
    match cfg.primary, cfg.alternate with
    | some p, some a => some { a with port := p.port }
    | _, _ => none
  | (true, true) => cfg.alternate

/-- The socket a response leaves from (RFC 5780 §7.2): the CHANGE-REQUEST
flags toggle IP and port relative to the socket the request arrived on.
Without a configured alternate the flags are ignored (the RFC 5780 service is
simply not deployed; plain §7.3.1 behavior applies). -/
def sendSock (cfg : Config) (recv : SockId) (flags : Bool × Bool) : SockId :=
  if cfg.alternate.isSome then (recv.1 ^^ flags.1, recv.2 ^^ flags.2) else recv

/-- An optional address attribute (absent endpoint contributes nothing). -/
def addrAttr (t : Nat) : Option Endpoint → List Attr
  | some o => [⟨t, mappedValue o⟩]
  | none => []

theorem addrAttr_mem (t : Nat) (o : Option Endpoint) (x : Attr)
    (hx : x ∈ addrAttr t o) : ∃ ep, o = some ep ∧ x = ⟨t, mappedValue ep⟩ := by
  match o with
  | none => simp [addrAttr] at hx
  | some ep =>
    rcases List.mem_singleton.mp hx with rfl
    exact ⟨ep, rfl, rfl⟩

theorem addrAttr_length (t : Nat) (o : Option Endpoint) :
    (addrAttr t o).length ≤ 1 := by
  cases o <;> simp [addrAttr]

/-- The success-response attribute list: MAPPED-ADDRESS and XOR-MAPPED-ADDRESS
reflecting the request's source (§7.3.1.2, §15.1, §15.2), RESPONSE-ORIGIN for
the sending socket, and OTHER-ADDRESS when an alternate is deployed
(RFC 5780 §7.3, §7.4). -/
def successAttrs (cfg : Config) (send : SockId) (txid : Bytes)
    (src : Endpoint) : List Attr :=
  [⟨attrMappedAddress, mappedValue src⟩,
   ⟨attrXorMappedAddress, xorMappedValue txid src⟩] ++
  addrAttr attrResponseOrigin (originEndpoint cfg send) ++
  addrAttr attrOtherAddress cfg.alternate

/-- **The authenticated Binding server step (§7.3.1, §10.1.2, RFC 5780 §7.2).**
Extends `respond` with the credential receipt rules, the RFC 5780 discovery
attributes, and CHANGE-REQUEST handling. Returns the socket to send from and
the response bytes; `none` is silence. Error responses leave from the
receiving socket. A CHANGE-REQUEST with a malformed value draws 400. When a
credential admitted the request, the success response carries
MESSAGE-INTEGRITY under the same key (§10.1.2), then FINGERPRINT. -/
def serve (cfg : Config) (recv : SockId) (msg : Bytes) (src : Endpoint) :
    Option (SockId × Bytes) :=
  (parse msg).bind fun m =>
    if m.typ = bindingRequest then
      match authCheck cfg.auth msg m with
      | .failed code reason => some (recv, bindingError m.txid code reason [])
      | .ok signKey =>
        if unknownComprehensionRequired m.attrs = [] then
          match findAttr attrChangeRequest m.attrs with
          | some cr =>
            match changeRequestFlags cr.value with
            | none => some (recv, bindingError m.txid 400 badRequestReason [])
            | some flags =>
              some (sendSock cfg recv flags,
                mkSuccess signKey m.txid
                  (successAttrs cfg (sendSock cfg recv flags) m.txid src))
          | none =>
            some (sendSock cfg recv (false, false),
              mkSuccess signKey m.txid
                (successAttrs cfg (sendSock cfg recv (false, false)) m.txid src))
        else
          some (recv, bindingError m.txid 420 unknownAttrReason
            (unknownComprehensionRequired m.attrs))
    else none
where
  /-- Success response: FINGERPRINT-protected, and MESSAGE-INTEGRITY-protected
  first when a credential admitted the request (§10.1.2). -/
  mkSuccess (signKey : Option Bytes) (txid : Bytes) (attrs : List Attr) : Bytes :=
    match signKey with
    | some key => withIntegrityFingerprint key bindingSuccessType txid attrs
    | none => withFingerprint bindingSuccessType txid attrs

/-! ### Theorems on the authenticated server step -/

/-- Malformed datagrams are silently discarded (§7.3). -/
theorem serve_malformed (cfg : Config) (recv : SockId) (msg : Bytes)
    (src : Endpoint) (h : parse msg = none) : serve cfg recv msg src = none := by
  simp [serve, h]

/-- Only Binding requests are answered (§7.3.1). -/
theorem serve_only_requests (cfg : Config) (recv : SockId) (msg : Bytes)
    (m : Message) (src : Endpoint)
    (hp : parse msg = some m) (ht : m.typ ≠ bindingRequest) :
    serve cfg recv msg src = none := by
  simp only [serve, hp, Option.some_bind, if_neg ht]

/-- **Missing credentials draw 400 (§10.1.2).** At a server requiring a
short-term credential, a Binding request without MESSAGE-INTEGRITY is answered
by a 400 error response from the receiving socket, never a success. -/
theorem serve_missing_integrity_400 (cfg : Config) (a : ShortTermAuth)
    (recv : SockId) (msg : Bytes) (m : Message) (src : Endpoint)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (ha : cfg.auth = some a)
    (hmi : findAttr attrMessageIntegrity m.attrs = none) :
    serve cfg recv msg src =
      some (recv, bindingError m.txid 400 badRequestReason []) := by
  have hac : authCheck cfg.auth msg m = .failed 400 badRequestReason := by
    simp [authCheck, ha, hmi]
  simp only [serve, hp, Option.some_bind, if_pos ht, hac]

/-- **A failing HMAC draws 401 (§10.1.2).** With the right username but a
MESSAGE-INTEGRITY that does not verify under the configured key, the request
is refused with 401 — the property that keeps an off-path attacker from
soliciting authenticated answers. -/
theorem serve_bad_integrity_401 (cfg : Config) (a : ShortTermAuth)
    (recv : SockId) (msg : Bytes) (m : Message) (src : Endpoint) (x u : Attr)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (ha : cfg.auth = some a)
    (hmi : findAttr attrMessageIntegrity m.attrs = some x)
    (hu : findAttr attrUsername m.attrs = some u)
    (huv : u.value = a.username)
    (hbad : messageIntegrityOk a.key msg = false) :
    serve cfg recv msg src =
      some (recv, bindingError m.txid 401 unauthorizedReason []) := by
  have hac : authCheck cfg.auth msg m = .failed 401 unauthorizedReason := by
    simp [authCheck, ha, hmi, hu, huv, hbad]
  simp only [serve, hp, Option.some_bind, if_pos ht, hac]

/-- **A wrong username draws 401 (§10.1.2).** -/
theorem serve_bad_username_401 (cfg : Config) (a : ShortTermAuth)
    (recv : SockId) (msg : Bytes) (m : Message) (src : Endpoint) (x u : Attr)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (ha : cfg.auth = some a)
    (hmi : findAttr attrMessageIntegrity m.attrs = some x)
    (hu : findAttr attrUsername m.attrs = some u)
    (huv : u.value ≠ a.username) :
    serve cfg recv msg src =
      some (recv, bindingError m.txid 401 unauthorizedReason []) := by
  have hac : authCheck cfg.auth msg m = .failed 401 unauthorizedReason := by
    simp [authCheck, ha, hmi, hu, huv]
  simp only [serve, hp, Option.some_bind, if_pos ht, hac]

/-- Error responses carry the ERROR-CODE attribute for their code and echo the
transaction id (§7.3.1.1, §15.6). -/
theorem bindingError_carries_code (txid : Bytes) (code : Nat) (reason : Bytes)
    (unk : List Nat) (htx : txid.length = 12)
    (hr : reason.length < 60000) (hk : unk.length < 1000) :
    ∃ mr, parse (bindingError txid code reason unk) = some mr ∧
      mr.typ = bindingErrorType ∧ mr.txid = txid ∧
      (⟨attrErrorCode, errorCodeValue code reason⟩ : Attr) ∈ mr.attrs := by
  have hul := unknownAttrsValue_length unk
  have hecl : (errorCodeValue code reason).length = 4 + reason.length := by
    simp only [errorCodeValue, List.length_append, List.length_cons,
      List.length_nil]
  have hpl := padLen_lt (4 + reason.length)
  have hpu := padLen_lt (2 * unk.length)
  by_cases hemp : unk.isEmpty = true
  · simp only [bindingError, if_pos hemp]
    refine ⟨_, parse_encode bindingErrorType txid _ (by simp [bindingErrorType])
      htx ?_ ?_, rfl, rfl, List.mem_cons_self _ _⟩
    · simp only [encodeAttrs, encodeAttr_length, attrSize, List.length_append,
        List.length_nil, hecl]
      omega
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨by simp [attrErrorCode], by simp only [hecl]; omega⟩
  · simp only [bindingError, if_neg hemp]
    refine ⟨_, parse_encode bindingErrorType txid _ (by simp [bindingErrorType])
      htx ?_ ?_, rfl, rfl, List.mem_cons_self _ _⟩
    · simp only [encodeAttrs, encodeAttr_length, attrSize, List.length_append,
        List.length_nil, hecl, hul]
      omega
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact ⟨by simp [attrErrorCode], by simp only [hecl]; omega⟩
      · exact ⟨by simp [attrUnknownAttributes], by simp only [hul]; omega⟩

/-- Hygiene of the success-response attribute list: bounded wire fields, and
free of MESSAGE-INTEGRITY and FINGERPRINT types (so the integrity attributes
appended after it are located correctly by any verifier). -/
theorem successAttrs_hygiene (cfg : Config) (send : SockId) (txid : Bytes)
    (src : Endpoint) (htx : txid.length = 12) (hsrc : src.addr.length ≤ 16)
    (hcfg : cfg.Wf) :
    (∀ x ∈ successAttrs cfg send txid src,
        x.type < 65536 ∧ x.value.length < 65536) ∧
    (∀ x ∈ successAttrs cfg send txid src, x.type ≠ attrMessageIntegrity) ∧
    (∀ x ∈ successAttrs cfg send txid src, x.type ≠ attrFingerprint) ∧
    (encodeAttrs (successAttrs cfg send txid src)).length + 32 < 65536 := by
  have hmv : ∀ ep : Endpoint, ep.addr.length ≤ 16 →
      (mappedValue ep).length ≤ 20 := by
    intro ep h
    simp only [mappedValue, List.length_append, List.length_cons,
      List.length_nil, enc16]
    omega
  have hxv : (xorMappedValue txid src).length ≤ 20 := by
    simp only [xorMappedValue, List.length_append, List.length_cons,
      List.length_nil, enc16, xorBytes, List.length_zipWith]
    omega
  have horig : ∀ o, originEndpoint cfg send = some o → o.addr.length ≤ 16 := by
    intro o ho
    obtain ⟨hcp, hca⟩ := hcfg
    match send with
    | (false, false) => exact (hcp o ho).2.2
    | (true, true) => exact (hca o ho).2.2
    | (false, true) =>
      simp only [originEndpoint] at ho
      match hp : cfg.primary, ha : cfg.alternate with
      | some p, some a =>
        rw [hp, ha] at ho
        cases ho
        exact (hcp p hp).2.2
      | some _, none => rw [hp, ha] at ho; cases ho
      | none, _ => rw [hp] at ho; cases ho
    | (true, false) =>
      simp only [originEndpoint] at ho
      match hp : cfg.primary, ha : cfg.alternate with
      | some p, some a =>
        rw [hp, ha] at ho
        cases ho
        exact (hca a ha).2.2
      | some _, none => rw [hp, ha] at ho; cases ho
      | none, _ => rw [hp] at ho; cases ho
  -- Every attribute in the list has one of four known types and a ≤20-byte value.
  have hshape : ∀ x ∈ successAttrs cfg send txid src,
      (x.type = attrMappedAddress ∨ x.type = attrXorMappedAddress ∨
       x.type = attrResponseOrigin ∨ x.type = attrOtherAddress) ∧
      x.value.length ≤ 20 := by
    intro x hx
    rcases List.mem_append.mp hx with h12 | ho
    · rcases List.mem_append.mp h12 with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | h1'
        · exact ⟨Or.inl rfl, hmv src hsrc⟩
        · rcases List.mem_singleton.mp h1' with rfl
          exact ⟨Or.inr (Or.inl rfl), hxv⟩
      · obtain ⟨ep, hep, rfl⟩ := addrAttr_mem _ _ _ h2
        exact ⟨Or.inr (Or.inr (Or.inl rfl)), hmv ep (horig ep hep)⟩
    · obtain ⟨ep, hep, rfl⟩ := addrAttr_mem _ _ _ ho
      exact ⟨Or.inr (Or.inr (Or.inr rfl)), hmv ep (hcfg.2 ep hep).2.2⟩
  have hlen : (successAttrs cfg send txid src).length ≤ 4 := by
    have h1 := addrAttr_length attrResponseOrigin (originEndpoint cfg send)
    have h2 := addrAttr_length attrOtherAddress cfg.alternate
    simp only [successAttrs, List.length_append, List.length_cons,
      List.length_nil]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hty, hv⟩ := hshape x hx
    refine ⟨?_, by omega⟩
    rcases hty with h | h | h | h <;>
      simp [h, attrMappedAddress, attrXorMappedAddress, attrResponseOrigin,
        attrOtherAddress]
  · intro x hx
    obtain ⟨hty, _⟩ := hshape x hx
    rcases hty with h | h | h | h <;>
      simp [h, attrMappedAddress, attrXorMappedAddress, attrResponseOrigin,
        attrOtherAddress, attrMessageIntegrity]
  · intro x hx
    obtain ⟨hty, _⟩ := hshape x hx
    rcases hty with h | h | h | h <;>
      simp [h, attrMappedAddress, attrXorMappedAddress, attrResponseOrigin,
        attrOtherAddress, attrFingerprint]
  · -- each attribute serializes to ≤ 4 + 20 + 3 bytes; at most 4 of them
    have hbound : ∀ (l : List Attr), (∀ x ∈ l, x.value.length ≤ 20) →
        (encodeAttrs l).length ≤ 27 * l.length := by
      intro l
      induction l with
      | nil => intro _; simp [encodeAttrs]
      | cons x rest ih =>
        intro hl
        have hx := hl x (List.mem_cons_self x rest)
        have hp := padLen_lt x.value.length
        have := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
        simp only [encodeAttrs, List.length_append, encodeAttr_length, attrSize,
          List.length_cons]
        omega
    have h1 := hbound (successAttrs cfg send txid src)
      (fun x hx => (hshape x hx).2)
    have := hlen
    omega

/-- **Authenticated success (§10.1.2, RFC 8445 §7.3).** When the configured
credential admits a Binding request (username matches, HMAC verifies) that has
no unknown comprehension-required attributes and no CHANGE-REQUEST, the server
answers with a success response that (i) parses as a Binding success echoing
the transaction id, (ii) itself passes MESSAGE-INTEGRITY verification under
the same key — the property an ICE agent demands before it will validate a
candidate pair — (iii) passes FINGERPRINT verification, and (iv) carries an
XOR-MAPPED-ADDRESS decoding to the request's source. -/
theorem serve_authenticated_success (cfg : Config) (a : ShortTermAuth)
    (recv : SockId) (msg : Bytes) (m : Message) (src : Endpoint) (x u : Attr)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (ha : cfg.auth = some a)
    (hmi : findAttr attrMessageIntegrity m.attrs = some x)
    (hu : findAttr attrUsername m.attrs = some u)
    (huv : u.value = a.username)
    (hok : messageIntegrityOk a.key msg = true)
    (h420 : unknownComprehensionRequired m.attrs = [])
    (hnocr : findAttr attrChangeRequest m.attrs = none)
    (hcfg : cfg.Wf)
    (hport : src.port < 65536)
    (hfam : (src.family = 1 ∧ src.addr.length = 4) ∨
            (src.family = 2 ∧ src.addr.length = 16)) :
    ∃ send r mr, serve cfg recv msg src = some (send, r) ∧
      messageIntegrityOk a.key r = true ∧
      fingerprintOk r = true ∧
      parse r = some mr ∧ mr.typ = bindingSuccessType ∧ mr.txid = m.txid ∧
      ∃ xa ∈ mr.attrs, xa.type = attrXorMappedAddress ∧
        decodeXorMapped m.txid xa.value = some src := by
  have htx : m.txid.length = 12 := stun_txid_length msg m hp
  have hsrc : src.addr.length ≤ 16 := by
    rcases hfam with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  obtain ⟨hwf, hnoMI, hnoFP, hblen⟩ :=
    successAttrs_hygiene cfg (sendSock cfg recv (false, false)) m.txid src
      htx hsrc hcfg
  have hty : bindingSuccessType < 65536 := by simp [bindingSuccessType]
  have hac : authCheck cfg.auth msg m = .ok (some a.key) := by
    simp [authCheck, ha, hmi, hu, huv, hok]
  have hserve : serve cfg recv msg src = some (sendSock cfg recv (false, false),
      withIntegrityFingerprint a.key bindingSuccessType m.txid
        (successAttrs cfg (sendSock cfg recv (false, false)) m.txid src)) := by
    simp only [serve, hp, Option.some_bind, if_pos ht, hac, if_pos h420, hnocr,
      serve.mkSuccess]
  refine ⟨sendSock cfg recv (false, false), _, _, hserve,
    withIntegrityFingerprint_integrity_ok a.key bindingSuccessType m.txid _
      hty htx hblen hwf hnoMI,
    withIntegrityFingerprint_fingerprint_ok a.key bindingSuccessType m.txid _
      hty htx hblen hwf hnoFP,
    withIntegrityFingerprint_parses a.key bindingSuccessType m.txid _
      hty htx hblen hwf, rfl, rfl,
    ⟨attrXorMappedAddress, xorMappedValue m.txid src⟩, ?_, rfl,
    xorMapped_roundtrip m.txid src htx hport hfam⟩
  simp [successAttrs]

/-- **CHANGE-REQUEST is honored (RFC 5780 §7.2).** With an alternate deployed,
an admitted request carrying CHANGE-REQUEST flags is answered from the socket
whose IP/port toggle relative to the receiving socket exactly as the flags
ask. (Stated for the unauthenticated service; the credential path composes the
same send-socket computation.) -/
theorem serve_change_request_honored (cfg : Config) (recv : SockId)
    (msg : Bytes) (m : Message) (src : Endpoint) (cr : Attr)
    (ci cp : Bool)
    (hp : parse msg = some m) (ht : m.typ = bindingRequest)
    (ha : cfg.auth = none)
    (h420 : unknownComprehensionRequired m.attrs = [])
    (hcr : findAttr attrChangeRequest m.attrs = some cr)
    (hflags : changeRequestFlags cr.value = some (ci, cp))
    (halt : cfg.alternate.isSome = true) :
    ∃ r, serve cfg recv msg src = some ((recv.1 ^^ ci, recv.2 ^^ cp), r) := by
  have hac : authCheck cfg.auth msg m = .ok none := by simp [authCheck, ha]
  simp only [serve, hp, Option.some_bind, if_pos ht, hac, if_pos h420, hcr,
    hflags, sendSock, halt, if_true]
  exact ⟨_, rfl⟩

def version : String := "0.3.0"

end Stun
