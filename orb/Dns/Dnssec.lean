import Dns.RData

/-!
# Canonical name form, key tags, and type bitmaps (RFC 1035 §2.3.3, RFC 4034)

Three pieces of DNS semantics that sit *between* the wire parse and resolution:

* **Case-insensitive name comparison (RFC 1035 §2.3.3).** "For all parts of
  the DNS that are part of the official protocol, all comparisons between
  character strings (e.g., labels, domain names, etc.) are done in a
  case-insensitive manner." `canonName` folds ASCII `A–Z` to `a–z` label-wise;
  `nameEq` is the §2.3.3 comparison. This is also exactly the *canonical form*
  of a domain name required by RFC 4034 §6.2 ("all uppercase US-ASCII letters
  in the owner name of the RR are replaced by the corresponding lowercase
  US-ASCII letters") — the form DNSSEC signatures are computed over.

* **Key tag (RFC 4034 Appendix B).** The 16-bit tag over a DNSKEY RDATA that
  RRSIG and DS records use to select a key: the ones-complement-style checksum
  of the RDATA read as big-endian 16-bit words.

* **Type bitmaps (RFC 4034 §4.1.2, shared by RFC 5155 §3.2.1).** The NSEC /
  NSEC3 "Type Bit Maps" field: a sequence of `(window, length, bitmap)`
  blocks, each bitmap octet's most-significant bit standing for the lowest
  type number of its 8-type slot.
-/

namespace Dns

/-! ## Canonical form (RFC 1035 §2.3.3, RFC 4034 §6.2) -/

/-- ASCII case fold of one octet: uppercase `A–Z` (0x41–0x5A) maps to
lowercase; every other octet — digits, hyphens, and non-ASCII binary labels —
is untouched, as §2.3.3 prescribes ("when data enters the domain system, its
original case should be preserved"; only *comparison* folds). -/
def canonByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then UInt8.ofNat (b.toNat + 32) else b

/-- Case-fold a label. -/
def canonLabel (l : List UInt8) : List UInt8 := l.map canonByte

/-- The RFC 4034 §6.2 canonical form of a domain name (case only; names here
are already fully expanded, never compressed). -/
def canonName (n : List (List UInt8)) : List (List UInt8) := n.map canonLabel

/-- **RFC 1035 §2.3.3 name comparison**: equality of canonical forms. -/
def nameEq (a b : List (List UInt8)) : Bool := canonName a == canonName b

/-- Case-folding is idempotent: a folded octet is never in `A–Z` again. -/
theorem canonByte_idem (b : UInt8) : canonByte (canonByte b) = canonByte b := by
  unfold canonByte
  split
  · rename_i h
    have ht : (UInt8.ofNat (b.toNat + 32)).toNat = b.toNat + 32 := by
      rw [UInt8.toNat_ofNat]; omega
    rw [if_neg (by rw [ht]; omega)]
  · rfl

theorem canonLabel_idem (l : List UInt8) : canonLabel (canonLabel l) = canonLabel l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    simp only [canonLabel, List.map_cons] at *
    rw [canonByte_idem, ih]

/-- The canonical form is a fixed point: folding twice is folding once. -/
theorem canonName_idem (n : List (List UInt8)) : canonName (canonName n) = canonName n := by
  induction n with
  | nil => rfl
  | cons l t ih =>
    simp only [canonName, List.map_cons] at *
    rw [canonLabel_idem, ih]

/-- `nameEq` is exactly equality of RFC 4034 §6.2 canonical forms. -/
theorem nameEq_iff (a b : List (List UInt8)) :
    nameEq a b = true ↔ canonName a = canonName b := by
  simp [nameEq]

theorem nameEq_refl (a : List (List UInt8)) : nameEq a a = true := by simp [nameEq]

theorem nameEq_of_eq (a b : List (List UInt8)) (h : a = b) : nameEq a b = true := by
  subst h; exact nameEq_refl a

theorem nameEq_symm (a b : List (List UInt8)) (h : nameEq a b = true) :
    nameEq b a = true := by
  rw [nameEq_iff] at *; exact h.symm

theorem nameEq_trans (a b c : List (List UInt8))
    (h1 : nameEq a b = true) (h2 : nameEq b c = true) : nameEq a c = true := by
  rw [nameEq_iff] at *; exact h1.trans h2

/-- Case-folding never changes a label's length… -/
theorem canonLabel_length (l : List UInt8) : (canonLabel l).length = l.length :=
  List.length_map ..

/-- …so it never changes a name's wire length: the canonical form of a legal
name is a legal name (RFC 1035 §2.3.4 limits are case-blind). -/
theorem wireLen_canon (n : List (List UInt8)) : wireLen (canonName n) = wireLen n := by
  unfold wireLen
  induction n with
  | nil => rfl
  | cons l t ih =>
    simp only [canonName, List.map_cons, labelsLen, canonLabel_length] at *
    omega

/-- Worked §2.3.3 pairs: `UP` compares equal to `up`; `a-b` is untouched and
distinct from `a.b`'s labels. -/
example : nameEq [[85, 80]] [[117, 112]] = true := by decide
example : nameEq [[65]] [[97], [98]] = false := by decide
example : canonLabel [65, 45, 90, 48] = [97, 45, 122, 48] := by decide

/-! ## Key tag (RFC 4034 Appendix B) -/

/-- The Appendix B accumulation: the RDATA read as big-endian 16-bit words
(a trailing odd octet contributes its high byte only). `i` is the octet index,
big-endian position selected by its parity. -/
def keyTagSum : Bytes → Nat → Nat
  | [], _ => 0
  | b :: rest, i => (if i % 2 = 0 then b.toNat * 256 else b.toNat) + keyTagSum rest (i + 1)

/-- **RFC 4034 Appendix B key tag** of a DNSKEY RDATA: the word sum plus its
carry, truncated to 16 bits. -/
def keyTag (rdata : Bytes) : Nat :=
  let s := keyTagSum rdata 0
  (s + s / 65536 % 65536) % 65536

/-- The key tag is a 16-bit value. -/
theorem keyTag_lt (rdata : Bytes) : keyTag rdata < 65536 :=
  Nat.mod_lt _ (by omega)

/-- Appendix B on a worked RDATA: flags 256, protocol 3, algorithm 8, two key
octets — sum = 0x0100 + 0x0308 + 0xABCD carries into the tag. -/
example : keyTag [1, 0, 3, 8, 0xAB, 0xCD] = (0x0100 + 0x0308 + 0xABCD) % 65536 := by decide

/-! ## Type bitmaps (RFC 4034 §4.1.2 / RFC 5155 §3.2.1) -/

/-- The set bit positions of one bitmap octet, most-significant first: bit 0
(the MSB) is the lowest type of the octet's slot. -/
def byteBits (b : Nat) : List Nat :=
  (List.range 8).filter (fun k => b / 2 ^ (7 - k) % 2 == 1)

/-- Types contributed by one window's bitmap octets, `j` the octet index. -/
def windowBits (base : Nat) : Nat → Bytes → List Nat
  | _, [] => []
  | j, b :: rest =>
    (byteBits b.toNat).map (fun k => base + j * 8 + k) ++ windowBits base (j + 1) rest

/-- Fuel-driven walk over `(window, length, bitmap)` blocks. RFC 4034 §4.1.2:
each block's bitmap is 1–32 octets ("Blocks with no types present MUST NOT be
included"; length is at most 32). `none` when a block overruns or violates the
length rule. -/
def bitmapTypesAux : Nat → Bytes → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | Nat.succ fuel, w :: n :: rest =>
    if 1 ≤ n.toNat ∧ n.toNat ≤ 32 ∧ n.toNat ≤ rest.length then
      match bitmapTypesAux fuel (rest.drop n.toNat) with
      | none => none
      | some ts => some (windowBits (w.toNat * 256) 0 (rest.take n.toNat) ++ ts)
    else none
  | Nat.succ _, [_] => none

/-- Decode a Type Bit Maps field into its type numbers. -/
def bitmapTypes (l : Bytes) : Option (List Nat) := bitmapTypesAux l.length l

theorem byteBits_lt (b : Nat) : ∀ k ∈ byteBits b, k < 8 := by
  intro k hk
  unfold byteBits at hk
  exact List.mem_range.mp (List.mem_filter.mp hk).1

theorem windowBits_lt (base : Nat) (hbase : base ≤ 65280) :
    ∀ (bytes : Bytes) (j : Nat), j * 8 + bytes.length * 8 ≤ 256 →
      ∀ t ∈ windowBits base j bytes, t < 65536 := by
  intro bytes
  induction bytes with
  | nil => intro j _ t ht; simp [windowBits] at ht
  | cons b rest ih =>
    intro j hlen t ht
    unfold windowBits at ht
    rcases List.mem_append.mp ht with h | h
    · rcases List.mem_map.mp h with ⟨k, hk, hkt⟩
      have hk8 := byteBits_lt b.toNat k hk
      simp only [List.length_cons] at hlen
      omega
    · exact ih (j + 1) (by simp only [List.length_cons] at hlen; omega) t h

theorem bitmapTypesAux_lt (fuel : Nat) :
    ∀ (l : Bytes) (ts : List Nat), bitmapTypesAux fuel l = some ts →
      ∀ t ∈ ts, t < 65536 := by
  induction fuel with
  | zero =>
    intro l ts h t ht
    match l with
    | [] => injection h with h; subst h; simp at ht
    | _ :: _ => exact absurd h (by simp [bitmapTypesAux])
  | succ fuel ih =>
    intro l ts h t ht
    match l with
    | [] => injection h with h; subst h; simp at ht
    | [_] => exact absurd h (by simp [bitmapTypesAux])
    | w :: n :: rest =>
      unfold bitmapTypesAux at h
      split at h
      · rename_i hc
        split at h
        · exact absurd h (by simp)
        · rename_i ts' htail
          injection h with h; subst h
          rcases List.mem_append.mp ht with h1 | h1
          · refine windowBits_lt (w.toNat * 256) ?_ (rest.take n.toNat) 0 ?_ t h1
            · have := u8_lt w; omega
            · rw [List.length_take]; omega
          · exact ih _ _ htail t h1
      · exact absurd h (by simp)

/-- **Every decoded type is a 16-bit type number** — the window/offset
arithmetic cannot escape the RR-type space. -/
theorem bitmapTypes_lt (l : Bytes) (ts : List Nat) (h : bitmapTypes l = some ts) :
    ∀ t ∈ ts, t < 65536 :=
  bitmapTypesAux_lt _ _ _ h

/-- The RFC 4034 §4.1.2 worked example, kernel-checked: the bitmap encoding
the type set {A, MX, RRSIG, NSEC, TYPE1234} decodes to exactly those numbers.
Window 0 carries A(1)/MX(15)/RRSIG(46)/NSEC(47); window 4, octet 26, bit 2
carries 1234. -/
example :
    bitmapTypes
      ([0x00, 0x06, 0x40, 0x01, 0x00, 0x00, 0x00, 0x03,
        0x04, 0x1B] ++ List.replicate 24 0x00 ++ [0x00, 0x00, 0x20])
      = some [1, 15, 46, 47, 1234] := by decide

end Dns
