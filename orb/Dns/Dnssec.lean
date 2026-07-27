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
      have he : (UInt8.ofNat (b.toNat + 32)).toNat = (b.toNat + 32) % 256 := rfl
      rw [he, Nat.mod_eq_of_lt (by omega)]
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

/-! ## Canonical RRset ordering (RFC 4034 §6.3)

For signing and verification an RRset's RRs are placed in canonical order:
"RRs with the same owner name, class, and type are sorted by treating the RDATA
portion of the canonical form of each RR as a left-justified unsigned octet
sequence in which the absence of an octet sorts before a zero octet."  This is
octet-by-octet lexicographic order on the (already canonical) RDATA byte
strings, with a proper prefix sorting first.

`canonSort` realises §6.3 by insertion sort under `rdataLe`.  We prove the two
properties a canonical order must have: the result is `Pairwise`-ordered
(actually sorted) and a permutation of the input (no RR added or dropped).  The
signature is computed over `RRSIG_RDATA | canonSort(RRs)`; the crypto boundary
below never sees an out-of-order set. -/

/-- RFC 4034 §6.3 octet order on RDATA: lexicographic on the octet sequences, a
proper prefix sorting first ("absence of an octet sorts before a zero octet").
Compared through `UInt8.toNat` so the arithmetic is over `Nat`. -/
def rdataLe : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a.toNat = b.toNat then rdataLe as bs
      else decide (a.toNat < b.toNat)

/-- The §6.3 order is total: any two RDATA strings are comparable. -/
theorem rdataLe_total : ∀ a b : Bytes, rdataLe a b = true ∨ rdataLe b a = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: as, b :: bs => by
    simp only [rdataLe]
    by_cases e : a.toNat = b.toNat
    · rw [if_pos e, if_pos e.symm]; exact rdataLe_total as bs
    · rw [if_neg e, if_neg (fun h => e h.symm), decide_eq_true_eq, decide_eq_true_eq]
      omega

/-- The §6.3 order is transitive — so insertion under it yields a sorted list. -/
theorem rdataLe_trans : ∀ a b c : Bytes,
    rdataLe a b = true → rdataLe b c = true → rdataLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h1, _ => by simp [rdataLe] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [rdataLe] at h2
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    simp only [rdataLe] at h1 h2 ⊢
    by_cases e1 : a.toNat = b.toNat <;> by_cases e2 : b.toNat = c.toNat
    · rw [if_pos e1] at h1; rw [if_pos e2] at h2; rw [if_pos (e1.trans e2)]
      exact rdataLe_trans as bs cs h1 h2
    · rw [if_pos e1] at h1; rw [if_neg e2, decide_eq_true_eq] at h2
      rw [if_neg (by omega), decide_eq_true_eq]; omega
    · rw [if_neg e1, decide_eq_true_eq] at h1; rw [if_pos e2] at h2
      rw [if_neg (by omega), decide_eq_true_eq]; omega
    · rw [if_neg e1, decide_eq_true_eq] at h1; rw [if_neg e2, decide_eq_true_eq] at h2
      rw [if_neg (by omega), decide_eq_true_eq]; omega

/-- Insert `x` into `l` keeping `rdataLe` order. -/
def rdataInsert (x : Bytes) : List Bytes → List Bytes
  | [] => [x]
  | y :: ys => if rdataLe x y then x :: y :: ys else y :: rdataInsert x ys

/-- Canonical §6.3 sort of an RRset's RDATA strings. -/
def canonSort : List Bytes → List Bytes
  | [] => []
  | x :: xs => rdataInsert x (canonSort xs)

/-- Inserting is a permutation: it moves no octet string, only reorders. -/
theorem rdataInsert_perm (x : Bytes) : ∀ l, List.Perm (rdataInsert x l) (x :: l)
  | [] => .refl _
  | y :: ys => by
    unfold rdataInsert
    split
    · exact .refl _
    · exact ((rdataInsert_perm x ys).cons y).trans (.swap x y ys)

/-- **`canonSort` is a permutation of its input** — the canonical order neither
adds nor drops an RR (RFC 4034 §6.3 reorders the RRset, nothing else). -/
theorem canonSort_perm : ∀ l, List.Perm (canonSort l) l
  | [] => .refl _
  | x :: xs => (rdataInsert_perm x (canonSort xs)).trans ((canonSort_perm xs).cons x)

/-- Membership through an insert. -/
theorem mem_rdataInsert (x : Bytes) (l : List Bytes) (a : Bytes) :
    a ∈ rdataInsert x l ↔ a = x ∨ a ∈ l := by
  rw [(rdataInsert_perm x l).mem_iff, List.mem_cons]

/-- Inserting into a sorted list stays sorted. -/
theorem rdataInsert_sorted (x : Bytes) : ∀ l,
    l.Pairwise (fun a b => rdataLe a b = true) →
    (rdataInsert x l).Pairwise (fun a b => rdataLe a b = true)
  | [], _ => by simp [rdataInsert]
  | y :: ys, hp => by
    unfold rdataInsert
    split
    · rename_i hle
      rw [List.pairwise_cons]
      refine ⟨?_, hp⟩
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; exact hle
      · exact rdataLe_trans _ _ _ hle ((List.pairwise_cons.mp hp).1 z h)
    · rename_i hle
      have hyx : rdataLe y x = true := by
        rcases rdataLe_total x y with h | h
        · exact absurd h hle
        · exact h
      rw [List.pairwise_cons]
      refine ⟨?_, rdataInsert_sorted x ys (List.pairwise_cons.mp hp).2⟩
      intro z hz
      rcases (mem_rdataInsert x ys z).mp hz with h | h
      · subst h; exact hyx
      · exact (List.pairwise_cons.mp hp).1 z h

/-- **`canonSort` produces a sorted list** — the RFC 4034 §6.3 canonical order,
realised: adjacent (indeed all) RDATA strings are `rdataLe`-ordered. -/
theorem canonSort_sorted : ∀ l,
    (canonSort l).Pairwise (fun a b => rdataLe a b = true)
  | [] => by simp [canonSort]
  | x :: xs => by
    show (rdataInsert x (canonSort xs)).Pairwise _
    exact rdataInsert_sorted x (canonSort xs) (canonSort_sorted xs)

/-! ## RRsets and RRSIG coverage (RFC 4035 §5.3.1)

An RRset is the RRs sharing an owner name, class, and type; its `rdatas` are the
per-RR RDATA byte strings.  RFC 4035 §5.3.1 says an RRSIG *covers* an RRset when
the RRSIG's Type Covered equals the RRset type, its owner name (case-insensitively)
and class equal the RRset's, its Original TTL equals the RRset TTL used in the
canonical form (RFC 4034 §6.2), and its Labels count does not exceed the number
of labels in the owner name.  These are the structural conditions that must hold
*before* the signature bytes are ever checked. -/

/-- The RRs sharing an owner name/class/type — the unit an RRSIG signs. -/
structure RRset where
  owner : List (List UInt8)
  rrClass : Nat
  rrType : Nat
  ttl : Nat
  rdatas : List Bytes
  deriving Repr, DecidableEq

/-- An RRSIG record view (RFC 4034 §3.1) together with the owner name and class
of the RRSIG RR itself (which, per §3.1, equal the covered RRset's). -/
structure Rrsig where
  owner : List (List UInt8)
  rrClass : Nat
  typeCovered : Nat
  algorithm : Nat
  labels : Nat
  origTtl : Nat
  expiration : Nat
  inception : Nat
  keyTag : Nat
  signer : List (List UInt8)
  signature : Bytes
  deriving Repr, DecidableEq

/-- RFC 4035 §5.3.1 coverage decision: the structural match between an RRSIG and
the RRset it claims to sign. -/
def rrsigCovers (s : Rrsig) (rs : RRset) : Bool :=
  (s.typeCovered == rs.rrType)
    && nameEq s.owner rs.owner
    && (s.rrClass == rs.rrClass)
    && (s.origTtl == rs.ttl)
    && (s.labels ≤ rs.owner.length)

/-- **RFC 4035 §5.3.1 — an RRSIG covers exactly the RRset whose type, owner,
class and TTL it matches, and it signs that RRset in RFC 4034 §6.3 canonical
order.** The coverage decision decodes into its component matches, and the
signed material `canonSort rs.rdatas` is a sorted permutation of the RRset. -/
theorem dnssec_rrsig_covers (s : Rrsig) (rs : RRset) (h : rrsigCovers s rs = true) :
    s.typeCovered = rs.rrType
      ∧ nameEq s.owner rs.owner = true
      ∧ s.rrClass = rs.rrClass
      ∧ s.origTtl = rs.ttl
      ∧ s.labels ≤ rs.owner.length
      ∧ List.Perm (canonSort rs.rdatas) rs.rdatas
      ∧ (canonSort rs.rdatas).Pairwise (fun a b => rdataLe a b = true) := by
  unfold rrsigCovers at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ht, hn⟩, hc⟩, hto⟩, hl⟩ := h
  refine ⟨?_, hn, ?_, ?_, ?_, canonSort_perm _, canonSort_sorted _⟩
  · exact eq_of_beq ht
  · exact eq_of_beq hc
  · exact eq_of_beq hto
  · exact of_decide_eq_true hl

/-- Mutant: an RRSIG whose Type Covered is A(1) does **not** cover a DS(43)
RRset, even with every other field matching. -/
example :
    rrsigCovers
      { owner := [[0x63,0x6f,0x6d]], rrClass := 1, typeCovered := 1, algorithm := 8,
        labels := 1, origTtl := 3600, expiration := 0, inception := 0, keyTag := 45013,
        signer := [[0x63,0x6f,0x6d]], signature := [1] }
      { owner := [[0x63,0x6f,0x6d]], rrClass := 1, rrType := 43, ttl := 3600,
        rdatas := [[0x11],[0x22]] } = false := by decide

/-! ## Chain of trust: DNSKEY → DS → parent → trust anchor
(RFC 4035 §5, RFC 4034 §5, RFC 4509)

Authentication proceeds from a configured trust anchor down the delegation
chain.  Each zone's DNSKEY (its secure-entry-point / KSK) is authenticated by a
DS record in the *parent* zone: the DS carries the key's tag (RFC 4034 App. B),
algorithm, and a digest of the DNSKEY.  That parent-side DS RRset is in turn
signed by the parent zone's DNSKEY — and so on, up to a DS the resolver trusts a
priori (the anchor).  A chain that links to an anchor is **Secure**; a chain
with a broken link (a DS that does not match its key, a signature that does not
verify, or a top that is no anchor) is **Bogus**.

Two cryptographic operations are named boundaries, never opened:
`verifyRRSIG` (RFC 4035 §5.3.3, the RRSIG-over-RRset check) and `dsDigestMatch`
(RFC 4034 §5.1.4 / RFC 4509, the DS digest of a DNSKEY).  Every theorem below
holds for *every* behaviour of those primitives — the result is about the
composition of the chain conditions, not the cipher.  Modelled in the drorb-
native `Dns` library; not the deployed serve path. -/

/-- A zone DNSKEY (RFC 4034 §2): owner name, flags, algorithm, and the full
DNSKEY RDATA (over which the key tag is computed). -/
structure Dnskey where
  owner : List (List UInt8)
  flags : Nat
  algorithm : Nat
  rdata : Bytes
  deriving Repr, DecidableEq

/-- A delegation-signer record (RFC 4034 §5). -/
structure Ds where
  owner : List (List UInt8)
  keyTag : Nat
  algorithm : Nat
  digestType : Nat
  digest : Bytes
  deriving Repr, DecidableEq

/-- The named crypto boundaries plus the configured trust anchors. -/
structure DnssecEnv where
  /-- RFC 4035 §5.3.3: `verifyRRSIG key sig rrset` is `true` iff `sig` is a valid
  RRSIG over `rrset` under `key`. Uninterpreted. -/
  verifyRRSIG : Dnskey → Rrsig → RRset → Bool
  /-- RFC 4034 §5.1.4 / RFC 4509: `dsDigestMatch ds key` is `true` iff `ds`'s
  digest is the digest of `key`'s DNSKEY RDATA. Uninterpreted. -/
  dsDigestMatch : Ds → Dnskey → Bool
  /-- Trust anchors: DS records trusted directly (the root KSK's DS). -/
  anchors : List Ds

/-- One link of the delegation chain: a zone's KSK, the parent's DS pointing at
it, and the parent-side DS RRset with its RRSIG. -/
structure Link where
  key : Dnskey
  ds : Ds
  dsSet : RRset
  dsSig : Rrsig
  deriving Repr, DecidableEq

/-- A DS matches a DNSKEY (RFC 4034 §5.1): key tag (App. B), algorithm and owner
agree, and the digest matches under the named boundary. -/
def dsMatchesKey (env : DnssecEnv) (d : Ds) (k : Dnskey) : Bool :=
  (d.keyTag == keyTag k.rdata)
    && (d.algorithm == k.algorithm)
    && nameEq d.owner k.owner
    && env.dsDigestMatch d k

/-- Field equality of two DS records (canonical owner comparison). -/
def dsEq (a b : Ds) : Bool :=
  (a.keyTag == b.keyTag) && (a.algorithm == b.algorithm)
    && (a.digestType == b.digestType) && (a.digest == b.digest)
    && nameEq a.owner b.owner

/-- A DS is a configured trust anchor. -/
def anchorMatch (env : DnssecEnv) (d : Ds) : Bool := env.anchors.any (dsEq d)

/-- **Chain validation.** The chain is ordered child-first up to the root.  A
single top link is Secure iff its DS is a trust anchor matching its key.  An
interior link is Secure iff its DS matches its key, the parent-side DS RRSIG
structurally covers and verifies under the parent's key, and the rest of the
chain up to the anchor is Secure. -/
def chainSecure (env : DnssecEnv) : List Link → Bool
  | [] => false
  | [top] => anchorMatch env top.ds && dsMatchesKey env top.ds top.key
  | cur :: parent :: rest =>
      dsMatchesKey env cur.ds cur.key
        && rrsigCovers cur.dsSig cur.dsSet
        && env.verifyRRSIG parent.key cur.dsSig cur.dsSet
        && chainSecure env (parent :: rest)

/-- DNSSEC validation status (RFC 4035 §5). `insecure` is the unsigned-delegation
outcome (out of scope here); validation yields `secure` or `bogus`. -/
inductive Status where
  | secure
  | insecure
  | bogus
  deriving Repr, DecidableEq

/-- The validator's verdict: Secure iff the chain links to an anchor, else Bogus. -/
def validate (env : DnssecEnv) (chain : List Link) : Status :=
  if chainSecure env chain then .secure else .bogus

/-- **A Secure chain terminates at a configured trust anchor.** If validation
accepts the chain, some link in it carries a DS that is a trust anchor and that
matches that link's key — the recursion cannot report Secure without reaching an
anchoring link (RFC 4035 §5, no self-signed shortcut). -/
theorem dnssec_chain_to_anchor (env : DnssecEnv) :
    ∀ chain, chainSecure env chain = true →
      ∃ top, top ∈ chain ∧ anchorMatch env top.ds = true
        ∧ dsMatchesKey env top.ds top.key = true := by
  intro chain
  induction chain with
  | nil => intro h; simp [chainSecure] at h
  | cons cur tl ih =>
    intro h
    cases tl with
    | nil =>
      simp only [chainSecure, Bool.and_eq_true] at h
      exact ⟨cur, List.mem_cons_self, h.1, h.2⟩
    | cons parent rest =>
      simp only [chainSecure, Bool.and_eq_true] at h
      obtain ⟨top, hmem, ha, hd⟩ := ih h.2
      exact ⟨top, List.mem_cons_of_mem _ hmem, ha, hd⟩

/-- **A broken link is rejected as Bogus, never Secure.** If the parent's DS
RRSIG fails to verify under the parent key at any interior link, the whole chain
is Bogus (RFC 4035 §5.5: a failed signature makes the answer Bogus). -/
theorem dnssec_bogus_rejected (env : DnssecEnv) (cur parent : Link) (rest : List Link)
    (hbreak : env.verifyRRSIG parent.key cur.dsSig cur.dsSet = false) :
    validate env (cur :: parent :: rest) = Status.bogus := by
  have hf : chainSecure env (cur :: parent :: rest) = false := by
    simp only [chainSecure, hbreak, Bool.and_false, Bool.false_and]
  unfold validate; rw [hf]; rfl

/-! ## Worked chain vectors (concrete env, kernel-checked) -/

/-- The signed DS RRset at `com` and the RRSIG that covers it. -/
def egDsSet : RRset :=
  { owner := [[0x63,0x6f,0x6d]], rrClass := 1, rrType := 43, ttl := 3600,
    rdatas := [[0x11],[0x22]] }
def egSig : Rrsig :=
  { owner := [[0x63,0x6f,0x6d]], rrClass := 1, typeCovered := 43, algorithm := 8,
    labels := 1, origTtl := 3600, expiration := 0, inception := 0, keyTag := 45013,
    signer := [[0x63,0x6f,0x6d]], signature := [0x01] }

/-- The `com` KSK; key tag of `[1,0,3,8,0xAB,0xCD]` is 45013 (RFC 4034 App. B). -/
def egRootKey : Dnskey :=
  { owner := [[0x63,0x6f,0x6d]], flags := 257, algorithm := 8, rdata := [1,0,3,8,0xAB,0xCD] }
def egAnchorDs : Ds :=
  { owner := [[0x63,0x6f,0x6d]], keyTag := 45013, algorithm := 8, digestType := 2, digest := [0xAA] }

/-- Env with the anchor DS and both crypto boundaries returning `true`. -/
def egEnv : DnssecEnv :=
  { verifyRRSIG := fun _ _ _ => true, dsDigestMatch := fun _ _ => true, anchors := [egAnchorDs] }

def egTop : Link := { key := egRootKey, ds := egAnchorDs, dsSet := egDsSet, dsSig := egSig }

/-- A one-link chain whose DS is the trust anchor validates Secure. -/
example : chainSecure egEnv [egTop] = true := by decide
example : validate egEnv [egTop] = Status.secure := by decide

/-- Mutant: change the top DS key tag so it neither matches the key nor the
anchor — the same chain is now Bogus. -/
def egBadTop : Link := { egTop with ds := { egAnchorDs with keyTag := 12345 } }
example : validate egEnv [egBadTop] = Status.bogus := by decide

/-- Child zone `www` under `com`; key tag of `[1,0,3,8,0x12,0x34]` is 5692. -/
def egChildKey : Dnskey :=
  { owner := [[0x77,0x77,0x77]], flags := 256, algorithm := 8, rdata := [1,0,3,8,0x12,0x34] }
def egChildDs : Ds :=
  { owner := [[0x77,0x77,0x77]], keyTag := 5692, algorithm := 8, digestType := 2, digest := [0xCC] }
def egChildSig : Rrsig :=
  { owner := [[0x77,0x77,0x77]], rrClass := 1, typeCovered := 43, algorithm := 8,
    labels := 1, origTtl := 3600, expiration := 0, inception := 0, keyTag := 45013,
    signer := [[0x63,0x6f,0x6d]], signature := [0x02] }
def egChildDsSet : RRset :=
  { owner := [[0x77,0x77,0x77]], rrClass := 1, rrType := 43, ttl := 3600, rdatas := [[0x33]] }
def egChild : Link := { key := egChildKey, ds := egChildDs, dsSet := egChildDsSet, dsSig := egChildSig }

/-- A two-link chain (`www` under `com`, `com` at the anchor) validates Secure:
the interior DS matches, its RRSIG covers and verifies, and the top anchors. -/
example : chainSecure egEnv [egChild, egTop] = true := by decide
example : validate egEnv [egChild, egTop] = Status.secure := by decide

/-- Mutant: break the interior DS RRSIG verify — the two-link chain is Bogus. -/
example :
    validate { egEnv with verifyRRSIG := fun _ _ _ => false } [egChild, egTop]
      = Status.bogus := by decide

end Dns
