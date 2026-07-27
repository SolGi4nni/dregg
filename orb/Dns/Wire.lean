import Dns.Message

/-!
# Whole-message parse with RDATA offsets (RFC 1035 §4.1)

`parseMsg` decodes a complete DNS message: the 12-octet header, then exactly
`QDCOUNT` questions and `ANCOUNT`/`NSCOUNT`/`ARCOUNT` resource records, and
requires the four sections to tile the message exactly (no trailing octets).

Beyond the section split, each resource record is paired with the **absolute
offset of its RDATA** within the message (`RRAt.rdOff`). Typed RDATA readers
(`Dns.RData`) need this: RFC 1035 §3.3 domain names *inside* RDATA (CNAME, NS,
PTR, MX, SOA) may use compression pointers whose targets live anywhere earlier
in the message, so the sliced `rdata` bytes alone cannot resolve them — the
name must be decoded against the whole message at the RDATA offset.

This file also gives the RFC 1035 §4.1.1 header flag field its meaning: QR,
Opcode, AA, TC, RD, RA and RCODE are read out of the 16-bit `flags` word.
-/

namespace Dns

/-! ## Header flag semantics (RFC 1035 §4.1.1)

The 16-bit flags word, big-endian:

```
 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|QR|   Opcode  |AA|TC|RD|RA|   Z    |   RCODE   |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
```
-/

/-- QR (bit 15 of the value): `false` = query, `true` = response. -/
def Header.qr (h : Header) : Bool := h.flags / 32768 % 2 == 1

/-- OPCODE (bits 14..11): 0 is a standard query (QUERY). -/
def Header.opcode (h : Header) : Nat := h.flags / 2048 % 16

/-- AA (bit 10): authoritative answer. -/
def Header.aa (h : Header) : Bool := h.flags / 1024 % 2 == 1

/-- TC (bit 9): truncation — the message was cut to fit the transport. -/
def Header.tc (h : Header) : Bool := h.flags / 512 % 2 == 1

/-- RD (bit 8): recursion desired. -/
def Header.rd (h : Header) : Bool := h.flags / 256 % 2 == 1

/-- RA (bit 7): recursion available. -/
def Header.ra (h : Header) : Bool := h.flags / 128 % 2 == 1

/-- RCODE (bits 3..0): 0 NoError, 1 FormErr, 2 ServFail, 3 NXDomain, … -/
def Header.rcode (h : Header) : Nat := h.flags % 16

/-- The RCODE field is 4 bits. -/
theorem Header.rcode_lt (h : Header) : h.rcode < 16 := Nat.mod_lt _ (by omega)

/-- The OPCODE field is 4 bits. -/
theorem Header.opcode_lt (h : Header) : h.opcode < 16 := Nat.mod_lt _ (by omega)

/-! ## Resource records with their RDATA offset -/

/-- A parsed resource record plus the absolute offset of its RDATA in the
containing message. `rdOff` is what lets typed RDATA readers resolve
compression pointers that point back into the message. -/
structure RRAt where
  rr : RR
  rdOff : Nat
  deriving Repr, DecidableEq

/-- Consume exactly `n` questions from `off`, threading `Dns.parseQuestion`.
`none` if any question fails to parse. Returns the questions and the offset
just past the last one. -/
def takeQs (msg : Bytes) : Nat → Nat → Option (List Question × Nat)
  | off, 0 => some ([], off)
  | off, Nat.succ n =>
    match parseQuestion msg off with
    | none => none
    | some (q, c) =>
      match takeQs msg (off + c) n with
      | none => none
      | some (qs, off') => some (q :: qs, off')

/-- Consume exactly `n` resource records from `off`, threading `Dns.parseRR`
(whose NAME decode honors the anti-loop pointer rule), and record each RDATA's
absolute offset. On success `parseRR` consumed `name + 10 + rdlength` octets
and produced an `rdata` of exactly `rdlength` octets, so the RDATA begins at
`off + consumed - rdata.length`. -/
def takeRsAt (msg : Bytes) : Nat → Nat → Option (List RRAt × Nat)
  | off, 0 => some ([], off)
  | off, Nat.succ n =>
    match parseRR msg off with
    | none => none
    | some (r, c) =>
      match takeRsAt msg (off + c) n with
      | none => none
      | some (rs, off') => some (⟨r, off + c - r.rdata.length⟩ :: rs, off')

/-- The header plus the four decoded sections of an RFC 1035 §4.1 message,
resource records carrying their RDATA offsets. -/
structure Msg where
  header : Header
  questions : List Question
  answers : List RRAt
  authority : List RRAt
  additional : List RRAt
  deriving Repr, DecidableEq

/-- **The RFC 1035 §4.1 whole-message parse, with RDATA offsets.** Parse the
12-octet header, then exactly `QDCOUNT` questions and `ANCOUNT`/`NSCOUNT`/
`ARCOUNT` resource records, and require the sections to tile the message
exactly (final offset = `msg.length`): a message that lies about its counts or
carries trailing octets is rejected. Total on every input — every step is a
total `Dns` function, and compression-pointer loops terminate via
`Dns.decodeName`. -/
def parseMsg (msg : Bytes) : Option Msg :=
  match parseHeader msg with
  | none => none
  | some (h, hn) =>
    match takeQs msg hn h.qdCount with
    | none => none
    | some (qs, o1) =>
      match takeRsAt msg o1 h.anCount with
      | none => none
      | some (ans, o2) =>
        match takeRsAt msg o2 h.nsCount with
        | none => none
        | some (aut, o3) =>
          match takeRsAt msg o3 h.arCount with
          | none => none
          | some (add, o4) =>
            if o4 = msg.length then some ⟨h, qs, ans, aut, add⟩ else none

theorem parseMsg_total (msg : Bytes) : ∃ r, parseMsg msg = r := ⟨_, rfl⟩

/-! ## The sections carry exactly the declared counts -/

theorem takeQs_length (msg : Bytes) (n : Nat) :
    ∀ (off : Nat) (qs : List Question) (off' : Nat),
      takeQs msg off n = some (qs, off') → qs.length = n := by
  induction n with
  | zero => intro off qs off' h; injection h with h; injection h with h _; subst h; rfl
  | succ n ih =>
    intro off qs off' h
    unfold takeQs at h
    split at h
    · exact absurd h (by simp)
    · rename_i q c _
      split at h
      · exact absurd h (by simp)
      · rename_i qs' o' htail
        injection h with h; injection h with h _; subst h
        simp [ih _ _ _ htail]

theorem takeRsAt_length (msg : Bytes) (n : Nat) :
    ∀ (off : Nat) (rs : List RRAt) (off' : Nat),
      takeRsAt msg off n = some (rs, off') → rs.length = n := by
  induction n with
  | zero => intro off rs off' h; injection h with h; injection h with h _; subst h; rfl
  | succ n ih =>
    intro off rs off' h
    unfold takeRsAt at h
    split at h
    · exact absurd h (by simp)
    · rename_i r c _
      split at h
      · exact absurd h (by simp)
      · rename_i rs' o' htail
        injection h with h; injection h with h _; subst h
        simp [ih _ _ _ htail]

/-- **Counts are load-bearing.** A parsed message's sections have exactly the
lengths its header declared. -/
theorem parseMsg_counts (msg : Bytes) (m : Msg) (h : parseMsg msg = some m) :
    m.questions.length = m.header.qdCount
    ∧ m.answers.length = m.header.anCount
    ∧ m.authority.length = m.header.nsCount
    ∧ m.additional.length = m.header.arCount := by
  unfold parseMsg at h
  split at h
  · exact absurd h (by simp)
  · rename_i hd hn _
    split at h
    · exact absurd h (by simp)
    · rename_i qs o1 hqs
      split at h
      · exact absurd h (by simp)
      · rename_i ans o2 hans
        split at h
        · exact absurd h (by simp)
        · rename_i aut o3 haut
          split at h
          · exact absurd h (by simp)
          · rename_i add o4 hadd
            split at h
            · injection h with h; subst h
              exact ⟨takeQs_length msg _ _ _ _ hqs, takeRsAt_length msg _ _ _ _ hans,
                     takeRsAt_length msg _ _ _ _ haut, takeRsAt_length msg _ _ _ _ hadd⟩
            · exact absurd h (by simp)

/-- Every record a section walk emits was produced by the real `Dns.parseRR`
at some offset, and its `rdOff` is that record's RDATA position (`parseRR`
consumed `name + 10 + rdlength`; the RDATA is the final `rdata.length` octets
of what it consumed). -/
theorem takeRsAt_sound (msg : Bytes) (n : Nat) :
    ∀ (off : Nat) (rs : List RRAt) (off' : Nat),
      takeRsAt msg off n = some (rs, off') →
      ∀ r ∈ rs, ∃ o c, parseRR msg o = some (r.rr, c) ∧ r.rdOff = o + c - r.rr.rdata.length := by
  induction n with
  | zero =>
    intro off rs off' h r hr
    injection h with h; injection h with h _; subst h; simp at hr
  | succ n ih =>
    intro off rs off' h r hr
    unfold takeRsAt at h
    split at h
    · exact absurd h (by simp)
    · rename_i r0 c hp
      split at h
      · exact absurd h (by simp)
      · rename_i rs' o' htail
        injection h with h; injection h with h _; subst h
        rcases List.mem_cons.mp hr with heq | htl
        · subst heq; exact ⟨off, c, hp, rfl⟩
        · exact ih _ _ _ htail r htl

/-! ## Worked vector: a full message with header semantics, kernel-checked -/

/-- A response header: id 0x1234, flags 0x8180 (QR, RD, RA, RCODE 0). -/
example :
    (Header.mk 0x1234 0x8180 1 1 0 0).qr = true ∧
    (Header.mk 0x1234 0x8180 1 1 0 0).opcode = 0 ∧
    (Header.mk 0x1234 0x8180 1 1 0 0).tc = false ∧
    (Header.mk 0x1234 0x8180 1 1 0 0).rcode = 0 := by decide

/-- NXDOMAIN flags 0x8183: QR set, RCODE 3. -/
example :
    (Header.mk 7 0x8183 1 0 0 0).qr = true ∧ (Header.mk 7 0x8183 1 0 0 0).rcode = 3 := by
  decide

/-- A query header (flags 0x0120: RD + AD bit): QR clear. -/
example : (Header.mk 7 0x0120 1 0 0 0).qr = false := by decide

/-- One question `up IN A`, one answer A record: full parse. The answer RR
begins at offset 20 and its name consumes 4 octets, so its RDATA (the 4
address octets) sits at offset 20 + 4 + 10 = 34 of the 38-octet message. -/
example :
    parseMsg
      [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
        2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
        2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
        93, 184, 216, 34 ]
      = some
          { header := { id := 0x1234, flags := 0x8180, qdCount := 1, anCount := 1,
                        nsCount := 0, arCount := 0 }
            questions := [{ qname := [[117, 112]], qtype := 1, qclass := 1 }]
            answers := [⟨{ name := [[117, 112]], rrType := 1, rrClass := 1, ttl := 60,
                           rdata := [93, 184, 216, 34] }, 34⟩]
            authority := []
            additional := [] } := by decide

/-- A trailing octet past the last section is rejected — the tiling check. -/
example :
    parseMsg
      [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
        2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
        2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
        93, 184, 216, 34, 0xFF ]
      = none := by decide

end Dns
