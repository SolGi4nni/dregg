import Dns.Message
import Reactor.Dns

/-!
# Correctness of DNS message parsing (RFC 1035 §4.1)

The `Dns` library's `parseHeader`, `parseQuestion`, and `parseRR` are the parsers
the deployed resolver (`Reactor.DnsWire.resolve`) runs over a DNS response before
the reactor honors an upstream connect. This module proves those *deployed*
parsers correct against an **independent specification written from RFC 1035
§4.1**, without reference to the implementation, and then states the whole-message
structural invariant the RFC mandates.

## What RFC 1035 §4.1 says

> §4.1: "All communications inside of the domain protocol are carried in a single
> format called a message. The top level format of message is divided into 5
> sections … Header | Question | Answer | Authority | Additional. … The header
> section is always present. … [it] includes fields that specify which of the
> remaining sections are present, and also specify whether the message is a query
> or a response …"

> §4.1.1 Header section format. A 12-octet header of six 16-bit fields, in order:
> `ID`, a 16-bit flags word (`QR|Opcode|AA|TC|RD|RA|Z|RCODE`), then the four
> section counts `QDCOUNT`, `ANCOUNT`, `NSCOUNT`, `ARCOUNT`. Each count "specifies
> the number of entries" in the corresponding section.

> §4.1.2 Question section format. Each question is `QNAME` (a domain name) followed
> by a 16-bit `QTYPE` and a 16-bit `QCLASS`.

> §4.1.3 Resource record format. Each RR is `NAME`, 16-bit `TYPE`, 16-bit `CLASS`,
> 32-bit `TTL`, 16-bit `RDLENGTH`, then `RDLENGTH` octets of `RDATA`.

Fixed-length numeric fields are transmitted in network byte order — most
significant octet first (RFC 1035 §2.3.2 / §3.3-style field layout diagrams read
bit 0 as the most significant). The header carries exactly `QDCOUNT` questions,
then `ANCOUNT` + `NSCOUNT` + `ARCOUNT` resource records; the counts must equal the
number of entries actually present (nothing more, nothing less).

## The specification (independent of the implementation)

`beU16` / `beU32` read network-order integers straight from octets. `specHeader`,
`specQuestion`, `specRR` read the §4.1.1-§4.1.3 field frames at their mandated
octet offsets. Domain-name *decoding* (compression pointers, §4.1.4) is the
subject of a separate lane; here it is an oracle (`Dns.decodeName`) supplying the
label list and the octet count a name occupies — this module specifies the
fixed-field frame *around* the name. `parseMessage` is the RFC §4.1 whole-message
layout: header, then exactly `QDCOUNT` questions, then the three RR sections,
tiling the message with no trailing octets.

## The refinement theorems

`parseHeader_refines_spec`, `parseQuestion_refines_spec`, `parseRR_refines_spec`
prove the deployed `Dns.parse*` functions equal the independent spec on **every**
input (the count fields equal the network-order value of their exact wire octets;
every other field equals its wire bytes; the parser fails exactly when the message
is too short). `parseMessage_counts` proves the RFC §4.1 layout parser yields
**exactly** the header-declared counts. Non-vacuity: mis-reading the `QDCOUNT`
octet flips a concrete success into a failure (`count_is_load_bearing`), a
too-short message is rejected (`spec_rejects_short`), and dropping/adding a
question breaks the tiling (`extra_declared_question_fails`).

## The deployed resolver enforces the §4.1 message structure

`Reactor.DnsWire.resolve` — the function the reactor runs before honoring an upstream
connect — validates the full RFC §4.1 message structure before extracting an answer: it
routes through `Reactor.DnsWire.parseMessage`, which consumes exactly `QDCOUNT` questions
and `ANCOUNT`+`NSCOUNT`+`ARCOUNT` resource records and requires the sections to tile the
message with no trailing octets. `parseMessage_none_iff` proves that deployed whole-message
parser agrees, on rejection, with the RFC-faithful `parseMessage` here; from it,
`resolve_rejects_when_spec_rejects` shows any message the RFC parser rejects is rejected by
the deployed `resolve` too. `resolve_enforces_structure` witnesses this on a message with
four trailing junk octets (now rejected, no answer) and a message that lies about its
`QDCOUNT` (now rejected), while a well-formed response still resolves to its A-record
address. See the module tail.
-/

namespace DnsMessageCorrect

open Dns (Bytes Header Question RR)

/-! ## Network-order field readers (RFC 1035 §2.3.2 / §3: most significant octet first) -/

/-- A 16-bit field, most-significant octet first (network byte order). -/
def beU16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- A 32-bit field, most-significant octet first (network byte order). -/
def beU32 (a b c d : UInt8) : Nat :=
  a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat

/-! ## RFC 1035 §4.1.1 — the 12-octet header -/

/-- The six 16-bit header fields, as the spec reads them. -/
structure SpecHeader where
  id : Nat
  flags : Nat
  qdCount : Nat
  anCount : Nat
  nsCount : Nat
  arCount : Nat
  deriving DecidableEq, Repr

/-- **RFC 1035 §4.1.1, independently.** The header is 12 octets: `ID` at octets
0-1, the flags word at 2-3, then `QDCOUNT` 4-5, `ANCOUNT` 6-7, `NSCOUNT` 8-9,
`ARCOUNT` 10-11, each a network-order 16-bit field. A message shorter than 12
octets has no header. Returns the header and the octets it occupies (12). -/
def specHeader (msg : Bytes) : Option (SpecHeader × Nat) :=
  if 12 ≤ msg.length then
    some
      ({ id := beU16 (msg.getD 0 0) (msg.getD 1 0)
         flags := beU16 (msg.getD 2 0) (msg.getD 3 0)
         qdCount := beU16 (msg.getD 4 0) (msg.getD 5 0)
         anCount := beU16 (msg.getD 6 0) (msg.getD 7 0)
         nsCount := beU16 (msg.getD 8 0) (msg.getD 9 0)
         arCount := beU16 (msg.getD 10 0) (msg.getD 11 0) }, 12)
  else none

/-- Bridge the deployed `Dns.Header` into the spec's field view. -/
def toSpecHeader (h : Header) : SpecHeader :=
  ⟨h.id, h.flags, h.qdCount, h.anCount, h.nsCount, h.arCount⟩

/-- **Refinement (header).** The deployed `Dns.parseHeader`, mapped into the spec's
field view, equals `specHeader` on every input: each of the six header fields is
the network-order value of its exact mandated octets, and the parser succeeds
exactly when at least 12 octets are present. -/
theorem parseHeader_refines_spec (msg : Bytes) :
    (Dns.parseHeader msg).map (fun p => (toSpecHeader p.1, p.2)) = specHeader msg := by
  unfold Dns.parseHeader specHeader
  by_cases h : 12 ≤ msg.length
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-! ## RFC 1035 §4.1.2 — the question frame -/

structure SpecQuestion where
  qname : List (List UInt8)
  qtype : Nat
  qclass : Nat
  deriving DecidableEq, Repr

/-- **RFC 1035 §4.1.2, independently.** A question is a domain name (decoded by the
name oracle `Dns.decodeName`, which reports the octets the name occupies) followed
by a network-order 16-bit `QTYPE` and `QCLASS`. It needs the four fixed octets past
the name; short input fails. -/
def specQuestion (msg : Bytes) (off : Nat) : Option (SpecQuestion × Nat) :=
  match Dns.decodeName msg off with
  | .error _ => none
  | .ok d =>
    if off + d.consumed + 4 ≤ msg.length then
      some
        ({ qname := d.labels
           qtype := beU16 (msg.getD (off + d.consumed) 0) (msg.getD (off + d.consumed + 1) 0)
           qclass := beU16 (msg.getD (off + d.consumed + 2) 0)
                           (msg.getD (off + d.consumed + 3) 0) },
         d.consumed + 4)
    else none

def toSpecQuestion (q : Question) : SpecQuestion := ⟨q.qname, q.qtype, q.qclass⟩

/-- **Refinement (question).** The deployed `Dns.parseQuestion`, mapped into the
spec's view, equals `specQuestion` on every input and offset: `QTYPE`/`QCLASS`
equal the network-order value of their wire octets past the name, `QNAME` is the
decoded name, and the parser consumes name+4. -/
theorem parseQuestion_refines_spec (msg : Bytes) (off : Nat) :
    (Dns.parseQuestion msg off).map (fun p => (toSpecQuestion p.1, p.2)) = specQuestion msg off := by
  unfold Dns.parseQuestion specQuestion
  cases Dns.decodeName msg off with
  | error e => rfl
  | ok d =>
    dsimp only
    split <;> rfl

/-! ## RFC 1035 §4.1.3 — the resource-record frame -/

structure SpecRR where
  name : List (List UInt8)
  rrType : Nat
  rrClass : Nat
  ttl : Nat
  rdata : List UInt8
  deriving DecidableEq, Repr

/-- **RFC 1035 §4.1.3, independently.** An RR is a name (decoded by the oracle),
then network-order `TYPE` (16), `CLASS` (16), `TTL` (32), `RDLENGTH` (16), then
`RDLENGTH` octets of `RDATA`. It needs the 10 fixed octets, then the `RDATA`;
either shortfall fails. -/
def specRR (msg : Bytes) (off : Nat) : Option (SpecRR × Nat) :=
  match Dns.decodeName msg off with
  | .error _ => none
  | .ok d =>
    if off + d.consumed + 10 ≤ msg.length then
      if off + d.consumed + 10
          + beU16 (msg.getD (off + d.consumed + 8) 0) (msg.getD (off + d.consumed + 9) 0)
          ≤ msg.length then
        some
          ({ name := d.labels
             rrType := beU16 (msg.getD (off + d.consumed) 0) (msg.getD (off + d.consumed + 1) 0)
             rrClass := beU16 (msg.getD (off + d.consumed + 2) 0)
                             (msg.getD (off + d.consumed + 3) 0)
             ttl := beU32 (msg.getD (off + d.consumed + 4) 0)
                          (msg.getD (off + d.consumed + 5) 0)
                          (msg.getD (off + d.consumed + 6) 0)
                          (msg.getD (off + d.consumed + 7) 0)
             rdata := (msg.drop (off + d.consumed + 10)).take
                        (beU16 (msg.getD (off + d.consumed + 8) 0)
                               (msg.getD (off + d.consumed + 9) 0)) },
           d.consumed + 10
             + beU16 (msg.getD (off + d.consumed + 8) 0) (msg.getD (off + d.consumed + 9) 0))
      else none
    else none

def toSpecRR (r : RR) : SpecRR := ⟨r.name, r.rrType, r.rrClass, r.ttl, r.rdata⟩

/-- **Refinement (resource record).** The deployed `Dns.parseRR`, mapped into the
spec's view, equals `specRR` on every input and offset: `TYPE`/`CLASS`/`TTL`/
`RDLENGTH` equal the network-order value of their wire octets, `RDATA` is exactly
the `RDLENGTH` octets that follow, and the parser consumes name+10+`RDLENGTH`. -/
theorem parseRR_refines_spec (msg : Bytes) (off : Nat) :
    (Dns.parseRR msg off).map (fun p => (toSpecRR p.1, p.2)) = specRR msg off := by
  simp only [Dns.parseRR, specRR, toSpecRR, show Dns.be16 = beU16 from rfl,
             show Dns.be32 = beU32 from rfl]
  cases Dns.decodeName msg off with
  | error e => rfl
  | ok d =>
    dsimp only
    split <;> first | rfl | (split <;> rfl)

/-! ## RFC 1035 §4.1 — the whole-message structural invariant

The header declares `QDCOUNT` questions and `ANCOUNT`+`NSCOUNT`+`ARCOUNT` resource
records; the sections carry exactly those many entries, tiling the message. This
layout is folded from the deployed single-record parsers. -/

/-- Consume exactly `n` questions from `off`, threading the deployed
`Dns.parseQuestion`. Returns the questions and the new offset. -/
def takeQuestions (msg : Bytes) : Nat → Nat → Option (List Question × Nat)
  | off, 0 => some ([], off)
  | off, Nat.succ n =>
    match Dns.parseQuestion msg off with
    | none => none
    | some (q, c) =>
      match takeQuestions msg (off + c) n with
      | none => none
      | some (qs, off') => some (q :: qs, off')

/-- Consume exactly `n` resource records from `off`, threading the deployed
`Dns.parseRR`. Returns the records and the new offset. -/
def takeRRs (msg : Bytes) : Nat → Nat → Option (List RR × Nat)
  | off, 0 => some ([], off)
  | off, Nat.succ n =>
    match Dns.parseRR msg off with
    | none => none
    | some (r, c) =>
      match takeRRs msg (off + c) n with
      | none => none
      | some (rs, off') => some (r :: rs, off')

/-- The header plus the four sections' decoded entries. -/
structure MessageView where
  header : Header
  questions : List Question
  answers : List RR
  authority : List RR
  additional : List RR
  deriving DecidableEq, Repr

/-- **RFC 1035 §4.1 message layout.** Parse the header, then exactly `QDCOUNT`
questions, then `ANCOUNT`, `NSCOUNT`, `ARCOUNT` resource records in the three RR
sections, and require the sections to tile the message exactly (final offset =
length): the counts must equal the number of entries present, with no trailing
octets. -/
def parseMessage (msg : Bytes) : Option MessageView :=
  match Dns.parseHeader msg with
  | none => none
  | some (h, hn) =>
    match takeQuestions msg hn h.qdCount with
    | none => none
    | some (qs, o1) =>
      match takeRRs msg o1 h.anCount with
      | none => none
      | some (ans, o2) =>
        match takeRRs msg o2 h.nsCount with
        | none => none
        | some (aut, o3) =>
          match takeRRs msg o3 h.arCount with
          | none => none
          | some (add, o4) =>
            if o4 = msg.length then some ⟨h, qs, ans, aut, add⟩ else none

/-- `takeQuestions` returns exactly `n` questions. -/
theorem takeQuestions_length (msg : Bytes) :
    ∀ (n off : Nat) (qs : List Question) (o' : Nat),
      takeQuestions msg off n = some (qs, o') → qs.length = n := by
  intro n
  induction n with
  | zero =>
    intro off qs o' h
    simp only [takeQuestions, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hqs, _⟩ := h; subst hqs; rfl
  | succ n ih =>
    intro off qs o' h
    unfold takeQuestions at h
    cases hq : Dns.parseQuestion msg off with
    | none => rw [hq] at h; simp at h
    | some p =>
      obtain ⟨q, c⟩ := p
      rw [hq] at h; dsimp only at h
      cases ht : takeQuestions msg (off + c) n with
      | none => rw [ht] at h; simp at h
      | some p2 =>
        obtain ⟨qs2, o2⟩ := p2
        rw [ht] at h; dsimp only at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hqs, _⟩ := h; subst hqs
        rw [List.length_cons, ih (off + c) qs2 o2 ht]

/-- `takeRRs` returns exactly `n` resource records. -/
theorem takeRRs_length (msg : Bytes) :
    ∀ (n off : Nat) (rs : List RR) (o' : Nat),
      takeRRs msg off n = some (rs, o') → rs.length = n := by
  intro n
  induction n with
  | zero =>
    intro off rs o' h
    simp only [takeRRs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hrs, _⟩ := h; subst hrs; rfl
  | succ n ih =>
    intro off rs o' h
    unfold takeRRs at h
    cases hr : Dns.parseRR msg off with
    | none => rw [hr] at h; simp at h
    | some p =>
      obtain ⟨r, c⟩ := p
      rw [hr] at h; dsimp only at h
      cases ht : takeRRs msg (off + c) n with
      | none => rw [ht] at h; simp at h
      | some p2 =>
        obtain ⟨rs2, o2⟩ := p2
        rw [ht] at h; dsimp only at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hrs, _⟩ := h; subst hrs
        rw [List.length_cons, ih (off + c) rs2 o2 ht]

/-- **The count theorem (RFC §4.1).** A successfully parsed message has exactly the
header-declared number of entries in every section: `QDCOUNT` questions, `ANCOUNT`
answers, `NSCOUNT` authority records, `ARCOUNT` additional records. -/
theorem parseMessage_counts (msg : Bytes) (v : MessageView)
    (h : parseMessage msg = some v) :
    v.questions.length = v.header.qdCount
      ∧ v.answers.length = v.header.anCount
      ∧ v.authority.length = v.header.nsCount
      ∧ v.additional.length = v.header.arCount := by
  unfold parseMessage at h
  cases hh : Dns.parseHeader msg with
  | none => rw [hh] at h; simp at h
  | some ph =>
    obtain ⟨hd, hn⟩ := ph
    rw [hh] at h; dsimp only at h
    cases hq : takeQuestions msg hn hd.qdCount with
    | none => rw [hq] at h; simp at h
    | some pq =>
      obtain ⟨qs, o1⟩ := pq
      rw [hq] at h; dsimp only at h
      cases ha : takeRRs msg o1 hd.anCount with
      | none => rw [ha] at h; simp at h
      | some pa =>
        obtain ⟨ans, o2⟩ := pa
        rw [ha] at h; dsimp only at h
        cases hns : takeRRs msg o2 hd.nsCount with
        | none => rw [hns] at h; simp at h
        | some pns =>
          obtain ⟨aut, o3⟩ := pns
          rw [hns] at h; dsimp only at h
          cases har : takeRRs msg o3 hd.arCount with
          | none => rw [har] at h; simp at h
          | some par =>
            obtain ⟨add, o4⟩ := par
            rw [har] at h; dsimp only at h
            by_cases ho : o4 = msg.length
            · rw [if_pos ho] at h
              simp only [Option.some.injEq] at h
              subst h
              exact ⟨takeQuestions_length msg _ _ _ _ hq,
                     takeRRs_length msg _ _ _ _ ha,
                     takeRRs_length msg _ _ _ _ hns,
                     takeRRs_length msg _ _ _ _ har⟩
            · rw [if_neg ho] at h; simp at h

/-! ## Non-vacuity and concrete vectors -/

/-- A real wire-format DNS response for `up`: header (`QDCOUNT` 1, `ANCOUNT` 1),
one question `up IN A`, one answer `A` record `93.184.216.34` (TTL 60). 38 octets,
tiling exactly. -/
def msgUp : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0,
    0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0,
    0x00, 0x01, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x3C,
    0x00, 0x04,
    93, 184, 216, 34 ]

/-- The RFC-faithful decode of `msgUp`. -/
def msgUpView : MessageView :=
  ⟨⟨0x1234, 0x8180, 1, 1, 0, 0⟩,
   [⟨[[117, 112]], 1, 1⟩],
   [⟨[[117, 112]], 1, 1, 60, [93, 184, 216, 34]⟩],
   [], []⟩

/-- **Non-vacuity: a well-formed message parses to exactly its declared counts.**
The whole-message parser accepts `msgUp` and yields exactly one question and one
answer record — the `QDCOUNT`/`ANCOUNT` the header declares. -/
theorem parseMessage_msgUp : parseMessage msgUp = some msgUpView := by decide

/-- The counts read off the concrete decode: one question, one answer. -/
theorem msgUp_exact_counts :
    msgUpView.questions.length = 1 ∧ msgUpView.answers.length = 1 := by decide

/-- `msgUp` with a single octet changed: `QDCOUNT` bumped from 1 to 2. Every other
octet is identical. -/
def msgUpBadQd : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x02, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0,
    0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0,
    0x00, 0x01, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x3C,
    0x00, 0x04,
    93, 184, 216, 34 ]

/-- **Non-vacuity: the count is load-bearing.** Changing only the `QDCOUNT` octet
(1 → 2) flips the whole-message parse from success to failure: the message no
longer tiles under the declared count, so `parseMessage` rejects it. A parser that
mis-read the count — or dropped/ignored a declared question — could not exhibit
this success/failure split on two messages differing in one octet. -/
theorem count_is_load_bearing :
    parseMessage msgUp = some msgUpView ∧ parseMessage msgUpBadQd = none := by
  decide

/-- **Non-vacuity: extra declared question fails.** The RFC-faithful parser rejects
`msgUpBadQd` (declares 2 questions, carries 1) — a dropped/miscounted question does
not silently pass. -/
theorem extra_declared_question_fails : parseMessage msgUpBadQd = none := by decide

/-- The header spec reads `QDCOUNT` from octets 4-5, not any shifted pair: on `msgUp`
it is 1, whereas the network-order value of octets 5-6 is 256. -/
theorem spec_reads_qdcount_from_octets_4_5 :
    ((specHeader msgUp).map (fun p => p.1.qdCount)) = some 1
      ∧ beU16 (msgUp.getD 5 0) (msgUp.getD 6 0) = 256 := by decide

/-- **Non-vacuity: too-short input is rejected.** An 11-octet message has no header;
both the deployed parser and the spec return `none`. -/
theorem spec_rejects_short :
    Dns.parseHeader (List.replicate 11 0) = none ∧ specHeader (List.replicate 11 0) = none := by
  decide

/-! ## The deployed resolver enforces the §4.1 message structure

`Reactor.DnsWire.resolve` (the function the reactor actually runs before an upstream
connect) now routes through `Reactor.DnsWire.parseMessage`, which validates the full §4.1
layout: exactly `QDCOUNT` questions and `ANCOUNT`/`NSCOUNT`/`ARCOUNT` records, tiling the
message with no trailing octets. The section that follows binds that deployed behavior to
the RFC-faithful `parseMessage` here: the two whole-message parsers reject the same
messages (`parseMessage_none_iff`), so any message this RFC spec rejects, the deployed
`resolve` rejects too (`resolve_rejects_when_spec_rejects`). -/

/-- The deployed section-consuming folds equal the ones here: both thread the very same
`Dns.parseQuestion`. -/
theorem takeQuestions_eq (msg : Bytes) (n : Nat) :
    ∀ off, Reactor.DnsWire.takeQuestions msg off n = takeQuestions msg off n := by
  induction n with
  | zero => intro off; rfl
  | succ n ih =>
    intro off
    unfold Reactor.DnsWire.takeQuestions takeQuestions
    cases Dns.parseQuestion msg off with
    | none => rfl
    | some p =>
      obtain ⟨q, c⟩ := p
      simp only [ih]
      cases takeQuestions msg (off + c) n <;> rfl

/-- The deployed RR folds equal the ones here: both thread the very same `Dns.parseRR`. -/
theorem takeRRs_eq (msg : Bytes) (n : Nat) :
    ∀ off, Reactor.DnsWire.takeRRs msg off n = takeRRs msg off n := by
  induction n with
  | zero => intro off; rfl
  | succ n ih =>
    intro off
    unfold Reactor.DnsWire.takeRRs takeRRs
    cases Dns.parseRR msg off with
    | none => rfl
    | some p =>
      obtain ⟨r, c⟩ := p
      simp only [ih]
      cases takeRRs msg (off + c) n <;> rfl

/-- **The deployed whole-message parser rejects exactly what the RFC spec rejects.** The
deployed `Reactor.DnsWire.parseMessage` and the RFC-faithful `parseMessage` here make the
identical sequence of accept/reject decisions — same header, same section folds, same
final tiling check — so one returns `none` iff the other does. -/
theorem parseMessage_none_iff (msg : Bytes) :
    Reactor.DnsWire.parseMessage msg = none ↔ parseMessage msg = none := by
  unfold Reactor.DnsWire.parseMessage parseMessage
  cases Dns.parseHeader msg with
  | none => simp
  | some ph =>
    obtain ⟨h, hn⟩ := ph
    dsimp only
    rw [takeQuestions_eq msg h.qdCount hn]
    cases takeQuestions msg hn h.qdCount with
    | none => simp
    | some pq =>
      obtain ⟨qs, o1⟩ := pq
      dsimp only
      rw [takeRRs_eq msg h.anCount o1]
      cases takeRRs msg o1 h.anCount with
      | none => simp
      | some pa =>
        obtain ⟨ans, o2⟩ := pa
        dsimp only
        rw [takeRRs_eq msg h.nsCount o2]
        cases takeRRs msg o2 h.nsCount with
        | none => simp
        | some pns =>
          obtain ⟨aut, o3⟩ := pns
          dsimp only
          rw [takeRRs_eq msg h.arCount o3]
          cases takeRRs msg o3 h.arCount with
          | none => simp
          | some par =>
            obtain ⟨add, o4⟩ := par
            dsimp only
            by_cases ho : o4 = msg.length
            · rw [if_pos ho, if_pos ho]; simp
            · rw [if_neg ho, if_neg ho]; simp

/-- **The deployed resolver rejects every structurally-invalid message.** If the
RFC-faithful `parseMessage` rejects `msg` (mismatched counts or trailing octets), the
deployed `Reactor.DnsWire.resolve` yields no answer — it never dials a host off a message
whose §4.1 structure does not check. This is the general non-vacuity link behind the
concrete witnesses below. -/
theorem resolve_rejects_when_spec_rejects (host : List (List UInt8)) (msg : Bytes)
    (h : parseMessage msg = none) : Reactor.DnsWire.resolve host msg = none := by
  have hd : Reactor.DnsWire.parseMessage msg = none := (parseMessage_none_iff msg).mpr h
  simp only [Reactor.DnsWire.resolve, hd]

/-- `msgUp` with four trailing octets that belong to no section. -/
def msgUpTrailing : Bytes := msgUp ++ [0xDE, 0xAD, 0xBE, 0xEF]

/-- **The fix, witnessed — the deployed resolver now enforces the §4.1 structure.**
(a) A well-formed response still resolves to its A-record address `93.184.216.34`.
(b) The message with four trailing junk octets is now REJECTED (no answer): the deployed
`resolve` no longer accepts bytes past the last section.
(c) A message that lies about its `QDCOUNT` (declares 2, carries 1) is REJECTED.
Non-vacuity: (b) and (c) are *derived* from the RFC-faithful `parseMessage` rejecting those
messages (`resolve_rejects_when_spec_rejects`), so the deployed resolver's rejection is
exactly the RFC §4.1 structural check — not an accident of the fixed shape it used to
read. The old finding (deployed `resolve` accepting the trailing-junk message) no longer
holds. -/
theorem resolve_enforces_structure :
    Reactor.DnsWire.resolve Reactor.DnsWire.hostUp msgUp = some ⟨1572395042⟩
      ∧ Reactor.DnsWire.resolve Reactor.DnsWire.hostUp msgUpTrailing = none
      ∧ Reactor.DnsWire.resolve Reactor.DnsWire.hostUp msgUpBadQd = none
      ∧ parseMessage msgUpTrailing = none
      ∧ parseMessage msgUpBadQd = none := by
  refine ⟨by decide, ?_, ?_, by decide, by decide⟩
  · exact resolve_rejects_when_spec_rejects _ _ (by decide)
  · exact resolve_rejects_when_spec_rejects _ _ (by decide)

#print axioms parseHeader_refines_spec
#print axioms parseQuestion_refines_spec
#print axioms parseRR_refines_spec
#print axioms parseMessage_counts
#print axioms count_is_load_bearing
#print axioms parseMessage_none_iff
#print axioms resolve_rejects_when_spec_rejects
#print axioms resolve_enforces_structure

end DnsMessageCorrect
