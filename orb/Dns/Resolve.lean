import Dns.RData
import Dns.Encode
import Dns.Dnssec

/-!
# Response resolution (RFC 1035 §7.3 answer matching + §3.3.1 CNAME chase)

The extraction layer over the whole-message parse: given the query it sent, a
resolver must decide what a response *answers*. That is more than reading the
first answer record:

* **Response matching (RFC 1035 §7.3).** The response's ID must equal the
  query's, QR must be set (a query is not an answer to a query), the opcode
  must be QUERY, and the question section must echo the question asked
  (name, type, class). A truncated response (TC) must not be consumed as if
  complete, and a non-zero RCODE (SERVFAIL, NXDOMAIN, …) answers *nothing*
  even if the section counts are non-zero.

* **CNAME chase (RFC 1035 §3.3.1, §7 resolution).** When the query is not for
  CNAME itself and the answer section holds `owner CNAME target`, the records
  that answer the query are those owned by the *canonical* name at the end of
  the chain. The chase is fuel-bounded by the answer count, so a CNAME cycle
  terminates (each hop uses one unit of fuel) — the anti-loop discipline of
  the name decoder, carried up a level.

* **Section scan.** Every answer record of the queried type and class IN owned
  by the (chased) name contributes — not just the first record, and records of
  other types interleaved in the section (an RRSIG next to its A records, the
  CNAME itself) do not block extraction.

`answersOf` needs only the two byte strings that actually exist at a resolver:
the query it sent and the response it received.
-/

namespace Dns

/-- A decoded domain name: the label list. -/
abbrev Name := List (List UInt8)

/-! ## The EDNS extended RCODE (RFC 6891 §6.1.3)

The header RCODE is only the *low 4 bits* of the response code: the OPT
pseudo-record's TTL field carries the upper 8 bits. BADVERS (16) and
BADCOOKIE (23) have header-RCODE 0 — a matcher that reads only the header
would consume such an error response as a success. -/

/-- The OPT pseudo-record of a message, if any (RFC 6891 §6.1.1: it lives in
the additional section; a compliant message carries at most one). -/
def Msg.ednsOpt (m : Msg) : Option RRAt :=
  m.additional.find? (fun r => r.rr.rrType == 41)

/-- The upper 8 bits of the extended RCODE — OPT TTL bits 24..31. `0` when the
message carries no OPT record, which §6.1.3 defines to mean an unextended
RCODE. -/
def Msg.extRcodeHi (m : Msg) : Nat :=
  match m.ednsOpt with
  | none => 0
  | some r => r.rr.ttl / 16777216 % 256

/-- **RFC 6891 §6.1.3 extended RCODE**: upper 8 bits from OPT, low 4 bits from
the header. -/
def Msg.extendedRcode (m : Msg) : Nat := m.extRcodeHi * 16 + m.header.rcode

/-- The extended RCODE is a 12-bit value. -/
theorem Msg.extendedRcode_lt (m : Msg) : m.extendedRcode < 4096 := by
  have h1 : m.extRcodeHi < 256 := by
    unfold extRcodeHi
    split
    · omega
    · exact Nat.mod_lt _ (by omega)
  have h2 := Header.rcode_lt m.header
  unfold extendedRcode
  omega

/-- The extended RCODE's low 4 bits are exactly the header RCODE — the merge
extends, never contradicts, the header. -/
theorem Msg.extendedRcode_mod (m : Msg) : m.extendedRcode % 16 = m.header.rcode := by
  have := Header.rcode_lt m.header
  unfold extendedRcode
  omega

/-- Without an OPT record the extended RCODE *is* the header RCODE. -/
theorem Msg.extendedRcode_no_opt (m : Msg) (h : m.ednsOpt = none) :
    m.extendedRcode = m.header.rcode := by
  unfold Msg.extendedRcode Msg.extRcodeHi
  rw [h]
  simp

/-! ## Response matching (RFC 1035 §7.3) -/

/-- Does the parsed message answer a question `(host, qtype)` asked under
`qid`? ID match, QR set, opcode QUERY, not truncated, *extended* RCODE 0
(RFC 6891 §6.1.3 — a BADVERS/BADCOOKIE response has header-RCODE 0 and must
not match), and the question echoed (name compared case-insensitively per
RFC 1035 §2.3.3, class IN). -/
def matchesQuery (qid : Nat) (host : Name) (qtype : Nat) (m : Msg) : Bool :=
  m.header.id == qid
    && m.header.qr
    && m.header.opcode == 0
    && !m.header.tc
    && m.extendedRcode == 0
    && match m.questions with
       | [q] => nameEq q.qname host && q.qtype == qtype && q.qclass == 1
       | _ => false

/-! ## The CNAME chase (RFC 1035 §3.3.1) -/

/-- The CNAME target of a record owned by `owner` (class IN, owner compared
case-insensitively per RFC 1035 §2.3.3), decoded against the whole message so
a compressed target resolves. -/
def cnameHop (msg : Bytes) (ans : List RRAt) (owner : Name) : Option Name :=
  match ans.find? (fun r =>
      r.rr.rrClass == 1 && r.rr.rrType == 5 && nameEq r.rr.name owner) with
  | none => none
  | some r =>
    match typedRData msg r with
    | some (.cname target) => some target
    | _ => none

/-- Follow the CNAME chain from `owner` through the answer section. Fuel bounds
the hops (callers seed it with the answer count, which bounds any acyclic
chain); a CNAME *cycle* exhausts the fuel and stops — termination is
structural, not a timeout. -/
def chase (msg : Bytes) (ans : List RRAt) : Nat → Name → Name
  | 0, owner => owner
  | Nat.succ fuel, owner =>
    match cnameHop msg ans owner with
    | some target => chase msg ans fuel target
    | none => owner

theorem chase_total (msg : Bytes) (ans : List RRAt) (fuel : Nat) (owner : Name) :
    ∃ r, chase msg ans fuel owner = r := ⟨_, rfl⟩

/-- A chase with no matching CNAME record is the identity. -/
theorem chase_no_cname (msg : Bytes) (ans : List RRAt) (fuel : Nat) (owner : Name)
    (h : cnameHop msg ans owner = none) : chase msg ans fuel owner = owner := by
  cases fuel with
  | zero => rfl
  | succ fuel => unfold chase; rw [h]

/-! ## The section scan -/

/-- All typed RDATA of type `qtype`, class IN, owned by `owner` (owner
compared case-insensitively per RFC 1035 §2.3.3), across the whole answer
section — not just the first record. -/
def collect (msg : Bytes) (qtype : Nat) (owner : Name) (ans : List RRAt) : List RData :=
  ans.filterMap fun r =>
    if r.rr.rrClass == 1 && r.rr.rrType == qtype && nameEq r.rr.name owner then
      typedRData msg r
    else none

/-- **Scan soundness.** Everything `collect` returns came from an answer
record of exactly the queried type and class IN, owned by the queried name
(equal in RFC 4034 §6.2 canonical form — the §2.3.3 comparison), through the
real typed reader. -/
theorem collect_sound (msg : Bytes) (qtype : Nat) (owner : Name) (ans : List RRAt)
    (d : RData) (hd : d ∈ collect msg qtype owner ans) :
    ∃ r ∈ ans, r.rr.rrClass = 1 ∧ r.rr.rrType = qtype
      ∧ canonName r.rr.name = canonName owner
      ∧ typedRData msg r = some d := by
  unfold collect at hd
  rcases List.mem_filterMap.mp hd with ⟨r, hr, hf⟩
  refine ⟨r, hr, ?_⟩
  by_cases hc : (r.rr.rrClass == 1 && r.rr.rrType == qtype && nameEq r.rr.name owner) = true
  · rw [if_pos hc] at hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact ⟨h1, h2, (nameEq_iff _ _).mp h3, hf⟩
  · rw [if_neg hc] at hf
    exact absurd hf (by simp)

/-! ## The resolution -/

/-- **Answer extraction against a validated response.** Parse the response
with the whole-message parser; check it matches the query (RFC 1035 §7.3);
chase CNAMEs from the queried name unless CNAME itself was asked; then collect
every record of the queried type/class owned by the canonical name. `[]` when
the response is malformed, mismatched, truncated, an error, or has no
answers of the queried type. -/
def answersFor (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes) : List RData :=
  match parseMsg resp with
  | none => []
  | some m =>
    if matchesQuery qid host qtype m then
      let owner := if qtype == 5 then host else chase resp m.answers m.answers.length host
      collect resp qtype owner m.answers
    else []

/-- **Query-driven extraction.** Everything a resolver holds is the query it
sent and the response it received; this reads the ID and the question from the
real query bytes and extracts the response's answers to exactly that
question. `[]` if the query bytes do not parse as a one-question query. -/
def answersOf (query resp : Bytes) : List RData :=
  match parseMsg query with
  | none => []
  | some qm =>
    match qm.questions with
    | [q] =>
      if !qm.header.qr && q.qclass == 1 then
        answersFor qm.header.id q.qname q.qtype resp
      else []
    | _ => []

/-- The resolved IPv4 addresses (A answers, RFC 1035 §3.4.1), after matching
and CNAME chase. -/
def resolveA (query resp : Bytes) : List Nat :=
  (answersOf query resp).filterMap fun
    | .a addr => some addr
    | _ => none

/-- The resolved IPv6 addresses (AAAA answers, RFC 3596), after matching and
CNAME chase. -/
def resolveAAAA (query resp : Bytes) : List Nat :=
  (answersOf query resp).filterMap fun
    | .aaaa addr => some addr
    | _ => none

theorem answersOf_total (query resp : Bytes) : ∃ r, answersOf query resp = r := ⟨_, rfl⟩

/-! ## Soundness: what an extracted answer implies about the wire bytes -/

/-- **Extraction soundness.** A non-`[]` member of `answersFor` certifies, of
the real response bytes: they parse as a whole RFC 1035 message; the header
carries the query's ID, QR set, opcode QUERY, TC clear; the *extended* RCODE
(RFC 6891 §6.1.3, OPT upper bits merged) is 0 — hence so is the header RCODE;
the question echoes the query (name equal in canonical form, RFC 1035
§2.3.3); and the value came from an answer record of the queried type, class
IN, through the typed reader. A response that is a query, an error (BADVERS
included), truncated, or mismatched contributes nothing. -/
theorem answersFor_sound (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (d : RData) (hd : d ∈ answersFor qid host qtype resp) :
    ∃ m, parseMsg resp = some m
      ∧ m.header.id = qid
      ∧ m.header.qr = true
      ∧ m.header.opcode = 0
      ∧ m.header.tc = false
      ∧ m.extendedRcode = 0
      ∧ m.header.rcode = 0
      ∧ (∃ q, m.questions = [q] ∧ canonName q.qname = canonName host
          ∧ q.qtype = qtype ∧ q.qclass = 1)
      ∧ (∃ r ∈ m.answers, r.rr.rrClass = 1 ∧ r.rr.rrType = qtype
          ∧ typedRData resp r = some d) := by
  unfold answersFor at hd
  split at hd
  · simp at hd
  · rename_i m hm
    split at hd
    · rename_i hmatch
      refine ⟨m, hm, ?_⟩
      unfold matchesQuery at hmatch
      simp only [Bool.and_eq_true] at hmatch
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hmatch
      have hx : m.extendedRcode = 0 := by simpa using h5
      have hr0 : m.header.rcode = 0 := by
        have := Msg.extendedRcode_mod m
        omega
      refine ⟨by simpa using h1, by simpa using h2, by simpa using h3,
              by simpa using h4, hx, hr0, ?_, ?_⟩
      · -- the echoed question
        split at h6
        · rename_i q heq
          simp only [Bool.and_eq_true, beq_iff_eq] at h6
          obtain ⟨⟨hq1, hq2⟩, hq3⟩ := h6
          exact ⟨q, heq, (nameEq_iff _ _).mp hq1, hq2, hq3⟩
        · exact absurd h6 (by simp)
      · -- the record behind the value
        obtain ⟨r, hr, hc, ht, _, hv⟩ := collect_sound resp qtype _ m.answers d hd
        exact ⟨r, hr, hc, ht, hv⟩
    · simp at hd

/-- A response with a non-zero *extended* RCODE answers nothing — this covers
BADVERS (16) and BADCOOKIE (23), whose header RCODE is 0. -/
theorem answersFor_extRcode (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (m : Msg) (hm : parseMsg resp = some m) (hrc : m.extendedRcode ≠ 0) :
    answersFor qid host qtype resp = [] := by
  have hfalse : matchesQuery qid host qtype m = false := by
    unfold matchesQuery
    have hb : (m.extendedRcode == 0) = false := by
      simp [hrc]
    simp [hb]
  unfold answersFor
  rw [hm]
  simp [hfalse]

/-- An error response (non-zero header RCODE) answers nothing, whatever its
counts say — the header RCODE survives in the low bits of the merge. -/
theorem answersFor_rcode (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (m : Msg) (hm : parseMsg resp = some m) (hrc : m.header.rcode ≠ 0) :
    answersFor qid host qtype resp = [] := by
  refine answersFor_extRcode qid host qtype resp m hm ?_
  intro h0
  exact hrc (by have := Msg.extendedRcode_mod m; omega)

/-- A truncated response (TC set, RFC 1035 §4.1.1) answers nothing: the
transport-level retry (§4.2.2) is modeled in `Dns.Transport`, never a partial
consume. -/
theorem answersFor_tc (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (m : Msg) (hm : parseMsg resp = some m) (htc : m.header.tc = true) :
    answersFor qid host qtype resp = [] := by
  have hfalse : matchesQuery qid host qtype m = false := by
    unfold matchesQuery
    simp [htc]
  unfold answersFor
  rw [hm]
  simp [hfalse]

/-- A message with QR clear (a query) answers nothing. -/
theorem answersFor_qr (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (m : Msg) (hm : parseMsg resp = some m) (hqr : m.header.qr = false) :
    answersFor qid host qtype resp = [] := by
  have hfalse : matchesQuery qid host qtype m = false := by
    unfold matchesQuery
    simp [hqr]
  unfold answersFor
  rw [hm]
  simp [hfalse]

/-- An ID-mismatched response answers nothing. -/
theorem answersFor_id (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (m : Msg) (hm : parseMsg resp = some m) (hid : m.header.id ≠ qid) :
    answersFor qid host qtype resp = [] := by
  have hfalse : matchesQuery qid host qtype m = false := by
    unfold matchesQuery
    have hb : (m.header.id == qid) = false := by
      simp [hid]
    simp [hb]
  unfold answersFor
  rw [hm]
  simp [hfalse]

/-! ## Kernel-checked vectors: the deepened semantics on concrete wire bytes

Everything below runs the REAL parsers on hand-laid wire messages by `decide`
(names uncompressed, so the whole pipeline reduces). -/

/-- The query: `up IN A`, id 0x1234, RD (flags 0x0100). -/
def qUp : Bytes :=
  [ 0x12, 0x34, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01 ]

/-- A response with a CNAME chain: `up CNAME cn` then `cn A 93.184.216.34`,
answer order CNAME-first — the shape a first-answer-only reader fails on. -/
def rUpCname : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    -- up CNAME cn (rdata: uncompressed name "cn", 4 octets)
    2, 117, 112, 0, 0x00, 0x05, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    2, 99, 110, 0,
    -- cn A 93.184.216.34
    2, 99, 110, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

/-- **CNAME chase, on the wire.** The A record is owned by the *canonical*
name, not the queried name, and sits second in the section; the chase finds
it. `93.184.216.34` = 1572395042. -/
theorem resolveA_cname_chain : resolveA qUp rUpCname = [1572395042] := by decide

/-- An AAAA response for `up`: one 16-octet answer, `2606:4700:10::ac42:93f3`. -/
def qUp6 : Bytes :=
  [ 0x12, 0x35, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x1C, 0x00, 0x01 ]

def rUp6 : Bytes :=
  [ 0x12, 0x35, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x1C, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x1C, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x10,
    0x26, 0x06, 0x47, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xAC, 0x42, 0x93, 0xF3 ]

/-- **AAAA extraction (RFC 3596).** The 16-octet RDATA reads as the 128-bit
address. -/
theorem resolveAAAA_up :
    resolveAAAA qUp6 rUp6 = [50543257672079214217829785593155064819] := by decide

/-- A SERVFAIL response (flags 0x8182, RCODE 2) with a *lying* nonempty answer
section: extraction refuses it. -/
def rUpServfail : Bytes :=
  [ 0x12, 0x34, 0x81, 0x82, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

theorem resolveA_servfail : resolveA qUp rUpServfail = [] := by decide

/-- A response whose ID does not match the query answers nothing. -/
def rUpWrongId : Bytes :=
  [ 0xDE, 0xAD, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

theorem resolveA_wrong_id : resolveA qUp rUpWrongId = [] := by decide

/-- A *query* echoed back (QR clear) is not an answer. -/
theorem resolveA_echo : resolveA qUp qUp = [] := by decide

/-- Interleaved non-A records (here an RRSIG-typed record, type 46) do not
block extraction of BOTH surrounding A records: the scan reads the section,
not the first record. -/
def rUpRrsigMix : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    -- up RRSIG (type 46, minimal 20-octet rdata: 18 fixed + root signer + 1 sig)
    2, 117, 112, 0, 0x00, 0x2E, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x14,
    0x00, 0x01, 13, 1, 0x00, 0x00, 0x00, 0x3C,
    0x60, 0x00, 0x00, 0x00, 0x5F, 0x00, 0x00, 0x00, 0x30, 0x39,
    0, 0xAB,
    -- up A 93.184.216.34
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34,
    -- up A 10.0.0.7
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    10, 0, 0, 7 ]

theorem resolveA_scans_section :
    resolveA qUp rUpRrsigMix = [1572395042, 167772167] := by decide

/-- An EDNS response whose OPT record is benign (extended RCODE 0): the OPT in
the additional section does not block extraction. -/
def rUpEdns : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34,
    -- OPT: root, type 41, class 4096 (udp payload), ttl 0, rdlen 0
    0, 0x00, 0x29, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]

theorem resolveA_edns_ok : resolveA qUp rUpEdns = [1572395042] := by decide

/-- **BADVERS is refused (RFC 6891 §6.1.3).** Same message, but the OPT TTL's
top octet is 1: header RCODE is still 0, the merged extended RCODE is 16
(BADVERS) — extraction consumes nothing, even though an answer record is
present. A header-only RCODE check would wrongly accept this response. -/
def rUpBadvers : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34,
    -- OPT with extended-RCODE upper bits 0x01 → merged RCODE 16 = BADVERS
    0, 0x00, 0x29, 0x10, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00 ]

theorem resolveA_badvers_refused : resolveA qUp rUpBadvers = [] := by decide

/-- The merged RCODE of that response really is BADVERS = 16. -/
example :
    (parseMsg rUpBadvers).map Msg.extendedRcode = some 16
      ∧ (parseMsg rUpBadvers).map (fun m => m.header.rcode) = some 0 := by decide

/-- **Case-insensitive extraction (RFC 1035 §2.3.3).** The query asks for
`UP`; the response echoes the question and owns the answer as `up`. Byte-exact
comparison extracts nothing here; the §2.3.3 comparison extracts the
address. -/
def qUpCase : Bytes :=
  [ 0x12, 0x37, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    2, 85, 80, 0, 0x00, 0x01, 0x00, 0x01 ]

def rUpCase : Bytes :=
  [ 0x12, 0x37, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

theorem resolveA_case_insensitive : resolveA qUpCase rUpCase = [1572395042] := by decide

/-- The case fold is not a wildcard: a genuinely different name still
extracts nothing. -/
def qDn : Bytes :=
  [ 0x12, 0x37, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    2, 100, 110, 0, 0x00, 0x01, 0x00, 0x01 ]

theorem resolveA_case_not_wildcard : resolveA qDn rUpCase = [] := by decide

end Dns
