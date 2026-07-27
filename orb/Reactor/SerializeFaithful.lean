/-
Reactor.SerializeFaithful — the EGRESS dual of parse-faithfulness.

`Reactor/Serialize.lean` defines the DEPLOYED response serializer `serialize`
(leanc-compiled, run inside `drorbServe` on the io_uring/kqueue/blocking paths;
`Reactor/SerializeFast.lean` installs the byte-identical flat-head twin as its
compiled implementation via `serialize_eq_fast`). It already proves the framing
DECOMPOSITION (`serialize_framing`) and `Content-Length := body.length` by
construction. What it left open — the G3-egress gap in
`docs/engine/review/ENGINE-ASSURANCE-STORY.md` — is the DUAL of the ingress
`Arena.Parse.parse_faithful` / `Reactor.Config.deployed_request_faithful`
theorems: whether the egress bytes are the *faithful RFC-7230 encoding* of the
`Response` structure (status-line + header-block + blank line + body), and
whether that encoding is *reversible* (distinct well-formed responses ⇒ distinct
wire bytes), so the deployed engine's OUTPUT is proven, not merely well-typed.

This file closes it, additively (it does not touch `serialize` /
`serialize_eq_fast`):

* `serialize_faithful` — `serialize resp` is EXACTLY `rfcStatusLine resp ++
  rfcHeaderBlock resp ++ CRLF ++ resp.body`, where the status-line renders as
  `HTTP/1.1 SP code SP reason CRLF`, each header field as `name ": " value
  CRLF`, and the derived `Content-Length` field carries `natToDec body.length`.
  A faithful ENCODE: every wire byte is an RFC-7230 rendering of a Response
  field, in RFC order.

* `serialize_injective` — for WELL-FORMED responses (`Response.Wf`: header
  names carry no CR/LF/colon, header values and the reason phrase carry no
  CR/LF — the RFC 7230 §3.2 field discipline), `serialize` is INJECTIVE: equal
  wire bytes force equal status, reason, headers, and body. This is the egress
  round-trip guarantee — the wire uniquely determines the Response — dual to the
  request-line round-trip `parse_faithful` proves on ingress. (A full
  `deserialize (serialize resp) = resp` awaits a response *parser*; the deployed
  parser is request-shaped, so injectivity is the standalone egress dual and the
  round-trip composes when a verified response reader lands.)

* `serialize_response_splitting` — the REAL FINDING. `Response.headers` is
  `List (Bytes × Bytes)` with NO construction-time CR/LF ban, and `serialize`
  neither escapes nor rejects: a header value carrying `CR LF` is rendered
  VERBATIM, forging extra header lines on the wire (HTTP response-splitting —
  the egress analogue of the ingress `parse_rejects_ctl_in_value`). Witnessed
  concretely: two DISTINCT responses whose `serialize` outputs are byte-equal.
  So injectivity holds exactly on the `Wf` domain, and egress safety is an
  obligation on whatever upstream produces the `Response` (`Wf`-maintenance),
  NOT provided by the serializer.

The digit facts (`natToDec` is all ASCII digits, and `dval` inverts it) are
reused from `Proto.Dec` — `Reactor.natToDec` is definitionally
`Proto.Dec.natToDec` (both `(Nat.repr n).toUTF8.toList`).
-/
import Reactor.Serialize
import Proto.Decimal

namespace Reactor

open Proto (Bytes)

/-! ## Digit facts for `natToDec`, lifted from `Proto.Dec` (defeq bridge) -/

/-- Every byte of `natToDec n` is an ASCII decimal digit (48–57). Lifted from
`Proto.Dec.natToDec_isDigit`; `Reactor.natToDec` is defeq to `Proto.Dec.natToDec`. -/
theorem natToDec_isDigit (n : Nat) (b : UInt8) (hb : b ∈ natToDec n) :
    48 ≤ b.toNat ∧ b.toNat ≤ 57 :=
  Proto.Dec.natToDec_isDigit n b hb

/-- A byte outside the ASCII-digit range never appears in `natToDec n`. -/
theorem natToDec_notMem (b : UInt8) (n : Nat) (hb : b.toNat < 48 ∨ 57 < b.toNat) :
    b ∉ natToDec n := by
  intro hm
  obtain ⟨h1, h2⟩ := natToDec_isDigit n b hm
  omega

theorem natToDec_no13 (n : Nat) : (13 : UInt8) ∉ natToDec n :=
  natToDec_notMem 13 n (by decide)

theorem natToDec_no10 (n : Nat) : (10 : UInt8) ∉ natToDec n :=
  natToDec_notMem 10 n (by decide)

theorem natToDec_no32 (n : Nat) : (32 : UInt8) ∉ natToDec n :=
  natToDec_notMem 32 n (by decide)

/-- `natToDec` is injective: `dval 0 ∘ natToDec = id` (`Proto.Dec.dval_natToDec`)
is a left inverse. -/
theorem natToDec_inj {a b : Nat} (h : natToDec a = natToDec b) : a = b := by
  have ha : Proto.Dec.dval 0 (natToDec a) = a := Proto.Dec.dval_natToDec a
  have hb : Proto.Dec.dval 0 (natToDec b) = b := Proto.Dec.dval_natToDec b
  rw [h, hb] at ha
  exact ha.symm

/-! ## A separator-split lemma: peel a byte the left piece never contains -/

/-- **`sep_split`.** If the separator byte `c` occurs in neither `a` nor `a'`,
then from `a ++ c :: r = a' ++ c :: r'` the prefixes and the tails coincide.
(The first `c` in each side is at the boundary, so the split point is forced.) -/
theorem sep_split {c : UInt8} : ∀ {a a' r r' : Bytes},
    c ∉ a → c ∉ a' → a ++ (c :: r) = a' ++ (c :: r') → a = a' ∧ r = r' := by
  intro a
  induction a with
  | nil =>
    intro a' r r' _ ha' h
    cases a' with
    | nil => simp only [List.nil_append, List.cons.injEq, true_and] at h; exact ⟨rfl, h⟩
    | cons x t =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [h.1]; simp : c ∈ x :: t) ha'
  | cons x t ih =>
    intro a' r r' ha ha' h
    cases a' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [← h.1]; simp : c ∈ x :: t) ha
    | cons y s =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxy, htl⟩ := h
      have ha2 : c ∉ t := fun hc => ha (List.mem_cons_of_mem x hc)
      have ha'2 : c ∉ s := fun hc => ha' (List.mem_cons_of_mem y hc)
      obtain ⟨ht, hr⟩ := ih ha2 ha'2 htl
      exact ⟨by rw [hxy, ht], hr⟩

/-- `a ++ [x] = b ++ [x] → a = b`. -/
theorem append_snoc_inj {α} {a b : List α} {x : α} (h : a ++ [x] = b ++ [x]) : a = b := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.cons.injEq, true_and] at hr
  calc a = a.reverse.reverse := (List.reverse_reverse a).symm
    _ = b.reverse.reverse := by rw [hr]
    _ = b := List.reverse_reverse b

/-! ## Well-formed responses: the RFC 7230 §3.2 field discipline -/

/-- No CR (13) and no LF (10): the line discipline that makes a rendered line
unambiguous (a bare CR/LF in a field would forge a line break on the wire). -/
def NoCRLF (bs : Bytes) : Prop := (13 : UInt8) ∉ bs ∧ (10 : UInt8) ∉ bs

/-- A single header field is well-formed: the NAME carries no CR, LF, or colon
(RFC 7230 §3.2 field-name is a colon-free token), and the VALUE carries no
CR/LF. Exactly the conditions under which `serialize`'s rendered line reverses. -/
def HdrOK (e : Bytes × Bytes) : Prop :=
  NoCRLF e.1 ∧ (58 : UInt8) ∉ e.1 ∧ NoCRLF e.2

/-- A well-formed `Response`: reason phrase CR/LF-free, every caller header
`HdrOK`. (The derived `Content-Length` field is well-formed by construction —
see `allHeaders_HdrOK`.) -/
structure Wf (r : Response) : Prop where
  reasonSafe : NoCRLF r.reason
  hdrOK : ∀ e ∈ r.headers, HdrOK e

/-! ## Header-line lemmas -/

/-- A well-formed header line contains no CR. -/
theorem headerLine_no13 {e : Bytes × Bytes} (h : HdrOK e) : (13 : UInt8) ∉ headerLine e := by
  intro hm
  rw [headerLine] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact h.1.1 hm
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
  · exact h.2.2.1 hm

/-- A well-formed header line is non-empty and its first byte is not CR (the
name's first byte, or the colon if the name is empty). -/
theorem headerLine_cons_ne13 {e : Bytes × Bytes} (h : HdrOK e) :
    ∃ c l, headerLine e = c :: l ∧ c ≠ (13 : UInt8) := by
  obtain ⟨n, v⟩ := e
  rw [headerLine]
  cases n with
  | nil => exact ⟨58, 32 :: v, by simp, by decide⟩
  | cons c t =>
    refine ⟨c, (t ++ [58, 32]) ++ v, by simp, ?_⟩
    intro hc
    exact h.1.1 (List.mem_cons.mpr (Or.inl hc.symm))

/-- **`headerLine` is injective** on well-formed fields: the rendered `name ": "
value` uniquely determines the name/value pair (name is colon-free ⇒ the first
colon is the delimiter). -/
theorem headerLine_inj {e f : Bytes × Bytes} (he : HdrOK e) (hf : HdrOK f)
    (h : headerLine e = headerLine f) : e = f := by
  rw [headerLine, headerLine, List.append_assoc, List.append_assoc] at h
  simp only [List.cons_append, List.nil_append] at h
  obtain ⟨h1, h2⟩ := sep_split he.2.1 hf.2.1 h
  injection h2 with _ h3
  obtain ⟨e1, e2⟩ := e
  obtain ⟨f1, f2⟩ := f
  simp only at h1 h3
  rw [h1, h3]

/-! ## The RFC-7230 message rendering (faithful ENCODE) -/

/-- RFC 7230 §3.1.2 status-line WITH its terminating CRLF:
`HTTP/1.1 SP code SP reason CRLF`. -/
def rfcStatusLine (r : Response) : Bytes := statusLineOf r ++ crlf

/-- One RFC 7230 §3.2 header-field WITH its terminating CRLF: `name ": " value CRLF`. -/
def rfcHeaderField (nv : Bytes × Bytes) : Bytes := headerLine nv ++ crlf

/-- The RFC header block: each field terminated by its own CRLF, the derived
`Content-Length` field included last. -/
def rfcHeaderBlock (r : Response) : Bytes :=
  ((allHeaders (build r)).map rfcHeaderField).flatten

/-- `renderHeaders` joins with CRLFs *between* lines; adding one trailing CRLF
per non-empty list yields the per-field-terminated block. -/
theorem renderHeaders_snoc_crlf :
    ∀ (hs : List (Bytes × Bytes)), hs ≠ [] →
      renderHeaders hs ++ crlf = (hs.map rfcHeaderField).flatten := by
  intro hs
  induction hs with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    cases t with
    | nil =>
      simp [renderHeaders, rfcHeaderField, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil]
    | cons b s =>
      have ihs : renderHeaders (b :: s) ++ crlf = ((b :: s).map rfcHeaderField).flatten :=
        ih (by simp)
      calc renderHeaders (a :: b :: s) ++ crlf
          = headerLine a ++ crlf ++ renderHeaders (b :: s) ++ crlf := by
              simp only [renderHeaders]
        _ = (headerLine a ++ crlf) ++ (renderHeaders (b :: s) ++ crlf) := by
              simp only [List.append_assoc]
        _ = (headerLine a ++ crlf) ++ ((b :: s).map rfcHeaderField).flatten := by rw [ihs]
        _ = ((a :: b :: s).map rfcHeaderField).flatten := by
              simp [rfcHeaderField, List.map_cons, List.flatten_cons]

/-- The rendered header list is never empty (the derived `Content-Length` field
is always appended). -/
theorem allHeaders_ne_nil (r : Response) : allHeaders (build r) ≠ [] := by
  simp [allHeaders]

/-- **`serialize_faithful` — egress bytes are the RFC-7230 encoding.** The
deployed serializer emits EXACTLY `status-line CRLF · (header-field CRLF)* ·
CRLF · body`: `rfcStatusLine` is `HTTP/1.1 SP code SP reason CRLF`,
`rfcHeaderBlock` is each header field `name ": " value CRLF` (the derived
`Content-Length: <body.length>` field last), then the blank-line separator and
the body. Every wire byte is an RFC rendering of a `Response` field, in RFC
order — the egress dual of `Arena.Parse.parse_faithful`. -/
theorem serialize_faithful (r : Response) :
    serialize r = rfcStatusLine r ++ rfcHeaderBlock r ++ crlf ++ r.body := by
  rw [serialize_framing]
  unfold rfcStatusLine rfcHeaderBlock headerBlockOf
  rw [← renderHeaders_snoc_crlf (allHeaders (build r)) (allHeaders_ne_nil r)]
  simp only [List.append_assoc]

/-! ## Status-line injectivity -/

/-- A well-formed status line contains no CR. -/
theorem statusLine_no13 (r : Response) (w : Wf r) : (13 : UInt8) ∉ statusLineOf r := by
  intro hm
  simp only [statusLineOf, statusLine, build, http11] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with h | h | h | h | h | h | h | h <;> exact absurd h (by decide)
        · simp only [List.mem_singleton] at hm; exact absurd hm (by decide)
      · exact natToDec_no13 r.status hm
    · simp only [List.mem_singleton] at hm; exact absurd hm (by decide)
  · exact w.reasonSafe.1 hm

/-- **The status line determines status and reason.** `HTTP/1.1 SP` is fixed,
`natToDec status` is space-free (digits), so the first space after it delimits
the reason. -/
theorem statusLine_inj (r1 r2 : Response) (h : statusLineOf r1 = statusLineOf r2) :
    r1.status = r2.status ∧ r1.reason = r2.reason := by
  simp only [statusLineOf, statusLine, build, http11, List.append_assoc, List.cons_append,
    List.nil_append, List.cons.injEq, true_and, and_true] at h
  obtain ⟨hd, hr⟩ := sep_split (natToDec_no32 r1.status) (natToDec_no32 r2.status) h
  exact ⟨natToDec_inj hd, hr⟩

/-! ## The header-block round-trip (the reversal core) -/

/-- The tail of `renderHeaders` after its first line: empty for a singleton,
else `CRLF ++ renderHeaders rest`. -/
def renderHeadersTail : List (Bytes × Bytes) → Bytes
  | [] => []
  | f :: t => crlf ++ renderHeaders (f :: t)

theorem renderHeaders_cons_eq (e : Bytes × Bytes) (rest : List (Bytes × Bytes)) :
    renderHeaders (e :: rest) = headerLine e ++ renderHeadersTail rest := by
  cases rest with
  | nil => simp [renderHeaders, renderHeadersTail]
  | cons f t => simp [renderHeaders, renderHeadersTail, List.append_assoc]

/-- **The header block reverses.** Two non-empty well-formed header lists whose
renderings (followed by the blank-line separator and a body) agree byte-for-byte
are the same list, over the same body. The blank line begins with CR while every
header line's first byte is not CR — so a length mismatch is impossible, and the
lists are peeled in lockstep. -/
theorem hdr_rt : ∀ (hs1 hs2 : List (Bytes × Bytes)) (b1 b2 : Bytes),
    (∀ e ∈ hs1, HdrOK e) → (∀ e ∈ hs2, HdrOK e) → hs1 ≠ [] → hs2 ≠ [] →
    renderHeaders hs1 ++ 13 :: 10 :: 13 :: 10 :: b1
      = renderHeaders hs2 ++ 13 :: 10 :: 13 :: 10 :: b2 →
    hs1 = hs2 ∧ b1 = b2 := by
  intro hs1
  induction hs1 with
  | nil => intro _ _ _ _ _ hne1 _; exact absurd rfl hne1
  | cons e1 rest1 ih =>
    intro hs2 b1 b2 hok1 hok2 _ hne2 h
    cases hs2 with
    | nil => exact absurd rfl hne2
    | cons e2 rest2 =>
      have he1 : HdrOK e1 := hok1 e1 (by simp)
      have he2 : HdrOK e2 := hok2 e2 (by simp)
      rw [renderHeaders_cons_eq, renderHeaders_cons_eq, List.append_assoc, List.append_assoc] at h
      cases rest1 with
      | nil =>
        cases rest2 with
        | nil =>
          simp only [renderHeadersTail, List.nil_append] at h
          obtain ⟨hln, htl⟩ := sep_split (headerLine_no13 he1) (headerLine_no13 he2) h
          have heq : e1 = e2 := headerLine_inj he1 he2 hln
          exact ⟨by rw [heq], by simpa using htl⟩
        | cons f2 t2 =>
          have hf2 : HdrOK f2 := hok2 f2 (by simp)
          simp only [renderHeadersTail, crlf, List.nil_append, List.cons_append,
            List.append_assoc] at h
          obtain ⟨_, htl⟩ := sep_split (headerLine_no13 he1) (headerLine_no13 he2) h
          exfalso
          injection htl with _ htl2
          obtain ⟨c, l, hc, hcne⟩ := headerLine_cons_ne13 hf2
          rw [renderHeaders_cons_eq, hc] at htl2
          simp only [List.cons_append] at htl2
          injection htl2 with hc13 _
          exact hcne hc13.symm
      | cons f1 t1 =>
        cases rest2 with
        | nil =>
          have hf1 : HdrOK f1 := hok1 f1 (by simp)
          simp only [renderHeadersTail, crlf, List.nil_append, List.cons_append,
            List.append_assoc] at h
          obtain ⟨_, htl⟩ := sep_split (headerLine_no13 he1) (headerLine_no13 he2) h
          exfalso
          injection htl with _ htl2
          obtain ⟨c, l, hc, hcne⟩ := headerLine_cons_ne13 hf1
          rw [renderHeaders_cons_eq, hc] at htl2
          simp only [List.cons_append] at htl2
          injection htl2 with hc13 _
          exact hcne hc13
        | cons f2 t2 =>
          simp only [renderHeadersTail, crlf, List.cons_append, List.append_assoc] at h
          obtain ⟨hln, htl⟩ := sep_split (headerLine_no13 he1) (headerLine_no13 he2) h
          have heq : e1 = e2 := headerLine_inj he1 he2 hln
          injection htl with _ htl2
          have hok1' : ∀ e ∈ f1 :: t1, HdrOK e := fun e he => hok1 e (List.mem_cons_of_mem e1 he)
          have hok2' : ∀ e ∈ f2 :: t2, HdrOK e := fun e he => hok2 e (List.mem_cons_of_mem e2 he)
          obtain ⟨hrest, hb⟩ := ih (f2 :: t2) b1 b2 hok1' hok2' (by simp) (by simp) htl2
          exact ⟨by rw [heq, hrest], hb⟩

/-- Every entry of `allHeaders (build r)` is `HdrOK` when `r` is `Wf` — the
caller headers by hypothesis, the derived `Content-Length` field by
construction (`Content-Length` is CR/LF/colon-free; `natToDec` is all digits). -/
theorem allHeaders_HdrOK (r : Response) (w : Wf r) :
    ∀ e ∈ allHeaders (build r), HdrOK e := by
  intro e he
  simp only [allHeaders, build, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · exact w.hdrOK e he
  · rw [he]
    refine ⟨⟨?_, ?_⟩, ?_, natToDec_no13 _, natToDec_no10 _⟩
    · show (13 : UInt8) ∉ clName; decide
    · show (10 : UInt8) ∉ clName; decide
    · show (58 : UInt8) ∉ clName; decide

/-! ## The egress round-trip: `serialize` is injective on well-formed responses -/

/-- **`serialize_injective` — the wire uniquely determines the Response.** For
well-formed responses (`Wf`: RFC 7230 §3.2 field discipline), equal egress bytes
force equal status, reason, headers, and body. The reversal peels the status
line (space-delimited, digit status), then the header block (each line CR-free,
the blank line the only CR-led boundary), then the body — the egress dual of the
request-line round-trip `Arena.Parse.parse_faithful` proves on ingress. -/
theorem serialize_injective {r1 r2 : Response} (w1 : Wf r1) (w2 : Wf r2)
    (h : serialize r1 = serialize r2) : r1 = r2 := by
  rw [serialize_framing, serialize_framing] at h
  simp only [headerBlockOf, crlf, List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨hsl, htl⟩ := sep_split (statusLine_no13 r1 w1) (statusLine_no13 r2 w2) h
  injection htl with _ hbodyhdr
  obtain ⟨hHdr, hBody⟩ := hdr_rt _ _ _ _ (allHeaders_HdrOK r1 w1) (allHeaders_HdrOK r2 w2)
    (allHeaders_ne_nil r1) (allHeaders_ne_nil r2) hbodyhdr
  obtain ⟨hStatus, hReason⟩ := statusLine_inj r1 r2 hsl
  simp only [allHeaders, build] at hHdr
  rw [hBody] at hHdr
  have hHeaders := append_snoc_inj hHdr
  cases r1
  cases r2
  simp only [Response.mk.injEq]
  exact ⟨hStatus, hReason, hHeaders, hBody⟩

/-! ## Non-vacuity: a concrete faithful encode, and the response-splitting finding -/

/-- Small digit-numeral evaluations (`natToDec` does not reduce by `rfl` — the
`toUTF8`/`ByteArray` obstacle noted in `Proto.Decimal` — so route through
`natToDec_eq`). -/
theorem natToDec_200 : natToDec 200 = [50, 48, 48] := by
  rw [show (natToDec 200) = Proto.Dec.natToDec 200 from rfl, Proto.Dec.natToDec_eq]; decide

theorem natToDec_2 : natToDec 2 = [50] := by
  rw [show (natToDec 2) = Proto.Dec.natToDec 2 from rfl, Proto.Dec.natToDec_eq]; decide

/-- A concrete `200 OK` response: one header `X: a`, body `ok`. -/
def exResp : Response :=
  { status := 200, reason := reasonOK, headers := [([88], [97])], body := [111, 107] }

/-- The exact wire bytes: `HTTP/1.1 200 OK CRLF X: a CRLF Content-Length: 2 CRLF CRLF ok`. -/
def exBytes : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10,
   88, 58, 32, 97, 13, 10,
   67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 50, 13, 10,
   13, 10,
   111, 107]

/-- **Non-vacuous worked example.** `serialize exResp` is byte-for-byte the
expected RFC-7230 wire, `Content-Length: 2` derived from the 2-byte body. -/
theorem exResp_serialize : serialize exResp = exBytes := by
  simp only [serialize, serializeWire, build, statusLine, allHeaders, renderHeaders, headerLine,
    http11, clName, reasonOK, crlf, exResp, List.length_cons, List.length_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  rw [natToDec_200, natToDec_2, exBytes]
  rfl

/-- `exResp` is well-formed, so `serialize_injective` is non-vacuous. -/
theorem exResp_wf : Wf exResp := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro e he
  simp only [exResp, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  subst he
  exact ⟨⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩⟩

/-! ### The response-splitting finding -/

/-- A response whose single header value carries an embedded `CR LF Y: b` — the
egress injection vector. NOT `Wf`. -/
def splitInjected : Response :=
  { status := 200, reason := reasonOK, headers := [([88], [97, 13, 10, 89, 58, 32, 98])], body := [] }

/-- The honest two-header response `X: a` / `Y: b`. `Wf`. -/
def splitHonest : Response :=
  { status := 200, reason := reasonOK, headers := [([88], [97]), ([89], [98])], body := [] }

/-- `splitInjected` is not well-formed: its header value contains CR/LF. -/
theorem splitInjected_not_wf : ¬ Wf splitInjected := by
  intro w
  have h := w.hdrOK ([88], [97, 13, 10, 89, 58, 32, 98]) (by simp [splitInjected])
  exact h.2.2.1 (by decide)

/-- `splitHonest` is well-formed. -/
theorem splitHonest_wf : Wf splitHonest := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro e he
  simp only [splitHonest, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩⟩
  · exact ⟨⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩⟩

/-- `splitInjected` and `splitHonest` are distinct responses (their header lists
differ). `Response` has no `DecidableEq`, so this is structural, not `decide`. -/
theorem split_ne : splitInjected ≠ splitHonest := by
  intro h
  simp [splitInjected, splitHonest, Response.mk.injEq] at h

/-- **`serialize_response_splitting` — egress header injection is real.** Two
DISTINCT responses serialize to IDENTICAL wire bytes: the CR/LF embedded in
`splitInjected`'s single header value is rendered verbatim, forging the exact
`Y: b` line that `splitHonest` carries as a real second header. `serialize`
neither escapes nor rejects the CR/LF — so injectivity holds only on the `Wf`
domain (`serialize_injective`), and egress safety is a `Wf`-maintenance
obligation on the upstream that builds the `Response`. This is the egress
analogue of the ingress `Arena.Parse.parse_rejects_ctl_in_value`, but where
INGRESS rejects, EGRESS renders. -/
theorem serialize_response_splitting :
    splitInjected ≠ splitHonest ∧ serialize splitInjected = serialize splitHonest := by
  refine ⟨split_ne, ?_⟩
  simp only [serialize, serializeWire, build, statusLine, allHeaders, renderHeaders, headerLine,
    clName, crlf, splitInjected, splitHonest, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil]

end Reactor
