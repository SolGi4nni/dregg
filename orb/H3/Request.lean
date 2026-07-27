import H3.Frame
import H3.Qpack

/-!
# HTTP/3 request streams (RFC 9114 §4.1) and request-head validation (§4.3.1)

`H3.decFrame` decodes one frame; this module gives a client-initiated
bidirectional stream its *request grammar*:

```
  Unknown*  HEADERS  (DATA | Unknown)*  [HEADERS (trailers)]  Unknown*
```

* `readRequestStream` — the frame-sequencing reader. Unknown/reserved frame
  types are skipped wherever they appear (§7.2.8, §9 greasing); the first
  HEADERS opens the request; DATA payloads are concatenated into the request
  content (§4.1); a second HEADERS is the trailer section and must end the
  stream. Any frame that is not permitted on a request stream — DATA before
  HEADERS, SETTINGS (§7.2.4.1), GOAWAY (§7.2.6), MAX_PUSH_ID (§7.2.7),
  CANCEL_PUSH (§7.2.3), a client-sent PUSH_PROMISE (§7.2.5) — makes the
  stream `malformed` (the `H3_FRAME_UNEXPECTED` conditions, surfaced as a
  typed outcome).

* `validRequestHead` — the §4.3.1 malformed-request gate over a decoded QPACK
  head: the required pseudo-headers are present (`:method`, and for
  non-CONNECT `:scheme` plus a non-empty `:path`, and an `:authority` or a
  `host` field; for CONNECT exactly `:method`+`:authority`, §4.4), no field
  name is uppercase or a pseudo-header in field position (§4.1.2, §4.3), no
  connection-specific field is present (§4.2), and any `te` field says
  `trailers` (§4.2).

The theorems bind the reader to the RFC behaviors: unknown frames ahead of
HEADERS never change the outcome (`readRequestStream_skips_unknown`, via the
proven `decFrame_unknown_skip`), a leading DATA frame is malformed
(`readRequestStream_rejects_leading_data`), a HEADERS+DATA stream reads back
exactly its section and content (`readRequestStream_headers_data`), and a
valid head necessarily carries its required pseudo-headers
(`validRequestHead_method` / `validRequestHead_path_scheme`).
-/

namespace H3

open Qpack (strBytes)

/-- Outcome of reading one FIN-terminated request stream's frames. -/
inductive ReqStream where
  /-- A complete request: the HEADERS frame's encoded field section, the
  concatenated DATA content, and the trailer section if present. -/
  | request (encoded : Bytes) (body : Bytes) (trailers : Option Bytes)
  /-- The last frame is truncated (more stream bytes required). -/
  | incomplete
  /-- The frame sequence violates the request-stream grammar
  (`H3_FRAME_UNEXPECTED` / `H3_FRAME_ERROR` conditions). -/
  | malformed
deriving Repr, DecidableEq

set_option linter.unusedVariables false in
/-- After the trailer HEADERS only unknown (grease) frames may follow. -/
def tailOk (bs : Bytes) : Bool :=
  match h : decFrame bs with
  | .complete (.unknown _ _) n => tailOk (bs.drop n)
  | .complete _ _ => false
  | .incomplete => bs.isEmpty
  | .error => false
termination_by bs.length
decreasing_by
  have := decFrame_consumed bs _ n h
  simp only [List.length_drop]
  omega

set_option linter.unusedVariables false in
/-- After the first HEADERS: DATA extends the content, unknown frames are
skipped, a second HEADERS is the trailer section (and must end the stream up
to trailing grease), any other frame is malformed. A clean end of stream
completes the request. -/
def readAfterHeaders (encoded body : Bytes) (bs : Bytes) : ReqStream :=
  match h : decFrame bs with
  | .complete (.data payload) n => readAfterHeaders encoded (body ++ payload) (bs.drop n)
  | .complete (.unknown _ _) n => readAfterHeaders encoded body (bs.drop n)
  | .complete (.headers tr) n =>
    if tailOk (bs.drop n) then .request encoded body (some tr) else .malformed
  | .complete _ _ => .malformed
  | .incomplete => if bs.isEmpty then .request encoded body none else .incomplete
  | .error => .malformed
termination_by bs.length
decreasing_by
  all_goals
    have := decFrame_consumed bs _ n h
    simp only [List.length_drop]
    omega

set_option linter.unusedVariables false in
/-- **The request-stream reader** (RFC 9114 §4.1). Skip unknown frames, open
on the first HEADERS, then read content/trailers; everything else is
malformed. -/
def readRequestStream (bs : Bytes) : ReqStream :=
  match h : decFrame bs with
  | .complete (.headers enc) n => readAfterHeaders enc [] (bs.drop n)
  | .complete (.unknown _ _) n => readRequestStream (bs.drop n)
  | .complete _ _ => .malformed
  | .incomplete => .incomplete
  | .error => .malformed
termination_by bs.length
decreasing_by
  all_goals
    have := decFrame_consumed bs _ n h
    simp only [List.length_drop]
    omega

/-! ## The reader refines the RFC frame rules -/

/-- **§7.2.8 / §9 greasing:** an unknown-type frame ahead of the request is
ignored and discarded — reading the stream with it prepended is reading the
stream without it. Holds for every unknown type and payload. -/
theorem readRequestStream_skips_unknown (t len : Nat)
    (tbs lbs payload rest : Bytes)
    (ht : Varint.encVarint t = some tbs) (hl : Varint.encVarint len = some lbs)
    (hunk : isKnownType t = false) (hp : payload.length = len) :
    readRequestStream (tbs ++ (lbs ++ (payload ++ rest)))
      = readRequestStream rest := by
  have hskip := decFrame_unknown_skip t len tbs lbs payload rest ht hl hunk hp
  have hdrop : (tbs ++ (lbs ++ (payload ++ rest))).drop (tbs.length + lbs.length + len)
      = rest := by
    rw [show tbs ++ (lbs ++ (payload ++ rest)) = (tbs ++ lbs ++ payload) ++ rest by
      simp [List.append_assoc]]
    rw [List.drop_left' (by simp only [List.length_append, hp])]
  rw [readRequestStream]
  split
  · rename_i enc n heq
    rw [hskip] at heq
    cases heq
  · rename_i t' len' n heq
    rw [hskip] at heq
    cases heq
    rw [hdrop]
  · rename_i hne _ heq
    rw [hskip] at heq
    cases heq
    rename_i hh
    exact absurd rfl (hh _ _)
  · rename_i heq
    rw [hskip] at heq
    cases heq
  · rename_i heq
    rw [hskip] at heq
    cases heq

/-- **§4.1:** a DATA frame before HEADERS on a request stream is
`H3_FRAME_UNEXPECTED` — the reader rejects the stream as malformed. -/
theorem readRequestStream_rejects_leading_data (bs payload : Bytes) (n : Nat)
    (h : decFrame bs = .complete (.data payload) n) :
    readRequestStream bs = .malformed := by
  rw [readRequestStream]
  split
  case h_1 => rename_i heq; rw [h] at heq; cases heq
  case h_2 => rename_i heq; rw [h] at heq; cases heq
  case h_3 => rfl
  case h_4 => rename_i heq; rw [h] at heq; cases heq
  case h_5 => rfl

/-- **§4.1, the accepting case:** a stream that is exactly one HEADERS frame
followed by one DATA frame reads back the request with that encoded section
and that content, no trailers. -/
theorem readRequestStream_headers_data (bs enc payload : Bytes) (n m : Nat)
    (h1 : decFrame bs = .complete (.headers enc) n)
    (h2 : decFrame (bs.drop n) = .complete (.data payload) m)
    (h3 : (bs.drop n).drop m = []) :
    readRequestStream bs = .request enc payload none := by
  rw [readRequestStream]
  split
  case h_2 => rename_i heq; rw [h1] at heq; cases heq
  case h_3 =>
    rename_i hnh hnu heq
    rw [h1] at heq
    cases heq
    exact (hnh _ rfl).elim
  case h_4 => rename_i heq; rw [h1] at heq; cases heq
  case h_5 => rename_i heq; rw [h1] at heq; cases heq
  case h_1 =>
    rename_i enc' n' heq
    rw [h1] at heq
    cases heq
    rw [readAfterHeaders]
    split
    case h_2 => rename_i heq2; rw [h2] at heq2; cases heq2
    case h_3 => rename_i heq2; rw [h2] at heq2; cases heq2
    case h_4 =>
      rename_i hnd hnu hnh heq2
      rw [h2] at heq2
      cases heq2
      exact (hnd _ rfl).elim
    case h_5 => rename_i heq2; rw [h2] at heq2; cases heq2
    case h_6 => rename_i heq2; rw [h2] at heq2; cases heq2
    case h_1 =>
      rename_i payload' m' heq2
      rw [h2] at heq2
      cases heq2
      rw [h3, readAfterHeaders]
      split
      case h_1 => rename_i heq3; cases heq3
      case h_2 => rename_i heq3; cases heq3
      case h_3 => rename_i heq3; cases heq3
      case h_4 => rename_i heq3; cases heq3
      case h_5 => simp
      case h_6 => rename_i heq3; cases heq3

/-! ## §4.3.1 request-head validation -/

/-- Resolve an arena entry to its bytes (`[]` for an out-of-bounds entry —
dead under `Wf`, as in the ingress). -/
def resolvedBytes (st : Arena.Store) (e : Arena.Entry) : Bytes :=
  match st.resolve e with
  | some arr => arr.toList
  | none => []

/-- §4.2: connection-specific fields MUST NOT appear in HTTP/3 field
sections; a request containing one is malformed. -/
def forbiddenReqField (n : Bytes) : Bool :=
  n == strBytes "connection" || n == strBytes "keep-alive"
    || n == strBytes "proxy-connection" || n == strBytes "transfer-encoding"
    || n == strBytes "upgrade"

/-- §4.1.2: an uppercase octet in a field name makes the message malformed. -/
def hasUpper (n : Bytes) : Bool :=
  n.any (fun b => 65 ≤ b.toNat && b.toNat ≤ 90)

/-- One regular (non-pseudo) field line is acceptable in a request: name is
not a pseudo-header (§4.3: unrecognized pseudo-headers are malformed), not
uppercase, not connection-specific, and a `te` field only says `trailers`. -/
def fieldOk (st : Arena.Store) (fl : Qpack.FieldLine) : Bool :=
  let n := resolvedBytes st fl.name
  !(n.head? == some 0x3a) && !hasUpper n && !forbiddenReqField n
    && (n != strBytes "te" || resolvedBytes st fl.value == strBytes "trailers")

/-- **The §4.3.1 malformed-request gate.** `:method` present; CONNECT (§4.4)
carries `:authority` and neither `:scheme` nor `:path`; every other method
carries `:scheme`, a non-empty `:path`, and an authority (`:authority` or a
`host` field); and every regular field passes `fieldOk`. -/
def validRequestHead (st : Arena.Store) (p : Qpack.Pseudo)
    (fields : List Qpack.FieldLine) : Bool :=
  let isConnect := (p.method.map (resolvedBytes st)) == some (strBytes "CONNECT")
  p.method.isSome
    && (if isConnect then
          p.authority.isSome && p.scheme.isNone && p.path.isNone
        else
          p.scheme.isSome && p.path.isSome
            && (p.path.map (resolvedBytes st)) != some []
            && (p.authority.isSome
                || fields.any (fun fl => resolvedBytes st fl.name == strBytes "host")))
    && fields.all (fieldOk st)

/-- A valid head always names its method (§4.3.1: `:method` is never
optional). -/
theorem validRequestHead_method (st : Arena.Store) (p : Qpack.Pseudo)
    (fields : List Qpack.FieldLine) (h : validRequestHead st p fields = true) :
    p.method.isSome := by
  unfold validRequestHead at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- A valid non-CONNECT head always carries `:scheme` and `:path` (§4.3.1's
"MUST include" clause, refined by the gate). -/
theorem validRequestHead_path_scheme (st : Arena.Store) (p : Qpack.Pseudo)
    (fields : List Qpack.FieldLine)
    (hnc : ((p.method.map (resolvedBytes st)) == some (strBytes "CONNECT")) = false)
    (h : validRequestHead st p fields = true) :
    p.scheme.isSome ∧ p.path.isSome := by
  unfold validRequestHead at h
  simp only [hnc, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
  exact ⟨h.1.2.1.1.1, h.1.2.1.1.2⟩

/-! ## Execution vectors (`#guard`, compiler-evaluated on the real decoders) -/

/-- The reader on the greased request the battery sends: an unknown frame
(type 0x21, empty) then a HEADERS frame — the grease is skipped and the
section is delivered. -/
private def vecGreased : Bool :=
  readRequestStream ([0x21, 0x00, 0x01, 0x03, 0x00, 0x00, 0xd1])
    == .request [0x00, 0x00, 0xd1] [] none
#guard vecGreased

/-! DATA before HEADERS is malformed (§4.1). -/
#guard readRequestStream [0x00, 0x03, 0x61, 0x62, 0x63] == .malformed

/-! SETTINGS on a request stream is malformed (§7.2.4.1). -/
#guard readRequestStream [0x04, 0x02, 0x01, 0x00] == .malformed

/-! HEADERS then DATA reads back section and content (a POST shape). -/
#guard readRequestStream [0x01, 0x02, 0x00, 0x00, 0x00, 0x03, 0x61, 0x62, 0x63]
  == .request [0x00, 0x00] [0x61, 0x62, 0x63] none

/-! HEADERS, DATA, trailing HEADERS: trailers delivered. -/
#guard readRequestStream
    [0x01, 0x02, 0x00, 0x00, 0x00, 0x01, 0x7a, 0x01, 0x02, 0x00, 0x00]
  == .request [0x00, 0x00] [0x7a] (some [0x00, 0x00])

/-! A truncated frame is incomplete, not malformed. -/
#guard readRequestStream [0x01, 0x05, 0x00] == .incomplete

/-- The battery's malformed head — `:method` only (`00 00 d1`) — fails the
§4.3.1 gate; the full head (`:method :scheme :path :authority`) passes it.
Driven through the REAL `decodeFieldSection` into the arena. -/
private def vecValidation : Bool :=
  let empty : Arena.Store := { main := #[], sidecar := #[], entries := [] }
  let bad :=
    match Qpack.decodeFieldSection Qpack.rfc7541Huffman empty [0x00, 0x00, 0xd1] with
    | .ok d => validRequestHead d.store d.pseudo d.fields == false
    | .error _ => false
  let good :=
    match Qpack.decodeFieldSection Qpack.rfc7541Huffman empty
        ([0x00, 0x00, 0xd1, 0xd7, 0x51, 0x07] ++ strBytes "/health"
          ++ [0x50, 0x01] ++ strBytes "x") with
    | .ok d => validRequestHead d.store d.pseudo d.fields == true
    | .error _ => false
  bad && good
#guard vecValidation

/-! ## The assembled request-stream processor — the single call the QUIC
dispatch makes per client-bidi stream. -/

/-- Outcome of processing one complete request stream: frame sequencing
(§4.1), QPACK decode (RFC 9204), and the §4.3.1 head gate, in order. -/
inductive ProcessedRequest where
  /-- A well-formed request: the grown store, the routed pseudo-headers, the
  regular fields, and the concatenated DATA content. -/
  | ok (store : Arena.Store) (pseudo : Qpack.Pseudo)
       (fields : List Qpack.FieldLine) (body : Bytes)
  /-- The stream violates the request grammar, its field section does not
  decode (`QPACK_DECOMPRESSION_FAILED`), or the head fails the §4.3.1 gate —
  answered with 400 and no dispatch. -/
  | malformed
  /-- The last frame is truncated: more stream bytes are required. -/
  | incomplete

/-- **The request-stream front end** (RFC 9114 §4.1 + §4.3.1, RFC 9204):
`readRequestStream` (grease skip, DATA concatenation, trailer close), then the
deployed `decodeFieldSection` against `dyn`, then the `validRequestHead` gate.
Everything a server needs before routing: pseudo-headers, fields, content. -/
def processRequestStream (hd : Qpack.HuffmanDecoder) (st : Arena.Store)
    (bs : Bytes) (dyn : Qpack.DynTable := Qpack.DynTable.empty) :
    ProcessedRequest :=
  match readRequestStream bs with
  | .incomplete => .incomplete
  | .malformed => .malformed
  | .request enc body _trailers =>
    match Qpack.decodeFieldSection hd st enc dyn with
    | .error _ => .malformed
    | .ok d =>
      if validRequestHead d.store d.pseudo d.fields then
        .ok d.store d.pseudo d.fields body
      else .malformed

/-- **§7.2.8 / §9 lifted to the processor**: an unknown-type frame ahead of the
request changes nothing — the whole pipeline (sequencing, QPACK, validation)
is grease-blind. -/
theorem processRequestStream_skips_unknown (hd : Qpack.HuffmanDecoder)
    (st : Arena.Store) (dyn : Qpack.DynTable) (t len : Nat)
    (tbs lbs payload rest : Bytes)
    (ht : Varint.encVarint t = some tbs) (hl : Varint.encVarint len = some lbs)
    (hunk : isKnownType t = false) (hp : payload.length = len) :
    processRequestStream hd st (tbs ++ (lbs ++ (payload ++ rest))) dyn
      = processRequestStream hd st rest dyn := by
  unfold processRequestStream
  rw [readRequestStream_skips_unknown t len tbs lbs payload rest ht hl hunk hp]

/-- The processor preserves store well-formedness: an accepted request's
store is `Wf` (every emitted view entry in-bounds), lifted from
`decodeFieldSection_wf`. -/
theorem processRequestStream_wf (hd : Qpack.HuffmanDecoder) (st : Arena.Store)
    (bs : Bytes) (dyn : Qpack.DynTable) (st' : Arena.Store)
    (p : Qpack.Pseudo) (fls : List Qpack.FieldLine) (body : Bytes)
    (hwf : st.Wf)
    (h : processRequestStream hd st bs dyn = .ok st' p fls body) : st'.Wf := by
  unfold processRequestStream at h
  repeat' split at h
  all_goals cases h
  exact Qpack.decodeFieldSection_wf_dyn hd st _ dyn _ hwf (by assumption)

/-- An accepted request always carries `:method` — the §4.3.1 gate is on the
accepting path by construction. -/
theorem processRequestStream_method (hd : Qpack.HuffmanDecoder)
    (st : Arena.Store) (bs : Bytes) (dyn : Qpack.DynTable) (st' : Arena.Store)
    (p : Qpack.Pseudo) (fls : List Qpack.FieldLine) (body : Bytes)
    (h : processRequestStream hd st bs dyn = .ok st' p fls body) :
    p.method.isSome := by
  unfold processRequestStream at h
  repeat' split at h
  all_goals cases h
  exact validRequestHead_method _ _ _ (by assumption)

/-! ## RFC 9110 §9.3.2: HEAD responses carry no content -/

/-- The response content for a request method: a HEAD response MUST NOT carry
content (its headers — `content-length` included — are those the equivalent
GET would have sent; only the body is suppressed). -/
def headSuppressedBody (method : Bytes) (body : Bytes) : Bytes :=
  if method = Qpack.strBytes "HEAD" then [] else body

theorem headSuppressedBody_head (body : Bytes) :
    headSuppressedBody (Qpack.strBytes "HEAD") body = [] := by
  unfold headSuppressedBody; rw [if_pos rfl]

theorem headSuppressedBody_other (method body : Bytes)
    (h : method ≠ Qpack.strBytes "HEAD") :
    headSuppressedBody method body = body := by
  unfold headSuppressedBody; rw [if_neg h]

/-! ### Processor execution vectors (`#guard`, the battery shapes end to end) -/

private def emptySt : Arena.Store := { main := #[], sidecar := #[], entries := [] }

/-- The greased GET the battery sends — unknown frame, then HEADERS carrying
`:method: GET`, `:scheme: https`, `:path: /health`, `:authority: x` — is
accepted with its pseudo-headers routed and an empty body. -/
private def vecProcessGreased : Bool :=
  let sec := [0x00, 0x00, 0xd1, 0xd7, 0x51, 0x07] ++ Qpack.strBytes "/health"
      ++ [0x50, 0x01] ++ Qpack.strBytes "x"
  let stream := [0x21, 0x00] ++ [0x01, UInt8.ofNat sec.length] ++ sec
  match processRequestStream Qpack.rfc7541Huffman emptySt stream with
  | .ok _ p _ body => p.method.isSome && p.path.isSome && body.isEmpty
  | _ => false
#guard vecProcessGreased

/-- The battery's `:method`-only HEADERS (missing `:path`/`:scheme`/
`:authority`) is malformed (§4.3.1) through the processor. -/
private def vecProcessMissingPseudo : Bool :=
  match processRequestStream Qpack.rfc7541Huffman emptySt
      [0x01, 0x03, 0x00, 0x00, 0xd1] with
  | .malformed => true
  | _ => false
#guard vecProcessMissingPseudo

/-- DATA before HEADERS stays malformed through the processor (§4.1). -/
private def vecProcessLeadingData : Bool :=
  match processRequestStream Qpack.rfc7541Huffman emptySt
      [0x00, 0x03, 0x61, 0x62, 0x63] with
  | .malformed => true
  | _ => false
#guard vecProcessLeadingData

/-- A POST shape delivers its DATA payload as the request content. -/
private def vecProcessPost : Bool :=
  let sec := [0x00, 0x00, 0xd4, 0xd7, 0x51, 0x07] ++ Qpack.strBytes "/health"
      ++ [0x50, 0x01] ++ Qpack.strBytes "x"
  let stream := [0x01, UInt8.ofNat sec.length] ++ sec
      ++ [0x00, 0x03, 0x61, 0x62, 0x63]
  match processRequestStream Qpack.rfc7541Huffman emptySt stream with
  | .ok _ _ _ body => body == [0x61, 0x62, 0x63]
  | _ => false
#guard vecProcessPost

/-! ## Axiom audit -/

#print axioms readRequestStream_skips_unknown
#print axioms readRequestStream_rejects_leading_data
#print axioms readRequestStream_headers_data
#print axioms validRequestHead_method
#print axioms validRequestHead_path_scheme
#print axioms processRequestStream_skips_unknown
#print axioms processRequestStream_wf
#print axioms processRequestStream_method

/-- A request carrying a connection-specific field is malformed (§4.2):
`connection: close` as a literal field line. -/
private def vecForbidden : Bool :=
  let empty : Arena.Store := { main := #[], sidecar := #[], entries := [] }
  match Qpack.decodeFieldSection Qpack.rfc7541Huffman empty
      ([0x00, 0x00, 0xd1, 0xd7, 0xc1, 0x50, 0x01] ++ strBytes "x"
        ++ [0x27, 0x03] ++ strBytes "connection" ++ [0x05] ++ strBytes "close") with
  | .ok d => validRequestHead d.store d.pseudo d.fields == false
  | .error _ => false
#guard vecForbidden

end H3
