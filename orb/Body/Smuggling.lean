import Body.Chunked

/-!
# Request-smuggling defense: message-body framing (RFC 9112 §6.1–§6.3)

An HTTP/1.1 message body is framed by exactly one of two mechanisms: a
`Content-Length` (a fixed octet count) or a `Transfer-Encoding: chunked` (a
self-delimiting chunk stream). Request smuggling exploits the *ambiguity* that
arises when a message carries framing signals a downstream pair of servers
resolve differently:

* **CL.TE** — the front server frames on `Content-Length`, the back server on
  the chunked stream. Body bytes the front server treats as payload the back
  server reads as a *second request*.
* **TE.CL** — the reverse split.
* **dup-CL** — two `Content-Length` values; one server believes the first, the
  other the second, and the octets in between smuggle a request.
* **bad-chunk** — a malformed chunk-size that one parser rejects and another
  silently truncates, leaving a smuggled tail.

RFC 9112 §6.1 resolves the CL/TE overlap by giving `Transfer-Encoding`
precedence (a sender that emits both is broken and MAY be treated as an error);
§6.3 requires rejecting a message whose framing is undeterminable. This file
takes the strict, non-ambiguous stance: **a message carrying both framings, or
conflicting `Content-Length` values, or a malformed chunk, is rejected** — there
is then a *single* interpretation (rejection) that no two servers can split, so
no octet is ever reinterpreted as a smuggled request.

The framing decision is factored as two independent classifiers over the parsed
header list — `clStatus` (the `Content-Length` picture) and `teStatus` (the
`Transfer-Encoding` picture) — combined by `decideOn`. The security theorems
reason about `decideOn` and hold for *every* request; concrete CL.TE / TE.CL /
dup-CL / bad-chunk attack vectors are then discharged against them, witnessing
the hypotheses are inhabited (non-vacuous) and that real smuggling attempts land
in the rejecting branch.

Headline theorems:

* `no_desync` — a request whose headers frame *both* a `Content-Length` and a
  `Transfer-Encoding: chunked` is **never** framed as a `Content-Length` body:
  the decision is a rejection. So the chunked tail can never be handed on as a
  smuggled second request (`decide` is never `.length _`; it is `.reject _`).
* `reject_dup_cl` — two differing `Content-Length` values are rejected, not
  silently reconciled.
* `reject_bad_chunk` — a chunked body whose chunk-size token is malformed is
  rejected (`decodeStream = .error`), never silently truncated to a short
  `.complete` body that leaves a smuggled tail.

The `naive_would_smuggle` theorem exhibits the *mutant*: a length-only framer
that ignores `Transfer-Encoding` frames the CL.TE vector as a 6-byte body — the
exact desync `no_desync` forbids.
-/

namespace Body
namespace Smuggling

open Body.Chunked

/-! ## Parsed headers -/

/-- One parsed header field: a name and a value, as raw octet runs (the shape a
request-line/header parser hands downstream). -/
structure Header where
  name : Bytes
  value : Bytes
deriving Repr, DecidableEq

/-- A parsed request head: its header fields, in wire order. -/
structure Request where
  headers : List Header
deriving Repr, DecidableEq

/-! ## Octet utilities -/

/-- ASCII comma (`,`), the `Transfer-Encoding` list separator. -/
def COMMA : UInt8 := 44
/-- ASCII space. -/
def SP : UInt8 := 32
/-- ASCII horizontal tab. -/
def HT : UInt8 := 9

/-- Fold an ASCII upper-case letter to lower case; every other octet is left
alone. Header field names are case-insensitive (RFC 9110 §5.1). -/
def asciiLower (b : UInt8) : UInt8 :=
  if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- Case-insensitive octet-run equality: lower-case `name`, compare to a
`target` given already in lower case. -/
def nameEq (name target : Bytes) : Bool := (name.map asciiLower) == target

/-- Is `b` linear whitespace (space or tab)? -/
def isLws (b : UInt8) : Bool := b == SP || b == HT

/-- Drop leading linear whitespace. -/
def dropLws : Bytes → Bytes
  | [] => []
  | b :: bs => if isLws b then dropLws bs else b :: bs

/-- Trim leading and trailing linear whitespace (field-value normalization,
RFC 9110 §5.5). -/
def trim (v : Bytes) : Bytes := (dropLws (dropLws v).reverse).reverse

/-- Is `b` an ASCII decimal digit? -/
def isDigit (b : UInt8) : Bool := 48 ≤ b ∧ b ≤ 57

/-- Big-endian decimal fold over a digit run, short-circuiting to `none` on the
first non-digit octet. -/
def parseDecAux (acc : Nat) : Bytes → Option Nat
  | [] => some acc
  | b :: bs => if isDigit b then parseDecAux (acc * 10 + (b.toNat - 48)) bs else none

/-- Parse a non-negative decimal integer. An empty run or any non-digit octet is
rejected — this is the `Content-Length` value validation that closes the
`Content-Length: -1` / `Content-Length: abc` desync vectors. -/
def parseDec (v : Bytes) : Option Nat :=
  match v with
  | [] => none
  | _ => parseDecAux 0 v

/-- Split an octet run on commas, producing the (always non-empty) list of
comma-separated fields. -/
def splitComma : Bytes → List Bytes
  | [] => [[]]
  | b :: bs =>
    if b == COMMA then [] :: splitComma bs
    else match splitComma bs with
      | [] => [[b]]
      | x :: xs => (b :: x) :: xs

theorem splitComma_ne_nil (v : Bytes) : splitComma v ≠ [] := by
  induction v with
  | nil => simp [splitComma]
  | cons b bs ih =>
    simp only [splitComma]
    split
    · simp
    · split <;> simp

/-! ## Lower-case name constants -/

/-- `content-length` as lower-case octets. -/
def clName : Bytes :=
  [99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104]
/-- `transfer-encoding` as lower-case octets. -/
def teName : Bytes :=
  [116, 114, 97, 110, 115, 102, 101, 114, 45, 101, 110, 99, 111, 100, 105, 110, 103]
/-- `chunked` as lower-case octets. -/
def chunkedToken : Bytes := [99, 104, 117, 110, 107, 101, 100]

/-! ## Content-Length classification -/

/-- The `Content-Length` picture of a request. -/
inductive ClStatus where
  /-- No `Content-Length` header field. -/
  | absent
  /-- A single well-formed non-negative value `n` (all present copies agree). -/
  | present (n : Nat)
  /-- A value that is not a valid non-negative integer. -/
  | invalid
  /-- Two `Content-Length` values that differ. -/
  | dup
deriving Repr, DecidableEq

/-- The values of every `Content-Length` header field, in order. -/
def clValues (req : Request) : List Bytes :=
  req.headers.filterMap (fun h => if nameEq h.name clName then some h.value else none)

/-- Classify the `Content-Length` header fields. A non-integer value is
`invalid`; two differing values are `dup`; agreeing well-formed values are
`present`; no field is `absent`. -/
def clStatus (req : Request) : ClStatus :=
  match clValues req with
  | [] => .absent
  | v :: vs =>
    let all := v :: vs
    if all.any (fun x => (parseDec (trim x)).isNone) then .invalid
    else
      let t0 := trim v
      if vs.all (fun x => trim x == t0) then
        match parseDec t0 with
        | some n => .present n
        | none => .invalid
      else .dup

/-! ## Transfer-Encoding classification -/

/-- The `Transfer-Encoding` picture of a request. -/
inductive TeStatus where
  /-- No `Transfer-Encoding` header field. -/
  | absent
  /-- A well-formed `chunked` framing (every coding is `chunked`). -/
  | chunked
  /-- `chunked` present but not the final coding (e.g. `chunked, gzip`). -/
  | chunkedNotLast
  /-- A coding the server does not implement (anything but `chunked`). -/
  | unsupported
deriving Repr, DecidableEq

/-- The values of every `Transfer-Encoding` header field, in order. -/
def teValues (req : Request) : List Bytes :=
  req.headers.filterMap (fun h => if nameEq h.name teName then some h.value else none)

/-- Is a trimmed coding token `chunked` (case-insensitive)? -/
def tokenIsChunked (t : Bytes) : Bool := nameEq t chunkedToken

/-- Classify one `Transfer-Encoding` field value. `chunked` must be the final
coding, and every coding must be `chunked` (the only one implemented). -/
def teValStatus (v : Bytes) : TeStatus :=
  let toks := (splitComma v).map trim
  let n := toks.length
  if (toks.zipIdx.any (fun p => tokenIsChunked p.1 && p.2 + 1 != n)) then .chunkedNotLast
  else if toks.any (fun t => !tokenIsChunked t) then .unsupported
  else .chunked

/-- Classify all `Transfer-Encoding` header fields together: the first field
that is malformed decides a rejection; otherwise `chunked` (when present) or
`absent`. -/
def teStatus (req : Request) : TeStatus :=
  match teValues req with
  | [] => .absent
  | vs =>
    match vs.findSome? (fun v =>
      match teValStatus v with
      | .chunked => none
      | s => some s) with
    | some s => s
    | none => .chunked

/-! ## The framing decision -/

/-- Why a message was rejected for smuggling. -/
inductive Reason where
  | bothClAndTe
  | dupContentLength
  | invalidContentLength
  | chunkedNotLast
  | unsupportedTransferEncoding
  /-- The head contained a **bare LF** (an LF not immediately preceded by CR)
  outside the content. RFC 9112 §2.2 permits a recipient to recognize a bare LF
  as a line terminator, so a head carrying one has two admissible parses; an
  intermediary that forwards such a head hands the next hop a message it parsed
  differently from the way that hop may parse it — RFC 9112 §11.2 request
  smuggling. Raised by `Body.FrameRaw.frameRaw`, which fails closed. -/
  | bareLF
deriving Repr, DecidableEq

/-- The framing decision for a message body. -/
inductive Framing where
  /-- Rejected: framing is ambiguous or malformed (a single, unsplittable fate). -/
  | reject (r : Reason)
  /-- Frame the body as exactly `n` octets (`Content-Length`). -/
  | length (n : Nat)
  /-- Frame the body as a chunked stream (`Transfer-Encoding: chunked`). -/
  | chunked
  /-- No body framing signalled. -/
  | empty
deriving Repr, DecidableEq

/-- Combine the two classifications into a framing decision. `Content-Length`
malformations reject first; a valid `Content-Length` **together with** a chunked
`Transfer-Encoding` is the CL/TE conflict and rejects; otherwise the single
present framing (if any) is used. Crucially, the CL+TE overlap never resolves to
`.length`. -/
def decideOn : ClStatus → TeStatus → Framing
  | .invalid, _ => .reject .invalidContentLength
  | .dup, _ => .reject .dupContentLength
  | .present _, .chunkedNotLast => .reject .chunkedNotLast
  | .present _, .unsupported => .reject .unsupportedTransferEncoding
  | .present _, .chunked => .reject .bothClAndTe
  | .present n, .absent => .length n
  | .absent, .chunkedNotLast => .reject .chunkedNotLast
  | .absent, .unsupported => .reject .unsupportedTransferEncoding
  | .absent, .chunked => .chunked
  | .absent, .absent => .empty

/-- The message-body framing decision for a parsed request. -/
def decide (req : Request) : Framing := decideOn (clStatus req) (teStatus req)

/-! ## Security theorems -/

/-- Every framing decision that involves a valid `Content-Length` alongside a
chunked `Transfer-Encoding` is a rejection — expressed purely over `decideOn`. -/
theorem decideOn_present_chunked (n : Nat) :
    decideOn (.present n) .chunked = .reject .bothClAndTe := rfl

/-- **No desync (headline).** If a request's headers frame *both* a
`Content-Length` and a `Transfer-Encoding: chunked`, the body is **never** framed
as a fixed-length body: the decision is a rejection. A CL.TE / TE.CL split is
therefore impossible — there is no length interpretation for one server to take
while another follows the chunk stream, so the chunked tail is never handed on as
a smuggled request. -/
theorem no_desync (req : Request) (n : Nat)
    (hcl : clStatus req = .present n) (hte : teStatus req = .chunked) :
    decide req = .reject .bothClAndTe ∧ (∀ m, decide req ≠ .length m) := by
  have hd : decide req = .reject .bothClAndTe := by
    simp only [decide, hcl, hte, decideOn]
  exact ⟨hd, by rw [hd]; intro m h; exact Framing.noConfusion h⟩

/-- **No desync, general form.** Whenever *any* `Content-Length` header is present
(valid, invalid, or duplicated) together with a chunked `Transfer-Encoding`, the
decision is a rejection and never a fixed-length framing. This is the full
guarantee that the two framings can never be resolved to `.length`. -/
theorem no_desync_general (req : Request)
    (hcl : clStatus req ≠ .absent) (hte : teStatus req = .chunked) :
    (∃ r, decide req = .reject r) ∧ (∀ m, decide req ≠ .length m) := by
  rw [decide, hte]
  cases hs : clStatus req with
  | absent => exact absurd hs hcl
  | present n => exact ⟨⟨_, rfl⟩, by intro m h; simp only [decideOn] at h; exact Framing.noConfusion h⟩
  | invalid => exact ⟨⟨_, rfl⟩, by intro m h; simp only [decideOn] at h; exact Framing.noConfusion h⟩
  | dup => exact ⟨⟨_, rfl⟩, by intro m h; simp only [decideOn] at h; exact Framing.noConfusion h⟩

/-- **Duplicate Content-Length rejected (headline).** A request whose
`Content-Length` header fields carry two differing values is rejected, never
silently reconciled to one framing that a peer resolves to the other. -/
theorem reject_dup_cl (req : Request) (h : clStatus req = .dup) :
    decide req = .reject .dupContentLength := by
  rw [decide, h]; cases teStatus req <;> rfl

/-- **Malformed chunk rejected (headline).** A chunked body buffer whose leading
chunk-size line is not a valid hex token decodes to `.error` — never to a
`.complete` body. The parser refuses to silently truncate, so no octet past the
malformed size is reinterpreted as a smuggled request.

`pre` is the (CR-free, non-hex) size token; the trailing `rest` is arbitrary
attacker-supplied bytes. -/
theorem reject_bad_chunk (pre rest : Bytes)
    (hpre : ∀ b ∈ pre, b ≠ CR) (hbad : Body.Hex.parseHex pre = none) :
    Chunked.decodeStream (pre ++ CR :: LF :: rest) = .error ∧
    (∀ body c, Chunked.decodeStream (pre ++ CR :: LF :: rest) ≠ .complete body c) := by
  have hph : Chunked.parseHeader (pre ++ CR :: LF :: rest) = .error :=
    Chunked.parseHeader_bad_hex pre rest hpre hbad
  have hdf : Chunked.decodeFrame (pre ++ CR :: LF :: rest) = .error := by
    unfold Chunked.decodeFrame; rw [hph]
  have hds : Chunked.decodeStream (pre ++ CR :: LF :: rest) = .error := by
    rw [Chunked.decodeStream, hdf]
  refine ⟨hds, ?_⟩
  intro body c h; rw [hds] at h; cases h

/-! ## Concrete attack vectors (non-vacuity) -/

/-! Each vector is the header view of a real smuggling probe. The raw wire form
is shown in the doc comment; the `Request` is its parsed head. -/

/-- **CL.TE vector.**

    POST / HTTP/1.1
    Host: x
    Content-Length: 6
    Transfer-Encoding: chunked

    0

    SMUGGLED

A length-framing server reads 6 octets as the body; a chunked-framing server
reads the `0`-terminator and treats `SMUGGLED` as the next request. -/
def clteVector : Request :=
  { headers :=
    [ { name := clName, value := [54] },              -- "6"
      { name := teName, value := chunkedToken } ] }   -- "chunked"

/-- **TE.CL vector** — the same conflict with the header order swapped. -/
def teclVector : Request :=
  { headers :=
    [ { name := teName, value := chunkedToken },
      { name := clName, value := [54] } ] }

/-- **Duplicate-Content-Length vector** — `Content-Length: 5` and
`Content-Length: 6`. -/
def dupClVector : Request :=
  { headers :=
    [ { name := clName, value := [53] },   -- "5"
      { name := clName, value := [54] } ] } -- "6"

/-- The CL.TE vector's `Content-Length` picture is a valid `6`. -/
theorem clte_cl : clStatus clteVector = .present 6 := by decide

/-- The CL.TE vector's `Transfer-Encoding` picture is `chunked`. -/
theorem clte_te : teStatus clteVector = .chunked := by decide

/-- **The CL.TE vector is rejected** — it cannot smuggle. -/
theorem clte_rejected : decide clteVector = .reject .bothClAndTe :=
  (no_desync clteVector 6 clte_cl clte_te).1

/-- **The TE.CL vector is rejected** — order does not matter. -/
theorem tecl_rejected : decide teclVector = .reject .bothClAndTe := by decide

/-- **The duplicate-Content-Length vector is rejected.** -/
theorem dup_cl_rejected : decide dupClVector = .reject .dupContentLength :=
  reject_dup_cl dupClVector (by decide)

/-- A concrete malformed chunk: the size token is `g` (`0x67`), not a hex digit.
It decodes to `.error`, never a truncated `.complete` body. -/
theorem bad_chunk_rejected :
    Chunked.decodeStream ([103] ++ CR :: LF :: [65, 66, 67]) = .error :=
  (reject_bad_chunk [103] [65, 66, 67]
    (by intro b hb; simp only [List.mem_singleton] at hb; subst hb; decide)
    (by decide)).1

/-! ## The mutant: what the defense buys -/

/-- A naive length-only framer that consults only `Content-Length`, ignoring
`Transfer-Encoding`. This is the vulnerable behavior `decide` replaces. -/
def frameNaive (req : Request) : Framing :=
  match clStatus req with
  | .present n => .length n
  | .invalid => .reject .invalidContentLength
  | .dup => .reject .dupContentLength
  | .absent => .empty

/-- **The mutant desyncs.** On the CL.TE vector the naive framer frames a 6-octet
body — precisely the length interpretation `no_desync` forbids and that a chunked
back-end would split into a smuggled request. The contract is therefore not
vacuous: a natural mutant violates it. -/
theorem naive_would_smuggle :
    frameNaive clteVector = .length 6 ∧ decide clteVector ≠ frameNaive clteVector := by
  refine ⟨by decide, ?_⟩
  rw [clte_rejected]; decide

end Smuggling
end Body
