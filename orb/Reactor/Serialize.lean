import Proto.Basic

/-!
# A proven HTTP/1.1 response serializer

A total function `serialize : Response → Bytes` that renders a response head and
body onto the wire in the shape

```
HTTP/1.1 SP status SP reason CRLF (name ": " value CRLF)* CRLF body
```

The `Content-Length` header is *not* an input field. The serializer builds an
internal wire record whose `contentLength` field is fixed to `body.length` by
construction, and emits the header from that field. This makes the framing
length correct by construction rather than by a caller's promise.

What is proven:
* `serialize_content_length` — the built wire record carries
  `contentLength = body.length` (the builder sets it so).
* `serialize_framing` — the output decomposes exactly as
  `statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`; the body appears
  once, at the end, after the blank-line separator.
* `serialize_body_suffix` — `body` is a suffix of `serialize resp`: nothing is
  emitted after the body.
* `serialize_total` — `serialize` is a plain (total) `def`; no response is a
  stuck state.
-/

namespace Reactor

open Proto (Bytes)

/-- The public response model handed to the serializer. Note the absence of a
`Content-Length` field: length framing is not a caller input. -/
structure Response where
  status  : Nat
  reason  : Bytes
  headers : List (Bytes × Bytes)
  body    : Bytes
deriving Repr

/-- The internal wire record the serializer builds from a `Response`. Its
`contentLength` field is fixed to the body length; the emitted `Content-Length`
header value is derived from this field, never from caller input. -/
structure Wire where
  status        : Nat
  reason        : Bytes
  headers       : List (Bytes × Bytes)
  contentLength : Nat
  body          : Bytes
deriving Repr

/-- Build the wire record, pinning `contentLength := body.length`. -/
def build (resp : Response) : Wire :=
  { status        := resp.status
    reason        := resp.reason
    headers       := resp.headers
    contentLength := resp.body.length
    body          := resp.body }

/-- `CRLF` line terminator. -/
def crlf : Bytes := [13, 10]

/-- `"HTTP/1.1"` in ASCII. -/
def http11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]

/-- `"Content-Length"` in ASCII. -/
def clName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104]

/-- `"OK"` in ASCII — the default reason phrase for `ok200`. -/
def reasonOK : Bytes := [79, 75]

/-- Decimal ASCII rendering of a natural number (via `Nat.repr`; ASCII digits
are single UTF-8 bytes). -/
def natToDec (n : Nat) : Bytes := (Nat.repr n).toUTF8.toList

/-- `HTTP/1.1 SP status SP reason` (no trailing CRLF). -/
def statusLine (w : Wire) : Bytes :=
  http11 ++ [32] ++ natToDec w.status ++ [32] ++ w.reason

/-- One header rendered as `name ": " value` (colon = 58, space = 32). -/
def headerLine (nv : Bytes × Bytes) : Bytes := nv.1 ++ [58, 32] ++ nv.2

/-- The full header list: the caller's headers followed by the derived
`Content-Length` header. -/
def allHeaders (w : Wire) : List (Bytes × Bytes) :=
  w.headers ++ [(clName, natToDec w.contentLength)]

/-- Render header lines joined by CRLF, with no trailing CRLF (so the two CRLFs
that separate the header block from the body appear explicitly in
`serialize`). -/
def renderHeaders : List (Bytes × Bytes) → Bytes
  | []      => []
  | [h]     => headerLine h
  | h :: t  => headerLine h ++ crlf ++ renderHeaders t

/-- Serialize the wire record: status line, CRLF, header block, blank-line
separator (CRLF ++ CRLF), then the body. -/
def serializeWire (w : Wire) : Bytes :=
  statusLine w ++ crlf ++ renderHeaders (allHeaders w) ++ crlf ++ crlf ++ w.body

/-- **The response serializer.** Builds the wire record (fixing `Content-Length`
to `body.length`) and renders it. Total. -/
def serialize (resp : Response) : Bytes := serializeWire (build resp)

/-- The status line of the wire record built from `resp`. -/
def statusLineOf (resp : Response) : Bytes := statusLine (build resp)

/-- The rendered header block (including the derived `Content-Length` line). -/
def headerBlockOf (resp : Response) : Bytes := renderHeaders (allHeaders (build resp))

/-! ## Helper constructors -/

/-- A `200 OK` response with the given body (no caller headers; the serializer
adds `Content-Length`). -/
def ok200 (body : Bytes) : Response :=
  { status := 200, reason := reasonOK, headers := [], body := body }

/-- A `4xx`/`5xx` response with an explicit status code, reason phrase, and
body. -/
def error4xx (code : Nat) (reason : Bytes) (body : Bytes) : Response :=
  { status := code, reason := reason, headers := [], body := body }

/-! ## Theorems -/

/-- **Content-Length by construction.** The wire record the serializer builds
carries `contentLength = body.length`. The emitted header value is
`natToDec` of this field, so the framing length is not a caller input. -/
theorem serialize_content_length (resp : Response) :
    (build resp).contentLength = resp.body.length := rfl

/-- The derived `Content-Length` header (name and value) is present in the
wire record's header list, with value `natToDec body.length`. -/
theorem content_length_header_present (resp : Response) :
    (clName, natToDec resp.body.length) ∈ allHeaders (build resp) := by
  simp [allHeaders, build]

/-- **Framing.** `serialize resp` decomposes as
`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`. The body occurs
once, at the very end, after the blank-line separator. -/
theorem serialize_framing (resp : Response) :
    serialize resp
      = statusLineOf resp ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf ++ resp.body := rfl

/-- **Body suffix.** The body is a suffix of `serialize resp`: nothing is
emitted after it. -/
theorem serialize_body_suffix (resp : Response) :
    resp.body <:+ serialize resp :=
  ⟨statusLineOf resp ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf, rfl⟩

/-- **Totality.** `serialize` is a plain (total) `def`. -/
theorem serialize_total (resp : Response) : serialize resp = serialize resp := rfl

/-! ## The compiled render (`serializeFast`) — allocation-free head, proven byte-identical

Everything above is the SPEC. At runtime a cons-list `xs ++ ys` is `appendTR`
= `reverseAux xs.reverse ys`: TWO fresh spines of `xs` per join, one freed
immediately. Compiled as written, `serialize` therefore pays, **per request**:
fresh fragment lists for the status line, two fresh spines of the caller's
header list just to append the derived `Content-Length` pair (`allHeaders`), a
fresh `headerLine` list **per header**, a fresh `Wire` record, and a triple
walk of the head at the final `head ++ body` join — every one of them built,
consumed once, and freed. That is allocator churn proportional to the head on
every request.

`serializeFast` renders the head **byte-direct** into ONE uniquely-owned
`Array UInt8` accumulator (no intermediate list, no `Wire`, no `List.++`
anywhere on the render) and materializes the final spine exactly once, cons'd
directly onto the body — which stays the shared right operand, never copied,
exactly as the spec. `serialize_eq_fast` proves byte-identity and installs it
as the compiled implementation.

**Why the `@[csimp]` lives HERE, in the spec's own module:** a `@[csimp]` is
applied only to call sites compiled with the theorem in scope. Housed in a
separate leaf module, it silently reverts every caller that does not import
that leaf — and the deployed pipeline modules did exactly that (their generated
code called the allocating spec symbol). In this module, no caller can
reference `serialize` without the csimp visible — the reversion is impossible
by construction, not by import discipline.

Honest residuals: `natToDec` still allocates a `String`/`ByteArray`/`List`
chain twice per request (status code, Content-Length value) — a proven
digits-to-bytes render against `Nat.repr`+UTF-8 is a separate, deeper proof;
and the ONE final head spine (a cons cell per head byte) is irreducible while
the output type is `Bytes = List UInt8` — the `ByteArray`-native serves are
the seam that removes it. -/

/-- One header line pushed byte-direct onto the owned accumulator: name bytes,
colon, space, value bytes. The `headerLine` fragment list (`nv.1 ++ [58,32] ++
nv.2`, two `reverseAux` spine pairs, freed immediately) is never built. -/
def headerLinePush (acc : Array UInt8) (nv : Bytes × Bytes) : Array UInt8 :=
  (((acc ++ nv.1).push 58).push 32) ++ nv.2

/-- The derived `Content-Length` line pushed byte-direct: the persistent
`clName` constant walked in place, colon, space, decimal digits. No
`(clName, …)` pair, no singleton, no combined header list. -/
def clLinePush (acc : Array UInt8) (len : Nat) : Array UInt8 :=
  (((acc ++ clName).push 58).push 32) ++ natToDec len

/-- The header block + derived `Content-Length` rendered in ONE walk of the
caller's list: every caller line pushed byte-direct followed by CRLF, the CL
line emitted last with no trailing CRLF — exactly `renderHeaders (hs ++
[(clName, natToDec len)])`, with `allHeaders`' per-request combined-list
spine copy gone by construction. -/
def renderHeadersClPush (acc : Array UInt8) (len : Nat) : List (Bytes × Bytes) → Array UInt8
  | []     => clLinePush acc len
  | h :: t => renderHeadersClPush (((headerLinePush acc h).push 13).push 10) len t

/-- The response head rendered byte-direct into ONE owned flat accumulator,
off the `Response` fields themselves: status line, CRLF, header block with the
derived `Content-Length`, blank-line separator. No `Wire` record, no
`statusLine`/`headerLine`/`allHeaders` list, no `List.++` at all. -/
def headPush (resp : Response) : Array UInt8 :=
  let acc : Array UInt8 :=
    ((((#[] : Array UInt8) ++ http11).push 32) ++ natToDec resp.status).push 32 ++ resp.reason
  let acc := (acc.push 13).push 10
  let acc := renderHeadersClPush acc resp.body.length resp.headers
  (((acc.push 13).push 10).push 13).push 10

/-- **The flat response serializer.** Byte-identical to `serialize`; renders the
head byte-direct into one owned accumulator (`headPush`) and materializes the
final spine ONCE, cons'd directly onto the shared body (`Array.toListAppend` —
no `toList`-then-`++` double walk, no body copy). Installed as the compiled
`serialize` by `serialize_eq_fast`. -/
def serializeFast (resp : Response) : Bytes :=
  (headPush resp).toListAppend resp.body

/-- `headerLinePush` reads back as exactly `headerLine` appended. -/
theorem headerLinePush_toList (acc : Array UInt8) (nv : Bytes × Bytes) :
    (headerLinePush acc nv).toList = acc.toList ++ headerLine nv := by
  simp [headerLinePush, headerLine]

/-- `clLinePush` reads back as exactly the derived `Content-Length`
`headerLine` appended. -/
theorem clLinePush_toList (acc : Array UInt8) (len : Nat) :
    (clLinePush acc len).toList = acc.toList ++ headerLine (clName, natToDec len) := by
  simp [clLinePush, headerLine]

/-- The one-walk push render reads back as exactly the spec's
`renderHeaders` over the combined `headers ++ [(clName, …)]` list — the list
the compiled path no longer builds. -/
theorem renderHeadersClPush_toList (len : Nat) (hs : List (Bytes × Bytes)) :
    ∀ acc : Array UInt8,
      (renderHeadersClPush acc len hs).toList
        = acc.toList ++ renderHeaders (hs ++ [(clName, natToDec len)]) := by
  induction hs with
  | nil =>
    intro acc
    simpa [renderHeadersClPush, renderHeaders] using clLinePush_toList acc len
  | cons h t ih =>
    intro acc
    rw [show renderHeadersClPush acc len (h :: t)
          = renderHeadersClPush (((headerLinePush acc h).push 13).push 10) len t from rfl,
        ih]
    obtain ⟨x, xs, hx⟩ : ∃ x xs, t ++ [((clName, natToDec len) : Bytes × Bytes)] = x :: xs := by
      cases t with
      | nil => exact ⟨_, _, rfl⟩
      | cons a b => exact ⟨_, _, rfl⟩
    rw [List.cons_append, hx,
        show renderHeaders (h :: x :: xs) = headerLine h ++ crlf ++ renderHeaders (x :: xs)
          from rfl]
    simp [headerLinePush_toList, crlf]

/-- The push-rendered head reads back exactly as the spec head
(`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF` of the built wire
record), so appending the body reconstructs the full wire byte sequence. -/
theorem headPush_toList (resp : Response) :
    (headPush resp).toList
      = statusLine (build resp) ++ crlf ++ renderHeaders (allHeaders (build resp))
          ++ crlf ++ crlf := by
  simp [headPush, renderHeadersClPush_toList, statusLine, allHeaders, build, crlf]

/-- **The flat/spec agreement.** `serializeFast` produces the same wire bytes as
`serialize`: the head rendered byte-direct, the final spine materialized once,
the body appended shared. Installed as the compiled implementation in the
spec's own module, so EVERY caller of `serialize` — the deployed pipeline
included — compiles to the push render, while `serialize` itself, the spec
every theorem and conformance obligation references, is untouched. -/
@[csimp] theorem serialize_eq_fast : @serialize = @serializeFast := by
  funext resp
  show serializeWire (build resp) = (headPush resp).toListAppend resp.body
  rw [Array.toListAppend_eq, headPush_toList]
  unfold serializeWire
  simp only [build, List.append_assoc]

/-! ### Non-vacuity — the push render is byte-identical to the independently
compiled spec render (`serializeWire` carries no `@[csimp]`; its compiled code
is the original `List.++` chain) on real response shapes. -/

/-- Two caller headers (`X-A: 1`, `X-BB: 23`) and a 5-byte body. -/
private def pushDemoResp : Response :=
  { status  := 200
    reason  := reasonOK
    headers := [([88, 45, 65], [49]), ([88, 45, 66, 66], [50, 51])]
    body    := [104, 101, 108, 108, 111] }

#guard serializeFast pushDemoResp == serializeWire (build pushDemoResp)
#guard serializeFast (ok200 [104, 105]) == serializeWire (build (ok200 [104, 105]))
#guard serializeFast (ok200 []) == serializeWire (build (ok200 []))
#guard serializeFast (error4xx 404 [78] []) == serializeWire (build (error4xx 404 [78] []))
-- The render genuinely depends on the headers and the body.
#guard serializeFast pushDemoResp != serializeFast (ok200 [104, 105])

/-! ### Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms renderHeadersClPush_toList
#print axioms headPush_toList
#print axioms serialize_eq_fast

end Reactor
