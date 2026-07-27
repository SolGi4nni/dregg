/-
  ServeSpec.lean — the SHARED serve-specification library.

  This is a small, standalone Lean library that BOTH the verified-translator tree
  and the verified-dataplane tree can `require` (neither imports the other; both
  may depend on this). It carries the serve WIRE SEMANTICS only — one byte type,
  the response record, the response serializer, the pipeline data (context,
  stage, the two-phase onion fold), and the per-stage semantic content
  (header constants, gate predicates, the stage value). NO builder/perf
  machinery, NO dataplane, NO codegen — those stay tree-local.

  The point: today each tree retypes the other's serve constants (header
  names/values, status codes, reason phrases) to state a `mine = theirs` pin,
  and that pin is byte-for-byte PROSE — a mirror, not a machine-checked equation,
  because the two trees cannot see one another. Move the constants here ONCE and
  each tree references them; the pin becomes a real equation elaborated against a
  shared definition. A fabricated constant simply fails to typecheck against the
  spec's.

  Byte type. This library fixes `Bytes := List UInt8` (the dataplane tree's
  native byte). The translator tree's model uses `List (BitVec 8)`; the two are
  connected by the pointwise iso `UInt8.toBitVec`, applied at the translator's
  serialize boundary (see the `toBitVecs` map in the pin file). Naming that one
  friction point up front is most of the linking work.

  Toolchain: leanprover/lean4:v4.30.0, Lean core only (no external package).
-/

namespace ServeSpec

/-! ## 1. One byte type -/

/-- The shared byte string: the dataplane tree's native `List UInt8`. The
translator tree maps this into `List (BitVec 8)` pointwise at its serialize
boundary via `UInt8.toBitVec`. -/
abbrev Bytes := List UInt8

/-- ASCII/UTF-8 byte string of a `String` — the one place a header name/value or
reason phrase is spelled, shared by both trees. -/
def s (x : String) : Bytes := x.toUTF8.toList

/-! ## 2. The response record + the wire serializer

The wire model, authored once. Each tree today duplicates this as its own
`Response`/`serialize`; the plan (§ fold-in) is for both to *define* theirs from
these and prove the render equal once, here. -/

/-- The public response model handed to the serializer. No `Content-Length`
field: length framing is not a caller input, it is derived by `build`. -/
structure Response where
  status  : Nat
  reason  : Bytes
  headers : List (Bytes × Bytes)
  body    : Bytes
deriving Repr, DecidableEq

/-- The internal wire record; `contentLength` pinned to the body length. -/
structure Wire where
  status        : Nat
  reason        : Bytes
  headers       : List (Bytes × Bytes)
  contentLength : Nat
  body          : Bytes

/-- Build the wire record, fixing `contentLength := body.length`. -/
def build (r : Response) : Wire :=
  { status := r.status, reason := r.reason, headers := r.headers,
    contentLength := r.body.length, body := r.body }

def crlf   : Bytes := [13, 10]
def http11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]                       -- "HTTP/1.1"
def clName : Bytes := [67,111,110,116,101,110,116,45,76,101,110,103,116,104] -- "Content-Length"

/-- Decimal ASCII rendering of a natural (single-byte ASCII digits). -/
def natToDec (n : Nat) : Bytes := (Nat.repr n).toUTF8.toList

/-- `HTTP/1.1 SP status SP reason` (no trailing CRLF). -/
def statusLine (w : Wire) : Bytes :=
  http11 ++ [32] ++ natToDec w.status ++ [32] ++ w.reason

/-- One header rendered `name ": " value` (colon 58, space 32). -/
def headerLine (nv : Bytes × Bytes) : Bytes := nv.1 ++ [58, 32] ++ nv.2

/-- Caller headers followed by the derived `Content-Length` header. -/
def allHeaders (w : Wire) : List (Bytes × Bytes) :=
  w.headers ++ [(clName, natToDec w.contentLength)]

/-- Header lines joined by CRLF, no trailing CRLF. -/
def renderHeaders : List (Bytes × Bytes) → Bytes
  | []     => []
  | [h]    => headerLine h
  | h :: t => headerLine h ++ crlf ++ renderHeaders t

/-- Status line, CRLF, header block, blank-line separator, body. -/
def serializeWire (w : Wire) : Bytes :=
  statusLine w ++ crlf ++ renderHeaders (allHeaders w) ++ crlf ++ crlf ++ w.body

/-- **The response serializer.** Total. -/
def serialize (r : Response) : Bytes := serializeWire (build r)

/-- Content-Length is fixed to the body length by construction. -/
theorem serialize_content_length (r : Response) :
    (build r).contentLength = r.body.length := rfl

/-! ## 3. The pipeline data (builder-erased)

The dataplane tree threads an affine `ResponseBuilder` through the response
phase for in-place perf; its own faithfulness theorems erase that builder to
exactly the functional `Response → Response` updates below, so the SHARED
semantics is builder-free. That erasure is the dataplane tree's codegen concern
and is untouched here. -/

/-- Minimal request the stages gate/branch on. (The dataplane tree's `Ctx.req`
is a full parsed request; the spec keeps the gate-relevant projection — method
and target — plus the raw input and an extensible attribute bag, matching the
deployed context shape.) -/
structure Req where
  method : Bytes := []
  target : Bytes := []
deriving Repr, DecidableEq

/-- The serve context threaded through the pipeline. -/
structure Ctx where
  input : Bytes := []
  req   : Req := {}
  attrs : List (String × Bytes) := []

/-- The outcome of a stage's request phase: gate (short-circuit with a response)
or pass through with a — possibly transformed — context. -/
inductive StageStep where
  | respond  (r : Response)
  | continue (c : Ctx)

/-- A pipeline stage: a request-phase transform (which may gate) and a response
phase, in the functional (builder-erased) form. -/
structure Stage where
  name      : String
  onRequest : Ctx → StageStep
  onResp    : Ctx → Response → Response

/-- **The response-only fold (the onion, without gating).** Thread the response
back OUTWARD through the stages' `onResp` phases in reverse list order (head
outermost, applied last) — what a gate short-circuit runs over. -/
def runResp : List Stage → Ctx → Response → Response
  | [],       _, r => r
  | st :: rest, c, r => st.onResp c (runResp rest c r)

/-- **The pipeline fold.** Run request phases in order; the first `.respond`
short-circuits (handler + every later request phase skipped) but the inner
stages' response phases still run over the refusal (`runResp rest`). If all pass,
the handler answers and each passed stage's response phase wraps it (the onion).
-/
def runPipeline : List Stage → (Ctx → Response) → Ctx → Response
  | [],       handler, c => handler c
  | st :: rest, handler, c =>
    match st.onRequest c with
    | .respond r   => runResp rest c r
    | .continue c' => st.onResp c' (runPipeline rest handler c')

/-- No stages: the bare handler. -/
theorem runPipeline_nil (handler : Ctx → Response) (c : Ctx) :
    runPipeline [] handler c = handler c := rfl

/-- `runResp` head/tail: the outer stage's response phase wraps the inner fold. -/
theorem runResp_cons (st : Stage) (rest : List Stage) (c : Ctx) (r : Response) :
    runResp (st :: rest) c r = st.onResp c (runResp rest c r) := rfl

/-! ## 4. Per-stage semantic content — one section per deployed stage

Just the constants + the stage value + its defining equation. This is what each
tree references instead of retyping. Below: the security-headers stage (a pure
response transform that never gates); the pattern repeats one stage per module
in the full package. -/

namespace SecurityHeaders

def xfoName     : Bytes := s "X-Frame-Options"
def xfoVal      : Bytes := s "DENY"
def noSniffName : Bytes := s "X-Content-Type-Options"
def noSniffVal  : Bytes := s "nosniff"

/-- The two security headers this stage appends to every response. -/
def headers : List (Bytes × Bytes) := [(xfoName, xfoVal), (noSniffName, noSniffVal)]

/-- The security-headers stage: never gates; its response phase appends the two
security headers at the end of the header list. -/
def stage : Stage :=
  { name      := "security-headers"
    onRequest := fun c => .continue c
    onResp    := fun _ r => { r with headers := r.headers ++ headers } }

/-- Defining equation of the stage's response phase. -/
theorem stage_onResp (c : Ctx) (r : Response) :
    stage.onResp c r = { r with headers := r.headers ++ headers } := rfl

end SecurityHeaders

/-! ## 5. The DEPLOYED security-headers stage (the dataplane tree's real 4-header stage)

Section 4's `SecurityHeaders` stage models the two-header (X-Frame-Options +
X-Content-Type-Options) transform the TRANSLATOR tree carries. The DATAPLANE
tree's *deployed* security-headers stage stamps the full set: HSTS
(`Strict-Transport-Security`), `X-Frame-Options: DENY`,
`X-Content-Type-Options: nosniff`, and `Referrer-Policy: no-referrer` — driven
off its response-security policy. This namespace carries those exact wire
constants + the deployed stage so the dataplane tree's real stage anchors here.

The two-header stage of §4 is the (XFO, nosniff) SUBSET of this one (`xfo_deployed`,
`nosniff_deployed`) — the precise relationship between what the translator models
and what the dataplane deploys. HSTS and Referrer-Policy are the deployed extras
the translator does not (yet) carry. -/
namespace SecurityHeadersDeployed

/-- `Strict-Transport-Security` header name. -/
def hstsName : Bytes := s "Strict-Transport-Security"
/-- The deployed HSTS value (max-age one year, includeSubDomains, preload). -/
def hstsVal  : Bytes := s "max-age=31536000; includeSubDomains; preload"
/-- `Referrer-Policy` header name. -/
def referrerName : Bytes := s "Referrer-Policy"
/-- The deployed referrer-policy value. -/
def referrerVal  : Bytes := s "no-referrer"

/-- The deployed four-header set, in the order the deployed policy renders:
HSTS, X-Frame-Options, X-Content-Type-Options, Referrer-Policy. The XFO and
nosniff members are the SHARED §4 constants. -/
def headers : List (Bytes × Bytes) :=
  [ (hstsName, hstsVal)
  , (SecurityHeaders.xfoName, SecurityHeaders.xfoVal)
  , (SecurityHeaders.noSniffName, SecurityHeaders.noSniffVal)
  , (referrerName, referrerVal) ]

/-- The deployed security-headers stage: never gates; appends the four-header set
at the end of the response header list. -/
def stage : Stage :=
  { name      := "securityheaders"
    onRequest := fun c => .continue c
    onResp    := fun _ r => { r with headers := r.headers ++ headers } }

/-- Defining equation of the deployed stage's response phase. -/
theorem stage_onResp (c : Ctx) (r : Response) :
    stage.onResp c r = { r with headers := r.headers ++ headers } := rfl

/-- The translator's X-Frame-Options member is one of the deployed headers. -/
theorem xfo_deployed :
    (SecurityHeaders.xfoName, SecurityHeaders.xfoVal) ∈ headers := by
  simp [headers]

/-- The translator's X-Content-Type-Options member is one of the deployed headers. -/
theorem nosniff_deployed :
    (SecurityHeaders.noSniffName, SecurityHeaders.noSniffVal) ∈ headers := by
  simp [headers]

end SecurityHeadersDeployed

end ServeSpec
