import Proto.ResponseParse

/-!
# A proven HTTP/1.1 request serializer — the client dual of the request parser

`Reactor.Serialize` renders a *response* onto the wire (the server's outbound
half). This module is its dual: it renders a *request* — `method SP target SP
version CRLF (name ": " value CRLF)* CRLF` — the half a verified *client* emits
to an upstream, plus the matching request-head parser (built from the same
single-pass scan primitives as `Proto.ResponseParse`).

## What is proven

`parse_serialize` — the client↔server round-trip on the request line: a request
the client *serializes* parses back to the same request:

    parse (serialize req) = some req

for every well-formed request (`WF`: the method/target carry no `SP`, the
version and header names/values carry no bare `CR`, and header names carry no
`:` — the RFC 9112 request-line and field discipline). `parse_serialize_get`
discharges `WF` on a concrete `GET / HTTP/1.1` with a `Host` header, witnessing
non-vacuity.

`serialize_framing` records the wire decomposition.

The request head this parser reads is the dual view of what the server's arena
parser (`Arena.Parse`) resolves; `ArenaSound.parse_reqline_sound` is the
server-side soundness partner (`resolve method = input[0,i₁)`, …). Wiring the
completeness direction *through* `Arena.Parse` itself (so the round-trip is
against the server's exact parser, headers included) is named as a residual —
`Arena.ParseTheorems`/`ArenaSound` leave the arena header round-trip open.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.
-/

namespace Proto
namespace RequestSerialize

open Reactor (headerLine crlf)
open Proto.ResponseParse (SP CR LF COLON takeUntil takeUntilCrlf parseHeaders parseHeadersFuel
  blockOf takeUntil_append takeUntilCrlf_append parseHeadersFuel_blockOf)

abbrev Bytes := List UInt8

/-- The request line `method SP target SP version` (no trailing CRLF). -/
def reqLine (req : Proto.Request) : Bytes :=
  req.method ++ [SP] ++ req.target ++ [SP] ++ req.version

/-- **The request serializer.** Request line, CRLF, the header block (each
`name ": " value` line CRLF-terminated), then the blank line. Total. -/
def serialize (req : Proto.Request) : Bytes :=
  reqLine req ++ crlf ++ (req.headers.flatMap (fun h => headerLine h ++ crlf)) ++ crlf

/-- **The request-head parser** (dual of the response parser). -/
def parse (bs : Bytes) : Option Proto.Request := do
  let (method, bs) ← takeUntil SP bs
  let (target, bs) ← takeUntil SP bs
  let (version, bs) ← takeUntilCrlf bs
  let (headers, _body) ← parseHeaders bs
  some { method := method, target := target, version := version, headers := headers }

/-- The RFC 9112 request-line + field discipline. -/
def WF (req : Proto.Request) : Prop :=
  SP ∉ req.method ∧ SP ∉ req.target ∧ CR ∉ req.version ∧
  ∀ kv ∈ req.headers, COLON ∉ kv.1 ∧ CR ∉ kv.1 ∧ CR ∉ kv.2

/-- Wire decomposition of `serialize`. -/
theorem serialize_framing (req : Proto.Request) :
    serialize req = reqLine req ++ crlf ++ blockOf req.headers ++ crlf := rfl

/-- **Client↔server round-trip.** A request the client serializes parses back to
the same request. Non-vacuous (see `parse_serialize_get`). -/
theorem parse_serialize (req : Proto.Request) (h : WF req) :
    parse (serialize req) = some req := by
  obtain ⟨hM, hT, hV, hH⟩ := h
  -- shape the serialized bytes for the three scans
  have hshape : serialize req
      = req.method ++ SP :: (req.target ++ SP ::
          (req.version ++ crlf ++ (blockOf req.headers ++ crlf))) := by
    simp only [serialize, reqLine, blockOf, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append]
  rw [parse, hshape]
  simp only [takeUntil_append SP req.method _ hM, takeUntil_append SP req.target _ hT,
    takeUntilCrlf_append req.version _ hV, Option.bind, bind, pure, Option.pure_def]
  -- the header block: `blockOf headers ++ crlf = blockOf headers ++ crlf ++ []`
  have hbody : blockOf req.headers ++ crlf = blockOf req.headers ++ crlf ++ [] := by
    rw [List.append_nil]
  rw [hbody, parseHeaders,
    parseHeadersFuel_blockOf req.headers [] _ hH (Nat.le_refl _)]

/-- Non-vacuity: `WF` holds for a concrete `GET / HTTP/1.1` with a `Host`. -/
def getExample : Proto.Request :=
  { method := [71, 69, 84],                              -- "GET"
    target := [47],                                      -- "/"
    version := [72, 84, 84, 80, 47, 49, 46, 49],         -- "HTTP/1.1"
    headers := [([72, 111, 115, 116], [120])] }          -- "Host: x"

theorem getExample_WF : WF getExample := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro kv hkv
    simp only [getExample, List.mem_singleton] at hkv
    subst hkv
    exact ⟨by decide, by decide, by decide⟩

/-- The round-trip, discharged concretely on `GET / HTTP/1.1`. -/
theorem parse_serialize_get : parse (serialize getExample) = some getExample :=
  parse_serialize _ getExample_WF

end RequestSerialize
end Proto
