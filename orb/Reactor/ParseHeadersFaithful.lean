/-
Reactor.ParseHeadersFaithful — discharging the HEADER half of parse-faithfulness
AT THE SEAM.

`Reactor/ParseFaithful.lean` composed `Arena.Parse.parse_faithful` with the
adapter to prove `deployed_request_faithful`: the `Proto.Request` the deployed
serve dispatches on has method / target / version equal to the exact wire bytes
of `buf`, rejoining into the request LINE verbatim. That left the HEADER LIST as
an assumption.

`Arena.Parse.parse_headers_faithful` closes the header half at the arena level:
the resolved `Request.headers` list equals the per-segment wire decode of the
CRLF-delimited header block (canonical lowercased names, OWS-trimmed values).
This file composes it with the adapter: `deployed_headers_faithful` states the
`Proto.Request.headers` the deployed serve dispatches on ARE the wire header
segments' decode, and `deployed_request_faithful_full` bundles line + headers —
the WHOLE parsed request (request line AND every header) proven faithful to the
wire bytes, fully discharging the parse-faithfulness assumption the serve carried.

Additive; the adapter's `resolveBytes` is definitionally the arena `viewBytes`
the faithfulness theorems are stated over (`viewBytes_eq_resolveBytes`).
-/
import Reactor.Config
import Reactor.ParseFaithful
import Arena.ParseHeadersFaithful

open Arena.Parse (SP startsWithHttpSlash wireHeaderName wireHeaderValue
  findDoubleCrlf segments crlfPositions)

namespace Reactor
namespace Config

/-- **`deployed_headers_faithful` — every dispatched header IS its wire segment.**
On a `complete` arena parse, the `Proto.Request.headers` the deployed serve
dispatches on (`(protoReqOf req).headers`) equals the per-segment wire decode of
the CRLF-delimited header block after the request line: for each wire segment
`sp`, the header's name is the **lowercased** wire field-name
(`wireHeaderName buf sp`) and its value the OWS-trimmed wire field-value
(`wireHeaderValue buf sp`). The `spans` are exactly the wire segments
(`segments 0 headEnd (crlfPositions …)` past the request-line span). The header
half of the parse-faithfulness assumption, discharged from real bytes. -/
theorem deployed_headers_faithful (buf : Proto.Bytes) (req : Arena.Parse.Request)
    (h : Arena.Parse.parse buf = .complete req) :
    ∃ (headEnd : Nat) (reqSpan : Arena.Parse.Span) (spans : List Arena.Parse.Span),
      findDoubleCrlf buf = some headEnd ∧
      segments 0 headEnd (crlfPositions (buf.take headEnd)) = reqSpan :: spans ∧
      (∀ sp ∈ spans, sp.off + sp.len ≤ buf.length) ∧
      (protoReqOf req).headers
        = spans.map (fun sp => (wireHeaderName buf sp, wireHeaderValue buf sp)) := by
  obtain ⟨headEnd, reqSpan, spans, hfd, hseg, hfit, hmap⟩ :=
    Arena.Parse.parse_headers_faithful h
  refine ⟨headEnd, reqSpan, spans, hfd, hseg, hfit, ?_⟩
  simp only [protoReqOf]
  exact hmap

/-- **`deployed_request_faithful_full` — the WHOLE dispatched request IS the
wire.** On a `complete` arena parse, the `Proto.Request` the deployed serve
dispatches on is faithful to the wire bytes of `buf` in BOTH halves: (1) method /
target / version are the exact wire slices, rejoining with single `SP`s into the
request line `buf.take (m+t+v+2)` verbatim (version begins `HTTP/`); and (2) every
header equals its wire CRLF-segment's decode — lowercased name, OWS-trimmed value.
Bundles `deployed_request_faithful` (line) with `deployed_headers_faithful`
(headers): the whole parsed request head is a faithful decode of the wire, fully
discharging the parse-faithfulness assumption the serve previously carried. -/
theorem deployed_request_faithful_full (buf : Proto.Bytes) (req : Arena.Parse.Request)
    (h : Arena.Parse.parse buf = .complete req) :
    (∃ m t v : Nat,
      (protoReqOf req).method  = buf.take m
      ∧ (protoReqOf req).target  = (buf.drop (m + 1)).take t
      ∧ (protoReqOf req).version = (buf.drop (m + t + 2)).take v
      ∧ (protoReqOf req).method
          ++ SP :: ((protoReqOf req).target ++ SP :: (protoReqOf req).version)
            = buf.take (m + t + v + 2)
      ∧ startsWithHttpSlash (protoReqOf req).version)
    ∧ (∃ (headEnd : Nat) (reqSpan : Arena.Parse.Span) (spans : List Arena.Parse.Span),
        findDoubleCrlf buf = some headEnd ∧
        segments 0 headEnd (crlfPositions (buf.take headEnd)) = reqSpan :: spans ∧
        (∀ sp ∈ spans, sp.off + sp.len ≤ buf.length) ∧
        (protoReqOf req).headers
          = spans.map (fun sp => (wireHeaderName buf sp, wireHeaderValue buf sp))) :=
  ⟨deployed_request_faithful buf req h, deployed_headers_faithful buf req h⟩

end Config
end Reactor
