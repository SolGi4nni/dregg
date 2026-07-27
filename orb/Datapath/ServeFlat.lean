import Datapath.IndexParse
import Datapath.FlatBody

/-!
# Datapath.ServeFlat — the ASSEMBLED flat serve (index-native parse ⟶ flat header
stage ⟶ flat `ByteArray` body ⟶ flat egress), the cons-list-removal MEASUREMENT gate.

Every prior `Datapath.*` module proves ONE piece of the serve byte-identical to its
`List` spec while never materializing the cons-list on the flat side:

* `Datapath.SpanBytes.parseIndexNative` — the request-head parse read by INDEX off the
  borrowed window; no per-byte request cons (`parseIndexNative_refines`: byte-identical
  `ParseOutcome` to the deployed `Reactor.Config.h1ParseFn s.read`, K1/K3).
* `Datapath.FlatStage.flatSecurityStage` — the `securityheaders` transform as an
  `Array.push` fold on the flat `HdrBlock`; no `List` header spine (K5).
* `Datapath.FlatBody.serializeFlatB` — the egress serializer over a genuine `ByteArray`
  body, a bulk `Array ++ Array` append; no `List UInt8` body, no `body.toArray` of a cons
  (`serializeFlatB_refines`: byte-identical to `Reactor.serialize`, K2/R3/K4).

This module ASSEMBLES them into one runnable serve `serveFlatEcho : ByteArray → ByteArray`
whose whole computation carries NO runtime `List UInt8` for the request, the headers, or
the body — the flat exemplar the codegen scope claims `leanc` lowers in place (RC==1 /
FBIP). `serveListEcho` is its bit-for-bit `List` twin: the SAME response, computed the
deployed way (`h1ParseFn s.read` conses the whole request, `Reactor.serialize` over a
`List` header spine and an `input.data.toList` body cons). `serveFlatEcho_refines` proves
the two produce the IDENTICAL bytes for every input — so the A/B measures ONLY the
cons-list materialization cost, never a behavioural difference.

## Honest scope of "the exemplar"

`serveFlatEcho` is the REPRESENTATIVE flat serve of `CONS-LIST-KILLLIST.md`: it runs the
real index-native parse and the real flat `securityheaders` stage, and echoes the request
bytes back as the response body (the controlled variable — a tiny GET gives a tiny body, an
8 KB POST an 8 KB body, so the A/B directly probes the K2 body cliff). It is NOT the full
14-stage deployed fold: that composition requires the pipeline to consume a `SpanBytes`
request and produce a `ByteArray` body end-to-end (the `Bytes := List UInt8` root change,
the "catastrophic reprove" `ServeArr.lean` names) — out of scope for the additive seam.
`serveFlatEcho_refines` is byte-identity to the exemplar's OWN `List` twin, not to
`Dataplane.drorbServe`. The remaining 13 stages are the mechanical composition
`FlatStage.lean` names (`RefinesHdrFn.comp`).
-/

namespace Datapath.ServeFlat

open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines)
open Datapath.SpanBytes (full full_wf)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.FlatStage (flatSecurityStage)
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatWire (respOf)

/-- The fixed flat header block for the exemplar: an empty base list run through the flat
`securityheaders` stage (`Array.push` fold — no `List` header spine). The deployed
security-header set is folded on flat; the body's `Content-Length` is pushed by
`serializeFlatB`. -/
def exemplarBlock : HdrBlock := flatSecurityStage (HdrBlock.ofList [])

/-- **The assembled FLAT serve.** Parse the request off the borrowed window by INDEX
(`parseIndexNative`, no request cons); on a dispatchable request, echo the request bytes
back as the response body carried as a genuine `ByteArray` (`input`, never a `List`) and
egress through `serializeFlatB` (flat header render + bulk body append). NO runtime
`List UInt8` for the request, the headers, or the body anywhere on this path. -/
@[export drorb_serve_span]
def serveFlatEcho (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ _ _ => serializeFlatB 200 Reactor.reasonOK exemplarBlock input
  | _ => ByteArray.empty

/-- **The `List` TWIN — the same serve, computed the deployed cons-list way.** Parse via
`Reactor.Config.h1ParseFn (full input).read` — `.read` is `List.ofFn`, the per-byte
request cons (K1) — and egress via `Reactor.serialize` of the deployed `Response` whose
body is `input.data.toList` (the per-byte body cons, K2) over a `List` header spine (K5),
then `ByteArray.mk … .toArray` (the K6 walk), exactly `Dataplane.drorbServe`'s shape.
Byte-identical to `serveFlatEcho` (`serveFlatEcho_refines`); the difference is ONLY the
`List` materialization. -/
@[export drorb_serve_span_list]
def serveListEcho (input : ByteArray) : ByteArray :=
  match Reactor.Config.h1ParseFn (full input).read with
  | .request _ _ _ =>
      ByteArray.mk (Reactor.serialize (respOf 200 Reactor.reasonOK exemplarBlock input.data.toList)).toArray
  | _ => ByteArray.empty

/-- **THE ASSEMBLED BYTE-IDENTITY.** The flat serve and its `List` twin produce the
IDENTICAL response bytes for EVERY input. The parse halves agree by
`parseIndexNative_refines` (the index-native parse computes the same `ParseOutcome` as the
deployed `List` parse), and on a dispatchable request the egress halves agree by
`serializeFlatB_refines` (the flat `ByteArray`-body serializer is byte-identical to
`Reactor.serialize` of the deployed `List`-body response). So swapping `drorb_serve_span`
for `drorb_serve_span_list` changes no served byte — the A/B measures only cons-list cost.
Non-vacuous: the conclusion genuinely depends on the request bytes (the body is echoed). -/
theorem serveFlatEcho_refines (input : ByteArray) :
    serveFlatEcho input = serveListEcho input := by
  unfold serveFlatEcho serveListEcho
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    have hr : (serializeFlatB 200 Reactor.reasonOK exemplarBlock input).data.toList
        = Reactor.serialize (respOf 200 Reactor.reasonOK exemplarBlock input.data.toList) :=
      serializeFlatB_refines 200 Reactor.reasonOK exemplarBlock input
    have hdata : (serializeFlatB 200 Reactor.reasonOK exemplarBlock input).data
        = (Reactor.serialize (respOf 200 Reactor.reasonOK exemplarBlock input.data.toList)).toArray := by
      apply Array.toList_inj.mp
      rw [List.toList_toArray]; exact hr
    show serializeFlatB 200 Reactor.reasonOK exemplarBlock input
        = ByteArray.mk (Reactor.serialize (respOf 200 Reactor.reasonOK exemplarBlock input.data.toList)).toArray
    rw [← hdata]
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## Non-vacuity — a concrete request through BOTH serves, evaluated by the kernel -/

/-- A real request span; the flat serve echoes it into a 200 response, byte-identical to
the `List` twin (both evaluated). -/
def demoReq : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The flat serve produces a genuine HTTP/1.1 200 response echoing the request as body.
#guard (serveFlatEcho demoReq).size > 0
-- The flat serve and the List twin are byte-identical on the concrete request (kernel-eval).
#guard (serveFlatEcho demoReq).data.toList == (serveListEcho demoReq).data.toList
-- Genuine dependence on the input: a different request gives a different response.
#guard (serveFlatEcho demoReq).data.toList != (serveFlatEcho "GET /other HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8).data.toList

/-! ## Axiom audit -/

#print axioms serveFlatEcho_refines

end Datapath.ServeFlat
