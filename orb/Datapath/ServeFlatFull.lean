import Datapath.ServeFlat
import Datapath.FlatBody
import Reactor.ServeArr
import Reactor.Ingress
import Reactor.H2Ingress

/-!
# Datapath.ServeFlatFull — the ASSEMBLED FULL flat serve over the REAL deployed
14-stage pipeline (all stages, real routing — NOT the echo exemplar), rendered
through the FLAT egress serializer, proven byte-identical to the DEPLOYED
`Dataplane.drorbServe`.

`Datapath.ServeFlat.serveFlatEcho` (the `DRORB_SPAN=1` exemplar) measured ~3.4× on
an 8 KB body — but it ECHOES the request as the body and runs only the flat
security-header stage; it is NOT what the deployed default serves (the deployed
default runs the full 14-stage `Reactor.Deploy.deployStagesFull2` fold and routes
to the real handler). Its byte-identity is to its OWN `List` twin, not to
`Dataplane.drorbServe`.

This module closes that gap on the axis that is provable in one additive pass: it
assembles a serve that

* runs the **REAL deployed 14-stage pipeline** (`Reactor.ServeArr.respOf`, the exact
  built `Reactor.Response` inside `servePipelineFull2` — all of jwt / basicauth /
  ipfilter / rate / cache / redirect / traversal / policy / headerRewrite / cors /
  gzip / htmlrewrite / securityheaders / header, the real route table + handler), so
  the served bytes are the ACTUAL deployed response, not an echo; and
* renders that built response through the **FLAT egress serializer**
  `Datapath.FlatBody.serializeFlatB` — the response header block is pushed/rendered
  on the flat `HdrBlock` (`Array`, no response-head `List` spine, K5) and the body is
  carried as a genuine `ByteArray` and bulk-appended (`++ fbody.data`, no
  `body.toArray`-of-a-cons, R3) — instead of the deployed path's
  `List`-`serialize` + `.toArray` round-trip.

`serveFlatFull_refines` proves it **byte-identical** to the deployed serve
(`deployedServeRef`, which `Dataplane.drorbServe` is definitionally — closed in
`Dataplane.serveFlatFull_eq_drorbServe`, where `drorbServe` is in scope). The
byte-identity holds for BOTH the h2c prior-knowledge fork and the HTTP/1.1 14-stage
fold, so `DRORB_SPAN=3` serves the SAME bytes as the deployed default on every real
request — the measurement is deployed-representative, not an echo.

## HONEST SCOPE — what is flat and what is NOT

The flatness this serve adds over the deployed `List` serve is the **EGRESS**: the
response header block (`HdrBlock`, `Array.push`/flat render) and the response body
(`ByteArray`, bulk append) never materialize the response-head `List` spine or the
`body.toArray`-of-a-cons the deployed `serialize`/`.toArray` build. This is exactly
the class of flattening `Reactor.ServeArr.serveArr` captures, reached here through
the `FlatHeaders`/`FlatBody` flat-block machinery.

What this serve does **NOT** flatten — pinned by byte-identity to the 14-stage
deployed serve, and named precisely:

* **The request cons (K1).** The deployed pipeline `servePipelineFull2` consumes
  `input.toList` (the reactor parse `deploySubs`, the correlation-id hash, the render
  all read the request `List`). Feeding it the index-native `parseIndexNative`
  (`Datapath.IndexParse`, no request cons) requires the whole decision pipeline to
  consume a `SpanBytes` — the root change (`Bytes := List UInt8`), the "catastrophic
  reprove". So `input.toList` remains on this path; `parseIndexNative` is NOT wired
  in (it would produce a byte-identical parse but the pipeline re-parses internally).

* **The internal per-stage `List` materializations.** `runPipeline` builds a
  `Reactor.Response` whose `headers : List` and `body : Bytes = List UInt8` fields are
  `List`-typed; the 14 stages fold over those `List`s. `serializeFlatB` flattens only
  the FINAL egress render of that built response, not the intermediate `List`s the
  fold threads. Removing those needs the fold itself re-expressed over
  `HdrBlock`/`ByteArray` end-to-end — the composition the individually-grounded flat
  stages (`FlatStage_*.lean`) are the pieces of, still to be chained into a fold equal
  to `servePipelineFull2` (a large multi-file proof, not this pass).

Consequently the MEASURED speed vs the deployed `List` serve is the egress-flattening
margin only — NOT the exemplar's 3.4× (the exemplar is fast because it SKIPS the
14-stage fold; a serve byte-identical to that fold cannot). This is the honest
deployed-representative number: the real 14-stage flat serve is byte-identical to the
deployed default and flat on egress; the pipeline-internal `List` cost is what a
genuinely-faster real flat serve must remove next (the root `Bytes`/`Response.body`
migration), which is a separate step.
-/

namespace Datapath.ServeFlatFull

open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatWire (respOf)

/-- **The deployed serve, as the reference expression this flat serve is proven
byte-identical to.** This is DEFINITIONALLY `Dataplane.drorbServe`'s body (the h2c
prior-knowledge fork to the real H2 engine, else the full 14-stage HTTP/1.1 fold),
written here — below `Dataplane` — so `serveFlatFull_refines` can be stated without a
`Dataplane` import cycle. `Dataplane.serveFlatFull_eq_drorbServe` closes
`deployedServeRef = drorbServe` by `rfl`/unfold where `drorbServe` is in scope. -/
def deployedServeRef (input : ByteArray) : ByteArray :=
  if Reactor.Ingress.hasH2Preface input.toList then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else
    ByteArray.mk (Reactor.Deploy.servePipelineFull2 input.toList).toArray

/-- **THE ASSEMBLED FULL FLAT SERVE.** Fork on the h2c connection preface exactly as
the deployed serve (drive the real H2 engine on prior knowledge); otherwise run the
REAL deployed 14-stage pipeline (`Reactor.ServeArr.respOf input.toList` — the exact
built `Reactor.Response` `servePipelineFull2` serializes, all stages + real routing)
and render it through the FLAT egress serializer `serializeFlatB`: the response header
block on the flat `HdrBlock` (`HdrBlock.ofList r.headers`, flat render — no response-head
`List` spine) and the body as a genuine `ByteArray` (`ByteArray.mk r.body.toArray`, bulk
append — no `body.toArray`-of-a-cons at egress). Byte-identical to the deployed serve
(`serveFlatFull_refines`); the egress `List` round-trip is what is removed. -/
@[export drorb_serve_full]
def serveFlatFull (input : ByteArray) : ByteArray :=
  if Reactor.Ingress.hasH2Preface input.toList then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else
    let r := Reactor.ServeArr.respOf input.toList
    serializeFlatB r.status r.reason (HdrBlock.ofList r.headers) (ByteArray.mk r.body.toArray)

/-- **The flat egress serializer of ANY built response is byte-identical to the
deployed `serialize`, wrapped as the wire `ByteArray`.** For any `Reactor.Response`
`r`, rendering it through `serializeFlatB` (flat `HdrBlock` header block +
`ByteArray` body) equals `ByteArray.mk (Reactor.serialize r).toArray` — the exact
bytes the deployed serve emits from `r`. Equality transfer to
`serializeFlatB_refines` (the flat egress = `serialize` byte-identity), the
`HdrBlock.denote_ofList` / `List.toList_toArray` denotation bridges, and the
`Array.toList_inj` `ByteArray`-equality closer. This is the per-response core of the
full flat serve's byte-identity. -/
theorem serializeFlatB_resp (r : Reactor.Response) :
    serializeFlatB r.status r.reason (HdrBlock.ofList r.headers) (ByteArray.mk r.body.toArray)
      = ByteArray.mk (Reactor.serialize r).toArray := by
  have hbody : (ByteArray.mk r.body.toArray).data.toList = r.body := by
    show r.body.toArray.toList = r.body
    rw [List.toList_toArray]
  have hkey : respOf r.status r.reason (HdrBlock.ofList r.headers)
        (ByteArray.mk r.body.toArray).data.toList = r := by
    show ({ status := r.status, reason := r.reason,
            headers := (HdrBlock.ofList r.headers).denote,
            body := (ByteArray.mk r.body.toArray).data.toList } : Reactor.Response) = r
    rw [HdrBlock.denote_ofList, hbody]
  have hlist : (serializeFlatB r.status r.reason (HdrBlock.ofList r.headers)
        (ByteArray.mk r.body.toArray)).data.toList = Reactor.serialize r := by
    have h := serializeFlatB_refines r.status r.reason (HdrBlock.ofList r.headers)
      (ByteArray.mk r.body.toArray)
    -- `Refines a d` unfolds to `d.data.toList = a`; rewrite the spec response to `r`
    rw [hkey] at h
    exact h
  have hdata : (serializeFlatB r.status r.reason (HdrBlock.ofList r.headers)
        (ByteArray.mk r.body.toArray)).data = (Reactor.serialize r).toArray := by
    apply Array.toList_inj.mp
    rw [List.toList_toArray]; exact hlist
  show serializeFlatB r.status r.reason (HdrBlock.ofList r.headers)
      (ByteArray.mk r.body.toArray) = ByteArray.mk (Reactor.serialize r).toArray
  rw [← hdata]

/-- **THE FULL FLAT-EGRESS BYTE-IDENTITY.** For EVERY input, the assembled full flat
serve produces the IDENTICAL bytes to the deployed serve (`deployedServeRef`, i.e.
`Dataplane.drorbServe`). Both fork on the h2c preface to the same `serveH2c`; on the
HTTP/1.1 path the flat egress `serializeFlatB` of the REAL deployed built response
(`Reactor.ServeArr.respOf`, the full 14-stage fold) is byte-identical to
`ByteArray.mk (serialize thatResponse).toArray` — the exact bytes the deployed serve
emits (`servePipelineFull2 = serialize ∘ respOf`, `Reactor.ServeArr.respOf_serialize`)
— by `serializeFlatB_refines` (flat header block + flat `ByteArray` body =
`serialize`), the `HdrBlock.denote_ofList` / `List.toList_toArray` denotation bridges,
and the `Array.toList_inj` `ByteArray`-equality closer. Non-vacuous: the served body is
the real routed response (a `GET /health` gives the deployed health body, an 8 KB
`POST /echo` the deployed echo body — the conclusion genuinely depends on the request
bytes AND the full pipeline's routing). NO deployed byte changes. -/
theorem serveFlatFull_refines (input : ByteArray) :
    serveFlatFull input = deployedServeRef input := by
  unfold serveFlatFull deployedServeRef
  by_cases h : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h, if_true]
  · simp only [h, if_false, Bool.false_eq_true]
    -- HTTP/1.1: the flat egress of the REAL deployed built response = deployed serialize
    rw [Reactor.ServeArr.respOf_serialize]
    exact serializeFlatB_resp (Reactor.ServeArr.respOf input.toList)

/-! ## Non-vacuity — a concrete real request through the full flat serve, evaluated -/

/-- A real `GET /health` request (routes to the deployed handler, not an echo). -/
def demoReq : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The full flat serve produces a genuine deployed response (non-empty, routed).
#guard (serveFlatFull demoReq).size > 0
-- The full flat serve is byte-identical to the deployed serve on the real request
-- (kernel-evaluated — the full 14-stage fold, flat egress).
#guard (serveFlatFull demoReq).data.toList == (deployedServeRef demoReq).data.toList
-- Genuine dependence on the request: a different target routes differently.
#guard (serveFlatFull demoReq).data.toList
        != (serveFlatFull "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8).data.toList

/-! ## Axiom audit -/

#print axioms serveFlatFull_refines

end Datapath.ServeFlatFull
