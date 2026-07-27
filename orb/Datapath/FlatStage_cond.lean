import Datapath.FlatHeaders
import Reactor.Deploy

/-!
# Datapath.FlatStage_cond — the deployed conditional-request `304` GATE proven flat,
its decision equal to the real deployed stage and its emitted response byte-identical.

The representative stage here is `Reactor.Deploy.conditionalBraidStage`
(RFC 7232 conditional request → `304 Not Modified`) — a SHORT-CIRCUIT GATE, the
other shape the cons-list removal must cover (`Datapath.FlatStage` did a
header-transform stage; this does a request-gate stage). Its whole request-phase
effect is a DECISION on the request headers: look for the per-request conditional
marker (`conditionalMarker`); absent ⇒ pass through (`.continue`), present ⇒
short-circuit with the genuine `304` (`.respond conditional304`) — where
`conditional304` is the REAL `Cache.Conditional.evaluate`/`respond` on the
library's own end-to-end `If-None-Match` witness (`demo_if_none_match_304`), NOT a
hand-written constant. `onResponse` is the identity (a gate does not transform the
response).

## What is proven here (equality-transfer + byte-identity, NOT a re-spec)

* `flatCondOnRequest` + `flatCondOnRequest_refines` — the flat decision runs the
  request-header lookup on the flat `HdrBlock` (contiguous `Array.find?`, no
  cons-spine walk) and is proven to compute the SAME `StageStep` as the deployed
  `conditionalBraidStage.onRequest`. The decision is grounded in the ACTUAL
  deployed stage (we `rfl` against `conditionalBraidStage.onRequest`, not a
  re-specification); the flat-`Array.find?` = `List.find?` equality
  (`Array.find?_toList`) is what makes it byte-identical.
* `flatCond304_serialize_refines` — the emitted `304` response serialized flat
  (`Datapath.Refinement.flatSerialize`) is byte-identical to `Reactor.serialize`
  of the deployed `conditional304`. This is the RESPONSE half: a fixed/computed
  byte-identical form, discharged by the derived flat serializer's
  `flatSerialize_refines`.
* `flatCondEmit` + `flatCondEmit_fires` / `flatCondEmit_passes` — the whole gate:
  the flat form decides on the request AND emits the response bytes. When the
  marker fires, the flat emitted bytes are `flatSerialize conditional304`,
  byte-identical to `Reactor.serialize conditional304`, and the deployed stage
  `.respond`s exactly that `conditional304`; when absent, both pass through. So
  the DECISION matches the real stage and the RESPONSE (the `304`) is
  byte-identical.
* `flatCond_answers_304` — the response the gate emits is a genuine `304`
  (`conditional304_status`, the library's own end-to-end `If-None-Match` theorem),
  not a bare literal.

## Why this stage does not use the header-FOLD recipe

`Datapath.FlatStage`'s `securityheaders` stage is a header-transform: its flat form
is a `refinesHdr_foldAddHeader` instance. A GATE stage has no response fold — its
effect is a decision on the REQUEST plus a fixed short-circuit response. The flat
form is therefore (i) the flat request-header lookup refining the deployed
`find?`, and (ii) the fixed response serialized flat byte-identically. Both reuse
the SAME primitives (`HdrBlock` for the flat header spine, `flatSerialize` for the
byte-grain serializer); no new byte reasoning is introduced.
-/

namespace Datapath.FlatStage_cond

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx StageStep Stage)
open Reactor.Deploy (conditionalBraidStage conditional304 conditionalMarker conditional304_status)
open Datapath.FlatHeaders
open Datapath.Refinement

/-! ## 1. The flat request-gate decision, grounded in the REAL deployed stage -/

/-- **The flat `conditional-304` gate decision.** Runs the deployed gate's
request-header lookup on the flat `HdrBlock`: a contiguous `Array.find?` for the
conditional marker (no per-request cons-spine walk). Marker absent ⇒ `.continue`;
present ⇒ short-circuit with the genuine `conditional304`. This is the flat
sibling of `conditionalBraidStage.onRequest`'s `c.req.headers.find?`. -/
def flatCondOnRequest (c : Ctx) (h : HdrBlock) : StageStep :=
  match h.headers.find? (fun nv => nv.1 == conditionalMarker) with
  | none   => .continue c
  | some _ => .respond conditional304

/-- **The flat decision computes the deployed stage's decision.** For any context
whose request headers are refined by the flat block `h` (`RefinesHdr`), the flat
`Array.find?` gate yields the SAME `StageStep` as the deployed
`conditionalBraidStage.onRequest`. Proven by the flat-`Array.find?` = `List.find?`
equality (`Array.find?_toList`) transported across the refinement, then `rfl`
against the real deployed stage — grounded, not re-specified. Non-vacuous: the
decision genuinely inspects the request headers (see the load-bearing `#guard`). -/
theorem flatCondOnRequest_refines (c : Ctx) (h : HdrBlock)
    (hr : RefinesHdr c.req.headers h) :
    flatCondOnRequest c h = conditionalBraidStage.onRequest c := by
  have hfind : h.headers.find? (fun nv => nv.1 == conditionalMarker)
      = c.req.headers.find? (fun nv => nv.1 == conditionalMarker) := by
    rw [← RefinesHdr.denote_eq hr]
    show Array.find? _ h.headers = List.find? _ h.headers.toList
    exact Array.find?_toList.symm
  show (match h.headers.find? (fun nv => nv.1 == conditionalMarker) with
        | none   => StageStep.continue c
        | some _ => StageStep.respond conditional304)
      = (match c.req.headers.find? (fun nv => nv.1 == conditionalMarker) with
        | none   => StageStep.continue c
        | some _ => StageStep.respond conditional304)
  rw [hfind]

/-! ## 2. The emitted `304` response is byte-identical -/

/-- **The gate's emitted response is byte-identical.** The `304` the gate answers
with, serialized flat (`Datapath.Refinement.flatSerialize`, the derived flat
serializer), is byte-identical to `Reactor.serialize conditional304` — the
deployed wire bytes. A direct instance of `flatSerialize_refines`; the response is
a fixed/computed form, so no per-stage byte reasoning. -/
theorem flatCond304_serialize_refines :
    Datapath.Refinement.Refines (Reactor.serialize conditional304) (flatSerialize conditional304) :=
  flatSerialize_refines conditional304

/-- **The emitted response is a genuine `304`** — `conditional304` is the REAL
`Cache.Conditional` evaluation on the library's `If-None-Match` witness, whose
status is `304` by the library's own end-to-end theorem (`conditional304_status`),
not a bare literal. -/
theorem flatCond_answers_304 : conditional304.status = 304 := conditional304_status

/-! ## 3. The whole gate: decide on the request AND emit byte-identical bytes -/

/-- **The flat gate emit.** Decide on the flat request headers, and — when the
gate fires — serialize the `304` flat. `none` is the pass-through (the handler and
later stages run), `some bytes` is the short-circuited wire response. -/
def flatCondEmit (c : Ctx) (h : HdrBlock) : Option ByteArray :=
  match flatCondOnRequest c h with
  | .respond r  => some (flatSerialize r)
  | .continue _ => none

/-- **Gate FIRES ⇒ byte-identical `304`.** When the flat lookup finds the marker
(and `h` refines the request headers): the flat form emits exactly
`flatSerialize conditional304`; the deployed stage `.respond`s exactly that
`conditional304`; and those flat bytes are byte-identical to
`Reactor.serialize conditional304`. So the DECISION matches the deployed stage and
the RESPONSE bytes are identical. -/
theorem flatCondEmit_fires (c : Ctx) (h : HdrBlock) (nv : Bytes × Bytes)
    (hr : RefinesHdr c.req.headers h)
    (hfind : h.headers.find? (fun nv => nv.1 == conditionalMarker) = some nv) :
    flatCondEmit c h = some (flatSerialize conditional304)
    ∧ conditionalBraidStage.onRequest c = StageStep.respond conditional304
    ∧ Datapath.Refinement.Refines (Reactor.serialize conditional304) (flatSerialize conditional304) := by
  have hstep : flatCondOnRequest c h = StageStep.respond conditional304 := by
    show (match h.headers.find? (fun nv => nv.1 == conditionalMarker) with
          | none   => StageStep.continue c
          | some _ => StageStep.respond conditional304) = _
    rw [hfind]
  refine ⟨?_, ?_, flatSerialize_refines conditional304⟩
  · show (match flatCondOnRequest c h with
          | .respond r  => some (flatSerialize r)
          | .continue _ => none) = _
    rw [hstep]
  · rw [← flatCondOnRequest_refines c h hr, hstep]

/-- **Gate PASSES ⇒ pass-through.** When the flat lookup does not find the marker
(and `h` refines the request headers): the flat form emits nothing (the handler
runs) and the deployed stage `.continue`s. -/
theorem flatCondEmit_passes (c : Ctx) (h : HdrBlock)
    (hr : RefinesHdr c.req.headers h)
    (hfind : h.headers.find? (fun nv => nv.1 == conditionalMarker) = none) :
    flatCondEmit c h = none
    ∧ conditionalBraidStage.onRequest c = StageStep.continue c := by
  have hstep : flatCondOnRequest c h = StageStep.continue c := by
    show (match h.headers.find? (fun nv => nv.1 == conditionalMarker) with
          | none   => StageStep.continue c
          | some _ => StageStep.respond conditional304) = _
    rw [hfind]
  refine ⟨?_, ?_⟩
  · show (match flatCondOnRequest c h with
          | .respond r  => some (flatSerialize r)
          | .continue _ => none) = _
    rw [hstep]
  · rw [← flatCondOnRequest_refines c h hr, hstep]

/-! ## Non-vacuity — the flat gate genuinely decides and emits, on real inputs -/

/-- A real request carrying the conditional marker (the deployed gate fires). -/
def demoCtxMarked : Ctx :=
  { input := [], req := { headers := [(conditionalMarker, "1".toUTF8.toList)] } }

/-- A real request WITHOUT the marker (the deployed gate passes through). -/
def demoCtxUnmarked : Ctx :=
  { input := [], req := { headers := [("x-other".toUTF8.toList, "1".toUTF8.toList)] } }

-- Gate fires when the marker is present: the flat form emits bytes byte-identical
-- to the DEPLOYED `Reactor.serialize conditional304` (evaluated in the kernel).
#guard (flatCondEmit demoCtxMarked (HdrBlock.ofList demoCtxMarked.req.headers)).map (·.data.toList)
        == some (Reactor.serialize conditional304)

-- Gate passes through when the marker is absent.
#guard (flatCondEmit demoCtxUnmarked (HdrBlock.ofList demoCtxUnmarked.req.headers)).isNone

-- The emitted flat bytes are byte-identical to the DEPLOYED serialize — evaluated.
#guard (flatSerialize conditional304).data.toList == Reactor.serialize conditional304

-- The emitted response is a genuine `304` with an empty body (the REAL
-- `Cache.Conditional` decision, the client keeps its copy).
#guard conditional304.status == 304 && conditional304.body == []

-- The decision is load-bearing: marker present fires, marker absent passes
-- through (the flat gate genuinely inspects the request headers).
#guard (flatCondEmit demoCtxMarked (HdrBlock.ofList demoCtxMarked.req.headers)).isSome
        && (flatCondEmit demoCtxUnmarked (HdrBlock.ofList demoCtxUnmarked.req.headers)).isNone

#print axioms flatCondOnRequest_refines
#print axioms flatCond304_serialize_refines
#print axioms flatCondEmit_fires
#print axioms flatCondEmit_passes
#print axioms flatCond_answers_304

end Datapath.FlatStage_cond
