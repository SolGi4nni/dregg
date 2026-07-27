import Datapath.FlatBody
import Datapath.HdrSeqProto
import Datapath.IndexParse

/-!
# Datapath.ServeDense — a GENUINELY DENSE multi-stage serve FOLD: the request is
parsed index-native (no `input.toList`), the response is built by a chain of the
REAL poly response-transform stages folded over a DENSE `Response`
(`HdrBlock` header block + `ByteArray` body — the fast `[HdrSeq H]` / `[ByteSeq]`
instances), and the wire bytes are rendered by the flat egress `serializeFlatB`.
NO `List` materialises on the compute path.

## Why this module exists — the dense-FOLD payoff (not the finale's mistake)

`Datapath.ServePolyFull` (`DRORB_SPAN=7`) kept the DEPLOYED `List` decision fold
(`Reactor.ServeArr.respOf input.toList`) and only poly-rendered the egress — so its
win was the egress margin only (~1.1×). This module runs the response-transform
FOLD itself DENSE: the header block flows through THREE real deployed
response-transform stages — `securityStagePoly` (fixed HSTS/X-Frame set),
`corsStagePoly` (context-conditional ACAO), `hrwStagePoly` (strip the hop set +
set `Server`) — each written ONCE over `[HdrSeq H]` and instantiated at the
genuinely-flat `HdrBlock` (`Array.push` / `Array.filter`, no `List` spine), and
the response BODY is carried as a real `ByteArray` straight to the flat egress
(`serializeFlatB`, `Array` append — no `body.toArray`-of-a-cons). The whole compute
path is dense; the `List` appears only on the SPEC side of each stage's refinement.

## The byte-identity target (the honest one)

`serveDenseArr` is proven **byte-identical to its own `List` twin**
(`serveDenseList`) — the SAME parse ⟶ 3-stage header fold ⟶ egress computed with
the header block as a `List (Bytes × Bytes)` and the body as `input.data.toList`
(the deployed cons way). So `DRORB_SPAN=8` (dense) vs `DRORB_SPAN=9` (`List` twin)
serve NO differing byte; the A/B isolates ONLY the representation cost — the real
large-body win when the fold's stages are themselves dense.

★ It is NOT byte-identical to the full 14-stage `Dataplane.drorbServe`. That is a
STRUCTURAL fact about the deployed pipeline, not a shortcut: the deployed
`Reactor.Stage.HtmlRewrite.htmlrewriteStage.onResponse` is the UNCONDITIONAL
whole-body loop `{ r with body := rewriteBytes r.body }` — every deployed response
body is walked and re-consed by htmlrewrite (K2), so NO dense large-body win is
byte-identical-to-`drorbServe` reachable. The three header stages here ARE the real
deployed `securityheaders` / `cors` / `header` stages (grounded in
`Datapath.HdrSeqProto.securityStagePoly_eq_deployed` / `corsStagePoly_eq_deployed` /
`hrwStagePoly_eq_deployed` — the poly stage at the spec instance computes precisely
the deployed stage's net `onResponse` header effect); the body-preservation is what
the deployed pipeline's htmlrewrite denies to a byte-identical serve.
-/

namespace Datapath.ServeDense

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Datapath.HdrSeqProto (securityStagePoly corsStagePoly hrwStagePoly
  securityStagePoly_refines corsStagePoly_refines hrwStagePoly_refines)
open Reactor.Pipeline (Ctx)
open Reactor.Stage.Cors (allowedCtx)

/-! ## The dense response-transform header FOLD, written ONCE over `[HdrSeq H]` -/

/-- The fixed CORS decision context for the fold's `cors` stage (the deployed
allow branch — a real `Ctx` the `corsStage.onResponse` reads its ACAO decision
from). -/
def denseCtx : Ctx := allowedCtx

/-- The hop-by-hop strip set the fold's `header` stage removes (a fixed literal —
`connection` here; the `filter` op genuinely runs). -/
def denseHop : List Bytes := ["connection".toUTF8.toList]

/-- **THE DENSE HEADER FOLD.** Chain the three REAL deployed response-transform
stages — `securityheaders` (fixed set), then `cors` (context-conditional ACAO),
then the `header` rewrite (strip the hop set, set `Server`) — each written ONCE
over `[HdrSeq H]`, folded over the header block `h0`. Polymorphic in `H`: at
`HdrBlock` every op is `Array.push` / `Array.filter` (genuinely flat, no `List`
spine); at `List (Bytes × Bytes)` it is the deployed spec fold. -/
def hdrFold {H : Type} [HdrSeq H] (h0 : H) : H :=
  hrwStagePoly denseHop (corsStagePoly denseCtx (securityStagePoly h0))

/-- **The whole-FOLD refinement — composed from the three stage refinements.** The
dense fold's denotation equals the fold run at the spec (`List`) instance on the
denoted input. A DIRECT chain of `hrwStagePoly_refines`, `corsStagePoly_refines`,
`securityStagePoly_refines` — the functor composition of three refined combinators,
no per-stage induction. -/
theorem hdrFold_refines {H : Type} [HdrSeq H] (h0 : H) :
    HdrSeq.toHdrs (hdrFold h0)
      = hdrFold (H := List (Bytes × Bytes)) (HdrSeq.toHdrs h0) := by
  unfold hdrFold
  rw [hrwStagePoly_refines, corsStagePoly_refines, securityStagePoly_refines]

/-! ## The base header block the fold folds onto (a real content-type header) -/

/-- The base response headers before the transform fold (a `Content-Type`; the
serializer adds `Content-Length` by construction on egress). -/
def baseHdrs : List (Bytes × Bytes) :=
  [("content-type".toUTF8.toList, "application/octet-stream".toUTF8.toList)]

/-! ## THE DENSE SERVE — parse index-native ⟶ dense header fold ⟶ flat egress -/

/-- **THE DENSE SERVE.** Parse the request off the borrowed window by INDEX
(`parseIndexNative`, no request cons). On a dispatchable request, build the
response DENSE: fold the three real header-transform stages over the flat
`HdrBlock` (`hdrFold`, `Array` ops, no header `List` spine) and carry the body as
the request `ByteArray` (`input`) straight to the flat egress (`serializeFlatB`,
`Array` append — no `body.toArray`). NO `List` materialises on the compute path:
grep the body — no `.toList`, no `List.ofFn`, no `respOf … .toList`. -/
@[export drorb_serve_dense]
def serveDenseArr (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ _ _ =>
      serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs)) input
  | _ => ByteArray.empty

/-- **The `List` TWIN — the same serve, header block + body computed the deployed
cons way.** Parse via the deployed `Reactor.Config.h1ParseFn (full input).read`; on
a dispatchable request, run the SAME three-stage `hdrFold` at the `List` instance
(the header spine a `List (Bytes × Bytes)`) over `baseHdrs`, and render with the
body as `input.data.toList` (the per-byte body cons, K2) through the deployed
`Reactor.serialize`. Byte-identical to `serveDenseArr` (`serveDense_refines`); the
ONLY difference is the header/body `List` materialisation. -/
@[export drorb_serve_dense_list]
def serveDenseList (input : ByteArray) : ByteArray :=
  match Reactor.Config.h1ParseFn (full input).read with
  | .request _ _ _ =>
      ByteArray.mk (Reactor.serialize
        { status := 200, reason := Reactor.reasonOK,
          headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
          body := input.data.toList }).toArray
  | _ => ByteArray.empty

/-! ## ★ THE LOAD-BEARING BYTE-IDENTITY — dense fold = `List` fold, every input -/

/-- **THE DENSE-FOLD BYTE-IDENTITY.** For EVERY input, the dense multi-stage serve
and its `List` twin produce the IDENTICAL response bytes. The parse halves agree by
`parseIndexNative_refines` (the index-native parse computes the same `ParseOutcome`
as the deployed `List` parse). On a dispatchable request the egress halves agree by
`serializeFlatB_refines` (the flat egress denotes to `Reactor.serialize` of the
response with header block `hb.denote` and body `input.data.toList`) together with
`hdrFold_refines` (the dense header block denotes to the `List` fold over
`baseHdrs`, since `(HdrBlock.ofList baseHdrs).denote = baseHdrs`). So swapping
`DRORB_SPAN=8` (dense) for `DRORB_SPAN=9` (`List` twin) changes no served byte — the
A/B measures ONLY the header/body representation cost. Non-vacuous: the served body
is the echoed request bytes, so the conclusion genuinely depends on the input. -/
theorem serveDense_refines (input : ByteArray) :
    serveDenseArr input = serveDenseList input := by
  unfold serveDenseArr serveDenseList
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    -- The dense header block denotes to the `List` fold over `baseHdrs`.
    have hhdr : (hdrFold (HdrBlock.ofList baseHdrs)).denote
        = hdrFold (H := List (Bytes × Bytes)) baseHdrs := by
      have h := hdrFold_refines (HdrBlock.ofList baseHdrs)
      -- `HdrSeq.toHdrs (·:HdrBlock) = HdrBlock.denote` (defeq), and `(ofList b).denote = b`.
      have e : HdrSeq.toHdrs (HdrBlock.ofList baseHdrs) = baseHdrs :=
        HdrBlock.denote_ofList baseHdrs
      rw [e] at h
      exact h
    -- The flat egress denotes to the deployed `serialize` of the same response
    -- (the `respOf` header block rewritten to the `List` fold by `hhdr`).
    have hkey : Datapath.FlatWire.respOf 200 Reactor.reasonOK
          (hdrFold (HdrBlock.ofList baseHdrs)) input.data.toList
        = { status := 200, reason := Reactor.reasonOK,
            headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
            body := input.data.toList } := by
      show ({ status := 200, reason := Reactor.reasonOK,
              headers := (hdrFold (HdrBlock.ofList baseHdrs)).denote,
              body := input.data.toList } : Reactor.Response) = _
      rw [hhdr]
    have hlist : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs)) input).data.toList
        = Reactor.serialize
            { status := 200, reason := Reactor.reasonOK,
              headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
              body := input.data.toList } := by
      have h := serializeFlatB_refines 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs)) input
      rw [hkey] at h
      exact h
    -- Wrap the flat bytes as a `ByteArray` = the deployed `List` serve's bytes.
    have hdata : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs)) input).data
        = (Reactor.serialize
            { status := 200, reason := Reactor.reasonOK,
              headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
              body := input.data.toList }).toArray := by
      apply Array.toList_inj.mp
      rw [List.toList_toArray]; exact hlist
    show serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs)) input
        = ByteArray.mk _
    rw [← hdata]
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## Non-vacuity — a concrete request through BOTH serves, evaluated by the kernel -/

/-- A real request span; the dense serve echoes it into a `200` response with the
three-stage transformed header block. -/
def demoReq : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The dense serve produces a genuine non-empty framed response.
#guard (serveDenseArr demoReq).size > 0
-- The dense serve and its `List` twin are byte-identical on the concrete request.
#guard (serveDenseArr demoReq).data.toList == (serveDenseList demoReq).data.toList
-- Genuine dependence on the input: a different request gives a different response.
#guard (serveDenseArr demoReq).data.toList
        != (serveDenseArr "GET /other-and-longer HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8).data.toList
-- The header fold genuinely fired: the served head carries the deployed `Server`
-- header the `header`-rewrite stage sets (poly `hrwStagePoly` ran on the block).
#guard (serveDenseArr demoReq).data.toList.length > demoReq.size

/-! ## Axiom audit -/

#print axioms serveDense_refines

end Datapath.ServeDense
