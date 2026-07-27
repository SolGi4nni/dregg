import Datapath.ServeDense
import Datapath.HtmlRewriteDense

/-!
# Datapath.ServeDenseFull — the DENSE serve that RUNS THE DEPLOYED BODY TRANSFORM
DENSE: parse index-native (no `input.toList`), fold the three real deployed header
stages over a flat `HdrBlock`, run the body through `rewriteBytesDense` (the
DENSE, `ByteArray`, index-native form of the deployed `Reactor.Stage.HtmlRewrite.
rewriteBytes` — the whole-body loop htmlrewrite runs on EVERY response), then render
the wire bytes with the flat egress `serializeFlatB`. The body flows dense THROUGH
the deployed html-rewrite; NO `List` materialises on the compute path.

## Why this module exists — closing the body-loop crux

`Datapath.ServeDense` (`DRORB_SPAN=8`) carried the body straight to egress
(`serializeFlatB … input`) — it never ran the deployed body transform. But the
deployed pipeline's `htmlrewriteStage.onResponse` runs `rewriteBytes r.body`
UNCONDITIONALLY on every response body (the K2 whole-body walk). This module runs
that SAME transform DENSE — `rewriteBytesDense` (`Datapath.HtmlRewriteDense`,
proven byte-identical to the deployed `rewriteBytes` by `rewriteBytesDense_refines`)
over the `ByteArray` body by index (`ByteArray.foldl feedF`, NO `input.toList`). So
the body loop that the deployed serve pays per response is now paid DENSE.

## The byte-identity target (the honest one)

`serveDenseFull` is proven **byte-identical to its own `List` twin**
(`serveDenseFullList`) — the SAME parse ⟶ 3-stage header fold ⟶ **deployed body
transform** ⟶ egress, but with the header block a `List (Bytes × Bytes)` and the
body the deployed `rewriteBytes input.data.toList` (the cons-list body walk, K2).
So `DRORB_SPAN=10` (dense) vs `DRORB_SPAN=11` (`List` twin) serve NO differing
byte; the A/B isolates ONLY the representation cost of running the deployed body
transform dense (`ByteArray`) vs consed (`List UInt8`) on a large HTML body.

★ HONEST SCOPE — it is NOT byte-identical to the full 14-stage `Dataplane.drorbServe`.
This is a THREE-header-stage serve whose BODY transform is the real deployed
`rewriteBytes` (run dense). The measured route is a large HTML body echoed through
the deployed html-rewrite; the body compute (`rewriteBytesDense`) is byte-identical
to what `drorbServe`'s htmlrewrite stage does to the body (`rewriteBytesDense_refines`).
The surrounding header/routing stages are O(header) not O(body), so they do not
move the body-representation ratio the A/B measures. The `List` appears only on the
SPEC side of each refinement (`hdrFold_refines`, `rewriteBytesDense_refines`,
`serializeFlatB_refines`, `parseIndexNative_refines`) — the compute path is dense.
-/

namespace Datapath.ServeDenseFull

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Datapath.ServeDense (hdrFold hdrFold_refines baseHdrs)
open Datapath.HtmlRewriteDense (rewriteBytesDense rewriteBytesDense_refines)
open Reactor.Stage.HtmlRewrite (rewriteBytes)

/-! ## THE DENSE SERVE — parse index-native ⟶ dense header fold ⟶ DENSE body transform ⟶ egress -/

/-- **THE DENSE SERVE WITH THE DEPLOYED BODY TRANSFORM.** Parse the request off the
borrowed window by INDEX (`parseIndexNative`, no request cons). On a dispatchable
request, build the response DENSE: fold the three real header-transform stages over
the flat `HdrBlock` (`hdrFold`, `Array` ops, no header `List` spine) and run the
request body through the DENSE deployed html-rewrite (`rewriteBytesDense input`,
`ByteArray.foldl feedF` by index — the real deployed `rewriteBytes` run dense), then
render with the flat egress (`serializeFlatB`, `Array` append). NO `List`
materialises on the compute path: grep the body — no `.toList`, no `List.ofFn`, no
`respOf … .toList`. -/
@[export drorb_serve_densefull]
def serveDenseFull (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ _ _ =>
      serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
        (rewriteBytesDense input)
  | _ => ByteArray.empty

/-- **The `List` TWIN — the same serve, header block + body computed the deployed
cons way.** Parse via the deployed `Reactor.Config.h1ParseFn`; on a dispatchable
request, run the SAME three-stage `hdrFold` at the `List` instance and run the body
through the DEPLOYED `rewriteBytes input.data.toList` (the per-byte body cons + the
cons-list tokenizer, K2), then render with the deployed `Reactor.serialize`.
Byte-identical to `serveDenseFull` (`serveDenseFull_refines`); the ONLY difference
is the header/body `List` materialisation. -/
@[export drorb_serve_densefull_list]
def serveDenseFullList (input : ByteArray) : ByteArray :=
  match Reactor.Config.h1ParseFn (full input).read with
  | .request _ _ _ =>
      ByteArray.mk (Reactor.serialize
        { status := 200, reason := Reactor.reasonOK,
          headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
          body := rewriteBytes input.data.toList }).toArray
  | _ => ByteArray.empty

/-! ## ★ THE LOAD-BEARING BYTE-IDENTITY — dense serve = `List` twin, every input -/

/-- **THE DENSE-SERVE-WITH-DEPLOYED-BODY BYTE-IDENTITY.** For EVERY input, the dense
serve (running the deployed body transform dense) and its `List` twin produce the
IDENTICAL response bytes. The parse halves agree by `parseIndexNative_refines`. On a
dispatchable request the egress halves agree by `serializeFlatB_refines` (the flat
egress denotes to `Reactor.serialize` of the response with header block `hb.denote`
and body `(rewriteBytesDense input).data.toList`), `hdrFold_refines` (the dense
header block denotes to the `List` fold over `baseHdrs`), and — the new link —
`rewriteBytesDense_refines` (the dense body transform denotes to the deployed
`rewriteBytes input.data.toList`). So swapping `DRORB_SPAN=10` (dense) for
`DRORB_SPAN=11` (`List` twin) changes no served byte — the A/B measures ONLY the
representation cost of the deployed body transform. Non-vacuous: the served body is
the request bytes run through the real deployed html-rewrite, so the conclusion
genuinely depends on the input. -/
theorem serveDenseFull_refines (input : ByteArray) :
    serveDenseFull input = serveDenseFullList input := by
  unfold serveDenseFull serveDenseFullList
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    -- The dense header block denotes to the `List` fold over `baseHdrs`.
    have hhdr : (hdrFold (HdrBlock.ofList baseHdrs)).denote
        = hdrFold (H := List (Bytes × Bytes)) baseHdrs := by
      have h := hdrFold_refines (HdrBlock.ofList baseHdrs)
      have e : HdrSeq.toHdrs (HdrBlock.ofList baseHdrs) = baseHdrs :=
        HdrBlock.denote_ofList baseHdrs
      rw [e] at h
      exact h
    -- The dense body transform denotes to the deployed `rewriteBytes` on the body list.
    have hbody : (rewriteBytesDense input).data.toList = rewriteBytes input.data.toList :=
      rewriteBytesDense_refines input
    -- The flat egress denotes to the deployed `serialize` of the response with the
    -- `List`-fold header block and the deployed-rewritten body.
    have hkey : Datapath.FlatWire.respOf 200 Reactor.reasonOK
          (hdrFold (HdrBlock.ofList baseHdrs)) (rewriteBytesDense input).data.toList
        = { status := 200, reason := Reactor.reasonOK,
            headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
            body := rewriteBytes input.data.toList } := by
      show ({ status := 200, reason := Reactor.reasonOK,
              headers := (hdrFold (HdrBlock.ofList baseHdrs)).denote,
              body := (rewriteBytesDense input).data.toList } : Reactor.Response) = _
      rw [hhdr, hbody]
    have hlist : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
            (rewriteBytesDense input)).data.toList
        = Reactor.serialize
            { status := 200, reason := Reactor.reasonOK,
              headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
              body := rewriteBytes input.data.toList } := by
      have h := serializeFlatB_refines 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
        (rewriteBytesDense input)
      rw [hkey] at h
      exact h
    have hdata : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
            (rewriteBytesDense input)).data
        = (Reactor.serialize
            { status := 200, reason := Reactor.reasonOK,
              headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
              body := rewriteBytes input.data.toList }).toArray := by
      apply Array.toList_inj.mp
      rw [List.toList_toArray]; exact hlist
    show serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
          (rewriteBytesDense input)
        = ByteArray.mk _
    rw [← hdata]
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## Non-vacuity — a concrete request whose body is HTML, dense-served through both -/

/-- A real request whose BODY is an HTML fragment the deployed html-rewrite rewrites
(`<b>hi` → `hi`), so the dense body transform genuinely fires. -/
def demoReq : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

-- The dense serve produces a genuine non-empty framed response.
#guard (serveDenseFull demoReq).size > 0
-- The dense serve and its `List` twin are byte-identical on the concrete request.
#guard (serveDenseFull demoReq).data.toList == (serveDenseFullList demoReq).data.toList
-- Genuine dependence on the input: a different request gives a different response.
#guard (serveDenseFull demoReq).data.toList
        != (serveDenseFull "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 8\r\n\r\n<i>other".toUTF8).data.toList

/-! ## Axiom audit -/

#print axioms serveDenseFull_refines

end Datapath.ServeDenseFull
