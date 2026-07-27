import Datapath.ServeDenseFull
import Datapath.HtmlRewriteDense2

/-!
# Datapath.ServeDenseFull2 — the FULLY-DENSE-TOKENIZER serve, byte-identical to the
`List` twin `serveDenseFullList` (DRORB_SPAN=11).

`Datapath.ServeDenseFull.serveDenseFull` (DRORB_SPAN=10) runs the deployed
html-rewrite body transform dense at the INPUT/OUTPUT (`rewriteBytesDense`), but the
TOKENIZER STATE stays a cons-list (`feedF`'s `curRev : List UInt8` — a per-byte
`cons`, the O(body) cost that caps that win at ~2.35×). This module swaps in
`Datapath.HtmlRewriteDense2.rewriteBytesDense2` — the FULLY-dense tokenizer whose
state (`FStateD`: `ByteArray` current run + `Array DToken` tokens) has NO token
`List` on the compute path (`rewriteBytesDense2_refines` proves it byte-identical
to the deployed `rewriteBytes`).

So `serveDenseFull2` is byte-identical to the SAME `List` twin `serveDenseFullList`
(DRORB_SPAN=11) that `serveDenseFull` matches — the A/B `=12` vs `=11` isolates the
FULL body-transform representation cost (fully-dense tokenizer vs the deployed
cons-list tokenizer + body cons), and `=12` vs `=10` isolates precisely the
token-`List` increment.
-/

namespace Datapath.ServeDenseFull2

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Datapath.ServeDense (hdrFold hdrFold_refines baseHdrs)
open Datapath.ServeDenseFull (serveDenseFullList)
open Datapath.HtmlRewriteDense2 (rewriteBytesDense2 rewriteBytesDense2_refines)
open Reactor.Stage.HtmlRewrite (rewriteBytes)

/-- **THE FULLY-DENSE-TOKENIZER SERVE.** Parse the request off the borrowed window by
INDEX, fold the three real header-transform stages over the flat `HdrBlock`, and run
the request body through the FULLY-dense html-rewrite (`rewriteBytesDense2` — the
tokenizer state a `ByteArray`/`Array`, NO token `List`), then render with the flat
egress. NO `List` materialises on the compute path — including the tokenizer state. -/
@[export drorb_serve_densefull2]
def serveDenseFull2 (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ _ _ =>
      serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
        (rewriteBytesDense2 input)
  | _ => ByteArray.empty

/-- **THE BYTE-IDENTITY.** For EVERY input, the fully-dense-tokenizer serve produces
the IDENTICAL response bytes as the `List` twin `serveDenseFullList` (DRORB_SPAN=11).
Same structure as `serveDenseFull_refines`, but the body link is
`rewriteBytesDense2_refines` (the fully-dense tokenizer denotes to the deployed
`rewriteBytes`). So swapping `=12` (fully dense) for `=11` (`List` twin) or `=10`
(input/output dense, token-`List`) changes no served byte. Non-vacuous: the served
body is the request bytes run through the real deployed html-rewrite. -/
theorem serveDenseFull2_refines (input : ByteArray) :
    serveDenseFull2 input = serveDenseFullList input := by
  unfold serveDenseFull2 serveDenseFullList
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    have hhdr : (hdrFold (HdrBlock.ofList baseHdrs)).denote
        = hdrFold (H := List (Bytes × Bytes)) baseHdrs := by
      have h := hdrFold_refines (HdrBlock.ofList baseHdrs)
      have e : HdrSeq.toHdrs (HdrBlock.ofList baseHdrs) = baseHdrs :=
        HdrBlock.denote_ofList baseHdrs
      rw [e] at h
      exact h
    have hbody : (rewriteBytesDense2 input).data.toList = rewriteBytes input.data.toList :=
      rewriteBytesDense2_refines input
    have hkey : Datapath.FlatWire.respOf 200 Reactor.reasonOK
          (hdrFold (HdrBlock.ofList baseHdrs)) (rewriteBytesDense2 input).data.toList
        = { status := 200, reason := Reactor.reasonOK,
            headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
            body := rewriteBytes input.data.toList } := by
      show ({ status := 200, reason := Reactor.reasonOK,
              headers := (hdrFold (HdrBlock.ofList baseHdrs)).denote,
              body := (rewriteBytesDense2 input).data.toList } : Reactor.Response) = _
      rw [hhdr, hbody]
    have hlist : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
            (rewriteBytesDense2 input)).data.toList
        = Reactor.serialize
            { status := 200, reason := Reactor.reasonOK,
              headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
              body := rewriteBytes input.data.toList } := by
      have h := serializeFlatB_refines 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
        (rewriteBytesDense2 input)
      rw [hkey] at h
      exact h
    have hdata : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
            (rewriteBytesDense2 input)).data
        = (Reactor.serialize
            { status := 200, reason := Reactor.reasonOK,
              headers := hdrFold (H := List (Bytes × Bytes)) baseHdrs,
              body := rewriteBytes input.data.toList }).toArray := by
      apply Array.toList_inj.mp
      rw [List.toList_toArray]; exact hlist
    show serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList baseHdrs))
          (rewriteBytesDense2 input)
        = ByteArray.mk _
    rw [← hdata]
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## Non-vacuity — a concrete request whose body is HTML, served through both -/

/-- A real request whose BODY is an HTML fragment the deployed html-rewrite rewrites. -/
def demoReq : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

#guard (serveDenseFull2 demoReq).size > 0
-- Fully-dense serve = the `List` twin (DRORB_SPAN=11), byte-identical.
#guard (serveDenseFull2 demoReq).data.toList == (serveDenseFullList demoReq).data.toList
-- Genuine dependence on the input.
#guard (serveDenseFull2 demoReq).data.toList
        != (serveDenseFull2 "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 8\r\n\r\n<i>other".toUTF8).data.toList

#print axioms serveDenseFull2_refines

end Datapath.ServeDenseFull2
