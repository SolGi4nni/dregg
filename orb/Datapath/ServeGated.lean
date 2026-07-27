import Datapath.ServeDenseFull
import Datapath.BodyGate

/-!
# Datapath.ServeGated — the CONTENT-TYPE-GATED serve: the common case is a ZERO-COPY
body passthrough (the pipeline RE-SHAPED so a non-HTML body is never tokenized).

`Datapath.ServeDenseFull` (`DRORB_SPAN=10/11/12`) runs the deployed html-rewrite body
transform on EVERY response body — it tokenizes the whole body unconditionally, which
is the deployed pipeline's shape (`htmlrewriteStage.onResponse` has NO content-type
check) and its inherent body-path ceiling. That is ALSO a latent correctness bug: it
tag-strips JSON / binary / octet-stream bodies (a `<` in the payload is deleted).

This module RE-SHAPES the body path. `serveGated` reads the response's declared
`Content-Type` (mirrored from the request, an echo server) and:

* on `text/html` — runs the DENSE deployed body transform (`rewriteBytesDense`), the
  same bytes `DRORB_SPAN=10` computes (the gate FIRES, exactly like deployed on HTML);
* on ANYTHING ELSE (the COMMON case) — the body flows as the borrowed `ByteArray`
  (`input`) STRAIGHT to the flat egress `serializeFlatB`, **never tokenized, never
  consed**. A pure zero-copy passthrough.

So the common case (`application/json`, `application/octet-stream`, images) is a
zero-copy body echo: parse index-native ⟶ dense header fold ⟶ body-as-borrowed-
`ByteArray` ⟶ flat egress. The body never enters the tokenizer, so this path is NOT
capped by the ~2.35× tokenizer ceiling — it approaches the zero-copy body-echo speed.

## What is proven

* `serveGated_refines` — `serveGated` is byte-identical to its own `List` twin
  `serveGatedList` for EVERY input (the dense-vs-`List` A/B: `DRORB_SPAN=13` vs `=14`
  serve NO differing byte). The `List` appears only on the SPEC side of each
  refinement (`parseIndexNative_refines`, `hdrFold_refines`, `serializeFlatB_refines`,
  `rewriteBytesDense_refines`); the compute path is dense.
* `serveGated_body_is_gate` — the served body IS exactly
  `(Datapath.BodyGate.gatedHtmlrewrite (declaredResp …)).body`: the serve genuinely
  realises the proven content-type gate (not an ad-hoc `if`).

The CORRECTNESS improvement over the deployed serve — a non-HTML body's `<`/`>` are
PRESERVED where the deployed `serveDenseFullList` strips them — is a concrete
kernel-checked `#guard` at the bottom.

★ HONEST SCOPE: like `ServeDense`/`ServeDenseFull`, this is a THREE-header-stage echo
serve whose body transform is the real deployed `rewriteBytes` — now content-type-
GATED. On a non-HTML body it is DELIBERATELY NOT byte-identical to the deployed
unconditional serve: it does not corrupt the body. That is the point (ember: reshape
into a better shape). It IS byte-identical to the deployed body behaviour on HTML
bodies and on tagless bodies (where `rewriteBytes` is the identity, so gate-on = gate-
off = deployed).
-/

namespace Datapath.ServeGated

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Datapath.ServeDense (hdrFold hdrFold_refines)
open Datapath.HtmlRewriteDense (rewriteBytesDense rewriteBytesDense_refines)
open Datapath.ServeDenseFull (serveDenseFullList)
open Reactor.Stage.HtmlRewrite (rewriteBytes)
open Datapath.BodyGate (isHtmlCT ctName gatedHtmlrewrite gatedHtmlrewrite_correct)
open Proto.Http10 (headerValue)

/-! ## The response's declared content-type — mirrored from the request (echo) -/

/-- The response's declared `Content-Type`: mirror the request's `Content-Type`
header (case-insensitive lookup via the deployed `Proto.Http10.headerValue`), or
`application/octet-stream` when the request declares none. -/
def reqCT (req : Proto.Request) : Bytes :=
  (headerValue req ctName).getD "application/octet-stream".toUTF8.toList

/-- The response's base header block: a single `Content-Type` header echoing the
request's. The gate keys on this — the media type the handler declares. -/
def respHdrs (req : Proto.Request) : List (Bytes × Bytes) := [(ctName, reqCT req)]

/-- The gate decision for the serve: is the (mirrored) response `Content-Type` HTML. -/
def isHtmlReq (req : Proto.Request) : Bool := isHtmlCT (respHdrs req)

/-! ## Shared egress lemma — the flat serializer denotes to the deployed serialize -/

/-- The flat egress over the dense header block + any `ByteArray` body is byte-
identical to `Reactor.serialize` of the deployed response with the `List`-fold header
block and the body's byte list. The `List` appears only on the RHS. (The `ServeDense`
egress step, factored so both gate branches reuse it.) -/
private theorem egress_eq (H : List (Bytes × Bytes)) (fbody : ByteArray) (lbody : Bytes)
    (hbody : fbody.data.toList = lbody) :
    serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList H)) fbody
      = ByteArray.mk (Reactor.serialize
          { status := 200, reason := Reactor.reasonOK,
            headers := hdrFold (H := List (Bytes × Bytes)) H, body := lbody }).toArray := by
  have hhdr : (hdrFold (HdrBlock.ofList H)).denote
      = hdrFold (H := List (Bytes × Bytes)) H := by
    have h := hdrFold_refines (HdrBlock.ofList H)
    have e : HdrSeq.toHdrs (HdrBlock.ofList H) = H := HdrBlock.denote_ofList H
    rw [e] at h
    exact h
  have hkey : Datapath.FlatWire.respOf 200 Reactor.reasonOK
        (hdrFold (HdrBlock.ofList H)) fbody.data.toList
      = { status := 200, reason := Reactor.reasonOK,
          headers := hdrFold (H := List (Bytes × Bytes)) H, body := lbody } := by
    show ({ status := 200, reason := Reactor.reasonOK,
            headers := (hdrFold (HdrBlock.ofList H)).denote,
            body := fbody.data.toList } : Reactor.Response) = _
    rw [hhdr, hbody]
  have hlist : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList H)) fbody).data.toList
      = Reactor.serialize
          { status := 200, reason := Reactor.reasonOK,
            headers := hdrFold (H := List (Bytes × Bytes)) H, body := lbody } := by
    have h := serializeFlatB_refines 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList H)) fbody
    rw [hkey] at h
    exact h
  have hdata : (serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList H)) fbody).data
      = (Reactor.serialize
          { status := 200, reason := Reactor.reasonOK,
            headers := hdrFold (H := List (Bytes × Bytes)) H, body := lbody }).toArray := by
    apply Array.toList_inj.mp
    rw [List.toList_toArray]; exact hlist
  show serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList H)) fbody = ByteArray.mk _
  rw [← hdata]

/-! ## THE GATED SERVE — non-HTML body is a zero-copy passthrough -/

/-- **THE CONTENT-TYPE-GATED SERVE.** Parse the request off the borrowed window by
INDEX (`parseIndexNative`, no request cons), fold the three real header-transform
stages over the flat `HdrBlock`, then GATE the body on the response's declared
`Content-Type`:

* HTML — run the DENSE deployed body transform (`rewriteBytesDense input`), the same
  bytes the deployed `serveDenseFull` computes;
* NON-HTML (the COMMON case) — the body is the borrowed `ByteArray` `input` handed
  STRAIGHT to the flat egress (`serializeFlatB`, an `Array` append). It is NEVER
  tokenized and NEVER consed — a zero-copy passthrough.

NO `List` materialises on the compute path: grep the passthrough branch — the body
arg to `serializeFlatB` is `input` itself, no `.toList`, no `rewriteBytes`, no
`tokenize`. -/
@[export drorb_serve_gated]
def serveGated (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ req _ =>
      if isHtmlReq req
      then serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req)))
             (rewriteBytesDense input)
      else serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req)))
             input
  | _ => ByteArray.empty

/-- **The `List` TWIN — the same gated serve, header block + body computed the
deployed cons way.** Parse via the deployed `Reactor.Config.h1ParseFn`; on a
dispatchable request run the SAME three-stage `hdrFold` at the `List` instance and
GATE the body on the SAME `isHtmlReq` decision, but with the body as the deployed
`rewriteBytes input.data.toList` (HTML) or `input.data.toList` (passthrough), then
render with the deployed `Reactor.serialize`. Byte-identical to `serveGated`
(`serveGated_refines`); the ONLY difference is the `List` materialisation. -/
@[export drorb_serve_gated_list]
def serveGatedList (input : ByteArray) : ByteArray :=
  match Reactor.Config.h1ParseFn (full input).read with
  | .request _ req _ =>
      ByteArray.mk (Reactor.serialize
        { status := 200, reason := Reactor.reasonOK,
          headers := hdrFold (H := List (Bytes × Bytes)) (respHdrs req),
          body := if isHtmlReq req then rewriteBytes input.data.toList
                  else input.data.toList }).toArray
  | _ => ByteArray.empty

/-! ## ★ THE LOAD-BEARING BYTE-IDENTITY — gated dense = `List` twin, every input -/

/-- **THE GATED-SERVE BYTE-IDENTITY.** For EVERY input, the gated dense serve and its
`List` twin produce the IDENTICAL response bytes. The parse halves agree by
`parseIndexNative_refines`. On a dispatchable request the gate decision `isHtmlReq r`
is computed identically on both sides, and each branch's egress agrees by `egress_eq`
— the HTML branch linking the dense body transform to the deployed `rewriteBytes`
(`rewriteBytesDense_refines`), the passthrough branch carrying `input`'s own byte
list (`rfl`). So swapping `DRORB_SPAN=13` (gated) for `=14` (`List` twin) changes no
served byte. -/
theorem serveGated_refines (input : ByteArray) :
    serveGated input = serveGatedList input := by
  unfold serveGated serveGatedList
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    cases hh : isHtmlReq r with
    | true =>
      simp only [hh, if_true]
      exact egress_eq (respHdrs r) (rewriteBytesDense input) (rewriteBytes input.data.toList)
        (rewriteBytesDense_refines input)
    | false =>
      simp only [hh, Bool.false_eq_true, if_false]
      exact egress_eq (respHdrs r) input input.data.toList rfl
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## The serve genuinely realises the proven content-type gate -/

/-- The abstract "declared" response the handler produces before the header-transform
stages run: the echoed `Content-Type`, the body as the request bytes. -/
def declaredResp (req : Proto.Request) (input : ByteArray) : Reactor.Response :=
  { status := 200, reason := Reactor.reasonOK, headers := respHdrs req, body := input.data.toList }

/-- **The gated serve's body IS the content-type gate.** The `List` twin's body
branch is exactly `(Datapath.BodyGate.gatedHtmlrewrite (declaredResp req input)).body`
— the serve is a genuine instance of the proven gate (`gatedHtmlrewrite_correct`), not
an ad-hoc conditional. -/
theorem serveGated_body_is_gate (req : Proto.Request) (input : ByteArray) :
    (if isHtmlReq req then rewriteBytes input.data.toList else input.data.toList)
      = (gatedHtmlrewrite (declaredResp req input)).body := by
  rw [gatedHtmlrewrite_correct]
  rfl

/-! ## Non-vacuity + ★ the correctness improvement over the deployed serve -/

/-- A NON-HTML (`application/json`) request whose body is the tag `"<b>hi"`. -/
def jsonReqTag : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: application/json\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

/-- An HTML request with the SAME tag body. -/
def htmlReqTag : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: text/html\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

/-- A NON-HTML request with a TAGLESS body. -/
def jsonReqPlain : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: application/json\r\nContent-Length: 5\r\n\r\nhello".toUTF8

-- The gated serve produces a genuine non-empty framed response.
#guard (serveGated jsonReqTag).size > 0

-- ★ THE COMMON-CASE PASSTHROUGH IS CORRECT: on a JSON body the served response ENDS
-- with the verbatim `"<b>hi"` (bytes 60,98,62,104,105) — the `<` and `>` PRESERVED,
-- the body never tokenized.
#guard (serveGated jsonReqTag).data.toList.reverse.take 5 == [105, 104, 62, 98, 60]

-- ★ THE DEPLOYED UNCONDITIONAL SERVE CORRUPTS IT: `serveDenseFullList` (the deployed
-- tokenize-everything body path) STRIPS the `<b>` — its tail is just `"hi"` (104,105),
-- the `<`/`>` gone. The gated serve is CORRECT where the deployed one is wrong.
#guard (serveDenseFullList jsonReqTag).data.toList.reverse.take 2 == [105, 104]
#guard (serveDenseFullList jsonReqTag).data.toList.reverse.take 5 != [105, 104, 62, 98, 60]

-- On an HTML request the gate FIRES: the body is tag-stripped, tail is `"hi"` — the
-- same body behaviour as the deployed serve on HTML.
#guard (serveGated htmlReqTag).data.toList.reverse.take 2 == [105, 104]

-- The gated dense serve and its `List` twin are byte-identical on every case.
#guard (serveGated jsonReqTag).data.toList == (serveGatedList jsonReqTag).data.toList
#guard (serveGated htmlReqTag).data.toList == (serveGatedList htmlReqTag).data.toList
#guard (serveGated jsonReqPlain).data.toList == (serveGatedList jsonReqPlain).data.toList

-- Genuine dependence on the gate: the JSON (passthrough) and HTML (rewrite) serves of
-- the SAME `"<b>hi"` body differ — the content-type genuinely drives the transform.
#guard (serveGated jsonReqTag).data.toList != (serveGated htmlReqTag).data.toList

/-! ## Axiom audit -/

#print axioms serveGated_refines
#print axioms serveGated_body_is_gate

end Datapath.ServeGated
