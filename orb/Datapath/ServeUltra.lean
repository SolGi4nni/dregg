import Datapath.ServeGated
import Datapath.HtmlRewriteDense2

/-!
# Datapath.ServeUltra — the COMBINED fast serve exemplar: ALL of tonight's wins in ONE
serve. Parse index-native (no request cons) ⟶ dense header fold (no header `List`) ⟶
the CONTENT-TYPE-GATED body (non-HTML = zero-copy passthrough, `text/html` = the
FULLY-DENSE tokenizer `rewriteBytesDense2`, no token `List`) ⟶ flat egress
(`serializeFlatB`, a `ByteArray` body, no `body.toList`).

`Datapath.ServeGated` (`DRORB_SPAN=13`) already assembled parse-index-native ⟶ dense
header fold ⟶ content-type gate ⟶ flat egress, but its HTML branch ran
`Datapath.HtmlRewriteDense.rewriteBytesDense` — DENSE at the input/output but running
the DEPLOYED `feedF` state machine, whose `FState` is still `List`-typed (`curRev :
List UInt8`, a per-byte `cons`; `toks : List Token`). So the tokenizer INTERMEDIATE
stayed a cons-list — the last `List` on the HTML body path.

`Datapath.HtmlRewriteDense2.rewriteBytesDense2` killed that last `List`: the tokenizer
state `FStateD` is fully dense (`cur : ByteArray`, `toks : Array DToken`), proven
byte-identical to the deployed `rewriteBytes` (`rewriteBytesDense2_refines`). This
module composes it into the gated serve — the SINGLE serve that carries NO `List` on
ANY branch of the compute path:

* parse: `parseIndexNative` — index reads, no request cons (`parseIndexNative_refines`);
* headers: `hdrFold` over a flat `HdrBlock` — `Array` ops, no header spine
  (`hdrFold_refines`);
* body/non-HTML (the COMMON case): the borrowed `ByteArray` `input` STRAIGHT to egress
  — never tokenized, never consed (a zero-copy passthrough);
* body/HTML: `rewriteBytesDense2 input` — the FULLY-DENSE tokenizer, no token `List`
  (`rewriteBytesDense2_refines`);
* egress: `serializeFlatB` — a `ByteArray` body append, no `body.toArray`
  (`serializeFlatB_refines`).

## What is proven

* `serveUltra_refines` — `serveUltra` is byte-identical to its own `List` twin
  `serveUltraList` for EVERY input. The parse halves agree by
  `parseIndexNative_refines`; on a dispatchable request the gate decision `isHtmlReq r`
  is computed identically on both sides; the HTML branch's egress agrees by linking the
  fully-dense tokenizer to the deployed `rewriteBytes` (`rewriteBytesDense2_refines`),
  the passthrough branch by carrying `input`'s own byte list (`rfl`). The `List`
  appears ONLY on the spec side of each refinement; the compute path is fully dense.
* `serveUltra_eq_serveGated` — the combined serve is byte-identical to the DEPLOYED
  content-type-gated serve (`Datapath.ServeGated.serveGated`, `DRORB_SPAN=13`): the
  fully-dense tokenizer and `HtmlRewriteDense.rewriteBytesDense` both compute the
  deployed `rewriteBytes` bytes, so the ULTRA serve and the deployed gated serve emit
  the IDENTICAL response bytes on every input. So `serveUltra` inherits ServeGated's
  byte-identity to the deployed gated body behaviour (HTML: tag-stripped; non-HTML:
  `<`/`>` preserved, the deployed unconditional serve's corruption fixed).

★ HONEST SCOPE: like `ServeGated`, this is a THREE-header-stage echo serve whose body
transform is the real deployed `rewriteBytes` (now fully-dense AND content-type gated).
It is NOT byte-identical to the full 14-stage `Dataplane.drorbServe` (different header
set). Its BODY compute is byte-identical to what `drorbServe`'s htmlrewrite stage does
to the body — with the deployed unconditional-tokenization bug fixed on non-HTML. The
`List` is only ever the SPEC on the RHS of a refinement; the exemplar's compute path is
`ByteArray`/`Array` end to end.
-/

namespace Datapath.ServeUltra

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Datapath.ServeDense (hdrFold hdrFold_refines)
open Datapath.HtmlRewriteDense2 (rewriteBytesDense2 rewriteBytesDense2_refines)
open Reactor.Stage.HtmlRewrite (rewriteBytes)
open Datapath.ServeGated (respHdrs isHtmlReq serveGated serveGated_refines)

/-! ## Shared egress lemma — the flat serializer denotes to the deployed serialize

The `ServeDense` egress step (factored so both gate branches reuse it), a copy of
`ServeGated.egress_eq` (which is `private`, so re-derived here from the SAME public
lemmas `hdrFold_refines` / `HdrBlock.denote_ofList` / `serializeFlatB_refines`). -/

/-- The flat egress over the dense header block + any `ByteArray` body is byte-identical
to `Reactor.serialize` of the deployed response with the `List`-fold header block and the
body's byte list. The `List` appears only on the RHS. -/
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

/-! ## THE COMBINED SERVE — index parse ⟶ dense header fold ⟶ GATED fully-dense body ⟶ flat egress -/

/-- **THE COMBINED FAST SERVE.** Parse the request off the borrowed window by INDEX
(`parseIndexNative`, no request cons), fold the three real header-transform stages over
the flat `HdrBlock` (`hdrFold`, `Array` ops), then GATE the body on the response's
declared `Content-Type`:

* HTML — run the FULLY-DENSE deployed body transform (`rewriteBytesDense2 input`, no
  token `List`, byte-identical to the deployed `rewriteBytes`);
* NON-HTML (the COMMON case) — the body is the borrowed `ByteArray` `input` handed
  STRAIGHT to the flat egress (`serializeFlatB`, an `Array` append). NEVER tokenized,
  NEVER consed — a zero-copy passthrough.

NO `List` materialises on ANY branch of the compute path. -/
@[export drorb_serve_ultra]
def serveUltra (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ req _ =>
      if isHtmlReq req
      then serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req)))
             (rewriteBytesDense2 input)
      else serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req)))
             input
  | _ => ByteArray.empty

/-- **The `List` TWIN — the same gated serve, header block + body computed the deployed
cons way.** Parse via the deployed `Reactor.Config.h1ParseFn`; on a dispatchable request
run the SAME three-stage `hdrFold` at the `List` instance and GATE the body on the SAME
`isHtmlReq` decision, but with the body as the deployed `rewriteBytes input.data.toList`
(HTML) or `input.data.toList` (passthrough), then render with the deployed
`Reactor.serialize`. Byte-identical to `serveUltra` (`serveUltra_refines`); the ONLY
difference is the `List` materialisation. (Structurally identical to
`ServeGated.serveGatedList` — the fully-dense tokenizer and `rewriteBytesDense` share the
one deployed `rewriteBytes` spec.) -/
@[export drorb_serve_ultra_list]
def serveUltraList (input : ByteArray) : ByteArray :=
  match Reactor.Config.h1ParseFn (full input).read with
  | .request _ req _ =>
      ByteArray.mk (Reactor.serialize
        { status := 200, reason := Reactor.reasonOK,
          headers := hdrFold (H := List (Bytes × Bytes)) (respHdrs req),
          body := if isHtmlReq req then rewriteBytes input.data.toList
                  else input.data.toList }).toArray
  | _ => ByteArray.empty

/-! ## ★ THE LOAD-BEARING BYTE-IDENTITY — combined dense serve = `List` twin, every input -/

/-- **THE COMBINED-SERVE BYTE-IDENTITY.** For EVERY input, the combined fully-dense serve
and its `List` twin produce the IDENTICAL response bytes. The parse halves agree by
`parseIndexNative_refines`. On a dispatchable request the gate decision `isHtmlReq r` is
computed identically on both sides, and each branch's egress agrees by `egress_eq` — the
HTML branch linking the FULLY-DENSE tokenizer to the deployed `rewriteBytes`
(`rewriteBytesDense2_refines`), the passthrough branch carrying `input`'s own byte list
(`rfl`). So swapping `DRORB_SPAN=16` (combined) for its `List` twin changes no served
byte. -/
theorem serveUltra_refines (input : ByteArray) :
    serveUltra input = serveUltraList input := by
  unfold serveUltra serveUltraList
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    cases hh : isHtmlReq r with
    | true =>
      simp only [hh, if_true]
      exact egress_eq (respHdrs r) (rewriteBytesDense2 input) (rewriteBytes input.data.toList)
        (rewriteBytesDense2_refines input)
    | false =>
      simp only [hh, Bool.false_eq_true, if_false]
      exact egress_eq (respHdrs r) input input.data.toList rfl
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## ★ Byte-identity to the DEPLOYED content-type-gated serve (`DRORB_SPAN=13`) -/

/-- **The combined serve is byte-identical to the DEPLOYED gated serve.** `serveUltra`
(fully-dense tokenizer on HTML) and `Datapath.ServeGated.serveGated`
(`HtmlRewriteDense.rewriteBytesDense` on HTML) emit the IDENTICAL response bytes on every
input: both `List` twins are the SAME expression (both bodies are the deployed
`rewriteBytes input.data.toList` on HTML / `input.data.toList` on passthrough), so
`serveUltra = serveUltraList = serveGatedList = serveGated`. The combined serve therefore
inherits ServeGated's byte-identity to the deployed gated body behaviour. -/
theorem serveUltra_eq_serveGated (input : ByteArray) :
    serveUltra input = serveGated input := by
  rw [serveUltra_refines, serveGated_refines]
  rfl

/-! ## Non-vacuity — concrete requests, combined-served through both, and the correctness fix -/

/-- A NON-HTML (`application/json`) request whose body is the tag `"<b>hi"`. -/
def jsonReqTag : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: application/json\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

/-- An HTML request with the SAME tag body. -/
def htmlReqTag : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: text/html\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

/-- A NON-HTML request with a TAGLESS body. -/
def jsonReqPlain : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: application/json\r\nContent-Length: 5\r\n\r\nhello".toUTF8

-- The combined serve produces a genuine non-empty framed response.
#guard (serveUltra jsonReqTag).size > 0

-- ★ THE COMMON-CASE PASSTHROUGH IS CORRECT: on a JSON body the served response ENDS with
-- the verbatim `"<b>hi"` (bytes 60,98,62,104,105) — the `<` and `>` PRESERVED, the body
-- never tokenized.
#guard (serveUltra jsonReqTag).data.toList.reverse.take 5 == [105, 104, 62, 98, 60]

-- On an HTML request the FULLY-DENSE tokenizer FIRES: the body is tag-stripped, tail is
-- `"hi"` (104,105) — byte-identical to the deployed rewrite on HTML.
#guard (serveUltra htmlReqTag).data.toList.reverse.take 2 == [105, 104]

-- The combined dense serve and its `List` twin are byte-identical on every case.
#guard (serveUltra jsonReqTag).data.toList == (serveUltraList jsonReqTag).data.toList
#guard (serveUltra htmlReqTag).data.toList == (serveUltraList htmlReqTag).data.toList
#guard (serveUltra jsonReqPlain).data.toList == (serveUltraList jsonReqPlain).data.toList

-- The combined serve is byte-identical to the DEPLOYED gated serve (=13) on every case.
#guard (serveUltra jsonReqTag).data.toList == (serveGated jsonReqTag).data.toList
#guard (serveUltra htmlReqTag).data.toList == (serveGated htmlReqTag).data.toList
#guard (serveUltra jsonReqPlain).data.toList == (serveGated jsonReqPlain).data.toList

-- Genuine dependence on the gate: the JSON (passthrough) and HTML (dense-tokenize) serves
-- of the SAME `"<b>hi"` body differ — the content-type genuinely drives the transform.
#guard (serveUltra jsonReqTag).data.toList != (serveUltra htmlReqTag).data.toList

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms serveUltra_refines
#print axioms serveUltra_eq_serveGated

end Datapath.ServeUltra
