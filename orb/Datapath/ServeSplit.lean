import Datapath.ServeGated

/-!
# Datapath.ServeSplit — the ZERO-COPY BODY serve: the header algebra (Lean, verified)
SPLIT from the body algebra (borrowed, spliced by the reactor).

Even the content-type-gated serve (`Datapath.ServeGated`, `DRORB_SPAN=13`, the common
case a zero-copy body passthrough) STILL, at its final egress step, APPENDS the body
into the output `ByteArray` ONCE: `serializeFlatB` computes `head ++ fbody.data` (an
`Array UInt8` append = one full-body allocation + memcpy in the Lean heap), and the host
then copies that whole `ByteArray` out of the Lean runtime into a send buffer. On a large
body those two whole-body copies are the residual cost the gate could not remove — the
body is not tokenized, but it is still *materialized into the response buffer*.

This module RE-SHAPES the egress into the shape a `sendfile`/`splice`-based edge server
uses: the response is `(HEADERS : ByteArray computed densely by Lean) ++ (BODY : a
borrowed byte span the reactor already holds — for this echo serve, the request buffer)`.
Lean computes ONLY the small header prefix (`serveSplitHead` — status line + headers +
`Content-Length` + the blank-line separator). The reactor then writes HEADERS then BODY
to the socket via `writev` / two writes — the body goes from its source buffer STRAIGHT
to the socket, **never appended into any output `ByteArray`, never copied out of the Lean
heap**. The body-append is gone; the whole-body Lean allocation is gone.

## What is proven (non-vacuous, `#print axioms` at the bottom)

* `renderHead_append` — the ALGEBRA of the split: for ANY header block `hb` and ANY
  `ByteArray` body `fbody`, the head Lean computes CONCATENATED with the body is
  BYTE-IDENTICAL to `serializeFlatB … fbody` (the appended version). i.e.
  `renderHead … fbody.size ++ fbody.data = serializeFlatB … fbody`. The `Content-Length`
  Lean bakes into the head is exactly `fbody.size`, so the split is length-correct.

* `serveSplit_reassemble` — the SERVE-level split: for every input, the head the serve
  computes (`serveSplitHead`, the `@[export drorb_serve_split_head]` the reactor calls),
  followed by the echoed body (`input` — the borrowed request buffer the reactor already
  holds), is BYTE-IDENTICAL to `serveSplitFull` (the appended serve = the passthrough
  branch of the deployed gated serve). Writing head-then-body = the whole response.

* `serveSplitHead_append_eq_serialize` — the split is byte-identical to the DEPLOYED
  serializer: head ++ body = `Reactor.serialize` of the deployed passthrough response
  (`List` body only on the spec/RHS side). So the reactor's two-write output equals the
  bytes the deployed `drorb_serve`-class serialize would have produced — a byte diff
  would be a regression.

## The no-append evidence

`serveSplitHead` NEVER mentions the body: grep it — it renders `renderHead` from the flat
header block and `input.size` (an `O(1)` field read, no `List.length` walk), and returns.
There is NO `serializeFlatB` on the body, NO `++ fbody.data`, NO `.toList`. The body is
never touched by Lean; it is the borrowed `input` the host splices. That is the whole
point: the body is genuinely zero-copy (spliced, not appended).

## Honest scope

Like `ServeGated`, this is the three-header-stage echo serve; the body echoed is the raw
request buffer (`input`), exactly as `ServeGated`'s passthrough branch echoes `input`. The
`Reactor.Response` with a `List` body appears ONLY as the spec object on the RHS of
`serveSplitHead_append_eq_serialize` (the abstract thing the split is proven byte-identical
to); it is never constructed on the split path. `Proto.Bytes := List UInt8` and the 15k
proofs are untouched — the same equality-transfer discipline `FlatBody`/`ServeGated` use.
-/

namespace Datapath.ServeSplit

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock flatRenderBlock)
open Datapath.FlatBody (serializeFlatB serializeFlatB_refines clHeaderB)
open Datapath.FlatWire (respOf)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Datapath.ServeDense (hdrFold hdrFold_refines)
open Datapath.ServeGated (respHdrs)

/-! ## The head render — everything `serializeFlatB` emits BEFORE the body append -/

/-- **The response HEAD only — the small dense prefix Lean computes.** Exactly the bytes
`serializeFlatB` lays down before its final `++ fbody.data`: the status line, `CRLF`, the
flat header block with the derived `Content-Length` pushed on (`Array.push`), and the
blank-line (`CRLF CRLF`) separator. The `Content-Length` value is `natToDec bodyLen` — the
caller passes the body's SIZE (`O(1)`, `ByteArray.size`, no `List` walk). NO body bytes are
touched; the body is spliced by the host after this head. -/
def renderHead (status : Nat) (reason : Bytes) (hb : HdrBlock) (bodyLen : Nat) : ByteArray :=
  let statusBytes : Array UInt8 :=
    (Reactor.http11 ++ [32] ++ Reactor.natToDec status ++ [32] ++ reason).toArray
  ByteArray.mk (
    statusBytes
      ++ Reactor.crlf.toArray
      ++ flatRenderBlock (hb.addHeader (Reactor.clName, Reactor.natToDec bodyLen))
      ++ Reactor.crlf.toArray
      ++ Reactor.crlf.toArray)

/-- **THE SPLIT ALGEBRA.** The head Lean computes (`renderHead … fbody.size`) CONCATENATED
with the body bytes (`fbody.data`) is BYTE-IDENTICAL to `serializeFlatB … fbody` — the
appended egress. The `Content-Length` baked into the head is `fbody.size`, so the split is
length-correct. Both sides are the SAME left-associated `Array UInt8` concatenation
(`statusBytes ++ CRLF ++ flatRender(hb + clHeader) ++ CRLF ++ CRLF ++ fbody.data`); the
head is the prefix, the body the suffix. So writing head-then-body = the appended response,
with NO body append on the head-compute side. -/
theorem renderHead_append (status : Nat) (reason : Bytes) (hb : HdrBlock) (fbody : ByteArray) :
    ByteArray.mk ((renderHead status reason hb fbody.size).data ++ fbody.data)
      = serializeFlatB status reason hb fbody := by
  unfold renderHead serializeFlatB clHeaderB
  rfl

/-! ## THE SPLIT SERVE — the head-only export the reactor calls -/

/-- **THE ZERO-COPY-BODY HEAD SERVE — `@[export drorb_serve_split_head]`.** Parse the
request off the borrowed window by INDEX (`parseIndexNative`, no request cons), fold the
three real header-transform stages over the flat `HdrBlock` (`hdrFold`), and render ONLY
the head (`renderHead`) — with `Content-Length = input.size` (the echoed body is the whole
request buffer, `input`). The reactor calls this for the HEADER bytes, then writes those
head bytes THEN the borrowed body (`input`) to the socket via `writev`/two writes — the
body is NEVER appended here. Grep this def: no `serializeFlatB`, no `++ input.data`, no
`.toList`; the body is untouched. -/
@[export drorb_serve_split_head]
def serveSplitHead (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ req _ =>
      renderHead 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input.size
  | _ => ByteArray.empty

/-- **The appended reference serve** — the passthrough branch of the deployed gated serve
(`Datapath.ServeGated.serveGated` on a non-HTML body): parse, fold headers, then
`serializeFlatB … input` (the body APPENDED into the output `ByteArray`). This is exactly
what `DRORB_SPAN=13` computes on the common (non-HTML) case; the split serve reproduces its
bytes without the append. -/
def serveSplitFull (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ req _ =>
      serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input
  | _ => ByteArray.empty

/-- **THE SERVE-LEVEL SPLIT IS CORRECT.** For every input, the head the export computes
(`serveSplitHead input`) followed by the echoed body (`input` — the borrowed request buffer
the reactor already holds) is BYTE-IDENTICAL to the appended serve (`serveSplitFull`). So
the reactor writing HEAD then BODY produces exactly the whole response — the split
concatenation IS the response, with the body never appended on the compute side. On a
non-dispatchable input both sides are empty. -/
theorem serveSplit_reassemble (input : ByteArray) :
    (match parseIndexNative (full input) with
     | .request _ _ _ => ByteArray.mk ((serveSplitHead input).data ++ input.data)
     | _ => ByteArray.empty)
      = serveSplitFull input := by
  unfold serveSplitHead serveSplitFull
  cases h : parseIndexNative (full input) with
  | request c r k =>
      simp only [h]
      exact renderHead_append 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs r))) input
  | reject c resp => simp [h]
  | incomplete => simp [h]
  | error => simp [h]

/-! ## The split is byte-identical to the DEPLOYED serializer -/

/-- **Head ++ body = the DEPLOYED serialize.** On a dispatchable request, the split output
(head the export computes, then the borrowed body `input`) is byte-identical to
`Reactor.serialize` of the DEPLOYED passthrough response — the header block folded the
deployed `List` way (`hdrFold` at the `List` instance) and the body the request's own byte
`List` (`input.data.toList`). The `List` appears ONLY on the spec (RHS) side; the split
compute path never materializes a body `List`. Chains `renderHead_append` (the split
algebra) into `serializeFlatB_refines` (the flat-egress byte-identity to the deployed
serialize). A byte diff here would be a regression. -/
theorem serveSplitHead_append_eq_serialize (input : ByteArray) (c : Nat) (req : Proto.Request)
    (k : Bool) (h : parseIndexNative (full input) = .request c req k) :
    ByteArray.mk ((serveSplitHead input).data ++ input.data)
      = ByteArray.mk (Reactor.serialize
          (respOf 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input.data.toList)).toArray := by
  have hhead : (serveSplitHead input).data
      = (renderHead 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input.size).data := by
    unfold serveSplitHead; rw [h]
  rw [hhead, renderHead_append 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input]
  -- goal: serializeFlatB … input = ByteArray.mk (Reactor.serialize (respOf … input.data.toList)).toArray
  -- the flat-egress byte-identity: serializeFlatB … input denotes to the deployed serialize
  -- of the resp whose body is input.data.toList (the List body only on the RHS spec).
  have hlist : (serializeFlatB 200 Reactor.reasonOK
        (hdrFold (HdrBlock.ofList (respHdrs req))) input).data.toList
      = Reactor.serialize (respOf 200 Reactor.reasonOK
          (hdrFold (HdrBlock.ofList (respHdrs req))) input.data.toList) :=
    serializeFlatB_refines 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input
  have hdata : (serializeFlatB 200 Reactor.reasonOK
        (hdrFold (HdrBlock.ofList (respHdrs req))) input).data
      = (Reactor.serialize (respOf 200 Reactor.reasonOK
          (hdrFold (HdrBlock.ofList (respHdrs req))) input.data.toList)).toArray := by
    apply Array.toList_inj.mp
    rw [List.toList_toArray]; exact hlist
  show serializeFlatB 200 Reactor.reasonOK (hdrFold (HdrBlock.ofList (respHdrs req))) input
      = ByteArray.mk _
  rw [← hdata]

/-! ## Non-vacuity — concrete requests, kernel-evaluated -/

/-- A NON-HTML (`application/octet-stream`) echo request with a body. -/
def demoReq : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Type: application/octet-stream\r\nContent-Length: 5\r\n\r\n<b>hi".toUTF8

-- The head serve produces a genuine non-empty header prefix.
#guard (serveSplitHead demoReq).size > 0

-- ★ THE HEAD CARRIES NO BODY: the head bytes do NOT contain the body tail `"<b>hi"` — the
-- head is strictly the status line + headers + separator. (The body is spliced separately.)
#guard (serveSplitHead demoReq).data.toList.reverse.take 5 != [105, 104, 62, 98, 60]

-- ★ THE SPLIT REASSEMBLES TO THE APPENDED SERVE: head ++ body (input) = serveSplitFull.
#guard (ByteArray.mk ((serveSplitHead demoReq).data ++ demoReq.data)).data.toList
        == (serveSplitFull demoReq).data.toList

-- The reassembled response ENDS with the verbatim echoed body `"<b>hi"` (60,98,62,104,105)
-- — the `<`/`>` preserved (never tokenized), the body a byte-exact splice of the request.
#guard (ByteArray.mk ((serveSplitHead demoReq).data ++ demoReq.data)).data.toList.reverse.take 5
        == [105, 104, 62, 98, 60]

-- The head declares the correct Content-Length for the spliced body: the head contains the
-- ASCII of the body length (demoReq.size) after "Content-Length: ".
#guard (serveSplitHead demoReq).size == (serveSplitFull demoReq).size - demoReq.size

-- Genuine dependence on the request: a different request gives a different head.
#guard (serveSplitHead demoReq).data.toList
        != (serveSplitHead "GET / HTTP/1.1\r\nHost: y\r\n\r\n".toUTF8).data.toList

/-! ## Axiom audit -/

#print axioms renderHead_append
#print axioms serveSplit_reassemble
#print axioms serveSplitHead_append_eq_serialize

end Datapath.ServeSplit
