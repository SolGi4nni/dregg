import Datapath.ServeConformantDense

/-!
# Datapath.ServeConformantFast — the conformant-dense serve with ONE body attach

`serveConformantDenseIdx` (`DRORB_SPAN=20`) fixed the INNER body-cliff, but the
conformance WRAPPER still re-copies the full response twice per `/bulk` hit:
`injectDateBA` (native head extract ++ … ++ native TAIL extract/append — the 1 MiB
body rides one extract + one append) and then `scrubCorrBA` on the dated bytes
(head extract/scrub ++ another 1 MiB tail extract/append). Measured: the
conformant-dense serve trails the bare dense serve (`DRORB_SPAN=18`) by ~47% on
`GET /bulk`, and the wrapper's ~4 whole-body `memcpy`s are the gap.

This module fuses the two post-processors: the `Date` splice and the `x-corr`
scrub BOTH rewrite only the HEAD (everything up to and including the first blank
line — a few hundred bytes), and the body bytes never change. `scrubDateBA`
extracts the head ONCE, applies the SAME list-spec transforms in the SAME order
(`scrubLines ∘ injectDate`) to the head alone, and attaches the unchanged body
with ONE native `ByteArray.copySlice` — a single body `memcpy` per request
instead of ~4.

## Honest scope

* `serveConformantFastIdx` (`@[export drorb_serve_conformant_fast]`,
  `DRORB_SPAN=22`) mirrors `conformantServe`'s control flow EXACTLY (same Z1
  431-gate, same validation/framing gates, same conditional-request branch, same
  `HEAD`-strip); only the accepted non-conditional post-processing is fused.
* The fused/unfused byte-identity `scrubDateBA bs = scrubCorrBA (injectDateBA bs)`
  is NOT yet a theorem — it is pinned by the `#guard` battery below (evaluator-
  checked on the REAL 1 MiB dense `/bulk` response and on adversarial head shapes
  incl. blank-after-status, no-CRLF, empty, head-only, `x-corr`-first/duplicate).
  The general proof needs the blank-scan shift lemma
  (`blankLen (injectDate L) = blankLen L + dateHdr.length + 2` when a CRLF exists)
  — the named next rung. Until it lands, `DRORB_SPAN=20` remains the proven
  conformant-dense serve and `=22` is the measured fused probe.
* Guarded fusion: the fused path fires only when the response head contains a
  CRLF within the blank-scan (`crIdxFrom + 2 ≤ blankTakeFrom` — every serialized
  response does); degenerate inputs take the UNFUSED composition verbatim.
-/

namespace Datapath.ServeConformantFast

open Reactor.ServeConformant
open Proto (Bytes Request)
open Reactor (Response serialize crlf)
open Reactor.Stage.RequestValidation (validationStage badRequestResp)
open Reactor.Stage.FramingValidation (framingValidationStage)
open Reactor.Stage.RequestHeadLimit (headGate)

/-! ## The tail-attaching `copySlice` — its list reading -/

/-- Attaching `src`'s tail (from `srcOff`) after `dest` via ONE native
`ByteArray.copySlice` reads back as `dest.toList ++ src.toList.drop srcOff` —
the single-`memcpy` body attach. -/
theorem copySlice_tail_toList (src dest : ByteArray) (srcOff : Nat) :
    (src.copySlice srcOff dest dest.size (src.size - srcOff) false).toList
      = dest.toList ++ src.toList.drop srcOff := by
  rw [ba_toList_eq (src.copySlice srcOff dest dest.size (src.size - srcOff) false),
      ba_toList_eq dest, ba_toList_eq src]
  show (dest.data.extract 0 dest.size
        ++ src.data.extract srcOff (srcOff + (src.size - srcOff))
        ++ dest.data.extract (dest.size + min (src.size - srcOff) (src.data.size - srcOff))
             dest.data.size).toList
      = dest.data.toList ++ src.data.toList.drop srcOff
  have h3 : dest.data.size
      - (dest.size + min (src.size - srcOff) (src.data.size - srcOff)) = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_add_right _ _)
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_drop_take,
    Nat.sub_zero, List.drop_zero, h3, List.take_zero, List.append_nil,
    Nat.add_sub_cancel_left]
  rw [show dest.size = dest.data.toList.length by
        rw [Array.length_toList, ba_data_size],
      List.take_length]
  congr 1
  have hlen : src.size - srcOff = (src.data.toList.drop srcOff).length := by
    rw [List.length_drop, Array.length_toList, ba_data_size]
  rw [hlen, List.take_length]

/-! ## The fused post-processor -/

/-- **The fused `Date`-splice + `x-corr`-scrub.** Both transforms only rewrite the
response HEAD; the body bytes are unchanged. Extract the head once, run the SAME
list-spec composition `scrubLines ∘ injectDate` on it (a few hundred bytes), and
attach the body with ONE native `copySlice` — a single whole-body `memcpy`,
replacing `scrubCorrBA (injectDateBA bs)`'s ~4. Inputs whose head carries no CRLF
inside the blank scan (no serialized response looks like that) take the unfused
composition verbatim. -/
def scrubDateBA (bs : ByteArray) : ByteArray :=
  let blank := blankTakeFrom bs 0
  if crIdxFrom bs 0 + 2 ≤ blank then
    let head := ByteArray.mk (scrubLines (injectDate (bs.extract 0 blank).toList)).toArray
    bs.copySlice blank head head.size (bs.size - blank) false
  else
    scrubCorrBA (injectDateBA bs)

/-- The accepted-path bytes with the FUSED post-processor: the (rare, gated)
conditional branch is the unfused record round-trip + scrub exactly as
`acceptedRawBA`; the common branch is the fused splice+scrub. -/
def acceptedFastBA (inner : ByteArray → ByteArray) (req : Request)
    (innerInput : ByteArray) : ByteArray :=
  if hasConditional req then
    scrubCorrBA (ByteArray.mk (condRewriteBytes req (inner (condInnerInput req)).toList).toArray)
  else scrubDateBA (inner innerInput)

/-- **The conformant serve with the fused post-processor.** Identical control flow
to `conformantServe` (Z1 head gate, `414`/`431` → validation gate → framing gate →
inner → post-process → `HEAD`-strip); the `x-corr` scrub is distributed into each
branch (reject branches scrub the tiny serialized reject; the accepted
non-conditional branch takes the fused single-`memcpy` path). -/
def conformantServeFast (inner : ByteArray → ByteArray) (input : ByteArray) : ByteArray :=
  match headGate input with
  | some r => ByteArray.mk (serialize (addDate r)).toArray
  | none =>
    let raw :=
      match Proto.RequestSerialize.parse (reqBytes input) with
      | none => scrubCorrBA (ByteArray.mk (serialize (addDate badRequestResp)).toArray)
      | some req =>
        match validationStage.onRequest (mkCtx input req) with
        | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
        | .continue c' =>
          match framingValidationStage.onRequest c' with
          | .respond r => scrubCorrBA (ByteArray.mk (serialize (addDate r)).toArray)
          | .continue c'' =>
            let innerInput :=
              if c''.req.target == req.target then input
              else ByteArray.mk (Proto.RequestSerialize.serialize c''.req).toArray
            acceptedFastBA inner req innerInput
    if isHeadReq input then stripBodyBA raw else raw

/-- **The exported fast conformant-dense serve** (`DRORB_SPAN=22`): the fused
wrapper around the index-decided dense inner — same inner as
`drorb_serve_conformant_dense` (`=20`), post-processing fused to one body attach. -/
@[export drorb_serve_conformant_fast]
def serveConformantFastIdx (input : ByteArray) : ByteArray :=
  conformantServeFast Datapath.ServeDenseIdx.serveDenseIdx input

/-! ## Byte-identity guards — fused = unfused, evaluator-checked

The fusion claim `scrubDateBA bs = scrubCorrBA (injectDateBA bs)` on adversarial
head shapes: blank-right-after-status (the boundary-spanning blank), `x-corr`
first/duplicated/absent, `x-corr`-lookalike in the BODY (must survive), no blank
line, no CRLF at all (fallback branch), empty, bare CRLFs, trailing CR. -/

private def fuseCases : List ByteArray :=
  [ "HTTP/1.1 200 OK\r\nx-corr: 1.2.3\r\ncontent-length: 4\r\n\r\nbody".toUTF8
  , "HTTP/1.1 200 OK\r\ncontent-length: 4\r\n\r\nbody".toUTF8
  , "HTTP/1.1 200 OK\r\nx-corr: a\r\nx-corr: b\r\n\r\nx-corr: body\r\n\r\ntail".toUTF8
  , "HTTP/1.1 200 OK\r\n\r\nbody".toUTF8
  , "HTTP/1.1 200 OK\r\n\r\n".toUTF8
  , "HTTP/1.1 200\r\nh: v\r\n\r\n\r\nbody".toUTF8
  , "\r\n".toUTF8
  , "\r\n\r\n".toUTF8
  , "\r\nx-corr: 999\r\n\r\ntail".toUTF8
  , "abc\r\n".toUTF8
  , "a\r\nb".toUTF8
  , "abc\r".toUTF8
  , "no crlf here".toUTF8
  , "".toUTF8
  ]

#guard fuseCases.all fun bs =>
  (scrubDateBA bs).data.toList == (scrubCorrBA (injectDateBA bs)).data.toList

open Datapath.ServeDenseReal (bulkDemoReqAnyHost)
open Datapath.ServeDenseIdx (healthReq)

-- The fusion on the REAL 1 MiB dense `/bulk` response bytes.
#guard (scrubDateBA (Datapath.ServeDenseIdx.serveDenseIdx bulkDemoReqAnyHost)).data.toList
        == (scrubCorrBA (injectDateBA
              (Datapath.ServeDenseIdx.serveDenseIdx bulkDemoReqAnyHost))).data.toList

/-! ## End-to-end guards — fast serve = the proven conformant-dense serve -/

private def headBulkReq : ByteArray := "HEAD /bulk HTTP/1.1\r\nHost: example.net\r\n\r\n".toUTF8
private def noHostReq : ByteArray := "GET /bulk HTTP/1.1\r\n\r\n".toUTF8
private def condReq : ByteArray :=
  "GET /bulk HTTP/1.1\r\nHost: example.net\r\nIf-None-Match: \"abc\"\r\n\r\n".toUTF8
private def garbageReq : ByteArray := "garbage".toUTF8

open Datapath.ServeConformantDense (serveConformantDenseIdx)

-- The accepted dense `/bulk` arm: byte-identical, and still > 1 MiB.
#guard (serveConformantFastIdx bulkDemoReqAnyHost).data.toList
        == (serveConformantDenseIdx bulkDemoReqAnyHost).data.toList
#guard (serveConformantFastIdx bulkDemoReqAnyHost).size > 1048576
-- Off-arm, HEAD-strip, reject (missing Host), conditional, unparsable.
#guard (serveConformantFastIdx healthReq).data.toList
        == (serveConformantDenseIdx healthReq).data.toList
#guard (serveConformantFastIdx headBulkReq).data.toList
        == (serveConformantDenseIdx headBulkReq).data.toList
#guard (serveConformantFastIdx noHostReq).data.toList
        == (serveConformantDenseIdx noHostReq).data.toList
#guard (serveConformantFastIdx condReq).data.toList
        == (serveConformantDenseIdx condReq).data.toList
#guard (serveConformantFastIdx garbageReq).data.toList
        == (serveConformantDenseIdx garbageReq).data.toList
-- The scrub still bites through the fused path (N2 — no x-corr line served).
#guard !(Datapath.ServeConformantDense.hasCorrLine (serveConformantFastIdx bulkDemoReqAnyHost))

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms copySlice_tail_toList

end Datapath.ServeConformantFast
