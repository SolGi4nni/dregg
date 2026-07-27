import Datapath.ByteSeqProto
import Datapath.IndexParse

/-!
# Datapath.ServeFlatBodyPoly — the response BODY carried DENSE (`ByteSeq T`) THROUGH
the serve fold: parse ⟶ a real body-touching stage (compress codec-tag prepend) ⟶
serialize, ALL polymorphic over `[ByteSeq T]`, so the body never materializes as a
runtime `List UInt8` on the fast path.

## Why this module exists (the deployed-body payoff test)

`Datapath.ServeFlat.serveFlatEcho` measured ~3.4× on an 8 KB body BECAUSE it carried
the body as a `ByteArray` and SKIPPED the pipeline. `Datapath.ServeFlatFull.serveFlatFull`
runs the REAL 14-stage pipeline but conses the body INSIDE the fold and flattens only
the egress, so it caps at ~1.07× on the body. The open question this module settles:
if the body flows DENSE through a *real body-touching stage* (not pure echo, not the
full List pipeline) — carried as `ByteSeq T`, the stage a genuine body transform — does
the 8 KB body recover the 3.4×-class win on the DEPLOYED path, or does a hidden `List`
materialization / a re-consing stage eat it?

## The serve, written ONCE over `[ByteSeq T]`

`serveBodyPolyG` reuses `Datapath.ByteSeqProto.servePoly` — the compressed-response
egress serializer, `foldCat frags ++ (singleton tag ++ body)` — as the polymorphic body
path: fold the head fragments, **prepend the compress codec tag to the body**
(`singleton tag ++ body`, exactly `Reactor.Stage.Compress.encode`'s container — the REAL
body-touching stage), append the body. The whole thing is polymorphic in `T`; the body
is `T`, never `List UInt8` on the runtime path.

* `serveBodyPolyArr : ByteArray → ByteArray` — instantiates at `ByteArray`: `append` is a
  `copySlice` bulk memcpy, `singleton tag` is a 1-byte `Array`, the 8 KB body is
  appended flat. NO body cons.
* `serveBodyPolyList : ByteArray → ByteArray` — the byte-identical `List` twin: the SAME
  serve computed with the body as `input.data.toList` (the 8 KB per-byte cons, K2) and the
  codec tag as a `List` cons; the deployed body way.
* `serveBodyPoly_refines` — **byte-identical** for every input. A DIRECT chain of
  `Datapath.ByteSeqProto.servePolyArray_refines` (the whole-stage refinement, itself a
  2-line `simp` over the op laws) with the fragment/`toArray` bridges — the load-bearing
  evidence that the dense body path serves the EXACT deployed bytes. So `DRORB_SPAN=5`
  (dense) and `DRORB_SPAN=6` (`List` twin) differ in NO served byte; the A/B measures ONLY
  the body representation.

## Honest scope

The **head fragments** are a fixed flat reconstruction (a valid HTTP/1.1 200 head with a
`Content-Length` derived `O(1)` from `input.size` and a `Content-Encoding: gzip` naming the
codec container) — the same "echo exemplar" head class as `serveFlatEcho`, NOT the deployed
14-stage route table. The body-touching stage is the REAL `Reactor.Stage.Compress.encode`
container (`codecTag .gzip :: body`), done dense (`singleton tag ++ body`). What this module
tests is precisely the BODY path: does carrying the 8 KB body dense THROUGH `servePoly`'s
fold + the codec-tag stage recover the body win. It is NOT a byte-match to the full
14-stage `Dataplane.drorbServe` (that is `ServeFlatFull`, egress-only, ~1.07×); it is
byte-identical to its OWN `List` twin, which is what the body A/B needs.
-/

namespace Datapath.ServeFlatBodyPoly

open Datapath.ByteSeq
open Datapath.ByteSeqProto (servePoly servePoly_refines servePolyArray_refines)
open Datapath.SpanBytes (parseIndexNative parseIndexNative_refines full full_wf)
open Reactor.Stage.Compress (Encoding codecTag)

/-! ## The fixed flat response head — `Content-Length` derived `O(1)` from the body size -/

/-- The HTTP/1.1 200 response head as flat bytes, with `Content-Length` = `bodyLen` (the
codec-encoded body length, `input.size + 1` for the one codec-tag byte) rendered by
`Reactor.natToDec` (`O(digits)`) and a `Content-Encoding: gzip` naming the codec container.
Computed from a `Nat` size — NEVER walks the body `List`. This is the echo-exemplar head
(a valid framed response), not the deployed 14-stage route head. -/
def headBytes (bodyLen : Nat) : List UInt8 :=
  "HTTP/1.1 200 OK\r\nContent-Encoding: gzip\r\nContent-Length: ".toUTF8.toList
    ++ Reactor.natToDec bodyLen
    ++ "\r\n\r\n".toUTF8.toList

/-! ## The DENSE body serve — body carried as `ByteArray` through `servePoly`'s fold -/

/-- **THE BODY-DENSE SERVE.** Parse the request off the borrowed window by INDEX
(`parseIndexNative`, no request cons); on a dispatchable request, run the polymorphic
`servePoly` at the `ByteArray` instance: the head is the single flat head fragment
(`Content-Length` from `input.size`, `O(1)`), the **body-touching stage** prepends the
gzip codec tag to the body (`singleton (codecTag .gzip) ++ body`, the real
`Reactor.Stage.Compress.encode` container), and the body is the request bytes carried as a
genuine `ByteArray` (`input`), bulk-appended (`ByteArray.append` = `copySlice`). The 8 KB
body NEVER materializes as a `List UInt8` — it flows dense through the fold + the stage. -/
@[export drorb_serve_bodypoly]
def serveBodyPolyArr (input : ByteArray) : ByteArray :=
  match parseIndexNative (full input) with
  | .request _ _ _ =>
      servePoly [(⟨(headBytes (input.size + 1)).toArray⟩ : ByteArray)] (codecTag Encoding.gzip) input
  | _ => ByteArray.empty

/-- **The `List` TWIN — the same serve, body computed the deployed cons-list way.** Parse
via the deployed `Reactor.Config.h1ParseFn (full input).read`; on a dispatchable request,
run `servePoly` at the `List UInt8` instance with the body as `input.data.toList` (the 8 KB
per-byte body cons, K2) and the codec tag as a `List` prepend (`tag :: body`), then
`ByteArray.mk … .toArray`. Byte-identical to `serveBodyPolyArr` (`serveBodyPoly_refines`);
the ONLY difference is the body `List` materialization. -/
@[export drorb_serve_bodypoly_list]
def serveBodyPolyList (input : ByteArray) : ByteArray :=
  match Reactor.Config.h1ParseFn (full input).read with
  | .request _ _ _ =>
      ByteArray.mk (servePoly (T := List UInt8) [headBytes (input.size + 1)]
        (codecTag Encoding.gzip) input.data.toList).toArray
  | _ => ByteArray.empty

/-! ## ★ THE LOAD-BEARING BYTE-IDENTITY — dense body = `List` body, for every input -/

/-- **THE BODY-DENSE BYTE-IDENTITY.** For EVERY input, the body-dense serve and its `List`
twin produce the IDENTICAL response bytes. The parse halves agree by
`parseIndexNative_refines` (the index-native parse computes the same `ParseOutcome` as the
deployed `List` parse); on a dispatchable request the egress halves agree by
`Datapath.ByteSeqProto.servePolyArray_refines` (the whole polymorphic stage's refinement,
itself discharged by `simp` over the op laws — the fold + the codec-tag stage + the append
all denote to the spec `List` computation), with the head fragment mapping through
`List.toList_toArray`. So swapping `DRORB_SPAN=5` (dense) for `DRORB_SPAN=6` (`List` twin)
changes no served byte — the A/B measures only the body-representation cost. Non-vacuous:
the served body is the echoed request bytes, so the conclusion genuinely depends on the
input. -/
theorem serveBodyPoly_refines (input : ByteArray) :
    serveBodyPolyArr input = serveBodyPolyList input := by
  unfold serveBodyPolyArr serveBodyPolyList
  rw [parseIndexNative_refines (full input) (full_wf input)]
  cases Reactor.Config.h1ParseFn (full input).read with
  | request c r k =>
    have hfrags : ([(⟨(headBytes (input.size + 1)).toArray⟩ : ByteArray)].map (·.data.toList))
        = [headBytes (input.size + 1)] := by
      simp [List.toList_toArray]
    have hr : (servePoly [(⟨(headBytes (input.size + 1)).toArray⟩ : ByteArray)]
          (codecTag Encoding.gzip) input).data.toList
        = servePoly (T := List UInt8) [headBytes (input.size + 1)]
            (codecTag Encoding.gzip) input.data.toList := by
      have h := servePolyArray_refines [(⟨(headBytes (input.size + 1)).toArray⟩ : ByteArray)]
        (codecTag Encoding.gzip) input
      rw [hfrags] at h; exact h
    have hdata : (servePoly [(⟨(headBytes (input.size + 1)).toArray⟩ : ByteArray)]
          (codecTag Encoding.gzip) input).data
        = (servePoly (T := List UInt8) [headBytes (input.size + 1)]
            (codecTag Encoding.gzip) input.data.toList).toArray := by
      apply Array.toList_inj.mp
      rw [List.toList_toArray]; exact hr
    show servePoly [(⟨(headBytes (input.size + 1)).toArray⟩ : ByteArray)] (codecTag Encoding.gzip) input
        = ByteArray.mk (servePoly (T := List UInt8) [headBytes (input.size + 1)]
            (codecTag Encoding.gzip) input.data.toList).toArray
    rw [← hdata]
  | reject c resp => rfl
  | incomplete => rfl
  | error => rfl

/-! ## Non-vacuity — a concrete request through BOTH serves, evaluated by the kernel -/

/-- A real request span; the body-dense serve echoes it into a 200 response. -/
def demoReq : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The body-dense serve produces a genuine non-empty framed response.
#guard (serveBodyPolyArr demoReq).size > 0
-- The body-dense serve and its List twin are byte-identical on the concrete request.
#guard (serveBodyPolyArr demoReq).data.toList == (serveBodyPolyList demoReq).data.toList
-- The body-touching stage genuinely fires: the byte after the head blank line is the gzip
-- codec tag (0x1F), i.e. the compress container was prepended to the body.
#guard (serveBodyPolyArr demoReq).data.toList.drop (headBytes (demoReq.size + 1)).length
        == ((0x1F : UInt8) :: demoReq.data.toList)
-- Genuine dependence on the input: a different request gives a different response.
#guard (serveBodyPolyArr demoReq).data.toList
        != (serveBodyPolyArr "GET /other HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8).data.toList

/-! ## Axiom audit -/

#print axioms serveBodyPoly_refines

end Datapath.ServeFlatBodyPoly
