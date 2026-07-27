import Reactor.Deploy
import Reactor.SerializeFast

/-!
# Reactor.ServeArr — the bridged flat `ByteArray → ByteArray` serve

The deployed serve (`Dataplane.drorbServe`, HTTP/1.1 branch) is the *List
sandwich*:

    ByteArray.mk (servePipelineFull2 input.toList).toArray

`input.toList` conses the request off the flat buffer, the pipeline runs over
`List UInt8`, `serialize` renders a `List UInt8`, and `.toArray` re-materializes
the whole response back into a flat buffer.

`serveArr` closes the OUTPUT seam of that sandwich without touching the pipeline
spec. The compiled `serialize` already flattens the response *head* into an
`Array UInt8` accumulator (`Reactor.serializeHeadAcc`, installed as the compiled
body of `serialize` by `Reactor.serialize_eq_fast`), but the deployed path then
walks it back to a `List` (`.toList`), re-appends the body cons-spine (`++
w.body`), and finally re-walks the whole `head ++ body` list into an `Array`
(`.toArray`). `serializeArr` skips those round-trips: it appends the body list
directly onto the flat head accumulator (`Array.appendList`, one push per byte)
and wraps the result as a `ByteArray` in place — the head is built once and never
re-walked, the body is copied exactly once (the same single body copy the
`.toArray` did), so no work is added and the head-proportional round-trips are
removed.

`serveArr_correct` proves it byte-identical to the deployed List serve via the
`serializeHeadAcc_toList` denotation bridge (the `parseHeadersAcc_toArray` pattern
scaled to the whole response render). The spec `servePipelineFull2` — and every
theorem/conformance obligation over it — is untouched: this file only *imports*
it.

## What this does and does NOT capture (the honest scope)

The `input.toList` at the INPUT seam is NOT removed. `servePipelineFull2 :
List UInt8 → List UInt8` consumes the request list in three places (the reactor
parse `deploySubs`, the correlation-id hash `corrVal`, and the response render),
so any function *provably equal to* `servePipelineFull2 input.toList` must feed it
that list. Removing that cons requires re-expressing the whole decision pipeline
over `ByteArray` (the rejected "catastrophic reprove") or emitting it flat from
the compiler (`flat-serveC`). So `serveArr` captures exactly the output-side head
round-trips — a head-proportional, hence marginal, saving, since the response
head is small and the deployed serve carries no large-body route. The measurement
(serve-bench / bench.sh / body-scaling.sh) is the deliverable; see the audit note.
-/

namespace Reactor
namespace ServeArr

open Proto (Bytes)

/-- **The response before serialization** — the built fold over `deployStagesFull2`,
the exact `Response` inside `servePipelineFull2` (which is `serialize` of this).
Naming it lets `serveArr` apply the flat serializer to the response the deployed
pipeline produced without duplicating the pipeline. -/
def respOf (input : Bytes) : Response :=
  (Reactor.Pipeline.runPipeline Reactor.Deploy.deployStagesFull2 Reactor.Deploy.appHandler
    (Reactor.Deploy.ctxOf input)).build

/-- `servePipelineFull2` IS `serialize (respOf …)` — definitional. -/
theorem respOf_serialize (input : Bytes) :
    Reactor.Deploy.servePipelineFull2 input = serialize (respOf input) := rfl

/-- **Serialize a response directly into a flat `ByteArray`.** The head is built
into the flat `Array UInt8` accumulator (`serializeHeadAcc`, the compiled body of
`serialize`'s head render) and the body list is appended onto it in place
(`Array.appendList` = one push per byte); the whole array is then wrapped as a
`ByteArray` with no further copy. Byte-identical to `ByteArray.mk (serialize
resp).toArray` (`serializeArr_eq`), but without the deployed path's
head→`List`→`Array` round-trips: the head is materialized once, the body copied
once. -/
def serializeArr (resp : Response) : ByteArray :=
  let w := build resp
  ⟨serializeHeadAcc w ++ w.body⟩

/-- **The flat serializer is byte-identical to the deployed one.** Reading the flat
buffer back as a list, `serializeArr resp` holds exactly the bytes of `serialize
resp`, so wrapping either as a `ByteArray` yields the same bytes. Proven through
the `serializeHeadAcc_toList` head-render bridge (the head accumulator reads back
`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF`) plus `Array.toList_appendList`
for the appended body — the whole-response analogue of `parseHeadersAcc_toArray`. -/
theorem serializeArr_eq (resp : Response) :
    serializeArr resp = ByteArray.mk (serialize resp).toArray := by
  unfold serializeArr serialize
  refine congrArg ByteArray.mk ?_
  apply Array.toList_inj.mp
  rw [Array.toList_appendList, serializeHeadAcc_toList, List.toList_toArray]
  unfold serializeWire
  simp only [List.append_assoc]

/-- **The bridged flat serve.** Parse-and-decide over the request (the deployed
`servePipelineFull2` fold, unchanged), then render the response straight into a
flat `ByteArray` with `serializeArr` — no output-side `List` round-trip. -/
def serveArr (input : ByteArray) : ByteArray :=
  serializeArr (respOf input.toList)

/-- **`serveArr` is byte-identical to the deployed List serve.** For every input,
`serveArr input` equals `ByteArray.mk (servePipelineFull2 input.toList).toArray` —
the exact bytes `Dataplane.drorbServe` emits on the HTTP/1.1 path. The pipeline
spec `servePipelineFull2` is untouched; only the OUTPUT materialization is
flat. -/
theorem serveArr_correct (input : ByteArray) :
    serveArr input
      = ByteArray.mk (Reactor.Deploy.servePipelineFull2 input.toList).toArray := by
  unfold serveArr
  rw [serializeArr_eq, ← respOf_serialize]

end ServeArr
end Reactor
