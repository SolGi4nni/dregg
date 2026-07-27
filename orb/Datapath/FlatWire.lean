import Datapath.FlatStage

/-!
# Datapath.FlatWire — the flat egress serializer that takes `HdrBlock` DIRECTLY

This module closes residual **(b)** of the cons-list removal (the `Response.headers`
`List` seam named at the bottom of `Datapath.FlatStage`). The flat stage work
(`FlatStage.flatSecuredResp`, `flatSecurity_serialize_refines`) still `denote`s the
flat `HdrBlock` back to a `List` at the `Reactor.Response.headers` field boundary —
it builds a whole `Reactor.Response` *record* whose `headers : List (Bytes × Bytes)`
field is the materialized cons-list, and only then serializes. That record-field
materialization is the last place the response header block becomes a `List` on the
egress path.

`serializeFlat` here takes the flat `HdrBlock` **directly** — no
`Reactor.Response` record with a `List` header field is ever constructed on the
flat path — and renders the response bytes:

```
status-line  ++  CRLF  ++  flatRenderBlock (hb.addHeader Content-Length)  ++  CRLF CRLF  ++  body
```

The single header the deployed serializer derives (`Content-Length`) is pushed onto
the flat block with `HdrBlock.addHeader` (an amortized-`O(1)` `Array.push`), then the
whole block renders flat through `FlatHeaders.flatRenderBlock`. The header block is
never converted to a `Reactor.Response.headers` cons-list.

## What is proven (equality-transfer to the DEPLOYED serializer, NOT a re-spec)

* `serializeFlat_refines` — `serializeFlat status reason hb body` is **byte-identical**
  to `Reactor.serialize (respOf status reason hb body)`, the *deployed* serializer run
  on the response whose header block is `hb.denote`. The `denote` appears ONLY on the
  spec (RHS) side — the theorem's statement of *what* bytes are produced — never in the
  flat computation. The proof chains `FlatHeaders.flatRenderBlock_refines` (the flat
  header render = `renderHeaders`) with `HdrBlock.denote_addHeader` (the pushed
  `Content-Length` header) and the array-append distribution — reusing, not re-proving,
  the deployed serialize structure (`Reactor.serialize` unfolds through
  `serializeWire`/`build`/`allHeaders`/`statusLine`). Non-vacuous: a concrete
  status + 2-header `HdrBlock` + body evaluates to the exact wire bytes (`#guard`).

* `flatSecurity_wire_refines` — the exemplar composition: `flatSecurityStage`'s flat
  `HdrBlock` feeds `serializeFlat` DIRECTLY, byte-identical to `Reactor.serialize` of
  the deployed security stage's response (`FlatStage.securedResp`), with NO
  intermediate `Reactor.Response`-record `List` header materialization — the seam
  `FlatStage.flatSecurity_serialize_refines` still paid via `flatSecuredResp`.

## Honest scope of "no `List` materialization"

`serializeFlat` constructs no `Reactor.Response` record and no `allHeaders`
cons-list; the header pairs stay in the `HdrBlock` `Array` and are pushed/rendered
flat. The one residual `Array.toList` is *inside* `FlatHeaders.flatRenderBlock`
(`foldAppend … (headerFragments h.denote)` enumerates the fragment structure from
`h.denote = h.headers.toList`); that lives in the un-modifiable `FlatHeaders` and is a
distinct, smaller item (one `O(#headers)` pair-list, not the per-stage response
spine). The named residual-(b) seam — the `Reactor.Response.headers` record field —
is genuinely removed by this path.
-/

namespace Datapath.FlatWire

open Proto (Bytes)
open Reactor (Response)
open Datapath.FlatHeaders
open Datapath.FlatStage
open Datapath.Refinement
open Reactor.Stage.SecurityHeaders (securityheadersStage wireHeaders policy)

/-! ## The derived `Content-Length` header, as a flat pushable pair -/

/-- The `Content-Length` header the deployed serializer derives from the body — the
SAME `(clName, natToDec body.length)` pair `Reactor.allHeaders` appends, presented as a
single `HdrBlock.addHeader` push onto the flat block. -/
def clHeader (body : Bytes) : Bytes × Bytes := (Reactor.clName, Reactor.natToDec body.length)

/-! ## The flat egress serializer — takes `HdrBlock` directly -/

/-- **The flat response serializer, over `HdrBlock` directly.** Renders the response
bytes from the flat header block with NO `Reactor.Response` record and NO `List`
header spine: push the derived `Content-Length` header onto the flat block
(`HdrBlock.addHeader`, an `Array.push`), render the whole block flat
(`FlatHeaders.flatRenderBlock`), and frame it with the status line and the blank-line
separator, with the body as the shared right operand. Wrapped as the `ByteArray` wire
type the host sends. -/
def serializeFlat (status : Nat) (reason : Bytes) (hb : HdrBlock) (body : Bytes) : ByteArray :=
  let statusBytes : Array UInt8 :=
    (Reactor.http11 ++ [32] ++ Reactor.natToDec status ++ [32] ++ reason).toArray
  ByteArray.mk (
    statusBytes
      ++ Reactor.crlf.toArray
      ++ flatRenderBlock (hb.addHeader (clHeader body))
      ++ Reactor.crlf.toArray
      ++ Reactor.crlf.toArray
      ++ body.toArray)

/-- The response the flat path's bytes are stated against on the SPEC side: the
deployed `Reactor.Response` whose header block is the flat block's denotation. This is
the abstract object `serializeFlat`'s output is proven byte-identical to; it is NOT
constructed on the flat computation path. -/
def respOf (status : Nat) (reason : Bytes) (hb : HdrBlock) (body : Bytes) : Response :=
  { status := status, reason := reason, headers := hb.denote, body := body }

/-! ## The byte-identity — flat `HdrBlock` egress = deployed `serialize`, exactly -/

/-- **THE FLAT EGRESS BYTE-IDENTITY.** `serializeFlat status reason hb body` is
byte-identical to `Reactor.serialize (respOf status reason hb body)` — the *deployed*
serializer on the response with header block `hb.denote`. The `denote` is only in the
SPEC (the `respOf` on the RHS): the flat computation pushes the `Content-Length`
header onto the `Array`-backed block and renders it flat, never building a
`Reactor.Response.headers` cons-list. Proof: unfold the deployed serialize structure
(`serializeWire`/`build`/`allHeaders`/`statusLine`), fold the pushed `Content-Length`
into the block by `HdrBlock.denote_addHeader`, discharge the header render by
`flatRenderBlock_refines`, and distribute `Array.toList` over the frame appends. No
re-specification of serialize — an equality transfer to the deployed function. -/
theorem serializeFlat_refines (status : Nat) (reason : Bytes) (hb : HdrBlock) (body : Bytes) :
    Datapath.Refinement.Refines (Reactor.serialize (respOf status reason hb body))
      (serializeFlat status reason hb body) := by
  -- the flat header render = renderHeaders of the block WITH Content-Length pushed
  have hrender : (flatRenderBlock (hb.addHeader (Reactor.clName, Reactor.natToDec body.length))).toList
      = Reactor.renderHeaders (hb.denote ++ [(Reactor.clName, Reactor.natToDec body.length)]) := by
    have h := flatRenderBlock_refines (hb.addHeader (Reactor.clName, Reactor.natToDec body.length))
    rwa [HdrBlock.denote_addHeader] at h
  show (serializeFlat status reason hb body).data.toList
      = Reactor.serialize (respOf status reason hb body)
  simp only [serializeFlat, Reactor.serialize, Reactor.serializeWire, Reactor.build,
    Reactor.allHeaders, Reactor.statusLine, respOf, clHeader,
    Array.toList_append, List.toList_toArray, hrender, List.append_assoc]

/-! ## Non-vacuity — a concrete response, evaluated to the exact wire bytes -/

/-- A concrete 2-header flat block: `X-A: 1` and `X-B: 22`. -/
def demoBlock : HdrBlock :=
  HdrBlock.ofList [("X-A".toUTF8.toList, "1".toUTF8.toList), ("X-B".toUTF8.toList, "22".toUTF8.toList)]

-- The flat egress serializer on a concrete status + 2-header block + body equals the
-- deployed serialize of the same response — evaluated by the kernel, not just proven.
#guard (serializeFlat 200 Reactor.reasonOK demoBlock "hello".toUTF8.toList).data.toList
        == Reactor.serialize (respOf 200 Reactor.reasonOK demoBlock "hello".toUTF8.toList)

-- The exact wire bytes are a genuine HTTP/1.1 response head (status line + the two
-- headers + derived Content-Length + blank line + body) — the concrete wire witness.
#guard (serializeFlat 200 Reactor.reasonOK demoBlock "hello".toUTF8.toList).data.toList
        == "HTTP/1.1 200 OK\r\nX-A: 1\r\nX-B: 22\r\nContent-Length: 5\r\n\r\nhello".toUTF8.toList

-- Genuine dependence on the input: different bodies give different flat wire bytes.
#guard (serializeFlat 200 Reactor.reasonOK demoBlock "a".toUTF8.toList).data.toList
        != (serializeFlat 200 Reactor.reasonOK demoBlock "bb".toUTF8.toList).data.toList

/-! ## The exemplar composition — flat security stage ⟶ flat egress, NO `List` seam -/

/-- **The seam closed for the exemplar stage.** `flatSecurityStage`'s flat `HdrBlock`
feeds `serializeFlat` DIRECTLY — no `flatSecuredResp` / `Reactor.Response`-record
`List` header materialization — and the result is byte-identical to `Reactor.serialize`
of the DEPLOYED security stage's response (`FlatStage.securedResp`). Chains the
flat-stage header effect (`flatSecurityStage_refines`, the push-fold = append-fold
equality) into `serializeFlat_refines`. The whole egress of the security stage is flat:
the header block is pushed flat and serialized flat, never a `Response.headers`
cons-cell. -/
theorem flatSecurity_wire_refines (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (securedResp r))
      (serializeFlat r.status r.reason (flatSecurityStage (HdrBlock.ofList r.headers)) r.body) := by
  have hh : (flatSecurityStage (HdrBlock.ofList r.headers)).denote
      = r.headers ++ wireHeaders policy := by
    rw [flatSecurityStage_refines (HdrBlock.ofList r.headers), HdrBlock.denote_ofList]
  have key : respOf r.status r.reason (flatSecurityStage (HdrBlock.ofList r.headers)) r.body
      = securedResp r := by
    unfold respOf securedResp
    rw [hh]
  rw [← key]
  exact serializeFlat_refines _ _ _ _

-- The exemplar composition, evaluated: the flat security stage's egress bytes equal
-- the deployed serialize of the secured response — on a real 200 OK with a base header.
#guard (serializeFlat (Reactor.ok200 "hi".toUTF8.toList).status (Reactor.ok200 "hi".toUTF8.toList).reason
          (flatSecurityStage (HdrBlock.ofList (Reactor.ok200 "hi".toUTF8.toList).headers))
          (Reactor.ok200 "hi".toUTF8.toList).body).data.toList
        == Reactor.serialize (securedResp (Reactor.ok200 "hi".toUTF8.toList))

end Datapath.FlatWire
