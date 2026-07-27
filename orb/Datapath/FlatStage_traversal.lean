import Datapath.ByteRefine
import Reactor.Deploy

/-!
# Datapath.FlatStage_traversal — the deployed `traversal` GATE stage, flat.

The confirmed exemplar `Datapath.FlatStage` de-risked a HEADER-transform stage
(`securityheaders`): its whole effect is a header fold, and the byte-identity is
about the folded response. This file does the sibling for a **GATE** stage — the
deployed `Reactor.Deploy.traversalStage` (position 0 of `deployStages`) — which
does NOT fold headers: it DECIDES on the request path and, on a `..`-escape,
short-circuits with a fixed `traversalBlocked404` response.

## The cons-list the gate walks (what "flat" removes)

The real decision is `Reactor.Deploy.escapesSegs`, read off Deploy.lean:

    escapesSegs segs = (Route.Path.decodeSegs segs).contains ".."
                     = (segs.map Route.Path.decodeSeg).contains ".."

`segs : List String` is the request-path segment spine. `decodeSegs` is a
`List.map` that copies that whole cons-spine, and `.contains ".."` walks it once
more. That outer segment cons-spine is the gate's half of the cons-list cost.

`SegBlock` holds those segments in a contiguous `Array String`; `flatEscapes`
runs the SAME percent-decode + `..`-check flat (`Array.map` / `Array.contains`,
no cons-spine copy), and denotes back to the `List String` the spec decides on.

## What is proven here (equality-transfer + byte-identity, NOT a re-spec)

* `flatEscapes_refines` — the flat decision equals the REAL `escapesSegs` on the
  denotation (`flatEscapes b = escapesSegs b.denote`). Equality-transfer of the
  `Array.map`/`Array.contains` flat form to the `List.map`/`List.contains` spec;
  non-vacuous (the flat op genuinely maps + checks a contiguous array).
* `flatEscapes_eq_targetEscapes` — grounded on the REAL request-level gate: for
  segments denoting the request's raw segments, `flatEscapes` equals the deployed
  `Reactor.Deploy.targetEscapes` (`= escapesSegs (rawSegsOf req)`).
* `flatTraversalStage_decides` — the flat decision reproduces the REAL
  `traversalStage.onRequest` branch exactly (`.respond traversalBlocked404` on a
  `..`-escape, `.continue` otherwise). The DECISION matches the real stage.
* `flatTraversal_response_byte_identical` — the emitted response is byte-identical:
  the flat serializer of `traversalBlocked404` refines `Reactor.serialize`
  (`Datapath.Refinement.flatSerialize_refines`, the derived flat serializer).
* `flatTraversal_guardOne_refines` — the END-TO-END byte identity grounded in the
  DEPLOYED byte effect: when the flat gate fires (and the segments denote the
  request's raw segments), the flat-serialized `traversalBlocked404` bytes are
  byte-identical to the REAL `Reactor.Deploy.guardOne` output — the very bytes
  `main` writes on an escaping request (`guardOne_blocks`).
-/

namespace Datapath.FlatStage.Traversal

open Proto (Bytes)
open Datapath.Refinement (flatSerialize flatSerialize_refines)

/-! ## 1. The flat segment block -/

/-- **The flat request-path segment block.** The path segments held in a
contiguous `Array String` instead of a `List String` cons-spine. The traversal
gate decodes + `..`-checks them flat (`Array.map`/`Array.contains`); `denote`
bridges back to the `List String` the deployed `escapesSegs` decides on. The
segment-grain analogue of `Datapath.FlatHeaders.HdrBlock` for the request path. -/
structure SegBlock where
  /-- The path segments, flat and contiguous. -/
  segs : Array String
deriving Repr

namespace SegBlock

/-- **The abstraction relation.** The `List String` segment list a flat `SegBlock`
denotes — `Array.toList` (in the running datapath the segments are already
contiguous and this is identity). -/
def denote (b : SegBlock) : List String := b.segs.toList

/-- Materialize a segment list into a flat block — the leaf of a derivation. -/
def ofList (segs : List String) : SegBlock := ⟨segs.toArray⟩

@[simp] theorem denote_ofList (segs : List String) : (ofList segs).denote = segs := by
  show segs.toArray.toList = segs
  rw [List.toList_toArray]

end SegBlock

/-! ## 2. The flat traversal decision, and its refinement of the REAL `escapesSegs` -/

/-- **The flat traversal decision.** Percent-decode every segment flat
(`Array.map Route.Path.decodeSeg`, no cons-spine copy) then check for a decoded
`..` (`Array.contains`). The flat sibling of the deployed
`Reactor.Deploy.escapesSegs` (`decodeSegs · |>.contains ".."`), computed over the
contiguous `SegBlock` instead of the `List String` spine. -/
def flatEscapes (b : SegBlock) : Bool :=
  (b.segs.map Route.Path.decodeSeg).contains (".." : String)

/-- **The flat decision equals the REAL `escapesSegs` on the denotation.**
Equality-transfer: `Array.map`+`Array.contains` over the contiguous block computes
exactly the `List.map`+`List.contains` the deployed `escapesSegs` runs on the
denoted segment list. Non-vacuous — the flat op genuinely maps and scans a real
array; the content is proven equal, not assumed. -/
theorem flatEscapes_refines (b : SegBlock) :
    flatEscapes b = Reactor.Deploy.escapesSegs b.denote := by
  unfold flatEscapes Reactor.Deploy.escapesSegs SegBlock.denote Route.Path.decodeSegs
  rw [← Array.toList_map, ← List.contains_toArray, Array.toArray_toList]

/-! ## 3. Grounding on the REAL request-level gate -/

/-- **The flat decision equals the deployed request-level gate.** For a segment
block denoting the request's raw segments (`rawSegsOf`), `flatEscapes` equals the
REAL `Reactor.Deploy.targetEscapes` — the gate `guardOne`/`traversalStage` decide
on. Grounded via `targetEscapes_eq_segs` (the deployed request→segment bridge). -/
theorem flatEscapes_eq_targetEscapes (b : SegBlock) (req : Proto.Request)
    (hb : b.denote = Reactor.Deploy.rawSegsOf req) :
    flatEscapes b = Reactor.Deploy.targetEscapes req := by
  rw [flatEscapes_refines, hb, Reactor.Deploy.targetEscapes_eq_segs]

/-- **The DECISION matches the REAL stage.** The flat decision reproduces the
deployed `traversalStage.onRequest` branch exactly: a `..`-escape yields
`.respond traversalBlocked404` (short-circuit; the escaped resource is never
reached), everything else `.continue`. Read off the REAL `traversalStage`
(`onRequest = match targetEscapes …`), with the gate value replaced by the flat
one via `flatEscapes_eq_targetEscapes`. Not re-specified: the stage's own branch. -/
theorem flatTraversalStage_decides (b : SegBlock) (c : Reactor.Pipeline.Ctx)
    (hb : b.denote = Reactor.Deploy.rawSegsOf c.req) :
    Reactor.Deploy.traversalStage.onRequest c
      = (match flatEscapes b with
         | true  => .respond Reactor.Deploy.traversalBlocked404
         | false => .continue c) := by
  show (match Reactor.Deploy.targetEscapes c.req with
        | true  => Reactor.Pipeline.StageStep.respond Reactor.Deploy.traversalBlocked404
        | false => Reactor.Pipeline.StageStep.continue c)
      = _
  rw [flatEscapes_eq_targetEscapes b c.req hb]

/-! ## 4. The RESPONSE is byte-identical (the fixed 404 form) -/

/-- **The emitted response is byte-identical.** The gate's `..`-escape arm emits
the serializer-built `traversalBlocked404` (a fixed, target-independent 404 — no
resolved file bytes can flow). Its flat serialization (the derived flat serializer
`Datapath.Refinement.flatSerialize`) is byte-identical to `Reactor.serialize`, by
`flatSerialize_refines`. -/
theorem flatTraversal_response_byte_identical :
    Datapath.Refinement.Refines (Reactor.serialize Reactor.Deploy.traversalBlocked404)
      (flatSerialize Reactor.Deploy.traversalBlocked404) :=
  flatSerialize_refines Reactor.Deploy.traversalBlocked404

/-- **END-TO-END, grounded in the DEPLOYED byte effect.** When the flat gate fires
on a request whose raw segments the block denotes, the flat-serialized
`traversalBlocked404` bytes are byte-identical to the REAL
`Reactor.Deploy.guardOne` output — the exact bytes `main` writes on an escaping
request (`guardOne_blocks`, the deployed Safety branch). So the flat gate's
decision AND its response bytes match the deployed serve, not a re-specification. -/
theorem flatTraversal_guardOne_refines (input : Bytes) (req : Proto.Request)
    (b : SegBlock) (hb : b.denote = Reactor.Deploy.rawSegsOf req)
    (hfire : flatEscapes b = true) :
    Datapath.Refinement.Refines (Reactor.Deploy.guardOne input req)
      (flatSerialize Reactor.Deploy.traversalBlocked404) := by
  have hesc : Reactor.Deploy.targetEscapes req = true := by
    rw [← flatEscapes_eq_targetEscapes b req hb]; exact hfire
  rw [Reactor.Deploy.guardOne_blocks input req hesc]
  exact flatSerialize_refines Reactor.Deploy.traversalBlocked404

/-! ## Non-vacuity — the flat gate genuinely computes the REAL deployed effect -/

-- The flat decision computes exactly the REAL `escapesSegs` — evaluated by the
-- kernel on the concrete segment lists a parsed target produces (mirroring the
-- deployed `escape_fires_dotdot` / `escape_quiet_double_encoded` witnesses).
#guard flatEscapes (SegBlock.ofList ["..", "etc", "passwd"])
        == Reactor.Deploy.escapesSegs ["..", "etc", "passwd"]
#guard flatEscapes (SegBlock.ofList ["health"])
        == Reactor.Deploy.escapesSegs ["health"]

-- The gate FIRES on a `..`-escape and on the once-decoded `%2e%2e` …
#guard flatEscapes (SegBlock.ofList ["..", "etc", "passwd"]) == true
#guard flatEscapes (SegBlock.ofList ["%2e%2e", "etc", "passwd"]) == true
-- … stays QUIET on a legitimate target and on the double-encoded `%252e%252e`
-- (single-decode boundary — the harmless literal `%2e%2e`, not `..`).
#guard flatEscapes (SegBlock.ofList ["health"]) == false
#guard flatEscapes (SegBlock.ofList ["%252e%252e", "etc"]) == false

-- The flat op genuinely depends on the input (not a constant).
#guard flatEscapes (SegBlock.ofList ["..", "x"]) != flatEscapes (SegBlock.ofList ["health"])

-- The emitted response bytes are byte-identical to the deployed `serialize` —
-- evaluated by the kernel.
#guard (flatSerialize Reactor.Deploy.traversalBlocked404).data.toList
        == Reactor.serialize Reactor.Deploy.traversalBlocked404

end Datapath.FlatStage.Traversal
