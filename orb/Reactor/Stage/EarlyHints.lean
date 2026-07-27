import Reactor.Pipeline

/-!
# Reactor.Stage.EarlyHints — 103 Early Hints (RFC 8297) over the serve pipeline

RFC 8297 lets a server send one or more **`103 (Early Hints)`** *informational*
(interim) responses BEFORE the single final (non-1xx) response. Each 103 carries
`Link` headers (typically `rel=preload` / `rel=preconnect`) so the client can
start fetching sub-resources while the origin is still assembling the final
response. The interim is out-of-band: it never becomes the response and never
touches the final status/body.

This file proves that discipline **against the real serve pipeline**
(`Reactor.Pipeline.runPipeline` / `ResponseBuilder.build`), not an abstract
transcript. The final response is exactly what the stage pipeline builds; the
103 is *derived* from it — it advertises precisely the `Link` headers the final
response carries (the RFC's intent: hint the very preloads the final will
reference) — and is placed on the wire *ahead* of that final response.

## The model

* `onlyLinks` — project a header list to just its `Link` headers.
* `mk103` — build a `103 Early Hints` interim from a link-header list: status
  `103`, empty body, headers = exactly those links.
* `Emission` — the ordered wire output: a list of interim responses followed by
  one final response; `Emission.wire = interims ++ [final]` is the emitted order.
* `earlyHintsEmit` — from a final `Response`, emit one 103 carrying its `Link`
  headers, then the unchanged final.
* `emitWithHints` — the pipeline hook: run `runPipeline`, `build` its
  `ResponseBuilder`, and emit early hints over that built response.

## Headline theorems (all over the real pipeline output)

* `early_hints_103`        — a `103` interim carrying the final's `Link` headers
  is emitted, and it precedes the final on the wire (`wire = [i103, final]`).
* `early_hints_then_final` — the final response is *unaffected* by the 103: it is
  byte-for-byte the pipeline's built response, and it is the last thing emitted.
* `early_hints_link_only`  — every header the `103` carries is a `Link` header
  (nothing else leaks into the interim).

Supporting: `early_hints_final_not_103` (a real ≥200 final never reports 103),
and a concrete non-vacuity witness (`example_103_drops_non_link`) showing a mixed
header block keeps only its `Link` headers in the interim.

Every theorem closes by `rfl` / core `List` lemmas — no axioms beyond
`{propext, Quot.sound, Classical.choice}`, and none is vacuous.
-/

namespace Reactor.Stage.EarlyHints

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx Stage runPipeline ResponseBuilder)

/-! ## Header names as bytes (rfl-reducible literals) -/

/-- The `Link` header name (`"Link"`) as explicit ASCII bytes, so `filter`/`==`
reduce in the kernel. -/
def linkName : Bytes := [76, 105, 110, 107]

/-- The `103` interim reason phrase (`"Early Hints"`) as ASCII bytes. -/
def earlyHintsReason : Bytes :=
  [69, 97, 114, 108, 121, 32, 72, 105, 110, 116, 115]

/-- The `103` status code. -/
def status103 : Nat := 103

/-- Is this header a `Link` header? (Exact-name match on the header key.) -/
def isLink (h : Bytes × Bytes) : Bool := h.1 == linkName

/-- Keep only the `Link` headers of a header block. -/
def onlyLinks (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  hs.filter isLink

/-- Build a `103 Early Hints` interim response from a list of link headers:
status `103`, empty body, and exactly the given (link) headers. -/
def mk103 (links : List (Bytes × Bytes)) : Response :=
  { status := status103, reason := earlyHintsReason, headers := links, body := [] }

/-! ## The emitted wire sequence -/

/-- The ordered output of an early-hints exchange: a list of interim (1xx)
responses, then exactly one final (non-1xx) response. -/
structure Emission where
  /-- The interim `103` responses, in emitted order (each precedes `final`). -/
  interims : List Response
  /-- The single final (non-1xx) response — the real answer. -/
  final : Response

/-- The full emitted sequence on the wire: every interim, in order, then the
final. This IS the order bytes leave the server. -/
def Emission.wire (e : Emission) : List Response := e.interims ++ [e.final]

/-- From a final `Response`, emit one `103` carrying exactly that response's
`Link` headers (RFC 8297: advertise the preloads the final will reference), then
the unchanged final response. -/
def earlyHintsEmit (final : Response) : Emission :=
  { interims := [mk103 (onlyLinks final.headers)], final := final }

/-- **The pipeline hook.** Run the stage pipeline, `build` its affine
`ResponseBuilder` to the wire `Response`, and emit early hints over that built
response. This is the exact object every headline theorem below is stated over —
`final` is literally the pipeline's output. -/
def emitWithHints (stages : List Stage) (handler : Ctx → Response) (c : Ctx) : Emission :=
  earlyHintsEmit ((runPipeline stages handler c).build)

/-! ## Headline theorems (over the real pipeline output) -/

/-- **`early_hints_103`.** Running the serve pipeline and emitting early hints
puts a `103` interim carrying exactly the final response's `Link` headers on the
wire *before* the final response: the emitted sequence is `[i103, final]` with the
`103` first. -/
theorem early_hints_103 (stages : List Stage) (handler : Ctx → Response) (c : Ctx) :
    ∃ i103 : Response,
      (emitWithHints stages handler c).wire = [i103, (runPipeline stages handler c).build] ∧
      i103.status = status103 ∧
      i103.headers = onlyLinks ((runPipeline stages handler c).build).headers := by
  exact ⟨mk103 (onlyLinks ((runPipeline stages handler c).build).headers), rfl, rfl, rfl⟩

/-- The `103` is literally the head of the emitted sequence (it precedes the
final), stated positionally. -/
theorem early_hints_103_is_head (stages : List Stage) (handler : Ctx → Response) (c : Ctx) :
    (emitWithHints stages handler c).wire.head?
      = some (mk103 (onlyLinks ((runPipeline stages handler c).build).headers)) := rfl

/-- **`early_hints_then_final`.** The final response is *unaffected* by the 103:
it is byte-for-byte the response the pipeline built, and it is the last thing on
the wire. The 103 changes only *when* / *what precedes*, never *what the final
is*. -/
theorem early_hints_then_final (stages : List Stage) (handler : Ctx → Response) (c : Ctx) :
    (emitWithHints stages handler c).final = (runPipeline stages handler c).build ∧
    (emitWithHints stages handler c).wire.getLast?
      = some ((runPipeline stages handler c).build) ∧
    (emitWithHints stages handler c).final.status
      = ((runPipeline stages handler c).build).status := by
  refine ⟨rfl, ?_, rfl⟩
  rfl

/-- **`early_hints_link_only`.** Every header the `103` interim carries is a
`Link` header — no non-`Link` header leaks into the interim. -/
theorem early_hints_link_only (stages : List Stage) (handler : Ctx → Response) (c : Ctx)
    (i : Response) (hi : i ∈ (emitWithHints stages handler c).interims) :
    ∀ h ∈ i.headers, isLink h = true := by
  simp only [emitWithHints, earlyHintsEmit, List.mem_singleton] at hi
  subst hi
  intro h hmem
  simp only [mk103, onlyLinks, List.mem_filter] at hmem
  exact hmem.2

/-! ## Supporting facts -/

/-- A real (≥ 200) final response never reports the interim `103` status — the
103 does not become the answer. (Hypothesis `200 ≤ status` is satisfiable, so
this is not vacuous.) -/
theorem early_hints_final_not_103
    (stages : List Stage) (handler : Ctx → Response) (c : Ctx)
    (h : 200 ≤ ((runPipeline stages handler c).build).status) :
    (emitWithHints stages handler c).final.status ≠ status103 := by
  show ((runPipeline stages handler c).build).status ≠ status103
  unfold status103
  omega

/-- The final response emitted is genuinely the *last* element and the `103` the
*first*; the wire has exactly these two, in this order. -/
theorem emitWithHints_wire (stages : List Stage) (handler : Ctx → Response) (c : Ctx) :
    (emitWithHints stages handler c).wire
      = [ mk103 (onlyLinks ((runPipeline stages handler c).build).headers),
          (runPipeline stages handler c).build ] := rfl

/-! ## Non-vacuity witness — a mixed header block keeps only its `Link` headers -/

/-- A `Content-Type` header name (`"CT"` shortened, ASCII bytes) — a NON-`Link`
header used to witness that the interim drops it. -/
def ctName : Bytes := [67, 84]

/-- A final response whose header block mixes two `Link` headers with one
non-`Link` (`CT`) header. -/
def exampleFinal : Response :=
  { status := 200, reason := [79, 75]  -- "OK"
    headers := [(linkName, [1]), (ctName, [2]), (linkName, [3])]
    body := [104, 105] }  -- "hi"

/-- **Non-vacuity.** The `103` emitted for a mixed header block carries exactly
the two `Link` headers and DROPS the `CT` header — `onlyLinks` really filters,
and the interim is nonempty. -/
theorem example_103_drops_non_link :
    (earlyHintsEmit exampleFinal).interims
      = [ { status := status103, reason := earlyHintsReason,
            headers := [(linkName, [1]), (linkName, [3])], body := [] } ] := rfl

/-- The witness interim is nonempty and carries two links (rules out the vacuous
empty-hint reading). -/
theorem example_103_two_links :
    (((earlyHintsEmit exampleFinal).interims.head?.map (·.headers)).getD []).length = 2 := rfl

def version : String := "0.1.0"

end Reactor.Stage.EarlyHints
