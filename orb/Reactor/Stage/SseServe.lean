import Reactor.Pipeline
import Sse.Framing

/-!
# Reactor.Stage.SseServe — the deployed Server-Sent-Events endpoint (PARITY-LEDGER sse.1)

sse.1 was PARTIAL with the deployed half missing: the SSE wire framing was fully
proven (`Sse.Frame.parseFrame_encodeFrame` — encode/decode inversion;
`SseFrameCorrect` — the wire-vector refinement), but the deployed serve answered
`GET /events` with a `404` — the proven leaf reached no wire. This module supplies
the missing half:

* `sseGateStage` — a request-phase gate: `GET /events` (method + target scoped) is
  answered `200` whose BODY is the LF-rendered wire encoding of two concrete
  events, produced by the PROVEN encoder (`Sse.encodeFrame` via
  `Sse.Framing.wireBytes`) — not hand-written bytes.
* `sseHeadStage` — a response-phase stamp on `GET /events`:
  `Content-Type: text/event-stream` (the SSE media type), placed OUTSIDE the
  deployed rewrite onion so the pair reaches the wire.

## What is proved here (all pure kernel)

* `sseGate_fires` / `sseGate_passes` — the gate answers exactly the scope.
* `sseHeadStage_effect` / `sseHeadStage_noop` — the stamp appends exactly the
  media-type pair in scope and is the identity off the target.
* `sseBody_renders` — the served body IS `renderLF` of the two encoded frames
  (definitional: the encoder produces the bytes).
* `frame1_parses` / `frame2_parses` — the served frames re-parse through the PROVEN
  `Sse.parseFrame` to exactly the two events, each consuming exactly its own
  encoded length (the round-trip `parseFrame_encodeFrame`, instantiated on the
  deployed events — the framing proof now grounds DEPLOYED bytes).

Named residuals (honest): this is a one-shot proven-framed event burst per
request, not a held-open push stream — the long-lived-connection scheduling is a
host concern the sans-IO fold does not model; the deployed onion's default
caching-policy stamp applies to `/events` like any other `200` (no `no-store`
override here).
-/

namespace Reactor.Stage.SseServe

open Reactor.Pipeline
open Proto (Bytes)

/-- ASCII `"GET"`. -/
def getBytes : Bytes := [71, 69, 84]

/-- ASCII `"/events"` — the SSE endpoint. -/
def eventsTarget : Bytes := [47, 101, 118, 101, 110, 116, 115]

/-- ASCII `"Content-Type"`. -/
def ctName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101]

/-- ASCII `"text/event-stream"` (the SSE media type). -/
def ctVal : Bytes :=
  [116, 101, 120, 116, 47, 101, 118, 101, 110, 116, 45, 115, 116, 114, 101, 97, 109]

/-- ASCII `"OK"`. -/
def okReason : Bytes := [79, 75]

/-- The endpoint's guard: method `GET`, target `/events`. -/
def inScope (c : Ctx) : Bool :=
  c.req.method == getBytes && c.req.target == eventsTarget

/-- The first served event: `event: greeting` / `id: 1` / `data: hello`. -/
def ev1 : Sse.Event :=
  { event := some [103, 114, 101, 101, 116, 105, 110, 103]
    id := some [49]
    retry := none
    data := [[104, 101, 108, 108, 111]] }

/-- The second served event: `data: world` (default event type). -/
def ev2 : Sse.Event :=
  { event := none, id := none, retry := none, data := [[119, 111, 114, 108, 100]] }

/-- Both events are well-formed for the round-trip (no `retry` field). -/
theorem ev1_wf : ev1.Wf := trivial
theorem ev2_wf : ev2.Wf := trivial

/-- **The served body**: the LF-rendered wire encoding of the two events, straight
from the PROVEN encoder. -/
def sseBody : Bytes := Sse.Framing.wireBytes ev1 ++ Sse.Framing.wireBytes ev2

/-- The endpoint's bare response. NO headers: the media type is stamped by
`sseHeadStage` outside the rewrite onion, and a header-less seed keeps the
deployed content-type-gated body rewrite a passthrough. -/
def sseResp : Reactor.Response :=
  { status := 200, reason := okReason, headers := [], body := sseBody }

/-- **The SSE gate.** Answers `GET /events` with the proven-framed event burst;
passes everything else through untouched. -/
def sseGateStage : Stage where
  name := "sse-endpoint"
  onRequest := fun c => if inScope c then .respond sseResp else .continue c
  onResponse := fun _ b => b

/-- **The SSE media-type stamp.** Response phase: on `GET /events`, push
`Content-Type: text/event-stream`; identity elsewhere. -/
def sseHeadStage : Stage where
  name := "sse-head"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if inScope c then b.addHeader (ctName, ctVal) else b

/-! ## The guard -/

theorem inScope_true (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = eventsTarget) : inScope c = true := by
  unfold inScope
  rw [hm, ht]
  rfl

theorem inScope_false_of_target (c : Ctx) (h : ¬ c.req.target = eventsTarget) :
    inScope c = false := by
  unfold inScope
  have hf : (c.req.target == eventsTarget) = false := by
    cases hb : c.req.target == eventsTarget
    · rfl
    · exact absurd (eq_of_beq hb) h
  rw [hf, Bool.and_false]

/-! ## Gate / stamp behaviour -/

theorem sseGate_fires (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = eventsTarget) :
    sseGateStage.onRequest c = .respond sseResp := by
  show (if inScope c then StageStep.respond sseResp else StageStep.continue c) = _
  rw [inScope_true c hm ht]
  rfl

theorem sseGate_passes (c : Ctx) (h : ¬ c.req.target = eventsTarget) :
    sseGateStage.onRequest c = .continue c := by
  show (if inScope c then StageStep.respond sseResp else StageStep.continue c) = _
  rw [inScope_false_of_target c h]
  rfl

theorem sseGate_statusStable : Stage.statusStable sseGateStage := fun _ _ => rfl

/-- **The stamp's byte-effect.** On `GET /events` the finalized pipeline is the
tail's with the media-type pair appended — for ANY tail/handler. -/
theorem sseHeadStage_effect (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (hm : c.req.method = getBytes) (ht : c.req.target = eventsTarget) :
    runPipeline (sseHeadStage :: rest) h c
      = (runPipeline rest h c).addHeader (ctName, ctVal) := by
  rw [pipeline_stage_effect sseHeadStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (ctName, ctVal)
        else runPipeline rest h c) = _
  rw [inScope_true c hm ht]
  rfl

theorem sseHeadStage_noop (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (ht : ¬ c.req.target = eventsTarget) :
    runPipeline (sseHeadStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect sseHeadStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (ctName, ctVal)
        else runPipeline rest h c) = _
  rw [inScope_false_of_target c ht]
  rfl

theorem sseHeadStage_statusStable : Stage.statusStable sseHeadStage := by
  intro c b
  show ((if inScope c then b.addHeader (ctName, ctVal) else b).build).status
       = b.build.status
  by_cases h : inScope c = true
  · rw [if_pos h]; rfl
  · rw [if_neg h]

/-! ## The framing proofs, grounded on the DEPLOYED bytes -/

/-- The served body IS the LF-rendering of the two encoded frames (the encoder
produces the bytes — definitional through `renderLF_append`). -/
theorem sseBody_renders :
    sseBody = Sse.Framing.renderLF (Sse.encodeFrame ev1 ++ Sse.encodeFrame ev2) := by
  rw [Sse.Framing.renderLF_append]
  rfl

/-- **The first served frame round-trips.** Parsing the served line sequence
dispatches EXACTLY `ev1`, consuming exactly its own encoded length and leaving
exactly the second frame — the proven encode/decode inversion, instantiated on
deployed bytes. -/
theorem frame1_parses :
    Sse.parseFrame (Sse.encodeFrame ev1 ++ Sse.encodeFrame ev2)
      = .complete ev1 (Sse.encodeFrame ev1).length (Sse.encodeFrame ev2) :=
  Sse.parseFrame_encodeFrame ev1 (Sse.encodeFrame ev2) ev1_wf

/-- **The second served frame round-trips** (the remainder the first parse leaves). -/
theorem frame2_parses :
    Sse.parseFrame (Sse.encodeFrame ev2)
      = .complete ev2 (Sse.encodeFrame ev2).length [] := by
  have h := Sse.parseFrame_encodeFrame ev2 [] ev2_wf
  simpa using h

/-- Concrete non-vacuity: the two deployed frames are the expected field-line
counts (`event:`/`id:`/`data:`/blank, then `data:`/blank) — kernel-computed. -/
theorem frames_concrete :
    (Sse.encodeFrame ev1).length = 4 ∧ (Sse.encodeFrame ev2).length = 2 := by
  decide

end Reactor.Stage.SseServe

#print axioms Reactor.Stage.SseServe.sseGate_fires
#print axioms Reactor.Stage.SseServe.sseHeadStage_effect
#print axioms Reactor.Stage.SseServe.sseBody_renders
#print axioms Reactor.Stage.SseServe.frame1_parses
#print axioms Reactor.Stage.SseServe.frame2_parses
#print axioms Reactor.Stage.SseServe.frames_concrete
